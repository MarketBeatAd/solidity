#include <libevmasm/Instruction.h>
#include <libsolidity/ast/AST.h>
#include <libsolidity/ast/Types.h>
#include <libsolidity/codegen/CompilerUtils.h>
#include <libsolidity/codegen/LValue.h>

using namespace solidity;
using namespace solidity::evmasm;
using namespace solidity::frontend;
using namespace solidity::langutil;

using StorageItem = GenericStorageItem<false>;
using TransientStorageItem = GenericStorageItem<true>;

/// Constructs the LValue and pushes the location of @a _declaration onto the stack.
template<bool isTransient>
GenericStorageItem<isTransient>::GenericStorageItem(CompilerContext& _compilerContext, VariableDeclaration const& _declaration):
	GenericStorageItem<isTransient>(_compilerContext, *_declaration.annotation().type)
{
	solAssert(!_declaration.immutable(), "");
	auto const& location = m_context.storageLocationOfVariable(_declaration);
	m_context << location.first << u256(location.second);
}
/// Constructs the LValue and assumes that the storage reference is already on the stack.
template<bool isTransient>
GenericStorageItem<isTransient>::GenericStorageItem(CompilerContext& _compilerContext, Type const& _type):
	LValue(_compilerContext, &_type)
{
	if (m_dataType->isValueType())
	{
		if (m_dataType->category() != Type::Category::Function)
			solAssert(m_dataType->storageSize() == m_dataType->sizeOnStack(), "");
		solAssert(m_dataType->storageSize() == 1, "Invalid storage size.");
	}
}

template<bool isTransient>
void GenericStorageItem<isTransient>::retrieveValue(langutil::SourceLocation const&, bool _remove) const
{
	// stack: storage_key storage_offset
	if (!m_dataType->isValueType())
	{
		solUnimplementedAssert(!isTransient, "Transient storage reference types are not supported yet.");
		solAssert(m_dataType->sizeOnStack() == 1, "Invalid storage ref size.");
		if (_remove)
			m_context << Instruction::POP; // remove byte offset
		else
			m_context << Instruction::DUP2;
		return;
	}
	if (!_remove)
		CompilerUtils(m_context).copyToStackTop(sizeOnStack(), sizeOnStack());
	if (m_dataType->storageBytes() == 32)
		m_context << Instruction::POP << m_loadInstruction;
	else
	{
		Type const* type = m_dataType;
		if (type->category() == Type::Category::UserDefinedValueType)
			type = type->encodingType();
		bool cleaned = false;
		m_context
			<< Instruction::SWAP1 << Instruction::SLOAD << Instruction::SWAP1
			<< u256(0x100) << Instruction::EXP << Instruction::SWAP1 << Instruction::DIV;
		if (type->category() == Type::Category::FixedPoint)
			// implementation should be very similar to the integer case.
			solUnimplemented("Not yet implemented - FixedPointType.");
		else if (FunctionType const* fun = dynamic_cast<decltype(fun)>(type))
		{
			if (fun->kind() == FunctionType::Kind::External)
			{
				CompilerUtils(m_context).splitExternalFunctionType(false);
				cleaned = true;
			}
			else if (fun->kind() == FunctionType::Kind::Internal)
			{
				m_context << Instruction::DUP1 << Instruction::ISZERO;
				CompilerUtils(m_context).pushZeroValue(*fun);
				m_context << Instruction::MUL << Instruction::OR;
			}
		}
		else if (type->leftAligned())
		{
			CompilerUtils(m_context).leftShiftNumberOnStack(256 - 8 * type->storageBytes());
			cleaned = true;
		}
		else if (
			type->category() == Type::Category::Integer &&
			dynamic_cast<IntegerType const&>(*type).isSigned()
		)
		{
			m_context << u256(type->storageBytes() - 1) << Instruction::SIGNEXTEND;
			cleaned = true;
		}

		if (!cleaned)
		{
			solAssert(type->sizeOnStack() == 1, "");
			m_context << ((u256(0x1) << (8 * type->storageBytes())) - 1) << Instruction::AND;
		}
	}
}

template<bool isTransient>
void GenericStorageItem<isTransient>::storeValue(Type const& _sourceType, langutil::SourceLocation const& _location, bool _move) const
{
	CompilerUtils utils(m_context);
	solAssert(m_dataType, "");

	// stack: value storage_key storage_offset
	if (m_dataType->isValueType())
	{
		solAssert(m_dataType->storageBytes() <= 32, "Invalid storage bytes size.");
		solAssert(m_dataType->storageBytes() > 0, "Invalid storage bytes size.");
		if (m_dataType->storageBytes() == 32)
		{
			solAssert(m_dataType->sizeOnStack() == 1, "Invalid stack size.");
			// offset should be zero
			m_context << Instruction::POP;
			if (!_move)
				m_context << Instruction::DUP2 << Instruction::SWAP1;

			m_context << Instruction::SWAP1;
			utils.convertType(_sourceType, *m_dataType, true);
			m_context << Instruction::SWAP1;

			m_context << m_storeInstruction;
		}
		else
		{
			// OR the value into the other values in the storage slot
			m_context << u256(0x100) << Instruction::EXP;
			// stack: value storage_ref multiplier
			// fetch old value
			m_context << Instruction::DUP2 << m_loadInstruction;
			// stack: value storage_ref multiplier old_full_value
			// clear bytes in old value
			m_context
				<< Instruction::DUP2 << ((u256(1) << (8 * m_dataType->storageBytes())) - 1)
				<< Instruction::MUL;
			m_context << Instruction::NOT << Instruction::AND << Instruction::SWAP1;
			// stack: value storage_ref cleared_value multiplier
			utils.copyToStackTop(3 + m_dataType->sizeOnStack(), m_dataType->sizeOnStack());
			// stack: value storage_ref cleared_value multiplier value
			if (auto const* fun = dynamic_cast<FunctionType const*>(m_dataType))
			{
				solAssert(
					_sourceType.isImplicitlyConvertibleTo(*m_dataType),
					"function item stored but target is not implicitly convertible to source"
				);
				solAssert(!fun->hasBoundFirstArgument(), "");
				if (fun->kind() == FunctionType::Kind::External)
				{
					solAssert(fun->sizeOnStack() == 2, "");
					// Combine the two-item function type into a single stack slot.
					utils.combineExternalFunctionType(false);
				}
				else
				{
					solAssert(fun->sizeOnStack() == 1, "");
					m_context <<
						((u256(1) << (8 * m_dataType->storageBytes())) - 1) <<
						Instruction::AND;
				}
			}
			else if (m_dataType->leftAligned())
			{
				solAssert(_sourceType.category() == Type::Category::FixedBytes || (
					_sourceType.encodingType() &&
					_sourceType.encodingType()->category() == Type::Category::FixedBytes
				), "source not fixed bytes");
				CompilerUtils(m_context).rightShiftNumberOnStack(256 - 8 * m_dataType->storageBytes());
			}
			else
			{
				solAssert(m_dataType->sizeOnStack() == 1, "Invalid stack size for opaque type.");
				// remove the higher order bits
				utils.convertType(_sourceType, *m_dataType, true, true);
			}
			m_context  << Instruction::MUL << Instruction::OR;
			// stack: value storage_ref updated_value
			m_context << Instruction::SWAP1 << m_storeInstruction;
			if (_move)
				utils.popStackElement(*m_dataType);
		}
	}
	else
	{
		solUnimplementedAssert(!isTransient, "Transient storage reference types are not supported yet.");
		solAssert(
			_sourceType.category() == m_dataType->category(),
			"Wrong type conversation for assignment."
		);
		if (m_dataType->category() == Type::Category::Array)
		{
			m_context << Instruction::POP; // remove byte offset
			ArrayUtils(m_context).copyArrayToStorage(
				dynamic_cast<ArrayType const&>(*m_dataType),
				dynamic_cast<ArrayType const&>(_sourceType)
			);
			if (_move)
				m_context << Instruction::POP;
		}
		else if (m_dataType->category() == Type::Category::Struct)
		{
			// stack layout: source_ref target_ref target_offset
			// note that we have structs, so offset should be zero and are ignored
			m_context << Instruction::POP;
			auto const& structType = dynamic_cast<StructType const&>(*m_dataType);
			auto const& sourceType = dynamic_cast<StructType const&>(_sourceType);
			solAssert(
				structType.structDefinition() == sourceType.structDefinition(),
				"Struct assignment with conversion."
			);
			solAssert(!structType.containsNestedMapping(), "");
			if (sourceType.location() == DataLocation::CallData)
			{
				solAssert(sourceType.sizeOnStack() == 1, "");
				solAssert(structType.sizeOnStack() == 1, "");
				m_context << Instruction::DUP2 << Instruction::DUP2;
				m_context.callYulFunction(m_context.utilFunctions().updateStorageValueFunction(sourceType, structType, 0), 2, 0);
			}
			else
			{
				for (auto const& member: structType.members(nullptr))
				{
					// assign each member that can live outside of storage
					Type const* memberType = member.type;
					solAssert(memberType->nameable(), "");
					Type const* sourceMemberType = sourceType.memberType(member.name);
					if (sourceType.location() == DataLocation::Storage)
					{
						// stack layout: source_ref target_ref
						std::pair<u256, unsigned> const& offsets = sourceType.storageOffsetsOfMember(member.name);
						m_context << offsets.first << Instruction::DUP3 << Instruction::ADD;
						m_context << u256(offsets.second);
						// stack: source_ref target_ref source_member_ref source_member_off
						StorageItem(m_context, *sourceMemberType).retrieveValue(_location, true);
						// stack: source_ref target_ref source_value...
					}
					else
					{
						solAssert(sourceType.location() == DataLocation::Memory, "");
						// stack layout: source_ref target_ref
						m_context << sourceType.memoryOffsetOfMember(member.name);
						m_context << Instruction::DUP3 << Instruction::ADD;
						MemoryItem(m_context, *sourceMemberType).retrieveValue(_location, true);
						// stack layout: source_ref target_ref source_value...
					}
					unsigned stackSize = sourceMemberType->sizeOnStack();
					std::pair<u256, unsigned> const& offsets = structType.storageOffsetsOfMember(member.name);
					m_context << dupInstruction(1 + stackSize) << offsets.first << Instruction::ADD;
					m_context << u256(offsets.second);
					// stack: source_ref target_ref target_off source_value... target_member_ref target_member_byte_off
					StorageItem(m_context, *memberType).storeValue(*sourceMemberType, _location, true);
				}
			}
			// stack layout: source_ref target_ref
			solAssert(sourceType.sizeOnStack() == 1, "Unexpected source size.");
			if (_move)
				utils.popStackSlots(2);
			else
				m_context << Instruction::SWAP1 << Instruction::POP;
		}
		else
			solAssert(false, "Invalid non-value type for assignment.");
	}
}

template<bool isTransient>
void GenericStorageItem<isTransient>::setToZero(langutil::SourceLocation const&, bool _removeReference) const
{
	if (m_dataType->category() == Type::Category::Array)
	{
		if (!_removeReference)
			CompilerUtils(m_context).copyToStackTop(sizeOnStack(), sizeOnStack());
		ArrayUtils(m_context).clearArray(dynamic_cast<ArrayType const&>(*m_dataType));
	}
	else if (m_dataType->category() == Type::Category::Struct)
	{
		// stack layout: storage_key storage_offset
		// @todo this can be improved: use StorageItem for non-value types, and just store 0 in
		// all slots that contain value types later.
		auto const& structType = dynamic_cast<StructType const&>(*m_dataType);
		for (auto const& member: structType.members(nullptr))
		{
			// zero each member that is not a mapping
			Type const* memberType = member.type;
			if (memberType->category() == Type::Category::Mapping)
				continue;
			std::pair<u256, unsigned> const& offsets = structType.storageOffsetsOfMember(member.name);
			m_context
				<< offsets.first << Instruction::DUP3 << Instruction::ADD
				<< u256(offsets.second);
			StorageItem(m_context, *memberType).setToZero();
		}
		if (_removeReference)
			m_context << Instruction::POP << Instruction::POP;
	}
	else
	{
		solAssert(m_dataType->isValueType(), "Clearing of unsupported type requested: " + m_dataType->toString());
		if (!_removeReference)
			CompilerUtils(m_context).copyToStackTop(sizeOnStack(), sizeOnStack());
		if (m_dataType->storageBytes() == 32)
		{
			// offset should be zero
			m_context
				<< Instruction::POP << u256(0)
				<< Instruction::SWAP1 << m_storeInstruction;
		}
		else
		{
			m_context << u256(0x100) << Instruction::EXP;
			// stack: storage_ref multiplier
			// fetch old value
			m_context << Instruction::DUP2 << m_loadInstruction;
			// stack: storage_ref multiplier old_full_value
			// clear bytes in old value
			m_context
				<< Instruction::SWAP1 << ((u256(1) << (8 * m_dataType->storageBytes())) - 1)
				<< Instruction::MUL;
			m_context << Instruction::NOT << Instruction::AND;
			// stack: storage_ref cleared_value
			m_context << Instruction::SWAP1 << m_storeInstruction;
		}
	}
}
