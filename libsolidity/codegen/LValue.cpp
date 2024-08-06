/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
// SPDX-License-Identifier: GPL-3.0
/**
 * @author Christian <c@ethdev.com>
 * @date 2015
 * LValues for use in the expression compiler.
 */

#include <libsolidity/codegen/LValue.h>

#include <libsolidity/ast/AST.h>
#include <libsolidity/ast/Types.h>
#include <libsolidity/codegen/CompilerUtils.h>
#include <libevmasm/Instruction.h>

#include <libsolutil/StackTooDeepString.h>

using namespace solidity;
using namespace solidity::evmasm;
using namespace solidity::frontend;
using namespace solidity::langutil;
using namespace solidity::util;


StackVariable::StackVariable(CompilerContext& _compilerContext, VariableDeclaration const& _declaration):
	LValue(_compilerContext, _declaration.annotation().type),
	m_baseStackOffset(m_context.baseStackOffsetOfVariable(_declaration)),
	m_size(m_dataType->sizeOnStack())
{
}

void StackVariable::retrieveValue(SourceLocation const& _location, bool) const
{
	unsigned stackPos = m_context.baseToCurrentStackOffset(m_baseStackOffset);
	if (stackPos + 1 > 16) //@todo correct this by fetching earlier or moving to memory
		BOOST_THROW_EXCEPTION(
			StackTooDeepError() <<
			errinfo_sourceLocation(_location) <<
			util::errinfo_comment(util::stackTooDeepString)
		);
	solAssert(stackPos + 1 >= m_size, "Size and stack pos mismatch.");
	for (unsigned i = 0; i < m_size; ++i)
		m_context << dupInstruction(stackPos + 1);
}

void StackVariable::storeValue(Type const&, SourceLocation const& _location, bool _move) const
{
	unsigned stackDiff = m_context.baseToCurrentStackOffset(m_baseStackOffset) - m_size + 1;
	if (stackDiff > 16)
		BOOST_THROW_EXCEPTION(
			StackTooDeepError() <<
			errinfo_sourceLocation(_location) <<
			util::errinfo_comment(util::stackTooDeepString)
		);
	else if (stackDiff > 0)
		for (unsigned i = 0; i < m_size; ++i)
			m_context << swapInstruction(stackDiff) << Instruction::POP;
	if (!_move)
		retrieveValue(_location);
}

void StackVariable::setToZero(SourceLocation const& _location, bool) const
{
	CompilerUtils(m_context).pushZeroValue(*m_dataType);
	storeValue(*m_dataType, _location, true);
}

MemoryItem::MemoryItem(CompilerContext& _compilerContext, Type const& _type, bool _padded):
	LValue(_compilerContext, &_type),
	m_padded(_padded)
{
}

void MemoryItem::retrieveValue(SourceLocation const&, bool _remove) const
{
	if (m_dataType->isValueType())
	{
		if (!_remove)
			m_context << Instruction::DUP1;
		CompilerUtils(m_context).loadFromMemoryDynamic(*m_dataType, false, m_padded, false);
	}
	else
		m_context << Instruction::MLOAD;
}

void MemoryItem::storeValue(Type const& _sourceType, SourceLocation const&, bool _move) const
{
	CompilerUtils utils(m_context);
	if (m_dataType->isValueType())
	{
		solAssert(_sourceType.isValueType(), "");
		utils.moveIntoStack(_sourceType.sizeOnStack());
		utils.convertType(_sourceType, *m_dataType, true);
		if (!_move)
		{
			utils.moveToStackTop(m_dataType->sizeOnStack());
			utils.copyToStackTop(1 + m_dataType->sizeOnStack(), m_dataType->sizeOnStack());
		}
		if (!m_padded)
		{
			solAssert(m_dataType->calldataEncodedSize(false) == 1, "Invalid non-padded type.");
			solAssert(m_dataType->category() != Type::Category::UserDefinedValueType, "");
			if (m_dataType->category() == Type::Category::FixedBytes)
				m_context << u256(0) << Instruction::BYTE;
			m_context << Instruction::SWAP1 << Instruction::MSTORE8;
		}
		else
		{
			utils.storeInMemoryDynamic(*m_dataType, m_padded);
			m_context << Instruction::POP;
		}
	}
	else
	{
		solUnimplementedAssert(_sourceType == *m_dataType, "Conversion not implemented for assignment to memory.");

		solAssert(m_dataType->sizeOnStack() == 1, "");
		if (!_move)
			m_context << Instruction::DUP2 << Instruction::SWAP1;
		// stack: [value] value lvalue
		// only store the reference
		m_context << Instruction::MSTORE;
	}
}

void MemoryItem::setToZero(SourceLocation const&, bool _removeReference) const
{
	CompilerUtils utils(m_context);
	solAssert(_removeReference, "");
	utils.pushZeroValue(*m_dataType);
	utils.storeInMemoryDynamic(*m_dataType, m_padded);
	m_context << Instruction::POP;
}


ImmutableItem::ImmutableItem(CompilerContext& _compilerContext, VariableDeclaration const& _variable):
	LValue(_compilerContext, _variable.annotation().type), m_variable(_variable)
{
	solAssert(_variable.immutable(), "");
}

void ImmutableItem::retrieveValue(SourceLocation const&, bool) const
{
	solUnimplementedAssert(m_dataType->isValueType());

	if (m_context.runtimeContext())
		CompilerUtils(m_context).loadFromMemory(
			static_cast<unsigned>(m_context.immutableMemoryOffset(m_variable)),
			*m_dataType,
			false,
			true
		);
	else
		for (auto&& slotName: m_context.immutableVariableSlotNames(m_variable))
			m_context.appendImmutable(slotName);
}

void ImmutableItem::storeValue(Type const& _sourceType, SourceLocation const&, bool _move) const
{
	CompilerUtils utils(m_context);
	solUnimplementedAssert(m_dataType->isValueType());
	solAssert(_sourceType.isValueType(), "");

	utils.convertType(_sourceType, *m_dataType, true);
	m_context << m_context.immutableMemoryOffset(m_variable);
	if (_move)
		utils.moveIntoStack(m_dataType->sizeOnStack());
	else
		utils.copyToStackTop(m_dataType->sizeOnStack() + 1, m_dataType->sizeOnStack());
	utils.storeInMemoryDynamic(*m_dataType);
	m_context << Instruction::POP;
}

void ImmutableItem::setToZero(SourceLocation const&, bool _removeReference) const
{
	CompilerUtils utils(m_context);
	solUnimplementedAssert(m_dataType->isValueType());
	solAssert(_removeReference);

	m_context << m_context.immutableMemoryOffset(m_variable);
	utils.pushZeroValue(*m_dataType);
	utils.storeInMemoryDynamic(*m_dataType);
	m_context << Instruction::POP;
}

StorageByteArrayElement::StorageByteArrayElement(CompilerContext& _compilerContext):
	LValue(_compilerContext, TypeProvider::byte())
{
}

void StorageByteArrayElement::retrieveValue(SourceLocation const&, bool _remove) const
{
	// stack: ref byte_number
	if (_remove)
		m_context << Instruction::SWAP1 << Instruction::SLOAD
			<< Instruction::SWAP1 << Instruction::BYTE;
	else
		m_context << Instruction::DUP2 << Instruction::SLOAD
			<< Instruction::DUP2 << Instruction::BYTE;
	m_context << (u256(1) << (256 - 8)) << Instruction::MUL;
}

void StorageByteArrayElement::storeValue(Type const&, SourceLocation const&, bool _move) const
{
	// stack: value ref byte_number
	m_context << u256(31) << Instruction::SUB << u256(0x100) << Instruction::EXP;
	// stack: value ref (1<<(8*(31-byte_number)))
	m_context << Instruction::DUP2 << Instruction::SLOAD;
	// stack: value ref (1<<(8*(31-byte_number))) old_full_value
	// clear byte in old value
	m_context << Instruction::DUP2 << u256(0xff) << Instruction::MUL
		<< Instruction::NOT << Instruction::AND;
	// stack: value ref (1<<(32-byte_number)) old_full_value_with_cleared_byte
	m_context << Instruction::SWAP1;
	m_context << (u256(1) << (256 - 8)) << Instruction::DUP5 << Instruction::DIV
		<< Instruction::MUL << Instruction::OR;
	// stack: value ref new_full_value
	m_context << Instruction::SWAP1 << Instruction::SSTORE;
	if (_move)
		m_context << Instruction::POP;
}

void StorageByteArrayElement::setToZero(SourceLocation const&, bool _removeReference) const
{
	// stack: ref byte_number
	solAssert(_removeReference, "");
	m_context << u256(31) << Instruction::SUB << u256(0x100) << Instruction::EXP;
	// stack: ref (1<<(8*(31-byte_number)))
	m_context << Instruction::DUP2 << Instruction::SLOAD;
	// stack: ref (1<<(8*(31-byte_number))) old_full_value
	// clear byte in old value
	m_context << Instruction::SWAP1 << u256(0xff) << Instruction::MUL;
	m_context << Instruction::NOT << Instruction::AND;
	// stack: ref old_full_value_with_cleared_byte
	m_context << Instruction::SWAP1 << Instruction::SSTORE;
}

TupleObject::TupleObject(
	CompilerContext& _compilerContext,
	std::vector<std::unique_ptr<LValue>>&& _lvalues
):
	LValue(_compilerContext), m_lvalues(std::move(_lvalues))
{
}

unsigned TupleObject::sizeOnStack() const
{
	unsigned size = 0;
	for (auto const& lv: m_lvalues)
		if (lv)
			size += lv->sizeOnStack();
	return size;
}

void TupleObject::retrieveValue(SourceLocation const&, bool) const
{
	solAssert(false, "Tried to retrieve value of tuple.");
}

void TupleObject::storeValue(Type const& _sourceType, SourceLocation const& _location, bool) const
{
	// values are below the lvalue references
	unsigned valuePos = sizeOnStack();
	TypePointers const& valueTypes = dynamic_cast<TupleType const&>(_sourceType).components();
	solAssert(valueTypes.size() == m_lvalues.size(), "");
	// valuePos .... refPos ...
	// We will assign from right to left to optimize stack layout.
	for (size_t i = 0; i < m_lvalues.size(); ++i)
	{
		std::unique_ptr<LValue> const& lvalue = m_lvalues[m_lvalues.size() - i - 1];
		Type const* valType = valueTypes[valueTypes.size() - i - 1];
		unsigned stackHeight = m_context.stackHeight();
		solAssert(!valType == !lvalue, "");
		if (!lvalue)
			continue;
		valuePos += valType->sizeOnStack();
		// copy value to top
		CompilerUtils(m_context).copyToStackTop(valuePos, valType->sizeOnStack());
		// move lvalue ref above value
		CompilerUtils(m_context).moveToStackTop(valType->sizeOnStack(), lvalue->sizeOnStack());
		lvalue->storeValue(*valType, _location, true);
		valuePos += m_context.stackHeight() - stackHeight;
	}
	// As the type of an assignment to a tuple type is the empty tuple, we always move.
	CompilerUtils(m_context).popStackElement(_sourceType);
}

void TupleObject::setToZero(SourceLocation const&, bool) const
{
	solAssert(false, "Tried to delete tuple.");
}
