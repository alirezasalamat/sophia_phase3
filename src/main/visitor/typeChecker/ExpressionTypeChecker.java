package main.visitor.typeChecker;

import main.ast.nodes.declaration.classDec.ClassDeclaration;
import main.ast.nodes.expression.*;
import main.ast.nodes.expression.values.ListValue;
import main.ast.nodes.expression.values.NullValue;
import main.ast.nodes.expression.values.primitive.BoolValue;
import main.ast.nodes.expression.values.primitive.IntValue;
import main.ast.nodes.expression.values.primitive.StringValue;
import main.ast.nodes.expression.operators.*;
import main.ast.types.NoType;
import main.ast.types.NullType;
import main.ast.types.Type;
import main.ast.types.functionPointer.FptrType;
import main.ast.types.list.ListType;
import main.ast.types.single.BoolType;
import main.ast.types.single.ClassType;
import main.ast.types.single.IntType;
import main.ast.types.single.StringType;
import main.compileErrorException.typeErrors.*;
import main.symbolTable.exceptions.ItemNotFoundException;
import main.symbolTable.items.*;
import main.symbolTable.utils.graph.Graph;
import main.visitor.Visitor;
import main.symbolTable.SymbolTable;


public class ExpressionTypeChecker extends Visitor<Type> {
    private final Graph<String> classHierarchy;
    public String currentClassName;
    private String currentMethodName;

    public ExpressionTypeChecker(Graph<String> classHierarchy) {
        this.classHierarchy = classHierarchy;
    }

    private SymbolTable getCurrentClassSymbolTable() {
        try {
            ClassSymbolTableItem classSymbolTableItem = (ClassSymbolTableItem)
                    SymbolTable.root.getItem(ClassSymbolTableItem.START_KEY + this.currentClassName, true);
            return classSymbolTableItem.getClassSymbolTable();
        } catch (ItemNotFoundException ignored) {
            return null;
        }
    }

    private boolean isLValue(Expression exp){
        return exp instanceof Identifier || exp instanceof ListAccessByIndex ||
                exp instanceof ObjectOrListMemberAccess;
    }


    @Override
    public Type visit(BinaryExpression binaryExpression) {
        if (binaryExpression == null)
            return new NullType();

        Expression left_exp = binaryExpression.getFirstOperand();
        Expression right_exp = binaryExpression.getSecondOperand();
        BinaryOperator binaryOperator = binaryExpression.getBinaryOperator();
        Type t1 = left_exp.accept(this);
        Type t2 = right_exp.accept(this);

        // operator add   sub  mult  div   mod
        if (binaryOperator.equals(BinaryOperator.add) || binaryOperator.equals(BinaryOperator.sub) ||
                binaryOperator.equals(BinaryOperator.mult) || binaryOperator.equals(BinaryOperator.div) ||
                binaryOperator.equals(BinaryOperator.mod)) {
            if ((t1 instanceof IntType || t1 instanceof NoType) &&
                    (t2 instanceof IntType || t2 instanceof NoType)) {
                return new IntType();
            }
            else {
                int line = binaryExpression.getLine();
                binaryExpression.addError(new UnsupportedOperandType(line, binaryOperator.toString()));
                return new NoType();
            }
        }

        // op > <
        else if (binaryOperator.equals(BinaryOperator.lt) || binaryOperator.equals(BinaryOperator.gt)) {
            if ((t1 instanceof IntType || t1 instanceof NoType) &&
                    (t2 instanceof IntType || t2 instanceof NoType)) {
                return new BoolType();
            }
            else {
                int line = binaryExpression.getLine();
                binaryExpression.addError(new UnsupportedOperandType(line, binaryOperator.toString()));
                return new NoType();
            }
        }

        // operator and or
        else if (binaryOperator.equals(BinaryOperator.and) ||  binaryOperator.equals(BinaryOperator.or)) {
            if ((t1 instanceof BoolType || t2 instanceof NoType) &&
                    (t2 instanceof BoolType || t2 instanceof NoType)) {
                return new BoolType();
            }
            else {
                int line = binaryExpression.getLine();
                binaryExpression.addError(new UnsupportedOperandType(line, binaryOperator.toString()));
                return new NoType();
            }
        }

        // op == !=
        else if (binaryOperator.equals(BinaryOperator.eq) || binaryOperator.equals(BinaryOperator.neq)) {
            if ((t1 instanceof IntType || t1 instanceof NoType) &&
                    (t2 instanceof IntType || t2 instanceof NoType)) {
                return new BoolType();
            } else if ((t1 instanceof BoolType || t1 instanceof NoType) &&
                    (t2 instanceof BoolType || t2 instanceof NoType)) {
                return new BoolType();
            } else if ((t1 instanceof StringType || t1 instanceof NoType) &&
                    (t2 instanceof StringType || t2 instanceof NoType)) {
                return new BoolType();
            } else if ((t1 instanceof ClassType || t1 instanceof NoType || (t1 instanceof NullType && t2 instanceof ClassType)) &&
                    (t2 instanceof ClassType || t2 instanceof NoType || (t2 instanceof NullType && t1 instanceof ClassType))) {
                return new BoolType();
            } else if ((t1 instanceof FptrType || t1 instanceof NoType || (t1 instanceof NullType && t2 instanceof FptrType)) &&
                    (t2 instanceof FptrType || t2 instanceof NoType || (t2 instanceof NullType && t1 instanceof FptrType))) {
                return new BoolType();
            }
            else{
                int line = binaryExpression.getLine();
                binaryExpression.addError(new UnsupportedOperandType(line, binaryOperator.toString()));
                return new NoType();
            }
        }
        return new NoType();
    }

    @Override
    public Type visit(UnaryExpression unaryExpression) {
        if (unaryExpression == null)
            return new NullType();
        Expression exp = unaryExpression.getOperand();
        UnaryOperator unaryOperator = unaryExpression.getOperator();
        Type t = exp.accept(this);
        if(unaryOperator.equals(UnaryOperator.postdec) || unaryOperator.equals(UnaryOperator.postinc)
                || unaryOperator.equals(UnaryOperator.predec) || unaryOperator.equals(UnaryOperator.preinc)
                || unaryOperator.equals(UnaryOperator.minus)){
            if(!isLValue(exp)){
                unaryExpression.addError(new LeftSideNotLvalue(unaryExpression.getLine()));
            }
            if(t instanceof IntType || t instanceof NoType){
                return new IntType();
            }
            else{
                int line = unaryExpression.getLine();
                unaryExpression.addError(new UnsupportedOperandType(line, unaryOperator.toString()));
                return new NoType();
            }
        }
        else if(unaryOperator.equals(UnaryOperator.not)){
            if(t instanceof BoolType || t instanceof NoType){
                return new BoolType();
            }
            else{
                int line = unaryExpression.getLine();
                unaryExpression.addError(new UnsupportedOperandType(line, unaryOperator.toString()));
                return new NoType();
            }

        }
        return new NoType();
    }

    @Override
    public Type visit(ObjectOrListMemberAccess objectOrListMemberAccess) {
        Expression e = objectOrListMemberAccess.getInstance();
        Identifier i = objectOrListMemberAccess.getMemberName();
        Type t1 = e.accept(this);
        Type t2 = i.accept(this);
        if(!(t1 instanceof ClassType) && !(t1 instanceof ListType)){
            objectOrListMemberAccess.addError(new MemberAccessOnNoneObjOrListType(objectOrListMemberAccess.getLine()));
            return new NoType();
        }
        return null;
    }

    @Override
    public Type visit(Identifier identifier) {
        try {
            SymbolTable xx = SymbolTable.top;
            VarSymbolTableItem xxx = ((VarSymbolTableItem) SymbolTable.top.get(VarSymbolTableItem.var_modifier + identifier.getName()));
            Type x4 = ((VarSymbolTableItem) SymbolTable.top().get(VarSymbolTableItem.var_modifier + identifier.getName()))
                    .getType();
            return ((VarSymbolTableItem) SymbolTable.top().get(VarSymbolTableItem.var_modifier + identifier.getName()))
                    .getType();
        }
    }

    @Override
    public Type visit(ListAccessByIndex listAccessByIndex) {
        Expression e1 = listAccessByIndex.getInstance();
        Expression e2 = listAccessByIndex.getIndex();
        Type t1 = e1.accept(this);
        Type t2 = e2.accept(this);
        if(!(t1 instanceof ListType)){
            listAccessByIndex.addError(new ListAccessByIndexOnNoneList(listAccessByIndex.getLine()));
            return new NoType();
        }
        if(!(t2 instanceof IntType)){
            listAccessByIndex.addError(new ListIndexNotInt(listAccessByIndex.getLine()));
            return new NoType();
        }
        return null;
    }

    @Override
    public Type visit(MethodCall methodCall) {
        Type instanceType = methodCall.getInstance().accept(this);
        if (instanceType instanceof ClassType) {
            String className = ((ClassType) instanceType).getClassName().getName();
            try {
                ClassSymbolTableItem currentClass = (ClassSymbolTableItem) SymbolTable.root
                        .getItem(ClassSymbolTableItem.START_KEY + className, true);
                try {
                    MethodSymbolTableItem calledMethod = (MethodSymbolTableItem) currentClass.getClassSymbolTable()
                            .getItem(MethodSymbolTableItem.START_KEY + methodCall.);
                    List<Type> actualParamsTypes = methodCall.getArgs().stream().map(a -> a.accept(this))
                            .collect(Collectors.toList());
                    List<Type> formalParamsTypes = calledMethod.getArgumentsTypes();
                    if (!areParametersTypeCorrespondence(formalParamsTypes,actualParamsTypes))
                        throw new ItemNotFoundException();
                    if (calledMethod.getAccessModifier() == AccessModifier.ACCESS_MODIFIER_PRIVATE
                            && !(methodCall.getInstance() instanceof Self))
                        methodCall.addError(
                                new IllegalAccessToMethod( calledMethod.getName() , currentClass.getName(), methodCall.line , methodCall.col) );
                    return calledMethod.getReturnType();
                } catch (ItemNotFoundException methodNotFound) {
                    methodCall.addError( new MethodNotDeclared(methodCall.getMethodName().getName() , className , methodCall.line , methodCall.col ));
                    return new Undefined();
                }
            } catch (ItemNotFoundException classNotFound) {
                methodCall.addError( new ClassNotDeclaredException(className, methodCall.line , methodCall.col));
                return new Undefined();
            }
        }
        return null;
    }

    @Override
    public Type visit(NewClassInstance newClassInstance) {
        String className = newClassInstance.getClassType().getClassName().getName();
        if( !classHierarchy.doesGraphContainNode(className)) {
            newClassInstance.addError(new ClassNotDeclared(newClassInstance.getLine(), className));
            return new NoType();
        }
        return newClassInstance.getClassType();
    }

    @Override
    public Type visit(ThisClass thisClass) {
        try {
            ClassSymbolTableItem classSymbolTableItem = (ClassSymbolTableItem)
                    SymbolTable.root.getItem(ClassSymbolTableItem.START_KEY + this.currentClassName, true);
            return new ClassType(classSymbolTableItem.getClassDeclaration().getClassName());
        } catch (ItemNotFoundException ignored) {
            return null;
        }
    }

    @Override
    public Type visit(ListValue listValue) {
        return new ListType();
    }

    @Override
    public Type visit(NullValue nullValue) {
        return new NullType();
    }

    @Override
    public Type visit(IntValue intValue) {
        return new IntType();
    }

    @Override
    public Type visit(BoolValue boolValue) {
        return new BoolType();
    }

    @Override
    public Type visit(StringValue stringValue) {
        return new StringType();
    }
}