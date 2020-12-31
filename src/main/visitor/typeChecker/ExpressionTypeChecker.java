package main.visitor.typeChecker;

import main.ast.nodes.declaration.classDec.ClassDeclaration;
import main.ast.nodes.declaration.classDec.classMembersDec.FieldDeclaration;
import main.ast.nodes.declaration.classDec.classMembersDec.MethodDeclaration;
import main.ast.nodes.declaration.variableDec.VarDeclaration;
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
import main.ast.types.list.ListNameType;
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

import java.util.ArrayList;


public class ExpressionTypeChecker extends Visitor<Type> {
    private final Graph<String> classHierarchy;
    public String currentClassName;
    public String previousClassName;
    public String currentMethodName;
    public boolean in_methodCallStatement = false;
    public boolean in_method = false;

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

    private boolean areParametersTypeCorrespondence(ArrayList<Type> formalTypes , ArrayList<Type> actualTypes )
    {
        boolean x;
        if (actualTypes.size() != formalTypes.size())
            x = false;
        else {
            x = true;
            for (int i = 0; i < actualTypes.size(); i++) {
                Type actualArgType = actualTypes.get(i);
                Type formalArgType = formalTypes.get(i);
               x = isFirstSubTypeOfSecond(
                        actualArgType, formalArgType
                );
                if (!x)
                    break;
            };
        }
        return x;
    }

    public boolean isFirstSubTypeOfSecond(Type first, Type second)
    {
        //System.out.println(first.toString() + "  " + second.toString());
        if (!second.equals(first)) {
            if (second instanceof ClassType && first instanceof ClassType) {
               return classHierarchy.isSecondNodeAncestorOf(first.toString()
                        , second.toString());
            }
        }
        if(first instanceof IntType || first instanceof NoType){
            return !(second instanceof IntType) && !(second instanceof NoType);
        }
        else if(first instanceof BoolType || first instanceof NoType){
            return !(second instanceof BoolType) && !(second instanceof NoType);
        }
        else if(first instanceof ListType || first instanceof NoType){
            return !(second instanceof ListType) && !(second instanceof NoType);
        }
        else if(first instanceof FptrType || first instanceof NoType){
            return !(second instanceof FptrType) && !(second instanceof NoType);
        }
        return true;
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
        //System.out.println(e.toString() + "   " + i.getName() + "   " + objectOrListMemberAccess.getLine());
        Type t1 = e.accept(this);
        //Type t2 = i.accept(this);
        if(!(t1 instanceof ClassType) && !(t1 instanceof ListType)){
            objectOrListMemberAccess.addError(new MemberAccessOnNoneObjOrListType(objectOrListMemberAccess.getLine()));
            return new NoType();
        }

        String className = currentClassName;
        if(t1 instanceof ClassType){
            try{
                ClassSymbolTableItem currentClass = (ClassSymbolTableItem) SymbolTable.root
                        .getItem(ClassSymbolTableItem.START_KEY + ((ClassType) t1).getClassName().getName(), true);
                ArrayList<FieldDeclaration> fieldDeclarations = currentClass.getClassDeclaration().getFields();
                ArrayList<MethodDeclaration> methodDeclarations = currentClass.getClassDeclaration().getMethods();
                for (FieldDeclaration fieldDeclaration : fieldDeclarations) {
                    if (i.getName().equals(fieldDeclaration.getVarDeclaration().getVarName().getName())) {
                        return fieldDeclaration.getVarDeclaration().getType();
                    }
                }
                try {
                    MethodSymbolTableItem calledMethod = (MethodSymbolTableItem) currentClass.getClassSymbolTable()
                            .getItem(MethodSymbolTableItem.START_KEY + i.getName(), true);
                    return new FptrType(calledMethod.getArgTypes(), calledMethod.getReturnType());
                }catch (ItemNotFoundException MethodNotFound){
                    objectOrListMemberAccess.addError(new MemberNotAvailableInClass(objectOrListMemberAccess.getLine(),
                            i.getName(), className));
                    return new NoType();
                }
            }catch (ItemNotFoundException classNotFound){
                System.out.println("goh to compiler");
            }
        }
        if(t1 instanceof ListType){
            ArrayList<ListNameType> listNameTypes = ((ListType) t1).getElementsTypes();
            for(ListNameType l : listNameTypes){
                if(l.getName().getName().equals(i.getName())) {
                    return l.getType();
                }
            }
            objectOrListMemberAccess.addError(new ListMemberNotFound(objectOrListMemberAccess.getLine(), i.getName()));
            return new NoType();
        }
        return new NoType();
    }

    @Override
    public Type visit(Identifier identifier) {
        String className = currentClassName;
        String methodName = currentMethodName;
        try {
            ClassSymbolTableItem currentClass = (ClassSymbolTableItem) SymbolTable.root
                    .getItem(ClassSymbolTableItem.START_KEY + className, true);
            if(in_method) {
                MethodSymbolTableItem currentMethod = (MethodSymbolTableItem) currentClass.getClassSymbolTable()
                        .getItem(MethodSymbolTableItem.START_KEY + methodName, true);
                ArrayList<VarDeclaration> x = currentMethod.getMethodDeclaration().getLocalVars();
                ArrayList<VarDeclaration> y = currentMethod.getMethodDeclaration().getArgs();
                for (VarDeclaration j : x) {
                    if (identifier.getName().equals(j.getVarName().getName())) {
                        return j.getType();
                    }
                }
                for (VarDeclaration j : y) {
                    if (identifier.getName().equals(j.getVarName().getName())) {
                        return j.getType();
                    }
                }
                identifier.addError(new VarNotDeclared(identifier.getLine(), identifier.getName()));
                return new NoType();
            }
        } catch (ItemNotFoundException classNotFound) {
            identifier.addError( new ClassNotDeclared(identifier.getLine(), className));
            return new NoType();
        }
        return new NoType();
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
        if(t1 instanceof ListType){
            boolean flag = false;
            ArrayList<ListNameType> l = ((ListType) t1).getElementsTypes();
            Type t = l.get(0).getType();
            for(ListNameType x : l){
                if(!(t.equals(x.getType()))){
                    flag = true;
                    break;
                }
            }
            if(flag){
                if(!(e2 instanceof IntValue)){
                    listAccessByIndex.addError(new CantUseExprAsIndexOfMultiTypeList(listAccessByIndex.getLine()));
                    return new NoType();
                }
            }
            return t;
        }
        return null;
    }

    @Override
    public Type visit(MethodCall methodCall) {
        Type instanceType = methodCall.getInstance().accept(this);
        if(!(instanceType instanceof FptrType)){
            methodCall.addError(new CallOnNoneFptrType(methodCall.getLine()));
            return new NoType();
        }
        else {
            if (!in_methodCallStatement) {
                boolean x = false , y = false;
                Type fptrType = ((FptrType) instanceType).getReturnType();
                if(fptrType instanceof NullType){
                    methodCall.addError(new CantUseValueOfVoidMethod(methodCall.getLine()));
                    x = true;
                }
                ArrayList<Expression> actualParams = methodCall.getArgs();
                ArrayList<Type> actualParamsTypes = new ArrayList<>();
                for (Expression actualParam : actualParams) {
                    Type t = actualParam.accept(this);
                    actualParamsTypes.add(t);
                }
                ArrayList<Type> formalParamsTypes = ((FptrType) instanceType).getArgumentsTypes();
                if (!areParametersTypeCorrespondence(formalParamsTypes, actualParamsTypes)) {
                    methodCall.addError(new MethodCallNotMatchDefinition(methodCall.getLine()));
                    y = true;
                }
                if (x || y) {
                    return new NoType();
                }
                return fptrType;
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

        try {
            ClassSymbolTableItem currentClass = (ClassSymbolTableItem) SymbolTable.root
                    .getItem(ClassSymbolTableItem.START_KEY + className, true);
            try {
                MethodSymbolTableItem calledMethod = (MethodSymbolTableItem) currentClass.getClassSymbolTable()
                        .getItem(MethodSymbolTableItem.START_KEY + className, false);

                ArrayList<Expression> actualParams = newClassInstance.getArgs();
                ArrayList<Type> actualParamsTypes = new ArrayList<>();
                for(Expression actualParam : actualParams){
                    Type t = actualParam.accept(this);
                    actualParamsTypes.add(t);
                }
                ArrayList<Type> formalParamsTypes = calledMethod.getArgTypes();
                if (!areParametersTypeCorrespondence(formalParamsTypes,actualParamsTypes)){
                    newClassInstance.addError(new ConstructorArgsNotMatchDefinition(newClassInstance));
                }

            } catch (ItemNotFoundException methodNotFound) {
                ArrayList<Expression> actualParams = newClassInstance.getArgs();
                if(!actualParams.isEmpty()) {
                    newClassInstance.addError(new ConstructorArgsNotMatchDefinition(newClassInstance));
                    return new NoType();
                }
            }
        } catch (ItemNotFoundException classNotFound) {
            newClassInstance.addError( new ClassNotDeclared(newClassInstance.getLine(), className));
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
