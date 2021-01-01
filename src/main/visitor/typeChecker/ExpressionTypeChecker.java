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

import javax.print.attribute.standard.NumberUp;
import java.util.ArrayList;


public class ExpressionTypeChecker extends Visitor<Type> {
    private final Graph<String> classHierarchy;
    public String currentClassName;
    public String previousClassName;
    public String currentMethodName;
    public boolean in_methodCallStatement = false;
    public boolean in_method = false;
    public boolean is_lvalue = true;

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

                x = isFirstSubTypeOfSecond(actualArgType, formalArgType);
                if (!x)
                    break;
            };
        }
        return x;
    }

    public boolean isFirstSubTypeOfSecond(Type first, Type second)
    {
        //System.out.println(first.toString() + "    " + second.toString());
        if(first instanceof NoType)
            return true;
        if(first instanceof NullType && (second instanceof ClassType || second instanceof FptrType)){
            return true;
        }

        if(first instanceof ClassType && second instanceof ClassType){
            return classHierarchy.isSecondNodeAncestorOf(((ClassType) first).getClassName().getName(),
                    ((ClassType) second).getClassName().getName());
        }

        else if(first instanceof ListType) {
            ArrayList<ListNameType> listNameTypes1 = ((ListType) first).getElementsTypes();
            if (second instanceof ListType) {
                ArrayList<ListNameType> listNameTypes2 = ((ListType) second).getElementsTypes();
                if(listNameTypes1.size() == listNameTypes2.size()){
                    for(int i = 0; i < listNameTypes1.size(); i++){
                        if(!isFirstSubTypeOfSecond(listNameTypes1.get(i).getType(), listNameTypes2.get(i).getType())){

                            return false;
                        }
                    }
                }
                else {
                    return false;
                }
            }
            else {
                return false;
            }
        }
        else if(first instanceof FptrType){
            if(second instanceof FptrType){
                Type t1 = ((FptrType) first).getReturnType();
                Type t2 = ((FptrType) second).getReturnType();
                ArrayList<Type> types1 = ((FptrType) first).getArgumentsTypes();
                ArrayList<Type> types2 = ((FptrType) second).getArgumentsTypes();
                if (isFirstSubTypeOfSecond(t2, t1)) {
                    if(types1.size() == types2.size()){
                        for(int i = 0; i < types1.size(); i++){
                            if(!isFirstSubTypeOfSecond(types1.get(i),types2.get(i))){
                                return false;
                            }
                        }
                    }
                    else
                        return false;
                }
                else
                    return false;
            }
            else
                return false;
        }
        if(first.toString().equals(second.toString())){
            return true;
        }
        else{return false;}
        //return true;
    }


    @Override
    public Type visit(BinaryExpression binaryExpression) {
        if (binaryExpression == null)
            return new NullType();

        Expression left_exp = binaryExpression.getFirstOperand();
        Expression right_exp = binaryExpression.getSecondOperand();
        BinaryOperator binaryOperator = binaryExpression.getBinaryOperator();
        Type t2 = right_exp.accept(this);
        Type t1 = left_exp.accept(this);

        if(t1 instanceof NoType && t2 instanceof NoType){
            is_lvalue = false;
            return new NoType();
        }

        //System.out.println("qqqqqqqqqqqq    " + t1.toString() + "   " + t2.toString() + "    " + binaryExpression.getLine());
        // operator add   sub  mult  div   mod
        if (binaryOperator.equals(BinaryOperator.add) || binaryOperator.equals(BinaryOperator.sub) ||
                binaryOperator.equals(BinaryOperator.mult) || binaryOperator.equals(BinaryOperator.div) ||
                binaryOperator.equals(BinaryOperator.mod) || binaryOperator.equals(BinaryOperator.lt) ||
                binaryOperator.equals(BinaryOperator.gt)) {
            if (!(t1 instanceof IntType || t1 instanceof NoType) ||
                    !(t2 instanceof IntType || t2 instanceof NoType)) {
                binaryExpression.addError(new UnsupportedOperandType(binaryExpression.getLine(), binaryOperator.toString()));
                is_lvalue = false;
                return new NoType();

            }
        }

        // operator and or
        else if (binaryOperator.equals(BinaryOperator.and) ||  binaryOperator.equals(BinaryOperator.or)) {
            if (!(t1 instanceof BoolType || t1 instanceof NoType) ||
                    !(t2 instanceof BoolType || t2 instanceof NoType)) {
                binaryExpression.addError(new UnsupportedOperandType(binaryExpression.getLine(), binaryOperator.toString()));
                is_lvalue = false;
                return new NoType();

            }
        }

        // op == !=
        else if (binaryOperator.equals(BinaryOperator.eq) || binaryOperator.equals(BinaryOperator.neq)) {
            if (t1 instanceof ListType || t2 instanceof ListType) {
                binaryExpression.addError(new UnsupportedOperandType(binaryExpression.getLine(), binaryOperator.toString()));
                is_lvalue = false;
                return new NoType();
            }
            else if (t1 instanceof ClassType || t2 instanceof ClassType){
                if(!t1.toString().equals(t2.toString()) && !(t1 instanceof NullType) && !(t2 instanceof NullType)){
                    binaryExpression.addError(new UnsupportedOperandType(binaryExpression.getLine(), binaryOperator.toString()));
                    is_lvalue = false;
                    return new NoType();
                }
            }
            else if ((t1 instanceof FptrType || t2 instanceof FptrType)){
                if((!isFirstSubTypeOfSecond(t1, t2) || !isFirstSubTypeOfSecond(t2, t1))
                    &&!(t1 instanceof NullType) && !(t2 instanceof NullType)){
                    //System.out.println("ccccccccccccccccccc    " + binaryExpression.getLine());
                    binaryExpression.addError(new UnsupportedOperandType(binaryExpression.getLine(), binaryOperator.toString()));
                    is_lvalue = false;
                    return new NoType();
                }
            }
            else if(!t1.toString().equals(t2.toString()) && !(t1 instanceof NoType || t2 instanceof NoType)){
                //System.out.println("rrrrrrrrrrrr    " + binaryExpression.getLine());
                binaryExpression.addError(new UnsupportedOperandType(binaryExpression.getLine(), binaryOperator.toString()));
                is_lvalue = false;
                return new NoType();
            }
        }
        else if(binaryOperator.equals(BinaryOperator.assign)){
            if(!is_lvalue){
                binaryExpression.addError(new LeftSideNotLvalue(binaryExpression.getLine()));
                return new NoType();
            }
            if(!isFirstSubTypeOfSecond(t2, t1)){
                binaryExpression.addError(new UnsupportedOperandType(binaryExpression.getLine(), binaryOperator.toString()));
                is_lvalue = false;
                return new NoType();
            }
        }

        if(t1 instanceof NoType || t2 instanceof NoType){
            is_lvalue = false;
            return new NoType();
        }

        if (binaryOperator.equals(BinaryOperator.add) || binaryOperator.equals(BinaryOperator.sub) ||
                binaryOperator.equals(BinaryOperator.mult) || binaryOperator.equals(BinaryOperator.div) ||
                binaryOperator.equals(BinaryOperator.mod)) {
            is_lvalue = false;
            return new IntType();
        }

        if (binaryOperator.equals(BinaryOperator.lt) || binaryOperator.equals(BinaryOperator.gt)) {
            is_lvalue = false;
            return new BoolType();
        }

        // operator and or
        if (binaryOperator.equals(BinaryOperator.and) ||  binaryOperator.equals(BinaryOperator.or)) {
            is_lvalue = false;
            return new BoolType();
        }

        // op == !=
        if (binaryOperator.equals(BinaryOperator.eq) || binaryOperator.equals(BinaryOperator.neq)) {
            is_lvalue = false;
            return new BoolType();
        }

        return new NoType();
    }

    @Override
    public Type visit(UnaryExpression unaryExpression) {
        if (unaryExpression == null)
            return new NoType();
        Expression exp = unaryExpression.getOperand();
        UnaryOperator unaryOperator = unaryExpression.getOperator();
        Type t = exp.accept(this);
        //System.out.println("xxxxxxxxxxxxxxxxxx   " + is_lvalue + "     " + t.toString() + "     " + unaryExpression.getLine());
        boolean x = false , y = false;
//        if(t instanceof NoType){
//            return new NoType();
//        }
        if(unaryOperator.equals(UnaryOperator.postdec) || unaryOperator.equals(UnaryOperator.postinc)
                || unaryOperator.equals(UnaryOperator.predec) || unaryOperator.equals(UnaryOperator.preinc)){
            if(!is_lvalue){
                //System.out.println("xxxxxxxxxxxxxxxxxx   " + is_lvalue + "     " + exp.toString() + "     " + unaryExpression.getLine());
                unaryExpression.addError(new IncDecOperandNotLvalue(unaryExpression.getLine(), unaryOperator.toString()));
                x = true;
            }
            is_lvalue = false;
            if(!(t instanceof IntType) && !(t instanceof NoType)){
                unaryExpression.addError(new UnsupportedOperandType(unaryExpression.getLine(), unaryOperator.toString()));
                y = true;
            }
            if(x || y){
                return new NoType();
            }
            return new IntType();
        }
        else if(unaryOperator.equals(UnaryOperator.minus)){
            is_lvalue = false;
            if(!(t instanceof IntType)){
                unaryExpression.addError(new UnsupportedOperandType(unaryExpression.getLine(), unaryOperator.toString()));
                return new NoType();
            }
            return new IntType();
        }
        else if(unaryOperator.equals(UnaryOperator.not)){
            is_lvalue = false;
            //System.out.println("ccccccccccccccccccccc    " + unaryExpression.getLine());
            if(!(t instanceof BoolType)){
                unaryExpression.addError(new UnsupportedOperandType(unaryExpression.getLine(), unaryOperator.toString()));
                return new NoType();
            }
            return new BoolType();
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
        if(!(t1 instanceof ClassType) && !(t1 instanceof ListType) && !(t1 instanceof NoType)){
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

                try {
                    FieldSymbolTableItem calledField = (FieldSymbolTableItem) currentClass.getClassSymbolTable()
                            .getItem(FieldSymbolTableItem.START_KEY + i.getName(), true);
                    return calledField.getType();
                }catch (ItemNotFoundException MethodNotFound) {
                    try {
                        MethodSymbolTableItem calledMethod = (MethodSymbolTableItem) currentClass.getClassSymbolTable()
                                .getItem(MethodSymbolTableItem.START_KEY + i.getName(), true);
                        is_lvalue = false;
                        return new FptrType(calledMethod.getArgTypes(), calledMethod.getReturnType());

                    }catch (ItemNotFoundException MemberNotFound){
                        objectOrListMemberAccess.addError(new MemberNotAvailableInClass(objectOrListMemberAccess.getLine(),
                                i.getName(), currentClass.getClassDeclaration().getClassName().getName()));
                        return new NoType();
                    }
                }
            }catch (ItemNotFoundException classNotFound){
                System.out.println("error");
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
                try {
                    MethodSymbolTableItem currentMethod = (MethodSymbolTableItem) currentClass.getClassSymbolTable()
                            .getItem(MethodSymbolTableItem.START_KEY + methodName, true);
                    try {
                        LocalVariableSymbolTableItem local = (LocalVariableSymbolTableItem) currentMethod.getMethodSymbolTable()
                                .getItem(LocalVariableSymbolTableItem.START_KEY + identifier.getName(), true);
                        return local.getType();
                    } catch (ItemNotFoundException VariableNotFound) {
                        identifier.addError(new VarNotDeclared(identifier.getLine(), identifier.getName()));
                        return new NoType();
                    }
                }catch (ItemNotFoundException methodNotFound){
                    System.out.println("error in identifier");
                }
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
        boolean temp = is_lvalue;
        is_lvalue = true;
        Type t2 = e2.accept(this);
        is_lvalue = temp;
        boolean  y = false, z = false;
        //System.out.println("qqqqqqqqqqqq   "+ is_lvalue + "     " + listAccessByIndex.getLine());
        if(!(t2 instanceof IntType) && !(t2 instanceof NoType)){
            listAccessByIndex.addError(new ListIndexNotInt(listAccessByIndex.getLine()));
            y = true;
        }
        if(!(t1 instanceof ListType) && !(t1 instanceof NoType)){
            listAccessByIndex.addError(new ListAccessByIndexOnNoneList(listAccessByIndex.getLine()));
            return new NoType();
        }
        if(t1 instanceof ListType){
            boolean flag = false;
            ArrayList<ListNameType> l = ((ListType) t1).getElementsTypes();
            Type t = l.get(0).getType();
            for(ListNameType x : l){
                if(!(t.toString().equals(x.getType().toString()))){
                    flag = true;
                    break;
                }
            }
            if(flag){
                if(!(e2 instanceof IntValue)){
                    listAccessByIndex.addError(new CantUseExprAsIndexOfMultiTypeList(listAccessByIndex.getLine()));
                    return new NoType();
                }
                else{
                    return l.get(((IntValue) e2).getConstant()).getType() ;
                }
            }
            else{
                if(y){
                    return new NoType();
                }
                if(e2 instanceof IntValue){
                    if(((IntValue) e2).getConstant() < l.size()){
                        return l.get(((IntValue) e2).getConstant()).getType() ;
                    }
                    else {
                        return t;
                    }
                }
            }
        }
        return new NoType();
    }

    @Override
    public Type visit(MethodCall methodCall) {
        is_lvalue = false;
        Type instanceType = methodCall.getInstance().accept(this);
        if(!(instanceType instanceof FptrType)){
            if(instanceType instanceof NoType){
                return new NoType();
            }
            methodCall.addError(new CallOnNoneFptrType(methodCall.getLine()));
            return new NoType();
        }
        else {
            if (!in_methodCallStatement) {
                boolean x = false , y = false, temp;
                Type fptrType = ((FptrType) instanceType).getReturnType();
                if(fptrType instanceof NullType){
                    methodCall.addError(new CantUseValueOfVoidMethod(methodCall.getLine()));
                    x = true;
                }
                ArrayList<Expression> actualParams = methodCall.getArgs();
                ArrayList<Type> actualParamsTypes = new ArrayList<>();
                for (Expression actualParam : actualParams) {
                    temp = is_lvalue;
                    is_lvalue = true;
                    Type t = actualParam.accept(this);
                    is_lvalue = temp;
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
            else{
                boolean y = false;
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
                if (y) {
                    return new NoType();
                }
            }
        }
        return null;
    }

    @Override
    public Type visit(NewClassInstance newClassInstance) {
        is_lvalue = false;
        String className = newClassInstance.getClassType().getClassName().getName();
        try {
            ClassSymbolTableItem currentClass = (ClassSymbolTableItem) SymbolTable.root
                    .getItem(ClassSymbolTableItem.START_KEY + className, true);
            try {
                MethodSymbolTableItem calledMethod = (MethodSymbolTableItem) currentClass.getClassSymbolTable()
                        .getItem(MethodSymbolTableItem.START_KEY + className, true);

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
        //is_lvalue = false;
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
        is_lvalue = false;
        ArrayList<ListNameType> listNameTypes = new ArrayList<>();
        for(Expression exp : listValue.getElements()){
            Type t = exp.accept(this);
            listNameTypes.add(new ListNameType(t));
        }
        return new ListType(listNameTypes);
    }

    @Override
    public Type visit(NullValue nullValue) {
        is_lvalue = false;
        return new NullType();
    }

    @Override
    public Type visit(IntValue intValue) {
        is_lvalue = false;
        return new IntType();
    }

    @Override
    public Type visit(BoolValue boolValue) {
       is_lvalue = false;
        return new BoolType();
    }

    @Override
    public Type visit(StringValue stringValue) {
        is_lvalue = false;
        return new StringType();
    }
}
