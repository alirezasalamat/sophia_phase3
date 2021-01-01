package main.visitor.typeChecker;

import main.ast.nodes.Program;
import main.ast.nodes.declaration.classDec.ClassDeclaration;
import main.ast.nodes.declaration.classDec.classMembersDec.ConstructorDeclaration;
import main.ast.nodes.declaration.classDec.classMembersDec.FieldDeclaration;
import main.ast.nodes.declaration.classDec.classMembersDec.MethodDeclaration;
import main.ast.nodes.declaration.variableDec.VarDeclaration;
import main.ast.nodes.expression.*;
import main.ast.nodes.expression.operators.BinaryOperator;
import main.ast.nodes.expression.values.ListValue;
import main.ast.nodes.statement.*;
import main.ast.nodes.statement.loop.BreakStmt;
import main.ast.nodes.statement.loop.ContinueStmt;
import main.ast.nodes.statement.loop.ForStmt;
import main.ast.nodes.statement.loop.ForeachStmt;
import main.ast.types.single.BoolType;
import main.compileErrorException.typeErrors.*;
import main.symbolTable.SymbolTable;
import main.symbolTable.exceptions.ItemNotFoundException;
import main.symbolTable.items.*;
import main.symbolTable.utils.graph.Graph;
import main.visitor.Visitor;
import main.ast.types.NullType;
import main.ast.types.NoType;
import main.ast.types.Type;
import main.ast.types.functionPointer.FptrType;
import main.ast.types.single.*;
import main.ast.types.list.*;

import javax.lang.model.element.TypeElement;
import java.io.StringReader;
import java.util.ArrayList;

public class TypeChecker extends Visitor<Void> {
    private final Graph<String> classHierarchy;
    private final ExpressionTypeChecker expressionTypeChecker;
    private int in_for = 0;
    private boolean has_main = false;
    private String currentClassName;
    private String currentMethodName;
    boolean has_return = false;

    public TypeChecker(Graph<String> classHierarchy) {
        this.classHierarchy = classHierarchy;
        this.expressionTypeChecker = new ExpressionTypeChecker(classHierarchy);
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
    private SymbolTable getCurrentMethodSymbolTable() {
        try {
            MethodSymbolTableItem methodSymbolTableItem = (MethodSymbolTableItem)
                    SymbolTable.root.getItem(MethodSymbolTableItem.START_KEY + this.currentMethodName, true);
            return methodSymbolTableItem.getMethodSymbolTable();
        } catch (ItemNotFoundException ignored) {
            return null;
        }
    }

    private boolean isLValue(Expression exp){
        return (exp instanceof Identifier || exp instanceof ListAccessByIndex ||
                exp instanceof ObjectOrListMemberAccess);
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

    public void listChecker(Type type, VarDeclaration varDeclaration) {
        LocalVariableSymbolTableItem local;
        FieldSymbolTableItem field;
        //System.out.println(type.toString() + "    " + varDeclaration.getLine());
        try {
            ClassSymbolTableItem currentClass = (ClassSymbolTableItem) SymbolTable.root
                    .getItem(ClassSymbolTableItem.START_KEY + currentClassName, true);
            if(expressionTypeChecker.in_method){
                MethodSymbolTableItem method = (MethodSymbolTableItem) currentClass.getClassSymbolTable()
                        .getItem(MethodSymbolTableItem.START_KEY + currentMethodName, true);
                local = (LocalVariableSymbolTableItem) method.getMethodSymbolTable()
                        .getItem(LocalVariableSymbolTableItem.START_KEY + varDeclaration.getVarName().getName(), true);
                if (type instanceof ListType) {

                    if (((ListType) type).getElementsTypes().isEmpty()) {
                        varDeclaration.addError(new CannotHaveEmptyList(varDeclaration.getLine()));
                        local.setType(new NoType());
                    }

                    ArrayList<ListNameType> listNameTypes = ((ListType) type).getElementsTypes();
                    for (ListNameType l : listNameTypes) {
                        if(l.getType() instanceof ClassType) {
                            try {
                                ClassSymbolTableItem foundClass = (ClassSymbolTableItem) SymbolTable.root
                                        .getItem(ClassSymbolTableItem.START_KEY +
                                                ((ClassType) l.getType()).getClassName().getName(), true);
                            }catch (ItemNotFoundException classNotFound){
                                varDeclaration.addError(new ClassNotDeclared(varDeclaration.getLine(),
                                        ((ClassType) l.getType()).getClassName().getName()));
                                local.setType(new NoType());
                            }
                        }
                        listChecker(l.getType(), varDeclaration);
                    }
                    int i, j, k = 0;
                    for (i = 0; i < listNameTypes.size() - 1; i++) {
                        for (j = i + 1; j < listNameTypes.size(); j++) {
                            if (listNameTypes.get(i).getName().getName().equals(listNameTypes.get(j).getName().getName())
                                    && !listNameTypes.get(i).getName().getName().equals("") &&
                                    !listNameTypes.get(j).getName().getName().equals("")) {
                                varDeclaration.addError(new DuplicateListId(varDeclaration.getLine()));
                                local.setType(new NoType());
                                k = 1;
                                break;
                            }
                        }
                        if (k == 1)
                            break;
                    }
                } else if (type instanceof FptrType) {
                    Type t1 = ((FptrType) type).getReturnType();
                    if(t1 instanceof ClassType) {
                        try {
                            ClassSymbolTableItem foundClass = (ClassSymbolTableItem) SymbolTable.root
                                    .getItem(ClassSymbolTableItem.START_KEY +
                                            ((ClassType)  t1).getClassName().getName(), true);
                        }catch (ItemNotFoundException classNotFound){
                            varDeclaration.addError(new ClassNotDeclared(varDeclaration.getLine(),
                                    ((ClassType) t1).getClassName().getName()));
                            local.setType(new NoType());
                        }
                    }
                    listChecker(t1, varDeclaration);
                    ArrayList<Type> types = ((FptrType) type).getArgumentsTypes();
                    for (Type x : types) {
                        if(x instanceof ClassType) {
                            try {
                                ClassSymbolTableItem foundClass = (ClassSymbolTableItem) SymbolTable.root
                                        .getItem(ClassSymbolTableItem.START_KEY +
                                                ((ClassType)  x).getClassName().getName(), true);
                            }catch (ItemNotFoundException classNotFound){
                                varDeclaration.addError(new ClassNotDeclared(varDeclaration.getLine(),
                                        ((ClassType)  x).getClassName().getName()));
                                local.setType(new NoType());
                            }
                        }
                        listChecker(x, varDeclaration);
                    }
                }
            }
            else{
                field = (FieldSymbolTableItem) currentClass.getClassSymbolTable()
                        .getItem(FieldSymbolTableItem.START_KEY + varDeclaration.getVarName().getName(), true);
                if (type instanceof ListType) {
                    if (((ListType) type).getElementsTypes().isEmpty()) {
                        varDeclaration.addError(new CannotHaveEmptyList(varDeclaration.getLine()));
                        field.setType(new NoType());
                    }

                    ArrayList<ListNameType> listNameTypes = ((ListType) type).getElementsTypes();
                    for (ListNameType l : listNameTypes) {
                        if(l.getType() instanceof ClassType) {
                            try {
                                ClassSymbolTableItem foundClass = (ClassSymbolTableItem) SymbolTable.root
                                        .getItem(ClassSymbolTableItem.START_KEY +
                                                ((ClassType) l.getType()).getClassName().getName(), true);
                            }catch (ItemNotFoundException classNotFound){
                                varDeclaration.addError(new ClassNotDeclared(varDeclaration.getLine(),
                                        ((ClassType) l.getType()).getClassName().getName()));
                                field   .setType(new NoType());
                            }
                        }
                        listChecker(l.getType(), varDeclaration);
                    }
                    int i, j, k = 0;
                    for (i = 0; i < listNameTypes.size() - 1; i++) {
                        for (j = i + 1; j < listNameTypes.size(); j++) {
                            if (listNameTypes.get(i).getName().getName().equals(listNameTypes.get(j).getName().getName())
                                    && !listNameTypes.get(i).getName().getName().equals("") &&
                                    !listNameTypes.get(j).getName().getName().equals("")) {
                                varDeclaration.addError(new DuplicateListId(varDeclaration.getLine()));
                                field.setType(new NoType());
                                k = 1;
                                break;
                            }
                        }
                        if (k == 1)
                            break;
                    }
                } else if (type instanceof FptrType) {
                    Type t1 = ((FptrType) type).getReturnType();
                    if(t1 instanceof ClassType) {
                        try {
                            ClassSymbolTableItem foundClass = (ClassSymbolTableItem) SymbolTable.root
                                    .getItem(ClassSymbolTableItem.START_KEY +
                                            ((ClassType)  t1).getClassName().getName(), true);
                        }catch (ItemNotFoundException classNotFound){
                            varDeclaration.addError(new ClassNotDeclared(varDeclaration.getLine(),
                                    ((ClassType) t1).getClassName().getName()));
                            field.setType(new NoType());
                        }
                    }

                    listChecker(t1, varDeclaration);
                    ArrayList<Type> types = ((FptrType) type).getArgumentsTypes();
                    for (Type x : types) {
                        if(x instanceof ClassType) {
                            try {
                                ClassSymbolTableItem foundClass = (ClassSymbolTableItem) SymbolTable.root
                                        .getItem(ClassSymbolTableItem.START_KEY +
                                                ((ClassType)  x).getClassName().getName(), true);
                            }catch (ItemNotFoundException classNotFound){
                                varDeclaration.addError(new ClassNotDeclared(varDeclaration.getLine(),
                                        ((ClassType)  x).getClassName().getName()));
                                field.setType(new NoType());
                            }
                        }
                        listChecker(x, varDeclaration);
                    }
                }
            }
        }catch(ItemNotFoundException classNotFound){
            System.out.println("Error dar listChecker    " + varDeclaration.getLine());
        }
    }

    public void listChecker_methodReturnMethod(Type type, MethodDeclaration methodDeclaration) {
        LocalVariableSymbolTableItem local;
        FieldSymbolTableItem field;
        //System.out.println(type.toString() + "    " + varDeclaration.getLine());
        try {
            ClassSymbolTableItem currentClass = (ClassSymbolTableItem) SymbolTable.root
                    .getItem(ClassSymbolTableItem.START_KEY + currentClassName, true);
            try {
                MethodSymbolTableItem method = (MethodSymbolTableItem) currentClass.getClassSymbolTable()
                        .getItem(MethodSymbolTableItem.START_KEY + currentMethodName, true);

                if (type instanceof ListType) {

                    if (((ListType) type).getElementsTypes().isEmpty()) {
                        methodDeclaration.addError(new CannotHaveEmptyList(methodDeclaration.getLine()));
                        method.setReturnType(new NoType());
                    }

                    ArrayList<ListNameType> listNameTypes = ((ListType) type).getElementsTypes();
                    for (ListNameType l : listNameTypes) {
                        if (l.getType() instanceof ClassType) {
                            try {
                                ClassSymbolTableItem foundClass = (ClassSymbolTableItem) SymbolTable.root
                                        .getItem(ClassSymbolTableItem.START_KEY +
                                                ((ClassType) l.getType()).getClassName().getName(), true);
                            } catch (ItemNotFoundException classNotFound) {
                                methodDeclaration.addError(new ClassNotDeclared(methodDeclaration.getLine(),
                                        ((ClassType) l.getType()).getClassName().getName()));
                                method.setReturnType(new NoType());
                            }
                        }
                        listChecker_methodReturnMethod(l.getType(), methodDeclaration);
                    }
                    int i, j, k = 0;
                    for (i = 0; i < listNameTypes.size() - 1; i++) {
                        for (j = i + 1; j < listNameTypes.size(); j++) {
                            if (listNameTypes.get(i).getName().getName().equals(listNameTypes.get(j).getName().getName())
                                    && !listNameTypes.get(i).getName().getName().equals("") &&
                                    !listNameTypes.get(j).getName().getName().equals("")) {
                                methodDeclaration.addError(new DuplicateListId(methodDeclaration.getLine()));
                                method.setReturnType(new NoType());
                                k = 1;
                                break;
                            }
                        }
                        if (k == 1)
                            break;
                    }
                } else if (type instanceof FptrType) {
                    Type t1 = ((FptrType) type).getReturnType();
                    if (t1 instanceof ClassType) {
                        try {
                            ClassSymbolTableItem foundClass = (ClassSymbolTableItem) SymbolTable.root
                                    .getItem(ClassSymbolTableItem.START_KEY +
                                            ((ClassType) t1).getClassName().getName(), true);
                        } catch (ItemNotFoundException classNotFound) {
                            methodDeclaration.addError(new ClassNotDeclared(methodDeclaration.getLine(),
                                    ((ClassType) t1).getClassName().getName()));
                            method.setReturnType(new NoType());
                        }
                    }
                    listChecker_methodReturnMethod(t1, methodDeclaration);
                    ArrayList<Type> types = ((FptrType) type).getArgumentsTypes();
                    for (Type x : types) {
                        if (x instanceof ClassType) {
                            try {
                                ClassSymbolTableItem foundClass = (ClassSymbolTableItem) SymbolTable.root
                                        .getItem(ClassSymbolTableItem.START_KEY +
                                                ((ClassType) x).getClassName().getName(), true);
                            } catch (ItemNotFoundException classNotFound) {
                                methodDeclaration.addError(new ClassNotDeclared(methodDeclaration.getLine(),
                                        ((ClassType) x).getClassName().getName()));
                                method.setReturnType(new NoType());
                            }
                        }
                        listChecker_methodReturnMethod(x, methodDeclaration);
                    }
                }
            } catch (ItemNotFoundException methodNotFound) {
                System.out.println("Error dar listChecker    " + methodDeclaration.getLine());
            }
        }catch(ItemNotFoundException classNotFound){
            System.out.println("Error dar listChecker    " + methodDeclaration.getLine());
        }
    }

    @Override
    public Void visit(Program program) {
        ArrayList<ClassDeclaration> classes = program.getClasses();
        for (ClassDeclaration classDeclaration : classes) {
            if(classDeclaration.getClassName().getName().equals("Main")){
                has_main = true;
            }
            classDeclaration.accept(this);
        }
        if(!has_main){
            program.addError(new NoMainClass());
        }
        return null;
    }

    @Override
    public Void visit(ClassDeclaration classDeclaration) {

        expressionTypeChecker.currentClassName = classDeclaration.getClassName().getName();
        currentClassName = classDeclaration.getClassName().getName();
        currentMethodName = classDeclaration.getClassName().getName();
        expressionTypeChecker.currentMethodName = classDeclaration.getClassName().getName();
        String parentName = "";
        if(classDeclaration.getParentClassName() != null){
            parentName = classDeclaration.getParentClassName().getName();
        }

        if(currentClassName.equals("Main")){
            if(!(parentName.equals("Main")) && (classDeclaration.getParentClassName() != null)){
                classDeclaration.addError(new MainClassCantExtend(classDeclaration.getLine()));
            }
        }

        if(!parentName.equals("")){
            try {
                ClassSymbolTableItem currentClass = (ClassSymbolTableItem) SymbolTable.root
                        .getItem(ClassSymbolTableItem.START_KEY + parentName, true);
            }catch (ItemNotFoundException classNotFound){
                classDeclaration.addError(new ClassNotDeclared(classDeclaration.getLine(), parentName));
            }

            if(parentName.equals("Main") && !currentClassName.equals("Main")){
                classDeclaration.addError(new CannotExtendFromMainClass(classDeclaration.getParentClassName().getLine()));
            }
        }
        ConstructorDeclaration constructorDeclaration;
        if( classDeclaration.getConstructor() != null) {
            constructorDeclaration = classDeclaration.getConstructor();
            constructorDeclaration.accept(this);
        }
        if(currentClassName.equals("Main")){
            if(classDeclaration.getConstructor() == null){
                classDeclaration.addError(new NoConstructorInMainClass(classDeclaration));
            }
        }
        ArrayList<FieldDeclaration> fieldDeclarations = classDeclaration.getFields();
        for(FieldDeclaration fieldDeclaration : fieldDeclarations){
            fieldDeclaration.accept(this);
        }
        ArrayList<MethodDeclaration> methodDeclarations =  classDeclaration.getMethods();
        for(MethodDeclaration methodDeclaration : methodDeclarations){
            methodDeclaration.accept(this);
        }
        return null;
    }

    @Override
    public Void visit(ConstructorDeclaration constructorDeclaration) {
        currentMethodName = constructorDeclaration.getMethodName().getName();
        expressionTypeChecker.currentMethodName = currentMethodName;
        expressionTypeChecker.in_method = true;
        String constructorDeclarationName = constructorDeclaration.getMethodName().getName();
        if(!constructorDeclarationName.equals(currentClassName)){
            constructorDeclaration.addError(new ConstructorNotSameNameAsClass(constructorDeclaration.getLine()));
        }
        if(!constructorDeclaration.getArgs().isEmpty() && constructorDeclarationName.equals("Main")){
            constructorDeclaration.addError(new MainConstructorCantHaveArgs(constructorDeclaration.getLine()));
        }
        ArrayList<VarDeclaration> args = constructorDeclaration.getArgs();
        for (VarDeclaration arg : args){
            arg.accept(this);
        }

        ArrayList<VarDeclaration> varDeclarations = constructorDeclaration.getLocalVars();
        for (VarDeclaration varDeclaration : varDeclarations){
            varDeclaration.accept(this);
        }

        ArrayList<Statement> statements =  constructorDeclaration.getBody();
        for(Statement statement : statements){
            statement.accept(this);
        }
        expressionTypeChecker.in_method = false;
        return null;
    }

    @Override
    public Void visit(MethodDeclaration methodDeclaration) {
        //String methodDeclarationName = methodDeclaration.getMethodName().getName();
        expressionTypeChecker.in_method = true;
        currentMethodName = methodDeclaration.getMethodName().getName();
        expressionTypeChecker.currentMethodName = methodDeclaration.getMethodName().getName();

        Type type = methodDeclaration.getReturnType();
        listChecker_methodReturnMethod(type,methodDeclaration);
        ArrayList<VarDeclaration> args = methodDeclaration.getArgs();
        for (VarDeclaration arg : args){
            arg.accept(this);
        }

        ArrayList<VarDeclaration> varDeclarations = methodDeclaration.getLocalVars();
        for (VarDeclaration varDeclaration : varDeclarations){
            varDeclaration.accept(this);
        }

        if(!(methodDeclaration.getReturnType() instanceof NullType)){
            has_return = true;
        }
        ArrayList<Statement> statements = methodDeclaration.getBody();
        for(Statement statement : statements){
            statement.accept(this);
        }
        expressionTypeChecker.in_method = false;
        if(has_return){
            methodDeclaration.addError(new MissingReturnStatement(methodDeclaration));
        }
        has_return = false;
        return null;
    }

    @Override
    public Void visit(FieldDeclaration fieldDeclaration) {
        fieldDeclaration.getVarDeclaration().accept(this);
        return null;
    }

    @Override
    public Void visit(VarDeclaration varDeclaration) {
        Type t = varDeclaration.getType();
        listChecker(t, varDeclaration);

        if(t instanceof ClassType){
            try {
                ClassSymbolTableItem currentClass = (ClassSymbolTableItem) SymbolTable.root
                        .getItem(ClassSymbolTableItem.START_KEY + ((ClassType) t).getClassName().getName(), true);
            }catch (ItemNotFoundException classNotFound){
                varDeclaration.addError(new ClassNotDeclared(varDeclaration.getLine(), ((ClassType) t).getClassName().getName()));
                if(expressionTypeChecker.in_method){
                    try{
                        ClassSymbolTableItem currentClass = (ClassSymbolTableItem) SymbolTable.root
                                .getItem(ClassSymbolTableItem.START_KEY +currentClassName, true);
                        MethodSymbolTableItem method = (MethodSymbolTableItem) currentClass.getClassSymbolTable()
                                .getItem(MethodSymbolTableItem.START_KEY + currentMethodName, true);
                        LocalVariableSymbolTableItem local = (LocalVariableSymbolTableItem) method.getMethodSymbolTable()
                                .getItem(LocalVariableSymbolTableItem.START_KEY + varDeclaration.getVarName().getName(), true);
                        local.setType(new NoType());
                    }catch (ItemNotFoundException x){
                        System.out.println("error in varDec");
                    }
                }
                else{
                    try{
                        ClassSymbolTableItem currentClass = (ClassSymbolTableItem) SymbolTable.root
                                .getItem(ClassSymbolTableItem.START_KEY +currentClassName, true);
                        FieldSymbolTableItem field = (FieldSymbolTableItem) currentClass.getClassSymbolTable()
                                .getItem(FieldSymbolTableItem.START_KEY + varDeclaration.getVarName().getName(), true);
                        field.setType(new NoType());
                    }catch (ItemNotFoundException x){
                        System.out.println("error in varDec");
                    }
                }
            }
        }
        return null;
    }

    @Override
    public Void visit(AssignmentStmt assignmentStmt) {
        Expression lvalue = assignmentStmt.getlValue();
        Expression rvalue = assignmentStmt.getrValue();
        //System.out.println(rvalue.toString() + "  [[[[[[[[[[[[[[[[[[[[[[[[[[[[[");
        //System.out.println("fffffffffff");
        expressionTypeChecker.is_lvalue = true;
        Type t2 = rvalue.accept(expressionTypeChecker);
        expressionTypeChecker.is_lvalue = true;
        Type t1 = lvalue.accept(expressionTypeChecker);
        //System.out.println(lvalue.toString() + "   "  + lvalue.getLine());
        //System.out.println(rvalue.toString() + "   "  + rvalue.getLine());

        //System.out.println(t1.toString() + "   " + t2.toString() + "   " + assignmentStmt.getLine());

        if (!expressionTypeChecker.is_lvalue) {
            assignmentStmt.addError(new LeftSideNotLvalue(assignmentStmt.getLine()));
        }

        //System.out.println(t1.toString() + "qqqqqqqqq");
        if(!isFirstSubTypeOfSecond(t2, t1) && !(t1 instanceof NoType)){
            assignmentStmt.addError(new UnsupportedOperandType(assignmentStmt.getLine(), BinaryOperator.assign.toString()));
        }
        return null;
    }

    @Override
    public Void visit(BlockStmt blockStmt) {
        if (blockStmt == null)
            return null;
        ArrayList<Statement> statements = blockStmt.getStatements();
        for (Statement statement : statements)
            statement.accept(this);
        return null;
    }

    @Override
    public Void visit(ConditionalStmt conditionalStmt) {
        Expression exp = conditionalStmt.getCondition();
        Type t = exp.accept(expressionTypeChecker);
        if(!(t instanceof BoolType) && !(t instanceof NoType)){
            int line = conditionalStmt.getLine();
            conditionalStmt.addError(new ConditionNotBool(line));
        }
        conditionalStmt.getThenBody().accept(this);
        if(conditionalStmt.getElseBody() != null){
            conditionalStmt.getElseBody().accept(this);
        }
        return null;
    }

    @Override
    public Void visit(MethodCallStmt methodCallStmt) {
        expressionTypeChecker.in_methodCallStatement = true;
        MethodCall methodCall = methodCallStmt.getMethodCall();
        methodCall.accept(expressionTypeChecker);
        expressionTypeChecker.in_methodCallStatement = false;
        return null;
    }

    @Override
    public Void visit(PrintStmt print) {
        Expression exp = print.getArg();
        Type t = exp.accept(expressionTypeChecker);
        if(!(t instanceof StringType) && !(t instanceof BoolType) && !(t instanceof IntType) && !(t instanceof NoType)){
            int line = print.getLine();
            print.addError(new UnsupportedTypeForPrint(line));
        }
        return null;
    }

    @Override
    public Void visit(ReturnStmt returnStmt) {
        has_return = false;
        Type t1 = returnStmt.getReturnedExpr().accept(expressionTypeChecker);
        try {
            ClassSymbolTableItem currentClass = (ClassSymbolTableItem) SymbolTable.root
                    .getItem(ClassSymbolTableItem.START_KEY + currentClassName, true);
            try {
                MethodSymbolTableItem methodSymbolTableItem = (MethodSymbolTableItem) currentClass.getClassSymbolTable()
                        .getItem(MethodSymbolTableItem.START_KEY + currentMethodName, true);
                Type t2 = methodSymbolTableItem.getReturnType();

                if(!isFirstSubTypeOfSecond(t1, t2) && !(t1 instanceof NullType) && !(t1 instanceof NoType)){
                    returnStmt.addError(new ReturnValueNotMatchMethodReturnType(returnStmt));
                    return null;
                }
            }catch (ItemNotFoundException methodNotFound){
                return null;
            }
        } catch (ItemNotFoundException ignored) {
            return null;
        }
        return null;
    }

    @Override
    public Void visit(BreakStmt breakStmt) {
        if(in_for <= 0){
            int line = breakStmt.getLine();
            breakStmt.addError(new ContinueBreakNotInLoop(line, 0));
        }
        return null;
    }

    @Override
    public Void visit(ContinueStmt continueStmt) {
        if(in_for <= 0){
            int line = continueStmt.getLine();
            continueStmt.addError(new ContinueBreakNotInLoop(line, 1));
        }
        return null;
    }

    @Override
    public Void visit(ForeachStmt foreachStmt) {
        //boolean flag = false;
        in_for++;
        int line = foreachStmt.getLine();
        Identifier var = foreachStmt.getVariable();
        Type id = var.accept(expressionTypeChecker);
        Expression x = foreachStmt.getList();
        Type list = x.accept(expressionTypeChecker);

        if(list instanceof NoType){
            foreachStmt.getBody().accept(this);
            return null;
        }
        if(!(list instanceof ListType)){
            foreachStmt.addError(new ForeachCantIterateNoneList(line));
            return null;
        }



        ArrayList<ListNameType> exp_list = ((ListType) list).getElementsTypes();
        Type y = exp_list.get(0).getType();
        Type a;
        Type b = null;
        boolean flag = false;
        int i = 0;

        for(ListNameType l : exp_list){
            i++;
            a = l.getType();
            if(a instanceof NoType){
                continue;
            }
            if(b == null){
                b = a;
                continue;
            }
            if(!(isFirstSubTypeOfSecond(a, b)) || !isFirstSubTypeOfSecond(b, a)){
                foreachStmt.addError(new ForeachListElementsNotSameType(foreachStmt.getLine()));
                if(!(id instanceof NoType) && !isFirstSubTypeOfSecond(id, y) && !isFirstSubTypeOfSecond(y, id)){
                    foreachStmt.addError(new ForeachVarNotMatchList(foreachStmt));
                }
                flag = true;
                break;
            }
        }

        if(!flag && !(id instanceof NoType) && b != null && !isFirstSubTypeOfSecond(id, b) && !isFirstSubTypeOfSecond(b, id)){
            foreachStmt.addError(new ForeachVarNotMatchList(foreachStmt));
        }

        Statement stat = foreachStmt.getBody();
        stat.accept(this);
        in_for--;
        return null;
    }

    @Override
    public Void visit(ForStmt forStmt) {
        in_for++;
        forStmt.getInitialize().accept(this);
        Expression exp = forStmt.getCondition();
        Type t = exp.accept(expressionTypeChecker);
        if(!(t instanceof BoolType) && !(t instanceof NoType)){
            int line = forStmt.getLine();
            forStmt.addError(new ConditionNotBool(line));
        }
        if(forStmt.getUpdate() != null) {
            forStmt.getUpdate().accept(this);
        }
        forStmt.getBody().accept(this);
        in_for--;
        return null;
    }
}
