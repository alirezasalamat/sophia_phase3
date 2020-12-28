package main.visitor.typeChecker;

import main.ast.nodes.Program;
import main.ast.nodes.declaration.classDec.ClassDeclaration;
import main.ast.nodes.declaration.classDec.classMembersDec.ConstructorDeclaration;
import main.ast.nodes.declaration.classDec.classMembersDec.FieldDeclaration;
import main.ast.nodes.declaration.classDec.classMembersDec.MethodDeclaration;
import main.ast.nodes.declaration.variableDec.VarDeclaration;
import main.ast.nodes.expression.*;
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

import java.io.StringReader;
import java.util.ArrayList;

public class TypeChecker extends Visitor<Void> {
    private final Graph<String> classHierarchy;
    private final ExpressionTypeChecker expressionTypeChecker;
    private boolean in_for = false;
    private boolean has_main = false;
    private String currentClassName;
    private String currentMethodName;

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
        return exp instanceof Identifier || exp instanceof ListAccessByIndex ||
                exp instanceof ObjectOrListMemberAccess;
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
        String parentName = classDeclaration.getParentClassName().getName();
        if(currentClassName.equals("Main")){
            if(!(parentName.equals("Main") && classDeclaration.getParentClassName() != null)){
                classDeclaration.addError(new MainClassCantExtend(classDeclaration.getLine()));
            }
        }
        if(parentName != null){
            if(classHierarchy.doesGraphContainNode(parentName) && !parentName.equals("Main")){
                classDeclaration.addError(new ClassNotDeclared(classDeclaration.getParentClassName().getLine(), parentName));
            }
            else if(parentName.equals("Main") && !currentClassName.equals("Main")){
                classDeclaration.addError(new CannotExtendFromMainClass(classDeclaration.getParentClassName().getLine()));
            }
        }
        ConstructorDeclaration constructorDeclaration = classDeclaration.getConstructor();
        constructorDeclaration.accept(this);
        if(currentClassName.equals("Main")){
            if(constructorDeclaration.getMethodName().getName().equals("")){
                classDeclaration.addError(new NoConstructorInMainClass(classDeclaration));
            }
        }

        ArrayList<MethodDeclaration> methodDeclarations =  classDeclaration.getMethods();
        for(MethodDeclaration methodDeclaration : methodDeclarations){
            methodDeclaration.accept(this);
        }

        ArrayList<FieldDeclaration> fieldDeclarations = classDeclaration.getFields();
        for(FieldDeclaration fieldDeclaration : fieldDeclarations){
            fieldDeclaration.accept(this);
        }
        return null;
    }

    @Override
    public Void visit(ConstructorDeclaration constructorDeclaration) {
        currentMethodName = constructorDeclaration.getMethodName().getName();
        String constructorDeclarationName = constructorDeclaration.getMethodName().getName();
        if(!constructorDeclarationName.equals(currentClassName)){
            constructorDeclaration.addError(new ConstructorNotSameNameAsClass(constructorDeclaration.getLine()));
        }
        if(!constructorDeclaration.getArgs().isEmpty() && constructorDeclarationName.equals("Main")){
            constructorDeclaration.addError(new MainConstructorCantHaveArgs(constructorDeclaration.getLine()));
        }
        if(constructorDeclaration.getReturnType() instanceof NullType){
            constructorDeclaration.addError(new CantUseValueOfVoidMethod(constructorDeclaration.getLine()));
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
        return null;
    }

    @Override
    public Void visit(MethodDeclaration methodDeclaration) {
        //String methodDeclarationName = methodDeclaration.getMethodName().getName();

        currentMethodName = methodDeclaration.getMethodName().getName();
        ArrayList<VarDeclaration> args = methodDeclaration.getArgs();
        for (VarDeclaration arg : args){
            arg.accept(this);
        }

        ArrayList<VarDeclaration> varDeclarations = methodDeclaration.getLocalVars();
        for (VarDeclaration varDeclaration : varDeclarations){
            varDeclaration.accept(this);
        }

        ArrayList<Statement> statements = methodDeclaration.getBody();
        for(Statement statement : statements){
            statement.accept(this);
        }
        return null;
    }

    @Override
    public Void visit(FieldDeclaration fieldDeclaration) {
        //TODO
        return null;
    }

    @Override
    public Void visit(VarDeclaration varDeclaration) {

        return null;
    }

    @Override
    public Void visit(AssignmentStmt assignmentStmt) {
        Expression rvalue = assignmentStmt.getrValue();
        Expression lvalue = assignmentStmt.getlValue();
        Type t1 = lvalue.accept(expressionTypeChecker);
        Type t2 = rvalue.accept(expressionTypeChecker);

        if (!isLValue(lvalue)) {
            assignmentStmt.addError(new LeftSideNotLvalue(assignmentStmt.getLine()));
        }
        return null;
    }

    @Override
    public Void visit(BlockStmt blockStmt) {
        if (blockStmt == null)
            return null;
        ArrayList<Statement> statements = blockStmt.getStatements();
        for (Statement statement : statements)
            statement.accept(expressionTypeChecker);
        return null;
    }

    @Override
    public Void visit(ConditionalStmt conditionalStmt) {
        Expression exp = conditionalStmt.getCondition();
        Type t = exp.accept(expressionTypeChecker);
        if(!(t instanceof BoolType)){
            int line = conditionalStmt.getLine();
            conditionalStmt.addError(new ConditionNotBool(line));
        }
        return null;
    }

    @Override
    public Void visit(MethodCallStmt methodCallStmt) {
        MethodCall methodCall = methodCallStmt.getMethodCall();
        methodCall.accept(expressionTypeChecker);
        return null;
    }

    @Override
    public Void visit(PrintStmt print) {
        Expression exp = print.getArg();
        Type t = exp.accept(expressionTypeChecker);
        if(!(t instanceof StringType) && !(t instanceof BoolType) && !(t instanceof IntType)){
            int line = print.getLine();
            print.addError(new UnsupportedTypeForPrint(line));
        }
        return null;
    }

    @Override
    public Void visit(ReturnStmt returnStmt) {
        Type t1 = returnStmt.getReturnedExpr().accept(expressionTypeChecker);
        try {
            MethodSymbolTableItem methodSymbolTableItem = (MethodSymbolTableItem)
                    SymbolTable.root.getItem(MethodSymbolTableItem.START_KEY + this.currentMethodName, true);
            Type t2 = methodSymbolTableItem.getReturnType();

            if(t2 instanceof NullType){
                if(!(t1 instanceof NullType) && !(t1 instanceof NoType)){
                    returnStmt.addError(new CantUseValueOfVoidMethod(returnStmt.getLine()));
                }
            }
            else if(t2 instanceof ClassType){
                if(t2 != t1){
                    ClassType c1 = (ClassType) t1;
                    ClassType c2 = (ClassType) t2;
                    if(!(classHierarchy.isSecondNodeAncestorOf(
                            c1.getClassName().getName(), c2.getClassName().getName())) && !(t1 instanceof NoType)){
                        returnStmt.addError(new ReturnValueNotMatchMethodReturnType(returnStmt));
                    }
                }
            }
            else if(t2 instanceof IntType){
                if(!(t1 instanceof IntType) && !(t1 instanceof NoType)){
                    returnStmt.addError(new ReturnValueNotMatchMethodReturnType(returnStmt));
                }
            }
            else if(t2 instanceof StringType){
                if(!(t1 instanceof StringType) && !(t1 instanceof NoType)){
                    returnStmt.addError(new ReturnValueNotMatchMethodReturnType(returnStmt));
                }
            }
            else if(t2 instanceof BoolType){
                if(!(t1 instanceof BoolType) && !(t1 instanceof NoType)){
                    returnStmt.addError(new ReturnValueNotMatchMethodReturnType(returnStmt));
                }
            }
            else if(t2 instanceof FptrType){
                if(!(t1 instanceof FptrType) && !(t1 instanceof NoType)){
                    returnStmt.addError(new ReturnValueNotMatchMethodReturnType(returnStmt));
                }
            }
            else if(t2 instanceof ListType){
                if(!(t1 instanceof ListType) && !(t1 instanceof NoType)){
                    returnStmt.addError(new ReturnValueNotMatchMethodReturnType(returnStmt));
                }
            }
        } catch (ItemNotFoundException ignored) {
            return null;
        }
        return null;
    }

    @Override
    public Void visit(BreakStmt breakStmt) {
        if(!in_for){
            int line = breakStmt.getLine();
            breakStmt.addError(new ContinueBreakNotInLoop(line, 0));
        }
        return null;
    }

    @Override
    public Void visit(ContinueStmt continueStmt) {
        if(!in_for){
            int line = continueStmt.getLine();
            continueStmt.addError(new ContinueBreakNotInLoop(line, 0));
        }
        return null;
    }

    @Override
    public Void visit(ForeachStmt foreachStmt) {
        //boolean flag = false;
        int line = foreachStmt.getLine();
        Identifier var = foreachStmt.getVariable();
        Type id = var.accept(expressionTypeChecker);
        Expression x = foreachStmt.getList();
        Type list = x.accept(expressionTypeChecker);
        ArrayList<Expression> exp_list = ((ListValue) x).getElements();

        if(list instanceof ListType){
            Type t1  = exp_list.get(0).accept(expressionTypeChecker);
            for(Expression exp : exp_list){
                Type t2 = exp.accept(expressionTypeChecker);
                if(t1 != t2){
                    //flag = true;
                    foreachStmt.addError(new ForeachListElementsNotSameType(line));
                    break;
                }
            }
            if(t1 != id){
                foreachStmt.addError(new ForeachVarNotMatchList(foreachStmt));
            }
        }
        else{
            foreachStmt.addError(new ForeachCantIterateNoneList(line));
        }

        Statement stat = foreachStmt.getBody();
        stat.accept(this);
        return null;
    }

    @Override
    public Void visit(ForStmt forStmt) {
        in_for = true;
        forStmt.getInitialize().accept(this);
        Expression exp = forStmt.getCondition();
        Type t = exp.accept(expressionTypeChecker);
        if(!(t instanceof BoolType)){
            int line = forStmt.getLine();
            forStmt.addError(new ConditionNotBool(line));
        }

        forStmt.getUpdate().accept(this);
        forStmt.getBody().accept(this);
        in_for = false;
        return null;
    }
}
