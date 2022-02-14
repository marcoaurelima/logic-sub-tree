#include <iostream>
#include <sstream>
#include <vector>
#include <map>
#include <set>
#include <algorithm>
#include <cstdlib>
#include <ctype.h>

/*

************************************************
**                                            **
**   Autor:      Marco Aurélio Lima - 2021    **
**   Linguagem:  C++11                        **
**                                            **
************************************************

*/

enum{
    TYPE_EXTERNAL,
    TYPE_DEEP,
    DIR_LEFT,
    DIR_RIGHT
};

void initInterface();
std::string getFormula();
void deleteSpaces(std::string& expression);
bool isValid(const std::string& expression);
std::string encapsule(std::string formula);
std::string desencapsule(std::string formula, int type);
std::vector< std::pair<int, char> > getIndexParenthesis(const std::string& formula);
std::vector< std::pair<int, int> > expressionIndexes(const std::string& formula);
std::vector<std::string> generateListSub(std::vector< std::pair<int, int> > parentIndexes, const std::string& formulaEnc);
void printStringList(std::vector<std::string>& stringList);
void showSubFormulas(const std::string& formula);
std::vector<std::string> getMainConective(std::string formula);
int showArvore(std::string formula, std::string line_V, int direction, int complexity);
std::string corrigirStr(std::string formula, bool printResult);
void showComplexity(const int& value);

void initInterface()
{
    puts("");

    printf(" %s%s ", "\u250c", "\u2500");
    printf(" LÓGICA PROPOSICIONAL - Subformulas e Arvore sintatica. \n");
    printf(" %s%s ", "\u2514", "\u2500");
    printf(" Marco Aurelio Lima - 2021 ");
    puts("\n");

        printf("     Conectivos:\n");
        printf("     [&]Conjunção [#]disjuncao [~]Negacao [>]Implicacao\n\n");
}

void deleteSpaces(std::string& expression)
{
    std::string temp;
    for(auto& i : expression){
        if(i != ' ') { temp += i; }
    }

    expression = temp;
}


int parentExcess(const std::string& formula)
{
    // No caso de "(a)"
    if(formula.size() == 3)
    {
        if(formula[0] == '(' && isalnum(formula[1]) && formula[2] == ')'){ return 1; }
    }

    // Remoção no caso specifico em que a extremidades tem que ser removidas, porem não estao no padrão "((a&b))"
    // como por exemplo: "(a&(c&d))"
    // Este metodo consiste em analizar os indices das subformulas e identificar quantos parenteses
    // que abrem na extremidade esquerda e so acabam na extremidade direira
    // O laço for vai procurar o seguinte padrão: ex.: formula tem 10 caracteres -> "0,9" , "1,8" (significa que os dois ultimos parenteses devem ser deletados)
    std::string                        formulaEnc      = encapsule(formula);
    std::vector< std::pair<int, int> > parentIndexes   = expressionIndexes(formulaEnc);
    int contParentExtremidade = 0;
    for(unsigned j=0;j<formulaEnc.size();j++)
    {
        // Encerar no primeiro caractere que não seja "("
        if(formulaEnc[j] != '('){ break; }
        for(auto& i : parentIndexes)
        {
            if((unsigned)i.first == j && (unsigned)i.second == formulaEnc.size()-j-1)
            {
                contParentExtremidade++;
            }
        }
    }

    return contParentExtremidade;
}

// Verificar a validade dos parenteses. Quantidade dos parenteses: abertos == fechados.
//Dois ou mais atomos nao podem aparecer juntos sem conectivos entre si.
bool isValid(const std::string& expression)
{
    enum {
        ERR_ATOM,              // Atomo fora do internalo a - z
        ERR_ATOM_WT_CONNECT,   // Atomos juntos sem conectivos
        ERR_CONNECT,           // Conectivo fora do padrao: ~ & # >
        ERR_NUM_PARENTESIS,    // Nº de parentesis abertos diferente do nº de parentesis fechados
        ERR_TWO_NEGATIVES,     // Existem dois conectivos unários de negação; redundancia
        ERR_NEG_PARENT_EXTERN, // Negacao de uma formula com parenteses externos
        ERR_PARENT_EXCESS,     // Excesso de parenteses
        ERR_USE_NEGATIVE       // Operador de negação usado incorretamente (a~)
    };
    std::map<std::string, bool> error_list;
    int parentesis_cont[2] = {0, 0};

    //Verificar se existem excesso d parenteses externos
    if(parentExcess(expression) > 1)
    {
        error_list["ERR_PARENT_EXCESS"] = true;
    }

    // verificar se atomos e conectivos estão dentro do padrão
    for(size_t i=0; i<expression.size(); i++)
    {
        if(isalpha(expression[i]))
        {
            if(expression[i] >= 'a' && expression[i] <= 'z')
            {
                if(i < expression.size()-1)
                {
                    // Dois atomos juntos sem conectivo (qq)
                    if(expression[i+1] >= 'a' && expression[i+1] <= 'z')
                    {
                        error_list["ERR_ATOM_WT_CONNECT"] = true;
                    }
                }

            } else {
                error_list["ERR_ATOM"] = true;
            }
        } else
        {
            if(expression[i] != '&' && expression[i] != '#' && expression[i] != '>' && expression[i] != '~')
            {
                if(expression[i] != '(' && expression[i] != ')'){
                    error_list["ERR_CONNECT"] = true;
                }
            } else {
                if(expression[i] == '~' && expression[i+1] == '~')
                {
                    error_list["ERR_TWO_NEGATIVES"] = true;
                }
            }
        }

        // Sequencia do tipo ")q"
        if( expression[i] == ')' && (expression[i+1] >= 'a' && expression[i+1] <= 'z'))
        {
            error_list["ERR_ATOM_WT_CONNECT"] = true;
        }
        // Sequencia do tipo "q("
        if((expression[i] >= 'a' && expression[i] <= 'z') && expression[i+1] == '(')
        {
            error_list["ERR_ATOM_WT_CONNECT"] = true;
        }

        // Sequencia do tipo "(~a)"
        if(expression[i] == '(')
        {
            if(expression[i+1] == '~' && isalnum(expression[i+2]) && expression[i+3] == ')')
            {
                error_list["ERR_NEG_PARENT_EXTERN"] = true;
            }
        }

        // Sequencia do tipo "~)"
        if(expression[i] == '~' && expression[i+1] == ')')
        {
            error_list["ERR_USE_NEGATIVE"] = true;
        }


        if(expression[i] == '(') { parentesis_cont[0]++; }
        if(expression[i] == ')') { parentesis_cont[1]++; }
    }

    if(parentesis_cont[0] != parentesis_cont[1]){
        error_list["ERR_NUM_PARENTESIS"] = true;
    }


   if(!error_list.empty()){
        std::cout << "\n  -------------------------------------------------------\n";
        std::cout << "                     FORMULA INVALIDA                     \n";
        std::cout << "  -------------------------------------------------------\n\n";
    }

    int err_cont = 0;
    if(error_list["ERR_ATOM"])
    {
        std::cout << "    [" << ++err_cont << "]  Algum simbolo atomico esta fora do intervalo [a-z]\n" << std::endl;
    }
    if(error_list["ERR_ATOM_WT_CONNECT"])
    {
        std::cout << "    [" << ++err_cont << "]  Algum atomo esta sem conectivo\n" << std::endl;
    }
    if(error_list["ERR_CONNECT"])
        std::cout << "    [" << ++err_cont << "]  Algum conectivo esta fora do padrao: \n         & (conjuncao)\n         # (disjuncao)\n         > (implicacao)\n         ~ (negacao)\n" << std::endl;
    {
    }
    if(error_list["ERR_NUM_PARENTESIS"])
    {
        std::cout << "    [" << ++err_cont << "]  Parenteses dispostos incorretamente\n" << std::endl;
    }
    if(error_list["ERR_TWO_NEGATIVES"])
    {
        std::cout << "    [" << ++err_cont << "]  Ha conectivos unarios de negacao redundantes (~~)\n" << std::endl;
    }
    if(error_list["ERR_NEG_PARENT_EXTERN"])
    {
        std::cout << "    [" << ++err_cont << "]  Negacao de uma formula com parenteses externos\n" << std::endl;
    }
    if(error_list["ERR_PARENT_EXCESS"])
    {
        std::cout << "    [" << ++err_cont << "]  Ha excesso de parenteses\n" << std::endl;
    }
    if(error_list["ERR_USE_NEGATIVE"])
    {
        std::cout << "    [" << ++err_cont << "]  Uso errado do operador de nagacao\n" << std::endl;
    }


    bool valid = !(error_list["ERR_ATOM"] ||
                   error_list["ERR_ATOM_WT_CONNECT"] ||
                   error_list["ERR_CONNECT"] ||
                   error_list["ERR_NUM_PARENTESIS"] ||
                   error_list["ERR_TWO_NEGATIVES"] ||
                   error_list["ERR_NEG_PARENT_EXTERN"] ||
                   error_list["ERR_PARENT_EXCESS"] ||
                   error_list["ERR_USE_NEGATIVE"]);

    if(!valid)
    {
       std::cout << "  -------------------------------------------------------\n\n\n";
    }

    return valid;
}


std::string encapsule(std::string formula)
{
    std::stringstream ss;
    ss << "(" << formula << ")";
    return ss.str();
}


std::string desencapsule(std::string formula, int type)
{
    // se a formula.size() for 1, significa que é um conectivo
    if(formula.size() == 1){ return formula; }


    // Remoção no caso specifico em que a extremidades tem que ser removidas, porem não estao no padrão "((a&b))"
    // como por exemplo: "(a&(c&d))"
    // Este metodo consiste em analizar os indices das subformulas e identificar quantos parenteses
    // que abrem na extremidade esquerda e so acabam na extremidade direira
    // O laço for vai procurar o seguinte padrão: ex.: formula tem 10 caracteres -> "0,9" , "1,8" (significa que os dois ultimos parenteses devem ser deletados)
    std::string                        formulaEnc      = encapsule(formula);
    std::vector< std::pair<int, int> > parentIndexes   = expressionIndexes(formulaEnc);
    int contParentExtremidade = 0;
    for(unsigned j=0;j<formulaEnc.size();j++)
    {
        // Encerar no primeiro caractere que não seja "("
        if(formulaEnc[j] != '('){ break; }
        for(auto& i : parentIndexes)
        {
            if((unsigned)i.first == j && (unsigned)i.second == formulaEnc.size()-j-1)
            {
                contParentExtremidade++;
            }
        }
    }

    std::stringstream ss;
    for(unsigned i=contParentExtremidade; i<formulaEnc.size()-contParentExtremidade; i++)
    {
        ss << formulaEnc[i];
    }
    formulaEnc = ss.str();


    // Remoção profunda de parenteses: retirar excesso de parenteses internamente em átomos na forma "(a)"
    if(type == TYPE_DEEP){

        std::stringstream ss;
        for(unsigned i=0;i<formulaEnc.size();i++){
            if(formulaEnc[i] == '(' && isalpha(formulaEnc[i+1]) && formulaEnc[i+2] == ')')
            {
                ss << formulaEnc[i+1];
                i+=2;
            } else {
                ss << formulaEnc[i];
            }
        }
        return ss.str();
    }

    return formulaEnc;
}


 std::vector< std::pair<int, char> > getIndexParenthesis(const std::string& formula)
 {
    std::vector< std::pair<int, char> > buffer;

    for(unsigned i=0;i<formula.size();i++){
        if(formula[i] == '(' || formula[i] == ')'){
            buffer.push_back(std::pair<int, char>(i, formula[i]));
        }
    }

    return buffer;
 }


std::vector< std::pair<int, int> > expressionIndexes(const std::string& formula)
{
    // Indices reais dos parenteses na string
    std::vector< std::pair<int, char> > parenthesisIndexes = getIndexParenthesis(formula);

    // Pares de indices que indicam o parentese que abre e o respectivo parentese que o fecha;
    std::vector< std::pair<int, int> > indexesPair;
    while(!parenthesisIndexes.empty())
    {
        std::vector< std::pair<int, char> > buffer;
        for(unsigned i=0;i<parenthesisIndexes.size();i++)
        {
            if(parenthesisIndexes[i].second == '(' && parenthesisIndexes[i+1].second == ')')
            {
                indexesPair.push_back(std::pair<int, int>(parenthesisIndexes[i].first , parenthesisIndexes[i+1].first));
                i++;
            } else
            {
                buffer.push_back(parenthesisIndexes[i]);
            }
        }
        parenthesisIndexes = buffer;
    }

    return indexesPair;
}


std::vector<std::string> generateListSub(std::vector< std::pair<int, int> > parentIndexes, const std::string& formulaEnc)
{
    std::vector<std::string> subformulas; /// Não usei map<string> por que ele altera a ordem dos itens quando ordena.
    // Subformulas de um átomo só
    for(unsigned i=0;i<formulaEnc.size();i++){
        if(isalpha(formulaEnc[i])){
            std::stringstream sub;
            sub << formulaEnc[i];
            subformulas.push_back(desencapsule(sub.str(), TYPE_EXTERNAL));
            // Verificar se tem negação antes do atomo e gerar uma nova subformula
            if(i > 0){
                if(formulaEnc[i-1] == '~'){
                    subformulas.push_back("~" + sub.str());
                }
            }
        }
    }

    // inverter esta primeira parte pra sair na sequencia certa na segunda inverção
    reverse(subformulas.rbegin(), subformulas.rend());

    // Subformulas separadas por parenteses
    for(auto& item : parentIndexes){
        std::string sub = "";
        for(int i=item.first;i<=item.second;i++){
            sub += formulaEnc[i];
        }

        // Verificar se tem negação antes dos parenteses de abertura e gerar uma nova subformula
        if(desencapsule(sub, TYPE_DEEP)[0] == '~'){
            subformulas.push_back(desencapsule(desencapsule(sub, TYPE_EXTERNAL).substr(1), TYPE_EXTERNAL));
        }

        subformulas.push_back(desencapsule(sub, TYPE_DEEP));
    }

    // Inverter a ordem para as subformulas maiores apareçam primeiro
    reverse(subformulas.rbegin(), subformulas.rend());

    // Deletar eventuais repetiçoes
    std::vector<std::string> subformulasNoRepeat;
    for(unsigned i=0;i<subformulas.size();i++){
        for(unsigned j=i;j<subformulas.size();j++){
            if(subformulas[i] == subformulas[j]){
                if(j != i){
                    subformulas.erase(subformulas.begin() + j);
                }
            }
            continue;
        }
    }

    return subformulas;
}


void printStringList(std::vector<std::string>& stringList, const std::string formula){

    printf("\n %s%s ", "\u250c", "\u2500");
    printf(" SUBFORMULAS \n");
    printf(" %s \n", "\u2502");

    for(unsigned i=0; i<stringList.size();i++){

        if(i == 0){
            printf(" %s  ", "\u2502");
            printf("%s \n", formula.c_str());
            printf(" %s \n", "\u2502");
        }

        if(i != stringList.size()-1){
            printf(" %s  ", "\u251c");
        } else {
            printf(" %s  ", "\u2514");
        }

        std::cout << stringList[i] << std::endl;
    }

    puts(" \n");
}

void showSubFormulas(const std::string& formula)
{
    std::string                        formulaEnc      = encapsule(formula);
    std::vector< std::pair<int, int> > parentIndexes   = expressionIndexes(formulaEnc);
    std::vector<std::string>           subformulasList = generateListSub(parentIndexes, formulaEnc);

    printStringList(subformulasList, formula);
}


std::vector<std::string> getMainConective(std::string formula)
{
    // Dado uma formula proposicional corretamente escrita, o conectivo principal é
    // aquele separa duas quantidades iguais de de parenteses de abertura e fechamento
    // (nenhum lado depende do outro e os parenteses abertos encontram o fechamento no mesmo lado).
    // Se eu testar um conectivo, e em cada lado independente nao sobrar a mesma quantidade de parenteses
    // de abertura e fechamento, este não é o principal. Neste caso, há fechamentos na outra parte, logo
    // as partes não são independentes.
    // EX.: (a#b)>(c) | ["(a"] ["b)(c)"]  => '#' NAO É O PRINCIPAL
    // EX.: (a#b)>(c) | ["(a#b)"] ["(c)"] => '>' NAO É O PRINCIPAL

    formula = encapsule(formula);
    formula = desencapsule(formula, TYPE_EXTERNAL);

    if(formula.size() == 3){
        std::vector<std::string> subFormDecomp;
        subFormDecomp.push_back(std::string(1, formula[0]));
        subFormDecomp.push_back(std::string(1, formula[1]));
        subFormDecomp.push_back(std::string(1, formula[2]));

        return subFormDecomp;
    }

    std::vector<std::string> subFormDecomp;
    for(unsigned i=0;i<formula.size();i++)
    {
        if(formula[i] == '&' || formula[i] == '#' || formula[i] == '>' || formula[i] == '~')
        {
            std::stringstream ssEsq;
            int qtdParentEsq[2]{0,0};
            for(unsigned j=0;j<i;j++)
            {
                ssEsq << formula[j];
                if(formula[j] == '('){ qtdParentEsq[0]++; } else
                if(formula[j] == ')'){ qtdParentEsq[1]++; }
            }

            std::stringstream ssDir;
            int qtdParentDir[2]{0,0};
            for(unsigned j=i+1;j<formula.size();j++)
            {
                ssDir << formula[j];
                if(formula[j] == '('){ qtdParentDir[0]++; } else
                if(formula[j] == ')'){ qtdParentDir[1]++; }
            }

            if(qtdParentEsq[0] == qtdParentEsq[1] && qtdParentDir[0] == qtdParentDir[1])
            {
                subFormDecomp.push_back(desencapsule(ssEsq.str(), TYPE_EXTERNAL));
                subFormDecomp.push_back(std::string(1, formula[i]));
                subFormDecomp.push_back(desencapsule(ssDir.str(), TYPE_EXTERNAL));

                return subFormDecomp;
            }
        }
    }

    return subFormDecomp;
}


int showArvore(std::string formula, std::string line_V = "", int direction = DIR_RIGHT, int complexity = 1, int cont = 0){

    // Para caso de formula seja "(a)" ou "a"
    if(formula.size() == 1 && isalnum(formula[0]) && cont == 0)
    {
        std::cout << "   " << formula;
        return 1;
    }

    if(formula.size() == 1 && isalnum(formula.c_str()[0])){

        // O '0' representa a esquerda da negação (0~p);
        // Na minha abstração, (~p) é representado por uma coneção entre '0' e 'p' atraves do conectivo '~';
        // Esta condicional serve para evitar o print de folhas do tipo '0';
        if(formula.c_str()[0] == '0'){ return 0; }

        std::string line_H = (direction == DIR_RIGHT) ? "\u2514" : "\u251c";
        std::cout << line_V << line_H << "\u2500" << "\u2500";

        std::cout << formula << "\n";
        return complexity++;
    }

    std::vector<std::string> subFormDecomp = getMainConective(formula);

    if(line_V != ""){ // Condicional usada para evitar a impressão de linhas antes do conectivo raiz
        std::string line_H = (direction == DIR_RIGHT) ? "\u2514" : "\u251c";
        std::cout << line_V << line_H << "\u2500"<< "\u2500";
    } else {
        std::cout << "   ";
    }
    std::cout << subFormDecomp[1] << "\n";

     if(direction == DIR_RIGHT){
        line_V += "   ";
    } else {
        line_V += "\u2502  ";
    }

    complexity += showArvore(subFormDecomp[0], line_V, DIR_LEFT, 1, ++cont);
    complexity += showArvore(subFormDecomp[2], line_V, DIR_RIGHT, 1, ++cont);

    return complexity;
}


std::string corrigirStr(std::string formula, bool printResult = false){

    // Iniciar a interface da arvore
    printf(" %s%s ", "\u250c", "\u2500");
    printf(" ARVORE SINTATICA \n");
    printf(" %s\n %s  ", "\u2502", "\u2502");
    printf("%s\n", formula.c_str());
    printf(" %s \n %s%s%s \n","\u2502", "\u2514", "\u2500", "\u2510");

    std::string                        formulaEnc      = encapsule(formula);
    std::vector< std::pair<int, int> > parentIndexes   = expressionIndexes(formulaEnc);

    // Procurar por conectivos de negação em casa subformula;
    // [1] Verificar negação nas subformulas com parenteses
    // [2] Verificar negação nos atomos
    // [3] Colocar os atomos sem negação entre parenteses
    // Padrao da string no caso de conectivo de negação: "~p" vira "(0~p)" "p>~(q&s)" vira "

    /// FASE [1] Verificar negação nas subformulas com parenteses
    // Guarda o indice dos parenteses de abertura / fechamento para aberturas com negação
    std::vector< std::pair<int, int> > negativeIndexes;
    for(auto& i : parentIndexes)
    {
        if(formulaEnc[i.first-1] == '~'){
            negativeIndexes.push_back(i);
        }
    }

    std::stringstream ss;
    for(unsigned j=0; j<formulaEnc.size(); j++)
    {
        for(auto& i : negativeIndexes)
        {
            if((int)j==i.first-1) { ss << "[0"; } else
            if((int)j==i.second+1){ ss << "]";  }
        }
        ss << formulaEnc[j];
    }
    formulaEnc = ss.str();


    /// FASE [2] Verificar negação nos atomos
    ss.str(std::string());
    for(unsigned i=0; i<formulaEnc.size(); i++)
    {
        if(formulaEnc[i] == '~')
        {
            //std::cout << formulaEnc[i] << formulaEnc[i+1] << " " << isalpha(formulaEnc[i+1]) << "\n";
            if(isalpha(formulaEnc[i+1])){
                ss << "{0" << formulaEnc[i] << formulaEnc[i+1] << "}";
                i += 2;
            }
        }
        ss << formulaEnc[i];
    }
    formulaEnc = ss.str();


    /// FASE [3] Colocar os atomos sem negação entre parenteses
    ss.str(std::string());
    for(unsigned i=0; i<formulaEnc.size(); i++)
    {
        if(formulaEnc[i+1] == '>' || formulaEnc[i+1] == '#' || formulaEnc[i+1] == '&')
        {
            if(isalpha(formulaEnc[i]) && !isalpha(formulaEnc[i+2]))
            {
                ss << '{' << formulaEnc[i] << '}';
            } else
            if(!isalpha(formulaEnc[i]) && isalpha(formulaEnc[i+2]))
            {
                ss << formulaEnc[i] << formulaEnc[i+1]  << '{' << formulaEnc[i+2] << '}';
                i+=2;
            } else
            {
                ss << formulaEnc[i];

            }
        }
        else
        {
            ss << formulaEnc[i];
        }
    }
    formulaEnc = ss.str();

    if(printResult){ std::cout << "   [CONVERTIDO] " << desencapsule(ss.str(), TYPE_EXTERNAL)  << "\n\n";}

    // Substituir "{}" e "[]" por "()"
    ss.str(std::string());
    for(auto& i : formulaEnc)
    {
        if(i == '{' || i == '[')
        {
            ss << '(';
        } else
        if(i == '}' || i == ']')
        {
            ss << ')';
        } else
        {
            ss << i;
        }
    }

    if(printResult){ std::cout << "   [CONV.FINAL] " << ss.str()  << "\n\n";}

    return desencapsule(ss.str(), TYPE_EXTERNAL);
}


void showComplexity(const int& value)
{
    printf("\n\n   ");
    printf("  COMPLEXIDADE: %d  ", value);
    printf("\n\n");
}

std::string getFormula()
{
    initInterface();

    std::string f = "";
    std::cout << "    ";
    std::cout << " Digite a formula: ";
    std::cout << " ";
    std::cin >> f;

    return f;
}



int main(){

    for(;;){
        std::string formula = getFormula(); // "((a#(b&c))>d)";// (p#~q)>(r&~q)"; // "(p&(k#q))>((~j>c)&t)";  //"((p&q)&((x&y)#s))>(~(v#k))";

        deleteSpaces(formula);

        if(!isValid(formula)){
            std::cout << " Inserir outra formula? [sn] ";
            std::string c;
            std::cin >> c;
            if(c[0] != 's' && c[0] != 'S'){ break; }
            else { system("clear"); continue; }
        };
        showSubFormulas(formula);

        std::string formula_convertida = corrigirStr(formula, 0);
        int complexity = showArvore(formula_convertida);
        showComplexity(complexity);

        std::cout << "\n Inserir outra formula? [sn] ";
        std::string c;
        std::cin >> c;
        if(c[0] != 's' && c[0] != 'S'){ break; } else { system("clear"); }

    }

    return 0;
}
