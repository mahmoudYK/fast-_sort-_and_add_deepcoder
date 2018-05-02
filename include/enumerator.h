#include <iostream>
#include <sstream>
#include <vector>
#include <list>
#include <stack>
#include "dsl/ast.h"
#include "dsl/type.h"
#include "dsl/utils.h"
#include <iomanip>
#include "find-program.h"

#pragma once

using namespace std;

extern std::list<dsl::Program> precomputed_program;
extern bool should_remove;

struct Restriction {
    int min_length;
    int max_length;
    std::vector<dsl::Function> functions;
    std::vector<dsl::PredicateLambda> predicates;
    std::vector<dsl::OneArgumentLambda> one_argument_lambda;
    std::vector<dsl::TwoArgumentsLambda> two_arguments_lambda;
};

template <class CalcInformation, class Process, class Information>
bool enumerate(const Restriction &restriction, const CalcInformation & calc_information, const Process &process,
         const dsl::Program &program, const dsl::TypeEnvironment &tenv, const Information &info) {
    for (const auto &f: restriction.functions) {
        auto arg_types = dsl::get_signature(f).arguments_type;
        auto as = std::vector<std::vector<dsl::Argument>>(arg_types.size());
        for (auto i = 0; i < arg_types.size(); i++) {
            auto t = arg_types[i];
            switch (t) {
                case dsl::Type::PredicateLambda:
                    as[i].reserve(restriction.predicates.size());
                    for (const auto& p: restriction.predicates) {
                        as[i].push_back(p);
                    }
                    break;
                case dsl::Type::OneArgumentLambda:
                    as[i].reserve(restriction.one_argument_lambda.size());
                    for (const auto& l: restriction.one_argument_lambda) {
                        as[i].push_back(l);
                    }
                    break;
                case dsl::Type::TwoArgumentsLambda:
                    as[i].reserve(restriction.two_arguments_lambda.size());
                    for (const auto& l: restriction.two_arguments_lambda) {
                        as[i].push_back(l);
                    }
                    break;
                case dsl::Type::Integer:
                    for (const auto &var: tenv) {
                        if (var.second == dsl::Type::Integer) {
                            as[i].push_back(dsl::Argument(var.first));
                        }
                    }
                    break;
                case dsl::Type::List:
                    for (const auto &var: tenv) {
                        if (var.second == dsl::Type::List) {
                            as[i].push_back(dsl::Argument(var.first));
                        }
                    }
                    break;
                default:
                    break;
            }
        }

        auto s = std::stack<std::vector<dsl::Argument>>();
        if (as.size() == 0) {
            auto p = program;
            auto s = dsl::Statement(p.size(), f, {});
            p.push_back(s);
            auto new_tenv = dsl::check(s, tenv);
            auto new_info = calc_information(p, info);

            if (new_tenv) {
                if (p.size() >= restriction.min_length && p.size() <= restriction.max_length) {
                    if (!process(p, info)) {
                        // Finish enumeration
                        return false;
                    }
                }

                if (p.size() < restriction.max_length) {
                    if(!enumerate(restriction, calc_information, process, p, new_tenv.value(), new_info)) {
                        return false;
                    }
                }
            }
        } else {
            for (auto it = as[0].rbegin(); it != as[0].rend(); ++it) {
                auto a = *it;
                s.push({a});
            }

            while (!s.empty()) {
                auto args = s.top();
                s.pop();

                if (args.size() == arg_types.size()) {
                    auto p = program;
                    auto s = dsl::Statement(p.size(), f, args);
                    p.push_back(s);
                    auto new_tenv = dsl::check(s, tenv);
                    auto new_info = calc_information(p, info);

                    if (new_tenv) {
                        if (p.size() >= restriction.min_length && p.size() <= restriction.max_length) {
                        	//cerr << "check program p, p now is:" <<endl;
                        	//cerr << p << endl;
                        	if(!should_remove){
                                //auto program_to_erase = std::find(precomputed_program.begin(), precomputed_program.end(), p);
                        	//if( program_to_erase == precomputed_program.end()){
                        	if(precomputed_program.front() != p){
                                
                                if (!process(p, new_info)) {
                                // Finish enumeration
                                return false;
                            }
                        	}
                        	else{
                        		//cerr <<"program will be erased from graph: " << endl<< p << endl;
                        		//precomputed_program.erase(precomputed_program.begin()/*program_to_erase*/);
                                         precomputed_program.pop_front();
                        	}
                        }
                       
                        else{
                         if (!process(p, new_info)) {
                                // Finish enumeration
                                return false;
                            }
                        }
                         
                       }

                        if (p.size() < restriction.max_length) {
                            if (!enumerate(restriction, calc_information, process, p, new_tenv.value(), new_info)) {
                                return false;
                            }
                        }
                    }
                } else {
                    for (auto it = as[args.size()].rbegin(); it != as[args.size()].rend(); ++it) {
                        auto a = *it;
                        auto new_args = args;
                        new_args.push_back(a);
                        s.push(new_args);
                    }
                }
            }
        }
    }
    return true;
}

template <class CalcInformation, class Process, class Information>
void enumerate(const Restriction &restriction, const CalcInformation & calc_information, const Process &process,
         const Information &initial_info) {
    enumerate(restriction, calc_information, process, {}, {}, initial_info);
}

template <class CalcInformation, class Process, class Information>
void enumerate(const Restriction &restriction, const CalcInformation & calc_information, const Process &process,
         const dsl::Program& initial_program, const Information &initial_info) {
    auto tenv = dsl::TypeEnvironment();
    for (const auto& s: initial_program) {
        auto tmp = dsl::check(s, tenv);
        if (!tmp) {
            return ;
        }
        tenv = tmp.value();
    }

    enumerate(restriction, calc_information, process, initial_program, tenv, initial_info);
}
