/// SysY standard library definitions.
use crate::base::Type;

thread_local! {
    pub static SYSY_LIB: Vec<(&'static str, Type)> = vec![
        (
            "getint",
            Type::Function {
                return_type: Box::new(Type::Int),
                param_types: vec![],
            },
        ),
        (
            "getfloat",
            Type::Function {
                return_type: Box::new(Type::Float),
                param_types: vec![],
            },
        ),
        (
            "getch",
            Type::Function {
                return_type: Box::new(Type::Int),
                param_types: vec![],
            },
        ),
        (
            "getarray",
            Type::Function {
                return_type: Box::new(Type::Int),
                param_types: vec![Type::Pointer {
                    base: Box::new(Type::Int),
                }],
            },
        ),
        (
            "getfarray",
            Type::Function {
                return_type: Box::new(Type::Int),
                param_types: vec![Type::Pointer {
                    base: Box::new(Type::Float),
                }],
            },
        ),
        (
            "putint",
            Type::Function {
                return_type: Box::new(Type::Void),
                param_types: vec![Type::Int],
            },
        ),
        (
            "putfloat",
            Type::Function {
                return_type: Box::new(Type::Void),
                param_types: vec![Type::Float],
            },
        ),
        (
            "putch",
            Type::Function {
                return_type: Box::new(Type::Void),
                param_types: vec![Type::Int],
            },
        ),
        (
            "putarray",
            Type::Function {
                return_type: Box::new(Type::Void),
                param_types: vec![
                    Type::Int,
                    Type::Pointer {
                        base: Box::new(Type::Int),
                    },
                ],
            },
        ),
        (
            "putfarray",
            Type::Function {
                return_type: Box::new(Type::Void),
                param_types: vec![
                    Type::Int,
                    Type::Pointer {
                        base: Box::new(Type::Float),
                    },
                ],
            },
        ),
        (
            "putf",
            Type::Function {
                return_type: Box::new(Type::Void),
                param_types: vec![
                    Type::Pointer {
                        base: Box::new(Type::Char),
                    },
                    /*only store the string type, since the trailing params are dynamic according to the format string*/
                ],
            },
        ),
        (
            "starttime",
            Type::Function {
                return_type: Box::new(Type::Void),
                param_types: vec![],
            },
        ),
        (
            "stoptime",
            Type::Function {
                return_type: Box::new(Type::Void),
                param_types: vec![],
            },
        ),
    ];
}
