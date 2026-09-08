use eqn_core::symbol::Symbol;
use eqn_parser::Parser;

use crate::monoid::{Monoid, MonoidExpr};

pub(super) enum MonoidExprToken<'a> {
    Symbol(&'a str),
    Op,
}

pub(super) struct MonoidExprTokenizer<'s> {
    src: &'s str,
    pos: usize,
}

impl<'s> MonoidExprTokenizer<'s> {
    pub(super) fn new(src: &'s str) -> Self {
        Self { src, pos: 0 }
    }
}

impl<'s> Iterator for MonoidExprTokenizer<'s> {
    type Item = MonoidExprToken<'s>;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

pub(super) struct MonoidParser<I, M> {
    token_iterator: I,
    _marker: std::marker::PhantomData<M>,
}

impl<I, M> MonoidParser<I, M> {
    pub fn new(token_iterator: I) -> Self {
        Self {
            token_iterator,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<'s, I, M> eqn_parser::Parser for MonoidParser<I, M>
where
    I: Iterator<Item = MonoidExprToken<'s>>,
    M: Monoid,
{
    type AstNode = MonoidExpr<M>;

    fn parse_with_ctx(&mut self, ctx: &mut Option<MonoidExpr<M>>) -> anyhow::Result<()> {
        while let Some(t) = self.token_iterator.next() {
            match t {
                MonoidExprToken::Op => match ctx.as_mut() {
                    Some(MonoidExpr::Op(terms)) => {
                        terms.push(self.next_term()?);
                    }
                    Some(me) => *me = MonoidExpr::Op(vec![me.clone(), self.next_term()?]),
                    None => anyhow::bail!("Expression start with operator"),
                },
                MonoidExprToken::Symbol(s) => {
                    *ctx = Some(MonoidExpr::Symbol(Symbol::new(s)));
                }
            }
        }

        Ok(())
    }

    fn next_term(&mut self) -> anyhow::Result<MonoidExpr<M>> {
        match self.token_iterator.next() {
            Some(MonoidExprToken::Op) => anyhow::bail!("Expected a term, got operator"),
            Some(MonoidExprToken::Symbol(s)) => Ok(MonoidExpr::Symbol(Symbol::new(s))),
            None => anyhow::bail!("Expected a term, got eof"),
        }
    }

    fn cursor<'a>(&self, ctx: &'a mut MonoidExpr<M>) -> &'a mut MonoidExpr<M> {
        ctx
    }
}
