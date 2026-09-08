/// Generalized pratt parser trait.
pub trait Parser: Sized {
    type AstNode;

    // ================================================================================
    // Required methods
    // ================================================================================

    /// Construct the ast with the given context.
    ///
    /// Here, context is that the ast node already parsed so far. This method
    /// specifies how a node should be merged to given tree.
    fn parse_with_ctx(&mut self, ctx: &mut Option<Self::AstNode>) -> anyhow::Result<()>;

    /// Parses the token stream and get minimal, and proper expression
    /// at the head of the rest token stream.
    ///
    /// For example,
    ///
    /// ```plaintext
    /// 1 + 2 * 3 -> 1
    /// (1 + 2) * 3 -> (1 + 2)
    /// ```
    fn next_term(&mut self) -> anyhow::Result<Self::AstNode>;

    /// Returns the pointer of ast node that next term will be merged into.
    fn cursor<'a>(&self, ctx: &'a mut Self::AstNode) -> &'a mut Self::AstNode;

    // ================================================================================
    // Provided methods
    // ================================================================================

    fn parse(mut self) -> anyhow::Result<Self::AstNode> {
        let mut ctx = None;
        self.parse_with_ctx(&mut ctx)?;
        ctx.ok_or(anyhow::anyhow!("No tokens provided"))
    }
}
