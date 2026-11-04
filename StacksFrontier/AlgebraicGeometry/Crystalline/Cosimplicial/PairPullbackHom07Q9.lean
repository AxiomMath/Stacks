module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamZigzag07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.EnvelopeBaseChangeRows
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.PairBaseChangeConnection07Q9

/-!
# The base change of a cosimplicial pair of base-change connections

Let `g : E ⟶ E'` be a morphism of cosimplicial divided power algebras and `(M(•), ∇, β)` the data
of `Crystalline.CosimplicialCompletedModule.baseChangePair` over `E`.  Its base change along `g`
(`Crystalline.CosimplicialCompletedModule.pullback07Q9`, with the connection
`pullbackNabla07Q9` and the identifications `pullbackBeta07Q9`) satisfies the hypotheses of
`baseChangePair` over `E'`, and the maps `m ↦ 1 ⊗ m` form a morphism of cosimplicial pairs over
`g` (`pairPullbackHom07Q9`).  In [Stacks, Tag 07Q9] this is the comparison of the double complex of
the crystal over the envelope of `W` with that of its pullback over the envelope of `f⁻¹(W)`.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public noncomputable section

open CategoryTheory Simplicial DividedPowers
open scoped TensorProduct

universe u

namespace Crystalline.CosimplicialCompletedModule

variable {A : Type u} [CommRing A] {E E' : CosimplicialDPAlgebra.{u, u} A} {p : ℕ}
  (V : CosimplicialCompletedModule.{u, u, u} E p) (g : E.Hom E')
  (nabla : CompletedConnection p (E.completedRing p 0) (E.forms p 1 0) (E.differential p 0)
    (V.carrier 0))
  (beta : ∀ b : ℕ, letI := E.coprojectionAlgebra p b
    CompletedConnection.baseChangeCarrier p (E.completedRing p 0) (E.completedRing p b)
      (V.carrier 0) ≃ₗ[E.completedRing p b] V.carrier b)
  (hbeta : ∀ (b : ℕ) (x : E.completedRing p b) (m : V.carrier 0),
    letI := E.coprojectionAlgebra p b
    beta b (AdicCompletion.of (pAdicIdeal (A := E.completedRing p b) p)
        (E.completedRing p b ⊗[E.completedRing p 0] V.carrier 0) (x ⊗ₜ[E.completedRing p 0] m)) =
      x • V.map (CosimplicialDPAlgebra.coprojection b) m)
  (hδ : ∀ x : V.carrier 0,
    V.baseChangeConnection nabla beta 1 (V.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) x) =
      V.tensorMap (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) 1 (nabla x))
  (hint : CompletedDeRham.HasIntegrableConnection p (E.completedRing p 0)
    (fun a => E.forms p a 0) (E.wedge p 0) (E.deRham p 0) (V.carrier 0) nabla
    (E.isGradedLeibniz p 0))

/-- The modules of the pair of base-change connections are those of the cosimplicial module, so
they are `p`-adically complete when those are. -/
instance baseChangePair_isAdicComplete07Q9
    [∀ b, IsAdicComplete (pAdicIdeal (A := E.completedRing p b) p) (V.carrier b)] (b : ℕ) :
    IsAdicComplete (pAdicIdeal (A := E.completedRing p b) p)
      ((V.baseChangePair nabla beta hbeta hδ hint).carrier b) :=
  inferInstanceAs (IsAdicComplete (pAdicIdeal (A := E.completedRing p b) p) (V.carrier b))

/-- **The base change along `g` of the cosimplicial pair of base-change connections**: the pair
`baseChangePair` of the base-changed data `(M'(•), ∇', β')` over `E'`. -/
abbrev pullbackPair07Q9 : CosimplicialCompletedPair.{u, u, u} E' p :=
  (V.pullback07Q9 g).baseChangePair (V.pullbackNabla07Q9 g nabla) (V.pullbackBeta07Q9 g beta)
    (V.pullbackBeta07Q9_tmul g beta hbeta)
    (V.pullback07Q9_horizontal_coface g nabla beta hbeta hδ)
    (V.pullbackNabla07Q9_integrable g nabla hint)

/-- **The morphism of cosimplicial pairs `M(•) ⟶ M'(•)`, `m ↦ 1 ⊗ m`, over `g`**: it commutes
with the transition maps (`pullbackApp07Q9_naturality`) and is horizontal for the base-change
connections (`baseChangeConnection_pullbackApp07Q9`). -/
def pairPullbackHom07Q9 :
    CosimplicialCompletedPair.Hom g (V.baseChangePair nabla beta hbeta hδ hint)
      (V.pullbackPair07Q9 g nabla beta hbeta hδ hint) where
  app b := V.pullbackApp07Q9 g b
  naturality φ x := V.pullbackApp07Q9_naturality g φ x
  nabla_app b x := V.baseChangeConnection_pullbackApp07Q9 g nabla beta hbeta b x

end Crystalline.CosimplicialCompletedModule
