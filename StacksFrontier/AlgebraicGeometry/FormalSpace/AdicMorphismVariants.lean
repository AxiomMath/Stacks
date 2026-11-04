module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicMorphism
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautMorphismRepresentabilityVariants

/-!
# Variants of the results of `StacksFrontier.AlgebraicGeometry.FormalSpace.AdicMorphism`

A primed name `X'` is a variant of the declaration `X` of
`StacksFrontier.AlgebraicGeometry.FormalSpace.AdicMorphism`.

## Main results

* `isAdicOnEveryAffineEtaleDiagram_of_isRepresentable'`: a morphism of locally countably indexed
  formal algebraic spaces which is representable by algebraic spaces is adic on every chart in
  `WAdm^{adic*}`, given the hypotheses of Stacks 0ANK.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Section 0AQ2, condition (1) implies condition (2).** A morphism of locally countably
indexed formal algebraic spaces over `S` which is representable by algebraic spaces has every
one of its chart maps in `WAdm^{adic*}` adic; this is the matching the section makes, and it is
the content of Definition 0AQ3's reference to the discussion.

Stacks 0ANK turns representability into the taut reading of the chart condition at the
countably indexed weakly admissible class, which contains `WAdm^{adic*}`; the footnote then
turns taut into adic. The three hypotheses `h0AN5`, `h0AQ0` and `h0AN4` are
those of Stacks 0ANK in this library and are passed straight through. -/
theorem isAdicOnEveryAffineEtaleDiagram_of_isRepresentable' {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (h0AN5 : ∀ {U V : FppfSheaf B S hS} (t : U ⟶ V),
      IsAffineFormalAlgebraicSpace B S hS U → IsAffineFormalAlgebraicSpace B S hS V →
      IsCountablyIndexed B S hS U → IsCountablyIndexed B S hS V →
      (Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS t.hom ↔
        HasPropertyOnAffineChartMap B S hS TopologicalRing.IsCountablyWeaklyAdmissible
          TautChartProperty t))
    (h0AQ0 : ∀ {A A' A'' : FppfSheaf B S hS} (s : A ⟶ A') (r : A' ⟶ A''),
      IsFormalAlgebraicSpace B S hS A → IsFormalAlgebraicSpace B S hS A' →
      IsFormalAlgebraicSpace B S hS A'' →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (s ≫ r).hom →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS s.hom)
    (h0AN4 : ∀ (I : Type (u + 1)) (U W : I → FppfSheaf B S hS) (a : ∀ i, U i ⟶ X)
      (b : ∀ i, W i ⟶ Y) (t : ∀ i, U i ⟶ W i), IsAffineEtaleCover B S hS U a →
      (∀ i, IsAffineFormalAlgebraicSpace B S hS (W i)) →
      (∀ i, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (b i).hom) →
      (∀ i, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (t i).hom) →
      (∀ i, a i ≫ f = t i ≫ b i) →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom) :
    IsAdicOnEveryAffineEtaleDiagram B S hS f := by
  have htaut : IsTautOnEveryAffineEtaleDiagram B S hS f :=
    ((isTaut_tfae_isRepresentableByAlgebraicSpaces_of_cancellation B S hS f hX hY h0AN5 h0AQ0
      h0AN4).out 4 1).mp hf
  refine (isAdicOnEveryAffineEtaleDiagram_iff_isTautAdicStar B S hS f).mpr ?_
  intro U V a b t hU hV ha hb hsq A R _ _ _ _ _ _ _ _ hCA hCR hA D E eU eV g hg
  exact htaut U V a b t hU hV ha hb hsq A R hCA.1 hCR.1 hA D E eU eV g hg

end AlgebraicGeometry.FormalSpace

end
