module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenSchemeLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactDenseOpenScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints

/-!
# Stacks 0GUL: the conclusions, and the upgrade from étale to finite étale

Stacks 0GUL asserts, for a quasi-compact and quasi-separated algebraic space `X` over a scheme
`S` whose space of points `|X|` has **finitely many irreducible components**, that

1. there is a surjective integral morphism `Y ⟶ X` with `Y` a scheme which is finite étale over
   a quasi-compact dense open `U ⊆ X`, and that
2. given a surjective étale morphism `V ⟶ X` the cover `Y` may be chosen so that every point of
   `Y` has an open neighbourhood `W ⊆ Y` with `W ⟶ X` factoring through `V`.

This file states the two conclusions and proves the steps of the source proof which turn a
cover *étale* over a dense open into one *finite étale* over a *quasi-compact* dense open. The
induction producing such a cover, and the theorem carrying `@[stacks 0GUL]`, are in
`StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverEtaleInduction`.

## Main definitions

* `AlgebraicGeometry.Space.IsIntegralSchemeCoverFiniteEtaleOverDenseOpen` is the conclusion of
  clause (1) for a named cover and a named open subspace.
* `AlgebraicGeometry.Space.ExistsIntegralSchemeCoverFiniteEtaleOverDenseOpen` is clause (1),
  and `AlgebraicGeometry.Space.ExistsIntegralSchemeCoverRefining` is clause (2) for one
  prescribed cover.
* `AlgebraicGeometry.Space.ExistsIntegralSchemeCoverEtaleRefining` is the form in which the
  induction produces the cover: the open subspace is asked only to have dense point set, and
  the cover only to be étale over it.

## Main results

* `AlgebraicGeometry.Space.exists_isOpenSubspace_isQuasiCompactSpace_dense_factorization`
  shrinks an open subspace with dense point set to a quasi-compact one with dense point set
  ("of course, we see that `U` is quasi-compact and dense in `X`"); `X` is decent (Stacks 03JX),
  its open subspace has finitely many irreducible components, and Stacks 086U in the
  quasi-compact form
  `AlgebraicGeometry.Space.exists_compactSpace_isOpenImmersion_denseRange_of_isDecentSpace`
  gives the quasi-compact dense open.
* `AlgebraicGeometry.Space.existsIntegralSchemeCoverRefining_of_etaleRefining` upgrades the
  étale form to the conclusion of the tag: étaleness survives the shrinking, and finiteness over
  the shrunken open is automatic, an integral morphism locally of finite type being finite
  (Stacks 0414).
* `AlgebraicGeometry.Space.existsIntegralSchemeCoverRefining_of_comp_chart` and
  `AlgebraicGeometry.Space.existsIntegralSchemeCoverFiniteEtaleOverDenseOpen_of_refining_id`
  are the source's first two reductions: a cover refining a chart composed with `p` refines
  `p`, and clause (1) is clause (2) at the identity.

## References

* [Stacks Project, Tag 0GUL](https://stacks.math.columbia.edu/tag/0GUL)
* [Stacks Project, Tag 086U](https://stacks.math.columbia.edu/tag/086U)
* [Stacks Project, Tag 0414](https://stacks.math.columbia.edu/tag/0414)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-! ### The two conclusions -/

/-- **The conclusion of clause (1) of Stacks 0GUL for a named cover.** The morphism
`f : h_Y ⟶ X` from the presheaf represented by an object `Y` of the big fppf site — a scheme
over `S` — is surjective and integral, and `U` is a quasi-compact open subspace of `X` whose
point set is dense in `|X|`, over which `f` is finite and étale. -/
def IsIntegralSchemeCoverFiniteEtaleOverDenseOpen
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (Y : BigFppfOver B S hS)
    (f : yoneda.obj Y ⟶ X) (U : Subfunctor X) : Prop :=
  IsSurjective B S hS f ∧ IsIntegralHom B S hS f ∧
    IsOpenSubspace B S hS U ∧ IsQuasiCompactSpace B S hS U.toFunctor ∧
    Dense (Set.range (pointsMap B S hS U.toFunctor U.ι)) ∧
    IsFinite B S hS (pullback.fst U.ι f) ∧ IsEtale B S hS (pullback.fst U.ι f)

/-- **Clause (1) of Stacks 0GUL.** There is a surjective integral morphism to `X` from the
presheaf represented by an object of the big fppf site — a scheme over `S` — which is finite
étale over a quasi-compact dense open subspace of `X`. -/
def ExistsIntegralSchemeCoverFiniteEtaleOverDenseOpen
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∃ (Y : BigFppfOver B S hS) (f : yoneda.obj Y ⟶ X) (U : Subfunctor X),
    IsIntegralSchemeCoverFiniteEtaleOverDenseOpen B S hS Y f U

/-- **Clause (2) of Stacks 0GUL for one prescribed cover `p`.** A cover as in clause (1) can be
chosen which in addition factors through `p` on a representable open subspace neighbourhood of
every one of its points. -/
def ExistsIntegralSchemeCoverRefining
    {X V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : V ⟶ X) : Prop :=
  ∃ (Y : BigFppfOver B S hS) (f : yoneda.obj Y ⟶ X) (U : Subfunctor X),
    IsIntegralSchemeCoverFiniteEtaleOverDenseOpen B S hS Y f U ∧
    FactorsZariskiLocallyThrough B S hS p Y f

/-- **The form of clause (2) which the induction produces.** The open subspace is asked only to
have dense point set — not to be quasi-compact — and the cover is asked only to be étale over
it, not finite; `AlgebraicGeometry.Space.existsIntegralSchemeCoverRefining_of_etaleRefining`
upgrades it. -/
def ExistsIntegralSchemeCoverEtaleRefining
    {X V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : V ⟶ X) : Prop :=
  ∃ (Y : BigFppfOver B S hS) (f : yoneda.obj Y ⟶ X) (U : Subfunctor X),
    (IsSurjective B S hS f ∧ IsIntegralHom B S hS f ∧
      IsOpenSubspace B S hS U ∧
      Dense (Set.range (pointsMap B S hS U.toFunctor U.ι)) ∧
      IsEtale B S hS (pullback.fst U.ι f)) ∧
    FactorsZariskiLocallyThrough B S hS p Y f

/-! ### Shrinking the dense open -/

/-- The base change of a multiplicative property of schemes to `BigFppfOver` contains identities. -/
private theorem containsIdentities_inverseImage_toScheme
    (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).ContainsIdentities := by
  have := MorphismProperty.IsMultiplicative.toContainsIdentities (W := P)
  infer_instance

/-- The base change of a property of schemes respecting isomorphisms to `BigFppfOver` does too. -/
private theorem respectsIso_inverseImage_toScheme
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).RespectsIso :=
  MorphismProperty.RespectsIso.inverseImage _ (BigFppfOver.toScheme B S hS)

/-- **A base change along a composite is a base change of a base change.** If `f` is étale over
the open subspace `U` then it is étale over any `U'` mapping to `U` over `X`. -/
theorem isEtale_pullback_fst_comp
    {X Z U' U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU' : IsAlgebraicSpace B S hS U') (hU : IsAlgebraicSpace B S hS U)
    (hX : IsAlgebraicSpace B S hS X) (hZ : IsAlgebraicSpace B S hS Z)
    (j : U' ⟶ U) (ι : U ⟶ X) (ι' : U' ⟶ X) (hι : j ≫ ι = ι') (f : Z ⟶ X)
    (h : IsEtale B S hS (pullback.fst ι f)) :
    IsEtale B S hS (pullback.fst ι' f) := by
  subst hι
  have := containsIdentities_inverseImage_toScheme B S hS (@AlgebraicGeometry.Etale.{u})
  have hP : IsAlgebraicSpace B S hS (pullback ι f) :=
    isAlgebraicSpace_pullback B S hS ι f hU hZ hX
  have h1 : IsEtale B S hS (pullback.fst j (pullback.fst ι f)) :=
    isEtale_pullback_fst B S hS hU' hU hP j (pullback.fst ι f) h
  have hiso : IsEtale B S hS (pullbackRightPullbackFstIso ι f j).inv :=
    isEtale_of_presheaf_etale B S hS (MorphismProperty.presheaf_of_isIso _ _)
  have hcomp := isEtale_comp B S hS hiso h1
  rwa [pullbackRightPullbackFstIso_inv_fst] at hcomp

/-- **An open subspace with dense point set of a quasi-separated algebraic space with finitely
many irreducible components contains a quasi-compact one with dense point set.**

The space is decent (Stacks 03JX), hence so is the open subspace, and the open subspace has
finitely many irreducible components because the point map of an open immersion is an open
embedding; so Stacks 086U, in the quasi-compact form
`AlgebraicGeometry.Space.exists_compactSpace_isOpenImmersion_denseRange_of_isDecentSpace`,
gives a quasi-compact dense open *subscheme* of it, whose image in `X` is the subspace
wanted. -/
theorem exists_isOpenSubspace_isQuasiCompactSpace_dense_factorization
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hcomp : (irreducibleComponents (points B S hS X)).Finite)
    (U : Subfunctor X) (hU : IsOpenSubspace B S hS U)
    (hUdense : Dense (Set.range (pointsMap B S hS U.toFunctor U.ι))) :
    ∃ (U' : Subfunctor X) (j : U'.toFunctor ⟶ U.toFunctor),
      IsOpenSubspace B S hS U' ∧ IsQuasiCompactSpace B S hS U'.toFunctor ∧
      Dense (Set.range (pointsMap B S hS U'.toFunctor U'.ι)) ∧
      j ≫ U.ι = U'.ι := by
  classical
  have := containsIdentities_inverseImage_toScheme B S hS (@AlgebraicGeometry.Surjective.{u})
  have := respectsIso_inverseImage_toScheme B S hS (@AlgebraicGeometry.Surjective.{u})
  have := containsIdentities_inverseImage_toScheme B S hS (@AlgebraicGeometry.Etale.{u})
  have hdec : IsDecentSpace B S hS X :=
    isDecentSpace_of_isAbsolutelyQuasiSeparated B S hS X hX hXqs
  have hUdec : IsDecentSpace B S hS U.toFunctor :=
    isDecentSpace_of_isOpenSubspace B S hS hX hdec hU
  have hemb : Topology.IsOpenEmbedding (pointsMap B S hS U.toFunctor U.ι) :=
    isOpenEmbedding_pointsMap_ι B S hS hU
  have hUcomp : (irreducibleComponents (points B S hS U.toFunctor)).Finite :=
    finite_irreducibleComponents_of_isOpenEmbedding _ hemb hcomp
  obtain ⟨A, u, hAcomp, hu, hudense⟩ :=
    exists_compactSpace_isOpenImmersion_denseRange_of_isDecentSpace B S hS hU.1 hUdec hUcomp
  set b : yoneda.obj A ⟶ X := u ≫ U.ι with hbdef
  have hb : IsOpenImmersion B S hS b := isOpenImmersion_comp B S hS _ _ hu hU.2
  have hmono : Mono b := mono_of_isOpenImmersion B S hS b hb
  set e := rangeIsoOfIsOpenImmersion A b hb with hedef
  have hetop : e.hom ≫ (Subfunctor.range b).ι = b := Subfunctor.toRange_ι b
  have hbdense : Dense (Set.range (pointsMap B S hS (yoneda.obj A) b)) := by
    rw [hbdef, pointsMap_comp, Set.range_comp]
    exact DenseRange.dense_image hUdense (continuous_pointsMap B S hS U.ι) hudense
  refine ⟨Subfunctor.range b, e.inv ≫ u, isOpenSubspace_range_of_isOpenImmersion A b hb,
    ⟨A, e.hom, hAcomp, MorphismProperty.presheaf_of_isIso _ _,
      isEtale_of_presheaf_etale B S hS (MorphismProperty.presheaf_of_isIso _ _)⟩, ?_, ?_⟩
  · rw [range_pointsMap_ι_range B S hS b]
    exact hbdense
  · rw [Category.assoc, ← hbdef, Iso.inv_comp_eq]
    exact hetop.symm

/-! ### Upgrading the weakened conclusion -/

/-- **An integral cover étale over a dense open subspace is finite étale over a quasi-compact
dense open subspace.** The open subspace is shrunk to a quasi-compact one by
`AlgebraicGeometry.Space.exists_isOpenSubspace_isQuasiCompactSpace_dense_factorization`,
étaleness survives the shrinking because it is a base change, and finiteness over the
shrunken open is then automatic: the base change of the cover is integral and, being étale,
locally of finite type, and an integral morphism locally of finite type is finite
(Stacks 0414). -/
theorem existsIntegralSchemeCoverRefining_of_etaleRefining
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hcomp : (irreducibleComponents (points B S hS X)).Finite)
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : V ⟶ X)
    (h : ExistsIntegralSchemeCoverEtaleRefining B S hS p) :
    ExistsIntegralSchemeCoverRefining B S hS p := by
  obtain ⟨Y, f, U, ⟨hfsurj, hfint, hUopen, hUdense, hfet⟩, hloc⟩ := h
  obtain ⟨U', j, hU'open, hU'qc, hU'dense, hju⟩ :=
    exists_isOpenSubspace_isQuasiCompactSpace_dense_factorization B S hS hZ hX hXqs hcomp U
      hUopen hUdense
  have hY : IsAlgebraicSpace B S hS (yoneda.obj Y) := isAlgebraicSpace_yoneda B S hS Y
  have hfet' : IsEtale B S hS (pullback.fst U'.ι f) :=
    isEtale_pullback_fst_comp B S hS hU'open.1 hUopen.1 hX hY j U.ι U'.ι hju f hfet
  have hffin : IsFinite B S hS (pullback.fst U'.ι f) :=
    isFinite_of_isIntegralHom_of_isLocallyOfFiniteType B S hS _
      (isAlgebraicSpace_pullback B S hS U'.ι f hU'open.1 hY hX) hU'open.1
      (isIntegralHom_of_isPullback B S hS (IsPullback.of_hasPullback U'.ι f).flip hfint)
      (isLocallyOfFiniteType_of_isEtale B S hS hU'open.1 hfet')
  exact ⟨Y, f, U', ⟨hfsurj, hfint, hU'open, hU'qc, hU'dense, hffin, hfet'⟩, hloc⟩

/-! ### The two reductions of the source proof -/

/-- **The first reduction of the proof of Stacks 0GUL: "choose a surjective étale morphism
`V' → V` where `V'` is a scheme; it is clear that we may replace `V` by `V'`".** A cover refining
the composite `c ≫ p` of a chart `c : h_{V₀} ⟶ V` with `p` refines `p`: a factorization through
the chart composes with it to one through `p`. -/
theorem existsIntegralSchemeCoverRefining_of_comp_chart
    {X V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : V ⟶ X) (V₀ : BigFppfOver B S hS)
    (c : yoneda.obj V₀ ⟶ V) (h : ExistsIntegralSchemeCoverRefining B S hS (c ≫ p)) :
    ExistsIntegralSchemeCoverRefining B S hS p := by
  obtain ⟨Y, f, U, hdata, hloc⟩ := h
  refine ⟨Y, f, U, hdata, fun y => ?_⟩
  obtain ⟨W, hWopen, hWrep, hymem, g, hg⟩ := hloc y
  exact ⟨W, hWopen, hWrep, hymem, g ≫ c, by rw [hg, Category.assoc]⟩

/-- **The second sentence of the proof of Stacks 0GUL: "part (1) is the special case of part (2)
where `V = X`".** A cover refining the identity of `X` is a cover as in clause (1), the local
factorizations being discarded. -/
theorem existsIntegralSchemeCoverFiniteEtaleOverDenseOpen_of_refining_id
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h : ExistsIntegralSchemeCoverRefining B S hS (𝟙 X)) :
    ExistsIntegralSchemeCoverFiniteEtaleOverDenseOpen B S hS X := by
  obtain ⟨Y, f, U, hdata, -⟩ := h
  exact ⟨Y, f, U, hdata⟩

end AlgebraicGeometry.Space

end
