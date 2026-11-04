module

public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalFunctionsRepresentableModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GlobalFunctionsStagesColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsTerminalBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecOfGlobalFunctionsUnique

/-!
# An affine algebraic space is the spectrum of its ring of global functions

Let `X` be an affine algebraic space over a *terminal* base scheme `S`, so that `X` is
isomorphic to the presheaf represented by an object `T` of the big fppf site of `S` whose
underlying scheme is affine. Then the canonical morphism

`X ⟶ Spec Γ(X, 𝒪_X)`

of `AlgebraicGeometry.Space.exists_specMap_of_globalHom`, taken for the `u`-model
`Γ(T, 𝒪_T)` of the ring of global functions supplied by
`AlgebraicGeometry.Space.globalFunctionsAffineEquiv`, is an isomorphism.

This is the step of Stacks 07SQ which identifies an affine algebraic space with the spectrum
of its ring of global functions. The content is that the canonical morphism, which is pinned
down only by its values on the étale charts of `X`, agrees with the composite

`X ≅ T ⟶ Spec Γ(T, 𝒪_T)`

of the chosen isomorphism with the `Γ`–`Spec` unit of the representing scheme, every factor of
which is invertible: the first by hypothesis, the second because over a terminal base the two
functors of points of an object of the site agree, and the third because the representing
scheme is affine.

## Main results

* `AlgebraicGeometry.Space.appTop_yonedaPreimage_globalFunctionsAffineEquiv` and
  `AlgebraicGeometry.Space.globalFunctionsChartRestriction_globalFunctionsAffineEquiv_symm`:
  **the chart formula for the model of the global functions.** Reading a global function of `X`
  as a regular function on the representing scheme and pulling it back along an étale chart is
  restriction of that global function to the chart.
* `AlgebraicGeometry.Space.yonedaEquiv_comp_affineSpecComparison`: the composite
  `X ≅ T ⟶ Spec Γ(T, 𝒪_T)` satisfies the chart formula which characterises the canonical
  morphism.
* `AlgebraicGeometry.Space.isIso_of_isAffineSpace_specMapOfGlobalHom`: **an affine algebraic
  space over a terminal base is the spectrum of its global functions.**
* `AlgebraicGeometry.Space.exists_isIso_specMap_of_isAffineSpace`: the same statement with the
  canonical morphism produced rather than assumed.
* `AlgebraicGeometry.Space.isIso_specMapOfGlobalHom_of_isAffineSpace`: the same statement for an
  arbitrary `u`-model of the ring of global functions, the two models differing by the spectrum
  of a ring isomorphism.

## Implementation notes

*Why the chart formula is the whole content.* The canonical morphism is characterised by
`AlgebraicGeometry.Space.specMapOfGlobalHom_unique`, so identifying it with the explicit
composite is a chart-by-chart computation. On a chart `V` the composite is, through the
`Γ`–`Spec` adjunction, the morphism of schemes attached to pullback of regular functions along
the morphism `V ⟶ T` of the site underlying the chart; and that pullback is exactly restriction
of global functions to `V`, read through the identification of the global functions of `X` with
`Γ(T, 𝒪_T)`. The latter is the first result above, and it is proved by substituting a regular
function on `T` for the global function, so that
`AlgebraicGeometry.Space.globalFunctionsMap_val_of_yoneda_map_comp` computes both sides at the
identity chart of the representable presheaf.

*Where each hypothesis is used.* Terminality of the base enters only through
`AlgebraicGeometry.Space.isIso_schemePointsUnit`, and affineness of the representing scheme
only through invertibility of its `Γ`–`Spec` unit. Neither is needed for the chart formula, so
the identification of the canonical morphism with the explicit composite is unconditional.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The model of the global functions, restricted to an étale chart -/

/-- **The chart formula for the regular-function model of the global functions of an affine
algebraic space.** Let `X` be an algebraic space over `S` identified by `e` with the presheaf
represented by an object `T` of the site, and let `V` be an étale chart of `X`. Reading a global
function `σ` of `X` as a regular function on the scheme underlying `T` and pulling that back
along the morphism `V ⟶ T` of the site underlying the chart gives the restriction of `σ` to
`V`. -/
theorem appTop_yonedaPreimage_globalFunctionsAffineEquiv (X : AlgebraicSpaces B S hS)
    (T : BigFppfOver B S hS) (e : X.obj ≅ yoneda.obj T) (V : SmallEtale B S hS X.1)
    (σ : globalFunctions B S hS X.1) :
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (V.1.hom ≫ e.hom))).appTop.hom
        (globalFunctionsAffineEquiv B S hS X T e σ)
      = globalFunctionsChartRestriction B S hS X V σ := by
  let Y : AlgebraicSpaces B S hS := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
  let i : Y ≅ X := isoOfPresheafIso B S hS (U := Y) (V := X) e.symm
  -- The chart formula for a regular function on the representing object.
  have key : ∀ τ : globalFunctions B S hS Y.1,
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (V.1.hom ≫ e.hom))).appTop.hom
          (globalFunctionsYonedaEquiv B S hS T τ)
        = globalFunctionsChartRestriction B S hS X V
            (globalFunctionsMap B S hS i.inv τ) := by
    intro τ
    have hmw : yoneda.map (yoneda.preimage (V.1.hom ≫ e.hom)) ≫
        (idChart B S hS T).1.hom = V.1.hom ≫ i.inv.hom := by
      show yoneda.map (yoneda.preimage (V.1.hom ≫ e.hom)) ≫ 𝟙 _ = V.1.hom ≫ e.hom
      rw [Functor.map_preimage, Category.comp_id]
    exact (globalFunctionsMap_val_of_yoneda_map_comp B S hS i.inv τ V (idChart B S hS T) _ hmw).symm
  -- Pullback along the two directions of the identification are mutually inverse.
  have hround : (globalFunctionsMap B S hS i.inv).comp (globalFunctionsMap B S hS i.hom)
      = RingHom.id (globalFunctions' B S hS X.1) := by
    rw [← globalFunctionsMap_comp, i.inv_hom_id, globalFunctionsMap_id]
  have hval : globalFunctionsAffineEquiv B S hS X T e σ
      = globalFunctionsYonedaEquiv B S hS T (globalFunctionsMap B S hS i.hom σ) := rfl
  rw [hval, key]
  exact congrArg (globalFunctionsChartRestriction B S hS X V)
    (by simpa using DFunLike.congr_fun hround σ)

/-- **The chart formula for the regular-function model of the global functions**, in the
direction which reads a regular function on the representing object as a global function: its
restriction to an étale chart `V` is its pullback along the morphism `V ⟶ T` of the site
underlying the chart. -/
theorem globalFunctionsChartRestriction_globalFunctionsAffineEquiv_symm
    (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS) (e : X.obj ≅ yoneda.obj T)
    (V : SmallEtale B S hS X.1) (s : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    globalFunctionsChartRestriction B S hS X V
        ((globalFunctionsAffineEquiv B S hS X T e).symm s)
      = ((BigFppfOver.toScheme B S hS).map
          (yoneda.preimage (V.1.hom ≫ e.hom))).appTop.hom s := by
  rw [← appTop_yonedaPreimage_globalFunctionsAffineEquiv B S hS X T e,
    RingEquiv.apply_symm_apply]

/-! ### The explicit comparison morphism and its chart formula -/

/-- The point of the functor of points of a scheme obtained by pushing the comparison morphism
of an object `W` of the site along a morphism of schemes out of the scheme underlying `W` is
that morphism of schemes. -/
theorem yonedaEquiv_schemePointsUnit_comp_schemePointsMap (W : BigFppfOver B S hS)
    {Z : Scheme.{u}} (f : (BigFppfOver.toScheme B S hS).obj W ⟶ Z) :
    yonedaEquiv (schemePointsUnit B S hS W ≫ schemePointsMap B S hS f) = f := by
  show (BigFppfOver.toScheme B S hS).map (𝟙 W) ≫ f = f
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The composite `X ≅ T ⟶ Spec Γ(T, 𝒪_T)` satisfies the chart formula of the canonical
morphism to the spectrum of the ring of global functions.** Here `X` is an algebraic space over
`S` identified by `e` with the presheaf represented by an object `T` of the site, the ring of
global functions of `X` is modelled by the regular functions of the scheme underlying `T`
through `AlgebraicGeometry.Space.globalFunctionsAffineEquiv`, and the right-hand morphism is
the `Γ`–`Spec` unit of that scheme read on functors of points.

Together with `AlgebraicGeometry.Space.specMapOfGlobalHom_unique` this identifies the canonical
morphism of `AlgebraicGeometry.Space.exists_specMap_of_globalHom` with the composite. -/
theorem yonedaEquiv_comp_affineSpecComparison (X : AlgebraicSpaces B S hS)
    (T : BigFppfOver B S hS) (e : X.obj ≅ yoneda.obj T) (V : SmallEtale B S hS X.1) :
    yonedaEquiv (V.1.hom ≫ (e.hom ≫ schemePointsUnit B S hS T ≫
        schemePointsMap B S hS ((BigFppfOver.toScheme B S hS).obj T).toSpecΓ))
      = specMapOfGlobalHom _ ((globalFunctionsChartRestriction B S hS X V).comp
          (globalFunctionsAffineEquiv B S hS X T e).symm.toRingHom) := by
  have happ : ((BigFppfOver.toScheme B S hS).map
        (yoneda.preimage (V.1.hom ≫ e.hom))).appTop
      = CommRingCat.ofHom ((globalFunctionsChartRestriction B S hS X V).comp
        (globalFunctionsAffineEquiv B S hS X T e).symm.toRingHom) :=
    CommRingCat.hom_ext (RingHom.ext fun s =>
      (globalFunctionsChartRestriction_globalFunctionsAffineEquiv_symm B S hS X T e V s).symm)
  have hmor : V.1.hom ≫ (e.hom ≫ schemePointsUnit B S hS T ≫
        schemePointsMap B S hS ((BigFppfOver.toScheme B S hS).obj T).toSpecΓ)
      = (schemePointsUnit B S hS V.1.left ≫ schemePointsMap B S hS
            ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (V.1.hom ≫ e.hom)))) ≫
          schemePointsMap B S hS ((BigFppfOver.toScheme B S hS).obj T).toSpecΓ := by
    rw [commSq_schemePointsUnit B S hS, Functor.map_preimage]
    simp only [Category.assoc]
  rw [hmor, yonedaEquiv_comp_schemePointsMap,
    yonedaEquiv_schemePointsUnit_comp_schemePointsMap, specMapOfGlobalHom,
    Scheme.toSpecΓ_naturality, happ]
  rfl

/-! ### An affine algebraic space is the spectrum of its global functions -/

/-- **An affine algebraic space over a terminal base is the spectrum of its ring of global
functions.** Let `X` be an algebraic space over a terminal base scheme `S`, identified by `e`
with the presheaf represented by an object `T` of the site whose underlying scheme is affine,
and let `p : X ⟶ Spec Γ(T, 𝒪_T)` satisfy the chart formula of
`AlgebraicGeometry.Space.exists_specMap_of_globalHom` for the resulting model of the global
functions of `X`. Then `p` is an isomorphism.

This is the step of Stacks 07SQ which identifies an affine algebraic space with the spectrum of
its ring of global functions. -/
theorem isIso_of_isAffineSpace_specMapOfGlobalHom (hterminal : IsTerminal S)
    (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (e : X.obj ≅ yoneda.obj T)
    {p : X.obj ⟶ schemePoints B S hS
      (Spec (CommRingCat.of Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)))}
    (hp : ∀ V : SmallEtale B S hS X.1, yonedaEquiv (V.1.hom ≫ p) =
      specMapOfGlobalHom _ ((globalFunctionsChartRestriction B S hS X V).comp
        (globalFunctionsAffineEquiv B S hS X T e).symm.toRingHom)) :
    IsIso p := by
  have hq : p = e.hom ≫ schemePointsUnit B S hS T ≫
      schemePointsMap B S hS ((BigFppfOver.toScheme B S hS).obj T).toSpecΓ :=
    specMapOfGlobalHom_unique B S hS X _
      (globalFunctionsAffineEquiv B S hS X T e).symm.toRingHom hp
      (yonedaEquiv_comp_affineSpecComparison B S hS X T e)
  have := isIso_schemePointsUnit B S hS hterminal T
  have : IsIso ((BigFppfOver.toScheme B S hS).obj T).toSpecΓ := hT.affine
  rw [hq]
  infer_instance

/-- **An affine algebraic space over a terminal base is the spectrum of its ring of global
functions**, with the canonical morphism produced rather than assumed: it is the morphism of
`AlgebraicGeometry.Space.exists_specMap_of_globalHom` for the model of the global functions of
`X` given by the regular functions of the representing scheme. -/
theorem exists_isIso_specMap_of_isAffineSpace (hterminal : IsTerminal S)
    (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (e : X.obj ≅ yoneda.obj T) :
    ∃ p : X.obj ⟶ schemePoints B S hS
        (Spec (CommRingCat.of Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))),
      IsIso p ∧ ∀ V : SmallEtale B S hS X.1, yonedaEquiv (V.1.hom ≫ p) =
        specMapOfGlobalHom _ ((globalFunctionsChartRestriction B S hS X V).comp
          (globalFunctionsAffineEquiv B S hS X T e).symm.toRingHom) := by
  obtain ⟨p, hp⟩ := exists_specMap_of_globalHom B S hS X _
    (globalFunctionsAffineEquiv B S hS X T e).symm.toRingHom
  exact ⟨p, isIso_of_isAffineSpace_specMapOfGlobalHom B S hS hterminal X T hT e hp, hp⟩

/-- **An affine algebraic space over a terminal base is the spectrum of its ring of global
functions, read in an arbitrary `u`-model of that ring.** Let `X` be an algebraic space over a
terminal base scheme `S`, identified by `e` with the presheaf represented by an object `T` of
the site whose underlying scheme is affine, let `A` be a ring identified by `eA` with the global
functions of `X`, and let `p : X ⟶ Spec A` satisfy the chart formula of
`AlgebraicGeometry.Space.exists_specMap_of_globalHom`. Then `p` is an isomorphism.

This is the form the proof of Stacks 07SQ consumes, where the model of the ring of global
functions is a polynomial presentation rather than the regular functions of the representing
scheme. The two differ by the spectrum of a ring isomorphism, which is invertible. -/
theorem isIso_specMapOfGlobalHom_of_isAffineSpace (hterminal : IsTerminal S)
    (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (e : X.obj ≅ yoneda.obj T)
    (A : Type u) [CommRing A] (eA : A ≃+* globalFunctions B S hS X.1)
    {p : X.obj ⟶ schemePoints B S hS (Spec (CommRingCat.of A))}
    (hp : ∀ V : SmallEtale B S hS X.1, yonedaEquiv (V.1.hom ≫ p) =
      specMapOfGlobalHom A ((globalFunctionsChartRestriction B S hS X V).comp eA.toRingHom)) :
    IsIso p := by
  obtain ⟨q, hqiso, hq⟩ := exists_isIso_specMap_of_isAffineSpace B S hS hterminal X T hT e
  -- The two models of the ring of global functions differ by this ring isomorphism.
  let χ : A ≃+* Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
    eA.trans (globalFunctionsAffineEquiv B S hS X T e)
  have hchart : ∀ V : SmallEtale B S hS X.1, V.1.hom ≫ p =
      V.1.hom ≫ q ≫ schemePointsMap B S hS (Spec.map (CommRingCat.ofHom χ.toRingHom)) := by
    intro V
    refine yonedaEquiv.injective ?_
    have hψ : (globalFunctionsChartRestriction B S hS X V).comp eA.toRingHom
        = ((globalFunctionsChartRestriction B S hS X V).comp
            (globalFunctionsAffineEquiv B S hS X T e).symm.toRingHom).comp χ.toRingHom :=
      RingHom.ext fun a => congrArg (globalFunctionsChartRestriction B S hS X V)
        ((globalFunctionsAffineEquiv B S hS X T e).symm_apply_apply (eA a)).symm
    rw [hp V, ← Category.assoc, yonedaEquiv_comp_schemePointsMap, hq V, specMapOfGlobalHom,
      specMapOfGlobalHom, Category.assoc, ← Spec.map_comp, hψ]
    rfl
  have hpq : p = q ≫ schemePointsMap B S hS (Spec.map (CommRingCat.ofHom χ.toRingHom)) :=
    hom_ext_of_charts B S hS X (isSheaf_schemePoints B S hS _) hchart
  have : IsIso (CommRingCat.ofHom χ.toRingHom) := χ.toCommRingCatIso.isIso_hom
  rw [hpq]
  infer_instance

end AlgebraicGeometry.Space

end
