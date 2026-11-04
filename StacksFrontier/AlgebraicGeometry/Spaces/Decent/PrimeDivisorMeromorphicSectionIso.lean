module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorMeromorphicSectionRatio
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullbackNatural
public import StacksFrontier.AlgebraicGeometry.Spaces.PicardTensorRatio

/-!
# Isomorphic invertible modules have the same Weil divisor class

Let `X` be a decent, locally Noetherian, integral algebraic space over a scheme `S` and let
`e : ℒ ≅ 𝒩` be an isomorphism of invertible `𝒪_X`-modules. This file proves, at the canonical
ratio `s / s_ξ` of Stacks 0EPR and the canonical embedding `R(X) → Q(𝒪^h_{X, ξ})` of Stacks
0ENK, that the Weil divisors of the chosen regular meromorphic sections of `ℒ` and of `𝒩`
differ by the divisor of an invertible rational function — the form of Stacks 0EPT that the
construction of Stacks 0EPW uses.

The argument is the source's. A regular meromorphic section `t` of `𝒩` is carried by the
isomorphism `𝒦_X(𝒩) ≅ 𝒦_X(ℒ)` to a regular meromorphic section `s₂` of `ℒ` with the *same*
order of vanishing along every prime divisor: the pullback of `s₂` to `Spec(𝒪_{U, u})` is the
coefficient of `t` against the image under `e⁻¹` of the generator chosen for `𝒩` there, that
image is again a free generator, and the order of vanishing does not see which free generator
is used (`AlgebraicGeometry.Space.PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_eq`).
Then `s₂` and the chosen section of `ℒ` are two regular meromorphic sections of one module, so
Stacks 0EPT in the form
`AlgebraicGeometry.Space.exists_units_orderOfVanishingSection_canonicalLocalRatio_eq_add_ord`
produces the invertible rational function.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_sectionsMap`:
  a regular meromorphic section of `𝒩` and its image in `𝒦_X(ℒ)` have the same order of
  vanishing along a prime divisor.
* `AlgebraicGeometry.Space.exists_divisorCoefficients_canonicalLocalRatioFamily_sub_eq_ord_of_iso`:
  **Stacks 0EPT in the form the construction of Stacks 0EPW uses**, at the canonical choices and
  with nothing assumed beyond `X` being decent, locally Noetherian and integral.

## References

* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EPW](https://stacks.math.columbia.edu/tag/0EPW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule
attribute [local instance] PrimeDivisor.genericStalkMeromorphicAlgebra
attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An isomorphism of sheaves of `𝒪_F`-modules is bijective on sections over every chart. -/
private theorem bijective_iso_val_app {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F} {P Q : Modules.{u, u} B S hS F hF} (ε : P ≅ Q)
    (V : (SmallEtale B S hS F)ᵒᵖ) :
    Function.Bijective (ε.hom.val.app V).hom := by
  have hround : ∀ z : P.val.obj V, (ε.inv.val.app V).hom ((ε.hom.val.app V).hom z) = z :=
    fun z => congrArg (fun φ : P ⟶ P => (PresheafOfModules.Hom.app φ.val V).hom z) ε.hom_inv_id
  have hround' : ∀ z : Q.val.obj V, (ε.hom.val.app V).hom ((ε.inv.val.app V).hom z) = z :=
    fun z => congrArg (fun φ : Q ⟶ Q => (PresheafOfModules.Hom.app φ.val V).hom z) ε.inv_hom_id
  exact ⟨fun x y h => by rw [← hround x, ← hround y, h],
    fun y => ⟨(ε.inv.val.app V).hom y, hround' y⟩⟩

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)
    (L N : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (hNinv : IsInvertibleModule (B := B) ⟨X, hX⟩ N)
    (hInt : IsIntegralSpace B S hS X)
    (hNoeth : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

/-- The generic Henselian local ring of every prime divisor is a nontrivial Noetherian ring of
Krull dimension at most one. -/
private theorem genericHenselianLocalRing_instances (hInt : IsIntegralSpace B S hS X)
    (hNoeth : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y)) :
    (∀ W : PrimeDivisor B S hS X, Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec)) ∧
    (∀ W : PrimeDivisor B S hS X, IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec)) ∧
    ∀ W : PrimeDivisor B S hS X, Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec) :=
  ⟨fun W => W.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hNoeth,
    fun W => W.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hNoeth,
    fun W => W.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hNoeth⟩

include hInt hNoeth in
/-- **A regular meromorphic section and its image under an isomorphism of modules have the same
order of vanishing.**  Let `e : ℒ ≅ 𝒩` and let `t` be a regular meromorphic section of `𝒩`. The
image `s₂` of `t` under the isomorphism `𝒦_X(𝒩) ≅ 𝒦_X(ℒ)` of
`AlgebraicGeometry.Space.meromorphicSectionSheafMapIso` has, along every prime divisor, the
order of vanishing of `t`.

The pullback of `s₂` to `Spec(𝒪_{U, u})` is the coefficient of `t` there against the image
under `e⁻¹` of the generator chosen for `𝒩` — this is the naturality of the pullback of
meromorphic sections in the module,
`AlgebraicGeometry.Space.pullbackMeromorphicSection_sectionsMap` — that image is again a free
generator, and the order of vanishing taken through the canonical ratio does not depend on the
free generator used. -/
theorem PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_sectionsMap (e : L ≅ N)
    (t : MeromorphicSection.{u, u} B S hS X hX N)
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X hX N t) :
    haveI : ∀ W : PrimeDivisor B S hS X,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    haveI : ∀ W : PrimeDivisor B S hS X,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    haveI : ∀ W : PrimeDivisor B S hS X,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    orderOfVanishingSection.{u, u} B S hS hX hdec Z L
        (SheafOfModules.sectionsMap (meromorphicSectionSheafMap B S hS X hX e.inv) t)
        (Z.canonicalLocalRatio B S hS hX hdec L hL hInt hNoeth) =
      orderOfVanishingSection.{u, u} B S hS hX hdec Z N t
        (Z.canonicalLocalRatio B S hS hX hdec N hNinv hInt hNoeth) := by
  obtain ⟨_, _, _⟩ := genericHenselianLocalRing_instances B S hS hX hdec hInt hNoeth
  set j := Z.genericStalkMorphism B S hS hX hdec with hj
  set hpull := Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec with hpulldef
  set chart := Z.genericStalkChart B S hS hX hdec with hchart
  set s₂ := SheafOfModules.sectionsMap (meromorphicSectionSheafMap B S hS X hX e.inv) t with hs₂def
  have hs₂ : IsRegularMeromorphicSection.{u, u} B S hS X hX L s₂ :=
    isRegularMeromorphicSection_sectionsMap_of_iso B S hS X hX e.symm t ht
  -- the image of the chosen generator of `j^*𝒩` under `j^*e⁻¹`
  set εP := (modulePullback B S hS j).mapIso e.symm with hεP
  set gen := Z.genericStalkGenerator B S hS hX hdec N hNinv chart (𝟙 chart) with hgen
  set g := ((εP.hom.val.app (op chart)).hom) gen with hgdef
  have hg : Function.Bijective fun r : chartRing B S hS
      (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2 chart ↦
      r • g := by
    have hcomp : (fun r : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2 chart ↦ r • g) =
        (fun z => ((εP.hom.val.app (op chart)).hom) z) ∘
          (fun r : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2 chart ↦ r • gen) := by
      funext r
      exact ((εP.hom.val.app (op chart)).hom.map_smul r gen).symm
    rw [hcomp]
    exact (bijective_iso_val_app B S hS εP (op chart)).comp
      (Z.bijective_smul_genericStalkGenerator B S hS hX hdec N hNinv chart (𝟙 chart))
  -- the pullback of `s₂` is the coefficient of `t` against that generator
  set a := Z.genericStalkCoefficient B S hS hX hdec N hNinv t with hadef
  have hnat := pullbackMeromorphicSection_sectionsMap B S hS j hpull e.inv t
  have ha : (pullbackMeromorphicSection B S hS j L hpull s₂).eval (op chart) =
      toMeromorphicSectionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2
        ((modulePullback B S hS j).obj L) chart
        (a ⊗ₜ[chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2 chart] g :
          (meromorphicSectionModule B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2
            ((modulePullback B S hS j).obj L)).obj (op chart)) := by
    refine (congrArg (fun w => w.eval (op chart)) hnat).trans ?_
    refine (congrArg ((meromorphicSectionSheafMap B S hS
        (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2
        ((modulePullback B S hS j).map e.inv)).val.app (op chart)).hom
      (Z.genericStalkCoefficient_spec B S hS hX hdec N hNinv t)).trans ?_
    refine (meromorphicSectionSheafMap_toMeromorphicSectionSheaf B S hS
      (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2
      ((modulePullback B S hS j).map e.inv) chart _).trans ?_
    exact congrArg (toMeromorphicSectionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2 ((modulePullback B S hS j).obj L) chart)
      (meromorphicSectionModuleMap_tmul B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2
        ((modulePullback B S hS j).map e.inv) chart a gen)
  refine (Z.orderOfVanishingSection_canonicalLocalRatio_eq B S hS hX hdec L hL hInt hNoeth s₂ hs₂
    g hg a ha (fun _ => Z.canonicalLocalRatio B S hS hX hdec N hNinv hInt hNoeth t) ?_).trans rfl
  exact Z.coe_canonicalLocalRatio B S hS hX hdec N hNinv hInt hNoeth t ht

include hInt hNoeth in
/-- **Stacks 0EPT in the form the construction of Stacks 0EPW uses, at the canonical choices.**
On a decent, locally Noetherian, integral algebraic space the Weil divisors of the chosen
regular meromorphic sections of two isomorphic invertible `𝒪_X`-modules differ coefficientwise
by the divisor of an invertible rational function on `X`, the order of vanishing being read at
the canonical ratio `s / s_ξ` of Stacks 0EPR and the embedding `R(X) → Q(𝒪^h_{X, ξ})` of
Stacks 0ENK.

The chosen section of `𝒩` is carried by the isomorphism `𝒦_X(𝒩) ≅ 𝒦_X(ℒ)` to a regular
meromorphic section of `ℒ` with the same orders of vanishing
(`AlgebraicGeometry.Space.PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_sectionsMap`),
and two regular meromorphic sections of the one module `ℒ` differ by an invertible rational
function, which is Stacks 0EPT in the form
`AlgebraicGeometry.Space.exists_units_orderOfVanishingSection_canonicalLocalRatio_eq_add_ord`. -/
@[stacks 0EPT "the second conclusion for two ISOMORPHIC invertible modules: the Weil divisors \
of the chosen regular meromorphic sections of ℒ and of 𝒩 differ coefficientwise by div(f) for \
an invertible rational function f, at the canonical ratio s/s_ξ of Stacks 0EPR and the \
embedding of Stacks 0ENK, with nothing assumed beyond X decent, locally Noetherian and integral"]
theorem exists_divisorCoefficients_canonicalLocalRatioFamily_sub_eq_ord_of_iso (e : L ≅ N) :
    haveI : ∀ W : PrimeDivisor B S hS X,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    haveI : ∀ W : PrimeDivisor B S hS X,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    haveI : ∀ W : PrimeDivisor B S hS X,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hNoeth
    ∃ f : (rationalFunctions B S hS hX)ˣ, ∀ W : PrimeDivisor B S hS X,
      divisorCoefficients.{u, u} B S hS hX hdec L
            (regularMeromorphicSection B S hS hX hInt hNoeth L hL)
            (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hNoeth) W -
          divisorCoefficients.{u, u} B S hS hX hdec N
            (regularMeromorphicSection B S hS hX hInt hNoeth N hNinv)
            (canonicalLocalRatioFamily B S hS hX hdec N hNinv hInt hNoeth) W =
        (genericFractionEmbedding B S hS hX hdec hInt hNoeth).ord f W := by
  obtain ⟨_, _, _⟩ := genericHenselianLocalRing_instances B S hS hX hdec hInt hNoeth
  have ht := isRegularMeromorphicSection_regularMeromorphicSection B S hS hX hInt hNoeth N hNinv
  have hs₂ : IsRegularMeromorphicSection.{u, u} B S hS X hX L
      (SheafOfModules.sectionsMap (meromorphicSectionSheafMap B S hS X hX e.inv)
        (regularMeromorphicSection B S hS hX hInt hNoeth N hNinv)) :=
    isRegularMeromorphicSection_sectionsMap_of_iso B S hS X hX e.symm _ ht
  obtain ⟨f, hf⟩ := exists_units_orderOfVanishingSection_canonicalLocalRatio_eq_add_ord B S hS hX
    hdec hInt hNoeth L hL (regularMeromorphicSection B S hS hX hInt hNoeth L hL) _
    (isRegularMeromorphicSection_regularMeromorphicSection B S hS hX hInt hNoeth L hL) hs₂
  refine ⟨f, fun W => ?_⟩
  have heq : orderOfVanishingSection.{u, u} B S hS hX hdec W L
        (SheafOfModules.sectionsMap (meromorphicSectionSheafMap B S hS X hX e.inv)
          (regularMeromorphicSection B S hS hX hInt hNoeth N hNinv))
        (W.canonicalLocalRatio B S hS hX hdec L hL hInt hNoeth) =
      orderOfVanishingSection.{u, u} B S hS hX hdec W N
        (regularMeromorphicSection B S hS hX hInt hNoeth N hNinv)
        (W.canonicalLocalRatio B S hS hX hdec N hNinv hInt hNoeth) :=
    W.orderOfVanishingSection_canonicalLocalRatio_sectionsMap B S hS hX hdec L N hL
      hNinv hInt hNoeth e (regularMeromorphicSection B S hS hX hInt hNoeth N hNinv) ht
  have hfW : orderOfVanishingSection.{u, u} B S hS hX hdec W L
        (regularMeromorphicSection B S hS hX hInt hNoeth L hL)
        (W.canonicalLocalRatio B S hS hX hdec L hL hInt hNoeth) =
      orderOfVanishingSection.{u, u} B S hS hX hdec W L
          (SheafOfModules.sectionsMap (meromorphicSectionSheafMap B S hS X hX e.inv)
            (regularMeromorphicSection B S hS hX hInt hNoeth N hNinv))
          (W.canonicalLocalRatio B S hS hX hdec L hL hInt hNoeth) +
        (genericFractionEmbedding B S hS hX hdec hInt hNoeth).ord f W := hf W
  simp only [divisorCoefficients, canonicalLocalRatioFamily]
  omega

end AlgebraicGeometry.Space

end
