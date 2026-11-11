module

public import StacksFrontier.AlgebraicGeometry.AmpleSectionConnected.StructureSheafDepth
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPointsDepth
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Depth
public import StacksFrontier.AlgebraicGeometry.Duality.CohenMacaulaySchemeOfDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.NormalDepthTwo
public import StacksFrontier.AlgebraicGeometry.Properties.Specialization
public import StacksFrontier.RingTheory.Dualizing.FlatLocalGorenstein
public import StacksFrontier.RingTheory.Dualizing.Gorenstein
public import StacksFrontier.RingTheory.Dualizing.GorensteinFormalFibres

/-!
# The Gorenstein step in the purity of the ramification locus

This file formalises the step of the proof of [Stacks, Tag 0EA3] which concludes that `𝒪_{X, x}`
is Gorenstein.  In the source that step reads: an étale morphism is a local complete
intersection, so [Stacks, Tag 0EA0] with `r = 0` produces a map

  `𝒪_X ⟶ ω_{X/Y} = H⁰(f^! 𝒪_Y)`

which is an isomorphism over `X ∖ closure {x}`; since `ω_{X/Y}` is `(S₂)` by
[Stacks, Tag 0E9V], that map is an isomorphism by [Stacks, Tag 0AVM]; and therefore `X`, and in
particular `𝒪_{X, x}`, is Gorenstein.

Everything in that paragraph *except* the construction of the map and the `(S₂)` property of
`ω_{X/Y}` is proved here.  Those two are the content of Tags 0EA0 and 0E9V, which are proved
elsewhere in the library (0E9V as
`Stacks.Duality.neg_le_and_propertySkModule_stalk_homology_upperShriek_of_residueTrdeg_le`);
the lemmas below are stated for an arbitrary scheme, so they appear as explicit data: the map
`φ` is an argument, the locus where it is already an isomorphism is a hypothesis, and the `(S₂)`
consequence is the hypothesis that the stalk of the target has positive depth at the points of
`closure {x}`.  No `@[stacks ...]` attribute appears below; these are auxiliary lemmas, not a
tag.

## Main results

* `Stacks.PurityRamification.two_le_depth_stalk_of_specializes` — on a locally Noetherian normal
  scheme, every point of `closure {x}` has local ring of depth at least two as soon as `x` has
  codimension at least two.  This is what makes [Stacks, Tag 0AVM] applicable at every point of
  the closed set over which `φ` is not already known to be an isomorphism.
* `Stacks.PurityRamification.isIso_of_stalk_isIso_outside_closure` — the appeal to
  [Stacks, Tag 0AVM] in the source: a map from `𝒪_X` to a coherent module which is an
  isomorphism on stalks outside `closure {x}` is an isomorphism, provided `x` has codimension at
  least two on a normal scheme and the target has positive depth along `closure {x}`.
* `Stacks.PurityRamification.isGorensteinLocalRing_stalk_of_stalk_isIso_outside_closure` — the
  conclusion `𝒪_{X, x}` is Gorenstein, from the hypothesis that the degree-zero complex of the
  stalk `ω_x` is a dualizing complex for `𝒪_{X, x}`.
* `Stacks.PurityRamification.isGorensteinRing_sections_of_hasDualizingModelOn_unit` and
  `Stacks.PurityRamification.isGorenstein_of_isDualizingComplex_unit` — the converse of
  [Stacks, Tag 0BFQ, clause (2)]: a locally Noetherian scheme whose structure sheaf, placed in
  degree zero, is a dualizing complex is Gorenstein.  This is the passage from the dualizing
  complex on `X` that [Stacks, Tag 0AA3] produces to the Gorensteinness of the local rings.
* `Stacks.PurityRamification.isGorenstein_of_stalk_isIso_outside_closure` and
  `Stacks.PurityRamification.isGorenstein_of_isIso_restrict_of_notSpecializes_mem` — the step of
  [Stacks, Tag 0EA3] in its scheme form: the hypothesis is that `ω[0]` is a dualizing complex on
  `X`, which is exactly what [Stacks, Tag 0AA3] gives for `ω = H⁰(f^!𝒪_Y)` once `X` has been
  shrunk to be Cohen–Macaulay, and the conclusion is that `X` is Gorenstein.  The two differ
  only in how the locus where `φ` is already an isomorphism is described: pointwise on stalks,
  or — as the source describes it — by the restriction of `φ` to an open subscheme being an
  isomorphism.

## Implementation notes

The source `𝒪_X` of the map is written `Stacks.Ample.unitModule X`, the spelling at which the
module structure on the stalk and its identification with the local ring,
`Stacks.Ample.unitStalkEquiv`, are available.

The hypothesis locating the points where `φ` is already an isomorphism is written as
`¬ x ⤳ y`, i.e. `y ∉ closure {x}`, and the two stalk conditions are written exactly in the shape
`AlgebraicGeometry.isIso_of_stalk_isIso_or_depth_two_and_not_associated` ([Stacks, Tag 0AVM])
consumes them, so that no translation is needed at the call site.

The codimension of `x` is read on the space, as `Order.coheight x`, rather than as
`ringKrullDim 𝒪_{X, x}`; the two agree by [Stacks, Tag 02IZ]
(`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`).  Reading it on the space is what lets the
bound propagate along a specialization, through `Order.coheight_anti`.

The derived category of modules over the local ring is taken at `HasDerivedCategory.standard`,
which is the choice `Dualizing.IsGorensteinLocalRing` is stated at; the derived category of
`𝒪_X`-modules is an instance *argument*, matching `Stacks.Duality.IsDualizingComplex`.

The identification of the dualizing model with `Γ(X, U)` in degree zero runs along the lines of
`Stacks.Duality.isCohenMacaulayRing_sections_of_hasDualizingModelOn`: the model is concentrated
in degree zero because `𝒪_X[0]` is and the two comparison functors are exact and reflect zero
objects, and the module it is the complex of is then identified with `Γ(X, U)` by taking `H⁰` of
the model isomorphism and using that `AlgebraicGeometry.tilde.functor` is fully faithful.

## References

* [Stacks Project, Tag 0AVM](https://stacks.math.columbia.edu/tag/0AVM)
* [Stacks Project, Tag 0EA3](https://stacks.math.columbia.edu/tag/0EA3)
* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
* [Stacks Project, Tag 031S](https://stacks.math.columbia.edu/tag/031S)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0BFQ](https://stacks.math.columbia.edu/tag/0BFQ)
* [Stacks Project, Tag 0AWW](https://stacks.math.columbia.edu/tag/0AWW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe u w

namespace Stacks.PurityRamification

variable {X : Scheme.{u}}

/-! ### Depth along the closure of a point of codimension at least two -/

/-- **Every specialization of a point of codimension at least two has depth at least two.**  On
a locally Noetherian normal scheme the local ring at a point of codimension at least two has
depth at least two by Serre's condition `(S₂)`, and codimension only grows along a
specialization: if `x ⤳ y` then `y ≤ x` in the specialization order, so
`Order.coheight x ≤ Order.coheight y`. -/
theorem two_le_depth_stalk_of_specializes [IsLocallyNoetherian X] [IsNormal X] {x y : X}
    (hxy : x ⤳ y) (hx : (2 : ℕ∞) ≤ Order.coheight x) :
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) (X.presheaf.stalk y) :=
  AlgebraicGeometry.two_le_depth_stalk_of_two_le_coheight y
    (hx.trans (Order.coheight_anti (AlgebraicGeometry.Scheme.le_iff_specializes.mpr hxy)))

/-! ### The appeal to Tag 0AVM -/

/-- **A map out of `𝒪_X` which is an isomorphism outside `closure {x}` is an isomorphism.**

This is the application of [Stacks, Tag 0AVM] made in the proof of [Stacks, Tag 0EA3].  At a
point `y ∉ closure {x}` the hypothesis `hout` gives an isomorphism on stalks.  At a point
`y ∈ closure {x}` the local ring has depth at least two by
`Stacks.PurityRamification.two_le_depth_stalk_of_specializes`, which is the depth hypothesis of
Tag 0AVM for the source `𝒪_X` after the identification `Stacks.Ample.unitStalkEquiv` of its
stalk with the local ring; and `y` is not an associated point of the target because the stalk of
the target there has positive depth. -/
theorem isIso_of_stalk_isIso_outside_closure [IsLocallyNoetherian X] [IsNormal X] {x : X}
    (hx : (2 : ℕ∞) ≤ Order.coheight x) {G : X.Modules} [G.IsQuasicoherent] [G.IsCoherent]
    (φ : Stacks.Ample.unitModule X ⟶ G)
    (hout : ∀ y : X, ¬ x ⤳ y →
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map φ.val)))
    (hdepth : ∀ y : X, x ⤳ y → (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y))
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf y)) :
    IsIso φ := by
  have : (Stacks.Ample.unitModule X).IsCoherent :=
    AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  refine AlgebraicGeometry.isIso_of_stalk_isIso_or_depth_two_and_not_associated φ fun y => ?_
  by_cases hy : x ⤳ y
  · refine Or.inr ⟨?_, Stacks.Divisors.notMem_associatedPoints_of_one_le_depth G y (hdepth y hy)⟩
    rw [Stacks.AmpleSectionConnected.depth_stalk_unit_eq]
    exact two_le_depth_stalk_of_specializes hy hx
  · exact Or.inl (hout y hy)

/-! ### The Gorenstein conclusion -/

/-- **The local ring at `x` is Gorenstein.**

The isomorphism `φ` of `Stacks.PurityRamification.isIso_of_stalk_isIso_outside_closure`
identifies `𝒪_{X, x}` with the stalk `ω_x` of the target, so the hypothesis that `ω_x`, placed
in degree zero, is a dualizing complex for `𝒪_{X, x}` transports to `𝒪_{X, x}` itself — which
is the definition of `𝒪_{X, x}` being Gorenstein.

In the proof of [Stacks, Tag 0EA3] the target is `ω_{X/Y} = H⁰(f^!𝒪_Y)`, and the hypothesis
`hdual` is the statement, from [Stacks, Tag 0AA3] and the Cohen–Macaulay shrinking of
[Stacks, Tag 0AWT], that `f^!𝒪_Y` is a dualizing complex concentrated in degree zero. -/
theorem isGorensteinLocalRing_stalk_of_stalk_isIso_outside_closure [IsLocallyNoetherian X]
    [IsNormal X] {x : X} (hx : (2 : ℕ∞) ≤ Order.coheight x)
    {G : X.Modules} [G.IsQuasicoherent] [G.IsCoherent]
    (φ : Stacks.Ample.unitModule X ⟶ G)
    (hout : ∀ y : X, ¬ x ⤳ y →
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map φ.val)))
    (hdepth : ∀ y : X, x ⤳ y → (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y))
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf y))
    (hdual : Dualizing.IsDualizingComplex
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj
        (ModuleCat.of (X.presheaf.stalk x) (G.presheaf.stalk x)))) :
    Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x) := by
  have hiso : IsIso φ := isIso_of_stalk_isIso_outside_closure hx φ hout hdepth
  let e : X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] G.presheaf.stalk x :=
    (Stacks.Ample.unitStalkEquiv X x).symm.trans
      (AlgebraicGeometry.schemeStalkLinearEquiv (asIso φ) x)
  exact Stacks.Duality.ringIsDualizingComplex_of_iso
    ((DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).mapIso
      e.toModuleIso).symm hdual

/-! ### A scheme whose structure sheaf is a dualizing complex is Gorenstein -/

section SchemeGorenstein

variable [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]

/-- **An affine open carrying a dualizing model of `𝒪_X[0]` has Gorenstein ring of sections.**

This is the converse direction of [Stacks, Tag 0BFQ, clause (2)], read at a single affine open:
there the scheme is *assumed* Gorenstein and the model is produced, here the model is given and
Gorensteinness is deduced.

The dualizing complex `D` over `Γ(X, U)` supplied by the model has its cohomology in the single
degree zero, because `𝒪_X[0]` does and the two functors relating them are exact and reflect
zero objects; so `D ≅ M[0]` for a `Γ(X, U)`-module `M`.  Taking `H⁰` of the model isomorphism
identifies the associated sheaf of `M` with the associated sheaf of `Γ(X, U)`, and the
associated-sheaf functor is fully faithful, so `M ≅ Γ(X, U)`.  Hence `Γ(X, U)` in degree zero is
a dualizing complex over itself, which is Gorensteinness. -/
theorem isGorensteinRing_sections_of_hasDualizingModelOn_unit (U : X.Opens)
    (hU : IsAffineOpen U)
    (h : Stacks.Duality.HasDualizingModelOn
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Stacks.Ample.unitModule X)) U hU) :
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    Dualizing.IsGorensteinRing Γ(X, U) := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨D, hD, ⟨e⟩⟩ := h
  set K := (DerivedCategory.singleFunctor X.Modules 0).obj (Stacks.Ample.unitModule X) with hK
  set G := Scheme.Modules.restrictFunctor U.ι with hG
  set F := tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom with hF
  -- Restricting along the inverse of `U ≅ Spec Γ(X, U)` undoes the restriction along it.
  have hback : Scheme.Modules.restrictFunctor hU.isoSpec.hom ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.inv ≅ 𝟭 (Spec Γ(X, U)).Modules :=
    (Scheme.Modules.restrictFunctorComp hU.isoSpec.inv hU.isoSpec.hom).symm ≪≫
      Scheme.Modules.restrictFunctorCongr hU.isoSpec.inv_hom_id ≪≫
      Scheme.Modules.restrictFunctorId
  -- The cohomology of the dualizing model `D` vanishes outside degree zero.
  have hvan : ∀ i : ℤ, i ≠ 0 →
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj D) := by
    intro i hi
    have hKzero : Limits.IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K) := by
      rcases lt_or_gt_of_ne hi with hlt | hgt
      · exact DerivedCategory.isZero_of_isGE K 0 i hlt
      · exact DerivedCategory.isZero_of_isLE K 0 i hgt
    have hGK : Limits.IsZero ((DerivedCategory.homologyFunctor U.toScheme.Modules i).obj
        (G.mapDerivedCategory.obj K)) :=
      (G.map_isZero hKzero).of_iso ((Dualizing.mapDerivedCategoryHomologyIso G i).app K)
    have hFD : Limits.IsZero ((DerivedCategory.homologyFunctor U.toScheme.Modules i).obj
        (F.mapDerivedCategory.obj D)) :=
      hGK.of_iso ((DerivedCategory.homologyFunctor U.toScheme.Modules i).mapIso e).symm
    have hFH : Limits.IsZero (F.obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj D)) :=
      hFD.of_iso ((Dualizing.mapDerivedCategoryHomologyIso F i).app D).symm
    have hTilde : Limits.IsZero ((tilde.functor Γ(X, U)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj D)) :=
      ((Scheme.Modules.restrictFunctor hU.isoSpec.inv).map_isZero hFH).of_iso
        (hback.app _).symm
    exact Limits.IsZero.of_full_of_faithful_of_isZero (tilde.functor Γ(X, U)) _ hTilde
  -- A complex with cohomology in the single degree zero is a module placed in degree zero.
  let : D.IsGE 0 :=
    (DerivedCategory.isGE_iff D 0).2 fun i hi => hvan i (by omega)
  let : D.IsLE 0 :=
    (DerivedCategory.isLE_iff D 0).2 fun i hi => hvan i (by omega)
  obtain ⟨M, ⟨eD⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE D 0
  -- `H⁰` of the model isomorphism compares the associated sheaf of `M` with `𝒪_U`.
  have hH : G.obj (Stacks.Ample.unitModule X) ≅ F.obj M :=
    (G.mapIso ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app
        (Stacks.Ample.unitModule X))).symm ≪≫
      ((Dualizing.mapDerivedCategoryHomologyIso G 0).app K).symm ≪≫
      (DerivedCategory.homologyFunctor U.toScheme.Modules 0).mapIso e ≪≫
      (Dualizing.mapDerivedCategoryHomologyIso F 0).app D ≪≫
      F.mapIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) 0).mapIso eD ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} Γ(X, U)) 0).app M)
  -- Transport the comparison back to `Spec Γ(X, U)`; there both sides are associated sheaves.
  have htilde : (tilde.functor Γ(X, U)).obj (ModuleCat.of Γ(X, U) Γ(X, U)) ≅
      (tilde.functor Γ(X, U)).obj M :=
    tildeSelf (R := Γ(X, U)) ≪≫ (Scheme.Modules.restrictUnitIso hU.isoSpec.inv).symm ≪≫
      (Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapIso
        ((Scheme.Modules.restrictUnitIso U.ι).symm ≪≫ hH) ≪≫
      hback.app ((tilde.functor Γ(X, U)).obj M)
  let eM : ModuleCat.of Γ(X, U) Γ(X, U) ≅ M :=
    (tilde.fullyFaithfulFunctor (R := Γ(X, U))).preimageIso htilde
  exact Dualizing.isGorensteinRing_of_isDualizingComplex_self Γ(X, U)
    (Stacks.Duality.ringIsDualizingComplex_of_iso
      ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).mapIso eM).symm
      (Stacks.Duality.ringIsDualizingComplex_of_iso eD hD))

/-- **A locally Noetherian scheme whose structure sheaf in degree zero is a dualizing complex is
Gorenstein.**  This is the converse of [Stacks, Tag 0BFQ, clause (2)]: every affine open has
Gorenstein ring of sections by
`Stacks.PurityRamification.isGorensteinRing_sections_of_hasDualizingModelOn_unit`, and the local
ring at a point of such an affine open is its localization at the corresponding prime. -/
theorem isGorenstein_of_isDualizingComplex_unit
    (hdual : Stacks.Duality.IsDualizingComplex
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Stacks.Ample.unitModule X))) :
    AlgebraicGeometry.IsGorenstein X := by
  refine (AlgebraicGeometry.isGorenstein_iff X).2 ⟨inferInstance, fun x => ?_⟩
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hG := isGorensteinRing_sections_of_hasDualizingModelOn_unit V hV (hdual V hV)
  let p : PrimeSpectrum Γ(X, V) := hV.primeIdealOf ⟨x, hxV⟩
  let : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  let : p.asIdeal.IsPrime := p.isPrime
  let : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  exact Dualizing.isGorensteinLocalRing_of_ringEquiv
    (IsLocalization.algEquiv p.asIdeal.primeCompl (X.presheaf.stalk x)
      (Localization.AtPrime p.asIdeal)).toRingEquiv (hG p.asIdeal)

/-- **The Gorenstein step of [Stacks, Tag 0EA3], in its scheme form.**

Let `X` be a locally Noetherian normal scheme, `x ∈ X` a point of codimension at least two, and
`ω` a coherent `𝒪_X`-module whose degree-zero complex is a dualizing complex on `X` — in the
source `ω = ω_{X/Y} = H⁰(f^!𝒪_Y)`, dualizing by [Stacks, Tag 0AA3] after the Cohen–Macaulay
shrinking of [Stacks, Tag 0AWT].  Given a map `𝒪_X ⟶ ω` which is an isomorphism on stalks
outside `closure {x}` — in the source the map of [Stacks, Tag 0EA0] with `r = 0`, an isomorphism
where `f` is étale — and given that `ω` has positive depth along `closure {x}` — in the source
the `(S₂)` property of [Stacks, Tag 0E9V] — the scheme `X` is Gorenstein.

In particular `𝒪_{X, x}` is Gorenstein, which is the conclusion the source draws at this point
of the argument. -/
theorem isGorenstein_of_stalk_isIso_outside_closure [IsNormal X] {x : X}
    (hx : (2 : ℕ∞) ≤ Order.coheight x) {G : X.Modules} [G.IsQuasicoherent] [G.IsCoherent]
    (φ : Stacks.Ample.unitModule X ⟶ G)
    (hout : ∀ y : X, ¬ x ⤳ y →
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map φ.val)))
    (hdepth : ∀ y : X, x ⤳ y → (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y))
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf y))
    (hdual : Stacks.Duality.IsDualizingComplex
      ((DerivedCategory.singleFunctor X.Modules 0).obj G)) :
    AlgebraicGeometry.IsGorenstein X :=
  have : IsIso φ := isIso_of_stalk_isIso_outside_closure hx φ hout hdepth
  isGorenstein_of_isDualizingComplex_unit
    (Stacks.Duality.isDualizingComplex_of_iso
      ((DerivedCategory.singleFunctor X.Modules 0).mapIso (asIso φ)).symm hdual)

/-- **The Gorenstein step of [Stacks, Tag 0EA3], with the hypothesis on `φ` in the source's
shape.**  The source says that the map `𝒪_X ⟶ ω_{X/Y}` of [Stacks, Tag 0EA0] "is an isomorphism
over `X ∖ closure {x}`", that is, that its restriction to that open subscheme is an isomorphism.
Here any open `V` containing every point outside `closure {x}` will do; the restriction of `φ`
to `V` being an isomorphism gives an isomorphism on the stalk at each point of `V`, by the
comparison `AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso` of the stalk of a restriction
with the stalk of the module itself. -/
theorem isGorenstein_of_isIso_restrict_of_notSpecializes_mem [IsNormal X] {x : X}
    (hx : (2 : ℕ∞) ≤ Order.coheight x) {G : X.Modules} [G.IsQuasicoherent] [G.IsCoherent]
    (φ : Stacks.Ample.unitModule X ⟶ G) (V : X.Opens)
    [IsIso ((Scheme.Modules.restrictFunctor V.ι).map φ)]
    (hV : ∀ y : X, ¬ x ⤳ y → y ∈ V)
    (hdepth : ∀ y : X, x ⤳ y → (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y))
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf y))
    (hdual : Stacks.Duality.IsDualizingComplex
      ((DerivedCategory.singleFunctor X.Modules 0).obj G)) :
    AlgebraicGeometry.IsGorenstein X := by
  refine isGorenstein_of_stalk_isIso_outside_closure hx φ (fun y hy => ?_) hdepth hdual
  have h0 : IsIso ((Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.toPresheaf V ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (⟨y, hV y hy⟩ : V)).map φ) := by
    simp only [Functor.comp_map]
    infer_instance
  exact (NatIso.isIso_map_iff
    (Scheme.Modules.restrictStalkNatIso V.ι (⟨y, hV y hy⟩ : V)) φ).mp h0

end SchemeGorenstein

end Stacks.PurityRamification

end
