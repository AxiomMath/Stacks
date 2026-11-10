module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeCohomology.CupProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.DeRhamComplexBaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.LerayComposite
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.Transverse

/-!
# Pullback maps on Hodge cohomology

Consider a commutative square of schemes

```
X' --g'--> X
|f'        |f
v          v
S' --g---> S
```

The canonical map of sheaves of differential forms of the square is a map
`Ω^p_{X/S} ⟶ g₀_*Ω^p_{X'/S'}` of `f⁻¹𝒪_S`-modules on `X`, where `g₀ : (X', f'⁻¹𝒪_{S'}) ⟶
(X, f⁻¹𝒪_S)` is the morphism of ringed spaces of the square, with underlying map that of `g'`.
Placing it in degree `0`, following it by the comparison `g₀_* ⟶ Rg₀_*` and taking cohomology of
derived global sections, the Leray identification `H^q(X, Rg₀_* -) = H^q(X', -)` of Tag 0D5W
gives the **pullback maps** of Section 50.5 (Tag 0FM4)

`g'^* : H^q(X, Ω^p_{X/S}) ⟶ H^q(X', Ω^p_{X'/S'})`

on the Hodge cohomology groups. They are additive and semilinear for the ring map
`Γ(X, f⁻¹𝒪_S) ⟶ Γ(X', f'⁻¹𝒪_{S'})` of `g₀`, the identity square induces the identity, and
pasting two squares induces the composite. These are the pullbacks of datum (D1) of Weil
cohomology theories for Hodge cohomology (Remark 0FWE); for a square over the identity of the
base they are functorial in the upper morphism.

The construction is carried out first for an arbitrary morphism of ringed spaces
`h : Z' ⟶ Z` and morphism of complexes of modules `φ : K ⟶ h_*K'`: the pullback
`H^n(Z, K) ⟶ H^n(Z', K')` is `H^n(RΓ(Z, φ))`, then `H^n(RΓ(Z, -))` of the comparison
`h_*K' ⟶ Rh_*K'`, then the Leray identification. Its functoriality comes from the compatibility
of the Leray identification with composition of morphisms of ringed spaces
(`Stacks.Cohomology.LerayComposite.lerayCohomologyIso_comp`) and from the classes of global
cocycles of a K-injective complex.

## Main definitions

* `Stacks.HodgeWeil.cohomologyPullback`: the pullback `H^n(Z, K) ⟶ H^n(Z', K')` along a
  morphism of ringed spaces `h : Z' ⟶ Z` and a morphism of complexes `K ⟶ h_*K'`.
* `Stacks.HodgeWeil.formsSinglePushforward`: the canonical map
  `Ω^p_{X/S}[0] ⟶ g₀_*(Ω^p_{X'/S'}[0])` of a commutative square.
* `Stacks.HodgeWeil.hodgeBaseRingHom`: the ring map `Γ(X, f⁻¹𝒪_S) ⟶ Γ(X', f'⁻¹𝒪_{S'})` of a
  commutative square.
* `Stacks.HodgeWeil.hodgePullback`: **the pullback on Hodge cohomology**
  `H^q(X, Ω^p_{X/S}) ⟶ H^q(X', Ω^p_{X'/S'})`, a semilinear map over `hodgeBaseRingHom`.

## Main results

* `Stacks.HodgeWeil.cohomologyPullback_naturality`, `Stacks.HodgeWeil.cohomologyPullback_comp`
  and `Stacks.HodgeWeil.cohomologyPullback_id`: the pullback along a morphism of complexes is
  natural, compatible with composition, and the identity along the identity.
* `Stacks.HodgeWeil.relativeDifferentialFormsPullback_id`: pulling back a differential form
  along the identity square does nothing.
* `Stacks.HodgeWeil.hodgePullback_id`: **the identity square induces the identity** on Hodge
  cohomology.
* `Stacks.HodgeWeil.hodgePullback_comp`: **pasting two squares induces the composite** of the
  pullbacks; `Stacks.HodgeWeil.hodgePullback_comp_overBase` is the case of squares over the
  identity of the base, the form datum (D1) uses for schemes over `Spec k`.
* `Stacks.HodgeWeil.hodgeBaseRingHom_id`, `Stacks.HodgeWeil.hodgeBaseRingHom_comp` and
  `Stacks.HodgeWeil.hodgeBaseRingHom_comp_inverseImageGlobalSections`: the ring maps are
  functorial and compatible with the maps from the global sections of the bases.

## Implementation notes

The groups `H^q(X, Ω^p_{X/S})` are those of
`AlgebraicGeometry.SheafOfModules.hodgeCohomologyComponent`, the cohomology of the derived
global sections, over the ringed space `(X, f⁻¹𝒪_S)`, of `Ω^p_{X/S}` placed in degree `0`; the
pullback is therefore built from the module form of the canonical map and of the Leray
identification, not from the abelian-sheaf realization used for de Rham cohomology. The
derived categories are those of `HasDerivedCategory.standard`, in which these groups are
stated.

The morphism of ringed spaces of the identity square is the identity, and that of a pasted
square is the composite (`Stacks.HodgeWeil.inverseImageBaseMap_id`,
`Stacks.HodgeWeil.inverseImageBaseMap_comp`) only up to equality, not by definition, so
functoriality is first proved for morphisms of ringed spaces that are equal to an identity or
to a composite (`Stacks.HodgeWeil.cohomologyPullback_congr`,
`Stacks.HodgeWeil.cohomologyPullback_comp_of_heq`). A morphism of ringed spaces into
`(X, f⁻¹𝒪_S)` is determined by its underlying continuous map and its composite with the
projection to `S`, since `f⁻¹` is left adjoint to `f_*`
(`Stacks.HodgeWeil.inverseImageBase_hom_ext`).

The compatibility of the pullback with the cup product of Hodge cohomology is not proved here.

## References

* [Stacks Project, Tag 0FM4](https://stacks.math.columbia.edu/tag/0FM4)
* [Stacks Project, Tag 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 07HX](https://stacks.math.columbia.edu/tag/07HX)
* [Stacks Project, Tag 0FID](https://stacks.math.columbia.edu/tag/0FID)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange
open Stacks.Cohomology.GlobalKunneth (baseRing baseSections)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule globalClass globalClass_map
  sectionsComplex globalSections)
open Stacks.Cohomology.LerayCupPairing (lerayCohomologyIso lerayCohomologyIso_naturality_apply
  lerayCohomologyIso_globalClass restrictGlobal globalRingHom)
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces (pushforwardComparisonQ
  pushforwardComparisonQ_naturality)
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward
  derivedPushforwardCompIso exists_quasiIso_isKInjective)
open Stacks.Cohomology.LerayComposite (pushforwardCompComplexHom pushforwardComparisonQ_comp
  lerayCohomologyIso_comp)
open Stacks.Cohomology.DerivedPushforwardAssociativity (modulePushforwardIdComplex)
open Stacks.Cohomology.HomologyPullback (map_map_comp_apply)
open AlgebraicGeometry.SheafOfModules (hodgeCohomologyComponent underlyingRingSheaf)

universe u

namespace Stacks.HodgeWeil

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

attribute [local instance] HasDerivedCategory.standard

/-! ### Pullback along a morphism of complexes -/

section General

variable {Z Z' Z'' : RingedSpace.{u, u}} (h : Z' ⟶ Z)

/-- **The pullback on cohomology along a morphism of complexes** `φ : K ⟶ h_*K'`, for a morphism
of ringed spaces `h : Z' ⟶ Z`: `H^n(RΓ(Z, φ))`, followed by `H^n(RΓ(Z, -))` of the comparison
`h_*K' ⟶ Rh_*K'` and the Leray identification `H^n(Z, Rh_*K') = H^n(Z', K')` of Tag 0D5W. It is
linear over `Γ(Z, 𝒪_Z)` for the module structure on the target restricted along `h^♯`. -/
def cohomologyPullback {K : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ}
    {K' : CochainComplex (SheafOfModules.{u} (structureSheafRing Z')) ℤ}
    (φ : K ⟶ (pushforwardComplex h).obj K') (n : ℤ) :
    cohomologyModule (DerivedCategory.Q.obj K) n ⟶
      (restrictGlobal h).obj (cohomologyModule (DerivedCategory.Q.obj K') n) :=
  (DerivedCategory.homologyFunctor _ n).map ((baseSections Z).map
      (DerivedCategory.Q.map φ ≫ pushforwardComparisonQ h K')) ≫
    (lerayCohomologyIso h (DerivedCategory.Q.obj K') n).hom

/-- `cohomologyPullback h φ n` sends a class `x` to the image under the Leray identification of
the map induced on `H^n(Z, -)` by `φ` followed by the comparison `h_*K' ⟶ Rh_*K'`. -/
theorem cohomologyPullback_apply
    {K : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ}
    {K' : CochainComplex (SheafOfModules.{u} (structureSheafRing Z')) ℤ}
    (φ : K ⟶ (pushforwardComplex h).obj K') (n : ℤ)
    (x : cohomologyModule (DerivedCategory.Q.obj K) n) :
    (cohomologyPullback h φ n).hom x =
      (lerayCohomologyIso h (DerivedCategory.Q.obj K') n).hom
        (((DerivedCategory.homologyFunctor _ n).map ((baseSections Z).map
          (DerivedCategory.Q.map φ ≫ pushforwardComparisonQ h K'))).hom x) :=
  rfl

/-- The Leray identification on `H^n(Z, -)` of a composite `u ≫ v` with `v` into `Rh_*C`, where
`u ≫ v` factors through `h_*` of a map `t : C' ⟶ C`, is natural in `t`. -/
private theorem leray_homology_map_comp_apply
    {A B : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))}
    {C C' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z'))}
    (u : A ⟶ B) (v : B ⟶ (derivedPushforward h).obj C) (φ : A ⟶ (derivedPushforward h).obj C')
    (t : C' ⟶ C) (key : u ≫ v = φ ≫ (derivedPushforward h).map t) (n : ℤ)
    (x : cohomologyModule A n) :
    (lerayCohomologyIso h C n).hom (((DerivedCategory.homologyFunctor _ n).map
        ((baseSections Z).map v)).hom (((DerivedCategory.homologyFunctor _ n).map
          ((baseSections Z).map u)).hom x)) =
      ((DerivedCategory.homologyFunctor _ n).map ((baseSections Z').map t)).hom
        ((lerayCohomologyIso h C' n).hom
          (((DerivedCategory.homologyFunctor _ n).map ((baseSections Z).map φ)).hom x)) := by
  rw [← map_map_comp_apply (baseSections Z) (DerivedCategory.homologyFunctor _ n), key,
    map_map_comp_apply (baseSections Z) (DerivedCategory.homologyFunctor _ n)]
  exact lerayCohomologyIso_naturality_apply h t n _

/-- **The pullback is natural**: a commuting square `φ ≫ h_*a' = a ≫ ψ` of morphisms of
complexes induces a commuting square on cohomology. -/
theorem cohomologyPullback_naturality
    {K L : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ}
    {K' L' : CochainComplex (SheafOfModules.{u} (structureSheafRing Z')) ℤ}
    (φ : K ⟶ (pushforwardComplex h).obj K') (ψ : L ⟶ (pushforwardComplex h).obj L')
    (a : K ⟶ L) (a' : K' ⟶ L') (hsq : φ ≫ (pushforwardComplex h).map a' = a ≫ ψ) (n : ℤ)
    (x : cohomologyModule (DerivedCategory.Q.obj K) n) :
    (cohomologyPullback h ψ n).hom
        (((DerivedCategory.homologyFunctor _ n).map ((baseSections Z).map
          (DerivedCategory.Q.map a))).hom x) =
      ((DerivedCategory.homologyFunctor _ n).map ((baseSections Z').map
          (DerivedCategory.Q.map a'))).hom ((cohomologyPullback h φ n).hom x) := by
  have key : DerivedCategory.Q.map a ≫ DerivedCategory.Q.map ψ ≫ pushforwardComparisonQ h L' =
      (DerivedCategory.Q.map φ ≫ pushforwardComparisonQ h K') ≫
        (derivedPushforward h).map (DerivedCategory.Q.map a') := by
    calc DerivedCategory.Q.map a ≫ DerivedCategory.Q.map ψ ≫ pushforwardComparisonQ h L'
        _ = DerivedCategory.Q.map (a ≫ ψ) ≫ pushforwardComparisonQ h L' :=
          (DerivedCategory.Q.map_comp_assoc a ψ _).symm
        _ = DerivedCategory.Q.map (φ ≫ (pushforwardComplex h).map a') ≫
            pushforwardComparisonQ h L' := by rw [hsq]
        _ = DerivedCategory.Q.map φ ≫ DerivedCategory.Q.map ((pushforwardComplex h).map a') ≫
            pushforwardComparisonQ h L' := DerivedCategory.Q.map_comp_assoc _ _ _
        _ = _ := by rw [pushforwardComparisonQ_naturality h a', Category.assoc]
  exact leray_homology_map_comp_apply h _ _ _ _ key n x

/-- **The pullback of the class of a global cocycle** is the class of the image cocycle: a
global cocycle `s` of `K` goes to the class of the cocycle `φ(s)` of `Γ(Z, h_*K') = Γ(Z', K')`. -/
theorem cohomologyPullback_globalClass
    {K : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ}
    {K' : CochainComplex (SheafOfModules.{u} (structureSheafRing Z')) ℤ}
    (φ : K ⟶ (pushforwardComplex h).obj K') (n : ℤ)
    (s : (sectionsComplex Z K).cycles n) (s' : (sectionsComplex Z' K').cycles n)
    (hs : ((sectionsComplex Z ((pushforwardComplex h).obj K')).iCycles n).hom
        ((HomologicalComplex.cyclesMap
          (((globalSections Z).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) n).hom s) =
      ((sectionsComplex Z' K').iCycles n).hom s') :
    (cohomologyPullback h φ n).hom (globalClass K n s) = globalClass K' n s' := by
  refine Eq.trans (congrArg (lerayCohomologyIso h (DerivedCategory.Q.obj K') n).hom
    ((map_map_comp_apply (baseSections Z) (DerivedCategory.homologyFunctor _ n) _ _ _).trans
      (congrArg _ (globalClass_map Z φ n s)))) ?_
  exact lerayCohomologyIso_globalClass h K' n _ s' hs

/-- The comparisons `h_* ⟶ Rh_*` along a composite, read on a morphism of complexes into the
direct image along the composite which agrees with the composite of two morphisms of
complexes. -/
theorem comparisonQ_comp_derivedPushforwardCompIso_inv (i : Z'' ⟶ Z')
    {K : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ}
    {K' : CochainComplex (SheafOfModules.{u} (structureSheafRing Z')) ℤ}
    {K'' : CochainComplex (SheafOfModules.{u} (structureSheafRing Z'')) ℤ}
    (φ : K ⟶ (pushforwardComplex h).obj K') (ψ : K' ⟶ (pushforwardComplex i).obj K'')
    (χ : K ⟶ (pushforwardComplex (i ≫ h)).obj K'')
    (hχ : χ ≫ pushforwardCompComplexHom i h K'' = φ ≫ (pushforwardComplex h).map ψ) :
    (DerivedCategory.Q.map χ ≫ pushforwardComparisonQ (i ≫ h) K'') ≫
      (derivedPushforwardCompIso i h).inv.app (DerivedCategory.Q.obj K'') =
      (DerivedCategory.Q.map φ ≫ pushforwardComparisonQ h K') ≫
        (derivedPushforward h).map (DerivedCategory.Q.map ψ ≫ pushforwardComparisonQ i K'') := by
  calc (DerivedCategory.Q.map χ ≫ pushforwardComparisonQ (i ≫ h) K'') ≫
        (derivedPushforwardCompIso i h).inv.app (DerivedCategory.Q.obj K'')
      _ = DerivedCategory.Q.map χ ≫ DerivedCategory.Q.map (pushforwardCompComplexHom i h K'') ≫
          pushforwardComparisonQ h ((pushforwardComplex i).obj K'') ≫
          (derivedPushforward h).map (pushforwardComparisonQ i K'') :=
        (Category.assoc _ _ _).trans (congrArg (DerivedCategory.Q.map χ ≫ ·)
          (pushforwardComparisonQ_comp i h K''))
      _ = DerivedCategory.Q.map (φ ≫ (pushforwardComplex h).map ψ) ≫
          pushforwardComparisonQ h ((pushforwardComplex i).obj K'') ≫
          (derivedPushforward h).map (pushforwardComparisonQ i K'') :=
        (DerivedCategory.Q.map_comp_assoc _ _ _).symm.trans (congrArg (fun t =>
          DerivedCategory.Q.map t ≫ pushforwardComparisonQ h ((pushforwardComplex i).obj K'') ≫
          (derivedPushforward h).map (pushforwardComparisonQ i K'')) hχ)
      _ = DerivedCategory.Q.map φ ≫ (DerivedCategory.Q.map ((pushforwardComplex h).map ψ) ≫
          pushforwardComparisonQ h ((pushforwardComplex i).obj K'')) ≫
          (derivedPushforward h).map (pushforwardComparisonQ i K'') :=
        (DerivedCategory.Q.map_comp_assoc _ _ _).trans
          (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm)
      _ = DerivedCategory.Q.map φ ≫ (pushforwardComparisonQ h K' ≫
          (derivedPushforward h).map (DerivedCategory.Q.map ψ)) ≫
          (derivedPushforward h).map (pushforwardComparisonQ i K'') :=
        congrArg (fun t => DerivedCategory.Q.map φ ≫ t ≫
          (derivedPushforward h).map (pushforwardComparisonQ i K''))
          (pushforwardComparisonQ_naturality h ψ)
      _ = (DerivedCategory.Q.map φ ≫ pushforwardComparisonQ h K') ≫
          (derivedPushforward h).map (DerivedCategory.Q.map ψ ≫ pushforwardComparisonQ i K'') :=
        (congrArg (DerivedCategory.Q.map φ ≫ ·) (Category.assoc _ _ _)).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (_ ≫ ·)
            ((derivedPushforward h).map_comp _ _).symm))

/-- **The pullback is compatible with composition**: for `i : Z'' ⟶ Z'` and `h : Z' ⟶ Z`, the
pullback along `i ≫ h` and a morphism of complexes `χ : K ⟶ (i ≫ h)_*K''` which is the
composite of `φ : K ⟶ h_*K'` and `h_*ψ` for `ψ : K' ⟶ i_*K''` is the pullback along `h` and `φ`
followed by the pullback along `i` and `ψ`. -/
theorem cohomologyPullback_comp (i : Z'' ⟶ Z')
    {K : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ}
    {K' : CochainComplex (SheafOfModules.{u} (structureSheafRing Z')) ℤ}
    {K'' : CochainComplex (SheafOfModules.{u} (structureSheafRing Z'')) ℤ}
    (φ : K ⟶ (pushforwardComplex h).obj K') (ψ : K' ⟶ (pushforwardComplex i).obj K'')
    (χ : K ⟶ (pushforwardComplex (i ≫ h)).obj K'')
    (hχ : χ ≫ pushforwardCompComplexHom i h K'' = φ ≫ (pushforwardComplex h).map ψ) (n : ℤ)
    (x : cohomologyModule (DerivedCategory.Q.obj K) n) :
    (cohomologyPullback (i ≫ h) χ n).hom x =
      (cohomologyPullback i ψ n).hom ((cohomologyPullback h φ n).hom x) := by
  have key := comparisonQ_comp_derivedPushforwardCompIso_inv h i φ ψ χ hχ
  refine Eq.trans (cohomologyPullback_apply (i ≫ h) χ n x) ?_
  refine Eq.trans (lerayCohomologyIso_comp i h (DerivedCategory.Q.obj K'') n _).symm ?_
  rw [leray_homology_map_comp_apply h _ _ _ _ key n x]
  rfl

/-- **The pullback along the identity is the identity**, for the identification
`K = (𝟙 Z)_*K`. Both sides are natural in `K`, so it suffices to treat a K-injective complex,
all of whose classes are classes of global cocycles. -/
theorem cohomologyPullback_id (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ)
    (n : ℤ) (x : cohomologyModule (DerivedCategory.Q.obj K) n) :
    (cohomologyPullback (𝟙 Z) ((modulePushforwardIdComplex Z).inv.app K) n).hom x = x := by
  obtain ⟨I, a, hI, ha⟩ := exists_quasiIso_isKInjective Z K
  have hid : ∀ y : cohomologyModule (DerivedCategory.Q.obj I) n,
      (cohomologyPullback (𝟙 Z) ((modulePushforwardIdComplex Z).inv.app I) n).hom y = y := by
    intro y
    obtain ⟨c, rfl⟩ := Stacks.Cohomology.DerivedGlobalCupProduct.exists_globalClass_of_isKInjective
      I hI n y
    refine cohomologyPullback_globalClass (𝟙 Z) _ n c c ?_
    exact ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
      (((globalSections Z).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((modulePushforwardIdComplex Z).inv.app I)) n) c
  have hnat := cohomologyPullback_naturality (𝟙 Z) ((modulePushforwardIdComplex Z).inv.app K)
    ((modulePushforwardIdComplex Z).inv.app I) a a
    ((modulePushforwardIdComplex Z).inv.naturality a).symm n x
  rw [hid] at hnat
  have : IsIso (DerivedCategory.Q.map a) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ a).2 ha
  exact ((ConcreteCategory.bijective_of_isIso ((DerivedCategory.homologyFunctor _ n).map
    ((baseSections Z).map (DerivedCategory.Q.map a)))).1 hnat).symm

/-- The transport of a direct image of complexes along an equality of morphisms of ringed
spaces. -/
def pushforwardComplexCongr {h₁ h₂ : Z' ⟶ Z} (e : h₁ = h₂)
    (K' : CochainComplex (SheafOfModules.{u} (structureSheafRing Z')) ℤ) :
    (pushforwardComplex h₁).obj K' ⟶ (pushforwardComplex h₂).obj K' :=
  eqToHom (congrArg (fun k => (pushforwardComplex k).obj K') e)

/-- On local sections the transport along an equality of morphisms does nothing. -/
theorem pushforwardComplexCongr_f_val_app_heq {h₁ h₂ : Z' ⟶ Z} (e : h₁ = h₂)
    (K' : CochainComplex (SheafOfModules.{u} (structureSheafRing Z')) ℤ) (n : ℤ)
    (U : (Opens Z.carrier)ᵒᵖ) (y : (((pushforwardComplex h₁).obj K').X n).val.obj U) :
    HEq (((pushforwardComplexCongr e K').f n).val.app U y) y := by
  subst e
  rfl

/-- The pullback along a morphism of ringed spaces is the pullback along an equal one, after
transport. -/
theorem cohomologyPullback_congr {h₁ h₂ : Z' ⟶ Z} (e : h₁ = h₂)
    {K : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ}
    {K' : CochainComplex (SheafOfModules.{u} (structureSheafRing Z')) ℤ}
    (φ : K ⟶ (pushforwardComplex h₁).obj K') (n : ℤ)
    (x : cohomologyModule (DerivedCategory.Q.obj K) n) :
    (cohomologyPullback h₁ φ n).hom x =
      (cohomologyPullback h₂ (φ ≫ pushforwardComplexCongr e K') n).hom x := by
  subst e
  rw [pushforwardComplexCongr, eqToHom_refl, Category.comp_id]

/-- **The pullback is compatible with composition**, for a morphism `l` of ringed spaces equal
to the composite `i ≫ k`: if on local sections `χ : K ⟶ l_*K''` is `k_*ψ` after
`φ : K ⟶ k_*K'`, the pullback along `l` and `χ` is the pullback along `k` and `φ` followed by
the pullback along `i` and `ψ`. -/
theorem cohomologyPullback_comp_of_heq (i : Z'' ⟶ Z') (k : Z' ⟶ Z) (l : Z'' ⟶ Z)
    (hl : i ≫ k = l)
    {K : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ}
    {K' : CochainComplex (SheafOfModules.{u} (structureSheafRing Z')) ℤ}
    {K'' : CochainComplex (SheafOfModules.{u} (structureSheafRing Z'')) ℤ}
    (φ : K ⟶ (pushforwardComplex k).obj K') (ψ : K' ⟶ (pushforwardComplex i).obj K'')
    (χ : K ⟶ (pushforwardComplex l).obj K'')
    (hχ : ∀ (n : ℤ) (U : (Opens Z.carrier)ᵒᵖ) (x : (K.X n).val.obj U),
      HEq ((χ.f n).val.app U x)
        ((((pushforwardComplex k).map ψ).f n).val.app U ((φ.f n).val.app U x)))
    (n : ℤ) (x : cohomologyModule (DerivedCategory.Q.obj K) n) :
    (cohomologyPullback l χ n).hom x =
      (cohomologyPullback i ψ n).hom ((cohomologyPullback k φ n).hom x) := by
  subst hl
  refine cohomologyPullback_comp k i φ ψ χ ?_ n x
  refine HomologicalComplex.hom_ext _ _ fun m => ?_
  ext U y
  exact eq_of_heq (hχ m U y)

/-- The direct image of a complex concentrated in degree `0` vanishes in every other degree. -/
theorem subsingleton_pushforwardComplex_single_X (k : Z' ⟶ Z)
    (M : SheafOfModules.{u} (structureSheafRing Z')) {n : ℤ} (hn : n ≠ 0)
    (U : (Opens Z.carrier)ᵒᵖ) :
    Subsingleton ((((pushforwardComplex k).obj
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M)).X n).val.obj U) := by
  have hZ : IsZero (((pushforwardComplex k).obj
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M)).X n) :=
    (StacksDraft.KFlat.modulePushforward k).map_isZero
      (HomologicalComplex.isZero_single_obj_X _ 0 M n hn)
  exact ModuleCat.isZero_iff_subsingleton.mp
    (((SheafOfModules.forget _) ⋙ PresheafOfModules.evaluation _ U).map_isZero hZ)

end General

/-! ### The morphism of ringed spaces of a square -/

section Square

variable {X X' X'' S S' S'' : Scheme.{u}}

/-- **A morphism of ringed spaces into `(X, f⁻¹𝒪_S)` is determined by its continuous map and its
composite with the projection to `S`**: the ring map out of `f⁻¹𝒪_S` is determined by its
adjoint under `f⁻¹ ⊣ f_*`, which is the composite with the unit. -/
theorem inverseImageBase_hom_ext (f : X ⟶ S) {Y : RingedSpace.{u, u}}
    {a b : Y ⟶ inverseImageBase f} (hbase : a.hom.base = b.hom.base)
    (h : a ≫ inverseImageBaseProjection f = b ≫ inverseImageBaseProjection f) : a = b := by
  obtain ⟨⟨ba, ca⟩⟩ := a
  obtain ⟨⟨bb, cb⟩⟩ := b
  change ba = bb at hbase
  subst hbase
  have hc : ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).unit.app
      S.sheaf).hom ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} f.base).map ca =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).unit.app
      S.sheaf).hom ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} f.base).map cb := by
    refine NatTrans.ext (funext fun U => ?_)
    refine (PresheafedSpace.congr_app (congrArg InducedCategory.Hom.hom h) U).trans ?_
    exact (congrArg (_ ≫ ·) ((congrArg Y.presheaf.map (eqToHom_refl _ _)).trans
      (Y.presheaf.map_id _))).trans (Category.comp_id _)
  have key : (ObjectProperty.homMk ca : (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} ba).obj Y.sheaf) = ObjectProperty.homMk cb := by
    exact ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv
      _ _).injective ((Adjunction.homEquiv_unit _ _ _ _).trans ((ObjectProperty.hom_ext _ hc).trans
        (Adjunction.homEquiv_unit _ _ _ _).symm))
  have hcab : ca = cb := congrArg (fun t => t.hom) key
  subst hcab
  rfl

/-- **The morphism of ringed spaces of the identity square is the identity.** -/
theorem inverseImageBaseMap_id (f : X ⟶ S) (w : 𝟙 X ≫ f = f ≫ 𝟙 S) :
    inverseImageBaseMap (𝟙 X) f f (𝟙 S) w = 𝟙 (inverseImageBase f) := by
  refine inverseImageBase_hom_ext f rfl ?_
  rw [inverseImageBaseMap_comp_inverseImageBaseProjection, Category.id_comp]
  exact Category.comp_id _

/-- **The morphism of ringed spaces of a pasted square is the composite** of those of the two
squares. -/
theorem inverseImageBaseMap_comp (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (w : g' ≫ f = f' ≫ g) (g'' : X'' ⟶ X') (f'' : X'' ⟶ S'') (h : S'' ⟶ S')
    (w' : g'' ≫ f' = f'' ≫ h) (w'' : (g'' ≫ g') ≫ f = f'' ≫ (h ≫ g)) :
    inverseImageBaseMap (g'' ≫ g') f'' f (h ≫ g) w'' =
      inverseImageBaseMap g'' f'' f' h w' ≫ inverseImageBaseMap g' f' f g w := by
  refine inverseImageBase_hom_ext f rfl ?_
  rw [inverseImageBaseMap_comp_inverseImageBaseProjection, Category.assoc,
    inverseImageBaseMap_comp_inverseImageBaseProjection, ← Category.assoc,
    inverseImageBaseMap_comp_inverseImageBaseProjection, Category.assoc]
  rfl

open Scheme.Hom in
/-- Pulling back an exact wedge `d b₁ ∧ ⋯ ∧ d bₚ` along the identity square does nothing. -/
theorem relativeDifferentialFormsPullback_id_of_isExactWedge (f : X ⟶ S)
    (w : 𝟙 X ≫ f = f ≫ 𝟙 S) :
    ∀ (p : ℕ) (U : X.Opens) (ω : Γ(relativeDifferentialForms f (p : ℤ), U)),
      SheafOfModules.IsExactWedge (deRhamAlgebras f) (op U) p ω →
      relativeDifferentialFormsPullback (𝟙 X) f f (𝟙 S) w (p : ℤ) U ω = ω := by
  intro p
  induction p with
  | zero =>
      intro U ω hω
      have hω' : ω = (relativeDifferentialFormsAlgebra f).one.eval (op U) := hω
      subst hω'
      exact relativeDifferentialFormsPullback_one (𝟙 X) f f (𝟙 S) w U
  | succ p ih =>
      intro U ω hω
      obtain ⟨b, η, hη, hheq⟩ := hω
      refine eq_of_heq ((relativeDifferentialFormsPullback_heq (𝟙 X) f f (𝟙 S) w
        (show ((p + 1 : ℕ) : ℤ) = 1 + (p : ℤ) by push_cast; ring) U hheq).trans ?_)
      refine HEq.trans (heq_of_eq ((relativeDifferentialFormsPullback_mul (𝟙 X) f f (𝟙 S) w 1
        (p : ℤ) U _ η).trans ?_)) hheq.symm
      rw [relativeDifferentialFormsPullback_exactOne, ih U η hη, Scheme.Hom.id_app]
      rfl

open Scheme.Hom in
/-- **Pulling back a relative differential form along the identity square does nothing.** Both
sides are additive and natural, and they agree on the multiples of the exact wedges, which
generate the sheaf of differential forms locally. -/
theorem relativeDifferentialFormsPullback_id (f : X ⟶ S) (w : 𝟙 X ≫ f = f ≫ 𝟙 S) (p : ℕ)
    (U : X.Opens) (ω : Γ(relativeDifferentialForms f (p : ℤ), U)) :
    relativeDifferentialFormsPullback (𝟙 X) f f (𝟙 S) w (p : ℤ) U ω = ω := by
  refine SheafOfModules.eq_of_exactWedges (deRhamAlgebras f) p
    (N := (deRhamAlgebras f).exteriorPower p)
    (fun V => AddMonoidHom.mk' (fun x => relativeDifferentialFormsPullback (𝟙 X) f f (𝟙 S) w
      (p : ℤ) V.unop x) (relativeDifferentialFormsPullback_add (𝟙 X) f f (𝟙 S) w (p : ℤ) V.unop))
    (fun V => AddMonoidHom.id _) ?_ ?_ ?_ (op U) ω
  · intro V W i x
    exact relativeDifferentialFormsPullback_map (𝟙 X) f f (𝟙 S) w (p : ℤ) i.unop.le x
  · intro V W i x
    rfl
  · intro V b η hη
    refine (relativeDifferentialFormsPullback_smul (𝟙 X) f f (𝟙 S) w (p : ℤ) V.unop b η).trans ?_
    refine (congrArg (fun z => (Scheme.Hom.app (𝟙 X) V.unop).hom b • z)
      (relativeDifferentialFormsPullback_id_of_isExactWedge f w p V.unop η hη)).trans ?_
    congr 1

end Square

/-! ### The pullback on Hodge cohomology -/

section Hodge

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- The sheaf `Ω^p_{X/S}` of relative differential `p`-forms, as a sheaf of `f⁻¹𝒪_S`-modules,
placed in degree `0`; its cohomology is the Hodge cohomology `H^q(X, Ω^p_{X/S})`. -/
abbrev formsSingle (f : X ⟶ S) (p : ℕ) :
    CochainComplex (SheafOfModules.{u} (structureSheafRing (inverseImageBase f))) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj ((Scheme.Hom.deRhamComplex f).X p)

/-- **The canonical map `Ω^p_{X/S}[0] ⟶ g₀_*(Ω^p_{X'/S'}[0])`** of a commutative square, where
`g₀ : (X', f'⁻¹𝒪_{S'}) ⟶ (X, f⁻¹𝒪_S)` is the morphism of ringed spaces of the square: the
canonical map of differential forms of Tag 07HX placed in degree `0`. -/
def formsSinglePushforward (p : ℕ) :
    formsSingle f p ⟶
      (pushforwardComplex (inverseImageBaseMap g' f' f g w)).obj (formsSingle f' p) :=
  HomologicalComplex.mkHomFromSingle
    (formsPushforward g' f' f g w p ≫
      (StacksDraft.KFlat.modulePushforward (inverseImageBaseMap g' f' f g w)).map
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((Scheme.Hom.deRhamComplex f').X p)).inv)
    (fun k _ => by
      have hd : ((pushforwardComplex (inverseImageBaseMap g' f' f g w)).obj
          (formsSingle f' p)).d 0 k = 0 :=
        (congrArg (StacksDraft.KFlat.modulePushforward (inverseImageBaseMap g' f' f g w)).map
          (HomologicalComplex.single_obj_d _ _ _ _ _)).trans (Functor.map_zero _ _ _)
      exact (congrArg (_ ≫ ·) hd).trans Limits.comp_zero)

/-- **The ring map `Γ(X, f⁻¹𝒪_S) ⟶ Γ(X', f'⁻¹𝒪_{S'})` of a commutative square**, over which the
pullback on Hodge cohomology is semilinear: the ring map on global sections of the morphism of
ringed spaces of the square. -/
def hodgeBaseRingHom :
    (underlyingRingSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)).obj.obj
        (op ⊤) →+*
      (underlyingRingSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} f'.base).obj S'.sheaf)).obj.obj
        (op ⊤) :=
  (globalRingHom (inverseImageBaseMap g' f' f g w)).hom

/-- **The pullback on Hodge cohomology** `g'^* : H^q(X, Ω^p_{X/S}) ⟶ H^q(X', Ω^p_{X'/S'})` of
a commutative square (Section 50.5, Tag 0FM4): the canonical map `Ω^p_{X/S} ⟶ g₀_*Ω^p_{X'/S'}`,
followed by the comparison `g₀_* ⟶ Rg₀_*` and the Leray identification
`H^q(X, Rg₀_* -) = H^q(X', -)`. It is additive and semilinear over `hodgeBaseRingHom`. -/
def hodgePullback (p : ℕ) (q : ℤ) :
    hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras f) p q →ₛₗ[hodgeBaseRingHom g' f' f g w]
      hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras f') p q where
  toFun x := (cohomologyPullback (inverseImageBaseMap g' f' f g w)
    (formsSinglePushforward g' f' f g w p) q).hom x
  map_add' x y := map_add _ x y
  map_smul' a x := (cohomologyPullback (inverseImageBaseMap g' f' f g w)
    (formsSinglePushforward g' f' f g w p) q).hom.map_smul a x

/-- `hodgePullback g' f' f g w p q` acts on a class `x` as `cohomologyPullback` of the canonical
map `Ω^p_{X/S}[0] ⟶ g₀_*(Ω^p_{X'/S'}[0])` in degree `q`. -/
theorem hodgePullback_apply (p : ℕ) (q : ℤ)
    (x : hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras f) p q) :
    hodgePullback g' f' f g w p q x =
      (cohomologyPullback (inverseImageBaseMap g' f' f g w)
        (formsSinglePushforward g' f' f g w p) q).hom x :=
  rfl

/-- The degree-`0` component of the canonical map `Ω^p_{X/S}[0] ⟶ g₀_*(Ω^p_{X'/S'}[0])`. -/
theorem formsSinglePushforward_f_zero (p : ℕ) :
    (formsSinglePushforward g' f' f g w p).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((Scheme.Hom.deRhamComplex f).X p)).hom ≫ formsPushforward g' f' f g w p ≫
        (StacksDraft.KFlat.modulePushforward (inverseImageBaseMap g' f' f g w)).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            ((Scheme.Hom.deRhamComplex f').X p)).inv :=
  HomologicalComplex.mkHomFromSingle_f _ _

/-- On local sections the canonical map in degree `0` is the pullback of differential forms. -/
theorem formsSinglePushforward_f_zero_val_app (p : ℕ)
    (U : (Opens (inverseImageBase f).carrier)ᵒᵖ) (x : ((formsSingle f p).X 0).val.obj U) :
    ((formsSinglePushforward g' f' f g w p).f 0).val.app U x =
      Scheme.Hom.relativeDifferentialFormsPullback g' f f' g w (p : ℤ) U.unop x :=
  congrArg (fun t : (formsSingle f p).X 0 ⟶
      ((pushforwardComplex (inverseImageBaseMap g' f' f g w)).obj (formsSingle f' p)).X 0 =>
        t.val.app U x) (formsSinglePushforward_f_zero g' f' f g w p)

/-- `formsSinglePushforward_f_zero_val_app`, read as a heterogeneous equality. -/
theorem formsSinglePushforward_f_zero_val_app_heq (p : ℕ)
    (U : (Opens (inverseImageBase f).carrier)ᵒᵖ) (x : ((formsSingle f p).X 0).val.obj U) :
    HEq (((formsSinglePushforward g' f' f g w p).f 0).val.app U x)
      (Scheme.Hom.relativeDifferentialFormsPullback g' f f' g w (p : ℤ) U.unop x) :=
  heq_of_eq (formsSinglePushforward_f_zero_val_app g' f' f g w p U x)

/-! #### The identity square -/

/-- On local sections the canonical map of the identity square in degree `0` is the identity. -/
theorem formsSinglePushforward_id_f_zero_val_app (f : X ⟶ S) (w : 𝟙 X ≫ f = f ≫ 𝟙 S) (p : ℕ)
    (U : (Opens X.carrier)ᵒᵖ) (x : ((formsSingle f p).X 0).val.obj U) :
    ((formsSinglePushforward (𝟙 X) f f (𝟙 S) w p).f 0).val.app U x = x := by
  exact (formsSinglePushforward_f_zero_val_app (𝟙 X) f f (𝟙 S) w p U x).trans
    (relativeDifferentialFormsPullback_id f w p U.unop x)

/-- **The canonical map of the identity square is the identification `K = (𝟙)_*K`**, after
transport along `inverseImageBaseMap_id`. -/
theorem formsSinglePushforward_id (f : X ⟶ S) (w : 𝟙 X ≫ f = f ≫ 𝟙 S) (p : ℕ) :
    formsSinglePushforward (𝟙 X) f f (𝟙 S) w p ≫
      pushforwardComplexCongr (inverseImageBaseMap_id f w) (formsSingle f p) =
      (modulePushforwardIdComplex (inverseImageBase f)).inv.app (formsSingle f p) := by
  refine HomologicalComplex.from_single_hom_ext ?_
  ext U x
  have h3 := pushforwardComplexCongr_f_val_app_heq (inverseImageBaseMap_id f w)
    (formsSingle f p) 0 U (((formsSinglePushforward (𝟙 X) f f (𝟙 S) w p).f 0).val.app U x)
  have h4 := formsSinglePushforward_id_f_zero_val_app f w p U x
  have hR : (((modulePushforwardIdComplex (inverseImageBase f)).inv.app (formsSingle f p)).f
      0).val.app U x = x := rfl
  exact eq_of_heq ((h3.trans (heq_of_eq h4)).trans (heq_of_eq hR).symm)

/-- The pullback along the canonical map of the identity square is the identity, on the
cohomology of `Ω^p_{X/S}[0]`. -/
theorem cohomologyPullback_formsSinglePushforward_id (f : X ⟶ S) (w : 𝟙 X ≫ f = f ≫ 𝟙 S)
    (p : ℕ) (q : ℤ) (x : cohomologyModule (DerivedCategory.Q.obj (formsSingle f p)) q) :
    (cohomologyPullback (inverseImageBaseMap (𝟙 X) f f (𝟙 S) w)
      (formsSinglePushforward (𝟙 X) f f (𝟙 S) w p) q).hom x = x := by
  have h1 := cohomologyPullback_congr (inverseImageBaseMap_id f w)
    (formsSinglePushforward (𝟙 X) f f (𝟙 S) w p) q x
  have h2 := cohomologyPullback_id (formsSingle f p) q x
  rw [formsSinglePushforward_id f w p] at h1
  exact h1.trans h2

/-- **The identity square induces the identity on Hodge cohomology**:
`(𝟙 X)^* = id` on `H^q(X, Ω^p_{X/S})`. -/
theorem hodgePullback_id (f : X ⟶ S) (w : 𝟙 X ≫ f = f ≫ 𝟙 S) (p : ℕ) (q : ℤ)
    (x : hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras f) p q) :
    hodgePullback (𝟙 X) f f (𝟙 S) w p q x = x :=
  cohomologyPullback_formsSinglePushforward_id f w p q x

/-- The ring map of the identity square is the identity. -/
theorem hodgeBaseRingHom_id (f : X ⟶ S) (w : 𝟙 X ≫ f = f ≫ 𝟙 S) :
    hodgeBaseRingHom (𝟙 X) f f (𝟙 S) w = RingHom.id _ := by
  ext a
  change ((inverseImageBaseMap (𝟙 X) f f (𝟙 S) w).hom.c.app (op ⊤)).hom a = a
  rw [inverseImageBaseMap_id]
  rfl

/-! #### Pasting two squares -/

section Comp

variable {X'' S'' : Scheme.{u}} (g'' : X'' ⟶ X') (f'' : X'' ⟶ S'') (h : S'' ⟶ S')
  (w' : g'' ≫ f' = f'' ≫ h) (w'' : (g'' ≫ g') ≫ f = f'' ≫ (h ≫ g))

/-- On local sections in degree `0`, the canonical map of the square `g'` followed by the direct
image of that of the square `g''` is the pullback of forms along `g'` followed by that along
`g''`. -/
theorem formsSinglePushforward_comp_val_app (p : ℕ)
    (U : (Opens (inverseImageBase f).carrier)ᵒᵖ) (x : ((formsSingle f p).X 0).val.obj U) :
    (((pushforwardComplex (inverseImageBaseMap g' f' f g w)).map
        (formsSinglePushforward g'' f'' f' h w' p)).f 0).val.app U
        (((formsSinglePushforward g' f' f g w p).f 0).val.app U x) =
      Scheme.Hom.relativeDifferentialFormsPullback g'' f' f'' h w' (p : ℤ) (g' ⁻¹ᵁ U.unop)
        (Scheme.Hom.relativeDifferentialFormsPullback g' f f' g w (p : ℤ) U.unop x) :=
  (formsSinglePushforward_f_zero_val_app g'' f'' f' h w' p
    (op (g' ⁻¹ᵁ U.unop)) (((formsSinglePushforward g' f' f g w p).f 0).val.app U x)).trans
    (congrArg _ (formsSinglePushforward_f_zero_val_app g' f' f g w p U x))

/-- On local sections in degree `0`, the canonical map of the square `g'` followed by the direct
image of that of the square `g''` is the pullback of forms along the pasted square. -/
theorem formsSinglePushforward_comp_val_app_heq (p : ℕ)
    (U : (Opens (inverseImageBase f).carrier)ᵒᵖ) (x : ((formsSingle f p).X 0).val.obj U) :
    HEq ((((pushforwardComplex (inverseImageBaseMap g' f' f g w)).map
        (formsSinglePushforward g'' f'' f' h w' p)).f 0).val.app U
        (((formsSinglePushforward g' f' f g w p).f 0).val.app U x))
      (Scheme.Hom.relativeDifferentialFormsPullback (g'' ≫ g') f f'' (h ≫ g) w'' (p : ℤ) U.unop
        x) :=
  heq_of_eq ((formsSinglePushforward_comp_val_app g' f' f g w g'' f'' h w' p U x).trans
    (Stacks.Gysin.relativeDifferentialFormsPullback_comp g' g'' f f' f'' g h (h ≫ g)
      w w' w'' (p : ℤ) U.unop x).symm)

/-- **The canonical map of the pasted square is the composite of the canonical maps**, on local
sections in every degree. -/
theorem formsSinglePushforward_comp_heq (n : ℤ) (p : ℕ)
    (U : (Opens (inverseImageBase f).carrier)ᵒᵖ) (x : ((formsSingle f p).X n).val.obj U) :
    HEq (((formsSinglePushforward (g'' ≫ g') f'' f (h ≫ g) w'' p).f n).val.app U x)
      ((((pushforwardComplex (inverseImageBaseMap g' f' f g w)).map
        (formsSinglePushforward g'' f'' f' h w' p)).f n).val.app U
        (((formsSinglePushforward g' f' f g w p).f n).val.app U x)) := by
  by_cases hn : n = 0
  · subst hn
    exact (formsSinglePushforward_f_zero_val_app_heq (g'' ≫ g') f'' f (h ≫ g) w'' p U x).trans
      (formsSinglePushforward_comp_val_app_heq g' f' f g w g'' f'' h w' w'' p U x).symm
  · have := subsingleton_pushforwardComplex_single_X
      (inverseImageBaseMap (g'' ≫ g') f'' f (h ≫ g) w'') ((Scheme.Hom.deRhamComplex f'').X p) hn U
    exact @Subsingleton.helim _ _ this (congrArg (fun k => (((((pushforwardComplex k).obj
      (formsSingle f'' p)).X n).val.obj U : ModuleCat _) : Type u))
      (inverseImageBaseMap_comp g' f' f g w g'' f'' h w' w'')) _ _

/-- **Pasting two squares induces the composite of the pullbacks on Hodge cohomology**:
`(g'' ≫ g')^* = g''^* ∘ g'^*` on `H^q(X, Ω^p_{X/S})`. -/
theorem hodgePullback_comp (p : ℕ) (q : ℤ)
    (x : hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras f) p q) :
    hodgePullback (g'' ≫ g') f'' f (h ≫ g) w'' p q x =
      hodgePullback g'' f'' f' h w' p q (hodgePullback g' f' f g w p q x) :=
  cohomologyPullback_comp_of_heq (inverseImageBaseMap g'' f'' f' h w')
    (inverseImageBaseMap g' f' f g w) (inverseImageBaseMap (g'' ≫ g') f'' f (h ≫ g) w'')
    (inverseImageBaseMap_comp g' f' f g w g'' f'' h w' w'').symm _ _ _
    (fun n U y => formsSinglePushforward_comp_heq g' f' f g w g'' f'' h w' w'' n p U y) q x

/-- The ring map of the pasted square is the composite of the ring maps of the two squares. -/
theorem hodgeBaseRingHom_comp :
    hodgeBaseRingHom (g'' ≫ g') f'' f (h ≫ g) w'' =
      (hodgeBaseRingHom g'' f'' f' h w').comp (hodgeBaseRingHom g' f' f g w) := by
  ext a
  change ((inverseImageBaseMap (g'' ≫ g') f'' f (h ≫ g) w'').hom.c.app (op ⊤)).hom a = _
  rw [inverseImageBaseMap_comp g' f' f g w g'' f'' h w' w'']
  rfl

end Comp

/-- The pullback depends on the lower morphism of the square only through the morphism
itself. -/
theorem hodgePullback_congr_base {g₁ g₂ : S' ⟶ S} (hg : g₁ = g₂) (w₁ : g' ≫ f = f' ≫ g₁)
    (w₂ : g' ≫ f = f' ≫ g₂) (p : ℕ) (q : ℤ)
    (x : hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras f) p q) :
    hodgePullback g' f' f g₁ w₁ p q x = hodgePullback g' f' f g₂ w₂ p q x := by
  subst hg
  rfl

/-- **Functoriality of the pullback for squares over the identity of the base**, the form in
which datum (D1) uses it for schemes over `Spec k`: for morphisms `g'' : X'' ⟶ X'` and
`g' : X' ⟶ X` of `S`-schemes, `(g'' ≫ g')^* = g''^* ∘ g'^*` on `H^q(X, Ω^p_{X/S})`. -/
theorem hodgePullback_comp_overBase {X'' : Scheme.{u}} (fX : X ⟶ S) (fX' : X' ⟶ S)
    (fX'' : X'' ⟶ S) (g'' : X'' ⟶ X') (w : g' ≫ fX = fX' ≫ 𝟙 S)
    (w' : g'' ≫ fX' = fX'' ≫ 𝟙 S) (w'' : (g'' ≫ g') ≫ fX = fX'' ≫ 𝟙 S) (p : ℕ) (q : ℤ)
    (x : hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras fX) p q) :
    hodgePullback (g'' ≫ g') fX'' fX (𝟙 S) w'' p q x =
      hodgePullback g'' fX'' fX' (𝟙 S) w' p q (hodgePullback g' fX' fX (𝟙 S) w p q x) :=
  (hodgePullback_congr_base (g'' ≫ g') fX'' fX (Category.comp_id (𝟙 S)).symm w''
      (by rw [w'', Category.id_comp]) p q x).trans
    (hodgePullback_comp g' fX' fX (𝟙 S) w g'' fX'' (𝟙 S) w' _ p q x)

/-- **The ring map of a square is compatible with the maps from the global sections of the
bases**: `Γ(S, 𝒪_S) ⟶ Γ(X, f⁻¹𝒪_S) ⟶ Γ(X', f'⁻¹𝒪_{S'})` is
`Γ(S, 𝒪_S) ⟶ Γ(S', 𝒪_{S'}) ⟶ Γ(X', f'⁻¹𝒪_{S'})`. -/
theorem hodgeBaseRingHom_comp_inverseImageGlobalSections :
    (hodgeBaseRingHom g' f' f g w).comp (Scheme.Hom.inverseImageGlobalSections f).hom =
      (Scheme.Hom.inverseImageGlobalSections f').hom.comp (g.app ⊤).hom := by
  have h := PresheafedSpace.congr_app (congrArg InducedCategory.Hom.hom
    (inverseImageBaseMap_comp_inverseImageBaseProjection g' f' f g w)) (op ⊤)
  have h' := (h.trans (congrArg (_ ≫ ·) ((congrArg (inverseImageBase f').presheaf.map
    (eqToHom_refl _ _)).trans ((inverseImageBase f').presheaf.map_id _)))).trans
    (Category.comp_id _)
  ext a
  exact congrArg (fun t => t.hom a) h'

/-- For a square over the identity of the base, the ring map is compatible with the maps from
`Γ(S, 𝒪_S)`: the pullback is `Γ(S, 𝒪_S)`-linear. -/
theorem hodgeBaseRingHom_comp_inverseImageGlobalSections_overBase (fX : X ⟶ S) (fX' : X' ⟶ S)
    (w : g' ≫ fX = fX' ≫ 𝟙 S) :
    (hodgeBaseRingHom g' fX' fX (𝟙 S) w).comp (Scheme.Hom.inverseImageGlobalSections fX).hom =
      (Scheme.Hom.inverseImageGlobalSections fX').hom := by
  rw [hodgeBaseRingHom_comp_inverseImageGlobalSections, Scheme.Hom.id_app]
  rfl

end Hodge

end Stacks.HodgeWeil

end
