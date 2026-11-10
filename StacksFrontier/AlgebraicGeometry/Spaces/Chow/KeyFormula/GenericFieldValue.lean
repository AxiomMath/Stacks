module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.GenericFieldPointChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.GenericResidueField
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.StructureSheafCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicGenericPointValue
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullbackValue
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionValueDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackChartGeneratorMultiple
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceRationalFunctionChart
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction

/-!
# The value at the generic point of a prime divisor of a meromorphic section of `ℒ|_Z`

Let `X` be a decent algebraic space over a scheme `S`, let `Z ⊂ X` be a prime divisor with
generic point `ξ`, let `(U, u)` be the chosen affine elementary étale neighbourhood of `ξ` and let
`ℒ` be an invertible `𝒪_X`-module, with the chosen generator `s_ξ` of its pullback to
`Spec 𝒪_{U, u}` (`AlgebraicGeometry.Space.PrimeDivisor.genericStalkGenerator`).

Section 0EQU reads a generator of `ℒ_ξ` in the fibre `ℒ_ξ ⊗ κ(ξ)`, as a meromorphic section of
the restriction `ℒ|_Z`.  This file builds the reading in the other direction, which is the one
that can be made canonical: a meromorphic section `σ` of `ℒ|_Z` is pulled back along
`ρ_Z : Spec κ(u) → Z` (`AlgebraicGeometry.Space.PrimeDivisor.genericFieldPoint`), where the
pullback of `ℒ|_Z` is trivialised by the image of `s_ξ` under the closed point
`Spec κ(u) → Spec 𝒪_{U, u}`; the coefficient of the pullback of `σ` against that image is an
element of `κ(u)`, the **value of `σ` at the generic point of `Z`**.

The trivialisation is canonical: `ρ_Z` followed by the inclusion of `Z` is the closed point
followed by `j : Spec 𝒪_{U, u} → X`, so the pullback of `ℒ|_Z` along `ρ_Z` is identified, by the
composition isomorphisms of inverse images (Stacks 03LU), with the pullback along the closed
point of `j^*ℒ`, which the chosen trivialisation of `j^*ℒ` trivialises.

## Main definitions

* `AlgebraicGeometry.Space.PrimeDivisor.restrictModule`: the restriction `ℒ|_Z`, the inverse
  image of `ℒ` along the closed immersion `Z → X`.
* `AlgebraicGeometry.Space.PrimeDivisor.genericFieldMorphism`: `ρ_Z : Spec κ(u) → Z` as a
  morphism of algebraic spaces, and
  `AlgebraicGeometry.Space.PrimeDivisor.genericFieldToStalk` the closed point
  `Spec κ(u) → Spec 𝒪_{U, u}`.
* `AlgebraicGeometry.Space.PrimeDivisor.genericFieldPullbackIso`: the identification
  `c^*(j^*ℒ) ≅ ρ_Z^*(ℒ|_Z)` of the two inverse images of `ℒ` to `Spec κ(u)`.
* `AlgebraicGeometry.Space.PrimeDivisor.genericFibreGenerator`: **the image `s_ξ|_Z` of `s_ξ` in
  the fibre**, the inverse image of `s_ξ` along the closed point read through that
  identification; `AlgebraicGeometry.Space.PrimeDivisor.genericFieldGenerator` is its family of
  restrictions, a free generator of `ρ_Z^*(ℒ|_Z)` over every chart of `Spec κ(u)`.
* `AlgebraicGeometry.Space.PrimeDivisor.genericFieldMeromorphicEquiv`: the meromorphic functions
  on `Spec κ(u)` are `κ(u)`.
* `AlgebraicGeometry.Space.PrimeDivisor.genericFieldValue`: the value at the generic point of
  `Z` of a meromorphic section of `ℒ|_Z`.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.genericFieldMorphism_comp_inclusion`: `ρ_Z` followed by
  the inclusion of `Z` is the closed point followed by `j`.
* `AlgebraicGeometry.Space.PrimeDivisor.genericFieldValue_spec` and
  `AlgebraicGeometry.Space.PrimeDivisor.genericFieldValue_eq_iff`: the defining property of the
  value, that the pullback of `σ` along `ρ_Z` is its value times the image of `s_ξ`.

## References

* [Stacks Project, Section 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule

/-- **A ring which is a field is its own total ring of fractions**: the structure map into any
total ring of fractions of it is bijective, every nonzerodivisor being a unit. -/
theorem bijective_algebraMap_of_isField_of_isFractionRing {R K : Type*} [CommRing R]
    [CommRing K] [Algebra R K] [IsFractionRing R K] (hR : IsField R) :
    Function.Bijective (algebraMap R K) := by
  have : Nontrivial R := ⟨hR.exists_pair_ne⟩
  refine ⟨IsFractionRing.injective R K, fun x => ?_⟩
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective R⁰ x
  obtain ⟨c, hc⟩ := hR.mul_inv_cancel (nonZeroDivisors.ne_zero b.2)
  refine ⟨a * c, ?_⟩
  rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, mul_assoc, mul_comm c, hc, mul_one]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)

/-! ### Free generators of a trivial module -/

section Trivial

variable {Y : AlgebraicSpaces B S hS} (M : Modules.{u, u} B S hS Y.1 Y.2)

/-- The chart ring of a field chart is not trivial. -/
theorem not_subsingleton_of_isField_chartRing (V : SmallEtale B S hS Y.1)
    (hV : IsField (chartRing B S hS Y.1 Y.2 V)) : ¬ Subsingleton (chartRing B S hS Y.1 Y.2 V) :=
  fun _ => hV.exists_pair_ne.elim fun x hx => hx.elim fun y hxy => hxy (Subsingleton.elim x y)

/-- The components of an isomorphism of modules are mutually inverse. -/
private theorem inv_app_hom_app_apply {M N : Modules.{u, u} B S hS Y.1 Y.2} (e : M ≅ N)
    (W : SmallEtale B S hS Y.1) (z : M.val.obj (op W)) :
    (e.inv.val.app (op W)).hom ((e.hom.val.app (op W)).hom z) = z :=
  ConcreteCategory.congr_hom (congrArg (fun χ => χ.val.app (op W)) e.hom_inv_id) z

/-- The components of an isomorphism of modules are injective. -/
theorem injective_app_of_iso {M N : Modules.{u, u} B S hS Y.1 Y.2} (e : M ≅ N)
    (W : SmallEtale B S hS Y.1) : Function.Injective (e.hom.val.app (op W)).hom := fun x y hxy => by
  rw [← inv_app_hom_app_apply B S hS e W x, ← inv_app_hom_app_apply B S hS e W y, hxy]

/-- A module trivialised by `T` all of whose sections over `W` vanish has a trivial chart ring
over `W`. -/
theorem subsingleton_chartRing_of_trivialisation_of_forall_eq_zero
    (T : M ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O))
    (W : SmallEtale B S hS Y.1) (h : ∀ y : M.val.obj (op W), y = 0) :
    Subsingleton (chartRing B S hS Y.1 Y.2 W) := by
  have hφψ := inv_app_hom_app_apply B S hS T.symm W
  have key : ∀ a, (T.hom.val.app (op W)).hom ((T.inv.val.app (op W)).hom a) = 0 := fun a =>
    (congrArg (T.hom.val.app (op W)).hom (h _)).trans (T.hom.val.app (op W)).hom.map_zero
  exact ⟨fun a b => ((hφψ a).symm.trans (key a)).trans ((hφψ b).symm.trans (key b)).symm⟩

/-- A section over a chart all of whose restrictions to the members of a covering sieve live
over trivial chart rings is zero. -/
theorem eq_zero_of_forall_subsingleton_chartRing_of_sieve (V : SmallEtale B S hS Y.1)
    (T : Sieve V) (hT : T ∈ SmallEtale.topology B S hS Y.1 V)
    (hsub : ∀ ⦃W : SmallEtale B S hS Y.1⦄ (k : W ⟶ V), T k →
      Subsingleton (chartRing B S hS Y.1 Y.2 W)) (y : M.val.obj (op V)) : y = 0 :=
  eq_of_modules_map_eq_of_sieve B S hS Y M V T hT y 0 fun W k hk => by
    have := hsub k hk
    refine Eq.trans ?_ ((M.val.map k.op).hom.map_zero).symm
    let y' : M.val.obj (op W) := (M.val.map k.op).hom y
    change y' = 0
    rw [← one_smul (chartRing B S hS Y.1 Y.2 W) y',
      Subsingleton.elim (1 : chartRing B S hS Y.1 Y.2 W) 0, zero_smul]

/-- If multiplication by the zero section is bijective, the chart ring is trivial. -/
theorem subsingleton_chartRing_of_bijective_smul_eq_zero (W : SmallEtale B S hS Y.1)
    (m : M.val.obj (op W)) (hm : Function.Bijective fun r : chartRing B S hS Y.1 Y.2 W ↦ r • m)
    (h0 : m = 0) : Subsingleton (chartRing B S hS Y.1 Y.2 W) :=
  ⟨fun a b => hm.1 (by
    change a • m = b • m
    rw [h0, smul_zero, smul_zero])⟩

/-- **A nonzero section of a trivial module over a field chart freely generates it over every
chart over that chart**: under the trivialisation it is a nonzero element of a field, hence a
unit, and units stay units under restriction. -/
theorem bijective_smul_map_of_trivialisation
    (T : M ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O))
    (V : SmallEtale B S hS Y.1) (hV : IsField (chartRing B S hS Y.1 Y.2 V))
    (y : M.val.obj (op V)) (hy : y ≠ 0) {W : SmallEtale B S hS Y.1} (k : W ⟶ V) :
    Function.Bijective fun r : chartRing B S hS Y.1 Y.2 W ↦
      r • (show M.val.obj (op W) from (M.val.map k.op).hom y) := by
  let φ : ∀ W' : SmallEtale B S hS Y.1, M.val.obj (op W') → chartRing B S hS Y.1 Y.2 W' :=
    fun W' x => (T.hom.val.app (op W')).hom x
  let ψ : chartRing B S hS Y.1 Y.2 W → M.val.obj (op W) := fun x => (T.inv.val.app (op W)).hom x
  have hψφ : ∀ x, ψ (φ W x) = x := inv_app_hom_app_apply B S hS T W
  have hne : φ V y ≠ 0 := fun h => hy
    (injective_app_of_iso B S hS T V (h.trans ((T.hom.val.app (op V)).hom.map_zero).symm))
  obtain ⟨z, hz⟩ := hV.mul_inv_cancel hne
  have hu : φ W ((M.val.map k.op).hom y) * chartRestrict (hF := Y.2) k z = 1 := by
    have h1 : φ W ((M.val.map k.op).hom y) = chartRestrict (hF := Y.2) k (φ V y) :=
      PresheafOfModules.naturality_apply T.hom.val k.op y
    rw [h1, ← map_mul, hz, map_one]
  have hlin' : ∀ r : chartRing B S hS Y.1 Y.2 W,
      φ W (r • (show M.val.obj (op W) from (M.val.map k.op).hom y)) =
        r * φ W ((M.val.map k.op).hom y) := fun r => (T.hom.val.app (op W)).hom.map_smul r _
  refine ⟨fun r r' h => ?_, fun x => ⟨φ W x * chartRestrict (hF := Y.2) k z, ?_⟩⟩
  · have h' := congrArg (φ W) h
    simp only [hlin'] at h'
    simpa only [mul_assoc, hu, mul_one] using congrArg (· * chartRestrict (hF := Y.2) k z) h'
  · change (φ W x * chartRestrict (hF := Y.2) k z) •
      (show M.val.obj (op W) from (M.val.map k.op).hom y) = x
    refine (hψφ _).symm.trans ?_
    rw [hlin', mul_assoc, mul_comm (chartRestrict (hF := Y.2) k z), hu, mul_one, hψφ]

end Trivial

/-! ### The prime divisor as an algebraic space, and the restriction `ℒ|_Z` -/

/-- A prime divisor, as an algebraic space over `S`. -/
abbrev PrimeDivisor.space : AlgebraicSpaces B S hS :=
  ⟨Z.subspace.toFunctor, Z.closed.1⟩

/-- The closed immersion `Z → X` of a prime divisor. -/
abbrev PrimeDivisor.inclusion : Z.space B S hS ⟶ (⟨X, hX⟩ : AlgebraicSpaces B S hS) :=
  closedSubspaceHom B S hS hX Z.subspace Z.closed

/-- **The restriction `ℒ|_Z`** of an `𝒪_X`-module to a prime divisor: its inverse image of Stacks
03LU along the closed immersion `Z → X`. -/
abbrev PrimeDivisor.restrictModule (L : Modules.{u, u} B S hS X hX) :
    Modules.{u, u} B S hS Z.subspace.toFunctor Z.closed.1 :=
  (modulePullback B S hS (Z.inclusion B S hS hX)).obj L

/-! ### The field-valued point `ρ_Z` as a morphism of algebraic spaces -/

/-- The site object `Spec κ(u)` of the field-valued point `ρ_Z`. -/
abbrev PrimeDivisor.genericFieldSpec : BigFppfOver B S hS :=
  (Z.genericFieldPoint B S hS hX hdec).siteObject B S hS Z.subspace.toFunctor

/-- `Spec κ(u)` as an algebraic space over `S`. -/
abbrev PrimeDivisor.genericFieldSpace : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj (Z.genericFieldSpec B S hS hX hdec), isAlgebraicSpace_yoneda B S hS _⟩

/-- **`ρ_Z : Spec κ(u) → Z`** as a morphism of algebraic spaces. -/
def PrimeDivisor.genericFieldMorphism :
    Z.genericFieldSpace B S hS hX hdec ⟶ Z.space B S hS :=
  ObjectProperty.homMk (fieldMorphism B S hS Z.subspace.toFunctor
    (Z.genericFieldPoint B S hS hX hdec))

/-- Pullbacks of meromorphic functions are defined along `ρ_Z`, by Stacks 0EN9, part (1): it
represents the generic point of `Z`, a point of codimension `0`. -/
theorem PrimeDivisor.pullbacksMeromorphicSections_genericFieldMorphism :
    PullbacksMeromorphicSections B S hS (Z.genericFieldMorphism B S hS hX hdec).hom :=
  pullbacksMeromorphicSections_fieldMorphism_of_class_eq_genericPoint B S hS Z.closed.1 Z.integral
    _ (Z.class_genericFieldPoint B S hS hX hdec)

/-- **The closed point `Spec κ(u) → Spec 𝒪_{U, u}`**, as a morphism of the site. -/
def PrimeDivisor.genericFieldToStalkSpec :
    Z.genericFieldSpec B S hS hX hdec ⟶ Z.genericStalkSpec B S hS hX hdec :=
  Over.homMk (B.inclusion.preimage
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥(Z.genericStalkRing B S hS hX hdec))))) (by
    have h2 : B.inclusion.map (Z.genericStalkSpec B S hS hX hdec).hom =
        ((BigFppfOver.toScheme B S hS).obj (Z.genericChart B S hS hX hdec).scheme).fromSpecStalk
          (Z.genericChart B S hS hX hdec).point ≫
          B.inclusion.map (Z.genericChart B S hS hX hdec).scheme.hom := by
      rw [← Over.w (Z.genericStalkSpecToChart B S hS hX hdec), Functor.map_comp]
      exact congrArg (· ≫ _) (Z.toScheme_map_genericStalkSpecToChart B S hS hX hdec)
    apply B.inclusion.map_injective
    refine (B.inclusion.map_comp _ _).trans ?_
    refine (congrArg (· ≫ _) (B.inclusion.map_preimage _)).trans ?_
    refine (congrArg (_ ≫ ·) h2).trans ?_
    exact (Category.assoc _ _ _).symm)

/-- The underlying morphism of schemes of the closed point `Spec κ(u) → Spec 𝒪_{U, u}` is the
spectrum of the residue map. -/
theorem PrimeDivisor.toScheme_map_genericFieldToStalkSpec :
    (BigFppfOver.toScheme B S hS).map (Z.genericFieldToStalkSpec B S hS hX hdec) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥(Z.genericStalkRing B S hS hX hdec))) :=
  B.inclusion.map_preimage _

/-- The closed point followed by `Spec 𝒪_{U, u} → U` is the residue-field morphism of the chart. -/
theorem PrimeDivisor.genericFieldToStalkSpec_comp :
    Z.genericFieldToStalkSpec B S hS hX hdec ≫ Z.genericStalkSpecToChart B S hS hX hdec =
      residueFieldMap B S hS (Z.genericChart B S hS hX hdec).scheme
        (Z.genericChart B S hS hX hdec).point
        (Z.genericChart B S hS hX hdec).residueField_contained := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp, Z.toScheme_map_genericFieldToStalkSpec B S hS hX hdec,
    Z.toScheme_map_genericStalkSpecToChart B S hS hX hdec]
  rfl

/-- The closed point `Spec κ(u) → Spec 𝒪_{U, u}` as a morphism of algebraic spaces. -/
def PrimeDivisor.genericFieldToStalk :
    Z.genericFieldSpace B S hS hX hdec ⟶ Z.genericStalkSpace B S hS hX hdec :=
  ObjectProperty.homMk (yoneda.map (Z.genericFieldToStalkSpec B S hS hX hdec))

/-- **`ρ_Z` followed by the inclusion of `Z` is the closed point followed by
`j : Spec 𝒪_{U, u} → X`.** -/
theorem PrimeDivisor.genericFieldMorphism_comp_inclusion :
    Z.genericFieldMorphism B S hS hX hdec ≫ Z.inclusion B S hS hX =
      Z.genericFieldToStalk B S hS hX hdec ≫ Z.genericStalkMorphism B S hS hX hdec := by
  ext1
  change fieldMorphism B S hS Z.subspace.toFunctor (Z.genericFieldPoint B S hS hX hdec) ≫
      Z.subspace.ι =
    yoneda.map (Z.genericFieldToStalkSpec B S hS hX hdec) ≫
      yoneda.map (Z.genericStalkSpecToChart B S hS hX hdec) ≫
        (Z.genericChart B S hS hX hdec).toSpace
  rw [Z.fieldMorphism_genericFieldPoint_comp_ι B S hS hX hdec, ← Category.assoc,
    ← yoneda.map_comp, Z.genericFieldToStalkSpec_comp B S hS hX hdec]
  exact neighborhoodFieldPoint_morphism B S hS X hX _ _

/-! ### The trivialisation of `ρ_Z^*(ℒ|_Z)` -/

variable (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)

/-- **The identification `c^*(j^*ℒ) ≅ ρ_Z^*(ℒ|_Z)`** of the two inverse images of `ℒ` to
`Spec κ(u)`, by the composition isomorphisms of Stacks 03LU and the equality
`ρ_Z ≫ (Z → X) = c ≫ j`. -/
def PrimeDivisor.genericFieldPullbackIso :
    (modulePullback B S hS (Z.genericFieldToStalk B S hS hX hdec)).obj
        ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L) ≅
      (modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
        (Z.restrictModule B S hS hX L) :=
  (modulePullbackCompIso B S hS (Z.genericFieldToStalk B S hS hX hdec)
      (Z.genericStalkMorphism B S hS hX hdec)).app L ≪≫
    eqToIso (by rw [Z.genericFieldMorphism_comp_inclusion B S hS hX hdec]) ≪≫
    ((modulePullbackCompIso B S hS (Z.genericFieldMorphism B S hS hX hdec)
      (Z.inclusion B S hS hX)).app L).symm

/-- **A trivialisation of `ρ_Z^*(ℒ|_Z)`**, induced by the chosen trivialisation of the pullback
of `ℒ` to `Spec 𝒪_{U, u}`.  It is used only to see that the image of `s_ξ` is a free
generator. -/
def PrimeDivisor.genericFieldTrivialisation :
    (modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
        (Z.restrictModule B S hS hX L) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (Z.genericFieldSpace B S hS hX hdec).1 (Z.genericFieldSpace B S hS hX hdec).2).O) :=
  (Z.genericFieldPullbackIso B S hS hX hdec L).symm ≪≫
    (modulePullback B S hS (Z.genericFieldToStalk B S hS hX hdec)).mapIso
      (Z.genericStalkTrivialisation B S hS hX hdec L hL) ≪≫
    modulePullbackUnitIso B S hS (Z.genericFieldToStalk B S hS hX hdec)

/-- `Spec κ(u)` as the identity chart of the algebraic space it represents. -/
abbrev PrimeDivisor.genericFieldChart :
    SmallEtale B S hS (Z.genericFieldSpace B S hS hX hdec).1 :=
  idEtaleChart B S hS (Z.genericFieldSpec B S hS hX hdec)

/-- The chart diagram `(Spec κ(u), Spec 𝒪_{U, u})` over the closed point. -/
def PrimeDivisor.genericFieldToStalkChartDiagram :
    ChartDiagram B S hS (Z.genericFieldSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericFieldToStalk B S hS hX hdec).hom where
  U := Z.genericFieldChart B S hS hX hdec
  V := Z.genericStalkChart B S hS hX hdec
  g := Z.genericFieldToStalkSpec B S hS hX hdec
  comm := by
    change 𝟙 _ ≫ yoneda.map (Z.genericFieldToStalkSpec B S hS hX hdec) =
      yoneda.map (Z.genericFieldToStalkSpec B S hS hX hdec) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]

/-- **The image `s_ξ|_Z` of the generator `s_ξ` in the fibre at the generic point of `Z`**: the
inverse image of `s_ξ` along the closed point `c : Spec κ(u) → Spec 𝒪_{U, u}`, read in
`ρ_Z^*(ℒ|_Z)` through `c^*(j^*ℒ) ≅ ρ_Z^*(ℒ|_Z)`. -/
def PrimeDivisor.genericFibreGenerator :
    ((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
      (Z.restrictModule B S hS hX L)).val.obj (op (Z.genericFieldChart B S hS hX hdec)) :=
  modulePullbackChartValue B S hS (Z.genericFieldToStalk B S hS hX hdec)
    ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L) _
    (Z.genericFieldPullbackIso B S hS hX hdec L).hom
    (Z.genericFieldToStalkChartDiagram B S hS hX hdec)
    (Z.genericStalkGenerator B S hS hX hdec L hL (Z.genericStalkChart B S hS hX hdec)
      (𝟙 (Z.genericStalkChart B S hS hX hdec)))

/-- The regular functions on `Spec κ(u)` form a field. -/
theorem PrimeDivisor.isField_genericFieldSections :
    IsField ((structurePresheaf B S hS (Z.genericFieldSpace B S hS hX hdec).1).obj
        (op (Z.genericFieldChart B S hS hX hdec))) :=
  MulEquiv.isField (Field.toIsField (Z.genericResidueField B S hS hX hdec))
    (Scheme.ΓSpecIso (CommRingCat.of
      (Z.genericResidueField B S hS hX hdec))).commRingCatIsoToRingEquiv.toMulEquiv

/-- If the image of `s_ξ` in the fibre vanished, so would the restrictions of the inverse image
of `s_ξ` to every chart over `Spec κ(u)`. -/
theorem PrimeDivisor.modulePullbackChartSectionRestrict_eq_zero_of_genericFibreGenerator_eq_zero
    (h0 : Z.genericFibreGenerator B S hS hX hdec L hL = 0)
    {W : SmallEtale B S hS (Z.genericFieldSpace B S hS hX hdec).1}
    (k : W ⟶ Z.genericFieldChart B S hS hX hdec) :
    modulePullbackChartSectionRestrict B S hS (Z.genericFieldToStalk B S hS hX hdec)
      ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L)
      (Z.genericFieldToStalkChartDiagram B S hS hX hdec)
      (Z.genericStalkGenerator B S hS hX hdec L hL (Z.genericStalkChart B S hS hX hdec)
        (𝟙 (Z.genericStalkChart B S hS hX hdec))) k = 0 := by
  apply injective_app_of_iso B S hS (Z.genericFieldPullbackIso B S hS hX hdec L) W
  have hres := modulePullbackChartValue_restrict B S hS (Z.genericFieldToStalk B S hS hX hdec)
    ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L) _
    (Z.genericFieldPullbackIso B S hS hX hdec L).hom
    (Z.genericFieldToStalkChartDiagram B S hS hX hdec)
    (Z.genericStalkGenerator B S hS hX hdec L hL (Z.genericStalkChart B S hS hX hdec)
      (𝟙 (Z.genericStalkChart B S hS hX hdec))) k
  refine hres.symm.trans ?_
  have h1 : (((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
      (Z.restrictModule B S hS hX L)).val.map k.op).hom
        (Z.genericFibreGenerator B S hS hX hdec L hL) = 0 := by
    rw [h0]
    exact map_zero _
  exact h1.trans (map_zero _).symm

/-- **The image of `s_ξ` in the fibre is nonzero.**  The inverse image of the free generator
`s_ξ` is a free generator over a covering sieve of `Spec κ(u)`; if it vanished, the regular
functions over every member of that sieve would vanish, hence every section of `ρ_Z^*(ℒ|_Z)`
over `Spec κ(u)` would, by the sheaf property, while those sections are a copy of the field
`κ(u)`. -/
theorem PrimeDivisor.genericFibreGenerator_ne_zero :
    Z.genericFibreGenerator B S hS hX hdec L hL ≠ 0 := by
  intro h0
  obtain ⟨T, hT, hfree⟩ := exists_sieve_bijective_smul_modulePullbackChartSection B S hS
    (Z.genericFieldToStalk B S hS hX hdec)
    ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L)
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
      (modulePullbackInvertible (Z.genericStalkMorphism B S hS hX hdec) L hL))
    (Z.genericFieldToStalkChartDiagram B S hS hX hdec)
    (Z.genericStalkGenerator B S hS hX hdec L hL)
    (Z.genericStalkGenerator_compat B S hS hX hdec L hL)
    (Z.bijective_smul_genericStalkGenerator B S hS hX hdec L hL)
  refine not_subsingleton_of_isField_chartRing B S hS (Y := Z.genericFieldSpace B S hS hX hdec)
    (Z.genericFieldChart B S hS hX hdec) (Z.isField_genericFieldSections B S hS hX hdec)
    (subsingleton_chartRing_of_trivialisation_of_forall_eq_zero B S hS _
      (Z.genericFieldTrivialisation B S hS hX hdec L hL) _
      (eq_zero_of_forall_subsingleton_chartRing_of_sieve B S hS _ _ T hT fun W k hk => ?_))
  exact subsingleton_chartRing_of_bijective_smul_eq_zero B S hS _ W _ (hfree k hk W (𝟙 W))
    (Z.modulePullbackChartSectionRestrict_eq_zero_of_genericFibreGenerator_eq_zero B S hS hX hdec
      L hL h0 (𝟙 W ≫ k))

/-- **The image of `s_ξ` in the fibre, over every chart over `Spec κ(u)`**: its restriction
there. -/
def PrimeDivisor.genericFieldGenerator
    (W : SmallEtale B S hS (Z.genericFieldSpace B S hS hX hdec).1)
    (k : W ⟶ Z.genericFieldChart B S hS hX hdec) :
    ((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
      (Z.restrictModule B S hS hX L)).val.obj (op W) :=
  (((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
    (Z.restrictModule B S hS hX L)).val.map k.op).hom (Z.genericFibreGenerator B S hS hX hdec L hL)

/-- At `Spec κ(u)` itself the family is the image of `s_ξ` in the fibre. -/
theorem PrimeDivisor.genericFieldGenerator_id :
    Z.genericFieldGenerator B S hS hX hdec L hL (Z.genericFieldChart B S hS hX hdec)
        (𝟙 (Z.genericFieldChart B S hS hX hdec)) = Z.genericFibreGenerator B S hS hX hdec L hL :=
  congrArg (fun φ => φ.hom (Z.genericFibreGenerator B S hS hX hdec L hL))
    (((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
      (Z.restrictModule B S hS hX L)).val.map_id _)

/-- The image of `s_ξ` in the fibre is compatible with restriction. -/
theorem PrimeDivisor.genericFieldGenerator_compat
    (W W' : SmallEtale B S hS (Z.genericFieldSpace B S hS hX hdec).1)
    (k : W ⟶ Z.genericFieldChart B S hS hX hdec) (g : W' ⟶ W) :
    (((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
        (Z.restrictModule B S hS hX L)).val.map g.op).hom
        (Z.genericFieldGenerator B S hS hX hdec L hL W k) =
      Z.genericFieldGenerator B S hS hX hdec L hL W' (g ≫ k) :=
  (PresheafOfModules.map_comp_apply (((modulePullback B S hS
    (Z.genericFieldMorphism B S hS hX hdec)).obj (Z.restrictModule B S hS hX L)).val) k.op g.op
    (Z.genericFibreGenerator B S hS hX hdec L hL)).symm

/-- **The image of `s_ξ` in the fibre freely generates `ρ_Z^*(ℒ|_Z)` over every chart over
`Spec κ(u)`**: under a trivialisation it is a nonzero element of the field of regular functions
on `Spec κ(u)`, hence a unit, and units stay units under restriction. -/
theorem PrimeDivisor.bijective_smul_genericFieldGenerator
    (W : SmallEtale B S hS (Z.genericFieldSpace B S hS hX hdec).1)
    (k : W ⟶ Z.genericFieldChart B S hS hX hdec) :
    Function.Bijective fun r : chartRing B S hS (Z.genericFieldSpace B S hS hX hdec).1
        (Z.genericFieldSpace B S hS hX hdec).2 W ↦
      r • Z.genericFieldGenerator B S hS hX hdec L hL W k :=
  bijective_smul_map_of_trivialisation B S hS (Y := Z.genericFieldSpace B S hS hX hdec) _
    (Z.genericFieldTrivialisation B S hS hX hdec L hL)
    (Z.genericFieldChart B S hS hX hdec) (Z.isField_genericFieldSections B S hS hX hdec) _
    (Z.genericFibreGenerator_ne_zero B S hS hX hdec L hL) k

/-- **The meromorphic sections of `ρ_Z^*(ℒ|_Z)` over a chart of `Spec κ(u)` are the multiples of
the image of `s_ξ` by meromorphic functions**, uniquely. -/
theorem PrimeDivisor.bijective_genericFieldTmul
    (W : SmallEtale B S hS (Z.genericFieldSpace B S hS hX hdec).1)
    (k : W ⟶ Z.genericFieldChart B S hS hX hdec) :
    Function.Bijective fun a : (Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS (Z.genericFieldSpace B S hS hX hdec).1
        (Z.genericFieldSpace B S hS hX hdec).2).O).obj.obj (op W) ↦
      toMeromorphicSectionSheaf B S hS (Z.genericFieldSpace B S hS hX hdec).1
        (Z.genericFieldSpace B S hS hX hdec).2
        ((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
          (Z.restrictModule B S hS hX L)) W
        (a ⊗ₜ[chartRing B S hS (Z.genericFieldSpace B S hS hX hdec).1
            (Z.genericFieldSpace B S hS hX hdec).2 W]
          Z.genericFieldGenerator B S hS hX hdec L hL W k :
          (meromorphicSectionModule B S hS (Z.genericFieldSpace B S hS hX hdec).1
            (Z.genericFieldSpace B S hS hX hdec).2
            ((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
              (Z.restrictModule B S hS hX L))).obj (op W)) := by
  have h := bijective_toMeromorphicSectionSheaf_tmul B S hS
    (Z.genericFieldSpace B S hS hX hdec).1 (Z.genericFieldSpace B S hS hX hdec).2 _ W
    (fun W' (g : W' ⟶ W) ↦ Z.genericFieldGenerator B S hS hX hdec L hL W' (g ≫ k))
    (fun W₁ W₂ k₁ g ↦
      (Z.genericFieldGenerator_compat B S hS hX hdec L hL W₁ W₂ (k₁ ≫ k) g).trans
        (congrArg (Z.genericFieldGenerator B S hS hX hdec L hL W₂)
          (Category.assoc g k₁ k).symm))
    fun W₁ k₁ ↦ Z.bijective_smul_genericFieldGenerator B S hS hX hdec L hL W₁ (k₁ ≫ k)
  simpa only [Category.id_comp] using h

/-! ### The meromorphic functions on `Spec κ(u)` -/

/-- The algebra structure of the meromorphic functions on the chart `Spec κ(u)` over its regular
functions. -/
abbrev PrimeDivisor.genericFieldMeromorphicAlgebra :
    Algebra ((structurePresheaf B S hS (Z.genericFieldSpace B S hS hX hdec).1).obj
        (op (Z.genericFieldChart B S hS hX hdec)))
      ((meromorphicFunctionSheaf B S hS (Z.genericFieldSpace B S hS hX hdec).1
        (Z.genericFieldSpace B S hS hX hdec).2).obj.obj
          (op (Z.genericFieldChart B S hS hX hdec))) :=
  chartMeromorphicFunctionAlgebra B S hS (Z.genericFieldSpace B S hS hX hdec)
    (Z.genericFieldChart B S hS hX hdec)

attribute [local instance] PrimeDivisor.genericFieldMeromorphicAlgebra

/-- **The meromorphic functions on `Spec κ(u)` are the total ring of fractions of its regular
functions**, by Stacks 0EN6, part (2): the spectrum of a field is reduced and Noetherian. -/
theorem PrimeDivisor.isFractionRing_genericFieldMeromorphic :
    IsFractionRing ((structurePresheaf B S hS (Z.genericFieldSpace B S hS hX hdec).1).obj
        (op (Z.genericFieldChart B S hS hX hdec)))
      ((meromorphicFunctionSheaf B S hS (Z.genericFieldSpace B S hS hX hdec).1
        (Z.genericFieldSpace B S hS hX hdec).2).obj.obj
          (op (Z.genericFieldChart B S hS hX hdec))) := by
  have hred : HasEtaleLocalProperty B S hS (Z.genericFieldSpace B S hS hX hdec).1
      (fun T : Scheme.{u} ↦ IsReduced T) :=
    hasEtaleLocalProperty_of_representable B S hS _ _ (Z.genericFieldSpec B S hS hX hdec)
      (Iso.refl _) (inferInstanceAs (IsReduced (Spec (.of (Z.genericResidueField B S hS hX hdec)))))
  have hnoeth : HasEtaleLocalProperty B S hS (Z.genericFieldSpace B S hS hX hdec).1
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) :=
    hasEtaleLocalProperty_of_representable B S hS _ _ (Z.genericFieldSpec B S hS hX hdec)
      (Iso.refl _)
      (inferInstanceAs (IsLocallyNoetherian (Spec (.of (Z.genericResidueField B S hS hX hdec)))))
  exact isFractionRing_meromorphicFunctionSheaf_obj B S hS (Z.genericFieldSpace B S hS hX hdec)
    (fun _ hz => by
      rwa [weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero B S hS _ hred] at hz)
    (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS _
      (Z.genericFieldSpace B S hS hX hdec).2 hnoeth)
    (Z.genericFieldChart B S hS hX hdec)
    (inferInstanceAs (IsAffine (Spec (.of (Z.genericResidueField B S hS hX hdec)))))

/-- **The meromorphic functions on `Spec κ(u)` are `κ(u)`**: an element of `κ(u)` is read as a
regular function on `Spec κ(u)` and then as a meromorphic one, and both steps are bijective. -/
def PrimeDivisor.genericFieldMeromorphicEquiv :
    Z.genericResidueField B S hS hX hdec ≃+*
      ((meromorphicFunctionSheaf B S hS (Z.genericFieldSpace B S hS hX hdec).1
        (Z.genericFieldSpace B S hS hX hdec).2).obj.obj
          (op (Z.genericFieldChart B S hS hX hdec))) :=
  haveI := Z.isFractionRing_genericFieldMeromorphic B S hS hX hdec
  RingEquiv.ofBijective
    ((algebraMap ((structurePresheaf B S hS (Z.genericFieldSpace B S hS hX hdec).1).obj
        (op (Z.genericFieldChart B S hS hX hdec)))
      ((meromorphicFunctionSheaf B S hS (Z.genericFieldSpace B S hS hX hdec).1
        (Z.genericFieldSpace B S hS hX hdec).2).obj.obj
          (op (Z.genericFieldChart B S hS hX hdec)))).comp
      (Scheme.ΓSpecIso (CommRingCat.of (Z.genericResidueField B S hS hX hdec))).inv.hom)
    ((bijective_algebraMap_of_isField_of_isFractionRing
      (Z.isField_genericFieldSections B S hS hX hdec)).comp
      (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of (Z.genericResidueField B S hS hX hdec))).inv))

/-- `κ(u)` maps to the meromorphic functions on `Spec κ(u)` through the regular ones. -/
theorem PrimeDivisor.genericFieldMeromorphicEquiv_apply (c : Z.genericResidueField B S hS hX hdec) :
    Z.genericFieldMeromorphicEquiv B S hS hX hdec c =
      chartToMeromorphic (X := Z.genericFieldSpace B S hS hX hdec)
        (Z.genericFieldChart B S hS hX hdec)
        ((Scheme.ΓSpecIso (CommRingCat.of (Z.genericResidueField B S hS hX hdec))).inv.hom c) :=
  rfl

/-! ### The value at the generic point -/

/-- The meromorphic sections of `ρ_Z^*(ℒ|_Z)` over `Spec κ(u)` are the `κ(u)`-multiples of the
image of `s_ξ`, uniquely. -/
theorem PrimeDivisor.bijective_genericFieldValueTmul :
    Function.Bijective fun c : Z.genericResidueField B S hS hX hdec ↦
      toMeromorphicSectionSheaf B S hS (Z.genericFieldSpace B S hS hX hdec).1
        (Z.genericFieldSpace B S hS hX hdec).2
        ((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
          (Z.restrictModule B S hS hX L)) (Z.genericFieldChart B S hS hX hdec)
        (Z.genericFieldMeromorphicEquiv B S hS hX hdec c ⊗ₜ[chartRing B S hS
            (Z.genericFieldSpace B S hS hX hdec).1 (Z.genericFieldSpace B S hS hX hdec).2
            (Z.genericFieldChart B S hS hX hdec)]
          Z.genericFieldGenerator B S hS hX hdec L hL (Z.genericFieldChart B S hS hX hdec)
            (𝟙 (Z.genericFieldChart B S hS hX hdec)) :
          (meromorphicSectionModule B S hS (Z.genericFieldSpace B S hS hX hdec).1
            (Z.genericFieldSpace B S hS hX hdec).2
            ((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
              (Z.restrictModule B S hS hX L))).obj
                (op (Z.genericFieldChart B S hS hX hdec))) :=
  (Z.bijective_genericFieldTmul B S hS hX hdec L hL (Z.genericFieldChart B S hS hX hdec)
    (𝟙 (Z.genericFieldChart B S hS hX hdec))).comp
    (Z.genericFieldMeromorphicEquiv B S hS hX hdec).bijective

/-- **The value at the generic point of `Z` of a meromorphic section `σ` of `ℒ|_Z`**: the element
`c ∈ κ(u)` such that the pullback of `σ` along `ρ_Z : Spec κ(u) → Z` is `c` times the image of
the generator `s_ξ` in the fibre. -/
def PrimeDivisor.genericFieldValue
    (σ : MeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L)) :
    Z.genericResidueField B S hS hX hdec :=
  (Equiv.ofBijective _ (Z.bijective_genericFieldValueTmul B S hS hX hdec L hL)).symm
    ((pullbackMeromorphicSection B S hS (Z.genericFieldMorphism B S hS hX hdec)
      (Z.restrictModule B S hS hX L)
      (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec) σ).eval
        (op (Z.genericFieldChart B S hS hX hdec)))

/-- **The characterization of the value at the generic point**: it is the unique `c ∈ κ(u)` for
which the pullback of `σ` along `ρ_Z` is `c` times the image of the generator `s_ξ`. -/
theorem PrimeDivisor.genericFieldValue_eq_iff
    (σ : MeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L)) (c : Z.genericResidueField B S hS hX hdec) :
    Z.genericFieldValue B S hS hX hdec L hL σ = c ↔
      (pullbackMeromorphicSection B S hS (Z.genericFieldMorphism B S hS hX hdec)
          (Z.restrictModule B S hS hX L)
          (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec) σ).eval
          (op (Z.genericFieldChart B S hS hX hdec)) =
        toMeromorphicSectionSheaf B S hS (Z.genericFieldSpace B S hS hX hdec).1
          (Z.genericFieldSpace B S hS hX hdec).2
          ((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
            (Z.restrictModule B S hS hX L)) (Z.genericFieldChart B S hS hX hdec)
          (Z.genericFieldMeromorphicEquiv B S hS hX hdec c ⊗ₜ[chartRing B S hS
              (Z.genericFieldSpace B S hS hX hdec).1 (Z.genericFieldSpace B S hS hX hdec).2
              (Z.genericFieldChart B S hS hX hdec)]
            Z.genericFieldGenerator B S hS hX hdec L hL (Z.genericFieldChart B S hS hX hdec)
              (𝟙 (Z.genericFieldChart B S hS hX hdec)) :
            (meromorphicSectionModule B S hS (Z.genericFieldSpace B S hS hX hdec).1
              (Z.genericFieldSpace B S hS hX hdec).2
              ((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
                (Z.restrictModule B S hS hX L))).obj
                  (op (Z.genericFieldChart B S hS hX hdec))) := by
  rw [genericFieldValue, Equiv.symm_apply_eq, Equiv.ofBijective_apply, eq_comm]

/-- **The defining property of the value at the generic point**: the pullback of `σ` along
`ρ_Z` is its value times the image of the generator `s_ξ`. -/
theorem PrimeDivisor.genericFieldValue_spec
    (σ : MeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L)) :
    (pullbackMeromorphicSection B S hS (Z.genericFieldMorphism B S hS hX hdec)
        (Z.restrictModule B S hS hX L)
        (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec) σ).eval
        (op (Z.genericFieldChart B S hS hX hdec)) =
      toMeromorphicSectionSheaf B S hS (Z.genericFieldSpace B S hS hX hdec).1
        (Z.genericFieldSpace B S hS hX hdec).2
        ((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
          (Z.restrictModule B S hS hX L)) (Z.genericFieldChart B S hS hX hdec)
        (Z.genericFieldMeromorphicEquiv B S hS hX hdec
            (Z.genericFieldValue B S hS hX hdec L hL σ) ⊗ₜ[chartRing B S hS
            (Z.genericFieldSpace B S hS hX hdec).1 (Z.genericFieldSpace B S hS hX hdec).2
            (Z.genericFieldChart B S hS hX hdec)]
          Z.genericFieldGenerator B S hS hX hdec L hL (Z.genericFieldChart B S hS hX hdec)
            (𝟙 (Z.genericFieldChart B S hS hX hdec)) :
          (meromorphicSectionModule B S hS (Z.genericFieldSpace B S hS hX hdec).1
            (Z.genericFieldSpace B S hS hX hdec).2
            ((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
              (Z.restrictModule B S hS hX L))).obj
                (op (Z.genericFieldChart B S hS hX hdec))) :=
  (Z.genericFieldValue_eq_iff B S hS hX hdec L hL σ _).1 rfl

end AlgebraicGeometry.Space

end
