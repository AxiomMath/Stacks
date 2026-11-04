module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceOfModulePoints
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ComponentStepEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Curves.Models.GenusFormulaModel
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ReducedFibreFiltration
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ReducedSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberComponentProperCurve
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberConnected
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberNegativeStep
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.LocalStructure.StalkConormal
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianValuativeCriterion.Separatedness
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.SmoothPullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.FibreRegularity
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.HypersurfaceStalkRegular
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.StalkSpecialization
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldEvaluation
public import StacksFrontier.RingTheory.FormallySmooth.Field
import StacksCore.Tactic.StacksAttribute

/-!
# A rational point of the generic curve and the special fibre of a regular proper model

In the situation of [Stacks, Tag 0C61] suppose that the curve `C` over the fraction field `K`
has a `K`-rational point. By the valuative criterion of properness that point extends to a
section `a : Spec(R) ⟶ X` of the model, and the image `x` of the closed point is a `k`-rational
point of the special fibre `X_k`. Since `a` splits the stalk map at `x`, the uniformizer `π` is
not in `𝔪_x²`, so `𝒪_{X_k, x} = 𝒪_{X, x}/π𝒪_{X, x}` is a regular local ring and `X_k ⟶ Spec(k)`
is smooth at `x`.

## Main results

* `Stacks.Models.RegularProperModelSituation.exists_section_of_rationalPoint` — the valuative
  criterion of properness extends a `K`-rational point of `C` to a section of the model.
* `Stacks.Models.RegularProperModelSituation.smoothAt_specialFiberSection` — the closed point of
  a section of the model lands on a smooth `k`-rational point of `X_k`.
* `Stacks.Models.RegularProperModelSituation`
  `.isIso_globalSections_specialFiberComponent_and_specialFiberMultiplicity_eq_one` — a component
  `Cᵢ` through a smooth `k`-rational point has `H⁰(Cᵢ, 𝒪_{Cᵢ}) = k` and multiplicity `mᵢ = 1`.
* `Stacks.Models.RegularProperModelSituation.exists_isRationalPoint_smoothAt_specialFiber` —
  parts (1) and (2) of [Stacks, Tag 0CE8] together.
* `Stacks.Models.RegularProperModelSituation.injective_specialFiberComponentι_appTop` and
  `isIso_globalSections_specialFiber_of_injective` — `H⁰(X_k, 𝒪_{X_k})` embeds into `H⁰` of the
  component through the smooth rational point, hence is `k`.
* `Stacks.Models.RegularProperModelSituation.genus_specialFiber_eq_of_eulerCharacteristic_eq` —
  the genus of `X_k` is that of `C`, both having `χ = 1 - g`.

## The argument

For part (2), the local ring `𝒪_{X_k, x}` at the smooth rational point is regular, hence a
domain; its localization at the generic point of a component `Cᵢ` through `x` is then a domain of
dimension zero, that is a field, so `𝒪_{X, ξᵢ}/ℐ_{X_k, ξᵢ}` is the residue field and has length
one. The field `H⁰(Cᵢ, 𝒪_{Cᵢ})`, finite over `k` by [Stacks, Tag 0C6P], embeds into the residue
field `κ(x) = k`.

For part (3), the global functions of `X_k` are reached from those of the component `C₀` through
the smooth rational point, which has `m₀ = 1` and `H⁰(C₀, 𝒪) = k`, by adding one component at a
time: as long as `D = Σ aᵢCᵢ ≠ X_k` the intersection form (Tag 0C66) provides a component `Cᵢ`
with `aᵢ < mᵢ` and `deg(𝒪_X(-D)|_{Cᵢ}) < 0`, and then `Γ(D + Cᵢ, 𝒪) ⟶ Γ(D, 𝒪)` is injective
(Tags 0C4T and 0B40). So `Γ(X_k, 𝒪) ↪ Γ(C₀, 𝒪) = k`, and `H⁰(X_k, 𝒪_{X_k}) = k`. The genus
equality then follows from `χ(C, 𝒪_C) = χ(X_k, 𝒪_{X_k})`, since both sides are `1 - g`.

## References

* [Stacks Project, Tag 0CE8](https://stacks.math.columbia.edu/tag/0CE8)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0BX5](https://stacks.math.columbia.edu/tag/0BX5)
* [Stacks Project, Tag 00NQ](https://stacks.math.columbia.edu/tag/00NQ)
* [Stacks Project, Tag 00TV](https://stacks.math.columbia.edu/tag/00TV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

/-- If the ground field maps isomorphically onto the global functions, then these form a
one-dimensional space over it. -/
theorem AlgebraicGeometry.finrank_globalSections_eq_one_of_isIso (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    Module.finrank k Γ(X, ⊤) = 1 := by
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have hbij : Function.Bijective (Algebra.linearMap k Γ(X, ⊤)) :=
    ConcreteCategory.bijective_of_isIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)
  rw [← (LinearEquiv.ofBijective _ hbij).finrank_eq, Module.finrank_self]

namespace Stacks.Models

/-- At a `k`-rational point the canonical map from `k` to the residue field, read through the
global functions, is an isomorphism. -/
theorem isIso_Γevaluation_of_isRationalPoint {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (y : Y) (hy : IsRationalPoint f y) :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ Y.Γevaluation y) := by
  have key : Spec.preimage (Y.fromSpecResidueField y ≫ f) =
      (Scheme.ΓSpecIso (.of k)).inv ≫ (Y.fromSpecResidueField y ≫ f).appTop ≫
        (Scheme.ΓSpecIso _).hom := by
    conv_rhs => rw [← Spec.map_preimage (Y.fromSpecResidueField y ≫ f)]
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rw [Scheme.Hom.comp_appTop, Category.assoc, fromSpecResidueField_appTop] at key
  rw [← key]
  exact hy

/-- **A retraction of a local homomorphism keeps a uniformizer a regular parameter.** Let
`φ : A ⟶ B` be a local homomorphism of local rings with a local retraction `ψ`, and let the
maximal ideal of `A` be generated by an element `ϖ ∉ 𝔪_A²`. Then `φ ϖ` lies in `𝔪_B` but not in
`𝔪_B²`, and it generates the extension of `𝔪_A` to `B`. -/
theorem map_mem_maximalIdeal_and_notMem_sq_of_retraction {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (φ : A →+* B) (ψ : B →+* A) [IsLocalHom φ] [IsLocalHom ψ]
    (hψφ : ψ.comp φ = RingHom.id A) {ϖ : A} (hϖ : maximalIdeal A = Ideal.span {ϖ})
    (hϖ2 : ϖ ∉ maximalIdeal A ^ 2) :
    φ ϖ ∈ maximalIdeal B ∧ φ ϖ ∉ maximalIdeal B ^ 2 ∧
      Ideal.map φ (maximalIdeal A) = Ideal.span {φ ϖ} := by
  have hϖm : ϖ ∈ maximalIdeal A := hϖ ▸ Ideal.subset_span rfl
  refine ⟨map_nonunit φ ϖ hϖm, fun h => hϖ2 ?_, ?_⟩
  · have hle : Ideal.map ψ (maximalIdeal B) ≤ maximalIdeal A :=
      Ideal.map_le_iff_le_comap.mpr fun b hb => map_nonunit ψ b hb
    have hψ : ψ (φ ϖ) = ϖ := by simpa using DFunLike.congr_fun hψφ ϖ
    have hmem : ψ (φ ϖ) ∈ Ideal.map ψ (maximalIdeal B ^ 2) := Ideal.mem_map_of_mem ψ h
    rw [Ideal.map_pow, hψ] at hmem
    exact Ideal.pow_right_mono hle 2 hmem
  · rw [hϖ, Ideal.map_span, Set.image_singleton]

/-- The local rings of the spectrum of a field are fields. -/
private theorem isField_stalk_spec_field (k : Type u) [Field k] (y : Spec (.of k)) :
    IsField ((Spec (.of k)).presheaf.stalk y) := by
  obtain rfl : y = closedPoint k := Subsingleton.elim _ _
  exact (stalkClosedPointIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField k)

/-- At a `k`-rational point the residue field is separable over `k`, being `k` itself. -/
theorem isSeparableExtension_residueField_of_isRationalPoint {k : Type u} [Field k]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) (y : Y) (hy : IsRationalPoint f y) :
    letI : Algebra k (Y.residueField y) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ Y.Γevaluation y).hom.toAlgebra
    Algebra.IsSeparableExtension k (Y.residueField y) := by
  let : Algebra k (Y.residueField y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ Y.Γevaluation y).hom.toAlgebra
  have := isIso_Γevaluation_of_isRationalPoint f y hy
  have hbij : Function.Bijective (algebraMap k (Y.residueField y)) :=
    ConcreteCategory.bijective_of_isIso
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ Y.Γevaluation y)
  exact (Algebra.FormallySmooth.iff_isSeparableExtension _ _).mp
    (Algebra.FormallySmooth.of_equiv (AlgEquiv.ofBijective (Algebra.ofId _ _) hbij))

/-- **At a smooth `k`-rational point the local ring is regular** (Tag 00TV). -/
theorem isRegularLocalRing_stalk_of_smoothAt_of_isRationalPoint {k : Type u} [Field k]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f] (y : Y)
    (hy : IsRationalPoint f y) (hsm : InfinitesimalLifting.SmoothAt f y) :
    IsRegularLocalRing (Y.presheaf.stalk y) :=
  (smoothAt_iff_isRegularLocalRing_stalk f y
    (isSeparableExtension_residueField_of_isRationalPoint f y hy)).mp hsm

/-- **A scheme over `k` whose global functions form a field and which has a `k`-rational point
has `H⁰ = k`.** The global functions embed into the residue field at the rational point, which
is `k`. -/
theorem isIso_globalSections_of_isField_of_isRationalPoint {k : Type u} [Field k]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) (hF : IsField Γ(Y, ⊤)) (y : Y)
    (hy : IsRationalPoint f y) : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) := by
  let := hF.toField
  have hiso := isIso_Γevaluation_of_isRationalPoint f y hy
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨RingHom.injective _, fun c => ?_⟩
  obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ Y.Γevaluation y)).2 (Y.Γevaluation y c)
  refine ⟨a, (Y.Γevaluation y).hom.injective ?_⟩
  rw [← ha]
  rfl

/-- **A rational point pulls back along a morphism inducing an isomorphism of residue fields.**
If `ι : Y ⟶ X` induces an isomorphism `κ(ι y) ≅ κ(y)` and `ι y` is a `k`-rational point of `X`,
then `y` is a `k`-rational point of `Y`. -/
theorem isRationalPoint_comp {k : Type u} [Field k] {X Y : Scheme.{u}} (ι : Y ⟶ X)
    (f : X ⟶ Spec (.of k)) (y : Y) [IsIso (ι.residueFieldMap y)]
    (h : IsRationalPoint f (ι y)) : IsRationalPoint (ι ≫ f) y := by
  have : IsIso (Spec.preimage (X.fromSpecResidueField (ι y) ≫ f)) := h
  unfold IsRationalPoint
  rw [← Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    Category.assoc, Spec.preimage_comp, Spec.preimage_map]
  infer_instance

attribute [local instance] AlgebraicGeometry.isIso_residueFieldMap_of_isClosedImmersion

/-- Raising a coordinate `g W < f W` by one lowers `∑ V, (f V - g V)` by one. -/
private theorem sum_tsub_update_add_one {ι : Type*} [Fintype ι] [DecidableEq ι] (f g : ι → ℕ)
    {W : ι} (hW : g W < f W) :
    ∑ V, (f V - Function.update g W (g W + 1) V) + 1 = ∑ V, (f V - g V) := by
  have e₁ := (Finset.add_sum_erase Finset.univ (fun V => f V - g V) (Finset.mem_univ W)).symm
  have e₂ := (Finset.add_sum_erase Finset.univ
    (fun V => f V - Function.update g W (g W + 1) V) (Finset.mem_univ W)).symm
  have e₃ : ∑ V ∈ Finset.univ.erase W, (f V - Function.update g W (g W + 1) V) =
      ∑ V ∈ Finset.univ.erase W, (f V - g V) :=
    Finset.sum_congr rfl fun V hV => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hV)]
  rw [e₁, e₂, e₃, Function.update_self]
  omega

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **The valuative criterion of properness extends a rational point of `C` to the model.** A
`K`-rational point of the curve `C`, read on `X` through the generic fibre, extends to a section
`Spec(R) ⟶ X` of the model morphism. -/
@[sga "7 X 1.12" "Direction"]
theorem exists_section_of_rationalPoint (p : Spec (.of S.K) ⟶ S.C) (hp : p ≫ S.C_to_K = 𝟙 _) :
    ∃ a : Spec (.of S.R) ⟶ S.X, a ≫ S.X_to_R = 𝟙 _ := by
  let q : Spec (.of S.K) ⟶ S.X := p ≫ S.genericFiberIso.hom ≫ pullback.fst _ _
  have hsq : CommSq q (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))) S.X_to_R (𝟙 _) := by
    refine ⟨?_⟩
    simp only [q, Category.assoc, pullback.condition, Category.comp_id]
    rw [← Category.assoc S.genericFiberIso.hom, S.genericFiberIso_over_K, ← Category.assoc, hp,
      Category.id_comp]
  have hE : (ValuativeCriterion.Existence ⊓ @QuasiCompact) S.X_to_R := by
    rw [← UniversallyClosed.eq_valuativeCriterion]
    infer_instance
  obtain ⟨l, -, hl₂⟩ := (hE.1 { R := S.R, K := S.K, i₁ := q, i₂ := 𝟙 _, commSq := hsq }).exists_lift
  exact ⟨l, hl₂⟩

/-- **The local ring of `Spec(R)` at the closed point has a uniformizer.** Its maximal ideal is
generated by the image of the chosen uniformizer `π` of `R`, which does not lie in the square of
the maximal ideal. -/
theorem exists_uniformizer_stalk (s : Spec (.of S.R)) (hs : s = closedPoint S.R) :
    ∃ ϖ : (Spec (.of S.R)).presheaf.stalk s,
      maximalIdeal _ = Ideal.span {ϖ} ∧ ϖ ∉ maximalIdeal _ ^ 2 := by
  subst hs
  let e := (stalkClosedPointIso (.of S.R)).commRingCatIsoToRingEquiv
  have hπ : maximalIdeal S.R = Ideal.span {S.π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer S.π).mp S.uniformizer
  have hdvd : ∀ x, e.symm S.π ∣ x ↔ S.π ∣ e x := fun x =>
    ⟨fun h => by simpa using map_dvd e h, fun h => by simpa using map_dvd e.symm h⟩
  have hm : maximalIdeal ((Spec (.of S.R)).presheaf.stalk (closedPoint S.R)) =
      Ideal.span {e.symm S.π} := by
    ext x
    rw [Ideal.mem_span_singleton, hdvd, ← Ideal.mem_span_singleton, ← hπ, mem_maximalIdeal,
      mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]
  refine ⟨e.symm S.π, hm, ?_⟩
  rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  intro h
  have h' : S.π ^ 2 ∣ S.π ^ 1 := by simpa using map_dvd e h
  have := (pow_dvd_pow_iff S.uniformizer.ne_zero S.uniformizer.not_isUnit).mp h'
  omega

variable {S}

/-- The section of the special fibre `X_k ⟶ Spec(k)` induced by a section of the model. -/
def specialFiberSection (a : Spec (.of S.R) ⟶ S.X) (ha : a ≫ S.X_to_R = 𝟙 _) :
    Spec (.of S.k) ⟶ S.specialFiber :=
  pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)) ≫ a) (𝟙 _)
    (by rw [Category.assoc, ha, Category.comp_id, Category.id_comp])

/-- The section `specialFiberSection a ha` is a section of the structure morphism
`X_k ⟶ Spec(k)`. -/
theorem specialFiberSection_toSpec (a : Spec (.of S.R) ⟶ S.X) (ha : a ≫ S.X_to_R = 𝟙 _) :
    specialFiberSection a ha ≫ S.specialFiberToSpec = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- Composing `specialFiberSection a ha` with the inclusion `X_k ⟶ X` gives the composite
`Spec(k) ⟶ Spec(R) ⟶ X` of the closed point with `a`. -/
theorem specialFiberSection_ι (a : Spec (.of S.R) ⟶ S.X) (ha : a ≫ S.X_to_R = 𝟙 _) :
    specialFiberSection a ha ≫ S.specialFiberι =
      Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)) ≫ a :=
  pullback.lift_fst _ _ _

/-- **The image of the closed point under a section of the model is a smooth point of the
special fibre.** Let `a : Spec(R) ⟶ X` be a section of the model and let `z ∈ X_k` be the
`k`-rational point induced by it. The section splits the stalk map of the model at `z`, so the
uniformizer is not in `𝔪_z²`; hence `𝒪_{X_k, z} = 𝒪_{X, z}/π` is regular (Tag 00NQ), and
`X_k ⟶ Spec(k)` is smooth at `z` (Tag 00TV). -/
@[sga "3 X 8.9" "If X is regular"]
theorem smoothAt_specialFiberSection (a : Spec (.of S.R) ⟶ S.X) (ha : a ≫ S.X_to_R = 𝟙 _) :
    InfinitesimalLifting.SmoothAt S.specialFiberToSpec
      ((specialFiberSection a ha).base (closedPoint (CommRingCat.of S.k))) := by
  set z := (specialFiberSection a ha).base (closedPoint (CommRingCat.of S.k))
  have hrat : IsRationalPoint S.specialFiberToSpec z :=
    isRationalPoint_base_of_comp_eq_id _ (specialFiberSection_toSpec a ha) _
  refine (smoothAt_iff_isRegularLocalRing_stalk S.specialFiberToSpec z
    (isSeparableExtension_residueField_of_isRationalPoint _ z hrat)).mpr ?_
  -- the points of the model and of the base below `z`
  set q := (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))).base
    (closedPoint (CommRingCat.of S.k))
  have hx' : S.specialFiberι z = a q :=
    congrArg (fun f : Spec (.of S.k) ⟶ S.X => f.base (closedPoint (CommRingCat.of S.k)))
      (specialFiberSection_ι a ha)
  have hs : S.X_to_R (S.specialFiberι z) = q := by
    rw [hx', ← Scheme.Hom.comp_apply, ha]
    rfl
  have has : a (S.X_to_R (S.specialFiberι z)) = S.specialFiberι z := by rw [hs, hx']
  have : IsLocalHom (algebraMap S.R S.k) := S.surjective_algebraMap_residueField.isLocalHom
  have hqc : q = closedPoint S.R := Spec_closedPoint (f := CommRingCat.ofHom (algebraMap S.R S.k))
  have : IsRegularLocalRing (S.X.presheaf.stalk (S.specialFiberι z)) :=
    S.isRegularLocalRing_stalk _
  obtain ⟨ϖ, hϖ, hϖ2⟩ := exists_uniformizer_stalk S _ (hs.trans hqc)
  -- the section splits the stalk map of the model
  let φ := (S.X_to_R.stalkMap (S.specialFiberι z)).hom
  let ψ := a.stalkMapAt (S.X_to_R (S.specialFiberι z)) (S.specialFiberι z) has
  have : IsLocalHom ψ := by
    show IsLocalHom (eqToHom _ ≫ a.stalkMap _).hom
    infer_instance
  have hψφ : ψ.comp φ = RingHom.id _ := by
    show ψ.comp (S.X_to_R.stalkMapAt (S.specialFiberι z) _ rfl) = _
    rw [Scheme.Hom.stalkMapAt_comp]
    have hid : (𝟙 (Spec (.of S.R)) : Spec (.of S.R) ⟶ _) (S.X_to_R (S.specialFiberι z)) =
        S.X_to_R (S.specialFiberι z) := rfl
    exact (Scheme.Hom.stalkMapAt_congr _ _ ha _ _ _ hid).trans
      (Scheme.Hom.stalkMapAt_id' _ _ hid)
  obtain ⟨h1, h2, h3⟩ := map_mem_maximalIdeal_and_notMem_sq_of_retraction φ ψ hψφ hϖ hϖ2
  refine isRegularLocalRing_stalk_of_ker_stalkMap_eq_span_singleton S.specialFiberι z h1 h2 ?_
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))) :=
    IsClosedImmersion.spec_of_surjective _ S.surjective_algebraMap_residueField
  have hk := ker_stalkMap_pullback_fst S.X_to_R
    (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))) z
  dsimp only at hk
  let := (isField_stalk_spec_field S.k
    (pullback.snd S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))) z)).toField
  rw [hk, IsLocalRing.ker_eq_maximalIdeal _ ((Scheme.Hom.stalkMap_surjective _ _).comp
    (ConcreteCategory.bijective_of_isIso (eqToHom _)).2)]
  exact h3

variable (S) in
/-- The image of a component of the special fibre under its closed immersion into the special
fibre is the component itself. -/
theorem range_specialFiberComponentι (Z : irreducibleComponents S.specialFiber) :
    Set.range (S.specialFiberComponentι Z).base = Z.1 := by
  have h1 : S.specialFiberι.base '' Set.range (S.specialFiberComponentι Z).base =
      S.specialFiberι.base '' Z.1 := by
    rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      S.specialFiberComponentι_specialFiberι Z, Scheme.IdealSheafData.range_subschemeι]
    exact S.coe_support_specialFiberComponentIdeal Z
  exact S.specialFiberι.isClosedEmbedding.injective.image_injective h1

/-- **Part (2) of [Stacks, Tag 0CE8], the global functions.** If an irreducible component `Cᵢ`
of the special fibre contains a `k`-rational point of `X_k`, then `H⁰(Cᵢ, 𝒪_{Cᵢ}) = k`: it is a
field finite over `k` (Tag 0C6P) which embeds into the residue field at that point. -/
theorem isIso_globalSections_specialFiberComponent_of_isRationalPoint
    (Z : irreducibleComponents S.specialFiber) (x : S.specialFiber)
    (hx : IsRationalPoint S.specialFiberToSpec x) (hxZ : x ∈ Z.1) :
    IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop) := by
  obtain ⟨y, rfl⟩ : x ∈ Set.range (S.specialFiberComponentι Z).base := by
    rwa [range_specialFiberComponentι]
  exact isIso_globalSections_of_isField_of_isRationalPoint _
    (S.isField_and_finite_globalSections_specialFiberComponent Z).1 y
    (isRationalPoint_comp (S.specialFiberComponentι Z) S.specialFiberToSpec y hx)

variable (S) in
/-- The generic point `ξ'` of a component `C` of the special fibre, as a point of `X_k`. -/
abbrev specialFiberComponentGenericPoint (Z : irreducibleComponents S.specialFiber) :
    S.specialFiber :=
  S.specialFiberComponentι Z (genericPoint (S.specialFiberComponentIdeal Z).subscheme)

/-- The generic point of a component of `X_k` maps to the generic point of the corresponding
prime divisor of `X`. -/
theorem specialFiberι_specialFiberComponentGenericPoint (Z : irreducibleComponents S.specialFiber) :
    S.specialFiberι (S.specialFiberComponentGenericPoint Z) =
      (S.specialFiberComponentPrimeDivisor Z).genericPoint := by
  rw [S.genericPoint_specialFiberComponentPrimeDivisor, ← Scheme.Hom.comp_apply,
    S.specialFiberComponentι_specialFiberι]

/-- **The local ring of `X_k` at the generic point of a component through a point with a domain
as local ring is a field.** It is a localization of that domain, and it has dimension zero
because the generic point of an irreducible component is maximal for specialization. -/
theorem isField_stalk_specialFiberComponentGenericPoint (Z : irreducibleComponents S.specialFiber)
    (x : S.specialFiber) (hxZ : x ∈ Z.1) [IsDomain (S.specialFiber.presheaf.stalk x)] :
    IsField (S.specialFiber.presheaf.stalk (S.specialFiberComponentGenericPoint Z)) := by
  set ξ := S.specialFiberComponentGenericPoint Z
  obtain ⟨y, rfl⟩ : x ∈ Set.range (S.specialFiberComponentι Z).base := by
    rwa [range_specialFiberComponentι]
  have hsp : ξ ⤳ S.specialFiberComponentι Z y :=
    (genericPoint_specializes y).map (S.specialFiberComponentι Z).continuous
  -- the local ring at `ξ` is a localization of a domain
  let : Algebra (S.specialFiber.presheaf.stalk (S.specialFiberComponentι Z y))
      (S.specialFiber.presheaf.stalk ξ) :=
    (S.specialFiber.presheaf.stalkSpecializes hsp).hom.toAlgebra
  have hloc : IsLocalization.AtPrime (S.specialFiber.presheaf.stalk ξ)
      ((maximalIdeal (S.specialFiber.presheaf.stalk ξ)).under
        (S.specialFiber.presheaf.stalk (S.specialFiberComponentι Z y))) :=
    Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes hsp
  have : IsDomain (S.specialFiber.presheaf.stalk ξ) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (S.specialFiber.presheaf.stalk ξ)
      (M := ((maximalIdeal (S.specialFiber.presheaf.stalk ξ)).under
        (S.specialFiber.presheaf.stalk (S.specialFiberComponentι Z y))).primeCompl)
      (Ideal.primeCompl_le_nonZeroDivisors _)
  -- `ξ` is a generic point of an irreducible component of `X_k`
  have hclosure : closure ({ξ} : Set S.specialFiber) = Z.1 := by
    show closure {(S.specialFiberComponentι Z) (genericPoint _)} = _
    rw [← Set.image_singleton,
      (S.specialFiberComponentι Z).isClosedEmbedding.closure_image_eq, genericPoint_closure,
      Set.image_univ, range_specialFiberComponentι]
  have hmax : IsMax ξ := fun w hw =>
    le_of_eq (Topology.eq_of_specializes_isGenericPoint (hclosure ▸ Z.2) hclosure hw)
  have hdim : ringKrullDim (S.specialFiber.presheaf.stalk ξ) = 0 := by
    rw [ringKrullDim_stalk_eq_coheight]
    simpa only [WithBot.coe_zero] using
      congrArg (fun d : ℕ∞ => (d : WithBot ℕ∞)) (Order.coheight_eq_zero.mpr hmax)
  have : Ring.KrullDimLE 0 (S.specialFiber.presheaf.stalk ξ) :=
    Ring.krullDimLE_iff.mpr hdim.le
  exact Ring.KrullDimLE.isField_of_isDomain

/-- **The multiplicity of a component is one when `X_k` is reduced at its generic point.** If the
local ring of `X_k` at the generic point of the component `C` is a field, then the ideal of `X_k`
at the generic point `ξ` of `C` in `X` is the maximal ideal of `𝒪_{X, ξ}`, so
`𝒪_{X, ξ}/ℐ_{X_k, ξ}` is the residue field, of length one. -/
theorem specialFiberMultiplicity_eq_one_of_isField (Z : irreducibleComponents S.specialFiber)
    (hF : IsField (S.specialFiber.presheaf.stalk (S.specialFiberComponentGenericPoint Z))) :
    S.specialFiberMultiplicity Z = 1 := by
  set ξ' := S.specialFiberComponentGenericPoint Z
  let e : S.specialFiber ≅ S.specialFiberIdeal.subscheme := asIso S.specialFiberι.toImage
  have he : e.hom ≫ S.specialFiberIdeal.subschemeι = S.specialFiberι :=
    S.specialFiberι.toImage_imageι
  -- the local ring of the subscheme at the image of `ξ'` is a field
  have hF' : IsField (S.specialFiberIdeal.subscheme.presheaf.stalk (e.hom ξ')) :=
    (asIso (e.hom.stalkMap ξ')).commRingCatIsoToRingEquiv.toMulEquiv.isField hF
  let := hF'.toField
  have hker : RingHom.ker (S.specialFiberIdeal.subschemeι.stalkMap (e.hom ξ')).hom =
      maximalIdeal _ :=
    IsLocalRing.ker_eq_maximalIdeal _ (S.specialFiberIdeal.subschemeι.stalkMap_surjective _)
  rw [IdealSheafData.ker_stalkMap_subschemeι_eq_stalk] at hker
  have hpt : S.specialFiberIdeal.subschemeι (e.hom ξ') =
      (S.specialFiberComponentPrimeDivisor Z).genericPoint := by
    rw [← specialFiberι_specialFiberComponentGenericPoint, ← he]
    rfl
  have hstalk : ∀ (p : S.X) (hp : S.specialFiberIdeal.subschemeι (e.hom ξ') = p),
      IdealSheafData.stalk S.specialFiberIdeal p = maximalIdeal (S.X.presheaf.stalk p) := by
    rintro p rfl
    exact hker
  rw [RegularModelSituation.specialFiberMultiplicity, effectiveCartierMultiplicity,
    hstalk _ hpt]
  have : IsSimpleModule (S.X.presheaf.stalk (S.specialFiberComponentPrimeDivisor Z).genericPoint)
      (S.X.presheaf.stalk (S.specialFiberComponentPrimeDivisor Z).genericPoint ⧸
        maximalIdeal _) :=
    isSimpleModule_iff_isCoatom.mpr (maximalIdeal.isMaximal _).out
  rw [Module.length_eq_one]
  rfl

/-- **Part (2) of [Stacks, Tag 0CE8], for every smooth rational point.** Let `x` be a
`k`-rational point of `X_k` at which `X_k ⟶ Spec(k)` is smooth, and let `Cᵢ` be an irreducible
component of `X_k` through `x`. Then `H⁰(Cᵢ, 𝒪_{Cᵢ}) = k` and the multiplicity `mᵢ` of `Cᵢ` in
`X_k` is one. The local ring `𝒪_{X_k, x}` is regular, hence a domain, so its localization at the
generic point of `Cᵢ` is a field, and `X_k` is reduced there. -/
theorem isIso_globalSections_specialFiberComponent_and_specialFiberMultiplicity_eq_one
    (x : S.specialFiber) (hx : IsRationalPoint S.specialFiberToSpec x)
    (hsm : InfinitesimalLifting.SmoothAt S.specialFiberToSpec x)
    (Z : irreducibleComponents S.specialFiber) (hxZ : x ∈ Z.1) :
    IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop) ∧
      S.specialFiberMultiplicity Z = 1 := by
  have := isRegularLocalRing_stalk_of_smoothAt_of_isRationalPoint _ x hx hsm
  have : IsDomain (S.specialFiber.presheaf.stalk x) := IsRegularLocalRing.isDomain _
  exact ⟨isIso_globalSections_specialFiberComponent_of_isRationalPoint Z x hx hxZ,
    specialFiberMultiplicity_eq_one_of_isField Z
      (isField_stalk_specialFiberComponentGenericPoint Z x hxZ)⟩

variable (S) in
/-- **Parts (1) and (2) of [Stacks, Tag 0CE8].** If the curve `C` has a `K`-rational point, the
special fibre `X_k` has a `k`-rational point `x` at which it is smooth over `k`, and every
irreducible component `Cᵢ` of `X_k` through `x` has `H⁰(Cᵢ, 𝒪_{Cᵢ}) = k` and multiplicity
`mᵢ = 1`. -/
theorem exists_isRationalPoint_smoothAt_specialFiber (p : Spec (.of S.K) ⟶ S.C)
    (hp : p ≫ S.C_to_K = 𝟙 _) :
    ∃ x : S.specialFiber, IsRationalPoint S.specialFiberToSpec x ∧
      InfinitesimalLifting.SmoothAt S.specialFiberToSpec x ∧
      ∀ Z : irreducibleComponents S.specialFiber, x ∈ Z.1 →
        IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop) ∧
          S.specialFiberMultiplicity Z = 1 := by
  obtain ⟨a, ha⟩ := S.exists_section_of_rationalPoint p hp
  have hx : IsRationalPoint S.specialFiberToSpec
      ((specialFiberSection a ha).base (closedPoint (CommRingCat.of S.k))) :=
    isRationalPoint_base_of_comp_eq_id _ (specialFiberSection_toSpec a ha) _
  have hsm := smoothAt_specialFiberSection a ha
  exact ⟨_, hx, hsm, fun Z hxZ =>
    isIso_globalSections_specialFiberComponent_and_specialFiberMultiplicity_eq_one _ hx hsm Z hxZ⟩

/-! ### Part (3): the global functions of the special fibre -/

open Scheme.IdealSheafData (prod_pow_le_prod_pow_of_le prod_pow_succ_at) in
/-- **Adding components of positive intersection keeps the global functions injective.** Let
`Z₀` be a component of multiplicity one and suppose that for every coefficient family
`a ≤ m` with `a_{Z₀} = 1` and `a ≠ m` some component `W` with `a_W < m_W` has
`deg(𝒪_X(-Σ aᵥCᵥ)|_W) < 0`. Then for every such `a` the restriction
`Γ(X_k, 𝒪) = Γ(Σ mᵥCᵥ, 𝒪) ⟶ Γ(Σ aᵥCᵥ, 𝒪)` is injective: each step
`Σ aᵥCᵥ ⊂ Σ aᵥCᵥ + C_W` is injective on global functions because the twist `𝒪_X(-Σ aᵥCᵥ)|_W`
has negative degree, hence no nonzero section (Tags 0C4T and 0B40). -/
theorem injective_inclusion_prod_appTop (Z₀ : irreducibleComponents S.specialFiber)
    (hZ₀ : S.specialFiberMultiplicity Z₀ = 1)
    (hstep : ∀ a : irreducibleComponents S.specialFiber → ℕ,
      (∀ W, a W ≤ S.specialFiberMultiplicity W) → a Z₀ = 1 → a ≠ S.specialFiberMultiplicity →
      ∃ W, a W < S.specialFiberMultiplicity W ∧
        S.specialFiberComponentDegree W
          (Stacks.Divisors.negativeTwist (∏ V, S.specialFiberComponentIdeal V ^ a V))
          (@Stacks.Divisors.stacksIsInvertible_negativeTwist _ _
            (Stacks.Divisors.isEffectiveCartierDivisor_prod Finset.univ _ a
              fun V _ => S.isEffectiveCartierDivisor_specialFiberComponent V)) < 0) :
    ∀ (n : ℕ) (a : irreducibleComponents S.specialFiber → ℕ)
      (ha : ∀ W ∈ Finset.univ, a W ≤ S.specialFiberMultiplicity W), a Z₀ = 1 →
      ∑ W, (S.specialFiberMultiplicity W - a W) = n →
      Function.Injective (Scheme.IdealSheafData.inclusion
        (prod_pow_le_prod_pow_of_le Finset.univ S.specialFiberComponentIdeal ha)).appTop.hom := by
  classical
  have hC : ∀ V ∈ (Finset.univ : Finset (irreducibleComponents S.specialFiber)),
      Stacks.Divisors.IsEffectiveCartierDivisor (S.specialFiberComponentIdeal V) :=
    fun V _ => S.isEffectiveCartierDivisor_specialFiberComponent V
  intro n
  induction n with
  | zero =>
    intro a ha _ hn
    obtain rfl : a = S.specialFiberMultiplicity := funext fun W =>
      le_antisymm (ha W (Finset.mem_univ W))
        (Nat.le_of_sub_eq_zero (Finset.sum_eq_zero_iff.mp hn W (Finset.mem_univ W)))
    rw [Scheme.IdealSheafData.inclusion_id]
    exact fun _ _ h => h
  | succ n ih =>
    intro a ha ha0 hn
    have hne : a ≠ S.specialFiberMultiplicity := fun h => by simp [h] at hn
    obtain ⟨W, hlt, hdeg⟩ := hstep a (fun W => ha W (Finset.mem_univ W)) ha0 hne
    have hWZ : W ≠ Z₀ := by
      rintro rfl
      omega
    set a' := Function.update a W (a W + 1)
    have ha'W : a' W = a W + 1 := Function.update_self ..
    have ha'ne : ∀ V, V ≠ W → a' V = a V := fun V hV => Function.update_of_ne hV ..
    have ha'le : ∀ V ∈ Finset.univ, a' V ≤ S.specialFiberMultiplicity V := fun V _ =>
      update_le_iff.2 ⟨hlt, fun j _ => ha j (Finset.mem_univ j)⟩ V
    have ha'0 : a' Z₀ = 1 := by rw [ha'ne Z₀ hWZ.symm, ha0]
    have hsum : ∑ V, (S.specialFiberMultiplicity V - a' V) + 1 =
        ∑ V, (S.specialFiberMultiplicity V - a V) := sum_tsub_update_add_one _ _ hlt
    have hprod : (∏ V, S.specialFiberComponentIdeal V ^ a' V) =
        (∏ V, S.specialFiberComponentIdeal V ^ a V) * S.specialFiberComponentIdeal W :=
      prod_pow_succ_at Finset.univ _ (Finset.mem_univ W) ha'W fun V _ hV => ha'ne V hV
    have hle : (∏ V, S.specialFiberComponentIdeal V ^ a' V) ≤
        ∏ V, S.specialFiberComponentIdeal V ^ a V :=
      prod_pow_le_prod_pow_of_le Finset.univ _ fun V _ =>
        le_update_iff.2 ⟨Nat.le_succ _, fun _ _ => le_rfl⟩ V
    have hDa := Stacks.Divisors.isEffectiveCartierDivisor_prod Finset.univ _ a hC
    have hvanish := forall_eq_zero_of_componentDegree_neg S.k
      (∏ V, S.specialFiberComponentIdeal V ^ a V) (S.specialFiberComponentIdeal W) hDa
      (S.specialFiberComponentToSpec W) (S.isProper_specialFiberComponentToSpec W)
      (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent W) inferInstance hdeg
    have hstepinj : ∀ (J : S.X.IdealSheafData)
        (_ : J = (∏ V, S.specialFiberComponentIdeal V ^ a V) * S.specialFiberComponentIdeal W)
        (h : J ≤ ∏ V, S.specialFiberComponentIdeal V ^ a V),
        Function.Injective (Scheme.IdealSheafData.inclusion h).appTop.hom := by
      rintro J rfl h
      exact injective_inclusion_appTop_of_forall_eq_zero _ _ hDa
        (hprod ▸ Stacks.Divisors.isEffectiveCartierDivisor_prod Finset.univ _ a' hC)
        (S.isEffectiveCartierDivisor_specialFiberComponent W) hvanish h
    rw [← Scheme.IdealSheafData.inclusion_comp (prod_pow_le_prod_pow_of_le Finset.univ _ ha'le) hle,
      Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    exact (hstepinj _ hprod hle).comp (ih a' ha'le ha'0 (by omega))

/-- **The restriction of global functions from `X_k` to a component is injective** once the
step hypothesis of `injective_inclusion_prod_appTop` holds for a component `Z₀` of multiplicity
one: start the chain at `C_{Z₀}` and end it at `Σ mᵥCᵥ = X_k`. -/
theorem injective_specialFiberComponentι_appTop (Z₀ : irreducibleComponents S.specialFiber)
    (hZ₀ : S.specialFiberMultiplicity Z₀ = 1)
    (hstep : ∀ a : irreducibleComponents S.specialFiber → ℕ,
      (∀ W, a W ≤ S.specialFiberMultiplicity W) → a Z₀ = 1 → a ≠ S.specialFiberMultiplicity →
      ∃ W, a W < S.specialFiberMultiplicity W ∧
        S.specialFiberComponentDegree W
          (Stacks.Divisors.negativeTwist (∏ V, S.specialFiberComponentIdeal V ^ a V))
          (@Stacks.Divisors.stacksIsInvertible_negativeTwist _ _
            (Stacks.Divisors.isEffectiveCartierDivisor_prod Finset.univ _ a
              fun V _ => S.isEffectiveCartierDivisor_specialFiberComponent V)) < 0) :
    Function.Injective (S.specialFiberComponentι Z₀).appTop.hom := by
  classical
  let a : irreducibleComponents S.specialFiber → ℕ := fun V => if V = Z₀ then 1 else 0
  have ha : ∀ W ∈ Finset.univ, a W ≤ S.specialFiberMultiplicity W := fun W _ => by
    by_cases h : W = Z₀ <;> simp [a, h, hZ₀]
  have hinj := injective_inclusion_prod_appTop Z₀ hZ₀ hstep _ a ha (by simp [a]) rfl
  have hDa : (∏ V, S.specialFiberComponentIdeal V ^ a V) = S.specialFiberComponentIdeal Z₀ := by
    rw [Fintype.prod_eq_single Z₀ fun V hV => by simp [a, hV]]
    simp [a]
  have hgen : ∀ (I J : S.X.IdealSheafData) (_ : I = S.specialFiberIdeal)
      (_ : J = S.specialFiberComponentIdeal Z₀) (h : I ≤ J),
      Function.Injective (Scheme.IdealSheafData.inclusion h).appTop.hom →
      Function.Injective (Scheme.IdealSheafData.inclusion
        (S.specialFiberIdeal_le_specialFiberComponentIdeal Z₀)).appTop.hom := by
    rintro I J rfl rfl h hh
    exact hh
  have h1 := hgen _ _ S.specialFiberIdeal_eq_prod.symm hDa _ hinj
  have hι : S.specialFiberComponentι Z₀ =
      Scheme.IdealSheafData.inclusion (S.specialFiberIdeal_le_specialFiberComponentIdeal Z₀) ≫
        (asIso S.specialFiberι.toImage).inv := rfl
  rw [hι, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  have : IsIso (asIso S.specialFiberι.toImage).inv.appTop := by
    show IsIso ((asIso S.specialFiberι.toImage).inv.app ⊤)
    infer_instance
  exact h1.comp (ConcreteCategory.bijective_of_isIso
    (asIso S.specialFiberι.toImage).inv.appTop).1

/-- **`H⁰(X_k, 𝒪_{X_k}) = k` from a component with `H⁰ = k`.** If the restriction of global
functions from `X_k` to a component `C` is injective and `H⁰(C, 𝒪_C) = k`, then
`H⁰(X_k, 𝒪_{X_k}) = k`. -/
theorem isIso_globalSections_specialFiber_of_injective (Z : irreducibleComponents S.specialFiber)
    (hinj : Function.Injective (S.specialFiberComponentι Z).appTop.hom)
    (hZ : IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop)) :
    IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫ S.specialFiberToSpec.appTop) := by
  have hcomp : (Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop =
      ((Scheme.ΓSpecIso (.of S.k)).inv ≫ S.specialFiberToSpec.appTop) ≫
        (S.specialFiberComponentι Z).appTop := by
    rw [RegularModelSituation.specialFiberComponentToSpec, Scheme.Hom.comp_appTop,
      Category.assoc]
  have hbij := ConcreteCategory.bijective_of_isIso
    ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop)
  rw [hcomp] at hbij
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun x y hxy => hbij.1 ?_, fun c => ?_⟩
  · show (S.specialFiberComponentι Z).appTop.hom _ = (S.specialFiberComponentι Z).appTop.hom _
    exact congrArg _ hxy
  · obtain ⟨a, ha⟩ := hbij.2 ((S.specialFiberComponentι Z).appTop.hom c)
    refine ⟨a, hinj ?_⟩
    rw [← ha]
    rfl

/-- **The genus of `X_k` is the genus of `C`** once `H⁰(X_k, 𝒪_{X_k}) = k` and
`χ(C, 𝒪_C) = χ(X_k, 𝒪_{X_k})`: both curves have `χ = 1 - g`. -/
theorem genus_specialFiber_eq_of_eulerCharacteristic_eq
    [IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫ S.specialFiberToSpec.appTop)]
    (hχ : eulerCharacteristic S.K S.C_to_K (SheafOfModules.unit S.C.ringCatSheaf) =
      eulerCharacteristic S.k S.specialFiberToSpec
        (SheafOfModules.unit S.specialFiber.ringCatSheaf)) :
    genus S.specialFiberToSpec = genus S.C_to_K := by
  have h1 := one_sub_genus_curve_eq_eulerCharacteristic S
  have h2 := one_sub_genus_eq_eulerCharacteristic_unit S.k S.specialFiberToSpec
    (S.toRegularModelSituation.topologicalKrullDim_specialFiber S.nonempty_specialFiber).le
    (finrank_globalSections_eq_one_of_isIso S.k S.specialFiberToSpec)
  omega

/-- **Part (3) of [Stacks, Tag 0CE8], the global functions.** At a smooth `k`-rational point `x`
of `X_k`, `H⁰(X_k, 𝒪_{X_k}) = k`: the component `C₀` through `x` has `m₀ = 1` and
`H⁰(C₀, 𝒪) = k`, and the global functions of `X_k` embed into those of `C₀`. -/
theorem isIso_globalSections_specialFiber_of_smoothAt (x : S.specialFiber)
    (hx : IsRationalPoint S.specialFiberToSpec x)
    (hsm : InfinitesimalLifting.SmoothAt S.specialFiberToSpec x) :
    IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫ S.specialFiberToSpec.appTop) := by
  let Z₀ : irreducibleComponents S.specialFiber :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  obtain ⟨hΓ, hm⟩ := isIso_globalSections_specialFiberComponent_and_specialFiberMultiplicity_eq_one
    x hx hsm Z₀ mem_irreducibleComponent
  exact isIso_globalSections_specialFiber_of_injective Z₀
    (injective_specialFiberComponentι_appTop Z₀ hm
      (S.exists_specialFiberComponentDegree_negativeTwist_neg Z₀ hm)) hΓ

variable (S) in
/-- **Stacks Project, Tag 0CE8.** In Situation [Stacks, Tag 0C61] assume that the curve `C` has a
`K`-rational point. Then

1. the special fibre `X_k` has a `k`-rational point `x` at which `X_k ⟶ Spec(k)` is smooth;
2. every irreducible component `Cᵢ` of `X_k` through `x` has `H⁰(Cᵢ, 𝒪_{Cᵢ}) = k` and
   multiplicity `mᵢ = 1` in `X_k = Σ mᵢCᵢ`;
3. `H⁰(X_k, 𝒪_{X_k}) = k`, and the genus of `X_k` is the genus of `C`.

`H⁰(Y, 𝒪_Y) = k` is the assertion that the canonical map `k ⟶ Γ(Y, 𝒪_Y)` is an isomorphism, and
the genus is `AlgebraicGeometry.genus`, `dim H¹(𝒪)` over the base field. -/
@[stacks 0CE8 "the k-rational smooth point x of X_k, H⁰(Cᵢ) = k and mᵢ = 1 for the components \
through x, H⁰(X_k) = k and g(X_k) = g(C)"]
theorem exists_isRationalPoint_smoothAt_specialFiber_and_genus_eq (p : Spec (.of S.K) ⟶ S.C)
    (hp : p ≫ S.C_to_K = 𝟙 _) :
    (∃ x : S.specialFiber, IsRationalPoint S.specialFiberToSpec x ∧
      InfinitesimalLifting.SmoothAt S.specialFiberToSpec x ∧
      ∀ Z : irreducibleComponents S.specialFiber, x ∈ Z.1 →
        IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop) ∧
          S.specialFiberMultiplicity Z = 1) ∧
    IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫ S.specialFiberToSpec.appTop) ∧
      genus S.specialFiberToSpec = genus S.C_to_K := by
  obtain ⟨x, hx, hsm, h2⟩ := S.exists_isRationalPoint_smoothAt_specialFiber p hp
  have := isIso_globalSections_specialFiber_of_smoothAt x hx hsm
  exact ⟨⟨x, hx, hsm, h2⟩, this,
    genus_specialFiber_eq_of_eulerCharacteristic_eq (S := S)
      S.eulerCharacteristic_C_eq_specialFiber⟩

end RegularProperModelSituation

end Stacks.Models

end
