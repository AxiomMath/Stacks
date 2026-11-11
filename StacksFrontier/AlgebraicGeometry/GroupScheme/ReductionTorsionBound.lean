module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.ReductionTorsion
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.FiniteFieldPoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.LocalSchemeSections

/-!
# The prime-to-`ℓ` order of a torsion point is bounded by the points over a finite field

Let `𝒜` be a commutative group scheme over `Spec R`, separated and of finite type, let `O` be a
local domain over `R` whose residue field has characteristic `ℓ` and embeds over `R` into a finite
field `F`, and let `gk : O → k` be an injective `R`-algebra map into a field. For `a ∈ 𝒜(O)` whose
restriction `P ∈ 𝒜(k)` has finite order, the part of the order of `P` prime to `ℓ` is at most
`#𝒜(F)`.

The kernel of reduction `𝒜(O) → 𝒜(κ(O))` has no element of prime order `q ≠ ℓ`: such an element
and the unit agree at the closed point and are equalized by multiplication by `q`, which is
unramified there because `q` is invertible in the residue field
(`AlgebraicGeometry.unramifiedAt_zpow_id_left_of_isUnit`), so they are equal
(`AlgebraicGeometry.eq_of_comp_eq_of_unramifiedAt`). Passing to `F` loses nothing
(`AlgebraicGeometry.specMap_comp_injective_of_field`), restriction to `k` preserves orders
(`AlgebraicGeometry.specOverMap_comp_injective`), and the group theory is
`ordCompl_addOrderOf_le_of_injective_on_prime`.

## Main results

* `AlgebraicGeometry.eq_one_of_pow_eq_one_of_residue_eq`.
* `AlgebraicGeometry.ordCompl_addOrderOf_le_natCard`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R]

/-- A natural number nonzero in a field `K` is invertible in the residue field of the image point
of any morphism `Spec K ⟶ X`. -/
theorem isUnit_natCast_residueField_of_ne_zero {X : Scheme.{u}} {K : Type u} [Field K]
    (g : Spec (.of K) ⟶ X) {n : ℕ} (hn : (n : K) ≠ 0) :
    IsUnit (n : X.residueField (g (IsLocalRing.closedPoint K))) := by
  obtain ⟨φ, -⟩ : ∃ φ : X.residueField (g (IsLocalRing.closedPoint K)) ⟶ .of K,
      Spec.map φ ≫ X.fromSpecResidueField _ = g :=
    ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X g⟩
  refine isUnit_iff_ne_zero.mpr fun h => hn ?_
  simpa using congrArg φ.hom h

/-- **The kernel of reduction has no prime-to-the-residue-characteristic torsion.** Let `O` be a
local ring over `R` and `b ∈ 𝒜(O)` with `b ^ q = 1` whose restriction to `Spec κ(O)` is the
unit, with `q` invertible in the residue field of `𝒜` at the image of the closed point. Then
`b = 1`. -/
theorem eq_one_of_pow_eq_one_of_residue_eq {O : Type u} [CommRing O] [IsLocalRing O]
    [Algebra R O] (𝒜 : Over (Spec (.of R))) [GrpObj 𝒜] [IsCommMonObj 𝒜]
    [LocallyOfFiniteType 𝒜.hom] {q : ℕ} {b : specOver R O ⟶ 𝒜} (hb : b ^ q = 1)
    (hκ : Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ≫ b.left =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ≫ (1 : specOver R O ⟶ 𝒜).left)
    (hq : IsUnit (q : 𝒜.left.residueField (b.left (IsLocalRing.closedPoint O)))) : b = 1 := by
  apply Over.OverMorphism.ext
  refine eq_of_comp_eq_of_unramifiedAt ((𝟙 𝒜 : 𝒜 ⟶ 𝒜) ^ (q : ℤ)).left ?_ hκ
    (unramifiedAt_zpow_id_left_of_isUnit 𝒜 q _ hq)
  have h1 : b ≫ (𝟙 𝒜 : 𝒜 ⟶ 𝒜) ^ (q : ℤ) = 1 := by
    rw [GrpObj.comp_zpow, Category.comp_id, zpow_natCast, hb]
  have h2 : (1 : specOver R O ⟶ 𝒜) ≫ (𝟙 𝒜 : 𝒜 ⟶ 𝒜) ^ (q : ℤ) = 1 := by
    rw [GrpObj.comp_zpow, Category.comp_id, one_zpow]
  exact congrArg CommaMorphism.left (h1.trans h2.symm)

/-- Precomposition with a morphism over `Spec R`, as a homomorphism of additive groups of points
of a commutative group object. -/
noncomputable def precompAddHom {X Y : Over (Spec (.of R))} (h : X ⟶ Y)
    (𝒜 : Over (Spec (.of R))) [GrpObj 𝒜] [IsCommMonObj 𝒜] :
    Additive (Y ⟶ 𝒜) →+ Additive (X ⟶ 𝒜) :=
  MonoidHom.toAdditive
    { toFun := fun a => h ≫ a
      map_one' := MonObj.comp_one h
      map_mul' := fun a b => MonObj.comp_mul h a b }

@[simp]
lemma precompAddHom_apply {X Y : Over (Spec (.of R))} (h : X ⟶ Y) (𝒜 : Over (Spec (.of R)))
    [GrpObj 𝒜] [IsCommMonObj 𝒜] (a : Additive (Y ⟶ 𝒜)) :
    precompAddHom h 𝒜 a = Additive.ofMul (h ≫ a.toMul) := rfl

/-- The closed point of `Spec κ(O)` maps to the closed point of `Spec O`. -/
lemma specMap_residue_closedPoint (O : Type u) [CommRing O] [IsLocalRing O] :
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))
        (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) = IsLocalRing.closedPoint O := by
  apply PrimeSpectrum.ext
  change Ideal.comap (IsLocalRing.residue O) (IsLocalRing.maximalIdeal _) = _
  rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue]
  rfl

/-- **The prime-to-`ℓ` part of the order of a torsion point is at most `#𝒜(F)`.** Let `O` be a
local domain over `R` with residue field of characteristic `ℓ`, embedded over `R` into a finite
field `F`, and `gk : O → k` an injective `R`-algebra map to a field. For `a ∈ 𝒜(O)` whose
restriction to `k` has finite order, the part of that order prime to `ℓ` is at most `#𝒜(F)`. -/
theorem ordCompl_addOrderOf_le_natCard {O k F : Type u} [CommRing O] [IsLocalRing O]
    [IsDomain O] [Algebra R O] [Field k] [Algebra R k] [Field F] [Finite F] [Algebra R F]
    (𝒜 : Over (Spec (.of R))) [GrpObj 𝒜] [IsCommMonObj 𝒜] [LocallyOfFiniteType 𝒜.hom]
    [QuasiCompact 𝒜.hom] [IsSeparated 𝒜.hom] (gk : O →ₐ[R] k) (hgk : Function.Injective gk)
    (τ : IsLocalRing.ResidueField O →ₐ[R] F) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hchar : CharP (IsLocalRing.ResidueField O) ℓ) (a : specOver R O ⟶ 𝒜)
    (ha : IsOfFinAddOrder (Additive.ofMul (specOverMap gk ≫ a))) :
    ordCompl[ℓ] (addOrderOf (Additive.ofMul (specOverMap gk ≫ a))) ≤
      Nat.card (specOver R F ⟶ 𝒜) := by
  let res : O →ₐ[R] IsLocalRing.ResidueField O := IsScalarTower.toAlgHom R O _
  have hinj : Function.Injective (precompAddHom (specOverMap gk) 𝒜) := fun x y h =>
    Additive.toMul.injective (specOverMap_comp_injective 𝒜 gk hgk (congrArg Additive.toMul h))
  have hord : addOrderOf (Additive.ofMul (specOverMap gk ≫ a)) = addOrderOf (Additive.ofMul a) :=
    addOrderOf_injective _ hinj (Additive.ofMul a)
  have hfin : Finite (specOver R F ⟶ 𝒜) := by
    have := finite_sections_of_finite 𝒜.hom F
    exact Finite.of_injective (fun x : specOver R F ⟶ 𝒜 =>
      (⟨x.left, Over.w x⟩ : {p : Spec (.of F) ⟶ 𝒜.left //
        p ≫ 𝒜.hom = Spec.map (CommRingCat.ofHom (algebraMap R F))})) fun x y h =>
      Over.OverMorphism.ext (congrArg Subtype.val h)
  have : Finite (Additive (specOver R F ⟶ 𝒜)) := hfin
  have ha' : IsOfFinAddOrder (Additive.ofMul a) := by
    rw [← addOrderOf_pos_iff, ← hord]
    exact ha.addOrderOf_pos
  rw [hord]
  refine ordCompl_addOrderOf_le_of_injective_on_prime
    (precompAddHom (specOverMap (τ.comp res)) 𝒜) hℓ ?_ ha'
  intro q hq hqℓ z hqz hz0
  have hb : z.toMul ^ q = 1 := by
    have := congrArg Additive.toMul hqz
    rwa [toMul_nsmul, toMul_zero] at this
  have h1 : specOverMap (τ.comp res) ≫ z.toMul = specOverMap (τ.comp res) ≫ 1 := by
    rw [MonObj.comp_one]
    exact congrArg Additive.toMul hz0
  rw [← specOverMap_comp, Category.assoc, Category.assoc] at h1
  have h2 : specOverMap res ≫ z.toMul = specOverMap res ≫ 1 := by
    apply Over.OverMorphism.ext
    have h1' := congrArg CommaMorphism.left h1
    simp only [Over.comp_left, specOverMap_left] at h1'
    exact specMap_comp_injective_of_field (X := 𝒜.left) τ.toRingHom h1'
  have hκ : Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ≫ z.toMul.left =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ≫ (1 : specOver R O ⟶ 𝒜).left :=
    congrArg CommaMorphism.left h2
  have hq' : ((q : ℕ) : IsLocalRing.ResidueField O) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff _ ℓ]
    exact fun h => hqℓ ((Nat.prime_dvd_prime_iff_eq hℓ hq).mp h).symm
  have hunit := isUnit_natCast_residueField_of_ne_zero
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ≫ z.toMul.left) hq'
  have hpt : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ≫ z.toMul.left)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) =
        z.toMul.left (IsLocalRing.closedPoint O) := by
    change z.toMul.left (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField O))) = _
    rw [specMap_residue_closedPoint]
  rw [hpt] at hunit
  have := eq_one_of_pow_eq_one_of_residue_eq 𝒜 hb hκ hunit
  exact Additive.toMul.injective (this.trans toMul_zero.symm)

end AlgebraicGeometry

end
