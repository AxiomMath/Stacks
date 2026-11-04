module

public import StacksFrontier.Homology.Perfect.PerfectConeDegreeZeroLift

/-!
# Lifting degree-zero cocycles of a fibre through two maps at once

Let `A` be a commutative ring and `𝔭` a prime with residue field `κ(𝔭)`. This file states the
fibrewise lifting of `StacksDraft.ConeLift.exists_cocycle_lift_of_isPerfect` for complexes
indexed by `ℕ`, and for a pair of maps `ΦX : C ⟶ DX`, `ΦY : C ⟶ DY` out of the same complex: if
`H⁰(ΦX ⊗ κ(𝔭))` is injective, the degree-one classes killed by both `ΦX ⊗ κ(𝔭)` and
`ΦY ⊗ κ(𝔭)` are coboundaries, and degree-zero cocycles of `DX ⊗ κ(𝔭)` and `DY ⊗ κ(𝔭)` lift,
then every degree-zero cocycle of `C ⊗ κ(𝔭)` lifts, up to a scalar `s ∉ 𝔭`, to a degree-zero
cocycle of `C`.

This is the form of the argument of [Stacks, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
used in the proof of the theorem of the cube, where the two maps are restrictions to two faces.
It is obtained from the one-map statement applied to `(ΦX, ΦY) : C ⟶ DX ⊞ DY`, after extending
the complexes from `ℕ` to `ℤ` by zero.

## Main results

* `StacksDraft.ConeLift.exists_cocycle_lift_of_isPerfect_nat`: the one-map statement for
  complexes indexed by `ℕ`.
* `StacksDraft.ConeLift.exists_cocycle_lift_of_two_faces`: the two-map statement.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open StacksDraft.Perfect (IsPerfect)

universe u

namespace StacksDraft.ConeLift

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A]

section Transport

variable {S : Type u} [CommRing S] (ρ : A →+* S)

/-- Base change of the inverse of an isomorphism undoes base change of the isomorphism. -/
theorem bcMap_inv_hom_apply {M N : ModuleCat.{u} A} (e : M ≅ N) (x : bcObj ρ M) :
    (bcMap ρ e.inv).hom ((bcMap ρ e.hom).hom x) = x := by
  rw [bcMap_apply_bcMap, e.hom_inv_id, bcMap_id]; rfl

/-- Base change of an isomorphism undoes base change of its inverse. -/
theorem bcMap_hom_inv_apply {M N : ModuleCat.{u} A} (e : M ≅ N) (x : bcObj ρ N) :
    (bcMap ρ e.hom).hom ((bcMap ρ e.inv).hom x) = x := by
  rw [bcMap_apply_bcMap, e.inv_hom_id, bcMap_id]; rfl

/-- Base change of a three-fold composite, applied to an element. -/
theorem bcMap_comp₃_apply {M N L P : ModuleCat.{u} A} (f : M ⟶ N) (g : N ⟶ L) (h : L ⟶ P)
    (x : bcObj ρ M) :
    (bcMap ρ (f ≫ g ≫ h)).hom x = (bcMap ρ h).hom ((bcMap ρ g).hom ((bcMap ρ f).hom x)) := by
  rw [bcMap_apply_bcMap, bcMap_apply_bcMap]

end Transport

/-- The terms of the extension by zero of a complex indexed by `ℕ` to `ℤ`. -/
noncomputable abbrev extXIso (K : CochainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) (i : ℤ)
    (h : (n : ℤ) = i) :
    ((ComplexShape.embeddingUpNat.extendFunctor _).obj K).X i ≅ K.X n :=
  K.extendXIso ComplexShape.embeddingUpNat h

/-- The differential of the extension by zero of a complex indexed by `ℕ` between the images of
degrees `n` and `m` is `K.d n m`, transported along `extXIso`. -/
theorem ext_d_eq (K : CochainComplex (ModuleCat.{u} A) ℕ) (n m : ℕ) (i j : ℤ)
    (hi : (n : ℤ) = i) (hj : (m : ℤ) = j) :
    ((ComplexShape.embeddingUpNat.extendFunctor _).obj K).d i j =
      (extXIso K n i hi).hom ≫ K.d n m ≫ (extXIso K m j hj).inv :=
  K.extend_d_eq ComplexShape.embeddingUpNat hi hj

/-- The component at the image of degree `n` of the extension by zero of a map of complexes
indexed by `ℕ` is its component in degree `n`, transported along `extXIso`. -/
theorem ext_map_f {K L : CochainComplex (ModuleCat.{u} A) ℕ} (φ : K ⟶ L) (n : ℕ) (i : ℤ)
    (hi : (n : ℤ) = i) :
    ((ComplexShape.embeddingUpNat.extendFunctor _).map φ).f i =
      (extXIso K n i hi).hom ≫ φ.f n ≫ (extXIso L n i hi).inv :=
  HomologicalComplex.extendMap_f φ ComplexShape.embeddingUpNat hi

/-- The extension by zero of a complex indexed by `ℕ` vanishes in degree `-1`. -/
theorem isZero_ext_X_neg (K : CochainComplex (ModuleCat.{u} A) ℕ) :
    IsZero (((ComplexShape.embeddingUpNat.extendFunctor _).obj K).X (-1)) :=
  K.isZero_extend_X ComplexShape.embeddingUpNat (-1) (fun n h => by
    change ((n : ℤ)) = -1 at h
    omega)

/-- If a complex indexed by `ℕ` vanishes in degrees `≥ b`, its extension by zero to `ℤ` is
strictly concentrated in degrees `≤ b`. -/
theorem isStrictlyLE_ext (K : CochainComplex (ModuleCat.{u} A) ℕ) (b : ℕ)
    (hK : ∀ n, b ≤ n → IsZero (K.X n)) :
    CochainComplex.IsStrictlyLE ((ComplexShape.embeddingUpNat.extendFunctor _).obj K) (b : ℤ) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = i := ⟨i.toNat, by omega⟩
  exact (hK n (by omega)).of_iso (extXIso K n _ rfl)

/-- The terms of the extension by zero of a complex of flat modules are flat. -/
theorem flat_ext_X (K : CochainComplex (ModuleCat.{u} A) ℕ) [∀ n, Module.Flat A (K.X n)]
    (i : ℤ) : Module.Flat A (((ComplexShape.embeddingUpNat.extendFunctor _).obj K).X i) := by
  rcases lt_or_ge i 0 with hi | hi
  · have hz : IsZero (((ComplexShape.embeddingUpNat.extendFunctor _).obj K).X i) :=
      K.isZero_extend_X ComplexShape.embeddingUpNat i (fun n h => by
        change ((n : ℤ)) = i at h
        omega)
    have := ModuleCat.subsingleton_of_isZero hz
    have := Module.Free.of_subsingleton A
      (((ComplexShape.embeddingUpNat.extendFunctor _).obj K).X i)
    exact Module.Flat.of_free
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = i := ⟨i.toNat, by omega⟩
    exact Module.Flat.of_linearEquiv (extXIso K n _ rfl).toLinearEquiv

/-- The differential of the extension by zero vanishes on an element iff `K.d n m` vanishes on its
transport to `K.X n`. -/
private theorem ext_d_apply_eq_zero_iff (K : CochainComplex (ModuleCat.{u} A) ℕ) (n m : ℕ)
    (i j : ℤ) (hi : (n : ℤ) = i) (hj : (m : ℤ) = j)
    (z : ((ComplexShape.embeddingUpNat.extendFunctor _).obj K).X i) :
    (((ComplexShape.embeddingUpNat.extendFunctor _).obj K).d i j).hom z = 0 ↔
      (K.d n m).hom ((extXIso K n i hi).hom z) = 0 := by
  rw [ext_d_eq K n m i j hi hj]
  change (extXIso K m j hj).inv ((K.d n m).hom ((extXIso K n i hi).hom z)) = 0 ↔ _
  exact (extXIso K m j hj).toLinearEquiv.symm.map_eq_zero_iff

/-- The base change of the differential of the extension by zero, applied to an element, is that
of `K.d n m` up to the transport isomorphisms. -/
private theorem bcMap_ext_d_apply {S : Type u} [CommRing S] (ρ : A →+* S)
    (K : CochainComplex (ModuleCat.{u} A) ℕ) (n m : ℕ)
    (i j : ℤ) (hi : (n : ℤ) = i) (hj : (m : ℤ) = j)
    (z : bcObj ρ (((ComplexShape.embeddingUpNat.extendFunctor _).obj K).X i)) :
    (bcMap ρ (((ComplexShape.embeddingUpNat.extendFunctor _).obj K).d i j)).hom z =
      (bcMap ρ (extXIso K m j hj).inv).hom
        ((bcMap ρ (K.d n m)).hom ((bcMap ρ (extXIso K n i hi).hom).hom z)) := by
  rw [ext_d_eq K n m i j hi hj, bcMap_comp₃_apply]

/-- The base change of the component of the extension by zero of a map, applied to an element, is
that of `φ.f n` up to the transport isomorphisms. -/
private theorem bcMap_ext_map_apply {S : Type u} [CommRing S] (ρ : A →+* S)
    {K L : CochainComplex (ModuleCat.{u} A) ℕ} (φ : K ⟶ L)
    (n : ℕ) (i : ℤ) (hi : (n : ℤ) = i)
    (z : bcObj ρ (((ComplexShape.embeddingUpNat.extendFunctor _).obj K).X i)) :
    (bcMap ρ (((ComplexShape.embeddingUpNat.extendFunctor _).map φ).f i)).hom z =
      (bcMap ρ (extXIso L n i hi).inv).hom
        ((bcMap ρ (φ.f n)).hom ((bcMap ρ (extXIso K n i hi).hom).hom z)) := by
  rw [ext_map_f φ n i hi, bcMap_comp₃_apply]

/-- Base change of the inverse of an isomorphism vanishes on an element iff the element does. -/
private theorem bcMap_inv_apply_eq_zero_iff {S : Type u} [CommRing S] (ρ : A →+* S)
    {M N : ModuleCat.{u} A} (e : M ≅ N) (x : bcObj ρ N) :
    (bcMap ρ e.inv).hom x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  have := congrArg (bcMap ρ e.hom).hom h
  rwa [bcMap_hom_inv_apply, map_zero] at this

/-- **Lifting a degree-zero cocycle of a fibre, for perfect complexes indexed by `ℕ`.** This is
`StacksDraft.ConeLift.exists_cocycle_lift_of_isPerfect` for complexes concentrated in degrees
`0, …, b - 1`, read through the extension by zero to `ℤ`. -/
theorem exists_cocycle_lift_of_isPerfect_nat (𝔭 : Ideal A) [𝔭.IsPrime]
    {C D : CochainComplex (ModuleCat.{u} A) ℕ} (Φ : C ⟶ D) (b : ℕ)
    (hCb : ∀ n, b ≤ n → IsZero (C.X n)) (hDb : ∀ n, b ≤ n → IsZero (D.X n))
    [∀ n, Module.Flat A (C.X n)] [∀ n, Module.Flat A (D.X n)]
    (hCp : IsPerfect (DerivedCategory.Q.obj ((ComplexShape.embeddingUpNat.extendFunctor _).obj C)))
    (hDp : IsPerfect (DerivedCategory.Q.obj ((ComplexShape.embeddingUpNat.extendFunctor _).obj D)))
    (h0 : ∀ x : bcObj (algebraMap A 𝔭.ResidueField) (C.X 0),
      (bcMap (algebraMap A 𝔭.ResidueField) (C.d 0 1)).hom x = 0 →
      (bcMap (algebraMap A 𝔭.ResidueField) (Φ.f 0)).hom x = 0 → x = 0)
    (h1 : ∀ c : bcObj (algebraMap A 𝔭.ResidueField) (C.X 1),
      (bcMap (algebraMap A 𝔭.ResidueField) (C.d 1 2)).hom c = 0 →
      ∀ e : bcObj (algebraMap A 𝔭.ResidueField) (D.X 0),
      (bcMap (algebraMap A 𝔭.ResidueField) (Φ.f 1)).hom c =
        (bcMap (algebraMap A 𝔭.ResidueField) (D.d 0 1)).hom e →
        ∃ c' : bcObj (algebraMap A 𝔭.ResidueField) (C.X 0),
          (bcMap (algebraMap A 𝔭.ResidueField) (C.d 0 1)).hom c' = c)
    (hsurj : ∀ y : bcObj (algebraMap A 𝔭.ResidueField) (D.X 0),
      (bcMap (algebraMap A 𝔭.ResidueField) (D.d 0 1)).hom y = 0 →
      ∃ y' : D.X 0, (D.d 0 1).hom y' = 0 ∧ ∃ t : A, t ∉ 𝔭 ∧
        (bcUnit (algebraMap A 𝔭.ResidueField) _).hom y' = t • y)
    (x : bcObj (algebraMap A 𝔭.ResidueField) (C.X 0))
    (hx : (bcMap (algebraMap A 𝔭.ResidueField) (C.d 0 1)).hom x = 0) :
    ∃ c : C.X 0, (C.d 0 1).hom c = 0 ∧ ∃ s : A, s ∉ 𝔭 ∧
      (bcUnit (algebraMap A 𝔭.ResidueField) _).hom c = s • x := by
  let E := ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} A)
  have := isStrictlyLE_ext C b hCb
  have := isStrictlyLE_ext D b hDb
  have : ∀ i, Module.Flat A ((E.obj C).X i) := flat_ext_X C
  have : ∀ i, Module.Flat A ((E.obj D).X i) := flat_ext_X D
  -- the hypotheses, read on the extended complexes
  have h0' : ∀ z : bcObj (algebraMap A 𝔭.ResidueField) ((E.obj C).X 0),
      (bcMap (algebraMap A 𝔭.ResidueField) ((E.obj C).d 0 1)).hom z = 0 →
        (bcMap (algebraMap A 𝔭.ResidueField) ((E.map Φ).f 0)).hom z = 0 → z = 0 := by
    intro z hz1 hz2
    rw [bcMap_ext_d_apply _ C 0 1 0 1 rfl rfl, bcMap_inv_apply_eq_zero_iff] at hz1
    rw [bcMap_ext_map_apply _ Φ 0 0 rfl, bcMap_inv_apply_eq_zero_iff] at hz2
    have := h0 _ hz1 hz2
    rw [← bcMap_inv_hom_apply (algebraMap A 𝔭.ResidueField) (extXIso C 0 0 rfl) z, this, map_zero]
  have h1' : ∀ c : bcObj (algebraMap A 𝔭.ResidueField) ((E.obj C).X 1),
      (bcMap (algebraMap A 𝔭.ResidueField) ((E.obj C).d 1 2)).hom c = 0 →
      ∀ e : bcObj (algebraMap A 𝔭.ResidueField) ((E.obj D).X 0),
      (bcMap (algebraMap A 𝔭.ResidueField) ((E.map Φ).f 1)).hom c =
        (bcMap (algebraMap A 𝔭.ResidueField) ((E.obj D).d 0 1)).hom e →
        ∃ c' : bcObj (algebraMap A 𝔭.ResidueField) ((E.obj C).X 0),
          (bcMap (algebraMap A 𝔭.ResidueField) ((E.obj C).d 0 1)).hom c' = c := by
    intro c hc e he
    rw [bcMap_ext_d_apply _ C 1 2 1 2 rfl rfl, bcMap_inv_apply_eq_zero_iff] at hc
    rw [bcMap_ext_map_apply _ Φ 1 1 rfl, bcMap_ext_d_apply _ D 0 1 0 1 rfl rfl] at he
    have he' := congrArg (bcMap (algebraMap A 𝔭.ResidueField) (extXIso D 1 1 rfl).hom).hom he
    rw [bcMap_hom_inv_apply, bcMap_hom_inv_apply] at he'
    obtain ⟨c₀, hc₀⟩ := h1 _ hc _ he'
    refine ⟨(bcMap (algebraMap A 𝔭.ResidueField) (extXIso C 0 0 rfl).inv).hom c₀, ?_⟩
    rw [bcMap_ext_d_apply _ C 0 1 0 1 rfl rfl, bcMap_hom_inv_apply, hc₀, bcMap_inv_hom_apply]
  have hsurj' : ∀ y : bcObj (algebraMap A 𝔭.ResidueField) ((E.obj D).X 0),
      (bcMap (algebraMap A 𝔭.ResidueField) ((E.obj D).d 0 1)).hom y = 0 →
      ∃ y' : (E.obj D).X 0, ((E.obj D).d 0 1).hom y' = 0 ∧ ∃ t : A, t ∉ 𝔭 ∧
        (bcUnit (algebraMap A 𝔭.ResidueField) _).hom y' = t • y := by
    intro y hy
    rw [bcMap_ext_d_apply _ D 0 1 0 1 rfl rfl, bcMap_inv_apply_eq_zero_iff] at hy
    obtain ⟨y₀, hy₀d, t, ht, hy₀⟩ := hsurj _ hy
    refine ⟨(extXIso D 0 0 rfl).inv.hom y₀, ?_, t, ht, ?_⟩
    · rw [ext_d_apply_eq_zero_iff D 0 1 0 1 rfl rfl]
      simpa using hy₀d
    · rw [← bcMap_bcUnit, hy₀, map_smul, bcMap_inv_hom_apply]
  obtain ⟨c, hcd, s, hs, hcx⟩ := exists_cocycle_lift_of_isPerfect 𝔭 (E.map Φ) (b : ℤ)
    (isZero_ext_X_neg D) hCp hDp h0' h1' hsurj'
    ((bcMap (algebraMap A 𝔭.ResidueField) (extXIso C 0 0 rfl).inv).hom x)
    (by rw [bcMap_ext_d_apply _ C 0 1 0 1 rfl rfl, bcMap_hom_inv_apply, hx, map_zero])
  refine ⟨(extXIso C 0 0 rfl).hom.hom c, ?_, s, hs, ?_⟩
  · exact (ext_d_apply_eq_zero_iff C 0 1 0 1 rfl rfl _).1 hcd
  · rw [← bcMap_bcUnit, hcx, map_smul, bcMap_hom_inv_apply]

/-- The terms of a biproduct of complexes of flat modules are flat. -/
theorem flat_biprod_X {K L : CochainComplex (ModuleCat.{u} A) ℕ} [∀ n, Module.Flat A (K.X n)]
    [∀ n, Module.Flat A (L.X n)] (n : ℕ) : Module.Flat A ((K ⊞ L).X n) :=
  have : Module.Flat A (K.X n × L.X n) := Module.Flat.prod
  Module.Flat.of_linearEquiv
    ((HomologicalComplex.biprodXIso K L n ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv)

/-- **Lifting a degree-zero cocycle of a fibre through two maps at once.** Let
`ΦX : C ⟶ DX` and `ΦY : C ⟶ DY` be maps of complexes of flat `A`-modules indexed by `ℕ`, vanishing
in degrees `≥ b`, with perfect images in `D(A)`. Write `- ⊗ κ(𝔭)` for base change to the residue
field of a prime `𝔭`. Assume that a degree-zero cocycle of `C ⊗ κ(𝔭)` killed by `ΦX ⊗ κ(𝔭)` is
zero, that a degree-one cocycle of `C ⊗ κ(𝔭)` whose images under `ΦX ⊗ κ(𝔭)` and `ΦY ⊗ κ(𝔭)` are
coboundaries is a coboundary, and that degree-zero cocycles of `DX ⊗ κ(𝔭)` and `DY ⊗ κ(𝔭)` lift
to degree-zero cocycles up to a scalar outside `𝔭`. Then every degree-zero cocycle `x` of
`C ⊗ κ(𝔭)` lifts, up to a scalar `s ∉ 𝔭`, to a degree-zero cocycle `c` of `C`.

This is `StacksDraft.ConeLift.exists_cocycle_lift_of_isPerfect_nat` applied to the map
`(ΦX, ΦY) : C ⟶ DX ⊞ DY`. -/
theorem exists_cocycle_lift_of_two_faces
    (𝔭 : Ideal A) [𝔭.IsPrime] {C DX DY : CochainComplex (ModuleCat.{u} A) ℕ}
    (ΦX : C ⟶ DX) (ΦY : C ⟶ DY) (b : ℕ)
    (hCb : ∀ n, b ≤ n → IsZero (C.X n)) (hXb : ∀ n, b ≤ n → IsZero (DX.X n))
    (hYb : ∀ n, b ≤ n → IsZero (DY.X n))
    [∀ n, Module.Flat A (C.X n)] [∀ n, Module.Flat A (DX.X n)] [∀ n, Module.Flat A (DY.X n)]
    (hCp : IsPerfect (DerivedCategory.Q.obj ((ComplexShape.embeddingUpNat.extendFunctor _).obj C)))
    (hXp : IsPerfect
      (DerivedCategory.Q.obj ((ComplexShape.embeddingUpNat.extendFunctor _).obj DX)))
    (hYp : IsPerfect
      (DerivedCategory.Q.obj ((ComplexShape.embeddingUpNat.extendFunctor _).obj DY)))
    (h0 : ∀ x : bcObj (algebraMap A 𝔭.ResidueField) (C.X 0),
      (bcMap (algebraMap A 𝔭.ResidueField) (C.d 0 1)).hom x = 0 →
      (bcMap (algebraMap A 𝔭.ResidueField) (ΦX.f 0)).hom x = 0 → x = 0)
    (h1 : ∀ c : bcObj (algebraMap A 𝔭.ResidueField) (C.X 1),
      (bcMap (algebraMap A 𝔭.ResidueField) (C.d 1 2)).hom c = 0 →
      ∀ (eX : bcObj (algebraMap A 𝔭.ResidueField) (DX.X 0))
        (eY : bcObj (algebraMap A 𝔭.ResidueField) (DY.X 0)),
      (bcMap (algebraMap A 𝔭.ResidueField) (ΦX.f 1)).hom c =
        (bcMap (algebraMap A 𝔭.ResidueField) (DX.d 0 1)).hom eX →
      (bcMap (algebraMap A 𝔭.ResidueField) (ΦY.f 1)).hom c =
        (bcMap (algebraMap A 𝔭.ResidueField) (DY.d 0 1)).hom eY →
      ∃ c' : bcObj (algebraMap A 𝔭.ResidueField) (C.X 0),
        (bcMap (algebraMap A 𝔭.ResidueField) (C.d 0 1)).hom c' = c)
    (hsX : ∀ y : bcObj (algebraMap A 𝔭.ResidueField) (DX.X 0),
      (bcMap (algebraMap A 𝔭.ResidueField) (DX.d 0 1)).hom y = 0 →
      ∃ y' : DX.X 0, (DX.d 0 1).hom y' = 0 ∧ ∃ t : A, t ∉ 𝔭 ∧
        (bcUnit (algebraMap A 𝔭.ResidueField) _).hom y' = t • y)
    (hsY : ∀ y : bcObj (algebraMap A 𝔭.ResidueField) (DY.X 0),
      (bcMap (algebraMap A 𝔭.ResidueField) (DY.d 0 1)).hom y = 0 →
      ∃ y' : DY.X 0, (DY.d 0 1).hom y' = 0 ∧ ∃ t : A, t ∉ 𝔭 ∧
        (bcUnit (algebraMap A 𝔭.ResidueField) _).hom y' = t • y)
    (x : bcObj (algebraMap A 𝔭.ResidueField) (C.X 0))
    (hx : (bcMap (algebraMap A 𝔭.ResidueField) (C.d 0 1)).hom x = 0) :
    ∃ c : C.X 0, (C.d 0 1).hom c = 0 ∧ ∃ s : A, s ∉ 𝔭 ∧
      (bcUnit (algebraMap A 𝔭.ResidueField) _).hom c = s • x := by
  let E := ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} A)
  let Φ : C ⟶ DX ⊞ DY := biprod.lift ΦX ΦY
  have : ∀ n, Module.Flat A ((DX ⊞ DY).X n) := flat_biprod_X
  have hfst : ∀ n, Φ.f n ≫ (biprod.fst : DX ⊞ DY ⟶ DX).f n = ΦX.f n := fun n => by
    rw [← HomologicalComplex.comp_f, biprod.lift_fst]
  have hsnd : ∀ n, Φ.f n ≫ (biprod.snd : DX ⊞ DY ⟶ DY).f n = ΦY.f n := fun n => by
    rw [← HomologicalComplex.comp_f, biprod.lift_snd]
  have hDb : ∀ n, b ≤ n → IsZero ((DX ⊞ DY).X n) := fun n hn =>
    ((biprod_isZero_iff _ _).2 ⟨hXb n hn, hYb n hn⟩).of_iso
      (HomologicalComplex.biprodXIso DX DY n)
  have hDp : IsPerfect (DerivedCategory.Q.obj (E.obj (DX ⊞ DY))) := by
    have : PreservesBinaryBiproducts E := preservesBinaryBiproducts_of_preservesBiproducts E
    have : PreservesBinaryBiproducts (DerivedCategory.Q (C := ModuleCat.{u} A)) :=
      preservesBinaryBiproducts_of_preservesBiproducts _
    have hb := (StacksDraft.Perfect.isPerfect_of_distinguished _
      (Pretriangulated.binaryBiproductTriangle_distinguished
        (DerivedCategory.Q.obj (E.obj DX)) (DerivedCategory.Q.obj (E.obj DY)))).2.1 hXp hYp
    exact StacksDraft.Perfect.isPerfect_of_iso
      (DerivedCategory.Q.mapIso (E.mapBiprod DX DY) ≪≫
        DerivedCategory.Q.mapBiprod (E.obj DX) (E.obj DY)) hb
  refine exists_cocycle_lift_of_isPerfect_nat 𝔭 Φ b hCb hDb hCp hDp ?_ ?_ ?_ x hx
  · intro z hz1 hz2
    refine h0 z hz1 ?_
    rw [← hfst, ← bcMap_apply_bcMap, hz2, map_zero]
  · intro c hc e he
    refine h1 c hc ((bcMap _ ((biprod.fst : DX ⊞ DY ⟶ DX).f 0)).hom e)
      ((bcMap _ ((biprod.snd : DX ⊞ DY ⟶ DY).f 0)).hom e) ?_ ?_
    · rw [← hfst, ← bcMap_apply_bcMap, he, bcMap_apply_bcMap, bcMap_apply_bcMap,
        HomologicalComplex.Hom.comm]
    · rw [← hsnd, ← bcMap_apply_bcMap, he, bcMap_apply_bcMap, bcMap_apply_bcMap,
        HomologicalComplex.Hom.comm]
  · intro y hy
    have hyX :
        (bcMap _ (DX.d 0 1)).hom ((bcMap _ ((biprod.fst : DX ⊞ DY ⟶ DX).f 0)).hom y) = 0 := by
      rw [bcMap_apply_bcMap, HomologicalComplex.Hom.comm, ← bcMap_apply_bcMap, hy, map_zero]
    have hyY :
        (bcMap _ (DY.d 0 1)).hom ((bcMap _ ((biprod.snd : DX ⊞ DY ⟶ DY).f 0)).hom y) = 0 := by
      rw [bcMap_apply_bcMap, HomologicalComplex.Hom.comm, ← bcMap_apply_bcMap, hy, map_zero]
    obtain ⟨yX, hyXd, tX, htX, hyXu⟩ := hsX _ hyX
    obtain ⟨yY, hyYd, tY, htY, hyYu⟩ := hsY _ hyY
    refine ⟨tY • ((biprod.inl : DX ⟶ DX ⊞ DY).f 0).hom yX +
      tX • ((biprod.inr : DY ⟶ DX ⊞ DY).f 0).hom yY, ?_, tX * tY,
      fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim htX htY, ?_⟩
    · rw [map_add, map_smul, map_smul]
      show tY • ((biprod.inl : DX ⟶ DX ⊞ DY).f 0 ≫ (DX ⊞ DY).d 0 1).hom yX +
        tX • ((biprod.inr : DY ⟶ DX ⊞ DY).f 0 ≫ (DX ⊞ DY).d 0 1).hom yY = 0
      rw [HomologicalComplex.Hom.comm, HomologicalComplex.Hom.comm]
      show tY • ((biprod.inl : DX ⟶ DX ⊞ DY).f 1).hom ((DX.d 0 1).hom yX) +
        tX • ((biprod.inr : DY ⟶ DX ⊞ DY).f 1).hom ((DY.d 0 1).hom yY) = 0
      rw [hyXd, hyYd, map_zero, map_zero, smul_zero, smul_zero, add_zero]
    · rw [map_add, map_smul, map_smul, ← bcMap_bcUnit, ← bcMap_bcUnit, hyXu, hyYu, map_smul,
        map_smul, bcMap_apply_bcMap, bcMap_apply_bcMap, smul_smul, smul_smul, mul_comm tY tX,
        ← smul_add, ← LinearMap.add_apply, ← ModuleCat.hom_add, ← bcMap_add,
        ← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, ← HomologicalComplex.add_f_apply,
        biprod.total, HomologicalComplex.id_f, bcMap_id]
      rfl

end StacksDraft.ConeLift

end
