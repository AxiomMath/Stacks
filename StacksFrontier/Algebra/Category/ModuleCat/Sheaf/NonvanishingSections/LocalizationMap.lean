module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjModuleRestriction
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistSectionRing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NonvanishingSections.DegreeZeroLocalizationLift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NonvanishingSections.TensorRestriction

/-!
# Sections on the nonvanishing open of a section of an invertible sheaf

Let `𝒪` be the structure sheaf of a scheme `X`, let `L` be an invertible sheaf of
`𝒪`-modules and let `s` be a global section of `L`. Writing `X_s` for the open on which `s`
does not vanish, a degree-zero homogeneous fraction `m / sⁿ`, with `m` a global section of
`F ⊗ L^{⊗ n}`, determines a section of `F` over `X_s`, because `sⁿ` trivializes `L^{⊗ n}`
there. This file constructs that map and identifies it by the fraction formula.

## Main definitions

* `Stacks.SheafOfModules.homogeneousLocalizationLift` is the ring-valued version of
  `Stacks.SheafOfModules.degreeZeroLocalizationLift`.
* `Stacks.SheafOfModules.sectionAtNonvanishingOpen` is the degree-zero homogeneous
  localization of the section module at `s`.
* `Stacks.SheafOfModules.tensorBasisAt` trivializes `F ⊗ L^{⊗ n}` over `X_s` by tensoring
  with `sⁿ`.
* `Stacks.SheafOfModules.sectionLocalizationMap` is the resulting map from degree-zero
  localized twisted sections to sections of `F` over `X_s`.

## Main results

* `Stacks.SheafOfModules.sectionLocalizationMap_fraction`: the value of the map on a
  fraction `m / sⁿ` is characterized by the restriction of `m` to `X_s` being the tensor of
  the value with `sⁿ`.
* `Stacks.SheafOfModules.sectionLocalizationMap_smul`: the map is linear over the induced
  ring map from the degree-zero homogeneous localization of the section ring.

## References

* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
-/

@[expose] public noncomputable section

namespace Stacks.SheafOfModules

attribute [local implicit_reducible] _root_.SheafOfModules.forget PresheafOfModules.restrictScalars
  TopCat.Presheaf.IsSheaf TopCat.Sheaf AlgebraicGeometry.SheafedSpace.sheaf

attribute [local instance_reducible] TensorSheafification.structureSheaf

open CategoryTheory Limits Opposite AlgebraicGeometry TopologicalSpace DirectSum
open scoped _root_.Stacks.SheafOfModules.TensorProduct

universe u

section RingFractionConstruction

variable {R : Type*} [CommRing R] {σ : Type*} [SetLike σ R] [AddSubgroupClass σ R]
  (A : ℕ → σ) [GradedRing A] {f : R}
  {K : Type*} [CommRing K]

omit [AddSubgroupClass σ R] [GradedRing A] in
private theorem ringFraction_values_eq (e : ℕ → R →+ K)
    (he : ∀ (n k : ℕ) (x : R), x ∈ A n → e (n + k) (f ^ k * x) = e n x)
    (n m : ℕ) (x y : R) (hx : x ∈ A n) (hy : y ∈ A m)
    (h : Localization.mk x (⟨f ^ n, by exact ⟨n, rfl⟩⟩ : Submonoid.powers f) =
      Localization.mk y (⟨f ^ m, by exact ⟨m, rfl⟩⟩ : Submonoid.powers f)) :
    e n x = e m y := by
  obtain ⟨⟨u, k, rfl⟩, hu⟩ := Localization.r_iff_exists.mp (Localization.mk_eq_mk_iff.mp h)
  change f ^ k * (f ^ m * x) = f ^ k * (f ^ n * y) at hu
  rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add] at hu
  rw [← he n (k + m) x hx, ← he m (k + n) y hy]
  rw [show n + (k + m) = m + (k + n) by omega, hu]

private noncomputable def ringFractionValue (hf : f ∈ A 1) (e : ℕ → R →+ K)
    (z : HomogeneousLocalization.Away A f) : K :=
  let h := HomogeneousLocalization.Away.mk_surjective A hf z
  e h.choose h.choose_spec.choose

private theorem ringFractionValue_eq (hf : f ∈ A 1) (e : ℕ → R →+ K)
    (he : ∀ (n k : ℕ) (x : R), x ∈ A n → e (n + k) (f ^ k * x) = e n x)
    (z : HomogeneousLocalization.Away A f)
    (n : ℕ) (x : R) (hx : x ∈ A n)
    (hz : HomogeneousLocalization.val z =
      Localization.mk x (⟨f ^ n, by exact ⟨n, rfl⟩⟩ : Submonoid.powers f)) :
    ringFractionValue A hf e z = e n x := by
  let h := HomogeneousLocalization.Away.mk_surjective A hf z
  have hh : HomogeneousLocalization.val
      (HomogeneousLocalization.Away.mk A hf h.choose h.choose_spec.choose
        h.choose_spec.choose_spec.choose) = HomogeneousLocalization.val z :=
    congrArg HomogeneousLocalization.val h.choose_spec.choose_spec.choose_spec
  rw [HomogeneousLocalization.Away.val_mk] at hh
  exact ringFraction_values_eq A e he _ _ _ _
    (by simpa using h.choose_spec.choose_spec.choose) hx (hh.trans hz)

private noncomputable def homogeneousLocalizationLift
    (hf : f ∈ A 1) (e : ℕ → R →+ K)
    (he : ∀ (n k : ℕ) (x : R), x ∈ A n → e (n + k) (f ^ k * x) = e n x)
    (h1 : e 0 1 = 1)
    (hmul : ∀ (n m : ℕ) (x y : R), x ∈ A n → y ∈ A m →
      e (n + m) (x * y) = e n x * e m y) :
    HomogeneousLocalization.Away A f →+* K where
  toFun := ringFractionValue A hf e
  map_zero' := by
    rw [ringFractionValue_eq A hf e he 0 0 0 (zero_mem _) (by simp [Localization.mk_zero])]
    exact map_zero _
  map_one' := by
    rw [ringFractionValue_eq A hf e he 1 0 1 (SetLike.one_mem_graded A) (by simp)]
    exact h1
  map_add' z w := by
    obtain ⟨n, x, hx, rfl⟩ := HomogeneousLocalization.Away.mk_surjective A hf z
    obtain ⟨m, y, hy, rfl⟩ := HomogeneousLocalization.Away.mk_surjective A hf w
    have hx' : x ∈ A n := by simpa using hx
    have hy' : y ∈ A m := by simpa using hy
    have hnx : f ^ m * x ∈ A (n + m) := by
      have hp : f ^ m ∈ A m := by simpa using SetLike.pow_mem_graded m hf
      simpa [Nat.add_comm] using SetLike.mul_mem_graded hp hx'
    have hmy : f ^ n * y ∈ A (n + m) := by
      have hp : f ^ n ∈ A n := by simpa using SetLike.pow_mem_graded n hf
      exact SetLike.mul_mem_graded hp hy'
    have hv : HomogeneousLocalization.val
        (HomogeneousLocalization.Away.mk A hf n x hx +
          HomogeneousLocalization.Away.mk A hf m y hy) =
        Localization.mk (f ^ m * x + f ^ n * y)
          (⟨f ^ (n + m), by exact ⟨n + m, rfl⟩⟩ : Submonoid.powers f) := by
      rw [HomogeneousLocalization.val_add, HomogeneousLocalization.Away.val_mk,
        HomogeneousLocalization.Away.val_mk, Localization.add_mk]
      congr 1
      · exact add_comm _ _
      · exact Subtype.ext (pow_add f n m).symm
    rw [ringFractionValue_eq A hf e he _ (n + m) _ (add_mem hnx hmy) hv,
      ringFractionValue_eq A hf e he _ n x hx' (HomogeneousLocalization.Away.val_mk ..),
      ringFractionValue_eq A hf e he _ m y hy' (HomogeneousLocalization.Away.val_mk ..),
      map_add, he n m x hx']
    congr 1
    simpa [Nat.add_comm] using he m n y hy'
  map_mul' z w := by
    obtain ⟨n, x, hx, rfl⟩ := HomogeneousLocalization.Away.mk_surjective A hf z
    obtain ⟨m, y, hy, rfl⟩ := HomogeneousLocalization.Away.mk_surjective A hf w
    have hx' : x ∈ A n := by simpa using hx
    have hy' : y ∈ A m := by simpa using hy
    have hv : HomogeneousLocalization.val
        (HomogeneousLocalization.Away.mk A hf n x hx *
          HomogeneousLocalization.Away.mk A hf m y hy) =
        Localization.mk (x * y)
          (⟨f ^ (n + m), by exact ⟨n + m, rfl⟩⟩ : Submonoid.powers f) := by
      rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.Away.val_mk,
        HomogeneousLocalization.Away.val_mk, Localization.mk_mul]
      congr 1
      exact Subtype.ext (pow_add f n m).symm
    rw [ringFractionValue_eq A hf e he _ (n + m) _ (SetLike.mul_mem_graded hx' hy') hv,
      ringFractionValue_eq A hf e he _ n x hx' (HomogeneousLocalization.Away.val_mk ..),
      ringFractionValue_eq A hf e he _ m y hy' (HomogeneousLocalization.Away.val_mk ..)]
    exact hmul n m x y hx' hy'

end RingFractionConstruction

section AcceptedStatementInstances

-- An imported instance gives a second route to terminal objects; disabling it keeps the
-- terminal object in which the statements below are phrased.
attribute [-instance] CategoryTheory.GrothendieckTopology.IsLocalSite.toHasLimitsOfShape

variable (X : Scheme.{u})
  (L F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

/-- Invertibility in the sense of Tag 01CS supplies the hypothesis under which the integer
tensor powers are defined. The bridging instance exists, but instance search does not find it
through the two spellings of the structure sheaf in play here, so it is applied by hand. -/
local instance tensorRightEquiv :
    ((Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj L).IsEquivalence :=
  TensorPower.isEquivalence_tensorRightFunctor (sectionSiteRing X) (sectionSiteSheaf X) L

/-- The graded commutative ring structure on the global sections of the tensor powers of `L`. -/
local instance : DirectSum.GCommRing
    (fun n : ℕ => (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      (n : ℤ)).val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :=
  sectionRingGradedRing (sectionSiteRing X) (sectionSiteSheaf X) L

/-- The twisted global sections of `F` form a module over the section ring of `L`. -/
local instance : Module
    (sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L)
    (sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L F) :=
  sectionModuleModule (sectionSiteRing X) (sectionSiteSheaf X) L F

/-- The section ring of `L` is graded by degree. -/
local instance : GradedRing
    (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L) :=
  sectionRingGradingGradedRing (sectionSiteRing X) (sectionSiteSheaf X) L

/-- The twisted global sections of `F` decompose by degree. -/
local instance : DirectSum.Decomposition
    (sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L F) :=
  sectionModuleDecomposition (sectionSiteRing X) (sectionSiteSheaf X) L F

/-- The action of the section ring of `L` on the twisted sections of `F` respects degrees. -/
local instance : SetLike.GradedSMul
    (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
    (sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L F) :=
  sectionModuleGradedSMul (sectionSiteRing X) (sectionSiteSheaf X) L F

/-- The global section, viewed as a homogeneous element of degree one. -/
public noncomputable def homogeneousSection (s : L.sections) :
    sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L :=
  DirectSum.of _ 1
    ((TensorPower.tensorPowerOneIso (sectionSiteRing X) (sectionSiteSheaf X) L).inv.val.app
      (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))
      (s.eval (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))))

/-- The embedded section lies in the degree-one component. -/
public theorem homogeneousSection_mem (s : L.sections) :
    homogeneousSection X L s ∈
      sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L 1 :=
  ⟨_, rfl⟩

/-- The degree-`n` section obtained by multiplying `s` with itself `n` times. -/
public noncomputable def sectionPower (s : L.sections) (n : ℕ) :
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      (n : ℤ)).val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))) :=
  (homogeneousSection X L s ^ n) n

/-- The `k`-th power of the degree-one element attached to `s` lies in degree `k`. -/
private theorem homogeneousSection_pow_mem (s : L.sections) (k : ℕ) :
    homogeneousSection X L s ^ k ∈
      sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L k := by
  simpa using SetLike.pow_mem_graded k (homogeneousSection_mem X L s)

/-- A power of the degree-one homogeneous element attached to `s` is the homogeneous element of
the matching degree carried by the power section. -/
public theorem homogeneousSection_pow_eq_of_sectionPower (s : L.sections) (e : ℕ) :
    homogeneousSection X L s ^ e = DirectSum.of _ e (sectionPower X L s e) := by
  obtain ⟨q, hq⟩ := homogeneousSection_pow_mem X L s e
  unfold sectionPower
  rw [← hq, DirectSum.of_eq_same]

/-- The product of two homogeneous elements of the section ring is the graded multiplication of
their components. -/
public theorem sectionRing_of_mul_of (n m : ℕ)
    (a : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      (n : ℤ)).val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (b : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      (m : ℤ)).val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
    (DirectSum.of _ n a : sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L) *
      DirectSum.of _ m b = DirectSum.of _ (n + m)
        (sectionRingMul (sectionSiteRing X) (sectionSiteSheaf X) L n m a b) := by
  rw [DirectSum.of_mul_of]
  exact congrArg (DirectSum.of _ (n + m))
    ((chosenRingStructure (sectionSiteRing X) (sectionSiteSheaf X) L).mul_eq n m a b)

private theorem sectionPower_add (s : L.sections) (n m : ℕ) :
    sectionRingMul (sectionSiteRing X) (sectionSiteSheaf X) L n m
      (sectionPower X L s n) (sectionPower X L s m) = sectionPower X L s (n + m) := by
  apply DirectSum.of_injective (β := fun k : ℕ =>
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (k : ℤ)).val.obj
      (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) (n + m)
  rw [← sectionRing_of_mul_of, ← homogeneousSection_pow_eq_of_sectionPower,
    ← homogeneousSection_pow_eq_of_sectionPower, ← homogeneousSection_pow_eq_of_sectionPower,
    pow_add]

private theorem tensorPowerReindex_apply_heq (U : Opens X.toRingedSpace)
    {j k : ℤ} (h : j = k)
    (a : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L j).val.obj (op U)) :
    HEq (((TensorPower.tensorPowerReindex (sectionSiteRing X) (sectionSiteSheaf X) L h).hom.val.app
      (op U)).hom a) a := by
  subst k
  rfl

private theorem sectionRing_of_zero_one_mul_of (n : ℕ)
    (a : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      (n : ℤ)).val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
    (DirectSum.of _ 0
        (1 : (sectionSiteRing X).obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
        sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L) *
      DirectSum.of _ n a = DirectSum.of _ n a := by
  rw [sectionRing_of_mul_of X L 0 n
    (1 : (sectionSiteRing X).obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) a]
  have he := TensorPower.coherentMulIso_zero_left
    (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)
  have h := tensorSections_leftUnitorAt (sectionSiteRing X) (sectionSiteSheaf X)
    (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)) a
  rw [← he] at h
  apply DirectSum.of_eq_of_gradedMonoid_eq
  apply Sigma.ext (Nat.zero_add n)
  exact (tensorPowerReindex_apply_heq X L _ (Int.natCast_add 0 n).symm _).trans
    ((tensorPowerReindex_apply_heq X L _ (Int.zero_add (n : ℤ)) _).symm.trans (heq_of_eq h))

private theorem sectionRing_of_zero_one :
    (DirectSum.of _ 0
        (1 : (sectionSiteRing X).obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
        sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L) = 1 := by
  have h : ∀ z : sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L,
      DirectSum.of _ 0
          (1 : (sectionSiteRing X).obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) *
        z = z := by
    intro z
    induction z using DirectSum.induction_on with
    | zero => exact mul_zero _
    | of n a => exact sectionRing_of_zero_one_mul_of X L n a
    | add a b ha hb => rw [mul_add, ha, hb]
  simpa using h 1

private theorem sectionPower_zero (s : L.sections) : sectionPower X L s 0 =
    (1 : (sectionSiteRing X).obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) := by
  have h := (homogeneousSection_pow_eq_of_sectionPower X L s 0).symm
  rw [pow_zero, ← sectionRing_of_zero_one X L] at h
  exact DirectSum.of_injective 0 h

/-- The degree-one section `Stacks.SheafOfModules.sectionPower X L s 1` is the global section
`s` itself, read through the identification `L^{⊗ 1} ≅ L` of [Stacks, Tag 01CU]. -/
public theorem sectionPower_one (s : L.sections) : sectionPower X L s 1 =
    (TensorPower.tensorPowerOneIso (sectionSiteRing X) (sectionSiteSheaf X) L).inv.val.app
      (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))
      (s.eval (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) := by
  simp only [sectionPower, pow_one, homogeneousSection, DirectSum.of_eq_same]

/-- Tensor a section on an open with a section of the `n`-th tensor power there. -/
public noncomputable def tensorSectionAtOpen (U : Opens X.toRingedSpace)
    (n : ℕ) (t : F.val.obj (op U))
    (q : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      (n : ℤ)).val.obj (op U)) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L
        (n : ℤ))))).val.obj (op U) :=
  ((TensorSheafification.toSheafify (sectionSiteRing X) (sectionSiteSheaf X)
    ((PresheafOfModules.tensorObj (O := (sectionSiteRing X)) (F.val) ((TensorPower.tensorPower
      (sectionSiteRing X) (sectionSiteSheaf X) L
        (n : ℤ)).val)))).app (op U)).hom
      (t ⊗ₜ[(sectionSiteRing X).obj (op U)] q)

private noncomputable def powerMulAt (U : Opens X.toRingedSpace) (n m : ℕ)
    (a : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      (n : ℤ)).val.obj (op U))
    (b : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      (m : ℤ)).val.obj (op U)) :
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      ((n + m : ℕ) : ℤ)).val.obj (op U) :=
  ((TensorPower.coherentMulIso (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ) (m : ℤ) ≪≫
    TensorPower.tensorPowerReindex (sectionSiteRing X) (sectionSiteSheaf X) L
      (Int.natCast_add n m).symm).hom.val.app (op U)).hom
    (tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X) (op U) _ _ a b)

private theorem powerMulAt_restrict (U : Opens X.toRingedSpace) (n m : ℕ)
    (a : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      (n : ℤ)).val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (b : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      (m : ℤ)).val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      ((n + m : ℕ) : ℤ)).val.map (terminal.from U).op
        (sectionRingMul (sectionSiteRing X) (sectionSiteSheaf X) L n m a b) =
    powerMulAt X L U n m
      ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.map
        (terminal.from U).op a)
      ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (m : ℤ)).val.map
        (terminal.from U).op b) := by
  let e := TensorPower.coherentMulIso (sectionSiteRing X) (sectionSiteSheaf X) L
      (n : ℤ) (m : ℤ) ≪≫
    TensorPower.tensorPowerReindex (sectionSiteRing X) (sectionSiteSheaf X) L
      (Int.natCast_add n m).symm
  have h := congrArg (fun f => f.hom
    (tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X)
      (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))) _ _ a b))
      (e.hom.val.naturality (terminal.from U).op)
  change ((e.hom.val.app (op U)).hom
    ((((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj (_)).obj (_))).val.map
      (terminal.from U).op).hom _)) = _ at h
  rw [tensorSections_naturalAt] at h
  exact h.symm

private theorem powerMulAt_sectionPower (s : L.sections) (U : Opens X.toRingedSpace) (n m : ℕ) :
    powerMulAt X L U n m
      ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.map
        (terminal.from U).op (sectionPower X L s n))
      ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (m : ℤ)).val.map
        (terminal.from U).op (sectionPower X L s m)) =
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      ((n + m : ℕ) : ℤ)).val.map (terminal.from U).op (sectionPower X L s (n + m)) := by
  rw [← powerMulAt_restrict, sectionPower_add]

private theorem of_tensorPowerReindex {j k : ℤ} (h : j = k)
    (a : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L j)))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
    (DirectSum.of _ k
      (((Invertible.tensorProductIso (sectionSiteRing X) (sectionSiteSheaf X) (Iso.refl F)
        (TensorPower.tensorPowerReindex (sectionSiteRing X) (sectionSiteSheaf X)
          L h)).hom.val.app _).hom a) :
        sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L F) =
      DirectSum.of _ j a := by
  subst k
  have hid : (Invertible.tensorProductIso (sectionSiteRing X) (sectionSiteSheaf X) (Iso.refl F)
      (TensorPower.tensorPowerReindex (sectionSiteRing X) (sectionSiteSheaf X) L
        (rfl : j = j))).hom = 𝟙 _ := by
    have h0 : ((Iso.refl F).prod (Iso.refl (TensorPower.tensorPower (sectionSiteRing X)
          (sectionSiteSheaf X) L j))).hom =
        𝟙 (F, TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L j) := rfl
    exact (congrArg (Invertible.tensorProductBifunctor (sectionSiteRing X)
        (sectionSiteSheaf X)).map h0).trans
      ((Invertible.tensorProductBifunctor (sectionSiteRing X) (sectionSiteSheaf X)).map_id _)
  rw [hid]
  rfl

private noncomputable def moduleMulAt (U : Opens X.toRingedSpace) (n m : ℕ)
    (a : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      (n : ℤ)).val.obj (op U))
    (b : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L
        (m : ℤ))))).val.obj (op U)) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L
        ((n + m : ℕ) : ℤ))))).val.obj (op U) :=
  ((Invertible.tensorProductBraiding (sectionSiteRing X) (sectionSiteSheaf X) _ _ ≪≫
    Invertible.tensorProductAssociator (sectionSiteRing X) (sectionSiteSheaf X) F _ _ ≪≫
    Invertible.tensorProductIso (sectionSiteRing X) (sectionSiteSheaf X) (Iso.refl F)
      (TensorPower.coherentMulIso (sectionSiteRing X) (sectionSiteSheaf X) L (m : ℤ) (n : ℤ)) ≪≫
    Invertible.tensorProductIso (sectionSiteRing X) (sectionSiteSheaf X) (Iso.refl F)
      (TensorPower.tensorPowerReindex (sectionSiteRing X) (sectionSiteSheaf X) L
        (Int.add_comm (m : ℤ) (n : ℤ))) ≪≫
    Invertible.tensorProductIso (sectionSiteRing X) (sectionSiteSheaf X) (Iso.refl F)
      (TensorPower.tensorPowerReindex (sectionSiteRing X) (sectionSiteSheaf X) L
        (Int.natCast_add n m).symm)).hom.val.app (op U)).hom
    (tensorSectionsAt (sectionSiteRing X) (sectionSiteSheaf X) (op U) _ _ a b)

private theorem sectionModule_of_smul (n m : ℕ)
    (a : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.obj
      (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (b : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L (m : ℤ))))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
    (DirectSum.of _ n a : sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L) •
      (DirectSum.of _ (m : ℤ) b : sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L F) =
    DirectSum.of _ ((n + m : ℕ) : ℤ)
      (moduleMulAt X L F (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)) n m a b) := by
  rw [(chosenModuleStructure (sectionSiteRing X) (sectionSiteSheaf X) L F).smul_eq]
  show _ = (DirectSum.of _ _
    (((Invertible.tensorProductIso (sectionSiteRing X) (sectionSiteSheaf X) (Iso.refl F)
      (TensorPower.tensorPowerReindex (sectionSiteRing X) (sectionSiteSheaf X) L
        (Int.natCast_add n m).symm)).hom.val.app _).hom
      (sectionModuleAction (sectionSiteRing X) (sectionSiteSheaf X) L F n (m : ℤ) a b)) :
      sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L F)
  rw [of_tensorPowerReindex]

private theorem moduleMulAt_restrict (U : Opens X.toRingedSpace) (n m : ℕ)
    (a : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.obj
      (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (b : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L (m : ℤ))))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L
        ((n + m : ℕ) : ℤ))))).val.map
      (terminal.from U).op
      (moduleMulAt X L F (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)) n m a b) =
    moduleMulAt X L F U n m
      ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.map
        (terminal.from U).op a)
      (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (m : ℤ))))).val.map
        (terminal.from U).op b) := by
  unfold moduleMulAt
  rw [← PresheafOfModules.naturality_apply]
  exact congrArg _ (tensorSections_naturalAt (sectionSiteRing X) (sectionSiteSheaf X) _ _ _ a b)

private theorem moduleMulAt_tensor (U : Opens X.toRingedSpace) (n m : ℕ)
    (a : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      (n : ℤ)).val.obj (op U))
    (b : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      (m : ℤ)).val.obj (op U))
    (t : F.val.obj (op U)) :
    moduleMulAt X L F U n m a (tensorSectionAtOpen X L F U m t b) =
    tensorSectionAtOpen X L F U (n + m) t (powerMulAt X L U n m a b) :=
  tensorPowerAction_pure (sectionSiteRing X) (sectionSiteSheaf X) F L n m (op U) a b t

/-- Degree-zero fractions of twisted global sections with denominator a power of `s`. -/
public noncomputable def sectionAtNonvanishingOpen (s : L.sections) :=
  GradedModuleDegreeZeroLocalization
    (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
    (sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L F)
    (homogeneousSection X L s)

/-- The chosen section is a basis of the invertible module after restricting to its
nonvanishing open.  This is the local inverse used to contract tensor powers in the
fraction map below. -/
private noncomputable def sectionUnitIsoOver (s : L.sections) :
    (SheafOfModules.unit (TensorSheafification.structureSheaf
      (sectionSiteRing X) (sectionSiteSheaf X))).over
        (nonvanishingOpen L s) ≅
      L.over (nonvanishingOpen L s) := by
  exact @asIso _ _ _ _ _
    (isIso_over_nonvanishingOpen L s)

private abbrev nonvanishingOpenRing (s : L.sections) :=
  (X.toRingedSpace.sheaf.over (nonvanishingOpen L s)).obj

private abbrev nonvanishingOpenRingSheaf (s : L.sections) :=
  (Presheaf.isSheaf_iff_isSheaf_comp
    ((Opens.grothendieckTopology X.toRingedSpace.carrier).over
      (nonvanishingOpen L s))
    (nonvanishingOpenRing X L s) (forget₂ CommRingCat RingCat)).mp
    (X.toRingedSpace.sheaf.over (nonvanishingOpen L s)).property

private abbrev nonvanishingOpenModuleSheaf (s : L.sections) :=
  TensorSheafification.structureSheaf (nonvanishingOpenRing X L s)
    (nonvanishingOpenRingSheaf X L s)

private noncomputable def restrictedTensorPower (s : L.sections) :
    ℕ → SheafOfModules (nonvanishingOpenModuleSheaf X L s)
  | 0 => SheafOfModules.unit (nonvanishingOpenModuleSheaf X L s)
  | n + 1 => (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(nonvanishingOpenRing X L s),
    Presheaf.isSheaf_of_isSheaf_comp _ ((nonvanishingOpenRing X L s)) (forget₂ CommRingCat RingCat)
    ((nonvanishingOpenRingSheaf X L s))⟩).obj ((restrictedTensorPower s n))).obj ((L.over
    (nonvanishingOpen L s))))

private noncomputable def restrictedTensorPowerBasisIso (s : L.sections) :
    (n : ℕ) → SheafOfModules.unit (nonvanishingOpenModuleSheaf X L s) ≅
      restrictedTensorPower X L s n
  | 0 => Iso.refl _
  | n + 1 =>
      (Invertible.tensorProductLeftUnitor (nonvanishingOpenRing X L s)
        (nonvanishingOpenRingSheaf X L s)
        (SheafOfModules.unit (nonvanishingOpenModuleSheaf X L s))).symm ≪≫
      Invertible.tensorProductIso (nonvanishingOpenRing X L s)
        (nonvanishingOpenRingSheaf X L s)
        (restrictedTensorPowerBasisIso s n) (sectionUnitIsoOver X L s)

private noncomputable def tensorPowerRestrictionIso (s : L.sections) :
    (n : ℕ) → (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      (n : ℤ)).over (nonvanishingOpen L s) ≅
      restrictedTensorPower X L s n
  | 0 => Iso.refl _
  | n + 1 =>
      let U := nonvanishingOpen L s
      let overF := SheafOfModules.overFunctor
        (TensorSheafification.structureSheaf (sectionSiteRing X) (sectionSiteSheaf X)) U
      overF.mapIso (TensorPower.tensorPowerSuccIso
        (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).symm ≪≫
      tensorRestrictionIsoOnScheme X
        (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)) L U ≪≫
      Invertible.tensorProductIso (nonvanishingOpenRing X L s)
        (nonvanishingOpenRingSheaf X L s)
        (tensorPowerRestrictionIso s n) (Iso.refl _)

private noncomputable def tensorPowerProductOver (s : L.sections) (n m : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(nonvanishingOpenRing X L s),
      Presheaf.isSheaf_of_isSheaf_comp _ ((nonvanishingOpenRing X L s)) (forget₂ CommRingCat
      RingCat) ((nonvanishingOpenRingSheaf X L s))⟩).obj (((TensorPower.tensorPower (sectionSiteRing
      X) (sectionSiteSheaf X) L n).over
        (nonvanishingOpen L s)))).obj (((TensorPower.tensorPower (sectionSiteRing X)
          (sectionSiteSheaf X) L m).over
        (nonvanishingOpen L s)))) ≅
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n + m)).over
      (nonvanishingOpen L s) := by
  let U := nonvanishingOpen L s
  let overF := SheafOfModules.overFunctor
    (TensorSheafification.structureSheaf (sectionSiteRing X) (sectionSiteSheaf X)) U
  exact (tensorRestrictionIsoOnScheme X
      (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L n)
      (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L m) U).symm ≪≫
    overF.mapIso (TensorPower.coherentMulIso
      (sectionSiteRing X) (sectionSiteSheaf X) L n m)

private noncomputable def tensorPowerBasisIsoNat (s : L.sections) :
    (n : ℕ) → SheafOfModules.unit (nonvanishingOpenModuleSheaf X L s) ≅
      (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).over
        (nonvanishingOpen L s)
  | 0 => Iso.refl _
  | n + 1 =>
      let U := nonvanishingOpen L s
      let overF := SheafOfModules.overFunctor
        (TensorSheafification.structureSheaf (sectionSiteRing X) (sectionSiteSheaf X)) U
      let qOne := sectionUnitIsoOver X L s ≪≫
        (overF.mapIso (TensorPower.tensorPowerOneIso
          (sectionSiteRing X) (sectionSiteSheaf X) L)).symm
      (Invertible.tensorProductLeftUnitor (nonvanishingOpenRing X L s)
        (nonvanishingOpenRingSheaf X L s)
        (SheafOfModules.unit (nonvanishingOpenModuleSheaf X L s))).symm ≪≫
      Invertible.tensorProductIso (nonvanishingOpenRing X L s)
        (nonvanishingOpenRingSheaf X L s)
        (tensorPowerBasisIsoNat s n) qOne ≪≫
      tensorPowerProductOver X L s (n : ℤ) 1

private noncomputable def powerBasisAt (s : L.sections) (n : ℕ) :
    (sectionSiteRing X).obj (op (nonvanishingOpen L s)) ≃+
      (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.obj
        (op (nonvanishingOpen L s)) :=
  sheafIsoAddEquiv (nonvanishingOpenRing X L s) (nonvanishingOpenRingSheaf X L s) _ _
    (tensorPowerBasisIsoNat X L s n)
    (op (Over.mk (𝟙 (nonvanishingOpen L s))))

private theorem sectionUnitIsoOver_one (s : L.sections) :
    ((sectionUnitIsoOver X L s).hom.val.app
      (op (Over.mk (𝟙 (nonvanishingOpen L s))))).hom
      (1 : (sectionSiteRing X).obj (op (nonvanishingOpen L s))) =
    s.eval (op (nonvanishingOpen L s)) :=
  congrArg (fun t : L.sections => t.eval (op (nonvanishingOpen L s)))
    (L.unitHomEquiv.apply_symm_apply s)

private theorem powerBasisAt_succ_one (s : L.sections) (n : ℕ) :
    powerBasisAt X L s (n + 1) 1 =
    powerMulAt X L (nonvanishingOpen L s) n 1
      (powerBasisAt X L s n 1)
      ((TensorPower.tensorPowerOneIso (sectionSiteRing X) (sectionSiteSheaf X) L).inv.val.app
        (op (nonvanishingOpen L s))
          (s.eval (op (nonvanishingOpen L s)))) := by
  let U := nonvanishingOpen L s
  let O := nonvanishingOpenRing X L s
  let hO := nonvanishingOpenRingSheaf X L s
  let overF := SheafOfModules.overFunctor
    (TensorSheafification.structureSheaf (sectionSiteRing X) (sectionSiteSheaf X)) U
  let qOne := sectionUnitIsoOver X L s ≪≫
    (overF.mapIso (TensorPower.tensorPowerOneIso (sectionSiteRing X) (sectionSiteSheaf X) L)).symm
  let V := op (Over.mk (𝟙 U))
  let E := Invertible.tensorProductIso O hO (tensorPowerBasisIsoNat X L s n) qOne
  let R := tensorRestrictionIsoOnScheme X
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L 1) U
  have h1 := tensorSections_leftUnitorInvAt O hO (SheafOfModules.unit _) V (1 : O.obj V)
  have h2 := tensorSections_tensorProductIsoAt O hO V (SheafOfModules.unit _) _
    (SheafOfModules.unit _) _ (tensorPowerBasisIsoNat X L s n) qOne
    (1 : O.obj V) (1 : O.obj V)
  have h3 := tensorRestrictionIso_inv_tensorAt X _ _ U
    (powerBasisAt X L s n 1) ((qOne.hom.val.app V).hom (1 : O.obj V))
  have h4 := (congrArg (R.inv.val.app V).hom
    ((congrArg (E.hom.val.app V).hom h1).trans h2)).trans h3
  have h5 := congrArg
    ((TensorPower.coherentMulIso (sectionSiteRing X) (sectionSiteSheaf X) L
      (n : ℤ) 1).hom.val.app (op U)).hom h4
  have hq := congrArg
    ((TensorPower.tensorPowerOneIso (sectionSiteRing X) (sectionSiteSheaf X) L).inv.val.app
      (op U)).hom
    (sectionUnitIsoOver_one X L s)
  exact h5.trans (congrArg (fun q => powerMulAt X L U n 1 (powerBasisAt X L s n 1) q) hq)

private theorem powerBasisAt_one (s : L.sections) (n : ℕ) :
    powerBasisAt X L s n 1 =
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.map
      (terminal.from (nonvanishingOpen L s)).op
      (sectionPower X L s n) := by
  let U := nonvanishingOpen L s
  induction n with
  | zero =>
      rw [sectionPower_zero]
      show (1 : (sectionSiteRing X).obj (op U)) =
        ((sectionSiteRing X).map (terminal.from U).op).hom 1
      exact (map_one _).symm
  | succ n ih =>
      rw [powerBasisAt_succ_one, ih]
      have h : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L 1).val.map
          (terminal.from U).op (sectionPower X L s 1) =
          (TensorPower.tensorPowerOneIso (sectionSiteRing X) (sectionSiteSheaf X) L).inv.val.app
            (op U) (s.eval (op U)) := by
        rw [sectionPower_one, ← PresheafOfModules.naturality_apply]
        exact congrArg
          (((TensorPower.tensorPowerOneIso (sectionSiteRing X) (sectionSiteSheaf X) L).inv.val.app
            (op U)).hom)
          (PresheafOfModules.sections_property s (terminal.from U).op)
      rw [← h]
      exact powerMulAt_sectionPower X L s U n 1

private noncomputable def tensorBasisAtImpl (s : L.sections) (n : ℕ) :
    F.val.obj (op (nonvanishingOpen L s)) ≃+
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (n : ℤ))))).val.obj
        (op (nonvanishingOpen L s)) := by
  let O := nonvanishingOpenRing X L s
  let hO := nonvanishingOpenRingSheaf X L s
  let U := nonvanishingOpen L s
  exact sheafIsoAddEquiv O hO _ _
    ((Invertible.tensorProductRightUnitor O hO (F.over U)).symm ≪≫
      Invertible.tensorProductIso O hO (Iso.refl _) (tensorPowerBasisIsoNat X L s n) ≪≫
      (tensorRestrictionIsoOnScheme X F
        (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)) U).symm)
    (op (Over.mk (𝟙 U)))

private theorem tensorBasisAtImpl_apply (s : L.sections) (n : ℕ)
    (t : F.val.obj (op (nonvanishingOpen L s))) :
    tensorBasisAtImpl X L F s n t = tensorSectionAtOpen X L F
      (nonvanishingOpen L s) n t (powerBasisAt X L s n 1) := by
  let U := nonvanishingOpen L s
  let O := nonvanishingOpenRing X L s
  let hO := nonvanishingOpenRingSheaf X L s
  let V := op (Over.mk (𝟙 U))
  let E := Invertible.tensorProductIso O hO (Iso.refl (F.over U)) (tensorPowerBasisIsoNat X L s n)
  let R := tensorRestrictionIsoOnScheme X F
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)) U
  have h1 := tensorSections_rightUnitorInvAt O hO (F.over U) V t
  have h2 := tensorSections_tensorProductIsoAt O hO V (F.over U) _
    (SheafOfModules.unit _) _ (Iso.refl _) (tensorPowerBasisIsoNat X L s n)
    t (1 : O.obj V)
  have h3 := tensorRestrictionIso_inv_tensorAt X F _ U t (powerBasisAt X L s n 1)
  simp only [tensorBasisAtImpl, sheafIsoAddEquiv]
  exact (congrArg (R.inv.val.app V).hom
    ((congrArg (E.hom.val.app V).hom h1).trans h2)).trans h3

private theorem tensorBasisAtImpl_eq_tensor (s : L.sections) (n : ℕ)
    (t : F.val.obj (op (nonvanishingOpen L s))) :
    tensorBasisAtImpl X L F s n t = tensorSectionAtOpen X L F
      (nonvanishingOpen L s) n t
      ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.map
        (terminal.from (nonvanishingOpen L s)).op
        (sectionPower X L s n)) := by
  rw [tensorBasisAtImpl_apply, powerBasisAt_one]

/-- Over `X_s`, tensoring with the restriction of `sⁿ` is an additive isomorphism from `F` onto
`F ⊗ L^{⊗ n}`. -/
public theorem exists_tensorBasisAt (s : L.sections) (n : ℕ) :
    ∃ e : F.val.obj (op (nonvanishingOpen L s)) ≃+
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (n : ℤ))))).val.obj
        (op (nonvanishingOpen L s)),
      ∀ t, e t = tensorSectionAtOpen X L F
        (nonvanishingOpen L s) n t
        ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.map
          (terminal.from (nonvanishingOpen L s)).op
          (sectionPower X L s n)) :=
  ⟨tensorBasisAtImpl X L F s n, tensorBasisAtImpl_eq_tensor X L F s n⟩

/-- The trivialization of `F ⊗ L^{⊗ n}` over `X_s` by tensoring with `sⁿ`. -/
public noncomputable def tensorBasisAt (s : L.sections) (n : ℕ) :
    F.val.obj (op (nonvanishingOpen L s)) ≃+
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (n : ℤ))))).val.obj
        (op (nonvanishingOpen L s)) :=
  Classical.choose (exists_tensorBasisAt X L F s n)

private theorem tensorBasisAt_eq_tensor (s : L.sections) (n : ℕ)
    (t : F.val.obj (op (nonvanishingOpen L s))) :
    tensorBasisAt X L F s n t = tensorSectionAtOpen X L F
      (nonvanishingOpen L s) n t
      ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.map
        (terminal.from (nonvanishingOpen L s)).op
        (sectionPower X L s n)) :=
  Classical.choose_spec (exists_tensorBasisAt X L F s n) t

private theorem tensorBasisAt_apply (s : L.sections) (n : ℕ)
    (t : F.val.obj (op (nonvanishingOpen L s))) :
    tensorBasisAt X L F s n t = tensorSectionAtOpen X L F
      (nonvanishingOpen L s) n t (powerBasisAt X L s n 1) := by
  rw [tensorBasisAt_eq_tensor, powerBasisAt_one]

private theorem powerBasisAt_smul (s : L.sections) (n : ℕ)
    (r : (sectionSiteRing X).obj (op (nonvanishingOpen L s))) :
    powerBasisAt X L s n r =
    ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.obj
      (op (nonvanishingOpen L s))).isModule.smul r
      (powerBasisAt X L s n 1) := by
  let U := nonvanishingOpen L s
  have h := ((tensorPowerBasisIsoNat X L s n).hom.val.app
    (op (Over.mk (𝟙 U)))).hom.map_smul r (1 : (sectionSiteRing X).obj (op U))
  change powerBasisAt X L s n (r * 1) = _ at h
  rwa [mul_one] at h

private theorem powerMulAt_basis (s : L.sections) (n m : ℕ)
    (r q : (sectionSiteRing X).obj (op (nonvanishingOpen L s))) :
    powerMulAt X L (nonvanishingOpen L s) n m
      (powerBasisAt X L s n r) (powerBasisAt X L s m q) =
      powerBasisAt X L s (n + m) (r * q) := by
  let U := nonvanishingOpen L s
  let P := fun k : ℕ => TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (k : ℤ)
  let _mn : Module ((sectionSiteRing X).obj (op U)) ((P n).val.obj (op U)) :=
    ((P n).val.obj (op U)).isModule
  let _mm : Module ((sectionSiteRing X).obj (op U)) ((P m).val.obj (op U)) :=
    ((P m).val.obj (op U)).isModule
  let _mnm : Module ((sectionSiteRing X).obj (op U)) ((P (n + m)).val.obj (op U)) :=
    ((P (n + m)).val.obj (op U)).isModule
  let _mt : Module ((sectionSiteRing X).obj (op U))
      (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj ((P n))).obj ((P m)))).val.obj (op U)) :=
    (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj ((P n))).obj ((P m)))).val.obj
      (op U)).isModule
  have h : powerMulAt X L U n m (powerBasisAt X L s n 1) (powerBasisAt X L s m 1) =
      powerBasisAt X L s (n + m) 1 := by
    rw [powerBasisAt_one, powerBasisAt_one, powerBasisAt_one]
    exact powerMulAt_sectionPower X L s U n m
  rw [powerBasisAt_smul X L s n r, powerBasisAt_smul X L s m q,
    powerBasisAt_smul X L s (n + m) (r * q)]
  unfold powerMulAt tensorSectionsAt
  have ht := TensorProduct.smul_tmul_smul (R := (sectionSiteRing X).obj (op U))
    r q (powerBasisAt X L s n 1) (powerBasisAt X L s m 1)
  let η := ((TensorSheafification.toSheafify (sectionSiteRing X) (sectionSiteSheaf X)
    ((PresheafOfModules.tensorObj (O := (sectionSiteRing X)) ((P n).val) ((P m).val)))).app (op
      U)).hom
  let e := ((TensorPower.coherentMulIso (sectionSiteRing X) (sectionSiteSheaf X) L
    (n : ℤ) (m : ℤ) ≪≫
    TensorPower.tensorPowerReindex (sectionSiteRing X) (sectionSiteSheaf X) L
      (Int.natCast_add n m).symm).hom.val.app (op U)).hom
  exact (congrArg (fun x => e (η x)) ht).trans
    ((congrArg e (η.map_smul (r * q) _)).trans
      ((e.map_smul (r * q) _).trans (congrArg (fun t => (r * q) • t) h)))

private theorem moduleMulAt_basis (s : L.sections) (n m : ℕ)
    (r : (sectionSiteRing X).obj (op (nonvanishingOpen L s)))
    (t : F.val.obj (op (nonvanishingOpen L s))) :
    moduleMulAt X L F (nonvanishingOpen L s) n m
      (powerBasisAt X L s n r) (tensorBasisAt X L F s m t) =
    tensorBasisAt X L F s (n + m)
      ((F.val.obj (op (nonvanishingOpen L s))).isModule.smul r t) := by
  let U := nonvanishingOpen L s
  let _mF : Module ((sectionSiteRing X).obj (op U)) (F.val.obj (op U)) :=
    (F.val.obj (op U)).isModule
  let _mP : Module ((sectionSiteRing X).obj (op U))
      ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
        ((n + m : ℕ) : ℤ)).val.obj (op U)) :=
    ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      ((n + m : ℕ) : ℤ)).val.obj (op U)).isModule
  rw [tensorBasisAt_apply, moduleMulAt_tensor, powerMulAt_basis, mul_one, tensorBasisAt_apply,
    powerBasisAt_smul X L s (n + m) r]
  unfold tensorSectionAtOpen
  exact congrArg
    ((TensorSheafification.toSheafify (sectionSiteRing X) (sectionSiteSheaf X)
      ((PresheafOfModules.tensorObj (O := (sectionSiteRing X)) (F.val) ((TensorPower.tensorPower
        (sectionSiteRing X) (sectionSiteSheaf X) L
          ((n + m : ℕ) : ℤ)).val)))).app
        (op U)).hom
    (TensorProduct.smul_tmul (R := (sectionSiteRing X).obj (op U))
      r t (powerBasisAt X L s (n + m) 1)).symm

private noncomputable def ringFractionNumerator (s : L.sections) (n : ℕ) :
    sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L →+
      (sectionSiteRing X).obj (op (nonvanishingOpen L s)) where
  toFun a := (powerBasisAt X L s n).symm
    ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.map
      (terminal.from (nonvanishingOpen L s)).op (a n))
  map_zero' := by
    simp only [DFinsupp.zero_apply, map_zero]
    exact (powerBasisAt X L s n).symm.map_zero
  map_add' a b := by
    simp only [DirectSum.add_apply, map_add]
    exact (powerBasisAt X L s n).symm.map_add _ _

/-- The degree-`n` numerator map: the degree-`n` component of a twisted global section of `F`,
restricted to `X_s` and divided by `sⁿ`. -/
public noncomputable def moduleFractionNumerator (s : L.sections) (n : ℕ) :
    sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L F →+
      F.val.obj (op (nonvanishingOpen L s)) where
  toFun a := (tensorBasisAt X L F s n).symm
    (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L (n : ℤ))))).val.map
      (terminal.from (nonvanishingOpen L s)).op (a (n : ℤ)))
  map_zero' := by
    simp only [DFinsupp.zero_apply, map_zero]
    exact (tensorBasisAt X L F s n).symm.map_zero
  map_add' a b := by
    simp only [DirectSum.add_apply, map_add]
    exact (tensorBasisAt X L F s n).symm.map_add _ _

private theorem ringFractionNumerator_of (s : L.sections) (n : ℕ)
    (a : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.obj
      (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
    powerBasisAt X L s n (ringFractionNumerator X L s n (DirectSum.of _ n a)) =
      (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.map
        (terminal.from (nonvanishingOpen L s)).op a := by
  show (powerBasisAt X L s n) ((powerBasisAt X L s n).symm
    ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.map
      (terminal.from (nonvanishingOpen L s)).op
        ((DirectSum.of _ n a : sectionRing
          (sectionSiteRing X) (sectionSiteSheaf X) L) n))) = _
  simpa only [DirectSum.of_eq_same] using
    (powerBasisAt X L s n).apply_symm_apply
      ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)).val.map
        (terminal.from (nonvanishingOpen L s)).op a)

private theorem ringFractionNumerator_power (s : L.sections) (n : ℕ) :
    ringFractionNumerator X L s n (homogeneousSection X L s ^ n) = 1 := by
  show (powerBasisAt X L s n).symm _ = 1
  exact (congrArg (powerBasisAt X L s n).symm (powerBasisAt_one X L s n).symm).trans
    ((powerBasisAt X L s n).symm_apply_apply 1)

private theorem moduleFractionNumerator_of (s : L.sections) (n : ℕ)
    (m : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L (n : ℤ))))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
    tensorBasisAt X L F s n
      (moduleFractionNumerator X L F s n (DirectSum.of _ (n : ℤ) m)) =
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L (n : ℤ))))).val.map
      (terminal.from (nonvanishingOpen L s)).op m := by
  show (tensorBasisAt X L F s n) ((tensorBasisAt X L F s n).symm
    (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L (n : ℤ))))).val.map
      (terminal.from (nonvanishingOpen L s)).op
        ((DirectSum.of _ (n : ℤ) m : sectionModule
          (sectionSiteRing X) (sectionSiteSheaf X) L F) (n : ℤ)))) = _
  simpa only [DirectSum.of_eq_same] using
    (tensorBasisAt X L F s n).apply_symm_apply
      (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L (n : ℤ))))).val.map
        (terminal.from (nonvanishingOpen L s)).op m)

private theorem ringFractionNumerator_mul (s : L.sections) (n m : ℕ)
    (a b : sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L)
    (ha : a ∈ sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L n)
    (hb : b ∈ sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L m) :
    ringFractionNumerator X L s (n + m) (a * b) =
      ringFractionNumerator X L s n a * ringFractionNumerator X L s m b := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  apply (powerBasisAt X L s (n + m)).injective
  rw [sectionRing_of_mul_of, ringFractionNumerator_of, powerMulAt_restrict,
    ← powerMulAt_basis, ringFractionNumerator_of, ringFractionNumerator_of]

private theorem moduleFractionNumerator_smul (s : L.sections) (n m : ℕ)
    (a : sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L)
    (b : sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L F)
    (ha : a ∈ sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L n)
    (hb : b ∈ sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L F (m : ℤ)) :
    moduleFractionNumerator X L F s (n + m) (a • b) =
      (F.val.obj (op (nonvanishingOpen L s))).isModule.smul
        (ringFractionNumerator X L s n a) (moduleFractionNumerator X L F s m b) :=
  Exists.elim ha fun ringSection ring_eq =>
    Exists.elim hb fun moduleSection module_eq =>
      ring_eq ▸ module_eq ▸
        (tensorBasisAt X L F s (n + m)).injective
          ((congrArg (fun value => tensorBasisAt X L F s (n + m)
              (moduleFractionNumerator X L F s (n + m) value))
            (sectionModule_of_smul X L F n m ringSection moduleSection)).trans
            ((moduleFractionNumerator_of X L F s (n + m)
              (moduleMulAt X L F (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))
                n m ringSection moduleSection)).trans
              ((moduleMulAt_restrict X L F (nonvanishingOpen L s) n m
                ringSection moduleSection).trans
                ((congrArg₂ (moduleMulAt X L F (nonvanishingOpen L s) n m)
                  (ringFractionNumerator_of X L s n ringSection).symm
                  (moduleFractionNumerator_of X L F s m moduleSection).symm).trans
                  (moduleMulAt_basis X L F s n m
                    (ringFractionNumerator X L s n (DirectSum.of _ n ringSection))
                    (moduleFractionNumerator X L F s m
                      (DirectSum.of _ (m : ℤ) moduleSection)))))))

private theorem ringFractionNumerator_mul_power (s : L.sections) (n k : ℕ)
    (a : sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L)
    (ha : a ∈ sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L n) :
    ringFractionNumerator X L s (n + k) (homogeneousSection X L s ^ k * a) =
      ringFractionNumerator X L s n a := by
  rw [Nat.add_comm n k, ringFractionNumerator_mul X L s k n _ _
      (homogeneousSection_pow_mem X L s k) ha,
    ringFractionNumerator_power, one_mul]

/-- Multiplying a twisted section of degree `n` by `sᵏ` does not change its degree-`(n + k)`
numerator. -/
public theorem moduleFractionNumerator_smul_power (s : L.sections) (n k : ℕ)
    (a : sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L F)
    (ha : a ∈ sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L F (n : ℤ)) :
    moduleFractionNumerator X L F s (n + k) (homogeneousSection X L s ^ k • a) =
      moduleFractionNumerator X L F s n a := by
  rw [Nat.add_comm n k, moduleFractionNumerator_smul X L F s k n _ _
      (homogeneousSection_pow_mem X L s k) ha,
    ringFractionNumerator_power]
  exact (F.val.obj _).isModule.one_smul _

private noncomputable def divisionIsoOver (s : L.sections) (n : ℕ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(nonvanishingOpenRing X L s),
      Presheaf.isSheaf_of_isSheaf_comp _ ((nonvanishingOpenRing X L s)) (forget₂ CommRingCat
      RingCat) ((nonvanishingOpenRingSheaf X L s))⟩).obj ((F.over (nonvanishingOpen L s)))).obj
      (((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
        (n : ℤ)).over (nonvanishingOpen L s)))) ≅
    F.over (nonvanishingOpen L s) := by
  let O := nonvanishingOpenRing X L s
  let hO := nonvanishingOpenRingSheaf X L s
  let U := nonvanishingOpen L s
  exact Invertible.tensorProductIso O hO (Iso.refl _) (tensorPowerRestrictionIso X L s n) ≪≫
    Invertible.tensorProductIso O hO (Iso.refl _)
      (restrictedTensorPowerBasisIso X L s n).symm ≪≫
    Invertible.tensorProductRightUnitor O hO (F.over U)

private noncomputable def divideSectionByPower (s : L.sections) (n : ℕ)
    (m : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L
        (n : ℤ))))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
    F.val.obj (op (nonvanishingOpen L s)) := by
  let U := nonvanishingOpen L s
  let uObj : Over U := Over.mk (𝟙 U)
  exact (divisionIsoOver X L F s n).hom.val.app (op uObj)
    (((tensorRestrictionIsoOnScheme X F
      (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
        (n : ℤ)) U).hom.val.app (op uObj))
      (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L
          (n : ℤ))))).val.map (terminal.from _).op m))

private theorem divideSectionByPower_add (s : L.sections) (n : ℕ)
    (m₁ m₂ : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L
        (n : ℤ))))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
    divideSectionByPower X L F s n (m₁ + m₂) =
      divideSectionByPower X L F s n m₁ + divideSectionByPower X L F s n m₂ := by
  let U := nonvanishingOpen L s
  let uObj : Over U := Over.mk (𝟙 U)
  let mres := ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
    Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
    ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
    (sectionSiteSheaf X) L (n : ℤ))))).val.map
      (terminal.from U).op
  let e₁ := tensorRestrictionIsoOnScheme X F
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)) U
  let e₂ := divisionIsoOver X L F s n
  show (e₂.hom.val.app (op uObj)).hom
      ((e₁.hom.val.app (op uObj)).hom (mres.hom (m₁ + m₂))) = _
  exact (congrArg (fun y => (e₂.hom.val.app (op uObj)).hom
      ((e₁.hom.val.app (op uObj)).hom y)) (mres.hom.map_add m₁ m₂)).trans
    ((congrArg (fun y => (e₂.hom.val.app (op uObj)).hom y)
        ((e₁.hom.val.app (op uObj)).hom.map_add _ _)).trans
      ((e₂.hom.val.app (op uObj)).hom.map_add _ _))

private theorem divideSectionByPower_zero (s : L.sections) (n : ℕ) :
    divideSectionByPower X L F s n 0 = 0 := by
  let U := nonvanishingOpen L s
  let uObj : Over U := Over.mk (𝟙 U)
  let mres := ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
    Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
    ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
    (sectionSiteSheaf X) L (n : ℤ))))).val.map
      (terminal.from U).op
  let e₁ := tensorRestrictionIsoOnScheme X F
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)) U
  let e₂ := divisionIsoOver X L F s n
  show (e₂.hom.val.app (op uObj)).hom
      ((e₁.hom.val.app (op uObj)).hom (mres.hom 0)) = 0
  exact (congrArg (fun y => (e₂.hom.val.app (op uObj)).hom
      ((e₁.hom.val.app (op uObj)).hom y)) mres.hom.map_zero).trans
    ((congrArg (fun y => (e₂.hom.val.app (op uObj)).hom y)
        (e₁.hom.val.app (op uObj)).hom.map_zero).trans
      (e₂.hom.val.app (op uObj)).hom.map_zero)

/-- The canonical map from degree-zero localized twisted sections to sections on `X_s`.
It restricts a numerator to `X_s` and divides by the corresponding power of `s`.
The section is invertible there, so this construction is independent of the fraction
representative. -/
@[stacks 0B5L]
public noncomputable def sectionLocalizationMap (s : L.sections) :
    sectionAtNonvanishingOpen X L F s →+
      F.val.obj (op (nonvanishingOpen L s)) :=
  degreeZeroLocalizationLift
    (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
    (sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L F)
    (homogeneousSection_mem X L s) (moduleFractionNumerator X L F s)
    (moduleFractionNumerator_smul_power X L F s)

/-- A homogeneous fraction `m/sⁿ` maps to the section `t` exactly when, on
`X_s`, the restricted numerator is the tensor product of `t` with `sⁿ`.
The local invertibility of `sⁿ` makes this condition a characterization. -/
@[stacks 0B5L "homogeneous fraction formula"]
public theorem sectionLocalizationMap_fraction (s : L.sections) (n : ℕ)
    (m : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L
        (n : ℤ))))).val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (z : sectionAtNonvanishingOpen X L F s)
    (t : F.val.obj (op (nonvanishingOpen L s)))
    (hz : (z : LocalizedModule.Away
      (R := sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L)
      (homogeneousSection X L s)
      (sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L F)) =
        LocalizedModule.mk (S := Submonoid.powers (homogeneousSection X L s))
          (DirectSum.of _ (n : ℤ) m)
          ⟨(homogeneousSection X L s) ^ n, by exact ⟨n, rfl⟩⟩)
    (hdiv :
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
        ((sectionSiteSheaf X))⟩).obj (F)).obj ((TensorPower.tensorPower (sectionSiteRing X)
        (sectionSiteSheaf X) L
          (n : ℤ))))).val.map (terminal.from _).op m =
      tensorSectionAtOpen X L F
        (nonvanishingOpen L s) n t
        ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
          (n : ℤ)).val.map (terminal.from _).op (sectionPower X L s n))) :
    sectionLocalizationMap X L F s z = t := by
  show fractionValue
    (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
    (sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L F)
    (homogeneousSection_mem X L s) (moduleFractionNumerator X L F s) z = t
  rw [fractionValue_eq _ _ _ _ (moduleFractionNumerator_smul_power X L F s)
    z n (DirectSum.of _ (n : ℤ) m) ⟨m, rfl⟩ hz]
  apply (tensorBasisAt X L F s n).injective
  rw [moduleFractionNumerator_of, tensorBasisAt_eq_tensor]
  exact hdiv

/-- The restriction-and-division map is linear over the induced map from the
degree-zero homogeneous localization of the section ring to functions on `X_s`. -/
@[stacks 0B5L "localized-ring linearity"]
public theorem sectionLocalizationMap_smul (s : L.sections) :
    let U := nonvanishingOpen L s
    letI : Module
        ((TensorSheafification.structureSheaf (sectionSiteRing X)
          (sectionSiteSheaf X)).obj.obj (op U))
        (F.val.obj (op U)) := (F.val.obj (op U)).isModule
    ∃ φ : HomogeneousLocalization.Away
        (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
        (homogeneousSection X L s) →+*
          (TensorSheafification.structureSheaf (sectionSiteRing X)
            (sectionSiteSheaf X)).obj.obj (op U),
      ∀ (a : HomogeneousLocalization.Away
          (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
          (homogeneousSection X L s)) (z : sectionAtNonvanishingOpen X L F s),
        sectionLocalizationMap X L F s (a • z) =
          φ a • sectionLocalizationMap X L F s z := by
  let U := nonvanishingOpen L s
  let _mF : Module ((sectionSiteRing X).obj (op U)) (F.val.obj (op U)) :=
    (F.val.obj (op U)).isModule
  let A := sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L
  let B := sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L F
  let e := ringFractionNumerator X L s
  let he := ringFractionNumerator_mul_power X L s
  have h1 : e 0 1 = 1 := by
    simpa only [pow_zero] using ringFractionNumerator_power X L s 0
  let φ := homogeneousLocalizationLift A (homogeneousSection_mem X L s) e he h1
    (ringFractionNumerator_mul X L s)
  refine ⟨φ, ?_⟩
  apply degreeZeroLocalizationLift_smul A B (homogeneousSection_mem X L s)
    (moduleFractionNumerator X L F s) (moduleFractionNumerator_smul_power X L F s) φ
  intro m n r x hr hx
  have hr' : r ∈ A m := by simpa using hr
  have hφ : φ (HomogeneousLocalization.Away.mk A (homogeneousSection_mem X L s) m r hr) =
      e m r :=
    ringFractionValue_eq A (homogeneousSection_mem X L s) e he _ m r hr'
      (HomogeneousLocalization.Away.val_mk ..)
  rw [hφ]
  exact moduleFractionNumerator_smul X L F s m n r x hr' hx

end AcceptedStatementInstances

end Stacks.SheafOfModules

end
