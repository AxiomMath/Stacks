module

public import Mathlib.Topology.Algebra.PontryaginDual
public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.GroupTheory.Torsion
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.LocallyConstant.Basic
public import StacksFrontier.Topology.Algebra.ProfiniteGroup

/-!
# Pontryagin duals of torsion and of profinite abelian groups

For an abelian topological group `A` (written multiplicatively, as Mathlib's
`PontryaginDual A = A →ₜ* Circle` requires) this file proves the group-theoretic content of the
"trivial duality" paragraph of [Stacks, Tag 03VI]: the functor `M ↦ M^∧ = Hom_cont(M, S¹)` maps
torsion discrete groups to profinite groups and profinite groups to torsion discrete groups, and
on these groups `M^∧` is a group of characters with values in `ℚ/ℤ`.

The group `ℚ/ℤ` is `AddCircle (1 : ℚ)`, the target of Mathlib's `CharacterModule`, and is
identified with the torsion subgroup of `Circle` by `x ↦ exp (2πix)`
(`Stacks.Pontryagin.ratCircleToCircle`).

## Main definitions

* `Stacks.Pontryagin.ratCircleToCircle`: the injective homomorphism `ℚ/ℤ → S¹`,
  `x ↦ exp (2πix)`, whose image is the torsion of `S¹`.
* `Stacks.Pontryagin.locallyConstantCharacters M`: the characters `M → ℚ/ℤ` that are continuous
  for the discrete topology on `ℚ/ℤ`, i.e. locally constant.
* `Stacks.Pontryagin.addEquivCharacterModule`: for `A` discrete and torsion,
  `A^∧ ≃ Hom(A, ℚ/ℤ) = CharacterModule (Additive A)`.
* `Stacks.Pontryagin.addEquivLocallyConstantCharacters`: for `A` profinite,
  `A^∧ ≃ Hom_cont(A, ℚ/ℤ)`.

## Main results

* `Stacks.Pontryagin.isProfiniteTop_of_isTorsion`: the dual of a discrete torsion abelian group is
  compact, Hausdorff and totally disconnected.
* `Stacks.Pontryagin.isEmbedding_addEquivCharacterModule`: for `A` discrete and torsion, the
  isomorphism `A^∧ ≃ Hom(A, ℚ/ℤ)` is a homeomorphism for the topology of pointwise convergence.
* `Stacks.Pontryagin.discreteTopology_and_isTorsion`: the dual of a profinite abelian group is
  discrete and torsion.
* `Stacks.Pontryagin.not_isTorsion_pontryaginDual_int`,
  `Stacks.Pontryagin.isEmpty_addEquiv_characterModule_int`: for the discrete group `ℤ`, which is
  not torsion, `ℤ^∧` is not torsion and is not isomorphic to `Hom(ℤ, ℚ/ℤ)`; so the identification
  `M^∧ = Hom(M, ℚ/ℤ)` for discrete `M` needs `M` torsion.

## Implementation notes

For an additive group `M` apply these results to `A = Multiplicative M`: then `Additive A` is `M`
by definition, so `CharacterModule (Additive A)` is `CharacterModule M` (the dual used for finite
coefficients in `StacksFrontier.Algebra.Module.CharacterModule.Finite`), and
`IsMulTorsion (Multiplicative M)` is `IsAddTorsion M`
(`Stacks.Pontryagin.isMulTorsion_multiplicative_iff`).

## References

* [Stacks, Tag 03VI]
-/

@[expose] public noncomputable section

open Real Topology Stacks.Chapter05.Tag_0BR1

namespace Stacks.Pontryagin

/-! ### `ℚ/ℤ` as the torsion of the circle -/

/-- The homomorphism `ℚ/ℤ → S¹`, `x ↦ exp (2πix)`, written additively on `S¹`. -/
def ratCircleToCircle : AddCircle (1 : ℚ) →+ Additive Circle :=
  QuotientAddGroup.lift _
    (Circle.expHom.comp ((AddMonoidHom.mulLeft (2 * π)).comp (Rat.castHom ℝ).toAddMonoidHom))
    (by
      intro x hx
      obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
      simp [AddMonoidHom.mem_ker, Circle.exp_two_pi_mul_int])

/-- `ratCircleToCircle` sends the class of `q ∈ ℚ` to `exp (2πiq)`. -/
theorem ratCircleToCircle_coe (q : ℚ) :
    ratCircleToCircle (q : AddCircle (1 : ℚ)) = Additive.ofMul (Circle.exp (2 * π * q)) :=
  rfl

/-- `exp (2πix) = 1` for `x ∈ ℚ` exactly when `x ∈ ℤ`. -/
theorem ratCircleToCircle_injective : Function.Injective ratCircleToCircle := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
  induction x using QuotientAddGroup.induction_on with | H q => ?_
  rw [ratCircleToCircle_coe] at hx
  obtain ⟨n, hn⟩ := Circle.exp_eq_one.mp (Additive.ofMul.injective hx)
  have hq : (q : ℝ) = n := by
    have := pi_pos
    field_simp at hn
    linarith
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨n, by simpa using (Rat.cast_injective (α := ℝ) (by simpa using hq.symm))⟩

/-- Every point of finite order of `S¹` is `exp (2πix)` for some `x ∈ ℚ/ℤ`. -/
theorem exists_ratCircleToCircle_eq {z : Circle} (hz : IsOfFinOrder z) :
    ∃ x, ratCircleToCircle x = Additive.ofMul z := by
  obtain ⟨n, hn, hzn⟩ := isOfFinOrder_iff_pow_eq_one.mp hz
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  rw [← Circle.exp_natCast_mul] at hzn
  obtain ⟨m, hm⟩ := Circle.exp_eq_one.mp hzn
  refine ⟨((m / n : ℚ) : AddCircle (1 : ℚ)), ?_⟩
  rw [ratCircleToCircle_coe]
  congr 2
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp
  linarith

/-- The points of `S¹` with `z ^ n = 1`, `n > 0`, form a finite set. -/
theorem finite_setOf_pow_eq_one {n : ℕ} (hn : 0 < n) : {z : Circle | z ^ n = 1}.Finite := by
  refine Set.Finite.of_finite_image (f := ((↑) : Circle → ℂ)) ?_ Subtype.val_injective.injOn
  refine (Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.subset ?_
  rintro _ ⟨z, hz, rfl⟩
  simp only [Set.mem_ofPred_eq] at hz
  simp [Polynomial.mem_nthRoots hn, ← Circle.coe_pow, hz]

/-- `Multiplicative M` is torsion exactly when `M` is. -/
theorem isMulTorsion_multiplicative_iff {M : Type*} [AddMonoid M] :
    IsMulTorsion (Multiplicative M) ↔ IsAddTorsion M :=
  ⟨fun h x ↦ h (Multiplicative.ofAdd x), fun h x ↦ h x.toAdd⟩

variable {A : Type*} [CommGroup A]

/-! ### Characters with values in `ℚ/ℤ` -/

/-- A character `χ : A → S¹` all of whose values have finite order, as a character
`A → ℚ/ℤ`. -/
def torsionLift (χ : A →* Circle) (hχ : ∀ a, IsOfFinOrder (χ a)) :
    Additive A →+ AddCircle (1 : ℚ) :=
  (AddMonoidHom.ofInjective ratCircleToCircle_injective).symm.toAddMonoidHom.comp
    ((MonoidHom.toAdditive χ).codRestrict _ fun a ↦
      AddMonoidHom.mem_range.mpr (exists_ratCircleToCircle_eq (hχ a.toMul)))

/-- `torsionLift χ` is characterized by `exp (2πi (torsionLift χ a)) = χ a`. -/
@[simp]
theorem ratCircleToCircle_torsionLift (χ : A →* Circle) (hχ : ∀ a, IsOfFinOrder (χ a))
    (a : Additive A) :
    ratCircleToCircle (torsionLift χ hχ a) = Additive.ofMul (χ a.toMul) := by
  simp only [torsionLift, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [← AddMonoidHom.ofInjective_apply ratCircleToCircle_injective, AddEquiv.apply_symm_apply]
  rfl

/-- The character `a ↦ exp (2πi f(a))` of `A` attached to `f : A → ℚ/ℤ`. -/
def toCircleHom (f : Additive A →+ AddCircle (1 : ℚ)) : A →* Circle :=
  MonoidHom.toAdditive.symm (ratCircleToCircle.comp f)

/-- The value of `toCircleHom f` at `a` is `exp (2πi f(a))`. -/
@[simp]
theorem toCircleHom_apply (f : Additive A →+ AddCircle (1 : ℚ)) (a : A) :
    Additive.ofMul (toCircleHom f a) = ratCircleToCircle (f (Additive.ofMul a)) :=
  rfl

/-- `toCircleHom` is a left inverse of `torsionLift`. -/
theorem toCircleHom_torsionLift (χ : A →* Circle) (hχ : ∀ a, IsOfFinOrder (χ a)) :
    toCircleHom (torsionLift χ hχ) = χ := by
  ext a
  exact congrArg (fun x ↦ ((Additive.toMul x : Circle) : ℂ))
    (ratCircleToCircle_torsionLift χ hχ (Additive.ofMul a))

/-- `torsionLift` is a left inverse of `toCircleHom`. -/
theorem torsionLift_toCircleHom (f : Additive A →+ AddCircle (1 : ℚ))
    (hf : ∀ a, IsOfFinOrder (toCircleHom f a)) : torsionLift (toCircleHom f) hf = f := by
  refine AddMonoidHom.ext fun a ↦ ?_
  apply ratCircleToCircle_injective
  rw [ratCircleToCircle_torsionLift]
  rfl

/-- `torsionLift` turns products of characters into sums. -/
theorem torsionLift_mul (χ ψ : A →* Circle) (hχ : ∀ a, IsOfFinOrder (χ a))
    (hψ : ∀ a, IsOfFinOrder (ψ a)) (hχψ : ∀ a, IsOfFinOrder ((χ * ψ) a)) :
    torsionLift (χ * ψ) hχψ = torsionLift χ hχ + torsionLift ψ hψ := by
  refine AddMonoidHom.ext fun a ↦ ?_
  apply ratCircleToCircle_injective
  rw [AddMonoidHom.add_apply, map_add, ratCircleToCircle_torsionLift,
    ratCircleToCircle_torsionLift, ratCircleToCircle_torsionLift]
  rfl

variable [TopologicalSpace A]

/-- The homomorphism `A →* S¹` underlying a continuous character. -/
def charHom (χ : PontryaginDual A) : A →* Circle :=
  (χ : A →ₜ* Circle).toMonoidHom

/-- `charHom χ` has the values of `χ`. -/
@[simp]
theorem charHom_apply (χ : PontryaginDual A) (a : A) : charHom χ a = χ a :=
  rfl

/-- Powers of characters are computed pointwise. -/
theorem pow_apply (χ : PontryaginDual A) (n : ℕ) (a : A) : (χ ^ n) a = χ a ^ n :=
  ContinuousMonoidHom.pow_apply (χ : A →ₜ* Circle) n a

/-! ### Discrete torsion groups -/

section Torsion

/-- The characters of a torsion group take values of finite order. -/
theorem isOfFinOrder_apply_of_isTorsion (hA : IsMulTorsion A) (χ : PontryaginDual A)
    (a : A) : IsOfFinOrder (charHom χ a) :=
  (charHom χ).isOfFinOrder (hA a)

/-- The dual of a torsion group is totally disconnected: a character is determined by its values,
the value at `a` lies in the finite set of roots of unity of order dividing the order of `a`. -/
theorem totallyDisconnectedSpace_of_isTorsion (hA : IsMulTorsion A) :
    TotallyDisconnectedSpace (PontryaginDual A) := by
  have hfin (a : A) : Finite {z : Circle // z ^ orderOf a = 1} :=
    (finite_setOf_pow_eq_one (hA a).orderOf_pos).to_subtype
  let F : PontryaginDual A → ∀ a : A, {z : Circle // z ^ orderOf a = 1} := fun χ a ↦
    ⟨χ a, by rw [← map_pow, pow_orderOf_eq_one, map_one]⟩
  have hFc : Continuous F :=
    continuous_pi fun a ↦
      (continuous_eval_const a : Continuous fun χ : A →ₜ* Circle ↦ χ a).subtype_mk _
  have hFi : Function.Injective F := fun χ ψ h ↦
    PontryaginDual.ext fun a ↦ congrArg Subtype.val (congrFun h a)
  exact ⟨fun s _ hs ↦ (hFi.subsingleton_image_iff).mp (hs.image F hFc.continuousOn).subsingleton⟩

/-- **The dual of a discrete torsion abelian group is profinite**: compact, Hausdorff and totally
disconnected. -/
@[stacks 03VI "the dual of a discrete torsion abelian group is profinite"]
theorem isProfiniteTop_of_isTorsion [DiscreteTopology A] (hA : IsMulTorsion A) :
    IsProfiniteTop (PontryaginDual A) :=
  ⟨inferInstance, inferInstance, totallyDisconnectedSpace_of_isTorsion hA⟩

/-- **The dual of a discrete torsion group is `Hom(M, ℚ/ℤ)`**: for `A` discrete and torsion,
`χ ↦ (a ↦ x)` with `χ(a) = exp (2πix)` is a group isomorphism from `A^∧ = Hom_cont(A, S¹)` onto
`Hom(A, ℚ/ℤ) = CharacterModule (Additive A)`. -/
@[stacks 03VI "for M discrete torsion, M^∧ = Hom(M, Q/Z)"]
def addEquivCharacterModule [DiscreteTopology A] (hA : IsMulTorsion A) :
    Additive (PontryaginDual A) ≃+ CharacterModule (Additive A) where
  toFun χ := torsionLift (charHom (Additive.toMul χ))
    (isOfFinOrder_apply_of_isTorsion hA χ.toMul)
  invFun f := Additive.ofMul (⟨toCircleHom f, continuous_of_discreteTopology⟩ : A →ₜ* Circle)
  left_inv χ := congrArg Additive.ofMul (PontryaginDual.ext fun a ↦
    DFunLike.congr_fun (toCircleHom_torsionLift (charHom (Additive.toMul χ))
      (isOfFinOrder_apply_of_isTorsion hA _)) a)
  right_inv f := by exact torsionLift_toCircleHom f _
  map_add' χ ψ := by exact torsionLift_mul _ _ _ _ _

/-- The value of `addEquivCharacterModule hA χ` at `a` is the `x ∈ ℚ/ℤ` with
`exp (2πix) = χ(a)`. -/
theorem ratCircleToCircle_addEquivCharacterModule_apply [DiscreteTopology A]
    (hA : IsMulTorsion A) (χ : Additive (PontryaginDual A)) (a : A) :
    ratCircleToCircle (addEquivCharacterModule hA χ (Additive.ofMul a)) =
      Additive.ofMul (Additive.toMul χ a) :=
  ratCircleToCircle_torsionLift (charHom (Additive.toMul χ))
    (isOfFinOrder_apply_of_isTorsion hA _) (Additive.ofMul a)

/-- The topology of the dual of a discrete group is the topology of pointwise convergence:
`χ ↦ (a ↦ χ a)` is an embedding of `A^∧` into `A → S¹`. -/
theorem isEmbedding_coeFn [DiscreteTopology A] :
    Topology.IsEmbedding fun χ : PontryaginDual A ↦ (χ : A → Circle) :=
  ContinuousMap.isHomeomorph_coe.isEmbedding.comp
    (ContinuousMonoidHom.isEmbedding_toContinuousMap A Circle)

/-- **The topology of `M^∧ = Hom(M, ℚ/ℤ)`**: for `A` discrete and torsion, the isomorphism
`addEquivCharacterModule` is a homeomorphism onto `Hom(A, ℚ/ℤ)` with the topology of pointwise
convergence, `ℚ/ℤ` carrying the topology of the torsion subgroup of `S¹`. -/
theorem isEmbedding_addEquivCharacterModule [DiscreteTopology A] (hA : IsMulTorsion A) :
    Topology.IsEmbedding fun χ : PontryaginDual A ↦ fun a : A ↦
      ratCircleToCircle (addEquivCharacterModule hA (Additive.ofMul χ) (Additive.ofMul a)) := by
  have h : (fun χ : PontryaginDual A ↦ fun a : A ↦
      ratCircleToCircle (addEquivCharacterModule hA (Additive.ofMul χ) (Additive.ofMul a))) =
      fun χ : PontryaginDual A ↦ fun a : A ↦ Additive.ofMul (χ a) :=
    funext fun χ ↦ funext fun a ↦
      ratCircleToCircle_addEquivCharacterModule_apply hA (Additive.ofMul χ) a
  rw [h]
  exact isEmbedding_coeFn

end Torsion

/-! ### Profinite groups -/

section Profinite

/-- The characters `M → ℚ/ℤ` that are continuous for the discrete topology on `ℚ/ℤ`, that is,
the locally constant ones (`IsLocallyConstant.iff_continuous`). -/
def locallyConstantCharacters (M : Type*) [AddCommGroup M] [TopologicalSpace M] :
    AddSubgroup (CharacterModule M) where
  carrier := {f | IsLocallyConstant f}
  add_mem' hf hg := hf.add hg
  zero_mem' := IsLocallyConstant.const 0
  neg_mem' hf := hf.neg

/-- Membership in `locallyConstantCharacters M` is local constancy. -/
theorem mem_locallyConstantCharacters {M : Type*} [AddCommGroup M] [TopologicalSpace M]
    {f : CharacterModule M} : f ∈ locallyConstantCharacters M ↔ IsLocallyConstant f :=
  Iff.rfl

variable [IsTopologicalGroup A] [CompactSpace A] [TotallyDisconnectedSpace A]

/-- A continuous character of a profinite group is trivial on an open normal subgroup: the
preimage of a small arc around `1` contains an open subgroup, whose image is a subgroup of `S¹`
inside the arc, hence trivial. -/
theorem exists_openNormalSubgroup_le_ker (χ : PontryaginDual A) :
    ∃ H : OpenNormalSubgroup A, ∀ h ∈ H, χ h = 1 := by
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    ((Circle.isOpen_centeredArc (π / 2)).preimage (map_continuous χ)) (by
      simp only [Set.mem_preimage, map_one]
      rw [Circle.mem_centeredArc (by linarith [pi_pos])]
      simp [pi_pos])
  refine ⟨H, fun h hh ↦ Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ ↦ ?_⟩
  rw [← map_pow]
  exact hH (pow_mem hh n)

/-- A continuous character of a profinite group is killed by a positive integer. -/
theorem exists_pow_apply_eq_one (χ : PontryaginDual A) :
    ∃ n, 0 < n ∧ ∀ a, χ a ^ n = 1 := by
  obtain ⟨H, hH⟩ := exists_openNormalSubgroup_le_ker χ
  have : H.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine ⟨H.toSubgroup.index, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, fun a ↦ ?_⟩
  rw [← map_pow]
  exact hH _ (H.toSubgroup.pow_index_mem a)

/-- The values of a continuous character of a profinite group have finite order. -/
theorem isOfFinOrder_apply (χ : PontryaginDual A) (a : A) : IsOfFinOrder (charHom χ a) := by
  obtain ⟨n, hn, h⟩ := exists_pow_apply_eq_one χ
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, h a⟩

/-- A continuous character of a profinite group has finite order. -/
theorem isOfFinOrder (χ : PontryaginDual A) : IsOfFinOrder χ := by
  obtain ⟨n, hn, h⟩ := exists_pow_apply_eq_one χ
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, PontryaginDual.ext fun a ↦ ?_⟩
  exact (pow_apply χ n a).trans (h a)

/-- **The dual of a profinite abelian group is discrete and torsion.** -/
@[stacks 03VI "the dual of a profinite abelian group is discrete torsion"]
theorem discreteTopology_and_isTorsion :
    DiscreteTopology (PontryaginDual A) ∧ IsMulTorsion (PontryaginDual A) :=
  ⟨inferInstance, isOfFinOrder⟩

/-- The `ℚ/ℤ`-valued character attached to a continuous character of a profinite group is locally
constant: it is constant on the cosets of an open subgroup. -/
theorem isLocallyConstant_torsionLift (χ : PontryaginDual A) :
    IsLocallyConstant (torsionLift (charHom χ) (isOfFinOrder_apply χ)) := by
  obtain ⟨H, hH⟩ := exists_openNormalSubgroup_le_ker χ
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x ↦ ?_
  have hmem : (H : Set A) ∈ 𝓝 ((Additive.toMul x)⁻¹ * Additive.toMul x) := by
    rw [inv_mul_cancel]
    exact H.isOpen.mem_nhds H.one_mem
  have hc : Continuous fun y : Additive A ↦ (Additive.toMul x)⁻¹ * Additive.toMul y :=
    continuous_const.mul continuous_toMul
  filter_upwards [hc.continuousAt.preimage_mem_nhds hmem] with y hy
  apply ratCircleToCircle_injective
  rw [ratCircleToCircle_torsionLift, ratCircleToCircle_torsionLift]
  have h1 : χ ((Additive.toMul x)⁻¹ * Additive.toMul y) = 1 := hH _ hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact congrArg Additive.ofMul h1.symm

/-- **The dual of a profinite group is `Hom_cont(M, ℚ/ℤ)`**: for `A` profinite,
`χ ↦ (a ↦ x)` with `χ(a) = exp (2πix)` is a group isomorphism from `A^∧ = Hom_cont(A, S¹)` onto
the group of characters `A → ℚ/ℤ` continuous for the discrete topology on `ℚ/ℤ`. -/
@[stacks 03VI "for M profinite, M^∧ = Hom_cont(M, Q/Z)"]
def addEquivLocallyConstantCharacters :
    Additive (PontryaginDual A) ≃+ locallyConstantCharacters (Additive A) where
  toFun χ := ⟨torsionLift (charHom (Additive.toMul χ))
    (isOfFinOrder_apply χ.toMul), isLocallyConstant_torsionLift χ.toMul⟩
  invFun f := Additive.ofMul (⟨toCircleHom f.1,
    ((mem_locallyConstantCharacters.mp f.2).comp
      (fun x ↦ Additive.toMul (ratCircleToCircle x))).continuous⟩ : A →ₜ* Circle)
  left_inv χ := congrArg Additive.ofMul (PontryaginDual.ext fun a ↦
    DFunLike.congr_fun (toCircleHom_torsionLift (charHom (Additive.toMul χ))
      (isOfFinOrder_apply _)) a)
  right_inv f := by
    refine Subtype.ext (AddMonoidHom.ext fun a ↦ ratCircleToCircle_injective ?_)
    dsimp only
    rw [ratCircleToCircle_torsionLift]
    rfl
  map_add' χ ψ := Subtype.ext (by
    simp only [AddSubgroup.coe_add]
    exact torsionLift_mul (charHom χ.toMul) (charHom ψ.toMul) _ _ _)

/-- The value of `addEquivLocallyConstantCharacters χ` at `a` is the `x ∈ ℚ/ℤ` with
`exp (2πix) = χ(a)`. -/
theorem ratCircleToCircle_addEquivLocallyConstantCharacters_apply
    (χ : Additive (PontryaginDual A)) (a : A) :
    ratCircleToCircle ((addEquivLocallyConstantCharacters χ : CharacterModule (Additive A))
      (Additive.ofMul a)) = Additive.ofMul (Additive.toMul χ a) :=
  ratCircleToCircle_torsionLift (charHom (Additive.toMul χ)) (isOfFinOrder_apply _)
    (Additive.ofMul a)

end Profinite

/-! ### The discrete group `ℤ` -/

section Int

/-- The character `n ↦ exp (2πi√2 n)` of `ℤ`. -/
def sqrtTwoCharacter : PontryaginDual (Multiplicative ℤ) :=
  (⟨zpowersHom Circle (Circle.exp (2 * π * √2)), continuous_of_discreteTopology⟩ :
    Multiplicative ℤ →ₜ* Circle)

/-- `sqrtTwoCharacter` sends `1` to `exp (2πi√2)`. -/
theorem sqrtTwoCharacter_apply_one :
    sqrtTwoCharacter (Multiplicative.ofAdd 1) = Circle.exp (2 * π * √2) := by
  change zpowersHom Circle _ (Multiplicative.ofAdd 1) = _
  simp

/-- **The dual of `ℤ` is not torsion**: the character `n ↦ exp (2πi√2 n)` has infinite order, as
`√2` is irrational. So for the discrete group `M = ℤ`, which is not torsion, `M^∧` is not
torsion. -/
theorem not_isTorsion_pontryaginDual_int : ¬ IsMulTorsion (PontryaginDual (Multiplicative ℤ)) := by
  intro h
  obtain ⟨n, hn, hχ⟩ := isOfFinOrder_iff_pow_eq_one.mp (h sqrtTwoCharacter)
  have h1 : Circle.exp (2 * π * √2) ^ n = 1 := by
    have := pow_apply sqrtTwoCharacter n (Multiplicative.ofAdd 1)
    rw [hχ, sqrtTwoCharacter_apply_one] at this
    exact this.symm
  obtain ⟨x, hx⟩ := exists_ratCircleToCircle_eq (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, h1⟩)
  induction x using QuotientAddGroup.induction_on with | H q => ?_
  rw [ratCircleToCircle_coe] at hx
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (Additive.ofMul.injective hx)
  refine irrational_sqrt_two ⟨q - m, ?_⟩
  have := pi_pos
  push_cast
  field_simp at hm
  linarith

/-- `Hom(ℤ, ℚ/ℤ)` is torsion. -/
theorem isAddTorsion_characterModule_int : IsAddTorsion (CharacterModule ℤ) := by
  intro f
  induction hx : f 1 using QuotientAddGroup.induction_on with | H q => ?_
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨q.den, q.den_pos, ?_⟩
  ext k
  change q.den • f k = 0
  have hk : f k = k • f 1 := by rw [← map_zsmul, smul_eq_mul, mul_one]
  have h0 : (((q.num : ℚ)) : AddCircle (1 : ℚ)) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨q.num, by simp⟩
  rw [hk, hx, smul_comm, ← QuotientAddGroup.mk_nsmul, nsmul_eq_mul, Rat.den_mul_eq_num, h0,
    smul_zero]

/-- **`ℤ^∧` is not `Hom(ℤ, ℚ/ℤ)`**: there is no group isomorphism between the dual of the discrete
group `ℤ` and its group of `ℚ/ℤ`-valued characters, the second being torsion and the first not.
So the identification `M^∧ = Hom(M, ℚ/ℤ)` of [Stacks, Tag 03VI] for discrete `M` needs `M`
torsion. -/
theorem isEmpty_addEquiv_characterModule_int :
    IsEmpty (Additive (PontryaginDual (Multiplicative ℤ)) ≃+ CharacterModule ℤ) := by
  refine ⟨fun e ↦ not_isTorsion_pontryaginDual_int fun χ ↦ ?_⟩
  have h := (e.symm : CharacterModule ℤ →+ Additive (PontryaginDual (Multiplicative ℤ)))
    |>.isOfFinAddOrder (isAddTorsion_characterModule_int (e (Additive.ofMul χ)))
  exact isOfFinAddOrder_ofMul_iff.mp (by simpa using h)

end Int

end Stacks.Pontryagin
