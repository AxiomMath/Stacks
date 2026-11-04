module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FieldBaseChangeGraded
public import StacksFrontier.AlgebraicGeometry.Chow.VectorBundleKZeroPullbackComp
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FieldBaseChangeChow

/-!
# The cohomological Chern character and the cycle class map along a field extension

Lemma 0FVT of the Stacks Project compares data (D0), (D1), (D2') `F(1), H^*, c₁^H` over `k`, `F`
with data `F'(1), (H')^*, c₁^{H'}` over `k'`, `F'` through isomorphisms
`F(1) ⊗_F F' ≅ F'(1)` and `H^*(X) ⊗_F F' ≅ (H')^*(X_{k'})` compatible with `c₁`
(`Stacks.WeilDeRham.FieldBaseChangeData`). In the middle of its proof it shows that, both data
satisfying (A1) – (A4), the cycle class maps `γ` and `γ'` of Lemma 0FIF are compatible with the
base change `g^* : CH^*(X) → CH^*(X_{k'})` of Chow Homology, Lemma 0FVJ. The source reduces this to
the compatibility of the cohomological Chern characters, `ch^H(β) ↦ ch^{H'}((X_{k'} → X)^*β)`,
which it proves with the splitting principle, from the agreement of first Chern classes.

## The coordinates

The comparison map `H^*(X)(n) → (H')^*(X_{k'})(n)` is coordinate free
(`Stacks.WeilDeRham.FieldBaseChangeData.twistHom`), but `ch^H` and `γ` are read in the
coordinates of the canonical coordinate `𝔇.coord` of `F(1)`, and `ch^{H'}`, `γ'` in those of
`𝔇'.coord`. On the `𝔇'` side `twistHom` is read in the coordinate induced from `𝔇.coord`
(`Stacks.WeilDeRham.inducedTateCoordinate`), which is `𝔇'.coord` up to a nonzero scalar `μ`
(`Stacks.WeilDeRham.FieldBaseChangeData.tateScale`). So in coordinates the degree `n` part of
`ch^{H'}` is `μⁿ` times the image of the degree `n` part of `ch^H`: this is what the agreement of
first Chern classes says for `n = 1`, and the comparison of the cycle classes in the twisted
groups, which is coordinate free, follows.

## Main definitions

* `Stacks.WeilDeRham.FieldBaseChangeData.tateScale`: the scalar `μ` relating the two
  coordinates of `F'(1)`.

## Main results

* `Stacks.WeilDeRham.FieldBaseChangeData.coe_coeff_cohomologicalChernCharacter_pullback`: the
  degree `n` part of `ch^{H'}((X_{k'} → X)^*α)` is `μⁿ` times the image of that of `ch^H(α)`.
  As in the source, this is reduced by the splitting principle to invertible modules, where it is
  the agreement of first Chern classes; the injectivity of the pullbacks of the splitting principle
  survives the base change because `F'` is flat over `F`.
* `Stacks.WeilDeRham.FieldBaseChangeData.twistHom_cycleClass`: `γ'(g^*α)` is the image of `γ(α)`.

## References

* [Stacks Project, Tag 0FVT](https://stacks.math.columbia.edu/tag/0FVT)
* [Stacks Project, Tag 0FIE](https://stacks.math.columbia.edu/tag/0FIE)
* [Stacks Project, Tag 0FIF](https://stacks.math.columbia.edu/tag/0FIF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Stacks.WeilCohomology
open Stacks.Chow

universe u w w'

namespace Stacks.WeilDeRham

open Stacks.WeilCohomology.SmoothProjectiveScheme

/-! ### Changing the coordinate of a Tate line -/

section Coordinates

variable {R : Type*} [Field R] {L : Type*} [AddCommGroup L] [Module R L]
  {V : Type*} [AddCommGroup V] [Module R V]

/-- Two coordinates `c' = r c` of a line give coordinates `c'^{⊗n} = rⁿ c^{⊗n}` of its `n`-th
tensor power. -/
theorem tensorPowerCoordinates_of_coord_eq_mul (c c' : L ≃ₗ[R] R) (r : R)
    (h : ∀ l, c' l = r * c l) (n : ℕ) (x : TensorPower R n L) :
    tensorPowerCoordinates c' n x = r ^ n * tensorPowerCoordinates c n x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a v =>
    simp [tensorPowerCoordinates, PiTensorProduct.constantBaseRingEquiv_tprod, h,
      Finset.prod_mul_distrib, mul_left_comm]
  | add x y hx hy => simp [hx, hy, mul_add]

/-- Two coordinates `c' = r c` of a line give coordinates on the twist `V(n)`, `n ≥ 0`, which
differ by `rⁿ`. -/
theorem tateTwistCoordinates_natCast_of_coord_eq_mul (c c' : L ≃ₗ[R] R) (r : R)
    (h : ∀ l, c' l = r * c l) (n : ℕ) (x : tateTwist R L V (n : ℤ)) :
    tateTwistCoordinates c' (n : ℤ) x = r ^ n • tateTwistCoordinates c (n : ℤ) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v l =>
    rw [tateTwistCoordinates_tmul, tateTwistCoordinates_tmul]
    show tensorPowerCoordinates c' n l • v = r ^ n • (tensorPowerCoordinates c n l • v)
    rw [tensorPowerCoordinates_of_coord_eq_mul c c' r h, mul_smul]
  | add x y hx hy => simp [hx, hy, smul_add]

end Coordinates

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']
  {F : Type w} [Field F] {F' : Type w'} [Field F'] [Algebra F F']
  {𝔇 : FirstChernClassData k F} {𝔇' : FirstChernClassData k' F'}

namespace FieldBaseChangeData

variable (B : FieldBaseChangeData 𝔇 𝔇')

/-- **The scalar `μ` relating the two coordinates of `F'(1)`**: the canonical coordinate
`𝔇'.coord` is `μ` times the coordinate induced from `𝔇.coord` by `F(1) ⊗_F F' ≅ F'(1)`. -/
def tateScale : F' :=
  𝔇'.coord ((inducedTateCoordinate 𝔇 𝔇' B.tateEquiv).symm 1)

/-- `𝔇'.coord = μ · c`, `c` the coordinate induced from `𝔇.coord`. -/
theorem coord_eq_tateScale_mul (l : 𝔇'.tate) :
    𝔇'.coord l = B.tateScale * inducedTateCoordinate 𝔇 𝔇' B.tateEquiv l := by
  set c := inducedTateCoordinate 𝔇 𝔇' B.tateEquiv
  have hl : l = c l • c.symm 1 := c.injective (by simp)
  conv_lhs => rw [hl]
  rw [map_smul, smul_eq_mul, mul_comm]
  rfl

/-- `twistHom` in the coordinates `κ` of both sides, in degree `n ≥ 0`. -/
theorem κ_twistHom_natCast (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℕ)
    (a : tateTwist F 𝔇.tate (𝔇.H X) (n : ℤ)) :
    𝔇'.κ ((fieldBaseChange k k').obj X) (n : ℤ) (B.twistHom X (n : ℤ) a) =
      B.tateScale ^ n • B.cohHom X (𝔇.κ X (n : ℤ) a) := by
  rw [FirstChernClassData.κ, tateTwistCoordinates_natCast_of_coord_eq_mul _ _ _
    B.coord_eq_tateScale_mul, tateTwistCoordinates_twistHom]

/-- `cohHom` carries the even part `⨁_{i ≥ 0} H^{2i}(X)` into the even part of
`(H')^*(X_{k'})`. -/
theorem cohHom_mem_evenPart (X : (SmoothProjectiveScheme k).FullSubcategory) {a : 𝔇.H X}
    (ha : a ∈ evenPart (𝔇.grade X)) :
    B.cohHom X a ∈ evenPart (𝔇'.grade ((fieldBaseChange k k').obj X)) := by
  rw [mem_evenPart_iff] at ha ⊢
  induction ha using Submodule.iSup_induction' with
  | mem i x hx => exact Submodule.mem_iSup_of_mem i (B.cohHom_mem_grade X hx)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy

/-- **The first Chern classes in coordinates**: `c₁^{H'}(ℒ_{k'}) = μ · c₁^H(ℒ)` in
`(H')^2(X_{k'})`. -/
theorem coe_c₁A_pullback (X : (SmoothProjectiveScheme k).FullSubcategory)
    (L : ((toScheme k).obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible ((toScheme k).obj X).presheaf
      ((toScheme k).obj X).ringCatSheaf.2 L) :
    ((𝔇'.c₁A ((fieldBaseChange k k').obj X)
        (picardClassOf _ ((Scheme.Modules.pullback (fieldBaseChangeProj X)).obj L)
          (isInvertible_pullback_obj _ L hL)) : 𝔇'.A _) : 𝔇'.H _) =
      B.tateScale • B.cohHom X (𝔇.c₁A X (picardClassOf _ L hL)) := by
  rw [FirstChernClassData.coe_c₁A, FirstChernClassData.coe_c₁A, ← B.twistHom_c₁ X L hL,
    ← pow_one B.tateScale]
  exact B.κ_twistHom_natCast X 1 (𝔇.c₁ X (picardClassOf _ L hL))

/-! ### Injectivity of pullbacks along `F'/F` -/

/-- For a family `cohEquiv`-compatible with `F' ⊗_F -`, injectivity of a finite family of maps
`φ_i` (jointly) passes to `1 ⊗ φ_i`, `F'` being flat over the field `F`. -/
theorem eq_zero_of_forall_lTensor_eq_zero {ι : Type*} [Finite ι] {V : Type*} [AddCommGroup V]
    [Module F V] {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module F (W i)]
    (φ : ∀ i, V →ₗ[F] W i) (hφ : Function.Injective fun v => fun i => φ i v)
    (s : F' ⊗[F] V) (hs : ∀ i, (φ i).lTensor F' s = 0) : s = 0 := by
  classical
  have := Fintype.ofFinite ι
  have hinj : Function.Injective ((LinearMap.pi φ).lTensor F') :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hφ
  refine hinj ((TensorProduct.piRight F F' F' W).injective ?_)
  rw [map_zero, map_zero]
  have key : ∀ t : F' ⊗[F] V, TensorProduct.piRight F F' F' W ((LinearMap.pi φ).lTensor F' t) =
      fun i => (φ i).lTensor F' t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; rfl
    | tmul c v => rfl
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
      funext i
      simp only [Pi.add_apply, map_add]
  rw [key]
  funext i
  exact hs i

/-- **The comparison map on even parts**, `F' ⊗_F A(X) → (H')^*(X_{k'})`, `c ⊗ a ↦ c · a'`. -/
def evenHom (X : (SmoothProjectiveScheme k).FullSubcategory) :
    F' ⊗[F] 𝔇.A X →ₗ[F'] 𝔇'.H ((fieldBaseChange k k').obj X) :=
  (B.cohEquiv X).toLinearEquiv.toLinearMap ∘ₗ
    ((evenPart (𝔇.grade X)).val.toLinearMap.baseChange F')

/-- `evenHom` on pure tensors. -/
theorem evenHom_tmul (X : (SmoothProjectiveScheme k).FullSubcategory) (c : F') (a : 𝔇.A X) :
    B.evenHom X (c ⊗ₜ a) = c • B.cohHom X a := by
  rw [cohHom_apply, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

/-- `evenHom` is injective: `A(X) ⊆ H^*(X)` stays injective after `F' ⊗_F -`, and `cohEquiv` is
an isomorphism. -/
theorem evenHom_injective (X : (SmoothProjectiveScheme k).FullSubcategory) :
    Function.Injective (B.evenHom X) :=
  (B.cohEquiv X).injective.comp (by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)

/-- `evenHom` is natural: it intertwines `1 ⊗ f^*` and `(f_{k'})^*`. -/
theorem pull_evenHom {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
    (s : F' ⊗[F] 𝔇.A Y) :
    𝔇'.pull ((fieldBaseChange k k').map f) (B.evenHom Y s) =
      B.evenHom X ((𝔇.pullA f).toLinearMap.lTensor F' s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul c a =>
    rw [evenHom_tmul, LinearMap.lTensor_tmul, evenHom_tmul, map_smul, ← cohHom_pull]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **The even part of `(H')^*(X_{k'})` is spanned by the image of `A(X)`**: every class of it is
`evenHom` of a tensor. -/
theorem exists_evenHom_eq (X : (SmoothProjectiveScheme k).FullSubcategory)
    {y : 𝔇'.H ((fieldBaseChange k k').obj X)}
    (hy : y ∈ evenPart (𝔇'.grade ((fieldBaseChange k k').obj X))) :
    ∃ s, B.evenHom X s = y := by
  rw [mem_evenPart_iff] at hy
  induction hy using Submodule.iSup_induction' with
  | mem i y hy =>
    let incl : 𝔇.grade X (2 * (i : ℤ)) →ₗ[F] 𝔇.A X :=
      { toFun := fun a => ⟨a, mem_evenPart_of_mem _ a.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine ⟨incl.baseChange F' ((B.gradedEquiv X _).symm ⟨y, hy⟩), ?_⟩
    have h := congrArg Subtype.val ((B.gradedEquiv X _).apply_symm_apply ⟨y, hy⟩)
    rw [coe_gradedEquiv] at h
    refine Eq.trans ?_ h
    have hc : (evenPart (𝔇.grade X)).val.toLinearMap ∘ₗ incl =
        (𝔇.grade X (2 * (i : ℤ))).subtype := rfl
    simp only [evenHom, gradedHom, LinearMap.comp_apply]
    rw [← hc, LinearMap.baseChange_comp, LinearMap.comp_apply]
  | zero => exact ⟨0, map_zero _⟩
  | add y z _ _ hy hz =>
    obtain ⟨s, rfl⟩ := hy
    obtain ⟨t, rfl⟩ := hz
    exact ⟨s + t, map_add _ _ _⟩

/-- **Injectivity of a family of pullbacks on even parts passes to the base change**: if the
`p_i^*` are jointly injective on `A(X)`, the `(p_i)_{k'}^*` are jointly injective on the even
part of `(H')^*(X_{k'})`. -/
theorem eq_zero_of_forall_pull_fieldBaseChange (B : FieldBaseChangeData 𝔇 𝔇') {ι : Type*} [Finite ι]
    {X : (SmoothProjectiveScheme k).FullSubcategory}
    {P : ι → (SmoothProjectiveScheme k).FullSubcategory} (p : ∀ i, P i ⟶ X)
    (hinj : Function.Injective fun a : 𝔇.A X => fun i => 𝔇.pullA (p i) a)
    {y : 𝔇'.H ((fieldBaseChange k k').obj X)}
    (hy : y ∈ evenPart (𝔇'.grade ((fieldBaseChange k k').obj X)))
    (h : ∀ i, 𝔇'.pull ((fieldBaseChange k k').map (p i)) y = 0) : y = 0 := by
  obtain ⟨s, rfl⟩ := B.exists_evenHom_eq X hy
  have hs : s = 0 := by
    refine eq_zero_of_forall_lTensor_eq_zero (fun i => (𝔇.pullA (p i)).toLinearMap) hinj s
      fun i => B.evenHom_injective (P i) ?_
    rw [← pull_evenHom, h i, map_zero]
  rw [hs, map_zero]

/-! ### The cohomological Chern characters -/

section ChernCharacter

variable [CharZero F] [CharZero F']
  (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom) (hA1' : 𝔇'.CoproductAxiom)
  (hA3' : 𝔇'.ProjectiveBundleAxiom)
  {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}
  {ch' : ∀ X : (SmoothProjectiveScheme k').FullSubcategory,
    VectorBundleKZero ((toScheme k').obj X) → ∀ n : ℕ, tateTwist F' 𝔇'.tate (𝔇'.H X) n}
  (h : 𝔇.IsCohomologicalChernCharacter ch) (h' : 𝔇'.IsCohomologicalChernCharacter ch')

omit [CharZero F'] in
/-- The image of a rational number in `A(X)`, read in `H^*(X)`. -/
theorem coe_algebraMap_rat_A (𝔇 : FirstChernClassData k F)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (q : ℚ) :
    ((algebraMap ℚ (𝔇.A X) q : 𝔇.A X) : 𝔇.H X) = algebraMap ℚ F q • (1 : 𝔇.H X) := by
  show ((algebraMap F (𝔇.A X) (algebraMap ℚ F q) : 𝔇.A X) : 𝔇.H X) = _
  rw [Algebra.algebraMap_eq_smul_one, Subalgebra.coe_smul, OneMemClass.coe_one]

omit [CharZero F'] in
/-- The degree `n` part of `exp(c₁^H(ℒ))`, read in `H^*(X)`: `(1/n!) c₁^H(ℒ)ⁿ`. -/
theorem coe_coeff_expFirstChernClass (𝔇 : FirstChernClassData k F) (hA1 : 𝔇.CoproductAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (X : (SmoothProjectiveScheme k).FullSubcategory)
    (L : ((toScheme k).obj X).picardGroup) (n : ℕ) :
    ((PowerSeries.coeff n (Weak.expFirstChernClass (𝔇.toChernSetup hA1 hA3) X L) : 𝔇.A X) :
      𝔇.H X) = algebraMap ℚ F ((n.factorial : ℚ)⁻¹) • ((𝔇.c₁A X L : 𝔇.A X) : 𝔇.H X) ^ n := by
  refine (congrArg (fun z : 𝔇.A X => (z : 𝔇.H X))
    (Weak.coeff_expFirstChernClass (𝔚 := 𝔇.toChernSetup hA1 hA3) X L n)).trans ?_
  show ((algebraMap ℚ (𝔇.A X) ((n.factorial : ℚ)⁻¹) * 𝔇.c₁A X L ^ n : 𝔇.A X) : 𝔇.H X) = _
  rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_algebraMap_rat_A, smul_one_mul]

/-- **The compatibility of the Chern characters, for one class `α ∈ K₀(Vect(X))`**: the degree
`n` part of `ch^{H'}((X_{k'} → X)^*α)` is `μⁿ` times the image of the degree `n` part of
`ch^H(α)`, for every `n`. -/
def ChernCharacterCompat (X : (SmoothProjectiveScheme k).FullSubcategory)
    (α : VectorBundleKZero ((toScheme k).obj X)) : Prop :=
  ∀ n : ℕ, ((PowerSeries.coeff n (h'.lift ((fieldBaseChange k k').obj X)
        (VectorBundleKZero.pullbackRingHom (fieldBaseChangeProj X) α)) :
        𝔇'.A _) : 𝔇'.H _) =
    B.tateScale ^ n • B.cohHom X
      (PowerSeries.coeff n (h.lift X α) : 𝔇.A X)

/-- The compatibility holds for `0`. -/
theorem chernCharacterCompat_zero (X : (SmoothProjectiveScheme k).FullSubcategory) :
    B.ChernCharacterCompat h h' X 0 := fun n => by simp

/-- The compatibility is additive. -/
theorem chernCharacterCompat_add {X : (SmoothProjectiveScheme k).FullSubcategory}
    {α β : VectorBundleKZero ((toScheme k).obj X)}
    (hα : B.ChernCharacterCompat h h' X α)
    (hβ : B.ChernCharacterCompat h h' X β) :
    B.ChernCharacterCompat h h' X (α + β) := fun n => by
  simp only [map_add, Subalgebra.coe_add, hα n, hβ n, smul_add]

/-- The compatibility holds for finite sums. -/
theorem chernCharacterCompat_sum {X : (SmoothProjectiveScheme k).FullSubcategory} {ι : Type*}
    (s : Finset ι) {α : ι → VectorBundleKZero ((toScheme k).obj X)}
    (hα : ∀ i ∈ s, B.ChernCharacterCompat h h' X (α i)) :
    B.ChernCharacterCompat h h' X (∑ i ∈ s, α i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact B.chernCharacterCompat_zero h h' X
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact B.chernCharacterCompat_add h h'
      (hα i (Finset.mem_insert_self i s)) (ih fun j hj => hα j (Finset.mem_insert_of_mem hj))

/-- A module of finite locally free rank `r` is finite locally free. -/
private theorem isFiniteLocallyFree_of_rank {X : Scheme.{u}} {E : X.Modules} {r : ℕ}
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E :=
  (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).mpr
    hE.isFiniteLocallyFree

include hA1 hA3 hA1' hA3' in
/-- **The Chern characters agree on invertible modules**, from the agreement of first Chern
classes: `ch^{H'}(ℒ_{k'}) = exp(μ c₁^H(ℒ))`, whose degree `n` part is `μⁿ` times that of
`ch^H(ℒ) = exp(c₁^H(ℒ))`. -/
theorem chernCharacterCompat_classOf_invertible (X : (SmoothProjectiveScheme k).FullSubcategory)
    (L : ((toScheme k).obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible ((toScheme k).obj X).presheaf
      ((toScheme k).obj X).ringCatSheaf.2 L) :
    B.ChernCharacterCompat h h' X
      (VectorBundleKZero.classOf _ L) := fun n => by
  have := hL
  rw [VectorBundleKZero.pullbackRingHom_classOf _ L
      (isFiniteLocallyFree_of_rank (r := 1) inferInstance),
    h'.lift_classOf hA1' hA3' _ _ (isInvertible_pullback_obj _ L hL),
    h.lift_classOf hA1 hA3 X L hL,
    coe_coeff_expFirstChernClass, coe_coeff_expFirstChernClass, B.coe_c₁A_pullback,
    B.cohHom_smul, map_pow, smul_pow, eq_ratCast (algebraMap ℚ F), map_ratCast,
    ← eq_ratCast (algebraMap ℚ F'), smul_comm]

/-- `K₀` pullbacks along `X_{k'} → X` are natural. -/
theorem pullbackRingHom_fieldBaseChangeProj_comm {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) (α : VectorBundleKZero ((toScheme k).obj Y)) :
    VectorBundleKZero.pullbackRingHom ((toScheme k').map ((fieldBaseChange k k').map f))
        (VectorBundleKZero.pullbackRingHom (fieldBaseChangeProj Y) α) =
      VectorBundleKZero.pullbackRingHom (fieldBaseChangeProj X)
        (VectorBundleKZero.pullbackRingHom ((toScheme k).map f) α) := by
  rw [← VectorBundleKZero.pullbackRingHom_comp_apply,
    ← VectorBundleKZero.pullbackRingHom_comp_apply, fieldBaseChange_map_comp_proj]

omit [CharZero F'] in
/-- The degree `n` part of `ch^H`, pulled back. -/
theorem pull_coe_coeff_cohomologicalChernCharacter {𝔈 : FirstChernClassData k F}
    {χ : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
      VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ, tateTwist F 𝔈.tate (𝔈.H X) n}
    (hχ : 𝔈.IsCohomologicalChernCharacter χ) {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) (α : VectorBundleKZero ((toScheme k).obj Y)) (n : ℕ) :
    𝔈.pull f ((PowerSeries.coeff n (hχ.lift Y α) : 𝔈.A Y) : 𝔈.H Y) =
      ((PowerSeries.coeff n (hχ.lift X
        (VectorBundleKZero.pullbackRingHom ((toScheme k).map f) α)) : 𝔈.A X) : 𝔈.H X) := by
  rw [← hχ.map_lift, PowerSeries.coeff_map]
  rfl

/-- **Descent along a jointly injective finite family**: the compatibility for `α` follows from
that for its pullbacks along finitely many morphisms whose pullbacks are jointly injective on
`A(X)`, those pullbacks staying jointly injective after base change. -/
theorem chernCharacterCompat_of_pull {ι : Type*} [Finite ι]
    {X : (SmoothProjectiveScheme k).FullSubcategory}
    {P : ι → (SmoothProjectiveScheme k).FullSubcategory} (p : ∀ i, P i ⟶ X)
    (hinj : Function.Injective fun a : 𝔇.A X => fun i => 𝔇.pullA (p i) a)
    {α : VectorBundleKZero ((toScheme k).obj X)}
    (hc : ∀ i, B.ChernCharacterCompat h h' (P i)
      (VectorBundleKZero.pullbackRingHom ((toScheme k).map (p i)) α)) :
    B.ChernCharacterCompat h h' X α := fun n => by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_pull_fieldBaseChange B p hinj
    (sub_mem (SetLike.coe_mem _)
      (Subalgebra.smul_mem _ (B.cohHom_mem_evenPart X (SetLike.coe_mem _)) _))
    fun i => ?_
  rw [map_sub, sub_eq_zero, map_smul, ← B.cohHom_pull,
    pull_coe_coeff_cohomologicalChernCharacter, pull_coe_coeff_cohomologicalChernCharacter,
    pullbackRingHom_fieldBaseChangeProj_comm]
  exact hc i n

include hA1 hA3 hA1' hA3' in
/-- **The compatibility for a module of constant rank**, by the splitting principle: on a
projective bundle tower `p : P → X` with `p^*` injective, `p^*ℰ` has a filtration with invertible
graded pieces, whose classes add up to `[p^*ℰ]`. -/
theorem chernCharacterCompat_classOf_of_rank (X : (SmoothProjectiveScheme k).FullSubcategory)
    (E : ((toScheme k).obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) :
    B.ChernCharacterCompat h h' X
      (VectorBundleKZero.classOf _ E) := by
  obtain ⟨P, p, -, hinj, hfil⟩ := (𝔇.toChernSetup hA1 hA3).exists_injective_hasInvertibleFiltration
    X Unit (fun _ => E) (fun _ => r) fun _ => hE
  obtain ⟨-, L, hL, hsum⟩ := (hfil ()).exists_classOf_eq_sum
  refine B.chernCharacterCompat_of_pull h h' (fun _ : Unit => p)
    (fun a b hab => hinj (congrFun hab ())) fun _ => ?_
  rw [VectorBundleKZero.pullbackRingHom_classOf _ E (isFiniteLocallyFree_of_rank hE), hsum]
  exact B.chernCharacterCompat_sum h h' _ fun j _ =>
    B.chernCharacterCompat_classOf_invertible hA1 hA3 hA1' hA3' h h' P (L j) (hL j)

include hA1 hA3 hA1' hA3' in
/-- **The compatibility for a finite locally free module**, reduced to constant rank on the
finitely many open and closed loci where the rank is constant, restriction to which is jointly
injective on `A(X)` by (A1). -/
theorem chernCharacterCompat_classOf (X : (SmoothProjectiveScheme k).FullSubcategory)
    (E : ((toScheme k).obj X).Modules)
    (hE : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E) :
    B.ChernCharacterCompat h h' X
      (VectorBundleKZero.classOf _ E) := by
  obtain ⟨ι, _, P, p, r, -, hrank, hinj⟩ := (𝔇.toChernSetup hA1 hA3).exists_clopenRankPieces X E
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).mp hE)
  refine B.chernCharacterCompat_of_pull h h' p hinj fun i => ?_
  rw [VectorBundleKZero.pullbackRingHom_classOf _ E hE]
  exact B.chernCharacterCompat_classOf_of_rank hA1 hA3 hA1' hA3' h h' (P i) _ (r i)
    (hrank i)

include hA1 hA3 hA1' hA3' in
/-- **The cohomological Chern characters are compatible with the base change** (the step of
the proof of Tag 0FVT reducing the comparison of `γ` and `γ'` to Chern classes): for
`α ∈ K₀(Vect(X))` the degree `n` part of `ch^{H'}((X_{k'} → X)^*α)` is `μⁿ` times the image of the
degree `n` part of `ch^H(α)`, `μ` relating the coordinates of `F'(1)` (`tateScale`). -/
theorem coe_coeff_cohomologicalChernCharacter_pullback
    (X : (SmoothProjectiveScheme k).FullSubcategory)
    (α : VectorBundleKZero ((toScheme k).obj X)) (n : ℕ) :
    ((PowerSeries.coeff n (h'.lift ((fieldBaseChange k k').obj X)
        (VectorBundleKZero.pullbackRingHom (fieldBaseChangeProj X) α)) :
        𝔇'.A _) : 𝔇'.H _) =
    B.tateScale ^ n • B.cohHom X
      (PowerSeries.coeff n (h.lift X α) : 𝔇.A X) := by
  let φ : VectorBundleKZero ((toScheme k).obj X) →+ 𝔇'.H ((fieldBaseChange k k').obj X) :=
    AddMonoidHom.mk' (fun α => ((PowerSeries.coeff n (h'.lift ((fieldBaseChange k k').obj X)
        (VectorBundleKZero.pullbackRingHom (fieldBaseChangeProj X) α)) : 𝔇'.A _) : 𝔇'.H _))
      fun a b => by simp only [map_add, Subalgebra.coe_add]
  let ψ : VectorBundleKZero ((toScheme k).obj X) →+ 𝔇'.H ((fieldBaseChange k k').obj X) :=
    AddMonoidHom.mk' (fun α => B.tateScale ^ n • B.cohHom X
      (PowerSeries.coeff n (h.lift X α) : 𝔇.A X))
      fun a b => by simp only [map_add, Subalgebra.coe_add, smul_add]
  have hφψ : φ = ψ := VectorBundleKZero.addHom_ext fun M hM =>
    B.chernCharacterCompat_classOf hA1 hA3 hA1' hA3' h h' X M hM n
  exact DFunLike.congr_fun hφψ α

include hA1 hA3 hA1' hA3' in
/-- **The compatibility of the Chern characters on `K₀(Vect(X)) ⊗ 𝐐`**: the degree `n` part of
`ch^{H'}((X_{k'} → X)^*a)` is `μⁿ` times the image of the degree `n` part of `ch^H(a)`. -/
theorem coe_coeff_rationalCohomologicalChernCharacter_pullback
    (X : (SmoothProjectiveScheme k).FullSubcategory)
    (a : ℚ ⊗[ℤ] VectorBundleKZero ((toScheme k).obj X)) (n : ℕ) :
    ((PowerSeries.coeff n (h'.rationalLift ((fieldBaseChange k k').obj X)
        ((VectorBundleKZero.pullback (fieldBaseChangeProj X)).toIntLinearMap.baseChange ℚ a)) :
        𝔇'.A _) : 𝔇'.H _) =
    B.tateScale ^ n • B.cohHom X (PowerSeries.coeff n (h.rationalLift X a) : 𝔇.A X) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, Subalgebra.coe_add, ha, hb, smul_add]
  | tmul q α =>
    rw [LinearMap.baseChange_tmul, h'.rationalLift_tmul, h.rationalLift_tmul,
      PowerSeries.coeff_smul, PowerSeries.coeff_smul,
      FirstChernClassData.rat_smul_A, FirstChernClassData.rat_smul_A, Subalgebra.coe_smul,
      Subalgebra.coe_smul, B.cohHom_smul, AddMonoidHom.coe_toIntLinearMap,
      VectorBundleKZero.pullback_eq_pullbackRingHom _ α]
    show algebraMap ℚ F' q • ((PowerSeries.coeff n (h'.lift ((fieldBaseChange k k').obj X)
        (VectorBundleKZero.pullbackRingHom (fieldBaseChangeProj X) α)) :
          𝔇'.A ((fieldBaseChange k k').obj X)) : 𝔇'.H ((fieldBaseChange k k').obj X)) = _
    rw [B.coe_coeff_cohomologicalChernCharacter_pullback hA1 hA3 hA1' hA3' h h' X α n,
      eq_ratCast (algebraMap ℚ F), map_ratCast,
      ← eq_ratCast (algebraMap ℚ F'), smul_comm]

/-! ### The cycle class maps -/

include hA1 hA3 hA1' hA3' in
/-- **The cycle class maps `γ` and `γ'` are compatible with the base change** (the step of the
proof of Tag 0FVT before (A6)): the square

  `CH^i(X)      --γ-->  H^*(X)(i)`
  `   | g^*                 |`
  `CH^i(X_{k'}) --γ'--> (H')^*(X_{k'})(i)`

commutes, `γ`, `γ'` the cycle class maps of Lemma 0FIF of the cohomological Chern characters
`h`, `h'`
(`Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter.codimensionCycleClass`)
and the right vertical arrow the comparison map `twistHom` on twisted classes. Write the class of
`α` in `CH^*(X) ⊗ 𝐐` as `ch(β) ∩ [X]`, so that `γ(α) = ch^H(β)`; then
`g^*α = ch((X_{k'} → X)^*β) ∩ [X_{k'}]`
(`Stacks.WeilDeRham.rationalChowRingBaseChange_rationalChernCharacterEquiv`) and
`γ'(g^*α) = ch^{H'}((X_{k'} → X)^*β)`, which is the image of `ch^H(β)`
(`coe_coeff_rationalCohomologicalChernCharacter_pullback`). -/
theorem twistHom_cycleClass (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℕ)
    (α : codimensionChowGroup k X.obj.hom i) :
    B.twistHom X i (h.codimensionCycleClass X i α) =
      h'.codimensionCycleClass ((fieldBaseChange k k').obj X) i (chowCodimBaseChange X i α) := by
  apply (𝔇'.κ ((fieldBaseChange k k').obj X) (i : ℤ)).injective
  rw [B.κ_twistHom_natCast X i, h.codimensionCycleClass_apply, h'.codimensionCycleClass_apply,
    codimensionClass_chowCodimBaseChange]
  obtain ⟨a, ha⟩ := (rationalChernCharacterAlgEquiv (isRegular_of_smooth_over_field X.obj.hom)
    (exists_bounds_relativeDimension_fieldChowSituation k X.obj.hom)).surjective
      (smoothChowEquiv X.obj.hom (codimensionToRationalChow k X.obj.hom i α))
  rw [← ha, rationalChowRingBaseChange_rationalChernCharacterEquiv,
    FirstChernClassData.IsCohomologicalChernCharacter.cycleClassMap,
    FirstChernClassData.IsCohomologicalChernCharacter.cycleClassMap, AlgEquiv.symm_apply_apply,
    AlgEquiv.symm_apply_apply, FirstChernClassData.κ_twistRule, FirstChernClassData.κ_twistRule]
  exact (B.coe_coeff_rationalCohomologicalChernCharacter_pullback hA1 hA3 hA1' hA3' h h' X a
    i).symm

end ChernCharacter

end FieldBaseChangeData

end Stacks.WeilDeRham

end
