module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PermutationModuleCount

/-!
# Functors killing the non-invariant part of the permutation module of a torsor

Let `G` be a topological group acting continuously on a finite set `Y`, and let a finite abelian
group `K` act on `Y` by `τ`, commuting with `G` and simply transitively, with `#K` invertible in
`ℤ/m`. On the permutation module `ℤ/m[Y] ⊗ ℤ/m^A` the average over `K`,
`e φ = #K⁻¹ ∑_{a ∈ K} φ ∘ τ_a`, is a `G`-equivariant idempotent whose image is the constants.

Let `T` be a functor from finite continuous `G`-modules to `ℤ/m`-modules. If `T(ℤ/m[Y])` is
finite with as many elements as `T(ℤ/m)` (`ℤ/m` with the trivial action), then `T(e) = 1`
on `T(ℤ/m[Y])`: `e` factors as the scaled augmentation `ℤ/m[Y] → ℤ/m` followed by the
constants `ℤ/m → ℤ/m[Y]`, whose composite the other way is the identity, so `T` of the
constants is injective, hence bijective by counting. For `T` additive the same holds for
`ℤ/m[Y] ⊗ ℤ/m^A`, a sum of copies of `ℤ/m[Y]`.

Consequently `T` kills every finite free `ℤ/m`-module `M` on which `G` acts through the character
`κ : G → K` of the torsor, by an action `ρ` of `K` without invariants (`∑_a ρ(a) = 0`): such an
`M` is a retract of `ℤ/m[Y] ⊗ M` through maps killed by `e`.

For the Artin–Schreier cover of the affine line and `T = Hⁱ_c(𝔸¹_k̄, ℱ_-)` this is the vanishing
of `Hⁱ_c(𝔸¹_k̄, L_ψ)` for a nontrivial additive character `ψ`, the kernel computation of the
`ℓ`-adic Fourier transform ([Laumon, 1.2.2]; [SGA 4½, Sommes trig., 2.7]): the cover is again an
affine line, so `T` has the same size on `ℤ/m[Y]` and on `ℤ/m`.

## Main definitions

* `Stacks.EtaleCohomology.permAverage`: the average `e` over the translations.
* `Stacks.EtaleCohomology.permConst`, `Stacks.EtaleCohomology.permAugment`: the constants and the
  scaled augmentation.

## Main results

* `Stacks.EtaleCohomology.map_permAverage_eq_id_of_natCard_eq`: `T(e) = 1` on `T(ℤ/m[Y])`.
* `Stacks.EtaleCohomology.map_permAverage_eq_id_of_additive`: `T(e) = 1` on `T(ℤ/m[Y] ⊗ ℤ/m^A)`.
* `Stacks.EtaleCohomology.subsingleton_obj_of_torsor_character`: `T(M) = 0`.

## References

* [G. Laumon, Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de
  Weil, 1.2]
* [P. Deligne, SGA 4½, Sommes trigonométriques, 2.7]
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

section Average

variable {G : Type (u + 1)} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (m : ℕ)
  [NeZero m] {Y : Type u} [Fintype Y] [MulAction G Y]
  (hY : ∀ y : Y, IsOpen (MulAction.stabilizer G y : Set G))
  {K : Type*} [AddCommGroup K] [Fintype K] (hK : IsUnit (Fintype.card K : ZMod m))
  (τ : K → Y → Y) (hτ : ∀ (a : K) (g : G) (y : Y), τ a (g • y) = g • τ a y)

/-- `#K⁻¹` in `ℤ/m`. -/
abbrev torsorCardInv : ZMod m := ((hK.unit⁻¹ : (ZMod m)ˣ) : ZMod m)

omit [NeZero m] [AddCommGroup K] in
/-- `#K⁻¹ * #K = 1` in `ℤ/m`. -/
theorem torsorCardInv_mul : torsorCardInv m hK * (Fintype.card K : ZMod m) = 1 :=
  hK.val_inv_mul

/-- **The average over the translations** `e φ = #K⁻¹ ∑_{a ∈ K} φ ∘ τ_a` on the permutation
module `ℤ/m[Y] ⊗ ℤ/m^A`, a `G`-equivariant endomorphism. -/
def permAverage (A : Type (u + 1)) [Fintype A] : permModule m A hY ⟶ permModule m A hY :=
  finiteTypeContinuousModuleHomMk m
    { toFun := fun φ => ⟨fun y a => torsorCardInv m hK * ∑ b : K, φ.down (τ b y) a⟩
      map_add' := fun φ ψ => by
        apply ULift.ext
        funext y a
        change torsorCardInv m hK * ∑ b : K, (φ.down (τ b y) a + ψ.down (τ b y) a) =
          torsorCardInv m hK * ∑ b : K, φ.down (τ b y) a +
            torsorCardInv m hK * ∑ b : K, ψ.down (τ b y) a
        rw [Finset.sum_add_distrib, mul_add]
      map_smul' := fun c φ => by
        apply ULift.ext
        funext y a
        change torsorCardInv m hK * ∑ b : K, c * φ.down (τ b y) a =
          c * (torsorCardInv m hK * ∑ b : K, φ.down (τ b y) a)
        rw [← Finset.mul_sum]
        ring }
    (fun g φ => by
      apply ULift.ext
      funext y a
      change torsorCardInv m hK * ∑ b : K, φ.down (g⁻¹ • τ b y) a =
        torsorCardInv m hK * ∑ b : K, φ.down (τ b (g⁻¹ • y)) a
      simp only [hτ])

omit [AddCommGroup K] in
/-- The value of the average at `(y, a)` is `#K⁻¹ ∑_{b ∈ K} φ(τ_b y, a)`. -/
theorem permAverage_apply (A : Type (u + 1)) [Fintype A] (φ : ULift.{u + 1} (Y → A → ZMod m))
    (y : Y) (a : A) :
    ((permAverage m hY hK τ hτ A).hom.hom.hom.hom.hom φ).down y a =
      torsorCardInv m hK * ∑ b : K, φ.down (τ b y) a :=
  rfl

/-- **The constants** `ℤ/m → ℤ/m[Y]`. -/
def permConst : trivialContinuousModule m ⟶ permModule m PUnit.{u + 2} hY :=
  finiteTypeContinuousModuleHomMk m
    { toFun := fun c => ⟨fun _ _ => c.down⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (fun _ _ => rfl)

/-- **The scaled augmentation** `φ ↦ #K⁻¹ ∑_y φ(y)` from `ℤ/m[Y]` to `ℤ/m`. -/
def permAugment : permModule m PUnit.{u + 2} hY ⟶ trivialContinuousModule m :=
  finiteTypeContinuousModuleHomMk m
    { toFun := fun φ => ⟨torsorCardInv m hK * ∑ y : Y, φ.down y PUnit.unit⟩
      map_add' := fun φ ψ => by
        apply ULift.ext
        change torsorCardInv m hK * ∑ y : Y, (φ.down y PUnit.unit + ψ.down y PUnit.unit) =
          torsorCardInv m hK * ∑ y : Y, φ.down y PUnit.unit +
            torsorCardInv m hK * ∑ y : Y, ψ.down y PUnit.unit
        rw [Finset.sum_add_distrib, mul_add]
      map_smul' := fun c φ => by
        apply ULift.ext
        change torsorCardInv m hK * ∑ y : Y, c * φ.down y PUnit.unit =
          c * (torsorCardInv m hK * ∑ y : Y, φ.down y PUnit.unit)
        rw [← Finset.mul_sum]
        ring }
    (fun g φ => by
      apply ULift.ext
      change torsorCardInv m hK * ∑ y : Y, φ.down (g⁻¹ • y) PUnit.unit =
        torsorCardInv m hK * ∑ y : Y, φ.down y PUnit.unit
      congr 1
      exact Fintype.sum_equiv (MulAction.toPerm g⁻¹) _ _ fun _ => rfl)

variable (htr : ∀ y y' : Y, ∃! a : K, τ a y = y')

omit [Fintype Y] [AddCommGroup K] [Fintype K] in
include htr in
/-- On a torsor, `b ↦ τ_b y` is a bijection `K ≃ Y`. -/
theorem bijective_torsor_apply (y : Y) : Function.Bijective fun b : K => τ b y :=
  ⟨fun _ _ h => (htr y _).unique rfl h.symm, fun y' => (htr y y').exists⟩

omit [AddCommGroup K] in
include htr in
/-- On a torsor, `∑_{b ∈ K} f(τ_b y) = ∑_{y' ∈ Y} f(y')`. -/
theorem sum_torsor_apply {R : Type*} [AddCommMonoid R] (f : Y → R) (y : Y) :
    ∑ b : K, f (τ b y) = ∑ y' : Y, f y' :=
  Fintype.sum_bijective _ (bijective_torsor_apply τ htr y) _ _ fun _ => rfl

omit [AddCommGroup K] in
include htr in
/-- A nonempty torsor under `K` has as many elements as `K`. -/
theorem card_eq_of_torsor [Nonempty Y] : Fintype.card K = Fintype.card Y :=
  Fintype.card_of_bijective (bijective_torsor_apply τ htr (Classical.arbitrary Y))

omit [AddCommGroup K] in
include htr in
/-- The constants followed by the scaled augmentation is the identity of `ℤ/m`. -/
theorem permConst_comp_permAugment [Nonempty Y] :
    permConst m hY ≫ permAugment m hY hK = 𝟙 _ :=
  finiteTypeContinuousModule_hom_ext m fun c => by
    apply ULift.ext
    show torsorCardInv m hK * ∑ _y : Y, c.down = c.down
    rw [Finset.sum_const, Finset.card_univ, ← card_eq_of_torsor τ htr, nsmul_eq_mul,
      ← mul_assoc, torsorCardInv_mul, one_mul]

omit [AddCommGroup K] in
include htr in
/-- The scaled augmentation followed by the constants is the average over the translations. -/
theorem permAugment_comp_permConst :
    permAugment m hY hK ≫ permConst m hY = permAverage m hY hK τ hτ PUnit.{u + 2} :=
  finiteTypeContinuousModule_hom_ext m fun φ => by
    apply ULift.ext
    funext y a
    show torsorCardInv m hK * ∑ y' : Y, φ.down y' PUnit.unit =
      torsorCardInv m hK * ∑ b : K, φ.down (τ b y) a
    rw [sum_torsor_apply τ htr (fun y' => φ.down y' a) y]

omit [AddCommGroup K] in
include htr in
/-- **`T(e) = 1` on `T(ℤ/m[Y])`** when `T(ℤ/m[Y])` is finite with as many elements as `T(ℤ/m)`:
`T` of the constants is a section of `T` of the augmentation, hence injective, hence bijective. -/
theorem map_permAverage_eq_id_of_natCard_eq [Nonempty Y]
    (T : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) G ⥤ ModuleCat.{u + 1} (ZMod m))
    [Finite (T.obj (permModule m PUnit.{u + 2} hY))]
    (hcard : Nat.card (T.obj (permModule m PUnit.{u + 2} hY)) =
      Nat.card (T.obj (trivialContinuousModule m))) :
    T.map (permAverage m hY hK τ hτ PUnit.{u + 2}) = 𝟙 _ := by
  have hsc : ∀ x, (T.map (permAugment m hY hK)).hom ((T.map (permConst m hY)).hom x) = x :=
    fun x => by
      rw [← ModuleCat.comp_apply, ← T.map_comp, permConst_comp_permAugment m hY hK τ htr,
        T.map_id]
      rfl
  have hinj : Function.Injective (T.map (permConst m hY)).hom :=
    Function.LeftInverse.injective hsc
  have : Finite (T.obj (trivialContinuousModule m)) := Finite.of_injective _ hinj
  rw [← permAugment_comp_permConst m hY hK τ hτ htr, T.map_comp]
  ext x
  obtain ⟨z, rfl⟩ := (hinj.bijective_of_nat_card_le hcard.le).2 x
  exact congrArg (T.map (permConst m hY)).hom (hsc z)

omit [IsTopologicalGroup G] [NeZero m] in
/-- The difference of two morphisms of finite continuous modules is computed pointwise. -/
theorem finiteTypeContinuousModule_sub_apply
    {P Q : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) G} (f g : P ⟶ Q)
    (x : P.obj.obj.obj.V) :
    (f - g).hom.hom.hom.hom.hom x = f.hom.hom.hom.hom.hom x - g.hom.hom.hom.hom.hom x :=
  rfl

/-- The inclusion `ℤ/m[Y] → ℤ/m[Y] ⊗ ℤ/m^A` of the summand of `a ∈ A`. -/
def permSummandIncl {A : Type (u + 1)} [Fintype A] [DecidableEq A] (a : A) :
    permModule m PUnit.{u + 2} hY ⟶ permModule m A hY :=
  finiteTypeContinuousModuleHomMk m
    { toFun := fun φ => ⟨fun y a' => if a' = a then φ.down y PUnit.unit else 0⟩
      map_add' := fun φ ψ => by
        apply ULift.ext
        funext y a'
        change (if a' = a then φ.down y PUnit.unit + ψ.down y PUnit.unit else 0) =
          (if a' = a then φ.down y PUnit.unit else 0) + (if a' = a then ψ.down y PUnit.unit else 0)
        split_ifs <;> simp
      map_smul' := fun c φ => by
        apply ULift.ext
        funext y a'
        change (if a' = a then c * φ.down y PUnit.unit else 0) =
          c * (if a' = a then φ.down y PUnit.unit else 0)
        split_ifs <;> simp }
    (fun _ _ => rfl)

/-- The projection `ℤ/m[Y] ⊗ ℤ/m^A → ℤ/m[Y]` onto the summand of `a ∈ A`. -/
def permSummandProj {A : Type (u + 1)} [Fintype A] (a : A) :
    permModule m A hY ⟶ permModule m PUnit.{u + 2} hY :=
  finiteTypeContinuousModuleHomMk m
    { toFun := fun φ => ⟨fun y _ => φ.down y a⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (fun _ _ => rfl)

omit [AddCommGroup K] in
include htr in
/-- **`T(e) = 1` on `T(ℤ/m[Y] ⊗ ℤ/m^A)`** for an additive `T` satisfying the hypotheses of
`Stacks.EtaleCohomology.map_permAverage_eq_id_of_natCard_eq`: the permutation module is the sum
of the copies `ℤ/m[Y]` indexed by `A`, compatibly with the averages. -/
theorem map_permAverage_eq_id_of_additive [Nonempty Y]
    (T : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) G ⥤ ModuleCat.{u + 1} (ZMod m))
    [T.Additive] [Finite (T.obj (permModule m PUnit.{u + 2} hY))]
    (hcard : Nat.card (T.obj (permModule m PUnit.{u + 2} hY)) =
      Nat.card (T.obj (trivialContinuousModule m)))
    (A : Type (u + 1)) [Fintype A] [DecidableEq A] :
    T.map (permAverage m hY hK τ hτ A) = 𝟙 _ := by
  have hdec : 𝟙 (permModule m A hY) - permAverage m hY hK τ hτ A =
      ∑ a : A, permSummandProj m hY a ≫ (𝟙 _ - permAverage m hY hK τ hτ PUnit.{u + 2}) ≫
        permSummandIncl m hY a := by
    refine finiteTypeContinuousModule_hom_ext m fun φ => ?_
    rw [finiteTypeContinuousModule_sum_apply]
    apply ULift.ext
    funext y a'
    refine Eq.trans ?_ (ulift_down_sum_apply m Finset.univ (fun i =>
      ((permSummandProj m hY i ≫ (𝟙 _ - permAverage m hY hK τ hτ PUnit.{u + 2}) ≫
        permSummandIncl m hY i).hom.hom.hom.hom.hom φ)) y a').symm
    show φ.down y a' - torsorCardInv m hK * ∑ b : K, φ.down (τ b y) a' =
      ∑ i : A, (if a' = i then φ.down y i - torsorCardInv m hK * ∑ b : K, φ.down (τ b y) i
        else 0)
    rw [Finset.sum_ite_eq]
    simp
  have h0 : T.map (𝟙 (permModule m A hY) - permAverage m hY hK τ hτ A) = 0 := by
    rw [hdec, T.map_sum]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [T.map_comp, T.map_comp, T.map_sub,
      map_permAverage_eq_id_of_natCard_eq m hY hK τ hτ htr T hcard, T.map_id, sub_self,
      Limits.zero_comp, Limits.comp_zero]
  rwa [T.map_sub, T.map_id, sub_eq_zero, eq_comm] at h0

/-! ### Modules on which `G` acts through the character of the torsor -/

section Character

variable (hτadd : ∀ (a b : K) (y : Y), τ (a + b) y = τ a (τ b y)) (y₀ : Y)

/-- The element of `K` carrying the base point `y₀` to `y`. -/
def torsorDiff (y : Y) : K := (htr y₀ y).exists.choose

omit [Fintype Y] [AddCommGroup K] [Fintype K] in
/-- `torsorDiff τ htr y₀ y` carries `y₀` to `y`. -/
theorem torsor_apply_torsorDiff (y : Y) : τ (torsorDiff τ htr y₀ y) y₀ = y :=
  (htr y₀ y).exists.choose_spec

omit [Fintype Y] [AddCommGroup K] [Fintype K] in
/-- `torsorDiff τ htr y₀ y` is the unique element of `K` carrying `y₀` to `y`. -/
theorem torsorDiff_eq {y : Y} {a : K} (h : τ a y₀ = y) : torsorDiff τ htr y₀ y = a :=
  (htr y₀ y).unique (torsor_apply_torsorDiff τ htr y₀ y) h

omit [Fintype Y] [Fintype K] in
include hτadd in
/-- For an additive action, with `δ = torsorDiff τ htr y₀`, `δ(τ_a y) = a + δ(y)`. -/
theorem torsorDiff_apply (a : K) (y : Y) :
    torsorDiff τ htr y₀ (τ a y) = a + torsorDiff τ htr y₀ y :=
  torsorDiff_eq τ htr y₀ (by rw [hτadd, torsor_apply_torsorDiff τ htr y₀ y])

variable (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) G)
  (ρ : Multiplicative K →* Module.End (ZMod m) M.obj.obj.obj.V) (κ : G →* Multiplicative K)
  (hκ : ∀ (g : G) (y : Y), g • y = τ (Multiplicative.toAdd (κ g)) y)
  (hM : ∀ (g : G) (v : M.obj.obj.obj.V), (M.obj.obj.obj.ρ g).asHom.hom v = ρ (κ g) v)
  {ι : Type (u + 1)} [Fintype ι] (bM : Module.Basis ι (ZMod m) M.obj.obj.obj.V)

omit [TopologicalSpace G] [IsTopologicalGroup G] [Fintype Y] [Fintype K] in
include hτadd hκ in
/-- When `G` acts through the character `κ`, with `δ = torsorDiff τ htr y₀`,
`δ(g • y) = κ(g) + δ(y)`. -/
theorem torsorDiff_smul (g : G) (y : Y) :
    torsorDiff τ htr y₀ (g • y) = Multiplicative.toAdd (κ g) + torsorDiff τ htr y₀ y := by
  rw [hκ, torsorDiff_apply τ htr hτadd]

/-- `v ↦ (y ↦ ρ(-δ(y)) v)` from `M` to `ℤ/m[Y] ⊗ M`, written in the basis `bM` of `M`; `δ(y)`
carries `y₀` to `y`. -/
def torsorRetractIncl : M ⟶ permModule m ι hY :=
  finiteTypeContinuousModuleHomMk m
    { toFun := fun v => ⟨fun y i =>
        bM.repr (ρ (Multiplicative.ofAdd (-torsorDiff τ htr y₀ y)) v) i⟩
      map_add' := fun v w => by
        apply ULift.ext
        funext y i
        change bM.repr (ρ _ (v + w)) i = bM.repr (ρ _ v) i + bM.repr (ρ _ w) i
        rw [map_add, map_add, Finsupp.add_apply]
      map_smul' := fun c v => by
        apply ULift.ext
        funext y i
        change bM.repr (ρ _ (c • v)) i = c * bM.repr (ρ _ v) i
        rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul] }
    (fun g v => by
      apply ULift.ext
      funext y i
      change bM.repr (ρ (Multiplicative.ofAdd (-torsorDiff τ htr y₀ y))
          ((M.obj.obj.obj.ρ g).asHom.hom v)) i =
        bM.repr (ρ (Multiplicative.ofAdd (-torsorDiff τ htr y₀ (g⁻¹ • y))) v) i
      have he : Multiplicative.ofAdd (-torsorDiff τ htr y₀ y) * κ g =
          Multiplicative.ofAdd (-torsorDiff τ htr y₀ (g⁻¹ • y)) := by
        rw [torsorDiff_smul τ htr hτadd y₀ κ hκ, map_inv]
        apply Multiplicative.toAdd.injective
        simp only [toAdd_mul, toAdd_ofAdd, toAdd_inv]
        abel
      rw [hM, ← Module.End.mul_apply, ← map_mul, he])

/-- `φ ↦ #K⁻¹ ∑_y ρ(δ(y)) φ(y)` from `ℤ/m[Y] ⊗ M` to `M`, a retraction of
`Stacks.EtaleCohomology.torsorRetractIncl`. -/
def torsorRetractProj : permModule m ι hY ⟶ M :=
  finiteTypeContinuousModuleHomMk m
    { toFun := fun φ => torsorCardInv m hK • ∑ y : Y,
        ρ (Multiplicative.ofAdd (torsorDiff τ htr y₀ y)) (∑ i : ι, φ.down y i • bM i)
      map_add' := fun φ ψ => by
        change torsorCardInv m hK • ∑ y : Y, ρ _ (∑ i : ι, (φ.down y i + ψ.down y i) • bM i) = _
        simp only [add_smul, Finset.sum_add_distrib, map_add, smul_add]
      map_smul' := fun c φ => by
        change torsorCardInv m hK • ∑ y : Y, ρ _ (∑ i : ι, (c * φ.down y i) • bM i) = _
        simp only [mul_smul, ← Finset.smul_sum, map_smul, RingHom.id_apply]
        rw [smul_comm] }
    (fun g φ => by
      change torsorCardInv m hK • ∑ y : Y, ρ (Multiplicative.ofAdd (torsorDiff τ htr y₀ y))
          (∑ i : ι, φ.down (g⁻¹ • y) i • bM i) =
        (M.obj.obj.obj.ρ g).asHom.hom (torsorCardInv m hK • ∑ y : Y,
          ρ (Multiplicative.ofAdd (torsorDiff τ htr y₀ y)) (∑ i : ι, φ.down y i • bM i))
      rw [hM, map_smul, map_sum]
      congr 1
      refine Fintype.sum_equiv (MulAction.toPerm g⁻¹) _ _ fun y => ?_
      change _ = ρ (κ g) (ρ (Multiplicative.ofAdd (torsorDiff τ htr y₀ (g⁻¹ • y))) _)
      have he : κ g * Multiplicative.ofAdd (torsorDiff τ htr y₀ (g⁻¹ • y)) =
          Multiplicative.ofAdd (torsorDiff τ htr y₀ y) := by
        rw [torsorDiff_smul τ htr hτadd y₀ κ hκ, map_inv]
        apply Multiplicative.toAdd.injective
        simp only [toAdd_mul, toAdd_ofAdd, toAdd_inv]
        abel
      rw [← Module.End.mul_apply, ← map_mul, he]
      rfl)

include hτadd hκ hM in
/-- `Stacks.EtaleCohomology.torsorRetractProj` is a retraction of
`Stacks.EtaleCohomology.torsorRetractIncl`. -/
theorem torsorRetractIncl_comp_proj [Nonempty Y] :
    torsorRetractIncl m hY τ htr hτadd y₀ M ρ κ hκ hM bM ≫
      torsorRetractProj m hY hK τ htr hτadd y₀ M ρ κ hκ hM bM = 𝟙 M :=
  finiteTypeContinuousModule_hom_ext m fun v => by
    show torsorCardInv m hK • ∑ y : Y, ρ (Multiplicative.ofAdd (torsorDiff τ htr y₀ y))
      (∑ i : ι, bM.repr (ρ (Multiplicative.ofAdd (-torsorDiff τ htr y₀ y)) v) i • bM i) = v
    simp only [Module.Basis.sum_repr]
    have h : ∀ y : Y, ρ (Multiplicative.ofAdd (torsorDiff τ htr y₀ y))
        (ρ (Multiplicative.ofAdd (-torsorDiff τ htr y₀ y)) v) = v := fun y => by
      rw [← Module.End.mul_apply, ← map_mul, ← ofAdd_add, add_neg_cancel, ofAdd_zero, map_one,
        Module.End.one_apply]
    simp only [h, Finset.sum_const, Finset.card_univ, ← card_eq_of_torsor τ htr]
    rw [← Nat.cast_smul_eq_nsmul (ZMod m), smul_smul, torsorCardInv_mul, one_smul]

variable (hfix : ∀ v, ∑ a : K, ρ (Multiplicative.ofAdd a) v = 0)

include hτadd hfix in
/-- When `K` acts on `M` without invariants, `Stacks.EtaleCohomology.torsorRetractIncl` followed by
the average over the translations is zero. -/
theorem torsorRetractIncl_comp_permAverage :
    torsorRetractIncl m hY τ htr hτadd y₀ M ρ κ hκ hM bM ≫ permAverage m hY hK τ hτ ι = 0 :=
  finiteTypeContinuousModule_hom_ext m fun v => by
    apply ULift.ext
    funext y i
    show torsorCardInv m hK * ∑ a : K,
      bM.repr (ρ (Multiplicative.ofAdd (-torsorDiff τ htr y₀ (τ a y))) v) i = 0
    have h : ∑ a : K, ρ (Multiplicative.ofAdd (-torsorDiff τ htr y₀ (τ a y))) v =
        ρ (Multiplicative.ofAdd (-torsorDiff τ htr y₀ y))
          (∑ a : K, ρ (Multiplicative.ofAdd a) v) := by
      rw [map_sum]
      refine Fintype.sum_equiv (Equiv.neg K) _ _ fun a => ?_
      rw [torsorDiff_apply τ htr hτadd, ← Module.End.mul_apply, ← map_mul, ← ofAdd_add]
      congr 3
      simp only [Equiv.neg_apply]
      abel
    rw [show (∑ a : K, bM.repr (ρ (Multiplicative.ofAdd (-torsorDiff τ htr y₀ (τ a y))) v) i) =
        bM.repr (∑ a : K, ρ (Multiplicative.ofAdd (-torsorDiff τ htr y₀ (τ a y))) v) i by
      rw [map_sum, Finsupp.finset_sum_apply], h, hfix, map_zero, map_zero, Finsupp.zero_apply,
      mul_zero]

include hK hτ htr hτadd y₀ ρ κ hκ hM bM hfix in
/-- **`T` kills a free module on which `G` acts through the character of the torsor by an action
of `K` without invariants**, for an additive `T` such that `T(ℤ/m[Y])` is finite with as many
elements as `T(ℤ/m)`. -/
theorem subsingleton_obj_of_torsor_character [Nonempty Y]
    (T : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) G ⥤ ModuleCat.{u + 1} (ZMod m))
    [T.Additive] [Finite (T.obj (permModule m PUnit.{u + 2} hY))]
    (hcard : Nat.card (T.obj (permModule m PUnit.{u + 2} hY)) =
      Nat.card (T.obj (trivialContinuousModule m))) [DecidableEq ι] :
    Subsingleton (T.obj M) := by
  have h0 : T.map (torsorRetractIncl m hY τ htr hτadd y₀ M ρ κ hκ hM bM) = 0 := by
    rw [← Category.comp_id (T.map (torsorRetractIncl m hY τ htr hτadd y₀ M ρ κ hκ hM bM)), ←
      map_permAverage_eq_id_of_additive m hY hK τ hτ htr T hcard ι, ← T.map_comp,
      torsorRetractIncl_comp_permAverage m hY hK τ hτ htr hτadd y₀ M ρ κ hκ hM bM hfix, T.map_zero]
  have h1 : 𝟙 (T.obj M) = 0 := by
    rw [← T.map_id, ← torsorRetractIncl_comp_proj m hY hK τ htr hτadd y₀ M ρ κ hκ hM bM,
      T.map_comp, h0, Limits.zero_comp]
  exact subsingleton_of_forall_eq 0 fun x => by simpa using congrArg (fun f => f.hom x) h1

end Character

end Average

end Stacks.EtaleCohomology
