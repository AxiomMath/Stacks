module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCompactSupportRightExact
public import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# `H²(X_k̄, M) = M` for a finite module `M`, with `π_X^* = q`

Let `X` be proper over a finite field `k` with `q` elements, of dimension one, such that `X_k̄` is
a smooth proper curve over an algebraically closed extension `k̄` of `k`, and let `m` be invertible
in `k̄`. For every finite `ℤ/m`-module `M` the map

`M ⟶ H²(X_k̄, M_X)`, `v ↦ v_*(c)`,

where `c` generates `H²(X_k̄, ℤ/m) ≅ ℤ/m`
(`Stacks.EtaleCohomology.exists_addEquiv_compactSupportSheafCohomology_two_constant`) and
`v_* : H²(X_k̄, ℤ/m) ⟶ H²(X_k̄, M)` is induced by `ℤ/m ⟶ M, 1 ↦ v`, is an isomorphism, natural
in `M`, and the canonical geometric Frobenius acts on `H²(X_k̄, M_X)` as multiplication by `q`.

Surjectivity: `H²(X_k̄, -)` is right exact (`H³ = 0` on a curve), so it suffices to treat a free
module, where the coordinate projections split the identity. Injectivity: every functional
`χ : M ⟶ ℤ/m` gives `χ_*(v_* c) = χ(v) c`, and functionals separate the points of a finite
`ℤ/m`-module (the structure theorem of finite abelian groups).

## Main definitions

* `Stacks.EtaleCohomology.constantTopCohomologyMap`: the map `M ⟶ H²(X_k̄, M_X)`, `v ↦ v_*(c)`.

## Main results

* `Stacks.EtaleCohomology.exists_zmodLinearMap_apply_ne_zero`: functionals separate the points of
  a finite `ℤ/m`-module.
* `Stacks.EtaleCohomology.constantTopCohomologyMap_naturality`: `v ↦ v_*(c)` is natural in `M`.
* `Stacks.EtaleCohomology.compactSupportSheafFrobenius_constantTopCohomologyMap`: the geometric
  Frobenius commutes with `v ↦ v_*(c)`.
* `Stacks.EtaleCohomology.exists_constantTopCohomology_generator`: there is `c ∈ H²(X_k̄, ℤ/m)`
  with Frobenius acting as `q` such that `v ↦ v_*(c)` is bijective for every finite `M`.

## References

* [Stacks, Tag 03VK]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

/-! ### Functionals separate the points of a finite `ℤ/m`-module -/

section Separation

/-- `ZMod a` embeds additively into `ZMod m` for `a ∣ m`, by `1 ↦ m / a`. -/
theorem exists_injective_zmod_addMonoidHom {a m : ℕ} (hm : m ≠ 0) (ham : a ∣ m) :
    ∃ j : ZMod a →+ ZMod m, Function.Injective j := by
  obtain ⟨d, rfl⟩ := ham
  have hd : d ≠ 0 := right_ne_zero_of_mul hm
  let g : ℤ →+ ZMod (a * d) := (d : ℤ) • Int.castAddHom (ZMod (a * d))
  have hg : g a = 0 := by
    show (d : ℤ) • ((a : ℤ) : ZMod (a * d)) = 0
    rw [zsmul_eq_mul, ← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [mul_comm]
  refine ⟨ZMod.lift a ⟨g, hg⟩, (ZMod.lift_injective a).2 fun z hz => ?_⟩
  have hz' : (((d : ℤ) * z : ℤ) : ZMod (a * d)) = 0 := by rwa [Int.cast_mul, ← zsmul_eq_mul]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz'
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast at hz'
  rw [mul_comm (a : ℤ)] at hz'
  exact (mul_dvd_mul_iff_left (by exact_mod_cast hd)).1 hz'

/-- **Functionals separate the points of a finite `ℤ/m`-module.** -/
theorem exists_zmodLinearMap_apply_ne_zero {m : ℕ} [NeZero m] {M : Type*} [AddCommGroup M]
    [Module (ZMod m) M] [Finite M] {v : M} (hv : v ≠ 0) :
    ∃ χ : M →ₗ[ZMod m] ZMod m, χ v ≠ 0 := by
  obtain ⟨ι, _, p, -, e, ⟨E⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite M
  classical
  have hEv : E v ≠ 0 := fun h => hv (E.injective (h.trans (map_zero E).symm))
  obtain ⟨i, hi⟩ : ∃ i, (E v) i ≠ 0 := not_forall.1 fun h => hEv (DFinsupp.ext h)
  have hkill : ∀ x : M, (m : ℕ) • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod m), ZMod.natCast_self, zero_smul]
  let ev : M →+ ZMod (p i ^ e i) := (DFinsupp.evalAddMonoidHom i).comp E.toAddMonoidHom
  have hdvd : p i ^ e i ∣ m := by
    let w := E.symm (DirectSum.of (fun i => ZMod (p i ^ e i)) i 1)
    have hw : ev w = 1 := by
      show (E (E.symm (DirectSum.of (fun i => ZMod (p i ^ e i)) i 1))) i = 1
      rw [AddEquiv.apply_symm_apply, DirectSum.of_eq_same]
    have h1 : m • ev w = 0 := by rw [← map_nsmul, hkill, map_zero]
    rw [hw, nsmul_eq_mul, mul_one] at h1
    exact (ZMod.natCast_eq_zero_iff m _).1 h1
  obtain ⟨j, hj⟩ := exists_injective_zmod_addMonoidHom (NeZero.ne m) hdvd
  exact ⟨(j.comp ev).toZModLinearMap m, fun h => hi (hj (h.trans (map_zero j).symm))⟩

end Separation

/-! ### The top cohomology of a constant sheaf on a proper curve -/

section Constant

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [IsProper f]
  (kbar : Type u) [Field kbar] [Algebra k kbar] (m : ℕ) [NeZero m]

/-- `M ↦ H²(X_k̄, M_X)`, for `X` proper over `k` compactified by itself. -/
abbrev constantTopCohomology : ModuleCat.{u + 1} (ZMod m) ⥤ ModuleCat.{u + 1} (ZMod m) :=
  constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod m)) ⋙
    compactSupportSheafCohomology (ZMod m) f (CompactificationOf.ofProper f) kbar 2

/-- The coefficient module `ℤ/m`, in the universe of the étale sheaves. -/
abbrev unitCoefficients : ModuleCat.{u + 1} (ZMod m) :=
  ModuleCat.of (ZMod m) (ULift.{u + 1} (ZMod m))

/-- The map `ℤ/m ⟶ M`, `1 ↦ v`. -/
def coefficientPoint {M : ModuleCat.{u + 1} (ZMod m)} (v : M) : unitCoefficients m ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton (ZMod m) M v ∘ₗ
    (ULift.moduleEquiv (R := ZMod m) (M := ZMod m)).toLinearMap)

omit [NeZero m] in
/-- The map `ℤ/m ⟶ M`, `1 ↦ v`, sends `a` to `a • v`. -/
@[simp]
lemma coefficientPoint_apply {M : ModuleCat.{u + 1} (ZMod m)} (v : M) (a : ULift.{u + 1} (ZMod m)) :
    (coefficientPoint m v).hom a = a.down • v :=
  rfl

omit [NeZero m] in
/-- `v ↦ (1 ↦ v)` is additive. -/
lemma coefficientPoint_add {M : ModuleCat.{u + 1} (ZMod m)} (v w : M) :
    coefficientPoint m (v + w) = coefficientPoint m v + coefficientPoint m w := by
  ext a
  exact smul_add a.down v w

omit [NeZero m] in
/-- Composing `1 ↦ v` with `g : M ⟶ N` gives `1 ↦ g v`. -/
lemma coefficientPoint_comp {M N : ModuleCat.{u + 1} (ZMod m)} (v : M) (g : M ⟶ N) :
    coefficientPoint m v ≫ g = coefficientPoint m (g.hom v) := by
  ext a
  exact map_smul g.hom a.down v

/-- On `M = ℤ/m`, the map `1 ↦ y` is multiplication by `y`. -/
lemma coefficientPoint_unit (y : ULift.{u + 1} (ZMod m)) :
    coefficientPoint m (M := unitCoefficients m) y = y.down.val • 𝟙 (unitCoefficients m) := by
  ext a
  show a.down * y.down = y.down.val • a.down
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]

omit [NeZero m] in
/-- A finite `ℤ/m`-module `M` is a quotient `P` of a free module whose coordinate projections `ev`
and inclusions `ins` split the identity, with `ins v ≫ P` the map `1 ↦ v`. -/
theorem exists_free_cover_coefficientPoint (M : ModuleCat.{u + 1} (ZMod m)) [Fintype M] :
    ∃ (F : ModuleCat.{u + 1} (ZMod m)) (P : F ⟶ M) (ev : M → (F ⟶ unitCoefficients m))
      (ins : M → (unitCoefficients m ⟶ F)),
      Epi P ∧ ∑ v : M, ev v ≫ ins v = 𝟙 F ∧ ∀ v, ins v ≫ P = coefficientPoint m v := by
  classical
  let F : ModuleCat.{u + 1} (ZMod m) := ModuleCat.of (ZMod m) (M → ULift.{u + 1} (ZMod m))
  let P : F ⟶ M := ModuleCat.ofHom
    { toFun := fun a => ∑ v : M, (a v).down • v
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r a => by simp [Finset.smul_sum, smul_smul] }
  have hsum : ∀ (v : M) (a : ULift.{u + 1} (ZMod m)),
      ∑ w : M, (Pi.single (M := fun _ : M => ULift.{u + 1} (ZMod m)) v a w).down • w =
        a.down • v := fun v a => by
    rw [Fintype.sum_eq_single v (fun w hw => by
      rw [Pi.single_eq_of_ne hw]
      exact zero_smul _ w), Pi.single_eq_same]
  have hP : Function.Surjective P.hom := fun v =>
    ⟨Pi.single v (ULift.up 1), (hsum v _).trans (one_smul _ v)⟩
  let ev : M → (F ⟶ unitCoefficients m) := fun v => ModuleCat.ofHom (LinearMap.proj v)
  let ins : M → (unitCoefficients m ⟶ F) := fun v => ModuleCat.ofHom (LinearMap.single (ZMod m)
    (fun _ : M => ULift.{u + 1} (ZMod m)) v)
  refine ⟨F, P, ev, ins, (ModuleCat.epi_iff_surjective P).2 hP, ?_, fun v => ?_⟩
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    funext w
    rw [ModuleCat.hom_sum, LinearMap.sum_apply, Finset.sum_apply]
    show ∑ v : M, (Pi.single (M := fun _ : M => ULift.{u + 1} (ZMod m)) v (a v)) w = a w
    rw [Fintype.sum_eq_single w (fun v hv => Pi.single_eq_of_ne (Ne.symm hv) _),
      Pi.single_eq_same]
  · ext a
    exact hsum v a

omit [Fintype k] in
/-- `M ↦ H²(X_k̄, M_X)` is additive. -/
theorem additive_constantTopCohomology [Finite k] : (constantTopCohomology f kbar m).Additive := by
  have := additive_liftSingle (ZMod m) X (fun _ => ⟨0, inferInstance⟩)
  dsimp only [constantTopCohomology, compactSupportSheafCohomology]
  infer_instance

/-- **The map `v ↦ v_*(c)`** from `M` to `H²(X_k̄, M_X)`, for a class `c ∈ H²(X_k̄, ℤ/m)`. -/
def constantTopCohomologyMap (c : (constantTopCohomology f kbar m).obj (unitCoefficients m))
    (M : ModuleCat.{u + 1} (ZMod m)) : M →+ (constantTopCohomology f kbar m).obj M :=
  AddMonoidHom.mk' (fun v => ((constantTopCohomology f kbar m).map (coefficientPoint m v)).hom c)
    fun v w => by
      have := additive_constantTopCohomology f kbar m
      rw [coefficientPoint_add, Functor.map_add]
      rfl

/-- `constantTopCohomologyMap` sends `v` to `v_*(c)`. -/
lemma constantTopCohomologyMap_apply (c : (constantTopCohomology f kbar m).obj (unitCoefficients m))
    (M : ModuleCat.{u + 1} (ZMod m)) (v : M) :
    constantTopCohomologyMap f kbar m c M v =
      ((constantTopCohomology f kbar m).map (coefficientPoint m v)).hom c :=
  rfl

/-- **`v ↦ v_*(c)` is natural in the module.** -/
theorem constantTopCohomologyMap_naturality
    (c : (constantTopCohomology f kbar m).obj (unitCoefficients m))
    {M N : ModuleCat.{u + 1} (ZMod m)}
    (g : M ⟶ N) (v : M) :
    ((constantTopCohomology f kbar m).map g).hom (constantTopCohomologyMap f kbar m c M v) =
      constantTopCohomologyMap f kbar m c N (g.hom v) := by
  rw [constantTopCohomologyMap_apply, constantTopCohomologyMap_apply, ← coefficientPoint_comp,
    Functor.map_comp]
  rfl

/-- On `M = ℤ/m`, the map `v ↦ v_*(c)` sends `y` to `y • c`. -/
lemma constantTopCohomologyMap_unit
    (c : (constantTopCohomology f kbar m).obj (unitCoefficients m)) (y : ULift.{u + 1} (ZMod m)) :
    constantTopCohomologyMap f kbar m c (unitCoefficients m) y = y.down.val • c := by
  have := additive_constantTopCohomology f kbar m
  rw [constantTopCohomologyMap_apply, coefficientPoint_unit, Functor.map_nsmul,
    CategoryTheory.Functor.map_id]
  rfl

/-- If `v ↦ v_*(c)` is injective on `ℤ/m`, it is injective on every finite `ℤ/m`-module. -/
theorem constantTopCohomologyMap_injective
    (c : (constantTopCohomology f kbar m).obj (unitCoefficients m))
    (hc : Function.Injective (constantTopCohomologyMap f kbar m c (unitCoefficients m)))
    (M : ModuleCat.{u + 1} (ZMod m)) [Finite M] :
    Function.Injective (constantTopCohomologyMap f kbar m c M) := by
  refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
  by_contra hne
  obtain ⟨χ, hχ⟩ := exists_zmodLinearMap_apply_ne_zero (m := m) hne
  let χ' : M ⟶ unitCoefficients m :=
    ModuleCat.ofHom ((ULift.moduleEquiv (R := ZMod m) (M := ZMod m)).symm.toLinearMap ∘ₗ χ)
  have h := constantTopCohomologyMap_naturality f kbar m c χ' v
  rw [hv, map_zero] at h
  exact hχ (congrArg ULift.down
    (hc (h.symm.trans (map_zero (constantTopCohomologyMap f kbar m c (unitCoefficients m))).symm)))

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- The canonical geometric Frobenius commutes with `v ↦ v_*(c)`. -/
theorem compactSupportSheafFrobenius_constantTopCohomologyMap
    (c : (constantTopCohomology f kbar m).obj (unitCoefficients m)) (M : ModuleCat.{u + 1} (ZMod m))
    (v : M) :
    ((compactSupportSheafFrobenius (ZMod m) f (CompactificationOf.ofProper f) kbar p q hcard 2).app
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod m))).obj M)).hom
        (constantTopCohomologyMap f kbar m c M v) =
      constantTopCohomologyMap f kbar m
        (((compactSupportSheafFrobenius (ZMod m) f (CompactificationOf.ofProper f) kbar p q hcard
          2).app ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod m))).obj
            (unitCoefficients m))).hom c) M v :=
  congrArg (fun φ => φ.hom c) ((compactSupportSheafFrobenius (ZMod m) f
    (CompactificationOf.ofProper f) kbar p q hcard 2).naturality
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod m))).map
        (coefficientPoint m v)))

variable [IsAlgClosed kbar] [IsCurve k f]
  [IsCurve kbar (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
  [Smooth (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
  [IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]

omit [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  [IsCurve kbar (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
  [Smooth (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
  [IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))] in
/-- Every class of `H²(X_k̄, M_X)` is a sum of classes `v_*(x_v)`, `v ∈ M`. -/
theorem exists_eq_sum_constantTopCohomology_map (M : ModuleCat.{u + 1} (ZMod m)) [Fintype M]
    [Finite k] (t : (constantTopCohomology f kbar m).obj M) :
    ∃ x : M → (constantTopCohomology f kbar m).obj (unitCoefficients m),
      t = ∑ v : M, ((constantTopCohomology f kbar m).map (coefficientPoint m v)).hom (x v) := by
  let T := constantTopCohomology f kbar m
  have : T.Additive := additive_constantTopCohomology f kbar m
  obtain ⟨F, P, ev, ins, _, hsplit, hins⟩ := exists_free_cover_coefficientPoint m M
  have hdim : topologicalKrullDim X ≤ 1 := (IsCurve.topologicalKrullDim_eq_one (f := f)).le
  obtain ⟨s, rfl⟩ := surjective_compactSupportSheafCohomology_two_map_of_epi f
    (CompactificationOf.ofProper f) kbar m hdim
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod m))).map P) t
  have hs : s = ∑ v : M, (T.map (ins v)).hom ((T.map (ev v)).hom s) := by
    have h := congrArg (fun φ => φ.hom s)
      (by rw [hsplit, T.map_id] : T.map (∑ v : M, ev v ≫ ins v) = 𝟙 _)
    simp only [Functor.map_sum, ModuleCat.hom_sum, LinearMap.sum_apply, Functor.map_comp,
      ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h.symm
  refine ⟨fun v => (T.map (ev v)).hom s, ?_⟩
  show (T.map P).hom s = _
  conv_lhs => rw [hs]
  rw [map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  show (T.map (ins v) ≫ T.map P).hom _ = _
  rw [← T.map_comp, hins]

omit [IsCurve kbar (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
  [Smooth (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
  [IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))] in
/-- If `v ↦ v_*(c)` is surjective on `ℤ/m`, it is surjective on every finite `ℤ/m`-module. -/
theorem constantTopCohomologyMap_surjective
    (c : (constantTopCohomology f kbar m).obj (unitCoefficients m))
    (hc : Function.Surjective (constantTopCohomologyMap f kbar m c (unitCoefficients m)))
    (M : ModuleCat.{u + 1} (ZMod m)) [Finite M] :
    Function.Surjective (constantTopCohomologyMap f kbar m c M) := fun t => by
  have : Fintype M := Fintype.ofFinite M
  choose y hy using hc
  obtain ⟨x, rfl⟩ := exists_eq_sum_constantTopCohomology_map f kbar m M t
  refine ⟨∑ v : M, (y (x v)).down.val • v, ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hx : x v = (y (x v)).down.val • c :=
    (hy _).symm.trans (constantTopCohomologyMap_unit f kbar m c _)
  rw [map_nsmul]
  conv_rhs => rw [hx]
  rw [map_nsmul]
  rfl

include hcard in
/-- **`H²(X_k̄, M_X) ≅ M`, with `π_X^*` acting as `q`.** There is a class `c ∈ H²(X_k̄, ℤ/m)`
with `π_X^* c = q c` such that `v ↦ v_*(c)` is a bijection `M ≅ H²(X_k̄, M_X)` for every finite
`ℤ/m`-module `M`. -/
theorem exists_constantTopCohomology_generator (hm : IsUnit (m : kbar)) :
    ∃ c : (constantTopCohomology f kbar m).obj (unitCoefficients m),
      ((compactSupportSheafFrobenius (ZMod m) f (CompactificationOf.ofProper f) kbar p q hcard
          2).app ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod m))).obj
            (unitCoefficients m))).hom c = (p ^ q : ℕ) • c ∧
      ∀ (M : ModuleCat.{u + 1} (ZMod m)) [Finite M],
        Function.Bijective (constantTopCohomologyMap f kbar m c M) := by
  obtain ⟨Φ, hΦ⟩ := exists_addEquiv_compactSupportSheafCohomology_two_constant f kbar p q hcard m hm
  let c : (constantTopCohomology f kbar m).obj (unitCoefficients m) := Φ.symm 1
  have hΦc : ∀ n : ℕ, Φ (n • c) = n := fun n => by
    rw [map_nsmul, AddEquiv.apply_symm_apply, nsmul_eq_mul, mul_one]
  have hc : ∀ y, Φ (constantTopCohomologyMap f kbar m c (unitCoefficients m) y) = y.down :=
    fun y => by rw [constantTopCohomologyMap_unit, hΦc, ZMod.natCast_zmod_val]
  refine ⟨c, Φ.injective ?_, fun M _ =>
    ⟨constantTopCohomologyMap_injective f kbar m c
      (fun y z h => congrArg ULift.up (by rw [← hc y, ← hc z, h])) M,
    constantTopCohomologyMap_surjective f kbar m c
      (fun x => ⟨ULift.up (Φ x), Φ.injective (by rw [hc])⟩) M⟩⟩
  rw [hΦ, hΦc, AddEquiv.apply_symm_apply, mul_one]

end Constant

end Stacks.EtaleCohomology

end
