module

public import Mathlib.FieldTheory.FinTrdeg
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary

/-!
# Functoriality of proper pushforward of cycles

Let `S` be the base scheme of chapter 42 of the Stacks Project, carrying a dimension function
`δ`, and let `X`, `Y`, `Z` be schemes locally of finite type over `S`. Stacks 02R5 says that
proper pushforward of `k`-cycles is functorial: for proper `f : X ⟶ Y` and `g : Y ⟶ Z` over `S`,

  `(f ≫ g)_* = g_* ∘ f_*` on `Z_k(-)`.

The coefficient of `f_*α` at a point is a weighted sum of the coefficients of `α` over the
fibre, the weight at `x` being the residue-field degree `[κ(x) : κ(f x)]` when the
delta-dimension is preserved and zero otherwise. Functoriality is therefore two statements: a
pointwise identity between the weights — the multiplicativity of the residue degree in a tower
of residue fields, available exactly when both transcendence degrees vanish, which is what
preservation of the delta-dimension means — and the interchange of the two locally finite sums,
which is Fubini over the finitely many points of a fibre of the composite.

## Main results

* `Stacks.Chow.properPushforward_comp` — Stacks 02R5: proper pushforward is functorial.
* `Stacks.Chow.properPushforward_neg`, `Stacks.Chow.properPushforward_sub` — proper pushforward
  is a homomorphism of abelian groups, in the two forms the group `Z_k(X)` is used with.

## Implementation notes

`Stacks.Chow.relativeDimension` adds to `δ (f x)` the transcendence degree of `κ(x)` over
`κ(f x)`, so the drop of the relative dimension along `f` is that transcendence degree
(`Stacks.Chow.relativeDimension_comp_eq_add_trdeg`). It is finite because the residue-field
extension of a morphism locally of finite type is essentially of finite type, and it vanishes
exactly when the extension is algebraic, hence finite, which is what makes
`Module.finrank_mul_finrank` applicable in the tower.

## References

* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The transcendence degree of a residue-field extension -/

/-- The transcendence degree of the residue-field extension of a morphism of schemes at a point.
This is the amount by which `Stacks.Chow.relativeDimension` grows along the morphism. -/
def residueTrdeg {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : Cardinal :=
  letI := (f.residueFieldMap x).hom.toAlgebra
  Algebra.trdeg (Y.residueField (f.base x)) (X.residueField x)

/-- The residue-field extension of a morphism locally of finite type is essentially of finite
type, hence of finite transcendence degree. -/
theorem residueTrdeg_lt_aleph0 {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X) :
    residueTrdeg f x < Cardinal.aleph0 := by
  let _ : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  let _ : Algebra.EssFiniteType (Y.residueField (f.base x)) (X.residueField x) :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap f x)
  exact trdeg_lt_aleph0 (Y.residueField (f.base x)) (X.residueField x)

/-- A vanishing `Cardinal.toNat` of the residue transcendence degree really means that the
degree is zero, since it is finite. -/
theorem residueTrdeg_eq_zero {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] {x : X}
    (h : Cardinal.toNat (residueTrdeg f x) = 0) : residueTrdeg f x = 0 :=
  (Cardinal.toNat_eq_zero.mp h).resolve_right fun hge ↦
    absurd (residueTrdeg_lt_aleph0 f x) (not_lt_of_ge hge)

/-- The relative dimension over `S` of a composite grows by the transcendence degree of the
residue-field extension: `relativeDimension (f ≫ s) x = relativeDimension s (f x) + trdeg f x`.
-/
theorem relativeDimension_comp_eq_add_trdeg {X Y S : Scheme.{u}} (δ : DimensionFunction S)
    (s : Y ⟶ S) [LocallyOfFiniteType s] (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X) :
    relativeDimension δ (f ≫ s) x =
      relativeDimension δ s (f.base x) + (Cardinal.toNat (residueTrdeg f x) : ℤ) := by
  let _ : Algebra (S.residueField (s.base (f.base x))) (Y.residueField (f.base x)) :=
    (s.residueFieldMap (f.base x)).hom.toAlgebra
  let _ : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  let _ : Algebra (S.residueField (s.base (f.base x))) (X.residueField x) :=
    ((f ≫ s).residueFieldMap x).hom.toAlgebra
  let _ : IsScalarTower (S.residueField (s.base (f.base x))) (Y.residueField (f.base x))
      (X.residueField x) := IsScalarTower.of_algebraMap_eq fun a ↦
    congrArg (fun φ : S.residueField (s.base (f.base x)) →+* X.residueField x ↦ φ a)
      (congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp f s x))
  have hfinS : Algebra.trdeg (S.residueField (s.base (f.base x))) (Y.residueField (f.base x)) <
      Cardinal.aleph0 := residueTrdeg_lt_aleph0 s (f.base x)
  have hfinf : Algebra.trdeg (Y.residueField (f.base x)) (X.residueField x) <
      Cardinal.aleph0 := residueTrdeg_lt_aleph0 f x
  have hnatZ := congrArg (fun n : ℕ ↦ (n : ℤ)) ((Cardinal.toNat_add hfinS hfinf).symm.trans
    (congrArg Cardinal.toNat (trdeg_add_eq (S.residueField (s.base (f.base x)))
      (Y.residueField (f.base x)) (A := X.residueField x))))
  change (δ (s.base (f.base x)) +
      (Cardinal.toNat (Algebra.trdeg (S.residueField (s.base (f.base x)))
        (X.residueField x)) : ℤ)) =
    δ (s.base (f.base x)) +
      (Cardinal.toNat (Algebra.trdeg (S.residueField (s.base (f.base x)))
        (Y.residueField (f.base x))) : ℤ) +
      (Cardinal.toNat (Algebra.trdeg (Y.residueField (f.base x)) (X.residueField x)) : ℤ)
  push_cast at hnatZ ⊢
  omega

/-- If the relative dimension over `S` is unchanged along `f`, the residue-field extension of
`f` has transcendence degree zero. -/
theorem residueTrdeg_eq_zero_of_relativeDimension_eq {X Y S : Scheme.{u}}
    (δ : DimensionFunction S) {sX : X ⟶ S} (sY : Y ⟶ S) [LocallyOfFiniteType sY] {f : X ⟶ Y}
    [LocallyOfFiniteType f] (hf : f ≫ sY = sX) {x : X}
    (hd : relativeDimension δ sX x = relativeDimension δ sY (f.base x)) :
    residueTrdeg f x = 0 := by
  have hstep := relativeDimension_comp_eq_add_trdeg δ sY f x
  rw [hf, hd] at hstep
  exact residueTrdeg_eq_zero f (by exact_mod_cast (by omega : (Cardinal.toNat
    (residueTrdeg f x) : ℤ) = 0))

/-- The residue degree is multiplicative in a composite whose two residue-field extensions are
both of transcendence degree zero: those extensions are then algebraic and essentially of finite
type, hence finite, and the degrees multiply in the tower. -/
theorem residueDegree_comp_of_trdeg_eq_zero {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (g : Y ⟶ Z) [LocallyOfFiniteType g] (x : X)
    (hf : residueTrdeg f x = 0) (hg : residueTrdeg g (f.base x) = 0) :
    (f ≫ g).residueDegree x = f.residueDegree x * g.residueDegree (f.base x) := by
  let _ : Algebra (Z.residueField (g.base (f.base x))) (Y.residueField (f.base x)) :=
    (g.residueFieldMap (f.base x)).hom.toAlgebra
  let _ : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  let _ : Algebra (Z.residueField (g.base (f.base x))) (X.residueField x) :=
    ((f ≫ g).residueFieldMap x).hom.toAlgebra
  let _ : IsScalarTower (Z.residueField (g.base (f.base x))) (Y.residueField (f.base x))
      (X.residueField x) := IsScalarTower.of_algebraMap_eq fun a ↦
    congrArg (fun φ : Z.residueField (g.base (f.base x)) →+* X.residueField x ↦ φ a)
      (congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp f g x))
  let _ : Algebra.IsAlgebraic (Y.residueField (f.base x)) (X.residueField x) :=
    trdeg_eq_zero_iff.mp hf
  let _ : Algebra.IsAlgebraic (Z.residueField (g.base (f.base x))) (Y.residueField (f.base x)) :=
    trdeg_eq_zero_iff.mp hg
  let _ : Algebra.EssFiniteType (Y.residueField (f.base x)) (X.residueField x) :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap f x)
  let _ : Algebra.EssFiniteType (Z.residueField (g.base (f.base x))) (Y.residueField (f.base x)) :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap g (f.base x))
  let _ : Module.Finite (Y.residueField (f.base x)) (X.residueField x) :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  let _ : Module.Finite (Z.residueField (g.base (f.base x))) (Y.residueField (f.base x)) :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  change Module.finrank (Z.residueField (g.base (f.base x))) (X.residueField x) =
    Module.finrank (Y.residueField (f.base x)) (X.residueField x) *
      Module.finrank (Z.residueField (g.base (f.base x))) (Y.residueField (f.base x))
  rw [← Module.finrank_mul_finrank (Z.residueField (g.base (f.base x)))
    (Y.residueField (f.base x)) (X.residueField x)]
  exact Nat.mul_comm _ _

/-- The pushforward weights of `f` and `g` multiply to the pushforward weight of `f ≫ g`. This
is the pointwise half of Stacks 02R5: the weight is the residue degree where the relative
dimension is preserved and zero elsewhere, and the relative dimension cannot be preserved by the
composite without being preserved by both factors. -/
theorem properPushforward_weight_comp (C : ChowSituation.{u}) {X Y Z : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ Z)
    [LocallyOfFiniteType g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (x : X) :
    (if relativeDimension C.dimensionFunction sX x =
        relativeDimension C.dimensionFunction sY (f.base x)
      then (f.residueDegree x : ℤ) else 0) *
      (if relativeDimension C.dimensionFunction sY (f.base x) =
          relativeDimension C.dimensionFunction sZ (g.base (f.base x))
        then (g.residueDegree (f.base x) : ℤ) else 0) =
      if relativeDimension C.dimensionFunction sX x =
          relativeDimension C.dimensionFunction sZ (g.base (f.base x))
        then ((f ≫ g).residueDegree x : ℤ) else 0 := by
  have hfstep := relativeDimension_comp_eq_add_trdeg C.dimensionFunction sY f x
  have hgstep := relativeDimension_comp_eq_add_trdeg C.dimensionFunction sZ g (f.base x)
  rw [hf] at hfstep
  rw [hg] at hgstep
  by_cases hxy : relativeDimension C.dimensionFunction sX x =
      relativeDimension C.dimensionFunction sY (f.base x)
  · by_cases hyz : relativeDimension C.dimensionFunction sY (f.base x) =
        relativeDimension C.dimensionFunction sZ (g.base (f.base x))
    · rw [residueDegree_comp_of_trdeg_eq_zero f g x
          (residueTrdeg_eq_zero_of_relativeDimension_eq C.dimensionFunction sY hf hxy)
          (residueTrdeg_eq_zero_of_relativeDimension_eq C.dimensionFunction sZ hg hyz)]
      simp only [hxy, hyz, ite_true, Nat.cast_mul]
    · simp only [hxy, hyz, ite_true, ite_false, mul_zero]
  · have hxz : relativeDimension C.dimensionFunction sX x ≠
        relativeDimension C.dimensionFunction sZ (g.base (f.base x)) := fun h ↦ hxy (by omega)
    simp only [hxy, hxz, ite_false, zero_mul]

/-! ### Functoriality -/

/-- Two weighted pushforwards of cycles compose to a single one when the weights multiply. -/
theorem locallyFinsupp_map_comp_of_weight_mul {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper f] [IsProper g] (c : AlgebraicCycle X ℤ) (wf : X → ℤ) (wg : Y → ℤ) (wfg : X → ℤ)
    (hw : ∀ x, wf x * wg (f.base x) = wfg x) :
    Function.locallyFinsupp.map g.base wg g.isSpectralMap
        (Function.locallyFinsupp.map f.base wf f.isSpectralMap c) =
      Function.locallyFinsupp.map (g.base ∘ f.base) wfg
        (g.isSpectralMap.comp f.isSpectralMap) c := by
  classical
  apply Function.locallyFinsuppWithin.ext
  intro z
  set K : Set X := (g.base ∘ f.base) ⁻¹' {z} ∩ c.support with hKdef
  set F : Y → ℤ := fun y ↦ Function.locallyFinsupp.map f.base wf f.isSpectralMap c y * wg y
    with hFdef
  have hK : K.Finite :=
    c.locallyFiniteSupport.finite_inter_support_of_isCompact
      (by
        simpa [hKdef] using
          (f ≫ g).isProperMap.isCompact_preimage (isCompact_singleton (x := z)))
  have hI : (f.base '' K).Finite := hK.image f.base
  have hIU : f.base '' K ⊆ g.base ⁻¹' {z} := by
    rintro y ⟨x, hxK, rfl⟩
    exact hxK.1
  have hFSupport : (g.base ⁻¹' {z}) ∩ F.support ⊆ f.base '' K := by
    intro y hy
    obtain ⟨x, hcx, rfl⟩ := Function.locallyFinsupp.support_map_subset_of_forall_mem
      f.isSpectralMap wf c c.support (f.base '' c.support) Set.Subset.rfl
      (fun x hx _ ↦ ⟨x, hx, rfl⟩) (mul_ne_zero_iff.mp hy.2).1
    exact ⟨x, ⟨by simpa using hy.1, hcx⟩, rfl⟩
  have hfib (y : Y) : ((f.base ⁻¹' {y}) ∩ K).Finite := hK.subset Set.inter_subset_right
  have hinner (y : Y) (hy : y ∈ f.base '' K) :
      (∑ᶠ x ∈ f.base ⁻¹' {y}, c x * wf x) = ∑ x ∈ (hfib y).toFinset, c x * wf x := by
    refine finsum_mem_eq_sum_of_subset (fun x ↦ c x * wf x) (fun x hx ↦
      (hfib y).mem_toFinset.mpr ⟨hx.1, ?_, (mul_ne_zero_iff.mp hx.2).1⟩)
      (fun x hx ↦ ((hfib y).mem_toFinset.mp hx).1)
    change g.base (f.base x) = z
    rw [show f.base x = y from hx.1]
    exact hIU hy
  have hFin : (g.base ⁻¹' {z}) ∩ F.support ⊆ (hI.toFinset : Finset Y) := by
    simpa only [hI.coe_toFinset] using hFSupport
  have hFout : ((hI.toFinset : Finset Y) : Set Y) ⊆ g.base ⁻¹' {z} := by
    simpa only [hI.coe_toFinset] using hIU
  have hGin : ((g.base ∘ f.base) ⁻¹' {z}) ∩ (fun x : X ↦ c x * wfg x).support ⊆
      (hK.toFinset : Finset X) := by
    rw [hK.coe_toFinset]
    exact fun x hx ↦ ⟨hx.1, (mul_ne_zero_iff.mp hx.2).1⟩
  have hGout : ((hK.toFinset : Finset X) : Set X) ⊆ (g.base ∘ f.base) ⁻¹' {z} := by
    rw [hK.coe_toFinset]
    exact fun x hx ↦ hx.1
  change (∑ᶠ y ∈ g.base ⁻¹' {z}, F y) = ∑ᶠ x ∈ (g.base ∘ f.base) ⁻¹' {z}, c x * wfg x
  rw [finsum_mem_eq_sum_of_subset F hFin hFout,
    finsum_mem_eq_sum_of_subset (fun x : X ↦ c x * wfg x) hGin hGout]
  calc ∑ y ∈ hI.toFinset, F y
      = ∑ y ∈ hI.toFinset, ∑ x ∈ (hfib y).toFinset, c x * wf x * wg y := by
        refine Finset.sum_congr rfl fun y hy ↦ ?_
        rw [hFdef]
        change (∑ᶠ x ∈ f.base ⁻¹' {y}, c x * wf x) * wg y = _
        rw [hinner y (by simpa using hy), Finset.sum_mul]
    _ = ∑ x ∈ hK.toFinset, c x * wf x * wg (f.base x) := by
        rw [← Finset.sum_fiberwise_of_maps_to (s := hK.toFinset) (t := hI.toFinset)
          (g := f.base) (f := fun x ↦ c x * wf x * wg (f.base x))
          (fun x hx ↦ hI.mem_toFinset.mpr ⟨x, hK.mem_toFinset.mp hx, rfl⟩)]
        refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr ?_ ?_
        · ext x
          simp [and_comm]
        · exact fun x hx ↦ by rw [(Finset.mem_filter.mp hx).2]
    _ = ∑ x ∈ hK.toFinset, c x * wfg x :=
        Finset.sum_congr rfl fun x _ ↦ by rw [mul_assoc, hw]

/-- **Stacks 02R5.** Proper pushforward of `k`-cycles is functorial: pushing forward along
`f : X ⟶ Y` and then along `g : Y ⟶ Z` is pushing forward along the composite. -/
@[stacks 02R5,
  stacks 0B0N "functoriality of proper pushforward of cycles, in the case of varieties"]
theorem properPushforward_comp (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (f : X ⟶ Y) [IsProper f] (g : Y ⟶ Z) [IsProper g]
    (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (k : ℤ) :
    properPushforward C sY sZ g hg k ∘ properPushforward C sX sY f hf k =
      properPushforward C sX sZ (f ≫ g) (by rw [Category.assoc, hg, hf]) k := by
  funext c
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro z
  set wx : X → ℤ := relativeDimension C.dimensionFunction sX with hwx
  set wy : Y → ℤ := relativeDimension C.dimensionFunction sY with hwy
  set wz : Z → ℤ := relativeDimension C.dimensionFunction sZ with hwz
  set wf : X → ℤ := fun x ↦ if wx x = wy (f.base x) then (f.residueDegree x : ℤ) else 0 with hwf
  set wg' : Y → ℤ := fun y ↦ if wy y = wz (g.base y) then (g.residueDegree y : ℤ) else 0
    with hwg'
  set wfg : X → ℤ :=
    fun x ↦ if wx x = wz (g.base (f.base x)) then ((f ≫ g).residueDegree x : ℤ) else 0 with hwfg
  have hmapf : AlgebraicCycle.map f wx wy c.1 =
      Function.locallyFinsupp.map f.base wf f.isSpectralMap c.1 := by
    ext y
    simp [AlgebraicCycle.map, AlgebraicCycle.mapCoeff, hwf]
  have hmapg : AlgebraicCycle.map g wy wz =
      Function.locallyFinsupp.map g.base wg' g.isSpectralMap := by
    funext d
    ext z'
    simp [AlgebraicCycle.map, AlgebraicCycle.mapCoeff, hwg']
  have hmapfg : AlgebraicCycle.map (f ≫ g) wx wz c.1 =
      Function.locallyFinsupp.map (g.base ∘ f.base) wfg
        (g.isSpectralMap.comp f.isSpectralMap) c.1 := by
    ext z'
    refine finsum_mem_congr rfl fun x _ ↦ ?_
    by_cases hdim : wx x = wz (g.base (f.base x)) <;>
      simp [AlgebraicCycle.mapCoeff, hwfg, hdim]
  change AlgebraicCycle.map g wy wz (AlgebraicCycle.map f wx wy c.1) z =
    AlgebraicCycle.map (f ≫ g) wx wz c.1 z
  rw [hmapf, hmapg, hmapfg]
  exact congrArg (fun d : AlgebraicCycle Z ℤ ↦ d z)
    (locallyFinsupp_map_comp_of_weight_mul f g c.1 wf wg' wfg
      (properPushforward_weight_comp C sX sY sZ f g hf hg))

/-- **Stacks 02R5.** Proper pushforward of `k`-cycles is functorial, read on a single cycle. -/
theorem properPushforward_properPushforward (C : ChowSituation.{u}) {X Y Z : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y) [IsProper f] (g : Y ⟶ Z) [IsProper g]
    (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (k : ℤ) (c : CycleGroup C sX k) :
    properPushforward C sY sZ g hg k (properPushforward C sX sY f hf k c) =
      properPushforward C sX sZ (f ≫ g) (by rw [Category.assoc, hg, hf]) k c :=
  congrFun (properPushforward_comp C sX sY sZ f g hf hg k) c

/-! ### Additivity -/

/-- Proper pushforward respects negation of cycles. -/
theorem properPushforward_neg (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f]
    (hf : f ≫ sY = sX) (k : ℤ) (c : CycleGroup C sX k) :
    properPushforward C sX sY f hf k (-c) = -properPushforward C sX sY f hf k c :=
  eq_neg_iff_add_eq_zero.mpr <| by
    rw [add_comm, ← properPushforward_add, add_neg_cancel, properPushforward_zero]

/-- Proper pushforward respects differences of cycles. -/
theorem properPushforward_sub (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f]
    (hf : f ≫ sY = sX) (k : ℤ) (a b : CycleGroup C sX k) :
    properPushforward C sX sY f hf k (a - b) =
      properPushforward C sX sY f hf k a - properPushforward C sX sY f hf k b := by
  rw [sub_eq_add_neg, properPushforward_add, properPushforward_neg, sub_eq_add_neg]

/-- Proper pushforward of `k`-cycles as a homomorphism of abelian groups. -/
def properPushforwardHom (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f]
    (hf : f ≫ sY = sX) (k : ℤ) : CycleGroup C sX k →+ CycleGroup C sY k where
  toFun := properPushforward C sX sY f hf k
  map_zero' := properPushforward_zero C sX sY f hf k
  map_add' := properPushforward_add C sX sY f hf k

/-- The homomorphism `properPushforwardHom` sends a cycle `c` to `properPushforward` of `c`. -/
@[simp]
theorem properPushforwardHom_apply (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f]
    (hf : f ≫ sY = sX) (k : ℤ) (c : CycleGroup C sX k) :
    properPushforwardHom C sX sY f hf k c = properPushforward C sX sY f hf k c :=
  rfl

end Stacks.Chow

end
