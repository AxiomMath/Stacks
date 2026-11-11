module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Canonical
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBase
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.CapLocallyFinite
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.RationalEquivalence

/-!
# The exterior product over a Dedekind base commutes with capping

Let `(S, δ)` be as in Stacks section 42.63, let `X` be locally of finite type over `S`, let
`Y ⟶ Z` be a morphism of schemes locally of finite type over `S` and let `c' ∈ A^q(Y ⟶ Z)`.
Then for `α ∈ CH_n(X)` and `β ∈ CH_m(Z)`

  `α × (c' ∩ β) = c' ∩ (α × β)`   in   `CH_*(X ×_S Y)`.

The identity is proved more generally for `β ∈ CH_m(T)` with `t : T ⟶ Z` any test scheme, the
two sides compared through the canonical isomorphism `X ×_S (Y ×_Z T) ≅ Y ×_Z (X ×_S T)`.

## Main results

* `Stacks.Chow.exteriorProductDedekindChowTensor_cap_comm`: the exterior product over a Dedekind
  base commutes with capping with a bivariant class, `α × (c' ∩ β) = c' ∩ (α × β)`.

## References

* [Stacks Project, Tag 0FC7](https://stacks.math.columbia.edu/tag/0FC7)
* [Stacks Project, Tag 0FC6](https://stacks.math.columbia.edu/tag/0FC6)
* [Stacks Project, Tag 0FC5](https://stacks.math.columbia.edu/tag/0FC5)
* [Stacks Project, Tag 0FC4](https://stacks.math.columbia.edu/tag/0FC4)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The fibre of a point closure in the two iterated fibre products -/

section Geometry

variable {C : ChowSituation.{u}} {X Y Z T : Scheme.{u}} (sX : X ⟶ C.S) (sZ : Z ⟶ C.S) (w : Y ⟶ Z)
  (t : T ⟶ Z) (x : X)

/-- Inside `X ×_S (Y ×_Z T)`, the subscheme `closure {x} ×_S (Y ×_Z T)` is the inverse image of
`closure {x} ×_S T ⊆ X ×_S T`. -/
theorem dedekindPointFibre_eq_comap_mixedCommuteSnd :
    dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x =
      (dedekindPointFibre sX (t ≫ sZ) x).comap (mixedCommuteSnd sX sZ w t) := by
  rw [dedekindPointFibre, dedekindPointFibre, ← Scheme.IdealSheafData.comap_comp,
    mixedCommuteSnd_fst]

/-- The morphism `closure {x} ×_S (Y ×_Z T) ⟶ closure {x} ×_S T`. -/
def mixedPointFibreMap :
    (dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x).subscheme ⟶
      (dedekindPointFibre sX (t ≫ sZ) x).subscheme :=
  Scheme.IdealSheafData.subschemeMap _ _ (mixedCommuteSnd sX sZ w t)
    (Scheme.IdealSheafData.le_map_iff_comap_le.2
      (le_of_eq (dedekindPointFibre_eq_comap_mixedCommuteSnd sX sZ w t x).symm))

/-- `mixedPointFibreMap` is the restriction of `mixedCommuteSnd` to the point fibres. -/
@[reassoc (attr := simp)]
theorem mixedPointFibreMap_subschemeι :
    mixedPointFibreMap sX sZ w t x ≫ (dedekindPointFibre sX (t ≫ sZ) x).subschemeι =
      (dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x).subschemeι ≫
        mixedCommuteSnd sX sZ w t :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The square exhibiting `X ×_S (Y ×_Z T)` as `Y ×_Z (X ×_S T)`. -/
theorem isPullback_mixedCommuteSnd :
    IsPullback (pullback.snd sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ pullback.fst w t)
      (mixedCommuteSnd sX sZ w t) w (pullback.snd sX (t ≫ sZ) ≫ t) :=
  IsPullback.of_iso_pullback ⟨by rw [← mixedCommuteHom_fst, ← mixedCommuteHom_snd,
      Category.assoc, Category.assoc, pullback.condition]⟩
    (asIso (mixedCommuteHom sX sZ w t)) (mixedCommuteHom_fst sX sZ w t)
    (mixedCommuteHom_snd sX sZ w t)

/-- The square exhibiting `closure {x} ×_S (Y ×_Z T)` as `Y ×_Z (closure {x} ×_S T)`. -/
theorem isPullback_mixedPointFibreMap :
    IsPullback ((dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x).subschemeι ≫
        pullback.snd sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ pullback.fst w t)
      (mixedPointFibreMap sX sZ w t x) w
      ((dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫ pullback.snd sX (t ≫ sZ) ≫ t) :=
  (isPullback_subschemeMap_of_eq_comap (mixedCommuteSnd sX sZ w t) _ _
    (dedekindPointFibre_eq_comap_mixedCommuteSnd sX sZ w t x)).paste_horiz
    (isPullback_mixedCommuteSnd sX sZ w t)

/-- The iterated fibre product `closure {x} ×_S (Y ×_Z T)` is isomorphic to
`Y ×_Z (closure {x} ×_S T)` over `X ×_S (Y ×_Z T)`, compatibly with `mixedCommuteHom`. -/
private theorem exists_isIso_comp_pullback_fst_eq_mixedPointFibre
    {gV : (dedekindPointFibre sX (t ≫ sZ) x).subscheme ⟶ Z}
    (hgV : (dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫ (pullback.snd sX (t ≫ sZ) ≫ t) = gV) :
    ∃ ρ : (dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x).subscheme ⟶ pullback w gV,
      IsIso ρ ∧
      ρ ≫ pullback.fst w gV = (dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x).subschemeι ≫
        pullback.snd sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ pullback.fst w t ∧
      ρ ≫ pullback.snd w gV = mixedPointFibreMap sX sZ w t x ∧
      ρ ≫ (pullback.fst w gV ≫ (w ≫ sZ)) =
        (dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x).subschemeι ≫
          (pullback.fst sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ sX) ∧
      ρ ≫ testBaseChangeMapOfEq w (pullback.snd sX (t ≫ sZ) ≫ t)
        (dedekindPointFibre sX (t ≫ sZ) x).subschemeι gV hgV =
        (dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x).subschemeι ≫
          mixedCommuteHom sX sZ w t := by
  subst hgV
  have hpb := isPullback_mixedPointFibreMap sX sZ w t x
  refine ⟨hpb.isoPullback.hom, inferInstance, hpb.isoPullback_hom_fst, hpb.isoPullback_hom_snd,
    ?_, ?_⟩
  · rw [reassoc_of% hpb.isoPullback_hom_fst, ← pullback.condition]
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, testBaseChangeMapOfEq_fst, hpb.isoPullback_hom_fst, Category.assoc,
        mixedCommuteHom_fst]
    · rw [Category.assoc, testBaseChangeMapOfEq_snd, reassoc_of% hpb.isoPullback_hom_snd,
        mixedPointFibreMap_subschemeι, Category.assoc, mixedCommuteHom_snd]

end Geometry

/-! ### Bookkeeping -/

section Bookkeeping

variable {C : ChowSituation.{u}}

/-- Pushforward commutes with transport along an equality of degrees, on coefficients. -/
theorem properPushforward_val_cast {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
    (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (f : A ⟶ B) [IsProper f] (hf : f ≫ sB = sA)
    {k k' : ℤ} (h : k = k') (c : CycleGroup C sA k) :
    (properPushforward C sA sB f hf k' (h ▸ c)).1 = (properPushforward C sA sB f hf k c).1 := by
  subst h
  rfl

/-- The class of a cycle transported along an equality of degrees is heterogeneously the class of
the cycle. -/
theorem mk_cast_heq {A : Scheme.{u}} (s : A ⟶ C.S) [LocallyOfFiniteType s] {k k' : ℤ}
    (h : k = k') (c : CycleGroup C s k) :
    QuotientAddGroup.mk' (rationalEquivalences C s k') (h ▸ c) ≍
      QuotientAddGroup.mk' (rationalEquivalences C s k) c := by
  subst h
  rfl

/-- Flat pullback on Chow groups does not depend on how the structure morphism of the source is
written. -/
theorem flatPullbackChow_heq_of_structure_eq {A B : Scheme.{u}} {sA sA' : A ⟶ C.S}
    [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (f : A ⟶ B) [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sB = sA) (hf' : f ≫ sB = sA')
    (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension f r) (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sA sB f hf r hr k)
    (hfac' : FlatPullbackFactorsThroughRationalEquivalence C sA' sB f hf' r hr k)
    (h : sA = sA') (α : chowGroup C sB k) :
    flatPullbackChow C sA sB f hf r hr k hfac α ≍ flatPullbackChow C sA' sB f hf' r hr k hfac' α :=
        by
  subst h
  rfl

/-- Flat pullback on Chow groups at two equal degrees. -/
theorem flatPullbackChow_heq_of_degree_eq {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (f : A ⟶ B)
    [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sB = sA) (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension f r) {k k' : ℤ} (h : k = k')
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sA sB f hf r hr k)
    (hfac' : FlatPullbackFactorsThroughRationalEquivalence C sA sB f hf r hr k')
    {x : chowGroup C sB k} {y : chowGroup C sB k'} (hxy : x ≍ y) :
    flatPullbackChow C sA sB f hf r hr k hfac x ≍ flatPullbackChow C sA sB f hf r hr k' hfac' y :=
        by
  subst h
  rw [eq_of_heq hxy]

/-- The Gysin map of Stacks 02TO at two equal degrees. -/
theorem gysinChowOfInvertible_heq {A : Scheme.{u}} (s : A ⟶ C.S) [LocallyOfFiniteType s]
    (L : A.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible A.sheaf.obj A.ringCatSheaf.property L]
    (σ : Γ(L, ⊤)) {k k' : ℤ} (h : k = k') {x : chowGroup C s (k + 1)}
    {y : chowGroup C s (k' + 1)} (hxy : x ≍ y) :
    gysinChowOfInvertible C s k L σ x ≍ gysinChowOfInvertible C s k' L σ y := by
  subst h
  rw [eq_of_heq hxy]

/-- Pushforward along an isomorphism undoes pushforward along its inverse. -/
theorem chowPushforwardOfIso_inv_apply {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (e : A ⟶ B) [IsIso e]
    (he : e ≫ sB = sA) (he' : inv e ≫ sA = sB) (k : ℤ) (y : chowGroup C sB k) :
    chowPushforwardOfIso C sA sB e he k (chowPushforwardOfIso C sB sA (inv e) he' k y) = y := by
  rw [chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_of_eq_id _ _ _ _ (IsIso.inv_hom_id e)]
  rfl

/-- `Eq.mp` is heterogeneously the identity. -/
theorem eqMp_heq_self {α β : Sort u} (h : α = β) (a : α) : Eq.mp h a ≍ a := by
  subst h
  rfl

/-- Two cycles with the same coefficients in equal degrees have heterogeneously equal classes. -/
theorem mk_heq_of_val_eq {A : Scheme.{u}} (s : A ⟶ C.S) [LocallyOfFiniteType s] {k k' : ℤ}
    (h : k = k') (x : CycleGroup C s k) (y : CycleGroup C s k') (hxy : x.1 = y.1) :
    QuotientAddGroup.mk' (rationalEquivalences C s k) x ≍
      QuotientAddGroup.mk' (rationalEquivalences C s k') y := by
  subst h
  rw [Subtype.ext hxy]

/-- A cycle read in an equal degree; unlike the transport `h ▸ c`, its coefficient function is
definitionally that of `c`. -/
def cycleOfDegreeEq {A : Scheme.{u}} (s : A ⟶ C.S) [LocallyOfFiniteType s] {k k' : ℤ}
    (h : k = k') (c : CycleGroup C s k) : CycleGroup C s k' :=
  ⟨c.1, by subst h; exact c.2⟩

/-- Pushforward of a cycle read in an equal degree, on coefficients. -/
theorem properPushforward_val_cycleOfDegreeEq {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (f : A ⟶ B) [IsProper f]
    (hf : f ≫ sB = sA) {k k' : ℤ} (h : k = k') (c : CycleGroup C sA k) :
    (properPushforward C sA sB f hf k' (cycleOfDegreeEq sA h c)).1 =
      (properPushforward C sA sB f hf k c).1 := by
  subst h
  rfl

end Bookkeeping

/-! ### The summands on the two sides -/

section Summands

variable {C : ChowSituation.{u}} (hC : IsDedekindChowBase C) {X Y Z T : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (w : Y ⟶ Z)
  [LocallyOfFiniteType w] (t : T ⟶ Z) [LocallyOfFiniteType t] (n m q : ℤ)
  (c' : CanonicalBivariantClass C (w ≫ sZ) sZ w rfl q) (a₀ : CycleGroup C sX n)
  (b₀ : CycleGroup C (t ≫ sZ) m) (γ₀ : CycleGroup C (pullback.fst w t ≫ (w ≫ sZ)) (m - q))

/-- The summand of `α × β` at a point `x` of the support of `α`, on `closure {x} ×_S T`, the
summand of `α × γ` at `x`, on `closure {x} ×_S (Y ×_Z T)`, and a cycle on
`Y ×_Z (closure {x} ×_S T)` which represents `c'` capped with the first and is the second
transported across the canonical isomorphism. The fibre product `Y ×_Z (closure {x} ×_S T)` is
formed at a test morphism `gV` equal to `closure {x} ×_S T ⟶ T ⟶ Z`, presented as convenient. -/
def SummandCapData (x : X) : Prop :=
  ∃ (gV : (dedekindPointFibre sX (t ≫ sZ) x).subscheme ⟶ Z) (_ : LocallyOfFiniteType gV)
    (hgV : (dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫ (pullback.snd sX (t ≫ sZ) ≫ t) = gV)
    (a : CycleGroup C ((dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫
      (pullback.fst sX (t ≫ sZ) ≫ sX)) (n + m - 1))
    (a' : CycleGroup C ((dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x).subschemeι ≫
      (pullback.fst sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ sX)) (n + (m - q) - 1))
    (b : CycleGroup C (pullback.fst w gV ≫ (w ≫ sZ)) (n + m - 1 - q)),
    (∀ z, (properPushforward C ((dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫
      (pullback.fst sX (t ≫ sZ) ≫ sX)) (pullback.fst sX (t ≫ sZ) ≫ sX)
      (dedekindPointFibre sX (t ≫ sZ) x).subschemeι rfl (n + m - 1) a).1 z =
        ∑ᶠ y : T, exteriorProductDedekindTerm C sX (t ≫ sZ) n m a₀ b₀ z (x, y)) ∧
    (∀ z, (properPushforward C
      ((dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x).subschemeι ≫
        (pullback.fst sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ sX))
      (pullback.fst sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ sX)
      (dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x).subschemeι rfl
        (n + (m - q) - 1) a').1 z =
        ∑ᶠ y : (pullback w t : Scheme.{u}), exteriorProductDedekindTerm C sX
          (pullback.fst w t ≫ (w ≫ sZ)) n (m - q) a₀ γ₀ z (x, y)) ∧
    QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst w gV ≫ (w ≫ sZ))
        (n + m - 1 - q)) b =
      c'.cap gV (n + m - 1) (chowGroupCongr C
        (by rw [← hgV]; simp only [Category.assoc, pullback.condition])
          (n + m - 1) (QuotientAddGroup.mk' (rationalEquivalences C
            ((dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫ (pullback.fst sX (t ≫ sZ) ≫ sX))
            (n + m - 1)) a)) ∧
    ∀ z, (properPushforward C (pullback.fst w gV ≫ (w ≫ sZ))
      (pullback.fst w (pullback.snd sX (t ≫ sZ) ≫ t) ≫ (w ≫ sZ))
      (testBaseChangeMapOfEq w (pullback.snd sX (t ≫ sZ) ≫ t)
        (dedekindPointFibre sX (t ≫ sZ) x).subschemeι gV hgV)
      (testBaseChangeMapOfEq_fst_assoc _ _ _ _ _ _) (n + m - 1 - q) b).1 z =
      (properPushforward C
        ((dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x).subschemeι ≫
          (pullback.fst sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ sX))
        (pullback.fst w (pullback.snd sX (t ≫ sZ) ≫ t) ≫ (w ≫ sZ))
        ((dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x).subschemeι ≫
          mixedCommuteHom sX sZ w t)
        (by rw [Category.assoc, mixedCommuteHom_comp_structureMorphism]) (n + (m - q) - 1)
        a').1 z

/-- If the degree of the flat pullback at a dominating point is not `n + m - 1`, the terms of the
exterior product attached to that point vanish. -/
theorem finsum_exteriorProductDedekindTerm_eq_zero {X' Y' : Scheme.{u}} (f : X' ⟶ C.S)
    [LocallyOfFiniteType f] (g : Y' ⟶ C.S) [LocallyOfFiniteType g] (n m : ℤ)
    (α : CycleGroup C f n) (β : CycleGroup C g m) (x : X') (hdom : DominatesBaseComponent C f x)
    [LocallyOfFiniteType ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g)]
    [Flat ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g)] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension
      ((dedekindPointFibre f g x).subschemeι ≫ pullback.snd f g) r)
    (hdeg : ¬ m + (r : ℤ) = n + m - 1) (z : (pullback f g : Scheme.{u})) :
    ∑ᶠ y : Y', exteriorProductDedekindTerm C f g n m α β z (x, y) = 0 := by
  by_cases hz : z ∈ Set.range (dedekindPointFibre f g x).subschemeι.base
  · obtain ⟨w, rfl⟩ := hz
    rw [finsum_exteriorProductDedekindTerm_of_flat C f g n m α β x hdom r hr w, ite_eq_right hdeg]
  · exact finsum_eq_zero_of_forall_eq_zero fun y ↦
      exteriorProductDedekindTerm_eq_zero_of_notMem_range C f g n m α β x y hz

include hC in
/-- **The summands at a dominating point.** If `[γ₀] = c' ∩ [b₀]`, then capping with `c'` commutes
with the summands at a point `x` whose closure dominates an irreducible component of the base, in
the sense of `SummandCapData`. -/
theorem summandCapData_of_dominates
    (hγ₀ : QuotientAddGroup.mk' (rationalEquivalences C _ (m - q)) γ₀ =
      c'.cap t m (QuotientAddGroup.mk' (rationalEquivalences C _ m) b₀))
    (x : X) (hdom : DominatesBaseComponent C sX x) :
    SummandCapData sX sZ w t n m q c' a₀ b₀ γ₀ x := by
  classical
  obtain ⟨hflat, r, hr, hrel⟩ :=
    exists_relativeDimension_dedekindPointFibre C sX (t ≫ sZ) hC x hdom
  obtain ⟨hflat', r', hr', hrel'⟩ :=
    exists_relativeDimension_dedekindPointFibre C sX (pullback.fst w t ≫ (w ≫ sZ)) hC x hdom
  obtain rfl : r = r' := by lia
  by_cases hdeg : m + (r : ℤ) = n + m - 1
  swap
  · have hdeg' : ¬ m - q + (r : ℤ) = n + (m - q) - 1 := by lia
    refine ⟨_, inferInstance, rfl, 0, 0, 0, fun z ↦ ?_, fun z ↦ ?_, by simp,
      fun z ↦ by simp [properPushforward_zero]⟩
    · rw [properPushforward_zero, finsum_exteriorProductDedekindTerm_eq_zero sX (t ≫ sZ) n m
        a₀ b₀ x hdom r hr hdeg z]
      rfl
    · rw [properPushforward_zero, finsum_exteriorProductDedekindTerm_eq_zero sX
        (pullback.fst w t ≫ (w ≫ sZ)) n (m - q) a₀ γ₀ x hdom r hr' hdeg' z]
      rfl
  have hdeg' : m - q + (r : ℤ) = n + (m - q) - 1 := by lia
  have hdq : n + (m - q) - 1 = n + m - 1 - q := by ring
  have hgV : (dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫ (pullback.snd sX (t ≫ sZ) ≫ t) =
      ((dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫ pullback.snd sX (t ≫ sZ)) ≫ t :=
    (Category.assoc _ _ _).symm
  obtain ⟨ρ, hρiso, hρfst, hρsnd, hρbase, hρtest⟩ :=
    exists_isIso_comp_pullback_fst_eq_mixedPointFibre sX sZ w t x hgV
  have hρh : ρ ≫ bivariantBaseChangeMap w t
      ((dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫ pullback.snd sX (t ≫ sZ)) =
      (dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x).subschemeι ≫
        pullback.snd sX (pullback.fst w t ≫ (w ≫ sZ)) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, bivariantBaseChangeMap_fst]
      exact hρfst
    · simp only [Category.assoc, bivariantBaseChangeMap, pullback.lift_snd]
      rw [reassoc_of% hρsnd, mixedPointFibreMap_subschemeι_assoc, mixedCommuteSnd_snd]
  have hbase : ((dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫ pullback.snd sX (t ≫ sZ)) ≫
      (t ≫ sZ) = (dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫
        (pullback.fst sX (t ≫ sZ) ≫ sX) := by
    rw [Category.assoc, ← pullback.condition]
  have hbase' : ((dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x).subschemeι ≫
      pullback.snd sX (pullback.fst w t ≫ (w ≫ sZ))) ≫ (pullback.fst w t ≫ (w ≫ sZ)) =
      (dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x).subschemeι ≫
        (pullback.fst sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ sX) := by
    rw [Category.assoc, ← pullback.condition]
  have hsqh := isPullback_bivariantBaseChangeMap w t
    ((dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫ pullback.snd sX (t ≫ sZ))
  have : LocallyOfFiniteType (bivariantBaseChangeMap w t
      ((dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫ pullback.snd sX (t ≫ sZ))) :=
    MorphismProperty.of_isPullback hsqh inferInstance
  have : Flat (bivariantBaseChangeMap w t
      ((dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫ pullback.snd sX (t ≫ sZ))) :=
    MorphismProperty.of_isPullback hsqh inferInstance
  have hrh : AlgebraicGeometry.RelativeDimension (bivariantBaseChangeMap w t
      ((dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫ pullback.snd sX (t ≫ sZ))) r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback hsqh hr
  refine ⟨_, inferInstance, hgV,
    hdeg ▸ flatPullback C ((dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫
      (pullback.fst sX (t ≫ sZ) ≫ sX)) (t ≫ sZ)
      ((dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫ pullback.snd sX (t ≫ sZ)) hbase r hr m
      (a₀.1 x • b₀),
    hdeg' ▸ flatPullback C ((dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x).subschemeι ≫
      (pullback.fst sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ sX)) (pullback.fst w t ≫ (w ≫ sZ))
      ((dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x).subschemeι ≫
        pullback.snd sX (pullback.fst w t ≫ (w ≫ sZ))) hbase' r hr' (m - q) (a₀.1 x • γ₀),
    hdq ▸ properPushforward C
      ((dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x).subschemeι ≫
        (pullback.fst sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ sX))
      (pullback.fst w (((dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫
        pullback.snd sX (t ≫ sZ)) ≫ t) ≫ (w ≫ sZ)) ρ hρbase (n + (m - q) - 1)
      (hdeg' ▸ flatPullback C
        ((dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x).subschemeι ≫
          (pullback.fst sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ sX)) (pullback.fst w t ≫ (w ≫ sZ))
        ((dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x).subschemeι ≫
          pullback.snd sX (pullback.fst w t ≫ (w ≫ sZ))) hbase' r hr' (m - q) (a₀.1 x • γ₀)),
    properPushforward_flatPullback_of_dominates C sX (t ≫ sZ) n m a₀ b₀ x hdom r hr hdeg _
      (val_cycleGroup_cast C _ hdeg _),
    properPushforward_flatPullback_of_dominates C sX (pullback.fst w t ≫ (w ≫ sZ)) n (m - q) a₀
      γ₀ x hdom r hr' hdeg' _ (val_cycleGroup_cast C _ hdeg' _), ?_, fun z ↦ ?_⟩
  · have hnat := c'.flat_naturality_of_relativeDimension t
      ((dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫ pullback.snd sX (t ≫ sZ)) r hr
      (bivariantBaseChangeMap w t
        ((dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫ pullback.snd sX (t ≫ sZ))) hsqh
      (bivariantBaseChangeMap_fst w t _) m hrh
      (QuotientAddGroup.mk' (rationalEquivalences C (t ≫ sZ) m) (a₀.1 x • b₀))
    have h02RG := flatPullbackChow_chowPushforwardOfIso C (pullback.fst w t ≫ (w ≫ sZ))
      ((dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x).subschemeι ≫
        (pullback.fst sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ sX)) (pullback.fst w t ≫ (w ≫ sZ))
      (pullback.fst w (((dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫
        pullback.snd sX (t ≫ sZ)) ≫ t) ≫ (w ≫ sZ)) (𝟙 _) (Category.id_comp _) ρ hρbase
      ((dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x).subschemeι ≫
        pullback.snd sX (pullback.fst w t ≫ (w ≫ sZ))) hbase'
      (bivariantBaseChangeMap w t
        ((dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫ pullback.snd sX (t ≫ sZ)))
      (by rw [← Category.assoc, bivariantBaseChangeMap_fst]) (by rw [Category.comp_id, hρh]) r
      hr' hrh (m - q) (flatPullbackDescends C _ _ _ _ _ _ _)
      (flatPullbackDescends C _ _ _ _ _ _ _)
      (QuotientAddGroup.mk' (rationalEquivalences C _ (m - q)) (a₀.1 x • γ₀))
    rw [chowPushforwardOfIso_id] at h02RG
    have hcap : QuotientAddGroup.mk' (rationalEquivalences C _ (m - q)) (a₀.1 x • γ₀) =
        c'.cap t m (QuotientAddGroup.mk' (rationalEquivalences C (t ≫ sZ) m) (a₀.1 x • b₀)) := by
      rw [map_zsmul, map_zsmul, hγ₀, map_zsmul]
    apply eq_of_heq
    refine (mk_cast_heq _ hdq _).trans ?_
    rw [← chowPushforwardOfIso_mk]
    refine (chowPushforwardOfIso_heq ρ hρbase hρbase rfl rfl hdeg'.symm
      ((mk_cast_heq _ hdeg' _).trans (heq_of_eq (flatPullbackChow_mk C _ _ _ hbase' r hr' (m - q)
        (flatPullbackDescends C _ _ _ _ _ _ _) _).symm))).trans ?_
    refine (heq_of_eq (h02RG.symm.trans (by rw [hcap]))).trans (hnat.symm.trans ?_)
    refine BivariantClass.cap_heq c' _ hdeg ?_
    refine HEq.trans ?_ (HEq.trans (mk_cast_heq _ hdeg _).symm (chowGroupCongr_heq C _ _ _).symm)
    refine HEq.trans ?_ (heq_of_eq (flatPullbackChow_mk C _ _ _ hbase r hr m
      (flatPullbackDescends C _ _ _ _ _ _ _) _))
    exact flatPullbackChow_heq_of_structure_eq (t ≫ sZ) _ _ hbase r hr m _ _
      (by rw [← hbase]; rfl) _
  · rw [properPushforward_val_cast, properPushforward_properPushforward,
      properPushforward_congr C _ _ _ _ hρtest]

/-- **Capping commutes with a Gysin map followed by a flat pullback.** Let `D ⊆ T` be the zero
scheme of a section of an invertible module on a test scheme `t : T ⟶ Z`, let `E ⊆ Y ×_Z T` be the
zero scheme of the pulled-back section, and let `wT : K ⟶ D` and `wV : K' ⟶ E` be flat of relative
dimension `r`, identified across an isomorphism `ρ : K' ≅ Y ×_Z K` lying over `Y ×_Z T`. Then
capping with `c'` commutes with `wT^* ∘ i_D^*`, the two sides compared through `ρ`. -/
theorem cap_flatPullbackChow_gysinChowOfInvertible {C : ChowSituation.{u}} {Y Z T K K' : Scheme.{u}}
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (w : Y ⟶ Z) [LocallyOfFiniteType w] (q : ℤ)
    (c' : CanonicalBivariantClass C (w ≫ sZ) sZ w rfl q) (t : T ⟶ Z) [LocallyOfFiniteType t]
    (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (σ : Γ(L, ⊤)) (sK : K ⟶ C.S) [LocallyOfFiniteType sK] (sK' : K' ⟶ C.S)
    [LocallyOfFiniteType sK']
    (wT : K ⟶ (Stacks.Divisors.zeroScheme T L σ).subscheme) [LocallyOfFiniteType wT] [Flat wT]
    (_hwT : wT ≫ ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ (t ≫ sZ)) = sK) (r : ℕ)
    (hrT : AlgebraicGeometry.RelativeDimension wT r)
    (wV : K' ⟶ (Stacks.Divisors.zeroScheme (pullback w t)
      ((Scheme.Modules.pullback (pullback.snd w t)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd w t) L σ)).subscheme)
    [LocallyOfFiniteType wV] [Flat wV]
    (hwV : wV ≫ ((Stacks.Divisors.zeroScheme (pullback w t)
      ((Scheme.Modules.pullback (pullback.snd w t)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd w t) L σ)).subschemeι ≫
        (pullback.fst w t ≫ (w ≫ sZ))) = sK')
    (hrV : AlgebraicGeometry.RelativeDimension wV r)
    (ρ : K' ⟶ pullback w (wT ≫ ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ t))) [IsIso ρ]
    (hρ : ρ ≫ (pullback.fst w (wT ≫ ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ t)) ≫
      (w ≫ sZ)) = sK')
    (hρV : ρ ≫ bivariantBaseChangeMap w ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ t) wT ≫
        bivariantBaseChangeMap w t (Stacks.Divisors.zeroScheme T L σ).subschemeι =
      wV ≫ (Stacks.Divisors.zeroScheme (pullback w t)
        ((Scheme.Modules.pullback (pullback.snd w t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd w t) L σ)).subschemeι)
    (k : ℤ) (β : chowGroup C (t ≫ sZ) (k + 1)) :
    chowPushforwardOfIso C sK' (pullback.fst w (wT ≫ ((Stacks.Divisors.zeroScheme T L σ).subschemeι
        ≫ t)) ≫ (w ≫ sZ)) ρ hρ (k - q + r)
      (flatPullbackChow C sK' _ wV hwV r hrV (k - q) (flatPullbackDescends C _ _ _ _ _ _ _)
        (gysinChowOfInvertible C (pullback.fst w t ≫ (w ≫ sZ)) (k - q)
          ((Scheme.Modules.pullback (pullback.snd w t)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd w t) L σ)
          (Eq.mp (congrArg (chowGroup C (pullback.fst w t ≫ (w ≫ sZ)))
            (by omega : (k + 1) - q = (k - q) + 1)) (c'.cap t (k + 1) β)))) ≍
      c'.cap (wT ≫ ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ t)) (k + r)
        (flatPullbackChow C ((wT ≫ ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ t)) ≫ sZ)
          (((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ t) ≫ sZ) wT
          (by simp [Category.assoc]) r hrT k (flatPullbackDescends C _ _ _ _ _ _ _)
          (gysinChowOfInvertible C (t ≫ sZ) k L σ β)) := by
  obtain ⟨e, he⟩ : ∃ e : pullback w ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ t) ≅
      (Stacks.Divisors.zeroScheme (pullback w t) ((Scheme.Modules.pullback (pullback.snd w t)).obj
          L) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd w t) L σ)).subscheme,
      e.hom ≫ (Stacks.Divisors.zeroScheme (pullback w t) ((Scheme.Modules.pullback (pullback.snd w
          t)).obj L) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd w t) L σ)).subschemeι
              = bivariantBaseChangeMap w t (Stacks.Divisors.zeroScheme T L σ).subschemeι :=
    ⟨(isPullback_bivariantBaseChangeMap w t (Stacks.Divisors.zeroScheme T L
        σ).subschemeι).flip.isoIsPullback _ _
        (Stacks.Divisors.isPullback_zeroSchemePullbackMap (pullback.snd w t) _ _),
      IsPullback.isoIsPullback_hom_fst _ _ _ _⟩
  have hebase : e.hom ≫ ((Stacks.Divisors.zeroScheme (pullback w t) ((Scheme.Modules.pullback
      (pullback.snd w t)).obj L) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd w t) L
          σ)).subschemeι ≫ pullback.fst w t ≫ (w ≫ sZ)) =
      pullback.fst w ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ t) ≫ (w ≫ sZ) := by
    rw [← Category.assoc, he, ← Category.assoc, bivariantBaseChangeMap_fst]
  have hsqh := isPullback_bivariantBaseChangeMap w ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫
      t) wT
  have : LocallyOfFiniteType (bivariantBaseChangeMap w ((Stacks.Divisors.zeroScheme T L
      σ).subschemeι ≫ t) wT) :=
    MorphismProperty.of_isPullback hsqh inferInstance
  have : Flat (bivariantBaseChangeMap w ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ t) wT) :=
    MorphismProperty.of_isPullback hsqh inferInstance
  have hrh : AlgebraicGeometry.RelativeDimension
      (bivariantBaseChangeMap w ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ t) wT) r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback hsqh hrT
  have hsq : bivariantBaseChangeMap w ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ t) wT ≫
      e.hom = inv ρ ≫ wV := by
    rw [IsIso.eq_inv_comp]
    refine (cancel_mono (Stacks.Divisors.zeroScheme (pullback w t) ((Scheme.Modules.pullback
        (pullback.snd w t)).obj L) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd w t) L
            σ)).subschemeι).1 ?_
    rw [Category.assoc, Category.assoc, he, hρV]
  have hu₁ : inv ρ ≫ sK' = pullback.fst w (wT ≫ ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫
      t)) ≫ (w ≫ sZ) := by
    rw [← hρ, IsIso.inv_hom_id_assoc]
  have hgys := c'.gysin_naturality_gysinChowOfInvertible t L σ k e he hebase β
  have h02RG := flatPullbackChow_chowPushforwardOfIso C
    (pullback.fst w ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ t) ≫ (w ≫ sZ))
    (pullback.fst w (wT ≫ ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ t)) ≫ (w ≫ sZ))
    ((Stacks.Divisors.zeroScheme (pullback w t) ((Scheme.Modules.pullback (pullback.snd w t)).obj
        L) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd w t) L σ)).subschemeι ≫
            pullback.fst w t ≫ (w ≫ sZ)) sK' e.hom hebase (inv ρ) hu₁
    (bivariantBaseChangeMap w ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ t) wT)
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (w ≫ sZ))
      (bivariantBaseChangeMap_fst _ _ _))) wV hwV hsq r hrh hrV (k - q)
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
    (c'.cap ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ t) k (gysinChowOfInvertible C (t ≫ sZ)
        k L σ β))
  have hnat := c'.flat_naturality_of_relativeDimension ((Stacks.Divisors.zeroScheme T L
      σ).subschemeι ≫ t) wT r hrT
    (bivariantBaseChangeMap w ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ t) wT) hsqh
        (bivariantBaseChangeMap_fst _ _ _)
    k hrh (gysinChowOfInvertible C (t ≫ sZ) k L σ β)
  rw [← hgys]
  refine HEq.trans (heq_of_eq ?_) hnat.symm
  exact (congrArg (chowPushforwardOfIso C _ _ ρ hρ (k - q + r)) h02RG).trans
    (chowPushforwardOfIso_inv_apply _ _ ρ hρ hu₁ _ _)

/-- The class of a multiple of the Gysin image of a cycle is the Gysin map of the class. -/
private theorem mk_zsmul_gysinCycleMap {C : ChowSituation.{u}} {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (k : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme X L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme X L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj L))
    (z : ℤ) (α : CycleGroup C p (k + 1)) :
    QuotientAddGroup.mk' (rationalEquivalences C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k) (z • gysinCycleMap C p k L s htriv α) =
      gysinChowOfInvertible C p k L s
        (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1)) (z • α)) := by
  rw [map_zsmul, map_zsmul, map_zsmul]
  congr 1
  exact (mk_gysinCycleMap C _ _ _ _ htriv _).trans (gysinChowOfInvertible_mk C _ _ _ _ _).symm

/-- **The summand at a point over a closed point, on cycles.** The cycle form of
`Stacks.Chow.cap_flatPullbackChow_gysinChowOfInvertible`: if `a` is the flat pullback along `wT`
of the Gysin image of `z b₀`, `a'` the flat pullback along `wV` of the Gysin image of `z γ₀`,
where `[γ₀] = c' ∩ [b₀]`, and `b` is `a'` transported by `ρ`, then `[b] = c' ∩ [a]`. -/
theorem mk_eq_cap_of_flatPullback_gysinCycleMap {C : ChowSituation.{u}} {Y Z T K K' : Scheme.{u}}
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (w : Y ⟶ Z) [LocallyOfFiniteType w] (q : ℤ)
    (c' : CanonicalBivariantClass C (w ≫ sZ) sZ w rfl q) (t : T ⟶ Z) [LocallyOfFiniteType t]
    (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (σ : Γ(L, ⊤))
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial (Stacks.Divisors.zeroScheme T L
        σ).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme T L σ).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme T L σ).subschemeι).obj L))
    (htrivV : AlgebraicGeometry.SheafOfModules.IsTrivial (Stacks.Divisors.zeroScheme (pullback w t)
        ((Scheme.Modules.pullback (pullback.snd w t)).obj L)
            (AlgebraicGeometry.pullbackGlobalSections (pullback.snd w t) L σ)).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme (pullback w t) ((Scheme.Modules.pullback (pullback.snd w t)).obj
          L) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd w t) L
              σ)).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme (pullback w t)
          ((Scheme.Modules.pullback (pullback.snd w t)).obj L)
              (AlgebraicGeometry.pullbackGlobalSections (pullback.snd w t) L σ)).subschemeι).obj
                  ((Scheme.Modules.pullback (pullback.snd w t)).obj L)))
    (sK : K ⟶ C.S) [LocallyOfFiniteType sK] (sK' : K' ⟶ C.S) [LocallyOfFiniteType sK']
    (wT : K ⟶ (Stacks.Divisors.zeroScheme T L σ).subscheme) [LocallyOfFiniteType wT] [Flat wT]
    (hwT : wT ≫ ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ (t ≫ sZ)) = sK) (r : ℕ)
    (hrT : AlgebraicGeometry.RelativeDimension wT r)
    (wV : K' ⟶ (Stacks.Divisors.zeroScheme (pullback w t) ((Scheme.Modules.pullback (pullback.snd w
        t)).obj L) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd w t) L σ)).subscheme)
            [LocallyOfFiniteType wV] [Flat wV]
    (hwV : wV ≫ ((Stacks.Divisors.zeroScheme (pullback w t) ((Scheme.Modules.pullback (pullback.snd
        w t)).obj L) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd w t) L σ)).subschemeι
            ≫ (pullback.fst w t ≫ (w ≫ sZ))) = sK')
    (hrV : AlgebraicGeometry.RelativeDimension wV r)
    (ρ : K' ⟶ pullback w (wT ≫ ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ t))) [IsIso ρ]
    (hρ : ρ ≫ (pullback.fst w (wT ≫ ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ t)) ≫ (w ≫
        sZ)) = sK')
    (hρV : ρ ≫ bivariantBaseChangeMap w ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ t) wT ≫
        bivariantBaseChangeMap w t (Stacks.Divisors.zeroScheme T L σ).subschemeι = wV ≫
            (Stacks.Divisors.zeroScheme (pullback w t) ((Scheme.Modules.pullback (pullback.snd w
                t)).obj L) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd w t) L
                    σ)).subschemeι)
    (n m : ℤ) (z : ℤ) (b₀ : CycleGroup C (t ≫ sZ) m) (b₀' : CycleGroup C (t ≫ sZ) (m - 1 + 1))
    (hb₀' : b₀'.1 = b₀.1) (γ₀ : CycleGroup C (pullback.fst w t ≫ (w ≫ sZ)) (m - q))
    (γ₀' : CycleGroup C (pullback.fst w t ≫ (w ≫ sZ)) (m - q - 1 + 1)) (hγ₀' : γ₀'.1 = γ₀.1)
    (hγ₀ : QuotientAddGroup.mk' (rationalEquivalences C _ (m - q)) γ₀ =
      c'.cap t m (QuotientAddGroup.mk' (rationalEquivalences C _ m) b₀))
    (hdeg : m - 1 + (r : ℤ) = n + m - 1)
    (a : CycleGroup C sK (n + m - 1))
    (ha : a.1 = (flatPullback C sK _ wT hwT r hrT (m - 1)
      (z • gysinCycleMap C (t ≫ sZ) (m - 1) L σ htriv b₀')).1)
    (a' : CycleGroup C sK' (n + (m - q) - 1))
    (ha' : a'.1 = (flatPullback C sK' _ wV hwV r hrV (m - q - 1)
      (z • gysinCycleMap C (pullback.fst w t ≫ (w ≫ sZ)) (m - q - 1) ((Scheme.Modules.pullback
          (pullback.snd w t)).obj L) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd w t) L
              σ) htrivV γ₀')).1)
    (b : CycleGroup C (pullback.fst w (wT ≫ ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ t)) ≫
        (w ≫ sZ)) (n + m - 1 - q))
    (hb : b.1 = (properPushforward C sK' _ ρ hρ (n + (m - q) - 1) a').1)
    (hsK : sK = (wT ≫ ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ t)) ≫ sZ) :
    QuotientAddGroup.mk' (rationalEquivalences C _ (n + m - 1 - q)) b =
      c'.cap (wT ≫ ((Stacks.Divisors.zeroScheme T L σ).subschemeι ≫ t)) (n + m - 1)
        (chowGroupCongr C hsK (n + m - 1) (QuotientAddGroup.mk' (rationalEquivalences C sK
          (n + m - 1)) a)) := by
  have hgysT := mk_zsmul_gysinCycleMap (t ≫ sZ) (m - 1) L σ htriv z b₀'
  have hgysV := mk_zsmul_gysinCycleMap (pullback.fst w t ≫ (w ≫ sZ)) (m - q - 1)
    ((Scheme.Modules.pullback (pullback.snd w t)).obj L)
    (AlgebraicGeometry.pullbackGlobalSections (pullback.snd w t) L σ) htrivV z γ₀'
  have hcap : QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst w t ≫ (w ≫ sZ))
      (m - q - 1 + 1)) (z • γ₀') ≍
      Eq.mp (congrArg (chowGroup C (pullback.fst w t ≫ (w ≫ sZ)))
        (by omega : (m - 1 + 1) - q = (m - 1 - q) + 1))
        (c'.cap t (m - 1 + 1) (QuotientAddGroup.mk' (rationalEquivalences C (t ≫ sZ) (m - 1 + 1))
          (z • b₀'))) := by
    refine HEq.trans ?_ (eqMp_heq_self _ _).symm
    refine HEq.trans (mk_heq_of_val_eq _ (by omega) _ (z • γ₀) (by simp [hγ₀'])) ?_
    refine HEq.trans (heq_of_eq ?_) (BivariantClass.cap_heq c' t (Int.sub_add_cancel m 1).symm
      (mk_heq_of_val_eq _ (Int.sub_add_cancel m 1).symm (z • b₀) _ (by simp [hb₀'])))
    exact ((map_zsmul (QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst w t ≫ (w ≫ sZ))
      (m - q))) _ _).trans (congrArg (z • ·) hγ₀)).trans
      ((map_zsmul _ _ _).symm.trans (congrArg (c'.cap t m) (map_zsmul (QuotientAddGroup.mk'
        (rationalEquivalences C (t ≫ sZ) m)) _ _).symm))
  have hcomm := cap_flatPullbackChow_gysinChowOfInvertible sZ w q c' t L σ sK sK' wT hwT r hrT wV
    hwV hrV ρ hρ hρV (m - 1)
    (QuotientAddGroup.mk' (rationalEquivalences C (t ≫ sZ) (m - 1 + 1)) (z • b₀'))
  apply eq_of_heq
  refine HEq.trans (mk_heq_of_val_eq _ (by omega) b _ hb) ?_
  refine HEq.trans (heq_of_eq (chowPushforwardOfIso_mk C _ _ ρ hρ _ a').symm) ?_
  refine HEq.trans (chowPushforwardOfIso_heq ρ hρ hρ rfl rfl (by omega) ?_) (hcomm.trans ?_)
  · refine HEq.trans (mk_heq_of_val_eq _ (by omega) a' _ ha') ?_
    refine HEq.trans (heq_of_eq (flatPullbackChow_mk C _ _ _ hwV r hrV (m - q - 1)
      (flatPullbackDescends C _ _ _ _ _ _ _) _).symm) ?_
    refine flatPullbackChow_heq_of_degree_eq _ _ wV hwV r hrV (by omega) _ _ ?_
    rw [hgysV]
    exact gysinChowOfInvertible_heq _ _ _ (by omega) hcap
  · refine BivariantClass.cap_heq c' _ hdeg ?_
    refine HEq.trans ?_ (chowGroupCongr_heq C _ _ _).symm
    refine HEq.trans ?_ (mk_heq_of_val_eq _ hdeg _ a ha.symm)
    refine HEq.trans ?_ (heq_of_eq (flatPullbackChow_mk C _ _ _ hwT r hrT (m - 1)
      (flatPullbackDescends C _ _ _ _ _ _ _) _))
    rw [hgysT]
    exact flatPullbackChow_heq_of_structure_eq _ _ _ hwT r hrT (m - 1) _ _ hsK.symm _


include hC in
/-- **The summands at a point over a closed point.** If `[γ₀] = c' ∩ [b₀]`, then capping with `c'`
commutes with the summands at a point `x` of the support of `a₀` whose closure does not dominate an
irreducible component of the base, in the sense of `SummandCapData`. -/
theorem summandCapData_of_not_dominates
    (hγ₀ : QuotientAddGroup.mk' (rationalEquivalences C _ (m - q)) γ₀ =
      c'.cap t m (QuotientAddGroup.mk' (rationalEquivalences C _ m) b₀))
    (x : X) (hx : a₀.1 x ≠ 0) (hnd : ¬ DominatesBaseComponent C sX x) :
    SummandCapData sX sZ w t n m q c' a₀ b₀ γ₀ x := by
  classical
  have hs : closure ({sX.base x} : Set C.S) ∉ irreducibleComponents C.S := hnd
  obtain ⟨L, hLinv, σ, hσ, htriv⟩ := hC.exists_section_zeroScheme_eq hs
  have htrivT := Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections (t ≫ sZ)
    L σ htriv
  have hDT := Stacks.Divisors.zeroScheme_pullback (t ≫ sZ) L σ
  obtain ⟨wT, hwTlft, hwTflat, r, hwT, hrT, hrn⟩ := exists_flat_dedekindPointFibre_fibre C sX
    (t ≫ sZ) n hC x hnd L σ hσ a₀ hx _ hDT
  have htrivV := Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections
    (pullback.snd w t) _ _ htrivT
  have hDV : Stacks.Divisors.zeroScheme (pullback w t)
      ((Scheme.Modules.pullback (pullback.snd w t)).obj
        ((Scheme.Modules.pullback (t ≫ sZ)).obj L))
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd w t) _
        (AlgebraicGeometry.pullbackGlobalSections (t ≫ sZ) L σ)) =
      (Stacks.Divisors.zeroScheme C.S L σ).comap (pullback.fst w t ≫ (w ≫ sZ)) := by
    rw [Stacks.Divisors.zeroScheme_pullback, hDT, ← Scheme.IdealSheafData.comap_comp,
      ← Category.assoc, ← pullback.condition, Category.assoc]
  obtain ⟨wV, hwVlft, hwVflat, r', hwV, hrV, hrn'⟩ := exists_flat_dedekindPointFibre_fibre C sX
    (pullback.fst w t ≫ (w ≫ sZ)) n hC x hnd L σ hσ a₀ hx _ hDV
  obtain rfl : r = r' := by lia
  have hdeg : m - 1 + (r : ℤ) = n + m - 1 := by omega
  have hdeg' : m - q - 1 + (r : ℤ) = n + (m - q) - 1 := by omega
  have hdq : n + (m - q) - 1 = n + m - 1 - q := by ring
  have hdgys : m - q - 1 = m - 1 - q := by ring
  have hgV : (dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫ (pullback.snd sX (t ≫ sZ) ≫ t) =
      wT ≫ ((Stacks.Divisors.zeroScheme T ((Scheme.Modules.pullback (t ≫ sZ)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (t ≫ sZ) L σ)).subschemeι ≫ t) := by
    rw [← Category.assoc, ← hwT, Category.assoc]
  obtain ⟨ρ, hρiso, hρfst, hρsnd, hρbase, hρtest⟩ :=
    exists_isIso_comp_pullback_fst_eq_mixedPointFibre sX sZ w t x hgV
  have hρV : ρ ≫ bivariantBaseChangeMap w ((Stacks.Divisors.zeroScheme T ((Scheme.Modules.pullback
      (t ≫ sZ)).obj L) (AlgebraicGeometry.pullbackGlobalSections (t ≫ sZ) L σ)).subschemeι ≫ t) wT ≫
      bivariantBaseChangeMap w t (Stacks.Divisors.zeroScheme T ((Scheme.Modules.pullback (t ≫
          sZ)).obj L) (AlgebraicGeometry.pullbackGlobalSections (t ≫ sZ) L σ)).subschemeι = wV ≫
              (Stacks.Divisors.zeroScheme (pullback w t) ((Scheme.Modules.pullback (pullback.snd w
                  t)).obj ((Scheme.Modules.pullback (t ≫ sZ)).obj L))
                      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd w t)
                          ((Scheme.Modules.pullback (t ≫ sZ)).obj L)
                              (AlgebraicGeometry.pullbackGlobalSections (t ≫ sZ) L σ))).subschemeι
                                  := by
    rw [hwV]
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, bivariantBaseChangeMap_fst, bivariantBaseChangeMap_fst,
        hρfst, Category.assoc]
    · simp only [Category.assoc, bivariantBaseChangeMap, pullback.lift_snd,
        pullback.lift_snd_assoc]
      rw [reassoc_of% hρsnd, hwT, mixedPointFibreMap_subschemeι_assoc]
      exact congrArg _ (mixedCommuteSnd_snd sX sZ w t)
  have hwTbase : wT ≫ ((Stacks.Divisors.zeroScheme T ((Scheme.Modules.pullback (t ≫ sZ)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (t ≫ sZ) L σ)).subschemeι ≫ (t ≫ sZ)) =
          ((dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫ (pullback.fst sX (t ≫ sZ) ≫ sX)) := by
    rw [reassoc_of% hwT, ← pullback.condition]
  have hwVbase : wV ≫ ((Stacks.Divisors.zeroScheme (pullback w t) ((Scheme.Modules.pullback
      (pullback.snd w t)).obj ((Scheme.Modules.pullback (t ≫ sZ)).obj L))
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd w t) ((Scheme.Modules.pullback (t
              ≫ sZ)).obj L) (AlgebraicGeometry.pullbackGlobalSections (t ≫ sZ) L σ))).subschemeι ≫
                  (pullback.fst w t ≫ (w ≫ sZ))) = ((dedekindPointFibre sX (pullback.fst w t ≫ (w ≫
                      sZ)) x).subschemeι ≫ (pullback.fst sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ sX)) :=
                          by
    rw [reassoc_of% hwV, ← pullback.condition]
  have hsK : ((dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫ (pullback.fst sX (t ≫ sZ) ≫ sX)) =
      (wT ≫ ((Stacks.Divisors.zeroScheme T ((Scheme.Modules.pullback (t ≫ sZ)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (t ≫ sZ) L σ)).subschemeι ≫ t)) ≫ sZ := by
    rw [← hwTbase]
    rfl
  refine ⟨_, inferInstance, hgV,
    cycleOfDegreeEq _ hdeg (flatPullback C ((dedekindPointFibre sX (t ≫ sZ) x).subschemeι ≫
        (pullback.fst sX (t ≫ sZ) ≫ sX)) ((Stacks.Divisors.zeroScheme T ((Scheme.Modules.pullback
            (t ≫ sZ)).obj L) (AlgebraicGeometry.pullbackGlobalSections (t ≫ sZ) L σ)).subschemeι ≫
                (t ≫ sZ)) wT hwTbase r hrT
      (m - 1) (a₀.1 x • gysinCycleMap C (t ≫ sZ) (m - 1) ((Scheme.Modules.pullback (t ≫ sZ)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (t ≫ sZ) L σ) htrivT
        (cycleOfDegreeEq _ (Int.sub_add_cancel m 1).symm b₀))),
    cycleOfDegreeEq _ hdeg' (flatPullback C ((dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ))
        x).subschemeι ≫ (pullback.fst sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ sX))
            ((Stacks.Divisors.zeroScheme (pullback w t) ((Scheme.Modules.pullback (pullback.snd w
                t)).obj ((Scheme.Modules.pullback (t ≫ sZ)).obj L))
                    (AlgebraicGeometry.pullbackGlobalSections (pullback.snd w t)
                        ((Scheme.Modules.pullback (t ≫ sZ)).obj L)
                            (AlgebraicGeometry.pullbackGlobalSections (t ≫ sZ) L σ))).subschemeι ≫
                                (pullback.fst w t ≫ (w ≫ sZ)))
      wV hwVbase r hrV (m - q - 1) (a₀.1 x • gysinCycleMap C (pullback.fst w t ≫ (w ≫ sZ))
        (m - q - 1) ((Scheme.Modules.pullback (pullback.snd w t)).obj ((Scheme.Modules.pullback (t
            ≫ sZ)).obj L)) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd w t)
                ((Scheme.Modules.pullback (t ≫ sZ)).obj L)
                    (AlgebraicGeometry.pullbackGlobalSections (t ≫ sZ) L σ)) htrivV
                        (cycleOfDegreeEq _ (Int.sub_add_cancel (m - q) 1).symm γ₀))),
    cycleOfDegreeEq _ hdq (properPushforward C ((dedekindPointFibre sX (pullback.fst w t ≫ (w ≫
        sZ)) x).subschemeι ≫ (pullback.fst sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ sX))
      (pullback.fst w (wT ≫ ((Stacks.Divisors.zeroScheme T ((Scheme.Modules.pullback (t ≫ sZ)).obj
          L) (AlgebraicGeometry.pullbackGlobalSections (t ≫ sZ) L σ)).subschemeι ≫ t)) ≫ (w ≫ sZ))
              ρ hρbase (n + (m - q) - 1)
      (cycleOfDegreeEq _ hdeg' (flatPullback C ((dedekindPointFibre sX (pullback.fst w t ≫ (w ≫
          sZ)) x).subschemeι ≫ (pullback.fst sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ sX))
        ((Stacks.Divisors.zeroScheme (pullback w t) ((Scheme.Modules.pullback (pullback.snd w
            t)).obj ((Scheme.Modules.pullback (t ≫ sZ)).obj L))
                (AlgebraicGeometry.pullbackGlobalSections (pullback.snd w t)
                    ((Scheme.Modules.pullback (t ≫ sZ)).obj L)
                        (AlgebraicGeometry.pullbackGlobalSections (t ≫ sZ) L σ))).subschemeι ≫
                            (pullback.fst w t ≫ (w ≫ sZ))) wV hwVbase r hrV (m - q - 1)
        (a₀.1 x • gysinCycleMap C (pullback.fst w t ≫ (w ≫ sZ)) (m - q - 1)
            ((Scheme.Modules.pullback (pullback.snd w t)).obj ((Scheme.Modules.pullback (t ≫
                sZ)).obj L)) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd w t)
                    ((Scheme.Modules.pullback (t ≫ sZ)).obj L)
                        (AlgebraicGeometry.pullbackGlobalSections (t ≫ sZ) L σ)) htrivV
          (cycleOfDegreeEq _ (Int.sub_add_cancel (m - q) 1).symm γ₀))))),
    properPushforward_flatPullback_gysin_of_not_dominates C sX (t ≫ sZ) n m hC x hnd L σ hσ a₀ b₀
      _ _ htrivT hDT wT hwT r hrT hdeg _ rfl _ rfl,
    properPushforward_flatPullback_gysin_of_not_dominates C sX (pullback.fst w t ≫ (w ≫ sZ)) n
      (m - q) hC x hnd L σ hσ a₀ γ₀ _ _ htrivV hDV wV hwV r hrV hdeg' _ rfl _ rfl,
    mk_eq_cap_of_flatPullback_gysinCycleMap sZ w q c' t ((Scheme.Modules.pullback (t ≫ sZ)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (t ≫ sZ) L σ) htrivT htrivV ((dedekindPointFibre
            sX (t ≫ sZ) x).subschemeι ≫ (pullback.fst sX (t ≫ sZ) ≫ sX)) ((dedekindPointFibre sX
                (pullback.fst w t ≫ (w ≫ sZ)) x).subschemeι ≫ (pullback.fst sX (pullback.fst w t ≫
                    (w ≫ sZ)) ≫ sX)) wT
      hwTbase r hrT wV hwVbase hrV ρ hρbase hρV n m (a₀.1 x) b₀ _ rfl γ₀ _ rfl hγ₀ hdeg _ rfl _
      rfl _ rfl hsK, fun z ↦ ?_⟩
  rw [properPushforward_val_cycleOfDegreeEq, properPushforward_properPushforward,
    properPushforward_congr C _ _ _ _ hρtest]


end Summands

/-! ### Stacks 0FC7 -/

section Main

variable {C : ChowSituation.{u}} (hC : IsDedekindChowBase C) {X Y Z : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (w : Y ⟶ Z)
  [LocallyOfFiniteType w] (n m q : ℤ) (c' : CanonicalBivariantClass C (w ≫ sZ) sZ w rfl q)

/-- **The exterior product over a Dedekind base commutes with capping.** Let `(S, δ)` be as in
Stacks section 42.63 — locally the spectrum of a Dedekind domain, with `δ = 0` at the closed points
and `δ = 1` elsewhere — let `X` be locally of finite type over `S`, let `Y ⟶ Z` be a morphism of
schemes locally of finite type over `S` and let `c' ∈ A^q(Y ⟶ Z)`. Then for `α ∈ CH_n(X)` and
`β ∈ CH_m(T)`, `t : T ⟶ Z` a test scheme,

  `α × (c' ∩ β) = c' ∩ (α × β)`,

the left hand side living on `X ×_S (Y ×_Z T)` and the right hand side on `Y ×_Z (X ×_S T)`,
compared through the canonical isomorphism `Stacks.Chow.mixedCommuteHom`, and in the degrees
`n + (m - q) - 1` and `(n + m - 1) - q`. The source's statement is the case `T = Z`. The exterior
product is the map of Stacks 0FC4 and `c'` ranges over the whole group `A^q(Y ⟶ Z)` of
Stacks 0B76. -/
@[stacks 0FC7 "α × (c' ∩ β) = c' ∩ (α × β) for every c' ∈ A^q(Y → Z) and every test scheme \
T → Z (the remark is the case T = Z), over every base as in Section 42.63, with the exterior \
product of Stacks 0FC4 on the tensor product of Chow groups"]
theorem exteriorProductDedekindChowTensor_cap_comm {T : Scheme.{u}} (t : T ⟶ Z)
    [LocallyOfFiniteType t] (α : chowGroup C sX n) (β : chowGroup C (t ≫ sZ) m) :
    chowPushforwardOfIso C (pullback.fst sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ sX)
        (pullback.fst w (pullback.snd sX (t ≫ sZ) ≫ t) ≫ (w ≫ sZ))
        (mixedCommuteHom sX sZ w t) (mixedCommuteHom_comp_structureMorphism sX sZ w t)
        (n + (m - q) - 1)
        (exteriorProductDedekindChowTensor C sX (pullback.fst w t ≫ (w ≫ sZ)) n (m - q) hC
          (α ⊗ₜ[ℤ] c'.cap t m β)) =
      chowGroupDegreeEquiv C (pullback.fst w (pullback.snd sX (t ≫ sZ) ≫ t) ≫ (w ≫ sZ))
        (by ring : (n + m - 1) - q = n + (m - q) - 1)
        (c'.cap (pullback.snd sX (t ≫ sZ) ≫ t) (n + m - 1)
          (chowGroupCongr C
            (by rw [Category.assoc]; exact pullback.condition (f := sX) (g := t ≫ sZ))
            (n + m - 1)
            (exteriorProductDedekindChowTensor C sX (t ≫ sZ) n m hC (α ⊗ₜ[ℤ] β)))) := by
  classical
  obtain ⟨a₀, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C sX n) α
  obtain ⟨b₀, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C (t ≫ sZ) m) β
  obtain ⟨γ₀, hγ₀⟩ := QuotientAddGroup.mk'_surjective
    (rationalEquivalences C (pullback.fst w t ≫ (w ≫ sZ)) (m - q))
    (c'.cap t m (QuotientAddGroup.mk' (rationalEquivalences C (t ≫ sZ) m) b₀))
  rw [← hγ₀, exteriorProductDedekindChowTensor_tmul_mk, exteriorProductDedekindChowTensor_tmul_mk,
    chowPushforwardOfIso_mk]
  have hsum : ∀ x : a₀.1.support, SummandCapData sX sZ w t n m q c' a₀ b₀ γ₀ x := fun x ↦ by
    by_cases hdom : DominatesBaseComponent C sX x.1
    · exact summandCapData_of_dominates hC sX sZ w t n m q c' a₀ b₀ γ₀ hγ₀ x.1 hdom
    · exact summandCapData_of_not_dominates hC sX sZ w t n m q c' a₀ b₀ γ₀ hγ₀ x.1 x.2 hdom
  choose gV hgVlft hgV a a' b hP1 hP4 hP2 hP3 using hsum
  have hfin : LocallyFinite fun x : a₀.1.support ↦
      Set.range (dedekindPointFibre sX (t ≫ sZ) x.1).subschemeι :=
    (locallyFinite_dedekindPointFibre sX (t ≫ sZ) a₀.1).subset fun x ↦ by
      rw [Scheme.IdealSheafData.range_subschemeι]
  have hfin' : LocallyFinite fun x : a₀.1.support ↦
      Set.range (dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x.1).subschemeι :=
    (locallyFinite_dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) a₀.1).subset fun x ↦ by
      rw [Scheme.IdealSheafData.range_subschemeι]
  have hdq : n + (m - q) - 1 = n + m - 1 - q := by ring
  have key := c'.cap_chowGroupCongr_mk_eq_mk_of_locallyFinite (pullback.snd sX (t ≫ sZ) ≫ t)
    (pullback.fst sX (t ≫ sZ) ≫ sX)
    (by rw [Category.assoc]; exact (pullback.condition (f := sX) (g := t ≫ sZ)).symm)
    (n + m - 1) (fun x : a₀.1.support ↦ (dedekindPointFibre sX (t ≫ sZ) x.1).subschemeι) hfin
    gV hgV (fun x ↦ (dedekindPointFibre sX (t ≫ sZ) x.1).subschemeι ≫
      (pullback.fst sX (t ≫ sZ) ≫ sX)) (fun _ ↦ rfl) a
    (exteriorProductDedekindCycles C sX (t ≫ sZ) n m a₀ b₀)
    (exteriorProductDedekindCycles_apply_eq_finsum C sX (t ≫ sZ) n m a₀ b₀ a hP1) b hP2
    (cycleOfDegreeEq _ hdq (properPushforward C
      (pullback.fst sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ sX)
      (pullback.fst w (pullback.snd sX (t ≫ sZ) ≫ t) ≫ (w ≫ sZ)) (mixedCommuteHom sX sZ w t)
      (mixedCommuteHom_comp_structureMorphism sX sZ w t) (n + (m - q) - 1)
      (exteriorProductDedekindCycles C sX (pullback.fst w t ≫ (w ≫ sZ)) n (m - q) a₀ γ₀)))
    (fun z ↦ ?_)
  · refine eq_of_heq (HEq.trans ?_ (HEq.trans (heq_of_eq key.symm)
      (chowGroupDegreeEquiv_heq C _ _ _).symm))
    exact mk_heq_of_val_eq _ hdq _ _ rfl
  · rw [show (cycleOfDegreeEq _ hdq (properPushforward C
        (pullback.fst sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ sX)
        (pullback.fst w (pullback.snd sX (t ≫ sZ) ≫ t) ≫ (w ≫ sZ)) (mixedCommuteHom sX sZ w t)
        (mixedCommuteHom_comp_structureMorphism sX sZ w t) (n + (m - q) - 1)
        (exteriorProductDedekindCycles C sX (pullback.fst w t ≫ (w ≫ sZ)) n (m - q) a₀ γ₀))).1 z =
      AlgebraicCycle.map (mixedCommuteHom sX sZ w t)
        (relativeDimension C.dimensionFunction (pullback.fst sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ sX))
        (relativeDimension C.dimensionFunction
          (pullback.fst w (pullback.snd sX (t ≫ sZ) ≫ t) ≫ (w ≫ sZ)))
        (exteriorProductDedekindCycles C sX (pullback.fst w t ≫ (w ≫ sZ)) n (m - q) a₀ γ₀).1 z
      from rfl]
    rw [algebraicCycle_map_finsum_apply (mixedCommuteHom sX sZ w t) _ _
      (fun x : a₀.1.support ↦
        Set.range (dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x.1).subschemeι) hfin'
      (fun x ↦ (properPushforward C _ _
        (dedekindPointFibre sX (pullback.fst w t ≫ (w ≫ sZ)) x.1).subschemeι rfl
        (n + (m - q) - 1) (a' x)).1)
      (fun x ↦ support_properPushforward_subset C _ _ _ _ _ _) _
      (exteriorProductDedekindCycles_apply_eq_finsum C sX (pullback.fst w t ≫ (w ≫ sZ)) n
        (m - q) a₀ γ₀ a' hP4) z]
    refine finsum_congr fun x ↦ ?_
    rw [hP3 x z]
    exact congrArg (fun c : CycleGroup C _ _ ↦ c.1 z)
      (properPushforward_properPushforward C _ _ _ _ _ rfl
        (mixedCommuteHom_comp_structureMorphism sX sZ w t) _ _)

end Main

end Stacks.Chow

end
