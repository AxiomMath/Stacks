module

public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Artinian

/-!
# Reduced schemes with finitely many rational points over an algebraically closed field

Let `k` be an algebraically closed field and `G` a reduced scheme locally of finite type over
`k` with only finitely many `k`-points. Then `G` is a finite disjoint union of copies of
`Spec k`: its closed points are its `k`-points, so there are finitely many of them, and since
`G` is a Jacobson space every point is closed (the closure of a point is the closure of the
finitely many closed points it contains). Each point is then an open subscheme, reduced with one
point and with a `k`-point, hence isomorphic to `Spec k` over `k`.

Consequently a `k[ε]`-point of `G` over `k` is determined by its image point: **`G` has no
nonzero tangent vectors**, and the map `G(k[ε]) ⟶ G(k)` is injective. This is the step turning
"finitely many `k`-points" and "a nontrivial `k[ε]`-point over the identity" into
non-reducedness.

## Main results

* `AlgebraicGeometry.isClosed_singleton_of_finite_points`: every point of `G` is closed.
* `AlgebraicGeometry.isIso_opensι_comp_of_isOpen_singleton`: the open subscheme at a point is
  `Spec k`.
* `AlgebraicGeometry.eq_of_dualNumber_points`: **two `k[ε]`-points of `G` over `k` agreeing on
  the closed point are equal.**

## References

* [Stacks Project, Tag 01TB](https://stacks.math.columbia.edu/tag/01TB)
* [Stacks Project, Tag 0DSU](https://stacks.math.columbia.edu/tag/0DSU)
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {k : Type u} [Field k]

/-- The spectrum of the dual numbers over a field has a single point, as an instance (the base
states the same fact as the theorem `AlgebraicGeometry.subsingleton_spec_dualNumber`). -/
instance instSubsingletonSpecDualNumber : Subsingleton (Spec (.of (DualNumber k))) := by
  have key : ∀ P : Spec (.of (DualNumber k)),
      P.asIdeal = RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom := by
    intro P
    have hmax : (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩
    refine (hmax.eq_of_le P.isPrime.ne_top fun x hx ↦ ?_).symm
    have hx0 : x.fst = 0 := hx
    have hsq : x * x = 0 := by
      ext <;> simp [hx0]
    exact P.isPrime.mem_of_pow_mem 2 (by rw [sq, hsq]; exact zero_mem _)
  exact ⟨fun P Q ↦ PrimeSpectrum.ext ((key P).trans (key Q).symm)⟩

variable [IsAlgClosed k] {G : Scheme.{u}} (π : G ⟶ Spec (.of k)) [LocallyOfFiniteType π]

include π in
/-- A scheme locally of finite type over `k` with finitely many `k`-points is discrete: it is
Jacobson with finitely many closed points. -/
private theorem discreteTopology_of_finite_points
    (hfin : Finite {p : Spec (.of k) ⟶ G // p ≫ π = 𝟙 _}) : DiscreteTopology G := by
  have : JacobsonSpace G := LocallyOfFiniteType.jacobsonSpace π
  have := Finite.of_equiv _ (pointEquivClosedPoint π)
  exact JacobsonSpace.discreteTopology (Set.toFinite _)

include π in
/-- **Every point is closed** when there are finitely many `k`-points: in a Jacobson space the
closure of a point is the closure of the closed points it contains, and finitely many closed
points form a closed set. -/
theorem isClosed_singleton_of_finite_points
    (hfin : Finite {p : Spec (.of k) ⟶ G // p ≫ π = 𝟙 _}) (y : G) : IsClosed {y} :=
  have := discreteTopology_of_finite_points π hfin
  isClosed_discrete _

include π in
/-- Every point is open when there are finitely many `k`-points. -/
theorem isOpen_singleton_of_finite_points
    (hfin : Finite {p : Spec (.of k) ⟶ G // p ≫ π = 𝟙 _}) (x : G) : IsOpen {x} :=
  have := discreteTopology_of_finite_points π hfin
  isOpen_discrete _

/-- **The open subscheme at an isolated closed point of a reduced scheme over `k` is `Spec k`**:
its structure morphism is an isomorphism, the `k`-point at the point being an inverse. -/
theorem isIso_opensι_comp_of_isOpen_singleton [IsReduced G] {x : G} (hx : IsClosed {x})
    (hx' : IsOpen {x}) : IsIso (Scheme.Opens.ι (X := G) ⟨{x}, hx'⟩ ≫ π) := by
  set U : G.Opens := ⟨{x}, hx'⟩
  have hrange : Set.range (pointOfClosedPoint π x hx).base ⊆ Set.range U.ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact pointOfClosedPoint_apply π x hx z
  let p := IsOpenImmersion.lift U.ι (pointOfClosedPoint π x hx) hrange
  have hp : p ≫ U.ι ≫ π = 𝟙 _ := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, pointOfClosedPoint_comp]
  have : Subsingleton U := by
    refine ⟨fun a b ↦ Subtype.ext ?_⟩
    rw [a.2, b.2]
  have : IsReduced U := isReduced_of_isOpenImmersion U.ι
  have : IsClosedImmersion p := isClosedImmersion_of_comp_eq_id _ p hp
  have : Surjective p := ⟨fun a ↦ ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩⟩
  have : IsIso p := isIso_of_isClosedImmersion_of_surjective p
  have e : U.ι ≫ π = inv p := by
    rw [← cancel_epi p, hp, IsIso.hom_inv_id]
  rw [e]
  infer_instance

/-- **A reduced scheme locally of finite type over an algebraically closed field `k` with
finitely many `k`-points has no nonzero tangent vectors**: two `k[ε]`-points over `k` which agree
on the closed point of `Spec k[ε]` are equal. -/
theorem eq_of_dualNumber_points [IsReduced G]
    (hfin : Finite {p : Spec (.of k) ⟶ G // p ≫ π = 𝟙 _})
    {φ₁ φ₂ : Spec (.of (DualNumber k)) ⟶ G}
    (h₁ : φ₁ ≫ π = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
    (h₂ : φ₂ ≫ π = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
    (h : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ φ₁ =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ φ₂) :
    φ₁ = φ₂ := by
  let z : Spec (.of (DualNumber k)) :=
    (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)).base
      (IsLocalRing.closedPoint k)
  set x := φ₁.base z
  have hx2 : φ₂.base z = x :=
    (congrArg (fun f : Spec (.of k) ⟶ G ↦ f.base (IsLocalRing.closedPoint k)) h).symm
  have hxo := isOpen_singleton_of_finite_points π hfin x
  set U : G.Opens := ⟨{x}, hxo⟩
  have hr : ∀ φ : Spec (.of (DualNumber k)) ⟶ G, φ.base z = x →
      Set.range φ.base ⊆ Set.range U.ι.base := by
    rintro φ hφ _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim w z, hφ]
    rfl
  have := isIso_opensι_comp_of_isOpen_singleton π
    (isClosed_singleton_of_finite_points π hfin x) hxo
  have h1 := IsOpenImmersion.lift_fac U.ι φ₁ (hr φ₁ rfl)
  have h2 := IsOpenImmersion.lift_fac U.ι φ₂ (hr φ₂ hx2)
  have e : IsOpenImmersion.lift U.ι φ₁ (hr φ₁ rfl) = IsOpenImmersion.lift U.ι φ₂ (hr φ₂ hx2) := by
    rw [← cancel_mono (U.ι ≫ π), ← Category.assoc, h1, ← Category.assoc, h2, h₁, h₂]
  rw [← h1, ← h2, e]

end AlgebraicGeometry
