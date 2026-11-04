module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.RingTheory.Algebraic.Cardinality
public import StacksFrontier.AlgebraicGeometry.Descent.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ArithmeticFrobeniusInverse
public import StacksFrontier.AlgebraicGeometry.Properties.NormalConnectedIntegral
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale

/-!
# The base change of a scheme to an extension field

Let `X` be a scheme over a field `k`, let `K` be an extension field of `k` and let
`X_K = X ×_k K`. This file records the properties of `X_K` used in Section 03VJ of the Trace
Formula chapter, where `K = k^{sep}` or `K = k̄`:

* `X_K` lies in every big étale site containing a nonempty `X`, when `K` is algebraic over `k`;
* `X_K` is connected when `X` is geometrically connected;
* `X_K` is not proper over `K` when `X` is not proper over `k`;
* `X_K` is integral when `X` is smooth and geometrically connected.

## References

* [Stacks Project, Tag 03VJ](https://stacks.math.columbia.edu/tag/03VJ)
* [Stacks Project, Tag 02L1](https://stacks.math.columbia.edu/tag/02L1)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (K : Type u) [Field K]
  [Algebra k K]

include f in
/-- The base field of a nonempty scheme over it is no larger than the size of the scheme: it
embeds in every local ring. -/
theorem mk_le_size_of_nonempty [Nonempty X] : #k ≤ X.size := by
  obtain ⟨x⟩ := ‹Nonempty X›
  let φ : k →+* X.presheaf.stalk x :=
    (X.presheaf.germ ⊤ x trivial).hom.comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
  exact (mk_le_of_injective φ.injective).trans (X.mk_stalk_le_size x)

/-- **The base change of a nonempty scheme of a big étale site to an algebraic extension of the
base field lies in the big étale site.** The extension field is no larger than `max ℵ₀ #k`, which
is at most the size of `X`, so `Spec K` lies in the site by Stacks 000R (9), and then so does the
fibre product by Stacks 000R (1). -/
theorem contains_fieldBaseChange (B : BigEtaleSite.{u}) (hX : B.Contains X) [Nonempty X]
    [Algebra.IsAlgebraic k K] : B.Contains (fieldBaseChange (Over.mk f) K) := by
  have hK : #K ≤ X.size ^ ℵ₀ :=
    (Algebra.IsAlgebraic.cardinalMk_le_max k K).trans
      ((max_le (mk_le_size_of_nonempty f) X.aleph0_le_size).trans
        (self_le_power _ one_le_aleph0))
  have hSpec : (Spec (.of K)).size < B.cutoff :=
    Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit (.of K) hX hK
  exact Scheme.size_pullback_lt _ _ hX hSpec

/-- **The base change to an extension field of a geometrically connected scheme is
connected.** -/
theorem connectedSpace_fieldBaseChange [GeometricallyConnected f] :
    ConnectedSpace (fieldBaseChange (Over.mk f) K) :=
  have : GeometricallyConnected (Over.mk f).hom := ‹GeometricallyConnected f›
  GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)

/-- **Properness descends along a field extension** (Tag 02L1): if `X_K` is proper over `K` then
`X` is proper over `k`, `Spec K ⟶ Spec k` being surjective, flat and quasi-compact. -/
theorem isProper_of_isProper_fieldBaseChange
    (h : IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k K))) : IsProper f := by
  have := isProper_descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := @IsProper)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (IsPullback.of_hasPullback (Over.mk f).hom (specAlgebraMap k K)).flip ?_ h
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> infer_instance

/-- **The base change to an extension field of a smooth geometrically connected scheme is
integral.** It is smooth over `K`, hence normal, and connected. -/
theorem isIntegral_fieldBaseChange [Smooth f] [GeometricallyConnected f] :
    IsIntegral (fieldBaseChange (Over.mk f) K) :=
  have := connectedSpace_fieldBaseChange f K
  have : Smooth (Over.mk f).hom := ‹Smooth f›
  isIntegral_of_smooth_of_connectedSpace (pullback.snd (Over.mk f).hom (specAlgebraMap k K))

end AlgebraicGeometry
