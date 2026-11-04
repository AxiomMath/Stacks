module

public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.Basic
public import StacksFrontier.AlgebraicGeometry.RelativelyAmple.AffineBase

/-!
# Quasi-projectivity after a change of base field

Let `k` be a field, `X` a scheme over `k` and `K/k` a field extension. [Stacks, Tag 0BDE] asserts
that `X` is quasi-projective over `k` as soon as `X_K` is quasi-projective over `K`, and its proof
in the source is three steps: finite type descends ([Stacks, Tag 00QP]), relative ampleness over
an affine base is ampleness ([Stacks, Tag 01VT]), and ampleness itself descends from a field
extension ([Stacks, Tag 0BDC]).

This file assembles the first two, with the descent of ampleness as an explicit hypothesis.

## Main results

* `AlgebraicGeometry.isQuasiProjective_of_fieldExtension_of_exists_isAmple`: quasi-projectivity
  descends from a field extension, given the descent of the existence of an ample invertible
  sheaf.
* `AlgebraicGeometry.isQuasiProjective_of_fieldExtension_of_exists_isAmple_comm`: the same, with
  the hypothesis taken at the other order of the two factors of the fibre product — the order
  [Stacks, Tag 0BDC] itself is stated at.

## Implementation notes

The finite-type half is
`AlgebraicGeometry.locallyOfFiniteType_and_quasiCompact_of_fieldExtension`, which descends along
any faithfully flat base change and needs no sheaf. The comparison of relative ampleness with
ampleness is `AlgebraicGeometry.Scheme.Modules.isRelativelyAmple_iff_isAmple`, used in both
directions: forgetfully over `Spec K`, where only `(2) ⇒ (1)` is needed and the base is merely
affine, and back over `Spec k`, where `(1) ⇒ (2)` is needed and uses that the spectrum of a field
is a single point.

The hypothesis is [Stacks, Tag 0BDC], at both orientations of the fibre product. The base change
of `X` is `CategoryTheory.Limits.pullback f (Spec.map (algebraMap k K))`, whose second projection
is the structure morphism over `K`, and that is the order Tag 0BDE is stated at; Tag 0BDC is
stated with the two factors in the other order. The two orders are reconciled by
`AlgebraicGeometry.Scheme.Modules.exists_isAmple_pullback_comm`, which transports the existence
of an ample invertible sheaf across `CategoryTheory.Limits.pullbackSymmetry`.

The hypothesis is discharged, and Tag 0BDE registered, in
`StacksFrontier/AlgebraicGeometry/FieldExtensionDescent/Unconditional.lean`.

## References

* [Stacks Project, Tag 0BDE](https://stacks.math.columbia.edu/tag/0BDE)
* [Stacks Project, Tag 0BDC](https://stacks.math.columbia.edu/tag/0BDC)
* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **[Stacks, Tag 0BDE] given [Stacks, Tag 0BDC].** If the base change of a scheme over a field
`k` to an extension field `K` is quasi-projective over `K`, and the existence of an ample
invertible sheaf descends from that base change to the scheme, then the scheme is quasi-projective
over `k`. The hypothesis `hample` is the content of [Stacks, Tag 0BDC]. -/
public theorem isQuasiProjective_of_fieldExtension_of_exists_isAmple
    (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (hample : (∃ L : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules,
        ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible
          (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).toRingedSpace.presheaf
          (structureSheafRing
            (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).toRingedSpace).property L,
          Scheme.Modules.IsAmple
            (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) L) →
      ∃ M : X.Modules, ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible
        X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property M,
        Scheme.Modules.IsAmple X M)
    (h : IsQuasiProjective (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    IsQuasiProjective f := by
  refine ⟨locallyOfFiniteType_and_quasiCompact_of_fieldExtension k K f h.1, ?_⟩
  obtain ⟨L, hL, hrel⟩ := h.2
  obtain ⟨M, hM, hamp⟩ := hample ⟨L, hL,
    Scheme.Modules.isAmple_of_isRelativelyAmple
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) L hrel⟩
  exact ⟨M, hM, Scheme.Modules.isRelativelyAmple_of_isAmple f M hamp⟩

/-- **[Stacks, Tag 0BDE] given [Stacks, Tag 0BDC] at Tag 0BDC's own order of the two factors.**
Identical to `AlgebraicGeometry.isQuasiProjective_of_fieldExtension_of_exists_isAmple` except
that the base change is written `Spec K ×_{Spec k} X` rather than `X ×_{Spec k} Spec K`, which is
the order [Stacks, Tag 0BDC] is stated at. The two are reconciled by
`AlgebraicGeometry.Scheme.Modules.exists_isAmple_pullback_comm`. -/
public theorem isQuasiProjective_of_fieldExtension_of_exists_isAmple_comm
    (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (hample : (∃ L : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).Modules,
        ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible
          (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).toRingedSpace.presheaf
          (structureSheafRing
            (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).toRingedSpace).property L,
          Scheme.Modules.IsAmple
            (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f) L) →
      ∃ M : X.Modules, ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible
        X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property M,
        Scheme.Modules.IsAmple X M)
    (h : IsQuasiProjective (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    IsQuasiProjective f :=
  isQuasiProjective_of_fieldExtension_of_exists_isAmple k K f
    (fun hK => hample ((Scheme.Modules.exists_isAmple_pullback_comm f
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mp hK)) h

end AlgebraicGeometry

end
