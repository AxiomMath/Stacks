module

public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.QuasiSeparated

/-!
# Quasi-compactness and quasi-separatedness from an ample sheaf on a base change

Let `k` be a field, `K/k` a field extension and `X` a scheme over `k`, with base change
`X_K = pullback (Spec.map (algebraMap k K)) f`. If `X_K` carries an ample invertible sheaf, then
`X` is quasi-compact and quasi-separated: `X_K → X` is surjective and quasi-compact, and `X_K` is
quasi-compact and quasi-separated. This is the first paragraph of the proof of [Stacks, Tag 0BDC].

## Main results

* `AlgebraicGeometry.compactSpace_of_isAmple_baseChange`: `X` is quasi-compact.
* `AlgebraicGeometry.quasiSeparatedSpace_of_isAmple_baseChange`: `X` is quasi-separated.
* `AlgebraicGeometry.compactSpace_and_quasiSeparatedSpace_of_isAmple_baseChange`: the two together.

## References

* [Stacks Project, Tag 0BDC](https://stacks.math.columbia.edu/tag/0BDC)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01PY](https://stacks.math.columbia.edu/tag/01PY)
* [Stacks Project, Tag 01KO](https://stacks.math.columbia.edu/tag/01KO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k))

/-- The projection of the base change of `X` to `K` onto `X` is surjective. -/
public instance surjective_pullback_snd_SpecMap_algebraMap :
    Surjective (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K))) f) :=
  letI : MorphismProperty.IsStableUnderBaseChangeAlong (@Surjective) f :=
    ⟨fun sq H => Surjective.instIsStableUnderBaseChangeScheme.of_isPullback sq H⟩
  MorphismProperty.pullback_snd _ _ inferInstance

/-- The projection of the base change of `X` to `K` onto `X` is quasi-compact. -/
public instance quasiCompact_pullback_snd_SpecMap_algebraMap :
    QuasiCompact (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K))) f) :=
  letI : MorphismProperty.IsStableUnderBaseChangeAlong (@QuasiCompact) f :=
    ⟨fun sq H => quasiCompact_isStableUnderBaseChange.of_isPullback sq H⟩
  MorphismProperty.pullback_snd _ _ inferInstance

variable (L : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible
    (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).toRingedSpace.presheaf
    (structureSheafRing
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).toRingedSpace).property L]

/-- A scheme over a field has quasi-compact underlying space as soon as its base change to an
extension field carries an ample invertible module. -/
public theorem compactSpace_of_isAmple_baseChange
    (hL : Scheme.Modules.IsAmple
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f) L) :
    CompactSpace X :=
  let := hL.compactSpace
  compactSpace_of_surjective (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K))) f)

/-- A scheme over a field has quasi-separated underlying space as soon as its base change to an
extension field carries an ample invertible module. -/
public theorem quasiSeparatedSpace_of_isAmple_baseChange
    (hL : Scheme.Modules.IsAmple
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f) L) :
    QuasiSeparatedSpace X :=
  let := Scheme.Modules.quasiSeparatedSpace_of_isAmple
    (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f) L hL
  quasiSeparatedSpace_of_surjective_of_quasiCompact
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K))) f)

/-- A scheme over a field whose base change to an extension field carries an ample invertible
module is quasi-compact and quasi-separated. -/
public theorem compactSpace_and_quasiSeparatedSpace_of_isAmple_baseChange
    (hL : Scheme.Modules.IsAmple
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f) L) :
    CompactSpace X ∧ QuasiSeparatedSpace X :=
  ⟨compactSpace_of_isAmple_baseChange k K f L hL,
    quasiSeparatedSpace_of_isAmple_baseChange k K f L hL⟩

end AlgebraicGeometry

end
