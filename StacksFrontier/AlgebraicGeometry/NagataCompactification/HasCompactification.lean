module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.QuasiAffineSource
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Having a compactification over a base

A scheme `X` over a scheme `S` *has a compactification over `S`* when the structure morphism
`f : X ⟶ S` factors as a quasi-compact open immersion into a scheme proper over `S`. This file
introduces the predicate `AlgebraicGeometry.HasCompactification` recording that, and its closure
properties: restriction to a quasi-compact open, composition with a closed immersion, base change,
and the case of a quasi-affine source.

## Main definitions

* `AlgebraicGeometry.HasCompactification`: the morphism factors as a quasi-compact open immersion
  followed by a proper morphism.

## Main results

* `AlgebraicGeometry.HasCompactification.of_isOpenImmersion`: a quasi-compact open subscheme of a
  compactifiable scheme is compactifiable.
* `AlgebraicGeometry.HasCompactification.of_isClosedImmersion`: a closed subscheme of a
  compactifiable scheme is compactifiable.
* `AlgebraicGeometry.HasCompactification.of_isPullback`: compactifiability is stable under base
  change.
* `AlgebraicGeometry.HasCompactification.of_isQuasiAffine`: a quasi-affine source, separated and of
  finite type over a quasi-compact quasi-separated base, is compactifiable.

## Implementation notes

The predicate is
`∃ j : AlgebraicGeometry.CompactificationOf (Over.mk f), QuasiCompact j.immersion`:
quasi-compactness of the open immersion is recorded separately from
`AlgebraicGeometry.IsCompactificationOf`, which does not ask for it.

## References

* [Stacks Project, Tag 0F41](https://stacks.math.columbia.edu/tag/0F41)
* [Stacks Project, Tag 0ATU](https://stacks.math.columbia.edu/tag/0ATU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The morphism `f : X ⟶ S` factors as a quasi-compact open immersion of `X` into a scheme proper
over `S`. -/
@[sga "4 XVII 3.2.7" "special case"]
def HasCompactification {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ j : CompactificationOf (Over.mk f), QuasiCompact j.immersion

namespace HasCompactification

variable {X Y S S' : Scheme.{u}}

/-- Compactifiability transports along an equality of morphisms. -/
theorem of_eq {f f' : X ⟶ S} (h : f = f') (hf : HasCompactification f) :
    HasCompactification f' := h ▸ hf

/-- The composite of a quasi-compact open immersion `i : X ⟶ P` and a proper morphism `p : P ⟶ S`
has a compactification. -/
theorem of_isOpenImmersion_isProper {P : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S) [IsOpenImmersion i]
    [QuasiCompact i] [IsProper p] : HasCompactification (i ≫ p) :=
  ⟨⟨StructuredArrow.mk (Y := Over.mk p)
      (Over.homMk (U := Over.mk (i ≫ p)) (V := Over.mk p) i rfl),
    inferInstanceAs (IsOpenImmersion i), inferInstanceAs (IsProper p)⟩,
    inferInstanceAs (QuasiCompact i)⟩

/-- A quasi-compact open subscheme of a compactifiable scheme is compactifiable: if `f` has a
compactification and `jU` is a quasi-compact open immersion, then `jU ≫ f` has one. -/
@[sga "4 XVII 3.2.2" "(iii), special case"]
theorem of_isOpenImmersion {f : X ⟶ S} {U : Scheme.{u}} (jU : U ⟶ X) [IsOpenImmersion jU]
    [QuasiCompact jU] (hf : HasCompactification f) : HasCompactification (jU ≫ f) := by
  obtain ⟨j, hj⟩ := hf
  refine ⟨j.restrictOpen jU, ?_⟩
  rw [CompactificationOf.restrictOpen_immersion]
  exact @quasiCompact_comp _ _ _ jU j.immersion inferInstance hj

/-- A closed subscheme of a compactifiable scheme is compactifiable: if `g` is quasi-compact and
has a compactification and `i` is a closed immersion, then `i ≫ g` has one. -/
@[sga "4 XVII 3.2.2" "(iii), special case"]
theorem of_isClosedImmersion {g : Y ⟶ S} (i : X ⟶ Y) [IsClosedImmersion i] [QuasiCompact g]
    (hg : HasCompactification g) : HasCompactification (i ≫ g) := by
  obtain ⟨j, -⟩ := hg
  have : QuasiCompact (i ≫ j.immersion) :=
    @quasiCompact_comp _ _ _ i j.immersion inferInstance
      (CompactificationOf.quasiCompact_immersion j)
  refine ⟨j.restrictClosed i, ?_⟩
  rw [CompactificationOf.restrictClosed_immersion]
  exact (inferInstance : QuasiCompact (Scheme.Hom.toImage (i ≫ j.immersion)))

/-- If `g` is quasi-compact and has a compactification, `i` is a closed immersion and `i ≫ g = f`,
then `f` has a compactification. -/
@[sga "4 XVII 3.2.2" "(iii), special case"]
theorem of_isClosedImmersion' {i : X ⟶ Y} {g : Y ⟶ S} {f : X ⟶ S} [IsClosedImmersion i]
    [QuasiCompact g] (hf : i ≫ g = f) (hg : HasCompactification g) : HasCompactification f :=
  of_eq hf (of_isClosedImmersion i hg)

/-- Compactifiability is stable under base change: if `f' : X' ⟶ S'` is the base change of
`f : X ⟶ S` along `g : S' ⟶ S`, exhibited by a cartesian square, and `f` is compactifiable, then so
is `f'`. -/
theorem of_isPullback {X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {p : X' ⟶ X}
    (hsq : IsPullback p f' f g) (hf : HasCompactification f) : HasCompactification f' := by
  obtain ⟨j, hj⟩ := hf
  have hbot : IsPullback (pullback.fst j.toBase g) (pullback.snd j.toBase g) j.toBase g :=
    IsPullback.of_hasPullback j.toBase g
  have hw : (p ≫ j.immersion) ≫ j.toBase = f' ≫ g := by
    rw [Category.assoc, CompactificationOf.immersion_toBase]; exact hsq.w
  set ℓ : X' ⟶ pullback j.toBase g := hbot.lift (p ≫ j.immersion) f' hw with hℓ
  have hsnd : ℓ ≫ pullback.snd j.toBase g = f' := hbot.lift_snd (p ≫ j.immersion) f' hw
  have htop : IsPullback p ℓ j.immersion (pullback.fst j.toBase g) := by
    refine IsPullback.of_bot ?_ (hbot.lift_fst (p ≫ j.immersion) f' hw).symm hbot
    rw [hsnd, CompactificationOf.immersion_toBase]
    exact hsq
  have : QuasiCompact j.immersion := hj
  have hopen : IsOpenImmersion ℓ :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) htop inferInstance
  have hqc : QuasiCompact ℓ :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) htop inferInstance
  exact of_eq hsnd (of_isOpenImmersion_isProper ℓ (pullback.snd j.toBase g))

/-- A separated morphism of finite type from a quasi-affine scheme to a quasi-compact
quasi-separated scheme is compactifiable. -/
@[sga "4 XVII 3.2.2" "(ii)", sga "7 XIII 2.1.6" "Clause c), special case"]
theorem of_isQuasiAffine (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] [X.IsQuasiAffine] : HasCompactification f :=
  exists_quasiCompact_compactificationOf_of_isQuasiAffine f

end HasCompactification

end AlgebraicGeometry
