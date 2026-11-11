module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Nagata
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizedBlowupAtClosedPoint

/-!
# The normalized blowing up of a Nagata algebraic space is proper

Let `S` be a scheme, let `X` be a Nagata algebraic space over `S` and let `z ∈ |X|` be a closed
point.  **Stacks 0BHK** says that the normalized blowing up `X'' ⟶ X' ⟶ X` of `X` at `z`
(Stacks 0BHJ) is a normal Nagata algebraic space proper over `X`.

The source's proof begins by observing that the blowing up `X' ⟶ X` is proper: `X` is locally
Noetherian, so the centre is cut out by an ideal of finite type, and Stacks 085Z applies.  This
file supplies that step, and with it the tag at exactly the source's hypotheses.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentation_ι_of_hasEtaleLocalProperty_isLocallyNoetherian`:
  every closed subspace of a locally Noetherian algebraic space has an inclusion of finite
  presentation.  On a locally Noetherian surjective étale chart every ideal of the ring of
  sections over an affine open is finitely generated, and Stacks 084Q, read on that chart, is
  finite presentation.
* `AlgebraicGeometry.Space.NormalizedBlowupAtClosedPoint.isProper_proj`: the blowing up of a
  Nagata algebraic space at a closed point is proper.  A Nagata scheme is locally Noetherian,
  so the centre is of finite presentation, and Stacks 085Z
  (`AlgebraicGeometry.Space.isProper_of_isBlowupAlong_of_isFinitePresentation`) applies.
* `NormalizedBlowupAtClosedPoint.isNormal_and_isNagata_and_isProper_of_isNagata` (in the
  namespace `AlgebraicGeometry.Space`) is **Stacks 0BHK**: if `X` is Nagata, the normalized
  blowing up of `X` at a closed point is an algebraic space which is normal and Nagata, and it
  is proper over `X`.

## Implementation notes

The normalized blowing up is `AlgebraicGeometry.Space.NormalizedBlowupAtClosedPoint` of
Stacks 0BHJ: a blowing up of `X` at `z` together with normalization data for it.  The statement
quantifies over that datum, so it applies to every normalized blowing up of `X` at `z`.  Being
normal and being Nagata are the étale-local scheme properties of Stacks 03E6.

The construction of blowups of algebraic spaces through which Stacks 085Z is proved uses
sheafification of `Type u`-valued presheaves on the big fppf site; that site is essentially
small, so sheafification exists (`AlgebraicGeometry.hasSheafify_bigFppfOver`) and is supplied
inside the proof rather than assumed.

## References

* [Stacks Project, Tag 0BHK](https://stacks.math.columbia.edu/tag/0BHK)
* [Stacks Project, Tag 0BHJ](https://stacks.math.columbia.edu/tag/0BHJ)
* [Stacks Project, Tag 085Z](https://stacks.math.columbia.edu/tag/085Z)
* [Stacks Project, Tag 084Q](https://stacks.math.columbia.edu/tag/084Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A closed subspace of a locally Noetherian algebraic space is of finite presentation.**  If
`X` has a surjective étale chart by a locally Noetherian scheme, the inclusion of every closed
subspace of `X` is of finite presentation.

On that chart the ring of sections over an affine open is Noetherian, so the ideal cut out by
the base-changed closed immersion is finitely generated there; this is finite presentation of
the inclusion by Stacks 084Q read on a surjective étale chart,
`AlgebraicGeometry.Space.isFinitePresentation_iff_fg_ker_of_surjectiveEtaleChart`. -/
theorem isFinitePresentation_ι_of_hasEtaleLocalProperty_isLocallyNoetherian
    (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)
    (hLN : HasEtaleLocalProperty B S hS X.obj (fun T : Scheme.{u} => IsLocallyNoetherian T)) :
    IsFinitePresentation B S hS Z.1.ι := by
  obtain ⟨V, b, hbSurj, hbEtale, hV⟩ := hLN
  refine (isFinitePresentation_iff_fg_ker_of_surjectiveEtaleChart B S hS
    (Z := ⟨Z.1.toFunctor, Z.2.1⟩) (X := X) (ObjectProperty.homMk Z.1.ι) Z.2.2
    hbEtale hbSurj).2 fun A => ?_
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) := hV
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, A.1) :=
    IsLocallyNoetherian.component_noetherian A
  exact IsNoetherian.noetherian _

namespace NormalizedBlowupAtClosedPoint

variable {X : AlgebraicSpaces B S hS} {z : points B S hS X.obj}
    {hz : IsClosed ({z} : Set (points B S hS X.obj))}
    (N : NormalizedBlowupAtClosedPoint B S hS X z hz)

/-- **The blowing up of a Nagata algebraic space at a closed point is proper.**  A Nagata
scheme is locally Noetherian, so `X` is locally Noetherian and the reduced closed subspace
supported on `z` has an inclusion of finite presentation; a blowing up in a closed subspace of
finite presentation is proper by Stacks 085Z,
`AlgebraicGeometry.Space.isProper_of_isBlowupAlong_of_isFinitePresentation`.  The blowing up
`X' ⟶ X` of the datum is isomorphic over `X` to such a blowing up, and properness respects
isomorphisms. -/
theorem isProper_proj
    (hNagata : HasEtaleLocalProperty B S hS X.obj (fun T : Scheme.{u} => IsNagataScheme T)) :
    IsProper B S hS N.proj.hom := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) := hasSheafify_bigFppfOver B S hS
  obtain ⟨V, a, haSurj, haEtale, hV⟩ := hNagata
  have hLN : HasEtaleLocalProperty B S hS X.obj (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    ⟨V, a, haSurj, haEtale,
      ((isNagataScheme_iff_isLocallyNoetherian_and_isUniversallyJapaneseScheme _).mp hV).1⟩
  obtain ⟨W, b, hb, e, he⟩ := N.isBlowup
  have hbp : IsProper B S hS b.hom :=
    isProper_of_isBlowupAlong_of_isFinitePresentation B S hS _ b
      (isFinitePresentation_ι_of_hasEtaleLocalProperty_isLocallyNoetherian X _ hLN) hb
  have h : properProperty B S hS (e.hom ≫ b) :=
    MorphismProperty.RespectsIso.precomp (properProperty B S hS) e.hom b hbp
  rw [he] at h
  exact h

/-- **Stacks 0BHK.**  If `X` is Nagata, then the normalized blowing up of `X` at a closed point
`z` is a normal Nagata algebraic space proper over `X`.

Spelled out: for every normalized blowing up `X'' ⟶ X' ⟶ X` of `X` at `z` (Stacks 0BHJ), `X''`
is an algebraic space over `S`, it is normal, it is Nagata, and the composite `X'' ⟶ X` is
proper.  The only hypothesis is that `X` is Nagata.

The proof is the source's.  The blowing up `X' ⟶ X` is proper,
`AlgebraicGeometry.Space.NormalizedBlowupAtClosedPoint.isProper_proj` (Stacks 085Z, `X` being
locally Noetherian); hence `X'` is Nagata (Stacks 0BAU), the normalization `X'' ⟶ X'` is finite
(Stacks 0BB5), hence proper (Stacks 04NZ), and the composite is proper (Stacks 04XY); `X''` is
normal by Stacks 0BB4 and Nagata by Stacks 0BAU again. -/
@[stacks 0BHK "the lemma in full, with NOTHING carried: for a Nagata X, every normalized \
blowing up of X at a closed point is an algebraic space, normal, Nagata, and proper over X"]
theorem isNormal_and_isNagata_and_isProper_of_isNagata
    (hNagata : HasEtaleLocalProperty B S hS X.obj (fun T : Scheme.{u} => IsNagataScheme T)) :
    IsAlgebraicSpace B S hS N.space.obj ∧
      HasEtaleLocalProperty B S hS N.space.obj
        (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsNormal T) ∧
      HasEtaleLocalProperty B S hS N.space.obj (fun T : Scheme.{u} => IsNagataScheme T) ∧
      IsProper B S hS N.hom.hom :=
  N.isNormal_and_isNagata_and_isProper hNagata (N.isProper_proj hNagata)

end NormalizedBlowupAtClosedPoint

end AlgebraicGeometry.Space

end
