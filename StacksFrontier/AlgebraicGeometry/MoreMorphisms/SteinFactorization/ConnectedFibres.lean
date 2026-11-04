module

public import StacksFrontier.AlgebraicGeometry.Fibres.IdempotentExtensionApproximation
public import StacksFrontier.AlgebraicGeometry.Fibres.SectionsFromFibre
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.ConnectedFibresOverField
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.GeometricallyConnectedFibre
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Fibres of a morphism whose pushforward of the structure sheaf is the structure sheaf

Let `f : X ⟶ S` be a proper morphism with `f_*𝒪_X = 𝒪_S`, as the first factor
`f' : X ⟶ f.normalization` of a Stein factorization is.  This file studies the fibres of such an
`f`, the question being whether they are geometrically connected:  that is the connectedness
conjunct of clause (1) of [Stacks, Tag 03H2], whose essential input is [Stacks, Tag 0G7X].

Everything here turns on one observation.  The fibre `X_s` sits in the cartesian square
```
X_s  ⟶  X
 |       |
 v       v
Spec κ(s) ⟶ S
```
so a section of `𝒪_X` over `f ⁻¹ᵁ U`, `U` an open neighbourhood of `s`, restricts to the fibre
through `Γ(Spec κ(s), ⊤)` (`Stacks.AlgebraicGeometry.app_comp_fiberι_appLE`).  Since
`f_*𝒪_X = 𝒪_S` makes `Γ(S, U) ⟶ Γ(X, f ⁻¹ᵁ U)` an isomorphism, *every* function on `X_s` that
extends over a neighbourhood of `s` in the sense of
`Stacks.AlgebraicGeometry.Fibres.ExtendsOverNeighbourhood` already comes from the residue field
`κ(s)`.  Two consequences:

* for an idempotent this forces the idempotent to be `0` or `1`, because `κ(s)` is a field, so
  `X_s` is connected;
* if *all* functions on `X_s` extend, then `κ(s) ⟶ Γ(X_s, 𝒪_{X_s})` is an isomorphism, and
  [Stacks, Tag 0FD1] (`geometricallyConnected_toSpecΓ_of_isProper_over_field`) upgrades this to
  geometric connectedness of `X_s`.

Extending a function on the fibre is [Stacks, Tag 0G7X],
`Stacks.AlgebraicGeometry.Fibres.extendsOverNeighbourhood_of_isProper`.  The intermediate results
below are stated with the extension property as a hypothesis, because that is the shape in which
the reduction is cleanest and because one case bypasses it entirely:  when `Spec κ(s) ⟶ S` is flat,
as it is whenever the local ring `𝒪_{S,s}` is its own residue field, flat base change carries
`f_*𝒪_X = 𝒪_S` to `Γ(X_s, 𝒪_{X_s}) = κ(s)` and the fibre at `s` is unconditionally geometrically
connected.  This covers, for instance, every point of a reduced zero-dimensional base and every
generic point of a reduced base.  The other unconditional case is the base being the spectrum of a
field, where Tag 0FD1 applies to `f` itself rather than to a fibre;  that is
`Stacks.SteinFactorization.geometricallyConnected_toNormalization_over_field` in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.ConnectedFibresOverField`, which
this file imports.

## Main results

* `Stacks.AlgebraicGeometry.app_comp_fiberι_appLE`: restriction to the fibre at `s` of a section
  pulled back from a neighbourhood of `s` factors through the residue field at `s`.
* `Stacks.AlgebraicGeometry.exists_appTop_eq_of_extendsOverNeighbourhood`: for `f_*𝒪_X = 𝒪_S`, a
  function on the fibre that extends over a neighbourhood comes from `Γ(Spec κ(s), ⊤)`.
* `Stacks.AlgebraicGeometry.eq_zero_or_one_of_isIdempotentElem_of_extendsOverNeighbourhood` and
  `Stacks.AlgebraicGeometry.connectedSpace_fiber_of_extendsOverNeighbourhood`: an idempotent that
  extends is trivial, hence the fibre is connected.
* `Stacks.AlgebraicGeometry.isIso_appTop_fiberToSpecResidueField_of_extendsOverNeighbourhood`: if
  every function on the fibre extends then `κ(s) ⟶ Γ(X_s, 𝒪_{X_s})` is an isomorphism.
* `Stacks.AlgebraicGeometry.geometricallyConnected_fiberToSpecResidueField_of_isIso_appTop`: a
  proper morphism whose fibre at `s` has `Γ(X_s, 𝒪_{X_s}) = κ(s)` has geometrically connected
  fibre at `s`.
* `Stacks.AlgebraicGeometry.geometricallyConnected_fiberToSpecResidueField_of_flat` and
  `Stacks.AlgebraicGeometry.geometricallyConnected_fiberToSpecResidueField_of_isIso_residue`: the
  unconditional case, for a point whose residue field is flat over the base, respectively a point
  at which the local ring of the base is its own residue field.
* `Stacks.AlgebraicGeometry.flat_fromSpecResidueField_of_isIso_residue`: `Spec κ(s) ⟶ S` is flat
  when `𝒪_{S,s} = κ(s)`.
* `Stacks.SteinFactorization`
  `.geometricallyConnected_fiberToSpecResidueField_toNormalization_of_flat`: the same for the
  first factor of the Stein factorization of a proper morphism.  This is the special case of the
  connectedness assertion in clause (1) of [Stacks, Tag 03H2] proved here.
* `Stacks.SteinFactorization.geometricallyConnected_toNormalization_of_extendsOverNeighbourhood`:
  clause (1) of [Stacks, Tag 03H2] in full, conditional on the extension property.
* `Stacks.SteinFactorization.geometricallyConnected_toNormalization_of_etaleNeighborhood`: the
  connectedness conjunct of clause (1) of [Stacks, Tag 03H2], with [Stacks, Tag 0G7X] carried as
  a named hypothesis in exactly the form in which that tag applies, and
  `Stacks.SteinFactorization.geometricallyConnected_toNormalization_of_isProper`: the same
  **unconditionally**, which is the registered clause.  This completes the covering set of
  Tag 03H2, whose other clauses are in
  `StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Proper`,
  `...StructureSheaf` and `...RelativeSpectrum`.

## Implementation notes

**How clause (1) is reached.**  The statement `GeometricallyConnected f.toNormalization` for an
arbitrary proper `f` is proved by the source's route:  [Stacks, Tag 03GZ] and degree-zero flat base
change along an étale neighbourhood (`...geometricallyConnected_fiber_iff_forall_etaleNeighborhood`
and `Stacks.AlgebraicGeometry.isIso_c_of_isPullback_of_flat`) reduce it to the connectedness of a
single fibre, and that to [Stacks, Tag 0G7X] — an idempotent of `Γ(X_s, 𝒪_{X_s})` lifts to a
neighbourhood of `s`.  The reduction is
`Stacks.AlgebraicGeometry.geometricallyConnected_fiberToSpecResidueField_of_etaleNeighborhood`, so
the whole of clause (1) rests on Tag 0G7X, which is
`Stacks.AlgebraicGeometry.Fibres.extendsOverNeighbourhood_of_isProper`.

## References

* [Stacks Project, Tag 03H2](https://stacks.math.columbia.edu/tag/03H2)
* [Stacks Project, Tag 03GY](https://stacks.math.columbia.edu/tag/03GY)
* [Stacks Project, Tag 03GZ](https://stacks.math.columbia.edu/tag/03GZ)
* [Stacks Project, Tag 0FD1](https://stacks.math.columbia.edu/tag/0FD1)
* [Stacks Project, Tag 0G7X](https://stacks.math.columbia.edu/tag/0G7X)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- Two equal morphisms of schemes have the same maps on sections, with no `eqToHom` left over:
the inequality witnessing the pair of opens is a proof, hence irrelevant. -/
private theorem appLE_eq_of_eq {A B : Scheme.{u}} {g g' : A ⟶ B} (h : g = g') (V : B.Opens)
    (W : A.Opens) (e : W ≤ g ⁻¹ᵁ V) (e' : W ≤ g' ⁻¹ᵁ V) : g.appLE V W e = g'.appLE V W e' := by
  subst h; rfl

/-- The unique point of `Spec κ(s)` is carried to `s`, so the preimage of a neighbourhood of `s`
is everything. -/
public theorem top_le_preimage_fromSpecResidueField {s : S} {U : S.Opens} (hs : s ∈ U) :
    (⊤ : (Spec (S.residueField s)).Opens) ≤ S.fromSpecResidueField s ⁻¹ᵁ U := by
  intro x _
  show S.fromSpecResidueField s x ∈ U
  rw [Scheme.fromSpecResidueField_apply]
  exact hs

/-- The ring of global sections of a nonempty fibre is nontrivial. -/
private theorem nontrivial_sections_fiber (f : X ⟶ S) (s : S) [Nonempty (f.fiber s)] :
    Nontrivial Γ(f.fiber s, ⊤) :=
  have : Nonempty ((⊤ : (f.fiber s).Opens)) := ⟨⟨Classical.arbitrary _, trivial⟩⟩
  Scheme.component_nontrivial _ ⊤

/-- The fibre of a proper morphism over `s` is proper over `Spec κ(s)`. -/
private theorem isProper_fiberToSpecResidueField (f : X ⟶ S) [IsProper f] (s : S) :
    IsProper (f.fiberToSpecResidueField s) :=
  inferInstanceAs (IsProper (pullback.snd f (S.fromSpecResidueField s)))

/-- The fibre of a surjective morphism over any point is nonempty. -/
private theorem nonempty_fiber_of_surjective (f : X ⟶ S) [Surjective f] (s : S) :
    Nonempty (f.fiber s) := by
  obtain ⟨x, hx⟩ := f.surjective s
  exact ⟨(f.fiberHomeo s).symm ⟨x, hx⟩⟩

/-- **Stacks Project, Tag 0G7X.**  Restricting to the fibre `X_s` a section of `𝒪_X` pulled back
from an open neighbourhood `U` of `s` is the same as pulling back along the structure morphism
`X_s ⟶ Spec κ(s)` a section pulled back from `U`:  this is the cartesian square defining the
fibre, read on sections.  In particular the image of `Γ(S, U)` in `Γ(X_s, 𝒪_{X_s})` lies in the
image of the residue field `κ(s)`. -/
public theorem app_comp_fiberι_appLE (f : X ⟶ S) (s : S) {U : S.Opens} (hs : s ∈ U) :
    f.app U ≫ (f.fiberι s).appLE (f ⁻¹ᵁ U) ⊤
        (Fibres.fiberι_preimage_preimage_eq_top f hs).ge =
      (S.fromSpecResidueField s).appLE U ⊤ (top_le_preimage_fromSpecResidueField hs) ≫
        (f.fiberToSpecResidueField s).appTop := by
  have hap : (f.fiberToSpecResidueField s).appTop
      = (f.fiberToSpecResidueField s).appLE ⊤ ⊤ (Scheme.Hom.preimage_top _).ge := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact appLE_eq_of_eq rfl ⊤ _ _ _
  rw [hap, Scheme.Hom.appLE_comp_appLE (f.fiberToSpecResidueField s)
    (S.fromSpecResidueField s), Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_comp_appLE (f.fiberι s) f]
  exact appLE_eq_of_eq (Scheme.Hom.fiber_fac f s) U ⊤ _ _

/-- For a morphism `f : X ⟶ S` with `f_*𝒪_X = 𝒪_S`, a function on the fibre `X_s` that is the
restriction of a section of `𝒪_X` over `f ⁻¹ᵁ U` for some neighbourhood `U` of `s` is the
pullback of a section over `Spec κ(s)`:  the section over `f ⁻¹ᵁ U` comes from `Γ(S, U)` because
`f_*𝒪_X = 𝒪_S`, and sections from the base reach the fibre through the residue field.

This is the step at which the conclusion of [Stacks, Tag 0G7X] is converted into information
about `Γ(X_s, 𝒪_{X_s})`, in the proof of clause (1) of [Stacks, Tag 03H2]. -/
public theorem exists_appTop_eq_of_extendsOverNeighbourhood (f : X ⟶ S) (s : S) (hc : IsIso f.c)
    {e : Γ(f.fiber s, ⊤)} (he : Fibres.ExtendsOverNeighbourhood f s e) :
    ∃ c, (f.fiberToSpecResidueField s).appTop c = e := by
  obtain ⟨U, hsU, a, ha⟩ := he
  obtain ⟨b, hb⟩ := (ConcreteCategory.bijective_of_isIso (f.app U)).2 a
  refine ⟨(S.fromSpecResidueField s).appLE U ⊤ (top_le_preimage_fromSpecResidueField hsU) b, ?_⟩
  rw [← CommRingCat.comp_apply, ← app_comp_fiberι_appLE f s hsU, CommRingCat.comp_apply, hb, ha]

/-- **The connectedness input to clause (1) of [Stacks, Tag 03H2].**  For a morphism
`f : X ⟶ S` with `f_*𝒪_X = 𝒪_S` and nonempty fibre over `s`, an idempotent of
`Γ(X_s, 𝒪_{X_s})` that extends over a neighbourhood of `s` in the sense of [Stacks, Tag 0G7X] is
`0` or `1`:  it comes from the residue field `κ(s)`, which has no other idempotents. -/
public theorem eq_zero_or_one_of_isIdempotentElem_of_extendsOverNeighbourhood (f : X ⟶ S) (s : S)
    (hc : IsIso f.c) [Nonempty (f.fiber s)] {e : Γ(f.fiber s, ⊤)} (hidem : IsIdempotentElem e)
    (he : Fibres.ExtendsOverNeighbourhood f s e) : e = 0 ∨ e = 1 := by
  have := nontrivial_sections_fiber f s
  obtain ⟨c, hc'⟩ := exists_appTop_eq_of_extendsOverNeighbourhood f s hc he
  set ψ : S.residueField s ⟶ Γ(f.fiber s, ⊤) :=
    (Scheme.ΓSpecIso (S.residueField s)).inv ≫ (f.fiberToSpecResidueField s).appTop with hψ
  have hinj : Function.Injective ψ.hom := RingHom.injective _
  set r : S.residueField s := (Scheme.ΓSpecIso (S.residueField s)).hom c with hr
  have hre : ψ r = e := by rw [hψ, hr]; simpa using hc'
  have : IsIdempotentElem r := hinj (by rw [map_mul, hre]; exact hidem)
  obtain h | h := IsIdempotentElem.iff_eq_zero_or_one.mp this
  · exact Or.inl (by rw [← hre, h, map_zero])
  · exact Or.inr (by rw [← hre, h, map_one])

/-- **The connectedness half of clause (1) of [Stacks, Tag 03H2], reduced to [Stacks, Tag
0G7X].**  A proper morphism `f : X ⟶ S` with `f_*𝒪_X = 𝒪_S` has connected fibre over `s` as soon
as every idempotent of `Γ(X_s, 𝒪_{X_s})` extends over a neighbourhood of `s`.

The fibre is proper over the field `κ(s)`, so connectedness is equivalent to triviality of the
idempotents of its ring of global sections
(`Stacks.AlgebraicGeometry.ProperGeomConnected.connectedSpace_of_isProper_of_isIdempotentElem`),
and that is what the extension property gives. -/
public theorem connectedSpace_fiber_of_extendsOverNeighbourhood (f : X ⟶ S) [IsProper f] (s : S)
    (hc : IsIso f.c) [Nonempty (f.fiber s)]
    (he : ∀ e : Γ(f.fiber s, ⊤), IsIdempotentElem e → Fibres.ExtendsOverNeighbourhood f s e) :
    ConnectedSpace (f.fiber s) := by
  have := isProper_fiberToSpecResidueField f s
  have := nontrivial_sections_fiber f s
  exact ProperGeomConnected.connectedSpace_of_isProper_of_isIdempotentElem
    (L := S.residueField s) (f.fiberToSpecResidueField s) fun e hidem ↦
      eq_zero_or_one_of_isIdempotentElem_of_extendsOverNeighbourhood f s hc hidem (he e hidem)

/-- **The reduction of clause (1) of [Stacks, Tag 03H2] at one point to [Stacks, Tag 0G7X].**
Let `f : X ⟶ S` be proper and surjective with `f_*𝒪_X = 𝒪_S`.  If, for every étale neighbourhood
`U` of `(S, s)`, every idempotent of the ring of global sections of the fibre of `X_U ⟶ U` at the
distinguished point of `U` extends over a neighbourhood of that point, then the fibre of `f` at
`s` is geometrically connected.

This is the proof of clause (1) of Tag 03H2 given in the Stacks project, with its one unavailable
input isolated as the hypothesis:  [Stacks, Tag 03GZ] tests geometric connectedness of the fibre
on étale neighbourhoods, degree-zero flat base change ([Stacks, Tag 02KH]) carries
`f_*𝒪_X = 𝒪_S` along an étale neighbourhood, and the connectedness of a single fibre then follows
from Tag 0G7X. -/
public theorem geometricallyConnected_fiberToSpecResidueField_of_etaleNeighborhood (f : X ⟶ S)
    [IsProper f] [Surjective f] (s : S) (hc : IsIso f.c)
    (he : ∀ (U : EtaleNeighborhood S s) (e : Γ((pullback.snd f U.toBase).fiber U.point, ⊤)),
      IsIdempotentElem e →
        Fibres.ExtendsOverNeighbourhood (pullback.snd f U.toBase) U.point e) :
    GeometricallyConnected (f.fiberToSpecResidueField s) := by
  rw [geometricallyConnected_fiber_iff_forall_etaleNeighborhood]
  intro U
  have : Flat U.toBase := (Etale.iff_flat_and_formallyUnramified.mp inferInstance).1
  have hpb : IsPullback (pullback.fst f U.toBase) (pullback.snd f U.toBase) f U.toBase :=
    IsPullback.of_hasPullback _ _
  have hc' : IsIso (pullback.snd f U.toBase).c := isIso_c_of_isPullback_of_flat hpb hc
  have := nonempty_fiber_of_surjective (pullback.snd f U.toBase) U.point
  exact connectedSpace_fiber_of_extendsOverNeighbourhood _ U.point hc' (he U)

/-- For a morphism `f : X ⟶ S` with `f_*𝒪_X = 𝒪_S` and nonempty fibre over `s`, if *every*
function on the fibre `X_s` extends over a neighbourhood of `s` then the canonical map
`κ(s) ⟶ Γ(X_s, 𝒪_{X_s})` is an isomorphism:  it is surjective by the extension property and
injective because its source is a field and its target is nonzero. -/
public theorem isIso_appTop_fiberToSpecResidueField_of_extendsOverNeighbourhood (f : X ⟶ S)
    (s : S) (hc : IsIso f.c) [Nonempty (f.fiber s)]
    (he : ∀ e : Γ(f.fiber s, ⊤), Fibres.ExtendsOverNeighbourhood f s e) :
    IsIso (f.fiberToSpecResidueField s).appTop := by
  have := nontrivial_sections_fiber f s
  have hiso : IsIso ((Scheme.ΓSpecIso (S.residueField s)).inv ≫
      (f.fiberToSpecResidueField s).appTop) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨RingHom.injective _, fun e ↦ ?_⟩
    obtain ⟨c, hc'⟩ := exists_appTop_eq_of_extendsOverNeighbourhood f s hc (he e)
    exact ⟨(Scheme.ΓSpecIso (S.residueField s)).hom c, by simpa using hc'⟩
  have hcomp : IsIso ((Scheme.ΓSpecIso (S.residueField s)).hom ≫
      (Scheme.ΓSpecIso (S.residueField s)).inv ≫ (f.fiberToSpecResidueField s).appTop) :=
    inferInstance
  simpa using hcomp

/-- **Stacks Project, Tag 0FD1, read at a fibre.**  If `f : X ⟶ S` is proper and the canonical
map `κ(s) ⟶ Γ(X_s, 𝒪_{X_s})` is an isomorphism, then the fibre of `f` at `s` is geometrically
connected.

The fibre is proper over `κ(s)`, so Tag 0FD1 makes `X_s ⟶ Spec Γ(X_s, 𝒪_{X_s})` geometrically
connected;  the hypothesis says that this morphism *is* the structure morphism
`X_s ⟶ Spec κ(s)`, up to an isomorphism of the target. -/
@[ega "III 4.3.4" "special case"]
public theorem geometricallyConnected_fiberToSpecResidueField_of_isIso_appTop (f : X ⟶ S)
    [IsProper f] (s : S) (h : IsIso (f.fiberToSpecResidueField s).appTop) :
    GeometricallyConnected (f.fiberToSpecResidueField s) := by
  have := isProper_fiberToSpecResidueField f s
  have hgc : GeometricallyConnected (f.fiber s).toSpecΓ :=
    ProperGeomConnected.geometricallyConnected_toSpecΓ_of_isProper_over_field
      (S.residueField s) _ (f.fiberToSpecResidueField s)
  have hresp : MorphismProperty.RespectsIso @GeometricallyConnected :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have h1 : GeometricallyConnected ((f.fiber s).toSpecΓ ≫
      Spec.map (f.fiberToSpecResidueField s).appTop) :=
    (MorphismProperty.cancel_right_of_respectsIso @GeometricallyConnected _
      (Spec.map (f.fiberToSpecResidueField s).appTop)).mpr hgc
  rw [← Scheme.toSpecΓ_naturality] at h1
  exact (MorphismProperty.cancel_right_of_respectsIso @GeometricallyConnected
    (f.fiberToSpecResidueField s) (Spec (S.residueField s)).toSpecΓ).mp h1

/-- **Clause (1) of [Stacks, Tag 03H2] at one point, reduced to [Stacks, Tag 0G7X].**  A proper
morphism `f : X ⟶ S` with `f_*𝒪_X = 𝒪_S` has geometrically connected fibre over `s` as soon as
every function on `Γ(X_s, 𝒪_{X_s})` extends over a neighbourhood of `s`. -/
public theorem geometricallyConnected_fiberToSpecResidueField_of_extendsOverNeighbourhood
    (f : X ⟶ S) [IsProper f] (s : S) (hc : IsIso f.c) [Nonempty (f.fiber s)]
    (he : ∀ e : Γ(f.fiber s, ⊤), Fibres.ExtendsOverNeighbourhood f s e) :
    GeometricallyConnected (f.fiberToSpecResidueField s) :=
  geometricallyConnected_fiberToSpecResidueField_of_isIso_appTop f s
    (isIso_appTop_fiberToSpecResidueField_of_extendsOverNeighbourhood f s hc he)

/-- If the local ring of `X` at `x` is its own residue field, then `Spec κ(x) ⟶ X` is flat:  it
is then `Spec 𝒪_{X,x} ⟶ X` up to an isomorphism.  The hypothesis holds exactly when the maximal
ideal of `𝒪_{X,x}` vanishes, as at every point of a reduced zero-dimensional scheme and at every
generic point of a reduced scheme. -/
public theorem flat_fromSpecResidueField_of_isIso_residue (x : X) [IsIso (X.residue x)] :
    Flat (X.fromSpecResidueField x) := by
  rw [Scheme.fromSpecResidueField]
  have h₁ : Flat (Spec.map (X.residue x)) := inferInstance
  have h₂ : Flat (X.fromSpecStalk x) := flat_fromSpecStalk X x
  exact MorphismProperty.comp_mem _ _ _ h₁ h₂

/-- The condition `f_*𝒪_X = 𝒪_S` passes to the fibre over a point whose residue field is flat
over the base:  the fibre square is a flat base change, so
`Stacks.AlgebraicGeometry.isIso_c_of_isPullback_of_flat` applies and
`Γ(X_s, 𝒪_{X_s}) = κ(s)`.

Flatness of `Spec κ(s) ⟶ S` says that `κ(s)` is a flat `𝒪_{S,s}`-module;  for `S` locally
Noetherian this holds exactly when `𝒪_{S,s}` is a field, as it is at every point of a reduced
zero-dimensional scheme and at every generic point of a reduced scheme. -/
public theorem isIso_c_fiberToSpecResidueField_of_flat (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] (s : S) [Flat (S.fromSpecResidueField s)] (hc : IsIso f.c) :
    IsIso (f.fiberToSpecResidueField s).c :=
  have h : IsPullback (f.fiberι s) (f.fiberToSpecResidueField s) f (S.fromSpecResidueField s) :=
    IsPullback.of_hasPullback _ _
  isIso_c_of_isPullback_of_flat h hc

/-- **The unconditional special case of clause (1) of [Stacks, Tag 03H2].**  A proper morphism
`f : X ⟶ S` with `f_*𝒪_X = 𝒪_S` has geometrically connected fibre over every point `s` whose
residue field is flat over the base — equivalently, for `S` locally Noetherian, over every point
at which the local ring of `S` is a field.

No form of [Stacks, Tag 0G7X] is used:  flat base change ([Stacks, Tag 02KH] in degree zero)
carries `f_*𝒪_X = 𝒪_S` to `Γ(X_s, 𝒪_{X_s}) = κ(s)` directly. -/
public theorem geometricallyConnected_fiberToSpecResidueField_of_flat (f : X ⟶ S) [IsProper f]
    (s : S) [Flat (S.fromSpecResidueField s)] (hc : IsIso f.c) :
    GeometricallyConnected (f.fiberToSpecResidueField s) := by
  have : IsIso (f.fiberToSpecResidueField s).c := isIso_c_fiberToSpecResidueField_of_flat f s hc
  have happ : IsIso ((f.fiberToSpecResidueField s).app ⊤) := inferInstance
  exact geometricallyConnected_fiberToSpecResidueField_of_isIso_appTop f s happ

/-- **The unconditional special case of clause (1) of [Stacks, Tag 03H2], in checkable form.**  A
proper morphism `f : X ⟶ S` with `f_*𝒪_X = 𝒪_S` has geometrically connected fibre over every
point `s` at which the local ring of `S` is its own residue field. -/
public theorem geometricallyConnected_fiberToSpecResidueField_of_isIso_residue (f : X ⟶ S)
    [IsProper f] (s : S) [IsIso (S.residue s)] (hc : IsIso f.c) :
    GeometricallyConnected (f.fiberToSpecResidueField s) :=
  have := flat_fromSpecResidueField_of_isIso_residue s
  geometricallyConnected_fiberToSpecResidueField_of_flat f s hc

end Stacks.AlgebraicGeometry

namespace Stacks.SteinFactorization

open Stacks.AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]

/-- **The special case of the connectedness assertion in clause (1) of [Stacks, Tag 03H2] proved
here.**  For `f : X ⟶ S` proper, the first factor `f' : X ⟶ S'` of the Stein factorization has
geometrically connected fibre over every point `s` of `S'` whose residue field is flat over `S'`
— equivalently, for `S'` locally Noetherian, over every point at which `𝒪_{S',s}` is a field.

The input is clause (3), `f'_*𝒪_X = 𝒪_{S'}`, which flat base change carries to
`Γ(X_s, 𝒪_{X_s}) = κ(s)`;  [Stacks, Tag 0FD1] then gives geometric connectedness.  The general
case, where `𝒪_{S',s}` is not a field, is not proved in this repository:  it needs
[Stacks, Tag 0G7X], see
`Stacks.SteinFactorization.geometricallyConnected_toNormalization_of_etaleNeighborhood` and the
module documentation. -/
public theorem geometricallyConnected_fiberToSpecResidueField_toNormalization_of_flat
    (s : f.normalization) [Flat (f.normalization.fromSpecResidueField s)] :
    GeometricallyConnected (f.toNormalization.fiberToSpecResidueField s) :=
  have := isProper_toNormalization f
  geometricallyConnected_fiberToSpecResidueField_of_flat
    f.toNormalization s (isIso_c_toNormalization f)

/-- **The special case of the connectedness assertion in clause (1) of [Stacks, Tag 03H2] proved
here, in checkable form.**  For `f : X ⟶ S` proper, the first factor `f' : X ⟶ S'` of the Stein
factorization has geometrically connected fibre over every point of `S'` at which the local ring
of `S'` is its own residue field — for instance over every generic point of `S'` when `S'` is
reduced. -/
public theorem geometricallyConnected_fiberToSpecResidueField_toNormalization_of_isIso_residue
    (s : f.normalization) [IsIso (f.normalization.residue s)] :
    GeometricallyConnected (f.toNormalization.fiberToSpecResidueField s) :=
  have := isProper_toNormalization f
  geometricallyConnected_fiberToSpecResidueField_of_isIso_residue f.toNormalization s
    (isIso_c_toNormalization f)

/-- **The connectedness half of clause (1) of [Stacks, Tag 03H2], at one point, reduced to
[Stacks, Tag 0G7X].**  The fibre of the first factor of the Stein factorization of a proper
morphism over a point `s` of `S'` is connected as soon as every idempotent of
`Γ(X_s, 𝒪_{X_s})` extends over a neighbourhood of `s`. -/
public theorem connectedSpace_fiber_toNormalization_of_extendsOverNeighbourhood
    (s : f.normalization)
    (he : ∀ e : Γ(f.toNormalization.fiber s, ⊤), IsIdempotentElem e →
      Fibres.ExtendsOverNeighbourhood f.toNormalization s e) :
    ConnectedSpace (f.toNormalization.fiber s) :=
  have := isProper_toNormalization f
  have := nonempty_fiber_of_surjective f.toNormalization s
  connectedSpace_fiber_of_extendsOverNeighbourhood f.toNormalization s
    (isIso_c_toNormalization f) he

/-- **Clause (1) of [Stacks, Tag 03H2], conditional on [Stacks, Tag 0G7X] in the strong form in
which every function on a fibre extends.**  If every function on every fibre of the first factor
`f' : X ⟶ S'` of the Stein factorization of a proper morphism extends over a neighbourhood of
its base point, then `f'` has geometrically connected fibres.

The hypothesis is stronger than Tag 0G7X, which asserts the extension property only for
idempotents;  for the reduction that uses Tag 0G7X as stated see
`Stacks.AlgebraicGeometry.geometricallyConnected_fiberToSpecResidueField_of_etaleNeighborhood`. -/
public theorem geometricallyConnected_toNormalization_of_extendsOverNeighbourhood
    (he : ∀ (s : f.normalization) (e : Γ(f.toNormalization.fiber s, ⊤)),
      Fibres.ExtendsOverNeighbourhood f.toNormalization s e) :
    GeometricallyConnected f.toNormalization := by
  have := isProper_toNormalization f
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  intro s
  have := nonempty_fiber_of_surjective f.toNormalization s
  exact geometricallyConnected_fiberToSpecResidueField_of_extendsOverNeighbourhood
    f.toNormalization s (isIso_c_toNormalization f) (he s)

/-- **Clause (1) of [Stacks, Tag 03H2], reduced to [Stacks, Tag 0G7X].**  The first factor
`f' : X ⟶ S'` of the Stein factorization of a proper morphism has geometrically connected fibres
provided that, over every point `s` of `S'` and every étale neighbourhood `U` of `(S', s)`, the
idempotents of the ring of global sections of the fibre of `X_U ⟶ U` at the distinguished point
of `U` extend over a neighbourhood of that point.

The hypothesis is exactly Tag 0G7X for the base changes of `f'` to étale neighbourhoods of `S'`,
and it is the only input to clause (1) that is unavailable in this repository;  see the module
documentation.  Tag 0G7X is the conclusion of a *different* tag, which clause (1) quotes rather
than proves, so it is carried here as the named hypothesis `he`;  once it is available, `he` is
discharged and nothing else about this statement changes. -/
-- No `@[stacks 03H2]` here: this declaration carries a mathematical input as a hypothesis,
-- and a tag counts only on a declaration proved under the source's own hypotheses.
-- The input is Tag 0G7X; clauses (2)-(5) and the properness half of (1) keep their own
-- unconditional registrations in SteinFactorization/Proper.lean.
public theorem geometricallyConnected_toNormalization_of_etaleNeighborhood
    (he : ∀ (s : f.normalization) (U : EtaleNeighborhood f.normalization s)
      (e : Γ((pullback.snd f.toNormalization U.toBase).fiber U.point, ⊤)), IsIdempotentElem e →
        Fibres.ExtendsOverNeighbourhood
          (pullback.snd f.toNormalization U.toBase) U.point e) :
    GeometricallyConnected f.toNormalization := by
  have := isProper_toNormalization f
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  intro s
  exact geometricallyConnected_fiberToSpecResidueField_of_etaleNeighborhood
    f.toNormalization s (isIso_c_toNormalization f) (he s)

/-- **Stacks Project, Tag 03H2, clause (1), the geometric connectedness conjunct.**  For `f`
proper onto an arbitrary scheme `S`, the first factor `f' : X ⟶ S'` of the Stein factorization —
`S'` the normalization of `S` in `X` and `f' = f.toNormalization` — has geometrically connected
fibres.

Unconditional, at the hypotheses of the tag:  nothing is assumed of `S`.  The two inputs are the
reduction above, which is the source's — [Stacks, Tag 03GZ] together with degree-zero flat base
change and `f'_* 𝒪_X = 𝒪_{S'}` — and [Stacks, Tag 0G7X] for the base changes of `f'` to étale
neighbourhoods of `S'`, which is
`Stacks.AlgebraicGeometry.Fibres.extendsOverNeighbourhood_of_isProper`.

The same statement covers the connectedness conjunct of clause (1) of [Stacks, Tag 03H0], whose
hypotheses are strictly stronger;
`Stacks.SteinFactorization.geometricallyConnected_toNormalization` in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Noetherian` is that reading of it.
The properness conjunct of clause (1) is `Stacks.SteinFactorization.isProper_toNormalization`. -/
@[stacks 03H2 "clause (1), the geometric connectedness conjunct: the first factor of the Stein \
  factorization of a proper morphism has geometrically connected fibres, over an arbitrary base. \
  The properness conjunct of the same clause is isProper_toNormalization",
  ega "III 4.3.4" "partial"]
public theorem geometricallyConnected_toNormalization_of_isProper :
    GeometricallyConnected f.toNormalization := by
  have : IsProper f.toNormalization := isProper_toNormalization f
  refine geometricallyConnected_toNormalization_of_etaleNeighborhood f (fun s U e he => ?_)
  exact Stacks.AlgebraicGeometry.Fibres.extendsOverNeighbourhood_of_isProper
    (pullback.snd f.toNormalization U.toBase) U.point e he

end Stacks.SteinFactorization
