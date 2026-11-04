module

public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.MaximalLocus

/-!
# Maximal loci of a source-local property in a groupoid slice

The transfer principle `AlgebraicGeometry.exists_open_with_preimage_maximal_locus` asks for two
things about the property `P` whose locus is to be descended: that maximal open `P`-loci exist
for `Q`-morphisms, and that they commute with base change along `R`-morphisms.  For every
property occurring in the list of Stacks Tag 047W both are consequences of one pointwise
condition `At`: the set of points where `At` holds is open, a restriction of the morphism to an
open has `P` exactly when `At` holds at each of its points, and `At` is insensitive to base
change along an `R`-morphism.  This file records that reduction once.

## Main definitions

This file introduces no definitions.

## Main results

* `AlgebraicGeometry.comp_ι_iff_forall_exists_mem`: for a property local on the source for the
  Zariski topology, the restriction of a morphism to an open has the property exactly when every
  point of that open has a neighbourhood whose restriction has it.
* `AlgebraicGeometry.comp_ι_of_appLE` and `AlgebraicGeometry.exists_appLE_of_comp_ι`: for a
  property of morphisms defined by a property of ring maps, the passage between the restriction
  to an open and the maps of sections over affine charts.
* `AlgebraicGeometry.exists_open_with_preimage_maximal_locus_of_pointwise`: the transfer
  principle, in the form fed by a pointwise condition.

## Implementation notes

The pointwise condition is a parameter rather than being defined as "some open neighbourhood
whose restriction has `P`", because the base-change hypothesis is always verified for a
recognizable condition — flatness of a stalk map, the dimension of a fibre, an affine chart on
which the map of sections has a property of ring maps — and not for the existential.  The
hypothesis `hpt` is where the two are matched up, and it is the only place a property-specific
argument about neighbourhoods is needed.

Maximality of the locus is `IsGreatest` on the lattice of opens, as in the transfer principle
itself; uniqueness of a greatest element is what identifies the locus supplied by an arbitrary
`IsGreatest` hypothesis with the set of points where `At` holds.

The two chart lemmas are the generic form of the `private` pair inside
`StacksFrontier.AlgebraicGeometry.Curves.NodalLocus`; they are stated here, and publicly, because
the syntomic and unramified cases of Tag 047W need them and must not acquire that file's import
cone.

## References

* [Stacks Project, Tag 04LH](https://stacks.math.columbia.edu/tag/04LH)
* [Stacks Project, Tag 047W](https://stacks.math.columbia.edu/tag/047W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- A property local on the source holds for the restriction of a morphism to a smaller open as
soon as it holds for the restriction to a larger one. -/
public theorem comp_ι_of_le {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtSource P]
    {X S : Scheme.{u}} {f : X ⟶ S} {U V : X.Opens} (h : V ≤ U) (hU : P (U.ι ≫ f)) :
    P (V.ι ≫ f) := by
  have h' := IsZariskiLocalAtSource.comp hU (X.homOfLE h)
  rwa [← Category.assoc, X.homOfLE_ι] at h'

/-- **A source-local property on an open is a pointwise condition.**  For a property of
morphisms local on the source for the Zariski topology, the restriction of `f` to an open `W`
has the property exactly when every point of `W` has an open neighbourhood to which the
restriction of `f` has it. -/
public theorem comp_ι_iff_forall_exists_mem (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtSource P] {X S : Scheme.{u}} (f : X ⟶ S) (W : X.Opens) :
    P (W.ι ≫ f) ↔ ∀ x ∈ W, ∃ U : X.Opens, x ∈ U ∧ P (U.ι ≫ f) := by
  classical
  refine ⟨fun h x hx => ⟨W, hx, h⟩, fun h => ?_⟩
  choose A hAmem hPA using fun y : W.toScheme => h y.1 y.2
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := P)
    (U := fun y : W.toScheme => W.ι ⁻¹ᵁ A y) ?_ fun y => ?_
  · refine top_le_iff.mp fun z _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨z, ?_⟩
    exact hAmem z
  · have hrange : Set.range ((W.ι ⁻¹ᵁ A y).ι ≫ W.ι) ⊆ Set.range (A y).ι := by
      rintro - ⟨z, rfl⟩
      exact ⟨⟨W.ι ((W.ι ⁻¹ᵁ A y).ι z), z.2⟩, rfl⟩
    rw [← Category.assoc, ← IsOpenImmersion.lift_fac (A y).ι _ hrange, Category.assoc]
    exact IsZariskiLocalAtSource.comp (hPA y) _

/-- If the map of sections of `f` over a pair of affine opens `U ≤ f ⁻¹ᵁ V` has the property `Q`
of ring maps defining `P`, then `P` holds for the restriction of `f` to `U`. -/
public theorem comp_ι_of_appLE (P : MorphismProperty Scheme.{u})
    {Q : ∀ {R T : Type u} [CommRing R] [CommRing T], (R →+* T) → Prop}
    [HasRingHomProperty P Q] [P.RespectsRight @IsOpenImmersion]
    {X S : Scheme.{u}} (f : X ⟶ S) {U : X.Opens} (hU : IsAffineOpen U)
    {V : S.Opens} (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V)
    (h : Q (f.appLE V U e).hom) : P (U.ι ≫ f) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have h1 : P (f.resLE V U e) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := P)]
    exact ((HasRingHomProperty.isLocal_ringHomProperty P).respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso f V U e)).mpr h
  simpa only [Scheme.Hom.resLE_comp_ι] using
    MorphismProperty.RespectsRight.postcomp (Q := @IsOpenImmersion) V.ι inferInstance _ h1

/-- If `P` holds for the restriction of `f` to an open `C`, then around every point of `C` there
is a pair of affine opens on which the map of sections of `f` has the property `Q` of ring maps
defining `P`. -/
public theorem exists_appLE_of_comp_ι (P : MorphismProperty Scheme.{u})
    {Q : ∀ {R T : Type u} [CommRing R] [CommRing T], (R →+* T) → Prop}
    [HasRingHomProperty P Q] [IsZariskiLocalAtSource P]
    {X S : Scheme.{u}} (f : X ⟶ S) {C : X.Opens} (h : P (C.ι ≫ f)) {x : X} (hx : x ∈ C) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ V : S.affineOpens, ∃ e : U.1 ≤ f ⁻¹ᵁ V.1,
      Q (f.appLE V.1 U.1 e).hom := by
  have aff : ∀ {Y : Scheme.{u}} {y : Y} {O : Y.Opens}, y ∈ O →
      ∃ A : Y.affineOpens, y ∈ A.1 ∧ A.1 ≤ O := fun hy =>
    let ⟨A, hA, hyA, hAO⟩ := exists_isAffineOpen_mem_and_subset hy
    ⟨⟨A, hA⟩, hyA, hAO⟩
  obtain ⟨V, hfxV, -⟩ := aff (O := ⊤) (y := f x) trivial
  obtain ⟨U, hxU, hUsub⟩ := aff (O := C ⊓ f ⁻¹ᵁ V.1) ⟨hx, hfxV⟩
  have e : U.1 ≤ f ⁻¹ᵁ V.1 := fun z hz => (hUsub hz).2
  have hPU : P (U.1.ι ≫ f) := comp_ι_of_le (fun z hz => (hUsub hz).1) h
  have : IsAffine U.1.toScheme := U.2
  have htop : (⊤ : U.1.toScheme.Opens) ≤ (U.1.ι ≫ f) ⁻¹ᵁ V.1 := fun z _ => e z.2
  have hQ := HasRingHomProperty.appLE P (U.1.ι ≫ f) hPU V
    ⟨⊤, isAffineOpen_top U.1.toScheme⟩ htop
  refine ⟨U, hxU, V, e, ?_⟩
  rw [← Scheme.Hom.appLE_comp_appLE U.1.ι f V.1 U.1 ⊤ e U.1.ι_preimage_self.ge,
    CommRingCat.hom_comp] at hQ
  exact ((HasRingHomProperty.isLocal_ringHomProperty P).respectsIso.cancel_right_isIso
    (f.appLE V.1 U.1 e) (U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge)).mp hQ

/-- **The transfer principle of Stacks Tag 04LH, fed by a pointwise condition.**  Let `P`, `Q`
and `R` be properties of morphisms of schemes with `R ≤ Q`, with `Q` stable under composition
and base change and `P` local on the source for the Zariski topology.  Suppose a pointwise
condition `At` is given for which, over a `Q`-morphism, the locus where it holds is open and the
restriction of the morphism to an open has `P` exactly when the condition holds at every point
of that open, and which is unchanged by base change along an `R`-morphism.  Then for a groupoid
scheme whose source and target maps have `R`, and a `Q`-morphism `g : U' ⟶ U` to its object
scheme, the maximal `P`-locus of `h : U' ×_{g, U, t} R ⟶ U` is the inverse image of an open of
`U'`. -/
public theorem exists_open_with_preimage_maximal_locus_of_pointwise
    (P Q R : MorphismProperty Scheme.{u}) (hRQ : R ≤ Q)
    [Q.IsStableUnderComposition] [Q.IsStableUnderBaseChange] [IsZariskiLocalAtSource P]
    (At : ∀ X Y : Scheme.{u}, (X ⟶ Y) → X → Prop)
    (hopen : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y), Q f → IsOpen {x : X | At X Y f x})
    (hpt : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y), Q f → ∀ x : X,
      ((∃ U : X.Opens, x ∈ U ∧ P (U.ι ≫ f)) ↔ At X Y f x))
    (hbc : ∀ {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {p : X' ⟶ X} {q : Y' ⟶ Y},
      Q f → R q → IsPullback p f' f q → ∀ x' : X', (At X' Y' f' x' ↔ At X Y f (p x')))
    {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Scheme.{u}}
    (g : U' ⟶ G.objects.left) (hs : R G.source.left) (ht : R G.target.left) (hg : Q g) :
    ∃ W : U'.Opens,
      IsGreatest
        {V : (pullback g G.target.left).Opens |
          P (V.ι ≫ pullback.snd g G.target.left ≫ G.source.left)}
        ((pullback.fst g G.target.left) ⁻¹ᵁ W) := by
  have key : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (hf : Q f),
      IsGreatest {W : X.Opens | P (W.ι ≫ f)}
        (⟨{x : X | At X Y f x}, hopen X Y f hf⟩ : X.Opens) := by
    intro X Y f hf
    refine ⟨(comp_ι_iff_forall_exists_mem P f _).mpr fun x hx => (hpt X Y f hf x).mpr hx,
      fun W hW x hx => (hpt X Y f hf x).mp ⟨W, hx, hW⟩⟩
  refine exists_open_with_preimage_maximal_locus P Q R hRQ ?_ ?_ G g hs ht hg
  · intro X Y f hf
    exact ⟨_, key X Y f hf⟩
  · intro X Y X' Y' f f' p q hf hq hp V hV
    have hf' : Q f' := MorphismProperty.IsStableUnderBaseChange.of_isPullback hp hf
    have hVeq : V = (⟨{x : X | At X Y f x}, hopen X Y f hf⟩ : X.Opens) :=
      hV.unique (key X Y f hf)
    have himg : p ⁻¹ᵁ V = (⟨{x' : X' | At X' Y' f' x'}, hopen X' Y' f' hf'⟩ : X'.Opens) := by
      rw [hVeq]
      ext x'
      exact (hbc hf hq hp x').symm
    rw [himg]
    exact key X' Y' f' hf'

end AlgebraicGeometry
