module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.OverCoproduct
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.RestrictionProperties
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.GroupoidRestriction
public import StacksFrontier.AlgebraicGeometry.Morphisms.JacobsonPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs

/-!
# Restricting a groupoid scheme along a coproduct of morphisms

Let `G` be a groupoid scheme over `S` with object scheme `U` and arrow scheme `R`, and let
`g i : U'_i ⟶ U` be a family of morphisms of `S`-schemes.  Their coproduct
`g = ∐ g i : ∐ U'_i ⟶ U` is a morphism of `S`-schemes, and `G` restricts along it.

What this file computes is the *reach map* of that coproduct.  The reach map of a morphism
`g : U' ⟶ U` is `h : U' ×_{g, U, t} R ⟶ U`, the morphism sending an arrow of `R` whose target
lifts along `g` to its source; it is the morphism from which the source and target maps of the
restriction `R|_{U'}` inherit their properties, by Stacks 04MV.  Because a fibre product over a
coproduct is the coproduct of the fibre products over the members
(`AlgebraicGeometry.nonempty_isColimit_cofanMk_of_isPullback_sigmaDesc`), the reach map of
`∐ g i` is the coproduct `∐ h i` of the reach maps of the members.  Hence it has every property
of morphisms of schemes which is Zariski-local at the source and holds for each `h i`, and it
is surjective as soon as the `h i` are jointly surjective — which, the `h i` being flat and
locally of finite presentation, it is enough to know at the finite type points of `U`.

This is Step 3 of the proof of Stacks 0489: `U'` is the coproduct of the affine slices produced
by Stacks 04N0 over the finite type points of `U`, and the reach map of the coproduct is flat,
locally of finite presentation and locally quasi-finite because each member's is, and
surjective because the image of the `u`-th member contains `u`.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.sigmaRestrictionReachι` is the comparison morphism from the
  source of the reach map of the `i`-th member to the source of the reach map of the
  coproduct.

## Main results

* `AlgebraicGeometry.GroupoidScheme.nonempty_isColimit_cofanMk_sigmaRestrictionReachι` and
  `AlgebraicGeometry.GroupoidScheme.nonempty_isColimit_cofanMk_sigmaRestrictionReachι_left`:
  the source of the reach map of the coproduct is the coproduct of the sources of the reach
  maps of the members, in `Over S` and on underlying schemes.
* `AlgebraicGeometry.GroupoidScheme.reach_sigmaOverDesc_mem`: the reach map of the coproduct
  has every property which is Zariski-local at the source and holds for the reach maps of the
  members.
* `AlgebraicGeometry.jointlySurjective_of_isFiniteTypePoint`: a family of flat morphisms
  locally of finite presentation whose images contain every finite type point of the target is
  jointly surjective.
* `AlgebraicGeometry.GroupoidScheme.surjective_reach_sigmaOverDesc` and
  `AlgebraicGeometry.GroupoidScheme.surjective_reach_sigmaOverDesc_of_isFiniteTypePoint`: the
  reach map of the coproduct is surjective when the reach maps of the members are jointly
  surjective, and that holds as soon as their images contain the finite type points.
* `AlgebraicGeometry.GroupoidScheme.restriction_sigmaOverDesc_mem`: the source and target maps
  of the restriction of `G` along the coproduct are flat, locally of finite presentation,
  locally of finite type and locally quasi-finite as soon as the reach maps of the members
  are flat, locally of finite presentation and locally quasi-finite.

## Implementation notes

The three properties the application needs — flatness, local finite presentation and local
quasi-finiteness — are Zariski-local at the source, but their
`AlgebraicGeometry.IsZariskiLocalAtSource` instances are not found by instance resolution,
since the ring-homomorphism property each one is affine-locally defined by is not determined by
the morphism property.  Each is therefore supplied explicitly from
`AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource`, as elsewhere in this
library.

The conclusion of `AlgebraicGeometry.GroupoidScheme.restriction_sigmaOverDesc_mem` is stated
for every groupoid scheme realizing the restriction, as
`AlgebraicGeometry.restriction_source_mem` and `AlgebraicGeometry.restriction_target_mem` are,
rather than for the realization built by `AlgebraicGeometry.GroupoidScheme.restrict`.

## References

* [Stacks Project, Tag 04MV](https://stacks.math.columbia.edu/tag/04MV)
* [Stacks Project, Tag 04N0](https://stacks.math.columbia.edu/tag/04N0)
* [Stacks Project, Tag 0489](https://stacks.math.columbia.edu/tag/0489)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u v

namespace AlgebraicGeometry

/-- A family of flat morphisms locally of finite presentation to a scheme whose images contain
every finite type point of the target is jointly surjective.

The images are open, since a flat morphism locally of finite presentation is universally open,
so the complement of their union is closed; were it nonempty it would contain a finite type
point, which lies in one of the images. -/
theorem jointlySurjective_of_isFiniteTypePoint {ι : Type v} {X : ι → Scheme.{u}}
    {Y : Scheme.{u}} (f : ∀ i, X i ⟶ Y) (hflat : ∀ i, Flat (f i))
    (hfp : ∀ i, LocallyOfFinitePresentation (f i))
    (h : ∀ y : Y, IsFiniteTypePoint y → ∃ i, y ∈ Set.range (f i)) (y : Y) :
    ∃ i, y ∈ Set.range (f i) := by
  by_contra hy
  have : ∀ i, Flat (f i) := hflat
  have : ∀ i, LocallyOfFinitePresentation (f i) := hfp
  have hopen : IsOpen (⋃ i, Set.range (f i)) :=
    isOpen_iUnion fun i => (f i).isOpenMap.isOpen_range
  have hne : (⋃ i, Set.range (f i))ᶜ.Nonempty := ⟨y, by simpa [Set.mem_iUnion] using hy⟩
  obtain ⟨z, hzT, hzft⟩ :=
    inter_finiteTypePoints_nonempty hopen.isClosed_compl.isLocallyClosed hne
  obtain ⟨i, hi⟩ := h z hzft
  exact hzT (Set.mem_iUnion.mpr ⟨i, hi⟩)

namespace GroupoidScheme

variable {S : Scheme.{u}} {ι : Type v} [Small.{u} ι] (G : GroupoidScheme S) {U : ι → Over S}

/-- The comparison morphism from the source `U'_i ×_{g i, U, t} R` of the reach map of the
`i`-th member of a family to the source `(∐ U'_i) ×_{∐ g i, U, t} R` of the reach map of the
coproduct. -/
noncomputable def sigmaRestrictionReachι (g : ∀ i, U i ⟶ G.objects) (i : ι) :
    pullback (g i) G.target ⟶ pullback (sigmaOverDesc g) G.target :=
  pullback.lift (pullback.fst (g i) G.target ≫ sigmaOverι U i) (pullback.snd (g i) G.target)
    (by rw [Category.assoc, sigmaOverι_desc]; exact pullback.condition)

/-- The comparison morphism followed by the first projection is the first projection followed by
the coprojection `U'_i ⟶ ∐ U'_i`. -/
@[reassoc (attr := simp)]
lemma sigmaRestrictionReachι_fst (g : ∀ i, U i ⟶ G.objects) (i : ι) :
    sigmaRestrictionReachι G g i ≫ pullback.fst (sigmaOverDesc g) G.target =
      pullback.fst (g i) G.target ≫ sigmaOverι U i :=
  pullback.lift_fst _ _ _

/-- The comparison morphism followed by the second projection to `R` is the second projection. -/
@[reassoc (attr := simp)]
lemma sigmaRestrictionReachι_snd (g : ∀ i, U i ⟶ G.objects) (i : ι) :
    sigmaRestrictionReachι G g i ≫ pullback.snd (sigmaOverDesc g) G.target =
      pullback.snd (g i) G.target :=
  pullback.lift_snd _ _ _

/-- The comparison morphisms are morphisms over the object scheme: the reach map of the
coproduct restricts on the `i`-th member to the reach map of that member. -/
@[reassoc (attr := simp)]
lemma sigmaRestrictionReachι_comp_reach (g : ∀ i, U i ⟶ G.objects) (i : ι) :
    sigmaRestrictionReachι G g i ≫ restrictionReachMap G (sigmaOverDesc g) =
      restrictionReachMap G (g i) := by
  rw [restrictionReachMap, ← Category.assoc, sigmaRestrictionReachι_snd]

/-- `sigmaRestrictionReachι_comp_reach` on underlying schemes. -/
private lemma sigmaRestrictionReachι_left_comp_reach (g : ∀ i, U i ⟶ G.objects) (i : ι) :
    (sigmaRestrictionReachι G g i).left ≫ (restrictionReachMap G (sigmaOverDesc g)).left =
      (restrictionReachMap G (g i)).left := by
  rw [← Over.comp_left, sigmaRestrictionReachι_comp_reach]

/-- **The source of the reach map of a coproduct is the coproduct of the sources of the reach
maps of the members**, on underlying schemes. -/
theorem nonempty_isColimit_cofanMk_sigmaRestrictionReachι_left (g : ∀ i, U i ⟶ G.objects) :
    Nonempty (IsColimit (Cofan.mk (pullback (sigmaOverDesc g) G.target).left
      fun i => (sigmaRestrictionReachι G g i).left)) := by
  refine nonempty_isColimit_cofanMk_of_isPullback_sigmaDesc
    (overFibreProduct_isPullback (sigmaOverDesc g) G.target)
    (fun i => overFibreProduct_isPullback (g i) G.target) _ (fun i => ?_) (fun i => ?_)
  · exact congrArg Over.Hom.left (sigmaRestrictionReachι_fst G g i)
  · exact congrArg Over.Hom.left (sigmaRestrictionReachι_snd G g i)

/-- **The source of the reach map of a coproduct is the coproduct of the sources of the reach
maps of the members**, in `Over S`. -/
theorem nonempty_isColimit_cofanMk_sigmaRestrictionReachι (g : ∀ i, U i ⟶ G.objects) :
    Nonempty (IsColimit (Cofan.mk (pullback (sigmaOverDesc g) G.target)
      (sigmaRestrictionReachι G g))) :=
  ⟨isColimitCofanMkOfLeft _ (nonempty_isColimit_cofanMk_sigmaRestrictionReachι_left G g).some⟩

/-- The reach map of a coproduct of morphisms to the object scheme has every property of
morphisms of schemes which is Zariski-local at the source and holds for the reach maps of the
members. -/
theorem reach_sigmaOverDesc_mem {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtSource P]
    (g : ∀ i, U i ⟶ G.objects) (hP : ∀ i, P (restrictionReachMap G (g i)).left) :
    P (restrictionReachMap G (sigmaOverDesc g)).left := by
  have hiso : IsIso (Sigma.desc fun i => (sigmaRestrictionReachι G g i).left) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mp
      (nonempty_isColimit_cofanMk_sigmaRestrictionReachι_left G g)
  have key : (Sigma.desc fun i => (sigmaRestrictionReachι G g i).left) ≫
      (restrictionReachMap G (sigmaOverDesc g)).left =
      Sigma.desc fun i => (restrictionReachMap G (g i)).left :=
    Sigma.hom_ext _ _ fun i => by
      rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, sigmaRestrictionReachι_left_comp_reach]
  have h2 : P (Sigma.desc fun i => (restrictionReachMap G (g i)).left) :=
    IsZariskiLocalAtSource.sigmaDesc hP
  rw [← key] at h2
  exact (P.cancel_left_of_respectsIso _ _).mp h2

/-- The reach map of a coproduct of morphisms to the object scheme is surjective as soon as the
reach maps of the members are jointly surjective. -/
theorem surjective_reach_sigmaOverDesc (g : ∀ i, U i ⟶ G.objects)
    (h : ∀ y : G.objects.left, ∃ i, y ∈ Set.range (restrictionReachMap G (g i)).left) :
    Surjective (restrictionReachMap G (sigmaOverDesc g)).left := by
  refine ⟨fun y => ?_⟩
  obtain ⟨i, x, hx⟩ := h y
  exact ⟨(sigmaRestrictionReachι G g i).left x, by
    rw [← hx, ← sigmaRestrictionReachι_left_comp_reach G g i, Scheme.Hom.comp_apply]⟩

/-- The reach map of a coproduct of morphisms to the object scheme is surjective as soon as the
reach maps of the members are flat, locally of finite presentation, and have images containing
every finite type point of the object scheme.

This is how Step 3 of the proof of Stacks 0489 gets surjectivity: the family is indexed by the
finite type points `u` of `U` and the image of `h u` contains `u`. -/
theorem surjective_reach_sigmaOverDesc_of_isFiniteTypePoint (g : ∀ i, U i ⟶ G.objects)
    (hflat : ∀ i, Flat (restrictionReachMap G (g i)).left)
    (hfp : ∀ i, LocallyOfFinitePresentation (restrictionReachMap G (g i)).left)
    (h : ∀ y : G.objects.left, IsFiniteTypePoint y →
      ∃ i, y ∈ Set.range (restrictionReachMap G (g i)).left) :
    Surjective (restrictionReachMap G (sigmaOverDesc g)).left :=
  surjective_reach_sigmaOverDesc G g (jointlySurjective_of_isFiniteTypePoint _ hflat hfp h)

/-- The reach map of a coproduct is flat when the reach maps of the members are. -/
theorem reach_sigmaOverDesc_flat (g : ∀ i, U i ⟶ G.objects)
    (h : ∀ i, Flat (restrictionReachMap G (g i)).left) :
    Flat (restrictionReachMap G (sigmaOverDesc g)).left :=
  have : IsZariskiLocalAtSource @Flat.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  reach_sigmaOverDesc_mem G g h

/-- The reach map of a coproduct is locally of finite presentation when the reach maps of the
members are. -/
theorem reach_sigmaOverDesc_locallyOfFinitePresentation (g : ∀ i, U i ⟶ G.objects)
    (h : ∀ i, LocallyOfFinitePresentation (restrictionReachMap G (g i)).left) :
    LocallyOfFinitePresentation (restrictionReachMap G (sigmaOverDesc g)).left :=
  have : IsZariskiLocalAtSource @LocallyOfFinitePresentation.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
      (Q := RingHom.FinitePresentation)
  reach_sigmaOverDesc_mem G g h

/-- The reach map of a coproduct is locally quasi-finite when the reach maps of the members
are. -/
theorem reach_sigmaOverDesc_locallyQuasiFinite (g : ∀ i, U i ⟶ G.objects)
    (h : ∀ i, LocallyQuasiFinite (restrictionReachMap G (g i)).left) :
    LocallyQuasiFinite (restrictionReachMap G (sigmaOverDesc g)).left :=
  have : IsZariskiLocalAtSource @LocallyQuasiFinite.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyQuasiFinite)
      (Q := RingHom.QuasiFinite)
  reach_sigmaOverDesc_mem G g h

/-- **The restriction of a groupoid scheme along a coproduct of morphisms.**

Let `g i : U'_i ⟶ U` be a family of morphisms to the object scheme of a groupoid scheme `G`
whose reach maps `h i : U'_i ×_{g i, U, t} R ⟶ U` are flat, locally of finite presentation and
locally quasi-finite.  Then the source and target maps of the restriction of `G` along the
coproduct `∐ g i` are flat, locally of finite presentation, locally of finite type and locally
quasi-finite.

This is the conclusion Step 3 of the proof of Stacks 0489 draws from Stacks 04N0: by Stacks
04MV the source and target of the restriction are base changes of the reach map of the
coproduct, and that reach map is the coproduct of the reach maps of the members. -/
theorem restriction_sigmaOverDesc_mem (g : ∀ i, U i ⟶ G.objects)
    (R : GroupoidScheme.Restriction G (sigmaOverDesc g))
    (hflat : ∀ i, Flat (restrictionReachMap G (g i)).left)
    (hfp : ∀ i, LocallyOfFinitePresentation (restrictionReachMap G (g i)).left)
    (hqf : ∀ i, LocallyQuasiFinite (restrictionReachMap G (g i)).left) :
    Flat R.groupoid.source.left ∧
    LocallyOfFinitePresentation R.groupoid.source.left ∧
    LocallyOfFiniteType R.groupoid.source.left ∧
    LocallyQuasiFinite R.groupoid.source.left ∧
    Flat R.groupoid.target.left ∧
    LocallyOfFinitePresentation R.groupoid.target.left ∧
    LocallyOfFiniteType R.groupoid.target.left ∧
    LocallyQuasiFinite R.groupoid.target.left := by
  have hF : Flat (restrictionReachMap G (sigmaOverDesc g)).left :=
    reach_sigmaOverDesc_flat G g hflat
  have hP : LocallyOfFinitePresentation (restrictionReachMap G (sigmaOverDesc g)).left :=
    reach_sigmaOverDesc_locallyOfFinitePresentation G g hfp
  have hQ : LocallyQuasiFinite (restrictionReachMap G (sigmaOverDesc g)).left :=
    reach_sigmaOverDesc_locallyQuasiFinite G g hqf
  refine ⟨AlgebraicGeometry.restriction_source_mem G _ R @Flat hF,
    AlgebraicGeometry.restriction_source_mem G _ R @LocallyOfFinitePresentation hP,
    AlgebraicGeometry.restriction_source_mem G _ R @LocallyOfFiniteType inferInstance,
    AlgebraicGeometry.restriction_source_mem G _ R @LocallyQuasiFinite hQ,
    AlgebraicGeometry.restriction_target_mem G _ R @Flat hF,
    AlgebraicGeometry.restriction_target_mem G _ R @LocallyOfFinitePresentation hP,
    AlgebraicGeometry.restriction_target_mem G _ R @LocallyOfFiniteType inferInstance,
    AlgebraicGeometry.restriction_target_mem G _ R @LocallyQuasiFinite hQ⟩

end GroupoidScheme

end AlgebraicGeometry

end
