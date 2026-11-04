module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionFinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Properties.CharacterizingModulesFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealAffineChartFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismKernelIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite

/-!
# A closed immersion of algebraic spaces of finite presentation

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  The structure map of `i` has a kernel
`𝓘 = Ker(𝒪_X ⟶ i_*𝒪_Z) = AlgebraicGeometry.Space.kernelIdealSheaf B S hS i`, a sheaf of ideals
of `𝒪_X` on the small étale ringed site of `X`.  Being of finite presentation is for `i` the
same as finite type of `𝓘` as an `𝒪_X`-module.

Both sides are read on the *affine* étale scheme charts of `X`.  On the side of finite
presentation that is the every-étale-chart definition together with Stacks 03MJ: local finite
presentation is étale local on source and target, so it may be tested on the squares of charts
in which the chart of the source is the base change `Z ×_X C` of a chart `C` along `i`, and
there the morphism of schemes being tested is a closed immersion.  On the side of finite type
it is finiteness of the sections over the affine charts,
`AlgebraicGeometry.Space.isFiniteTypeOnSite_iff_forall_affine_moduleFinite`.  With both sides
on an affine chart the statement is the case of schemes, Stacks 01TV.

Passing from the affine charts back to all of `X` uses that local finite presentation is
Zariski local on the target together with Stacks 03G2, part (4) on schemes
(`AlgebraicGeometry.Space.exists_isPullback_snd_comp`): the cartesian projection over the chart
cut out by an affine open of a chart's scheme is the base change of the projection over that
chart along the inclusion of the affine open.

## Main results

* `AlgebraicGeometry.Space.isQuasiSeparated_of_isClosedImmersion`: a closed immersion of
  algebraic spaces is quasi-separated.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_forall_affine_chart`: local finite
  presentation of a closed immersion is read on the affine étale charts.
* `AlgebraicGeometry.Space.isFinitePresentation_iff_isFiniteTypeOnSite_kernelIdealSheaf`:
  **Stacks 084Q** — a closed immersion of algebraic spaces is of finite presentation exactly
  when its kernel ideal sheaf is of finite type.
* `AlgebraicGeometry.Space.fg_ideal_ker_rep_snd_of_isFinitePresentation`: the forward direction
  of Tag 084Q on an étale chart that need not be surjective.

## Implementation notes

The conclusion is stated for `AlgebraicGeometry.Space.IsFinitePresentation`, which is the
source's own reading, and not only for its first conjunct
`AlgebraicGeometry.Space.IsLocallyOfFinitePresentation`: the other two conjuncts hold for every
closed immersion.  Quasi-compactness is
`AlgebraicGeometry.Space.isQuasiCompact_of_isClosedImmersion'`, and quasi-separatedness follows
from `AlgebraicGeometry.Space.isQuasiSeparated_of_mono` once a closed immersion is known to be a
monomorphism, which it is because a closed immersion of schemes is one and
`AlgebraicGeometry.BigFppfOver.toScheme` is faithful.

Finite type of `𝓘` is finite type of the sheaf of modules it determines, that is
`SheafOfModules.IsFiniteTypeOnSite` applied to
`SheafOfModules.Submodule.toSheafOfModules`: a `SheafOfModules.Submodule` records a submodule of
the sections over every object of the site together with locality of membership, and
`toSheafOfModules` assembles those submodules into a sheaf of modules over the same sheaf of
rings.

Comparing finite type of `𝓘` on the small étale site of `X` with finite generation of the
ideals it cuts out on the charts is
`AlgebraicGeometry.Space.isFiniteTypeOnSite_kernelIdealSheaf_iff_forall_affine_fg_ker`, whose
two halves are the equivalence of finite type on the site with finiteness of the sections over
the affine charts and the identification, at a chart, of those sections with the kernel of
pullback of regular functions along the cartesian projection (Stacks 03G8, part (2)).

`AlgebraicGeometry.Space.isFinitePresentation_iff_isFiniteTypeOnSite_kernelIdealSheaf_of_chart`
below carries the same comparison as an explicit hypothesis `hchart`.  That hypothesis is now
unnecessary — the unconditional statement is the theorem above — and the declaration is
retained only because four modules of the `Quot` development consume it; those uses should be
migrated to the unconditional form.

## References

* [Stacks Project, Tag 084Q](https://stacks.math.columbia.edu/tag/084Q)
* [Stacks Project, Tag 01TV](https://stacks.math.columbia.edu/tag/01TV)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A closed immersion of algebraic spaces over `S` is quasi-separated.** It is a
monomorphism, so its relative diagonal is an isomorphism and in particular quasi-compact. -/
theorem isQuasiSeparated_of_isClosedImmersion {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : IsClosedImmersion B S hS f) : IsQuasiSeparated B S hS f :=
  isQuasiSeparated_of_mono B S hS f (mono_of_isClosedImmersion B S hS f hf)

variable {X Z : AlgebraicSpaces B S hS}

/-- **For a closed immersion, finite presentation is local finite presentation.** The two
remaining conjuncts of finite presentation, quasi-compactness and quasi-separatedness, hold for
every closed immersion of algebraic spaces: the first by
`AlgebraicGeometry.Space.isQuasiCompact_of_isClosedImmersion'`, the second because a closed
immersion is a monomorphism. -/
theorem isFinitePresentation_iff_isLocallyOfFinitePresentation (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    IsFinitePresentation B S hS i.hom ↔ IsLocallyOfFinitePresentation B S hS i.hom :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h, isQuasiCompact_of_isClosedImmersion' B S hS hi,
    isQuasiSeparated_of_isClosedImmersion B S hS hi⟩⟩

/-- Local finite presentation of a closed immersion follows from that of its base change along one
surjective étale chart. -/
private theorem isLocallyOfFinitePresentation_of_surjectiveEtaleChart (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) {V : BigFppfOver B S hS} {b : yoneda.obj V ⟶ X.1}
    (hbEtale : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hbSurj : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (h : _root_.AlgebraicGeometry.LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (hi.rep.snd b))) :
    IsLocallyOfFinitePresentation B S hS i.hom :=
  (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS
    (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
    _root_.AlgebraicGeometry.LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
    Z.2 X.2 i.hom).mpr
    ⟨_, V, hi.rep.fst b, b, hi.rep.snd b,
      (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
        (hi.rep.isPullback b).flip hbEtale, hbEtale,
      (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
        (hi.rep.isPullback b).flip hbSurj, ((hi.rep.isPullback b).w).symm, h⟩

/-- **On any étale scheme chart, the ideal cut out by the base change of a closed immersion of
finite presentation is finitely generated over every affine open.**  Surjectivity of the chart
is not needed: local finite presentation of a morphism of algebraic spaces is by definition the
chartwise condition of Stacks 03MJ, so it holds on the square of charts whose source chart is
the base change `Z ×_X V` of `V` along `i`, where the morphism being tested is the closed
immersion `Z ×_X V ⟶ V`; finite generation of its ideal over the affine opens is then the case
of schemes, `AlgebraicGeometry.locallyOfFinitePresentation_iff_fg_ker` (Stacks 01TV).

This is the forward direction of
`AlgebraicGeometry.Space.isFinitePresentation_iff_fg_ker_of_surjectiveEtaleChart` below, which
is Tag 084Q; surjectivity of the chart is what the *converse* needs, to get back from one chart
to the morphism of spaces.  No attribute is attached here: one direction of a tag is not the
tag. -/
theorem fg_ideal_ker_rep_snd_of_isFinitePresentation (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (h : IsFinitePresentation B S hS i.hom)
    {V : BigFppfOver B S hS} {b : yoneda.obj V ⟶ X.1}
    (hbEtale : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (A : ((BigFppfOver.toScheme B S hS).obj V).affineOpens) :
    (((BigFppfOver.toScheme B S hS).map (hi.rep.snd b)).ker.ideal A).FG := by
  have ha : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (hi.rep.fst b) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (hi.rep.isPullback b).flip hbEtale
  have hcomm : yoneda.map (hi.rep.snd b) ≫ b = hi.rep.fst b ≫ i.hom :=
    ((hi.rep.isPullback b).w).symm
  have hclosed : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hi.rep.snd b)) := hi.property_snd b
  exact (_root_.AlgebraicGeometry.locallyOfFinitePresentation_iff_fg_ker
    ((BigFppfOver.toScheme B S hS).map (hi.rep.snd b))).1
    (h.1 _ V (hi.rep.fst b) b (hi.rep.snd b) ha hbEtale hcomm) A

/-- **Stacks 084Q, with finite type of the ideal sheaf read on a surjective étale chart.** A
closed immersion `i : Z ⟶ X` of algebraic spaces over `S` is of finite presentation if and only
if, on one surjective étale scheme chart `U ⟶ X`, the ideal cut out by the base-changed closed
immersion `Z ×_X U ⟶ U` is finitely generated over every affine open of `U`.

The ideal appearing on the right is the chart-level reading of the quasi-coherent sheaf of
ideals `𝓘 = Ker(𝒪_X ⟶ i_*𝒪_Z)` of the source: by Stacks 03LX it is the restriction of `𝓘` to
`U`, and finite generation over the affine opens of `U` is finite type of that restriction.
The reading of finite type of `𝓘` itself, as a module on the small étale site of `X`, which is
the source's own condition, is
`AlgebraicGeometry.Space.isFinitePresentation_iff_isFiniteTypeOnSite_kernelIdealSheaf` below.

Local finite presentation is étale local on source and target (Stacks 03MJ), which is how the
chart is used; on the chart the statement is the case of schemes,
`AlgebraicGeometry.locallyOfFinitePresentation_iff_fg_ker` (Stacks 01TV). The remaining two
conjuncts of finite presentation hold for every closed immersion, by
`AlgebraicGeometry.Space.isFinitePresentation_iff_isLocallyOfFinitePresentation`. -/
@[ega "IV 1.4.5" "closed immersion case",
  ega "IV 8.6.1" "more general",
  sga "3 XI 6.4" "more general"]
theorem isFinitePresentation_iff_fg_ker_of_surjectiveEtaleChart (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) {V : BigFppfOver B S hS} {b : yoneda.obj V ⟶ X.1}
    (hbEtale : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hbSurj : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b) :
    IsFinitePresentation B S hS i.hom ↔
      ∀ A : ((BigFppfOver.toScheme B S hS).obj V).affineOpens,
        (((BigFppfOver.toScheme B S hS).map (hi.rep.snd b)).ker.ideal A).FG := by
  have hclosed : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hi.rep.snd b)) := hi.property_snd b
  refine ⟨fun h ↦ fg_ideal_ker_rep_snd_of_isFinitePresentation B S hS i hi h hbEtale, fun h ↦ ?_⟩
  rw [isFinitePresentation_iff_isLocallyOfFinitePresentation B S hS i hi]
  exact isLocallyOfFinitePresentation_of_surjectiveEtaleChart B S hS i hi hbEtale hbSurj
    ((_root_.AlgebraicGeometry.locallyOfFinitePresentation_iff_fg_ker _).2 h)

/-- **Local finite presentation of a closed immersion is read on the affine étale charts.**
If the cartesian projection `Z ×_X C ⟶ C` is locally of finite presentation for every étale
chart `C` of `X` whose scheme is affine, then `i` is locally of finite presentation.

The affine opens of the scheme of a surjective étale chart `b` cut out affine charts, and the
cartesian projection over such a chart is the base change of the projection over `b` along the
inclusion of that affine open — `AlgebraicGeometry.Space.exists_isPullback_snd_comp`, which is
Stacks 03G2 part (4) on schemes.  Local finite presentation is Zariski local on the target, so
it holds over `b`, and Stacks 03MJ then gives it on every chart. -/
theorem isLocallyOfFinitePresentation_of_forall_affine_chart (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    (hchartLFP : ∀ C : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj C) →
        _root_.AlgebraicGeometry.LocallyOfFinitePresentation
          ((BigFppfOver.toScheme B S hS).map (hi.rep.snd C.1.hom))) :
    IsLocallyOfFinitePresentation B S hS i.hom := by
  obtain ⟨V, b, hbSurj, hbEtale⟩ := X.2.exists_atlas
  have hbchart : IsEtaleChart B S hS X.1 (CostructuredArrow.mk b) := hbEtale
  have hzl : _root_.AlgebraicGeometry.IsZariskiLocalAtTarget
      (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u}) :=
    _root_.AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget
      (P := @_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u})
      (Q := RingHom.FinitePresentation)
  have : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hb : _root_.AlgebraicGeometry.LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (hi.rep.snd b)) := by
    refine _root_.AlgebraicGeometry.IsZariskiLocalAtTarget.of_iSup_eq_top
      (fun A : ((BigFppfOver.toScheme B S hS).obj V).affineOpens => A.1)
      (iSup_affineOpens_eq_top _) fun A => ?_
    obtain ⟨l, hsq⟩ := exists_isPullback_snd_comp B S hS hi.rep b (openSubHom V A.1) _ rfl
    rw [toScheme_map_openSubHom B S hS V A.1] at hsq
    have hLFP : _root_.AlgebraicGeometry.LocallyOfFinitePresentation
        ((BigFppfOver.toScheme B S hS).map
          (hi.rep.snd (yoneda.map (openSubHom V A.1) ≫ b))) :=
      hchartLFP (openChart B S hS X.1 ⟨CostructuredArrow.mk b, hbchart⟩ A.1) A.2
    rw [← hsq.isoIsPullback_hom_snd _ _
      (_root_.AlgebraicGeometry.isPullback_morphismRestrict
        ((BigFppfOver.toScheme B S hS).map (hi.rep.snd b)) A.1).flip] at hLFP
    exact (MorphismProperty.cancel_left_of_respectsIso
      (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u}) _ _).1 hLFP
  exact isLocallyOfFinitePresentation_of_surjectiveEtaleChart B S hS i hi hbEtale hbSurj hb

/-- **Stacks 084Q.** A closed immersion `i : Z ⟶ X` of algebraic spaces over `S` is of finite
presentation if and only if the associated quasi-coherent sheaf of ideals
`𝓘 = Ker(𝒪_X ⟶ i_*𝒪_Z)` is of finite type as an `𝒪_X`-module, that is, of finite type on the
small étale site of `X` in the sense of Stacks 03DL (5), which is how Properties of Spaces,
Section 66.30 reads the condition.

Both implications go through the affine étale charts of `X`.  On such a chart `C` the sections
of `𝓘` are the ideal cut out by the cartesian projection `Z ×_X C ⟶ C`
(`AlgebraicGeometry.Space.ker_structureSharp_app_eq_ker_appTop`, Stacks 03G8 part (2)), and
finite type of `𝓘` is finite generation of those ideals
(`AlgebraicGeometry.Space.isFiniteTypeOnSite_kernelIdealSheaf_iff_forall_affine_fg_ker`); on the
other side, finite generation of that ideal over an affine chart is local finite presentation of
the projection, by the case of schemes (Stacks 01TV) together with
`AlgebraicGeometry.Scheme.IdealSheafData.isFiniteType_of_fg_ideal_top`.  Local finite
presentation on all affine charts is local finite presentation of `i`, and the two remaining
conjuncts of finite presentation hold for every closed immersion. -/
@[stacks 084Q "finite type of the ideal sheaf on the small étale site of the target",
  ega "IV 1.4.5" "closed immersion case",
  ega "IV 8.6.1" "more general",
  sga "3 XI 6.4" "more general"]
theorem isFinitePresentation_iff_isFiniteTypeOnSite_kernelIdealSheaf (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    IsFinitePresentation B S hS i.hom ↔
      SheafOfModules.IsFiniteTypeOnSite (kernelIdealSheaf B S hS i).toSheafOfModules := by
  refine ⟨isFiniteTypeOnSite_kernelIdealSheaf_of_isFinitePresentation B S hS i hi, fun hft => ?_⟩
  refine (isFinitePresentation_iff_isLocallyOfFinitePresentation B S hS i hi).2 ?_
  refine isLocallyOfFinitePresentation_of_forall_affine_chart B S hS i hi fun C hCaff => ?_
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj C.1.left) := hCaff
  have hclosed : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hi.rep.snd C.1.hom)) := hi.property_snd C.1.hom
  refine (_root_.AlgebraicGeometry.locallyOfFinitePresentation_iff_fg_ker _).2 ?_
  refine _root_.AlgebraicGeometry.Scheme.IdealSheafData.isFiniteType_of_fg_ideal_top _ ?_
  rw [Scheme.Hom.ker_apply]
  exact (isFiniteTypeOnSite_kernelIdealSheaf_iff_forall_affine_fg_ker B S hS i
    (isQuasiCompact_of_isClosedImmersion' B S hS hi) hi.rep).1 hft C hCaff

/-- **Stacks 084Q, with finite type of the ideal sheaf itself**, granted the comparison
`hchart` of finite type of `𝓘 = Ker(𝒪_X ⟶ i_*𝒪_Z)` on the small étale site of `X` with finite
generation of the chart-level ideal over the affine opens of a surjective étale scheme chart.

This carries no attribute: a hypothesis is part of a citation, so a hypothesis-carrying form of
a tag must not claim the tag.  `hchart` is the source's appeal to Properties of Spaces,
Section 66.30 — that finite type of a module is étale local — in the form needed here, and it is
now *proved*: see
`AlgebraicGeometry.Space.isFiniteTypeOnSite_kernelIdealSheaf_iff_forall_affine_fg_ker`.  This
declaration is therefore redundant and is kept only for its existing consumers in the `Quot`
development.

The unconditional forms of the tag are
`AlgebraicGeometry.Space.isFinitePresentation_iff_isFiniteTypeOnSite_kernelIdealSheaf`, at the
source's own finite-type condition, and
`AlgebraicGeometry.Space.isFinitePresentation_iff_fg_ker_of_surjectiveEtaleChart`, at the
chart-level surrogate. -/
theorem isFinitePresentation_iff_isFiniteTypeOnSite_kernelIdealSheaf_of_chart (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    (hchart : ∀ (V : BigFppfOver B S hS) (b : yoneda.obj V ⟶ X.1),
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b →
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b →
      (SheafOfModules.IsFiniteTypeOnSite (kernelIdealSheaf B S hS i).toSheafOfModules ↔
        ∀ A : ((BigFppfOver.toScheme B S hS).obj V).affineOpens,
          (((BigFppfOver.toScheme B S hS).map (hi.rep.snd b)).ker.ideal A).FG)) :
    IsFinitePresentation B S hS i.hom ↔
      SheafOfModules.IsFiniteTypeOnSite (kernelIdealSheaf B S hS i).toSheafOfModules := by
  obtain ⟨V, b, hbSurj, hbEtale⟩ := X.2.exists_atlas
  rw [isFinitePresentation_iff_fg_ker_of_surjectiveEtaleChart B S hS i hi hbEtale hbSurj,
    hchart V b hbEtale hbSurj]

end AlgebraicGeometry.Space

end
