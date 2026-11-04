module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DenseSubsiteSheafVanishingTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DenseSubsiteCohomologyVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSections

/-!
# Acyclicity over the open subschemes is acyclicity of the restrictions

Let `S` be a scheme and `F` an abelian sheaf on the one-universe model
`Stacks.EtaleCohomology.MayerVietoris.Site S` of its small étale site. For an open subscheme `U`
of `S` the degree-`q` cohomology of `F` *over* `U`, read as an object of that site, is the
degree-`q` *global* cohomology of the restriction of `F` to the small étale site of `U` — the open
subscheme being a scheme in its own right, whose small étale site has a terminal object.

This is the statement
`Stacks.EtaleCohomology.ConstantTransport.subsingleton_H'_opensToSite` with the restriction to
*constant* sheaves removed: nothing in it is about the constant sheaf except the step identifying
the restriction of the constant sheaf with the constant sheaf, and for an arbitrary abelian sheaf
that step is not needed, the restriction being named in the statement instead.

## Why this is wanted

The Mayer--Vietoris descent
`Stacks.EtaleCohomology.MayerVietoris.subsingleton_H_of_affineOpens_acyclic` and its form on
Mathlib's site,
`Stacks.EtaleCohomology.MayerVietoris.subsingleton_H_smallEtale_of_affineOpens_acyclic`, ask for
acyclicity in positive degrees over every *affine open* of a quasi-compact quasi-separated scheme.
That hypothesis is about cohomology over an *object* of the small étale site, which is `Ext` out of
the free abelian sheaf on a representable; it is not global cohomology, so neither the lemma
`subsingleton_H_of_subsingleton_H_restriction_of_isDenseSubsite` of
`Stacks.Cohomology.DenseSubsiteSheaf` nor any other transport of `CategoryTheory.Sheaf.H` applies
to it directly. This file converts it into a statement about global cohomology — of the restriction
of the sheaf to the affine open — and global cohomology of an abelian sheaf on an affine scheme is
where the transports of `CategoryTheory.Sheaf.H`, and the affine case of [Stacks, Tag 09YQ], live.

## Main definitions

* `Stacks.EtaleCohomology.OpensAcyclicity.opensRestrict`: restriction of an abelian sheaf along
  the inclusion of the small étale site of an open subscheme, read on the one-universe models.
* `Stacks.EtaleCohomology.OpensAcyclicity.h'OpensToSiteIso`: **the cohomology of `F` over `U` is
  the global cohomology of the restriction of `F` to `U`**, in every degree.

## Main results

* `Stacks.EtaleCohomology.OpensAcyclicity.subsingleton_opensCohomology_iff`: the two groups vanish
  together.
* `Stacks.EtaleCohomology.OpensAcyclicity.subsingleton_H_of_affineOpens_restrict_acyclic`:
  `Stacks.EtaleCohomology.MayerVietoris.subsingleton_H_of_affineOpens_acyclic` with its acyclicity
  hypothesis read on the restrictions.
* `OpensAcyclicity.subsingleton_H_smallEtale_of_affineOpens_restrict_acyclic`: the same for
  `MayerVietoris.subsingleton_H_smallEtale_of_affineOpens_acyclic`, so **global étale cohomology
  vanishing on Mathlib's small étale site of a quasi-compact quasi-separated scheme follows from
  the vanishing of the global cohomology of the restrictions to the affine opens together with the
  degree-zero gluing condition.**

## Implementation notes

The comparison is [Stacks, Tag 03YU], statement 2, in the form
`Stacks.Cohomology.BiggerSite.cohomologyPresheafFunctorIso`, at the functor
`Stacks.EtaleCohomology.ConstantTransport.opensInclusion` of composition with the open immersion;
that functor's continuity, cocontinuity and preservation of fibre products and equalizers are
already instances. The terminal object of the small étale site of `U` is
`Stacks.EtaleCohomology.MayerVietoris.self`, and
`Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'` turns global cohomology
there into cohomology over it; `Stacks.EtaleCohomology.ConstantTransport.opensInclusionSelfIso`
identifies its image with `U` read as an object of the site of `S`.

The `Ext` universe of the *conclusion* of the two transported Mayer--Vietoris statements is
inherited from them: arbitrary in the statement on Mathlib's site, the model's own in the statement
on the model. The hypotheses are read in the model's own `Ext` universe, which is where the
Mayer--Vietoris sequence of [Stacks, Tag 0A50] lives.

## References

* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 0A50](https://stacks.math.columbia.edu/tag/0A50)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed (SectionsSub)
open Stacks.EtaleCohomology.StrictlyHenselian (opensCohomology)

universe w u

namespace Stacks.EtaleCohomology.OpensAcyclicity

variable (S : Scheme.{u}) (U : S.Opens)

/-- **Restriction of an abelian sheaf to the small étale site of an open subscheme**, read on the
one-universe models of the two sites. It is restriction along
`Stacks.EtaleCohomology.ConstantTransport.opensInclusion`, composition with the open immersion. -/
public abbrev opensRestrict :
    Sheaf (MayerVietoris.topology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (MayerVietoris.topology U.toScheme) AddCommGrpCat.{u + 1} :=
  (ConstantTransport.opensInclusion S U).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (MayerVietoris.topology U.toScheme) (MayerVietoris.topology S)

/-- **The cohomology of an abelian sheaf over an open subscheme is the global cohomology of its
restriction to that open subscheme**, in every degree. This is [Stacks, Tag 03YU], statement 2,
at composition with the open immersion, followed by the identification of the image of the
terminal object of the site of `U` with `U` read as an object of the site of `S`. -/
public def h'OpensToSiteIso (F : Sheaf (MayerVietoris.topology S) AddCommGrpCat.{u + 1})
    (q : ℕ) :
    Sheaf.H'.{u + 1} ((opensRestrict S U).obj F) q (MayerVietoris.self U.toScheme) ≅
      Sheaf.H'.{u + 1} F q ((MayerVietoris.opensToSite S).obj U) :=
  have : ∀ P : (MayerVietoris.Site U.toScheme)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (ConstantTransport.opensInclusion S U).op.HasPointwiseRightKanExtension P :=
    fun P => Stacks.Cohomology.BiggerSite.hasPointwiseRightKanExtension_op _ P
  (Stacks.Cohomology.BiggerSite.cohomologyPresheafFunctorIso
      (MayerVietoris.topology U.toScheme) (MayerVietoris.topology S)
      (ConstantTransport.opensInclusion S U) (MayerVietoris.self U.toScheme) q).app F ≪≫
    (F.cohomologyPresheaf q).mapIso (ConstantTransport.opensInclusionSelfIso S U).op.symm

/-- **Acyclicity over an open subscheme is acyclicity of the restriction to it.** -/
public theorem subsingleton_opensCohomology_iff
    (F : Sheaf (MayerVietoris.topology S) AddCommGrpCat.{u + 1}) (q : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} ((opensRestrict S U).obj F) q) ↔
      Subsingleton ((opensCohomology F q).obj (op U)) := by
  rw [Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'
    (MayerVietoris.topology U.toScheme) _ q _ (MayerVietoris.selfIsTerminal U.toScheme)]
  exact (h'OpensToSiteIso S U F q).addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr

/-- **Global étale cohomology vanishing from the acyclicity of the restrictions to the affine
opens**, on the one-universe model of the small étale site. This is
`Stacks.EtaleCohomology.MayerVietoris.subsingleton_H_of_affineOpens_acyclic` with the acyclicity
hypothesis read as the vanishing of the *global* cohomology of the restriction of `F` to each
affine open, which `Stacks.EtaleCohomology.OpensAcyclicity.subsingleton_opensCohomology_iff` says
is the same condition. -/
public theorem subsingleton_H_of_affineOpens_restrict_acyclic {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf (MayerVietoris.topology X) AddCommGrpCat.{u + 1})
    (haff : ∀ V : X.Opens, IsAffineOpen V → ∀ n, 0 < n →
      Subsingleton (Sheaf.H.{u + 1} ((opensRestrict X V).obj F) n))
    (hsub : ∀ U V : X.Opens, IsCompact (U : Set X) → IsAffineOpen V → SectionsSub F U V)
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1} F q) :=
  MayerVietoris.subsingleton_H_of_affineOpens_acyclic F
    (fun V hV n hn => (subsingleton_opensCohomology_iff X V F n).1 (haff V hV n hn)) hsub q hq

/-- **Global étale cohomology vanishing on Mathlib's small étale site from the acyclicity of the
restrictions to the affine opens.** Let `X` be a quasi-compact quasi-separated scheme and `F` an
abelian sheaf on `AlgebraicGeometry.Scheme.smallEtaleTopology`. If for every affine open `V` of
`X` the restriction of `F` to the small étale site of `V` has vanishing global cohomology in every
positive degree, and if for every quasi-compact open `U` and affine open `V` each degree-zero
section of `F` over `U ⊓ V` is a difference of sections over `U` and over `V`, then
`H^q(X, F) = 0` for every `q > 0`.

This is `Stacks.EtaleCohomology.MayerVietoris.subsingleton_H_smallEtale_of_affineOpens_acyclic`
with its first hypothesis in the global form. The `Ext` universe of the conclusion is arbitrary. -/
public theorem subsingleton_H_smallEtale_of_affineOpens_restrict_acyclic {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (haff : ∀ V : X.Opens, IsAffineOpen V → ∀ n, 0 < n →
      Subsingleton (Sheaf.H.{u + 1}
        ((opensRestrict X V).obj ((MayerVietoris.mayerVietorisRestrict X).obj F)) n))
    (hsub : ∀ U V : X.Opens, IsCompact (U : Set X) → IsAffineOpen V →
      SectionsSub ((MayerVietoris.mayerVietorisRestrict X).obj F) U V)
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{w} F q) :=
  MayerVietoris.subsingleton_H_smallEtale_of_affineOpens_acyclic F
    (fun V hV n hn => (subsingleton_opensCohomology_iff X V _ n).1 (haff V hV n hn)) hsub q hq

/-! ### The same on Mathlib's small étale site -/

section SmallEtale

/-- **Restriction of an abelian sheaf to the small étale site of an open subscheme**, on Mathlib's
small étale sites: restriction along composition with the open immersion. -/
public abbrev smallEtaleOpensRestrict :
    Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (AlgebraicGeometry.Scheme.Etale.smallEtaleCompose U.ι).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} U.toScheme.smallEtaleTopology S.smallEtaleTopology

/-- Reading a sheaf on Mathlib's small étale site of `S` on the one-universe model and then
restricting it to the open subscheme `U` is the same as restricting it to `U` on Mathlib's sites
and then reading the result on the one-universe model: both are restriction along
`AsSmall.down ⋙ Scheme.Etale.smallEtaleCompose U.ι`. -/
public theorem opensRestrict_mayerVietorisRestrict
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (opensRestrict S U).obj ((MayerVietoris.mayerVietorisRestrict S).obj F) =
      (MayerVietoris.mayerVietorisRestrict U.toScheme).obj
        ((smallEtaleOpensRestrict S U).obj F) :=
  rfl

/-- **Acyclicity over an open subscheme, on Mathlib's small étale site, is acyclicity of the
restriction to that open subscheme.** -/
public theorem subsingleton_opensCohomology_smallEtale_iff
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Subsingleton (Sheaf.H.{u + 1}
        ((MayerVietoris.mayerVietorisRestrict U.toScheme).obj
          ((smallEtaleOpensRestrict S U).obj F)) q) ↔
      Subsingleton
        ((opensCohomology ((MayerVietoris.mayerVietorisRestrict S).obj F) q).obj (op U)) := by
  rw [← opensRestrict_mayerVietorisRestrict S U F]
  exact subsingleton_opensCohomology_iff S U _ q

/-- **Acyclicity over an open subscheme from the vanishing of the global cohomology of the
restriction on Mathlib's own small étale site.** The restriction of `F` to the small étale site of
`U` is read on the one-universe model by
`Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict`, which is an equivalence of sheaf
categories, and the keystone
`Stacks.Cohomology.DenseSubsiteVanishing.subsingleton_H_restriction_of_isDenseSubsite` carries
the vanishing
across it. -/
public theorem subsingleton_opensCohomology_of_subsingleton_H_smallEtale
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{u + 1} ((smallEtaleOpensRestrict S U).obj F) q)) :
    Subsingleton
      ((opensCohomology ((MayerVietoris.mayerVietorisRestrict S).obj F) q).obj (op U)) :=
  (subsingleton_opensCohomology_smallEtale_iff S U F q).1
    (Stacks.Cohomology.DenseSubsiteVanishing.subsingleton_H_restriction_of_isDenseSubsite
      (MayerVietoris.topology U.toScheme) U.toScheme.smallEtaleTopology
      (AsSmall.down : MayerVietoris.Site U.toScheme ⥤ U.toScheme.Etale)
      (MayerVietoris.selfIsTerminal U.toScheme)
      (MayerVietoris.isTerminalAsSmallDownSelf U.toScheme)
      ((smallEtaleOpensRestrict S U).obj F) q h)

/-- **Global étale cohomology vanishing on Mathlib's small étale site from the acyclicity of the
restrictions to the affine opens, with the restrictions taken on Mathlib's sites too.** Let `X` be
a quasi-compact quasi-separated scheme and `F` an abelian sheaf on
`AlgebraicGeometry.Scheme.smallEtaleTopology`. If for every affine open `V` of `X` the restriction
of `F` to the small étale site of `V` — restriction along composition with the open immersion —
has vanishing global cohomology in every positive degree, and if for every quasi-compact open `U`
and affine open `V` each degree-zero section of `F` over `U ⊓ V` is a difference of sections over
`U` and over `V`, then `H^q(X, F) = 0` for every `q > 0`.

This is the form of
`Stacks.EtaleCohomology.MayerVietoris.subsingleton_H_smallEtale_of_affineOpens_acyclic` whose
acyclicity hypothesis never leaves `AlgebraicGeometry.Scheme.smallEtaleTopology`, and so is the
form a statement about a sheaf given on those sites — such as the colimit sheaf
`colim f_i^{-1}F_i` of [Stacks, Tag 09YQ] — can discharge. The `Ext` universe of the conclusion is
arbitrary. -/
public theorem subsingleton_H_smallEtale_of_affineOpens_smallEtale_acyclic {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (haff : ∀ V : X.Opens, IsAffineOpen V → ∀ n, 0 < n →
      Subsingleton (Sheaf.H.{u + 1} ((smallEtaleOpensRestrict X V).obj F) n))
    (hsub : ∀ U V : X.Opens, IsCompact (U : Set X) → IsAffineOpen V →
      SectionsSub ((MayerVietoris.mayerVietorisRestrict X).obj F) U V)
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{w} F q) :=
  MayerVietoris.subsingleton_H_smallEtale_of_affineOpens_acyclic F
    (fun V hV n hn => subsingleton_opensCohomology_of_subsingleton_H_smallEtale X V F n
      (haff V hV n hn)) hsub q hq

end SmallEtale

/-! ### The degree-zero gluing condition as a condition on sections -/

section Sections

variable {X : Scheme.{u}} (F : Sheaf (MayerVietoris.topology X) AddCommGrpCat.{u + 1})

/-- **The group of sections of an abelian sheaf over an open subscheme**, read as an object of the
small étale site. -/
public abbrev opensSections (U : X.Opens) : AddCommGrpCat.{u + 1} :=
  F.obj.obj (op ((MayerVietoris.opensToSite X).obj U))

/-- Restriction of sections along an inclusion of open subschemes. -/
public abbrev opensSectionsRestrict {U V : X.Opens} (h : U ≤ V) :
    opensSections F V ⟶ opensSections F U :=
  F.obj.map ((MayerVietoris.opensToSite X).map (homOfLE h)).op

/-- **The degree-zero gluing condition for two open subschemes, as a condition on sections**:
every section of `F` over `U ⊓ V` is the difference of the restrictions of a section over `U` and
a section over `V`.

This is `Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed.SectionsSub` with the degree-zero
cohomology groups replaced by the groups of sections they are, which is what
`Stacks.EtaleCohomology.OpensAcyclicity.sectionsSub_iff_sectionsDifference` says. -/
public def SectionsDifference (U V : X.Opens) : Prop :=
  ∀ τ : ToType (opensSections F (U ⊓ V)),
    ∃ (a : ToType (opensSections F U)) (b : ToType (opensSections F V)),
      opensSectionsRestrict F (inf_le_left : U ⊓ V ≤ U) a -
        opensSectionsRestrict F (inf_le_right : U ⊓ V ≤ V) b = τ

/-- **Degree-zero cohomology over the open subschemes is the presheaf of sections.** This is
`Stacks.Cohomology.FreeYoneda.cohomologyPresheafIsoSections` restricted along the inclusion of the
opens into the small étale site. -/
public def opensSectionsIso :
    opensCohomology F 0 ≅
      (MayerVietoris.opensToSite X).op ⋙
        (sheafToPresheaf (MayerVietoris.topology X) AddCommGrpCat.{u + 1}).obj F :=
  Functor.isoWhiskerLeft (MayerVietoris.opensToSite X).op
    (Stacks.Cohomology.FreeYoneda.cohomologyPresheafIsoSections F)

/-- The additive bijection between the degree-zero cohomology of `F` over `U` and the sections of
`F` over `U`. -/
public def opensSectionsAddEquiv (U : X.Opens) :
    ToType ((opensCohomology F 0).obj (op U)) ≃+ ToType (opensSections F U) :=
  ((opensSectionsIso F).app (op U)).addCommGroupIsoToAddEquiv

/-- The additive bijection of
`Stacks.EtaleCohomology.OpensAcyclicity.opensSectionsAddEquiv` commutes with restriction along an
inclusion of open subschemes. -/
public theorem opensSectionsAddEquiv_restrict {U V : X.Opens} (h : U ≤ V)
    (x : ToType ((opensCohomology F 0).obj (op V))) :
    opensSectionsAddEquiv F U ((opensCohomology F 0).map (homOfLE h).op x) =
      opensSectionsRestrict F h (opensSectionsAddEquiv F V x) :=
  (opensSectionsIso F).hom.naturality_apply (homOfLE h).op x

/-- **The degree-zero gluing condition is the condition on sections.** -/
public theorem sectionsSub_iff_sectionsDifference (U V : X.Opens) :
    SectionsSub F U V ↔ SectionsDifference F U V := by
  constructor
  · intro h τ
    obtain ⟨a, b, hab⟩ := h ((opensSectionsAddEquiv F (U ⊓ V)).symm τ)
    refine ⟨opensSectionsAddEquiv F U a, opensSectionsAddEquiv F V b, ?_⟩
    rw [← opensSectionsAddEquiv_restrict F (inf_le_left : U ⊓ V ≤ U) a,
      ← opensSectionsAddEquiv_restrict F (inf_le_right : U ⊓ V ≤ V) b,
      ← map_sub (opensSectionsAddEquiv F (U ⊓ V)), hab,
      AddEquiv.apply_symm_apply]
  · intro h τ
    obtain ⟨a, b, hab⟩ := h (opensSectionsAddEquiv F (U ⊓ V) τ)
    refine ⟨(opensSectionsAddEquiv F U).symm a, (opensSectionsAddEquiv F V).symm b, ?_⟩
    refine (opensSectionsAddEquiv F (U ⊓ V)).injective ?_
    rw [map_sub, opensSectionsAddEquiv_restrict F (inf_le_left : U ⊓ V ≤ U),
      opensSectionsAddEquiv_restrict F (inf_le_right : U ⊓ V ≤ V),
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hab]

/-- **The vanishing hypothesis of [Stacks, Tag 09YQ], reduced to two statements of pure geometry.**
Let `X` be a quasi-compact quasi-separated scheme and `F` an abelian sheaf on Mathlib's small étale
site of `X`. Then `H^q(X, F) = 0` for every `q > 0` as soon as

* for every affine open `V` of `X`, the restriction of `F` to the small étale site of `V` has
  vanishing global cohomology in every positive degree; and
* for every quasi-compact open `U` and affine open `V` of `X`, every section of `F` over `U ⊓ V`
  is the difference of a section over `U` and a section over `V`.

Neither hypothesis mentions cohomology over an object, `Ext` out of a free abelian sheaf, or the
one-universe model's `CategoryTheory.Sheaf.H'`: the first is global cohomology on Mathlib's small
étale site of an affine scheme, and the second is a statement about sections. The `Ext` universe of
the conclusion is arbitrary.

This is
`Stacks.EtaleCohomology.MayerVietoris.subsingleton_H_smallEtale_of_affineOpens_acyclic` with both
hypotheses restated, by `subsingleton_opensCohomology_of_subsingleton_H_smallEtale` and
`sectionsSub_iff_sectionsDifference`; nothing is added and nothing is dropped. -/
public theorem subsingleton_H_smallEtale_of_affineOpens_acyclic_of_sectionsDifference
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (haff : ∀ V : X.Opens, IsAffineOpen V → ∀ n, 0 < n →
      Subsingleton (Sheaf.H.{u + 1} ((smallEtaleOpensRestrict X V).obj F) n))
    (hsub : ∀ U V : X.Opens, IsCompact (U : Set X) → IsAffineOpen V →
      SectionsDifference ((MayerVietoris.mayerVietorisRestrict X).obj F) U V)
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{w} F q) :=
  subsingleton_H_smallEtale_of_affineOpens_smallEtale_acyclic F haff
    (fun U V hU hV => (sectionsSub_iff_sectionsDifference _ U V).2 (hsub U V hU hV)) q hq

end Sections

end Stacks.EtaleCohomology.OpensAcyclicity

end
