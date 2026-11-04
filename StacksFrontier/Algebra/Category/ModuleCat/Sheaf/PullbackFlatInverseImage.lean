module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FactorizationSheafSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatEquivalenceIff
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackJointEpi
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackFlatExtendScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingImageAdjunction
import StacksCore.Tactic.StacksAttribute

/-! # Stacks 05VD: the pullback of a flat sheaf of modules is flat

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and let `G` be a flat
sheaf of `O_D`-modules.  **Stacks 05VD** asserts that the pullback `f^*G` is a flat `O_C`-module.
The source's proof splits along the definition of the pullback (Stacks 03D6, part (2)),
`f^*G = O_C ⊗_{f⁻¹O_D} f⁻¹G`, into two steps: that extension of scalars preserves flatness
(Stacks 05V4), and that `f⁻¹G` is a flat `f⁻¹O_D`-module.  The first step is
`Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules_of_isFlat_inverseImageModules`; this
file proves the second and assembles the two.

## The argument, and why it is this one

The source proves flatness of `f⁻¹G` by computing `(f⁻¹G)(U)` as a filtered colimit, which needs
the comma category `(StructuredArrow U f.u)ᵒᵖ` to be filtered and hence needs the morphism of
topoi to come from a morphism of sites with finite limits — that is Stacks 03CR, and it is not
available here.  The route taken instead uses only three properties an inverse image has by
definition: left exactness, preservation of colimits, and preservation of epimorphisms.

The local equational criterion for flatness (Stacks 08FC, part (2)) is a *geometric* condition: a
relation among `n` sections lies, locally, in the image of a finite-free factorization of *some*
rank.  Expressed categorically it says that the morphism of sheaves of sets

`⨿_{l : ℕ} factorizationSheaf O G n l ⟶ relationSheaf O G n`

is an epimorphism.  The target is a **finite limit** of the ring and module operation morphisms,
so the inverse image carries it to the corresponding object for `f⁻¹O_D` and `f⁻¹G`
(`Stacks.Sheaves.ToposPullback.isIso_relationSheafComparison`); the source is a **coproduct of
finite limits**, which the inverse image carries over too; and epimorphy survives because the
inverse image is a left adjoint.  Reading the criterion back gives flatness of `f⁻¹G`.

## Main results

* `Stacks.Sheaves.RelationSheaf.epi_sigmaDesc_factorizationToRelation_of_isLocallySurjective`
  and `isLocallySurjective_relationOfFactorization_of_epi`: Stacks 08FC part (2) for a sheaf of
  modules on a ringed site *is* the epimorphy of the factorization-to-relation morphism out of
  the coproduct over the ranks.
* `Stacks.Sheaves.ToposPullback.isFlat_pullbackModuleObj_of_isFlat`: **the inverse image of a
  flat sheaf of modules is flat over the inverse-image sheaf of commutative rings.**
* `Stacks.Sheaves.RingedToposModules.isFlat_inverseImageModules_of_isFlat`: the same for a
  morphism of ringed topoi, in the shape the extension-of-scalars half consumes.
* `Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules`: **Stacks 05VD**, at five free
  universes, with the sheafification instances assumed.
* `Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules_maxSectionUniverse`: **Stacks 05VD
  with every sheafification instance derived**, for ringed topoi whose section universe is the
  `max` of their site's object and morphism universes.

## What this file does not contain

Stacks Tag 05VD has **two** clauses.  Only the *ringed topoi* one is proved here, and the tag
below is part-qualified accordingly.  The *ringed sites* clause is about
`AlgebraicGeometry.SheafOfModules.pullback` along the structure map of a morphism of ringed
sites, i.e. about Mathlib's pullback of sheaves of modules along a continuous functor, not about
the transported inverse image of Stacks 03D2 that this file is written for.  Identifying the two
is the comparison carried out for the geometric half of Stacks 0G6R by
`Stacks.Sheaves.InverseImageExactness.ringCompare`; with that
identification in hand the ringed-sites clause follows from the theorem below, but the
identification is not done here and no claim about that clause is made.

## Implementation notes

**Universes, and where the sheafification hypotheses come from.**  Tag 05VD states its two
ringed topoi with five independent universes and only `HasWeakSheafify _ AddCommGrpCat.{w}`.
`Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules` keeps all five free and carries
instead the `HasSheafCompose`, `HasWeakSheafify`, `WEqualsLocallyBijective` and `HasSheafify`
hypotheses of its `variable` block; neither its object nor its morphism nor its section universes
are constrained, on either side.

Those hypotheses are not needed when the section universe of each ringed topos is the `max` of
its own object and morphism universes, which is
`Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules_maxSectionUniverse`: at that shape
every one of them is an instance of the pinned Mathlib, the object and morphism universes stay
free and independent on both sides, and the statement of Stacks 05VD assumes nothing the source
does not.  That docstring says which Mathlib instance supplies each, and why
`HasWeakSheafify _ AddCommGrpCat.{w}` is the one that cannot be had at a free `w` — not even
under `UnivLE.{max u v, w}`.

The `max u v` shape is what the inputs want anyway:

* Stacks 08FC, on either site, is stated with the sections of the structure sheaf in `max v w`
  for the morphism universe `v` of that site — it comes down from the free presheaf on the index
  set `V ⟶ U` in `FlatEquivalence` — and
  `Stacks.SheafOfModules.isFlat_iff_isLocallySurjective_relationOfFactorization_freeUniverse`
  below is that criterion re-derived at a free section universe, which is what keeps the six
  parameters independent;
* the comparison of epimorphy with local surjectivity for sheaves of **sets**
  (`CategoryTheory.Sheaf.isLocallySurjective_iff_epi`) needs `HasSheafify _ (Type w)`, whose
  Mathlib instance for `Type`-valued sheaves is at `max u v` for a site with objects in `Type u`
  and morphisms in `Type v`.

**`HasColimitsOfShape (Discrete ℕ)` is restated rather than synthesized.**  Mathlib's instance
for `Sheaf J D` applies, but in this import closure the search for it exceeds the default
`synthInstance` budget.  `hasColimitsOfShape_discreteNat` is Mathlib's instance written out, which
costs nothing and avoids raising any elaboration budget; it is introduced locally with `haveI`
where a coproduct
over the ranks is needed, so no new global instance is registered.

**The commutativity hypothesis of `factorizationToRelation` is a proof, so the two spellings of it
that occur here are interchangeable.**  Upstairs the morphism is built with
`Stacks.Sheaves.ToposPullback.pullback_sections_mul_comm` and downstream with
`Stacks.Sheaves.ToposPullback.commRingSheaf_mul_comm`; they prove the same proposition, so the
morphisms are equal by proof irrelevance and `exact` crosses between them.

## References

* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4)
* [Stacks Project, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Sheaf
open AlgebraicGeometry

universe v u w v' u' w'

namespace Stacks.Sheaves.RelationSheaf

/-! ## Stacks 08FC part (2) as one epimorphism -/

section Criterion

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (O : Sheaf J CommRingCat.{w})
  (F : _root_.SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O)) (n : ℕ)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Mathlib's instance for colimits of sheaves, written out at the shape `Discrete ℕ`.  See the
implementation notes: the search for it exceeds the default `synthInstance` budget in this import
closure, and writing it out avoids raising that budget. -/
lemma hasColimitsOfShape_discreteNat [HasSheafify J (Type w)] :
    HasColimitsOfShape (Discrete ℕ) (Sheaf J (Type w)) :=
  ⟨fun G => Limits.HasColimit.mk
    ⟨Sheaf.sheafifyCocone (Limits.colimit.cocone (G ⋙ sheafToPresheaf J (Type w))),
      Sheaf.isColimitSheafifyCocone _ (Limits.colimit.isColimit _)⟩⟩

/-- The identification of the sections of the sheaf of `n`-term relations with the `n`-term
relations is natural in the object. -/
lemma relationSheafSectionsEquiv_naturality {X Y : Cᵒᵖ} (g : X ⟶ Y)
    (y : (relationSheaf (Stacks.commRingSheafToRingSheaf O) F n).obj.obj X) :
    relationSheafSectionsEquiv O F n Y
        ((relationSheaf (Stacks.commRingSheafToRingSheaf O) F n).obj.map g y) =
      Stacks.SheafOfModules.relationRestrict O F g
        (relationSheafSectionsEquiv O F n X y) := by
  have h := ConcreteCategory.congr_hom ((relationSheafIso O F n).hom.naturality g) y
  rw [types_comp_apply, types_comp_apply] at h
  exact h

variable [HasSheafify J (Type w)]
  [HasCoproduct (fun l : ℕ =>
    factorizationSheaf (Stacks.commRingSheafToRingSheaf O) F n l)]

/-- **Stacks 08FC part (2) implies the epimorphy of the factorization-to-relation morphism.**
If every relation among `n` sections of `F` locally factors through a finite free module, then the
morphism out of the coproduct over the ranks is an epimorphism. -/
theorem epi_sigmaDesc_factorizationToRelation_of_isLocallySurjective
    (h : Presheaf.IsLocallySurjective J
      (Stacks.SheafOfModules.relationOfFactorization O F n)) :
    Epi (Limits.Sigma.desc (fun l : ℕ =>
      factorizationToRelation (Stacks.commRingSheafToRingSheaf O) F n l
        (Stacks.Sheaves.ToposPullback.commRingSheaf_mul_comm O))) := by
  refine Stacks.Sheaves.TypeSheaf.epi_sigmaDesc_of_forall_exists_covering _ _ (fun U q => ?_)
  refine ⟨Presheaf.imageSieve (Stacks.SheafOfModules.relationOfFactorization O F n)
    (relationSheafSectionsEquiv O F n (op U) q), h.imageSieve_mem _, ?_⟩
  intro V g hg
  obtain ⟨x, hx⟩ := hg
  obtain ⟨y, hy⟩ := exists_sections_of_factorizationData O F n x.1 (op V)
    (Stacks.Sheaves.ToposPullback.commRingSheaf_mul_comm O) x.2
  refine ⟨x.1, y, ?_⟩
  refine (relationSheafSectionsEquiv O F n (op V)).injective ?_
  refine hy.trans (Eq.trans ?_ (relationSheafSectionsEquiv_naturality O F n g.op q).symm)
  exact hx

/-- **The epimorphy of the factorization-to-relation morphism implies Stacks 08FC part (2).** -/
theorem isLocallySurjective_relationOfFactorization_of_epi
    (h : Epi (Limits.Sigma.desc (fun l : ℕ =>
      factorizationToRelation (Stacks.commRingSheafToRingSheaf O) F n l
        (Stacks.Sheaves.ToposPullback.commRingSheaf_mul_comm O)))) :
    Presheaf.IsLocallySurjective J
      (Stacks.SheafOfModules.relationOfFactorization O F n) := by
  have := h
  refine ⟨fun {U} p => ?_⟩
  obtain ⟨S, hS, hfac⟩ := Stacks.Sheaves.TypeSheaf.exists_covering_of_epi_sigmaDesc
    (fun l : ℕ => factorizationSheaf (Stacks.commRingSheafToRingSheaf O) F n l)
    (fun l : ℕ => factorizationToRelation (Stacks.commRingSheafToRingSheaf O) F n l
      (Stacks.Sheaves.ToposPullback.commRingSheaf_mul_comm O))
    U ((relationSheafSectionsEquiv O F n (op U)).symm p)
  refine J.superset_covering ?_ hS
  intro V g hg
  obtain ⟨l, a, ha⟩ := hfac g hg
  refine ⟨⟨l, factorizationSheafSectionsEquiv O F n l (op V) a⟩, ?_⟩
  refine (relationSheafSectionsEquiv_factorizationToRelation O F n l (op V)
    (Stacks.Sheaves.ToposPullback.commRingSheaf_mul_comm O) a).symm.trans ?_
  refine Eq.trans (congrArg (relationSheafSectionsEquiv O F n (op V)) ha) ?_
  refine (relationSheafSectionsEquiv_naturality O F n g.op
    ((relationSheafSectionsEquiv O F n (op U)).symm p)).trans ?_
  exact congrArg (Stacks.SheafOfModules.relationRestrict O F g.op)
    ((relationSheafSectionsEquiv O F n (op U)).apply_symm_apply p)

end Criterion

end Stacks.Sheaves.RelationSheaf

namespace Stacks.SheafOfModules

/-- **Flatness as the local surjectivity of a map of presheaves of sets, at an independent
section universe.**  This is
`Stacks.SheafOfModules.isFlat_iff_isLocallySurjective_relationOfFactorization` with the
sections of the structure sheaf in a universe unrelated to the two universes of the site: the
`max v w` of that statement comes from the `max v w` pairing of the two halves of Stacks 08FC
in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCriterionConverse`, and
`Stacks.SheafOfModules.isFlat_iff_hasLocalSingleRelationFactorizations_freeUniverse` is that
pairing at free universes.  The re-expression of the criterion as local surjectivity
(`hasLocalSingleRelationFactorizations_iff_isLocallySurjective`) never narrowed the universes
at all. -/
theorem isFlat_iff_isLocallySurjective_relationOfFactorization_freeUniverse
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
    (O : Sheaf J CommRingCat.{w})
    (F : _root_.SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O)) :
    IsFlat F ↔
      ∀ n : ℕ, Presheaf.IsLocallySurjective J (relationOfFactorization O F n) :=
  (isFlat_iff_hasLocalSingleRelationFactorizations_freeUniverse O F).trans
    (hasLocalSingleRelationFactorizations_iff_isLocallySurjective O F)

end Stacks.SheafOfModules

/-! ## Flatness of the inverse image -/

namespace Stacks.Sheaves.ToposPullback

open Stacks.Sheaves.RelationSheaf
open Stacks.SheafOfModules (isFlat_iff_isLocallySurjective_relationOfFactorization_freeUniverse)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [J.HasSheafCompose (forget RingCat.{w})]
  [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify K AddCommGrpCat.{w'}]
  [HasSheafify J (Type w)] [HasSheafify K (Type w')]
  (Φ : Sheaf K (Type w') ⥤ Sheaf J (Type w))
  [PreservesFiniteLimits Φ] [Φ.PreservesEpimorphisms]
  (O : Sheaf K CommRingCat.{w'})
  (G : _root_.SheafOfModules.{w'} (Stacks.commRingSheafToRingSheaf O))

/-- **The inverse image of a flat sheaf of modules is flat.**  For a left exact,
coproduct-preserving functor `Φ` between categories of sheaves of sets which preserves
epimorphisms — in particular for the inverse image of a morphism of topoi — a flat sheaf of
`O`-modules has flat inverse image over the inverse-image sheaf of commutative rings.

This is the half of Stacks 05VD that the source gets from Stacks 03CR; here it is the geometric
character of the local equational criterion of Stacks 08FC part (2). -/
@[sga "4 V 1.7.1" "A' = u⁻¹A", sga "4 VI 8.6.4" "special case"]
theorem isFlat_pullbackModuleObj_of_isFlat
    [∀ n : ℕ, Limits.PreservesColimit (Discrete.functor (fun l : ℕ =>
      factorizationSheaf (Stacks.commRingSheafToRingSheaf O) G n l)) Φ]
    (hG : Stacks.SheafOfModules.IsFlat G) :
    Stacks.SheafOfModules.IsFlat (O := pullbackCommRingSheaf J Φ O)
      (pullbackModuleObj J Φ (Stacks.commRingSheafToRingSheaf O) G) := by
  have := hasColimitsOfShape_discreteNat (J := J)
  have := hasColimitsOfShape_discreteNat (J := K)
  refine (isFlat_iff_isLocallySurjective_relationOfFactorization_freeUniverse
    (pullbackCommRingSheaf J Φ O)
    (pullbackModuleObj J Φ (Stacks.commRingSheafToRingSheaf O) G)).2 (fun n => ?_)
  have hdown : Presheaf.IsLocallySurjective K
      (Stacks.SheafOfModules.relationOfFactorization O G n) :=
    (isFlat_iff_isLocallySurjective_relationOfFactorization_freeUniverse O G).1 hG n
  have hepi := epi_sigmaDesc_factorizationToRelation_of_isLocallySurjective O G n hdown
  refine isLocallySurjective_relationOfFactorization_of_epi
    (pullbackCommRingSheaf J Φ O)
    (pullbackModuleObj J Φ (Stacks.commRingSheafToRingSheaf O) G) n ?_
  exact epi_sigmaDesc_factorizationToRelation_map J Φ (Stacks.commRingSheafToRingSheaf O) G n
    (commRingSheaf_mul_comm O) hepi

end Stacks.Sheaves.ToposPullback

/-! ## Stacks 05VD for a morphism of ringed topoi -/

namespace Stacks.Sheaves.RingedToposModules

open Stacks.Sheaves.ToposPullback Stacks.Sheaves.RelationSheaf

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')]
  (f : RingedToposHom X Y)
  (G : _root_.SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- **The inverse image of a flat sheaf of modules along a morphism of ringed topoi is flat over
the inverse image of the structure sheaf.**  This is the half of Stacks 05VD that the source
deduces from Stacks 03CR. -/
@[sga "4 V 1.7.1" "Case A′ = u⁻¹A"]
theorem isFlat_inverseImageModules_of_isFlat
    (hG : Stacks.SheafOfModules.IsFlat (O := Y.O) G) :
    Stacks.SheafOfModules.IsFlat (O := inverseImageStructureCommRingSheaf f)
      ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G) := by
  have : f.toToposHom.inverseImage.IsLeftAdjoint := ⟨_, ⟨f.toToposHom.adj⟩⟩
  have : PreservesFiniteLimits f.toToposHom.inverseImage := f.toToposHom.preservesFiniteLimits
  have : f.toToposHom.inverseImage.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_isLeftAdjoint _
  exact isFlat_pullbackModuleObj_of_isFlat f.toToposHom.inverseImage Y.O G hG

/-- **Stacks Project, Tag 05VD.**  The pullback of a flat sheaf of modules along a morphism of
ringed topoi is flat.

All five universe parameters of the tagged statement are free here; what the tag does not state
are the sheafification hypotheses in the `variable` block above — `HasSheafCompose` for the three
forgetful functors, `HasWeakSheafify` and `WEqualsLocallyBijective` for `AddCommGrpCat`, and
`HasSheafify` for `Type` — on each of the two sites.  They arise because `Stacks.ringSheaf` and
`Stacks.SheafOfModules.IsFlat` take them as instance binders where a `ringSheaf` construction
could build them internally, so they are a formulation difference rather than added mathematical
strength; but they are *not* nothing, and a consumer whose binder context lacks them cannot apply
this theorem without supplying them.

They need not be supplied when each ringed topos has its section universe equal to the `max` of
its site's object and morphism universes, which is what
`Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules_maxSectionUniverse` below records: at
that shape every one of them is an instance of the pinned Mathlib, so that statement of Stacks
05VD assumes nothing beyond the source's own hypotheses.  Both object universes and both morphism
universes stay free there; it is only the two section universes that are determined. -/
@[stacks 05VD "ringed topoi, at free universes, assuming on each site the HasSheafCompose, \
HasWeakSheafify, WEqualsLocallyBijective and HasSheafify instances of the variable block; \
isFlat_pullbackModules_maxSectionUniverse is the same statement with all of them derived",
  sga "4 V 8.2.9",
  sga "4 V 1.7.1"]
theorem isFlat_pullbackModules (hG : Stacks.SheafOfModules.IsFlat (O := Y.O) G) :
    Stacks.SheafOfModules.IsFlat (O := X.O) ((f.pullbackModules).obj G) :=
  isFlat_pullbackModules_of_isFlat_inverseImageModules f G
    (isFlat_inverseImageModules_of_isFlat f G hG)

end Stacks.Sheaves.RingedToposModules

/-! ## Stacks 05VD with the sheafification hypotheses discharged -/

namespace Stacks.Sheaves.RingedToposModules

section Derived

variable {X : RingedTopos.{v, u, max u v}} {Y : RingedTopos.{v', u', max u' v'}}
  (f : RingedToposHom X Y)
  (G : _root_.SheafOfModules.{max u' v'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- **Stacks Project, Tag 05VD, assuming nothing the source does not assume.**  The pullback of a
flat sheaf of modules along a morphism of ringed topoi is flat.

This is `Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules` with every one of its
sheafification hypotheses discharged by instance search instead of assumed.  That is possible
exactly when each ringed topos has its section universe equal to the `max u v` of its site's
object and morphism universes, which is the shape above; the two object universes and the two
morphism universes remain free and independent.

Where each hypothesis comes from, and which of them need the section universe at all:

* the three `HasSheafCompose` hypotheses hold at **every** universe and for every site, so they
  were never where the narrowing lived: `forget AddCommGrpCat` by
  `CategoryTheory.hasSheafCompose_of_preservesMulticospan`, and `forget RingCat` and
  `forget₂ CommRingCat RingCat` by `CategoryTheory.hasSheafComposeEssentiallySmallSite`;
* `HasSheafify J (Type (max u v))` is `CategoryTheory.instHasSheafifyType`, and it too is less
  rigid than it looks: `HasSheafify J (Type w)` holds for a free `w` under
  `UnivLE.{max u v, w}`, by
  `CategoryTheory.instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover`;
* `HasWeakSheafify J AddCommGrpCat.{max u v}` is `CategoryTheory.instHasWeakSheafifyOfHasSheafify`
  applied to that same plus-construction instance at `AddCommGrpCat`;
* `J.WEqualsLocallyBijective AddCommGrpCat.{max u v}` follows from the previous one by the
  concrete-category instance of `Mathlib/CategoryTheory/Sites/LocallyBijective.lean`, built on
  `CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.mk'`.

**Why the section universe cannot be left free.**  Exactly one of the five resists:
`HasWeakSheafify J AddCommGrpCat.{w}` for a free `w`, which fails even under
`UnivLE.{max u v, w}`.  The plus construction needs `PreservesColimitsOfShape (J.Cover X)ᵒᵖ
(forget AddCommGrpCat.{w})`, and the only instance supplying it is
`AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits`, which is
`PreservesFilteredColimits (forget AddCommGrpCat.{w})` — filtered shapes in the *same* universe
`w` as the groups, while the cover categories live in `max u v`.  The two agree precisely at
`w = max u v`.  Since `Stacks.SheafOfModules.IsFlat` takes `HasWeakSheafify` as an instance
binder, this blocks the statement and not merely the proof.  For a `w` strictly below `max u v`
there is nothing to lift at all: sheafification of `AddCommGrpCat.{w}`-valued presheaves on a
site whose covers are `max u v`-large does not exist in general.  So
`isFlat_pullbackModules` above, with the hypotheses carried and all five universes free, and this
statement, with the section universes determined and no hypotheses, are each the strongest
available in their own direction, and neither subsumes the other. -/
@[stacks 05VD "ringed topoi whose section universe is the max of their site's object and \
morphism universes -- object and morphism universes free and independent -- with no \
sheafification hypothesis assumed: HasSheafCompose, HasWeakSheafify, WEqualsLocallyBijective \
and HasSheafify are all derived",
  sga "4 V 8.2.9",
  sga "4 V 1.7.1", sga "4 VI 8.6.4" "special case"]
theorem isFlat_pullbackModules_maxSectionUniverse
    (hG : Stacks.SheafOfModules.IsFlat (J := Y.J) (O := Y.O) G) :
    Stacks.SheafOfModules.IsFlat (J := X.J) (O := X.O) ((f.pullbackModules).obj G) :=
  isFlat_pullbackModules f G hG

end Derived

end Stacks.Sheaves.RingedToposModules

end
