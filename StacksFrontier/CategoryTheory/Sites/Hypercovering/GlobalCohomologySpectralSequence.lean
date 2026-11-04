module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.PresheafSpectralSequence

/-!
# The spectral sequence of a hypercovering, converging to global cohomology

Let `C` be a site with equalizers and fibre products and let `K` be a hypercovering, that is a
hypercovering of the final presheaf ([Stacks, Tag 09VU]).  [Stacks, Tag 09VY] asserts that for a
sheaf of abelian groups `F` on `C` there is a spectral sequence `(E_r, d_r)_{r ≥ 0}` with second
page

```
E_2^{p,q} = Ȟ^p(K, H̲^q(F))
```

converging to the global cohomology groups `H^{p+q}(F)`.
`HypercoveringGlobalSpectralSequenceData` bundles that assertion and
`hypercoveringGlobalSpectralSequence` supplies it.

The statement is the special case `G = *` of [Stacks, Tag 09VX], the spectral sequence of a
hypercovering of a presheaf `G`, whose second page is the same and whose abutment is cohomology
over `G`.  What has to be supplied is the identification of that abutment with global cohomology:
the free abelian sheaf on the final presheaf is the constant sheaf `**Z**`, so sections over the
final presheaf are global sections and their right derived functors are the `Ext`-groups out of
`**Z**` that global cohomology is.

## The identification of the abutment

Sections over a presheaf `G` are `Hom(**Z**_G^♯, -)`, so they are corepresented by the free
abelian sheaf `**Z**_G^♯` on the nose, and `Ext` out of a corepresenting object computes the
right derived functors of a left exact additive functor
(`ModuleSheafCohomology.extFunctorObjIsoRightDerived`).  For `G` the final presheaf the
corepresenting object is identified with `**Z**` by `freeAbelianSheafTerminalIso`: the final
presheaf is sectionwise a one-point set, hence sectionwise universe-lifted it is the constant
presheaf on `ULift PUnit`, the free abelian group on a one-point set is `ℤ`, and the free abelian
presheaf functor and sheafification both carry constant presheaves to constant ones, which is
what `constantSheaf` is.

Global cohomology is Mathlib's `CategoryTheory.Sheaf.H`, the `Ext`-groups out of the constant
sheaf with value `ULift ℤ`; `globalCohomologyFunctor` is the same groups assembled into a
functor of the sheaf, and `globalCohomologyFunctor_obj` records that the two agree.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.globalCohomologyFunctor`: global sheaf cohomology
  `H^n(-)` as a functor of the abelian sheaf.
* `Stacks.CategoryTheory.Hypercovering.HypercoveringGlobalSpectralSequenceData`: the data
  [Stacks, Tag 09VY] asserts.
* `Stacks.CategoryTheory.Hypercovering.hypercoveringGlobalSpectralSequence`: that data, for a
  hypercovering of the final presheaf.

## Main results

* `Stacks.CategoryTheory.Hypercovering.globalCohomologyFunctor_obj`: the value of
  `globalCohomologyFunctor` is Mathlib's `CategoryTheory.Sheaf.H`.
* `Stacks.CategoryTheory.Hypercovering.freeAbelianSheafTerminalIso`: the free abelian sheaf on
  the final presheaf is the constant sheaf `**Z**`.
* `Stacks.CategoryTheory.Hypercovering.globalCohomologyAbutmentIso`: the abutment of the spectral
  sequence of a hypercovering of the final presheaf is global cohomology, naturally in the sheaf.

## Implementation notes

Sheafification and existence of enough injectives at `AddCommGrpCat.{max (max u v) (max v w)}`,
and `HasExt` in the same universe, are taken as hypotheses, as they are by the other carriers of
this chapter's presheaf-side tags.  The first two are theorems for every site whose objects lie
in `Type u` and whose morphisms in `Type v`
(`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` and
`CategoryTheory.Sheaf.enoughInjectives_addCommGrpCat`), but they cannot be supplied as local
instances here: the coefficient universe has `w` occurring only inside a `max`, so instance
search cannot recover it and reports the universe constraint as stuck.

The abutment identification is assembled from
`ModuleSheafCohomology.extFunctorObjIsoRightDerived`, whose two degree ranges are built by
different constructions with no compatibility between them claimed.  Consequently no
compatibility of `globalCohomologyAbutmentIso` with the canonical comparison
`Ȟ^i(K, -) ⟶ H^i(-)` of [Stacks, Tag 09VX] is asserted.

## References

* [Stacks Project, Tag 09VY](https://stacks.math.columbia.edu/tag/09VY)
* [Stacks Project, Tag 09VX](https://stacks.math.columbia.edu/tag/09VX)
* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
* [Stacks Project, Tag 01ER](https://stacks.math.columbia.edu/tag/01ER)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.Leray

universe w v u

namespace Stacks.CategoryTheory.Hypercovering

/-! ### Global cohomology as a functor -/

section GlobalCohomology

variable {C : Type u} [Category.{v} C] [HasPullbacks C] (J : Pretopology C)
  [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)}]
  [HasExt.{max (max u v) (max v w)}
    (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})]

/-- **Global cohomology `H^n(-)` of a sheaf of abelian groups on a site, as a functor of the
sheaf**: the `n`-th `Ext`-functor out of the constant sheaf with value `ℤ`. -/
abbrev globalCohomologyFunctor (n : ℕ) :
    Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)} ⥤
      AddCommGrpCat.{max (max u v) (max v w)} :=
  Abelian.extFunctorObj
    ((constantSheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)}).obj
      (AddCommGrpCat.of (ULift.{max (max u v) (max v w), 0} ℤ))) n

/-- The value of `globalCohomologyFunctor` at a sheaf is its global cohomology. -/
lemma globalCohomologyFunctor_obj
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)}) (n : ℕ) :
    (globalCohomologyFunctor.{w} J n).obj F =
      AddCommGrpCat.of (Sheaf.H.{max (max u v) (max v w)} F n) :=
  rfl

end GlobalCohomology

/-! ### The free abelian sheaf on the final presheaf -/

section FreeAbelianSheafOfTerminal

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]
variable (J : Pretopology C)
  [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)}]

/-- **The free abelian sheaf on the final presheaf is the constant sheaf `**Z**`.**  The final
presheaf is sectionwise a one-point set and the free abelian group on a one-point set is `ℤ`;
taking free abelian presheaves and sheafifying both carry constant presheaves to constant ones. -/
def freeAbelianSheafTerminalIso (K : HypercoveringOfTerminal.{w} J) :
    (Presheaf.freeAbelianSheaf J.toGrothendieck).obj
        ((K.toAugmentedULift J (⊤_ (Cᵒᵖ ⥤ Type v))).right) ≅
      (constantSheaf J.toGrothendieck
          AddCommGrpCat.{max (max u v) (max v w)}).obj
        (AddCommGrpCat.of (ULift.{max (max u v) (max v w), 0} ℤ)) := by
  let eTerminal : (⊤_ (Cᵒᵖ ⥤ Type v)) ⋙ uliftFunctor.{max (max u v) (max v w), v} ≅
      (Functor.const Cᵒᵖ).obj (ULift.{max (max u v) (max v w), v} PUnit.{v + 1}) :=
    Functor.isoWhiskerRight
        ((terminalIsTerminal (C := Cᵒᵖ ⥤ Type v)).uniqueUpToIso
          (Functor.isTerminalConst Cᵒᵖ Types.isTerminalPUnit))
        uliftFunctor.{max (max u v) (max v w), v} ≪≫
      Functor.constComp Cᵒᵖ (PUnit.{v + 1} : Type v)
        uliftFunctor.{max (max u v) (max v w), v}
  let eFree : AddCommGrpCat.free.{max (max u v) (max v w)}.obj
        (ULift.{max (max u v) (max v w), v} PUnit.{v + 1}) ≅
      AddCommGrpCat.of (ULift.{max (max u v) (max v w), 0} ℤ) :=
    ((FreeAbelianGroup.uniqueEquiv
        (ULift.{max (max u v) (max v w), v} PUnit.{v + 1})).trans
      { toFun := ULift.up
        invFun := ULift.down
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl }).toAddCommGrpIso
  refine (Presheaf.freeAbelianSheaf J.toGrothendieck).mapIso
      (liftedPresheafULiftIso.{v, w, v, u} (C := C) (⊤_ (Cᵒᵖ ⥤ Type v)) ≪≫
        eTerminal) ≪≫ ?_
  refine (presheafToSheaf J.toGrothendieck
      AddCommGrpCat.{max (max u v) (max v w)}).mapIso
    (Functor.constComp Cᵒᵖ (ULift.{max (max u v) (max v w), v} PUnit.{v + 1})
      AddCommGrpCat.free) ≪≫ ?_
  exact (constantSheaf J.toGrothendieck
    AddCommGrpCat.{max (max u v) (max v w)}).mapIso eFree

end FreeAbelianSheafOfTerminal

/-! ### The abutment is global cohomology -/

section Abutment

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]
variable (J : Pretopology C) (K : HypercoveringOfTerminal.{w} J)
  [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)}]
  [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})]
  [HasExt.{max (max u v) (max v w)}
    (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})]

/-- **The abutment of the spectral sequence of a hypercovering of the final presheaf is global
cohomology**, naturally in the sheaf: sections over the final presheaf are corepresented by the
constant sheaf `**Z**`, and `Ext` out of a corepresenting object computes right derived
functors. -/
def globalCohomologyAbutmentIso (n : ℕ) :
    (presheafSectionsFunctor J (⊤_ (Cᵒᵖ ⥤ Type v)) K).rightDerived n ≅
      globalCohomologyFunctor.{w} J n := by
  letI : PreservesFiniteLimits (presheafSectionsFunctor J (⊤_ (Cᵒᵖ ⥤ Type v)) K) :=
    inferInstanceAs (PreservesFiniteLimits (preadditiveCoyoneda.obj
      (op ((Presheaf.freeAbelianSheaf J.toGrothendieck).obj
        ((K.toAugmentedULift J (⊤_ (Cᵒᵖ ⥤ Type v))).right)))))
  refine (ModuleSheafCohomology.extFunctorObjIsoRightDerived
    (presheafSectionsFunctor J (⊤_ (Cᵒᵖ ⥤ Type v)) K)
    ((Presheaf.freeAbelianSheaf J.toGrothendieck).obj
      ((K.toAugmentedULift J (⊤_ (Cᵒᵖ ⥤ Type v))).right))
    (Iso.refl _) n).symm ≪≫ ?_
  exact (Abelian.extFunctor n).mapIso (freeAbelianSheafTerminalIso J K).symm.op

end Abutment

/-! ### The assembled statement -/

section Assembled

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]
variable (J : Pretopology C) (K : HypercoveringOfTerminal.{w} J)
  [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)}]
  [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})]
  [HasExt.{max (max u v) (max v w)}
    (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})]

/-- **The spectral sequence of a hypercovering**, which is [Stacks, Tag 09VY]: a first-quadrant
`E₂` cohomological spectral sequence, functorial in the coefficient sheaf, whose second page is
`Ȟ^p(K, H̲^q(F))` and which converges to the global cohomology groups `H^{p+q}(F)`.

The cohomology presheaf `H̲^q` is the `q`-th right derived functor of the inclusion of abelian
sheaves into presheaves ([Stacks, Tag 01ER]) and global cohomology is `globalCohomologyFunctor`,
that is Mathlib's `CategoryTheory.Sheaf.H`. -/
structure HypercoveringGlobalSpectralSequenceData where
  /-- The spectral sequence is functorial in the coefficient sheaf. -/
  sequence : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)} ⥤
    E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{max (max u v) (max v w)}
  /-- Its second page is the Čech cohomology of `K` of the cohomology presheaf. -/
  pageTwoIso (p q : ℕ) :
    sequence ⋙ CategoryTheory.SpectralSequence.pageFunctor _ _ 2 2 ⋙
        HomologicalComplex.eval _ _ (p, q) ≅
      (sheafToPresheaf J.toGrothendieck
          AddCommGrpCat.{max (max u v) (max v w)}).rightDerived q ⋙
        presheafCechCohomologyFunctor J (⊤_ (Cᵒᵖ ⥤ Type v)) K p
  /-- The functorial finite filtered abutment is global cohomology. -/
  abutment : FunctorialFirstQuadrantAbutsTo sequence
    (fun n => globalCohomologyFunctor.{w} J n)

/-- **Stacks Project, Tag 09VY.**  For a hypercovering `K` of the final presheaf on a site with
equalizers and fibre products there is a spectral sequence, functorial in the sheaf of abelian
groups `F`, with second page `E_2^{p,q} = Ȟ^p(K, H̲^q(F))` converging to the global cohomology
groups `H^{p+q}(F)`.

It is [Stacks, Tag 09VX] at the final presheaf, with its abutment transported along
`globalCohomologyAbutmentIso`. -/
@[stacks 09VY, sga "4 V 7.4.0" "(7.4.0.3)", sga "4 V 3.6" "more general"]
def hypercoveringGlobalSpectralSequence :
    HypercoveringGlobalSpectralSequenceData J K where
  sequence := hypercoverPresheafSpectralSequenceFunctor J (⊤_ (Cᵒᵖ ⥤ Type v)) K
  pageTwoIso p q := hypercoverPresheafPageTwoIso J (⊤_ (Cᵒᵖ ⥤ Type v)) K p q
  abutment := (hypercoverPresheafAbutment J (⊤_ (Cᵒᵖ ⥤ Type v)) K).ofIsoAbutment
    (globalCohomologyAbutmentIso J K)

end Assembled

end Stacks.CategoryTheory.Hypercovering

end
