module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import StacksFrontier.Homology.DerivedIndexing.Extend

/-!
# An exact functor commutes with the homology of an extension by zero

Let `e : c.Embedding c'` be an embedding of complex shapes, let `M` be a complex of shape `c` in
an abelian category `B` and let `G : B ⥤ D` be an additive functor that preserves homology.
There are two routes from the degree-`e.f j` homology of the extension by zero of `G` applied
termwise to `M` to `G` applied to the degree-`j` homology of `M`:

* compare the extension of `G(M)` with `G` applied to the extension of `M`
  (`Stacks.DerivedIndexing.mapExtendIso`), commute `G` past the homology
  (`CategoryTheory.ShortComplex.mapHomologyIso`) and then use that extension by zero does not
  change homology in the degrees `e` hits (`HomologicalComplex.extendHomologyIso`); or
* use `HomologicalComplex.extendHomologyIso` first, on `G(M)`, and commute `G` past the
  homology afterwards.

The two agree. That is `Stacks.DerivedIndexing.homologyMap_mapExtendIso_hom_comp`, the main
result, and `Stacks.DerivedIndexing.cyclesMap_mapExtendIso_hom_comp` is the same statement for
the cycles, to which it reduces.

This is the one piece of generic homological algebra needed to carry a statement about the
`ℕ`-indexed right derived functors across an exact functor into the `ℤ`-indexed world in which
`Stacks.DerivedIndexing.rightDerivedIsoRes` reads them: the `ℕ`-side comparison of a composite
`F ⋙ G` with `G` applied to the derived functor of `F` is a statement about complexes indexed by
`ℕ`, and the comparison of the two indexings extends those complexes by zero to complexes
indexed by `ℤ`.

The consumer lives two modules up. `Stacks.DerivedIndexing.rightDerivedIsoRes` is assembled on
*homotopy* categories, so the statement here is first carried across the quotient functor, as
`Stacks.DerivedIndexing.homologyMap_mapExtendHomotopyNatIso_hom_comp` in
`StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorExtendHomotopyHomology`, and is then
used in
`Stacks.DerivedIndexing.rightDerivedCompIso_hom_app_comp_rightDerivedIsoRes`
(`StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPostcomposeIndexing`), which says
that pulling an exact functor out of a right derived functor is compatible with the comparison
of the two indexings.

## Main definitions

* `Stacks.DerivedIndexing.mapExactCyclesIso`,
  `Stacks.DerivedIndexing.mapExactHomologyIso`: for an additive `G` preserving homology, the
  comparison between the cycles (resp. the homology) of `G` applied termwise to a complex and
  `G` applied to the cycles (resp. the homology). These are
  `CategoryTheory.ShortComplex.mapCyclesIso` and `CategoryTheory.ShortComplex.mapHomologyIso` at
  the short complex of a homological complex in a degree, named so that the source and target
  are spelled as the cycles and homology *of a homological complex*.

## Main results

* `Stacks.DerivedIndexing.cyclesMap_mapExtendIso_hom_comp`,
  `Stacks.DerivedIndexing.homologyMap_mapExtendIso_hom_comp`: **an exact functor commutes with
  the comparison of cycles, and of homology, of an extension by zero.**
* `Stacks.DerivedIndexing.homologyπ_mapHomologyIso_hom`: the projection from the cycles against
  `CategoryTheory.ShortComplex.mapHomologyIso`.
* `Stacks.DerivedIndexing.mono_map_iCycles`: an exact functor applied to the inclusion of the
  cycles of a complex is a monomorphism.

## Implementation notes

**One spelling for each object.** `CategoryTheory.ShortComplex.mapCyclesIso` and
`CategoryTheory.ShortComplex.mapHomologyIso` have `((K.sc i).map G).cycles` and
`((K.sc i).map G).homology` as their sources, whereas the morphisms they must compose with —
`HomologicalComplex.cyclesMap`, `HomologicalComplex.homologyMap`,
`HomologicalComplex.extendCyclesIso` — are spelled with
`((G.mapHomologicalComplex c).obj K).cycles`
and `((G.mapHomologicalComplex c).obj K).homology`. The two spellings are definitionally equal
but not syntactically so, and a statement that mixes them is a goal that `rw` and `simp` refuse
to touch: the rewrite motive is not type-correct at `implicit` transparency. The two
definitions `mapExactCyclesIso` and `mapExactHomologyIso` fix the homological-complex spelling
once; everything below is stated with them, so every goal here is syntactically well typed.

**`homologyπ_mapHomologyIso_hom` in term mode.** The same lemma is proved, for one concrete
functor, inside `StacksFrontier.Homology.Tor.CrossProduct`, with the pragma
`backward.isDefEq.respectTransparency false` covering the file; that pragma is not used here.
The substitute is a term-mode `calc` chain: `CategoryTheory.ShortComplex.LeftHomologyData`'s
`mapHomologyIso_eq` and `mapCyclesIso_eq` have right-hand sides that are themselves only
definitionally type-correct, so they are introduced by `congrArg Iso.hom` into named hypotheses
and every subsequent step is a `congrArg`, each of which elaborates at default transparency.

**The chases bottom out degreewise.** The cycles statement is proved by cancelling the
monomorphism `G.map (M.iCycles j)`, after which both sides are computed by the simp set of
`HomologicalComplex.extendCyclesIso_hom_iCycles`,
`CategoryTheory.ShortComplex.mapCyclesIso_hom_iCycles` and `HomologicalComplex.cyclesMap_i`, and
the remaining content is `Stacks.DerivedIndexing.mapExtendIso_hom_f_comp_map_extendXIso`, the
degreewise closed form of the termwise comparison. The homology statement is proved by
cancelling the epimorphism `HomologicalComplex.homologyπ` and reduces to the cycles statement.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits HomologicalComplex

namespace Stacks.DerivedIndexing

universe v v' u u'

variable {B : Type u} {D : Type u'} [Category.{v} B] [Category.{v'} D] [Abelian B] [Abelian D]

/-- `CategoryTheory.ShortComplex.mapHomologyIso` against the projection from the cycles. -/
lemma homologyπ_mapHomologyIso_hom (S : ShortComplex B) (G : B ⥤ D) [G.Additive]
    [G.PreservesLeftHomologyOf S] :
    (S.map G).homologyπ ≫ (S.mapHomologyIso G).hom =
      (S.mapCyclesIso G).hom ≫ G.map S.homologyπ := by
  have h := S.homologyData.left
  have hA : (S.mapHomologyIso G).hom =
      (h.map G).homologyIso.hom ≫ G.map h.homologyIso.inv :=
    congrArg Iso.hom (ShortComplex.LeftHomologyData.mapHomologyIso_eq h G)
  have hB : (S.mapCyclesIso G).hom =
      (h.map G).cyclesIso.hom ≫ G.map h.cyclesIso.inv :=
    congrArg Iso.hom (ShortComplex.LeftHomologyData.mapCyclesIso_eq h G)
  refine Eq.trans (congrArg (fun w => (S.map G).homologyπ ≫ w) hA) ?_
  refine Eq.trans ?_ (congrArg (fun w => w ≫ G.map S.homologyπ) hB).symm
  calc (S.map G).homologyπ ≫ ((h.map G).homologyIso.hom ≫ G.map h.homologyIso.inv)
      = ((S.map G).homologyπ ≫ (h.map G).homologyIso.hom) ≫ G.map h.homologyIso.inv :=
        (Category.assoc _ _ _).symm
    _ = ((h.map G).cyclesIso.hom ≫ (h.map G).π) ≫ G.map h.homologyIso.inv :=
        congrArg (fun w => w ≫ G.map h.homologyIso.inv)
          (h.map G).homologyπ_comp_homologyIso_hom
    _ = (h.map G).cyclesIso.hom ≫ (h.map G).π ≫ G.map h.homologyIso.inv :=
        Category.assoc _ _ _
    _ = (h.map G).cyclesIso.hom ≫ G.map h.π ≫ G.map h.homologyIso.inv :=
        congrArg (fun w => (h.map G).cyclesIso.hom ≫ w ≫ G.map h.homologyIso.inv)
          (ShortComplex.LeftHomologyData.map_π h G)
    _ = (h.map G).cyclesIso.hom ≫ G.map (h.π ≫ h.homologyIso.inv) :=
        congrArg (fun w => (h.map G).cyclesIso.hom ≫ w) (G.map_comp _ _).symm
    _ = (h.map G).cyclesIso.hom ≫ G.map (h.cyclesIso.inv ≫ S.homologyπ) :=
        congrArg (fun w => (h.map G).cyclesIso.hom ≫ G.map w)
          h.π_comp_homologyIso_inv
    _ = (h.map G).cyclesIso.hom ≫ G.map h.cyclesIso.inv ≫ G.map S.homologyπ :=
        congrArg (fun w => (h.map G).cyclesIso.hom ≫ w) (G.map_comp _ _)
    _ = ((h.map G).cyclesIso.hom ≫ G.map h.cyclesIso.inv) ≫ G.map S.homologyπ :=
        (Category.assoc _ _ _).symm

section Extend

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (G : B ⥤ D) [G.Additive] [G.PreservesHomology] (e : c.Embedding c')
  (M : HomologicalComplex B c) {j : ι} {j' : ι'}

/-- For an exact `G`, the comparison between the cycles of `G` applied termwise to a complex
and `G` applied to the cycles. -/
def mapExactCyclesIso (K : HomologicalComplex B c) (i : ι) :
    ((G.mapHomologicalComplex c).obj K).cycles i ≅ G.obj (K.cycles i) :=
  (K.sc i).mapCyclesIso G

/-- For an exact `G`, the comparison between the homology of `G` applied termwise to a complex
and `G` applied to the homology. -/
def mapExactHomologyIso (K : HomologicalComplex B c) (i : ι) :
    ((G.mapHomologicalComplex c).obj K).homology i ≅ G.obj (K.homology i) :=
  (K.sc i).mapHomologyIso G

/-- `mapExactCyclesIso` against the inclusion of the cycles. -/
@[reassoc (attr := simp)]
lemma mapExactCyclesIso_hom_iCycles (K : HomologicalComplex B c) (i : ι) :
    (mapExactCyclesIso G K i).hom ≫ G.map (K.iCycles i) =
      ((G.mapHomologicalComplex c).obj K).iCycles i :=
  ShortComplex.mapCyclesIso_hom_iCycles (K.sc i) G

/-- `mapExactHomologyIso` against the projection from the cycles. -/
@[reassoc (attr := simp)]
lemma homologyπ_mapExactHomologyIso_hom (K : HomologicalComplex B c) (i : ι) :
    ((G.mapHomologicalComplex c).obj K).homologyπ i ≫ (mapExactHomologyIso G K i).hom =
      (mapExactCyclesIso G K i).hom ≫ G.map (K.homologyπ i) :=
  homologyπ_mapHomologyIso_hom (K.sc i) G

include G in
/-- An exact functor applied to the inclusion of the cycles is a monomorphism. -/
lemma mono_map_iCycles : Mono (G.map (M.iCycles j)) := by
  have hfac : G.map (M.iCycles j) =
      (mapExactCyclesIso G M j).inv ≫ ((G.mapHomologicalComplex c).obj M).iCycles j := by
    rw [Iso.eq_inv_comp]
    exact mapExactCyclesIso_hom_iCycles G M j
  rw [hfac]
  exact mono_comp _ _

/-- **An exact functor commutes with the comparison of cycles of an extension by zero.** -/
@[reassoc]
theorem cyclesMap_mapExtendIso_hom_comp (hj : e.f j = j') :
    cyclesMap (mapExtendIso G e M).hom j' ≫ (mapExactCyclesIso G (M.extend e) j').hom ≫
          G.map ((M.extendCyclesIso e hj).hom) =
      (((G.mapHomologicalComplex c).obj M).extendCyclesIso e hj).hom ≫
        (mapExactCyclesIso G M j).hom := by
  have := mono_map_iCycles G M (j := j)
  refine (cancel_mono (G.map (M.iCycles j))).mp ?_
  simp only [Category.assoc]
  rw [← G.map_comp, extendCyclesIso_hom_iCycles, G.map_comp]
  simp [mapExtendIso_hom_f_comp_map_extendXIso]

/-- **An exact functor commutes with the comparison of homology of an extension by zero.** -/
theorem homologyMap_mapExtendIso_hom_comp (hj : e.f j = j') :
    homologyMap (mapExtendIso G e M).hom j' ≫ (mapExactHomologyIso G (M.extend e) j').hom ≫
          G.map ((M.extendHomologyIso e hj).hom) =
      (((G.mapHomologicalComplex c).obj M).extendHomologyIso e hj).hom ≫
        (mapExactHomologyIso G M j).hom := by
  refine (cancel_epi ((((G.mapHomologicalComplex c).obj M).extend e).homologyπ j')).mp ?_
  rw [homologyπ_naturality_assoc, homologyπ_mapExactHomologyIso_hom_assoc,
    homologyπ_extendHomologyIso_hom_assoc, homologyπ_mapExactHomologyIso_hom]
  rw [← G.map_comp, homologyπ_extendHomologyIso_hom, G.map_comp]
  exact cyclesMap_mapExtendIso_hom_comp_assoc G e M hj _

end Extend

end Stacks.DerivedIndexing

end
