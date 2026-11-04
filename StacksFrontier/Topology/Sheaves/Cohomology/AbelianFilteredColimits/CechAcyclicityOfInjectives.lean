module

public import StacksFrontier.Topology.Sheaves.Cohomology.AbelianFilteredColimits.CechComplexOfAFiniteFamily
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.InjectiveSheavesRestrictOnto
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasqueCechVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.CohomologyOverAQuasiCompactOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Čech acyclicity of injective abelian sheaves and of their filtered colimits

The two open clauses of Tag 0A37 need Stacks 01FF for abelian sheaves, which is proved modulo
its vanishing input `Hⁿ⁺¹(U, colimᵢ Eᵢ) = 0` for a filtered system of *injective* abelian
sheaves (`Stacks.Cohomology.AbelianColimit.isIso_colimit_post_H'functor_of_isCompact`).  This
file supplies the **Čech** half of that vanishing for abelian sheaves: the positive-degree Čech
cohomology of a filtered colimit of injective abelian sheaves vanishes for every finite cover by
quasi-compact opens.

That is one of the two hypotheses of Stacks 01EW; the other, cofinality of those covers, is
already available (`Stacks.Cohomology.Vanishing.exists_compactCover_refines`).  Stacks 01EW
itself is formalized only in the sheaves-of-modules spelling
(`Stacks.Cohomology.BasisCycles.isZero_hgroup_of_cech_isZero_on_basis`, stated for
`SheafOfModules R` and proved through `Hgroup R`, `abPresheaf R` and the cocycle staircase
`cechSurjKer_of_le`), so the step from the Čech vanishing proved here to the vanishing of
`Sheaf.H'` is *not* available and no declaration here carries the tag 0A37.

## Main results

* `isFlasque_of_injective`: **an injective abelian sheaf is flasque.**  This is the abelian form
  of the input that Stacks 01EP supplies for sheaves of modules; it needs none of the module
  machinery, because Stacks 01EA is already formalized for abelian sheaves as
  `Stacks.Cohomology.InjectiveRestriction.injective_abelian_restriction_surjective`.
* `isZero_cechComplex_homology_of_injective`: **the positive-degree Čech cohomology of an
  injective abelian sheaf vanishes**, by Stacks 09SZ, which is already abelian.
* `preservesColimitsOfShape_cechComplexFunctor_sheaf`: the Čech complex of a finite cover by
  quasi-compact opens, as a functor on abelian *sheaves*, preserves filtered colimits.
* `isZero_cechComplex_homology_colimit_of_injective`: **the positive-degree Čech cohomology of a
  filtered colimit of injective abelian sheaves vanishes**, for every finite cover by
  quasi-compact opens.

## Implementation notes

The sheaves are spelled `Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}` with
`X : Type u` carrying a topology, because that is the spelling in which the degree-zero input
Stacks 009F and the `δ`-functor instances are available; Stacks 01EA and 09SZ are stated for
`TopCat.Sheaf AddCommGrpCat.{u} X` with `X : TopCat`, which is the same category by a
semireducible `def`.  Crossing between them is definitional, but instance search does not
cross it within its heartbeat budget, so `isFlasque_of_injective` transports the `Injective`
instance by `assumption` and passes it explicitly.

A colimit of abelian sheaves is not computed as a colimit of presheaves, so `sheafToPresheaf`
does not preserve filtered colimits; it does so after composing with evaluation at a
quasi-compact open, by Stacks 009F.  All the opens occurring in the Čech complex of a cover by
quasi-compact opens are quasi-compact — the index type `Fin (n + 1)` of an intersection is never
empty, so (H2) applies — and a *finite* product of such evaluations is a coproduct, hence
preserves colimits.  This is the same argument as in `StacksDraft.Ch20.Sec18.Tag01FFVanishing`,
with the forgetful functor from sheaves of modules removed from the front.

## References

* [Stacks Project, Tag 01EA](https://stacks.math.columbia.edu/tag/01EA)
* [Stacks Project, Tag 01EW](https://stacks.math.columbia.edu/tag/01EW)
* [Stacks Project, Tag 09SZ](https://stacks.math.columbia.edu/tag/09SZ)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.Cohomology.Basis (OpenCover)
open Stacks.Cohomology.Vanishing (compactCovers isCompact_coe_iInf)

universe u

namespace Stacks.Cohomology.AbelianVanishing

variable {X : Type u} [TopologicalSpace X]

/-! ### An injective abelian sheaf is flasque, hence Čech-acyclic -/

/-- **An injective abelian sheaf is flasque.**  Stacks 01EA for abelian sheaves says that the
restriction maps of an injective abelian sheaf are surjective, and a surjection of abelian
groups is an epimorphism. -/
@[sga "4 V 4.6" "special case"]
instance isFlasque_of_injective (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [Injective F] :
    TopCat.Sheaf.IsFlasque (X := TopCat.of X) F := by
  have hinj : @Injective (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of X)) _ F := by assumption
  refine ⟨fun {U V} i => ?_⟩
  rw [AddCommGrpCat.epi_iff_surjective]
  exact @Stacks.Cohomology.InjectiveRestriction.injective_abelian_restriction_surjective
    (TopCat.of X) F hinj _ _ (leOfHom i.unop)

/-- **The positive-degree Čech cohomology of an injective abelian sheaf vanishes**, for every
family of open subsets: an injective abelian sheaf is flasque, and a flasque sheaf of abelian
groups has vanishing higher Čech cohomology by Stacks 09SZ. -/
theorem isZero_cechComplex_homology_of_injective {ι : Type u}
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [Injective F]
    (U : ι → Opens X) (p : ℕ) (hp : 0 < p) :
    IsZero (((cechComplexFunctor U).obj F.obj).homology p) :=
  Stacks.Cohomology.FlasqueCech.isZero_cechComplex_homology_of_isFlasque
    (X := TopCat.of X) F (⨆ i, U i) U rfl p hp

/-! ### The Čech complex of abelian sheaves and filtered colimits -/

section Colimit

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  {I : Type u} [SmallCategory I] [IsFiltered I]

/-- **A finite product of sections functors over quasi-compact opens preserves filtered
colimits**, as a functor on abelian sheaves.  The degree-`n` term of the Čech complex of a cover
is `Stacks.Cohomology.CechColimit.piEval` applied to the family of intersections occurring in
it; each factor preserves filtered colimits by Stacks 009F for abelian sheaves, because the
corresponding open is quasi-compact, and a finite product of abelian groups is a coproduct. -/
theorem preservesColimitsOfShape_piEval_sheaf
    (hBasis : PrespectralSpace X) (hInter : QuasiSeparatedSpace X)
    (T : Type u) [Finite T] (V : T → Opens X) (hV : ∀ t, IsCompact (V t : Set X)) :
    PreservesColimitsOfShape I
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        CechColimit.piEval (A := AddCommGrpCat.{u}) T V) := by
  have hwhisk : PreservesColimitsOfShape I
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        (Functor.whiskeringLeft (Discrete T) (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj
          (Discrete.functor fun t => op (V t))) := by
    refine preservesColimitsOfShape_of_evaluation _ I fun t => ?_
    exact Stacks.Cohomology.Sections.preservesColimitsOfShape_sheafSections_of_isCompact
      hBasis hInter (V t.as) (hV t.as)
  have hsigma : PreservesColimitsOfShape I
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        CechColimit.sigmaEval (A := AddCommGrpCat.{u}) T V) :=
    comp_preservesColimitsOfShape
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        (Functor.whiskeringLeft (Discrete T) (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj
          (Discrete.functor fun t => op (V t)))
      (colim : (Discrete T ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u})
  exact preservesColimitsOfShape_of_natIso
    (Functor.isoWhiskerLeft
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (CechColimit.piEvalIsoSigmaEval (A := AddCommGrpCat.{u}) T V).symm)

/-- **The Čech complex of a finite cover by quasi-compact opens, as a functor on abelian
sheaves, preserves filtered colimits.**  Colimits of cochain complexes are computed degreewise,
and the degree-`n` term is the finite product of the sections over the intersections occurring
in the cover, all of which are quasi-compact. -/
theorem preservesColimitsOfShape_cechComplexFunctor_sheaf
    (hBasis : PrespectralSpace X) (hInter : QuasiSeparatedSpace X)
    (W : OpenCover X) (hW : W ∈ compactCovers X) :
    PreservesColimitsOfShape I
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        cechComplexFunctor (A := AddCommGrpCat.{u}) W.obj) := by
  have := hW.1
  refine HomologicalComplex.preservesColimitsOfShape_of_eval _ fun n => ?_
  exact preservesColimitsOfShape_piEval_sheaf hBasis hInter (Fin (n + 1) → W.ι)
    (inter W.obj) fun x => by
      rw [inter_eq_iInf]
      exact isCompact_coe_iInf hInter (fun k => W.obj (x k)) fun k => hW.2.2 _

/-- **The positive-degree Čech cohomology of a filtered colimit of injective abelian sheaves
vanishes**, for every finite cover by quasi-compact opens.

The Čech complex of the colimit is the colimit of the Čech complexes
(`preservesColimitsOfShape_cechComplexFunctor_sheaf`); each of those is acyclic in positive
degrees, because an injective abelian sheaf is flasque and a flasque sheaf has vanishing higher
Čech cohomology; and a filtered colimit of complexes acyclic in a positive degree is acyclic
there (Stacks 00DB).

This is the Čech input of Stacks 01EW for abelian sheaves.  Stacks 01EW itself is available only
for sheaves of modules, so this does not yet give the vanishing of `Sheaf.H'` that the open
clauses of Tag 0A37 need. -/
theorem isZero_cechComplex_homology_colimit_of_injective
    (hBasis : PrespectralSpace X) (hInter : QuasiSeparatedSpace X)
    (W : OpenCover X) (hW : W ∈ compactCovers X)
    (E : I ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hE : ∀ i, Injective (E.obj i)) (n : ℕ) :
    IsZero (((cechComplexFunctor W.obj).obj (colimit E).obj).homology (n + 1)) := by
  have hpres := preservesColimitsOfShape_cechComplexFunctor_sheaf
    (I := I) hBasis hInter W hW
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  refine CechColimit.exactAt_succ_of_isColimit
    (isColimitOfPreserves (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      cechComplexFunctor (A := AddCommGrpCat.{u}) W.obj) (colimit.isColimit E)) n fun i => ?_
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have := hE i
  exact isZero_cechComplex_homology_of_injective (E.obj i) W.obj (n + 1) (Nat.succ_pos n)

end Colimit

end Stacks.Cohomology.AbelianVanishing

end
