module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitCoherence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorMonoidalLift

/-!
# The right-unitor coherence of the Tag 079U comparison, from the monoidal lift of `f^*`

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitObject_of_kFlat`
proves [Stacks, Tag 08EU] at `K = 𝒪_Y[0]` from one remaining equation, the right-unitor
coherence of the comparison of [Stacks, Tag 079U] at the image of a **K-flat** complex:

`Lf^*(QK ⊗^𝐋_{𝒪_Y} 𝒪_Y[0]) ⟶ Lf^*(QK) ⊗^𝐋_{𝒪_X} Lf^*(𝒪_Y[0])`, then `𝟙 ⊗ ν`, then `ρX`,
equals `Lf^*ρY`.

**This file proves that equation**, and with it the base case, on the single hypothesis that
`f^*` carries a monoidal structure for the tensor product sheaf whose oplax tensorator is the
comparison of [Stacks, Tag 01CD].  That hypothesis is discharged — it is
`Stacks.PullbackSheafTensor.monoidal` — in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitObject`, which
is where the base case becomes unconditional.

The whole of the complex-level content is
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIsoOfIsIso_rightUnitor`: the
comparison of total tensor complexes is the tensorator of the monoidal lift of `f^*` to
complexes, so its right unit coherence is a unitality axiom of
`CategoryTheory.Functor.Monoidal` and no total complex is taken apart anywhere below.

## Main results

* `Stacks.Cohomology.DerivedProjectionFormula.rightUnitorCoherence_complex`: **the right-unitor
  coherence on total tensor complexes**, in the spelling of the comparison
  `Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso` of [Stacks, Tag 079U].
* `Stacks.Cohomology.DerivedProjectionFormula.derivedUnitComparison`: the unit comparison
  `Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]`, through the K-flat representative `𝒪_Y[0]`.
* `Stacks.Cohomology.DerivedProjectionFormula.rightUnitorCoherence_app_q`: **the right-unitor
  coherence of [Stacks, Tag 079U] at the image of a K-flat complex** — the hypothesis of
  `rightUnitorCoherence_of_kFlat`, discharged.
* `Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitObject_of_monoidal`:
  **[Stacks, Tag 08EU] at `K = 𝒪_Y[0]`** for an arbitrary morphism of ringed spaces and an
  arbitrary `E ∈ D(𝒪_X)`, carrying nothing but the monoidal structure of `f^*`.

## Implementation notes

**Why the monoidal structure of `f^*` is a hypothesis here.**  It exists:
`Stacks.PullbackSheafTensor.monoidal`, whose oplax tensorator is the comparison of
[Stacks, Tag 01CD] and whose oplax unit is `ν : f^*𝒪_Y ≅ 𝒪_X`.  Importing that module into this
one is what fails: its transitive import
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackAlgebraIso` makes instance search unable
to synthesize `HasFiniteCoproducts (Mod 𝒪_Z)`, and the total tensor product of complexes —
`HomologicalComplex.monoidalCategory`, which every statement below is read at — needs
`HasZeroObject (Mod 𝒪_Z)`, which goes the same way.  Carrying the structure as a binder keeps
this module free of that import; the companion module supplies it, and needs none of the
monoidal structure on complexes to do so.

**Which unit comparison is used, and why that is free.**  `ν` is not a parameter below: it is
`derivedUnitComparison`, the comparison `Lf^*(QM) ⟶ Q(f^*M)` of
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans` at the K-flat complex `𝒪_Y[0]`,
followed by `Q` of the complex-level unit comparison of the monoidal lift.  Fixing it costs
nothing: the conclusion of `isIso_projectionFormulaMap_unitObject_of_kFlat` does not mention `ν`,
so a particular choice of it is as good as a quantified one, and this choice is the one for which
the coherence is the monoidal unitality axiom.

**The ascriptions.**  Three pairs of terms are equal by `rfl` and not syntactically equal, and a
`rw` whose pattern straddles a pair finds nothing: the source of the right unitor of complexes,
spelled by `totalComplexPair` in the comparisons of [Stacks, Tag 079U] and by
`(Tot(- ⊗ -)).flip.obj 𝒪[0]` by `tensorComplexRightUnitorNatIso` (`totalRightUnitor` ascribes it
at the first); the component of a natural isomorphism read as `Iso.app` and as `NatTrans.app`
(`derivedTensorRightUnitor_app_hom`); and the right comparison of [Stacks, Tag 079U] as a
whiskered composite and written out (`rightComparison_app_eq`).  Each crossing is a `rfl` lemma
used once.

**The two `implicit_reducible` opt-ins, and what is *not* among them.**
`AlgebraicGeometry.SheafedSpace.sheaf` is the structure projection `Z ↦ Z.sheaf`, whose value is
typed `TopCat.Sheaf CommRingCat Z` where `Sheaf (Opens.grothendieckTopology Z) CommRingCat` is
wanted, and `CategoryTheory.sheafCompose` is Mathlib's whiskering of sheaves along a functor.
Without both at the `implicit` transparency level, a `rw` or `dsimp` on a goal mixing the two
spellings reports a missing pattern rather than the cause, and
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans` is not found by instance
search at the unit complex.  Neither of the two is a sheaf-of-**rings** spelling:
`Stacks.RingedSpace.structureRingSheaf` and `StacksDraft.KFlat.modulePullback` were both tried
in this list and are **not** needed, so nothing below makes a ring-sheaf spelling reducible, and
`CategoryTheory.Sheaf.toRingCat` is mentioned nowhere.  The companion module
`ProjectionFormulaUnitObject` needs no opt-in at all.

**Where the elaborator's budget is spent.**  `derivedUnitComparison` carries an `IsIso` instance,
so unfolding it is expensive; a `rw` whose pattern mentions it exceeds the default budget.  Every
intermediate statement therefore writes the unit comparison out as
`derivedPullbackNatTrans ≫ Q(ν_c)`, and `derivedUnitComparison_hom` is applied once, at the end.
For the same reason associativity is normalised by a single `simp only [Category.assoc]` rather
than by `rw [Category.assoc]` inside the large composites.

## References

* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace
open AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedPullbackTensor
open Stacks.DerivedTensor.RingedSite
open Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedProjectionFormula

section Monoidal

variable (Z : RingedSpace.{u, u})

/-- The monoidal structure on `Mod(𝒪_Z)` whose tensor product is the tensor product sheaf. -/
@[instance_reducible] local instance monoidalModules :
    MonoidalCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) :=
  _root_.SheafOfModules.monoidalCategorySheafTensor Z.sheaf

/-- The symmetry of that structure. -/
@[instance_reducible] local instance symmetricModules :
    SymmetricCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) :=
  _root_.SheafOfModules.symmetricCategorySheafTensor Z.sheaf

/-- That structure is additive in each variable. -/
local instance monoidalPreadditiveModules :
    MonoidalPreadditive (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) :=
  _root_.SheafOfModules.monoidalPreadditiveSheafTensor Z.sheaf

/-- That structure is closed. -/
@[instance_reducible] local instance monoidalClosedModules :
    MonoidalClosed (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) :=
  _root_.SheafOfModules.monoidalClosedSheafTensor Z.sheaf

-- The antidiagonal coproducts of a total tensor complex exist.  The instance is
-- `Stacks.Cohomology.DerivedPullbackTensor.hasTensorModules` of
-- `StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/PullbackTensorMonoidalLift.lean`,
-- seated here rather than restated: that module owns it, it is imported above, and
-- `monoidalComplexes` below needs it.
attribute [local instance] Stacks.Cohomology.DerivedPullbackTensor.hasTensorModules

/-- The total tensor product of complexes of `𝒪_Z`-modules. -/
@[instance_reducible] local instance monoidalComplexes :
    MonoidalCategory
      (CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :=
  HomologicalComplex.monoidalCategory _ _

attribute [local instance] modulePullback_preservesAntidiagonalCoproducts
attribute [local instance] HasDerivedCategory.standard


variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [(StacksDraft.KFlat.modulePullback f).Monoidal]

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### The right unitor of a total tensor complex, ascribed -/

/-- **The right unitor of the total tensor complex** `Tot(K ⊗_{𝒪_W} 𝒪_W[0]) ⟶ K`, with its
source **ascribed** at the `Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair` spelling.

That spelling and `((Tot(- ⊗ -)).flip.obj 𝒪_W[0]).obj K`, which
`Stacks.DerivedTensor.RingedSite.tensorComplexRightUnitorNatIso` produces, are equal by `rfl`
and are not syntactically equal; a naturality square taken at the unascribed morphism therefore
does not rewrite inside a statement about the comparisons of [Stacks, Tag 079U], which are
indexed by `totalComplexPair`. -/
def totalRightUnitor (W : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules W) ℤ) :
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf)).obj
        (K, unitComplex (Stacks.RingedSpace.toRingedSite W)) ⟶ K :=
  ((tensorComplexRightUnitorNatIso (Stacks.RingedSpace.toRingedSite W)).app K).hom

/-- The component of the derived right unitor read as an isomorphism and read as the value of its
underlying natural transformation agree; the two spellings both occur among the statements this
file composes, and `rw` matches neither against the other. -/
private theorem derivedTensorRightUnitor_app_hom (W : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (A : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing W))) :
    ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso W).app A).hom =
      (Stacks.RingedSpace.derivedTensorRightUnitorNatIso W).hom.app A :=
  rfl

/-! ### The unit comparison on complexes -/

/-- **The unit comparison of the monoidal lift of `f^*` to complexes**, as an isomorphism
`f^*(𝒪_Y[0]) ≅ 𝒪_X[0]` of complexes of `𝒪_X`-modules. -/
def pullbackUnitComplexIso :
    (pullbackComplex f).obj (unitComplex (Stacks.RingedSpace.toRingedSite Y)) ≅
      unitComplex (Stacks.RingedSpace.toRingedSite X) :=
  (asIso (ε (pullbackComplex f))).symm

omit [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The inverse of `pullbackUnitComplexIso` is the lax unit of the monoidal lift. -/
theorem pullbackUnitComplexIso_inv :
    (pullbackUnitComplexIso f).inv = ε (pullbackComplex f) :=
  rfl

/-! ### The coherence on complexes -/

/-- `rightUnitorCoherence_complex` in the monoidal spelling of the two categories of
complexes. -/
private theorem rightUnitorCoherence_complex_monoidal
    (hδ : IsComparisonTensorator f)
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    ((pullbackComplex f).obj K ◁ (pullbackUnitComplexIso f).hom) ≫
        (ρ_ ((pullbackComplex f).obj K)).hom =
      (pullbackTensorComplexIsoOfIsIso f K
          (𝟙_ (CochainComplex
            (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ))).inv ≫
        (pullbackComplex f).map (ρ_ K).hom :=
  have hw : ((pullbackComplex f).obj K ◁ (pullbackUnitComplexIso f).hom) ≫
      ((pullbackComplex f).obj K ◁ ε (pullbackComplex f)) =
        𝟙 ((pullbackComplex f).obj K ⊗ (pullbackComplex f).obj
          (𝟙_ (CochainComplex
            (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ))) :=
    (MonoidalCategory.whiskerLeftIso ((pullbackComplex f).obj K)
      (pullbackUnitComplexIso f)).hom_inv_id
  ((congrArg (fun φ => ((pullbackComplex f).obj K ◁ (pullbackUnitComplexIso f).hom) ≫ φ)
        (pullbackTensorComplexIsoOfIsIso_rightUnitor f hδ K)).trans
      (Category.assoc _ _ _).symm).trans
    ((congrArg (fun φ => φ ≫ ((pullbackTensorComplexIsoOfIsIso f K
          (𝟙_ (CochainComplex
            (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ))).inv ≫
        (pullbackComplex f).map (ρ_ K).hom)) hw).trans (Category.id_comp _))

/-- **The right-unitor coherence of the comparison of [Stacks, Tag 01CD] on total tensor
complexes.**  The comparison `f^*Tot(K ⊗_{𝒪_Y} 𝒪_Y[0]) ⟶ Tot(f^*K ⊗_{𝒪_X} f^*𝒪_Y[0])`, followed
by the unit comparison in the second factor and the right unitor of complexes on `X`, is `f^*`
of the right unitor of complexes on `Y`. -/
theorem rightUnitorCoherence_complex (hδ : IsComparisonTensorator f)
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj K))
          (pullbackUnitComplexIso f).hom
          (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ) ≫
        totalRightUnitor X ((pullbackComplex f).obj K) =
      (pullbackTensorComplexNatIso f).inv.app
          (K, unitComplex (Stacks.RingedSpace.toRingedSite Y)) ≫
        (pullbackComplex f).map (totalRightUnitor Y K) :=
  rightUnitorCoherence_complex_monoidal f hδ K

/-! ### The unit comparison on the derived category -/

/-- **The derived unit comparison** `Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]`, obtained on the K-flat
representative `𝒪_Y[0]`: there the derived pullback is the degreewise pullback, whose unit
comparison is `pullbackUnitComplexIso`. -/
def derivedUnitComparison : (derivedPullback f).obj (singleUnit Y) ≅ singleUnit X :=
  @asIso _ _ _ _ ((derivedPullbackNatTrans f).app (unitComplex (Stacks.RingedSpace.toRingedSite Y)))
      (isIso_derivedPullbackNatTrans_app f (unitComplex (Stacks.RingedSpace.toRingedSite Y))
        (Stacks.SheafOfModules.isKFlat_single_unit (Stacks.RingedSpace.toRingedSite Y).O)) ≪≫
    DerivedCategory.Q.mapIso (pullbackUnitComplexIso f)

/-- The derived unit comparison, on the K-flat representative. -/
theorem derivedUnitComparison_hom :
    (derivedUnitComparison f).hom =
      (derivedPullbackNatTrans f).app (unitComplex (Stacks.RingedSpace.toRingedSite Y)) ≫
        DerivedCategory.Q.map (pullbackUnitComplexIso f).hom :=
  rfl

/-! ### The coherence at a K-flat representative -/

omit [(StacksDraft.KFlat.modulePullback f).Monoidal] in
/-- **The left comparison at the unit, followed by the degreewise right unitor, is the derived
right unitor.**  The derived pullback of the canonical map to the ordinary total tensor complex
is the derived pullback of the right unit constraint, by
`Stacks.Cohomology.DerivedProjectionFormula.derivedTensorRightUnitorNatIso_hom_app_q`; the
passage from the total complex to `K` is the naturality of `derivedPullbackNatTrans`. -/
private theorem leftComparison_app_unit_comp
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (leftComparison f).app (K, unitComplex (Stacks.RingedSpace.toRingedSite Y)) ≫
        DerivedCategory.Q.map ((pullbackComplex f).map (totalRightUnitor Y K)) =
      (derivedPullback f).map
          ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso Y).hom.app
            (DerivedCategory.Q.obj K)) ≫
        (derivedPullbackNatTrans f).app K := by
  have hnat := (derivedPullbackNatTrans f).naturality (totalRightUnitor Y K)
  have hinner : (canonicalDerivedTensorProduct Y.sheaf).toTensor K
          (unitComplex (Stacks.RingedSpace.toRingedSite Y)) ≫
        DerivedCategory.Q.map (totalRightUnitor Y K) =
      (Stacks.RingedSpace.derivedTensorRightUnitorNatIso Y).hom.app
        (DerivedCategory.Q.obj K) := by
    rw [derivedTensorRightUnitorNatIso_hom_app_q Y K,
      (canonicalDerivedTensorProduct Y.sheaf).toTensor_eq_comparisonRight K
        (unitComplex (Stacks.RingedSpace.toRingedSite Y))
        (Stacks.SheafOfModules.isKFlat_single_unit (Stacks.RingedSpace.toRingedSite Y).O)]
    rfl
  have happ : (leftComparison f).app (K, unitComplex (Stacks.RingedSpace.toRingedSite Y)) =
      (derivedPullback f).map ((canonicalDerivedTensorProduct Y.sheaf).toTensor K
          (unitComplex (Stacks.RingedSpace.toRingedSite Y))) ≫
        (derivedPullbackNatTrans f).app
          ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).obj
            (K, unitComplex (Stacks.RingedSpace.toRingedSite Y))) :=
    rfl
  refine (congrArg (fun φ => φ ≫
      DerivedCategory.Q.map ((pullbackComplex f).map (totalRightUnitor Y K))) happ).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun φ => (derivedPullback f).map
      ((canonicalDerivedTensorProduct Y.sheaf).toTensor K
        (unitComplex (Stacks.RingedSpace.toRingedSite Y))) ≫ φ) hnat.symm).trans ?_
  refine Eq.trans (Category.assoc _ _ _).symm
    (congrArg (fun φ => φ ≫ (derivedPullbackNatTrans f).app K) ?_)
  exact ((derivedPullback f).map_comp _ _).symm.trans
    (congrArg (derivedPullback f).map hinner)

/-- **The canonical map to the ordinary total tensor complex on `X`, followed by the comparison
of total complexes and the degreewise right unitor on `Y`, is the unit comparison followed by the
derived right unitor on `X`.**  Both sides start from `Q(f^*K) ⊗^𝐋_{𝒪_X} Q(f^*𝒪_Y[0])`; the
degreewise pullback of `𝒪_Y[0]` is K-flat, so the right K-flat comparison computes that object,
and the naturality of that comparison in the right factor reduces the identity to the
coherence `rightUnitorCoherence_complex` on complexes. -/
private theorem toTensor_pullbackUnit_comp (hδ : IsComparisonTensorator f)
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (canonicalDerivedTensorProduct X.sheaf).toTensor ((pullbackComplex f).obj K)
          ((pullbackComplex f).obj (unitComplex (Stacks.RingedSpace.toRingedSite Y))) ≫
        DerivedCategory.Q.map ((pullbackTensorComplexNatIso f).inv.app
            (K, unitComplex (Stacks.RingedSpace.toRingedSite Y))) ≫
          DerivedCategory.Q.map ((pullbackComplex f).map (totalRightUnitor Y K)) =
      (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
            ((𝟙 (DerivedCategory.Q.obj ((pullbackComplex f).obj K)) ×ₘ
                DerivedCategory.Q.map (pullbackUnitComplexIso f).hom) :
              ((DerivedCategory.Q.obj ((pullbackComplex f).obj K),
                  DerivedCategory.Q.obj ((pullbackComplex f).obj
                    (unitComplex (Stacks.RingedSpace.toRingedSite Y)))) : _ × _) ⟶
                (DerivedCategory.Q.obj ((pullbackComplex f).obj K), singleUnit X)) ≫
          ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).app
            (DerivedCategory.Q.obj ((pullbackComplex f).obj K))).hom := by
  rw [uncurry_map_id_left (derivedTensorProductFunctor X.sheaf)
    (DerivedCategory.Q.obj ((pullbackComplex f).obj K))
    (DerivedCategory.Q.map (pullbackUnitComplexIso f).hom)]
  have hPU : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X
      ((pullbackComplex f).obj (unitComplex (Stacks.RingedSpace.toRingedSite Y))) :=
    Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_unconditional f
      (unitComplex (Stacks.RingedSpace.toRingedSite Y))
      (Stacks.SheafOfModules.isKFlat_single_unit (Stacks.RingedSpace.toRingedSite Y).O)
  have hcrn := (canonicalDerivedTensorProduct X.sheaf).comparisonRight_naturality
    (𝟙 ((pullbackComplex f).obj K)) (pullbackUnitComplexIso f).hom hPU
    (Stacks.SheafOfModules.isKFlat_single_unit (Stacks.RingedSpace.toRingedSite X).O)
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at hcrn
  have hR : ((derivedTensorProductFunctor X.sheaf).obj
            (DerivedCategory.Q.obj ((pullbackComplex f).obj K))).map
          (DerivedCategory.Q.map (pullbackUnitComplexIso f).hom) ≫
        ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).app
          (DerivedCategory.Q.obj ((pullbackComplex f).obj K))).hom =
      ((canonicalDerivedTensorProduct X.sheaf).comparisonRight ((pullbackComplex f).obj K)
            ((pullbackComplex f).obj (unitComplex (Stacks.RingedSpace.toRingedSite Y)))
            hPU).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
            (𝟙 ((pullbackComplex f).obj K)) (pullbackUnitComplexIso f).hom
            (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)) ≫
          DerivedCategory.Q.map (totalRightUnitor X ((pullbackComplex f).obj K)) := by
    refine (congrArg (fun φ => ((derivedTensorProductFunctor X.sheaf).obj
        (DerivedCategory.Q.obj ((pullbackComplex f).obj K))).map
          (DerivedCategory.Q.map (pullbackUnitComplexIso f).hom) ≫ φ)
      ((derivedTensorRightUnitor_app_hom X
          (DerivedCategory.Q.obj ((pullbackComplex f).obj K))).trans
        (derivedTensorRightUnitorNatIso_hom_app_q X ((pullbackComplex f).obj K)))).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun φ => φ ≫
      DerivedCategory.Q.map (totalRightUnitor X ((pullbackComplex f).obj K))) hcrn).trans ?_
    exact Category.assoc _ _ _
  rw [(canonicalDerivedTensorProduct X.sheaf).toTensor_eq_comparisonRight _ _ hPU]
  refine Eq.trans (congrArg (fun φ =>
      ((canonicalDerivedTensorProduct X.sheaf).comparisonRight ((pullbackComplex f).obj K)
        ((pullbackComplex f).obj (unitComplex (Stacks.RingedSpace.toRingedSite Y)))
        hPU).hom ≫ φ) ?_) hR.symm
  exact ((DerivedCategory.Q.map_comp _ _).symm.trans
      (congrArg DerivedCategory.Q.map (rightUnitorCoherence_complex f hδ K).symm)).trans
    (DerivedCategory.Q.map_comp _ _)

/-- The product morphism `(𝟙, b ≫ Qν_c) ≫ (a, 𝟙)` of the product category, rewritten as
`(a, b) ≫ (𝟙, Qν_c)`: both are `(a, b ≫ Qν_c)`.

The unit comparison is written out as `b ≫ Qν_c` rather than as `derivedUnitComparison`, which
it is: unfolding that definition exposes the `IsIso` instance it carries, and a rewrite whose
pattern mentions it exceeds the elaborator's budget. -/
private theorem prod_comp_unitComparison
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    ((𝟙 ((derivedPullback f).obj (DerivedCategory.Q.obj K)) ×ₘ
            ((derivedPullbackNatTrans f).app
                (unitComplex (Stacks.RingedSpace.toRingedSite Y)) ≫
              DerivedCategory.Q.map (pullbackUnitComplexIso f).hom)) :
          (((derivedPullback f).obj (DerivedCategory.Q.obj K),
              (derivedPullback f).obj (singleUnit Y)) : _ × _) ⟶
            ((derivedPullback f).obj (DerivedCategory.Q.obj K), singleUnit X)) ≫
        (((derivedPullbackNatTrans f).app K ×ₘ
            𝟙 (singleUnit X)) :
          (((derivedPullback f).obj (DerivedCategory.Q.obj K), singleUnit X) : _ × _) ⟶
            (DerivedCategory.Q.obj ((pullbackComplex f).obj K), singleUnit X)) =
      (((derivedPullbackNatTrans f).app K ×ₘ
            (derivedPullbackNatTrans f).app
              (unitComplex (Stacks.RingedSpace.toRingedSite Y))) :
          (((derivedPullback f).obj (DerivedCategory.Q.obj K),
              (derivedPullback f).obj (singleUnit Y)) : _ × _) ⟶
            (DerivedCategory.Q.obj ((pullbackComplex f).obj K),
              DerivedCategory.Q.obj ((pullbackComplex f).obj
                (unitComplex (Stacks.RingedSpace.toRingedSite Y))))) ≫
        ((𝟙 (DerivedCategory.Q.obj ((pullbackComplex f).obj K)) ×ₘ
            DerivedCategory.Q.map (pullbackUnitComplexIso f).hom) :
          ((DerivedCategory.Q.obj ((pullbackComplex f).obj K),
              DerivedCategory.Q.obj ((pullbackComplex f).obj
                (unitComplex (Stacks.RingedSpace.toRingedSite Y)))) : _ × _) ⟶
            (DerivedCategory.Q.obj ((pullbackComplex f).obj K), singleUnit X)) :=
  Prod.ext ((Category.id_comp _).trans (Category.comp_id _).symm) (Category.comp_id _)

omit [(StacksDraft.KFlat.modulePullback f).Monoidal] in
/-- The right comparison at a pair of complexes, written out: the derived pullback of each
factor, then the canonical map to the ordinary total tensor complex on `X`, then the comparison
of total complexes. -/
private theorem rightComparison_app_eq
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (rightComparison f).app (K, L) =
      (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
            (((derivedPullbackNatTrans f).app K ×ₘ (derivedPullbackNatTrans f).app L) :
              (((derivedPullback f).obj (DerivedCategory.Q.obj K),
                  (derivedPullback f).obj (DerivedCategory.Q.obj L)) : _ × _) ⟶
                (DerivedCategory.Q.obj ((pullbackComplex f).obj K),
                  DerivedCategory.Q.obj ((pullbackComplex f).obj L))) ≫
          (canonicalDerivedTensorProduct X.sheaf).toTensor ((pullbackComplex f).obj K)
              ((pullbackComplex f).obj L) ≫
            DerivedCategory.Q.map ((pullbackTensorComplexNatIso f).inv.app (K, L)) :=
  rfl

/-- **The right comparison at the unit, followed by the degreewise right unitor on `Y`, is the
unit comparison followed by the derived right unitor on `X`.**  The derived right unitor is moved
from `Lf^*(QK)` to `Q(f^*K)` by its own naturality, and the rest is
`toTensor_pullbackUnit_comp`. -/
private theorem rightComparison_app_unit_comp (hδ : IsComparisonTensorator f)
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (rightComparison f).app (K, unitComplex (Stacks.RingedSpace.toRingedSite Y)) ≫
        DerivedCategory.Q.map ((pullbackComplex f).map (totalRightUnitor Y K)) =
      (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
            ((𝟙 ((derivedPullback f).obj (DerivedCategory.Q.obj K)) ×ₘ
                ((derivedPullbackNatTrans f).app
                    (unitComplex (Stacks.RingedSpace.toRingedSite Y)) ≫
                  DerivedCategory.Q.map (pullbackUnitComplexIso f).hom)) :
              (((derivedPullback f).obj (DerivedCategory.Q.obj K),
                  (derivedPullback f).obj (singleUnit Y)) : _ × _) ⟶
                ((derivedPullback f).obj (DerivedCategory.Q.obj K), singleUnit X)) ≫
          ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).app
              ((derivedPullback f).obj (DerivedCategory.Q.obj K))).hom ≫
            (derivedPullbackNatTrans f).app K := by
  have hnatu := Stacks.RingedSpace.derivedTensorRightUnitor_naturality X
    ((derivedPullbackNatTrans f).app K)
  refine (eq_whisker (rightComparison_app_eq f K (unitComplex (Stacks.RingedSpace.toRingedSite Y)))
    _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _ ((Category.assoc _ _ _).trans (toTensor_pullbackUnit_comp f hδ K))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (eq_whisker
    (((Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map_comp _ _).symm.trans
    (congrArg (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
      (prod_comp_unitComparison f K).symm)) _).trans ?_
  refine (eq_whisker ((Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map_comp _ _)
    _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact whisker_eq _ hnatu

/-! ### The coherence, and the base case of [Stacks, Tag 08EU] -/

omit [(StacksDraft.KFlat.modulePullback f).Monoidal] in
/-- `pullbackTensorComparison_app_q_of_kFlat` at the unit complex, with the second entry of the
pair written as `singleUnit Y`. -/
private theorem pullbackTensorComparison_app_q_unit
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K) :
    (pullbackTensorComparison f).app (DerivedCategory.Q.obj K, singleUnit Y) =
      (Stacks.Cohomology.DerivedPullbackTensor.modelComparison f K
        (unitComplex (Stacks.RingedSpace.toRingedSite Y)) hK
        (Stacks.SheafOfModules.isKFlat_single_unit
          (Stacks.RingedSpace.toRingedSite Y).O)).hom :=
  pullbackTensorComparison_app_q_of_kFlat f K
    (unitComplex (Stacks.RingedSpace.toRingedSite Y)) hK
    (Stacks.SheafOfModules.isKFlat_single_unit (Stacks.RingedSpace.toRingedSite Y).O)

/-- **The right-unitor coherence of the comparison of [Stacks, Tag 079U], at the image of a
K-flat complex.**  This is the hypothesis `h` of
`Stacks.Cohomology.DerivedProjectionFormula.rightUnitorCoherence_of_kFlat`, with the unit
comparison supplied by `derivedUnitComparison`.

On a K-flat representative the comparison of [Stacks, Tag 079U] is
`Stacks.Cohomology.DerivedPullbackTensor.modelComparison`, the left comparison followed by the
inverse of the right one.  `leftComparison_app_unit_comp` and `rightComparison_app_unit_comp`
compute each of the two against the degreewise right unitor on `Y`, and the comparison
`Lf^*(QK) ⟶ Q(f^*K)` — invertible because `K` is K-flat — is cancelled at the end. -/
theorem rightUnitorCoherence_app_q (hδ : IsComparisonTensorator f)
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K) :
    (pullbackTensorComparison f).app (DerivedCategory.Q.obj K, singleUnit Y) ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
          ((𝟙 ((derivedPullback f).obj (DerivedCategory.Q.obj K)) ×ₘ
              (derivedUnitComparison f).hom) :
            (((derivedPullback f).obj (DerivedCategory.Q.obj K),
                (derivedPullback f).obj (singleUnit Y)) : _ × _) ⟶
              ((derivedPullback f).obj (DerivedCategory.Q.obj K), singleUnit X)) ≫
          ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).app
            ((derivedPullback f).obj (DerivedCategory.Q.obj K))).hom =
      (derivedPullback f).map
        ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso Y).app
          (DerivedCategory.Q.obj K)).hom := by
  have _ := isIso_derivedPullbackNatTrans_app f K hK
  have hRi := isIso_rightComparison_app f K (unitComplex (Stacks.RingedSpace.toRingedSite Y)) hK
    (Stacks.SheafOfModules.isKFlat_single_unit (Stacks.RingedSpace.toRingedSite Y).O)
  have hR := rightComparison_app_unit_comp f hδ K
  have hL := leftComparison_app_unit_comp f K
  refine (cancel_mono ((derivedPullbackNatTrans f).app K)).1 ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _ (Category.assoc _ _ _)).trans ?_
  refine (eq_whisker (pullbackTensorComparison_app_q_unit f K hK) _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _
    ((whisker_eq _ hR.symm).trans (IsIso.inv_hom_id_assoc (I := hRi) _ _))).trans ?_
  exact hL

/-- **[Stacks, Tag 08EU] at `K = 𝒪_Y[0]`, with the right-unitor coherence of [Stacks, Tag 079U]
discharged.**  For an arbitrary morphism of ringed spaces `f : X ⟶ Y` and an arbitrary `E` in
`D(𝒪_X)`, the derived projection-formula morphism

`Rf_*E ⊗^𝐋_{𝒪_Y} 𝒪_Y ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*𝒪_Y)`

is an isomorphism, granted only a monoidal structure on `f^*` whose oplax tensorator is the
comparison of [Stacks, Tag 01CD].  Both right unitors, the naturality of the one on `X`, the
unit comparison and the right-unitor coherence of [Stacks, Tag 079U] are supplied. -/
theorem isIso_projectionFormulaMap_unitObject_of_monoidal (hδ : IsComparisonTensorator f)
    (E : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))) :
    IsIso (projectionFormulaMap f E (singleUnit Y)) :=
  isIso_projectionFormulaMap_unitObject_of_kFlat f (derivedUnitComparison f)
    (fun K hK => rightUnitorCoherence_app_q f hδ K hK) E

end Monoidal

end Stacks.Cohomology.DerivedProjectionFormula

end
