module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.DerivedColimitOnKProjective
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.EvaluationToDerivedColimit
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CosimplicialResolutionOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitPointResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.MooreCochainComplex
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek computed by a point resolution, in the derived category

Let `C` be a small category with the chaotic topology, let `B` be a ring, so that a `B̲`-module is
a diagram `ℱ` of `B`-modules on `Cᵒᵖ`, and let `U_•` be a cosimplicial object of `C` such that
every simplicial set `Mor_C(U_•, W)` is homotopy equivalent to a singleton. This file proves the
**derived** form of [Stacks, Tag 08PT] at module coefficients:

`Q(ℱ(U_•)) ≅ Lπ_!(ℱ)` in `D(B)`,

where `ℱ(U_•)` is the Moore complex of the simplicial `B`-module obtained by evaluating `ℱ` on
`U_•`, read as a cochain complex over `ℤ` with the simplicial degree `n` in cohomological degree
`-n`, and `Lπ_!` is the total left derived functor of the colimit over `Cᵒᵖ`.

The degreewise statement — `L_nπ_!(ℱ) = H_n(ℱ(U_•))` for each `n` — is
`Stacks.ChaoticSite.ModuleValued.moduleLeftDerivedColimitNatIso`, and it does *not* give the
isomorphism in `D(B)`: a complex is not determined by its cohomology. What produces the derived
statement is the comparison of the two filtrations of the double complex obtained by evaluating a
projective resolution `P^• ⟶ ℱ` on `U_•`, and that is what is carried out here.

## The double complex

For a cochain complex `P^•` of diagrams of `B`-modules, bounded above by `0`, let

`Z^{p,q} = (P^p(U_•))^q`,

the extended Moore complex of `P^p(U_•)` in the second variable. It vanishes for `p > 0` and for
`q > 0`, so it lies in the third quadrant and has a total complex
(`StacksDraft.TotalComplexQuasiIso.hasTotal_of_upperBound`). Its two filtrations are compared by
the two halves of [Stacks, Tag 0133] for double complexes bounded above:

* **columns.** The column `p` is the extended Moore complex of `P^p(U_•)`. For `P^p` projective it
  is a resolution of `colim P^p`: its homology vanishes in positive simplicial degrees
  (`isZero_moduleCosimplicialHomology_projective_succ`) and in degree zero the colimit injection
  at `U_0` is a cokernel of the degree-one differential (`moduleColimitι_isColimit`). So the
  augmentation `Z ⟶ (colim P^•)[0]` is a columnwise quasi-isomorphism and
  `StacksDraft.TotalComplexQuasiIso.quasiIso_total_map_of_upperBound` gives
  `Tot(Z) ≃ colim P^•`.
* **rows.** The row `q` is `P^•(U_{-q})`, which is a resolution of `ℱ(U_{-q})` because evaluation
  at an object of the site is exact. So the augmentation `Z ⟶ ℱ(U_•)[0]` — the double complex of
  the single complex `ℱ` — is a rowwise quasi-isomorphism and
  `StacksDraft.TotalComplexQuasiIso.quasiIso_total_map_of_upperBound_flip` gives
  `Tot(Z) ≃ ℱ(U_•)`.

Finally `Lπ_!` of a K-projective complex is the degreewise colimit
(`Stacks.CategoryHomology.totalDerivedColimitObjIsoOfIsKProjective`), and a bounded above complex
of projectives is K-projective, so `Lπ_!(ℱ) = Lπ_!(P^•) = Q(colim P^•) = Q(ℱ(U_•))`.

## Main definitions

* `Stacks.ChaoticSite.ModuleValued.mooreCochainComplex`: the Moore complex of `ℱ(U_•)` as a
  cochain complex over `ℤ`, functorially in `ℱ`.
* `Stacks.ChaoticSite.ModuleValued.mooreCochainAugmentation`: its augmentation to
  `(colim ℱ)[0]`.
* `Stacks.ChaoticSite.ModuleValued.mooreBicomplex`: the double complex above.

## Main results

* `Stacks.ChaoticSite.ModuleValued.quasiIso_mooreCochainAugmentation`: for a projective diagram
  the extended Moore complex of `ℱ(U_•)` is a resolution of `colim ℱ`.
* `Stacks.ChaoticSite.ModuleValued.quasiIso_mooreBicomplexColumnTotalMap` and
  `Stacks.ChaoticSite.ModuleValued.quasiIso_mooreBicomplexRowTotalMap`: the two filtrations of the
  double complex.
* `Stacks.ChaoticSite.ModuleValued.mooreCochainQIsoDerivedColimitOfResolution`: the
  comparison for a given projective resolution.
* `Stacks.ChaoticSite.ModuleValued.mooreCochainQIsoDerivedColimit`: **the derived form of
  [Stacks, Tag 08PT] at module coefficients** — `Q(ℱ(U_•)) ≅ Lπ_!(ℱ)` in `D(B)`.

## Implementation notes

**The Moore-cochain development is not written out here.** The extended Moore complex, its
augmentation to `(colim ℱ)[0]`, the double complex of a complex of presheaves and the first of its
two filtrations are stated once for an arbitrary abelian category of coefficients in
`StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.MooreCochainComplex`, and this module
instantiates them at `ModuleCat B`. Only the two inputs that module coefficients supply enter
here: the positive-degree vanishing of [Stacks, Tag 08Q9] on a projective diagram and the
cokernel presentation of the colimit injection at `U_0`.

**What is proved and what is not.** The isomorphism is produced for each diagram `ℱ`; it is *not*
shown to be natural in `ℱ`. Naturality is not available from this argument: the comparison is
built from a projective resolution of `ℱ`, and no projective resolution is functorial in `ℱ`.
Obtaining a natural isomorphism would need a canonical map between the two sides — the derived
form of the canonical map of [Stacks, Tag 08Q6] — which is not constructed here. The object-level
statement is what [Stacks, Tag 08PU] in `D(B)` consumes, since there it is applied to one sheaf.

**The K-projective computation is imported.** That `Lπ_!` is the degreewise colimit on a
K-projective complex is `Stacks.CategoryHomology.totalDerivedColimitObjIsoOfIsKProjective`, and
the initiality of a K-projective complex that it rests on is
`Stacks.Homology.isInitialStructuredArrowOfIsKProjective`; both are stated for an arbitrary
abelian category, and the first is the copy whose naturality in the complex is also available
(`Stacks.CategoryHomology.totalDerivedColimitObjIsoOfIsKProjective_naturality`). The same
initiality argument is still written out a second time in
`StacksFrontier/Homology/TorAmplitude/Comparison.lean`, for termwise tensoring, where it carries no
`public` marker and so cannot be reused; that copy should be replaced by the general statement.

**Why the extended Moore complex.** The tools for [Stacks, Tag 0133] are stated for double
complexes indexed by `ℤ × ℤ` with cochain conventions in both directions, so the Moore complex —
a chain complex indexed by `ℕ` — is placed in cohomological degrees `≤ 0` along
`ComplexShape.embeddingUpIntLE 0`. This is the same reindexing by which
`CommAlgCat.standardResolutionModuleLeftDerivedCotangentComplexIso` compares the Moore complex
with the cotangent complex, so the two statements compose.

**Why the rows need no homology computation.** In the row direction the identification of the
row `q` of the double complex with `P^•(U_{-q})` is an equality of complexes, not merely an
isomorphism: `HomologicalComplex₂.flip` and `Functor.mapHomologicalComplex` of a composite are
both defined degreewise. So the rowwise quasi-isomorphism is `quasiIso_map_of_preservesHomology`
for the exact functor `ℱ ↦ ℱ(U_•)^q`, which is evaluation at `U_{-q}` for `q ≤ 0` and zero for
`q > 0`.

## References

* [Stacks Project, Tag 08PT](https://stacks.math.columbia.edu/tag/08PT)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Tag 0646](https://stacks.math.columbia.edu/tag/0646)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.CategoryHomology StacksDraft.TotalComplexQuasiIso

namespace Stacks.ChaoticSite.ModuleValued

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### The Moore complex of `ℱ(U_•)` as a cochain complex over `ℤ` -/

section MooreCochain

variable {C : Type u} [SmallCategory C] {B : Type u} [Ring B] (U : CosimplicialObject C)

/-- **The Moore complex of `ℱ(U_•)` read as a cochain complex over `ℤ`**, the simplicial degree
`n` sitting in cohomological degree `-n`. This is
`Stacks.ChaoticSite.GeneralValued.mooreCochainComplex` at module coefficients: the reindexing
along `ComplexShape.embeddingUpIntLE 0` of
`Stacks.ChaoticSite.ModuleValued.moduleCosimplicialMooreComplex`. -/
abbrev mooreCochainComplex :
    (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ CochainComplex (ModuleCat.{u} B) ℤ :=
  GeneralValued.mooreCochainComplex U (ModuleCat.{u} B)

end MooreCochain

/-! ### The augmentation of the extended Moore complex -/

section Augmentation

variable {C : Type u} [SmallCategory C] {B : Type u} [Ring B] (U : CosimplicialObject C)
  (F : Cᵒᵖ ⥤ ModuleCat.{u} B)

/-- **The augmentation `ℱ(U_•) ⟶ (colim ℱ)[0]`**, as a natural transformation of functors of the
diagram `ℱ`: in degree zero it is the colimit injection at `U_0`. This is
`Stacks.ChaoticSite.GeneralValued.mooreCochainAugmentation` at module coefficients. -/
abbrev mooreCochainAugmentation :
    mooreCochainComplex U ⟶
      (colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B) ⋙
        HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0 :=
  GeneralValued.mooreCochainAugmentation U

/-- **For a projective diagram of `B`-modules the extended Moore complex of `ℱ(U_•)` is a
resolution of `colim ℱ`**, when `U_•` is a point resolution. This is the columnwise input to the
comparison of the two filtrations of the double complex. The general statement
`Stacks.ChaoticSite.GeneralValued.quasiIso_mooreCochainAugmentation` is fed here with the two
inputs module coefficients supply: the positive-degree vanishing
`Stacks.ChaoticSite.ModuleValued.isZero_moduleCosimplicialHomology_projective_succ` of
[Stacks, Tag 08Q9] and the cokernel presentation
`Stacks.ChaoticSite.ModuleValued.moduleColimitι_isColimit` of the colimit injection at `U_0`. -/
lemma quasiIso_mooreCochainAugmentation (hU : IsPointResolution U) [Projective F] :
    QuasiIso ((mooreCochainAugmentation U).app F) :=
  GeneralValued.quasiIso_mooreCochainAugmentation U F
    (fun n => isZero_moduleCosimplicialHomology_projective_succ U hU n F)
    (moduleColimitι_isColimit U hU F)

end Augmentation

/-! ### Total complexes of isomorphic and of concentrated double complexes -/

section TotalAux

variable {A : Type*} [Category* A] [Abelian A]

/-- **An isomorphism of double complexes induces an isomorphism of total complexes.** This is
`HomologicalComplex₂.total.mapIso` read as invertibility of `HomologicalComplex₂.total.map`,
which is the form the comparisons below consume. -/
lemma isIso_total_map_of_isIso
    {Z Z' : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)} (f : Z ⟶ Z')
    [IsIso f] [Z.HasTotal (ComplexShape.up ℤ)] [Z'.HasTotal (ComplexShape.up ℤ)] :
    IsIso (HomologicalComplex₂.total.map f (ComplexShape.up ℤ)) :=
  (HomologicalComplex₂.total.mapIso (asIso f) (ComplexShape.up ℤ)).isIso_hom

/-- **The total complex of a double complex concentrated in the column `0` is that column.**
This is `StacksDraft.TotalComplexQuasiIso.totalSingleColumnUnit` at `a = 0`, where the shift by
`-0` it carries is the identity. -/
def totalSingleColumnZeroIso (W : CochainComplex A ℤ)
    [(singleColumn W 0).HasTotal (ComplexShape.up ℤ)] :
    W ≅ (singleColumn W 0).total (ComplexShape.up ℤ) :=
  have := isIso_totalSingleColumnUnit W 0
  ((CategoryTheory.shiftFunctorZero (CochainComplex A ℤ) ℤ).app W).symm ≪≫
    asIso (totalSingleColumnUnit W 0)

end TotalAux

/-! ### The double complex of a resolution evaluated on the point resolution -/

section Bicomplex

variable {C : Type u} [SmallCategory C] {B : Type u} [Ring B] (U : CosimplicialObject C)
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ)

/-- **The double complex obtained by evaluating a complex `P^•` of diagrams of `B`-modules on the
cosimplicial object `U_•`**: its column `p` is the extended Moore complex of `P^p(U_•)` and its
row `q` is `P^•(U_{-q})`. -/
abbrev mooreBicomplex :
    HomologicalComplex₂ (ModuleCat.{u} B) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  ((mooreCochainComplex U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

/-! #### The columns -/

/-- **The columnwise augmentation of the double complex**, `Z ⟶ (colim P^•)[0]`: in each column
it is the augmentation `P^p(U_•) ⟶ (colim P^p)[0]` of the extended Moore complex. -/
abbrev mooreBicomplexColumnMap :
    mooreBicomplex U P ⟶
      singleRowZero
        (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  (NatTrans.mapHomologicalComplex (mooreCochainAugmentation U) (ComplexShape.up ℤ)).app P

/-- **The first filtration of the double complex**: for `P^•` a bounded above complex of
projective diagrams the columnwise augmentation is a quasi-isomorphism on total complexes, so
`Tot(Z) ≃ colim P^•`. This is [Stacks, Tag 0133] for double complexes bounded above, with the
hypothesis on the columns. -/
lemma quasiIso_mooreBicomplexColumnTotalMap (hU : IsPointResolution U)
    [P.IsStrictlyLE 0] [∀ n, Projective (P.X n)] :
    QuasiIso (HomologicalComplex₂.total.map (mooreBicomplexColumnMap U P)
      (ComplexShape.up ℤ)) :=
  GeneralValued.quasiIso_mooreBicomplexColumnTotalMap U P
    fun p => quasiIso_mooreCochainAugmentation U (P.X p) hU

/-! #### The rows -/

variable (F : Cᵒᵖ ⥤ ModuleCat.{u} B)

/-- **The rowwise augmentation of the double complex**, `Z ⟶ ℱ(U_•)[0]`: it is the double complex
of the resolution `ε : P^• ⟶ ℱ[0]`. -/
abbrev mooreBicomplexRowMap
    (ε : P ⟶ (HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj F) :
    mooreBicomplex U P ⟶
      mooreBicomplex U
        ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj F) :=
  ((mooreCochainComplex U).mapHomologicalComplex (ComplexShape.up ℤ)).map ε

/-- **The second filtration of the double complex**: a quasi-isomorphism `P^• ⟶ ℱ[0]` of bounded
above complexes of diagrams is a quasi-isomorphism on total complexes, so `Tot(Z) ≃ ℱ(U_•)`. This
is [Stacks, Tag 0133] for double complexes bounded above, with the hypothesis on the rows; the
rows are exact functors of the diagram, so no homology is computed. -/
lemma quasiIso_mooreBicomplexRowTotalMap [P.IsStrictlyLE 0]
    (ε : P ⟶ (HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj F)
    [QuasiIso ε] :
    QuasiIso (HomologicalComplex₂.total.map (mooreBicomplexRowMap U P F ε)
      (ComplexShape.up ℤ)) := by
  refine quasiIso_total_map_of_upperBound_flip (mooreBicomplexRowMap U P F ε) 0 0
    (fun p q hpq => ?_) (fun p q hpq => ?_) (fun q => ?_)
  · rcases hpq with hp | hq
    · exact Functor.map_isZero (HomologicalComplex.eval (ModuleCat.{u} B)
        (ComplexShape.up ℤ) q) (GeneralValued.isZero_mooreBicomplex_X U P p
          (CochainComplex.isZero_of_isStrictlyLE P 0 p hp))
    · exact GeneralValued.isZero_mooreBicomplex_X_X U P p q hq
  · rcases hpq with hp | hq
    · exact Functor.map_isZero (HomologicalComplex.eval (ModuleCat.{u} B)
        (ComplexShape.up ℤ) q) (GeneralValued.isZero_mooreBicomplex_X U _ p
          (CochainComplex.isZero_of_isStrictlyLE _ 0 p hp))
    · exact GeneralValued.isZero_mooreBicomplex_X_X U _ p q hq
  · have h : (flipHom (mooreBicomplexRowMap U P F ε)).f q =
        ((mooreCochainComplex U ⋙ HomologicalComplex.eval (ModuleCat.{u} B)
          (ComplexShape.up ℤ) q).mapHomologicalComplex (ComplexShape.up ℤ)).map ε := rfl
    rw [h]
    exact HomologicalComplex.quasiIso_map_of_preservesHomology ε
      (mooreCochainComplex U ⋙
        HomologicalComplex.eval (ModuleCat.{u} B) (ComplexShape.up ℤ) q)

end Bicomplex

/-! ### The derived form of Tag 08PT -/

section Derived

variable {C : Type u} [SmallCategory C] {B : Type u} [Ring B] (U : CosimplicialObject C)
  (F : Cᵒᵖ ⥤ ModuleCat.{u} B)

/-- **The extended Moore complex of `ℱ(U_•)` is the total complex of the double complex of a
resolution**, in the derived category: the comparison through the second filtration. -/
def mooreCochainQIsoTotal
    (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ) [P.IsStrictlyLE 0]
    (ε : P ⟶ (HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj F)
    [QuasiIso ε] :
    DerivedCategory.Q.obj ((mooreCochainComplex U).obj F) ≅
      DerivedCategory.Q.obj ((mooreBicomplex U P).total (ComplexShape.up ℤ)) :=
  let := hasTotal_singleColumn ((mooreCochainComplex U).obj F) (0 : ℤ)
  have _h1 : IsIso (HomologicalComplex₂.total.map
      ((HomologicalComplex.singleMapHomologicalComplex (mooreCochainComplex U)
        (ComplexShape.up ℤ) 0).app F).inv (ComplexShape.up ℤ)) :=
    isIso_total_map_of_isIso _
  have _h2 : QuasiIso (HomologicalComplex₂.total.map (mooreBicomplexRowMap U P F ε)
      (ComplexShape.up ℤ)) := quasiIso_mooreBicomplexRowTotalMap U P F ε
  DerivedCategory.Q.mapIso (totalSingleColumnZeroIso ((mooreCochainComplex U).obj F)) ≪≫
    DerivedCategory.Q.mapIso (asIso (HomologicalComplex₂.total.map
      ((HomologicalComplex.singleMapHomologicalComplex (mooreCochainComplex U)
        (ComplexShape.up ℤ) 0).app F).inv (ComplexShape.up ℤ))) ≪≫
    (asIso (DerivedCategory.Q.map (HomologicalComplex₂.total.map
      (mooreBicomplexRowMap U P F ε) (ComplexShape.up ℤ)))).symm

/-- **The total complex of the double complex is the degreewise colimit of the resolution**, in
the derived category: the comparison through the first filtration. -/
def totalQIsoColimOfResolution (hU : IsPointResolution U)
    (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ) [P.IsStrictlyLE 0]
    [∀ n, Projective (P.X n)] :
    DerivedCategory.Q.obj ((mooreBicomplex U P).total (ComplexShape.up ℤ)) ≅
      DerivedCategory.Q.obj
        (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  have _h1 : QuasiIso (HomologicalComplex₂.total.map (mooreBicomplexColumnMap U P)
      (ComplexShape.up ℤ)) := quasiIso_mooreBicomplexColumnTotalMap U P hU
  have _h2 : IsIso (totalSingleRowZeroUnit
      (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)) := isIso_totalSingleRowZeroUnit _
  asIso (DerivedCategory.Q.map (HomologicalComplex₂.total.map (mooreBicomplexColumnMap U P)
    (ComplexShape.up ℤ))) ≪≫
    (DerivedCategory.Q.mapIso (asIso (totalSingleRowZeroUnit
      (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)))).symm

/-- **The derived form of [Stacks, Tag 08PT] at module coefficients, for a given projective
resolution**: `Q(ℱ(U_•)) ≅ Lπ_!(ℱ)` in `D(B)`, where `Lπ_!` is the total left derived functor of
the colimit over `Cᵒᵖ` and `ℱ` is placed in degree zero.

The isomorphism is the composite of the two filtrations of the double complex of `P^•` evaluated
on `U_•` with the computation of `Lπ_!` on the K-projective complex `P^•`. -/
def mooreCochainQIsoDerivedColimitOfResolution (hU : IsPointResolution U)
    (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ) [P.IsStrictlyLE 0]
    [∀ n, Projective (P.X n)]
    (ε : P ⟶ (HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj F)
    [QuasiIso ε] :
    DerivedCategory.Q.obj ((mooreCochainComplex U).obj F) ≅
      (totalDerivedColimit C (ModuleCat.{u} B)).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj F)) :=
  have _hKP : P.IsKProjective := CochainComplex.isKProjective_of_projective P 0
  mooreCochainQIsoTotal U F P ε ≪≫ totalQIsoColimOfResolution U hU P ≪≫
    (Stacks.CategoryHomology.totalDerivedColimitObjIsoOfIsKProjective C
      (ModuleCat.{u} B) P).symm ≪≫
    (totalDerivedColimit C (ModuleCat.{u} B)).mapIso (asIso (DerivedCategory.Q.map ε))

/-- **The derived form of [Stacks, Tag 08PT] at module coefficients.** Let `C` be a small
category with the chaotic topology, `B` a ring, and `U_•` a cosimplicial object of `C` such that
every simplicial set `Mor_C(U_•, W)` is homotopy equivalent to a singleton. Then for every
diagram `ℱ` of `B`-modules on `Cᵒᵖ` — that is, every `B̲`-module on the chaotic site — the
extended Moore complex of the simplicial `B`-module `ℱ(U_•)` computes derived lower shriek:

`Q(ℱ(U_•)) ≅ Lπ_!(ℱ)` in `D(B)`.

Here `Lπ_!` is `Stacks.CategoryHomology.totalDerivedColimit`, the total left derived functor of
the colimit over `Cᵒᵖ`, which is `π_!` on the chaotic site by [Stacks, Tag 08PF]. The proof
compares the two filtrations of the double complex obtained by evaluating a projective resolution
of `ℱ` on `U_•`.

The isomorphism depends on the chosen projective resolution and is not asserted to be natural in
`ℱ`; see the implementation notes of this module. -/
@[stacks 08PT "derived form at module coefficients, for one module over the constant sheaf of \
  rings: the extended Moore complex of the evaluation on a point resolution is derived lower \
  shriek in D(B), derived lower shriek being the total left derived functor of the colimit over \
  the index category. Not asserted natural in the coefficient module"]
def mooreCochainQIsoDerivedColimit (hU : IsPointResolution U) :
    DerivedCategory.Q.obj ((mooreCochainComplex U).obj F) ≅
      (totalDerivedColimit C (ModuleCat.{u} B)).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj F)) :=
  let R := (ProjectiveResolutionLemma.statement3 (0 : ℤ)
    ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj F)
    inferInstance).choose
  have : ∀ n, Projective (R.complex.X n) := R.projective
  have : CochainComplex.IsStrictlyLE R.complex 0 := R.boundedAbove
  have : QuasiIso R.α := R.quasiIso
  mooreCochainQIsoDerivedColimitOfResolution U F hU R.complex R.α

end Derived

end Stacks.ChaoticSite.ModuleValued

end
