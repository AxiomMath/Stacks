module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian

/-!
# Direct sums of differential graded modules

Let `R` be a sheaf of rings on a site `(C, J)` and let `A` be a sheaf of differential graded
`R`-algebras. The category of right differential graded `A`-modules has arbitrary direct sums,
and forgetting the differential takes them to the direct sums of the underlying graded modules.

A direct sum is formed degreewise on the underlying sheaves of modules, with componentwise
differential and action: its underlying graded module is `SheafOfModules.GradedModule.directSum`,
its differential is the morphism that the universal property of that degreewise coproduct
produces from the differentials of the summands, and its action is the one the graded direct sum
already carries.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.directSum` is the direct sum of a family of right
  differential graded modules, and `SheafOfModules.DifferentialGradedModule.directSumι` the
  inclusion of a summand.

## Main results

* `SheafOfModules.DifferentialGradedModule.hasCoproducts`: right differential graded modules
  over a sheaf of differential graded algebras admit arbitrary direct sums.
* `SheafOfModules.DifferentialGradedModule.directSumIsColimit` says that `directSum` with its
  inclusions is a coproduct.
* `SheafOfModules.DifferentialGradedModule.coproductIsColimit_graded` identifies the underlying
  graded coproduct cocone of an arbitrary chosen coproduct.
* `SheafOfModules.DifferentialGradedModule.coproductIsColimit_degree` gives the universal
  property of the components of the chosen coproduct injections in each degree, so that it can
  be used to descend homogeneous data.

## Implementation notes

Categorical coproducts express the direct sums of the source. They are formed degreewise on the
underlying sheaves of modules, with componentwise differentials and actions, and the degreewise
universal property is the coproduct-preservation of the homogeneous-component functor
`SheafOfModules.GradedModule.pieceFunctor_preservesCoproducts`. Forgetting the differential is
already known to commute with all colimits — it is a left adjoint, by
`SheafOfModules.forgetToGradedModule_preservesColimitsOfSize` — so no compatibility of the
coproduct with that functor has to be proved here, and `coproductIsColimit_graded` is only a
naming of what preservation gives.

The base is an arbitrary sheaf of rings on an arbitrary site rather than the structure sheaf of a
ringed site; a ringed site `X` is the case `R := X.ringSheaf`. The universes of the site, the
ring, the algebra pieces and the module pieces are independent, and the index type of a direct
sum lies in the module universe. That is forced rather than chosen: `SheafOfModules.{m} R` has
colimits only of shapes small relative to `m`, so a direct sum indexed by a larger type does not
exist.

Two sheafification hypotheses, `HasWeakSheafify J AddCommGrpCat.{m}` and
`J.WEqualsLocallyBijective AddCommGrpCat.{m}`, are taken as instance-implicit hypotheses on
everything that mentions a direct sum. They are exactly the conditions under which the
degreewise direct sum of graded modules exists at all, and they are needed because a coproduct
of sheaves of modules has no description on sections: it is the sheafification of the sectionwise
direct sum. They are inherited verbatim from `SheafOfModules.GradedModule.hasCoproducts`, and
nothing further is assumed; `HasSheafify J AddCommGrpCat.{m}` implies the first of them.

The only field of a differential graded module that does not follow from the universal property
of the degreewise coproduct is the Leibniz rule, because the action is a map on *sections* and a
section of a coproduct of sheaves is only *locally* a finite sum of images of the injections.
That locality is supplied by `Stacks.eq_of_forall_lift`: the two sides of the Leibniz rule are
compared after restriction along a local lift to the sectionwise direct sum, where the identity
is a `DirectSum.induction_on` away from the Leibniz rule of a single summand.

`SheafOfModules.forgetToGradedModule` and the constructions below are given a file-local
`implicit_reducible` attribute. Under Lean 4.34 the identification of
`((forgetToGradedModule A).obj M).piece n` with `M.complex.X n`, which is definitional, is
hidden from the transparency at which `rw` checks that a term is well typed, and without the
attribute every rewrite on a composite of a differential of a summand with an inclusion fails.
This is the same remedy as the `@[reducible]` on `AlgebraicGeometry.compatibleOpensDiagram`, and
it is preferred to weakening the transparency check globally with a file-level `set_option`.

`directSum`, `directSumι` and `directSumIsColimit` are `@[no_expose]`: a public definition whose
body is exposed may not mention a `private` declaration, and the plumbing of the construction is
private. What a consumer needs of them is `directSumIsColimit` together with
`coproductIsColimit_degree`, neither of which requires the body.

## References

* [Stacks Project, Tag 0FRJ](https://stacks.math.columbia.edu/tag/0FRJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules

namespace DifferentialGradedModule

attribute [local instance low] SheafOfModules.decidableEqIndex
attribute [local implicit_reducible] SheafOfModules.forgetToGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R}
  [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  {ι : Type m} (M : ι → DifferentialGradedModule.{t, a, m} A)

/-- The family of underlying graded modules of a family of differential graded modules. -/
private noncomputable abbrev gradedFamily : ι → GradedModule.{t, a, m} A.toGradedAlgebra :=
  fun k ↦ (forgetToGradedModule A).obj (M k)

/-- The degreewise direct sum of the underlying graded modules. -/
private noncomputable abbrev gradedSum : GradedModule.{t, a, m} A.toGradedAlgebra :=
  GradedModule.directSum (gradedFamily M)

/-- The inclusion of one summand into the degreewise direct sum of the underlying graded
modules. -/
private noncomputable abbrev gradedSumι (k : ι) : gradedFamily M k ⟶ gradedSum M :=
  GradedModule.directSumι (gradedFamily M) k

/-- The canonical map from the sectionwise direct sum onto a homogeneous piece of the graded
direct sum. -/
private noncomputable abbrev toSum (n : ℤ) (U : Cᵒᵖ) :
    (DirectSum ι fun k ↦ ((gradedFamily M k).piece n).val.obj U) →+
      ((gradedSum M).piece n).val.obj U :=
  GradedModule.toSheafifyDirectSum (gradedFamily M) n U

/-- The differential of the direct sum, induced on each homogeneous piece by the universal
property of the degreewise coproduct. -/
private noncomputable def diff (n : ℤ) : (gradedSum M).piece n ⟶ (gradedSum M).piece (n + 1) :=
  GradedModule.directSumPieceDesc (gradedFamily M) n ((gradedSum M).piece (n + 1))
    fun k ↦ (M k).complex.d n (n + 1) ≫ (gradedSumι M k).app (n + 1)

private theorem ι_comp_diff (k : ι) (n : ℤ) :
    (gradedSumι M k).app n ≫ diff M n
      = (M k).complex.d n (n + 1) ≫ (gradedSumι M k).app (n + 1) :=
  GradedModule.directSumι_desc (gradedFamily M) n _ _ k

/-- Two maps out of a piece of the graded direct sum are equal if they agree on every summand. -/
private theorem gradedSum_piece_hom_ext {n : ℤ} {X : SheafOfModules.{m} R}
    {f g : (gradedSum M).piece n ⟶ X}
    (h : ∀ k, (gradedSumι M k).app n ≫ f = (gradedSumι M k).app n ≫ g) : f = g :=
  Cofan.IsColimit.hom_ext (GradedModule.directSumPieceIsColimit (gradedFamily M) n) _ _ h

private theorem diff_comp_diff (n : ℤ) : diff M n ≫ diff M (n + 1) = 0 := by
  refine gradedSum_piece_hom_ext M fun k ↦ ?_
  rw [comp_zero, ← Category.assoc, ι_comp_diff, Category.assoc, ι_comp_diff,
    ← Category.assoc, HomologicalComplex.d_comp_d, zero_comp]

/-- The underlying cochain complex of the direct sum. -/
private noncomputable def sumComplex : CochainComplex (SheafOfModules.{m} R) ℤ :=
  CochainComplex.of (gradedSum M).piece (diff M) (diff_comp_diff M)

attribute [local implicit_reducible] diff sumComplex
private theorem homSections_diff_ι (k : ι) (n : ℤ) (U : Cᵒᵖ)
    (x : ((M k).complex.X n).val.obj U) :
    homSections (diff M n) U (homSections ((gradedSumι M k).app n) U x)
      = homSections ((gradedSumι M k).app (n + 1)) U
          (homSections ((M k).complex.d n (n + 1)) U x) :=
  homSections_congr (ι_comp_diff M k n) U x

private theorem toSum_of (n : ℤ) (U : Cᵒᵖ) (k : ι)
    (x : ((gradedFamily M k).piece n).val.obj U) :
    toSum M n U (DirectSum.of (fun l ↦ ((gradedFamily M l).piece n).val.obj U) k x)
      = homSections ((gradedSumι M k).app n) U x :=
  GradedModule.toSheafifyDirectSum_of (gradedFamily M) n U k x

private theorem isLocallySurjective_toDirectSumPiece (n : ℤ) :
    PresheafOfModules.IsLocallySurjective J (GradedModule.toDirectSumPiece (gradedFamily M) n) :=
  inferInstanceAs (PresheafOfModules.IsLocallySurjective J
    ((GradedModule.preDirectSum (gradedFamily M)).toSheafifyPiece n))

private theorem ι_map_smul (k : ι) (n i : ℤ) (U : Cᵒᵖ)
    (x : ((M k).complex.X n).val.obj U) (y : (A.complex.X i).val.obj U) :
    (gradedSum M).smul n i U (homSections ((gradedSumι M k).app n) U x) y
      = homSections ((gradedSumι M k).app (n + i)) U (((M k).mul n i).app U x y) :=
  ((gradedSumι M k).map_smul n i U x y).symm

private theorem homSections_ι_castHom (k : ι) {p q : ℤ} (h : p = q) (U : Cᵒᵖ)
    (z : ((M k).complex.X p).val.obj U) :
    homSections ((gradedSumι M k).app q) U (castHom (M k).complex.X h U z)
      = castHom (gradedSum M).piece h U (homSections ((gradedSumι M k).app p) U z) := by
  subst h; rfl

omit [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}] in
/-- The Leibniz rule of one summand, with its transports of degree written through
`SheafOfModules.castHom`. -/
private theorem summand_leibniz (k : ι) (n i : ℤ) (U : Cᵒᵖ)
    (x : ((M k).complex.X n).val.obj U) (y : (A.complex.X i).val.obj U) :
    homSections ((M k).complex.d (n + i) (n + i + 1)) U (((M k).mul n i).app U x y)
      = castHom (M k).complex.X (add_right_comm n 1 i) U
          (((M k).mul (n + 1) i).app U (homSections ((M k).complex.d n (n + 1)) U x) y)
        + (Int.negOnePow n : ℤ) • castHom (M k).complex.X (add_assoc n i 1).symm U
            (((M k).mul n (i + 1)).app U x (homSections (A.complex.d i (i + 1)) U y)) := by
  rw [castHom_apply, castHom_apply]
  exact (M k).leibniz n i U x y

/-- The Leibniz rule of the direct sum, on a section coming from the sectionwise direct sum.
Such a section is a finite sum of images of the inclusions, so the identity reduces to the
Leibniz rule of a single summand. -/
private theorem leibniz_toSum (n i : ℤ) (U : Cᵒᵖ)
    (p : DirectSum ι fun k ↦ ((gradedFamily M k).piece n).val.obj U)
    (y : (A.complex.X i).val.obj U) :
    homSections (diff M (n + i)) U ((gradedSum M).smul n i U (toSum M n U p) y)
      = castHom (gradedSum M).piece (add_right_comm n 1 i) U
          ((gradedSum M).smul (n + 1) i U (homSections (diff M n) U (toSum M n U p)) y)
        + (Int.negOnePow n : ℤ) • castHom (gradedSum M).piece (add_assoc n i 1).symm U
            ((gradedSum M).smul n (i + 1) U (toSum M n U p)
              (homSections (A.complex.d i (i + 1)) U y)) := by
  induction p using DirectSum.induction_on with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply, smul_zero, add_zero]
  | of k x =>
    have h := congrArg (homSections ((gradedSumι M k).app (n + i + 1)) U)
      (summand_leibniz M k n i U x y)
    rw [map_add, map_zsmul, homSections_ι_castHom, homSections_ι_castHom] at h
    rw [toSum_of, ι_map_smul, homSections_diff_ι, homSections_diff_ι, ι_map_smul, ι_map_smul]
    exact h
  | add p p' hp hp' =>
    simp only [map_add, AddMonoidHom.add_apply, smul_add, hp, hp']
    abel

/-- The Leibniz rule of the direct sum. Both sides agree after restriction along every local
lift of the module section to the sectionwise direct sum, and the target is a sheaf. -/
private theorem leibniz_sections (n i : ℤ) (U : Cᵒᵖ)
    (x : ((gradedSum M).piece n).val.obj U) (y : (A.complex.X i).val.obj U) :
    homSections (diff M (n + i)) U ((gradedSum M).smul n i U x y)
      = castHom (gradedSum M).piece (add_right_comm n 1 i) U
          ((gradedSum M).smul (n + 1) i U (homSections (diff M n) U x) y)
        + (Int.negOnePow n : ℤ) • castHom (gradedSum M).piece (add_assoc n i 1).symm U
            ((gradedSum M).smul n (i + 1) U x (homSections (A.complex.d i (i + 1)) U y)) := by
  have := isLocallySurjective_toDirectSumPiece M n
  refine Stacks.eq_of_forall_lift ((gradedSum M).piece (n + i + 1)).isSheaf.isSeparated
    (GradedModule.toDirectSumPiece (gradedFamily M) n) x _ _ ?_
  intro V f p hp
  have key := leibniz_toSum M n i V p ((A.complex.X i).val.map f y)
  rw [show toSum M n V p = ((gradedSum M).piece n).val.map f x from hp] at key
  rw [homSections_naturality, (gradedSum M).smul_naturality, map_add, map_zsmul_sections,
    castHom_naturality, castHom_naturality, (gradedSum M).smul_naturality,
    (gradedSum M).smul_naturality, homSections_naturality, homSections_naturality]
  exact key

/-- **The direct sum of a family of right differential graded modules** over a sheaf of
differential graded algebras: degreewise the direct sum of the underlying sheaves of modules,
with componentwise differential and action. -/
@[no_expose]
noncomputable def directSum : DifferentialGradedModule.{t, a, m} A where
  complex := sumComplex M
  mul n i := GradedModule.smulBil (gradedSum M) n i
  mul_assoc := (gradedSum M).smul_mul
  mul_one := (gradedSum M).smul_one
  leibniz n i U x y := by
    rw [show (sumComplex M).d (n + i) (n + i + 1) = diff M (n + i) from
        CochainComplex.of_d _ _ (n + i),
      show (sumComplex M).d n (n + 1) = diff M n from CochainComplex.of_d _ _ n,
      ← castHom_apply, ← castHom_apply]
    exact leibniz_sections M n i U x y

attribute [local implicit_reducible] directSum

/-- The inclusion of one summand into the direct sum. -/
@[no_expose]
noncomputable def directSumι (k : ι) : M k ⟶ directSum M where
  toHomologicalComplex :=
    { f := fun n ↦ (gradedSumι M k).app n
      comm' := fun n j hnj ↦ by
        obtain rfl : n + 1 = j := hnj
        rw [show (directSum M).complex.d n (n + 1) = diff M n from CochainComplex.of_d _ _ n]
        exact ι_comp_diff M k n }
  map_mul := (gradedSumι M k).map_smul

private noncomputable def gradedDesc (s : Cofan M) :
    gradedSum M ⟶ (forgetToGradedModule A).obj s.pt :=
  Cofan.IsColimit.desc (GradedModule.directSumIsColimit (gradedFamily M))
    fun k ↦ (forgetToGradedModule A).map (s.inj k)

private theorem ι_comp_gradedDesc (s : Cofan M) (k : ι) (n : ℤ) :
    (gradedSumι M k).app n ≫ (gradedDesc M s).app n = (s.inj k).toHomologicalComplex.f n :=
  congrArg (fun φ : gradedFamily M k ⟶ (forgetToGradedModule A).obj s.pt ↦ φ.app n)
    (Cofan.IsColimit.fac (GradedModule.directSumIsColimit (gradedFamily M)) _ k)

attribute [local implicit_reducible] gradedDesc

private noncomputable def desc (s : Cofan M) : directSum M ⟶ s.pt where
  toHomologicalComplex :=
    { f := fun n ↦ (gradedDesc M s).app n
      comm' := fun n j hnj ↦ by
        obtain rfl : n + 1 = j := hnj
        refine gradedSum_piece_hom_ext M fun k ↦ ?_
        rw [show (directSum M).complex.d n (n + 1) = diff M n from CochainComplex.of_d _ _ n,
          ← Category.assoc, ι_comp_gradedDesc, ← Category.assoc, ι_comp_diff, Category.assoc,
          ι_comp_gradedDesc]
        exact (s.inj k).toHomologicalComplex.comm n (n + 1) }
  map_mul := (gradedDesc M s).map_smul

/-- **The direct sum is the coproduct**: `directSum` with the inclusions `directSumι` is a
coproduct of the family in the category of right differential graded modules. -/
@[no_expose]
noncomputable def directSumIsColimit : IsColimit (Cofan.mk (directSum M) (directSumι M)) :=
  Cofan.IsColimit.mk _ (desc M) (fun s k ↦ Hom.ext fun n ↦ ι_comp_gradedDesc M s k n)
    fun s g hg ↦ Hom.ext fun n ↦ by
      refine Cofan.IsColimit.hom_ext
        (GradedModule.directSumPieceIsColimit (gradedFamily M) n) _ _ fun k ↦ ?_
      exact (congrArg (fun φ : M k ⟶ s.pt ↦ φ.toHomologicalComplex.f n) (hg k)).trans
        (ι_comp_gradedDesc M s k n).symm

section Coproducts

variable (A)

/-- **Right differential graded modules over a sheaf of differential graded algebras admit
arbitrary direct sums**, formed degreewise on the underlying sheaves of modules. -/
instance hasCoproducts : HasCoproducts.{m} (DifferentialGradedModule.{t, a, m} A) :=
  hasCoproducts_of_colimit_cofans (fun {_} M ↦ Cofan.mk (directSum M) (directSumι M))
    fun {_} M ↦ directSumIsColimit M

/-- Forgetting the differential takes a coproduct cocone of a family of right differential
graded modules to a coproduct of the underlying graded modules. -/
noncomputable def coproductIsColimit_graded :
    IsColimit (Cofan.mk ((forgetToGradedModule A).obj (∐ M))
      fun k ↦ (forgetToGradedModule A).map (Sigma.ι M k)) :=
  isColimitOfHasCoproductOfPreservesColimit (forgetToGradedModule A) M

/-- A coproduct cocone of a family of right differential graded modules is, in each degree, a
coproduct of the degree-`n` sheaves of modules of the summands. The injections are the
components of the chosen coproduct injections, so this universal property can be used to descend
homogeneous data. -/
noncomputable def coproductIsColimit_degree (n : ℤ) :
    IsColimit (Cofan.mk ((∐ M).complex.X n)
      fun k ↦ (Sigma.ι M k).toHomologicalComplex.f n) :=
  isColimitCofanMkObjOfIsColimit (GradedModule.pieceFunctor A.toGradedAlgebra n) _ _
    (coproductIsColimit_graded A M)

end Coproducts

end DifferentialGradedModule

end SheafOfModules
