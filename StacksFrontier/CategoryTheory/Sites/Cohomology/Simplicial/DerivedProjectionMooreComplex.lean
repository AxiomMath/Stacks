module

public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOnBoundedResolutions
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.MooreTotalComplexGeneralCoefficients
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.SimplexMooreGeneralCoefficients
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.FibreInclusion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialSheafEquivalence
import StacksCore.Tactic.StacksAttribute

/-!
# `Lπ_!` of an abelian sheaf on `Δ × C` is its alternating-face-map complex

Let `(C, J)` be a small site, let `π : Δ × C ⥤ C` be the projection of Stacks 09D0 and let
`Δ × C` carry the topology `K = Stacks.SimplicialModules.projectionTopology C J` it inherits from
`(C, J)` along `π`. A sheaf of abelian groups `ℱ` on `Δ × C` *is* a simplicial abelian sheaf
`ℱ_•` on `C` (`Stacks.SimplicialModules.simplicialSheafEquivalence`), and Stacks 09D0 asserts
that the abelian derived lower shriek of Remark 09CY,

`Lπ_! : D(Ab(Δ × C)) ⥤ D(Ab(C))`,

carries `ℱ` to the *associated chain complex* `s(ℱ_•)` of Simplicial, Section 14.23 — that is, to
the alternating-face-map complex of the simplicial abelian sheaf `ℱ_•`.

This file proves that, in the form

`Stacks.SimplicialModules.derivedProjectionLowerShriekIsoMooreComplex`.

## Main results

* `Stacks.SimplicialModules.derivedProjectionLowerShriekIsoMooreComplex`: **Stacks 09D0.** For
  every abelian sheaf `ℱ` on `Δ × C`,
  `Lπ_!(ℱ[0]) ≅ s(ℱ_•)` in `D(Ab(C))`, where `s(ℱ_•)` is the extended Moore complex of the
  simplicial abelian sheaf `ℱ_•` that `ℱ` is.
* `Stacks.SimplicialModules.evaluationLeftAdjointObjIsoFreeSimplicial`: the value of the left
  adjoint of evaluation at `op m` is the free simplicial object `∐_{Mor_Δ(-, m)} Y` of
  `Stacks.ChaoticSite.SimplexValued.freeSimplicial`.
* `Stacks.SimplicialModules.fibreExtensionCompFibrewiseIso`: reading `(i_m)_!` fibrewise gives
  the left adjoint of evaluation in degree `m`.
* `Stacks.SimplicialModules.fibrewiseExtensionByZeroUnitAbIso`: the free abelian sheaf
  `j_{(m,U)!}ℤ` on a representable of `Δ × C`, read fibrewise, is the free simplicial object on
  `j_{U!}ℤ_U` at `m`.
* `Stacks.SimplicialModules.quasiIso_mooreCochainAugmentation_fibrewise`: **the Moore
  augmentation of every term of a resolution of Stacks 06XX is a quasi-isomorphism** — the one
  hypothesis that `Stacks.ChaoticSite.GeneralValued.mooreCochainQIsoColimOfResolution` carries.

## How the theorem is assembled

The proof is the one the source gives: Lemmas 21.40.2 and 21.39.7, which here are the two
inputs
`Stacks.SimplicialModules.abelianLowerShriekAcyclic_projection` (the acyclicity of `π_!`, so
that `Lπ_!` is computed by a resolution whose terms are direct sums of the `j_{W!}ℤ_W`) and
`Stacks.ChaoticSite.GeneralValued.mooreCochainQIsoColimOfResolution` (the two filtrations of the
Moore double complex over `Δ`). In five steps:

1. Stacks 06XX (`StacksDraft.UnboundedLeftDerivedFunctor.exists_sequence_quasiIso_truncLE`) at
   stage `0` produces a complex `R` with `R.IsStrictlyLE 0`, whose terms are direct sums of the
   `j_{W!}ℤ_W`, together with a quasi-isomorphism `ε : R ⟶ ℱ[0]` — the composite of the
   resolution of `τ_{≤0}(ℱ[0])` with `ιTruncLE`, which is invertible because `ℱ[0]` is strictly
   `≤ 0`.
2. `StacksDraft.UnboundedLeftDerivedFunctor.leftDerivedObjIsoOfBoundedProp`, fed with the
   acyclicity of `π_!`, computes `Lπ_!(R) = π_!(R)` degreewise.
3. `ε` is inverted by `DerivedCategory.Q`, so `Lπ_!(ℱ[0]) ≅ Lπ_!(R)`.
4. `Stacks.SimplicialModules.abelianLowerShriekIsoColim` rewrites `π_!` as
   `fibrewise ⋙ colim`, degreewise.
5. `Stacks.ChaoticSite.GeneralValued.mooreCochainQIsoColimOfResolution`, at the site `Δ` with the
   tautological cosimplicial object `𝟭 Δ` and coefficients `Ab(C)`, identifies
   `colim (fibrewise R)` with the extended Moore complex of `ℱ_•`.

## The new input: the Moore augmentation of a term of the resolution

Step 5 asks for its hypothesis `haug`: the Moore augmentation of each `fibrewise (R^p)` is a
quasi-isomorphism. That is
`Stacks.SimplicialModules.quasiIso_mooreCochainAugmentation_fibrewise`, and it is proved here by
identifying the fibrewise reading of the generators of the simplicial site with the free
simplicial objects, for which the vanishing is
`Stacks.ChaoticSite.SimplexValued.isZero_homology_alternatingFaceMapComplex_freeSimplicial_succ`:

* `j_{(m,U)!}ℤ ≅ (i_m)_!(j_{U!}ℤ_U)` is
  `Stacks.SimplicialModules.extensionByZeroUnitAbFibreIso`;
* `(i_m)_! ⋙ fibrewise` is the left adjoint of evaluation in degree `m`, because
  `fibrewise` is an equivalence carrying restriction along `i_m` to evaluation at `op m` — and
  restriction along `i_m` *is* evaluation of the fibrewise reading, on the nose, both being
  precomposition with `i_m^{op}`;
* the value of that left adjoint is the free simplicial object `∐_{Mor_Δ(-, m)} Y`, the two
  being coproducts of copies of `Y` indexed by the two spellings `op m ⟶ j` and `Mor_Δ(j, m)` of
  one and the same hom-set;
* `fibrewise` is an equivalence, so it carries the direct sum presenting a term of `R` to a
  direct sum of free simplicial objects, and the positive-degree vanishing passes to direct sums
  because coproducts of abelian sheaves are exact.

## Implementation notes

Every universe is the universe `w` of the objects and of the morphisms of the site `C`, and the
abelian coefficients are `AddCommGrpCat.{w}`, as in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Simplicial/FibreInclusion.lean`; `Δ` contributes
nothing, `SimplexCategory` being a `Type` with `Type`-valued homs.

The coproducts of abelian sheaves indexed by a `Type` — not by a type in the coefficient
universe — are not reached by instance search on their own, since they ask for coproducts of
abelian groups that search only finds near the end of its budget. They are recorded as
`Stacks.SimplicialModules.hasColimitsOfShape_discrete_type_sheafAb`, by shrinking the index
universe of `Stacks.Cohomology.DerivedLowerShriek.hasColimitsOfShape_discrete_sheafAb`. The free
simplicial objects need exactly those, their index sets being hom-sets of `Δ`.

`Stacks.SimplicialModules.fibreRestriction C J m` and
`fibrewise J AddCommGrpCat.{w} ⋙ (evaluation _ _).obj (op m)` are *equal*, both being
precomposition with `i_m^{op}`, so the comparison needed in the adjoint-uniqueness argument is
only `Stacks.SimplicialModules.fibrewiseSheafUncurryIso` whiskered by evaluation.

## References

* [Stacks Project, Tag 09D0](https://stacks.math.columbia.edu/tag/09D0)
* [Stacks Project, Tag 09CY](https://stacks.math.columbia.edu/tag/09CY)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 06XX](https://stacks.math.columbia.edu/tag/06XX)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.Cohomology.DerivedLowerShriek

namespace Stacks.SimplicialModules

universe w

attribute [local instance] HasDerivedCategory.standard

/-! ### The free simplicial objects are the values of the left adjoint of evaluation -/

section FreeSimplicial

variable {A : Type*} [Category* A] [HasCoproducts.{0} A]

/-- **The free simplicial object on `Y` at `m` is the value at `Y` of the left adjoint of
evaluation at `op m`.** Both corepresent one and the same functor of a simplicial object `Z` of
`A`, namely `Z ↦ (Y ⟶ Z_m)`: the left adjoint of evaluation by its adjunction
(`CategoryTheory.evaluationAdjunctionRight`), and the free simplicial object by
[Stacks, Tag 017F] (1) (`CategoryTheory.SimplicialObject.constProdStd.phi_bijective`), whose
bijection is restriction to the summand indexed by the identity of `m`. Two objects
corepresenting the same functor are isomorphic, which is
`Stacks.SimplicialModules.isoOfHomEquivs`.

`Stacks.ChaoticSite.SimplexValued.freeSimplicial` is written as a copower so that the product of
[Stacks, Tag 017C] applies to it with no comparison map, and its docstring records this
identification as not proved there. It is obtained here from the two universal properties rather
than by writing down a morphism of coproducts — the same route by which
`Stacks.SimplicialModules.extensionByZeroUnitAbFibreIso` identifies `j_{(m,U)!}ℤ`. The
`Stacks.ChaoticSite.SimplexValued.freeSimplicial m Y` of the statement and the
`CategoryTheory.SimplicialObject.constProdStd Y m.len` of Tag 017F are the same object: an
object of `Δ` is the structure `⦋m.len⦌` on its length, and restricting a presheaf along
`(𝟭 Δ)^{op}` changes nothing. -/
@[sga "4 Vbis 1.2.11" "special case"]
def evaluationLeftAdjointObjIsoFreeSimplicial (m : SimplexCategory) (Y : A) :
    (evaluationLeftAdjoint A (op m)).obj Y ≅
      Stacks.ChaoticSite.SimplexValued.freeSimplicial m Y :=
  isoOfHomEquivs (T := fun Z : SimplexCategoryᵒᵖ ⥤ A => (Y ⟶ Z.obj (op m)))
    (fun Z => (evaluationAdjunctionRight A (op m)).homEquiv Y Z)
    (fun Z => Equiv.ofBijective (SimplicialObject.constProdStd.phi Y m.len Z)
      (SimplicialObject.constProdStd.phi_bijective Y m.len Z))
    (fun k t => t ≫ k.app (op m))
    (fun a k => (evaluationAdjunctionRight A (op m)).homEquiv_naturality_right a k)
    (fun b k => by
      change SimplicialObject.constProdStd.incl Y m.len ≫ (b ≫ k).app (op m) =
        (SimplicialObject.constProdStd.incl Y m.len ≫ b.app (op m)) ≫ k.app (op m)
      rw [NatTrans.comp_app, Category.assoc])

end FreeSimplicial

/-! ### Coproducts of abelian sheaves indexed by a `Type` -/

section Coproducts

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}]

/-- **Coproducts of abelian sheaves indexed by a `Type`.** This is
`Stacks.Cohomology.DerivedLowerShriek.hasColimitsOfShape_discrete_sheafAb` with its index
universe shrunk to `Type`; instance search does not get there on its own, the colimits of
abelian groups it asks for being found only near the end of its budget. The free simplicial
objects of `Stacks.ChaoticSite.SimplexValued.freeSimplicial` need exactly these, their index
sets being hom-sets of `Δ`. -/
instance hasColimitsOfShape_discrete_type_sheafAb (ι : Type) :
    HasColimitsOfShape (Discrete ι) (Sheaf J AddCommGrpCat.{w}) :=
  haveI := hasColimitsOfShape_discrete_sheafAb J (ULift.{w} ι)
  hasColimitsOfShape_of_equivalence
    (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w} ι) ≌ Discrete ι)

end Coproducts

/-! ### Reading the fibre extension fibrewise -/

section FibreEvaluation

variable (C : Type w) [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}]
  [HasSheafify (projectionTopology C J) AddCommGrpCat.{w}]

/-- `fibrewise` is a left adjoint, being half of an equivalence. -/
instance isLeftAdjoint_fibrewise : (fibrewise J AddCommGrpCat.{w}).IsLeftAdjoint :=
  (simplicialSheafEquivalence J AddCommGrpCat.{w}).toAdjunction.isLeftAdjoint

/-- `fibrewise` is an equivalence of categories: it is the functor of
`Stacks.SimplicialModules.simplicialSheafEquivalence`. -/
instance isEquivalence_fibrewise : (fibrewise J AddCommGrpCat.{w}).IsEquivalence :=
  (simplicialSheafEquivalence J AddCommGrpCat.{w}).isEquivalence_functor

/-- `fibrewise` preserves zero morphisms, being a left adjoint between preadditive
categories. -/
instance preservesZeroMorphisms_fibrewise :
    (fibrewise J AddCommGrpCat.{w}).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_isLeftAdjoint _

/-- `fibrewise` is additive: it is an equivalence, hence preserves binary coproducts, hence
binary biproducts, the source and target being preadditive with biproducts. -/
instance additive_fibrewise : (fibrewise J AddCommGrpCat.{w}).Additive :=
  haveI : PreservesBinaryBiproducts (fibrewise J AddCommGrpCat.{w}) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

/-- `fibrewise` preserves homology, being an equivalence: it preserves all kernels and all
cokernels. -/
instance preservesHomology_fibrewise : (fibrewise J AddCommGrpCat.{w}).PreservesHomology where

omit [HasSheafify J AddCommGrpCat] [HasSheafify (projectionTopology C J) AddCommGrpCat] in
/-- **Evaluation in degree `m` of the fibrewise reading of a sheaf on `Δ × C` is restriction
along the fibre inclusion `i_m`.** The two are equal, not merely isomorphic: both are
precomposition with `i_m^{op}`. -/
theorem fibreRestriction_eq_fibrewise_comp_evaluation (m : SimplexCategory) :
    fibreRestriction C J m =
      fibrewise J AddCommGrpCat.{w} ⋙
        (evaluation SimplexCategoryᵒᵖ (Sheaf J AddCommGrpCat.{w})).obj (op m) :=
  rfl

/-- **Uncurrying a simplicial abelian sheaf and restricting to the fibre over `m` gives back its
degree `m`.** This is `Stacks.SimplicialModules.fibrewiseSheafUncurryIso` evaluated in degree
`m`, available in this shape because restriction along `i_m` is evaluation of the fibrewise
reading on the nose
(`Stacks.SimplicialModules.fibreRestriction_eq_fibrewise_comp_evaluation`). -/
def sheafUncurryCompFibreRestrictionIso (m : SimplexCategory) :
    sheafUncurry J AddCommGrpCat.{w} ⋙ fibreRestriction C J m ≅
      (evaluation SimplexCategoryᵒᵖ (Sheaf J AddCommGrpCat.{w})).obj (op m) :=
  Functor.isoWhiskerRight (fibrewiseSheafUncurryIso J AddCommGrpCat.{w})
      ((evaluation SimplexCategoryᵒᵖ (Sheaf J AddCommGrpCat.{w})).obj (op m)) ≪≫
    Functor.leftUnitor _

/-- **`(i_m)_!` read fibrewise is left adjoint to evaluation in degree `m`.** Compose the
adjunction `(i_m)_! ⊣ (i_m)^{-1}` with the equivalence `fibrewise ⊣ sheafUncurry` and identify
the resulting right adjoint with evaluation by
`Stacks.SimplicialModules.sheafUncurryCompFibreRestrictionIso`. -/
def fibreExtensionCompFibrewiseAdjunction (m : SimplexCategory) :
    fibreExtension C J m ⋙ fibrewise J AddCommGrpCat.{w} ⊣
      (evaluation SimplexCategoryᵒᵖ (Sheaf J AddCommGrpCat.{w})).obj (op m) :=
  Adjunction.ofNatIsoRight
    ((fibreAdjunction C J m).comp
      (simplicialSheafEquivalence J AddCommGrpCat.{w}).toAdjunction)
    (sheafUncurryCompFibreRestrictionIso C J m)

/-- **`(i_m)_!` read fibrewise is the left adjoint of evaluation in degree `m`.** Both are left
adjoints of the same functor — the first by
`Stacks.SimplicialModules.fibreExtensionCompFibrewiseAdjunction`, the second by Mathlib's
`CategoryTheory.evaluationAdjunctionRight` — and left adjoints of one functor agree. -/
def fibreExtensionCompFibrewiseIso (m : SimplexCategory) :
    fibreExtension C J m ⋙ fibrewise J AddCommGrpCat.{w} ≅
      evaluationLeftAdjoint (Sheaf J AddCommGrpCat.{w}) (op m) :=
  Adjunction.leftAdjointUniq (fibreExtensionCompFibrewiseAdjunction C J m)
    (evaluationAdjunctionRight (Sheaf J AddCommGrpCat.{w}) (op m))

/-- **The free abelian sheaf on a representable of the simplicial site, read fibrewise, is a
free simplicial object.** For `W = (m, U)`, `j_{W!}ℤ_W` is `(i_m)_!(j_{U!}ℤ_U)`
(`Stacks.SimplicialModules.extensionByZeroUnitAbFibreIso`), reading `(i_m)_!` fibrewise gives the
left adjoint of evaluation at `op m`
(`Stacks.SimplicialModules.fibreExtensionCompFibrewiseIso`), and that left adjoint has the free
simplicial objects as its values
(`Stacks.SimplicialModules.evaluationLeftAdjointObjIsoFreeSimplicial`). -/
def fibrewiseExtensionByZeroUnitAbIso (W : SimplexCategory × C) :
    (fibrewise J AddCommGrpCat.{w}).obj
        (extensionByZeroUnitAb.{w} (projectionTopology C J) W) ≅
      Stacks.ChaoticSite.SimplexValued.freeSimplicial W.1
        (extensionByZeroUnitAb.{w} J W.2) :=
  (fibrewise J AddCommGrpCat.{w}).mapIso (extensionByZeroUnitAbFibreIso C J W.1 W.2) ≪≫
    (fibreExtensionCompFibrewiseIso C J W.1).app (extensionByZeroUnitAb.{w} J W.2) ≪≫
    evaluationLeftAdjointObjIsoFreeSimplicial W.1 (extensionByZeroUnitAb.{w} J W.2)

end FibreEvaluation

/-! ### The Moore augmentation of a term of the resolution -/

section Augmentation

variable (C : Type w) [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}]
  [HasSheafify (projectionTopology C J) AddCommGrpCat.{w}]

/-- **The Moore complex of the fibrewise reading of a direct sum of free abelian sheaves on
representables has no homology in positive degrees.** Such a sheaf is a direct sum of the
`j_{W!}ℤ_W`, `fibrewise` is an equivalence and so carries that direct sum to a direct sum of the
fibrewise readings, each of which is a free simplicial object
(`Stacks.SimplicialModules.fibrewiseExtensionByZeroUnitAbIso`); the vanishing holds for a free
simplicial object by contractibility of the standard simplex
(`Stacks.ChaoticSite.SimplexValued.isZero_homology_alternatingFaceMapComplex_freeSimplicial_succ`)
and passes to direct sums because coproducts of abelian sheaves are exact. -/
theorem isZero_homology_alternatingFaceMapComplex_fibrewise_succ
    (P : Sheaf (projectionTopology C J) AddCommGrpCat.{w})
    (hP : IsSumOfExtensionByZeroUnitsAb.{w} (projectionTopology C J) P) (k : ℕ) :
    IsZero (((alternatingFaceMapComplex (Sheaf J AddCommGrpCat.{w})).obj
      ((fibrewise J AddCommGrpCat.{w}).obj P)).homology (k + 1)) := by
  obtain ⟨ι, W, ⟨e⟩⟩ := hP
  have hiso :
      (fibrewise J AddCommGrpCat.{w}).obj P ≅
        ∐ fun i : ι => Stacks.ChaoticSite.SimplexValued.freeSimplicial (W i).1
          (extensionByZeroUnitAb.{w} J (W i).2) :=
    (fibrewise J AddCommGrpCat.{w}).mapIso e.symm ≪≫
      PreservesCoproduct.iso (fibrewise J AddCommGrpCat.{w})
        (fun i : ι => extensionByZeroUnitAb.{w} (projectionTopology C J) (W i)) ≪≫
      Sigma.whiskerEquiv (Equiv.refl ι)
        (fun i => (fibrewiseExtensionByZeroUnitAbIso C J (W i)).symm)
  refine ChaoticSite.SimplexValued.isZero_homology_alternatingFaceMapComplex_of_iso
    hiso (k + 1) ?_
  exact ChaoticSite.SimplexValued.isZero_homology_alternatingFaceMapComplex_succ_of_coproduct _
    (fun i n =>
      ChaoticSite.SimplexValued.isZero_homology_alternatingFaceMapComplex_freeSimplicial_succ
        _ _ n) k

/-- **The Moore augmentation of the fibrewise reading of a direct sum of free abelian sheaves on
representables is a quasi-isomorphism.** This is the hypothesis `haug` of
`Stacks.ChaoticSite.GeneralValued.mooreCochainQIsoColimOfResolution` at the terms of the
resolution that Stacks 06XX produces: over `Δ` with the tautological cosimplicial object `𝟭 Δ`
the cokernel presentation of the colimit injection needs no hypothesis at all
(`Stacks.ChaoticSite.SimplexValued.colimitIotaZeroIsColimit`), so the only input is the
positive-degree vanishing
`Stacks.SimplicialModules.isZero_homology_alternatingFaceMapComplex_fibrewise_succ`. -/
theorem quasiIso_mooreCochainAugmentation_fibrewise
    (P : Sheaf (projectionTopology C J) AddCommGrpCat.{w})
    (hP : IsSumOfExtensionByZeroUnitsAb.{w} (projectionTopology C J) P) :
    QuasiIso ((Stacks.ChaoticSite.GeneralValued.mooreCochainAugmentation
      (𝟭 SimplexCategory)).app ((fibrewise J AddCommGrpCat.{w}).obj P)) :=
  Stacks.ChaoticSite.SimplexValued.quasiIso_mooreCochainAugmentation_of_isZero _
    fun k => isZero_homology_alternatingFaceMapComplex_fibrewise_succ C J P hP k

end Augmentation

/-! ### The theorem -/

section Assembly

variable (C : Type w) [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}]
  [HasSheafify (projectionTopology C J) AddCommGrpCat.{w}]
  [((projection C).sheafPushforwardContinuous AddCommGrpCat.{w}
    (projectionTopology C J) J).IsRightAdjoint]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{w})]
  [HasExt.{w} (Sheaf (projectionTopology C J) AddCommGrpCat.{w})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]
  [EnoughInjectives (Sheaf (projectionTopology C J) AddCommGrpCat.{w})]

/-- **Stacks 07AC for the projection, unconditionally**: degreewise lower shriek along `π` has a
pointwise left derived functor, because `π_!` is acyclic on the generators
(`Stacks.SimplicialModules.abelianLowerShriekAcyclic_projection`). Recorded as an instance so
that `Lπ_!` can be named with no hypothesis beyond the standing ones. -/
instance hasPointwiseLeftDerivedFunctor_abelianLowerShriek_projection :
    (abelianLowerShriekOnHomotopy.{w} (projectionTopology C J) J (projection C) ⋙
        DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (projectionTopology C J) AddCommGrpCat.{w})
        (ComplexShape.up ℤ)) :=
  hasPointwiseLeftDerivedAbelianLowerShriek_of_acyclic.{w} (projectionTopology C J) J
    (projection C) (abelianLowerShriekAcyclic_projection C J)

variable [HasColimitsOfShape SimplexCategoryᵒᵖ (Sheaf J AddCommGrpCat.{w})]

/-- **Stacks 09D0, in the form the assembly produces it.** The existence of the isomorphism of
`Stacks.SimplicialModules.derivedProjectionLowerShriekIsoMooreComplex`; the resolution of
Stacks 06XX is chosen inside the proof. -/
theorem nonempty_derivedProjectionLowerShriekIsoMooreComplex
    (F : Sheaf (projectionTopology C J) AddCommGrpCat.{w}) :
    Nonempty
      ((derivedAbelianLowerShriek.{w} (projectionTopology C J) J (projection C)).obj
          (DerivedCategory.Q.obj
            ((HomologicalComplex.single
              (Sheaf (projectionTopology C J) AddCommGrpCat.{w})
              (ComplexShape.up ℤ) 0).obj F)) ≅
        DerivedCategory.Q.obj
          ((Stacks.ChaoticSite.GeneralValued.mooreCochainComplex (𝟭 SimplexCategory)
            (Sheaf J AddCommGrpCat.{w})).obj ((fibrewise J AddCommGrpCat.{w}).obj F))) := by
  have hnatA := hasExactColimitsOfShape_nat_sheafAb.{w} (projectionTopology C J)
  have hnatB := hasExactColimitsOfShape_nat_sheafAb.{w} J
  -- Step 1: the resolution of Stacks 06XX, read off at stage `0`.
  obtain ⟨R, f, g, hqis, hLE, hprops, -, -⟩ :=
    StacksDraft.UnboundedLeftDerivedFunctor.exists_sequence_quasiIso_truncLE
      (IsSumOfExtensionByZeroUnitsAb.{w} (projectionTopology C J))
      (fun _ _ => isSumOfExtensionByZeroUnitsAb_biprod.{w} (projectionTopology C J))
      (fun X => exists_epi_isSumOfExtensionByZeroUnitsAb.{w} (projectionTopology C J) X)
      ((HomologicalComplex.single (Sheaf (projectionTopology C J) AddCommGrpCat.{w})
        (ComplexShape.up ℤ) 0).obj F)
  have hRLE : CochainComplex.IsStrictlyLE (R 0) (0 : ℤ) := by
    have h := hLE 0
    rwa [Nat.cast_zero] at h
  have hsingleLE : CochainComplex.IsStrictlyLE
      ((HomologicalComplex.single (Sheaf (projectionTopology C J) AddCommGrpCat.{w})
        (ComplexShape.up ℤ) 0).obj F) ((0 : ℕ) : ℤ) := by
    rw [Nat.cast_zero]; infer_instance
  have := hqis 0
  set ε := f 0 ≫ CochainComplex.ιTruncLE
    ((HomologicalComplex.single (Sheaf (projectionTopology C J) AddCommGrpCat.{w})
      (ComplexShape.up ℤ) 0).obj F) ((0 : ℕ) : ℤ) with hεdef
  have hε : QuasiIso ε := by rw [hεdef]; infer_instance
  -- Step 2: `Lπ_!` computed on the resolution.
  have step2 :=
    StacksDraft.UnboundedLeftDerivedFunctor.leftDerivedObjIsoOfBoundedProp
      (abelianLowerShriek.{w} (projectionTopology C J) J (projection C))
      (IsSumOfExtensionByZeroUnitsAb.{w} (projectionTopology C J))
      (fun _ _ => isSumOfExtensionByZeroUnitsAb_biprod.{w} (projectionTopology C J))
      (fun X => exists_epi_isSumOfExtensionByZeroUnitsAb.{w} (projectionTopology C J) X)
      (abelianLowerShriekAcyclic_projection C J)
      (derivedAbelianLowerShriek.{w} (projectionTopology C J) J (projection C))
      (derivedAbelianLowerShriekComparison.{w} (projectionTopology C J) J (projection C))
      (R 0) (fun i => hprops 0 i)
  -- Step 3: `ε` moves `Lπ_!` across.
  have step3 :
      (derivedAbelianLowerShriek.{w} (projectionTopology C J) J (projection C)).obj
          (DerivedCategory.Q.obj
            ((HomologicalComplex.single
              (Sheaf (projectionTopology C J) AddCommGrpCat.{w})
              (ComplexShape.up ℤ) 0).obj F)) ≅
        (derivedAbelianLowerShriek.{w} (projectionTopology C J) J (projection C)).obj
          (DerivedCategory.Q.obj (R 0)) :=
    (derivedAbelianLowerShriek.{w} (projectionTopology C J) J (projection C)).mapIso
      (CochainComplex.derivedIsoOfQuasiIso ε hε).symm
  -- Step 4: `π_!` is the colimit over `Δᵒᵖ`, degreewise.
  have step4 :
      DerivedCategory.Q.obj
          (((abelianLowerShriek.{w} (projectionTopology C J) J
            (projection C)).mapHomologicalComplex (ComplexShape.up ℤ)).obj (R 0)) ≅
        DerivedCategory.Q.obj
          (((colim : (SimplexCategoryᵒᵖ ⥤ Sheaf J AddCommGrpCat.{w}) ⥤
                Sheaf J AddCommGrpCat.{w}).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((fibrewise J AddCommGrpCat.{w}).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (R 0))) :=
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (abelianLowerShriekIsoColim C J)
        (ComplexShape.up ℤ)).app (R 0))
  -- Step 5: the two filtrations of the Moore double complex over `Δ`.
  have hfibLE : CochainComplex.IsStrictlyLE
      (((fibrewise J AddCommGrpCat.{w}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (R 0)) (0 : ℤ) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact Functor.map_isZero (fibrewise J AddCommGrpCat.{w})
      (CochainComplex.isZero_of_isStrictlyLE (R 0) 0 i hi)
  have hεmap : QuasiIso (((fibrewise J AddCommGrpCat.{w}).mapHomologicalComplex
      (ComplexShape.up ℤ)).map ε) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology ε (fibrewise J AddCommGrpCat.{w})
  have hεcomp : QuasiIso ((HomologicalComplex.singleMapHomologicalComplex
      (fibrewise J AddCommGrpCat.{w}) (ComplexShape.up ℤ) 0).app F).hom := by
    infer_instance
  set εfib :=
    ((fibrewise J AddCommGrpCat.{w}).mapHomologicalComplex (ComplexShape.up ℤ)).map ε ≫
      ((HomologicalComplex.singleMapHomologicalComplex (fibrewise J AddCommGrpCat.{w})
        (ComplexShape.up ℤ) 0).app F).hom with hεfibdef
  have hεfib : QuasiIso εfib := by
    rw [hεfibdef]
    infer_instance
  have step5 :=
    Stacks.ChaoticSite.GeneralValued.mooreCochainQIsoColimOfResolution
      (𝟭 SimplexCategory) ((fibrewise J AddCommGrpCat.{w}).obj F)
      (((fibrewise J AddCommGrpCat.{w}).mapHomologicalComplex (ComplexShape.up ℤ)).obj (R 0))
      εfib
      (fun p => quasiIso_mooreCochainAugmentation_fibrewise C J ((R 0).X p) (hprops 0 p))
  exact ⟨step3 ≪≫ step2 ≪≫ step4 ≪≫ step5.symm⟩

/-- **Stacks 09D0.** Let `(C, J)` be a small site and let `Δ × C` carry the topology inherited
from `(C, J)` along the projection `π : Δ × C ⥤ C`. For every sheaf of abelian groups `ℱ` on
`Δ × C`, the abelian derived lower shriek of Remark 09CY carries `ℱ` to the associated chain
complex of the simplicial abelian sheaf `ℱ_•` that `ℱ` is:

`Lπ_!(ℱ[0]) ≅ s(ℱ_•)` in `D(Ab(C))`,

where `s(ℱ_•)` is the alternating-face-map complex of `ℱ_• = fibrewise ℱ`, read as a cochain
complex over `ℤ` in non-positive degrees.

This is the source's own argument: a resolution of `ℱ` by direct sums of the free abelian
sheaves `j_{W!}ℤ_W` (Stacks 06XX) computes `Lπ_!` because `π_!` is acyclic on those
(`Stacks.SimplicialModules.abelianLowerShriekAcyclic_projection`, which is Lemma 21.40.2), and
the degreewise colimit over `Δᵒᵖ` of such a resolution is the Moore complex
(`Stacks.ChaoticSite.GeneralValued.mooreCochainQIsoColimOfResolution`, which is Lemma
21.39.7). -/
@[stacks 09D0 "Lπ_!(ℱ_•) is represented by the alternating-face-map complex s(ℱ_•) of the \
  simplicial abelian sheaf ℱ_•, for every abelian sheaf on Δ × C — in particular for the \
  underlying abelian sheaf of a simplicial A_•-module over any simplicial sheaf of rings A_•, \
  the Lπ_! of the section being the abelian one of Remark 09CY. Proved from Stacks 08PJ's two \
  inputs as the source directs: the acyclicity of π_! and the Moore computation over Δ"]
def derivedProjectionLowerShriekIsoMooreComplex
    (F : Sheaf (projectionTopology C J) AddCommGrpCat.{w}) :
    (derivedAbelianLowerShriek.{w} (projectionTopology C J) J (projection C)).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (Sheaf (projectionTopology C J) AddCommGrpCat.{w})
            (ComplexShape.up ℤ) 0).obj F)) ≅
      DerivedCategory.Q.obj
        ((Stacks.ChaoticSite.GeneralValued.mooreCochainComplex (𝟭 SimplexCategory)
          (Sheaf J AddCommGrpCat.{w})).obj ((fibrewise J AddCommGrpCat.{w}).obj F)) :=
  (nonempty_derivedProjectionLowerShriekIsoMooreComplex C J F).some

end Assembly

end Stacks.SimplicialModules

end
