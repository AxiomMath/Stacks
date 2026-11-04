module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraCounitEssentiallySmall
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackUnital

/-!
# The pullback functor and the counit of sheaves of graded algebras preserve the unit

Complements to `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackUnital` for the
two constructions of Stacks 0FQX:

* the pullback `f^*` of sheaves of graded algebras along a morphism of ringed topoi carries a
  homomorphism preserving the unit to one preserving the unit
  (`Stacks.Sheaves.GradedAlgebraPullback.toposPullbackGradedAlgebraFunctor_map_one`);
* the counit `f^* f_* 𝒜 ⟶ 𝒜` of the adjunction of Stacks 0FQX, part (3), preserves the unit
  (`Stacks.Sheaves.GradedAlgebraEssentiallySmall.counitApp_map_one`).  The unit of `f_* 𝒜`, as a
  morphism out of the terminal sheaf, is the transpose of the unit of `𝒜`
  (`Stacks.Sheaves.GradedAlgebraEssentiallySmall.pushforward_oneSheafHom_eq`), so its inverse
  image followed by the counit of the adjunction of topoi is the unit of `𝒜`
  (`Stacks.Sheaves.GradedAlgebraEssentiallySmall.inverseImage_oneSheafHom_comp_counit`).

## References

* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

namespace Stacks.Sheaves.GradedAlgebraPullback

open AlgebraicGeometry Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.GradedAlgebraInverseImage
open Stacks.Sheaves.GradedAlgebraExtendScalars

universe w v u

variable {X Y : AlgebraicGeometry.RingedTopos.{v, u, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

/-- **Pullback of sheaves of graded algebras along a morphism of ringed topoi preserves unital
homomorphisms**: part (2) of Stacks 0FQX carries a homomorphism preserving the unit to one
preserving the unit.  The pullback is the inverse image followed by extension of scalars, and
both preserve the unit. -/
theorem toposPullbackGradedAlgebraFunctor_map_one
    {B C : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (ψ : B ⟶ C) (hψ : ∀ U, (ψ.app 0).val.app U (B.one.eval U) = C.one.eval U) (U : X.Cᵒᵖ) :
    (((toposPullbackGradedAlgebraFunctor f).map ψ).app 0).val.app U
        ((toposPullbackGradedAlgebra f B).one.eval U) =
      (toposPullbackGradedAlgebra f C).one.eval U :=
  let : PreservesFiniteLimits f.toToposHom.inverseImage := f.toToposHom.preservesFiniteLimits
  extendScalarsGradedAlgebraHom_map_one _ X.J _ _ _
    (transportHom_map_one X.J f.toToposHom.inverseImage ψ hψ) U

end Stacks.Sheaves.GradedAlgebraPullback

open AlgebraicGeometry TensorProduct Stacks.PresheafOfModules.ChangeOfRings
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.GradedAlgebraExtendScalars
open Stacks.Sheaves.GradedAlgebraInverseImage
open Stacks.Sheaves.GradedAlgebraPullback
open Stacks.Sites.SheafSection
open scoped Stacks.Sites.SheafSection.OfEssentiallySmall

namespace Stacks.Sheaves.GradedAlgebraEssentiallySmall

universe v u₁ w

variable {X Y : RingedTopos.{v, u₁, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} Y.C]
  (f : AlgebraicGeometry.RingedToposHom X Y)

/-- **The unit of a direct-image graded algebra is the transpose of the unit of the source**:
read as a morphism out of the terminal sheaf of sets, it is the unit of the adjunction of topoi
followed by the direct image of the unit of the source. -/
theorem pushforward_oneSheafHom_eq
    (A : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    oneSheafHom (pushforwardGradedAlgebra f A) =
      f.toToposHom.adj.unit.app _ ≫
        f.toToposHom.pushforward.map (terminal.from _ ≫ oneSheafHom A) := by
  obtain ⟨h, -, sU, tU, tI, hs, ht, hc⟩ := isPushforwardGradedAlgebra_pushforwardGradedAlgebra f A
  have hsU : sU = oneSheafHom A := by
    ext U z
    exact (hs U z).trans (sections_oneSheafHom A U z).symm
  have htU : tU = oneSheafHom (pushforwardGradedAlgebra f A) := by
    ext U z
    exact (ht U z).trans (sections_oneSheafHom (pushforwardGradedAlgebra f A) U z).symm
  have hpc : (pieceComparison f A (pushforwardGradedAlgebra f A) h 0).hom = 𝟙 _ := by
    have he : eqToHom (h 0) = 𝟙 ((pushforwardGradedAlgebra f A).piece 0) := eqToHom_refl _ (h 0)
    simp only [pieceComparison, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom, he]
    rfl
  have hterm : f.toToposHom.adj.unit.app _ ≫ f.toToposHom.pushforward.map (terminal.from _) =
      tI.inv := by
    rw [← cancel_mono tI.hom, Iso.inv_hom_id]
    exact terminal.hom_ext _ _
  rw [hpc] at hc
  have hc' : tU = tI.inv ≫ f.toToposHom.pushforward.map sU :=
    (Category.comp_id tU).symm.trans hc
  rw [← htU, hc', hsU, Functor.map_comp, ← Category.assoc, hterm]

/-- **The counit of the adjunction of topoi carries the inverse image of the unit of a direct
image to the unit of the source.**  This is the transpose of
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.pushforward_oneSheafHom_eq`. -/
theorem inverseImage_oneSheafHom_comp_counit
    (A : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    f.toToposHom.inverseImage.map (oneSheafHom (pushforwardGradedAlgebra f A)) ≫
        f.toToposHom.adj.counit.app (Stacks.underlyingModuleSheaf X.J (A.piece 0)) =
      terminal.from _ ≫ oneSheafHom A := by
  refine (f.toToposHom.adj.homEquiv_counit _ _ _).symm.trans ?_
  refine Eq.trans (congrArg (f.toToposHom.adj.homEquiv _ _).symm
    ((pushforward_oneSheafHom_eq f A).trans
      (f.toToposHom.adj.homEquiv_unit _ _ _).symm)) ?_
  exact Equiv.symm_apply_apply _ _

/-- **The counit `f^* f_* 𝒜 ⟶ 𝒜` of the adjunction of Stacks 0FQX, part (3), preserves the
unit.**  The unit of the pullback is the pure tensor `1 ⊗ 1`, on which the counit is the counit
of the adjunction of topoi by `counit_scalarUnit_app`, and that carries the inverse image of the
unit of `f_* 𝒜` to the unit of `𝒜`. -/
theorem counitApp_map_one
    (A : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (V : X.Cᵒᵖ) :
    ((counitApp f A).app 0).val.app V
        (((pullFunctor f).obj ((pushFunctor f).obj A)).one.eval V) = A.one.eval V := by
  have h1 := (pullbackScalarUnit_app f (f.pushforwardModules.obj (A.piece 0)) V
    ((inverseImageGradedAlgebra f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      (pushforwardGradedAlgebra f A)).one.eval V)).symm
  refine (congrArg (fun t => ((counitApp f A).app 0).val.app V t) h1).trans ?_
  refine (counit_scalarUnit_app f (A.piece 0) V _).trans ?_
  let : PreservesFiniteLimits f.toToposHom.inverseImage := f.toToposHom.preservesFiniteLimits
  show (f.toToposHom.adj.counit.app (Stacks.underlyingModuleSheaf X.J (A.piece 0))).hom.app V
      ((transportSections X.J f.toToposHom.inverseImage V).map
        (oneSheafHom (pushforwardGradedAlgebra f A)) default) = _
  generalize (default : (transportSections X.J f.toToposHom.inverseImage V).obj
    (⊤_ (Sheaf Y.J (Type w)))) = p
  exact (congrArg (fun k => k.hom.app V p) (inverseImage_oneSheafHom_comp_counit f A)).trans
    (sections_oneSheafHom A V ((terminal.from (f.toToposHom.inverseImage.obj
      (⊤_ (Sheaf Y.J (Type w))))).hom.app V p))

end Stacks.Sheaves.GradedAlgebraEssentiallySmall
