module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushforwardNaturalSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraUnitEssentiallySmall

/-!
# The unit sections of a pullback of a sheaf of graded algebras multiply

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and `𝒜` a sheaf of graded
`O_D`-algebras.  A local section `s` of `𝒜_n` over an object `U` of `D` has a canonical image in
the direct image `f_*f^*𝒜_n` over `U`, the unit of the Stacks 03D7 adjunction at `s`.  Read
through any family of maps `θ_F : (f_*F)(U) ⟶ F(Q)` natural in the sheaf of sets `F` on `C` — a
chart projection, for instance — these images multiply as the original sections do, the product
on the right being that of the pullback `f^*𝒜`.

## Main results

All in the namespace `Stacks.Sheaves.GradedAlgebraEssentiallySmall`.

* `pullbackAdjPushforwardModulesViaComparison_unit_app_val_app`: the unit of the adjunction
  transported along the comparison of the two spellings of the direct image acts on local sections
  as the untransported unit.
* `natural_family_pullbackUnit_mul`: **the unit sections of a pullback multiply as the original
  sections do**, read through a natural family.

## Implementation notes

The multiplicativity of the unit is `Stacks.Sheaves.GradedAlgebraEssentiallySmall.unitApp`, which
is stated for the unit of
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModulesViaComparison` rather than that of
`Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules`.  The two differ by
`AlgebraicGeometry.RingedToposHom.pushforwardModulesIso`, which is the identity on underlying
sheaves of sets (`moduleSheafFunctor_map_pushforwardModulesIso_hom_app`), so they agree on local
sections; and `natural_family_mul` carries the multiplication of a direct image to the
multiplication of the original algebra.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.Sheaves.GradedAlgebraPullback (toposPullbackGradedAlgebra)
open Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.GradedAlgebraEssentiallySmall

universe w v u₁

variable {X Y : RingedTopos.{v, u₁, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : AlgebraicGeometry.RingedToposHom X Y)

/-- **The transported and the untransported unit agree on local sections.**  The transported
unit is the untransported one followed by the comparison of the two spellings of the direct
image, and that comparison is the identity on underlying sheaves of sets. -/
theorem pullbackAdjPushforwardModulesViaComparison_unit_app_val_app
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (U : Y.Cᵒᵖ)
    (s : M.val.obj U) :
    (f.pullbackAdjPushforwardModulesViaComparison.unit.app M).val.app U s =
      ((pullbackAdjPushforwardModules f.toRingedToposModulesHom).unit.app M).val.app U s := by
  have hiso : f.pullbackAdjPushforwardModulesViaComparison.unit.app M =
      (pullbackAdjPushforwardModules f.toRingedToposModulesHom).unit.app M ≫
        f.pushforwardModulesIso.hom.app _ := rfl
  have h := congrArg (fun g => (ConcreteCategory.hom (g.hom.app U))
      (((pullbackAdjPushforwardModules f.toRingedToposModulesHom).unit.app M).val.app U s))
    (moduleSheafFunctor_map_pushforwardModulesIso_hom_app f
      ((f.toRingedToposModulesHom.pullbackModules).obj M))
  rw [hiso]
  exact h

variable [EssentiallySmall.{w} Y.C]

/-- **The unit sections of a pullback of a sheaf of graded algebras multiply as the original
sections do**, read through any family of maps out of the sections of a direct image which is
natural in the sheaf of sets.

The unit is a homomorphism of sheaves of graded algebras into the direct image of the pullback
(`Stacks.Sheaves.GradedAlgebraEssentiallySmall.unitApp`), and a natural family carries the
multiplication of a direct image to that of the algebra it is the direct image of
(`Stacks.Sheaves.GradedAlgebraEssentiallySmall.natural_family_mul`). -/
theorem natural_family_pullbackUnit_mul (U : Y.Cᵒᵖ) (Q : X.Cᵒᵖ)
    (θ : ∀ F : Sheaf X.J (Type w), (f.toToposHom.pushforward.obj F).obj.obj U → F.obj.obj Q)
    (hθ : ∀ {F F' : Sheaf X.J (Type w)} (g : F ⟶ F')
      (x : (f.toToposHom.pushforward.obj F).obj.obj U),
      θ F' ((f.toToposHom.pushforward.map g).hom.app U x) = g.hom.app Q (θ F x))
    (A : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (i j : ℤ) (s : (A.piece i).val.obj U) (t : (A.piece j).val.obj U) :
    θ (underlyingPiece (toposPullbackGradedAlgebra f.toRingedToposModulesHom A) (i + j))
        (((pullbackAdjPushforwardModules f.toRingedToposModulesHom).unit.app
          (A.piece (i + j))).val.app U ((A.mul i j).app U s t)) =
      ((toposPullbackGradedAlgebra f.toRingedToposModulesHom A).mul i j).app Q
        (θ (underlyingPiece (toposPullbackGradedAlgebra f.toRingedToposModulesHom A) i)
          (((pullbackAdjPushforwardModules f.toRingedToposModulesHom).unit.app
            (A.piece i)).val.app U s))
        (θ (underlyingPiece (toposPullbackGradedAlgebra f.toRingedToposModulesHom A) j)
          (((pullbackAdjPushforwardModules f.toRingedToposModulesHom).unit.app
            (A.piece j)).val.app U t)) := by
  have hm := (unitApp f A).map_mul i j U s t
  rw [← pullbackAdjPushforwardModulesViaComparison_unit_app_val_app,
    ← pullbackAdjPushforwardModulesViaComparison_unit_app_val_app,
    ← pullbackAdjPushforwardModulesViaComparison_unit_app_val_app]
  have key := natural_family_mul f U Q θ hθ
    (toposPullbackGradedAlgebra f.toRingedToposModulesHom A) i j
    ((f.pullbackAdjPushforwardModulesViaComparison.unit.app (A.piece i)).val.app U s)
    ((f.pullbackAdjPushforwardModulesViaComparison.unit.app (A.piece j)).val.app U t)
  refine Eq.trans ?_ key
  exact congrArg _ hm

end Stacks.Sheaves.GradedAlgebraEssentiallySmall

end
