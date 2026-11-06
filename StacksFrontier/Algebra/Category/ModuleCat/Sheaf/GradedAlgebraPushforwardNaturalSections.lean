module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushforwardEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.RightAdjointSections

/-!
# Natural maps out of the local sections of a direct image of a graded algebra

Let `f : X ⟶ Y` be a morphism of ringed topoi, let `U` be an object of the site of `Y` and `Q`
one of the site of `X`, and let `θ_F : (f_* F)(U) ⟶ F(Q)` be maps natural in the sheaf of sets
`F` on `X`.  For a sheaf of graded algebras `𝒜` on `X` the multiplication and the unit of the
direct image `f_* 𝒜` are the ones induced from `𝒜`, so `θ` carries them to the multiplication
and the unit of `𝒜` over `Q`.

## Main results

* `Stacks.Sheaves.GradedAlgebraEssentiallySmall.natural_family_mul`: `θ` is multiplicative.
* `Stacks.Sheaves.GradedAlgebraEssentiallySmall.natural_family_one`: `θ` is unital.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.Sites.SheafSection
open scoped Stacks.Sites.SheafSection.OfEssentiallySmall

namespace Stacks.Sheaves.GradedAlgebraEssentiallySmall

universe v u₁ w v' u₁' w'

variable {X : RingedTopos.{v, u₁, w}} {Y : RingedTopos.{v', u₁', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} X.C] [EssentiallySmall.{w'} Y.C]
  (f : RingedToposHom X Y) (U : Y.Cᵒᵖ) (Q : X.Cᵒᵖ)
  (θ : ∀ F : Sheaf X.J (Type w), (f.toToposHom.pushforward.obj F).obj.obj U → F.obj.obj Q)
  (hθ : ∀ {F F' : Sheaf X.J (Type w)} (g : F ⟶ F') (x : (f.toToposHom.pushforward.obj F).obj.obj U),
    θ F' ((f.toToposHom.pushforward.map g).hom.app U x) = g.hom.app Q (θ F x))

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [EssentiallySmall.{w} X.C] in
include hθ in
/-- A natural family evaluates a transposed section at the image of the universal section. -/
theorem natural_family_transposedSectionEquiv_symm {F : Sheaf X.J (Type w)}
    (g : f.toToposHom.inverseImage.obj
      ((presheafToSheaf Y.J (Type w')).obj (smallYoneda.{w'} U.unop)) ⟶ F) :
    θ F ((transposedSectionEquiv f U F).symm g) =
      g.hom.app Q (θ _ (universalSection f.toToposHom.adj U)) :=
  eq_app_universalSection f.toToposHom.adj U θ hθ g

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} X.C] in
include hθ in
/-- **A natural family is multiplicative on a direct image of a graded algebra.** -/
theorem natural_family_mul
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (i j : ℤ) (s : (f.pushforwardModules.obj (A.piece i)).val.obj U)
    (t : (f.pushforwardModules.obj (A.piece j)).val.obj U) :
    θ (underlyingPiece A (i + j)) (transposedMultiplicationAt f A i j U s t) =
      (A.mul i j).app Q (θ (underlyingPiece A i) s) (θ (underlyingPiece A j) t) := by
  have key : ∀ {F : Sheaf X.J (Type w)} (x : (f.toToposHom.pushforward.obj F).obj.obj U),
      θ F x = (transposedSectionEquiv f U F x).hom.app Q
        (θ _ (universalSection f.toToposHom.adj U)) := fun x =>
    (congrArg (θ _) ((transposedSectionEquiv f U _).symm_apply_apply x)).symm.trans
      (natural_family_transposedSectionEquiv_symm f U Q θ hθ _)
  rw [key (F := underlyingPiece A i) s, key (F := underlyingPiece A j) t]
  refine (natural_family_transposedSectionEquiv_symm f U Q θ hθ _).trans ?_
  set e := θ _ (universalSection f.toToposHom.adj U)
  exact congrArg₂ (fun a b => (A.mul i j).app Q a b)
    (congrArg (fun k => k.hom.app Q e)
      (prod.lift_fst (transposedSectionEquiv f U _ s) (transposedSectionEquiv f U _ t)))
    (congrArg (fun k => k.hom.app Q e)
      (prod.lift_snd (transposedSectionEquiv f U _ s) (transposedSectionEquiv f U _ t)))

omit [EssentiallySmall.{w} X.C] in
include hθ in
/-- **A natural family is unital on a direct image of a graded algebra.** -/
theorem natural_family_one
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O)) :
    θ (underlyingPiece A 0) ((pushforwardGradedAlgebra f A).one.eval U) = A.one.eval Q := by
  obtain ⟨h, -, sU, tU, tI, hs, ht, hc⟩ := isPushforwardGradedAlgebra_pushforwardGradedAlgebra f A
  let z : (⊤_ (Sheaf Y.J (Type w'))).obj.obj U :=
    (Stacks.Sheaves.GradedAlgebraPushforward.terminalPUnitIso (X := Y)).hom.hom.app U PUnit.unit
  exact (congrArg (θ (underlyingPiece A 0))
    ((ht U z).symm.trans (congrArg (fun k => k.hom.app U z) hc))).trans
      ((hθ sU _).trans (hs Q _))

end Stacks.Sheaves.GradedAlgebraEssentiallySmall

end
