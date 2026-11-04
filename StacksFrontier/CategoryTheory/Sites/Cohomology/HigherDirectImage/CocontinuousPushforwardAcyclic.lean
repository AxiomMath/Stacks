module

public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ExtAlongAnExactFunctor
public import StacksFrontier.CategoryTheory.Sites.DerivedPushforwardSheafify
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Acyclicity for the direct image along a cocontinuous functor, through `Ext`

Let `u : C ⥤ D` be a cocontinuous functor of sites and `u_*` the direct image of abelian sheaves
along it, the right Kan extension of the underlying presheaf along `uᵒᵖ`. For an object `y` of `D`
the sections of `u_* H` over `y` are the morphisms out of the free abelian sheaf `ℤ_{K_y}^♯` on the
presheaf of sets `K_y = h_y ∘ uᵒᵖ`, naturally in `H`; deriving, the value at `y` of the `n`-th
derived presheaf direct image of `H` is `Ext^n(ℤ_{K_y}^♯, H)`. The higher direct images are the
sheafifications of those derived presheaves
(`CategoryTheory.Functor.rightDerivedSheafPushforwardCocontinuousIso`), so `R^n u_* H = 0` as soon
as `Ext^n(ℤ_{K_y}^♯, H) = 0` for every `y`.

When `u` is the restriction `f'` of a 1-morphism of algebraic stacks to the lisse-étale or
flat-fppf sites, `K_y` is the presheaf `x ↦ Hom(f x, y)` restricted to the subsite, which is what
lets the descent of `Stacks.Sites.CoverDescent` compute these `Ext` groups.

## Main definitions

* `Stacks.Cohomology.CocontinuousPushforward.preadditiveCoyonedaIsoOfCompForget`: a
  corepresentation of the underlying functor of sets of an additive functor is a corepresentation
  as an additive functor.
* `Stacks.Cohomology.CocontinuousPushforward.pushforwardSectionsCorepresentation`: sections over
  `y` of the direct image along `u` are corepresented by `ℤ_{K_y}^♯`.

## Main results

* `Stacks.Cohomology.CocontinuousPushforward.isZero_rightDerived_sheafPushforwardCocontinuous`:
  `R^{n+1} u_* H = 0` when `Ext^{n+1}(ℤ_{K_y}^♯, H) = 0` for every object `y` of `D`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian

namespace Stacks.Cohomology.CocontinuousPushforward

section Corepresentation

universe v u

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜]

/-- **A corepresentation of the underlying functor of sets of an additive functor is additive.**
If `F : 𝒜 ⥤ Ab` is additive and its underlying functor of sets is corepresented by `X`, then `F`
itself is isomorphic to `Hom(X, -)` as a functor to abelian groups: the inverse of the
corepresentation sends `g : X ⟶ H` to `F(g)(ξ)` for the universal element `ξ`, which is additive
in `g` because `F` is. -/
def preadditiveCoyonedaIsoOfCompForget (F : 𝒜 ⥤ AddCommGrpCat.{v}) [F.Additive] (X : 𝒜)
    (e : F ⋙ forget AddCommGrpCat.{v} ≅ coyoneda.obj (op X)) :
    F ≅ preadditiveCoyoneda.obj (op X) := by
  have hinv : ∀ (H : 𝒜) (g : X ⟶ H), (e.app H).toEquiv.symm g =
      F.map g ((e.app X).toEquiv.symm (𝟙 X)) := fun H g => by
    have h := congrArg (fun φ => φ (𝟙 X)) (e.inv.naturality g)
    simpa using h
  have hadd : ∀ (H : 𝒜) (g g' : X ⟶ H), (e.app H).toEquiv.symm (g + g') =
      (e.app H).toEquiv.symm g + (e.app H).toEquiv.symm g' := fun H g g' => by
    rw [hinv H (g + g'), hinv H g, hinv H g', F.map_add]
    rfl
  refine NatIso.ofComponents (fun H => AddEquiv.toAddCommGrpIso
    { toEquiv := (e.app H).toEquiv
      map_add' := fun a b => by
        apply (e.app H).toEquiv.symm.injective
        change (e.app H).toEquiv.symm ((e.app H).toEquiv (a + b)) =
          (e.app H).toEquiv.symm ((show X ⟶ H from (e.app H).toEquiv a) +
            (show X ⟶ H from (e.app H).toEquiv b))
        rw [hadd, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        rfl })
    (fun {H H'} φ => ?_)
  refine AddCommGrpCat.ext fun a => ?_
  exact congrArg (fun ψ => ψ a) (e.hom.naturality φ)

end Corepresentation

universe v₁ v₂ w₁ w₂ a

variable {C : Type v₁} [Category.{w₁} C] {D : Type v₂} [Category.{w₂} D]
  (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasSheafify J AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}]
  [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}, u.op.HasPointwiseRightKanExtension P]
  [∀ P : Cᵒᵖ ⥤ Type (max v₁ v₂ w₁ w₂ a), u.op.HasPointwiseRightKanExtension P]

/-- The presheaf of sets `K_y = h_y ∘ uᵒᵖ` on `C`, whose free abelian sheaf corepresents sections
over `y` of the direct image along `u`. -/
abbrev restrictedYoneda (y : D) : Cᵒᵖ ⥤ Type (max v₁ v₂ w₁ w₂ a) :=
  u.op ⋙ uliftYoneda.{max v₁ v₂ w₁ a}.obj y

/-- Sections over `y` of the right Kan extension along `uᵒᵖ`, as a functor of sheaves of sets,
are morphisms out of `K_y`: the Yoneda lemma followed by the right Kan extension adjunction. -/
@[sga "4 I 5.4"]
def ranSectionsCoyonedaIso (y : D) :
    u.op.ran ⋙ (evaluation Dᵒᵖ (Type (max v₁ v₂ w₁ w₂ a))).obj (op y) ≅
      coyoneda.obj (op (restrictedYoneda.{v₁, v₂, w₁, w₂, a} u y)) :=
  Functor.isoWhiskerLeft u.op.ran
      (NatIso.ofComponents (fun P => Equiv.toIso
          (X := ((evaluation Dᵒᵖ (Type (max v₁ v₂ w₁ w₂ a))).obj (op y)).obj P)
          (Y := uliftYoneda.{max v₁ v₂ w₁ a}.obj y ⟶ P)
          (uliftYonedaEquiv.{max v₁ v₂ w₁ a} (X := y) (F := P)).symm)
        (fun {P P'} φ => by
          ext t
          exact uliftYonedaEquiv.{max v₁ v₂ w₁ a}.injective (by
            simp [uliftYonedaEquiv_comp])) :
        (evaluation Dᵒᵖ (Type (max v₁ v₂ w₁ w₂ a))).obj (op y) ≅
          coyoneda.obj (op (uliftYoneda.{max v₁ v₂ w₁ a}.obj y)))
    ≪≫ (((u.op.ranAdjunction (Type (max v₁ v₂ w₁ w₂ a))).compCoyonedaIso).app
      (op (uliftYoneda.{max v₁ v₂ w₁ a}.obj y))).symm

/-- **Sections over `y` of the direct image along `u` are corepresented by `ℤ_{K_y}^♯`**, as an
additive functor of the abelian sheaf. -/
def pushforwardSectionsCorepresentation (y : D) :
    sheafToPresheaf J AddCommGrpCat.{max v₁ v₂ w₁ w₂ a} ⋙ u.op.ran ⋙
        (evaluation Dᵒᵖ AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}).obj (op y) ≅
      preadditiveCoyoneda.obj
        (op ((Presheaf.freeAbelianSheaf J).obj (restrictedYoneda.{v₁, v₂, w₁, w₂, a} u y))) := by
  haveI := (u.op.ranAdjunction AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}).right_adjoint_additive
  refine preadditiveCoyonedaIsoOfCompForget _ _ ?_
  refine Functor.isoWhiskerLeft (sheafToPresheaf J AddCommGrpCat.{max v₁ v₂ w₁ w₂ a})
      (Functor.isoWhiskerRight
        ((forget AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}).ranCompIsoOfPreserves u.op)
        ((evaluation Dᵒᵖ (Type (max v₁ v₂ w₁ w₂ a))).obj (op y))) ≪≫ ?_
  refine Functor.isoWhiskerLeft (sheafToPresheaf J AddCommGrpCat.{max v₁ v₂ w₁ w₂ a} ⋙
      (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}))
      (ranSectionsCoyonedaIso.{v₁, v₂, w₁, w₂, a} u y) ≪≫ ?_
  exact (((Presheaf.freeAbelianSheafAdj J).compCoyonedaIso).app
    (op (restrictedYoneda.{v₁, v₂, w₁, w₂, a} u y))).symm

variable [u.IsCocontinuous J K] [HasSheafify K AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max v₁ v₂ w₁ w₂ a})]
  [HasExt.{max v₁ v₂ w₁ w₂ a} (Sheaf J AddCommGrpCat.{max v₁ v₂ w₁ w₂ a})]

/-- **A criterion for acyclicity for the direct image along a cocontinuous functor.** If
`Ext^{n+1}(ℤ_{K_y}^♯, H) = 0` for every object `y` of `D`, where `K_y = h_y ∘ uᵒᵖ`, then
`R^{n+1} u_* H = 0`. Indeed `R^{n+1} u_* H` is the sheafification of the `(n+1)`-th derived
presheaf direct image of `H`, whose value at `y` is `R^{n+1}` of sections over `y` of the direct
image, that is `Ext^{n+1}` out of the corepresenting object `ℤ_{K_y}^♯`. -/
@[sga "4 V 5.2" "special case"]
theorem isZero_rightDerived_sheafPushforwardCocontinuous
    (H : Sheaf J AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}) (n : ℕ)
    (h : ∀ (y : D) (b : Ext ((Presheaf.freeAbelianSheaf J).obj
      (restrictedYoneda.{v₁, v₂, w₁, w₂, a} u y)) H (n + 1)), b = 0) :
    letI := Functor.sheafPushforwardCocontinuous_additive.{v₁, v₂, w₁, w₂, a} u J K
    IsZero (((u.sheafPushforwardCocontinuous AddCommGrpCat.{max v₁ v₂ w₁ w₂ a} J K).rightDerived
      (n + 1)).obj H) := by
  let := Functor.sheafPushforwardCocontinuous_additive.{v₁, v₂, w₁, w₂, a} u J K
  have := (sheafificationAdjunction J AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}).right_adjoint_additive
  have := (u.op.ranAdjunction AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}).right_adjoint_additive
  refine IsZero.of_iso ?_
    ((Functor.rightDerivedSheafPushforwardCocontinuousIso.{v₁, v₂, w₁, w₂, a} u J K (n + 1)).app H)
  refine (presheafToSheaf K AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}).map_isZero
    (X := (Functor.derivedPresheafDirectImage.{v₁, v₂, w₁, w₂, a} J u (n + 1)).obj H) ?_
  rw [Functor.derivedPresheafDirectImage_eq]
  refine Functor.isZero _ (fun y => ?_)
  refine IsZero.of_iso ?_ ((Functor.rightDerivedCompIso
    (sheafToPresheaf J AddCommGrpCat.{max v₁ v₂ w₁ w₂ a} ⋙ u.op.ran)
    ((evaluation Dᵒᵖ AddCommGrpCat.{max v₁ v₂ w₁ w₂ a}).obj y) (n + 1)).app H).symm
  refine IsZero.of_iso ?_ ((Functor.rightDerivedIsoOfNatIso
    (pushforwardSectionsCorepresentation.{v₁, v₂, w₁, w₂, a} u J y.unop) (n + 1)).app H)
  refine IsZero.of_iso ?_
    ((ExtComparison.extFunctorObjIsoRightDerivedCoyoneda _ (n + 1)).app H).symm
  have : Subsingleton (Ext ((Presheaf.freeAbelianSheaf J).obj
      (restrictedYoneda.{v₁, v₂, w₁, w₂, a} u y.unop)) H (n + 1)) :=
    ⟨fun b b' => (h y.unop b).trans (h y.unop b').symm⟩
  show IsZero (AddCommGrpCat.of (Ext ((Presheaf.freeAbelianSheaf J).obj
      (restrictedYoneda.{v₁, v₂, w₁, w₂, a} u y.unop)) H (n + 1)))
  exact AddCommGrpCat.isZero_of_subsingleton _

end Stacks.Cohomology.CocontinuousPushforward
