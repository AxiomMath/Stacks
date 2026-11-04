module

public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLiftFunctorial
public import StacksFrontier.CategoryTheory.Sites.AbelianInternalHomTensor

/-!
# The abelian internal Hom out of a sheaf of `Λ`-modules, as a sheaf of `Λᵒᵖ`-modules

Let `(C, K)` be a site, `Λ` a ring (not necessarily commutative) and `G` a sheaf of left
`Λ`-modules. The internal Hom `ℋom_ℤ(G, F)` of the underlying abelian sheaf of `G` into an
abelian sheaf `F` carries a right `Λ`-action, by precomposition with the endomorphisms `r • -`
of `G` (`Stacks.ModuleCatLift.sheafScalarEnd`). This file makes it a sheaf of `Λᵐᵒᵖ`-modules
whose underlying abelian sheaf is `internalHomSheaf K G F` on the nose, functorially in both
variables, and identifies its sections over a terminal object with the `Λᵐᵒᵖ`-module of
morphisms of abelian sheaves `G ⟶ F`.

## Main definitions

* `Stacks.AbelianInternalHom.homOpAction`: the action of `Λᵐᵒᵖ` on `ℋom_ℤ(G, F)`.
* `Stacks.AbelianInternalHom.homOpSheaf`: `ℋom_ℤ(G, F)` as a sheaf of `Λᵐᵒᵖ`-modules.
* `Stacks.AbelianInternalHom.homOpFunctor`: the same, as a functor of `F`, and
  `Stacks.AbelianInternalHom.homOpMapLeft` its contravariance in `G`.
* `Stacks.AbelianInternalHom.homOpSectionsIso`: its sections over a terminal object are the
  `Λᵐᵒᵖ`-module `G ⟶ F`.
* `Stacks.AbelianInternalHom.scalarEndComplex`: the action of `Λ` on the complex of abelian
  sheaves underlying a complex of sheaves of `Λ`-modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MulOpposite Stacks.ModuleCatLift

universe w v u

namespace Stacks.AbelianInternalHom

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) {Λ : Type w} [Ring Λ]

/-- The abelian sheaf underlying a sheaf of `Λ`-modules. -/
abbrev toAb (G : Sheaf K (ModuleCat.{max u v} Λ)) : Sheaf K AddCommGrpCat.{max u v} :=
  (sheafCompose K (forget₂ (ModuleCat.{max u v} Λ) AddCommGrpCat.{max u v})).obj G

/-- **The action of `Λ` on the complex of abelian sheaves underlying a complex `L` of sheaves
of `Λ`-modules**, degreewise by `r • -`. -/
def scalarEndComplex (L : CochainComplex (Sheaf K (ModuleCat.{max u v} Λ)) ℤ) :
    Λ →+* End (((sheafCompose K (forget₂ (ModuleCat.{max u v} Λ)
      AddCommGrpCat.{max u v})).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) where
  toFun r :=
    { f := fun n => sheafScalarEnd Λ K (L.X n) r
      comm' := fun i j _ => sheafScalarEnd_naturality Λ K (L.d i j) r }
  map_one' := HomologicalComplex.hom_ext _ _ fun n => (sheafScalarEnd Λ K (L.X n)).map_one
  map_mul' r s := HomologicalComplex.hom_ext _ _ fun n => (sheafScalarEnd Λ K (L.X n)).map_mul r s
  map_zero' := HomologicalComplex.hom_ext _ _ fun n => (sheafScalarEnd Λ K (L.X n)).map_zero
  map_add' r s := HomologicalComplex.hom_ext _ _ fun n =>
    (sheafScalarEnd Λ K (L.X n)).map_add r s

/-- In degree `n`, `scalarEndComplex K L r` is the action `r • -` on `L.X n`. -/
lemma scalarEndComplex_f (L : CochainComplex (Sheaf K (ModuleCat.{max u v} Λ)) ℤ) (r : Λ)
    (n : ℤ) : (scalarEndComplex K L r).f n = sheafScalarEnd Λ K (L.X n) r := rfl

section HomOp

variable (G : Sheaf K (ModuleCat.{max u v} Λ))

/-- Precomposition with an endomorphism of `G`, on `ℋom_ℤ(G, F)`. -/
def precompEnd (F : Sheaf K AddCommGrpCat.{max u v}) (e : End (toAb K G)) :
    End (internalHomSheaf K (toAb K G) F) :=
  (internalHomFunctor K F).map e.op

/-- On sections over `U`, `precompEnd K G F e` sends `a` to the restriction of `e` to the slice
over `U` composed with `a`. -/
lemma precompEnd_hom_app_apply (F : Sheaf K AddCommGrpCat.{max u v}) (e : End (toAb K G))
    (U : Cᵒᵖ) (a : (internalHomSheaf K (toAb K G) F).obj.obj U) :
    ((precompEnd K G F e).hom.app U).hom a =
      Functor.whiskerLeft (Over.forget U.unop).op e.hom ≫ a :=
  rfl

/-- **The action of `Λᵐᵒᵖ` on `ℋom_ℤ(G, F)`**: `op r` acts by precomposition with `r • -`. -/
def homOpAction (F : Sheaf K AddCommGrpCat.{max u v}) :
    Λᵐᵒᵖ →+* End (internalHomSheaf K (toAb K G) F) where
  toFun r := precompEnd K G F (sheafScalarEnd Λ K G r.unop)
  map_one' := by
    rw [MulOpposite.unop_one, map_one]
    exact (internalHomFunctor K F).map_id _
  map_mul' r s := by
    rw [MulOpposite.unop_mul, map_mul]
    exact (internalHomFunctor K F).map_comp _ _
  map_zero' := by
    rw [MulOpposite.unop_zero, map_zero]
    exact (internalHomFunctor K F).map_zero _ _
  map_add' r s := by
    rw [MulOpposite.unop_add, map_add]
    refine Sheaf.hom_ext (NatTrans.ext (funext fun U => AddCommGrpCat.hom_ext
      (AddMonoidHom.ext fun x => NatTrans.ext (funext fun W => AddCommGrpCat.hom_ext
        (AddMonoidHom.ext fun y => ?_)))))
    exact map_add (x.app W).hom _ _

/-- **`ℋom_ℤ(G, F)` as a sheaf of `Λᵐᵒᵖ`-modules.** -/
def homOpSheaf (F : Sheaf K AddCommGrpCat.{max u v}) : Sheaf K (ModuleCat.{max u v} Λᵐᵒᵖ) :=
  sheafOfEndAction Λᵐᵒᵖ K (internalHomSheaf K (toAb K G) F) (homOpAction K G F)

/-- Postcomposition with a morphism of abelian sheaves, on `ℋom_ℤ(G, -)`. -/
def homOpMap {F F' : Sheaf K AddCommGrpCat.{max u v}} (g : F ⟶ F') :
    homOpSheaf K G F ⟶ homOpSheaf K G F' :=
  ObjectProperty.homMk (ofEndActionMap Λᵐᵒᵖ _ _ ((internalHomRightFunctor K (toAb K G)).map g).hom
    fun _ => rfl)

/-- **`ℋom_ℤ(G, -)` from abelian sheaves to sheaves of `Λᵐᵒᵖ`-modules.** -/
@[simps obj]
def homOpFunctor : Sheaf K AddCommGrpCat.{max u v} ⥤ Sheaf K (ModuleCat.{max u v} Λᵐᵒᵖ) where
  obj F := homOpSheaf K G F
  map g := homOpMap K G g
  map_id F := (sheafCompose K (forget₂ (ModuleCat.{max u v} Λᵐᵒᵖ)
    AddCommGrpCat.{max u v})).map_injective
      (by exact (internalHomRightFunctor K (toAb K G)).map_id F)
  map_comp f g := (sheafCompose K (forget₂ (ModuleCat.{max u v} Λᵐᵒᵖ)
    AddCommGrpCat.{max u v})).map_injective
      (by exact (internalHomRightFunctor K (toAb K G)).map_comp f g)

/-- **The abelian sheaf underlying `ℋom_ℤ(G, F)` is `internalHomSheaf K G F`**, naturally in
`F`. -/
def homOpFunctorForgetIso :
    homOpFunctor K G ⋙ sheafCompose K (forget₂ (ModuleCat.{max u v} Λᵐᵒᵖ) AddCommGrpCat.{max u v}) ≅
      internalHomRightFunctor K (toAb K G) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- Precomposition with a morphism `φ : G₁ ⟶ G₂` of sheaves of `Λ`-modules, on
`ℋom_ℤ(-, F)`. It is `Λᵐᵒᵖ`-linear because `φ` commutes with the actions. -/
def homOpMapLeft {G₁ G₂ : Sheaf K (ModuleCat.{max u v} Λ)} (φ : G₁ ⟶ G₂)
    (F : Sheaf K AddCommGrpCat.{max u v}) : homOpSheaf K G₂ F ⟶ homOpSheaf K G₁ F :=
  ObjectProperty.homMk (ofEndActionMap Λᵐᵒᵖ _ _
    ((internalHomFunctor K F).map
      ((sheafCompose K (forget₂ (ModuleCat.{max u v} Λ) AddCommGrpCat.{max u v})).map φ).op).hom
    fun r => by
      change ((internalHomFunctor K F).map _ ≫ (internalHomFunctor K F).map _).hom =
        ((internalHomFunctor K F).map _ ≫ (internalHomFunctor K F).map _).hom
      rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
        sheafScalarEnd_naturality])

section Sections

variable {T : C} (hT : IsTerminal T) (F : Sheaf K AddCommGrpCat.{max u v})

/-- The `Λᵐᵒᵖ`-module structure on morphisms of abelian sheaves out of `G`:
`op r • φ = (r • -) ≫ φ`. -/
abbrev sheafHomModule : Module Λᵐᵒᵖ (toAb K G ⟶ F) :=
  Module.compHom _ (RingHom.op (sheafScalarEnd Λ K G))

/-- Restriction of a morphism of abelian sheaves to the slice over `T`. -/
def restrictToTerminal : letI := sheafHomModule K G F
    (toAb K G ⟶ F) →ₗ[Λᵐᵒᵖ]
      ((sheafSections K (ModuleCat.{max u v} Λᵐᵒᵖ)).obj (op T)).obj (homOpSheaf K G F) :=
  letI := sheafHomModule K G F
  { toFun := fun φ => Functor.whiskerLeft (Over.forget T).op φ.hom
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- `restrictToTerminal` sends `φ` to its whiskering along the forgetful functor from the slice
over `T`. -/
lemma restrictToTerminal_apply (φ : toAb K G ⟶ F) :
    restrictToTerminal (T := T) K G F φ = Functor.whiskerLeft (Over.forget T).op φ.hom := rfl

include hT in
/-- For `T` terminal, `restrictToTerminal` is bijective. -/
lemma bijective_restrictToTerminal : Function.Bijective (restrictToTerminal (T := T) K G F) := by
  let e := (Over.equivalenceOfIsTerminal hT).op.congrLeft (E := AddCommGrpCat.{max u v})
  exact (e.fullyFaithfulInverse.map_bijective _ _).comp
    ((fullyFaithfulSheafToPresheaf K AddCommGrpCat.{max u v}).map_bijective _ _)

/-- **The sections of `ℋom_ℤ(G, F)` over a terminal object are the `Λᵐᵒᵖ`-module of morphisms
of abelian sheaves `G ⟶ F`**, a section being the restriction of a morphism to the slice. -/
def homOpSectionsIso :
    ((sheafSections K (ModuleCat.{max u v} Λᵐᵒᵖ)).obj (op T)).obj (homOpSheaf K G F) ≅
      (letI := sheafHomModule K G F; ModuleCat.of Λᵐᵒᵖ (toAb K G ⟶ F)) :=
  letI := sheafHomModule K G F
  (LinearEquiv.ofBijective _ (bijective_restrictToTerminal K G hT F)).toModuleIso.symm

/-- The inverse of `homOpSectionsIso` sends `φ` to its whiskering along the forgetful functor from
the slice over `T`. -/
lemma homOpSectionsIso_inv_apply (φ : toAb K G ⟶ F) :
    (homOpSectionsIso K G hT F).inv.hom φ = Functor.whiskerLeft (Over.forget T).op φ.hom := rfl

end Sections

end HomOp

end Stacks.AbelianInternalHom
