module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLift

/-!
# Adjunctions between lifts of additive functors on abelian sheaves

Let `Λ` be a ring and let `L ⊣ R` be an adjunction between additive functors on categories of
abelian sheaves. The lifts of `L` and `R` to sheaves of `Λ`-modules are again adjoint, with the
hom-set bijection the restriction of the original one to the `Λ`-linear morphisms.

## Main definitions

* `Stacks.ModuleCatLift.sheafHomOfScalarComm` — a morphism of the underlying abelian sheaves
  commuting with multiplication by scalars, read as a morphism of sheaves of `Λ`-modules.
* `Stacks.ModuleCatLift.moduleLiftAdjunction` — the lift of an adjunction.

## Main results

* `Stacks.ModuleCatLift.sheafCompose_map_moduleLiftAdjunction_counit_app` and
  `Stacks.ModuleCatLift.sheafCompose_map_moduleLiftAdjunction_unit_app` — **the lifted adjunction
  lifts the unit and the counit.** Forgetting the `Λ`-module structure of the unit or the counit
  of the lift returns the unit or the counit of the adjunction it was lifted from.

## Implementation notes

A morphism of sheaves of `Λ`-modules is a morphism of the underlying abelian sheaves which is
`Λ`-linear, and `Λ`-linearity is exactly commutation with
`Stacks.ModuleCatLift.sheafScalarEnd`; `sheafHomOfScalarComm` is that identification, and
forgetting the module structure of what it produces returns the morphism it was given. The
action of `Λ` on a lift is the image of the action under the functor, so the commutation
condition for the transpose of a `Λ`-linear morphism is the image of the commutation condition
for the morphism under the hom-set bijection, which is the naturality of that bijection. All
the equations are checked on the underlying abelian sheaves, where the two lifts are the
original functors.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w r u₁ v₁ u₂ v₂

namespace Stacks.ModuleCatLift

section Hom

variable (Λ : Type r) [Ring Λ] {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- A morphism of the abelian sheaves underlying two sheaves of `Λ`-modules which commutes with
multiplication by scalars is a morphism of sheaves of `Λ`-modules. -/
public def sheafHomOfScalarComm {F G : Sheaf J (ModuleCat.{w} Λ)}
    (α : (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F ⟶
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj G)
    (hα : ∀ a : Λ, (sheafScalarEnd Λ J F a).asHom ≫ α = α ≫ (sheafScalarEnd Λ J G a).asHom) :
    F ⟶ G :=
  ObjectProperty.homMk
    { app U := ModuleCat.homMk (α.hom.app U)
        fun a => (NatTrans.congr_app (congrArg InducedCategory.Hom.hom (hα a)) U).symm
      naturality _ _ g := (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).map_injective
        (α.hom.naturality g) }

/-- Forgetting the `Λ`-module structure of `sheafHomOfScalarComm Λ J α hα` returns `α`. -/
@[simp]
public lemma sheafCompose_map_sheafHomOfScalarComm {F G : Sheaf J (ModuleCat.{w} Λ)}
    (α : (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F ⟶
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj G)
    (hα : ∀ a : Λ, (sheafScalarEnd Λ J F a).asHom ≫ α = α ≫ (sheafScalarEnd Λ J G a).asHom) :
    (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
        (sheafHomOfScalarComm Λ J α hα) = α :=
  rfl

end Hom

section Lift

variable (Λ : Type r) [Ring Λ] {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂}
  [Category.{v₂} C₂] (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
  [J₁.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [J₂.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- Multiplication by a scalar on the abelian sheaf underlying the lift of `G` is the image
under `G` of multiplication by that scalar. -/
public lemma sheafScalarEnd_moduleLift_obj
    (G : Sheaf J₁ AddCommGrpCat.{w} ⥤ Sheaf J₂ AddCommGrpCat.{w}) [G.Additive]
    (F : Sheaf J₁ (ModuleCat.{w} Λ)) (a : Λ) :
    (sheafScalarEnd Λ J₂ ((moduleLift Λ J₁ J₂ G).obj F) a).asHom =
      G.map (sheafScalarEnd Λ J₁ F a).asHom :=
  rfl

/-- Forgetting the `Λ`-module structure of the morphism the lift of `G` produces gives `G`
applied to the morphism of underlying abelian sheaves. -/
@[simp]
public lemma sheafCompose_map_moduleLift_map
    (G : Sheaf J₁ AddCommGrpCat.{w} ⥤ Sheaf J₂ AddCommGrpCat.{w}) [G.Additive]
    {F₁ F₂ : Sheaf J₁ (ModuleCat.{w} Λ)} (φ : F₁ ⟶ F₂) :
    (sheafCompose J₂ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
        ((moduleLift Λ J₁ J₂ G).map φ) =
      G.map ((sheafCompose J₁ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map φ) :=
  rfl

variable (L : Sheaf J₁ AddCommGrpCat.{w} ⥤ Sheaf J₂ AddCommGrpCat.{w}) [L.Additive]
  (R : Sheaf J₂ AddCommGrpCat.{w} ⥤ Sheaf J₁ AddCommGrpCat.{w}) [R.Additive]

/-- The hom-set bijection of an adjunction `L ⊣ R`, restricted to the `Λ`-linear morphisms:
the transpose of a `Λ`-linear morphism is `Λ`-linear, the action of `Λ` on a lift being the
image of the action under the functor. -/
public def moduleLiftHomEquiv (adj : L ⊣ R) (F : Sheaf J₁ (ModuleCat.{w} Λ))
    (G : Sheaf J₂ (ModuleCat.{w} Λ)) :
    ((moduleLift Λ J₁ J₂ L).obj F ⟶ G) ≃ (F ⟶ (moduleLift Λ J₂ J₁ R).obj G) where
  toFun φ := sheafHomOfScalarComm Λ J₁
    (adj.homEquiv _ _ ((sheafCompose J₂
      (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map φ)) (fun a => by
      have h := sheafScalarEnd_naturality Λ J₂ φ a
      rw [sheafScalarEnd_moduleLift_obj] at h
      rw [sheafScalarEnd_moduleLift_obj]
      exact (adj.homEquiv_naturality_left_square_iff _ _ _ _).2 h)
  invFun ψ := sheafHomOfScalarComm Λ J₂
    ((adj.homEquiv _ _).symm ((sheafCompose J₁
      (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map ψ)) (fun a => by
      have h := sheafScalarEnd_naturality Λ J₁ ψ a
      rw [sheafScalarEnd_moduleLift_obj] at h
      rw [sheafScalarEnd_moduleLift_obj]
      exact (adj.homEquiv_naturality_right_square_iff _ _ _ _).2 h)
  left_inv φ := (sheafCompose J₂
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map_injective
      ((adj.homEquiv _ _).symm_apply_apply _)
  right_inv ψ := (sheafCompose J₁
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map_injective
      ((adj.homEquiv _ _).apply_symm_apply _)

/-- Forgetting the `Λ`-module structure of the image of `φ` under `moduleLiftHomEquiv` gives the
transpose under `adj` of the underlying morphism of abelian sheaves. -/
@[simp]
public lemma sheafCompose_map_moduleLiftHomEquiv (adj : L ⊣ R)
    {F : Sheaf J₁ (ModuleCat.{w} Λ)} {G : Sheaf J₂ (ModuleCat.{w} Λ)}
    (φ : (moduleLift Λ J₁ J₂ L).obj F ⟶ G) :
    (sheafCompose J₁ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
        (moduleLiftHomEquiv Λ J₁ J₂ L R adj F G φ) =
      adj.homEquiv _ _ ((sheafCompose J₂
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map φ) :=
  rfl

/-- Forgetting the `Λ`-module structure of the image of `ψ` under the inverse of
`moduleLiftHomEquiv` gives the inverse transpose under `adj` of the underlying morphism of abelian
sheaves. -/
@[simp]
public lemma sheafCompose_map_moduleLiftHomEquiv_symm (adj : L ⊣ R)
    {F : Sheaf J₁ (ModuleCat.{w} Λ)} {G : Sheaf J₂ (ModuleCat.{w} Λ)}
    (ψ : F ⟶ (moduleLift Λ J₂ J₁ R).obj G) :
    (sheafCompose J₂ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
        ((moduleLiftHomEquiv Λ J₁ J₂ L R adj F G).symm ψ) =
      (adj.homEquiv _ _).symm ((sheafCompose J₁
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map ψ) :=
  rfl

/-- **The lift of an adjunction.** If `L ⊣ R` is an adjunction between additive functors on
abelian sheaves, then the lifts of `L` and `R` to sheaves of `Λ`-modules are adjoint, with
hom-set bijection the restriction of the given one to the `Λ`-linear morphisms. -/
public def moduleLiftAdjunction (adj : L ⊣ R) :
    moduleLift Λ J₁ J₂ L ⊣ moduleLift Λ J₂ J₁ R :=
  Adjunction.mkOfHomEquiv
    { homEquiv := moduleLiftHomEquiv Λ J₁ J₂ L R adj
      homEquiv_naturality_left_symm _ _ := (sheafCompose J₂
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map_injective (by
          simp only [Functor.map_comp, sheafCompose_map_moduleLiftHomEquiv_symm,
            sheafCompose_map_moduleLift_map]
          exact adj.homEquiv_naturality_left_symm _ _)
      homEquiv_naturality_right _ _ := (sheafCompose J₁
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map_injective (by
          simp only [Functor.map_comp, sheafCompose_map_moduleLiftHomEquiv,
            sheafCompose_map_moduleLift_map]
          exact adj.homEquiv_naturality_right _ _) }

/-- **The counit of the lifted adjunction lifts the counit.** Forgetting the `Λ`-module structure
of the counit of `Stacks.ModuleCatLift.moduleLiftAdjunction` returns the counit of the adjunction
it was lifted from. The counit is the transpose of the identity, and the hom-set bijection of the
lift is the restriction of the given one. -/
@[simp]
public lemma sheafCompose_map_moduleLiftAdjunction_counit_app (adj : L ⊣ R)
    (G : Sheaf J₂ (ModuleCat.{w} Λ)) :
    (sheafCompose J₂ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
        ((moduleLiftAdjunction Λ J₁ J₂ L R adj).counit.app G) =
      adj.counit.app ((sheafCompose J₂
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj G) := by
  change (sheafCompose J₂ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
      ((moduleLiftHomEquiv Λ J₁ J₂ L R adj ((moduleLift Λ J₂ J₁ R).obj G) G).symm
        (𝟙 ((moduleLift Λ J₂ J₁ R).obj G))) = _
  rw [sheafCompose_map_moduleLiftHomEquiv_symm, CategoryTheory.Functor.map_id]
  exact adj.homEquiv_symm_id _

/-- **The unit of the lifted adjunction lifts the unit.** Forgetting the `Λ`-module structure of
the unit of `Stacks.ModuleCatLift.moduleLiftAdjunction` returns the unit of the adjunction it was
lifted from. -/
@[simp]
public lemma sheafCompose_map_moduleLiftAdjunction_unit_app (adj : L ⊣ R)
    (F : Sheaf J₁ (ModuleCat.{w} Λ)) :
    (sheafCompose J₁ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
        ((moduleLiftAdjunction Λ J₁ J₂ L R adj).unit.app F) =
      adj.unit.app ((sheafCompose J₁
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F) := by
  change (sheafCompose J₁ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
      (moduleLiftHomEquiv Λ J₁ J₂ L R adj F ((moduleLift Λ J₁ J₂ L).obj F)
        (𝟙 ((moduleLift Λ J₁ J₂ L).obj F))) = _
  rw [sheafCompose_map_moduleLiftHomEquiv, CategoryTheory.Functor.map_id]
  exact adj.homEquiv_id _

end Lift

end Stacks.ModuleCatLift

end
