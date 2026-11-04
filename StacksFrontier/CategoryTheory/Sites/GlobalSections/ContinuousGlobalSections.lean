module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.CategoryTheory.Sites.ConstantSheaf.FinalFunctor

/-!
# Restricting a global section along a continuous functor of sites

Let `u : C ⥤ D` be a continuous functor of sites `(C, J) ⟶ (D, K)` and let `A` be a coefficient
category in which both sites admit a global sections functor.  Restriction of sheaves along `u`
is `CategoryTheory.Functor.sheafPushforwardContinuous`, which on underlying presheaves is
precomposition with `uᵒᵖ`.  A global section of a sheaf `F` on `(D, K)` is in particular a
compatible family of sections over the objects `u(U)`, so it restricts to a global section of
`u⁻¹F`; that restriction is the natural transformation

`Γ(D, -) ⟶ u⁻¹(-) ⋙ Γ(C, -)`

constructed below.  No hypothesis beyond continuity is needed, and in particular neither site
need have a terminal object: global sections are a limit of the underlying presheaf by
`CategoryTheory.Sheaf.isLimitConeΓ` whether or not limits of that shape exist in `A`, and the
transformation is the comparison of that limit with the limit over the smaller index category.

`Stacks.ConstantSheaf.gammaCompRestrictionIsoOfFinal` of
`StacksFrontier/CategoryTheory/Sites/ConstantSheaf/FinalFunctor.lean` is the special case in which
`u` is **final**, where the comparison is an isomorphism; the point of this file is that the map
itself exists with no such hypothesis, which is what a tower of restrictions along a chain of
sites needs.  The last section records that at a final `u` — in particular at an *equivalence* of
sites, which is a right adjoint and hence final — the map built here *is* that isomorphism, so
the two global sections functors are identified by the canonical comparison and not merely by
some isomorphism.

## Main definitions

* `Stacks.Sites.globalSectionsAlongContinuousApp` — **the restriction map on global sections**
  `Γ(D, F) ⟶ Γ(C, u⁻¹F)` at a single sheaf.
* `Stacks.Sites.globalSectionsAlongContinuous` — the same as a natural transformation
  `Γ(D, -) ⟶ u⁻¹ ⋙ Γ(C, -)`.
* `Stacks.Sites.globalSectionsAlongContinuousIso` — **for a final `u`, that natural
  transformation as an isomorphism** `Γ(D, -) ≅ u⁻¹ ⋙ Γ(C, -)`.

## Main results

* `Stacks.Sites.globalSectionsAlongContinuousApp_comp_ΓRes` — **the map is pinned down**:
  restricting a global section of `F` to `u⁻¹F` and then to the object `U` of `C` is restricting
  it to `u(U)`.  Since `CategoryTheory.Sheaf.isLimitConeΓ` exhibits global sections as a limit
  with the maps `CategoryTheory.Sheaf.ΓRes` as its legs, this determines the map uniquely, so it
  is *the* comparison and not merely some map.
* `Stacks.Sites.isIso_globalSectionsAlongContinuous` — **for a final `u` the comparison is
  invertible**, being the inverse of `Stacks.ConstantSheaf.gammaRestrictionIsoApp`.

## What is and is not proved

Only the underived comparison is built, and nothing here derives it.  It is *not* an isomorphism
for a general continuous functor; the hypothesis under which it is one is finality of `u`, and
that is the only case treated.  No tag attribute is placed: the restriction of a global section
along a continuous functor is infrastructure, not a numbered assertion of the source.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₄ u₄ v₁ v₂ u₁ u₂

namespace Stacks.Sites

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (A : Type u₄) [Category.{v₄} A] [u.IsContinuous J K]
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  [HasGlobalSectionsFunctor J A] [HasGlobalSectionsFunctor K A]

/-- **The restriction map on global sections along a continuous functor of sites**,
`Γ(D, F) ⟶ Γ(C, u⁻¹F)`.  The underlying presheaf of `u⁻¹F` is `F ∘ uᵒᵖ`, whose limit is
`Γ(C, u⁻¹F)` by `CategoryTheory.Sheaf.isLimitConeΓ`; the map is the one induced by the cone
`Stacks.ConstantSheaf.coneΓRestrict`, whose legs are the restrictions of a global section of `F`
to the objects `u(U)`. -/
def globalSectionsAlongContinuousApp (F : Sheaf K A) :
    (Sheaf.Γ K A).obj F ⟶ (Sheaf.Γ J A).obj ((u.sheafPushforwardContinuous A J K).obj F) :=
  ((u.sheafPushforwardContinuous A J K).obj F).isLimitConeΓ.lift
    (ConstantSheaf.coneΓRestrict u K A F)

/-- **The restriction map on global sections is pinned down by the restriction maps**: a global
section of `F`, restricted to `u⁻¹F` and then to `U`, is its restriction to `u(U)`. -/
@[reassoc]
theorem globalSectionsAlongContinuousApp_comp_ΓRes (F : Sheaf K A) (U : Cᵒᵖ) :
    globalSectionsAlongContinuousApp u J K A F ≫
        ((u.sheafPushforwardContinuous A J K).obj F).ΓRes U =
      F.ΓRes (u.op.obj U) :=
  ((u.sheafPushforwardContinuous A J K).obj F).isLimitConeΓ.fac
    (ConstantSheaf.coneΓRestrict u K A F) U

/-- **Restriction of global sections along a continuous functor of sites**,

`Γ(D, -) ⟶ u⁻¹ ⋙ Γ(C, -)`,

naturally in the sheaf on `(D, K)`.  This is the underived comparison of global sections that a
chain of sites gives rise to; it is an isomorphism when `u` is final, by
`Stacks.ConstantSheaf.gammaCompRestrictionIsoOfFinal`, but is available with no hypothesis beyond
continuity. -/
def globalSectionsAlongContinuous :
    Sheaf.Γ K A ⟶ u.sheafPushforwardContinuous A J K ⋙ Sheaf.Γ J A where
  app F := globalSectionsAlongContinuousApp u J K A F
  naturality F G f := by
    refine ((u.sheafPushforwardContinuous A J K).obj G).isLimitConeΓ.hom_ext fun U => ?_
    have h₁ : ((Sheaf.Γ K A).map f ≫ globalSectionsAlongContinuousApp u J K A G) ≫
        ((u.sheafPushforwardContinuous A J K).obj G).ΓRes U =
        F.ΓRes (u.op.obj U) ≫ f.hom.app (u.op.obj U) := by
      rw [Category.assoc, globalSectionsAlongContinuousApp_comp_ΓRes]
      exact Sheaf.ΓRes_naturality f (u.op.obj U)
    have h₂ : (globalSectionsAlongContinuousApp u J K A F ≫
        (Sheaf.Γ J A).map ((u.sheafPushforwardContinuous A J K).map f)) ≫
        ((u.sheafPushforwardContinuous A J K).obj G).ΓRes U =
        F.ΓRes (u.op.obj U) ≫ f.hom.app (u.op.obj U) := by
      rw [Category.assoc, Sheaf.ΓRes_naturality, ← Category.assoc,
        globalSectionsAlongContinuousApp_comp_ΓRes]
      rfl
    exact h₁.trans h₂.symm

/-- The component of `globalSectionsAlongContinuous` at a sheaf `F` is
`globalSectionsAlongContinuousApp`. -/
@[simp]
theorem globalSectionsAlongContinuous_app (F : Sheaf K A) :
    (globalSectionsAlongContinuous u J K A).app F = globalSectionsAlongContinuousApp u J K A F :=
  rfl

/-! ### The comparison at a final functor -/

section Final

variable [u.Final]

/-- **At a final functor the comparison is the isomorphism of
`Stacks.ConstantSheaf.gammaRestrictionIsoApp`**, read backwards.  Both maps are induced on the
limit `Γ(C, u⁻¹F)` by the cone over `uᵒᵖ ⋙ F` whose legs are the restrictions of a global
section of `F` to the objects `u(U)`, so they agree by definition. -/
theorem globalSectionsAlongContinuousApp_eq_inv (F : Sheaf K A) :
    globalSectionsAlongContinuousApp u J K A F =
      (Stacks.ConstantSheaf.gammaRestrictionIsoApp u J K A F).inv :=
  rfl

/-- **Restriction of global sections along a final continuous functor is invertible**, at a
single sheaf. -/
instance isIso_globalSectionsAlongContinuousApp (F : Sheaf K A) :
    IsIso (globalSectionsAlongContinuousApp u J K A F) := by
  rw [globalSectionsAlongContinuousApp_eq_inv]
  infer_instance

/-- **Restriction of global sections along a final continuous functor is invertible.**  A
natural transformation whose every component is invertible is invertible. -/
instance isIso_globalSectionsAlongContinuous :
    IsIso (globalSectionsAlongContinuous u J K A) :=
  haveI (F : Sheaf K A) : IsIso ((globalSectionsAlongContinuous u J K A).app F) := by
    rw [globalSectionsAlongContinuous_app]
    infer_instance
  NatIso.isIso_of_isIso_app _

/-- **Restriction along a final continuous functor of sites does not change global sections**,

`Γ(D, -) ≅ u⁻¹ ⋙ Γ(C, -)`,

the isomorphism being the canonical comparison `globalSectionsAlongContinuous`.  This is
`Stacks.ConstantSheaf.gammaCompRestrictionIsoOfFinal` with the map named: the content beyond that
isomorphism is that it is the restriction map pinned down by
`globalSectionsAlongContinuousApp_comp_ΓRes`, so two sites identified by a final continuous
functor have their global sections identified by restriction of sections and nothing else. -/
def globalSectionsAlongContinuousIso :
    Sheaf.Γ K A ≅ u.sheafPushforwardContinuous A J K ⋙ Sheaf.Γ J A :=
  asIso (globalSectionsAlongContinuous u J K A)

/-- The forward map of `globalSectionsAlongContinuousIso` is `globalSectionsAlongContinuous`. -/
@[simp]
theorem globalSectionsAlongContinuousIso_hom :
    (globalSectionsAlongContinuousIso u J K A).hom = globalSectionsAlongContinuous u J K A :=
  rfl

/-- **The isomorphism is pinned down by the restriction maps**, as the comparison itself is. -/
@[reassoc]
theorem globalSectionsAlongContinuousIso_hom_app_comp_ΓRes (F : Sheaf K A) (U : Cᵒᵖ) :
    (globalSectionsAlongContinuousIso u J K A).hom.app F ≫
        ((u.sheafPushforwardContinuous A J K).obj F).ΓRes U =
      F.ΓRes (u.op.obj U) :=
  globalSectionsAlongContinuousApp_comp_ΓRes u J K A F U

end Final

end Stacks.Sites

end
