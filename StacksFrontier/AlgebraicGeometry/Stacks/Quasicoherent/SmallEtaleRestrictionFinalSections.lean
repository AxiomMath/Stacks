module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.CategoryTheory.Sites.GlobalSections

/-!
# The global sections of a small étale restriction

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, `x` an object of `𝒳` lying over
a scheme `U` and `F` a presheaf on `𝒳`, and let `F|_{U_ét}` be the restriction of Stacks 06W1 of
`F` to the small étale site of `U`, whose final object is `U / U`. This file identifies the
global sections of the restriction with the sections of `F` at `x`:

`Γ(U_ét, F|_{U_ét}) ≅ F(x)`,

the identification being given by the counit of the localization equivalence of Stacks 06W0 at
the final object.

## Main definitions

* `AlgebraicGeometry.Stack.smallEtaleFinal`: the final object `U / U` of the small étale site of
  the scheme below an object `x`.
* `AlgebraicGeometry.Stack.smallEtaleFinalObject`: the object of `𝒳` at which the restriction to
  the small étale site reads the global sections.
* `AlgebraicGeometry.Stack.smallEtaleFinalObjectIso`: that object is isomorphic to `x`.

## Main results

* `AlgebraicGeometry.Stack.restrictToSmallEtaleFinalIso`: **the sections at the final object of
  the small étale site of `U` of the restriction of a presheaf `F` at `x` are the sections of
  `F` at `x`.**
* `AlgebraicGeometry.Stack.restrictToSmallEtaleFinalIso_hom_naturality`: that identification is
  natural in the presheaf.
* `AlgebraicGeometry.Stack.restrictModuleToSmallEtaleFinalIso`: the same for the restriction of
  a presheaf of modules of Stacks 06WJ, on underlying abelian groups.
* `AlgebraicGeometry.Stack.globalSectionsRestrictToSmallEtaleEquiv`: **`Γ(U_ét, F|_{U_ét}) =
  F(x)`**, with the global sections those of Stacks 06UN.
* `CategoryTheory.Presheaf.globalSectionsEquivObjOfIsTerminal`: on a category with a terminal
  object the global sections of Stacks 06UN are the sections at the terminal object.

## References

* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
* [Stacks Project, Tag 06W1](https://stacks.math.columbia.edu/tag/06W1)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w t s m

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] {T : C}

/-- On a category with a terminal object, the compatible families of sections of a presheaf of
sets are the sections at the terminal object. -/
@[sga "7 VII 1.1.2.1" "special case"]
def sectionsEquivObjOfIsTerminal (hT : IsTerminal T) (F : Cᵒᵖ ⥤ Type w) :
    F.sections ≃ F.obj (op T) where
  toFun s := s.val (op T)
  invFun a :=
    ⟨fun W ↦ F.map (hT.from W.unop).op a, fun {W W'} f ↦ by
      rw [← Functor.map_comp_apply, show (hT.from W.unop).op ≫ f = (hT.from W'.unop).op from
        Quiver.Hom.unop_inj (hT.hom_ext _ _)]⟩
  left_inv s := by
    ext W
    exact s.property (hT.from W.unop).op
  right_inv a := by
    simp only [show hT.from T = 𝟙 T from hT.hom_ext _ _, op_id, Functor.map_id_apply]

/-- The global sections `Γ(C, F)` of Stacks 06UN of a presheaf of sets over a category with a
terminal object `T` are the sections of `F` at `T`. -/
noncomputable def globalSectionsEquivObjOfIsTerminal (hT : IsTerminal T) (F : Cᵒᵖ ⥤ Type w) :
    globalSections F ≃ F.obj (op T) :=
  (globalSectionsEquivSections F).trans (sectionsEquivObjOfIsTerminal hT F)

end CategoryTheory.Presheaf

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (x : 𝒳)

/-- The final object `U / U` of the small étale site of the scheme `U` below an object `x` of a
category fibred in groupoids. -/
abbrev smallEtaleFinal : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x) :=
  SmallEtale.final E (p.obj x).left.1 (contains_base B E h S hS p x)

/-- The image of the final object of the small étale site of `U` in the big fppf slice over `U`
is `U / U` there as well, hence terminal. -/
noncomputable def isTerminal_smallEtaleInclusion_obj_final :
    IsTerminal ((smallEtaleInclusion B E h (p.obj x).left.1
      (contains_base B E h S hS p x)).obj (smallEtaleFinal B E h S hS p x)) :=
  Over.mkIdTerminal

/-- The object of `𝒳` at which the restriction of Stacks 06W1 reads the global sections over the
small étale site of `U`: the final object `U / U`, transported back across the localization
equivalence of Stacks 06W0 and read in `𝒳`. -/
noncomputable abbrev smallEtaleFinalObject : 𝒳 :=
  letI := isEquivalence_overPost B S hS p hp x
  ((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv.obj
    ((smallEtaleInclusion B E h (p.obj x).left.1
      (contains_base B E h S hS p x)).obj (smallEtaleFinal B E h S hS p x))).left

/-- **The counit of the equivalence of Stacks 06W0 at the final object of the small étale
site.** The object of `𝒳` carrying the global sections of a small étale restriction at `x` is
isomorphic to `x`. -/
noncomputable def smallEtaleFinalObjectIso :
    smallEtaleFinalObject B E h S hS p hp x ≅ x :=
  letI := isEquivalence_overPost B S hS p hp x
  (Over.forget x).mapIso
    ((IsTerminal.isTerminalObj (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv _
      (isTerminal_smallEtaleInclusion_obj_final B E h S hS p x)).uniqueUpToIso Over.mkIdTerminal)

/-- **The global sections over the small étale site of `U` of the restriction of a presheaf at
an object `x` are the sections of that presheaf at `x`.** Here the global sections are the
sections at the final object `U / U`. -/
noncomputable def restrictToSmallEtaleFinalIso {A : Type t} [Category.{s} A] (F : 𝒳ᵒᵖ ⥤ A) :
    (restrictToSmallEtale B E h S hS p hp x F).obj (op (smallEtaleFinal B E h S hS p x)) ≅
      F.obj (op x) :=
  (F.mapIso (smallEtaleFinalObjectIso B E h S hS p hp x).op).symm

/-- The identification of the global sections of a small étale restriction with the sections at
the object is restriction along the counit of Stacks 06W0. -/
@[simp]
theorem restrictToSmallEtaleFinalIso_hom {A : Type t} [Category.{s} A] (F : 𝒳ᵒᵖ ⥤ A) :
    (restrictToSmallEtaleFinalIso B E h S hS p hp x F).hom =
      F.map (smallEtaleFinalObjectIso B E h S hS p hp x).inv.op :=
  rfl

/-- The identification of the global sections of a small étale restriction with the sections at
the object is natural in the presheaf. -/
theorem restrictToSmallEtaleFinalIso_hom_naturality {A : Type t} [Category.{s} A]
    {F G : 𝒳ᵒᵖ ⥤ A} (α : F ⟶ G) :
    α.app (op (smallEtaleFinalObject B E h S hS p hp x)) ≫
        (restrictToSmallEtaleFinalIso B E h S hS p hp x G).hom =
      (restrictToSmallEtaleFinalIso B E h S hS p hp x F).hom ≫ α.app (op x) :=
  (α.naturality (smallEtaleFinalObjectIso B E h S hS p hp x).inv.op).symm

/-- **The global sections over the small étale site of `U` of the restriction of a presheaf of
modules at `x` are the sections at `x`**, as abelian groups, for the restriction of
Stacks 06WJ. -/
noncomputable def restrictModuleToSmallEtaleFinalIso (τ : GrothendieckTopology B.Schemes)
    (hτ : τ ≤ B.topology)
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ).obj) :
    (restrictModuleToSmallEtale B E h S hS p hp x τ hτ F).presheaf.obj
        (op (smallEtaleFinal B E h S hS p x)) ≅
      F.presheaf.obj (op x) :=
  restrictToSmallEtaleFinalIso B E h S hS p hp x F.presheaf

/-- **`Γ(U_ét, F|_{U_ét}) = F(x)`.** The global sections, in the sense of Stacks 06UN, over the
small étale site of the scheme `U` below `x` of the restriction of Stacks 06W1 of a presheaf of
sets `F` on `𝒳` are the sections of `F` at `x`. -/
noncomputable def globalSectionsRestrictToSmallEtaleEquiv (F : 𝒳ᵒᵖ ⥤ Type t) :
    Presheaf.globalSections (restrictToSmallEtale B E h S hS p hp x F) ≃ F.obj (op x) :=
  (Presheaf.globalSectionsEquivObjOfIsTerminal
    (SmallEtale.finalIsTerminal E (p.obj x).left.1 (contains_base B E h S hS p x))
    (restrictToSmallEtale B E h S hS p hp x F)).trans
      (restrictToSmallEtaleFinalIso B E h S hS p hp x F).toEquiv

end AlgebraicGeometry.Stack

end
