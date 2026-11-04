module

public import StacksFrontier.AlgebraicGeometry.RelativeSpecRepresentability.Basic

/-!
# Morphisms out of a quasi-coherent algebra over an affine base

Let `X` be an affine scheme, let `A` be a quasi-coherent sheaf of commutative `𝒪_X`-algebras and
let `B` be an *arbitrary* sheaf of commutative `𝒪_X`-algebras.  This file proves that taking
global sections is a bijection
```
Hom_{𝒪_X-alg}(A, B) ≃ {χ : A(X) ⟶ B(X) // the structure maps commute with χ}.
```

This is the universal property of the relative spectrum over an affine base in the form in which
it tests against an arbitrary algebra sheaf, and not only against a pushed-forward structure
sheaf `f_* 𝒪_T`.  The case of `B = f_* 𝒪_T` is Stacks Tag 01LT, which is
`Stacks.RelativeSpec.pairEquivRingHom`; the content here is that nothing about the target is
used beyond its being a sheaf of `𝒪_X`-algebras.  That generality is what is needed in order to
*verify a universal property* of an algebra sheaf, as opposed to using one: a cocone of sheaves
of commutative rings has an arbitrary sheaf of rings at its tip.

## Main definitions

* `Stacks.RelativeSpec.AlgebraSheaf.algebraBasisComp` is the component over a basic open of the
  morphism determined by a ring map on global sections, and
  `Stacks.RelativeSpec.AlgebraSheaf.algebraHomOfRingHom` is the morphism of presheaves of
  commutative rings obtained by gluing those components over the basis of basic opens.
* `Stacks.RelativeSpec.AlgebraSheaf.algebraHom` promotes it to a morphism of algebra sheaves,
  i.e. to a morphism in `Under X.sheaf`.
* `Stacks.RelativeSpec.AlgebraSheaf.homEquivUnitTopHom` is the bijection displayed above.

## Main results

* `Stacks.RelativeSpec.AlgebraSheaf.hom_ext_app_top`: a morphism of sheaves of commutative rings
  out of a quasi-coherent algebra over an affine base is determined by its component on global
  sections.  The target is an arbitrary sheaf.
* `Stacks.RelativeSpec.AlgebraSheaf.algebraHom_right_app_top`: the morphism of algebra sheaves
  built from `χ` has `χ` as its component on global sections.

## Implementation notes

The three ingredients are already available for a quasi-coherent algebra over an affine base and
are reused unchanged: the sections over the basic open of `a` are the localization of the global
sections away from the image of `a`
(`Stacks.RelativeSpec.AlgebraSheaf.isLocalization_sections_basicOpen`), two ring maps out of
them agreeing after restriction are equal
(`Stacks.RelativeSpec.AlgebraSheaf.sections_basicOpen_hom_ext`), and a ring map on global
sections carrying the image of `a` to a unit extends over the basic open
(`Stacks.RelativeSpec.AlgebraSheaf.sectionsLift`).

What replaces the computation `f⁻¹ X_a = T_{f^♯ a}` of the pushed-forward case is simpler, and
is `Stacks.RelativeSpec.AlgebraSheaf.isUnit_res_unitTop`: the image of `a` in `B(X_a)` is a unit
because `a` restricts to a unit in `𝒪_X(X_a)` and `B` is an `𝒪_X`-algebra.  No preimage of an
open and no comparison of basic opens on a second scheme occurs.

Gluing from the basis of basic opens to all opens is `TopCat.Sheaf.restrictHomEquivHom`, which
needs the *target* to be a sheaf and the source only to be a presheaf; the component on global
sections is recovered from the components on basic opens through `X.basicOpen 1 = ⊤`, exactly as
in the pushed-forward case.

## References

* [Stacks Project, Tag 01LR](https://stacks.math.columbia.edu/tag/01LR)
* [Stacks Project, Tag 01LT](https://stacks.math.columbia.edu/tag/01LT)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.RelativeSpec

namespace AlgebraSheaf

variable {X : Scheme.{u}}

/-! ### The structure map of an arbitrary algebra sheaf on a basic open -/

/-- Pushing a global section of the structure sheaf into an algebra sheaf and then restricting it
to an open agrees with restricting it first. -/
theorem unitTop_comp_res (B : AlgebraSheaf.{u} X) (U : X.Opens) :
    B.unitTop ≫ B.res U =
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ B.hom.hom.app (op U) :=
  (B.presheaf_map_comp_app (le_top : U ≤ ⊤)).symm

/-- The image in `B(X_a)` of a global section `a` of the structure sheaf is a unit, for any sheaf
of `𝒪_X`-algebras `B`: the section `a` restricts to a unit of `𝒪_X(X_a)`. -/
theorem isUnit_res_unitTop (B : AlgebraSheaf.{u} X) (a : Γ(X, ⊤)) :
    IsUnit ((B.res (X.basicOpen a)).hom (B.unitTop.hom a)) := by
  have h : (B.res (X.basicOpen a)).hom (B.unitTop.hom a) =
      (B.hom.hom.app (op (X.basicOpen a))).hom
        (X.presheaf.map (homOfLE (le_top : X.basicOpen a ≤ ⊤)).op a) :=
    congrArg (fun k : Γ(X, ⊤) ⟶ B.sections (X.basicOpen a) => k.hom a)
      (unitTop_comp_res B (X.basicOpen a))
  rw [h]
  exact IsUnit.map (ConcreteCategory.hom (B.hom.hom.app (op (X.basicOpen a))))
    (isUnit_res_of_le_basicOpen X a le_rfl)

/-- A ring map on global sections compatible with the two structure maps carries the image of `a`
to a unit after restriction to the basic open of `a`. -/
theorem isUnit_comp_res_unitTop (A B : AlgebraSheaf.{u} X)
    {χ : A.sections ⊤ ⟶ B.sections ⊤} (hχ : A.unitTop ≫ χ = B.unitTop) (a : Γ(X, ⊤)) :
    IsUnit ((χ ≫ B.res (X.basicOpen a)).hom (A.unitTop.hom a)) := by
  have h : (χ ≫ B.res (X.basicOpen a)).hom (A.unitTop.hom a) =
      (B.res (X.basicOpen a)).hom (B.unitTop.hom a) := by
    rw [← hχ]; rfl
  rw [h]
  exact isUnit_res_unitTop B a

/-- The restriction map of an algebra sheaf to the basic open of `1` is an isomorphism, that open
being the whole space. -/
theorem isIso_res_basicOpen_one (C : AlgebraSheaf.{u} X) :
    IsIso (C.res (X.basicOpen (1 : Γ(X, ⊤)))) :=
  ⟨⟨C.right.obj.map (homOfLE (le_of_eq (X.basicOpen_one).symm)).op,
    map_homOfLE_comp_self C.right.obj _ _, map_homOfLE_comp_self C.right.obj _ _⟩⟩

/-- The component on global sections of a morphism of algebra sheaves is compatible with the two
structure maps. -/
theorem unitTop_comp_right_app_top {A B : AlgebraSheaf.{u} X} (φ : A ⟶ B) :
    A.unitTop ≫ φ.right.hom.app (op ⊤) = B.unitTop :=
  congrArg (fun α : X.sheaf ⟶ B.right ↦ α.hom.app (op ⊤)) (Under.w φ)

/-! ### The components over the basic opens -/

section

variable (A B : AlgebraSheaf.{u} X) [A.IsQuasicoherent] [IsAffine X]
  {χ : A.sections ⊤ ⟶ B.sections ⊤} (hχ : A.unitTop ≫ χ = B.unitTop)

/-- The component over the basic open of `a` of the morphism of algebra sheaves `A ⟶ B`
determined by a ring map `χ` on global sections. -/
noncomputable def algebraBasisComp (a : Γ(X, ⊤)) :
    A.sections (X.basicOpen a) ⟶ B.sections (X.basicOpen a) :=
  A.sectionsLift a (χ ≫ B.res (X.basicOpen a)) (isUnit_comp_res_unitTop A B hχ a)

/-- The component over the basic open of `a`, precomposed with restriction from global sections,
is `χ` followed by restriction. -/
@[simp]
theorem res_comp_algebraBasisComp (a : Γ(X, ⊤)) :
    A.res (X.basicOpen a) ≫ algebraBasisComp A B hχ a = χ ≫ B.res (X.basicOpen a) :=
  A.res_comp_sectionsLift a _ (isUnit_comp_res_unitTop A B hχ a)

/-- The components over the basic opens are compatible with restriction, in the form of an
inclusion of basic opens. -/
theorem algebraBasisComp_naturality' {a b : Γ(X, ⊤)} (h : X.basicOpen b ≤ X.basicOpen a) :
    A.right.obj.map (homOfLE h).op ≫ algebraBasisComp A B hχ b =
      algebraBasisComp A B hχ a ≫ B.right.obj.map (homOfLE h).op := by
  refine A.sections_basicOpen_hom_ext a ?_
  simp only [← Category.assoc]
  rw [map_homOfLE_comp, res_comp_algebraBasisComp A B hχ b, res_comp_algebraBasisComp A B hχ a,
    Category.assoc, map_homOfLE_comp]

/-- The components over the basic opens are compatible with restriction. -/
theorem algebraBasisComp_naturality {a b : Γ(X, ⊤)} (u : X.basicOpen b ⟶ X.basicOpen a) :
    A.right.obj.map u.op ≫ algebraBasisComp A B hχ b =
      algebraBasisComp A B hχ a ≫ B.right.obj.map u.op :=
  algebraBasisComp_naturality' A B hχ (leOfHom u)

/-! ### Gluing the components -/

/-- The morphism of presheaves of commutative rings `A ⟶ B` determined by a ring map `χ` on
global sections compatible with the two structure maps. -/
noncomputable def algebraHomOfRingHom : A.right.obj ⟶ B.right.obj :=
  TopCat.Sheaf.restrictHomEquivHom A.right.obj B.right (isBasis_basicOpen X)
    { app := fun a ↦ algebraBasisComp A B hχ a.unop
      naturality := fun _ _ φ ↦ algebraBasisComp_naturality A B hχ φ.unop.hom }

/-- The glued morphism has component `algebraBasisComp` over the basic open of `a`. -/
theorem algebraHomOfRingHom_app_basicOpen (a : Γ(X, ⊤)) :
    (algebraHomOfRingHom A B hχ).app (op (X.basicOpen a)) = algebraBasisComp A B hχ a :=
  TopCat.Sheaf.extend_hom_app _ _ _ _ a

/-- The glued morphism has the ring map `χ` as its component on global sections. -/
@[simp]
theorem algebraHomOfRingHom_app_top : (algebraHomOfRingHom A B hχ).app (op ⊤) = χ := by
  have := isIso_res_basicOpen_one B
  have hnat : A.res (X.basicOpen (1 : Γ(X, ⊤))) ≫
      (algebraHomOfRingHom A B hχ).app (op (X.basicOpen (1 : Γ(X, ⊤)))) =
        (algebraHomOfRingHom A B hχ).app (op ⊤) ≫ B.res (X.basicOpen (1 : Γ(X, ⊤))) :=
    (algebraHomOfRingHom A B hχ).naturality
      (homOfLE (le_top : X.basicOpen (1 : Γ(X, ⊤)) ≤ ⊤)).op
  have hnat2 : χ ≫ B.res (X.basicOpen (1 : Γ(X, ⊤))) =
      (algebraHomOfRingHom A B hχ).app (op ⊤) ≫ B.res (X.basicOpen (1 : Γ(X, ⊤))) :=
    Eq.trans (Eq.trans (res_comp_algebraBasisComp A B hχ 1).symm
      (congrArg (fun k ↦ A.res (X.basicOpen (1 : Γ(X, ⊤))) ≫ k)
        (algebraHomOfRingHom_app_basicOpen A B hχ 1).symm)) hnat
  exact ((cancel_mono _).mp hnat2).symm

/-- The glued morphism is a morphism of algebra sheaves: it is compatible with the two structure
maps. -/
theorem hom_comp_algebraHomOfRingHom : A.hom.hom ≫ algebraHomOfRingHom A B hχ = B.hom.hom := by
  refine TopCat.Sheaf.hom_ext X.presheaf B.right (isBasis_basicOpen X) fun a ↦ ?_
  refine presheaf_basicOpen_hom_ext a ?_
  rw [NatTrans.comp_app, algebraHomOfRingHom_app_basicOpen]
  erw [← Category.assoc, ← unitTop_comp_res A, Category.assoc, res_comp_algebraBasisComp,
    ← Category.assoc, hχ, unitTop_comp_res]

end

/-! ### The bijection -/

section

variable (A B : AlgebraSheaf.{u} X) [A.IsQuasicoherent] [IsAffine X]

/-- A morphism of presheaves of commutative rings out of a quasi-coherent algebra sheaf over an
affine base, into an arbitrary sheaf, is determined by its component on global sections. -/
theorem hom_ext_app_top {G : TopCat.Sheaf CommRingCat.{u} X} {ψ₁ ψ₂ : A.right.obj ⟶ G.obj}
    (h : ψ₁.app (op ⊤) = ψ₂.app (op ⊤)) : ψ₁ = ψ₂ := by
  refine TopCat.Sheaf.hom_ext A.right.obj G (isBasis_basicOpen X) fun a ↦ ?_
  refine A.sections_basicOpen_hom_ext a ?_
  refine Eq.trans (ψ₁.naturality (homOfLE (le_top : X.basicOpen a ≤ ⊤)).op) (Eq.trans ?_
    (ψ₂.naturality (homOfLE (le_top : X.basicOpen a ≤ ⊤)).op).symm)
  exact congrArg (fun k ↦ k ≫ G.obj.map (homOfLE (le_top : X.basicOpen a ≤ ⊤)).op) h

/-- The morphism of algebra sheaves `A ⟶ B` determined by a ring map on global sections which is
compatible with the two structure maps. -/
noncomputable def algebraHom {χ : A.sections ⊤ ⟶ B.sections ⊤}
    (hχ : A.unitTop ≫ χ = B.unitTop) : A ⟶ B :=
  Under.homMk (⟨algebraHomOfRingHom A B hχ⟩ : A.right ⟶ B.right)
    (Sheaf.hom_ext (hom_comp_algebraHomOfRingHom A B hχ))

/-- The morphism of algebra sheaves built from `χ` has `χ` as its component on global sections. -/
@[simp]
theorem algebraHom_right_app_top {χ : A.sections ⊤ ⟶ B.sections ⊤}
    (hχ : A.unitTop ≫ χ = B.unitTop) :
    (algebraHom A B hχ).right.hom.app (op ⊤) = χ :=
  algebraHomOfRingHom_app_top A B hχ

/-- **The universal property of the relative spectrum over an affine base.**  For `X` affine and
`A` a quasi-coherent sheaf of commutative `𝒪_X`-algebras, a morphism of algebra sheaves from `A`
to an arbitrary sheaf of commutative `𝒪_X`-algebras `B` is the same thing as a ring map
`A(X) ⟶ B(X)` compatible with the two structure maps on global sections. -/
noncomputable def homEquivUnitTopHom :
    (A ⟶ B) ≃ { χ : A.sections ⊤ ⟶ B.sections ⊤ // A.unitTop ≫ χ = B.unitTop } where
  toFun φ := ⟨φ.right.hom.app (op ⊤), unitTop_comp_right_app_top φ⟩
  invFun χ := algebraHom A B χ.2
  left_inv φ :=
    Under.UnderMorphism.ext (Sheaf.hom_ext (hom_ext_app_top A
      (algebraHom_right_app_top A B (unitTop_comp_right_app_top φ))))
  right_inv χ := Subtype.ext (algebraHom_right_app_top A B χ.2)

end

end AlgebraSheaf

end Stacks.RelativeSpec

end
