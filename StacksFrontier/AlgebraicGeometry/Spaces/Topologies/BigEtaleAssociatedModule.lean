module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleSite
public import StacksFrontier.CategoryTheory.Functor.ConjugateHom
public import StacksCore.Tactic.StacksAttribute

/-!
# The associated presheaf `𝓕ᵃ` of a module on an algebraic space

Let `S` be a scheme, `X` an algebraic space over `S` and `𝓕` an `𝒪_X`-module on the small étale
site of `X`.  Stacks 0DGN introduces the rule

  `𝓕ᵃ : (Spaces/X)_étale ⥤ Ab`,  `(f : Y ⟶ X) ↦ Γ(Y, f^*𝓕)`,

and then makes seven assertions about it.  This file constructs the rule itself — the presheaf
of abelian groups on the category `Over X` underlying the big étale site of `X` of Stacks 0DBX
— and proves that its value at `(f : Y ⟶ X)` is the group of global sections of the inverse
image `f^*𝓕` of Stacks 03LU.  None of the seven assertions is claimed here; see the final
section of this comment for what each of them still needs.

## Main definitions

* `AlgebraicGeometry.Space.associatedSections`: the value of `𝓕ᵃ` at an object `(f : Y ⟶ X)` of
  `Over X`, as an abelian group.
* `AlgebraicGeometry.Space.associatedSectionsMap`: its restriction maps.
* `AlgebraicGeometry.Space.associatedPresheaf`: **the rule `𝓕ᵃ`**, as a presheaf of abelian
  groups on `Over X`.
* `AlgebraicGeometry.Space.associatedPresheafFunctor`: the rule `𝓕 ↦ 𝓕ᵃ` as a functor from
  `𝒪_X`-modules to presheaves of abelian groups on `Over X`.
* `AlgebraicGeometry.BigEtaleSpaceSite.associatedPresheaf`: the same presheaf, read on the
  category underlying the big étale site of `X`.

## Main results

* `AlgebraicGeometry.Space.associatedSectionsEquiv`: **the value of `𝓕ᵃ` at `(f : Y ⟶ X)` is
  `Γ(Y, f^*𝓕)`**, the global sections of the inverse image of Stacks 03LU.

## Implementation notes

The sections of a module `M` on the small étale site of an algebraic space are the morphisms
`𝒪 ⟶ M` out of the structure sheaf (`CategoryTheory.SheafOfModules.unitHomEquiv`), and that is
how `Γ` is taken here: the small étale site of an algebraic space has no final object, so there
is no evaluation at one to use instead, and the global-sections functor of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulesGlobalSections.lean` is built from limits over the
site for exactly that reason.

`𝒪_X` read as a module over itself is `CategoryTheory.SheafOfModules.unit` of the structure
sheaf of rings of the small étale ringed site; it is written inline rather than abbreviated,
because `AlgebraicGeometry.Space.structureModule` of
`StacksFrontier/AlgebraicGeometry/Quot/PicardStackSection.lean` already names it and this file has
no reason to depend on that one.

The value of the presheaf is taken to be `Hom(f^*𝒪_X, f^*𝓕)` rather than `Hom(𝒪_Y, f^*𝓕)`.  The
two are identified by `AlgebraicGeometry.Space.modulePullbackUnitIso`, which is proved with no
hypothesis, and `AlgebraicGeometry.Space.associatedSectionsEquiv` is that identification
composed with `CategoryTheory.SheafOfModules.unitHomEquiv`; so the presheaf's value *is*
`Γ(Y, f^*𝓕)`, as a theorem and not by fiat.  The reason for the choice is the restriction maps.
Written in the first shape, a restriction map is the conjugate, in the sense of
`CategoryTheory.Functor.conjHom`, of the comparison `h^* ∘ f^* ≅ (h ≫ f)^*` of Stacks 03LU, and
then the two functor laws are precisely the unit law and the associativity coherence of that
comparison: `AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackTriangle_id` and
`AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackTriangle_comp'`, both of which
the library has.  Written in the second shape they would instead be a coherence of
`AlgebraicGeometry.Space.modulePullbackUnitIso` against that comparison, which the library does
not have.  The same choice, for the same reason, is made by
`AlgebraicGeometry.Space.moduleHomOver` of Stacks 08JT, whose value at `(f : Y ⟶ X)` is
`Hom(f^*𝓖, f^*𝓗)`; the present construction is its abelian-group-valued analogue at `𝓖 = 𝒪_X`,
and differs from it in being a presheaf of abelian groups rather than of types, which is what
the source asks for and what any sheaf condition for `𝓕ᵃ` will be stated against.

The pseudofunctoriality datum of the comparison is supplied by
`AlgebraicGeometry.Space.modulePushforwardCoherence`, which carries no hypothesis, so nothing
here is conditional.

The target universe is `AddCommGrpCat.{u + 1}`: the objects of the small étale site of an
algebraic space over a `Scheme.{u}` lie in `Type (u + 1)` while its structure sheaf and its
modules lie at `u`, so the Hom types of those modules lie in `Type (u + 1)`.

## What this file does not claim

Clause (1), the sheaf condition for `𝓕ᵃ` for fpqc — a fortiori fppf and étale — coverings, is
not proved.  What the library has at the level of algebraic spaces is the faithfulness half of
Stacks 04W8,
`AlgebraicGeometry.Space.QuasiCoherentDescent.faithful_canonicalDescentFunctor_of_isFpqcCovering`,
which has the covering as its only input; the gluing half, which is what a sheaf condition
needs, is absent.

Clause (2), `𝓕ᵃ = π_X^*𝓕`, needs the comparison of
`AlgebraicGeometry.Space.bigToSmallEtaleMorphism` of Stacks 0DF3 on *modules* rather than on
sheaves of sets, together with the comparison of Stacks 03G1 between the spaces-étale site
where `π_X` lands and the small étale site of charts where `𝒪_X`-modules are defined.  The
sheaf-of-sets template is `AlgebraicGeometry.Space.bigToSmall_inverseImageSectionsIso` of
Stacks 0DG7.

Clauses (3), (5), (6) and (7) all speak of the big fppf site of `X` as a ringed site.  There is
no structure sheaf and no category of modules on the big fppf site of an algebraic space in the
library — big étale has both, and the fppf analogue exists only for schemes, as Stacks 03DU —
so those clauses cannot yet be stated.

Clause (4) additionally needs the quasi-coherent modules on the big étale ringed site of `X`
together with essential surjectivity of `𝓕 ↦ 𝓕ᵃ` onto them; the scheme analogue is
`AlgebraicGeometry.smallEtaleBigEtaleQuasicoherentEquivalence` of Stacks 0DEW.

## References

* [Stacks Project, Tag 0DGN](https://stacks.math.columbia.edu/tag/0DGN)
* [Stacks Project, Tag 0DBX](https://stacks.math.columbia.edu/tag/0DBX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0DEW](https://stacks.math.columbia.edu/tag/0DEW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor Opposite

universe v w₀ w₁ w₂ w₃ u

namespace CategoryTheory.Functor

/-!
### Conjugation as a map of abelian groups

The restriction maps of `𝓕ᵃ` are conjugations by a comparison of functors in the sense of
`CategoryTheory.Functor.conjHom`, and they have to be *additive* maps between *bundled* abelian
groups.  Both the additivity and the bundling are settled here, in the abstract, for a reason
that is purely practical: identifying the group structure that `AddCommGrpCat.of` puts on a Hom
type with the one `CategoryTheory.Preadditive` puts on it is cheap for the kernel when the
categories are variables and extremely expensive when they are the module categories of
algebraic spaces.  Stating every step abstractly means the concrete construction only ever
*applies* these results.
-/

section ConjHomAdditive

variable {C : Type w₀} {D₀ : Type w₁} {D₁ : Type w₂} {D₂ : Type w₃}
  [Category.{v} C] [Category.{v} D₀] [Category.{v} D₁] [Category.{v} D₂]

section
variable {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂}

/-- **Conjugation is compatible with post-composition.**  The conjugate of `α` followed by the
image of `ψ` is the conjugate of the composite of `α` with the image of `ψ`.  This is the
naturality of the comparison `e` in the second variable, and it is what makes a conjugation
construction natural in the object it is applied to. -/
theorem conjHom_comp_right (e : P₂ ≅ P₁ ⋙ L) {M N N' : C}
    (α : P₁.obj M ⟶ P₁.obj N) (ψ : N ⟶ N') :
    conjHom e (α ≫ P₁.map ψ) = conjHom e α ≫ P₂.map ψ := by
  have h : L.map (P₁.map ψ) ≫ e.inv.app N' = e.inv.app N ≫ P₂.map ψ := e.inv.naturality ψ
  simp only [conjHom, Functor.map_comp, Category.assoc, h]

end

variable [Preadditive D₀] [Preadditive D₁] [Preadditive D₂]

section
variable {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} [L.Additive]

/-- Conjugation by a comparison carries the zero morphism to the zero morphism. -/
theorem conjHom_zero (e : P₂ ≅ P₁ ⋙ L) (M N : C) :
    conjHom e (0 : P₁.obj M ⟶ P₁.obj N) = 0 := by
  simp [conjHom]

/-- Conjugation by a comparison is additive, the further functor being additive. -/
theorem conjHom_add (e : P₂ ≅ P₁ ⋙ L) {M N : C} (α β : P₁.obj M ⟶ P₁.obj N) :
    conjHom e (α + β) = conjHom e α + conjHom e β := by
  simp [conjHom, Preadditive.comp_add, Preadditive.add_comp]

/-- Conjugation by a comparison, as an additive map of Hom groups. -/
def conjAddHom (e : P₂ ≅ P₁ ⋙ L) (M N : C) :
    (P₁.obj M ⟶ P₁.obj N) →+ (P₂.obj M ⟶ P₂.obj N) where
  toFun := conjHom e
  map_zero' := conjHom_zero e M N
  map_add' := conjHom_add e

/-- Conjugation by a comparison, as a morphism of bundled abelian groups. -/
def conjGrpHom (e : P₂ ≅ P₁ ⋙ L) (M N : C) :
    AddCommGrpCat.of (P₁.obj M ⟶ P₁.obj N) ⟶ AddCommGrpCat.of (P₂.obj M ⟶ P₂.obj N) :=
  AddCommGrpCat.ofHom (conjAddHom e M N)

end

/-- Post-composition with the image of a morphism, as a morphism of bundled abelian groups. -/
def rightCompGrpHom (P : C ⥤ D₁) (M : C) {N N' : C} (ψ : N ⟶ N') :
    AddCommGrpCat.of (P.obj M ⟶ P.obj N) ⟶ AddCommGrpCat.of (P.obj M ⟶ P.obj N') :=
  AddCommGrpCat.ofHom (Preadditive.rightComp _ (P.map ψ))

/-- Post-composition with the image of an identity is the identity. -/
theorem rightCompGrpHom_id (P : C ⥤ D₁) (M N : C) :
    rightCompGrpHom P M (𝟙 N) = 𝟙 (AddCommGrpCat.of (P.obj M ⟶ P.obj N)) :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext fun α => by
    simp [rightCompGrpHom, Preadditive.rightComp])

/-- Post-composition with the image of a composite is the composite of the post-compositions. -/
theorem rightCompGrpHom_comp (P : C ⥤ D₁) (M : C) {N N' N'' : C}
    (ψ : N ⟶ N') (χ : N' ⟶ N'') :
    rightCompGrpHom P M (ψ ≫ χ) = rightCompGrpHom P M ψ ≫ rightCompGrpHom P M χ :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext fun α => by
    simp [rightCompGrpHom, Preadditive.rightComp])

/-- **The unit law for conjugation of bundled Hom groups.** -/
theorem conjGrpHom_id {P : C ⥤ D₁} {L : D₁ ⥤ D₁} [L.Additive] (γ : 𝟭 D₁ ≅ L)
    (e : P ≅ P ⋙ L) (hfac : e = (rightUnitor P).symm ≪≫ isoWhiskerLeft P γ) (M N : C) :
    conjGrpHom e M N = 𝟙 (AddCommGrpCat.of (P.obj M ⟶ P.obj N)) :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext fun α => conjHom_id γ e hfac α)

/-- **The composition law for conjugation of bundled Hom groups.** -/
theorem conjGrpHom_comp {P₀ : C ⥤ D₀} {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂}
    {L₁ : D₀ ⥤ D₁} {L₂ : D₁ ⥤ D₂} {L : D₀ ⥤ D₂} [L₁.Additive] [L₂.Additive] [L.Additive]
    (c₁ : P₁ ≅ P₀ ⋙ L₁) (c₂ : P₂ ≅ P₁ ⋙ L₂) (c : P₂ ≅ P₀ ⋙ L) (τ : L ≅ L₁ ⋙ L₂)
    (hfac : c = (c₂ ≪≫ isoWhiskerRight c₁ L₂ ≪≫ associator P₀ L₁ L₂) ≪≫
      (isoWhiskerLeft P₀ τ).symm)
    (M N : C) :
    conjGrpHom c M N = conjGrpHom c₁ M N ≫ conjGrpHom c₂ M N :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext fun α => conjHom_comp c₁ c₂ c τ hfac α)

/-- **Conjugation commutes with post-composition**, for bundled Hom groups.  This is the
naturality square of `CategoryTheory.Functor.conjGrpHom` in its second object. -/
theorem conjGrpHom_rightCompGrpHom {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} [L.Additive]
    (e : P₂ ≅ P₁ ⋙ L) (M : C) {N N' : C} (ψ : N ⟶ N') :
    conjGrpHom e M N ≫ rightCompGrpHom P₂ M ψ =
      rightCompGrpHom P₁ M ψ ≫ conjGrpHom e M N' :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext fun α => (conjHom_comp_right e α ψ).symm)

end ConjHomAdditive

end CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The value of `𝓕ᵃ` at an object `(f : Y ⟶ X)` of `Over X`**: the morphisms
`f^*𝒪_X ⟶ f^*𝓕` of `𝒪_Y`-modules, which
`AlgebraicGeometry.Space.associatedSectionsEquiv` identifies with `Γ(Y, f^*𝓕)`. -/
noncomputable def associatedSections {X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) (Y : Over X) : AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.of
    ((modulePullback B S hS Y.hom).obj (SheafOfModules.unit _ :
          Modules.{u, u} B S hS X.1 X.2) ⟶
      (modulePullback B S hS Y.hom).obj F)

/-- **The restriction maps of `𝓕ᵃ`.**  A morphism `m : Z ⟶ Y` of `Over X` has underlying
morphism `h = m.left` with `h ≫ f = g`, where `f` and `g` are the structure morphisms of `Y`
and `Z`; the restriction map is the conjugate, in the sense of
`CategoryTheory.Functor.conjGrpHom`, of the comparison `g^* ≅ f^* ⋙ h^*` of Stacks 03LU.

It is additive because the inverse image of modules is an additive functor,
`AlgebraicGeometry.Space.modulePullback_additive`. -/
noncomputable def associatedSectionsMap {X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) {Y Z : Over X} (m : Z ⟶ Y) :
    associatedSections F Y ⟶ associatedSections F Z :=
  conjGrpHom (modulePullbackTriangle B S hS (Over.w m))
    (SheafOfModules.unit _ : Modules.{u, u} B S hS X.1 X.2) F

/-- **Stacks 0DGN, the rule `𝓕ᵃ`.**  For an `𝒪_X`-module `𝓕` on the small étale site of an
algebraic space `X`, the presheaf of abelian groups on the category `Over X` underlying the big
étale site of `X` whose value at `(f : Y ⟶ X)` is `Γ(Y, f^*𝓕)`.

The two functor laws are the unit law and the associativity coherence of the comparison
`g^* ≅ f^* ⋙ h^*` of Stacks 03LU, taken from
`AlgebraicGeometry.Space.modulePushforwardCoherence`, which carries no hypothesis. -/
noncomputable def associatedPresheaf {X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj Y := associatedSections F Y.unop
  map m := associatedSectionsMap F m.unop
  map_id Y :=
    conjGrpHom_id ((modulePushforwardCoherence B S hS).modulePullbackIdIso Y.unop.left).symm _
      ((modulePushforwardCoherence B S hS).modulePullbackTriangle_id (Over.w (𝟙 Y.unop))) _ _
  map_comp m n :=
    conjGrpHom_comp (modulePullbackTriangle B S hS (Over.w m.unop))
      (modulePullbackTriangle B S hS (Over.w n.unop))
      (modulePullbackTriangle B S hS (Over.w (n.unop ≫ m.unop)))
      (modulePullbackTriangle B S hS rfl)
      ((modulePushforwardCoherence B S hS).modulePullbackTriangle_comp' rfl
        (Over.w m.unop) (Over.w n.unop) (Over.w (n.unop ≫ m.unop))) _ _

/-- The value of `associatedPresheaf F` at `Y` is `associatedSections F Y`. -/
@[simp]
theorem associatedPresheaf_obj {X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) (Y : Over X) :
    (associatedPresheaf F).obj (op Y) = associatedSections F Y := rfl

/-- The restriction map of `associatedPresheaf F` along `m : Z ⟶ Y` is
`associatedSectionsMap F m`. -/
@[simp]
theorem associatedPresheaf_map {X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) {Y Z : Over X} (m : Z ⟶ Y) :
    (associatedPresheaf F).map m.op = associatedSectionsMap F m := rfl

/-- **The value of `𝓕ᵃ` at `(f : Y ⟶ X)` is `Γ(Y, f^*𝓕)`**: the morphisms `f^*𝒪_X ⟶ f^*𝓕` of
`𝒪_Y`-modules correspond to the global sections of `f^*𝓕`.

The inverse image of the structure sheaf is the structure sheaf
(`AlgebraicGeometry.Space.modulePullbackUnitIso`), and a morphism out of the structure sheaf is
a global section (`CategoryTheory.SheafOfModules.unitHomEquiv`). -/
@[stacks 0DGN "the value of the rule 𝓕 ↦ 𝓕ᵃ at an object (f : Y ⟶ X) of the big étale site of
an algebraic space X is Γ(Y, f^*𝓕), the global sections of the inverse image of 𝓕 along f"]
noncomputable def associatedSectionsEquiv {X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) (Y : Over X) :
    ((modulePullback B S hS Y.hom).obj (SheafOfModules.unit _ :
          Modules.{u, u} B S hS X.1 X.2) ⟶
        (modulePullback B S hS Y.hom).obj F) ≃
      ((modulePullback B S hS Y.hom).obj F).sections :=
  ((modulePullbackUnitIso B S hS Y.hom).homCongr (Iso.refl _)).trans
    (SheafOfModules.unitHomEquiv _)

/-- The morphism of presheaves `𝓕ᵃ ⟶ 𝓖ᵃ` attached to a morphism `𝓕 ⟶ 𝓖` of `𝒪_X`-modules:
post-composition with the inverse image of the morphism.  Its naturality is the naturality of
the comparison `g^* ≅ f^* ⋙ h^*` of Stacks 03LU in the module. -/
noncomputable def associatedPresheafMap {X : AlgebraicSpaces B S hS}
    {F G : Modules.{u, u} B S hS X.1 X.2} (ψ : F ⟶ G) :
    associatedPresheaf F ⟶ associatedPresheaf G where
  app Y := rightCompGrpHom (modulePullback B S hS Y.unop.hom)
    (SheafOfModules.unit _ : Modules.{u, u} B S hS X.1 X.2) ψ
  naturality _ _ m :=
    conjGrpHom_rightCompGrpHom (modulePullbackTriangle B S hS (Over.w m.unop))
      (SheafOfModules.unit _ : Modules.{u, u} B S hS X.1 X.2) ψ

/-- **The rule `𝓕 ↦ 𝓕ᵃ` as a functor** from the `𝒪_X`-modules on the small étale site of an
algebraic space `X` to the presheaves of abelian groups on the category `Over X` underlying the
big étale site of `X`. -/
noncomputable def associatedPresheafFunctor (X : AlgebraicSpaces B S hS) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ ((Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) where
  obj F := associatedPresheaf F
  map ψ := associatedPresheafMap ψ
  map_id F :=
    NatTrans.ext (funext fun Y =>
      rightCompGrpHom_id (modulePullback B S hS Y.unop.hom)
        (SheafOfModules.unit _ : Modules.{u, u} B S hS X.1 X.2) F)
  map_comp ψ χ :=
    NatTrans.ext (funext fun Y =>
      rightCompGrpHom_comp (modulePullback B S hS Y.unop.hom)
        (SheafOfModules.unit _ : Modules.{u, u} B S hS X.1 X.2) ψ χ)

end Space

/-- **Stacks 0DGN, the rule `𝓕ᵃ` on the big étale site of an algebraic space.**  For an
`𝒪_X`-module `𝓕` on the small étale site of an algebraic space `X` of a big étale space site of
Stacks 0DBX, the presheaf of abelian groups on the category underlying the big étale site of
`X` whose value at `(f : Y ⟶ X)` is `Γ(Y, f^*𝓕)`.

This is `AlgebraicGeometry.Space.associatedPresheaf` read on that category; the identification
of its value with `Γ(Y, f^*𝓕)` is `AlgebraicGeometry.Space.associatedSectionsEquiv`. -/
@[stacks 0DGN "the construction of the rule 𝓕 ↦ 𝓕ᵃ as a presheaf of abelian groups on the big
étale site of an algebraic space; none of the seven assertions the source makes about it"]
noncomputable def BigEtaleSpaceSite.associatedPresheaf {S : Scheme.{u}}
    (T : BigEtaleSpaceSite S) (X : T.Spaces)
    (F : Space.Modules.{u, u} T.fppfSite S T.fppf_mem X.1 X.2) :
    (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  Space.associatedPresheaf F

end AlgebraicGeometry

end
