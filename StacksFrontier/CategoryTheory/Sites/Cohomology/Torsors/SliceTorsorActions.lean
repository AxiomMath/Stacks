module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.ModObj
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.SmallSections
public import StacksFrontier.CategoryTheory.Sites.Localization.LowerShriekCoproductSheaf
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A torsor on a localized site, read as an action over the representable presheaf

Let `(C, J)` be a site, let `U` be an object of `C`, let `𝒢` be a sheaf of groups on the
localized site `C/U` and let `F` be a pseudo-torsor under `𝒢` in the sense of Stacks 03AH.
This file turns that section-wise datum into a genuine *action of a group object*: a group
object and an object of the slice `PSh(C)/h_U`, together with the action morphism
`γ : 𝒢† ⊗ F† ⟶ F†` of that slice, whose shear map `(g, x) ↦ (g · x, x)` is an isomorphism.

The passage happens in two steps. First, a sheaf of groups and a pseudo-torsor under it are
group and module objects of the presheaf category `PSh(C/U)` itself, whose cartesian monoidal
structure is computed section-wise, so the structure morphisms are the section-wise group law
and the section-wise action. Second, the presheaf-level form of Stacks 00Y1
(`CategoryTheory.OverShriek.presheafEquivalence`) is an equivalence `PSh(C/U) ≌ PSh(C)/h_U`,
hence preserves finite products, hence is monoidal; so it carries both objects over, and
`CategoryTheory.Functor.LaxMonoidal.modObj` carries the action with them.

## Main definitions

* `SheafOfGroups.grpObj`: a sheaf of groups is a group object of the presheaf
  category.
* `PseudoTorsor.modObj`: a pseudo-torsor is a module object over it.
* `PseudoTorsor.overYonedaGrp` and `PseudoTorsor.overYonedaObj`:
  the group object and the acted-on object of `PSh(C)/h_U` carried over, the second with its
  action `PseudoTorsor.overYonedaModObj`.

## Main results

* `PseudoTorsor.isIso_leftSMul`: the shear map of the section-wise action is an
  isomorphism of presheaves on `C/U`, that is, the module object is a pseudo-torsor.
* `PseudoTorsor.isIso_leftSMul_overYoneda`: the same for the carried action,
  which is the pseudo-torsor condition for an action of group objects over `h_U`.
* `PseudoTorsor.isSheaf_overYonedaObj`: the acted-on object is a sheaf on `C`,
  provided `h_U` is.
* `PseudoTorsor.isLocallySurjective_overYonedaObj_hom`: a torsor, that is a
  locally nonempty pseudo-torsor, has an acted-on object whose structure morphism to `h_U` is
  locally surjective. Together with the previous two this is the whole torsor condition of
  Stacks 04UL for the carried action.
* `PseudoTorsor.isIso_leftSMul_overYoneda_shrink` and
  `PseudoTorsor.isLocallySurjective_overYonedaObj_hom_shrink`: the same two statements for a
  pseudo-torsor whose sections live in an arbitrary universe, through
  `PseudoTorsor.shrink`.
* `PseudoTorsor.sliceIsoObj`: the sections of the carried object over an object
  `(V, a)` of `C/U` lying over `a` are the sections of `F` over `(V, a)`, so nothing is lost in
  the passage.

## Implementation notes

The universe of the sections of a pseudo-torsor is unconstrained, while the equivalence of
Stacks 00Y1 is about presheaves valued in the universe of the homs of the site. The two are
reconciled by `PseudoTorsor.shrink`, which replaces the sections of a
pseudo-torsor by a model of them in the universe of the sections of the sheaf of groups; the
constructions below are therefore stated for a pseudo-torsor whose sections already live in
that universe, and a client holding one at a larger universe shrinks it first.

A sheaf of groups carries only the multiplicativity of its restriction maps. That they
preserve the unit is already `SheafOfGroups.map_one`; that they preserve inverses is derived
here as `SheafOfGroups.map_inv`.

## References

* [Stacks Project, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)
* [Stacks Project, Tag 00Y1](https://stacks.math.columbia.edu/tag/00Y1)
* [Stacks Project, Tag 04UL](https://stacks.math.columbia.edu/tag/04UL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

universe t v u

/-! ### Section-wise formulas in a presheaf category of types -/

namespace CategoryTheory

variable {D : Type u} [Category.{v} D]

/-- The two components of a morphism into a product of presheaves of types. -/
theorem presheafLift_app_apply {P Q R : Dᵒᵖ ⥤ Type v} (a : R ⟶ P) (b : R ⟶ Q) (V : Dᵒᵖ)
    (z : R.obj V) : (lift a b).app V z = (a.app V z, b.app V z) :=
  rfl

end CategoryTheory

/-! ### A sheaf of groups is a group object of the presheaf category -/

section GroupObject

variable {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}

/-- The restriction maps of a sheaf of groups preserve inverses. -/
theorem SheafOfGroups.map_inv (𝒢 : SheafOfGroups.{v} (C := D) K) {V W : Dᵒᵖ} (f : V ⟶ W)
    (g : 𝒢.presheaf.obj V) : 𝒢.presheaf.map f g⁻¹ = (𝒢.presheaf.map f g)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by
    rw [← 𝒢.map_mul, inv_mul_cancel, SheafOfGroups.map_one (G := 𝒢) f])

/-- The unit of a sheaf of groups, as a morphism of presheaves out of the terminal presheaf. -/
def SheafOfGroups.oneHom (𝒢 : SheafOfGroups.{v} (C := D) K) :
    𝟙_ (Dᵒᵖ ⥤ Type v) ⟶ 𝒢.presheaf where
  app V := ↾fun _ : (𝟙_ (Dᵒᵖ ⥤ Type v)).obj V => (1 : 𝒢.presheaf.obj V)
  naturality _ _ f := by ext _; exact (SheafOfGroups.map_one (G := 𝒢) f).symm

/-- The group law of a sheaf of groups, as a morphism of presheaves out of the product. -/
def SheafOfGroups.mulHom (𝒢 : SheafOfGroups.{v} (C := D) K) :
    𝒢.presheaf ⊗ 𝒢.presheaf ⟶ 𝒢.presheaf where
  app V := ↾fun p : 𝒢.presheaf.obj V × 𝒢.presheaf.obj V => p.1 * p.2
  naturality _ _ f := by ext p; exact (𝒢.map_mul f p.1 p.2).symm

/-- Inversion in a sheaf of groups, as an endomorphism of its underlying presheaf. -/
def SheafOfGroups.invHom (𝒢 : SheafOfGroups.{v} (C := D) K) : 𝒢.presheaf ⟶ 𝒢.presheaf where
  app V := ↾fun g : 𝒢.presheaf.obj V => g⁻¹
  naturality _ _ f := by ext g; exact (𝒢.map_inv f g).symm

/-- Each component of `SheafOfGroups.oneHom` is the constant map to the unit section. -/
@[simp]
theorem SheafOfGroups.oneHom_app_apply (𝒢 : SheafOfGroups.{v} (C := D) K) (V : Dᵒᵖ)
    (x : (𝟙_ (Dᵒᵖ ⥤ Type v)).obj V) : 𝒢.oneHom.app V x = 1 :=
  rfl

/-- Each component of `SheafOfGroups.mulHom` is the product of sections. -/
@[simp]
theorem SheafOfGroups.mulHom_app_apply (𝒢 : SheafOfGroups.{v} (C := D) K) (V : Dᵒᵖ)
    (p : 𝒢.presheaf.obj V × 𝒢.presheaf.obj V) : 𝒢.mulHom.app V p = p.1 * p.2 :=
  rfl

/-- Each component of `SheafOfGroups.invHom` is the inverse of a section. -/
@[simp]
theorem SheafOfGroups.invHom_app_apply (𝒢 : SheafOfGroups.{v} (C := D) K) (V : Dᵒᵖ)
    (g : 𝒢.presheaf.obj V) : 𝒢.invHom.app V g = g⁻¹ :=
  rfl

/-- **A sheaf of groups is a group object of the presheaf category.** The cartesian monoidal
structure of a presheaf category of types is computed section-wise, so the group law of the
sections is already the required morphism out of the product. -/
@[sga "3 I 2.1.1" "partial"]
instance SheafOfGroups.grpObj (𝒢 : SheafOfGroups.{v} (C := D) K) : GrpObj 𝒢.presheaf where
  one := 𝒢.oneHom
  mul := 𝒢.mulHom
  inv := 𝒢.invHom
  one_mul := by ext V x; exact one_mul _
  mul_one := by ext V x; exact mul_one _
  mul_assoc := by ext V x; exact mul_assoc _ _ _
  left_inv := by ext V x; exact inv_mul_cancel _
  right_inv := by ext V x; exact mul_inv_cancel _

/-! ### A pseudo-torsor is a module object over it -/

variable {𝒢 : SheafOfGroups.{v} (C := D) K}

/-- The action of a pseudo-torsor, as a morphism of presheaves out of the product. -/
def PseudoTorsor.smulHom (F : PseudoTorsor.{v} 𝒢) : 𝒢.presheaf ⊗ F.presheaf ⟶ F.presheaf where
  app V := ↾fun p : 𝒢.presheaf.obj V × F.presheaf.obj V => F.act V p.1 p.2
  naturality _ _ f := by ext p; exact (F.naturality f p.1 p.2).symm

/-- Each component of `PseudoTorsor.smulHom` is the section-wise action. -/
@[simp]
theorem PseudoTorsor.smulHom_app_apply (F : PseudoTorsor.{v} 𝒢) (V : Dᵒᵖ)
    (p : 𝒢.presheaf.obj V × F.presheaf.obj V) : F.smulHom.app V p = F.act V p.1 p.2 :=
  rfl

/-- **A pseudo-torsor is a module object over the group object of its sheaf of groups.** As for
the group law, the section-wise action is already the required morphism out of the product. -/
instance PseudoTorsor.modObj (F : PseudoTorsor.{v} 𝒢) : ModObj 𝒢.presheaf F.presheaf where
  smul := F.smulHom
  one_smul := by ext V x; exact F.one_act V x.2
  mul_smul := by ext V x; exact F.mul_act V x.1.1 x.1.2 x.2

/-- The action of a section of the sheaf of groups on a section of a pseudo-torsor, read in the
module-object notation, is the section-wise action. -/
theorem PseudoTorsor.smul_app_apply (F : PseudoTorsor.{v} 𝒢) {R : Dᵒᵖ ⥤ Type v}
    (g : R ⟶ 𝒢.presheaf) (x : R ⟶ F.presheaf) (V : Dᵒᵖ) (z : R.obj V) :
    (g • x).app V z = F.act V (g.app V z) (x.app V z) :=
  rfl

/-- The unique section of the sheaf of groups carrying one section of a pseudo-torsor over an
object to another: the action of the sections over an object with a section is simply
transitive. -/
noncomputable def PseudoTorsor.ratio (F : PseudoTorsor.{v} 𝒢) (V : Dᵒᵖ)
    (s t : F.presheaf.obj V) : 𝒢.presheaf.obj V :=
  (F.simplyTransitive V ⟨s⟩ s t).choose

/-- `PseudoTorsor.ratio` carries the first section to the second. -/
theorem PseudoTorsor.act_ratio (F : PseudoTorsor.{v} 𝒢) (V : Dᵒᵖ) (s t : F.presheaf.obj V) :
    F.act V (F.ratio V s t) s = t :=
  (F.simplyTransitive V ⟨s⟩ s t).choose_spec.1

/-- `PseudoTorsor.ratio` is the only section carrying the first section to the
second. -/
theorem PseudoTorsor.eq_ratio (F : PseudoTorsor.{v} 𝒢) (V : Dᵒᵖ) (s t : F.presheaf.obj V)
    (g : 𝒢.presheaf.obj V) (hg : F.act V g s = t) : g = F.ratio V s t :=
  (F.simplyTransitive V ⟨s⟩ s t).choose_spec.2 g hg

/-- The unique section of the sheaf of groups carrying one section of a pseudo-torsor to
another over an arbitrary presheaf of test objects: it is the section-wise ratio, and the
ratios are compatible with restriction because each of them is unique. -/
noncomputable def PseudoTorsor.shearInv (F : PseudoTorsor.{v} 𝒢) {R : Dᵒᵖ ⥤ Type v}
    (x y : R ⟶ F.presheaf) : R ⟶ 𝒢.presheaf where
  app V := ↾fun z : R.obj V => F.ratio V (x.app V z) (y.app V z)
  naturality V W f := by
    ext z
    have hx : x.app W (R.map f z) = F.presheaf.map f (x.app V z) :=
      ConcreteCategory.congr_hom (CC := fun T : Type v => T) (x.naturality f) z
    have hy : y.app W (R.map f z) = F.presheaf.map f (y.app V z) :=
      ConcreteCategory.congr_hom (CC := fun T : Type v => T) (y.naturality f) z
    refine (F.eq_ratio W (x.app W (R.map f z)) (y.app W (R.map f z))
      (𝒢.presheaf.map f (F.ratio V (x.app V z) (y.app V z))) ?_).symm
    rw [hx, hy, ← F.naturality f, F.act_ratio]

/-- The section `PseudoTorsor.shearInv x y` of the sheaf of groups carries `x` to `y`. -/
theorem PseudoTorsor.shearInv_smul (F : PseudoTorsor.{v} 𝒢) {R : Dᵒᵖ ⥤ Type v}
    (x y : R ⟶ F.presheaf) : F.shearInv x y • x = y := by
  ext V z
  exact F.act_ratio V (x.app V z) (y.app V z)

/-- **The shear map of a pseudo-torsor is an isomorphism of presheaves.** Simple transitivity
over the objects with a section gives, over an arbitrary presheaf of test objects, a unique
section of the sheaf of groups carrying one section of the pseudo-torsor to another; the test
presheaf itself supplies the section needed to invoke simple transitivity. -/
@[sga "3 III 0.1" "implication (i) ⇒ (ii)", sga "3 IV 5.1.0" "partial"]
theorem PseudoTorsor.isIso_leftSMul (F : PseudoTorsor.{v} 𝒢) :
    IsIso (ModObj.leftSMul 𝒢.presheaf F.presheaf) := by
  rw [ModObj.isIso_leftSMul_iff]
  intro R x y
  refine ⟨F.shearInv x y, F.shearInv_smul x y, fun g hg => ?_⟩
  ext V z
  exact F.eq_ratio V (x.app V z) (y.app V z) (g.app V z)
    (ConcreteCategory.congr_hom (CC := fun T : Type v => T)
      (congrArg (fun α : R ⟶ F.presheaf => α.app V) hg) z)

end GroupObject

/-! ### Carrying the action over to the slice over the representable presheaf -/

namespace PseudoTorsor

variable {C : Type u} [Category.{v} C] {U : C} (J : GrothendieckTopology C)

/-- The presheaf-level `j_{U!}` into the slice over `h_U` preserves finite products, being an
equivalence, hence is monoidal for the two cartesian monoidal structures. -/
@[instance_reducible]
noncomputable def overShriekMonoidal (U : C) :
    (OverShriek.presheafFunctorToOver (U := U)).Monoidal :=
  .ofChosenFiniteProducts _

attribute [local instance] overShriekMonoidal

variable {𝒢 : SheafOfGroups.{v} (C := Over U) (J.over U)}

/-- The group object of `PSh(C)/h_U` carried over from the sheaf of groups of a pseudo-torsor
on the localized site: the coproduct presheaf `V ↦ ∐_{a : V ⟶ U} 𝒢(V, a)` over `h_U`. -/
noncomputable def overYonedaGrp (_F : PseudoTorsor.{v} 𝒢) : Over (yoneda.obj U) :=
  OverShriek.presheafFunctorToOver.obj 𝒢.presheaf

/-- The acted-on object of `PSh(C)/h_U` carried over from a pseudo-torsor on the localized
site: the coproduct presheaf `V ↦ ∐_{a : V ⟶ U} F(V, a)` over `h_U`. -/
noncomputable def overYonedaObj (F : PseudoTorsor.{v} 𝒢) : Over (yoneda.obj U) :=
  OverShriek.presheafFunctorToOver.obj F.presheaf

/-- The underlying presheaf of `overYonedaGrp` is the coproduct presheaf of the sheaf of groups. -/
theorem overYonedaGrp_left (F : PseudoTorsor.{v} 𝒢) :
    (F.overYonedaGrp (J := J)).left = OverShriek.presheaf 𝒢.presheaf :=
  rfl

/-- The underlying presheaf of `overYonedaObj` is the coproduct presheaf of the pseudo-torsor. -/
theorem overYonedaObj_left (F : PseudoTorsor.{v} 𝒢) :
    (F.overYonedaObj (J := J)).left = OverShriek.presheaf F.presheaf :=
  rfl

/-- The structure morphism of `overYonedaObj` is the projection of the coproduct presheaf of the
pseudo-torsor to `h_U`. -/
theorem overYonedaObj_hom (F : PseudoTorsor.{v} 𝒢) :
    (F.overYonedaObj (J := J)).hom = OverShriek.presheafToYoneda F.presheaf :=
  rfl

/-- The carried group object is a group object: the equivalence of Stacks 00Y1 preserves finite
products, so it carries group objects to group objects. -/
noncomputable instance overYonedaGrpObj (F : PseudoTorsor.{v} 𝒢) :
    GrpObj (F.overYonedaGrp (J := J)) :=
  ((OverShriek.presheafFunctorToOver (U := U)).mapGrp.obj (.mk 𝒢.presheaf)).grp

/-- **The action morphism, manufactured.** The carried acted-on object is a module object over
the carried group object, the action being the image of the section-wise action read through
the product comparison of the equivalence of Stacks 00Y1. -/
noncomputable instance overYonedaModObj (F : PseudoTorsor.{v} 𝒢) :
    ModObj (F.overYonedaGrp (J := J)) (F.overYonedaObj (J := J)) :=
  Functor.LaxMonoidal.modObj (OverShriek.presheafFunctorToOver (U := U))
    (overYonedaGrpObj J F).toMonObj rfl rfl

/-- **The carried action is a pseudo-torsor.** Its shear map is the image of the shear map of
the section-wise action, read through the product comparison isomorphisms, and the latter is an
isomorphism by `PseudoTorsor.isIso_leftSMul`. -/
@[sga "3 III 0.1" "(i) ⇒ (ii)"]
theorem isIso_leftSMul_overYoneda (F : PseudoTorsor.{v} 𝒢) :
    IsIso (ModObj.leftSMul (F.overYonedaGrp (J := J)) (F.overYonedaObj (J := J))) := by
  have hshear := F.isIso_leftSMul
  have key : ModObj.leftSMul (F.overYonedaGrp (J := J)) (F.overYonedaObj (J := J)) =
      (prodComparisonIso (OverShriek.presheafFunctorToOver (U := U)) 𝒢.presheaf F.presheaf).inv ≫
        OverShriek.presheafFunctorToOver.map (ModObj.leftSMul 𝒢.presheaf F.presheaf) ≫
          (prodComparisonIso (OverShriek.presheafFunctorToOver (U := U)) F.presheaf
            F.presheaf).hom :=
    Functor.LaxMonoidal.mapModObj_leftSMul (OverShriek.presheafFunctorToOver (U := U))
      (X := F.presheaf) (overYonedaGrpObj J F).toMonObj rfl rfl
  have h1 : IsIso (OverShriek.presheafFunctorToOver.map
      (ModObj.leftSMul 𝒢.presheaf F.presheaf)) := inferInstance
  have h2 : IsIso (prodComparisonIso (OverShriek.presheafFunctorToOver (U := U)) 𝒢.presheaf
      F.presheaf).inv := inferInstance
  have h3 : IsIso (prodComparisonIso (OverShriek.presheafFunctorToOver (U := U)) F.presheaf
      F.presheaf).hom := inferInstance
  rw [key]
  exact IsIso.comp_isIso' h2 (IsIso.comp_isIso' h1 h3)

/-! ### The torsor conditions of the carried action -/

/-- The acted-on object carried over from a pseudo-torsor on the localized site is a sheaf on
`C`, provided the representable presheaf of `U` is one. -/
theorem isSheaf_overYonedaObj (F : PseudoTorsor.{v} 𝒢)
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    Presheaf.IsSheaf J (F.overYonedaObj (J := J)).left := by
  rw [isSheaf_iff_isSheaf_of_type]
  exact OverShriek.isSheaf_presheaf J F.presheaf ((isSheaf_iff_isSheaf_of_type _ _).1 hU)
    ((isSheaf_iff_isSheaf_of_type _ _).1 F.isSheaf)

/-- The group object carried over from a sheaf of groups on the localized site is a sheaf on
`C`, provided the representable presheaf of `U` is one. -/
theorem isSheaf_overYonedaGrp (F : PseudoTorsor.{v} 𝒢)
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    Presheaf.IsSheaf J (F.overYonedaGrp (J := J)).left := by
  rw [isSheaf_iff_isSheaf_of_type]
  exact OverShriek.isSheaf_presheaf J 𝒢.presheaf ((isSheaf_iff_isSheaf_of_type _ _).1 hU)
    ((isSheaf_iff_isSheaf_of_type _ _).1 𝒢.isSheaf)

/-- **Local nonemptiness becomes local surjectivity.** A torsor on the localized site has
sections over a covering sieve of every object `(V, a)` of `C/U`, and such a sieve is a
covering sieve of `V` all of whose members carry a section of the coproduct presheaf over the
restriction of `a`; that is exactly local surjectivity of the structure morphism to `h_U`. -/
theorem isLocallySurjective_overYonedaObj_hom (F : PseudoTorsor.{v} 𝒢) (hF : F.IsTorsor) :
    Presheaf.IsLocallySurjective J (F.overYonedaObj (J := J)).hom := by
  constructor
  intro V a
  obtain ⟨S, hS, hne⟩ := hF (Over.mk a)
  rw [GrothendieckTopology.mem_over_iff] at hS
  refine J.superset_covering (fun W k hk => ?_) hS
  rw [Sieve.overEquiv_iff] at hk
  exact ⟨⟨k ≫ a, (hne hk).some⟩, rfl⟩

/-! ### Sections in an arbitrary universe -/

/-- The shrinking of a pseudo-torsor is locally nonempty as soon as the pseudo-torsor is. -/
theorem isTorsor_shrink (F : PseudoTorsor.{t} 𝒢) (hF : F.IsTorsor) : F.shrink.IsTorsor :=
  F.shrink_isTorsor.2 hF

/-- **The action manufactured from a pseudo-torsor whose sections live in an arbitrary
universe.** The comparison of Stacks 00Y1 is about presheaves valued in the universe of the
homs of the site, so the sections are first replaced by a model of them in the universe of the
sections of the sheaf of groups; that is `PseudoTorsor.shrink`, and it changes neither the
action nor local nonemptiness. This is the form in which a pseudo-torsor produced by effective
descent, whose sections live one universe up, is consumed. -/
theorem isIso_leftSMul_overYoneda_shrink (F : PseudoTorsor.{t} 𝒢) :
    IsIso (ModObj.leftSMul (F.shrink.overYonedaGrp (J := J))
      (F.shrink.overYonedaObj (J := J))) :=
  F.shrink.isIso_leftSMul_overYoneda (J := J)

/-- The acted-on object manufactured after shrinking has a locally surjective structure
morphism as soon as the pseudo-torsor is locally nonempty. -/
theorem isLocallySurjective_overYonedaObj_hom_shrink (F : PseudoTorsor.{t} 𝒢)
    (hF : F.IsTorsor) :
    Presheaf.IsLocallySurjective J (F.shrink.overYonedaObj (J := J)).hom :=
  F.shrink.isLocallySurjective_overYonedaObj_hom (J := J) (isTorsor_shrink J F hF)

/-! ### Nothing is lost -/

/-- The sections of the carried group object over an object `(V, a)` of `C/U` lying over `a`
are the sections of the sheaf of groups over `(V, a)`. This is the unit of Stacks 00Y1 at the
presheaf level. -/
def sliceIsoGrp (F : PseudoTorsor.{v} 𝒢) :
    𝒢.presheaf ≅ OverShriek.fiber (𝟙 (yoneda.obj U)) (F.overYonedaGrp (J := J)).hom :=
  OverShriek.presheafUnitIsoApp 𝒢.presheaf

/-- The sections of the carried acted-on object over an object `(V, a)` of `C/U` lying over `a`
are the sections of the pseudo-torsor over `(V, a)`. -/
def sliceIsoObj (F : PseudoTorsor.{v} 𝒢) :
    F.presheaf ≅ OverShriek.fiber (𝟙 (yoneda.obj U)) (F.overYonedaObj (J := J)).hom :=
  OverShriek.presheafUnitIsoApp F.presheaf

end PseudoTorsor

end
