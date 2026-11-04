module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyOverAnObject

/-!
# Restricting the first cohomology class of a torsor to an object of the site

For an abelian sheaf `H` on a site `(C, J)` with a terminal object `T`, the bijection of Tag
03AJ sends a torsor `F` under `H` to a class in `H¹(H)`, which the comparison of
`Stacks.Cohomology.TerminalCohomology` reads as a class in `H¹(T, H)`, the value at `T` of
Mathlib's cohomology presheaf. Restricting that class along a morphism `f : V ⟶ T` gives a
class in `H¹(V, H)`, and this file proves that its vanishing forces `F` to have a section
over `V`.

This is the compatibility of the torsor–cohomology dictionary with *restriction to an object*
of the site; `Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1_naturality` is the
compatibility with change of the coefficient sheaf.

## Main results

* `Stacks.Cohomology.Torsors.freeYonedaSheafHomEquiv_apply`: the corepresentation of
  evaluation at `X` by the free abelian sheaf on `yoneda.obj X` sends a morphism to the value
  of its underlying natural transformation on the generator of the identity of `X`.
* `Stacks.Cohomology.Torsors.cohomologyPresheaf_map_apply`: the restriction map of the
  cohomology presheaf is composition with the map of corepresenting sheaves in `Ext`.
* `Stacks.Cohomology.Torsors.nonempty_sections_of_class_restriction_eq_zero`: **the
  localization statement.** If the restriction to `V` of the class of a torsor vanishes, the
  torsor has a section over `V`.

## Implementation notes

Everything is an `Ext`-computation with the two corepresenting sheaves. The class of a torsor
is the `Ext`-class of the short exact sequence `torsorPushoutComplex` out of the constant
sheaf `ℤ`; the comparison `freeOfTerminalIsoConstantSheaf` turns it into a class out of the
free abelian sheaf on `yoneda.obj T`; and the restriction map of the cohomology presheaf is
composition with the induced map on free abelian sheaves. So the restricted class is the
boundary of a single morphism `A_V ⟶ constant sheaf ℤ`, and
`Stacks.Cohomology.Torsors.ext_one_boundary_eq_zero_iff_lift` turns its vanishing into a lift
of that morphism to the middle sheaf of the extension. A lift is a section of the middle sheaf
over `V` whose image is the unit section, i.e. a section over `V` of the unit fibre, and the
unit fibre is the torsor itself by `torsorPushoutFiberHom`.

The only computation is that the composite `A_V ⟶ A_T ⟶ ℤ` sends the generator of the
identity of `V` to `1`: a generator of the free abelian group on a one-element set, which is
`rfl`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.Cohomology.Torsors

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]

/-- **The corepresentation of evaluation, computed.** A morphism from the free abelian sheaf on
`yoneda.obj X` to a sheaf `F` corresponds to the section of `F` over `X` obtained by evaluating
it at the generator attached to the identity of `X`. -/
public lemma freeYonedaSheafHomEquiv_apply (X : C) (F : Sheaf J AddCommGrpCat.{v})
    (α : OverObjectCohomology.freeYonedaSheaf J X ⟶ F) :
    OverObjectCohomology.freeYonedaSheafHomEquiv J X F α =
      α.hom.app (op X) ((toSheafify J (yoneda.obj X ⋙ AddCommGrpCat.free)).app (op X)
        (FreeAbelianGroup.of (𝟙 X))) := by
  dsimp only [OverObjectCohomology.freeYonedaSheafHomEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [yonedaEquiv, sheafificationAdjunction_unit_app]
  rfl

/-- The unit of sheafification is natural: sheafifying a morphism of presheaves and then
taking sections over an object is taking sections first. -/
private lemma presheafToSheaf_map_hom_app_toSheafify
    {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (β : P ⟶ Q) (X : Cᵒᵖ) (x : P.obj X) :
    ((presheafToSheaf J AddCommGrpCat.{v}).map β).hom.app X ((toSheafify J P).app X x) =
      (toSheafify J Q).app X (β.app X x) := by
  have h : (toSheafify J P ≫ sheafifyMap J β).app X x = (β ≫ toSheafify J Q).app X x := by
    rw [← toSheafify_naturality]
  simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using h

/-- The corepresentation of evaluation on a sheafified morphism of presheaves. -/
private lemma freeYonedaSheafHomEquiv_presheafToSheaf_map {P : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (X : C)
    (β : yoneda.obj X ⋙ AddCommGrpCat.free ⟶ P) :
    OverObjectCohomology.freeYonedaSheafHomEquiv J X
        ((presheafToSheaf J AddCommGrpCat.{v}).obj P)
        ((presheafToSheaf J AddCommGrpCat.{v}).map β) =
      (toSheafify J P).app (op X) (β.app (op X) (FreeAbelianGroup.of (𝟙 X))) := by
  rw [freeYonedaSheafHomEquiv_apply]
  exact presheafToSheaf_map_hom_app_toSheafify β (op X) _

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

/-- **The restriction map of the cohomology presheaf is composition in `Ext`** with the map of
corepresenting sheaves induced by the morphism of the site. -/
public lemma cohomologyPresheaf_map_apply (F : Sheaf J AddCommGrpCat.{v}) {T V : C} (f : V ⟶ T)
    (x : Sheaf.H' F 1 T) :
    ((F.cohomologyPresheaf 1).map f.op) x =
      (Ext.mk₀ ((presheafToSheaf J AddCommGrpCat.{v}).map
        (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free))).comp x (zero_add 1) := by
  simp only [Sheaf.cohomologyPresheaf, Sheaf.cohomologyPresheafFunctor, Functor.flip_obj_map,
    Functor.comp_map, Functor.op_map, Abelian.extFunctor_map_app]
  rfl

/-- **The first cohomology class of a torsor localizes.** Let `H` be an abelian sheaf on a site
with a terminal object `T`, let `F` be a torsor under `H` and let `f : V ⟶ T`. If the
restriction along `f` of the class of `F` in `H¹(T, H)` vanishes, then `F` has a section
over `V`. -/
public theorem nonempty_sections_of_class_restriction_eq_zero
    (H : Sheaf J AddCommGrpCat.{v}) (F : AbelianTorsor H)
    {T V : C} (hT : IsTerminal T) (f : V ⟶ T)
    (h : ((H.cohomologyPresheaf 1).map f.op)
        ((Ext.mk₀ (TerminalCohomology.freeOfTerminalIsoConstantSheaf J T hT).hom).comp
            (torsorPushoutClass H F) (zero_add 1)) = 0) :
    Nonempty (F.1.presheaf.obj (op V)) := by
  have hS : (torsorPushoutComplex H F).ShortExact := torsorPushoutComplex_shortExact H F
  have key := cohomologyPresheaf_map_apply H f
    ((Ext.mk₀ ((presheafToSheaf J AddCommGrpCat.{v}).map
      (TerminalCohomology.freeYonedaIsoConstULiftInt T hT).hom)).comp hS.extClass (zero_add 1))
  have hzero : (Ext.mk₀ ((presheafToSheaf J AddCommGrpCat.{v}).map
        (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free))).comp
      ((Ext.mk₀ ((presheafToSheaf J AddCommGrpCat.{v}).map
        (TerminalCohomology.freeYonedaIsoConstULiftInt T hT).hom)).comp
          hS.extClass (zero_add 1)) (zero_add 1) = 0 := key.symm.trans h
  rw [Ext.mk₀_comp_mk₀_assoc, ← Functor.map_comp] at hzero
  obtain ⟨r, hr⟩ := (ext_one_boundary_eq_zero_iff_lift (torsorPushoutComplex H F) hS
    (OverObjectCohomology.freeYonedaSheaf J V) _).1 hzero
  have hval : OverObjectCohomology.freeYonedaSheafHomEquiv J V
        (torsorPushoutComplex H F).X₃
        ((presheafToSheaf J AddCommGrpCat.{v}).map
          (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free ≫
            (TerminalCohomology.freeYonedaIsoConstULiftInt T hT).hom)) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{v} ℤ)))).app
        (op V) ⟨1⟩ := by
    rw [freeYonedaSheafHomEquiv_presheafToSheaf_map]
    rfl
  have hiso : IsIso (torsorPushoutFiberHom H F).hom := torsorPushoutFiberHom_isIso H F
  refine ⟨(inv (torsorPushoutFiberHom H F).hom).app (op V)
    ⟨OverObjectCohomology.freeYonedaSheafHomEquiv J V (torsorPushoutComplex H F).X₂ r, ?_⟩⟩
  rw [← OverObjectCohomology.freeYonedaSheafHomEquiv_comp, hr]
  exact hval

/-- **Injectivity of the restriction of first cohomology to an object**, from triviality of the
torsors with a section over that object. Let `H` be an abelian sheaf on a site with a terminal
object `T` and let `f : V ⟶ T`. If every torsor under `H` with a section over `V` is trivial,
then `H¹(T, H) → H¹(V, H)` is injective.

Injectivity is the triviality of the kernel because the restriction map is a group homomorphism;
a class in the kernel is the class of a torsor, which the hypothesis makes trivial. -/
public theorem injective_cohomologyPresheaf_map_of_isTrivial
    (H : Sheaf J AddCommGrpCat.{v}) {T V : C} (hT : IsTerminal T) (f : V ⟶ T)
    (htriv : ∀ F : AbelianTorsor H, Nonempty (F.1.presheaf.obj (op V)) → F.1.IsTrivial) :
    Function.Injective ((H.cohomologyPresheaf 1).map f.op) := by
  have main : ∀ x : Ext.{w} ((presheafToSheaf J AddCommGrpCat.{v}).obj
        (yoneda.obj T ⋙ AddCommGrpCat.free)) H 1,
      ((H.cohomologyPresheaf 1).map f.op) x = 0 → x = 0 := by
    intro x hx
    obtain ⟨cls, hcls⟩ := torsorIsoClassesToH1_surjective H
      ((Ext.mk₀ (TerminalCohomology.freeOfTerminalIsoConstantSheaf J T hT).inv).comp
        x (zero_add 1))
    obtain ⟨F, rfl⟩ := Quotient.exists_rep cls
    have hcls' : torsorPushoutClass H F =
        (Ext.mk₀ (TerminalCohomology.freeOfTerminalIsoConstantSheaf J T hT).inv).comp
          x (zero_add 1) := hcls
    have hxval : x =
        (Ext.mk₀ (TerminalCohomology.freeOfTerminalIsoConstantSheaf J T hT).hom).comp
          (torsorPushoutClass H F) (zero_add 1) := by
      rw [hcls', Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id, Ext.mk₀_id_comp]
    subst hxval
    have hsec := nonempty_sections_of_class_restriction_eq_zero H F hT f hx
    have hq : Quotient.mk (torsorSetoid H)
        (⟨trivialTorsor (abelianSheafAsGroupSheaf H),
          trivialTorsor_isTorsor (abelianSheafAsGroupSheaf H)⟩ : AbelianTorsor H) =
        Quotient.mk (torsorSetoid H) F := Quotient.sound (htriv F hsec)
    have h0 := torsorIsoClassesEquivH1_trivial H
    rw [hq] at h0
    have hc0 : torsorPushoutClass H F = 0 := h0
    rw [hc0, Ext.comp_zero]
  intro a b hab
  have h0 : a - b = 0 := main (a - b) (by rw [map_sub, hab, sub_self])
  rwa [sub_eq_zero] at h0

end Stacks.Cohomology.Torsors

end
