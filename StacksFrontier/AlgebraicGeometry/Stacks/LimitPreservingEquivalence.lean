module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp

/-!
# Limit preservation is invariant under equivalence over the site

Being *limit preserving* in the sense of Stacks 07XL — the comparison `colim 𝒳_{Tᵢ} ⥤ 𝒳_T` is an
equivalence for every cofiltered inverse system of affine schemes with limit `T` — depends only on
the equivalence class of a category fibred in groupoids in the 2-category of categories over the
site. This file proves that invariance.

The argument runs through the three descent conditions of
`StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent`, which characterise the
comparison's being an equivalence and mention no colimit: they speak only of objects of the
fibres, of morphisms, and of lying over a morphism of the base, and a 1-morphism over the base
carries all three along. An equivalence over the base therefore transports each condition, and the
characterisation turns the transported conditions back into an equivalence of comparison functors.

## Main results

* `Deformation.Artin.descentObj_of_equivalenceOver`,
  `Deformation.Artin.descentHom_of_equivalenceOver` and
  `Deformation.Artin.descentEq_of_equivalenceOver`: each of the three descent conditions
  transports along an equivalence over the base.
* `Deformation.Artin.isEquivalence_colimitComparison_of_equivalenceOver`: the colimit comparison
  of Stacks 07XL at a fixed cone is an equivalence for a category fibred in groupoids as soon as
  it is one for an equivalent category over the base.
* `AlgebraicGeometry.Stack.isLimitPreserving_of_equivalenceOver` and
  `AlgebraicGeometry.Stack.isLimitPreserving_iff_of_equivalenceOver`: limit preservation over the
  big fppf site of `S` transports along an equivalence over the site, in either direction.

## Implementation notes

*Why the descent conditions and not the comparison functor.* The colimit of Stacks 07XL is formed
from the split fibres of Stacks 004A, whose morphisms are morphisms between *chosen* pullbacks. A
1-morphism over the base commutes strictly with the structure functors but need not match the two
choices of pullbacks, so it does not induce a functor between the split fibres on the nose and
there is no direct conjugation of one comparison functor into the other. The descent conditions
avoid this entirely, since nothing in them is a chosen pullback.

*The correction by the unit.* Each descent condition asks for data over a *prescribed* object of a
fibre, so pushing the datum forward along `hom.functor` and pulling the answer back along
`inv.functor` lands on `inv.functor.obj (hom.functor.obj x)` rather than on `x`. The components of
the unit 2-isomorphism repair this, and they are vertical by the coherence condition of
`StacksRepresentableCFG.EquivalenceOver`
(`StacksRepresentableCFG.EquivalenceOver.isHomLift_unitIso_hom_app`), so the corrected morphisms
still lie over the morphisms of the base that the conditions require.

## References

* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 004A](https://stacks.math.columbia.edu/tag/004A)
* [Stacks Project, Tag 02XS](https://stacks.math.columbia.edu/tag/02XS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w uC vC uX vX uY vY vI wI

namespace Deformation.Artin

section Transport

attribute [local implicit_reducible] Functor.Fiber

variable {𝒞 : Type uC} [Category.{vC} 𝒞] {X : Type uX} [Category.{vX} X]
  {Y : Type uY} [Category.{vY} Y] {p : X ⥤ 𝒞} {q : Y ⥤ 𝒞}
  {I : Type vI} [Category.{wI} I] (D : I ⥤ 𝒞) (c : Cone D)

/-- A 1-morphism over the base takes an object of a fibre to an object of the same fibre. -/
private abbrev fiberOfMorphismOver (m : StacksRepresentableCFG.MorphismOver p q) {V : 𝒞}
    (x : p.Fiber V) : q.Fiber V :=
  ⟨m.functor.obj x.1, show (m.functor ⋙ q).obj x.1 = V from
    (Functor.congr_obj m.w x.1).trans x.2⟩

/-- A 1-morphism over the base takes a morphism lying over a morphism of the base to a morphism
lying over the same morphism. -/
private lemma isHomLift_map_of_morphismOver (m : StacksRepresentableCFG.MorphismOver p q)
    {R T : 𝒞} (f : R ⟶ T) {a b : X} (φ : a ⟶ b) (hφ : p.IsHomLift f φ) :
    q.IsHomLift f (m.functor.map φ) := by
  have := hφ
  refine IsHomLift.of_fac' q f (m.functor.map φ)
    (show (m.functor ⋙ q).obj a = R from
      (Functor.congr_obj m.w a).trans (IsHomLift.domain_eq p f φ))
    (show (m.functor ⋙ q).obj b = T from
      (Functor.congr_obj m.w b).trans (IsHomLift.codomain_eq p f φ)) ?_
  rw [show q.map (m.functor.map φ) = (m.functor ⋙ q).map φ from rfl,
    Functor.congr_hom m.w φ, IsHomLift.fac' p f φ]
  simp

/-- The unit of an equivalence over the base, composed with the image under the backward
1-morphism of the image under the forward 1-morphism of a morphism and with the inverse unit,
is that morphism again. -/
private lemma unitIso_conj (e : StacksRepresentableCFG.EquivalenceOver p q) {a b : X}
    (g : a ⟶ b) {w : e.hom.functor.obj a ⟶ e.hom.functor.obj b} (hw : w = e.hom.functor.map g) :
    e.unitIso.hom.app a ≫ e.inv.functor.map w ≫ e.unitIso.inv.app b = g := by
  subst hw
  have hnat : e.unitIso.hom.app a ≫ e.inv.functor.map (e.hom.functor.map g)
      = g ≫ e.unitIso.hom.app b := (e.unitIso.hom.naturality g).symm
  rw [← Category.assoc, hnat, Category.assoc]
  simp

/-- Precomposing the image under the backward 1-morphism of a morphism lying over `f` with the
inverse unit gives a morphism lying over `f`. -/
private lemma isHomLift_map_comp_unitIso_inv (e : StacksRepresentableCFG.EquivalenceOver p q)
    {R T : 𝒞} (f : R ⟶ T) {a : X} {z : Y} (d : z ⟶ e.hom.functor.obj a) (hd : q.IsHomLift f d)
    (ha : p.obj a = T) : p.IsHomLift f (e.inv.functor.map d ≫ e.unitIso.inv.app a) := by
  have := e.isHomLift_unitIso_inv_app a
  have := isHomLift_map_of_morphismOver e.inv f d hd
  subst ha
  exact IsHomLift.comp_lift_id_right' p f _ (p.obj a) _

/-- Postcomposing the unit with the image under the backward 1-morphism of a morphism lying over
`f` gives a morphism lying over `f`. -/
private lemma isHomLift_unitIso_hom_comp_map (e : StacksRepresentableCFG.EquivalenceOver p q)
    {R T : 𝒞} (f : R ⟶ T) {a : X} {z : Y} (d : e.hom.functor.obj a ⟶ z) (hd : q.IsHomLift f d)
    (ha : p.obj a = R) : p.IsHomLift f (e.unitIso.hom.app a ≫ e.inv.functor.map d) := by
  have := e.isHomLift_unitIso_hom_app a
  have := isHomLift_map_of_morphismOver e.inv f d hd
  subst ha
  exact IsHomLift.comp_lift_id_left' p (p.obj a) _ f _

/-- **Descent of objects transports along an equivalence over the base.** -/
lemma descentObj_of_equivalenceOver (e : StacksRepresentableCFG.EquivalenceOver p q)
    (h : DescentObj q D c) : DescentObj p D c := by
  intro x
  obtain ⟨i, yi, ε, hε⟩ := h (fiberOfMorphismOver e.hom x)
  refine ⟨i, fiberOfMorphismOver e.inv yi, e.unitIso.hom.app x.1 ≫ e.inv.functor.map ε, ?_⟩
  exact isHomLift_unitIso_hom_comp_map e _ ε hε x.2

/-- **Descent of vertical morphisms transports along an equivalence over the base.** -/
lemma descentHom_of_equivalenceOver (e : StacksRepresentableCFG.EquivalenceOver p q)
    (h : DescentHom q D c) : DescentHom p D c := by
  intro i xi yi x y δ ε hδ hε φ hφ
  obtain ⟨k, s, xk, yk, dx, dy, δk, ψ, hdx, hdy, hδk, hψ, h₁, h₂⟩ :=
    h i (fiberOfMorphismOver e.hom xi) (fiberOfMorphismOver e.hom yi)
      (fiberOfMorphismOver e.hom x) (fiberOfMorphismOver e.hom y)
      (e.hom.functor.map δ) (e.hom.functor.map ε)
      (isHomLift_map_of_morphismOver e.hom (c.π.app i) δ hδ)
      (isHomLift_map_of_morphismOver e.hom (c.π.app i) ε hε)
      (e.hom.functor.map φ) (isHomLift_map_of_morphismOver e.hom (𝟙 c.pt) φ hφ)
  refine ⟨k, s, fiberOfMorphismOver e.inv xk, fiberOfMorphismOver e.inv yk,
    e.inv.functor.map dx ≫ e.unitIso.inv.app xi.1,
    e.inv.functor.map dy ≫ e.unitIso.inv.app yi.1,
    e.unitIso.hom.app x.1 ≫ e.inv.functor.map δk, e.inv.functor.map ψ,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isHomLift_map_comp_unitIso_inv e _ dx hdx xi.2
  · exact isHomLift_map_comp_unitIso_inv e _ dy hdy yi.2
  · exact isHomLift_unitIso_hom_comp_map e _ δk hδk x.2
  · exact isHomLift_map_of_morphismOver e.inv (𝟙 (D.obj k)) ψ hψ
  · simpa only [Functor.map_comp, Category.assoc] using unitIso_conj e δ h₁
  · simpa only [Functor.map_comp, Category.assoc] using unitIso_conj e (φ ≫ ε)
      (w := δk ≫ ψ ≫ dy) (by rw [h₂, Functor.map_comp])

/-- **Descent of equalities of vertical morphisms transports along an equivalence over the
base.** -/
lemma descentEq_of_equivalenceOver (e : StacksRepresentableCFG.EquivalenceOver p q)
    (h : DescentEq q D c) : DescentEq p D c := by
  intro i xi yi x δ hδ ψ ψ' hψ hψ' hδψ
  obtain ⟨k, s, xk, dx, hdx, hres⟩ :=
    h i (fiberOfMorphismOver e.hom xi) (fiberOfMorphismOver e.hom yi)
      (fiberOfMorphismOver e.hom x) (e.hom.functor.map δ)
      (isHomLift_map_of_morphismOver e.hom (c.π.app i) δ hδ)
      (e.hom.functor.map ψ) (e.hom.functor.map ψ')
      (isHomLift_map_of_morphismOver e.hom (𝟙 (D.obj i)) ψ hψ)
      (isHomLift_map_of_morphismOver e.hom (𝟙 (D.obj i)) ψ' hψ')
      (by rw [← Functor.map_comp, ← Functor.map_comp, hδψ])
  refine ⟨k, s, fiberOfMorphismOver e.inv xk,
    e.inv.functor.map dx ≫ e.unitIso.inv.app xi.1, ?_, ?_⟩
  · exact isHomLift_map_comp_unitIso_inv e _ dx hdx xi.2
  have key : ∀ χ : xi.1 ⟶ yi.1,
      (e.inv.functor.map dx ≫ e.unitIso.inv.app xi.1) ≫ χ =
        e.inv.functor.map (dx ≫ e.hom.functor.map χ) ≫ e.unitIso.inv.app yi.1 := by
    intro χ
    have hn : e.unitIso.inv.app xi.1 ≫ χ =
        e.inv.functor.map (e.hom.functor.map χ) ≫ e.unitIso.inv.app yi.1 :=
      (e.unitIso.inv.naturality χ).symm
    rw [Category.assoc, hn, ← Category.assoc, ← Functor.map_comp]
  rw [key ψ, key ψ', hres]

/-- **The colimit comparison of Stacks 07XL is an equivalence for a category fibred in groupoids
as soon as it is one for an equivalent category over the base.** Both sides are read at the same
cofiltered cone of the base.

The transport is through the three descent conditions, which involve no colimit; see the
implementation notes of this module. -/
lemma isEquivalence_colimitComparison_of_equivalenceOver
    (e : StacksRepresentableCFG.EquivalenceOver p q) [p.IsFibered] [q.IsFibered]
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) [IsCofiltered I]
    (h : (colimitComparison q D c).IsEquivalence) :
    (colimitComparison p D c).IsEquivalence := by
  have := h.faithful
  have := h.full
  have := h.essSurj
  exact ⟨faithful_of_descentEq p hp D c
      (descentEq_of_equivalenceOver D c e (descentEq_of_faithful q hq D c)),
    full_of_descentHom p hp D c
      (descentHom_of_equivalenceOver D c e (descentHom_of_full q hq D c)),
    essSurj_of_descentObj p hp D c
      (descentObj_of_equivalenceOver D c e (descentObj_of_essSurj q D c))⟩

end Transport

end Deformation.Artin

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, vX, u + 1, uX} (BigFppfOver B S hS))
  (𝒴 : CatFiberedInGroupoids.{u, vY, u + 1, uY} (BigFppfOver B S hS))

/-- **Limit preservation transports along an equivalence over the site.** If `𝒳` and `𝒴` are
categories fibred in groupoids over the big fppf site of `S` which are equivalent in the
2-category of categories over that site, and `𝒴` is limit preserving in the sense of Stacks 07XL,
then so is `𝒳`.

An equivalence over the site induces an equivalence of every fibre category compatibly with
restriction, so the two comparison functors `colim 𝒳_{Tᵢ} ⥤ 𝒳_T` and `colim 𝒴_{Tᵢ} ⥤ 𝒴_T` are
equivalences together; the proof realises this through the descent conditions characterising them.
Use `StacksRepresentableCFG.EquivalenceOver.symm` to read the hypothesis on the other side, or
`AlgebraicGeometry.Stack.isLimitPreserving_iff_of_equivalenceOver`. -/
theorem isLimitPreserving_of_equivalenceOver
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳.val.p 𝒴.val.p)
    (h𝒴 : Deformation.Artin.IsLimitPreserving.{u, v, w, uY, vY} B S hS 𝒴) :
    Deformation.Artin.IsLimitPreserving.{u, v, w, uX, vX} B S hS 𝒳 := by
  have hp : 𝒳.val.p.IsFiberedInGroupoids := 𝒳.2
  have hq : 𝒴.val.p.IsFiberedInGroupoids := 𝒴.2
  have : 𝒳.val.p.IsFibered := hp.isFibered
  have : 𝒴.val.p.IsFibered := hq.isFibered
  intro J _ _ D c hc
  exact Deformation.Artin.isEquivalence_colimitComparison_of_equivalenceOver
    (D ⋙ BigAffineFppf.inclusion B S hS)
    ((BigAffineFppf.inclusion B S hS).mapCone c) e hp hq (h𝒴 J D c hc)

/-- **Limit preservation is an invariant of the equivalence class over the site.** Two categories
fibred in groupoids over the big fppf site of `S` which are equivalent in the 2-category of
categories over that site are limit preserving in the sense of Stacks 07XL together. -/
theorem isLimitPreserving_iff_of_equivalenceOver
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳.val.p 𝒴.val.p) :
    Deformation.Artin.IsLimitPreserving.{u, v, w, uX, vX} B S hS 𝒳 ↔
      Deformation.Artin.IsLimitPreserving.{u, v, w, uY, vY} B S hS 𝒴 :=
  ⟨isLimitPreserving_of_equivalenceOver B S hS 𝒴 𝒳 e.symm,
    isLimitPreserving_of_equivalenceOver B S hS 𝒳 𝒴 e⟩

end AlgebraicGeometry.Stack

end
