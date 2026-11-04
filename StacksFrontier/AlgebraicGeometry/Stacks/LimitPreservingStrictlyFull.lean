module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingEquivalence
import all StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingEquivalence

/-!
# Limit preservation along a fully faithful 1-morphism over the site

Let `𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of a
scheme `S` which is *fully faithful*, so that `𝒳` is a strictly full subcategory of `𝒴`. If `𝒴`
is limit preserving in the sense of Stacks 07XL, then so is `𝒳`, **provided** the image of `𝒳`
is recognised at a finite stage: whenever an object of a fibre of `𝒳` over the vertex of a
cofiltered cone is the restriction of an object of `𝒴` over a stage, that stage object must
already lie in the image of `𝒳` after passing to a later stage. That proviso is
`Deformation.Artin.DescentImage`.

## Main definitions

* `Deformation.Artin.DescentImage`: the image of a 1-morphism over the base is recognised at a
  finite stage of a cofiltered cone.

## Main results

* `Deformation.Artin.descentObj_of_morphismOver`,
  `Deformation.Artin.descentHom_of_morphismOver` and
  `Deformation.Artin.descentEq_of_morphismOver`: the three descent conditions
  `Deformation.Artin.DescentObj`, `Deformation.Artin.DescentHom` and
  `Deformation.Artin.DescentEq` pull back along a fully faithful 1-morphism over the base.
  Fullness and faithfulness alone suffice for the conditions on morphisms; the condition on
  objects needs `Deformation.Artin.DescentImage` as well.
* `Deformation.Artin.isEquivalence_colimitComparison_of_morphismOver`: the colimit comparison of
  Stacks 07XL at a fixed cofiltered cone is an equivalence for the source as soon as it is one
  for the target.
* `AlgebraicGeometry.Stack.isLimitPreserving_of_morphismOver`: limit preservation passes from the
  target of a fully faithful 1-morphism over the site to its source.

## References

* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 003S](https://stacks.math.columbia.edu/tag/003S)
* [Stacks Project, Tag 02XK](https://stacks.math.columbia.edu/tag/02XK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w uC vC uX vX uY vY vI wI

namespace Deformation.Artin

section StrictlyFull

attribute [local implicit_reducible] Functor.Fiber

variable {𝒞 : Type uC} [Category.{vC} 𝒞] {X : Type uX} [Category.{vX} X]
  {Y : Type uY} [Category.{vY} Y] {p : X ⥤ 𝒞} {q : Y ⥤ 𝒞}
  {I : Type vI} [Category.{wI} I] (D : I ⥤ 𝒞) (c : Cone D)

/-- A morphism of the source whose image lies over a morphism of the base already lies over that
morphism: a 1-morphism over the base reflects the lifting relation. -/
private lemma isHomLift_pull (m : StacksRepresentableCFG.MorphismOver p q)
    {R T : 𝒞} (f : R ⟶ T) {a b : X} (φ : a ⟶ b)
    (hφ : q.IsHomLift f (m.functor.map φ)) : p.IsHomLift f φ := by
  have := hφ
  refine IsHomLift.of_fac' p f φ
    ((Functor.congr_obj m.w a).symm.trans (IsHomLift.domain_eq q f (m.functor.map φ)))
    ((Functor.congr_obj m.w b).symm.trans (IsHomLift.codomain_eq q f (m.functor.map φ))) ?_
  rw [Functor.congr_hom m.w.symm φ,
    show (m.functor ⋙ q).map φ = q.map (m.functor.map φ) from rfl,
    IsHomLift.fac' q f (m.functor.map φ)]
  simp

/-- Two lifts of the same base morphism, one along `p` and one along `q`, differ by a vertical
isomorphism. -/
private lemma exists_isIso_comp_map_eq (m : StacksRepresentableCFG.MorphismOver p q)
    (hq : q.IsFiberedInGroupoids) {R T : 𝒞} (f : R ⟶ T) {xk xi : X} (dx : xk ⟶ xi)
    (hdx : p.IsHomLift f dx) {zk : Y} (dz : zk ⟶ m.functor.obj xi) (hdz : q.IsHomLift f dz) :
    ∃ θ : zk ⟶ m.functor.obj xk, IsIso θ ∧ q.IsHomLift (𝟙 R) θ ∧ θ ≫ m.functor.map dx = dz := by
  have := hdz
  have := isHomLift_map_of_morphismOver m f dx hdx
  have := hq.isStronglyCartesian_homLift f (m.functor.map dx)
  set θ := Functor.IsStronglyCartesian.map q f (m.functor.map dx) (Category.id_comp f).symm dz
  have := hq.isStronglyCartesian_homLift (𝟙 R) θ
  exact ⟨θ, Functor.IsStronglyCartesian.isIso_of_base_isIso q (𝟙 R) θ, inferInstance,
    Functor.IsStronglyCartesian.fac q f (m.functor.map dx) _ dz⟩

/-- **The image of a 1-morphism over the base is recognised at a finite stage.** Whenever an
object `x` of the fibre over the vertex of the cone maps, over a cone projection, to an object
`zi` of the fibre over the stage `i` of the target category, some later stage carries an object
of the source category whose image maps to `zi` over the corresponding transition morphism. -/
def DescentImage (m : StacksRepresentableCFG.MorphismOver p q) : Prop :=
  ∀ (i : I) (x : p.Fiber c.pt) (zi : q.Fiber (D.obj i))
    (ε : m.functor.obj x.1 ⟶ zi.1), q.IsHomLift (c.π.app i) ε →
    ∃ (k : I) (s : k ⟶ i) (xk : p.Fiber (D.obj k))
      (d : m.functor.obj xk.1 ⟶ zi.1), q.IsHomLift (D.map s) d

/-- **Descent of objects pulls back along a fully faithful 1-morphism over the base whose image
is recognised at a finite stage.** -/
lemma descentObj_of_morphismOver (m : StacksRepresentableCFG.MorphismOver p q)
    (hq : q.IsFiberedInGroupoids) (hfull : m.functor.Full)
    (himg : DescentImage D c m) (h : DescentObj q D c) : DescentObj p D c := by
  intro x
  obtain ⟨i, zi, ε, hε⟩ := h (fiberOfMorphismOver m x)
  obtain ⟨k, s, xk, d, hd⟩ := himg i x zi ε hε
  have := hε
  have := hd
  have := hq.isStronglyCartesian_homLift (D.map s) d
  have hfac : c.π.app i = c.π.app k ≫ D.map s := (c.w s).symm
  obtain ⟨δ, hδ⟩ := hfull.map_surjective
    (Functor.IsStronglyCartesian.map q (D.map s) d hfac ε)
  refine ⟨k, xk, δ, isHomLift_pull m (c.π.app k) δ ?_⟩
  rw [hδ]
  infer_instance

/-- **Descent of equalities of vertical morphisms pulls back along a faithful 1-morphism over the
base.** No condition on the image is needed. -/
lemma descentEq_of_morphismOver (m : StacksRepresentableCFG.MorphismOver p q)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hfaith : m.functor.Faithful) (h : DescentEq q D c) : DescentEq p D c := by
  intro i xi yi x δ hδ ψ ψ' hψ hψ' hδψ
  obtain ⟨k, s, zk, dz, hdz, hres⟩ :=
    h i (fiberOfMorphismOver m xi) (fiberOfMorphismOver m yi) (fiberOfMorphismOver m x)
      (m.functor.map δ)
      (isHomLift_map_of_morphismOver m (c.π.app i) δ hδ)
      (m.functor.map ψ) (m.functor.map ψ')
      (isHomLift_map_of_morphismOver m (𝟙 (D.obj i)) ψ hψ)
      (isHomLift_map_of_morphismOver m (𝟙 (D.obj i)) ψ' hψ')
      (by rw [← Functor.map_comp, ← Functor.map_comp, hδψ])
  obtain ⟨xk, dx, hdx⟩ := hp.exists_lift (D.map s) xi.1 xi.2
  obtain ⟨θ, hθ, -, hθfac⟩ := exists_isIso_comp_map_eq m hq (D.map s) dx hdx dz hdz
  refine ⟨k, s, ⟨xk, IsHomLift.domain_eq p (D.map s) dx⟩, dx, hdx, ?_⟩
  refine hfaith.map_injective ?_
  rw [Functor.map_comp, Functor.map_comp]
  refine (cancel_epi θ).mp ?_
  rw [← Category.assoc, ← Category.assoc, hθfac]
  exact hres

/-- **Descent of vertical morphisms pulls back along a fully faithful 1-morphism over the
base.** No condition on the image is needed. -/
lemma descentHom_of_morphismOver (m : StacksRepresentableCFG.MorphismOver p q)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hfull : m.functor.Full) (hfaith : m.functor.Faithful)
    (h : DescentHom q D c) : DescentHom p D c := by
  intro i xi yi x y δ ε hδ hε φ hφ
  obtain ⟨k, s, zk, wk, dz, dw, δk, ψq, hdz, hdw, hδk, hψq, h₁, h₂⟩ :=
    h i (fiberOfMorphismOver m xi) (fiberOfMorphismOver m yi)
      (fiberOfMorphismOver m x) (fiberOfMorphismOver m y)
      (m.functor.map δ) (m.functor.map ε)
      (isHomLift_map_of_morphismOver m (c.π.app i) δ hδ)
      (isHomLift_map_of_morphismOver m (c.π.app i) ε hε)
      (m.functor.map φ) (isHomLift_map_of_morphismOver m (𝟙 c.pt) φ hφ)
  obtain ⟨xk, dx, hdx⟩ := hp.exists_lift (D.map s) xi.1 xi.2
  obtain ⟨yk, dy, hdy⟩ := hp.exists_lift (D.map s) yi.1 yi.2
  obtain ⟨θ, hθ, hθl, hθfac⟩ := exists_isIso_comp_map_eq m hq (D.map s) dx hdx dz hdz
  obtain ⟨ρ, -, hρl, hρfac⟩ := exists_isIso_comp_map_eq m hq (D.map s) dy hdy dw hdw
  have := hδk
  have := hψq
  have : q.IsHomLift (𝟙 (D.obj k)) (inv θ) := by
    simpa using IsHomLift.inv (p := q) (f := 𝟙 (D.obj k)) (φ := θ)
  obtain ⟨ψ, hψ⟩ := hfull.map_surjective (inv θ ≫ ψq ≫ ρ)
  obtain ⟨δkp, hδkp⟩ := hfull.map_surjective (δk ≫ θ)
  refine ⟨k, s, ⟨xk, IsHomLift.domain_eq p (D.map s) dx⟩,
    ⟨yk, IsHomLift.domain_eq p (D.map s) dy⟩, dx, dy, δkp, ψ,
    hdx, hdy, ?_, ?_, ?_, ?_⟩
  · refine isHomLift_pull m (c.π.app k) δkp ?_
    rw [hδkp]
    exact IsHomLift.comp_lift_id_right' q (c.π.app k) δk (D.obj k) θ
  · refine isHomLift_pull m (𝟙 (D.obj k)) ψ ?_
    rw [hψ]
    infer_instance
  · refine hfaith.map_injective ?_
    rw [Functor.map_comp, hδkp, Category.assoc, hθfac]
    exact h₁
  · refine hfaith.map_injective ?_
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, hδkp, hψ]
    simpa [hρfac] using h₂

/-- **The colimit comparison of Stacks 07XL is an equivalence for the source of a fully faithful
1-morphism over the base whose image is recognised at a finite stage, as soon as it is one for
the target.** Both sides are read at the same cofiltered cone of the base. -/
lemma isEquivalence_colimitComparison_of_morphismOver [IsCofiltered I]
    (m : StacksRepresentableCFG.MorphismOver p q) [p.IsFibered] [q.IsFibered]
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hfull : m.functor.Full) (hfaith : m.functor.Faithful)
    (himg : DescentImage D c m)
    (h : (colimitComparison q D c).IsEquivalence) :
    (colimitComparison p D c).IsEquivalence := by
  have := h.faithful
  have := h.full
  have := h.essSurj
  exact ⟨faithful_of_descentEq p hp D c
      (descentEq_of_morphismOver D c m hp hq hfaith (descentEq_of_faithful q hq D c)),
    full_of_descentHom p hp D c
      (descentHom_of_morphismOver D c m hp hq hfull hfaith (descentHom_of_full q hq D c)),
    essSurj_of_descentObj p hp D c
      (descentObj_of_morphismOver D c m hq hfull himg (descentObj_of_essSurj q D c))⟩

end StrictlyFull

end Deformation.Artin

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, vX, u + 1, uX} (BigFppfOver B S hS))
  (𝒴 : CatFiberedInGroupoids.{u, vY, u + 1, uY} (BigFppfOver B S hS))

/-- **Limit preservation passes to a strictly full subcategory whose image is recognised at a
finite stage.** Let `m : 𝒳 ⟶ 𝒴` be a fully faithful 1-morphism of categories fibred in groupoids
over the big fppf site of `S`, and suppose that for every cofiltered inverse system of affine
schemes over `S` with limit `T` the image of `𝒳` is recognised at a finite stage of the system
(`Deformation.Artin.DescentImage`). If `𝒴` is limit preserving in the sense of Stacks 07XL then
so is `𝒳`. -/
theorem isLimitPreserving_of_morphismOver
    (m : StacksRepresentableCFG.MorphismOver 𝒳.val.p 𝒴.val.p)
    (hfull : m.functor.Full) (hfaith : m.functor.Faithful)
    (himg : ∀ (J : Type v) [Category.{w} J] [IsCofiltered J]
      (D : J ⥤ BigAffineFppf B S hS) (cc : Cone D),
      IsLimit ((BigAffineFppf.toScheme B S hS).mapCone cc) →
      Deformation.Artin.DescentImage (D ⋙ BigAffineFppf.inclusion B S hS)
        ((BigAffineFppf.inclusion B S hS).mapCone cc) m)
    (h𝒴 : Deformation.Artin.IsLimitPreserving.{u, v, w, uY, vY} B S hS 𝒴) :
    Deformation.Artin.IsLimitPreserving.{u, v, w, uX, vX} B S hS 𝒳 := by
  have hp : 𝒳.val.p.IsFiberedInGroupoids := 𝒳.2
  have hq : 𝒴.val.p.IsFiberedInGroupoids := 𝒴.2
  have : 𝒳.val.p.IsFibered := hp.isFibered
  have : 𝒴.val.p.IsFibered := hq.isFibered
  intro J _ _ D cc hc
  exact Deformation.Artin.isEquivalence_colimitComparison_of_morphismOver
    (D ⋙ BigAffineFppf.inclusion B S hS)
    ((BigAffineFppf.inclusion B S hS).mapCone cc) m hp hq hfull hfaith
    (himg J D cc hc) (h𝒴 J D cc hc)

end AlgebraicGeometry.Stack

end
