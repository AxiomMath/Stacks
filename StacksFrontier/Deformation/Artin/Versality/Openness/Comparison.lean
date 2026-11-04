module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver
public import StacksFrontier.CategoryTheory.FiberedCategory.PairIsoClassPresheaf
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.Deformation.Artin.FormalObject.Versal
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.Smooth.Basic
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor
public import StacksFrontier.Deformation.Artin.Predeformation.FibreProduct
public import StacksFrontier.Deformation.Artin.Versality.Openness.Composition
public import StacksFrontier.Deformation.Artin.Versality.Openness.BaseChange

/-!
# Comparisons of categories over the site are smooth on predeformation categories

A 1-morphism over the big fppf site that is full and surjective on objects is smooth on
predeformation categories, the condition is invariant under 2-isomorphism, and consequently the
exchange of the factors of a 2-fibre product and the first projection of a 2-fibre product are
smooth on predeformation categories.
-/

@[expose] public section

namespace Deformation.Artin

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v v' w w' vX vY vZ wX wY wZ

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.TwoFibreProductOver.structureFunctor
  CategoryTheory.TwoFibreProductOver.fst CategoryTheory.TwoFibreProductOver.snd

/-! ### A comparison of categories over the site is smooth on predeformation categories

Stacks 07XV is stated for one of the two orderings of a cospan: it concludes the smoothness
condition for `CategoryTheory.TwoFibreProductOver.snd`, the projection of `𝒳 ×_𝒴 𝒵` to its
*second* factor. Several consumers — `AlgebraicGeometry.Stack.HasRelativeProperty`
(**Stacks 03YK**) among them — present the same 2-fibre product with the factors in the other
order, and so ask for the condition at
`CategoryTheory.TwoFibreProductOver.fst`. The exchange of the two factors,
`CategoryTheory.TwoFibreProductOver.swap`, carries one presentation to the other strictly over
the site, so what is needed to pass between them is that the smoothness condition on
predeformation categories is *transported* along such an exchange.

That is supplied here by the observation that makes the transport cheap: a 1-morphism over the
site which is full and surjective on objects solves every lifting problem defining smoothness by
taking a preimage, so it is itself smooth on predeformation categories, and Stacks 07XU then
composes it with the library's form of Stacks 07XV. -/

noncomputable section Comparison

open AlgebraicGeometry CategoryTheory

universe uA uB vA vB

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {S : Scheme.{u}}
variable (iΛ : Spec (.of Λ) ⟶ S)

attribute [local instance] explicitDeformationCategory

/-- **A based functor over `𝒞_Λ` which is full and surjective on objects is smooth.** A lifting
problem for it is a morphism `g : y ⟶ Φ x`; surjectivity on objects writes `y` as `Φ y'` and
fullness writes `g` as `Φ h` for an `h : y' ⟶ x`, which lies over the same arrow of `𝒞_Λ` as
`g` because `Φ` is over `𝒞_Λ`. So `h` is a solution, with the identity of `y` as its comparison
arrow. Neither faithfulness nor any hypothesis on the two categories is used. -/
private lemma isSmooth_of_full_of_surjective_obj
    {𝓐 : BasedCategory.{vA, uA} (ArtinianLocalAlgCat.{u, u, u} Λ k)}
    {ℬ : BasedCategory.{vB, uB} (ArtinianLocalAlgCat.{u, u, u} Λ k)}
    (Φ : BasedFunctor 𝓐 ℬ) (hfull : Φ.toFunctor.Full) (hs : Function.Surjective Φ.obj) :
    Deformation.IsSmooth Φ := by
  let := hfull
  intro A₁ A₂ f _ y x g hg
  obtain ⟨y', rfl⟩ := hs y
  obtain ⟨h, rfl⟩ := Φ.toFunctor.map_surjective g
  let : ℬ.p.IsHomLift f (Φ.map h) := hg
  exact ⟨y', h, 𝟙 (Φ.obj y'), BasedFunctor.isHomLift_map Φ f h,
    IsHomLift.id (IsHomLift.domain_eq ℬ.p f (Φ.map h)),
    (Category.id_comp (Φ.map h)).symm⟩

/-- **Smoothness of a based functor is invariant under a 2-isomorphism.** A lifting problem
`g : y ⟶ Ψ x` for `Ψ` becomes one for `Φ` on composing with the component of `α⁻¹` at `x`,
which is vertical; the object `x'` and the arrow `h : x' ⟶ x` that smoothness of `Φ` returns
then solve the original problem, with the component of `α⁻¹` at `x'` prepended to the
comparison arrow returned. The equation to be checked is the naturality square of `α` at `h`.

The two hypotheses are exactly the data of an isomorphism `Φ ≅ Ψ` in `𝓐 ⥤ᵇ ℬ`, read off
through `CategoryTheory.BasedNatIso.mkNatIso`. -/
private lemma isSmooth_of_natIso
    {𝓐 : BasedCategory.{vA, uA} (ArtinianLocalAlgCat.{u, u, u} Λ k)}
    {ℬ : BasedCategory.{vB, uB} (ArtinianLocalAlgCat.{u, u, u} Λ k)}
    {Φ Ψ : BasedFunctor 𝓐 ℬ} (α : Φ.toFunctor ≅ Ψ.toFunctor)
    (hα : ∀ a : 𝓐.obj, ℬ.p.IsHomLift (𝟙 (𝓐.p.obj a)) (α.hom.app a))
    (hΦ : Deformation.IsSmooth Φ) : Deformation.IsSmooth Ψ := by
  have hinv : ∀ a : 𝓐.obj, ℬ.p.IsHomLift (𝟙 (𝓐.p.obj a)) (α.inv.app a) := by
    intro a
    have h₁ : ℬ.p.IsHomLift (𝟙 (𝓐.p.obj a)) (α.app a).hom := (Iso.app_hom α a) ▸ hα a
    let := h₁
    rw [← Iso.app_inv]
    exact IsHomLift.lift_id_inv ℬ.p (𝓐.p.obj a) (α.app a)
  intro A₁ A₂ f hf y x g hg
  let := hg
  have hx : 𝓐.p.obj x = A₂ := (Ψ.w_obj x).symm.trans (IsHomLift.codomain_eq ℬ.p f g)
  let : ℬ.p.IsHomLift (𝟙 A₂) (α.inv.app x) := by rw [← hx]; exact hinv x
  obtain ⟨x', l, a, hl, ha, he⟩ := hΦ f hf y x (g ≫ α.inv.app x) inferInstance
  let := hl
  let := ha
  have hx' : 𝓐.p.obj x' = A₁ := IsHomLift.domain_eq 𝓐.p f l
  let : ℬ.p.IsHomLift (𝟙 A₁) (α.inv.app x') := by rw [← hx']; exact hinv x'
  refine ⟨x', l, α.inv.app x' ≫ a, hl, inferInstance, ?_⟩
  calc Ψ.map l = α.inv.app x' ≫ α.hom.app x' ≫ Ψ.map l := by
        rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    _ = α.inv.app x' ≫ Φ.map l ≫ α.hom.app x := by rw [← α.hom.naturality l]
    _ = (α.inv.app x' ≫ a) ≫ g := by rw [he]; simp

section Explicit

variable {X : Type v} [Category.{w} X] (q : X ⥤ Over S) (x₀ : X)
variable (hx₀ : q.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
variable {Y : Type v'} [Category.{w'} Y] (qY : Y ⥤ Over S) (F : X ⥤ Y) (hF : F ⋙ qY = q)

/-- The arrow of `𝒞_Λ` of a composite of morphisms of deformations is the composite of the
two. -/
private lemma explicit_comp_ringHom {a b c : DeformationObject iΛ q x₀ hx₀}
    (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).ringHom = f.ringHom ≫ g.ringHom := rfl

/-- The reversed arrow of a composite of morphisms of deformations is the composite of the two
in the other order. -/
private lemma explicit_comp_arrow {a b c : DeformationObject iΛ q x₀ hx₀}
    (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).arrow = g.arrow ≫ f.arrow := rfl

/-- The arrow of `𝒞_Λ` of an identity of deformations is an identity. -/
private lemma explicit_id_ringHom (a : DeformationObject iΛ q x₀ hx₀) :
    (𝟙 a : a ⟶ a).ringHom = 𝟙 a.algebra := rfl

/-- The reversed arrow of an identity of deformations is an identity. -/
private lemma explicit_id_arrow (a : DeformationObject iΛ q x₀ hx₀) :
    (𝟙 a : a ⟶ a).arrow = 𝟙 a.point := rfl

/-- The induced functor of explicit presentations of deformations is full as soon as the
1-morphism it comes from is full and faithful: a reversed arrow between the images is the image
of its preimage, the triangle it has to satisfy is the image of the triangle to be proved — so
faithfulness gives that — and lying over an arrow of `𝒞_Λ` is read in the base through
`Deformation.Artin.map_left_of_comp_eq`. -/
private lemma explicitMap_full [F.Full] [F.Faithful] :
    (explicitMap iΛ q x₀ hx₀ qY F hF).Full where
  map_surjective {a b} m := by
    obtain ⟨ar, har⟩ : ∃ ar : b.point ⟶ a.point, F.map ar = m.arrow :=
      ⟨F.preimage m.arrow, F.map_preimage _⟩
    have htri : b.arrow ≫ ar = a.arrow := by
      apply F.map_injective
      rw [F.map_comp, har]
      exact m.triangle
    have hbase : eqToHom (congrArg Over.left b.base).symm ≫ (q.map ar).left ≫
        eqToHom (congrArg Over.left a.base) =
          Spec.map (CommRingCat.ofHom m.ringHom.hom.toRingHom) := by
      have h := m.arrow_base
      rw [← har, map_left_of_comp_eq q qY F hF ar] at h
      simpa using h
    exact ⟨{ ringHom := m.ringHom, arrow := ar, triangle := htri, arrow_base := hbase },
      DeformationMorphism.ext_of_components _ _ _ _ rfl har⟩

/-- The induced functor of explicit presentations of deformations is surjective on objects as
soon as the 1-morphism it comes from is full, faithful and surjective on objects. A deformation
of the image point deforms a preimage of its deformed object, along the preimage of its arrow;
that the preimage lies over the right spectrum, and that its arrow lies over the closed-point
map, are the two equations of the given deformation read through
`Deformation.Artin.map_left_of_comp_eq`. -/
private lemma explicitMap_surjective_obj [F.Full] [F.Faithful]
    (hsurj : Function.Surjective F.obj) :
    Function.Surjective (explicitMap iΛ q x₀ hx₀ qY F hF).obj := by
  intro d
  obtain ⟨p, hp⟩ := hsurj d.point
  obtain ⟨ar, har⟩ : ∃ ar : x₀ ⟶ p, F.map ar = d.arrow ≫ eqToHom hp.symm :=
    ⟨F.preimage _, F.map_preimage _⟩
  have hbase : q.obj p = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ d.algebra)) ≫ iΛ) :=
    (Functor.congr_obj hF p).symm.trans ((congrArg qY.obj hp).trans d.base)
  have harrow : d.arrow = F.map ar ≫ eqToHom hp := by
    rw [har, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  refine ⟨{ algebra := d.algebra, point := p, arrow := ar, base := hbase,
            arrow_base := ?_ }, ?_⟩
  · have h := d.arrow_base
    rw [harrow, Functor.map_comp, Over.comp_left, eqToHom_map, Over.eqToHom_left,
      map_left_of_comp_eq q qY F hF ar] at h
    simpa using h
  · exact deformationObject_ext_of_arrow rfl hp har

/-- **Rebasing explicit deformations along a vertical isomorphism of basepoints is full.** The
functor leaves the reversed arrow and the arrow of `𝒞_Λ` of a morphism of deformations
untouched, and the triangle demanded of a preimage is obtained from the triangle of the image
by cancelling the isomorphism. -/
private lemma rebaseExplicit_full (x₁ : X)
    (hx₁ : q.obj x₁ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (e : x₀ ≅ x₁) (he : q.IsHomLift (𝟙 (q.obj x₀)) e.hom) :
    (rebaseExplicit iΛ q x₀ hx₀ x₁ hx₁ e he).Full where
  map_surjective {a b} m :=
    ⟨{ ringHom := m.ringHom
       arrow := m.arrow
       triangle := by
         have h : e.hom ≫ b.arrow ≫ m.arrow = e.hom ≫ a.arrow := by
           simpa only [Category.assoc] using
             (m.triangle : (e.hom ≫ b.arrow) ≫ m.arrow = e.hom ≫ a.arrow)
         simpa using congrArg (e.inv ≫ ·) h
       arrow_base := m.arrow_base },
     DeformationMorphism.ext_of_components _ _ _ _ rfl rfl⟩

/-- **Rebasing explicit deformations along a vertical isomorphism of basepoints is surjective
on objects.** Rebasing along the inverse isomorphism, which is vertical over the same object of
the base, is a section of it. -/
private lemma rebaseExplicit_surjective_obj (x₁ : X)
    (hx₁ : q.obj x₁ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (e : x₀ ≅ x₁) (he : q.IsHomLift (𝟙 (q.obj x₀)) e.hom) :
    Function.Surjective (rebaseExplicit iΛ q x₀ hx₀ x₁ hx₁ e he).obj := by
  let := he
  have hb : q.obj x₁ = q.obj x₀ := IsHomLift.codomain_eq q (𝟙 (q.obj x₀)) e.hom
  have he' : q.IsHomLift (𝟙 (q.obj x₁)) e.symm.hom := by
    rw [hb]
    exact IsHomLift.lift_id_inv q (q.obj x₀) e
  exact fun d => ⟨(rebaseExplicit iΛ q x₁ hx₁ x₀ hx₀ e.symm he').obj d,
    deformationObject_ext_of_arrow rfl rfl (by simp)⟩

variable (G : X ⥤ Y) (hG : G ⋙ qY = q)

/-- **Smoothness of the induced functor of explicit presentations is invariant under a
2-isomorphism of the 1-morphism inducing it.** The two induced functors land in the explicit
presentations based at `F x₀` and at `G x₀`, which the component of `α` at `x₀` identifies by
rebasing; the rebasing functor is full and surjective on objects, hence smooth, so the
composite of the one for `F` with it is smooth by Stacks 07XU. That composite is isomorphic to
the one for `G` over `𝒞_Λ`, by the component of `α⁻¹` at the deformed object, naturality of `α`
being exactly the triangle such a morphism of deformations has to satisfy. -/
private lemma isSmooth_explicitMap_of_natIso (α : F ≅ G)
    (hα : ∀ x : X, qY.IsHomLift (𝟙 (q.obj x)) (α.hom.app x))
    (hs : Deformation.IsSmooth (explicitMapBased iΛ q x₀ hx₀ qY F hF)) :
    Deformation.IsSmooth (explicitMapBased iΛ q x₀ hx₀ qY G hG) := by
  let hF₀ := imageBasePoint (qY := qY) iΛ q F hF x₀ hx₀
  let hG₀ := imageBasePoint (qY := qY) iΛ q G hG x₀ hx₀
  have hinv : ∀ x : X, qY.IsHomLift (𝟙 (q.obj x)) (α.inv.app x) := by
    intro x
    have h₁ : qY.IsHomLift (𝟙 (q.obj x)) (α.app x).hom := (Iso.app_hom α x) ▸ hα x
    let := h₁
    rw [← Iso.app_inv]
    exact IsHomLift.lift_id_inv qY (q.obj x) (α.app x)
  have hv : qY.IsHomLift (𝟙 (qY.obj (G.obj x₀))) (α.app x₀).symm.hom := by
    rw [show qY.obj (G.obj x₀) = q.obj x₀ from Functor.congr_obj hG x₀]
    exact hinv x₀
  let Rb := rebaseExplicit iΛ qY (G.obj x₀) hG₀ (F.obj x₀) hF₀ (α.app x₀).symm hv
  let RbBased : BasedFunctor
      (BasedCategory.ofFunctor (explicitProjection iΛ qY (F.obj x₀) hF₀))
      (BasedCategory.ofFunctor (explicitProjection iΛ qY (G.obj x₀) hG₀)) :=
    { toFunctor := Rb
      w := rfl }
  have hcomp : Deformation.IsSmooth
      (BasedFunctor.comp (explicitMapBased iΛ q x₀ hx₀ qY F hF) RbBased) :=
    Deformation.isSmooth_comp _ _ hs
      (isSmooth_of_full_of_surjective_obj RbBased
        (rebaseExplicit_full iΛ qY (G.obj x₀) hG₀ (F.obj x₀) hF₀ (α.app x₀).symm hv)
        (rebaseExplicit_surjective_obj iΛ qY (G.obj x₀) hG₀ (F.obj x₀) hF₀ (α.app x₀).symm hv))
  have hσ : ∀ a : DeformationObject iΛ q x₀ hx₀,
      (α.inv.app x₀ ≫ F.map a.arrow) ≫ α.hom.app a.point = G.map a.arrow := by
    intro a
    rw [Category.assoc, α.hom.naturality a.arrow, ← Category.assoc, Iso.inv_hom_id_app,
      Category.id_comp]
  let ε (a : DeformationObject iΛ q x₀ hx₀) :
      (explicitMap iΛ q x₀ hx₀ qY F hF ⋙ Rb).obj a ≅
        (explicitMap iΛ q x₀ hx₀ qY G hG).obj a :=
    { hom := verticalDeformationMorphism_of_isHomLift iΛ rfl (α.inv.app a.point)
        (α.inv.naturality a.arrow) (hinv a.point)
      inv := verticalDeformationMorphism_of_isHomLift iΛ rfl (α.hom.app a.point)
        (hσ a) (hα a.point)
      hom_inv_id := by
        apply DeformationMorphism.ext_of_components <;>
          simp [Rb, explicit_comp_ringHom, explicit_comp_arrow, explicit_id_ringHom,
            explicit_id_arrow, verticalDeformationMorphism_of_isHomLift]
      inv_hom_id := by
        apply DeformationMorphism.ext_of_components <;>
          simp [Rb, explicit_comp_ringHom, explicit_comp_arrow, explicit_id_ringHom,
            explicit_id_arrow, verticalDeformationMorphism_of_isHomLift] }
  let ν : explicitMap iΛ q x₀ hx₀ qY F hF ⋙ Rb ≅ explicitMap iΛ q x₀ hx₀ qY G hG :=
    NatIso.ofComponents ε (by
      intro a b m
      apply DeformationMorphism.ext_of_components
      · simp [ε, Rb, explicit_comp_ringHom, verticalDeformationMorphism_of_isHomLift]
      · simp [ε, Rb, explicit_comp_arrow, verticalDeformationMorphism_of_isHomLift,
          α.inv.naturality m.arrow])
  refine isSmooth_of_natIso
    (Φ := BasedFunctor.comp (explicitMapBased iΛ q x₀ hx₀ qY F hF) RbBased)
    (Ψ := explicitMapBased iΛ q x₀ hx₀ qY G hG) ν (fun a => ?_) hcomp
  have hb : (ν.hom.app a).ringHom = 𝟙 a.algebra := by
    simp [ν, ε, Rb, verticalDeformationMorphism_of_isHomLift]
  show (explicitProjection iΛ qY (G.obj x₀) hG₀).IsHomLift (𝟙 a.algebra) (ν.hom.app a)
  rw [← hb]
  exact IsHomLift.map _ (ν.hom.app a)

end Explicit

/-- **The smoothness condition of Stacks 07XS holds for a 1-morphism over the big fppf site of
`S` which is full and surjective on objects.** Faithfulness is used only to recognise the
preimage of a reversed arrow; the conclusion itself needs no hypothesis on either category.

An isomorphism of categories over the site is the case this exists for: it lets the condition be
transported from one presentation of a 2-fibre product to another. -/
public theorem isSmoothOnPredeformationCategories_of_full_of_surjective_obj
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Type vX} [Category.{wX} X] {Y : Type vY} [Category.{wY} Y]
    (pX : X ⥤ BigFppfOver B S hS) (pY : Y ⥤ BigFppfOver B S hS)
    (F : X ⥤ Y) (hF : F ⋙ pY = pX) [F.Full] [F.Faithful]
    (hsurj : Function.Surjective F.obj) :
    IsSmoothOnPredeformationCategories B S hS pX pY F hF := by
  let Q : BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
  dsimp [IsSmoothOnPredeformationCategories]
  intro Λ k _ _ _ iΛ x₀ hx₀ _ _ _
  have hF' : F ⋙ pY ⋙ Q = pX ⋙ Q := comp_over_eq hF Q
  refine (isSmooth_explicitMap_iff iΛ (pX ⋙ Q) x₀ hx₀ (pY ⋙ Q) F hF'
    (mapPredeformationCategory iΛ (pX ⋙ Q) (pY ⋙ Q) F hF' x₀ hx₀)).mp ?_
  exact isSmooth_of_full_of_surjective_obj (explicitMapBased iΛ (pX ⋙ Q) x₀ hx₀ (pY ⋙ Q) F hF')
    (explicitMap_full iΛ (pX ⋙ Q) x₀ hx₀ (pY ⋙ Q) F hF')
    (explicitMap_surjective_obj iΛ (pX ⋙ Q) x₀ hx₀ (pY ⋙ Q) F hF' hsurj)

/-- **The smoothness condition of Stacks 07XS is invariant under a 2-isomorphism of
1-morphisms.** Let `F` and `G` be 1-morphisms `𝒳 ⟶ 𝒴` of categories over the big fppf site of
`S`, and let `α : F ≅ G` be a 2-isomorphism between them, that is, a natural isomorphism each
of whose components is vertical over the site — the data `(α, hα)` is exactly an isomorphism
`⟨F, hF⟩ ≅ ⟨G, hG⟩` in the bicategory of based categories, see
`CategoryTheory.BasedNatIso.mkNatIso`. If `F` satisfies the condition, so does `G`.

This is what identifies a composite with a strictly given 1-morphism when only a natural
isomorphism between the two is available, as in the assembly of **Stacks 07XX**, where a
composite `(Sch/W)_fppf ⟶ 𝒵 ⟶ (Sch/V)_fppf` has to be recognised as `Over.map g.left`.

It carries no tag: the invariance of the condition under 2-isomorphism is not a statement of
the Stacks project, which works with 1-morphisms up to 2-isomorphism throughout. Unlike
`Deformation.Artin.isSmoothOnPredeformationCategories_of_full_of_surjective_obj`, which
*establishes* the condition for a comparison that is full and surjective on objects, this
*transports* it along an arbitrary 2-isomorphism; neither hypothesis implies the other. -/
public theorem isSmoothOnPredeformationCategories_of_natIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Type vX} [Category.{wX} X] {Y : Type vY} [Category.{wY} Y]
    (pX : X ⥤ BigFppfOver B S hS) (pY : Y ⥤ BigFppfOver B S hS)
    (F G : X ⥤ Y) (hF : F ⋙ pY = pX) (hG : G ⋙ pY = pX) (α : F ≅ G)
    (hα : ∀ x : X, pY.IsHomLift (𝟙 (pX.obj x)) (α.hom.app x))
    (h : IsSmoothOnPredeformationCategories B S hS pX pY F hF) :
    IsSmoothOnPredeformationCategories B S hS pX pY G hG := by
  let Q : BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
  dsimp [IsSmoothOnPredeformationCategories] at h ⊢
  intro Λ k _ _ _ iΛ x₀ hx₀ hLFT hQC hOpen
  have hF' : F ⋙ pY ⋙ Q = pX ⋙ Q := comp_over_eq hF Q
  have hG' : G ⋙ pY ⋙ Q = pX ⋙ Q := comp_over_eq hG Q
  have hαQ : ∀ x : X, (pY ⋙ Q).IsHomLift (𝟙 ((pX ⋙ Q).obj x)) (α.hom.app x) := fun x => by
    have H := Functor.isHomLift_comp_functor (p := pY) Q (𝟙 (pX.obj x)) (α.hom.app x) (hα x)
    rw [Q.map_id] at H
    exact H
  refine (isSmooth_explicitMap_iff iΛ (pX ⋙ Q) x₀ hx₀ (pY ⋙ Q) G hG'
    (mapPredeformationCategory iΛ (pX ⋙ Q) (pY ⋙ Q) G hG' x₀ hx₀)).mp ?_
  exact isSmooth_explicitMap_of_natIso iΛ (pX ⋙ Q) x₀ hx₀ (pY ⋙ Q) F hF' G hG' α hαQ
    ((isSmooth_explicitMap_iff iΛ (pX ⋙ Q) x₀ hx₀ (pY ⋙ Q) F hF'
      (mapPredeformationCategory iΛ (pX ⋙ Q) (pY ⋙ Q) F hF' x₀ hx₀)).mpr
      (h iΛ x₀ hx₀ hLFT hQC hOpen))

/-- **Exchanging the two factors of a 2-fibre product is smooth on predeformation categories.**
`CategoryTheory.TwoFibreProductOver.swap` is full, faithful and an involution on objects on the
nose, and it is strictly over the site, so the previous result applies to it. -/
public theorem isSmoothOnPredeformationCategories_twoFibreProductSwap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Type vX} [Category.{wX} X] {Y : Type vY} [Category.{wY} Y]
    {Z : Type vZ} [Category.{wZ} Z]
    (pX : X ⥤ BigFppfOver B S hS) (pZ : Z ⥤ BigFppfOver B S hS)
    (pY : Y ⥤ BigFppfOver B S hS) (f : X ⥤ Y) (g : Z ⥤ Y) :
    IsSmoothOnPredeformationCategories B S hS
      (TwoFibreProductOver.structureFunctor pZ pX pY g f)
      (TwoFibreProductOver.structureFunctor pX pZ pY f g)
      (TwoFibreProductOver.swap pZ pX pY g f)
      (TwoFibreProductOver.swap_comp_structureFunctor pZ pX pY g f) :=
  isSmoothOnPredeformationCategories_of_full_of_surjective_obj B S hS
    (TwoFibreProductOver.structureFunctor pZ pX pY g f)
    (TwoFibreProductOver.structureFunctor pX pZ pY f g)
    (TwoFibreProductOver.swap pZ pX pY g f)
    (TwoFibreProductOver.swap_comp_structureFunctor pZ pX pY g f)
    (fun P => ⟨(TwoFibreProductOver.swap pX pZ pY f g).obj P, rfl⟩)

/-- **Stacks 07XV at the other ordering of the cospan.** The library's form of Stacks 07XV,
`Deformation.Artin.isSmoothOnPredeformationCategories_twoFibreProductSnd`, concludes the
smoothness condition for the projection of `𝒳 ×_𝒴 𝒵` to its second factor. This is the same
assertion for the presentation `𝒵 ×_𝒴 𝒳` of the 2-fibre product, whose projection to `𝒵` is the
*first* one — the form in which `AlgebraicGeometry.Stack.HasRelativeProperty` (**Stacks 03YK**)
presents a base change along a scheme-valued point of the target.

It carries no tag: it is Stacks 07XV composed, by Stacks 07XU, with the exchange of
the two factors, so the tag is already registered on the declaration carrying the content. -/
public theorem isSmoothOnPredeformationCategories_twoFibreProductFst
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsLocallyNoetherian S]
    {X : Type vX} [Category.{wX} X] {Y : Type vY} [Category.{wY} Y]
    {Z : Type vZ} [Category.{wZ} Z]
    (pX : X ⥤ BigFppfOver B S hS) (pY : Y ⥤ BigFppfOver B S hS)
    (pZ : Z ⥤ BigFppfOver B S hS) (f : X ⥤ Y) (g : Z ⥤ Y)
    (hpX : pX.IsFiberedInGroupoids) (hpY : pY.IsFiberedInGroupoids)
    (hpZ : pZ.IsFiberedInGroupoids)
    (hf : f ⋙ pY = pX) (hg : g ⋙ pY = pZ)
    (h : IsSmoothOnPredeformationCategories B S hS pX pY f hf) :
    IsSmoothOnPredeformationCategories B S hS
      (TwoFibreProductOver.structureFunctor pZ pX pY g f) pZ
      (TwoFibreProductOver.fst pZ pX pY g f)
      (TwoFibreProductOver.fst_comp_eq) :=
  isSmoothOnPredeformationCategories_comp B S hS
    (TwoFibreProductOver.structureFunctor pZ pX pY g f)
    (TwoFibreProductOver.structureFunctor pX pZ pY f g) pZ
    (TwoFibreProductOver.swap pZ pX pY g f) (TwoFibreProductOver.snd pX pZ pY f g)
    (TwoFibreProductOver.swap_comp_structureFunctor pZ pX pY g f)
    TwoFibreProductOver.snd_comp_eq
    (isSmoothOnPredeformationCategories_twoFibreProductSwap B S hS pX pZ pY f g)
    (isSmoothOnPredeformationCategories_twoFibreProductSnd B S hS pX pY pZ f g
      hpX hpY hpZ hf hg h)

end Comparison

end

end Deformation.Artin
