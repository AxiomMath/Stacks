module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusTwistStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointStalkMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaDimensionOne

/-!
# Stalks of inverse images and the geometric Frobenius

For `g : X' ⟶ X` the identification `(g⁻¹ F)_s ≅ F_{g(s)}` of the stalk of an inverse image at a
geometric point `s` is natural in morphisms of geometric points.  At a rational point `x'` of `X'`
over a field `k`, with image `x = g(x')`, it gives `(g⁻¹ F)_{x̄'} ≅ F_{x̄}` compatibly with the
Galois actions, hence with the geometric Frobenius `π_x` of [Stacks, Tag 03SW].  This is the stalk
side of Step 1 of the proof of [Stacks, Tag 03UG]: `T'(U, j⁻¹K) + T'(Z, i⁻¹K) = T'(X, K)`.

All names are in the namespace `Stacks.EtaleCohomology`.

## Main definitions

* `rationalPointStalkPullbackIso` — `(g⁻¹ F)_{x̄'} ≅ F_{x̄}`.

## Main results

* `smallEtalePointHom_sheafFiber_comp_etaleModuleStalkPullbackIso_inv` — `(g⁻¹ F)_s ≅ F_{g(s)}` is
  natural in morphisms of geometric points.
* `galoisStalkAction_comp_rationalPointStalkPullbackIso_hom` — `(g⁻¹ F)_{x̄'} ≅ F_{x̄}` is Galois
  equivariant.
* `geometricFrobeniusStalkFunctor_comp_rationalPointStalkPullbackIso_hom` —
  `(g⁻¹ F)_{x̄'} ≅ F_{x̄}` commutes with the geometric Frobenius.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

section PointHom

variable {X X' : Scheme.{u}} (g : X' ⟶ X) {s t : GeometricPoint X'} (a : GeometricPoint.Hom s t)

/-- The morphism of image geometric points induced by a morphism of geometric points. -/
def _root_.AlgebraicGeometry.GeometricPoint.Hom.map :
    GeometricPoint.Hom (s.map g) (t.map g) where
  hom := a.hom
  comm := by
    change a.hom ≫ t.hom ≫ g = s.hom ≫ g
    rw [← Category.assoc, a.comm]

/-- The lift of a geometric point to a base change of an étale neighbourhood commutes with
precomposition by a morphism of geometric points. -/
lemma pointSmallEtaleComapFiberIso_hom_app_smallEtalePointHom (W : X.Etale)
    (v : (Scheme.pointSmallEtale (t.hom ≫ g)).fiber.obj W) :
    (pointSmallEtaleComapFiberIso g s.hom).hom.app W
        ((smallEtalePointHom X (a.map g)).hom.app W v) =
      (smallEtalePointHom X' a).hom.app ((smallEtaleBaseChange g).obj W)
        ((pointSmallEtaleComapFiberIso g t.hom).hom.app W v) := by
  apply CategoryTheory.Over.OverMorphism.ext
  refine pullback.hom_ext ?_ ?_
  · refine (pointSmallEtaleComapFiberIso_hom_app_left_fst g s.hom W _).trans ?_
    exact congrArg (a.hom ≫ ·)
      (pointSmallEtaleComapFiberIso_hom_app_left_fst g t.hom W v).symm
  · refine (CategoryTheory.Over.w ((pointSmallEtaleComapFiberIso g s.hom).hom.app W
      ((smallEtalePointHom X (a.map g)).hom.app W v))).trans ?_
    exact (CategoryTheory.Over.w ((smallEtalePointHom X' a).hom.app ((smallEtaleBaseChange g).obj W)
        ((pointSmallEtaleComapFiberIso g t.hom).hom.app W v))).symm

variable (Λ : Type r) [Ring Λ]

private lemma germChase {C : Type*} [Category* C] {A B B' D E E' : C} {v₀ : A ⟶ B} {act : B ⟶ B'}
    {v₁ : A ⟶ B'} {inv_s : B' ⟶ D} {u : A ⟶ E} {w₁ : E ⟶ D} {inv_t : B ⟶ E'} {w₀ : E ⟶ E'}
    {act' : E' ⟶ D} (h₁ : v₀ ≫ act = v₁) (h₂ : v₁ ≫ inv_s = u ≫ w₁)
    (h₃ : v₀ ≫ inv_t = u ≫ w₀) (h₄ : w₀ ≫ act' = w₁) :
    v₀ ≫ act ≫ inv_s = v₀ ≫ inv_t ≫ act' := by
  rw [reassoc_of% h₁, h₂, reassoc_of% h₃, h₄]

/-- A morphism of points acts on germs by evaluating the fibre transformation. -/
private lemma toPresheafFiber_comp_sheafFiber_app {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {Φ₁ Φ₂ : Point.{u} J} (f : Φ₁ ⟶ Φ₂) (W : C) (v : Φ₂.fiber.obj W)
    (F : Sheaf J (ModuleCat.{max (u + 1) r} Λ)) :
    Φ₂.toPresheafFiber W v F.obj ≫ f.sheafFiber.app F =
      Φ₁.toPresheafFiber W (f.hom.app W v) F.obj := by
  change _ ≫ Point.presheafFiberDesc (A := ModuleCat.{max (u + 1) r} Λ) _ _ _ = _
  exact Point.toPresheafFiber_presheafFiberDesc _ _ _ _ _

/-- **The stalk of an inverse image is natural in the geometric point.**  For `g : X' ⟶ X` and a
morphism `a : s ⟶ t` of geometric points of `X'`, the identification `(g⁻¹ F)_s ≅ F_{g(s)}`
intertwines the actions of `a` on the stalks of `g⁻¹ F` and of `F`. -/
theorem smallEtalePointHom_sheafFiber_comp_etaleModuleStalkPullbackIso_inv
    (F : EtaleModules.{u, r} Λ X) :
    (smallEtalePointHom X (a.map g)).sheafFiber.app F ≫
        (etaleModuleStalkPullbackIso Λ g s.hom).inv.app F =
      (etaleModuleStalkPullbackIso Λ g t.hom).inv.app F ≫
        (smallEtalePointHom X' a).sheafFiber.app ((etaleModuleInverseImage.{u, r} Λ g).obj F) := by
  refine Point.presheafFiber_hom_ext _ (fun W v => ?_)
  have h₁ := toPresheafFiber_comp_sheafFiber_app Λ (smallEtalePointHom X (a.map g)) W v F
  have h₂ := toPresheafFiber_comp_etaleModuleStalkPullbackIso_inv Λ g s.hom F W
    ((smallEtalePointHom X (a.map g)).hom.app W v)
  have h₃ := toPresheafFiber_comp_etaleModuleStalkPullbackIso_inv Λ g t.hom F W v
  have h₄ := toPresheafFiber_comp_sheafFiber_app Λ (smallEtalePointHom X' a)
    ((smallEtaleBaseChange g).obj W) ((pointSmallEtaleComapFiberIso g t.hom).hom.app W v)
    ((etaleModuleInverseImage.{u, r} Λ g).obj F)
  rw [pointSmallEtaleComapFiberIso_hom_app_smallEtalePointHom] at h₂
  exact germChase h₁ h₂ h₃ h₄

end PointHom

section RationalPoint

open Stacks.Frobenius

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] {X X' : Scheme.{u}} (g : X' ⟶ X)
  (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K] (x' : Spec (.of k) ⟶ X')
  (x : Spec (.of k) ⟶ X) (hx : x' ≫ g = x)

include hx in
/-- The identification of the geometric point over `x` with the image under `g` of the geometric
point over `x'`, when `x' ≫ g = x`. -/
def rationalGeometricPointMapHom :
    GeometricPoint.Hom (rationalGeometricPoint K x) ((rationalGeometricPoint K x').map g) where
  hom := 𝟙 _
  comm := by
    change 𝟙 _ ≫ (_ ≫ x') ≫ g = _ ≫ x
    rw [Category.id_comp, Category.assoc, hx]

/-- An isomorphism of points of a site induces an isomorphism of their fibre functors on
sheaves. -/
def _root_.CategoryTheory.GrothendieckTopology.Point.sheafFiberIsoOfIso {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {A : Type*} [Category* A] [HasColimitsOfSize.{u, u} A]
    {Φ₁ Φ₂ : Point.{u} J} (f : Φ₁ ≅ Φ₂) :
    Φ₂.sheafFiber (A := A) ≅ Φ₁.sheafFiber where
  hom := f.hom.sheafFiber
  inv := f.inv.sheafFiber
  hom_inv_id := by rw [← Point.Hom.sheafFiber_comp, f.inv_hom_id, Point.Hom.sheafFiber_id]
  inv_hom_id := by rw [← Point.Hom.sheafFiber_comp, f.hom_inv_id, Point.Hom.sheafFiber_id]

include hx in
/-- **The stalk of an inverse image at a rational point.**  For `g : X' ⟶ X` and rational points
`x'` of `X'` and `x = g(x')` of `X`, the stalk of `g⁻¹ F` at the geometric point over `x'` is the
stalk of `F` at the geometric point over `x`, naturally in `F`. -/
def rationalPointStalkPullbackIso :
    etaleModuleInverseImage.{u, r} Λ g ⋙ rationalPointStalkFunctor.{u, r} Λ K x' ≅
      rationalPointStalkFunctor.{u, r} Λ K x :=
  etaleModuleStalkPullbackIso Λ g (rationalGeometricPoint K x').hom ≪≫
    Point.sheafFiberIsoOfIso (A := ModuleCat.{max (u + 1) r} Λ)
      (@asIso _ _ _ _ (smallEtalePointHom X (rationalGeometricPointMapHom g K x' x hx))
        (smallEtalePointHom_isIso _ _))

private lemma stalkIsoChase {C : Type*} [Category* C] {A B D : C} {m : B ⟶ B} {i : A ⟶ B}
    {i' : B ⟶ A} {P : A ⟶ A} {a₀ : B ⟶ D} {gx : D ⟶ D} (h₄ : m ≫ i' = i' ≫ P)
    (hi : i ≫ i' = 𝟙 A) (hi' : i' ≫ i = 𝟙 B) (h₃ : a₀ ≫ gx = m ≫ a₀) :
    P ≫ i ≫ a₀ = i ≫ a₀ ≫ gx := by
  have : P ≫ i = i ≫ m := by
    rw [← Category.id_comp (P ≫ i), ← hi, Category.assoc, ← reassoc_of% h₄, hi',
      Category.comp_id]
  rw [h₃, reassoc_of% this]

include hx in
/-- **The stalk of an inverse image at a rational point is Galois equivariant.** -/
theorem galoisStalkAction_comp_rationalPointStalkPullbackIso_hom (σ : K ≃ₐ[k] K)
    (F : EtaleModules.{u, r} Λ X) :
    (Point.Hom.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)
        (smallEtalePointHom X' (galoisPointHom K σ x'))).app
        ((etaleModuleInverseImage.{u, r} Λ g).obj F) ≫
      (rationalPointStalkPullbackIso Λ g K x' x hx).hom.app F =
    (rationalPointStalkPullbackIso Λ g K x' x hx).hom.app F ≫
      (Point.Hom.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)
        (smallEtalePointHom X (galoisPointHom K σ x))).app F := by
  let a := galoisPointHom K σ x'
  let a₀ := rationalGeometricPointMapHom g K x' x hx
  let c : GeometricPoint.Hom (rationalGeometricPoint K x) ((rationalGeometricPoint K x').map g) :=
    ⟨Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom), by
      show _ ≫ (_ ≫ x') ≫ g = _ ≫ x
      rw [Category.assoc, hx, ← Category.assoc, ← Spec.map_comp]
      congr 2
      ext y
      exact σ.commutes y⟩
  have h₁ : smallEtalePointHom X c = smallEtalePointHom X (galoisPointHom K σ x) ≫
      smallEtalePointHom X a₀ :=
    smallEtalePointHom_comp _ _ _ (Category.comp_id _).symm
  have h₂ : smallEtalePointHom X c = smallEtalePointHom X a₀ ≫
      smallEtalePointHom X (a.map g) :=
    smallEtalePointHom_comp _ _ _ (Category.id_comp _).symm
  have h₃ := congrArg (fun f => (Point.Hom.sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)
    (J := X.smallEtaleTopology) f).app F) (h₁.symm.trans h₂)
  simp only [Point.Hom.sheafFiber_comp, NatTrans.comp_app] at h₃
  have h₄ := smallEtalePointHom_sheafFiber_comp_etaleModuleStalkPullbackIso_inv g a Λ F
  exact stalkIsoChase h₄ (Iso.hom_inv_id_app _ _) (Iso.inv_hom_id_app _ _) h₃

include hx in
/-- **The stalk of an inverse image at a rational point intertwines the geometric Frobenius.** -/
theorem geometricFrobeniusStalkFunctor_comp_rationalPointStalkPullbackIso_hom [Fintype k]
    (p q : ℕ) [Fact p.Prime] [CharP K p] (hcard : Fintype.card k = p ^ q)
    (F : EtaleModules.{u, r} Λ X) :
    (geometricFrobeniusStalkFunctor (ModuleCat.{max (u + 1) r} Λ) K p q hcard x').app
        ((etaleModuleInverseImage.{u, r} Λ g).obj F) ≫
      (rationalPointStalkPullbackIso Λ g K x' x hx).hom.app F =
    (rationalPointStalkPullbackIso Λ g K x' x hx).hom.app F ≫
      (geometricFrobeniusStalkFunctor (ModuleCat.{max (u + 1) r} Λ) K p q hcard x).app F :=
  galoisStalkAction_comp_rationalPointStalkPullbackIso_hom Λ g K x' x hx _ F

end RationalPoint

end Stacks.EtaleCohomology

end
