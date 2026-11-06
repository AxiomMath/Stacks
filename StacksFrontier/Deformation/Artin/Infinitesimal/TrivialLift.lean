module

public import StacksFrontier.Deformation.Artin.Infinitesimal.Functoriality
public import StacksFrontier.Deformation.Artin.Infinitesimal.TwoFibreBoundary

/-!
# Trivial lifts along a trivial square-zero extension

Let `p : 𝒳 ⥤ (Sch/S)_fppf` be fibred in groupoids and let `x` lie over `Spec A`. A lift of `x`
along `Spec A ⟶ Spec A[M]` is *trivial* when it admits a retraction onto `x` lying over the
retraction `Spec A[M] ⟶ Spec A`. The trivial deformation of `x` is a trivial lift, any two trivial
lifts are isomorphic, and a lift admitting a morphism over the identity of `Spec A[M]` to a trivial
lift is trivial. Consequently an element of `T_x(M)` (Stacks 07Y9) whose lift maps to the trivial
deformation over the identity of `Spec A[M]` is zero.

## Main definitions

* `Deformation.Artin.IsTrivialLift`: a lift with a retraction onto `x` over the retraction.

## Main results

* `Deformation.Artin.isTrivialLift_trivialDeformation`: the trivial deformation is a trivial lift.
* `Deformation.Artin.isIsomorphic_of_isTrivialLift`: any two trivial lifts are isomorphic.
* `Deformation.Artin.isTrivialLift_of_hom`: a lift with a morphism over the identity to a trivial
  lift is trivial.
* `Deformation.Artin.eq_zero_of_hom_trivialDeformation`: an element of `T_x(M)` whose lift maps to
  the trivial deformation over the identity is zero.

## References

* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v w

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

namespace Deformation.Artin

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))

variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)

/-- The base of a lift of `x` along `Spec A ⟶ Spec A[M]` is `Spec A[M]`. -/
theorem squareZeroLift_right_eq {M : SiteModule A B}
    (y : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M))) :
    p.obj y.1.right = squareZeroOver A B S hS toS M :=
  congrArg Under.right y.2

/-- The arrow of a lift of `x` along `Spec A ⟶ Spec A[M]` lies over the square-zero immersion. -/
theorem map_squareZeroLift_hom {M : SiteModule A B}
    (y : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M))) :
    p.map y.1.hom = eqToHom hx ≫ squareZeroArrow A B S hS toS hA M ≫
      eqToHom (squareZeroLift_right_eq A B S hS toS hA p x hx y).symm := by
  have h := Under.w (eqToHom y.2)
  rw [Under.eqToHom_right] at h
  change p.map y.1.hom ≫ eqToHom (squareZeroLift_right_eq A B S hS toS hA p x hx y) =
    eqToHom hx ≫ squareZeroArrow A B S hS toS hA M at h
  rw [← Category.assoc]
  exact ((comp_eqToHom_iff _ _ _).mp h)

/-- A lift of `x` along `Spec A ⟶ Spec A[M]` is *trivial* when it admits a retraction onto `x`
lying over the retraction `Spec A[M] ⟶ Spec A`. -/
def IsTrivialLift {M : SiteModule A B}
    (y : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M))) :
    Prop :=
  ∃ r : y.1.right ⟶ x, y.1.hom ≫ r = 𝟙 x ∧
    p.map r = eqToHom (squareZeroLift_right_eq A B S hS toS hA p x hx y) ≫
      squareZeroRetraction A B S hS toS hA M ≫ eqToHom hx.symm

variable (hp : p.IsFiberedInGroupoids)

include hp in
/-- A lift with a map onto `x` lying over the retraction is trivial. -/
theorem isTrivialLift_of_map {M : SiteModule A B}
    (y : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M)))
    (χ : y.1.right ⟶ x)
    (hχ : p.map χ = eqToHom (squareZeroLift_right_eq A B S hS toS hA p x hx y) ≫
      squareZeroRetraction A B S hS toS hA M ≫ eqToHom hx.symm) :
    IsTrivialLift A B S hS toS hA p x hx y := by
  have hτ : p.map (y.1.hom ≫ χ) = 𝟙 (p.obj x) := by
    rw [p.map_comp, hχ, map_squareZeroLift_hom A B S hS toS hA p x hx y]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (squareZeroArrow A B S hS toS hA M),
      squareZeroArrow_comp_squareZeroRetraction, Category.id_comp, eqToHom_trans, eqToHom_refl]
  have hlift : p.IsHomLift (𝟙 (p.obj x)) (y.1.hom ≫ χ) := by
    rw [← hτ]
    exact IsHomLift.map (p := p) _
  have := isIso_of_isHomLift_id_fibered p hp (y.1.hom ≫ χ) hlift
  refine ⟨χ ≫ inv (y.1.hom ≫ χ), ?_, ?_⟩
  · rw [← Category.assoc, IsIso.hom_inv_id]
  · have hinv : inv (p.map (y.1.hom ≫ χ)) = 𝟙 _ :=
      IsIso.inv_eq_of_hom_inv_id (by rw [hτ, Category.comp_id])
    rw [p.map_comp, Functor.map_inv, hinv, Category.comp_id, hχ]


include hp in
/-- The trivial deformation is a trivial lift. -/
theorem isTrivialLift_trivialDeformation (M : SiteModule A B) :
    IsTrivialLift A B S hS toS hA p x hx (trivialDeformation A B S hS toS hA p x hx hp M) := by
  have := trivialRetract_isHomLift A B S hS toS hA p x hx hp M
  exact ⟨trivialRetract A B S hS toS hA p x hx hp M, trivialRetract_fac A B S hS toS hA p x hx hp M,
    IsHomLift.fac' p _ _⟩

include hp in
/-- **Any two trivial lifts are isomorphic.** -/
theorem isIsomorphic_of_isTrivialLift {M : SiteModule A B}
    (y y' : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M)))
    (hy : IsTrivialLift A B S hS toS hA p x hx y) (hy' : IsTrivialLift A B S hS toS hA p x hx y') :
    IsIsomorphic y y' := by
  obtain ⟨r, hr, hpr⟩ := hy
  obtain ⟨r', hr', hpr'⟩ := hy'
  have he : p.obj y.1.right = p.obj y'.1.right :=
    (squareZeroLift_right_eq A B S hS toS hA p x hx y).trans
      (squareZeroLift_right_eq A B S hS toS hA p x hx y').symm
  obtain ⟨e, ⟨hpe, hre⟩, -⟩ := hp.unique_lift r' r (eqToHom he) (by
    rw [hpr, hpr', ← Category.assoc, eqToHom_trans])
  obtain ⟨χ, -, huniq⟩ := hp.unique_lift r' (𝟙 x) (p.map y'.1.hom) (by
    rw [← p.map_comp, hr'])
  have h1 : y.1.hom ≫ e = y'.1.hom :=
    (huniq (y.1.hom ≫ e) ⟨by
      rw [p.map_comp, hpe, map_squareZeroLift_hom A B S hS toS hA p x hx y,
        map_squareZeroLift_hom A B S hS toS hA p x hx y']
      simp only [Category.assoc, eqToHom_trans], by rw [Category.assoc, hre, hr]⟩).trans
      (huniq y'.1.hom ⟨rfl, hr'⟩).symm
  let φ : y.1 ⟶ y'.1 := Under.homMk e h1
  have hφ : (Under.post p).IsHomLift
      (𝟙 (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M))) φ := by
    refine IsHomLift.of_fac' _ _ _ y.2 y'.2 ?_
    apply Under.UnderMorphism.ext
    simp only [Under.post_map, Under.homMk_right, Under.comp_right, Under.eqToHom_right,
      Category.id_comp, φ]
    rw [hpe, eqToHom_trans]
  have := isIso_of_isHomLift_id_fibered _ (underPost_isFiberedInGroupoids p hp x) φ hφ
  exact ⟨Functor.Fiber.isoMk (asIso φ) hφ⟩


include hp in
/-- A lift admitting a morphism over the identity of `Spec A[M]` to a trivial lift is trivial. -/
theorem isTrivialLift_of_hom {M : SiteModule A B}
    (y y₀ : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M)))
    (hy₀ : IsTrivialLift A B S hS toS hA p x hx y₀) (Φ : y.1.right ⟶ y₀.1.right)
    (hΦ : p.map Φ = eqToHom ((squareZeroLift_right_eq A B S hS toS hA p x hx y).trans
      (squareZeroLift_right_eq A B S hS toS hA p x hx y₀).symm)) :
    IsTrivialLift A B S hS toS hA p x hx y := by
  obtain ⟨r₀, -, hr₀⟩ := hy₀
  exact isTrivialLift_of_map A B S hS toS hA p x hx hp y (Φ ≫ r₀)
    (by rw [p.map_comp, hΦ, hr₀, ← Category.assoc, eqToHom_trans])

include hp in
/-- **An element of `T_x(M)` whose lift admits a morphism over the identity of `Spec A[M]` to the
trivial deformation is zero.** -/
theorem eq_zero_of_hom_trivialDeformation (T : TangentFunctorData A B S hS toS hA p x hx)
    {M : SiteModule A B} (a : T.functor.obj M)
    (y : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M)))
    (hy : T.liftEquiv M a = Quotient.mk _ y)
    (Φ : y.1.right ⟶ (trivialDeformation A B S hS toS hA p x hx hp M).1.right)
    (hΦ : p.map Φ = eqToHom ((squareZeroLift_right_eq A B S hS toS hA p x hx y).trans
      (squareZeroLift_right_eq A B S hS toS hA p x hx
        (trivialDeformation A B S hS toS hA p x hx hp M)).symm)) :
    a = 0 := by
  apply (T.liftEquiv M).injective
  rw [hy, liftEquiv_zero A B S hS toS hA p x hx hp T M]
  exact Quotient.sound (isIsomorphic_of_isTrivialLift A B S hS toS hA p x hx hp _ _
    (isTrivialLift_of_hom A B S hS toS hA p x hx hp y _
      (isTrivialLift_trivialDeformation A B S hS toS hA p x hx hp M) Φ hΦ)
    (isTrivialLift_trivialDeformation A B S hS toS hA p x hx hp M))

end Deformation.Artin

end
