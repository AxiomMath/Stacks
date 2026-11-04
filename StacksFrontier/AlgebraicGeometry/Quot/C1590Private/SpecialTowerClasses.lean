module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SpecialTowerInterfaces

/-!
# Effectivity of special towers: from objects to lift classes

`AlgebraicGeometry.C1590Private.IsSpecialSquareZeroTowerEffectiveOnClasses` asks for lift classes
over the limit of a special tower restricting to given compatible lift classes over the levels.
It follows from the corresponding statement for objects
(`AlgebraicGeometry.C1590Private.SpecialTowerObjectsEffective`): a tower `y₀ → y₁ → ⋯` of objects
over the levels has a limit object `ŷ` over `Spec (lim Rₙ)` with compatible morphisms `yₙ ⟶ ŷ`.
Representatives of compatible lift classes form such a tower, the category being fibred in
groupoids.

## Main definitions

* `AlgebraicGeometry.C1590Private.SpecialTowerObjectsEffective`.

## Main results

* `AlgebraicGeometry.C1590Private.isSpecialSquareZeroTowerEffectiveOnClasses_of_objects`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin
open Deformation.Artin.SquareZeroTower

universe u v w

namespace AlgebraicGeometry.C1590Private

section Classes

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)

/-- **Effectivity of special towers of objects.** For every special tower `⋯ → R₁ → R₀` of
square-zero thickenings in the site and every tower `y₀ → y₁ → ⋯` of objects over the levels
`Spec Rₙ`, the transition morphisms lying over `Spec Rₙ ⟶ Spec Rₙ₊₁`, there are an object `ŷ`
over `Spec (lim Rₙ)` and compatible morphisms `yₙ ⟶ ŷ` over `Spec Rₙ ⟶ Spec (lim Rₙ)`. -/
def SpecialTowerObjectsEffective : Prop :=
  ∀ (R : ℕ → Type u) [∀ n, CommRing (R n)] (f : ∀ n, R (n + 1) →+* R n),
    (∀ n, Function.Surjective (f n)) → (∀ n, RingHom.ker (toBase f n) ^ 2 = ⊥) →
    IsSpecialTower f →
    ∀ (toS : Spec (.of (R 0)) ⟶ S) (hA : B.Contains (Spec (.of (R 0))))
    (Λ : AugmentedSiteRing (R 0) B S hS toS hA) (β : ∀ n, Λ.ring →+* R n)
    (hβ : ∀ n, (f n).comp (β (n + 1)) = β n) (hβ0 : β 0 = Λ.aug)
    (hR : ∀ n, B.Contains (Spec (.of (R n)))) (y : ℕ → X)
    (_ : ∀ n, p.obj (y n) = (level f Λ β hβ hβ0 hR n).siteOver) (t : ∀ n, y n ⟶ y (n + 1)),
    (∀ n, p.IsHomLift (transition f Λ β hβ hβ0 hR n).toHom.right (t n)) →
    ∃ (ŷ : X) (_ : p.obj ŷ = (limitRing f Λ β hβ hβ0 hR).siteOver) (ψ : ∀ n, y n ⟶ ŷ),
      (∀ n, p.IsHomLift (limitProj f Λ β hβ hβ0 hR n).toHom.right (ψ n)) ∧
        ∀ n, t n ≫ ψ (n + 1) = ψ n

variable {B S hS p}

/-- The image of `Under.mk a` under `Under.post p` is `Under.mk g` when `p.obj z = T` and `p.map a`
followed by the induced `eqToHom` is `g`. -/
theorem underPost_obj_mk_eq {x z : X} {T : BigFppfOver B S hS} (g : p.obj x ⟶ T) (a : x ⟶ z)
    (hz : p.obj z = T) (h : p.map a ≫ eqToHom hz = g) :
    (Under.post p).obj (Under.mk a) = Under.mk g := by
  subst hz
  simp only [eqToHom_refl, Category.comp_id] at h
  subst h
  rfl

/-- For an equality `A = A'` of objects under `Y`, `A.hom` followed by the induced `eqToHom` of
right objects is `A'.hom`. -/
theorem under_hom_eq {C : Type*} [Category C] {Y : C} {A A' : Under Y} (h : A = A') :
    A.hom ≫ eqToHom (congrArg (fun z => z.right) h) = A'.hom := by
  subst h
  simp

/-- **Special towers are effective on lift classes once they are effective on objects.** -/
theorem isSpecialSquareZeroTowerEffectiveOnClasses_of_objects (hp : p.IsFiberedInGroupoids)
    (h : SpecialTowerObjectsEffective B S hS p) :
    IsSpecialSquareZeroTowerEffectiveOnClasses B S hS p hp := by
  intro R _ f hf hsq hsp toS hA Λ β hβ hβ0 hR _ x hx b hb
  have hrep : ∀ n, ∃ d : (Under.post p).Fiber
      (Under.mk (eqToHom hx ≫ (level f Λ β hβ hβ0 hR n).toAffine.arrow)),
      Quotient.mk _ d = b n := fun n => Quotient.exists_rep (b n)
  choose d hd using hrep
  have hy : ∀ n, p.obj (d n).1.right = (level f Λ β hβ hβ0 hR n).siteOver := fun n =>
    congrArg (fun z => z.right) (d n).2
  have hhom : ∀ n, p.map (d n).1.hom ≫ eqToHom (hy n) =
      eqToHom hx ≫ (level f Λ β hβ hβ0 hR n).toAffine.arrow := fun n => under_hom_eq (d n).2
  have htr : ∀ n, ∃ τ : (d n).1.right ⟶ (d (n + 1)).1.right,
      p.IsHomLift (transition f Λ β hβ hβ0 hR n).toHom.right τ ∧
        (d n).1.hom ≫ τ = (d (n + 1)).1.hom := by
    intro n
    obtain ⟨e, φ, hφ, hw, hmap⟩ := AugmentedSiteRing.representative_map p x hx hp
      (transition f Λ β hβ hβ0 hR n).toHom (d (n + 1))
    have hen : (Quotient.mk _ e : BasedSiteRing.classes p x hx (level f Λ β hβ hβ0 hR n)) =
        Quotient.mk _ (d n) := by
      rw [← hmap, hd, hd]
      exact hb n
    obtain ⟨ι⟩ := Quotient.exact hen
    have h1 : p.IsHomLift (𝟙 (level f Λ β hβ hβ0 hR n).siteOver) ι.inv.1.right :=
      underPost_isHomLift_right p (𝟙 _) ι.inv.1 ι.inv.2
    have := hφ.toIsHomLift
    have : p.IsHomLift (𝟙 (level f Λ β hβ hβ0 hR n).toAffine.under.right) ι.inv.1.right := h1
    refine ⟨ι.inv.1.right ≫ φ, ?_, ?_⟩
    · simpa using (inferInstance : p.IsHomLift (𝟙 _ ≫ (transition f Λ β hβ hβ0 hR n).toHom.right)
        (ι.inv.1.right ≫ φ))
    · rw [← Category.assoc, Under.w ι.inv.1, hw]
  choose τ hτ hτd using htr
  obtain ⟨ŷ, hŷ, ψ, hψ, hcomp⟩ :=
    h R f hf hsq hsp toS hA Λ β hβ hβ0 hR (fun n => (d n).1.right) hy τ hτ
  have hkey : ∀ n, (d n).1.hom ≫ ψ n = (d 0).1.hom ≫ ψ 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [← hτd n, Category.assoc, hcomp n, ih]
  have hψ0 := IsHomLift.fac' p (limitProj f Λ β hβ hβ0 hR 0).toHom.right (ψ 0)
  let ξ₀ : (Under.post p).Fiber
      (Under.mk (eqToHom hx ≫ (limitRing f Λ β hβ hβ0 hR).toAffine.arrow)) :=
    ⟨Under.mk ((d 0).1.hom ≫ ψ 0), underPost_obj_mk_eq _ _ hŷ (by
      rw [Functor.map_comp, hψ0]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
      rw [← Category.assoc, hhom 0, Category.assoc]
      congr 1
      exact Under.w (limitProj f Λ β hβ hβ0 hR 0).toHom)⟩
  refine ⟨Quotient.mk _ ξ₀, fun n => ?_⟩
  rw [← hd n]
  have := hψ n
  exact AugmentedSiteRing.map_eq_of_lift p x hx hp _ ξ₀ (d n) (ψ n)
    (hp.isStronglyCartesian_homLift _ _) (hkey n)

end Classes

end AlgebraicGeometry.C1590Private

end
