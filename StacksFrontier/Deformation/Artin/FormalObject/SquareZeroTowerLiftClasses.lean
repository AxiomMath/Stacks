module

public import StacksFrontier.Deformation.Artin.FormalObject.SquareZeroTowerLifts
public import StacksFrontier.Deformation.Artin.FormalObject.SquareZeroTowerSiteRings

/-!
# Lift classes over the ring of sequences with a common base

For a tower `⋯ → R₁ → R₀ = A` of square-zero thickenings in the site, under a fixed augmented
ring, and an object `x` over `Spec A` of a category fibred in groupoids satisfying (RS*), this
file proves the lift-class part of the proof of Stacks 0CYF: if the lift classes of `x` over
`A[∏ Mₙ]` are the products of those over the `A[Mₙ]` (assumption (5)(a)), then any lift class of
`x` over `R̃` can be corrected to one which restricts to a prescribed compatible system of lift
classes over the levels `Rₙ`, and its restriction along the difference map `R̃ → A[∏ Mₙ]` is
then the class pulled back from `A`.

## Main results

* `Deformation.Artin.SquareZeroTower.exists_classes_eq` — the corrected lift class.

## References

* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Deformation.Artin.SquareZeroTower

open BasedSiteRing

variable {R : ℕ → Type u} [∀ n, CommRing (R n)] (f : ∀ n, R (n + 1) →+* R n)
  (hf : ∀ n, Function.Surjective (f n)) (hsq : ∀ n, RingHom.ker (toBase f n) ^ 2 = ⊥)
  {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of (R 0)) ⟶ S} {hA : B.Contains (Spec (.of (R 0)))}
  (Λ : AugmentedSiteRing (R 0) B S hS toS hA) (β : ∀ n, Λ.ring →+* R n)
  (hβ : ∀ n, (f n).comp (β (n + 1)) = β n) (hβ0 : β 0 = Λ.aug)
  (hR : ∀ n, B.Contains (Spec (.of (R n))))

/-! ### The relations between the maps -/

/-- The map `A[∏ Mₙ] → A[Mₙ]` is the identity on the `A`-component. -/
theorem squareZeroProj_hom_fst (n : ℕ) (w : (productSquareZero f hf hsq Λ hR).ring) :
    ((squareZeroProj f hf hsq Λ hR n).hom w).1 = w.1 :=
  TrivSqZeroExt.fst_map _ w

/-- The map `A[∏ Mₙ] → A[Mₙ]` takes the module component to its `n`-th component. -/
theorem squareZeroProj_hom_snd (n : ℕ) (w : (productSquareZero f hf hsq Λ hR).ring) :
    ((squareZeroProj f hf hsq Λ hR n).hom w).2 = component f hf hsq w.2 n :=
  TrivSqZeroExt.snd_map _ w

/-- The kernel element of the `n`-th module component of the image of `w` in `A[Mₙ]` is the
`n`-th component of `w.2`. -/
private theorem kerVal_squareZeroProj_hom_snd (n : ℕ) (w : (productSquareZero f hf hsq Λ hR).ring) :
    kerVal _ _ _ ((squareZeroProj f hf hsq Λ hR n).hom w).2 = (component f hf hsq w.2 n : R n) := by
  rw [squareZeroProj_hom_snd]
  rfl

/-- The untwisting map `Rₙ ×_A Rₙ → Rₙ ×_A A[Mₙ]` followed by the first projection is the first
projection. -/
theorem fst_comp_levelUntwist (n : ℕ) :
    (fst _ _).comp (levelUntwist f hf hsq Λ β hβ hβ0 hR n) = fst _ _ :=
  RingMap.ext rfl

/-- Untwisting `Rₙ ×_A Rₙ → Rₙ ×_A A[Mₙ]` and then twisting back to `Rₙ` is the second
projection: `s + (t − s) = t`. -/
theorem levelTwist_comp_levelUntwist (n : ℕ) :
    (levelTwist f hf hsq Λ β hβ hβ0 hR n).comp (levelUntwist f hf hsq Λ β hβ hβ0 hR n) =
      snd _ _ := by
  refine RingMap.ext (RingHom.ext fun z => ?_)
  change z.1.1 + (z.1.2 - z.1.1) = z.1.2
  ring

/-- The first component of `R̃ ×_A A[∏ Mₙ] → Rₙ ×_A A[Mₙ]` is the projection `R̃ → Rₙ`. -/
theorem fst_comp_twistedProj (n : ℕ) :
    (fst _ _).comp (twistedProj f hf hsq Λ β hβ hβ0 hR n) =
      (projMap f Λ β hβ hβ0 hR n).comp (fst _ _) :=
  RingMap.ext rfl

/-- The second component of `R̃ ×_A A[∏ Mₙ] → Rₙ ×_A A[Mₙ]` is the map `A[∏ Mₙ] → A[Mₙ]`. -/
theorem snd_comp_twistedProj (n : ℕ) :
    (snd _ _).comp (twistedProj f hf hsq Λ β hβ hβ0 hR n) =
      (squareZeroProj f hf hsq Λ hR n).comp (snd _ _) :=
  RingMap.ext rfl

/-- Twisting commutes with the projections: projecting `R̃ ×_A A[∏ Mₙ]` to `Rₙ ×_A A[Mₙ]` and
twisting to `Rₙ` is twisting to `R̃` and projecting to `Rₙ`. -/
theorem levelTwist_comp_twistedProj (n : ℕ) :
    (levelTwist f hf hsq Λ β hβ hβ0 hR n).comp (twistedProj f hf hsq Λ β hβ hβ0 hR n) =
      (projMap f Λ β hβ hβ0 hR n).comp (sameBaseTwist f hf hsq Λ β hβ hβ0 hR) := by
  refine RingMap.ext (RingHom.ext fun z => ?_)
  change z.1.1.1 n + kerVal _ _ _ ((squareZeroProj f hf hsq Λ hR n).hom z.1.2).2 =
    z.1.1.1 n + (component f hf hsq z.1.2.2 n : R n)
  rw [kerVal_squareZeroProj_hom_snd]

/-- The diagonal `Rₙ → Rₙ ×_A Rₙ` followed by the first projection is the identity. -/
theorem fst_comp_diagMap (n : ℕ) :
    (fst _ _).comp (diagMap f Λ β hβ hβ0 hR n) = RingMap.id Λ _ :=
  RingMap.ext rfl

/-- The diagonal `Rₙ → Rₙ ×_A Rₙ` followed by the second projection is the identity. -/
theorem snd_comp_diagMap (n : ℕ) :
    (snd _ _).comp (diagMap f Λ β hβ hβ0 hR n) = RingMap.id Λ _ :=
  RingMap.ext rfl

/-- The first component of `R̃ → Rₙ ×_A Rₙ` is the projection to `Rₙ₊₁` followed by the transition
map `Rₙ₊₁ → Rₙ`. -/
theorem fst_comp_stepMap (n : ℕ) :
    (fst _ _).comp (stepMap f Λ β hβ hβ0 hR n) =
      (transition f Λ β hβ hβ0 hR n).comp (projMap f Λ β hβ hβ0 hR (n + 1)) :=
  RingMap.ext rfl

/-- The second component of `R̃ → Rₙ ×_A Rₙ` is the projection to `Rₙ`. -/
theorem snd_comp_stepMap (n : ℕ) :
    (snd _ _).comp (stepMap f Λ β hβ hβ0 hR n) = projMap f Λ β hβ hβ0 hR n :=
  RingMap.ext rfl

/-- The inclusion `A → A[∏ Mₙ]` followed by `A[∏ Mₙ] → A[Mₙ]` is the inclusion `A → A[Mₙ]`. -/
theorem squareZeroProj_comp_inlMap (n : ℕ) :
    (squareZeroProj f hf hsq Λ hR n).comp (inlMap f hf hsq Λ β hβ hβ0 hR) =
      inlLevelMap f hf hsq Λ β hβ hβ0 hR n := by
  refine RingMap.ext (RingHom.ext fun z => ?_)
  exact Prod.ext (squareZeroProj_hom_fst f hf hsq Λ hR n _)
    (kerVal_injective _ _ _ (kerVal_squareZeroProj_hom_snd f hf hsq Λ hR n _))

/-- The difference map `R̃ → A[∏ Mₙ]` followed by `A[∏ Mₙ] → A[Mₙ]` factors as `R̃ → Rₙ ×_A Rₙ`
followed by the difference map `Rₙ ×_A Rₙ → A[Mₙ]`. -/
theorem squareZeroProj_comp_differenceMap (n : ℕ) :
    (squareZeroProj f hf hsq Λ hR n).comp (differenceMap f hf hsq Λ β hβ hβ0 hR) =
      (levelDiffMap f hf hsq Λ β hβ hβ0 hR n).comp (stepMap f Λ β hβ hβ0 hR n) := by
  refine RingMap.ext (RingHom.ext fun r => ?_)
  exact Prod.ext ((squareZeroProj_hom_fst f hf hsq Λ hR n _).trans (r.2 (n + 1)).symm)
    (kerVal_injective _ _ _ (kerVal_squareZeroProj_hom_snd f hf hsq Λ hR n _))

/-- The difference map `Rₙ ×_A Rₙ → A[Mₙ]` on the diagonal is the augmentation `Rₙ → A` followed
by the inclusion `A → A[Mₙ]`. -/
theorem levelDiffMap_comp_diagMap (n : ℕ) :
    (levelDiffMap f hf hsq Λ β hβ hβ0 hR n).comp (diagMap f Λ β hβ hβ0 hR n) =
      (inlLevelMap f hf hsq Λ β hβ hβ0 hR n).comp (augMap f Λ β hβ hβ0 hR n) := by
  refine RingMap.ext (RingHom.ext fun s => Prod.ext rfl (kerVal_injective _ _ _ ?_))
  exact sub_self s

/-- The augmentation of the level `R₀ = A` is the identity. -/
theorem augMap_zero : augMap f Λ β hβ hβ0 hR 0 = RingMap.id Λ _ :=
  RingMap.ext rfl

/-- The augmentation `Rₙ₊₁ → A` is the transition map `Rₙ₊₁ → Rₙ` followed by the augmentation
`Rₙ → A`. -/
theorem augMap_succ (n : ℕ) :
    augMap f Λ β hβ hβ0 hR (n + 1) =
      (augMap f Λ β hβ hβ0 hR n).comp (transition f Λ β hβ hβ0 hR n) :=
  RingMap.ext rfl


/-! ### The assembly -/

/-- The morphism under the base associated to the identity ring map is the identity. -/
theorem toHom_id (D : BasedSiteRing (R 0) B S hS toS hA Λ) :
    (RingMap.id Λ D).toHom = 𝟙 D.toAffine.under :=
  AugmentedSiteRing.hom_ext (Spec.map_id _)

/-- A commutative square of ring maps gives a commutative square of the associated morphisms. -/
theorem toHom_comp_eq {D E F G : BasedSiteRing (R 0) B S hS toS hA Λ}
    {g : RingMap E F} {f₁ : RingMap D E} {g' : RingMap G F} {f' : RingMap D G}
    (h : g.comp f₁ = g'.comp f') : g.toHom ≫ f₁.toHom = g'.toHom ≫ f'.toHom := by
  rw [← RingMap.toHom_comp, ← RingMap.toHom_comp, h]

/-- A commutative triangle of ring maps gives a commutative triangle of the associated
morphisms. -/
theorem toHom_comp_eq' {D E F : BasedSiteRing (R 0) B S hS toS hA Λ}
    {g : RingMap E F} {f₁ : RingMap D E} {h₁ : RingMap D F}
    (h : g.comp f₁ = h₁) : g.toHom ≫ f₁.toHom = h₁.toHom := by
  rw [← RingMap.toHom_comp, h]

/-- If `g ∘ f₁` is the identity ring map, the associated morphisms compose to the identity. -/
theorem toHom_comp_eq_id {D E : BasedSiteRing (R 0) B S hS toS hA Λ}
    {g : RingMap E D} {f₁ : RingMap D E}
    (h : g.comp f₁ = RingMap.id Λ D) : g.toHom ≫ f₁.toHom = 𝟙 _ := by
  rw [← RingMap.toHom_comp, h, toHom_id]

variable {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {x : X}
  {hx : p.obj x = algebraOver (R 0) B S hS toS hA} {hp : p.IsFiberedInGroupoids}

/-- Under (RS*), the lift classes of `x` over `D ×_A A[M]` are the pairs of lift classes over `D`
and over `A[M]`. -/
theorem pair_bijective_squareZero (hRS : SatisfiesRSStar B S hS p hp)
    (D : BasedSiteRing (R 0) B S hS toS hA Λ) (M : SiteModule (R 0) B) :
    Function.Bijective (fun z : classes p x hx (prod D (squareZero Λ M)) =>
      (map p x hx hp (fst D (squareZero Λ M)) z, map p x hx hp (snd D (squareZero Λ M)) z)) :=
  pair_bijective p x hx hp hRS D (squareZero Λ M) (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩)
    (squareZeroProjection_ker_sq (R 0) M.obj)

include hf hsq in
/-- Under (RS*), the lift classes of `x` over `Rₙ ×_A Rₙ` are the pairs of lift classes over
`Rₙ`. -/
theorem pair_bijective_level (hRS : SatisfiesRSStar B S hS p hp) (n : ℕ) :
    Function.Bijective (fun z : classes p x hx (levelPair f Λ β hβ hβ0 hR n) =>
      (map p x hx hp (fst (level f Λ β hβ hβ0 hR n) (level f Λ β hβ hβ0 hR n)) z,
        map p x hx hp (snd (level f Λ β hβ hβ0 hR n) (level f Λ β hβ hβ0 hR n)) z)) :=
  pair_bijective p x hx hp hRS (level f Λ β hβ hβ0 hR n) (level f Λ β hβ hβ0 hR n)
    (toBase_surjective f hf n) (hsq n)

/-- A system of lift classes `bₙ` over the levels, compatible under the transition maps, restricts
along each augmentation `Rₙ → A` to `b₀`. -/
theorem map_augMap_eq (b : ∀ n, classes p x hx (level f Λ β hβ hβ0 hR n))
    (hb : ∀ n, BasedSiteRing.map p x hx hp (transition f Λ β hβ hβ0 hR n) (b (n + 1)) = b n) :
    ∀ n, BasedSiteRing.map p x hx hp (augMap f Λ β hβ hβ0 hR n) (b n) = b 0
  | 0 => by rw [augMap_zero, map_id]
  | n + 1 => by
    rw [augMap_succ, map_comp, hb, map_augMap_eq b hb n]

/-- **The lift-class step of the proof of Stacks 0CYF.** Assume (RS*) and that the lift classes of
`x` over `A[∏ Mₙ]` are, through the projections, the products of the lift classes over the
`A[Mₙ]`. Given a lift class over `R̃` and a system of lift classes `bₙ` over the levels `Rₙ`,
compatible under the transition maps, some lift class over `R̃` restricts to every `bₙ`, and
its restriction along the difference map `R̃ → A[∏ Mₙ]` is the class pulled back from `b₀`. -/
public theorem exists_classes_eq (hRS : SatisfiesRSStar B S hS p hp)
    (hQ : Function.Bijective fun d : classes p x hx (productSquareZero f hf hsq Λ hR) =>
      fun n => BasedSiteRing.map p x hx hp (squareZeroProj f hf hsq Λ hR n) d)
    (ξ₀ : classes p x hx (sameBaseRing f Λ β hβ hβ0 hR))
    (b : ∀ n, classes p x hx (level f Λ β hβ hβ0 hR n))
    (hb : ∀ n, BasedSiteRing.map p x hx hp (transition f Λ β hβ hβ0 hR n) (b (n + 1)) = b n) :
    ∃ η : classes p x hx (sameBaseRing f Λ β hβ hβ0 hR),
      (∀ n, BasedSiteRing.map p x hx hp (projMap f Λ β hβ hβ0 hR n) η = b n) ∧
      BasedSiteRing.map p x hx hp (differenceMap f hf hsq Λ β hβ hβ0 hR) η =
        BasedSiteRing.map p x hx hp (inlMap f hf hsq Λ β hβ hβ0 hR) (b 0) := by
  have hTq := pair_bijective_squareZero (x := x) (hx := hx) Λ hRS (sameBaseRing f Λ β hβ hβ0 hR)
    (productModule f hf hsq hR)
  have hDq := fun n => pair_bijective_squareZero (x := x) (hx := hx) Λ hRS (level f Λ β hβ hβ0 hR n)
    (levelModule f hf hsq hR n)
  have hP := pair_bijective_level (x := x) (hx := hx) f hf hsq Λ β hβ hβ0 hR hRS
  obtain ⟨η, hη⟩ := AugmentedSiteRing.exists_classes_map_eq_of_difference (hp := hp)
    (fun n => (projMap f Λ β hβ hβ0 hR n).toHom)
    (fun n => (squareZeroProj f hf hsq Λ hR n).toHom) hQ.2
    (fst _ _).toHom (sameBaseTwist f hf hsq Λ β hβ hβ0 hR).toHom (snd _ _).toHom hTq.2
    (fun n => (fst _ _).toHom) (fun n => (levelTwist f hf hsq Λ β hβ hβ0 hR n).toHom)
    (fun n => (snd _ _).toHom) (fun n => (hDq n).1)
    (fun n => (fst _ _).toHom) (fun n => (snd _ _).toHom) (fun n => (hP n).2)
    (fun n => (levelUntwist f hf hsq Λ β hβ hβ0 hR n).toHom)
    (fun n => toHom_comp_eq' Λ (fst_comp_levelUntwist f hf hsq Λ β hβ hβ0 hR n))
    (fun n => toHom_comp_eq' Λ (levelTwist_comp_levelUntwist f hf hsq Λ β hβ hβ0 hR n))
    (fun n => (twistedProj f hf hsq Λ β hβ hβ0 hR n).toHom)
    (fun n => toHom_comp_eq Λ (fst_comp_twistedProj f hf hsq Λ β hβ hβ0 hR n))
    (fun n => toHom_comp_eq Λ (snd_comp_twistedProj f hf hsq Λ β hβ hβ0 hR n))
    (fun n => toHom_comp_eq Λ (levelTwist_comp_twistedProj f hf hsq Λ β hβ hβ0 hR n))
    ξ₀ b
  refine ⟨η, hη, ?_⟩
  exact AugmentedSiteRing.classes_map_difference_eq (hp := hp)
    (fun n => (projMap f Λ β hβ hβ0 hR n).toHom)
    (fun n => (transition f Λ β hβ hβ0 hR n).toHom)
    (fun n => (squareZeroProj f hf hsq Λ hR n).toHom) hQ.1
    (differenceMap f hf hsq Λ β hβ hβ0 hR).toHom (inlMap f hf hsq Λ β hβ hβ0 hR).toHom
    (fun n => (inlLevelMap f hf hsq Λ β hβ hβ0 hR n).toHom)
    (fun n => toHom_comp_eq' Λ (squareZeroProj_comp_inlMap f hf hsq Λ β hβ hβ0 hR n))
    (fun n => (augMap f Λ β hβ hβ0 hR n).toHom)
    (fun n => (fst _ _).toHom) (fun n => (snd _ _).toHom) (fun n => (hP n).1)
    (fun n => (diagMap f Λ β hβ hβ0 hR n).toHom)
    (fun n => toHom_comp_eq_id Λ (fst_comp_diagMap f Λ β hβ hβ0 hR n))
    (fun n => toHom_comp_eq_id Λ (snd_comp_diagMap f Λ β hβ hβ0 hR n))
    (fun n => (stepMap f Λ β hβ hβ0 hR n).toHom)
    (fun n => toHom_comp_eq Λ (fst_comp_stepMap f Λ β hβ hβ0 hR n))
    (fun n => toHom_comp_eq' Λ (snd_comp_stepMap f Λ β hβ hβ0 hR n))
    (fun n => (levelDiffMap f hf hsq Λ β hβ hβ0 hR n).toHom)
    (fun n => toHom_comp_eq Λ (squareZeroProj_comp_differenceMap f hf hsq Λ β hβ hβ0 hR n))
    (fun n => toHom_comp_eq Λ (levelDiffMap_comp_diagMap f hf hsq Λ β hβ hβ0 hR n))
    η b hη hb (b 0) (map_augMap_eq f Λ β hβ hβ0 hR b hb)

end Deformation.Artin.SquareZeroTower
