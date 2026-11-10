module

public import StacksFrontier.CategoryTheory.TwoYoneda.Fibered
public import StacksFrontier.Deformation.Artin.Infinitesimal.CanonicalElementTangentSpace
public import StacksFrontier.Deformation.Artin.Infinitesimal.DeformationSpaceComparison
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityDerivation
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityFieldClassEquation
public import StacksFrontier.Deformation.Artin.SliceTangentSpace
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation

/-!
# The canonical element computes the tangent map induced by a family

Let `𝒳` be a category fibred in groupoids over the big fppf site of a locally Noetherian scheme
`S`, satisfying (RS*), let `Spec Λ ⊂ S` be an affine open through which `U = Spec A ⟶ S`
factors, with `A` of finite type over `Λ`, and let `x` be an object of `𝒳` over `U`. Let `k` be
the residue field of a finite type point `u₀` of `U` and `x₀ = x|_{u₀}`. The object `x` is a
`1`-morphism `(Sch/U) ⟶ 𝒳` (Stacks 004B), so it induces a morphism of deformation categories
`𝓕_{U,k,u₀} ⟶ 𝓕_{𝒳,k,x₀}` (Stacks 07WJ) and hence a map on tangent spaces
`T𝓕_{U,k,u₀} ⟶ T𝓕_{𝒳,k,x₀}`. Stacks 07YC says that, through
`T𝓕_{U,k,u₀} = Der_Λ(A, k) = Hom_A(Ω_{A/Λ}, k)` and `T_x(k) = T𝓕_{𝒳,k,x₀}`, this map is
`θ ↦ T_x(θ)(x_can)`, where `x_can ∈ T_x(Ω_{A/Λ})` is the canonical element. This file proves
that.

## Main definitions

* `Deformation.Artin.residuePoint` — the point `u₀ : Spec k ⟶ U` as an object of `(Sch/U)`.
* `Deformation.Artin.derivationDeformation` — the deformation of `u₀` over `k[ε]` given by the
  morphism `Spec k[ε] ⟶ U` of `a ↦ (ā, θ(d a))`.
* `Deformation.Artin.derivationTangentEquiv` — `Hom_A(Ω_{A/Λ}, k) ≃ T𝓕_{U,k,u₀}` (Stacks 06IC
  for `U` at `u₀`).
* `Deformation.Artin.familyMorphism`, `Deformation.Artin.familyDeformationFunctor`,
  `Deformation.Artin.familyTangentMap` — the `1`-morphism `(Sch/U) ⟶ 𝒳` of `x`, the morphism
  of deformation categories it induces, and the induced map on tangent spaces.

## Main results

* `Deformation.Artin.canonicalTangentMap_eq_familyTangentMap` — **Stacks 07YC**: under the two
  identifications the induced map on tangent spaces is `θ ↦ T_x(θ)(x_can)`.

## Implementation notes

The argument is the source's. The ring map `A → k[ε]`, `a ↦ (ā, θ(d a))`, is the composite
`A → A[Ω_{A/Λ}] → A[k] → k[k]` of the canonical section, the map induced by `θ`, and the base
change along `A → k` (`Deformation.Artin.ringHomArrow_derivationRingHom`). Pulling `x` back along
it is therefore, on the one hand, the image of the deformation attached to `θ` under the induced
morphism of deformation categories, and on the other hand the restriction across
`A[k] = A ×_k k[k]` of `T_x(θ)(x_can)`; the class equation
`Deformation.Artin.canonicalFieldBaseChangeEquiv_canonicalTangentMap` of Stacks 07YM identifies
the latter, and two lifts of `x₀` with compatible cartesian arrows to `x` over the same morphism
have the same class (`Deformation.Artin.liftAlongClassMk_eq_of_cartesian`).

That `T𝓕_{U,k,u₀} → Hom_A(Ω_{A/Λ}, k)` is a bijection uses that `Spec Λ ⟶ S` is a monomorphism
(an open immersion): a deformation of `u₀` lies over `Spec Λ`, so its ring map `A → k[ε]` is
`Λ`-linear, and its `ε`-component is a `Λ`-derivation.

The field `k` is only required to be an `A`-algebra with `Spec k ⟶ U` locally of finite type,
which covers the residue field at a finite type point; Noetherianity of `Λ` is not used. The
containments of the spectra of the square-zero extensions in the chosen big site are size
conditions on the site, as elsewhere in this development.

## References

* [Stacks Project, Tag 07YC](https://stacks.math.columbia.edu/tag/07YC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Deformation.Artin

/-! ### The residue point of `U = Spec A` -/

section ResiduePoint

variable (A k : Type u) [CommRing A] [Field k] [Algebra A k]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A))) (hAk : B.Contains (Spec (.of k)))

/-- The point `u₀ : Spec k ⟶ U = Spec A` determined by the `A`-algebra structure of `k`, as an
object of the slice `(Sch/U)` of the chosen big fppf site. -/
public def residuePoint : Over (algebraOver A B S hS toS hA) :=
  Over.mk (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
    (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)

variable (Λ : Type u) [CommRing Λ] [Algebra Λ A] [Algebra Λ k] [IsScalarTower Λ A k]
  (baseMap : Spec (.of Λ) ⟶ S)
  (baseFactorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)

include baseFactorization in
/-- The structure morphism of `Spec k` through `U` factors through the chosen `Spec Λ`. -/
public theorem residueStructure_eq :
    Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS =
      Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ baseMap := by
  rw [← baseFactorization, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq]

include baseFactorization in
/-- The residue point lies over `Spec k ⟶ Spec Λ ⟶ S`, which is what makes it the base point of
the deformation category `𝓕_{U,k,u₀}`. -/
public theorem residuePoint_base :
    (Over.forget (algebraOver A B S hS toS hA) ⋙ Over.post B.inclusion).obj
        (residuePoint A k B S hS toS hA hAk) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ baseMap) :=
  congrArg (fun g : Spec (.of k) ⟶ S => (Over.mk g : Over S))
    (residueStructure_eq A k S toS Λ baseMap baseFactorization)

end ResiduePoint

/-! ### Morphisms `Spec k[M] ⟶ U` attached to ring maps -/

section RingHomPoint

variable (Λ A k : Type u) [CommRing Λ] [CommRing A] [Field k] [Algebra Λ A] [Algebra A k]
  [Algebra Λ k] [IsScalarTower Λ A k]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A))) (hAk : B.Contains (Spec (.of k)))
  (baseMap : Spec (.of Λ) ⟶ S)
  (baseFactorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)
  (M : SiteModule k B) (r : A →+* TrivSqZeroExt k M.obj)
  (hr : ∀ c : Λ, r (algebraMap Λ A c) = TrivSqZeroExt.inl (algebraMap A k (algebraMap Λ A c)))

include baseFactorization hr in
/-- The morphism `Spec k[M] ⟶ U` of the site over `S` given by a ring map `A → k[M]` which is
`Λ`-linear, i.e. restricts on `Λ` to `Λ → k ⊂ k[M]`. -/
public def ringHomArrow :
    squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) M ⟶
      algebraOver A B S hS toS hA := by
  refine Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom r)) : B.obj M.property ⟶ B.obj hA) ?_
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom r) ≫ toS =
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom k M.obj)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS
  have hring : CommRingCat.ofHom (algebraMap Λ A) ≫ CommRingCat.ofHom r =
      (CommRingCat.ofHom (algebraMap Λ A) ≫ CommRingCat.ofHom (algebraMap A k)) ≫
        CommRingCat.ofHom (TrivSqZeroExt.inlHom k M.obj) :=
    CommRingCat.hom_ext (RingHom.ext hr)
  rw [← baseFactorization, ← Category.assoc, ← Category.assoc, ← Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp, hring, Category.assoc]

omit [Algebra Λ k] [IsScalarTower Λ A k] in
/-- The morphism `ringHomArrow` is the spectrum of its ring map. -/
public theorem ringHomArrow_spec :
    (BigFppfOver.toScheme B S hS).map
        (ringHomArrow Λ A k B S hS toS hA baseMap baseFactorization M r hr) =
      Spec.map (CommRingCat.ofHom r) :=
  rfl

omit [Algebra Λ k] [IsScalarTower Λ A k] in
/-- A ring map `A → k[M]` lifting `A → k` gives a morphism restricting to the residue point
along the square-zero immersion `Spec k ⟶ Spec k[M]`. -/
public theorem squareZeroArrow_comp_ringHomArrow
    (hfst : ∀ a : A, (r a).fst = algebraMap A k a) :
    squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk M ≫
      ringHomArrow Λ A k B S hS toS hA baseMap baseFactorization M r hr =
    algebraOverMapOfRingHom (algebraMap A k) B S hS toS
      (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k M.obj).toRingHom) ≫
      Spec.map (CommRingCat.ofHom r) =
    Spec.map (CommRingCat.ofHom (algebraMap A k))
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext hfst)

include baseFactorization in
/-- The site object `Spec k[V]`, read over `S`, is the spectrum of the corresponding object of
`𝒞_Λ` over `Spec Λ`. -/
public theorem squareZeroOver_post_fgSiteModule (V : FGModuleCat.{u} k) :
    (Over.post B.inclusion).obj
        (squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS)
          ((fgSiteModule B hAk).obj V)) =
      Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap Λ ((artinianSquareZeroExtensionFunctor Λ k).obj V))) ≫ baseMap) := by
  have h : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom k V.obj)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS =
      Spec.map (CommRingCat.ofHom
        (algebraMap Λ ((artinianSquareZeroExtensionFunctor Λ k).obj V))) ≫ baseMap := by
    rw [residueStructure_eq A k S toS Λ baseMap baseFactorization, ← Category.assoc,
      ← Spec.map_comp]
    rfl
  exact congrArg
    (fun g : Spec (CommRingCat.of (TrivSqZeroExt k V.obj)) ⟶ S => (Over.mk g : Over S)) h

end RingHomPoint

/-! ### The tangent vector of `U` attached to a derivation -/

section DerivationPoint

variable (Λ A k : Type u) [CommRing Λ] [CommRing A] [Field k] [Algebra Λ A] [Algebra A k]
  [Algebra Λ k] [IsScalarTower Λ A k]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A))) (hAk : B.Contains (Spec (.of k)))
  (baseMap : Spec (.of Λ) ⟶ S)
  (baseFactorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)

omit [Algebra Λ k] [IsScalarTower Λ A k] in
/-- The ring map `A → k[k]`, `a ↦ (ā, θ(d a))`, attached to an `A`-linear map
`θ : Ω_{A/Λ} → k`. -/
public def derivationRingHom (θ : Ω[A⁄Λ] →ₗ[A] k) :
    A →+* TrivSqZeroExt k ((fgSiteModule B hAk).obj (FGModuleCat.of k k)).obj where
  toFun a := TrivSqZeroExt.inl (algebraMap A k a) +
    TrivSqZeroExt.inr (θ (KaehlerDifferential.D Λ A a))
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · change algebraMap A k 1 + 0 = 1
      simp
    · change (0 : k) + θ (KaehlerDifferential.D Λ A 1) = 0
      simp
  map_mul' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · change algebraMap A k (a * b) + 0 = (algebraMap A k a + 0) * (algebraMap A k b + 0)
      simp
    · change (0 : k) + θ (KaehlerDifferential.D Λ A (a * b)) =
        (algebraMap A k a + 0) * ((0 : k) + θ (KaehlerDifferential.D Λ A b)) +
          (algebraMap A k b + 0) * ((0 : k) + θ (KaehlerDifferential.D Λ A a))
      simp only [Derivation.leibniz, map_add, map_smul, zero_add, add_zero,
        Algebra.smul_def]
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · change algebraMap A k 0 + 0 = 0
      simp
    · change (0 : k) + θ (KaehlerDifferential.D Λ A 0) = 0
      simp
  map_add' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · change algebraMap A k (a + b) + 0 = (algebraMap A k a + 0) + (algebraMap A k b + 0)
      simp
    · change (0 : k) + θ (KaehlerDifferential.D Λ A (a + b)) =
        ((0 : k) + θ (KaehlerDifferential.D Λ A a)) + ((0 : k) + θ (KaehlerDifferential.D Λ A b))
      simp

omit [Algebra Λ k] [IsScalarTower Λ A k] in
/-- The ring map `derivationRingHom` agrees with `algebraMap A k` after the augmentation
`k[k] → k`. -/
public theorem fst_derivationRingHom (θ : Ω[A⁄Λ] →ₗ[A] k) (a : A) :
    (derivationRingHom Λ A k B hAk θ a).fst = algebraMap A k a := by
  change algebraMap A k a + 0 = algebraMap A k a
  rw [add_zero]

omit [Algebra Λ k] [IsScalarTower Λ A k] in
/-- The ring map `derivationRingHom` is `Λ`-linear: it kills the differentials of the
constants. -/
public theorem derivationRingHom_algebraMap (θ : Ω[A⁄Λ] →ₗ[A] k) (c : Λ) :
    derivationRingHom Λ A k B hAk θ (algebraMap Λ A c) =
      TrivSqZeroExt.inl (algebraMap A k (algebraMap Λ A c)) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · change algebraMap A k (algebraMap Λ A c) + 0 = algebraMap A k (algebraMap Λ A c)
    rw [add_zero]
  · change (0 : k) + θ (KaehlerDifferential.D Λ A (algebraMap Λ A c)) = 0
    rw [Derivation.map_algebraMap, map_zero, add_zero]

omit [IsScalarTower Λ A k] in
/-- The `ε`-component of a `Λ`-linear ring map `A → k[ε]` lifting `A → k` is a `Λ`-derivation. -/
private def derivationOfRingHom
    (q : A →+* TrivSqZeroExt k ((fgSiteModule B hAk).obj (FGModuleCat.of k k)).obj)
    (hfst : ∀ a, (q a).fst = algebraMap A k a)
    (hΛ : ∀ c : Λ, q (algebraMap Λ A c) = TrivSqZeroExt.inl (algebraMap Λ k c)) :
    Derivation Λ A k where
  toFun a := (q a).snd
  map_add' a b := by
    change (q (a + b)).snd = _
    rw [map_add]
    rfl
  map_smul' c a := by
    change (q (c • a)).snd = _
    rw [Algebra.smul_def, map_mul, TrivSqZeroExt.snd_mul, hΛ c, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.snd_inl, smul_zero, add_zero]
    exact (Algebra.smul_def (A := k) c _).symm
  map_one_eq_zero' := by
    change (q 1).snd = 0
    rw [map_one]
    rfl
  leibniz' a b := by
    change (q (a * b)).snd = _
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst a, hfst b, Algebra.smul_def, Algebra.smul_def]
    rfl

/-- A `Λ`-linear ring map `A → k[ε]` lifting `A → k` is the ring map attached to its
`ε`-component. -/
private theorem eq_derivationRingHom_derivationOfRingHom
    (q : A →+* TrivSqZeroExt k ((fgSiteModule B hAk).obj (FGModuleCat.of k k)).obj)
    (hfst : ∀ a, (q a).fst = algebraMap A k a)
    (hΛ : ∀ c : Λ, q (algebraMap Λ A c) = TrivSqZeroExt.inl (algebraMap Λ k c)) :
    q = derivationRingHom Λ A k B hAk
      (derivationOfRingHom Λ A k B hAk q hfst hΛ).liftKaehlerDifferential := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · exact (hfst a).trans (fst_derivationRingHom Λ A k B hAk _ a).symm
  · change (q a).snd = (0 : k) + (derivationOfRingHom Λ A k B hAk q hfst hΛ).liftKaehlerDifferential
      (KaehlerDifferential.D Λ A a)
    rw [zero_add, Derivation.liftKaehlerDifferential_comp_D]
    rfl

/-- The deformation of the residue point `u₀` of `U` over the dual numbers `k[ε]` attached to
a morphism `Spec k[ε] ⟶ U` given by a `Λ`-linear ring map `r : A → k[ε]` lifting `A → k`:
the morphism itself, with the square-zero immersion `Spec k ⟶ Spec k[ε]` as its arrow from
`u₀`. -/
public def ringHomDeformation
    (r : A →+* TrivSqZeroExt k ((fgSiteModule B hAk).obj (FGModuleCat.of k k)).obj)
    (hr : ∀ c : Λ, r (algebraMap Λ A c) = TrivSqZeroExt.inl (algebraMap A k (algebraMap Λ A c)))
    (hfst : ∀ a : A, (r a).fst = algebraMap A k a) :
    DeformationObject baseMap
      (Over.forget (algebraOver A B S hS toS hA) ⋙ Over.post B.inclusion)
      (residuePoint A k B S hS toS hA hAk)
      (residuePoint_base A k B S hS toS hA hAk Λ baseMap baseFactorization) where
  algebra := (artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k)
  point := Over.mk (ringHomArrow Λ A k B S hS toS hA baseMap baseFactorization
    ((fgSiteModule B hAk).obj (FGModuleCat.of k k)) r hr)
  arrow := Over.homMk (squareZeroArrow k B S hS
      (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
        ((fgSiteModule B hAk).obj (FGModuleCat.of k k)))
    (squareZeroArrow_comp_ringHomArrow Λ A k B S hS toS hA hAk baseMap baseFactorization
      ((fgSiteModule B hAk).obj (FGModuleCat.of k k)) r hr hfst)
  base := squareZeroOver_post_fgSiteModule Λ A k B S hS toS hAk baseMap baseFactorization
    (FGModuleCat.of k k)
  arrow_base := rfl

/-- The deformation of the residue point of `U` over `k[ε]` attached to
`θ : Ω_{A/Λ} → k`, through the ring map `a ↦ (ā, θ(d a))`. This is the element of
`T𝓕_{U,k,u₀}` which corresponds to `θ` under `T𝓕_{U,k,u₀} = Der_Λ(A, k) = Hom_A(Ω_{A/Λ}, k)`. -/
public def derivationDeformation (θ : Ω[A⁄Λ] →ₗ[A] k) :
    DeformationObject baseMap
      (Over.forget (algebraOver A B S hS toS hA) ⋙ Over.post B.inclusion)
      (residuePoint A k B S hS toS hA hAk)
      (residuePoint_base A k B S hS toS hA hAk Λ baseMap baseFactorization) :=
  ringHomDeformation Λ A k B S hS toS hA hAk baseMap baseFactorization
    (derivationRingHom Λ A k B hAk θ) (derivationRingHom_algebraMap Λ A k B hAk θ)
    (fst_derivationRingHom Λ A k B hAk θ)

end DerivationPoint

/-! ### The tangent space of `U` at the residue point -/

section TangentU

open SliceTangent

attribute [local instance] PredeformationConstruction.category

variable (Λ A k : Type u) [CommRing Λ] [CommRing A] [Field k] [Algebra Λ A] [Algebra A k]
  [Algebra Λ k] [IsScalarTower Λ A k]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A))) (hAk : B.Contains (Spec (.of k)))
  (baseMap : Spec (.of Λ) ⟶ S)
  (baseFactorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)

/-- The deformation category `𝓕_{U,k,u₀}` of the residue point of `U = Spec A`, i.e. the
predeformation category of `u₀` in `(Sch/U)`, is cofibered in groupoids. -/
public theorem residueDeformations_isCofiberedInGroupoids :
    IsCofiberedInGroupoids (BasedCategory.ofFunctor (predeformationCategory baseMap
      (Over.forget (algebraOver A B S hS toS hA) ⋙ Over.post B.inclusion)
      (residuePoint A k B S hS toS hA hAk)
      (residuePoint_base A k B S hS toS hA hAk Λ baseMap baseFactorization)).projection).p :=
  (predeformationCategory_isPredeformationCategory B hS baseMap
    (Over.forget (algebraOver A B S hS toS hA)) (residuePoint A k B S hS toS hA hAk)
    (residuePoint_base A k B S hS toS hA hAk Λ baseMap baseFactorization)
    (Functor.IsFiberedInGroupoids.over_forget _)).cofibered

/-- The deformation category `𝓕_{U,k,u₀}` of the residue point of `U`, as a category over
`𝒞_Λ`. -/
public abbrev residueDeformations : BasedCategory (ArtinianLocalAlgCat.{u, u, u} Λ k) :=
  BasedCategory.ofFunctor (predeformationCategory baseMap
    (Over.forget (algebraOver A B S hS toS hA) ⋙ Over.post B.inclusion)
    (residuePoint A k B S hS toS hA hAk)
    (residuePoint_base A k B S hS toS hA hAk Λ baseMap baseFactorization)).projection

/-- The tangent vector of `T𝓕_{U,k,u₀}` attached to `θ : Ω_{A/Λ} → k`: the class of
`Deformation.Artin.derivationDeformation θ`. -/
public def derivationTangentVector (θ : Ω[A⁄Λ] →ₗ[A] k) :
    artinianTangentSpace Λ k (isomorphismClasses (BasedCategory.ofFunctor
      (predeformationCategory baseMap
        (Over.forget (algebraOver A B S hS toS hA) ⋙ Over.post B.inclusion)
        (residuePoint A k B S hS toS hA hAk)
        (residuePoint_base A k B S hS toS hA hAk Λ baseMap baseFactorization)).projection)
      (residueDeformations_isCofiberedInGroupoids Λ A k B S hS toS hA hAk baseMap
        baseFactorization)) :=
  classOf (residueDeformations Λ A k B S hS toS hA hAk baseMap baseFactorization)
    (residueDeformations_isCofiberedInGroupoids Λ A k B S hS toS hA hAk baseMap
      baseFactorization)
    (⟨derivationDeformation Λ A k B S hS toS hA hAk baseMap baseFactorization θ, rfl⟩ :
      (residueDeformations Λ A k B S hS toS hA hAk baseMap baseFactorization).p.Fiber
        ((artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k)))

/-- The morphism to `U` underlying the deformation attached to a ring map is the spectrum of
that ring map. -/
public theorem deformationMap_ringHomDeformation
    (r : A →+* TrivSqZeroExt k ((fgSiteModule B hAk).obj (FGModuleCat.of k k)).obj)
    (hr : ∀ c : Λ, r (algebraMap Λ A c) = TrivSqZeroExt.inl (algebraMap A k (algebraMap Λ A c)))
    (hfst : ∀ a : A, (r a).fst = algebraMap A k a) :
    deformationMap (ringHomDeformation Λ A k B S hS toS hA hAk baseMap baseFactorization r hr
        hfst) =
      Spec.map (CommRingCat.ofHom r) :=
  Category.id_comp (Spec.map (CommRingCat.ofHom r))

/-- The morphism to `U` underlying the deformation attached to `θ` is the spectrum of
`a ↦ (ā, θ(d a))`. -/
public theorem deformationMap_derivationDeformation (θ : Ω[A⁄Λ] →ₗ[A] k) :
    deformationMap (derivationDeformation Λ A k B S hS toS hA hAk baseMap baseFactorization θ) =
      Spec.map (CommRingCat.ofHom (derivationRingHom Λ A k B hAk θ)) :=
  deformationMap_ringHomDeformation Λ A k B S hS toS hA hAk baseMap baseFactorization _ _ _

/-- Distinct `θ` give distinct tangent vectors of `U`: the deformation attached to `θ`
remembers its morphism `Spec k[ε] ⟶ U`, hence `a ↦ θ(d a)`, hence `θ`. -/
public theorem derivationTangentVector_injective :
    Function.Injective (derivationTangentVector Λ A k B S hS toS hA hAk baseMap
      baseFactorization) := by
  intro θ θ' h
  let 𝓕 := BasedCategory.ofFunctor (predeformationCategory baseMap
    (Over.forget (algebraOver A B S hS toS hA) ⋙ Over.post B.inclusion)
    (residuePoint A k B S hS toS hA hAk)
    (residuePoint_base A k B S hS toS hA hAk Λ baseMap baseFactorization)).projection
  let h𝓕 := residueDeformations_isCofiberedInGroupoids Λ A k B S hS toS hA hAk baseMap
    baseFactorization
  let a : 𝓕.p.Fiber ((artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k)) :=
    ⟨derivationDeformation Λ A k B S hS toS hA hAk baseMap baseFactorization θ, rfl⟩
  let b : 𝓕.p.Fiber ((artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k)) :=
    ⟨derivationDeformation Λ A k B S hS toS hA hAk baseMap baseFactorization θ', rfl⟩
  have hq : Quotient.mk (isIsomorphicSetoid _) a = Quotient.mk (isIsomorphicSetoid _) b := by
    rwa [← classOf_eq 𝓕 h𝓕, ← classOf_eq 𝓕 h𝓕]
  obtain ⟨e⟩ := Quotient.exact hq
  have hlift : 𝓕.p.IsHomLift (𝟙 _) e.hom.1 := e.hom.2
  have hring : (e.hom.1 : DeformationMorphism _ _ _ _ a.1 b.1).ringHom = 𝟙 _ := by
    have hfac := IsHomLift.fac' 𝓕.p
      (𝟙 ((artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k))) e.hom.1
    rw [Category.id_comp, eqToHom_trans] at hfac
    exact hfac.trans (eqToHom_refl _ _)
  have hmaps := deformationMap_of_morphism (e.hom.1 : DeformationMorphism _ _ _ _ a.1 b.1)
  have hid : Spec.map (CommRingCat.ofHom
      (e.hom.1 : DeformationMorphism _ _ _ _ a.1 b.1).ringHom.hom.toRingHom) = 𝟙 _ := by
    rw [hring]
    exact Spec.map_id _
  rw [hid] at hmaps
  replace hmaps := hmaps.trans (Category.id_comp _)
  have hspec : Spec.map (CommRingCat.ofHom (derivationRingHom Λ A k B hAk θ)) =
      Spec.map (CommRingCat.ofHom (derivationRingHom Λ A k B hAk θ')) :=
    (deformationMap_derivationDeformation Λ A k B S hS toS hA hAk baseMap baseFactorization
      θ).symm.trans (hmaps.symm.trans
        (deformationMap_derivationDeformation Λ A k B S hS toS hA hAk baseMap
          baseFactorization θ'))
  apply Derivation.liftKaehlerDifferential_unique
  ext a
  have := congrArg TrivSqZeroExt.snd
    (RingHom.congr_fun (congrArg (fun f => f.hom) (Spec.map_injective hspec)) a)
  change (0 : k) + θ (KaehlerDifferential.D Λ A a) = (0 : k) + θ' (KaehlerDifferential.D Λ A a)
    at this
  simpa using this

/-- The ring map `A → R` underlying a deformation of the residue point lifts `A → k`. -/
private theorem comp_residueMap_of_spec_map_eq_deformationMap
    (d : DeformationObject baseMap
      (Over.forget (algebraOver A B S hS toS hA) ⋙ Over.post B.inclusion)
      (residuePoint A k B S hS toS hA hAk)
      (residuePoint_base A k B S hS toS hA hAk Λ baseMap baseFactorization))
    {q : CommRingCat.of A ⟶ CommRingCat.of d.algebra}
    (hq : Spec.map q = (deformationMap d : Spec (.of d.algebra) ⟶ Spec (.of A))) :
    ∀ a : A, residueMap d.algebra (q.hom a) = algebraMap A k a := by
  have hres := residue_deformationMap d
  have hpt : pointMap (residuePoint_base A k B S hS toS hA hAk Λ baseMap baseFactorization) =
      Spec.map (CommRingCat.ofHom (algebraMap A k)) :=
    Category.id_comp (Spec.map (CommRingCat.ofHom (algebraMap A k)))
  rw [hpt, ← hq] at hres
  exact fun a => RingHom.congr_fun (congrArg CommRingCat.Hom.hom
    (Spec.map_injective ((Spec.map_comp _ _).trans hres))) a

/-- The ring map `A → R` underlying a deformation of the residue point is `Λ`-linear, as
`Spec Λ ⟶ S` is a monomorphism. -/
private theorem algebraMap_comp_of_spec_map_eq_deformationMap [IsOpenImmersion baseMap]
    (d : DeformationObject baseMap
      (Over.forget (algebraOver A B S hS toS hA) ⋙ Over.post B.inclusion)
      (residuePoint A k B S hS toS hA hAk)
      (residuePoint_base A k B S hS toS hA hAk Λ baseMap baseFactorization))
    {q : CommRingCat.of A ⟶ CommRingCat.of d.algebra}
    (hq : Spec.map q = (deformationMap d : Spec (.of d.algebra) ⟶ Spec (.of A))) :
    ∀ c : Λ, q.hom (algebraMap Λ A c) = algebraMap Λ d.algebra c := by
  have hcomp := deformationMap_comp d
  rw [← hq] at hcomp
  change Spec.map q ≫ toS = _ at hcomp
  have hcomp' : Spec.map q ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap =
      Spec.map (CommRingCat.ofHom (algebraMap Λ d.algebra)) ≫ baseMap := by
    rwa [baseFactorization]
  exact fun c => RingHom.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective
    ((Spec.map_comp _ _).trans ((cancel_mono baseMap).mp ((Category.assoc _ _ _).trans hcomp'))))) c

include baseFactorization in
/-- Every tangent vector of `U` at the residue point is attached to some `θ : Ω_{A/Λ} → k`: a
deformation of `u₀` over `k[ε]` is a morphism `Spec k[ε] ⟶ U` lying over `Spec Λ`, i.e. (as
`Spec Λ ⟶ S` is an open immersion, hence a monomorphism) a `Λ`-algebra map `A → k[ε]` lifting
`A → k`, and the `ε`-component of such a map is a `Λ`-derivation `A → k`. -/
public theorem derivationTangentVector_surjective [IsOpenImmersion baseMap] :
    Function.Surjective (derivationTangentVector Λ A k B S hS toS hA hAk baseMap
      baseFactorization) := by
  let 𝓕 := residueDeformations Λ A k B S hS toS hA hAk baseMap baseFactorization
  let h𝓕 := residueDeformations_isCofiberedInGroupoids Λ A k B S hS toS hA hAk baseMap
    baseFactorization
  intro z
  obtain ⟨⟨⟨alg, pt, ar, base, ab⟩, hd⟩, rfl⟩ := classOf_surjective 𝓕 h𝓕 _ z
  obtain rfl : alg = _ := hd
  let d : DeformationObject baseMap _ _
      (residuePoint_base A k B S hS toS hA hAk Λ baseMap baseFactorization) := ⟨_, pt, ar, base, ab⟩
  obtain ⟨q, hq⟩ := Spec.map_surjective
    (deformationMap d : Spec (.of d.algebra) ⟶ Spec (.of A))
  -- The ring map lifts `A → k`.
  have hfst : ∀ a : A, TrivSqZeroExt.fst (q.hom a : TrivSqZeroExt k k) = algebraMap A k a :=
    comp_residueMap_of_spec_map_eq_deformationMap Λ A k B S hS toS hA hAk baseMap
    baseFactorization d hq
  -- The ring map is `Λ`-linear.
  have hΛ : ∀ c : Λ, (q.hom (algebraMap Λ A c) : TrivSqZeroExt k k) = .inl (algebraMap Λ k c) :=
    algebraMap_comp_of_spec_map_eq_deformationMap Λ A k B S hS toS hA hAk baseMap
    baseFactorization d hq
  -- Its `ε`-component is a `Λ`-derivation.
  let D' := derivationOfRingHom Λ A k B hAk q.hom hfst hΛ
  refine ⟨D'.liftKaehlerDifferential, ?_⟩
  have hqθ : q = CommRingCat.ofHom (derivationRingHom Λ A k B hAk D'.liftKaehlerDifferential) :=
    CommRingCat.hom_ext (eq_derivationRingHom_derivationOfRingHom Λ A k B hAk q.hom hfst hΛ)
  have hmain : deformationMap d = deformationMap
      (derivationDeformation Λ A k B S hS toS hA hAk baseMap baseFactorization
        D'.liftKaehlerDifferential) := by
    rw [deformationMap_derivationDeformation, ← hqθ]
    exact hq.symm
  obtain ⟨m, hm⟩ := exists_morphism_of_deformationMap_eq
    (a := derivationDeformation Λ A k B S hS toS hA hAk baseMap baseFactorization
      D'.liftKaehlerDifferential) (b := d) rfl
    (hmain.trans ((Category.id_comp _).symm.trans
      (congrArg (· ≫ deformationMap (derivationDeformation Λ A k B S hS toS hA hAk baseMap
        baseFactorization D'.liftKaehlerDifferential)) (Spec.map_id _).symm)))
  let C := predeformationCategory baseMap
    (Over.forget (algebraOver A B S hS toS hA) ⋙ Over.post B.inclusion)
    (residuePoint A k B S hS toS hA hAk)
    (residuePoint_base A k B S hS toS hA hAk Λ baseMap baseFactorization)
  let a' : C.carrier := derivationDeformation Λ A k B S hS toS hA hAk baseMap baseFactorization
    D'.liftKaehlerDifferential
  let m' : a' ⟶ (d : C.carrier) := m
  have hlift : 𝓕.p.IsHomLift
      (𝟙 ((artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k))) m' :=
    IsHomLift.of_fac 𝓕.p _ m' rfl rfl (by
      change 𝟙 _ = 𝟙 _ ≫ m.ringHom ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id, hm]
      exact (eqToHom_refl _ _).symm)
  exact classOf_eq_of_isIsomorphic 𝓕 h𝓕
    (⟨a', rfl⟩ : 𝓕.p.Fiber ((artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k)))
    ⟨d, rfl⟩ ⟨Functor.Fiber.isoMk (isoOfIsHomLiftId h𝓕 m' hlift) hlift⟩

include baseFactorization in
/-- **Stacks Example 06IC at the residue point of `U`.** The tangent space of the deformation
category `𝓕_{U,k,u₀}` is `Der_Λ(A, k) = Hom_A(Ω_{A/Λ}, k)`: `θ` corresponds to the class of the
deformation `Spec k[ε] ⟶ U` given by `a ↦ (ā, θ(d a))`. -/
public def derivationTangentEquiv [IsOpenImmersion baseMap] :
    (Ω[A⁄Λ] →ₗ[A] k) ≃
      artinianTangentSpace Λ k (isomorphismClasses
        (residueDeformations Λ A k B S hS toS hA hAk baseMap baseFactorization)
        (residueDeformations_isCofiberedInGroupoids Λ A k B S hS toS hA hAk baseMap
          baseFactorization)) :=
  Equiv.ofBijective _
    ⟨derivationTangentVector_injective Λ A k B S hS toS hA hAk baseMap baseFactorization,
      derivationTangentVector_surjective Λ A k B S hS toS hA hAk baseMap baseFactorization⟩

/-- The identification `Deformation.Artin.derivationTangentEquiv` sends `θ` to the class of the
deformation given by `a ↦ (ā, θ(d a))`. -/
public theorem derivationTangentEquiv_apply [IsOpenImmersion baseMap] (θ : Ω[A⁄Λ] →ₗ[A] k) :
    derivationTangentEquiv Λ A k B S hS toS hA hAk baseMap baseFactorization θ =
      derivationTangentVector Λ A k B S hS toS hA hAk baseMap baseFactorization θ :=
  rfl

end TangentU

/-! ### The morphism of deformation categories induced by `x` -/

section Induced

attribute [local instance] PredeformationConstruction.category

variable (Λ A k : Type u) [CommRing Λ] [CommRing A] [Field k] [Algebra Λ A] [Algebra A k]
  [Algebra Λ k] [IsScalarTower Λ A k]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A))) (hAk : B.Contains (Spec (.of k)))
  (baseMap : Spec (.of Λ) ⟶ S)
  (baseFactorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA) (hp : p.IsFiberedInGroupoids)

/-- The `1`-morphism `(Sch/U) ⟶ 𝒳` over the site determined by the object `x` over
`U = Spec A` (Stacks 004B): a morphism `T ⟶ U` goes to the chosen pullback of `x` to `T`. -/
public abbrev familyMorphism : Over (algebraOver A B S hS toS hA) ⥤ X :=
  letI : p.IsFibered := hp.isFibered
  Functor.FiberedMor.OfFiberObj.pullbackFunctor p (algebraOver A B S hS toS hA) hx

/-- The `1`-morphism determined by `x` commutes with the functors to schemes over `S`. -/
public theorem familyMorphism_comp :
    familyMorphism A B S hS toS hA p x hx hp ⋙ (p ⋙ Over.post B.inclusion) =
      Over.forget (algebraOver A B S hS toS hA) ⋙ Over.post B.inclusion := by
  let : p.IsFibered := hp.isFibered
  rw [← Functor.assoc]
  exact congrArg (· ⋙ Over.post B.inclusion)
    (Functor.FiberedMor.OfFiberObj.pullbackFunctor_comp p (algebraOver A B S hS toS hA) hx)

include baseFactorization in
/-- The image `x₀ = x|_{u₀}` of the residue point under the `1`-morphism determined by `x`
lies over `Spec k ⟶ Spec Λ ⟶ S`. -/
public theorem familyMorphism_residuePoint_base :
    (p ⋙ Over.post B.inclusion).obj
        ((familyMorphism A B S hS toS hA p x hx hp).obj (residuePoint A k B S hS toS hA hAk)) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ baseMap) :=
  imageBasePoint baseMap _ _ _ (familyMorphism_comp A B S hS toS hA p x hx hp) _
    (residuePoint_base A k B S hS toS hA hAk Λ baseMap baseFactorization)

/-- The image `x₀` of the residue point lies over `Spec k`. -/
public theorem familyMorphism_residuePoint_obj :
    p.obj ((familyMorphism A B S hS toS hA p x hx hp).obj (residuePoint A k B S hS toS hA hAk)) =
      algebraOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk :=
  let : p.IsFibered := hp.isFibered
  Functor.IsPreFibered.pullbackObj_proj hx _

/-- The deformation category `𝓕_{𝒳,k,x₀}` of `x₀ = x|_{u₀}` is cofibered in groupoids. -/
public theorem familyDeformations_isCofiberedInGroupoids :
    IsCofiberedInGroupoids (BasedCategory.ofFunctor (predeformationCategory baseMap
      (p ⋙ Over.post B.inclusion)
      ((familyMorphism A B S hS toS hA p x hx hp).obj (residuePoint A k B S hS toS hA hAk))
      (familyMorphism_residuePoint_base Λ A k B S hS toS hA hAk baseMap baseFactorization p x hx
        hp)).projection).p :=
  (predeformationCategory_isPredeformationCategory B hS baseMap p _ _ hp).cofibered

/-- **The morphism `𝓕_{U,k,u₀} ⟶ 𝓕_{𝒳,k,x₀}` induced by the object `x` over `U`** (Stacks 07WJ
applied to the `1`-morphism `(Sch/U) ⟶ 𝒳` determined by `x`). -/
public def familyDeformationFunctor :
    InducedPredeformationFunctor baseMap
      (Over.forget (algebraOver A B S hS toS hA) ⋙ Over.post B.inclusion)
      (p ⋙ Over.post B.inclusion) (familyMorphism A B S hS toS hA p x hx hp)
      (familyMorphism_comp A B S hS toS hA p x hx hp) (residuePoint A k B S hS toS hA hAk)
      (residuePoint_base A k B S hS toS hA hAk Λ baseMap baseFactorization) :=
  mapPredeformationCategory baseMap _ _ _ _ _ _

/-- **The map on tangent spaces `T𝓕_{U,k,u₀} ⟶ T𝓕_{𝒳,k,x₀}` induced by the object `x` over
`U`**: the value at the dual numbers of the map of associated functors of isomorphism classes
induced by `Deformation.Artin.familyDeformationFunctor`. -/
public def familyTangentMap :
    artinianTangentSpace Λ k (isomorphismClasses
        (residueDeformations Λ A k B S hS toS hA hAk baseMap baseFactorization)
        (residueDeformations_isCofiberedInGroupoids Λ A k B S hS toS hA hAk baseMap
          baseFactorization)) →
      artinianTangentSpace Λ k (isomorphismClasses (BasedCategory.ofFunctor
        (predeformationCategory baseMap (p ⋙ Over.post B.inclusion)
          ((familyMorphism A B S hS toS hA p x hx hp).obj (residuePoint A k B S hS toS hA hAk))
          (familyMorphism_residuePoint_base Λ A k B S hS toS hA hAk baseMap baseFactorization p
            x hx hp)).projection)
        (familyDeformations_isCofiberedInGroupoids Λ A k B S hS toS hA hAk baseMap
          baseFactorization p x hx hp)) :=
  mapIsomorphismClasses
    (residueDeformations_isCofiberedInGroupoids Λ A k B S hS toS hA hAk baseMap
      baseFactorization)
    (familyDeformations_isCofiberedInGroupoids Λ A k B S hS toS hA hAk baseMap
      baseFactorization p x hx hp)
    (familyDeformationFunctor Λ A k B S hS toS hA hAk baseMap baseFactorization p x hx
      hp).toBasedFunctor _

end Induced

/-! ### The canonical element computes the induced tangent map -/

section Comparison

attribute [local instance] PredeformationConstruction.category

variable (Λ A k : Type u) [CommRing Λ] [CommRing A] [Field k] [Algebra Λ A] [Algebra A k]
  [Algebra Λ k] [IsScalarTower Λ A k]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A))) (hAk : B.Contains (Spec (.of k)))
  (baseMap : Spec (.of Λ) ⟶ S)
  (baseFactorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA) (hp : p.IsFiberedInGroupoids)
  (hRS : SatisfiesRSStar B S hS p hp)
  (hΩ : B.Contains (Spec (squareZeroRing A (differentialsModule Λ A))))
  (hk : B.Contains (Spec (squareZeroRing A (ModuleCat.of A k))))
  (hkk : B.Contains (Spec (squareZeroRing k (ModuleCat.of k k))))

omit [Algebra Λ k] [IsScalarTower Λ A k] in
/-- The morphism `Spec k[ε] ⟶ U` attached to `θ` is the one along which the canonical element is
read at the dual numbers of `k`: `a ↦ (ā, θ(d a))` is the canonical section `a ↦ (a, d a)`
pushed along `θ` and base-changed along `A → k`. -/
public theorem ringHomArrow_derivationRingHom (θ : Ω[A⁄Λ] →ₗ[A] k) :
    ringHomArrow Λ A k B S hS toS hA baseMap baseFactorization
        ((fgSiteModule B hAk).obj (FGModuleCat.of k k)) (derivationRingHom Λ A k B hAk θ)
        (derivationRingHom_algebraMap Λ A k B hAk θ) =
      canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  refine Eq.trans ?_ (canonicalDualNumbersArrow_spec Λ A k B S hS toS hA p x hx hp hRS hΩ hkk
    baseMap baseFactorization θ).symm
  change Spec.map (CommRingCat.ofHom (derivationRingHom Λ A k B hAk θ)) = _
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun a => (canonicalDualNumbersMap_apply Λ A k B S hS
    toS hA p x hx hp hRS hΩ baseMap baseFactorization θ a).symm)

include baseFactorization in
/-- A residue field at a finite type point of `U`, with `U` of finite type over the affine open
`Spec Λ ⊂ S`, is of finite type over `S`. -/
public theorem residue_locallyOfFiniteType [IsOpenImmersion baseMap] [Algebra.FiniteType Λ A]
    (hpt : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap A k)))) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ baseMap) := by
  rw [← residueStructure_eq A k S toS Λ baseMap baseFactorization, ← baseFactorization]
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ A))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  infer_instance

/-- A morphism out of the spectrum of a field is quasi-compact, its source having one point. -/
public theorem residue_quasiCompact :
    QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ baseMap) := by
  have : Finite (Spec (CommRingCat.of k)) := inferInstanceAs (Finite (PrimeSpectrum k))
  exact ⟨fun _ _ _ => (Set.toFinite _).isCompact⟩

attribute [local instance] residueTangentModule in
include baseFactorization in
/-- **Stacks 07YC: the canonical element produces the map on tangent spaces induced by `x`.**

Let `𝒳` be a category fibred in groupoids over the big fppf site of a locally Noetherian `S`,
satisfying (RS*), let `Spec Λ ⊂ S` be an affine open through which `U = Spec A ⟶ S` factors,
with `A` of finite type over `Λ`, let `x` be an object of `𝒳` over `U`, and let `k` be the
residue field of a finite type point `u₀` of `U`, with `x₀ = x|_{u₀}`. Then:

* `T_x(k)` is the tangent space of `𝓕_{𝒳,k,x₀}`: the `k`-linear identification `e` below is
  the one of Stacks 0D18 composed with the (RS*) identification `T_x(k) = T_{x₀}(k)` across
  `A[k] = A ×_k k[k]`, pinned down by sending the class of a deformation to the class of the
  corresponding lift;
* `T𝓕_{U,k,u₀} = Der_Λ(A, k) = Hom_A(Ω_{A/Λ}, k)` (Stacks 06IC), by
  `Deformation.Artin.derivationTangentEquiv`;
* through these identifications the map on tangent spaces `T𝓕_{U,k,u₀} ⟶ T𝓕_{𝒳,k,x₀}`
  induced by the object `x` over `U` (`Deformation.Artin.familyTangentMap`) is
  `θ ↦ T_x(θ)(x_can)`.

The field `k` is only required to be an `A`-algebra with `Spec k ⟶ U` of finite type, which
includes the residue field at a finite type point. The containments of the spectra of the
square-zero extensions in the chosen big site are size conditions on the site. -/
@[stacks 07YC "the canonical element gives the tangent map `T𝓕_{U,k,u₀} ⟶ T𝓕_{𝒳,k,x₀}` \
induced by `x`: `θ ↦ T_x(θ)(x_can)`"]
public theorem canonicalTangentMap_eq_familyTangentMap [IsLocallyNoetherian S]
    [IsOpenImmersion baseMap] [Algebra.FiniteType Λ A]
    (hpt : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap A k)))) :
    letI : p.IsFibered := hp.isFibered
    let x₀ := (familyMorphism A B S hS toS hA p x hx hp).obj (residuePoint A k B S hS toS hA hAk)
    let D := predeformationCategory baseMap (p ⋙ Over.post B.inclusion) x₀
      (familyMorphism_residuePoint_base Λ A k B S hS toS hA hAk baseMap baseFactorization p x hx
        hp)
    let 𝓕 := BasedCategory.ofFunctor D.projection
    let hD : IsDeformationCategory D.projection :=
      isDeformationCategory_predeformationCategory_of_satisfiesRSStar B S hS p hp hRS baseMap x₀
        (familyMorphism_residuePoint_base Λ A k B S hS toS hA hAk baseMap baseFactorization p x
          hx hp)
        (residue_locallyOfFiniteType Λ A k S toS baseMap baseFactorization hpt)
        (residue_quasiCompact Λ k S baseMap)
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses 𝓕 hD.predeformation.cofibered))) :=
      ⟨schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD⟩
    let M : SiteModule k B := ⟨ModuleCat.of k k, hkk⟩
    let L := tangentFunctor k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk p
      x₀ (familyMorphism_residuePoint_obj A k B S hS toS hA hAk p x hx hp) hp hRS
    ∃ e : artinianTangentSpace Λ k (isomorphismClasses 𝓕 hD.predeformation.cofibered) ≃ₗ[k]
        ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj
          (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) : Type max (u + 1) v w),
      (∀ z : D.projection.Fiber ((artinianSquareZeroExtensionFunctor Λ k).obj
          (FGModuleCat.of k k)),
        ∃ y : (Under.post p).Fiber (Under.mk (eqToHom
            (familyMorphism_residuePoint_obj A k B S hS toS hA hAk p x hx hp) ≫
              squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS)
                hAk M)),
          L.liftEquiv M (residueTangentEquiv A k B S hS toS hA p x hx hp hRS hk hAk hkk
              (e (classOf 𝓕 hD.predeformation.cofibered z))) = Quotient.mk _ y ∧
            ∃ (η : y.1.right ≅ (D.objects z.1).point)
              (hbase : p.obj y.1.right = p.obj (D.objects z.1).point),
              p.map η.hom = eqToHom hbase ∧ y.1.hom ≫ η.hom = (D.objects z.1).arrow) ∧
      ∀ θ : Ω[A⁄Λ] →ₗ[A] k,
        e (familyTangentMap Λ A k B S hS toS hA hAk baseMap baseFactorization p x hx hp
            (derivationTangentEquiv Λ A k B S hS toS hA hAk baseMap baseFactorization θ)) =
          (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map
            (⟨ModuleCat.ofHom θ⟩ : differentialsSiteModule Λ A B hΩ ⟶
              (⟨ModuleCat.of A k, hk⟩ : SiteModule A B))
            (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
              baseFactorization).element := by
  intro x₀ D 𝓕 hD M L
  let : p.IsFibered := hp.isFibered
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
  let : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses 𝓕 hD.predeformation.cofibered))) :=
    ⟨schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD⟩
  obtain ⟨e₀, he₀⟩ := tangentSpace_deformationCategory_linearEquiv B S hS baseMap
    (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
    (residue_locallyOfFiniteType Λ A k S toS baseMap baseFactorization hpt)
    (residue_quasiCompact Λ k S baseMap) p hp hRS x₀
    (familyMorphism_residuePoint_base Λ A k B S hS toS hA hAk baseMap baseFactorization p x hx hp)
    (familyMorphism_residuePoint_obj A k B S hS toS hA hAk p x hx hp)
  let R := residueTangentEquiv A k B S hS toS hA p x hx hp hRS hk hAk hkk
  refine ⟨e₀.trans R.symm, fun z => ?_, fun θ => ?_⟩
  · obtain ⟨y, hy, hrest⟩ := he₀ z
    exact ⟨y, (congrArg (L.liftEquiv M) (R.apply_symm_apply _)).trans hy, hrest⟩
  · let τ := derivationDeformation Λ A k B S hS toS hA hAk baseMap baseFactorization θ
    let G := familyDeformationFunctor Λ A k B S hS toS hA hAk baseMap baseFactorization p x hx hp
    let F := familyMorphism A B S hS toS hA p x hx hp
    let g := canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
      baseFactorization θ
    let z' : 𝓕.p.Fiber ((artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k)) :=
      (fiberFunctor G.toBasedFunctor _).obj ⟨τ, rfl⟩
    have hT : familyTangentMap Λ A k B S hS toS hA hAk baseMap baseFactorization p x hx hp
        (derivationTangentEquiv Λ A k B S hS toS hA hAk baseMap baseFactorization θ) =
          classOf 𝓕 hD.predeformation.cofibered z' :=
      mapIsomorphismClasses_classOf
        (residueDeformations_isCofiberedInGroupoids Λ A k B S hS toS hA hAk baseMap
          baseFactorization)
        (familyDeformations_isCofiberedInGroupoids Λ A k B S hS toS hA hAk baseMap
          baseFactorization p x hx hp) G.toBasedFunctor
        (⟨τ, rfl⟩ : (residueDeformations Λ A k B S hS toS hA hAk baseMap baseFactorization).p.Fiber
          ((artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k)))
    obtain ⟨y, hy, η, hbase, hη, hyη⟩ := he₀ z'
    -- The chosen pullback of `x` along the morphism `Spec k[ε] ⟶ U` attached to `θ`.
    let φ : F.obj τ.point ⟶ x := Functor.IsPreFibered.pullbackMap hx τ.point.hom
    have hτg : τ.point.hom = g :=
      ringHomArrow_derivationRingHom Λ A k B S hS toS hA hAk baseMap baseFactorization p x hx hp
        hRS hΩ hkk θ
    have hφ : p.IsHomLift g φ := hτg ▸ (inferInstance : p.IsCartesian τ.point.hom
      (Functor.IsPreFibered.pullbackMap hx τ.point.hom)).toIsHomLift
    have hpt : (D.objects z'.1).point = F.obj τ.point := G.object_point τ
    have harr : (D.objects z'.1).arrow = F.map τ.arrow ≫ eqToHom hpt.symm := G.object_arrow τ
    apply R.injective
    refine (R.apply_symm_apply _).trans ?_
    apply (L.liftEquiv M).injective
    refine ((congrArg (L.liftEquiv M) (congrArg e₀ hT)).trans hy).trans ?_
    refine Eq.trans ?_ (liftEquiv_residueTangentEquiv A k B S hS toS hA p x hx hp hRS hk hAk hkk
      _).symm
    refine Eq.trans ?_ (canonicalFieldBaseChangeEquiv_canonicalTangentMap Λ A k B S hS toS hA hAk
      p x hx hp hRS hΩ hk hkk baseMap baseFactorization θ (F.obj τ.point) φ hφ).symm
    have hyb : p.obj y.1.right = squareZeroOver k B S hS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) M :=
      liftAlong_base_obj p x₀ _ y
    have hχ : p.IsHomLift g (η.hom ≫ eqToHom hpt ≫ φ) := by
      refine IsHomLift.of_fac' p g _ hyb hx ?_
      rw [Functor.map_comp, Functor.map_comp, hη, eqToHom_map, IsHomLift.fac' p g φ]
      simp
    refine liftAlongClassMk_eq_of_cartesian (g := g) y _ (η.hom ≫ eqToHom hpt ≫ φ) φ
      (hp.isStronglyCartesian_homLift _ _) (hp.isStronglyCartesian_homLift _ _) ?_
    refine Eq.trans ?_ (canonicalDualNumbersConnectingArrow_fac Λ A k B S hS toS hA hAk p x hx hp
      hRS hΩ hkk baseMap baseFactorization θ (F.obj τ.point) φ hφ).symm
    rw [← Category.assoc, hyη, harr, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    exact Functor.FiberedMor.OfFiberObj.pullbackFunctor_map_fac p _ hx τ.arrow

end Comparison

end Deformation.Artin
