module

public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.AffineSpaceCriterion
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreLocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeAssassin.ClosureRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.NoetherNormalization
public import StacksFrontier.RingTheory.CohenMacaulay.OpenLocus
public import StacksFrontier.RingTheory.CohenMacaulay.Locus
public import StacksFrontier.RingTheory.KrullDimension.Defs
public import StacksFrontier.RingTheory.RelativeDimension.QuasiFinite
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeNeTop
import all StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.AffineSpaceCriterion

/-!
# Further results

Results complementing
`StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.AffineSpaceCriterion`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry

section FiberFlatness

open IsLocalRing Algebra.TensorProduct TensorProduct

section FiberLocalization

variable {R X : Type*} [CommRing R] [CommRing X] [Algebra R X] (p : Ideal R) [p.IsPrime]
  (r : Ideal X) [r.IsPrime] [r.LiesOver p] (J : Ideal (Localization.AtPrime r))

end FiberLocalization

section Core

open Localization.AtPrime

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] {σ : Type*} [Finite σ]
  [Algebra (MvPolynomial σ R) T] [IsScalarTower R (MvPolynomial σ R) T]

end Core

end FiberFlatness

attribute [local instance 2000] CategoryTheory.CategoryStruct.toQuiver

/-- Composing with the map of affine spaces induced by an open `V ⊆ S` and the structure map of
`𝔸_S` is composing with the structure map of `𝔸_V` and the inclusion of `V`. -/
private theorem affineSpace_map_ι_comp_over {S Y : Scheme.{u}} (σ : Type u) (V : S.Opens)
    (π : Y ⟶ AffineSpace σ V.toScheme) :
    (π ≫ AffineSpace.map σ V.ι) ≫ (AffineSpace σ S ↘ S) =
      π ≫ (AffineSpace.over σ V.toScheme).hom ≫ V.ι := by
  rw [Category.assoc, AffineSpace.map_over]
  rfl

/-- Composing a locally quasi-finite morphism of finite type into `𝔸_V` with the open immersion
`𝔸_V ⟶ 𝔸_S` induced by an open `V ⊆ S` keeps it locally of finite type and locally
quasi-finite. -/
private theorem locallyOfFiniteType_and_locallyQuasiFinite_comp_affineSpace_map
    {S Y : Scheme.{u}} (σ : Type u) (V : S.Opens) (π : Y ⟶ AffineSpace σ V.toScheme)
    [LocallyOfFiniteType π] [LocallyQuasiFinite π] :
    LocallyOfFiniteType (π ≫ AffineSpace.map σ V.ι) ∧
      LocallyQuasiFinite (π ≫ AffineSpace.map σ V.ι) := by
  have := affineSpace_map_isOpenImmersion σ V.ι
  exact ⟨inferInstance, inferInstance⟩

/-- Let `f : X ⟶ S` be locally of finite type and let `n` be the dimension at `x` of the fibre
of `f` through `x`. Then some open neighbourhood `U` of `x` carries a locally quasi-finite
`S`-morphism `U ⟶ 𝔸ⁿ_S`. -/
public theorem exists_locallyQuasiFinite_affineSpace {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) (n : ℕ)
    (hn : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (n : WithBot ℕ∞)) :
    ∃ (U : X.Opens) (_ : x ∈ U) (g : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) S),
      g ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = U.ι ≫ f ∧
        LocallyOfFiniteType g ∧ LocallyQuasiFinite g := by
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  let V : S.affineOpens := ⟨V₀, hV₀⟩
  obtain ⟨U, hxU, hUV, π, hfac, hprops⟩ :=
    exists_affineOpen_quasiFinite_affineSpace_factorization f x V hxV n hn
  have : LocallyOfFiniteType π := hprops.1.1
  have : LocallyQuasiFinite π := hprops.2
  exact ⟨U.1, hxU, _, (affineSpace_map_ι_comp_over _ V.1 π).trans hfac,
    (locallyOfFiniteType_and_locallyQuasiFinite_comp_affineSpace_map _ V.1 π).1,
    (locallyOfFiniteType_and_locallyQuasiFinite_comp_affineSpace_map _ V.1 π).2⟩

/-- If `π : U₀ ⟶ Y` is locally of finite presentation and flat at `x`, then inside any open
`G ∋ x` there is an affine open `U₁ ∋ x` contained in `U₀` on which `π` restricts to a flat
morphism. -/
private theorem exists_affineOpen_flat_homOfLE_comp {X Y : Scheme.{u}} {U₀ : X.Opens}
    (π : U₀.toScheme ⟶ Y) [LocallyOfFinitePresentation π] {x : X} (hxU₀ : x ∈ U₀)
    (hflatx : AlgebraicGeometry.IsFlatAt π.toLRSHom.toShHom ⟨x, hxU₀⟩) {G : X.Opens}
    (hxG : x ∈ G) :
    ∃ (U₁ : X.Opens) (_ : IsAffineOpen U₁) (hle : U₁ ≤ U₀), x ∈ U₁ ∧ U₁ ≤ G ∧
      Flat (X.homOfLE hle ≫ π) := by
  let W : U₀.toScheme.Opens :=
    ⟨{y | AlgebraicGeometry.IsFlatAt π.toLRSHom.toShHom y}, isOpen_flatAt π⟩
  obtain ⟨_, ⟨U₁, hU₁, rfl⟩, hxU₁, hU₁sub⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((U₀.ι ''ᵁ W ⊓ G : X.Opens) : Set X) from ⟨⟨⟨x, hxU₀⟩, hflatx, rfl⟩, hxG⟩)
      (U₀.ι ''ᵁ W ⊓ G).isOpen
  have hle : U₁ ≤ U₀ := fun z hz => by
    obtain ⟨w, -, rfl⟩ := (hU₁sub hz).1
    exact w.2
  refine ⟨U₁, hU₁, hle, hxU₁, fun z hz => (hU₁sub hz).2, ?_⟩
  refine (Flat.iff_flat_stalkMap _).mpr fun z =>
    (flatAt_precomp_openImmersion_iff (X.homOfLE hle) π z).mp ?_
  obtain ⟨w, hw, hwz⟩ := (hU₁sub z.2).1
  have : X.homOfLE hle z = w := by
    apply U₀.ι.isOpenEmbedding.injective
    change (X.homOfLE hle ≫ U₀.ι) z = U₀.ι w
    rw [Scheme.homOfLE_ι]
    exact hwz.symm
  rwa [this]

/-- A ring homomorphism `θ : R → Γ(X, U)` with `U` affine is flat if the composite
`U ≅ Spec Γ(X, U) ⟶ Spec R` is flat. -/
private theorem IsAffineOpen.flat_of_flat_isoSpec_hom_comp {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {R : Type u} [CommRing R] (θ : R →+* Γ(X, U))
    (h : Flat (hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom θ))) : θ.Flat := by
  have h' : Flat (hU.isoSpec.inv ≫ hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom θ)) :=
    inferInstance
  rw [Iso.inv_hom_id_assoc] at h'
  exact (HasRingHomProperty.Spec_iff (P := @Flat)).mp h'

/-- **An affine chart at a Cohen–Macaulay point, flat and quasi-finite over affine space.** Let
`f` be flat and locally of finite presentation, Cohen–Macaulay at `x`, with fibre of dimension
`n` at `x`, and let `V ∋ f(x)` be an affine open. Inside any open neighbourhood `G` of `x` there
is an affine open `U ∋ x` with `f(U) ⊆ V` and a flat quasi-finite homomorphism
`Γ(S, V)[x_1, …, x_n] → Γ(X, U)` over `Γ(S, V)`. -/
public theorem exists_affine_flat_quasiFinite_mvPolynomial {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] (hf : ∀ s : S, IsLocallyNoetherian (f.fiber s))
    (x : X) (hx : Scheme.Hom.IsCohenMacaulayAt f hf x) (n : ℕ)
    (hn : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (n : WithBot ℕ∞))
    (G : X.Opens) (hxG : x ∈ G) (V : S.Opens) (hV : IsAffineOpen V) (hxV : f x ∈ V) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (hUV : U ≤ f ⁻¹ᵁ V), x ∈ U ∧ U ≤ G ∧
      ∃ θ : MvPolynomial (ULift.{u} (Fin n)) Γ(S, V) →+* Γ(X, U),
        θ.comp MvPolynomial.C = (f.appLE V U hUV).hom ∧ θ.QuasiFinite ∧ θ.Flat := by
  let V' : S.affineOpens := ⟨V, hV⟩
  obtain ⟨U₀, hxU₀, hU₀V, π, hfac, hprops⟩ :=
    exists_affineOpen_quasiFinite_affineSpace_factorization f x V' hxV n hn
  let j : AffineSpace (ULift.{u} (Fin n)) V'.1.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) S :=
    AffineSpace.map (ULift.{u} (Fin n)) V'.1.ι
  have : IsOpenImmersion j := affineSpace_map_isOpenImmersion _ _
  have : LocallyOfFiniteType π := hprops.1.1
  have : LocallyQuasiFinite π := hprops.2
  let g := π ≫ j
  have hfacS : g ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = U₀.1.ι ≫ f :=
    (affineSpace_map_ι_comp_over _ V'.1 π).trans hfac
  obtain ⟨hLFTg, hLQFg⟩ :=
    locallyOfFiniteType_and_locallyQuasiFinite_comp_affineSpace_map (ULift.{u} (Fin n)) V'.1 π
  have hflatx : AlgebraicGeometry.IsFlatAt π.toLRSHom.toShHom ⟨x, hxU₀⟩ := by
    have h4 := ((isCohenMacaulayAt_tfae f x n hn).out 1 4).mp hx
    exact (flatAt_postcomp_openImmersion_iff π j ⟨x, hxU₀⟩).mpr (h4 U₀.1 hxU₀ g hfacS
      (((AlgebraicGeometry.forall_quasiFiniteAt_iff g).mpr ⟨hLFTg, hLQFg⟩) ⟨x, hxU₀⟩))
  have : LocallyOfFinitePresentation π := by
    have : LocallyOfFinitePresentation g := by
      have : LocallyOfFinitePresentation (g ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S)) := by
        rw [hfacS]
        infer_instance
      exact AlgebraicGeometry.locallyOfFinitePresentation_of_comp g
        (AffineSpace (ULift.{u} (Fin n)) S ↘ S)
    exact AlgebraicGeometry.locallyOfFinitePresentation_of_comp π j
  obtain ⟨U₁, hU₁, hle, hxU₁, hU₁G, hflat⟩ :=
    exists_affineOpen_flat_homOfLE_comp π hxU₀ hflatx hxG
  have hU₁V : U₁ ≤ f ⁻¹ᵁ V'.1 := hle.trans hU₀V
  let π₁ := X.homOfLE hle ≫ π
  have hfac₁ : π₁ ≫ (AffineSpace.over (ULift.{u} (Fin n)) V'.1.toScheme).hom ≫ V'.1.ι =
      U₁.ι ≫ f := by
    dsimp [π₁]
    rw [Category.assoc, hfac, ← Category.assoc, Scheme.homOfLE_ι]
  have hLQF₁ : LocallyQuasiFinite π₁ := by
    dsimp [π₁]
    infer_instance
  have hflat₁ : Flat π₁ := hflat
  obtain ⟨θ, hθ, hbase, hqf⟩ := affineFactorizationAlgHom f V' ⟨U₁, hU₁⟩ hU₁V n π₁ hfac₁ hLQF₁
  refine ⟨U₁, hU₁, hU₁V, hxU₁, hU₁G, θ, hbase, hqf, ?_⟩
  have : IsIso (AffineSpace.map (ULift.{u} (Fin n)) V'.2.isoSpec.hom) :=
    ⟨⟨AffineSpace.map (ULift.{u} (Fin n)) V'.2.isoSpec.inv,
      by rw [← AffineSpace.map_comp, Iso.hom_inv_id, AffineSpace.map_id],
      by rw [← AffineSpace.map_comp, Iso.inv_hom_id, AffineSpace.map_id]⟩⟩
  have hcomp : Flat (hU₁.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom θ)) := by
    rw [hθ]
    infer_instance
  exact hU₁.flat_of_flat_isoSpec_hom_comp θ hcomp

/-- **Cohen–Macaulayness at a point of an affine chart from the fibre algebra.** Let `f` be flat
and locally of finite presentation and `U ⊆ f⁻¹(V)` affine opens. If the localization of the fibre
algebra `κ(z ∩ Γ(S, V)) ⊗ Γ(X, U)` at a prime `Q` over the prime `z` of `Γ(X, U)` is a
Cohen–Macaulay local ring, then `f` is Cohen–Macaulay at the point of `U` given by `z`. -/
public theorem isCohenMacaulayAt_fromSpec_of_isCohenMacaulayLocalRing {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (hf : ∀ s : S, IsLocallyNoetherian (f.fiber s)) (V : S.affineOpens) (U : X.affineOpens)
    (e : U.1 ≤ f ⁻¹ᵁ V.1) (z : PrimeSpectrum Γ(X, U.1)) :
    letI : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 e).hom.toAlgebra
    ∀ (Q : Ideal ((z.asIdeal.under Γ(S, V.1)).Fiber Γ(X, U.1))) [Q.IsPrime]
      (_ : Q.comap (Algebra.TensorProduct.includeRight :
        Γ(X, U.1) →ₐ[Γ(S, V.1)] (z.asIdeal.under Γ(S, V.1)).Fiber Γ(X, U.1)).toRingHom =
          z.asIdeal) [IsNoetherianRing (Localization.AtPrime Q)],
      IsCohenMacaulayLocalRing (Localization.AtPrime Q) →
        Scheme.Hom.IsCohenMacaulayAt f hf (U.2.fromSpec z) := by
  let : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 e).hom.toAlgebra
  intro Q _ hQ _ hCM
  have : Algebra.FiniteType Γ(S, V.1) Γ(X, U.1) := f.finiteType_appLE V.2 U.2 e
  let m := Spec.map (f.appLE V.1 U.1 e)
  have : LocallyOfFiniteType m :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (f.finiteType_appLE V.2 U.2 e)
  have : IsLocallyNoetherian (f.fiber (f (U.2.fromSpec z))) := hf _
  have : IsLocallyNoetherian (m.fiber (m z)) :=
    isLocallyNoetherian_fiber_of_locallyOfFiniteType m _
  have : IsNoetherianRing (((affineSpecMap Γ(S, V.1) Γ(X, U.1)).fiber
      ((affineSpecMap Γ(S, V.1) Γ(X, U.1)) z)).presheaf.stalk
        ((affineSpecMap Γ(S, V.1) Γ(X, U.1)).asFiber z)) :=
    noetherianStalk_of_locallyNoetherian _ inferInstance
  exact ⟨(Flat.iff_flat_stalkMap f).mp inferInstance _,
    (fiberCM_iff_fromSpec f V U e z).mpr <|
      (maxCM_fiberChart_iff_CohenMacaulayLocalRing (R := Γ(S, V.1)) (A := Γ(X, U.1)) z).1.mp <|
        (isMaximalCohenMacaulay_fiber_localization_iff z.asIdeal Q hQ).mpr <|
          (maxCM_self_iff_CohenMacaulayLocalRing (Localization.AtPrime Q)).mpr hCM⟩

end AlgebraicGeometry
