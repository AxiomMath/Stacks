module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.ProjectiveSpacePairing
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.GradedIsoCohomology
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Comparison
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.HgroupSchemeTransport

/-!
# The multiplication pairing on the top cohomology across a graded ring isomorphism

Let `ψ : 𝒮 →+*ᵍ A[X₀, …, Xₙ]` be an isomorphism of graded rings. The twist comparison
`θ : (Proj.map ψ)^* 𝒪_{Proj 𝒮}(d) ⟶ 𝒪_{ℙⁿ_A}(d)` intertwines multiplication by a homogeneous
element `a` with multiplication by `ψ a`, so the multiplication pairing on the top cohomology of
`Proj 𝒮`, taken against the monomials in the preimages `ψ⁻¹(Xᵢ)`, is bijective as it is on
`ℙⁿ_A`.

## Main results

* `Stacks.ProjTwistComparison.twistMap_twistMulLeftIntOf`: `θ` intertwines multiplication by
  `a` with multiplication by `ψ a`.
* `ProjectiveSpacePairing.bijective_monomialPairingOf`: the multiplication pairing on
  `Hⁿ(Proj 𝒮, 𝒪(d))` is bijective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj HomogeneousIdeal

universe u

attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.ProjTwistComparison

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ)

/-- The image of a homogeneous element under a graded ring homomorphism. -/
def mapHomogeneous {k : ℕ} (a : 𝒜 k) : ℬ k := ⟨φ a, φ.map_mem a.2⟩

/-- The pointwise comparison intertwines multiplication by `a` with multiplication by `φ a`. -/
theorem pushforwardTwistMap_twistMulLeftIntOf {k : ℕ} (a : 𝒜 k) (d e : ℤ)
    (he : (k : ℤ) + d = e) :
    twistMulLeftIntOf 𝒜 a d e he ≫ pushforwardTwistMap φ hφ e =
      pushforwardTwistMap φ hφ d ≫
        (Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map φ hφ)).map
          (twistMulLeftIntOf ℬ (mapHomogeneous φ a) d e he) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun s => Subtype.ext (funext fun y => ?_)
  show fibreMap φ hφ y.1 (LocalizedModule.map _ (LinearMap.mulLeft A (a : A)) (s.1 ⟨_, y.2⟩)) =
    LocalizedModule.map _ (LinearMap.mulLeft B (φ a)) (fibreMap φ hφ y.1 (s.1 ⟨_, y.2⟩))
  induction s.1 ⟨_, y.2⟩ using LocalizedModule.induction_on with
  | h m t =>
    refine (congrArg (fibreMap φ hφ y.1) (LocalizedModule.map_mk
      (ProjectiveSpectrum.comapFun φ hφ y.1).asHomogeneousIdeal.toIdeal.primeCompl
      (LinearMap.mulLeft A (a : A)) m t)).trans ?_
    refine ((fibreMap_mk φ hφ y.1 _ t).trans ?_).trans
      (congrArg (LocalizedModule.map _ (LinearMap.mulLeft B (φ a)))
        (fibreMap_mk φ hφ y.1 m t)).symm
    refine Eq.trans ?_ (LocalizedModule.map_mk y.1.asHomogeneousIdeal.toIdeal.primeCompl
      (LinearMap.mulLeft B (φ a)) (φ m) ⟨φ t, t.2⟩).symm
    simp only [LinearMap.mulLeft_apply, map_mul]

/-- **The twist comparison intertwines multiplication by `a` with multiplication by `φ a`.** -/
theorem twistMap_twistMulLeftIntOf {k : ℕ} (a : 𝒜 k) (d e : ℤ) (he : (k : ℤ) + d = e) :
    (Scheme.Modules.pullback (AlgebraicGeometry.Proj.map φ hφ)).map
        (twistMulLeftIntOf 𝒜 a d e he) ≫ twistMap φ hφ e =
      twistMap φ hφ d ≫ twistMulLeftIntOf ℬ (mapHomogeneous φ a) d e he := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (AlgebraicGeometry.Proj.map φ hφ)
  apply (adj.homEquiv _ _).injective
  refine (adj.homEquiv_naturality_left _ _).trans ?_
  refine Eq.trans ?_ (adj.homEquiv_naturality_right _ _).symm
  rw [homEquiv_twistMap, homEquiv_twistMap]
  exact pushforwardTwistMap_twistMulLeftIntOf φ hφ a d e he

end Stacks.ProjTwistComparison


namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.ProjectiveSpacePairing

open Stacks.ProjTwistComparison Stacks.Cohomology.ModuleComparison

section General

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (ψ : 𝒜 →+*ᵍ ℬ) (χ : ℬ →+*ᵍ 𝒜) (hψχ : ∀ b, ψ (χ b) = b) (hχψ : ∀ a, χ (ψ a) = a)

/-- The comparison of the cohomology of the twists of `Proj 𝒜` with that of the twists of
`Proj ℬ`, along a graded ring isomorphism `ψ : 𝒜 ≅ ℬ`. -/
abbrev twistHgroupHom (q : ℕ) (t : ℤ) :
    Hgroup (AlgebraicGeometry.Proj 𝒜).ringCatSheaf ⊤ q (twistingSheaf 𝒜 t) ⟶
      Hgroup (AlgebraicGeometry.Proj ℬ).ringCatSheaf ⊤ q (twistingSheaf ℬ t) :=
  haveI := isIso_projMap_of_inverse ψ χ hψχ hχψ
  (hfunctorPullbackIso (asIso (AlgebraicGeometry.Proj.map ψ
      (irrelevant_le_map_of_inverse ψ χ hψχ))) q).inv.app (twistingSheaf 𝒜 t) ≫
    (Hfunctor (AlgebraicGeometry.Proj ℬ).ringCatSheaf ⊤ q).map
      (twistMap ψ (irrelevant_le_map_of_inverse ψ χ hψχ) t)

/-- The comparison `twistHgroupHom` of cohomology groups is an isomorphism. -/
theorem isIso_twistHgroupHom (q : ℕ) (t : ℤ) : IsIso (twistHgroupHom ψ χ hψχ hχψ q t) := by
  have := isIso_projMap_of_inverse ψ χ hψχ hχψ
  have h1 : IsIso (twistMap ψ (irrelevant_le_map_of_inverse ψ χ hψχ) t) :=
    isIso_twistMap_of_inverse ψ χ hψχ hχψ t
  exact @IsIso.comp_isIso _ _ _ _ _ _ _
    ⟨⟨_, Iso.inv_hom_id_app _ _, Iso.hom_inv_id_app _ _⟩⟩
    (@Functor.map_isIso _ _ _ _ _ _ _ _ h1)

omit [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B]
  [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- A natural transformation followed by the image of a comparison, against a morphism and its
counterpart under the comparison. -/
theorem natTrans_comp_map_naturality {C D E : Type*} [Category C] [Category D] [Category E]
    (P : C ⥤ D) (H₁ : C ⥤ E) (H₂ : D ⥤ E) (η : H₁ ⟶ P ⋙ H₂) {X Y : C} {X' Y' : D}
    (f : X ⟶ Y) (θX : P.obj X ⟶ X') (θY : P.obj Y ⟶ Y') (f' : X' ⟶ Y')
    (h : P.map f ≫ θY = θX ≫ f') :
    H₁.map f ≫ η.app Y ≫ H₂.map θY = (η.app X ≫ H₂.map θX) ≫ H₂.map f' := by
  rw [← Category.assoc, η.naturality, Functor.comp_map, Category.assoc, Category.assoc,
    ← H₂.map_comp, h, H₂.map_comp]

/-- **The comparison of top cohomologies intertwines multiplication by `a` with multiplication
by `ψ a`.** -/
theorem twistHgroupHom_naturality (q : ℕ) {k : ℕ} (a : 𝒜 k) (d e : ℤ)
    (he : (k : ℤ) + d = e) :
    (Hfunctor (AlgebraicGeometry.Proj 𝒜).ringCatSheaf ⊤ q).map (twistMulLeftIntOf 𝒜 a d e he) ≫
        twistHgroupHom ψ χ hψχ hχψ q e =
      twistHgroupHom ψ χ hψχ hχψ q d ≫
        (Hfunctor (AlgebraicGeometry.Proj ℬ).ringCatSheaf ⊤ q).map
          (twistMulLeftIntOf ℬ (mapHomogeneous ψ a) d e he) :=
  have := isIso_projMap_of_inverse ψ χ hψχ hχψ
  natTrans_comp_map_naturality _ _ _ _ _ _ _ _
    (twistMap_twistMulLeftIntOf ψ (irrelevant_le_map_of_inverse ψ χ hψχ) a d e he)

end General


section Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {m : ℕ} {σ : Type u} {S : Type u} [CommRing S]
  [SetLike σ S] [AddSubgroupClass σ S] {𝒮 : ℕ → σ} [GradedRing 𝒮]
  (ψ : 𝒮 →+*ᵍ Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading A (m + 1))
  (χ : Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading A (m + 1) →+*ᵍ 𝒮)
  (hψχ : ∀ b, ψ (χ b) = b) (hχψ : ∀ a, χ (ψ a) = a)

/-- The multiplication pairing on `ℙⁿ_A`, with the cohomology read over the structure sheaf of
the scheme `ℙⁿ_A`. -/
def monomialPairing' (k : ℕ) (d : ℤ) (hd : (k : ℤ) + d = -((m + 1 : ℕ) : ℤ) - 1)
    (c : Hgroup (AlgebraicGeometry.Proj
      (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading A (m + 1))).ringCatSheaf ⊤ (m + 1)
      (twistingSheaf (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading A (m + 1)) d)) :
    Monomials m k →
      Hgroup (AlgebraicGeometry.Proj
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading A (m + 1))).ringCatSheaf ⊤ (m + 1)
        (twistingSheaf (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading A (m + 1))
          (-((m + 1 : ℕ) : ℤ) - 1)) :=
  monomialPairing A m k d hd c

/-- The multiplication pairing `monomialPairing'` on the top cohomology of `ℙⁿ_A` is bijective. -/
theorem bijective_monomialPairing' (k : ℕ) (d : ℤ) (hd : (k : ℤ) + d = -((m + 1 : ℕ) : ℤ) - 1) :
    Function.Bijective (monomialPairing' (A := A) k d hd) :=
  bijective_monomialPairing k d hd

/-- **The multiplication pairing on the top cohomology of `Proj 𝒮`**, for `𝒮` isomorphic to
`A[X₀, …, Xₙ]` as a graded ring, against the monomials in the preimages of the coordinates. -/
def monomialPairingOf (k : ℕ) (d : ℤ) (hd : (k : ℤ) + d = -((m + 1 : ℕ) : ℤ) - 1)
    (c : Hgroup (AlgebraicGeometry.Proj 𝒮).ringCatSheaf ⊤ (m + 1) (twistingSheaf 𝒮 d)) :
    Monomials m k →
      Hgroup (AlgebraicGeometry.Proj 𝒮).ringCatSheaf ⊤ (m + 1)
        (twistingSheaf 𝒮 (-((m + 1 : ℕ) : ℤ) - 1)) :=
  fun α => ((Hfunctor (AlgebraicGeometry.Proj 𝒮).ringCatSheaf ⊤ (m + 1)).map
    (twistMulLeftIntOf 𝒮 (mapHomogeneous χ (monomialElt (A := A) α)) d _ hd)).hom c

/-- The comparison `twistHgroupHom` carries the pairing `monomialPairingOf` on `Proj 𝒮` to the
pairing `monomialPairing'` on `ℙⁿ_A`. -/
theorem twistHgroupHom_monomialPairingOf (k : ℕ) (d : ℤ)
    (hd : (k : ℤ) + d = -((m + 1 : ℕ) : ℤ) - 1)
    (c : Hgroup (AlgebraicGeometry.Proj 𝒮).ringCatSheaf ⊤ (m + 1) (twistingSheaf 𝒮 d))
    (α : Monomials m k) :
    (twistHgroupHom ψ χ hψχ hχψ (m + 1) _).hom (monomialPairingOf χ k d hd c α) =
      monomialPairing' k d hd ((twistHgroupHom ψ χ hψχ hχψ (m + 1) d).hom c) α := by
  refine (congrArg (fun φ => φ.hom c) (twistHgroupHom_naturality ψ χ hψχ hχψ (m + 1)
    (mapHomogeneous χ (monomialElt (A := A) α)) d _ hd)).trans ?_
  have hx : mapHomogeneous ψ (mapHomogeneous χ (monomialElt (A := A) α)) = monomialElt α :=
    Subtype.ext (hψχ _)
  exact congrArg (fun x => ((Hfunctor (AlgebraicGeometry.Proj
      (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading A (m + 1))).ringCatSheaf ⊤ (m + 1)).map
      (twistMulLeftIntOf _ x d _ hd)).hom ((twistHgroupHom ψ χ hψχ hχψ (m + 1) d).hom c)) hx

include ψ hψχ hχψ in
/-- **The multiplication pairing on the top cohomology of `Proj 𝒮` is bijective**, for `𝒮`
isomorphic to `A[X₀, …, Xₙ]` as a graded ring. -/
theorem bijective_monomialPairingOf (k : ℕ) (d : ℤ)
    (hd : (k : ℤ) + d = -((m + 1 : ℕ) : ℤ) - 1) :
    Function.Bijective (monomialPairingOf χ k d hd) := by
  have hρ : ∀ t, Function.Bijective (twistHgroupHom ψ χ hψχ hχψ (m + 1) t).hom := fun t =>
    have := isIso_twistHgroupHom ψ χ hψχ hχψ (m + 1) t
    ConcreteCategory.bijective_of_isIso _
  have hP := bijective_monomialPairing' (A := A) (m := m) k d hd
  have key := twistHgroupHom_monomialPairingOf ψ χ hψχ hχψ k d hd
  refine ⟨fun c c' h => (hρ d).1 <| hP.1 <| funext fun α => (key c α).symm.trans
    ((congrArg (twistHgroupHom ψ χ hψχ hχψ (m + 1) _).hom (congrFun h α)).trans (key c' α)),
    fun g => ?_⟩
  obtain ⟨x, hx⟩ := hP.2 (fun α => (twistHgroupHom ψ χ hψχ hχψ (m + 1) _).hom (g α))
  obtain ⟨c, rfl⟩ := (hρ d).2 x
  exact ⟨c, funext fun α => (hρ _).1 ((key c α).trans (congrFun hx α))⟩

end Polynomial

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.ProjectiveSpacePairing

end
