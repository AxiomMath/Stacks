module

public import StacksFrontier.AlgebraicGeometry.AffineGradedTilde.GlobalSections
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde
public import StacksFrontier.AlgebraicGeometry.Morphism.TwistExists
public import StacksFrontier.AlgebraicGeometry.ProjTwistCompare.NotIsoExample

/-!
# The comparison maps of Stacks 07ZG need not be isomorphisms

The map `θ_n : r_ψ^*𝒪_X(n) ⟶ 𝒪_Y(n)` that Stacks 07ZG attaches to a map `ψ : 𝒜 ⟶ ℬ` of
quasi-coherent graded algebras on a scheme `S` restricts, over an affine open `U` of `S`, to the
comparison map of Tag 01MY for the graded rings of sections over `U`. So it is an isomorphism
only if those are (`isIso_twistMap_sectionHom_of_isIso_relativeTwistMap`).

Applied to the example of `StacksFrontier.AlgebraicGeometry.ProjTwistCompare.NotIsoExample`, read as
quasi-coherent graded algebras on `S = Spec R` (`StacksDraft.AlgebraicGeometry.AffineGradedTilde`),
this gives a map `ψ : 𝒜 ⟶ ℬ` of quasi-coherent graded `𝒪_S`-algebras which is surjective in every
degree, while `θ₁` is not an isomorphism. This is the assertion "surjective but not isomorphisms in
general (even if `𝒜 ⟶ ℬ` is surjective)" of Stacks 07ZI (3), and the scheme case of the same
assertion in Stacks 085H (3).

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistCompare.isIso_twistMap_sectionHom_of_isIso_relativeTwistMap`:
  `θ_n` iso implies the comparison of Tag 01MY over each affine open is.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.NotIsoExample.epi_sheafHom_app`: the map of
  quasi-coherent graded algebras is surjective in every degree.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.NotIsoExample.not_isIso_relativeTwistMap`: `θ₁` is
  not an isomorphism.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 07ZI](https://stacks.math.columbia.edu/tag/07ZI)
* [Stacks Project, Tag 085H](https://stacks.math.columbia.edu/tag/085H)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.AlgebraicGeometry.ProjTwistCompare

open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGTwist

/-! ### The comparison maps of Stacks 07ZG on an affine open -/

/-- **If the map `θ_n` of Stacks 07ZG is an isomorphism, so is the comparison map of Tag 01MY for
the graded rings of sections over any affine open of the base.** The restriction of `θ_n` to the
piece over `U` is that comparison map conjugated by isomorphisms
(`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap_chart`), and pulling back along an
isomorphism reflects isomorphisms. -/
theorem isIso_twistMap_sectionHom_of_isIso_relativeTwistMap
    {S : _root_.AlgebraicGeometry.Scheme.{u}} {A B : SheafGradedAlgebra S}
    (ψ : SheafGradedAlgebraHom A B) (n : ℤ) (U : S.affineOpens)
    [IsIso (relativeTwistMap ψ n)] :
    IsIso (twistMap (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) n) := by
  have h1 : IsIso ((_root_.AlgebraicGeometry.Scheme.Modules.pullback (pieceIncl ψ U)).map
      (relativeTwistMap ψ n)) := inferInstance
  rw [relativeTwistMap_chart] at h1
  unfold relativeTwistChart at h1
  have h2 := @IsIso.of_isIso_comp_left _ _ _ _ _ (chartSourceIso ψ n U).hom _ _ h1
  have h3 := @IsIso.of_isIso_comp_right _ _ _ _ _ _ (chartTargetIso ψ n U).inv _ h2
  exact isIso_of_reflects_iso _
    (_root_.AlgebraicGeometry.Scheme.Modules.pullback (chartDomainIso ψ U).inv)

/-! ### Graded ring isomorphisms -/

section Graded

variable {A B C : Type u} {σ τ ρ : Type u} [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike ρ C] [AddSubgroupClass ρ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- A homomorphism of graded rings which is surjective in every degree satisfies the hypothesis of
`AlgebraicGeometry.Proj.map`. -/
theorem irrelevant_le_map_of_surjOn (f : 𝒜 →+*ᵍ ℬ)
    (hf : ∀ (n : ℕ) (b : B), b ∈ ℬ n → ∃ a ∈ 𝒜 n, f a = b) :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f := by
  rw [← toIdeal_le_toIdeal_iff, HomogeneousIdeal.toIdeal_map,
    HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi b hb
  obtain ⟨a, ha, rfl⟩ := hf i b hb
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ hi ha)

/-- If `e'.comp e` is the identity, the irrelevant ideal of `𝒜` lies in the image under `e'` of the
irrelevant ideal of `ℬ`. -/
private theorem irrelevant_le_map_of_comp_eq_id (e : 𝒜 →+*ᵍ ℬ) (e' : ℬ →+*ᵍ 𝒜)
    (h : e'.comp e = GradedRingHom.id 𝒜) :
    HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant ℬ).map e' :=
  irrelevant_le_map_of_surjOn e' fun n a ha =>
    ⟨e a, e.map_mem ha, by rw [← GradedRingHom.comp_apply, h]; rfl⟩

/-- `AlgebraicGeometry.Proj.map` depends only on the homomorphism. -/
theorem proj_map_congr {f g : 𝒜 →+*ᵍ ℬ} (h : f = g)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g) :
    _root_.AlgebraicGeometry.Proj.map f hf = _root_.AlgebraicGeometry.Proj.map g hg := by
  subst h
  rfl

/-- A graded ring isomorphism induces an isomorphism of homogeneous spectra. -/
theorem isIso_proj_map_of_inverse (e : 𝒜 →+*ᵍ ℬ) (e' : ℬ →+*ᵍ 𝒜)
    (h₁ : e'.comp e = GradedRingHom.id 𝒜) (h₂ : e.comp e' = GradedRingHom.id ℬ)
    (he : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map e) :
    IsIso (_root_.AlgebraicGeometry.Proj.map e he) := by
  have he' := irrelevant_le_map_of_comp_eq_id e e' h₁
  refine ⟨⟨_root_.AlgebraicGeometry.Proj.map e' he', ?_, ?_⟩⟩
  · rw [← _root_.AlgebraicGeometry.Proj.map_comp, proj_map_congr h₂ _ (by simp),
      _root_.AlgebraicGeometry.Proj.map_id]
  · rw [← _root_.AlgebraicGeometry.Proj.map_comp, proj_map_congr h₁ _ (by simp),
      _root_.AlgebraicGeometry.Proj.map_id]

end Graded

/-! ### The example, on `Spec R` -/

namespace NotIsoExample

variable (R : Type u) [CommRing R]

open Stacks.AffineGradedTilde

/-- The quotient map `ψ : A ⟶ B`, as a homomorphism of `R`-algebras. -/
def psiAlg : RingA R →ₐ[R] RingB R := Ideal.Quotient.factorₐ R (relA_le_relB R)

/-- `psiAlg R` maps the degree `n` piece of `A` into the degree `n` piece of `B`. -/
theorem psiAlg_mem (n : ℕ) (a : RingA R) (ha : a ∈ gradA R n) : psiAlg R a ∈ gradB R n :=
  (psi R).map_mem ha

/-- **The map `ψ : A~ ⟶ B~` of quasi-coherent graded algebras on `Spec R`.** -/
abbrev sheafHom :=
  sheafGradedAlgebraHom (R := CommRingCat.of R) (gradA R) (gradB R) (psiAlg R) (psiAlg_mem R)

/-- **`ψ : A~ ⟶ B~` is surjective in every degree.** -/
theorem epi_sheafHom_app (n : ℤ) : Epi ((sheafHom R).app n) := by
  have hs : Function.Surjective (gradedPieceMap (R := CommRingCat.of R) (gradA R) (gradB R)
      (psiAlg R) (psiAlg_mem R) n) := by
    rintro ⟨b, hb⟩
    match n, hb with
    | .ofNat k, hb =>
        obtain ⟨a, ha, rfl⟩ := surjOn_psi R k hb
        exact ⟨⟨a, ha⟩, rfl⟩
    | .negSucc _, hb =>
        refine ⟨0, Subtype.ext ?_⟩
        exact (map_zero _).trans (show b = 0 from hb).symm
  have : Epi (pieceModuleMap (R := CommRingCat.of R) (gradA R) (gradB R) (psiAlg R)
      (psiAlg_mem R) n) := (ModuleCat.epi_iff_surjective _).2 hs
  have := (_root_.AlgebraicGeometry.tilde.adjunction (R := CommRingCat.of R)).isLeftAdjoint
  exact (_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of R)).map_epi _

/-! ### The comparison map on `Spec R` -/

/-- The identification `A ≅ Γ(A~)` of graded rings. -/
abbrev eA := gradedGlobalSectionsHom (R := CommRingCat.of R) (gradA R)

/-- The inverse identification `Γ(A~) ≅ A`. -/
abbrev eAinv := gradedGlobalSectionsInv (R := CommRingCat.of R) (gradA R)

/-- The identification `B ≅ Γ(B~)` of graded rings. -/
abbrev eB := gradedGlobalSectionsHom (R := CommRingCat.of R) (gradB R)

/-- The inverse identification `Γ(B~) ≅ B`. -/
abbrev eBinv := gradedGlobalSectionsInv (R := CommRingCat.of R) (gradB R)

/-- The map `ψ` on the graded rings of global sections. -/
abbrev psiGamma := (sheafHom R).sectionHom ⊤

/-- On global sections, `ψ` is `psi R` conjugated by the identifications `eA R` and `eB R`. -/
theorem psiGamma_eq : psiGamma R = ((eB R).comp (psi R)).comp (eAinv R) := by
  refine GradedRingHom.ext fun z => ?_
  obtain ⟨x, rfl⟩ := (globalSectionsRingEquiv (R := CommRingCat.of R) (gradA R)).surjective z
  refine (sectionHom_globalSectionsRingEquiv (R := CommRingCat.of R) (gradA R) (gradB R)
    (psiAlg R) (psiAlg_mem R) x).trans ?_
  show _ = globalSectionsRingEquiv (R := CommRingCat.of R) (gradB R) (psi R
    ((globalSectionsRingEquiv (R := CommRingCat.of R) (gradA R)).symm
      (globalSectionsRingEquiv (R := CommRingCat.of R) (gradA R) x)))
  rw [RingEquiv.symm_apply_apply]
  rfl

/-- `eAinv R` is a left inverse of `eA R`. -/
theorem eAinv_comp_eA : (eAinv R).comp (eA R) = GradedRingHom.id _ :=
  GradedRingHom.ext fun x =>
    (globalSectionsRingEquiv (R := CommRingCat.of R) (gradA R)).symm_apply_apply x

/-- `eAinv R` is a right inverse of `eA R`. -/
theorem eA_comp_eAinv : (eA R).comp (eAinv R) = GradedRingHom.id _ :=
  GradedRingHom.ext fun z =>
    (globalSectionsRingEquiv (R := CommRingCat.of R) (gradA R)).apply_symm_apply z

/-- `eBinv R` is a left inverse of `eB R`. -/
theorem eBinv_comp_eB : (eBinv R).comp (eB R) = GradedRingHom.id _ :=
  GradedRingHom.ext fun x =>
    (globalSectionsRingEquiv (R := CommRingCat.of R) (gradB R)).symm_apply_apply x

/-- `eBinv R` is a right inverse of `eB R`. -/
theorem eB_comp_eBinv : (eB R).comp (eBinv R) = GradedRingHom.id _ :=
  GradedRingHom.ext fun z =>
    (globalSectionsRingEquiv (R := CommRingCat.of R) (gradB R)).apply_symm_apply z

/-- The irrelevant ideal of `A` is contained in the image under `eAinv R` of the irrelevant ideal
of `Γ(A~)`. -/
theorem irrelevant_le_map_eAinv :
    HomogeneousIdeal.irrelevant (gradA R) ≤
      (HomogeneousIdeal.irrelevant ((sheafGradedAlgebra (R := CommRingCat.of R) (gradA R)).grading
        ⊤)).map (eAinv R) :=
  irrelevant_le_map_of_comp_eq_id (eA R) (eAinv R) (eAinv_comp_eA R)

/-- The irrelevant ideal of `Γ(B~)` is contained in the image under `eB R` of the irrelevant ideal
of `B`. -/
theorem irrelevant_le_map_eB :
    HomogeneousIdeal.irrelevant ((sheafGradedAlgebra (R := CommRingCat.of R) (gradB R)).grading ⊤) ≤
      (HomogeneousIdeal.irrelevant (gradB R)).map (eB R) :=
  irrelevant_le_map_of_comp_eq_id (eBinv R) (eB R) (eB_comp_eBinv R)

/-- The irrelevant ideal of `Γ(B~)` is contained in the image of the irrelevant ideal of `Γ(A~)`
under the composite of `eAinv R`, `psi R` and `eB R`. -/
theorem irrelevant_le_map_comp_psi :
    HomogeneousIdeal.irrelevant ((sheafGradedAlgebra (R := CommRingCat.of R) (gradB R)).grading ⊤) ≤
      (HomogeneousIdeal.irrelevant ((sheafGradedAlgebra (R := CommRingCat.of R) (gradA R)).grading
        ⊤)).map (((eB R).comp (psi R)).comp (eAinv R)) :=
  HomogeneousIdeal.irrelevant_le_map_comp (irrelevant_le_map_eAinv R)
    (HomogeneousIdeal.irrelevant_le_map_comp (irrelevant_le_map R) (irrelevant_le_map_eB R))

/-- The irrelevant ideal of `Γ(B~)` is contained in the image under `psiGamma R` of the irrelevant
ideal of `Γ(A~)`. -/
theorem irrelevant_le_map_psiGamma :
    HomogeneousIdeal.irrelevant ((sheafGradedAlgebra (R := CommRingCat.of R) (gradB R)).grading ⊤) ≤
      (HomogeneousIdeal.irrelevant ((sheafGradedAlgebra (R := CommRingCat.of R) (gradA R)).grading
        ⊤)).map (psiGamma R) :=
  (psiGamma_eq R) ▸ irrelevant_le_map_comp_psi R

/-- `Proj Γ(B~) ⟶ Proj Γ(A~)` is an isomorphism. -/
theorem isIso_projMap_psiGamma :
    IsIso (_root_.AlgebraicGeometry.Proj.map (psiGamma R) (irrelevant_le_map_psiGamma R)) := by
  rw [proj_map_congr (psiGamma_eq R) _ (irrelevant_le_map_comp_psi R),
    _root_.AlgebraicGeometry.Proj.map_comp _ _ (irrelevant_le_map_eAinv R)
      (HomogeneousIdeal.irrelevant_le_map_comp (irrelevant_le_map R) (irrelevant_le_map_eB R)),
    _root_.AlgebraicGeometry.Proj.map_comp _ _ (irrelevant_le_map R) (irrelevant_le_map_eB R)]
  have := isIso_proj_map_of_inverse (eB R) (eBinv R) (eBinv_comp_eB R) (eB_comp_eBinv R)
    (irrelevant_le_map_eB R)
  have := isIso_proj_map_of_inverse (eAinv R) (eA R) (eA_comp_eAinv R) (eAinv_comp_eA R)
    (irrelevant_le_map_eAinv R)
  infer_instance

variable [Nontrivial R]

/-- **The comparison map `θ₁ : r_ψ^*𝒪(1) ⟶ 𝒪(1)` of Stacks 07ZG for `ψ : A~ ⟶ B~` on `Spec R` is
not an isomorphism**, although `ψ` is surjective in every degree (`epi_sheafHom_app`). -/
@[stacks 085H "(3), second half: the maps θ are not isomorphisms in general, even if A → B is surjective: A = R[x,y]/(x²) with deg x = 1, deg y = 2, B = A/(x) on Spec R, θ₁ is not an iso"]
theorem not_isIso_relativeTwistMap :
    ¬ IsIso (relativeTwistMap (sheafHom R) ((1 : ℕ) : ℤ)) := by
  intro h
  have := h
  have := isIso_twistMap_sectionHom_of_isIso_relativeTwistMap (sheafHom R) ((1 : ℕ) : ℤ)
    ⟨⊤, _root_.AlgebraicGeometry.isAffineOpen_top _⟩
  have := isIso_projMap_psiGamma R
  let e := globalSectionsRingEquiv (R := CommRingCat.of R) (gradA R)
  have h2 : e (xA R) * e (xA R) = 0 := by rw [← map_mul, xA_sq, map_zero]
  have hann : ∀ s, s * e (xA R) = 0 → s ∈ Ideal.span {e (xA R)} := by
    intro s hs
    have hs' : e.symm s * xA R = 0 := by
      apply e.injective
      rw [map_mul, e.apply_symm_apply, hs, map_zero]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (mem_span_xA_of_mul_eq_zero R hs')
    rw [← e.apply_symm_apply s, ← hc, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  let a : (sheafGradedAlgebra (R := CommRingCat.of R) (gradA R)).grading ⊤ 1 :=
    ⟨e (xA R), (eA R).map_mem (xA_mem R)⟩
  have ha : psiGamma R a = 0 := by
    show psiGamma R (eA R (xA R)) = 0
    rw [psiGamma_eq]
    show eB R (psi R (eAinv R (eA R (xA R)))) = 0
    rw [← GradedRingHom.comp_apply (eAinv R) (eA R), eAinv_comp_eA]
    show eB R (psi R (xA R)) = 0
    rw [psi_xA, map_zero]
  obtain ⟨pt⟩ : Nonempty (PrimeSpectrum (HomogeneousLocalization.Away (gradB R)
    (psi R (yA R)))) := inferInstance
  let w₀ : ProjectiveSpectrum (gradA R) :=
    (_root_.AlgebraicGeometry.Proj.map (psi R) (irrelevant_le_map R)).base
      ((_root_.AlgebraicGeometry.Proj.awayι (gradB R) (psi R (yA R))
        ((psi R).map_mem (yA_mem R)) two_pos).base pt)
  let w : ProjectiveSpectrum ((sheafGradedAlgebra (R := CommRingCat.of R) (gradA R)).grading ⊤) :=
    (_root_.AlgebraicGeometry.Proj.map (eAinv R) (irrelevant_le_map_eAinv R)).base w₀
  exact not_isIso_twistMap_of_map_eq_zero (irrelevant_le_map_psiGamma R) 1 a ha w
    (mk_ne_zero_of_mul_self_eq_zero _ h2 hann w) inferInstance

end NotIsoExample

end Stacks.AlgebraicGeometry.ProjTwistCompare

end
