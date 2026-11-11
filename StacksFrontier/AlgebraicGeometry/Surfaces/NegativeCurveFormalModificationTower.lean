module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionOfThickeningTower
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionMorphismsAffine
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalCurve.SpaceTower
public import StacksFrontier.AlgebraicGeometry.Surfaces.NegativeCurveAlgebraization

/-!
# The completion along a curve is the completion of its algebraization along the closed fibre

Let `D` be an ideal sheaf on a scheme `X` over `S`, with subscheme `C`, ring of formal functions
`A = lim Γ(Cₙ, 𝒪)`, an ideal `I ⊆ A` vanishing on `C` and a monotone `M : ℕ → ℕ` with `n ≤ M n`.
The adic tower `Xₙ = C_{M n} ×_{Spec A} Spec (A ⧸ Iⁿ⁺¹)`
(`AlgebraicGeometry.Scheme.IdealSheafData.adicTower`) sits inside `X`, and every thickening
`V(Dᵏ)` of `C` lies in some `Xₙ`, so `Xₙ` is a cofinal tower for `(X, |C|)`. If
`Y ⟶ Spec A` algebraizes the tower (Stacks 089A,
`AlgebraicGeometry.Scheme.IdealSheafData.exists_isProper_algebraization`), that is
`Xₙ = Y ×_{Spec A} Spec (A ⧸ Iⁿ⁺¹)` compatibly with the transition maps, the same tower is
cofinal for `(Y, |Y ×_{Spec A} V(I)|)`, being the base change of the cofinal tower
`Spec (A ⧸ Iⁿ⁺¹)` of `(Spec A, V(I))`. The two completions are therefore isomorphic, as fppf
sheaves over `S` (Stacks 0AMC): this is the comparison `X_{/C} ≅ Y_{/Y_{V(I)}}` of the
construction of Stacks 0D5E.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.adicTowerObject`: `Xₙ` as an object of the site, with
  its inclusion `adicTowerObjectι` into `X` and transition maps `adicTowerObjectSucc`.
* `AlgebraicGeometry.Scheme.IdealSheafData.thickeningToAdicTowerDiag`: `C_k ⟶ X_k`.
* `AlgebraicGeometry.Scheme.IdealSheafData.adicThickeningSiteObject`: `Spec (A ⧸ Iⁿ⁺¹)` as an
  object of the site.
* `AlgebraicGeometry.Scheme.IdealSheafData.adicTowerObjectToAlgebraization`: `kₙ : Xₙ ⟶ Y` as a
  morphism of the site.
* `AlgebraicGeometry.Scheme.IdealSheafData.completionSheafIsoAlgebraization`: the isomorphism of
  completions `X_{/|C|} ≅ Y_{/f⁻¹ V(I)}`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.isCofinalTower_adicTowerObject`: the adic tower is
  cofinal for `(X, |C|)`.
* `AlgebraicGeometry.Scheme.IdealSheafData.isCofinalTower_adicThickeningSiteObject`: the adic
  thickenings are cofinal for `(Spec A, V(I))`.
* `AlgebraicGeometry.Scheme.IdealSheafData.isCofinalTower_algebraization`: the adic tower is
  cofinal for `(Y, f⁻¹ V(I))`.

## References

* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Scheme.{u}} (D : X.IdealSheafData) (I : Ideal (formalNeighborhoodRing D)) (M : ℕ → ℕ)
  (hX : B.Contains X) (πX : X ⟶ S)

local notation "𝒯" => BigFppfOver.toScheme B S hS

/-! ### The adic tower in the site -/

include hX in
/-- The members `Xₙ` of the adic tower lie in the site when `X` does: `Xₙ ⟶ X` is a closed
immersion. -/
theorem contains_adicTower (n : ℕ) : B.Contains (adicTower D I M n) :=
  (Scheme.size_le_of_mono_quasiCompact (adicTowerToScheme D I M n)).trans_lt hX

/-- The `n`-th member `Xₙ` of the adic tower, as an object of the site over `S` through
`Xₙ ⟶ X ⟶ S`. -/
abbrev adicTowerObject (n : ℕ) : BigFppfOver B S hS :=
  siteObject B S hS (contains_adicTower D I M hX n) (adicTowerToScheme D I M n ≫ πX)

/-- The inclusion `Xₙ ⟶ X`, as a morphism of the site. -/
def adicTowerObjectι (n : ℕ) :
    adicTowerObject (hS := hS) D I M hX πX n ⟶ siteObject B S hS hX πX :=
  FormalSpace.siteHom B S hS (adicTowerToScheme D I M n) rfl

/-- The inclusion `Xₙ ⟶ X` of the site is the inclusion of schemes. -/
@[simp]
theorem toScheme_map_adicTowerObjectι (n : ℕ) :
    (𝒯).map (adicTowerObjectι D I M hX πX n) = adicTowerToScheme D I M n :=
  rfl

variable {M} (hM : Monotone M)

/-- The transition map `Xₙ ⟶ Xₙ₊₁`, as a morphism of the site. -/
def adicTowerObjectSucc (n : ℕ) :
    adicTowerObject (hS := hS) D I M hX πX n ⟶ adicTowerObject D I M hX πX (n + 1) :=
  FormalSpace.siteHom B S hS (adicTowerSucc D I hM n)
    (adicTowerSucc_adicTowerToScheme_assoc D I hM n πX)

/-- The transition map of the site is the transition map of schemes. -/
@[simp]
theorem toScheme_map_adicTowerObjectSucc (n : ℕ) :
    (𝒯).map (adicTowerObjectSucc D I hX πX hM n) = adicTowerSucc D I hM n :=
  rfl

/-- The inclusions into `X` are compatible with the transition maps. -/
@[reassoc]
theorem adicTowerObjectSucc_ι (n : ℕ) :
    adicTowerObjectSucc (hS := hS) D I hX πX hM n ≫ adicTowerObjectι D I M hX πX (n + 1) =
      adicTowerObjectι D I M hX πX n :=
  (𝒯).map_injective (by rw [Functor.map_comp]; exact adicTowerSucc_adicTowerToScheme D I hM n)

/-! ### The adic tower is cofinal in `X` -/

variable {I}

/-- **The thickening `C_k` lies in `X_k`**, for an ideal `I ⊆ F₁` and `k ≤ M k`: it maps to
`C_{M k}`, and to `Spec (A ⧸ Iᵏ⁺¹)` because `Iᵏ⁺¹ ⊆ F_{k+1}` vanishes on `C_k`. -/
def thickeningToAdicTowerDiag (hI : I ≤ formalNeighborhoodFiltration D 1) (hMle : ∀ n, n ≤ M n)
    (k : ℕ) : thickening D k ⟶ adicTower D I M k :=
  pullback.lift (thickeningInclusion D (hMle k))
    (adicThickeningLift _ I k (formalNeighborhoodProjection D k)
      (by
        rw [← formalNeighborhoodFiltration_succ]
        exact (isCompleteFiltration_formalNeighborhoodFiltration D).pow_le I hI (k + 1)))
    (by rw [thickeningInclusion_thickeningToSpec, adicThickeningLift_ι]; rfl)

/-- `C_k ⟶ X_k ⟶ X` is the inclusion of `C_k`. -/
@[reassoc (attr := simp)]
theorem thickeningToAdicTowerDiag_adicTowerToScheme (hI : I ≤ formalNeighborhoodFiltration D 1)
    (hMle : ∀ n, n ≤ M n) (k : ℕ) :
    thickeningToAdicTowerDiag D hI hMle k ≫ adicTowerToScheme D I M k = (D ^ (k + 1)).subschemeι := by
  rw [adicTowerToScheme, thickeningToAdicTowerDiag, pullback.lift_fst_assoc, thickeningInclusion,
    inclusion_subschemeι]

/-- **The adic tower is cofinal for `(X, |C|)`.** For `X` locally Noetherian, an ideal `I ⊆ F₁`
of `A` and `n ≤ M n`, the members `Xₙ` of the adic tower form a cofinal tower of `X` along the
support of `D`: every `V(Dᵏ)` lies in `C_k ⊆ X_k`. -/
theorem isCofinalTower_adicTowerObject [IsLocallyNoetherian X]
    (hI : I ≤ formalNeighborhoodFiltration D 1) (hMle : ∀ n, n ≤ M n) :
    FormalSpace.IsCofinalTower (adicTowerObjectSucc (hS := hS) D I hX πX hM)
      (adicTowerObjectι D I M hX πX) (D.support : Set X) := by
  have : IsLocallyNoetherian ((𝒯).obj (siteObject B S hS hX πX)) := ‹IsLocallyNoetherian X›
  refine FormalSpace.isCofinalTower_of_idealSheafData (X := siteObject B S hS hX πX) _ D
    (fun n => ?_) (adicTowerObjectSucc_ι D I hX πX hM) (fun n y => ?_) (fun k => ?_)
  · change Mono (adicTowerToScheme D I M n)
    infer_instance
  · have h : (D ^ (M n + 1)).subschemeι (adicTowerToThickeningOfD D I M n y) ∈
        ((D ^ (M n + 1)).support : Set X) := by
      rw [← range_subschemeι]
      exact Set.mem_range_self _
    exact h
  · refine ⟨k, inclusion (le_def.mpr fun U => by
        simp only [ideal_pow]; exact Ideal.pow_le_pow_right (Nat.le_succ k)) ≫
      thickeningToAdicTowerDiag D hI hMle k, ?_⟩
    change _ ≫ adicTowerToScheme D I M k = _
    rw [Category.assoc, thickeningToAdicTowerDiag_adicTowerToScheme, inclusion_subschemeι]

/-! ### The adic thickenings of `Spec A` in the site -/

variable (I M)
variable (hA : B.Contains (Spec (.of (formalNeighborhoodRing D))))
  (σ : Spec (.of (formalNeighborhoodRing D)) ⟶ S)

/-- The adic thickening `Spec (A ⧸ Iⁿ⁺¹)`, as an object of the site over `S` through
`Spec (A ⧸ Iⁿ⁺¹) ⟶ Spec A ⟶ S`. -/
abbrev adicThickeningSiteObject (n : ℕ) : BigFppfOver B S hS :=
  siteObject B S hS (Space.contains_adicThickening _ I B hA n)
    (adicThickeningι (formalNeighborhoodRing D) I n ≫ σ)

/-- The closed immersion `Spec (A ⧸ Iⁿ⁺¹) ⟶ Spec A`, as a morphism of the site. -/
def adicThickeningSiteObjectι (n : ℕ) :
    adicThickeningSiteObject (hS := hS) D I hA σ n ⟶ siteObject B S hS hA σ :=
  FormalSpace.siteHom B S hS (adicThickeningι (formalNeighborhoodRing D) I n) rfl

/-- The transition map `Spec (A ⧸ Iⁿ⁺¹) ⟶ Spec (A ⧸ Iⁿ⁺²)`, as a morphism of the site. -/
def adicThickeningSiteObjectSucc (n : ℕ) :
    adicThickeningSiteObject (hS := hS) D I hA σ n ⟶ adicThickeningSiteObject D I hA σ (n + 1) :=
  FormalSpace.siteHom B S hS (adicThickeningSucc (formalNeighborhoodRing D) I n)
    (adicThickeningSucc_ι_assoc _ I n σ)

/-- The closed immersions into `Spec A` are compatible with the transition maps. -/
@[reassoc]
theorem adicThickeningSiteObjectSucc_ι (n : ℕ) :
    adicThickeningSiteObjectSucc (hS := hS) D I hA σ n ≫
        adicThickeningSiteObjectι D I hA σ (n + 1) =
      adicThickeningSiteObjectι D I hA σ n :=
  (𝒯).map_injective (by rw [Functor.map_comp]; exact adicThickeningSucc_ι _ I n)

/-- **The adic thickenings are cofinal for `(Spec A, V(I))`**, `A` being Noetherian. -/
theorem isCofinalTower_adicThickeningSiteObject [IsNoetherianRing (formalNeighborhoodRing D)] :
    FormalSpace.IsCofinalTower (adicThickeningSiteObjectSucc (hS := hS) D I hA σ)
      (adicThickeningSiteObjectι D I hA σ)
      (PrimeSpectrum.zeroLocus (I : Set (formalNeighborhoodRing D))) := by
  have h := FormalSpace.isCofinalTower_of_specMap_quotient_pow
    (X := siteObject B S hS hA σ) (A := .of (formalNeighborhoodRing D))
    (adicThickeningSiteObjectSucc (hS := hS) D I hA σ)
    (Iso.refl (Spec (.of (formalNeighborhoodRing D)))) I (ι := adicThickeningSiteObjectι D I hA σ)
    (fun n => ⟨Iso.refl _, by
      simp only [Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]
      rfl⟩)
    (adicThickeningSiteObjectSucc_ι (hS := hS) D I hA σ)
  exact h

/-! ### The algebraization -/

variable (hσ : ∀ n, thickeningToSpec D n ≫ σ = (D ^ (n + 1)).subschemeι ≫ πX)

include hσ in
/-- If the thickenings lie over `S` compatibly with `σ : Spec A ⟶ S`, so does
`Xₙ ⟶ Spec (A ⧸ Iⁿ⁺¹)`. -/
@[reassoc]
theorem adicTowerToThickening_comp_eq (n : ℕ) :
    adicTowerToThickening D I M n ≫ adicThickeningι (formalNeighborhoodRing D) I n ≫ σ =
      adicTowerToScheme D I M n ≫ πX := by
  rw [← pullback.condition_assoc, hσ, Category.assoc]

/-- The projection `Xₙ ⟶ Spec (A ⧸ Iⁿ⁺¹)`, as a morphism of the site. -/
def adicTowerObjectToThickening (n : ℕ) :
    adicTowerObject (hS := hS) D I M hX πX n ⟶ adicThickeningSiteObject D I hA σ n :=
  FormalSpace.siteHom B S hS (adicTowerToThickening D I M n)
    (adicTowerToThickening_comp_eq D I M πX σ hσ n)

variable {Y : Scheme.{u}} (fY : Y ⟶ Spec (.of (formalNeighborhoodRing D))) [IsProper fY]

include hA fY in
/-- A scheme proper over `Spec A` lies in the site when `Spec A` does. -/
theorem contains_of_isProper : B.Contains Y :=
  -- instance search for `LocallyOfFiniteType fY` times out under Lean v4.35.0
  have : LocallyOfFiniteType fY := IsProper.toLocallyOfFiniteType
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact fY hA

/-- `Y` as an object of the site over `S`, through `Y ⟶ Spec A ⟶ S`. -/
abbrev algebraizationObject : BigFppfOver B S hS :=
  siteObject B S hS (contains_of_isProper D hA fY) (fY ≫ σ)

/-- `Y ⟶ Spec A`, as a morphism of the site. -/
def algebraizationObjectHom :
    algebraizationObject (hS := hS) D hA σ fY ⟶ siteObject B S hS hA σ :=
  FormalSpace.siteHom B S hS fY rfl

/-- The morphism of the site `Y ⟶ Spec A` is `fY`. -/
@[simp]
theorem toScheme_map_algebraizationObjectHom :
    (𝒯).map (algebraizationObjectHom D hA σ fY) = fY :=
  rfl

variable {k : ∀ n, adicTower D I M n ⟶ Y}
  (hpb : ∀ n, IsPullback (k n) (adicTowerToThickening D I M n) fY
    (adicThickeningι (formalNeighborhoodRing D) I n))

omit [IsProper fY] in
include hσ hpb in
/-- The morphisms `kₙ : Xₙ ⟶ Y` lie over `S`. -/
@[reassoc]
theorem algebraization_comp_eq (n : ℕ) : k n ≫ fY ≫ σ = adicTowerToScheme D I M n ≫ πX := by
  rw [reassoc_of% (hpb n).w]
  exact adicTowerToThickening_comp_eq D I M πX σ hσ n

/-- The morphism `kₙ : Xₙ ⟶ Y` of an algebraization of the adic tower, as a morphism of the
site. -/
def adicTowerObjectToAlgebraization (n : ℕ) :
    adicTowerObject (hS := hS) D I M hX πX n ⟶ algebraizationObject D hA σ fY :=
  FormalSpace.siteHom B S hS (k n) (algebraization_comp_eq D I M πX σ hσ fY hpb n)

/-- **The adic tower is cofinal for `(Y, f⁻¹ V(I))`.** If `kₙ : Xₙ ⟶ Y` are compatible with the
transition maps and exhibit `Xₙ` as `Y ×_{Spec A} Spec (A ⧸ Iⁿ⁺¹)`, the adic tower is the base
change of the cofinal tower `Spec (A ⧸ Iⁿ⁺¹)` of `(Spec A, V(I))`, hence cofinal. -/
theorem isCofinalTower_algebraization [IsNoetherianRing (formalNeighborhoodRing D)]
    (hk : ∀ n, adicTowerSucc D I hM n ≫ k (n + 1) = k n) :
    FormalSpace.IsCofinalTower (adicTowerObjectSucc (hS := hS) D I hX πX hM)
      (adicTowerObjectToAlgebraization D I M hX πX hA σ hσ fY hpb)
      (fY ⁻¹' PrimeSpectrum.zeroLocus (I : Set (formalNeighborhoodRing D))) :=
  FormalSpace.isCofinalTower_of_isPullback _ (algebraizationObjectHom D hA σ fY)
    (isCofinalTower_adicThickeningSiteObject D I hA σ)
    (adicTowerObjectToThickening D I M hX πX hA σ hσ)
    (fun n => (𝒯).map_injective (by rw [Functor.map_comp]; exact hk n)) hpb

/-! ### The comparison of completions -/

/-- **The completion of `X` along `|C|` is the completion of the algebraization `Y` along the
inverse image of `V(I)`.** Let `X` be locally Noetherian, `I ⊆ F₁` an ideal of the Noetherian
ring `A` of formal functions, `n ≤ M n`, and `kₙ : Xₙ ⟶ Y` an algebraization of the adic tower
over a proper `fY : Y ⟶ Spec A`, everything over `S`. Then `X_{/|C|} ≅ Y_{/f⁻¹ V(I)}` as fppf
sheaves: both are the completion along the common cofinal tower `Xₙ`. -/
def completionSheafIsoAlgebraization [IsLocallyNoetherian X]
    [IsNoetherianRing (formalNeighborhoodRing D)]
    (hI : I ≤ formalNeighborhoodFiltration D 1) (hMle : ∀ n, n ≤ M n)
    (hk : ∀ n, adicTowerSucc D I hM n ≫ k (n + 1) = k n) :
    Space.completionSheaf B S hS (yoneda.obj (siteObject B S hS hX πX))
        (Space.pointsToScheme B S hS _ ⁻¹' (D.support : Set X)) ≅
      Space.completionSheaf B S hS (yoneda.obj (algebraizationObject D hA σ fY))
        (Space.pointsToScheme B S hS _ ⁻¹'
          (fY ⁻¹' PrimeSpectrum.zeroLocus (I : Set (formalNeighborhoodRing D)))) :=
  FormalSpace.completionSheafIsoOfCofinalTower (isCofinalTower_adicTowerObject D hX πX hM hI hMle)
    (isCofinalTower_algebraization D I M hX πX hM hA σ hσ fY hpb hk)

end AlgebraicGeometry.Scheme.IdealSheafData

end
