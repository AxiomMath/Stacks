module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFractionEmbeddingNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.HenselianLocalRingMapUnramified

/-!
# Naturality of the embedding of Stacks 0ENK along an étale morphism, with unramifiedness

Let `f : X ⟶ Y` be an étale morphism of decent, locally Noetherian, integral algebraic spaces
carrying the generic point of `X` to the generic point of `Y`, and let `Z ⊆ X`, `Z' ⊆ Y` be prime
divisors with the generic point `ξ` of `Z` over the generic point `ξ'` of `Z'`. This file proves
that there is **one** flat local homomorphism `φ : 𝒪^h_{Y, ξ'} ⟶ 𝒪^h_{X, ξ}` which both makes the
naturality square of Stacks 0ENK commute
(`AlgebraicGeometry.Space.exists_genericHenselianLocalRingHom_naturality`) and is unramified,

  `𝔪_{𝒪^h_{Y, ξ'}} · 𝒪^h_{X, ξ} = 𝔪_{𝒪^h_{X, ξ}}`.

## Main results

* `Space.exists_genericHenselianLocalRingHom_naturality_map_maximalIdeal_of_isEtale`:
  one `φ` with both properties.
* `Space.exists_genericHenselianLocalRingHom_naturality_multiplicity_eq_one_of_isEtale`:
  the same with unramifiedness read as `primeDivisorFlatMultiplicity … φ = 1`.

## References

* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hintX : IsIntegralSpace B S hS X) (hintY : IsIntegralSpace B S hS Y) (f : X ⟶ Y)
    (hgen : pointsMap B S hS X f (genericPoint B S hS hX hintX) =
      genericPoint B S hS hY hintY)
    (hdecX : IsDecentSpace B S hS X) (hdecY : IsDecentSpace B S hS Y)
    (hNX : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hNY : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (ZX : PrimeDivisor B S hS X) (ZY : PrimeDivisor B S hS Y)

/-- The structure morphism of an elementary étale neighbourhood is étale on charts. -/
private theorem presheaf_etale_toSpace_of_neighborhood {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hZ : IsAlgebraicSpace B S hS Z} {z : points B S hS Z}
    (W : ElementaryEtaleNeighborhood B S hS Z hZ z) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf W.toSpace :=
  (isEtale_iff_presheaf_of_yoneda B S hS W.toSpace).1 W.etale_toSpace

include hX hintX hintY hgen in
/-- Naturality of the embedding of Stacks 0ENK along an étale morphism, together with
unramifiedness of the induced homomorphism of henselian local rings. Let `f : X ⟶ Y` be an
étale morphism of decent, locally Noetherian, integral algebraic spaces over `S` carrying the
generic point of `X` to the generic point of `Y`, let `Z ⊆ X` and `Z' ⊆ Y` be prime divisors and
suppose the generic point `ξ` of `Z` lies over the generic point `ξ'` of `Z'`. There is a flat
local homomorphism `φ : 𝒪^h_{Y, ξ'} ⟶ 𝒪^h_{X, ξ}` which

* extends the maximal ideal to the maximal ideal, and
* makes the naturality square of Stacks 0ENK commute: the embedding of the pullback `g ∘ f` of a
  rational function `g` of `Y` is the image of the embedding of `g` under `Q(φ)`. -/
theorem exists_genericHenselianLocalRingHom_naturality_map_maximalIdeal_of_isEtale
    (hf : IsEtale B S hS f)
    (hZ : pointsMap B S hS X f (ZX.genericPoint B S hS X) = ZY.genericPoint B S hS Y) :
    letI := henselianLocalRing_isLocalRing B S hS Y hY (ZY.genericPoint B S hS Y) hdecY
    letI := henselianLocalRing_isLocalRing B S hS X hX (ZX.genericPoint B S hS X) hdecX
    ∃ (φ : ↥(ZY.genericHenselianLocalRing B S hS hY hdecY) →+*
        ↥(ZX.genericHenselianLocalRing B S hS hX hdecX)) (_ : IsLocalHom φ) (hφflat : φ.Flat),
      Ideal.map φ (IsLocalRing.maximalIdeal ↥(ZY.genericHenselianLocalRing B S hS hY hdecY)) =
          IsLocalRing.maximalIdeal ↥(ZX.genericHenselianLocalRing B S hS hX hdecX) ∧
        ∀ g : rationalFunctions B S hS hY,
          ZX.rationalFunctionsToGenericTotalFractionRing B S hS hX hdecX hintX hNX
              (rationalFunctionMap B S hS hX hY hintX hintY f hgen g) =
            IsLocalization.map (T := (↥(ZX.genericHenselianLocalRing B S hS hX hdecX))⁰)
              (ZX.genericTotalFractionRing B S hS hX hdecX) φ
              (fun _ hc => Ring.map_mem_nonZeroDivisors_of_flatHom hφflat hc)
              (ZY.rationalFunctionsToGenericTotalFractionRing B S hS hY hdecY hintY hNY g) := by
  have := henselianLocalRing_isLocalRing B S hS Y hY (ZY.genericPoint B S hS Y) hdecY
  have := henselianLocalRing_isLocalRing B S hS X hX (ZX.genericPoint B S hS X) hdecX
  obtain ⟨V, U₀, j₀, hj₀, φ, hsq₀, hVaff, hφloc, hcompat₀, hφflat, -, hmax⟩ := hZ ▸
    exists_henselianLocalRingHom_chartSquare_map_maximalIdeal_of_isEtale B S hS hX
      hdecX hY hdecY f hf (ZX.genericPoint B S hS X)
  obtain ⟨U, r, hUaff⟩ := ElementaryEtaleNeighborhood.exists_affine_refinement B S hS X hX
    (ZX.genericPoint B S hS X) U₀
  have : IsAffine V.scheme.left.1 := hVaff
  have : IsAffine U.scheme.left.1 := hUaff
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.scheme) := hUaff
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V.scheme) := hVaff
  have hsq : yoneda.map (r.hom ≫ j₀) ≫ V.toSpace = U.toSpace ≫ f := by
    rw [Functor.map_comp, Category.assoc, hsq₀, ← Category.assoc, r.over]
  have : AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map (r.hom ≫ j₀)) :=
    isFlat_of_isEtale B S hS hf U.scheme V.scheme U.toSpace V.toSpace (r.hom ≫ j₀)
      (presheaf_etale_toSpace_of_neighborhood B S hS U)
      (presheaf_etale_toSpace_of_neighborhood B S hS V) hsq
  have hj : (Γ(V.scheme.left.1, ⊤))⁰ ≤ ((Γ(U.scheme.left.1, ⊤))⁰).comap
      (chartGlobalSectionsRestrict B S hS (r.hom ≫ j₀)) := fun _ hc =>
    Ring.map_mem_nonZeroDivisors_of_flatHom
      (Scheme.Hom.flat_appTop ((BigFppfOver.toScheme B S hS).map (r.hom ≫ j₀))) hc
  have hcompat : ∀ a : Γ(V.scheme.left.1, ⊤),
      φ (ZY.neighborhoodSectionsToGenericHenselianLocalRing B S hS hY hdecY V a) =
        ZX.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdecX U
          (chartGlobalSectionsRestrict B S hS (r.hom ≫ j₀) a) := by
    intro a
    have h₁ := hcompat₀ (V.scheme.left.1.presheaf.germ ⊤ V.point trivial a)
    rw [germ_top_stalkCongr_stalkMap j₀.left.1 hj₀ a] at h₁
    have h₂ := ZX.neighborhoodSectionsToGenericHenselianLocalRing_naturality B S hS hX hdecX r
      (j₀.left.1.appTop a)
    rw [show chartGlobalSectionsRestrict B S hS (r.hom ≫ j₀) a =
        r.hom.left.1.appTop (j₀.left.1.appTop a) by
      rw [chartGlobalSectionsRestrict, Functor.map_comp, Scheme.Hom.comp_appTop]; rfl, h₂]
    exact h₁
  exact ⟨φ, hφloc, hφflat, hmax, fun g =>
    toGenericTotalFractionRing_rationalFunctionMap_of_chartSquare
      B S hS hX hY hintX hintY f hgen hdecX hdecY hNX hNY ZX ZY U V (r.hom ≫ j₀) hsq hj φ
      (fun _ hc => Ring.map_mem_nonZeroDivisors_of_flatHom hφflat hc) hcompat g⟩

include hX hintX hintY hgen in
/-- The multiplicity of a prime divisor over its image under an étale morphism is one, for a
homomorphism which also makes the naturality square of Stacks 0ENK commute: there is a flat
local homomorphism `φ : 𝒪^h_{Y, ξ'} ⟶ 𝒪^h_{X, ξ}` with
`primeDivisorFlatMultiplicity … φ = 1` making that square commute. -/
theorem exists_genericHenselianLocalRingHom_naturality_multiplicity_eq_one_of_isEtale
    (hf : IsEtale B S hS f)
    (hZ : pointsMap B S hS X f (ZX.genericPoint B S hS X) = ZY.genericPoint B S hS Y) :
    letI := henselianLocalRing_isLocalRing B S hS Y hY (ZY.genericPoint B S hS Y) hdecY
    letI := henselianLocalRing_isLocalRing B S hS X hX (ZX.genericPoint B S hS X) hdecX
    ∃ (φ : ↥(ZY.genericHenselianLocalRing B S hS hY hdecY) →+*
        ↥(ZX.genericHenselianLocalRing B S hS hX hdecX)) (_ : IsLocalHom φ) (hφflat : φ.Flat),
      primeDivisorFlatMultiplicity B S hS hX hdecX ZX hY hdecY ZY φ = ((1 : ℕ) : ℕ∞) ∧
        ∀ g : rationalFunctions B S hS hY,
          ZX.rationalFunctionsToGenericTotalFractionRing B S hS hX hdecX hintX hNX
              (rationalFunctionMap B S hS hX hY hintX hintY f hgen g) =
            IsLocalization.map (T := (↥(ZX.genericHenselianLocalRing B S hS hX hdecX))⁰)
              (ZX.genericTotalFractionRing B S hS hX hdecX) φ
              (fun _ hc => Ring.map_mem_nonZeroDivisors_of_flatHom hφflat hc)
              (ZY.rationalFunctionsToGenericTotalFractionRing B S hS hY hdecY hintY hNY g) := by
  have := henselianLocalRing_isLocalRing B S hS Y hY (ZY.genericPoint B S hS Y) hdecY
  have := henselianLocalRing_isLocalRing B S hS X hX (ZX.genericPoint B S hS X) hdecX
  obtain ⟨φ, hφloc, hφflat, hmax, hnat⟩ :=
    exists_genericHenselianLocalRingHom_naturality_map_maximalIdeal_of_isEtale B S hS hX hY
      hintX hintY f hgen hdecX hdecY hNX hNY ZX ZY hf hZ
  refine ⟨φ, hφloc, hφflat, ?_, hnat⟩
  rw [primeDivisorFlatMultiplicity, hmax, Nat.cast_one]
  have : IsSimpleModule ↥(ZX.genericHenselianLocalRing B S hS hX hdecX)
      (↥(ZX.genericHenselianLocalRing B S hS hX hdecX) ⧸
        IsLocalRing.maximalIdeal ↥(ZX.genericHenselianLocalRing B S hS hX hdecX)) :=
    isSimpleModule_iff_isCoatom.2
      (IsLocalRing.maximalIdeal.isMaximal
        ↥(ZX.genericHenselianLocalRing B S hS hX hdecX)).out
  exact Module.length_eq_one _ _

end AlgebraicGeometry.Space

end
