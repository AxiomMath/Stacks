module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierPunctualTransformLisse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierNoPunctualSectionsDegreeZeroProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformPunctual
public import StacksFrontier.Algebra.Homology.DerivedCategory.PlusTwoDegreeImageFactor

/-!
# Mechanism (c): a quotient of `H¹(Φ F)` killed through a punctual image

Let `k` be a finite field, `Λ` a finite commutative ring in which `q = #k` is invertible, `ψ` an
additive character of `k` with values in `Λ` and `∑ ψ = 0`, and `Φ` the Fourier transform on
`D⁺(𝔸¹_k, Λ)`. Let `F` be étale-locally free of finite rank on `𝔸¹_k`, `G = H¹(Φ(F[0]))` and
`β : G ⟶ Q` an epimorphism, `Q` without sections supported off a nonempty open `V` on which it is
locally constant with finite values. If `n • H¹(Φ(β))` factors through a punctual sheaf, then
`n • 𝟙 Q = 0`:

* `u = n • Φ(β) : Φ(G[0]) ⟶ Φ(Q[0])` goes between objects concentrated in degrees `[1, 2]`
  (`H⁰(Φ G) = 0`, `H⁰(Φ Q) = 0` by (L1));
* `H¹(Φ(I[0])) = 0` for a punctual `I` (L5), and `H⁰(Φ(H²(Φ G)[0])) = 0`, `H²(Φ G)` being
  locally constant of finite type (L1), so `H²(Φ(u)) = 0`
  (`Stacks.DerivedCategoryPlus.homology_two_map_eq_zero_of_homology_one_map_eq_comp`);
* `H² ∘ Φ ∘ Φ` is faithful on sheaves with finite stalks, so `β ≫ n • 𝟙 = 0`, and `β` is onto.

The only named input is the twist input
`Stacks.EtaleCohomology.FourierTwistNoConstantQuotientInput` (through the lisseness of `H²(Φ G)`).
This is the mechanism (c) of the single-level argument for the irreducibility of the Fourier
transform in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.isZero_homology_zero_fourierTransform_of_isFiniteTypeLocallyConstant`.
* `Stacks.EtaleCohomology.nsmul_id_eq_zero_of_nsmul_homology_one_fourierTransform_map_eq_comp`.

## Implementation notes

The Fourier transform lives in the standard model `HasDerivedCategory.standard`, and so do the
statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

local notation "𝔸f" => affineLineStructureMap k

/-- **(L1) `H⁰(Φ(H[0])) = 0` for `H` locally constant of finite type on `𝔸¹_k`**: the case
`V = 𝔸¹_k` of `Stacks.EtaleCohomology.fourierNoPunctualSectionsDegreeZeroInput`, the unit of
`id⁻¹ ⊣ id_*` being an isomorphism. -/
theorem isZero_homology_zero_fourierTransform_of_isFiniteTypeLocallyConstant
    (j : CompactificationOf (Over.mk 𝔸f)) (H : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))))
    (hH : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
      (Spec (.of (Polynomial k))).smallEtaleTopology H) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj H))) := by
  have : (etaleModuleInverseImage.{u, 0} Λ (𝟙 (Spec (.of (Polynomial k))))).Full :=
    Functor.Full.of_iso (etaleModuleInverseImageIdIso.{u, 0} Λ _).symm
  have : (etaleModuleInverseImage.{u, 0} Λ (𝟙 (Spec (.of (Polynomial k))))).Faithful :=
    Functor.Faithful.of_iso (etaleModuleInverseImageIdIso.{u, 0} Λ _).symm
  exact fourierNoPunctualSectionsDegreeZeroInput k Λ ψ B p₀ j H (𝟙 _)
    (isLocallyConstantWith_inverseImage Λ _ (𝟙 _)
      (isLocallyConstantWith_of_imp Λ (fun E hE => (ModuleCat.isFG_iff E).1 hE) hH))
    inferInstance

/-- **Mechanism (c) for a quotient of `G = H¹(Φ(F[0]))`**: for `F` étale-locally free of finite
rank, `β : G ⟶ Q` an epimorphism with `Q` locally constant with finite values on a nonempty open
`V` and without sections supported off `V`, if `n • H¹(Φ(β)) = p ≫ m` factors through a punctual
sheaf `I`, then `n • 𝟙 Q = 0`. -/
theorem nsmul_id_eq_zero_of_nsmul_homology_one_fourierTransform_map_eq_comp
    (hT : FourierTwistNoConstantQuotientInput.{u}) (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) (hF : IsLocallyFreeEtaleModule Λ F)
    {Q : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))}
    (β : (DerivedCategory.Plus.homologyFunctor _ 1).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ⟶ Q)
    [Epi β] {V : Scheme.{u}} (jV : V ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion jV]
    [Nonempty V]
    (hQ : Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology
      (fun E => Module.Finite Λ E) ((etaleModuleInverseImage.{u, 0} Λ jV).obj Q))
    (hQm : Mono ((etaleModuleInverseImageAdj.{u, 0} Λ jV).unit.app Q)) (n : ℕ)
    {I : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))}
    (p : (DerivedCategory.Plus.homologyFunctor _ 1).obj ((fourierTransform k Λ ψ B p₀ j).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((DerivedCategory.Plus.homologyFunctor _ 1).obj
          ((fourierTransform k Λ ψ B p₀ j).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))) ⟶ I)
    (m : I ⟶ (DerivedCategory.Plus.homologyFunctor _ 1).obj ((fourierTransform k Λ ψ B p₀ j).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj Q)))
    (hpm : n • (DerivedCategory.Plus.homologyFunctor _ 1).map
      ((fourierTransform k Λ ψ B p₀ j).map ((DerivedCategory.Plus.singleFunctor _ 0).map β)) =
        p ≫ m)
    (hI : IsPunctualEtaleModule Λ I) :
    n • 𝟙 Q = 0 := by
  let Φ := fourierTransform k Λ ψ B p₀ j
  let := fourierTransformCommShift k Λ ψ B p₀ j
  have := isTriangulated_fourierTransform k Λ ψ B p₀ j
  have : Φ.Additive := inferInstance
  have : IsNoetherianRing Λ := inferInstance
  let S := DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) 0
  have hFc := isConstructibleEtaleModule_of_isLocallyFreeEtaleModule Λ hF
  have hGf := finite_globalSections_inverseImage_of_isConstructible Λ
    (isConstructibleEtaleModule_homology_fourierTransform k Λ ψ B p₀ j F hFc 1)
  have hG0 := isZero_homology_zero_fourierTransform_homology_one k Λ ψ B p₀ hψ hq j jQ F hF
    (finite_globalSections_inverseImage_of_isConstructible Λ hFc)
  have hQ0 := fourierNoPunctualSectionsDegreeZeroInput k Λ ψ B p₀ j Q jV hQ hQm
  have hGE : ∀ (X : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))),
      IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj (Φ.obj (S.obj X))) →
        (Φ.obj (S.obj X)).IsGE 1 := fun X hX =>
    (DerivedCategory.Plus.isGE_iff _ 1).2 fun i hi => by
      rcases lt_or_eq_of_le (show i ≤ 0 by omega) with h | rfl
      · exact isZero_homology_fourierTransform_of_neg k Λ ψ B p₀ j X i h
      · exact hX
  have := hGE _ hG0
  have := hGE Q hQ0
  have : (Φ.obj (S.obj ((DerivedCategory.Plus.homologyFunctor _ 1).obj
      (Φ.obj (S.obj F))))).IsLE 2 :=
    (DerivedCategory.Plus.isLE_iff _ 2).2 fun i hi =>
      isZero_homology_fourierTransform_of_two_lt k Λ ψ B p₀ j _ i (by omega)
  obtain ⟨-, hL₂⟩ := isFiniteTypeLocallyConstant_homology_fourierTransform_homology_one k Λ ψ
    B p₀ hψ hq j jQ F hF
    (isFiniteTypeLocallyConstant_homology_two_fourierTransform_comp Λ k ψ B p₀ hψ hq j jQ F hF 2)
    (isFiniteTypeLocallyConstant_homology_zero_fourierTransform_homology_two k Λ ψ B p₀ hT hψ hq
      j F hF)
  have hX := isZero_homology_zero_fourierTransform_of_isFiniteTypeLocallyConstant k Λ ψ B p₀ j
    _ hL₂
  obtain ⟨U, jU, hjU, hU, hz⟩ := hI
  have := hjU
  have := hU
  have hI1 := isZero_homology_fourierTransform_of_isZero_inverseImage k Λ ψ B p₀ j I jU hz 1
    one_ne_zero
  have h2 := Stacks.DerivedCategoryPlus.homology_two_map_eq_zero_of_homology_one_map_eq_comp Φ
    (Φ.map (S.map (β ≫ (n • 𝟙 Q)))) p m (by
      rw [Preadditive.comp_nsmul, Category.comp_id, Functor.map_nsmul, Functor.map_nsmul,
        Functor.map_nsmul]
      exact hpm) hI1 hX
  have h0 : β ≫ (n • 𝟙 Q) = 0 :=
    eq_zero_of_homology_two_fourierTransform_comp_map_eq_zero k Λ ψ B p₀ hψ hq j jQ
      (β ≫ (n • 𝟙 Q))
      hGf (finite_globalSections_inverseImage_of_epi Λ β hGf) (by
        rw [Functor.comp_map]
        exact h2)
  rw [← cancel_epi β, h0, comp_zero]

end Stacks.EtaleCohomology

end
