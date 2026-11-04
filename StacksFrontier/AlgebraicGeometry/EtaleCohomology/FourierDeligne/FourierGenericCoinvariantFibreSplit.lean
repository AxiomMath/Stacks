module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierGenericCoinvariantFibreReduction
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformDegreeZero

/-!
# Generic vanishing of the fibre coinvariants: the curve half and the Artin–Schreier half

The input `Stacks.EtaleCohomology.FourierFibreCoinvariantVanishingInput` asks, for a sheaf `M` on
a nonempty open `V ⊆ 𝔸¹_k` which is locally constant with finite values, for a nonempty open `U`
of the `t`-line such that `H²_c(C_s, t⁻¹ M ⊗ L_ψ(x s)) = 0` at the geometric points `s` of `U`,
where `C_s ≅ V_Ω` is the open over `V` of the fibre `X_s ≅ 𝔸¹_Ω` of `pr₂`. It splits into two
independent statements:

* **the curve half**: on a nonempty open `C` of the affine line `𝔸¹_Ω` over an algebraically
  closed field, the top compactly supported cohomology `H²_c(C, N)` of a locally constant sheaf
  `N` with finite values vanishes as soon as `N` has no nonzero morphism to a constant sheaf with
  simple value. Indeed `H²_c(C, N)` is the module of coinvariants `(N_x̄)_{π₁(C, x̄)}` (Tate
  twisted), and a nonzero finite module of coinvariants has a simple quotient, which is a
  quotient of `N` by a constant sheaf;
* **the Artin–Schreier half**: for `s` in a nonempty open `U`, the twisted sheaf
  `t⁻¹ M ⊗ L_ψ(x s)` on `C_s` has no nonzero morphism to a constant sheaf with simple value `E`.
  Such a morphism is adjoint to a morphism `M_Ω ⟶ L_ψ(-x s) ⊗ E`, whose image is trivialised by a
  finite étale cover `W ⟶ V` trivialising `M`, so `L_ψ(-x s) ⊗ E` is trivial on a component of
  `W_Ω`. The residue character of `ψ` at the maximal ideal annihilating `E` is nontrivial (`#k`
  is a unit and `∑ ψ = 0`), and the class of `s x` in `O(W₀)/℘ O(W₀)` vanishes only for finitely
  many `s` (the reduced polar part of `s x` at a pole of `x` is a nonzero additive polynomial in
  `s`).

This file states the two halves and proves that together they give
`Stacks.EtaleCohomology.FourierFibreCoinvariantVanishingInput`, hence the input (L2)
`Stacks.EtaleCohomology.FourierGenericCoinvariantVanishingInput` of the single-level argument for
the irreducibility of the Fourier transform in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.HasNoConstantSimpleQuotient`.
* `Stacks.EtaleCohomology.AffineLineOpenTopCohomologyVanishingInput`: the curve half.
* `Stacks.EtaleCohomology.FourierTwistNoConstantQuotientInput`: the Artin–Schreier half.

## Main results

* `Stacks.EtaleCohomology.isLocallyConstantWith_of_imp`.
* `Stacks.EtaleCohomology.fourierFibreCoinvariantVanishingInput_of_halves`.
* `Stacks.EtaleCohomology.fourierGenericCoinvariantVanishingInput_of_halves`.

## Implementation notes

`Rf_!` lives in the standard model `HasDerivedCategory.standard`, and so do the statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  HasDerivedCategory.standard

/-- Local constancy with values in `Q` implies local constancy with values in any weaker `Q'`. -/
theorem isLocallyConstantWith_of_imp (Λ : Type) [Ring Λ] {X : Scheme.{u}}
    {Q Q' : ModuleCat.{u + 1} Λ → Prop} (hQ : ∀ E, Q E → Q' E) {G : EtaleModules.{u, 0} Λ X}
    (hG : Stacks.ConstantSheaf.IsLocallyConstantWith Λ X.smallEtaleTopology Q G) :
    Stacks.ConstantSheaf.IsLocallyConstantWith Λ X.smallEtaleTopology Q' G := by
  intro U
  obtain ⟨I, V, f, hcov, htriv⟩ := hG U
  exact ⟨I, V, f, hcov, fun i => (htriv i).imp fun E hE => ⟨hQ E hE.1, hE.2⟩⟩

/-- **`N` has no constant simple quotient**: every morphism from `N` to the constant sheaf with
value a simple `Λ`-module vanishes. For a locally constant `N` on a connected scheme this says
that the monodromy module of `N` has no simple quotient with trivial action, i.e. that its
coinvariants vanish. -/
def HasNoConstantSimpleQuotient (Λ : Type) [Ring Λ] {C : Scheme.{u}}
    (N : EtaleModules.{u, 0} Λ C) : Prop :=
  ∀ (E : ModuleCat.{u + 1} Λ), IsSimpleModule Λ E →
    ∀ φ : N ⟶ (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E, φ = 0

/-- **The curve half: `H²_c` of a locally constant sheaf on an open of `𝔸¹_Ω` is its
coinvariants.** For `Ω` algebraically closed, `C` a nonempty open of `X ≅ 𝔸¹_Ω` and `N` a locally
constant sheaf of modules over a finite ring with finite values and no constant simple quotient,
`H²_c(C, N) = 0` (computed through any compactification): `H²_c(C, N)` is the Tate twisted
module of coinvariants of the monodromy of `N` under `π₁(C)`. -/
def AffineLineOpenTopCohomologyVanishingInput : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (Λ : Type) [CommRing Λ] [Finite Λ] {X C : Scheme.{u}}
    (f : X ⟶ Spec (.of Ω)),
    (∃ e : X ≅ AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω)),
      e.hom ≫ (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω)) ↘ Spec (.of Ω)) = f) →
    ∀ (ι : C ⟶ X) [IsOpenImmersion ι] [Nonempty C] (N : EtaleModules.{u, 0} Λ C),
      Stacks.ConstantSheaf.IsLocallyConstantWith Λ C.smallEtaleTopology
        (fun E => Module.Finite Λ E) N →
      HasNoConstantSimpleQuotient Λ N →
      ∀ jc : CompactificationOf (Over.mk (ι ≫ f)),
        IsZero ((DerivedCategory.Plus.homologyFunctor _ 2).obj
          ((derivedLowerShriek.{u, 0} (ι ≫ f) jc Λ).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj N)))

local notation "𝔸f" => affineLineStructureMap

/-- **The Artin–Schreier half: the twisted sheaves `t⁻¹ M ⊗ L_ψ(x s)` generically have no
constant simple quotient.** For a sheaf `M` on a nonempty open `V` of `𝔸¹_k`, locally constant
with finite values, there is a nonempty open `U` of the `t`-line such that at the geometric point
`s` of every point of `U`, the sheaf `t⁻¹ M ⊗ L_ψ(x s)` on the open `C_s = X_s ×_{𝔸¹_k} V` of the
fibre `X_s` of `pr₂` has no constant simple quotient; here `∑ ψ = 0` and `#k` is a unit in the
finite ring `Λ`, so that the residue characters of `ψ` are nontrivial and the sheaves
`L_ψ(x s)` modulo a maximal ideal are pairwise non-isomorphic on `V_Ω`. -/
def FourierTwistNoConstantQuotientInput : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
    (B : BigEtaleSite.{u})
    (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj
      (cover k (Polynomial k) Polynomial.X)),
    ∑ a : k, ψ a = 0 → IsUnit (Fintype.card k : Λ) →
    ∀ {V : Scheme.{u}} (jV : V ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion jV] [Nonempty V]
      (M : EtaleModules.{u, 0} Λ V),
      Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology
        (fun E => Module.Finite Λ E) M →
      ∃ (U : Scheme.{u}) (jU : U ⟶ Spec (.of (Polynomial k))), IsOpenImmersion jU ∧ Nonempty U ∧
        ∀ y : U, HasNoConstantSimpleQuotient Λ
          ((etaleModuleInverseImage.{u, 0} Λ
              (pullback.snd (pullback.fst (pullback.snd (𝔸f k) (𝔸f k))
                ((GeometricPoint.ofPoint U y).hom ≫ jU) ≫ pullback.fst (𝔸f k) (𝔸f k)) jV)).obj M ⊗
            (etaleModuleInverseImage.{u, 0} Λ
              (pullback.fst (pullback.fst (pullback.snd (𝔸f k) (𝔸f k))
                  ((GeometricPoint.ofPoint U y).hom ≫ jU) ≫ pullback.fst (𝔸f k) (𝔸f k)) jV ≫
                pullback.fst (pullback.snd (𝔸f k) (𝔸f k))
                  ((GeometricPoint.ofPoint U y).hom ≫ jU))).obj
              ((etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
                (affineLineArtinSchreierSheaf k Λ ψ B p₀)))

/-- **The two halves give the fibre input**: on the open `U` of the Artin–Schreier half, the
fibre `X_s` of `pr₂` is a copy of `𝔸¹_Ω`, its open `C_s` over `V` is nonempty (the fibre maps
onto the `x`-line), and `t⁻¹ M ⊗ L_ψ(x s)` is locally constant with finite values, so the curve
half applies. -/
theorem fourierFibreCoinvariantVanishingInput_of_halves
    (hC : AffineLineOpenTopCohomologyVanishingInput.{u})
    (hT : FourierTwistNoConstantQuotientInput.{u}) :
    FourierFibreCoinvariantVanishingInput.{u} := by
  intro k _ _ Λ _ _ ψ B p₀ hψ hq V jV _ _ M hM
  obtain ⟨U, jU, hU, hUne, hNQ⟩ := hT k Λ ψ B p₀ hψ hq jV M hM
  refine ⟨U, jU, hU, hUne, fun y jc => ?_⟩
  let pr₁ := pullback.fst (𝔸f k) (𝔸f k)
  let pr₂ := pullback.snd (𝔸f k) (𝔸f k)
  let s := (GeometricPoint.ofPoint U y).hom ≫ jU
  let Ω := (GeometricPoint.ofPoint U y).residueField
  let f' := pullback.snd pr₂ s
  let u' := pullback.fst pr₂ s
  let w := u' ≫ pr₁
  let ι := pullback.fst w jV
  let t := pullback.snd w jV
  -- `C_s` is nonempty: the fibre maps onto the `x`-line
  have hsq : IsPullback w f' (𝔸f k) (s ≫ 𝔸f k) :=
    (IsPullback.of_hasPullback pr₂ s).paste_horiz (IsPullback.of_hasPullback (𝔸f k) (𝔸f k))
  have : Surjective (s ≫ 𝔸f k) :=
    ⟨fun x => ⟨(default : Spec (.of Ω)), Subsingleton.elim _ _⟩⟩
  have hw : Surjective w := MorphismProperty.of_isPullback (P := @Surjective) hsq.flip inferInstance
  have : Nonempty ↥(pullback w jV : Scheme.{u}) := by
    obtain ⟨v⟩ := ‹Nonempty V›
    obtain ⟨z, hz⟩ := hw.surj (jV v)
    obtain ⟨c, -⟩ : z ∈ Set.range ι.base := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨v, hz.symm⟩
    exact ⟨c⟩
  -- the twisted sheaf is locally constant with finite values
  have hN := isLocallyConstantWith_tensor Λ _ _ (isLocallyConstantWith_inverseImage Λ _ t hM)
    (isLocallyFreeEtaleModule_inverseImage Λ (ι ≫ u')
      (isLocallyFreeEtaleModule_fourierKernel k Λ ψ B p₀))
  refine hC Ω Λ f' (nonempty_affineLineFibre_iso k s) ι _ ?_ (hNQ y) jc
  refine isLocallyConstantWith_of_imp Λ ?_ hN
  rintro E ⟨E₁, E₂, h₁, h₂, rfl⟩
  have := h₁
  have := h₂.2
  exact inferInstanceAs (Module.Finite Λ (TensorProduct Λ E₁ E₂))

/-- **(L2) from its two halves**: `Stacks.EtaleCohomology.FourierGenericCoinvariantVanishingInput`
follows from the computation of `H²_c` of a locally constant sheaf on an open of `𝔸¹_Ω` as
coinvariants, and the generic absence of constant simple quotients of the twisted sheaves
`t⁻¹ M ⊗ L_ψ(x s)`. -/
theorem fourierGenericCoinvariantVanishingInput_of_halves
    (hC : AffineLineOpenTopCohomologyVanishingInput.{u})
    (hT : FourierTwistNoConstantQuotientInput.{u}) :
    FourierGenericCoinvariantVanishingInput.{u} :=
  fourierGenericCoinvariantVanishingInput_of_fibre
    (fourierFibreCoinvariantVanishingInput_of_halves hC hT)

end Stacks.EtaleCohomology

end
