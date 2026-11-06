module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierCoefficientVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LissePermutationDirectImage
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategoryTransitivity
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleConnectedObjects
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleGaloisCategory

/-!
# A constant simple sheaf twisted by a connected Artin–Schreier cover has no sections

Let `Spec A` be connected and `g ∈ A` such that the Artin–Schreier cover `t^q - t = g` of
`Spec A` is connected, and let `E` be a simple module over a finite commutative ring `Λ`. For an
additive character `ψ` of `k = 𝔽_q` with `∑ ψ = 0` and `q` a unit of `Λ`, every morphism from the
constant sheaf `E` to `E ⊗ L_ψ(g)` vanishes
(`Stacks.ArtinSchreier.eq_zero_of_hom_constantSheaf_tensor_artinSchreierLevelSheaf`).

Indeed `E ⊗ L_ψ(g)` is the lisse sheaf of `E` with `π₁` acting through the Artin–Schreier character
`ψ(-χ)` (`Stacks.EtaleCohomology.nonempty_constantSheaf_tensor_lisseEtaleSheaf_iso`), the constant
sheaf is the lisse sheaf with trivial action, and lisse sheaves are fully faithful in their
representations: a nonzero morphism would be an isomorphism of the simple `E` intertwining the
trivial action with the twisted one. The character `χ : π₁ → k` of a connected torsor is onto
(`AlgebraicGeometry.TorsorCover.surjective_character`), so `ψ(a)` would act trivially on `E` for
every `a ∈ k`, and `q e = ∑ ψ(a) e = 0` would force `E = 0`.

This is the non-triviality of the sheaves `L_ψ(s x)`, `s ≠ 0`, on opens of the affine line over an
algebraically closed field, in the Artin–Schreier half of the generic coinvariant vanishing in
Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `AlgebraicGeometry.TorsorCover.surjective_character`.
* `Stacks.EtaleCohomology.nonempty_constantSheaf_tensor_lisseEtaleSheaf_iso`.
* `Stacks.EtaleCohomology.eq_zero_of_hom_constantSheaf_lisseEtaleSheaf_characterTwist`.
* `Stacks.ArtinSchreier.eq_zero_of_hom_constantSheaf_tensor_artinSchreierLevelSheaf`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.TorsorCover

variable {X : Scheme.{u}} [ConnectedSpace X] {K : Type*} [AddCommGroup K]

/-- **The character of a connected torsor cover is onto**: `π₁` acts transitively on the fibre of
the connected cover, and the character records the translation carrying the base point to its
image. -/
theorem surjective_character (T : TorsorCover X K) [ConnectedSpace T.cover.left]
    (x : GeometricPoint X) (p₀ : (finiteEtaleFiberFunctor x).obj T.cover) :
    Function.Surjective (T.character x p₀) := by
  intro a
  have : PreGaloisCategory.IsConnected T.cover := isConnected_of_connectedSpace_left T.cover
  obtain ⟨σ, hσ⟩ := Stacks.FundamentalGroup.exists_aut_app_eq_of_isConnected
    (finiteEtaleFiberFunctor x) T.cover p₀
      ((finiteEtaleFiberFunctor x).map (T.τ (Multiplicative.toAdd a)) p₀)
  exact ⟨σ, Multiplicative.toAdd.injective (T.character_eq_of_smul x p₀ σ p₀ hσ)⟩

end AlgebraicGeometry.TorsorCover

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (Λ : Type) [CommRing Λ] [Finite Λ]

/-- Sheafification of étale sheaves of `Λ`-modules, at the universes of `EtaleModules.{u, 0}`. -/
local instance hasSheafify_etaleModules_twistNoInvariants (Y : Scheme.{u}) :
    HasSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  hasSheafifyEtale Y Λ

omit [Finite Λ] in
/-- Twisting by the trivial character gives the trivial action. -/
private theorem characterTwistContinuousModule_one_ρ (M : ModuleCat.{u + 1} Λ) [Finite M]
    (g : EtaleFundamentalGroup X.1 x) :
    (characterTwistContinuousModule Λ (1 : EtaleFundamentalGroup X.1 x →* Λˣ)
      (isOpen_ker_one Λ) M).obj.obj.obj.ρ g = 1 := by
  refine End.ext (ModuleCat.hom_ext (LinearMap.ext fun v => ?_))
  change (((1 : EtaleFundamentalGroup X.1 x →* Λˣ) g : Λˣ) : Λ) • v = v
  rw [MonoidHom.one_apply, Units.val_one, one_smul]

/-- **`M ⊗ ℱ_{Λ_χ} ≅ ℱ_{M_χ}`**: the constant sheaf on a finite `Λ`-module `M` tensored with the
lisse sheaf of a character `χ` of `π₁(X, x̄)` is the lisse sheaf of `M` with `π₁` acting through
`χ`. The constant sheaf is the lisse sheaf of `M` with trivial action, and multiplication
`M × Λ_χ → M_χ` is an equivariant bilinear map inducing an isomorphism on the fibres. -/
theorem nonempty_constantSheaf_tensor_lisseEtaleSheaf_iso
    (χ : EtaleFundamentalGroup X.1 x →* Λˣ)
    (hχ : IsOpen (χ.ker : Set (EtaleFundamentalGroup X.1 x)))
    (M : ModuleCat.{u + 1} Λ) [Finite M] :
    Nonempty (etaleModuleConstantSheaf Λ M X.1 ⊗
        (lisseEtaleSheaf B X x Λ).obj (characterContinuousModule Λ χ hχ) ≅
      (lisseEtaleSheaf B X x Λ).obj (characterTwistContinuousModule Λ χ hχ M)) := by
  let G := EtaleFundamentalGroup X.1 x
  let M₁ := characterTwistContinuousModule Λ (1 : G →* Λˣ) (isOpen_ker_one Λ) M
  let Lχ := characterContinuousModule Λ χ hχ
  let Mχ := characterTwistContinuousModule Λ χ hχ M
  obtain ⟨e₁⟩ := nonempty_lisseEtaleSheaf_iso_constantSheaf_of_trivial B X x Λ M₁
    (characterTwistContinuousModule_one_ρ B X x Λ M)
  let μ : M₁.obj.obj.obj.V →ₗ[Λ] Lχ.obj.obj.obj.V →ₗ[Λ] Mχ.obj.obj.obj.V :=
    LinearMap.mk₂ Λ (fun (v : M) (a : ULift.{u + 1} Λ) => a.down • v)
      (fun v₁ v₂ a => smul_add a.down v₁ v₂) (fun c v a => smul_comm a.down c v)
      (fun v a₁ a₂ => add_smul a₁.down a₂.down v)
      (fun c v a => by
        change (c * a.down) • v = c • a.down • v
        rw [mul_smul])
  have hμ : ∀ (g : G) (a : M₁.obj.obj.obj.V) (b : Lχ.obj.obj.obj.V),
      μ ((M₁.obj.obj.obj.ρ g).asHom.hom a) ((Lχ.obj.obj.obj.ρ g).asHom.hom b) =
        (Mχ.obj.obj.obj.ρ g).asHom.hom (μ a b) := fun g a b => by
    change ((χ g : Λ) * b.down) • ((((1 : G →* Λˣ) g : Λˣ) : Λ) • (a : M)) =
      (χ g : Λ) • (b.down • (a : M))
    rw [MonoidHom.one_apply, Units.val_one, one_smul, mul_smul]
  have hsurj : ∀ r : Mχ.obj.obj.obj.V, ∃ p q, μ p q = r :=
    fun r => ⟨r, ULift.up 1, one_smul Λ (r : M)⟩
  have hcard : Nat.card (TensorProduct Λ M₁.obj.obj.obj.V Lχ.obj.obj.obj.V) ≤
      Nat.card Mχ.obj.obj.obj.V :=
    (Nat.card_congr ((TensorProduct.congr (LinearEquiv.refl Λ M)
      (ULift.moduleEquiv (R := Λ))).trans (TensorProduct.rid Λ M)).toEquiv).le
  exact ⟨whiskerRightIso e₁.symm _ ≪≫
    @asIso _ _ _ _ (lisseEtaleSheafTensorHom B X x Λ μ hμ)
      (isIso_lisseEtaleSheafTensorHom B X x Λ μ hμ hsurj hcard)⟩

/-- **A simple module twisted by a character acting nontrivially has no invariant sections**:
every morphism from the constant sheaf `E̲` to the lisse sheaf of `E` with `π₁` acting through
`χ` vanishes, as soon as some `χ(g)` moves some element of the simple module `E`. Lisse sheaves
are fully faithful in their representations, and a nonzero equivariant endomorphism of the simple
`E` from the trivial action to the twisted one is onto, so the twisted action would be trivial. -/
theorem eq_zero_of_hom_constantSheaf_lisseEtaleSheaf_characterTwist
    (χ : EtaleFundamentalGroup X.1 x →* Λˣ)
    (hχ : IsOpen (χ.ker : Set (EtaleFundamentalGroup X.1 x)))
    (E : ModuleCat.{u + 1} Λ) [Finite E] [IsSimpleModule Λ E]
    (hχE : ∃ (g : EtaleFundamentalGroup X.1 x) (e : E), (χ g : Λ) • e ≠ e)
    (φ : etaleModuleConstantSheaf Λ E X.1 ⟶
      (lisseEtaleSheaf B X x Λ).obj (characterTwistContinuousModule Λ χ hχ E)) : φ = 0 := by
  let G := EtaleFundamentalGroup X.1 x
  let E₁ := characterTwistContinuousModule Λ (1 : G →* Λˣ) (isOpen_ker_one Λ) E
  obtain ⟨e₁⟩ := nonempty_lisseEtaleSheaf_iso_constantSheaf_of_trivial B X x Λ E₁
    (characterTwistContinuousModule_one_ρ B X x Λ E)
  let Eχ := characterTwistContinuousModule Λ χ hχ E
  -- every equivariant map from the trivial action to the twisted one vanishes
  have key : ∀ f : E₁ ⟶ Eχ, f.hom.hom.hom.hom.hom = 0 := fun f => by
    let f₀ : E →ₗ[Λ] E := f.hom.hom.hom.hom.hom
    have hf₀ : ∀ (g : G) (v : E), f₀ v = (χ g : Λ) • f₀ v := fun g v => by
      have h := ConcreteCategory.congr_hom (f.hom.hom.hom.comm g) v
      change f₀ ((((1 : G →* Λˣ) g : Λˣ) : Λ) • v) = (χ g : Λ) • f₀ v at h
      rwa [MonoidHom.one_apply, Units.val_one, one_smul] at h
    by_contra hne
    obtain ⟨g, e, he⟩ := hχE
    obtain ⟨v, rfl⟩ := LinearMap.range_eq_top.1
      ((eq_bot_or_eq_top (LinearMap.range f₀)).resolve_left
        fun h => hne (LinearMap.range_eq_bot.1 h)) e
    exact he (hf₀ g v).symm
  have hext : ∀ f f' : E₁ ⟶ Eχ, f = f' := fun f f' => by
    apply ObjectProperty.hom_ext
    apply InducedCategory.hom_ext
    apply InducedCategory.hom_ext
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    rw [key f, key f']
  let hff := lisseEtaleSheafFullyFaithful B X x Λ
  have hφ' : e₁.hom ≫ φ = 0 := by
    rw [← hff.map_preimage (e₁.hom ≫ φ), ← hff.map_preimage 0,
      hext (hff.preimage (e₁.hom ≫ φ)) (hff.preimage 0)]
  refine (e₁.inv_hom_id_assoc φ).symm.trans ?_
  rw [hφ', comp_zero]
  rfl

end Stacks.EtaleCohomology

namespace Stacks.ArtinSchreier

open Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules

variable (k : Type u) [Field k] [Fintype k] (A : Type u) [CommRing A] [Algebra k A] (g : A)
  [ConnectedSpace (Spec (.of A))] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u}) (hX : schemeSizeBelow B.cutoff (Spec (.of A)))

/-- Sheafification of étale sheaves of `Λ`-modules, at the universes of `EtaleModules.{u, 0}`. -/
local instance hasSheafify_etaleModules_artinSchreierTwist (Y : Scheme.{u}) :
    HasSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  hasSheafifyEtale Y Λ

/-- **A constant simple sheaf twisted by a connected Artin–Schreier cover has no sections.** If
the Artin–Schreier cover `t^q - t = g` of the connected `Spec A` is connected, `∑ ψ = 0` and
`q = #k` is a unit of `Λ`, every morphism from the constant sheaf on a simple `Λ`-module `E` to
`E̲ ⊗ L_ψ(g)` vanishes: the Artin–Schreier character is onto `k`, and a trivial action of all the
`ψ(a)` on `E` would give `q e = ∑ ψ(a) e = 0`. -/
theorem eq_zero_of_hom_constantSheaf_tensor_artinSchreierLevelSheaf
    [ConnectedSpace (cover k A g).left] (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) (x : GeometricPoint (Spec (.of A)))
    (p₀ : (finiteEtaleFiberFunctor x).obj (cover k A g))
    (E : ModuleCat.{u + 1} Λ) [Finite E] [IsSimpleModule Λ E]
    (φ : etaleModuleConstantSheaf Λ E (Spec (.of A)) ⟶
      etaleModuleConstantSheaf Λ E (Spec (.of A)) ⊗ artinSchreierLevelSheaf k A g Λ ψ B hX x p₀) :
    φ = 0 := by
  have : ConnectedSpace (specObject A B hX).1 := inferInstanceAs (ConnectedSpace (Spec (.of A)))
  let χ := artinSchreierCharacter k A g ψ x p₀
  let hχ := isOpen_ker_artinSchreierCharacter k A g Λ ψ x p₀
  obtain ⟨e₀⟩ := nonempty_constantSheaf_tensor_lisseEtaleSheaf_iso B (specObject A B hX) x Λ χ hχ E
  let e : etaleModuleConstantSheaf Λ E (Spec (.of A)) ⊗
        artinSchreierLevelSheaf k A g Λ ψ B hX x p₀ ≅
      (lisseEtaleSheaf B (specObject A B hX) x Λ).obj (characterTwistContinuousModule Λ χ hχ E) :=
    e₀
  have hχE : ∃ (σ : EtaleFundamentalGroup (specObject A B hX).1 x) (v : E), (χ σ : Λ) • v ≠ v := by
    by_contra hall
    simp only [not_exists, ne_eq, not_not] at hall
    have : ConnectedSpace (torsorCover k A g).cover.left := ‹ConnectedSpace (cover k A g).left›
    have hsurj := (torsorCover k A g).surjective_character x p₀
    have hfix : ∀ (a : k) (v : E), ψ a • v = v := fun a v => by
      obtain ⟨σ, hσ⟩ := hsurj (Multiplicative.ofAdd (-a))
      have h := hall σ v
      rwa [artinSchreierCharacter_apply, hσ, toAdd_ofAdd, neg_neg] at h
    have := IsSimpleModule.nontrivial Λ E
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    apply hv
    have hsum : (∑ a : k, ψ a) • v = (Fintype.card k : Λ) • v := by
      rw [Finset.sum_smul, Finset.sum_congr rfl fun a _ => hfix a v, Finset.sum_const,
        Finset.card_univ, ← Nat.cast_smul_eq_nsmul Λ]
    rw [hψ, zero_smul] at hsum
    exact hq.smul_left_cancel.1 (hsum.symm.trans (smul_zero _).symm)
  have h0 := eq_zero_of_hom_constantSheaf_lisseEtaleSheaf_characterTwist B (specObject A B hX) x Λ
    χ hχ E hχE (φ ≫ e.hom)
  rw [← cancel_mono e.hom, h0, zero_comp]

end Stacks.ArtinSchreier

end
