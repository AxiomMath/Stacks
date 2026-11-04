module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupSituation

/-!
# The dictionary `Hom_{𝒪_X}(p^*M, 𝒢) = Hom_A(M, Γ(X, 𝒢))` on the blowup

Let `p : X → Spec(A)` be the blowing up of `Spec(A)` in `I` and, for an `A`-module `M`, let
`p^*M` be the pullback of `M~`. The proofs of [Stacks, Tags 0GAC and 0GAD] turn an `A`-linear map
`φ : M → I^q/I^{q+n}` into a map of sheaves `χ : p^*M → 𝒪_{Yₙ}(q)` ("using this and pulling back
`φ` we obtain a map `χ`"), and read a map of sheaves back as a homomorphism of modules through
Tag 0GA7(2). Both directions are one adjunction:

`(M ↦ p^*M) = (M ↦ M~) ⋙ p^*  ⊣  Γ(X, -)`,

the composite of `~ ⊣ Γ(Spec A, -)` and `p^* ⊣ p_*`, since `Γ(Spec A, p_*𝒢) = Γ(X, 𝒢)` as
`A`-modules (`blowupPullbackAdjunction`). For `𝒢 = 𝒪_{Yₙ}(q)` and `q ≥ q(S)` the target
`Γ(X, 𝒪_{Yₙ}(q)) = H⁰(X, 𝒪_{Yₙ}(q))` is `I^q/I^{q+n}` by Tag 0GA7(2), which gives the
dictionary `Hom_{𝒪_X}(p^*M, 𝒪_{Yₙ}(q)) = Hom_A(M, I^q/I^{q+n})`
(`pullbackThickeningHomEquiv`).

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.blowupPullback`: `M ↦ p^*M`, `ModuleCat A ⥤ Mod(𝒪_X)`.
* `Stacks.LocalCohomology.UniformityIII.blowupPullbackAdjunction`: `p^* ⊣ Γ(X, -)`.
* `Stacks.LocalCohomology.UniformityIII.pullbackThickeningHomEquiv`: the dictionary at
  `𝒪_{Yₙ}(q)`, for `q ≥ q₀`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Stacks.LocalCohomology.UniformityIII

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- **`M ↦ p^*M`**: the pullback to the blowup of the quasi-coherent module `M~` attached to an
`A`-module. -/
noncomputable abbrev blowupPullback : ModuleCat.{u} A ⥤ (blowupScheme I).Modules :=
  tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.pullback (Stacks.Blowup.toSpec I)

/-- `Γ(Spec A, p_*𝒢) = Γ(X, 𝒢)` as `A`-modules: both are the sections of `𝒢` over `X`, with `A`
acting through `A = Γ(Spec A, 𝒪) → Γ(X, 𝒪)`. -/
noncomputable def pushforwardΓIso :
    Scheme.Modules.pushforward (Stacks.Blowup.toSpec I) ⋙ moduleSpecΓFunctor ≅
      blowupΓmod I :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- **`p^* ⊣ Γ(X, -)`**: a map of sheaves `p^*M ⟶ 𝒢` on the blowup is an `A`-linear map
`M → Γ(X, 𝒢)`. It is `~ ⊣ Γ(Spec A, -)` composed with `p^* ⊣ p_*`. -/
noncomputable def blowupPullbackAdjunction : blowupPullback I ⊣ blowupΓmod I :=
  (tilde.adjunction.comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Stacks.Blowup.toSpec I))).ofNatIsoRight
    (pushforwardΓIso I)

/-- The dictionary is natural in the module: precomposing a map of sheaves with `p^*u` is
precomposing the corresponding homomorphism with `u`. -/
theorem blowupPullbackAdjunction_homEquiv_naturality_left {M M' : ModuleCat.{u} A}
    (u : M ⟶ M') {G : (blowupScheme I).Modules} (g : (blowupPullback I).obj M' ⟶ G) :
    (blowupPullbackAdjunction I).homEquiv M G ((blowupPullback I).map u ≫ g) =
      u ≫ (blowupPullbackAdjunction I).homEquiv M' G g :=
  Adjunction.homEquiv_naturality_left _ _ _

/-- The dictionary is natural in the sheaf: postcomposing a map of sheaves with `t : 𝒢 ⟶ 𝒢'` is
postcomposing the corresponding homomorphism with `Γ(X, t)`. -/
theorem blowupPullbackAdjunction_homEquiv_naturality_right {M : ModuleCat.{u} A}
    {G G' : (blowupScheme I).Modules} (g : (blowupPullback I).obj M ⟶ G) (t : G ⟶ G') :
    (blowupPullbackAdjunction I).homEquiv M G' (g ≫ t) =
      (blowupPullbackAdjunction I).homEquiv M G g ≫ (blowupΓmod I).map t :=
  Adjunction.homEquiv_naturality_right _ _ _

variable [IsNoetherianRing A]

/-- `Γ(X, 𝒪_{Yₙ}(q)) = I^q/I^{q+n}` for `q ≥ q₀` and `n = m + 1 ≥ 1`, with `q₀` having the defining
property of `q(S)`: global sections are `H⁰` (`blowupΓmodToH0`), which is `I^q/I^{q+n}` by
Tag 0GA7(2). -/
noncomputable def thickeningSectionsEquiv {q₀ : ℕ} (h : IsBaseThreshold I q₀) (m : ℕ) {q : ℕ}
    (hq : q₀ ≤ q) :
    (blowupΓmod I).obj (thickeningTwist I (m + 1) q) ≃ₗ[A] powQuot I q (m + 1) :=
  (LinearEquiv.ofBijective (blowupΓmodToH0 I (thickeningTwist I (m + 1) q)).hom
    (bijective_blowupΓmodToH0 I _)).trans
    (LinearEquiv.ofBijective (cdivMod I m q) (bijective_cdivMod_of_le I h hq)).symm

/-- **The dictionary of Tags 0GAC and 0GAD.** For `q ≥ q₀`, with `q₀` having the defining
property of `q(S)`, and `n = m + 1 ≥ 1`, maps of sheaves `p^*M ⟶ 𝒪_{Yₙ}(q)` on the blowup are the
`A`-linear maps `M → I^q/I^{q+n}`: the adjunction `p^* ⊣ Γ(X, -)`, followed by
`Γ(X, 𝒪_{Yₙ}(q)) = I^q/I^{q+n}` (`thickeningSectionsEquiv`). -/
noncomputable def pullbackThickeningHomEquiv {q₀ : ℕ} (h : IsBaseThreshold I q₀) (m : ℕ)
    {q : ℕ} (hq : q₀ ≤ q) (M : ModuleCat.{u} A) :
    ((blowupPullback I).obj M ⟶ thickeningTwist I (m + 1) q) ≃ (M →ₗ[A] powQuot I q (m + 1)) :=
  ((blowupPullbackAdjunction I).homEquiv M _).trans
    { toFun := fun g => (thickeningSectionsEquiv I h m hq).toLinearMap ∘ₗ g.hom
      invFun := fun φ =>
        (ModuleCat.ofHom φ ≫ (thickeningSectionsEquiv I h m hq).symm.toModuleIso.hom :
          M ⟶ (blowupΓmod I).obj (thickeningTwist I (m + 1) q))
      left_inv := fun g => by
        ext z
        simp
      right_inv := fun φ => by
        ext z
        simp }

end Stacks.LocalCohomology.UniformityIII

end
