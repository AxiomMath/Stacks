module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.Affine
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentBijective

/-!
# Quasi-coherence of the pullback of the sheaf of relative differentials

Let `f : X ⟶ S` be a morphism of schemes and let `a : T ⟶ X` be a morphism from an **affine**
scheme which maps `T` into an affine open `W` of `X` lying over an affine open `V` of `S`. This
file proves that `a^*Ω_{X/S}` is a **quasi-coherent** sheaf of modules on `T`, and deduces the
statement that [Stacks Project, Tag 02H6] consumes: for every `g : Γ(T, ⊤)` the restriction map

`Γ(a^*Ω_{X/S}, ⊤) → Γ(a^*Ω_{X/S}, T.basicOpen g)`

exhibits the right-hand side as the localization of the left-hand side away from `g`.

## Main definitions

* `Stacks.Modules.pushforwardIsoPullbackInv` identifies the pushforward of sheaves of modules
  along an isomorphism of schemes with the pullback along its inverse.

## Main results

* `Stacks.Modules.isQuasicoherent_pushforward_of_iso`: pushforward along an isomorphism of
  schemes preserves quasi-coherence.
* `Stacks.Modules.isQuasicoherent_specModules`: the sheaf of modules on an affine scheme attached
  to a module over its global sections by `Stacks.Modules.specModules` is quasi-coherent.
* `Stacks.Modules.isQuasicoherent_of_splitMono`: on an affine scheme, a split subobject of a
  quasi-coherent module is quasi-coherent.
* `Stacks.Smooth.isQuasicoherent_pullbackCotangentSheaf`: for `T` affine and `a` mapping `T` into
  an affine open `W` of `X` lying over an affine open `V` of `S`, the sheaf `a^*Ω_{X/S}` is
  quasi-coherent.
* `Stacks.Smooth.isLocalizedModule_restrictₗ_pullbackCotangentSheaf`: the restriction of sections
  of `a^*Ω_{X/S}` to a basic open of `T` is the corresponding localization. This is the statement
  that the correction step of [Stacks Project, Tag 02H6] runs on.
* `Stacks.Smooth.isQuasicoherent_pullbackCotangentSheaf_opens`: the special case `T = W`,
  `a = W.ι`, which says that `Ω_{X/S}` restricted to an affine chart is quasi-coherent.

## Implementation notes

The affine computation `Stacks.Smooth.bijective_cotangentComparison` is *not* by itself
enough to conclude quasi-coherence: it computes the global sections of `a^*Ω_{X/S}` and says
nothing about the sections over a proper open of `T`. What it does give, when its proof is run
again rather than quoted, is a **retraction**: writing `N` for the sheaf of modules attached by
`Stacks.Modules.specModules` to the `Γ(T, ⊤)`-module `Γ(T, ⊤) ⊗[Γ(X, W)] Ω[Γ(X, W)⁄Γ(S, V)]`,
corepresentability (`Stacks.Smooth.existsUnique_hom_pullbackCotangentSheaf`) produces
`φ : a^*Ω_{X/S} ⟶ N` out of the derivation `b ↦ 1 ⊗ d b`, the adjointness of
`Stacks.Modules.specModulesLift` produces `χ : N ⟶ a^*Ω_{X/S}` out of
`Stacks.Smooth.cotangentComparison`, and the uniqueness half
`Stacks.Smooth.pullbackCotangentSheaf_hom_ext` gives `φ ≫ χ = 𝟙`. So `a^*Ω_{X/S}` is a split
subobject of `N`, i.e. the image of the idempotent `χ ≫ φ` of `N`.

That is enough, because `N` is quasi-coherent and on an affine scheme the cokernel of a morphism
between quasi-coherent modules is quasi-coherent
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_cokernel`, Tag 01IC): a split subobject is the
cokernel of `𝟙 - χ ≫ φ`. This is `Stacks.Modules.isQuasicoherent_of_splitMono`, and it is why the
reverse composite `χ ≫ φ = 𝟙` — which would need a uniqueness statement for morphisms *out of*
`N` that `Stacks.Modules.specModulesLift` does not currently carry — is never needed.

Quasi-coherence of `N` is in turn `Stacks.Modules.isQuasicoherent_specModules`. By definition
`Stacks.Modules.specModules M` is `M^~` pushed forward along `T.isoSpec.inv`, and `M^~` is
quasi-coherent in Mathlib; what is missing is that pushforward along an **isomorphism** preserves
quasi-coherence, since Mathlib and the repository only know this for pullback
(`Stacks.Modules.isQuasicoherent_pullback`, Tag 01BG) and for restriction along an open
immersion. `Stacks.Modules.pushforwardIsoPullbackInv` supplies it: for `w : Y ≅ Z` the functors
`pullback w.hom` and `pullback w.inv` are mutually inverse equivalences by
`AlgebraicGeometry.Scheme.Modules.pullbackComp` and
`AlgebraicGeometry.Scheme.Modules.pullbackId`, so `pullback w.inv` is a right adjoint of
`pullback w.hom`, and uniqueness of right adjoints identifies it with `pushforward w.hom`.

Finally, the passage from quasi-coherence to the localization statement is
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`, applied to the
affine open `⊤` of `T`; no further computation is needed.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01IC](https://stacks.math.columbia.edu/tag/01IC)
* [Stacks Project, Tag 01UM](https://stacks.math.columbia.edu/tag/01UM)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.Modules

/-! ### Pushforward along an isomorphism -/

/-- **Pushing forward along an isomorphism is pulling back along its inverse.** For an
isomorphism `w : Y ≅ Z` of schemes the functors `pullback w.hom` and `pullback w.inv` on sheaves
of modules are mutually inverse equivalences, so `pullback w.inv` is a right adjoint of
`pullback w.hom`; uniqueness of right adjoints identifies it with `pushforward w.hom`. -/
noncomputable def pushforwardIsoPullbackInv {Y Z : Scheme.{u}} (w : Y ≅ Z) :
    Scheme.Modules.pushforward w.hom ≅ Scheme.Modules.pullback w.inv :=
  Adjunction.rightAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction w.hom)
    (CategoryTheory.Equivalence.mk (Scheme.Modules.pullback w.hom)
      (Scheme.Modules.pullback w.inv)
      (Scheme.Modules.pullbackComp w.inv w.hom ≪≫
        Scheme.Modules.pullbackCongr w.inv_hom_id ≪≫ Scheme.Modules.pullbackId Z).symm
      (Scheme.Modules.pullbackComp w.hom w.inv ≪≫
        Scheme.Modules.pullbackCongr w.hom_inv_id ≪≫
          Scheme.Modules.pullbackId Y)).toAdjunction

/-- **Pushforward along an isomorphism of schemes preserves quasi-coherence.** This is
`Stacks.Modules.isQuasicoherent_pullback` (Tag 01BG) transported along
`Stacks.Modules.pushforwardIsoPullbackInv`. -/
theorem isQuasicoherent_pushforward_of_iso {Y Z : Scheme.{u}} (w : Y ≅ Z) (M : Y.Modules)
    (hM : M.IsQuasicoherent) : ((Scheme.Modules.pushforward w.hom).obj M).IsQuasicoherent :=
  Stacks.Descent.isQuasicoherent_of_iso ((pushforwardIsoPullbackInv w).app M).symm
    (isQuasicoherent_pullback w.inv M hM)

/-- **The sheaf of modules attached to a module over the global sections of an affine scheme is
quasi-coherent.** By definition `Stacks.Modules.specModules M` is `M^~` pushed forward along
`T.isoSpec.inv`, and `M^~` is quasi-coherent. -/
instance isQuasicoherent_specModules {T : Scheme.{u}} [IsAffine T] (M : ModuleCat.{u} Γ(T, ⊤)) :
    (specModules M).IsQuasicoherent :=
  isQuasicoherent_pushforward_of_iso T.isoSpec.symm (tilde M) inferInstance

/-! ### Split subobjects -/

/-- **On an affine scheme a split subobject of a quasi-coherent module is quasi-coherent.** If
`φ : M ⟶ N` has a retraction `χ` then `M` is the cokernel of the idempotent complement
`𝟙 - χ ≫ φ` of `N`, and the cokernel of a morphism between quasi-coherent modules on an affine
scheme is quasi-coherent by [Stacks Project, Tag 01IC]. -/
theorem isQuasicoherent_of_splitMono {T : Scheme.{u}} [IsAffine T] {M N : T.Modules}
    [N.IsQuasicoherent] (φ : M ⟶ N) (χ : N ⟶ M) (h : φ ≫ χ = 𝟙 M) : M.IsQuasicoherent := by
  have hp : (𝟙 N - χ ≫ φ) ≫ χ = 0 := by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, h, Category.comp_id, sub_self]
  have hπ : χ ≫ φ ≫ cokernel.π (𝟙 N - χ ≫ φ) = cokernel.π (𝟙 N - χ ≫ φ) := by
    have hc := cokernel.condition (𝟙 N - χ ≫ φ)
    rw [Preadditive.sub_comp, Category.id_comp, sub_eq_zero, Category.assoc] at hc
    exact hc.symm
  have h1 : cokernel.desc _ χ hp ≫ (φ ≫ cokernel.π (𝟙 N - χ ≫ φ))
      = 𝟙 (cokernel (𝟙 N - χ ≫ φ)) :=
    (cancel_epi (cokernel.π (𝟙 N - χ ≫ φ))).mp (by
      simp only [Category.comp_id, cokernel.π_desc_assoc, hπ])
  have h2 : (φ ≫ cokernel.π (𝟙 N - χ ≫ φ)) ≫ cokernel.desc _ χ hp = 𝟙 M := by
    simp only [Category.assoc, cokernel.π_desc, h]
  exact Stacks.Descent.isQuasicoherent_of_iso
    ⟨cokernel.desc _ χ hp, φ ≫ cokernel.π _, h1, h2⟩
    (Scheme.Modules.isQuasicoherent_cokernel _)

end Stacks.Modules

namespace Stacks.Smooth

open Stacks.Modules

variable {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X) {V : S.Opens} {W : X.Opens}

/-- **`a^*Ω_{X/S}` is quasi-coherent.** Let `f : X ⟶ S` be a morphism of schemes, let `V` be an
affine open of `S` and `W` an affine open of `X` with `W ≤ f ⁻¹ᵁ V`, and let `a : T ⟶ X` be a
morphism from an affine scheme `T` mapping into `W`. Then the pullback `a^*Ω_{X/S}` of the sheaf
of relative differentials is a quasi-coherent sheaf of modules on `T`.

This is the sheaf-theoretic form of the affine computation of [Stacks Project, Tag 01UM]; see the
implementation notes of this file for the argument, which exhibits `a^*Ω_{X/S}` as a split
subobject of the quasi-coherent sheaf `Stacks.Modules.specModules` attached to
`Γ(T, ⊤) ⊗[Γ(X, W)] Ω[Γ(X, W)⁄Γ(S, V)]`. -/
theorem isQuasicoherent_pullbackCotangentSheaf [IsAffine T] (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) (hWV : W ≤ f ⁻¹ᵁ V) (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W) :
    (pullbackCotangentSheaf f a).IsQuasicoherent := by
  let := algebraAppLE f hWV
  let := algebraAppLE a hUW
  let Mod : ModuleCat.{u} Γ(T, ⊤) :=
    ModuleCat.of Γ(T, ⊤) (Γ(T, ⊤) ⊗[Γ(X, W)] Ω[Γ(X, W)⁄Γ(S, V)])
  let N : T.Modules := specModules Mod
  let e : Mod ≃ₗ[Γ(T, ⊤)] Γ(N, (⊤ : T.Opens)) := specModulesEquiv Mod
  let := moduleAppLE a N hUW
  let := moduleAppLEBase f a N hWV hUW
  let := isScalarTowerAppLE a N hUW
  let := isScalarTowerAppLEBase f a N hWV hUW
  -- the `Γ(S, V)`-derivation `b ↦ e (1 ⊗ d b)` of `Γ(X, W)` with values in `Γ(N, ⊤)`
  let L : Ω[Γ(X, W)⁄Γ(S, V)] →ₗ[Γ(X, W)] Γ(N, (⊤ : T.Opens)) :=
    (e.toLinearMap.restrictScalars Γ(X, W)) ∘ₗ
      (TensorProduct.mk Γ(X, W) Γ(T, ⊤) Ω[Γ(X, W)⁄Γ(S, V)] 1)
  let δ : Derivation Γ(S, V) Γ(X, W) Γ(N, (⊤ : T.Opens)) :=
    L.compDer (KaehlerDifferential.D Γ(S, V) Γ(X, W))
  have hδ : ∀ b, δ b = e (1 ⊗ₜ KaehlerDifferential.D Γ(S, V) Γ(X, W) b) := fun _ ↦ rfl
  obtain ⟨φ, hφ, -⟩ := existsUnique_hom_pullbackCotangentSheaf f a N hWV hW hUW δ hV
  -- the morphism adjoint to the comparison map is a retraction of `φ`
  let χ : N ⟶ pullbackCotangentSheaf f a :=
    specModulesLift Mod (pullbackCotangentSheaf f a) (cotangentComparison f a W hWV hUW)
  have hχ := specModulesLift_app_top Mod (pullbackCotangentSheaf f a)
    (cotangentComparison f a W hWV hUW)
  have hsection : φ ≫ χ = 𝟙 _ := by
    refine pullbackCotangentSheaf_hom_ext f a _ hW hUW fun b ↦ ?_
    change (χ.app ⊤).hom ((φ.app ⊤).hom (pullbackD f a W hUW b)) = _
    rw [hφ b, hδ b, hχ (1 ⊗ₜ KaehlerDifferential.D Γ(S, V) Γ(X, W) b),
      cotangentComparison_one_tmul_D]
    rfl
  exact isQuasicoherent_of_splitMono φ χ hsection

/-- **The sections of `a^*Ω_{X/S}` over a basic open are a localization.** In the situation of
`Stacks.Smooth.isQuasicoherent_pullbackCotangentSheaf`, for every global section `g` of `T` the
restriction map

`Γ(a^*Ω_{X/S}, ⊤) → Γ(a^*Ω_{X/S}, T.basicOpen g)`

exhibits its target as the localization of its source away from `g`.

This is the input that the correction step (II) of [Stacks Project, Tag 02H6] consumes: together
with `Stacks.Smooth.isLocalizedModule_rTensor_basicOpen` and
`Stacks.Smooth.map_cotangentComparison` it turns the differences of two local lifts along a
square-zero thickening into a Čech cochain for the standard covering. -/
theorem isLocalizedModule_restrictₗ_pullbackCotangentSheaf [IsAffine T] (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) (hWV : W ≤ f ⁻¹ᵁ V) (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W) (g : Γ(T, ⊤)) :
    letI := moduleOfLE (pullbackCotangentSheaf f a) (le_top : T.basicOpen g ≤ ⊤)
    IsLocalizedModule.Away g (restrictₗ (pullbackCotangentSheaf f a)
      (le_top : T.basicOpen g ≤ ⊤)) :=
  have := isQuasicoherent_pullbackCotangentSheaf f a hV hW hWV hUW
  isLocalizedModule_restrictₗ (pullbackCotangentSheaf f a) (isAffineOpen_top T) g rfl le_top

/-- **`Ω_{X/S}` is quasi-coherent on an affine chart.** The special case `T = W` and `a = W.ι` of
`Stacks.Smooth.isQuasicoherent_pullbackCotangentSheaf`: for `W` an affine open of `X` contained
in the preimage of an affine open `V` of `S`, the pullback of `Ω_{X/S}` along the inclusion of
`W` is a quasi-coherent sheaf of modules on `W`. -/
theorem isQuasicoherent_pullbackCotangentSheaf_opens (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hWV : W ≤ f ⁻¹ᵁ V) : (pullbackCotangentSheaf f W.ι).IsQuasicoherent :=
  have : IsAffine (W : Scheme.{u}) := hW
  isQuasicoherent_pullbackCotangentSheaf f W.ι hV hW hWV (by simp)

/-- **`Ω_{X/S}` restricted to an affine chart is quasi-coherent.** Mathlib's restriction along an
open immersion is the pullback (`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`),
so this is `Stacks.Smooth.isQuasicoherent_pullbackCotangentSheaf_opens`. -/
theorem isQuasicoherent_restrict_cotangentSheaf (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hWV : W ≤ f ⁻¹ᵁ V) : ((cotangentSheaf f).restrict W.ι).IsQuasicoherent :=
  Stacks.Descent.isQuasicoherent_of_iso
    (((Scheme.Modules.restrictFunctorIsoPullback W.ι).app (cotangentSheaf f))).symm
    (isQuasicoherent_pullbackCotangentSheaf_opens f hV hW hWV)

end Stacks.Smooth

end
