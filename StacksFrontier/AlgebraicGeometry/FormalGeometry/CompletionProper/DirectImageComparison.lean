module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Pullback
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Comparison of a coherent adic system with the direct image of a completion

Let `f : X ⟶ Y` be a morphism of Noetherian schemes, let `𝒥 ⊆ 𝒪_Y` be a quasi-coherent sheaf of
ideals and set `ℐ = f^{-1}𝒥 𝒪_X`. Let `(𝒢_n)` be an object of `Coh(Y, 𝒥)`, let `𝓕` be a coherent
`𝒪_X`-module and let `β : (f^*𝒢_n) ⟶ 𝓕^` be an isomorphism in `Coh(X, ℐ)`. The composites

`γ_n : 𝒢_n ⟶ f_*f^*𝒢_n ⟶ f_*(𝓕/ℐ ⁿ⁺¹𝓕)`

of the adjunction map with `f_*β_n` form a morphism of inverse systems of `𝒪_Y`-modules, and the
levelwise kernels and cokernels of `γ` are annihilated by a power of a second quasi-coherent
sheaf of ideals `𝒦` exactly when those of the adjunction maps are.

## Main definitions

* `Stacks.Coherent.pullbackPushforwardUnitSystem` — the adjunction maps `𝒢_n ⟶ f_*f^*𝒢_n` of an
  inverse system, as a morphism of inverse systems.
* `Stacks.Coherent.directImageComparison` — **the maps `γ_n`.**

## Main results

* `Stacks.Coherent.isKernelCokernelAnnihilatedByPower_comp_iso_iff` — annihilation of the
  levelwise kernels and cokernels by a power of an ideal sheaf is unchanged by composing with an
  isomorphism of inverse systems.
* `Stacks.Coherent.pushforward_completion_obj` — the target of `γ` is `f_*(𝓕/ℐ ⁿ⁺¹𝓕)` at
  level `n`.
* `Stacks.Coherent.directImageComparison_app` — `γ_n` is the adjunction map followed by `f_*β_n`.
* `Stacks.Coherent.kernelDirectImageComparisonIso` and
  `Stacks.Coherent.cokernelDirectImageComparisonIso` — the levelwise kernel and cokernel of `γ`
  are those of the adjunction map.
* `Stacks.Coherent.isKernelCokernelAnnihilatedByPower_directImageComparison_iff` — **the
  kernel–cokernel condition on `γ` is the one on the adjunction maps.**

## References

* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 08BD](https://stacks.math.columbia.edu/tag/08BD)
* [Stacks Project, Tag 0887](https://stacks.math.columbia.edu/tag/0887)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Coherent

open Stacks.Algebraization

variable {X Y : Scheme.{u}}

/-! ### The adjunction maps of an inverse system -/

/-- **The adjunction maps `𝒢_n ⟶ f_*f^*𝒢_n` of an inverse system of `𝒪_Y`-modules**, assembled
into a morphism of inverse systems. -/
public def pullbackPushforwardUnitSystem (f : X ⟶ Y) (G : ℕᵒᵖ ⥤ Y.Modules) :
    G ⟶ G ⋙ Scheme.Modules.pullback f ⋙ Scheme.Modules.pushforward f where
  app n := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (G.obj n)
  naturality _ _ g :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality (G.map g)

/-- The `n`-th adjunction map of an inverse system is the adjunction map of its `n`-th term. -/
public theorem pullbackPushforwardUnitSystem_app (f : X ⟶ Y) (G : ℕᵒᵖ ⥤ Y.Modules) (n : ℕᵒᵖ) :
    (pullbackPushforwardUnitSystem f G).app n =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (G.obj n) :=
  rfl

/-! ### Annihilation of levelwise kernels and cokernels is an isomorphism-invariant -/

/-- **Annihilation of the levelwise kernels and cokernels by a power of `𝒦` is unchanged by
composing with an isomorphism of inverse systems.** -/
public theorem isKernelCokernelAnnihilatedByPower_comp_iso_iff (K : Y.IdealSheafData)
    {A B C : ℕᵒᵖ ⥤ Y.Modules} (α : A ⟶ B) (e : B ≅ C) :
    IsKernelCokernelAnnihilatedByPower K (α ≫ e.hom) ↔
      IsKernelCokernelAnnihilatedByPower K α := by
  have hker : ∀ k : ℕ, kernel ((α ≫ e.hom).app (op k)) ≅ kernel (α.app (op k)) := fun k ↦
    kernelCompMono (α.app (op k)) (e.hom.app (op k))
  have hcok : ∀ k : ℕ, cokernel ((α ≫ e.hom).app (op k)) ≅ cokernel (α.app (op k)) := fun k ↦
    cokernelCompIsIso (α.app (op k)) (e.hom.app (op k))
  have hiff : ∀ {M N : Y.Modules}, (M ≅ N) → ∀ t : ℕ,
      idealPowerMultiple K t M = ⊥ ↔ idealPowerMultiple K t N = ⊥ := fun e t ↦
    ⟨idealPowerMultiple_eq_bot_of_iso K e.symm t, idealPowerMultiple_eq_bot_of_iso K e t⟩
  exact exists_congr fun t ↦ and_congr_right fun _ ↦
    forall_congr' fun k ↦ and_congr (hiff (hker k) t) (hiff (hcok k) t)

/-! ### The terms of the direct image of a completion -/

/-- The direct image of the completion of `𝓕` along `ℐ` has `f_*(𝓕/ℐ ⁿ⁺¹𝓕)` at level `n`. -/
public theorem pushforward_completion_obj [IsLocallyNoetherian X] (f : X ⟶ Y)
    (J : Y.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    (((completionFunctor X (J.comap f)).obj F).obj ⋙ Scheme.Modules.pushforward f).obj (op n) =
      (Scheme.Modules.pushforward f).obj (idealPowerQuotient (J.comap f) (n + 1) F.obj) :=
  congrArg (Scheme.Modules.pushforward f).obj (completionFunctor_obj X (J.comap f) F n)

/-! ### The maps `γ_n` -/

variable [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) (J : Y.IdealSheafData)
  (G : CoherentAdicSystems J)
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
  (β : (coherentAdicPullback f J).obj G ≅ (completionFunctor X (J.comap f)).obj F)

/-- The isomorphism `β : (f^*𝒢_n) ⟶ 𝓕^`, pushed forward along `f`. -/
public def directImagePushforwardIso :
    G.obj ⋙ Scheme.Modules.pullback f ⋙ Scheme.Modules.pushforward f ≅
      ((completionFunctor X (J.comap f)).obj F).obj ⋙ Scheme.Modules.pushforward f :=
  Functor.isoWhiskerRight ((ObjectProperty.ι (IsCoherentAdicSystem (J.comap f))).mapIso β)
    (Scheme.Modules.pushforward f)

/-- **The maps `γ_n : 𝒢_n ⟶ f_*f^*𝒢_n ⟶ f_*(𝓕/ℐ ⁿ⁺¹𝓕)`**, as a morphism of inverse systems of
`𝒪_Y`-modules: the adjunction map followed by `f_*β_n`. -/
public def directImageComparison :
    G.obj ⟶ ((completionFunctor X (J.comap f)).obj F).obj ⋙ Scheme.Modules.pushforward f :=
  pullbackPushforwardUnitSystem f G.obj ≫ (directImagePushforwardIso f J G F β).hom

/-- `γ_n` is the adjunction map followed by `f_*β_n`. -/
public theorem directImageComparison_app (n : ℕᵒᵖ) :
    (directImageComparison f J G F β).app n =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (G.obj.obj n) ≫
        (Scheme.Modules.pushforward f).map (β.hom.hom.app n) :=
  rfl

/-- The levelwise kernel of `γ` is the kernel of the adjunction map. -/
public def kernelDirectImageComparisonIso (n : ℕᵒᵖ) :
    kernel ((directImageComparison f J G F β).app n) ≅
      kernel ((pullbackPushforwardUnitSystem f G.obj).app n) :=
  kernelCompMono ((pullbackPushforwardUnitSystem f G.obj).app n)
    ((directImagePushforwardIso f J G F β).hom.app n)

/-- The levelwise cokernel of `γ` is the cokernel of the adjunction map. -/
public def cokernelDirectImageComparisonIso (n : ℕᵒᵖ) :
    cokernel ((directImageComparison f J G F β).app n) ≅
      cokernel ((pullbackPushforwardUnitSystem f G.obj).app n) :=
  cokernelCompIsIso ((pullbackPushforwardUnitSystem f G.obj).app n)
    ((directImagePushforwardIso f J G F β).hom.app n)

/-- **The kernel–cokernel condition on `γ` is the kernel–cokernel condition on the adjunction
maps.** Let `f : X ⟶ Y` be a morphism of Noetherian schemes, let `𝒥, 𝒦 ⊆ 𝒪_Y` be quasi-coherent
sheaves of ideals and set `ℐ = f^{-1}𝒥 𝒪_X`. Let `(𝒢_n)` be an object of `Coh(Y, 𝒥)`, let `𝓕` be
a coherent `𝒪_X`-module and let `β : (f^*𝒢_n) ⟶ 𝓕^` be an isomorphism in `Coh(X, ℐ)`. The maps

`γ_n : 𝒢_n ⟶ f_*f^*𝒢_n ⟶ f_*(𝓕/ℐ ⁿ⁺¹𝓕)`

have their levelwise kernels and cokernels annihilated by a power of `𝒦` exactly when the
adjunction maps `𝒢_n ⟶ f_*f^*𝒢_n` do. -/
public theorem isKernelCokernelAnnihilatedByPower_directImageComparison_iff
    (K : Y.IdealSheafData) :
    IsKernelCokernelAnnihilatedByPower K (directImageComparison f J G F β) ↔
      IsKernelCokernelAnnihilatedByPower K (pullbackPushforwardUnitSystem f G.obj) :=
  isKernelCokernelAnnihilatedByPower_comp_iso_iff K (pullbackPushforwardUnitSystem f G.obj)
    (directImagePushforwardIso f J G F β)

end Stacks.Coherent

end
