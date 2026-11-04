module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.AffineSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A homomorphism out of a pullback, recovered from its effect on global sections

Let `S` be an **affine** scheme, `ℳ` a quasi-coherent `𝒪_S`-module, `g : T ⟶ S` a morphism of
schemes and `𝒩` an arbitrary `𝒪_T`-module. A morphism of `𝒪_T`-modules `g^*ℳ ⟶ 𝒩` is the same
datum as a `Γ(S, 𝒪_S)`-linear map on global sections

`Γ(S, ℳ) ⟶ Γ(S, g_*𝒩)`,

and `Γ(S, g_*𝒩)` is the module of sections of `𝒩` over `g^{-1}S`, with the ring of functions on
`S` acting through `g^♯`. Both directions hold: a morphism out of `g^*ℳ` is determined by its
effect on the pullbacks of global sections, and that effect may be prescribed arbitrarily.

This is the composite of two adjunctions, neither of which asks anything of `𝒩`:

* `Stacks.RingedSpace.pullbackAdjunction`, the adjunction `g^* ⊣ g_*` of sheaves of modules on
  the underlying ringed spaces, which identifies `g^*ℳ ⟶ 𝒩` with `ℳ ⟶ g_*𝒩`;
* the mapping property of the quasi-coherent module attached to a module over an affine base,
  `Stacks.Algebraization.sectionsTop_bijective`, which identifies `ℳ ⟶ 𝒫` with the
  `Γ(S, 𝒪_S)`-linear maps `Γ(S, ℳ) ⟶ Γ(S, 𝒫)` for an **arbitrary** `𝒪_S`-module `𝒫`.

The second is where the affineness of `S` and the quasi-coherence of `ℳ` are used, and they are
the only hypotheses: `𝒫 = g_*𝒩` is not asked to be quasi-coherent, so no quasi-compactness or
quasi-separatedness of `g` enters.

## Main definitions

* `Stacks.AlgebraicGeometry.AffineHomRecovery.homEquiv`: **the bijection** between the morphisms
  `g^*ℳ ⟶ 𝒩` and the `Γ(S, 𝒪_S)`-linear maps `Γ(S, ℳ) ⟶ Γ(S, g_*𝒩)`.

## Main results

* `Stacks.AlgebraicGeometry.AffineHomRecovery.exists_hom`: **the existence half**, a morphism
  `g^*ℳ ⟶ 𝒩` realising a prescribed linear map on global sections.
* `Stacks.AlgebraicGeometry.AffineHomRecovery.hom_ext`: **the uniqueness half**, two morphisms
  `g^*ℳ ⟶ 𝒩` with the same effect on global sections are equal.
* `Stacks.AlgebraicGeometry.AffineHomRecovery.pushforward_sectionsTop_eq`: the sections of
  `g_*𝒩` over `⊤` are the global sections of `𝒩`, on the nose.

## Implementation notes

The pullback and pushforward are the ringed-space functors `Stacks.RingedSpace.pullbackFunctor`
and `Stacks.RingedSpace.pushforwardFunctor` at `g.toLRSHom.toShHom`, the morphism of ringed
spaces underlying `g`; that is the spelling in which the twisting of a quadruple of Section 01NS
is stated. The intermediate identification is read on sections over `⊤`, which for the
pushforward is the preimage `g^{-1}⊤ = ⊤`, so no transport along an equality of opens is needed.

`SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf S.toRingedSpace)` and
`AlgebraicGeometry.Scheme.Modules S` are the same type, by `rfl`; the statements below are
phrased with whichever of the two makes the hypothesis available, and no comparison is inserted.

The module structures on the sections of a sheaf of modules over an open are the local instances
of `Stacks.Algebraization`, taken as local instances here too; without them the linear maps
below cannot be stated.

## References

* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
* [Stacks Project, Tag 01IA](https://stacks.math.columbia.edu/tag/01IA)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.AffineHomRecovery

open Stacks.RingedSpace (structureRingSheaf pullbackFunctor pushforwardFunctor pullbackAdjunction)

attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf Stacks.Algebraization.sectionsSMulCommClassΓ
  Stacks.Algebraization.sectionsModuleΓPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafVal

variable {S T : Scheme.{u}} (g : T ⟶ S)

/-- The direct image of an `𝒪_T`-module along `g`, as an `𝒪_S`-module: the ringed-space
pushforward at the morphism of ringed spaces underlying `g`. -/
abbrev pushforward (N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) : S.Modules :=
  (pushforwardFunctor g.toLRSHom.toShHom).obj N

variable (M : S.Modules) (N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))

/-- **The effect of a morphism `g^*M ⟶ N` on global sections**: the transpose of the morphism
across the adjunction `g^* ⊣ g_*` of `Stacks.RingedSpace.pullbackAdjunction`, read on sections
over `⊤`. It is `Γ(S, 𝒪_S)`-linear, the sections of `g_*N` over `⊤` being the sections of `N`
over `g^{-1}⊤` with the functions on `S` acting through `g^♯`.

Concretely, this carries a global section `x` of `M` to the image under the morphism of the
pullback of `x` along `g`, since the transpose is obtained by composing with the unit of the
adjunction. No hypothesis on `S`, `M` or `N` is needed to define it. -/
def sectionsMap (h : (pullbackFunctor g.toLRSHom.toShHom).obj M ⟶ N) :
    Γ(M, ⊤) →ₗ[Γ(S, ⊤)] Γ(pushforward g N, ⊤) :=
  ((((pullbackAdjunction g.toLRSHom.toShHom).homEquiv M N) h).val.app (op ⊤)).hom

/-- **A morphism out of the pullback of a quasi-coherent module over an affine base is the same
datum as a linear map on global sections.**

Let `S` be affine, `M` a quasi-coherent `𝒪_S`-module, `g : T ⟶ S` a morphism of schemes and `N`
an arbitrary `𝒪_T`-module. Composing the adjunction `g^* ⊣ g_*` with the mapping property of a
quasi-coherent module over an affine base identifies the morphisms `g^*M ⟶ N` with the
`Γ(S, 𝒪_S)`-linear maps `Γ(S, M) ⟶ Γ(S, g_*N)`, the bijection being `sectionsMap`.

Nothing is asked of `N`. In particular `g_*N` is not assumed quasi-coherent, which is why no
quasi-compactness or quasi-separatedness hypothesis on `g` appears. -/
@[ega "I 2.2.5" "more general"]
def homEquiv [IsAffine S] [M.IsQuasicoherent] :
    ((pullbackFunctor g.toLRSHom.toShHom).obj M ⟶ N) ≃
      (Γ(M, ⊤) →ₗ[Γ(S, ⊤)] Γ(pushforward g N, ⊤)) :=
  ((pullbackAdjunction g.toLRSHom.toShHom).homEquiv M N).trans
    (Equiv.ofBijective _ (Stacks.Algebraization.sectionsTop_bijective M (pushforward g N)))

/-- `homEquiv` sends a morphism `g^*M ⟶ N` to its effect `sectionsMap` on global sections. -/
@[simp]
theorem homEquiv_apply [IsAffine S] [M.IsQuasicoherent]
    (h : (pullbackFunctor g.toLRSHom.toShHom).obj M ⟶ N) :
    homEquiv g M N h = sectionsMap g M N h :=
  rfl

/-- **The existence half.** Every `Γ(S, 𝒪_S)`-linear map `Γ(S, M) ⟶ Γ(S, g_*N)` is the effect on
global sections of a morphism `g^*M ⟶ N`. -/
theorem exists_hom [IsAffine S] [M.IsQuasicoherent]
    (φ : Γ(M, ⊤) →ₗ[Γ(S, ⊤)] Γ(pushforward g N, ⊤)) :
    ∃ h : (pullbackFunctor g.toLRSHom.toShHom).obj M ⟶ N, sectionsMap g M N h = φ :=
  ⟨(homEquiv g M N).symm φ, (homEquiv g M N).apply_symm_apply φ⟩

/-- **The uniqueness half.** Two morphisms `g^*M ⟶ N` agreeing on global sections are equal. -/
theorem hom_ext [IsAffine S] [M.IsQuasicoherent]
    {h h' : (pullbackFunctor g.toLRSHom.toShHom).obj M ⟶ N}
    (hyp : ∀ x : Γ(M, ⊤), sectionsMap g M N h x = sectionsMap g M N h' x) :
    h = h' :=
  (homEquiv g M N).injective (LinearMap.ext hyp)

/-- **The sections of `g_*N` over `⊤` are the global sections of `N`**, on the nose: the
preimage of `⊤` is `⊤`, so no transport along an equality of opens is needed. The two differ
only in their scalars, the left-hand side being a module over `Γ(S, 𝒪_S)` through `g^♯` and the
right-hand side one over `Γ(T, 𝒪_T)`. This is what makes the linear maps of `sectionsMap`
prescribable by their values as maps `Γ(S, M) → Γ(T, N)`. -/
theorem pushforward_sectionsTop_eq : (Γ(pushforward g N, ⊤) : Type u) = (Γ(N, ⊤) : Type u) :=
  rfl

end Stacks.AlgebraicGeometry.AffineHomRecovery

end
