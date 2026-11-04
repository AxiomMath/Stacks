module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.AffineColimitReflexivePower
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.AffineReflexivePowerTransition
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.AffineSectionLocusPrimes
public import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 0EBQ]: the open `U` and the colimit of the reflexive powers

Let `A` be a Noetherian normal domain, `M` a finite reflexive `A`-module of rank one, `s ∈ M`
nonzero, and `𝔭₁, …, 𝔭_r` the height one primes of `A` in the support of `M ⧸ A·s`. Let `U` be
the open `AlgebraicGeometry.sectionIsomorphismOpen (Spec A) (M^~) s` of [Stacks, Tag 0EBN]
attached to the section `s` of `M^~` on `Spec A`. Then

`U = Spec(A) \ (V(𝔭₁) ∪ ⋯ ∪ V(𝔭_r))`   and   `Γ(U, 𝒪_U) = colim M^{[n]}`,

where `M^{[0]} = A`, `M^{[1]} = M` and `M^{[n+1]} = (M ⊗_A M^{[n]})^{∨∨}`, the transitions being
multiplication by `s`.

## Main definitions

* `AlgebraicGeometry.reflexivePowerSystemTildeIso`: the isomorphism of the sheaf-level and the
  module-level reflexive power systems.
* `AlgebraicGeometry.moduleColimitCocone`: the cocone of `A`-modules with vertex `Γ(U, 𝒪_U)` and
  `n`-th leg out of `M^{[n]}`.

## Main results

* `AlgebraicGeometry.isColimitModuleColimitCocone`: `Γ(U, 𝒪_U)` is the colimit of
  `A → M → M^{[2]} → ⋯`.
* `AlgebraicGeometry.objective_0EBQ`: [Stacks, Tag 0EBQ], both displays.

## References

* [Stacks Project, Tag 0EBQ](https://stacks.math.columbia.edu/tag/0EBQ)
* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 0EBP](https://stacks.math.columbia.edu/tag/0EBP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.ReflexivePowers
open Stacks.AlgebraicGeometry.ReflexiveHeightOnePrimes

universe u

namespace AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.isNormal_spec
attribute [local instance] AlgebraicGeometry.tilde_isCoherent_of_finite

section Systems

variable (R : CommRingCat.{u}) [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R]
  (M : ModuleCat.{u} R) [Module.Finite R M] [Module.IsReflexive R M] (s : M)
  [Nonempty (AlgebraicGeometry.sectionIsomorphismOpen (Spec R) (tilde M)
    (tildeGlobalSection M s)).toScheme]

/-- The comparison of the sheaf-level and the module-level reflexive power systems, as a
natural transformation: at `n` it is `reflexivePowerTildeIso`. -/
def reflexivePowerSystemTildeHom :
    reflexivePowerSystem (tilde M) (tildeGlobalSection M s) ⟶
      Stacks.AlgebraicGeometry.ModuleReflexivePower.reflexivePowerSystem M s ⋙
        tilde.functor R :=
  NatTrans.ofSequence (fun n => (reflexivePowerTildeIso R M n).hom) (fun n => by
    simp only [reflexivePowerSystem_map_succ, Functor.comp_map,
      Stacks.AlgebraicGeometry.ModuleReflexivePower.reflexivePowerSystem_map_succ]
    exact reflexivePowerTildeIso_transition R M s n)

/-- The comparison `reflexivePowerSystemTildeHom` of the sheaf-level and the module-level
reflexive power systems is an isomorphism. -/
instance isIso_reflexivePowerSystemTildeHom :
    IsIso (reflexivePowerSystemTildeHom R M s) := by
  have : ∀ n : ℕ, IsIso ((reflexivePowerSystemTildeHom R M s).app n) :=
    fun n => (inferInstance : IsIso (reflexivePowerTildeIso R M n).hom)
  exact NatIso.isIso_of_isIso_app _

/-- The sheaf-level reflexive power system of [Stacks, Tag 0EBN] for `M^~` is isomorphic to the
associated sheaf of the module-level reflexive power system for `M`. -/
def reflexivePowerSystemTildeIso :
    reflexivePowerSystem (tilde M) (tildeGlobalSection M s) ≅
      Stacks.AlgebraicGeometry.ModuleReflexivePower.reflexivePowerSystem M s ⋙
        tilde.functor R :=
  asIso (reflexivePowerSystemTildeHom R M s)

/-- The module-level reflexive power system is isomorphic to the system of global sections of
the sheaf-level one. -/
def reflexivePowerGammaSystemIso :
    Stacks.AlgebraicGeometry.ModuleReflexivePower.reflexivePowerSystem M s ≅
      reflexivePowerSystem (tilde M) (tildeGlobalSection M s) ⋙ moduleSpecΓFunctor :=
  (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ tilde.toTildeΓNatIso ≪≫
    Functor.isoWhiskerRight (reflexivePowerSystemTildeIso R M s).symm moduleSpecΓFunctor

end Systems

section Objective

variable (R : CommRingCat.{u}) [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R]
  (M : ModuleCat.{u} R) [Module.Finite R M] [Module.IsReflexive R M]

/-- The cocone of `A`-modules with vertex `Γ(U, 𝒪_U)` and `n`-th leg out of the module-level
reflexive power `M^{[n]}`, the transitions being multiplication by `s`. -/
def moduleColimitCocone (hrank : Module.rank R M = 1) {s : M} (hs : s ≠ 0) :
    Cocone (Stacks.AlgebraicGeometry.ModuleReflexivePower.reflexivePowerSystem M s) :=
  have := nonempty_sectionIsomorphismOpen_tilde M hrank hs
  (Cocone.precompose (reflexivePowerGammaSystemIso R M s).hom).obj
    (gammaReflexivePowerCocone M (tildeGlobalSection M s))

/-- `Γ(U, 𝒪_U)` is the colimit of `A → M → M^{[2]} → ⋯`, the system of module-level reflexive
powers with transitions multiplication by `s`. -/
def isColimitModuleColimitCocone (hrank : Module.rank R M = 1) {s : M} (hs : s ≠ 0) :
    IsColimit (moduleColimitCocone R M hrank hs) :=
  have := nonempty_sectionIsomorphismOpen_tilde M hrank hs
  (IsColimit.precomposeHomEquiv (reflexivePowerGammaSystemIso R M s) _).symm
    (isColimitGammaReflexivePowerCocone M (tildeGlobalSection M s))

/-- For `A` a Noetherian normal domain, `M` a finite reflexive `A`-module of rank one and `s ∈ M`
nonzero, the open `U` of [Stacks, Tag 0EBN] is the complement of `V(𝔭₁) ∪ ⋯ ∪ V(𝔭_r)` for the
height one primes `𝔭ᵢ` of `A` in the support of `M ⧸ A·s`, and `Γ(U, 𝒪_U)` is the colimit of the
reflexive powers `M^{[n]}`. -/
@[stacks 0EBQ]
theorem objective_0EBQ (hrank : Module.rank R M = 1) {s : M} (hs : s ≠ 0) :
    ((AlgebraicGeometry.sectionIsomorphismOpen (Spec R) (tilde M)
          (tildeGlobalSection M s) : Set (Spec R)) =
        (heightOneSupportZeroLocus R s)ᶜ) ∧
      Nonempty (IsColimit (moduleColimitCocone R M hrank hs)) :=
  ⟨(sectionIsomorphismLocus_tilde_eq M s).trans
    (sectionIsomorphismPrimes_eq_compl_heightOneSupportZeroLocus hrank hs),
    ⟨isColimitModuleColimitCocone R M hrank hs⟩⟩

end Objective

end AlgebraicGeometry

end
