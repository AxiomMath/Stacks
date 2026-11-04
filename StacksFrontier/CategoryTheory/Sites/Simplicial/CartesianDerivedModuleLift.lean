module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianDerivedModuleProjectionVanishing
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSystemOfObject
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleResolutionDerivedTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedMapVanishing
public import StacksFrontier.CategoryTheory.Triangulated.SequentialPostnikovSystems
import StacksCore.Tactic.StacksAttribute

/-!
# The tower step of Stacks 0D9S for sheaves of modules

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site. Stacks 0D9S says that, over flat structure-sheaf transitions, a morphism of the
simplicial systems of `D(O)` attached to two objects `K`, `K'` of `D(O)` comes from a morphism
`K ⟶ K'`, provided `K` is cartesian and `Hom(K_i[i - 1], K'_i) = 0` for `i > 1`. Its proof is, in
the source's own words, "exactly the same as the proof of Lemma 0D9K except using Lemma 0D9Q
instead of Lemma 0D9I".

This file is the triangulated step of that proof: the construction step of Stacks 0D9K, stated
for an arbitrary complex and an arbitrary exact functor in
`StacksFrontier/CategoryTheory/Sites/Simplicial/CartesianDerivedMapVanishing.lean`, instantiated at
the module resolution of Stacks 0D9B and the functor `- ⊗^L_O K`. A map `b : X₀ ⟶ K'` out of the
bottom term of the Postnikov system whose composite with the differential `X₁ ⟶ X₀` vanishes
extends over the derived colimit, as soon as `Hom(X_{i+1}[i], K') = 0` for `i > 0`; the latter is
hypothesis (3) of Stacks 0D9S read through the identification `X_i = g_{i!}K_i` of Stacks 0D9E (2).
The choice of `b` and the reading of the conclusion are made in
`StacksFrontier/CategoryTheory/Sites/Simplicial/CartesianDerivedModuleLiftConstruction.lean`, and
Stacks 0D9S is assembled in
`StacksFrontier/CategoryTheory/Sites/Simplicial/CartesianDerivedModuleMorphism.lean`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.moduleResolutionTensorFunctor` and
  `…moduleResolutionTensorTermCanonicalIso`: the functor `- ⊗^L_O K` of Stacks 0D9Q and the
  identification of the terms of its Postnikov system with the source's `Xₙ`, both taken at the
  canonical derived tensor product of the total ringed site, which is the one at which
  `CategoryTheory.SimplicialSiteSituation.moduleProjection` is stated.

## Main results

* `CategoryTheory.SimplicialSiteSituation.hom_moduleResolutionTensorTerm_shift_eq_zero`:
  hypothesis (3) of Stacks 0D9S supplies the vanishing hypothesis of the tower step.
* `CategoryTheory.SimplicialSiteSituation.exists_hom_of_moduleResolution_termDiff_comp_eq_zero`:
  the tower step of Stacks 0D9S, for the module Postnikov system of Stacks 0D9Q.

## Implementation notes

*The identification of Stacks 0D9E (2) is an argument here.* What the statements below take is
the invertibility of `CategoryTheory.SimplicialSiteSituation.moduleProjection`, the canonical map
`g_{i!}K_i ⟶ g_{i!}O_i ⊗^L_O K`, as `hproj`; Stacks 0D9E (2) supplies it from flatness and
cartesianness of `K`, through
`CategoryTheory.SimplicialSiteSituation`
`.isCartesianDerivedModule_iff_isIso_moduleProjection_of_coherence`.

*Why the resolution and the coprojections are explicit arguments.* The Postnikov presentation of
Stacks 0D9Q is attached to a choice of resolution of the structure sheaf, which exists by Stacks
0D9B but is not canonical, and the derived colimit of a tower determines its coprojections no
better than it determines the colimit itself. The conclusion below names the coprojection `c 0`,
so both have to be carried: the resolution as `D`, the coprojections as `c` together with
`IsHomotopyColimitWith`.

## References

* [Stacks Project, Tag 0D9S](https://stacks.math.columbia.edu/tag/0D9S)
* [Stacks Project, Tag 0D9K](https://stacks.math.columbia.edu/tag/0D9K)
* [Stacks Project, Tag 0D9Q](https://stacks.math.columbia.edu/tag/0D9Q)
* [Stacks Project, Tag 0D9R](https://stacks.math.columbia.edu/tag/0D9R)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 0D9B](https://stacks.math.columbia.edu/tag/0D9B)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

open AlgebraicGeometry Stacks.Cohomology.DerivedPushforward
open StacksDraft.BrutalPostnikov

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

attribute [local instance] hasSheafifyTotal

attribute [local instance] CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

variable [∀ (m n : SimplexCategory) (φ : m ⟶ n),
    (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
      (targetQuasiIso (S.componentRingedTopos O m))]

/-- The functor `- ⊗^L_O K` of Stacks 0D9Q at the canonical derived tensor product of the total
ringed site, with its ambient category written as the derived category of modules on that site.
The spelling matters: `moduleProjection` and
`CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriekDerivedTensorTerm` are stated
at the canonical derived tensor product, and the hom-groups below are the ones of
`D((S.totalRingedTopos O).Modules)`. -/
noncomputable abbrev moduleResolutionTensorFunctor
    (K : DerivedCategory (S.totalRingedTopos O).Modules) :=
  derivedTensorRight O (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O) K

/-- The identification of the `n`-th term of the Postnikov system of Stacks 0D9Q with the
source's `X_n = (g_{n!}O_n) ⊗^L_O K`, at the canonical derived tensor product. -/
noncomputable abbrev moduleResolutionTensorTermCanonicalIso
    (D : SimplicialModuleResolutionActual S
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O))
    (K : DerivedCategory (S.totalRingedTopos O).Modules) (n : ℕ) :=
  moduleResolutionTensorTermIso O
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O) D K n

omit [∀ (m n : SimplexCategory) (φ : m ⟶ n),
    (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
      (targetQuasiIso (S.componentRingedTopos O m))] in
/-- **Hypothesis (3) of Stacks 0D9S is the vanishing hypothesis the construction step
consumes.** The construction step asks for the vanishing of `Hom(X_{i+1}[i], K')` for `i > 0`,
where `X_{i+1}` is the term of the Postnikov system of Stacks 0D9Q attached to the module
resolution. That term is `g_{i+1!}K_{i+1}` by Stacks 0D9E (2) — the hypothesis `hproj` — and the
derived adjunction `Lg_{i+1!} ⊣ Lg_{i+1}^*` turns the group into `Hom(K_{i+1}[i], K'_{i+1})`,
which hypothesis (3) of Stacks 0D9S kills because `i + 1 > 1`. -/
theorem hom_moduleResolutionTensorTerm_shift_eq_zero
    (D : SimplicialModuleResolutionActual S
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O))
    (K K' : DerivedCategory (S.totalRingedTopos O).Modules)
    (hflat : ∀ ⦃m n : SimplexCategory⦄ (φ : m ⟶ n), (S.transitionRingedToposHom O φ).IsFlat)
    (hproj : ∀ i : ℕ, IsIso (S.moduleProjection O ⦋i⦌ (fun _ φ => hflat φ) K))
    (hHom : ∀ i : ℕ, 1 < i →
      ∀ g : (shiftFunctor (DerivedCategory ((S.componentRingedTopos O ⦋i⦌).Modules))
          ((i : ℤ) - 1)).obj ((S.derivedComponentModuleRestriction O ⦋i⦌).obj K) ⟶
          (S.derivedComponentModuleRestriction O ⦋i⦌).obj K', g = 0) :
    ∀ i : ℕ, 0 < i →
      ∀ g : (shiftFunctor (DerivedCategory (S.totalRingedTopos O).Modules) (i : ℤ)).obj
        ((S.moduleResolutionTensorFunctor O K).obj
          (moduleResolutionTerm D (i + 1))) ⟶ K', g = 0 := by
  intro i hi
  refine hom_eq_zero_of_iso
    ((shiftFunctor (DerivedCategory (S.totalRingedTopos O).Modules) (i : ℤ)).mapIso
      (S.moduleResolutionTensorTermCanonicalIso O D K (i + 1))) (Iso.refl K') ?_
  refine S.hom_componentModuleLowerShriekDerivedTensorTerm_eq_zero O K K' (i + 1)
    (fun _ φ => hflat φ) (i : ℤ) (hproj (i + 1)) ?_
  have he : ((i + 1 : ℕ) : ℤ) - 1 = (i : ℤ) := by push_cast; ring
  exact he ▸ hHom (i + 1) (by omega)

omit [∀ (m n : SimplexCategory) (φ : m ⟶ n),
    (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
      (targetQuasiIso (S.componentRingedTopos O m))] in
/-- **The tower step of Stacks 0D9S.** Let `O` be a sheaf of commutative rings on the
total site of a simplicial-site situation, let `K, K'` be objects of `D(O)`, let `D` be a
resolution `… ⟶ g_{1!}O_1 ⟶ g_{0!}O_0` of the structure sheaf (Stacks 0D9B) and let `K` be the
derived colimit of the tower `Yₙ[n] = (g_{n!}O_n ⟶ ⋯ ⟶ g_{0!}O_0)[-n] ⊗^L_O K` with the
coprojections `c` (Stacks 0D9Q (2)). Assume

1. every structure-sheaf transition `f_φ^{-1}O_n ⟶ O_m` is flat, and
2. `Hom(K_i[i - 1], K'_i) = 0` for `i > 1`.

Then a map `b : X₀ ⟶ K'` out of the bottom term `X₀ = g_{0!}O_0 ⊗^L_O K` whose composition with
the differential `X₁ ⟶ X₀` vanishes extends over the derived colimit: there is a `γ : K ⟶ K'`
restricting to `b` along the bottom coprojection.

This is the source's argument from "the map `K_0 ⟶ K'_0` induces a morphism `X₀ ⟶ K'`" to
"this produces a map `γ : K = hocolim Yₙ[n] ⟶ K'`", with the Postnikov system of Stacks 0D9Q in
place of the integral one of Stacks 0D9I. The induction up the tower is
`StacksDraft.BrutalPostnikov.exists_hom_of_termDiff_comp_eq_zero`, which takes hypothesis (2) in
the form `hom_moduleResolutionTensorTerm_shift_eq_zero` puts it.

The invertibility `hproj` of the projection maps of Stacks 0D9E (2) is an argument because the
statement is used where it is already known; the vanishing `hb` is the first of the two
computations the source omits, which
`StacksFrontier/CategoryTheory/Sites/Simplicial/CartesianDerivedModuleLiftConstruction.lean` carries
out for the map `b` it feeds in. -/
theorem exists_hom_of_moduleResolution_termDiff_comp_eq_zero
    (D : SimplicialModuleResolutionActual S
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O))
    (K K' : DerivedCategory (S.totalRingedTopos O).Modules)
    (hflat : ∀ ⦃m n : SimplexCategory⦄ (φ : m ⟶ n), (S.transitionRingedToposHom O φ).IsFlat)
    (hproj : ∀ i : ℕ, IsIso (S.moduleProjection O ⦋i⦌ (fun _ φ => hflat φ) K))
    (hHom : ∀ i : ℕ, 1 < i →
      ∀ g : (shiftFunctor (DerivedCategory ((S.componentRingedTopos O ⦋i⦌).Modules))
          ((i : ℤ) - 1)).obj ((S.derivedComponentModuleRestriction O ⦋i⦌).obj K) ⟶
          (S.derivedComponentModuleRestriction O ⦋i⦌).obj K', g = 0)
    {c : ∀ n, (mapTruncTowerSystem (moduleResolutionComplex D)
      (S.moduleResolutionTensorFunctor O K)).obj n ⟶ K}
    (hc : IsHomotopyColimitWith (mapTruncTowerSystem (moduleResolutionComplex D)
      (S.moduleResolutionTensorFunctor O K)) K c)
    (b : S.componentModuleLowerShriekDerivedTensorTerm O K 0 ⟶ K')
    (hb : (S.moduleResolutionTensorFunctor O K).map (moduleResolutionTermDiff D 0) ≫
      (S.moduleResolutionTensorTermCanonicalIso O D K 0).hom ≫ b =
      (0 : (show DerivedCategory (S.totalRingedTopos O).Modules from
        (S.moduleResolutionTensorFunctor O K).obj (moduleResolutionTerm D 1)) ⟶ K')) :
    ∃ γ : K ⟶ K', c 0 ≫ γ =
      (S.moduleResolutionTensorFunctor O K).map (totAtTowerIso (moduleResolutionComplex D)
          (-((1 : ℕ) : ℤ)) (by simp)).inv ≫
        (S.moduleResolutionTensorFunctor O K).map (moduleResolutionTotProj D 0) ≫
          (S.moduleResolutionTensorTermCanonicalIso O D K 0).hom ≫ b := by
  let : (S.moduleResolutionTensorFunctor O K).CommShift ℤ :=
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).commShift_left K
  let : (S.moduleResolutionTensorFunctor O K).IsTriangulated :=
    isTriangulated_derivedTensorRight O
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O) K
  exact exists_hom_of_termDiff_comp_eq_zero (moduleResolutionComplex D)
    (S.moduleResolutionTensorFunctor O K) hc
    ((S.moduleResolutionTensorTermCanonicalIso O D K 0).hom ≫ b) hb
    (S.hom_moduleResolutionTensorTerm_shift_eq_zero O D K K' hflat hproj hHom)

end CategoryTheory.SimplicialSiteSituation

end
