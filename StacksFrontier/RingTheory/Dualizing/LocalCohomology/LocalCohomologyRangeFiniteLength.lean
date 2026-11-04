module

public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.LocalDualityExtVanishing
public import StacksFrontier.RingTheory.Length.ArtinianPowerTorsion
public import StacksFrontier.RingTheory.Length.Finiteness
public import StacksFrontier.RingTheory.LocalCohomology.ArtinianOverLocalRing

/-!
# Finite length of the image of a local cohomology map, from its dual Ext map

Let `(A, 𝔪, κ)` be a Noetherian local ring, `ω` a normalized dualizing complex, `Z = V(𝔪)`, and
let `h : M ⟶ N` be a map of finite `A`-modules.  Local duality relates the local cohomology map

  `H^i_Z(M) ⟶ H^i_Z(N)`

to the `Ext` map `Ext^{-i}_A(N, ω) ⟶ Ext^{-i}_A(M, ω)`, which is precomposition with `h`.  This
file carries a *finite length* statement across that relation, in the direction the proof of
[Stacks, Tag 0DXU] needs: from the finite length of the image of the `Ext` map to the finite
length of the image of the local cohomology map.

The transport is not a formal consequence of local duality, because the two images live in
modules of different natures: `Ext^{-i}_A(M, ω)` is a finite `A`-module, while `H^i_Z(N)` is
almost never finite.  What makes it work is that only an *annihilation* has to be transported.
A module of finite length over a local ring is annihilated by a power of the maximal ideal, so
the hypothesis says `𝔪^k` kills every `h ≫ u`; the vanishing of each `a • h` with `a ∈ 𝔪^k` on
local cohomology then follows from the vanishing transport, and the image of the local cohomology
map is therefore annihilated by `𝔪^k`.  Finally `H^i_Z(N)` is artinian for a finite `N`
([Stacks, Tag 0DX0] part (1)), and an artinian module annihilated by a power of `𝔪` has finite
length.

## Main results

* `Dualizing.LocalDuality.isFiniteLength_range_homologyMap_localCohomology_of_isFiniteLength_range`
  — the transport, with the vanishing direction of local duality taken as a hypothesis in the
  exact form `Dualizing.LocalDuality.homologyMap_localCohomology_eq_zero_of_forall_comp_eq_zero`
  supplies it.

## Implementation notes

The `A`-linearity of `H^i_Z(−)` on morphisms is what turns `H^i_Z(a • g) = 0` into
`a • H^i_Z(g) = 0`: it is `Stacks.Algebraization.localCohomologyFunctor_map_smul` for the
coreflection and `derivedHomologyFunctorLinear` for the homology functor.

## References

* [Stacks Project, Tag 0DXU](https://stacks.math.columbia.edu/tag/0DXU)
* [Stacks Project, Tag 0AAK](https://stacks.math.columbia.edu/tag/0AAK), local duality.
* [Stacks Project, Tag 0DX0](https://stacks.math.columbia.edu/tag/0DX0), the descending chain
  condition on local cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Dualizing.LocalDuality

/-- **The finite length of the image of a local cohomology map, from that of its dual `Ext`
map.** Let `A` be a Noetherian local ring, `Z = V(𝔪)`, `ω` an object of `D(A)` and
`h : M ⟶ N` a map of `A`-modules with `N` finite.  Nothing is assumed about `ω`: the statement is
formal given `hrev`, and it is for `hrev` — local duality — that `ω` has to be a normalized
dualizing complex.  Assume the vanishing direction of local
duality, `hrev`: a morphism of `D(A)` out of `M` into `N` whose every composite with a map
`N ⟶ ω⟦-i⟧` vanishes induces zero on `H^i_Z`.  If the image of precomposition with `h`,
`Ext^{-i}_A(N, ω) ⟶ Ext^{-i}_A(M, ω)`, has finite length, then so does the image of
`H^i_Z(M) ⟶ H^i_Z(N)`.

Finite length over a local ring means annihilation by a power of `𝔪` together with the two chain
conditions; here the hypothesis is used only through the annihilation, which `hrev` carries over
to the local cohomology side, and the descending chain condition on the target is
[Stacks, Tag 0DX0] part (1). -/
theorem isFiniteLength_range_homologyMap_localCohomology_of_isFiniteLength_range
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (ω : DerivedCategory (ModuleCat.{u} A)) (i : ℤ)
    (M N : ModuleCat.{u} A) [Module.Finite A N]
    (h : M ⟶ N)
    (hrev : ∀ g : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M ⟶
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N,
      (∀ u : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N ⟶
          (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω,
        g ≫ u = 0) →
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        ((Stacks.LocalCohomology.CechFormula.localCohomologyEndofunctor A
          (IsLocalRing.maximalIdeal A) (IsNoetherian.noetherian _)).map g) = 0)
    (hExt : IsFiniteLength A
      (LinearMap.range (CategoryTheory.Linear.leftComp A
        ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω)
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map h)))) :
    IsFiniteLength A ↥(LinearMap.range
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        ((Stacks.LocalCohomology.CechFormula.localCohomologyEndofunctor A
          (IsLocalRing.maximalIdeal A) (IsNoetherian.noetherian _)).map
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map h))).hom) := by
  classical
  set m : Ideal A := IsLocalRing.maximalIdeal A with hm
  set hmfg : m.FG := IsNoetherian.noetherian _ with hmfgdef
  set G := Stacks.LocalCohomology.CechFormula.localCohomologyEndofunctor A m hmfg with hG
  set H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) i with hH
  set W := (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω with hW
  set g : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N :=
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map h with hg
  -- the Ext image is annihilated by a power of the maximal ideal
  obtain ⟨k, hk⟩ :=
    exists_pow_maximalIdeal_smul_eq_bot_of_isFiniteLength A
      ↥(LinearMap.range (CategoryTheory.Linear.leftComp A W g)) hExt
  -- hence every `a • g` with `a ∈ 𝔪^k` kills every map into `ω⟦-i⟧`
  have hzero : ∀ a ∈ m ^ k, (H.map (G.map (a • g))) = 0 := by
    intro a ha
    refine hrev (a • g) ?_
    intro u
    have hmem : (g ≫ u) ∈ LinearMap.range (CategoryTheory.Linear.leftComp A W g) := ⟨u, rfl⟩
    have hsm : a • (⟨g ≫ u, hmem⟩ :
        ↥(LinearMap.range (CategoryTheory.Linear.leftComp A W g))) = 0 := by
      have : a • (⟨g ≫ u, hmem⟩ :
          ↥(LinearMap.range (CategoryTheory.Linear.leftComp A W g))) ∈
          m ^ k • (⊤ : Submodule A ↥(LinearMap.range (CategoryTheory.Linear.leftComp A W g))) :=
        Submodule.smul_mem_smul ha Submodule.mem_top
      rw [hk] at this
      simpa using this
    have : a • (g ≫ u) = 0 := congrArg Subtype.val hsm
    rw [CategoryTheory.Linear.smul_comp]
    exact this
  -- the `A`-linearity of `H^i_Z` turns that into the annihilation of the image
  have hlin : ∀ a : A, H.map (G.map (a • g)) = a • H.map (G.map g) := by
    intro a
    have h1 : G.map (a • g) = a • G.map g := by
      have := Stacks.Algebraization.localCohomologyFunctor_map_smul (A := A) m hmfg a g
      exact this
    rw [h1]
    let := derivedHomologyFunctorLinear (R := A) i
    rw [Functor.Linear.map_smul]
  have hann : m ^ k • (⊤ : Submodule A ↥(LinearMap.range (H.map (G.map g)).hom)) = ⊥ := by
    refine le_antisymm (Submodule.smul_le.mpr ?_) bot_le
    intro a ha x _
    obtain ⟨y, hy⟩ := x.2
    have hz : a • H.map (G.map g) = 0 := by rw [← hlin a]; exact hzero a ha
    have hxz : a • ((H.map (G.map g)).hom y) = 0 := by
      have h2 : (a • H.map (G.map g)).hom y = 0 := by rw [hz]; rfl
      exact h2
    refine (Submodule.mem_bot A).mpr (Subtype.ext ?_)
    change a • (x : ↑(H.obj (G.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)))) = 0
    rw [← hy]
    exact hxz
  -- the target is artinian, so the image is artinian, and annihilated by `𝔪^k` it is finite
  have hart : IsArtinian A (H.obj (G.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N))) :=
    Stacks.LocalCohomology.isArtinian_localCohomology_maximalIdeal A N i
  have hartr : IsArtinian A ↥(LinearMap.range (H.map (G.map g)).hom) :=
    isArtinian_of_injective (LinearMap.range (H.map (G.map g)).hom).subtype
      (Submodule.injective_subtype _)
  exact Stacks.RingTheory.isFiniteLength_of_isArtinian_of_pow_maximalIdeal_smul_eq_bot hartr k hann

end Dualizing.LocalDuality

end
