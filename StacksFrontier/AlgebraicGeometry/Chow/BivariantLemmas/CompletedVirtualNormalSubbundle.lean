module

public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.SubbundleCompleted
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedVirtualNormalBundleClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBaseChangeExcess
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.DualBaseChangeNaturality
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedRestrictionFlatCommute
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedRestrictionComposite
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedIdentity
public import StacksFrontier.AlgebraicGeometry.Chow.TopChernClassOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalClassPieces
public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChernClass.ArbitraryRank
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackShortExactLocallyFree
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalSubbundleClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantClassCopy

/-!
# The Gysin class of a subbundle of a virtual normal sheaf of arbitrary rank

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `i : Z ⟶ X` be a closed subscheme with virtual normal sheaf `𝒩` in the
sense of Stacks 0FBQ, and let

  `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0`

be a short exact sequence of finite locally free `𝒪_Z`-modules, of arbitrary (locally constant)
ranks, such that the surjection `σ : 𝒩^∨ ⟶ 𝒞_{Z/X}` factors as `σ = σ' ∘ (𝒩^∨ ⟶ (𝒩')^∨)`
through the surjection `σ'` of the virtual normal sheaf `𝒩'`. **Stacks 0FBL** asserts that

  `c(Z ⟶ X, 𝒩) = c_top(ℰ) ∘ c(Z ⟶ X, 𝒩')`

as bivariant classes, in the completed bivariant group `A^*(Z ⟶ X)^∧` of Stacks 0FE0, where
`c(Z ⟶ X, -)` is the class of Stacks 0FBK and `c_top(ℰ)` the top Chern class of Stacks 0FA4.

## The proof

As in the source, the statement follows from the case of constant ranks
(`Stacks.Chow.virtualNormalBundleClass_eq_of_isTopChernComposition`). Both sides are completed
classes, so they are compared on each connected component `Z_a` of `Z` and in each degree. On
`Z_a` the three modules have constant ranks `r_a`, `m_a` and `e_a`, with `r_a = m_a + e_a`
(`Stacks.Chow.componentRank_eq_add_of_shortExact`), and both sides are concentrated in degree
`r_a`. There the left-hand side is `c(Z_a ⟶ U_a, 𝒩|_{Z_a}) ∘ (U_a ⟶ X_b)^*`, the top Chern class is
`c_{e_a}(ℰ|_{Z_a})` (`Stacks.Chow.bivariantConnectedComponentRestriction_topChernTotalClass_heq`)
and the a-component of `c(Z ⟶ X, 𝒩')` is `c(Z_a ⟶ U_a, 𝒩'|_{Z_a}) ∘ (U_a ⟶ X_b)^*`. The
restricted sequence `0 ⟶ 𝒩'|_{Z_a} ⟶ 𝒩|_{Z_a} ⟶ ℰ|_{Z_a} ⟶ 0` is short exact and the
factorization of the conormal surjection restricts
(`Stacks.Chow.VirtualNormalBundle.dualMap_comp_toComponent_surjection`), so Stacks 0FBL at constant
rank applies to `Z_a ⟶ U_a`, and the associativity of Stacks 0B75 concludes.

## Main results

* `Stacks.Chow.componentRank_eq_add_of_shortExact` — ranks add along a short exact sequence, on a
  connected component.
* `Stacks.Chow.VirtualNormalBundle.dualMap_comp_toComponent_surjection` — the factorization of the
  conormal surjection restricts to a connected component.
* `Stacks.Chow.bivariantConnectedComponentRestriction_topChernTotalClass_heq` — on a connected
  component of rank `e`, the top Chern class is `c_e` of the restricted module.
* `Stacks.Chow.completedVirtualNormalGysinClass_eq_of_isTopChernComposition` — **Stacks 0FBL**.

## References

* [Stacks Project, Tag 0FBL](https://stacks.math.columbia.edu/tag/0FBL)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0FA4](https://stacks.math.columbia.edu/tag/0FA4)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

/-! ### Transport lemmas -/

/-- The zero bivariant classes for equal morphisms and of equal degrees are the same class. -/
theorem BivariantClass.zero_heq_of_eq {C : ChowSituation.{u}} {G : GysinSystem C}
    {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] {f f' : X ⟶ Y} [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    (hff : f = f') {hf : f ≫ sY = sX} {hf' : f' ≫ sY = sX} {p p' : ℤ} (hp : p = p') :
    (0 : BivariantClass C G sX sY f hf p) ≍ (0 : BivariantClass C G sX sY f' hf' p') := by
  subst hff hp
  rfl

/-- Composing with the zero class on the right gives the zero class (Stacks 0B75: the composition
is bilinear). -/
theorem bivariantCompositeOfInvertible_zero_right (C : ChowSituation.{u}) {X Y Z : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ Z)
    [LocallyOfFiniteType g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (p q : ℤ)
    (a : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) :
    bivariantCompositeOfInvertible C sX sY sZ f g hf hg p q a 0 = 0 :=
  (bivariantCompositeBilinearOfInvertible C sX sY sZ f g hf hg p q a).map_zero

/-- The class `c(Z ⟶ X, 𝒩)` at constant rank does not depend on how the rank is written. -/
theorem virtualNormalGysinClass_heq_of_rank_eq (C : ChowSituation.{u}) {Z X : Scheme.{u}}
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ) (𝒩 : VirtualNormalBundle i) {r r' : ℕ}
    (h : r = r') [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r'] :
    virtualNormalBundleClass C sZ sX i hi 𝒩 r ≍ virtualNormalBundleClass C sZ sX i hi 𝒩 r' := by
  subst h
  rfl

/-! ### Ranks and the conormal factorization on a connected component -/

section Component

variable {Z : Scheme.{u}} [IsLocallyNoetherian Z]

/-- **Ranks add along a short exact sequence, on a connected component.** For a short exact
sequence `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` of finite locally free modules, the rank of `𝒩` on a connected
component `Z_a` is the sum of those of `𝒩'` and `ℰ`: the sequence restricts to a short exact
sequence on `Z_a` of modules of constant ranks, and ranks add in such a sequence. -/
theorem componentRank_eq_add_of_shortExact {N' N E : Z.Modules}
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (f : N' ⟶ N) (g : N ⟶ E) (w : f ≫ g = 0)
    (hS : (ShortComplex.mk f g w).ShortExact) (a : _root_.ConnectedComponents Z) :
    componentRank N a = componentRank N' a + Scheme.Modules.rankOnConnectedComponent E a := by
  have hS' := Scheme.Modules.shortExact_map_pullback_of_isFiniteLocallyFree
    (Z.connectedComponentOpens a).ι _ hS
  have h₁ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((ShortComplex.mk f g w).map
        (Scheme.Modules.pullback (Z.connectedComponentOpens a).ι)).X₁ (componentRank N' a) :=
    isFiniteLocallyFreeOfRank_componentRank N' a
  have h₃ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((ShortComplex.mk f g w).map (Scheme.Modules.pullback (Z.connectedComponentOpens a).ι)).X₃
      (Scheme.Modules.rankOnConnectedComponent E a) :=
    isFiniteLocallyFreeOfRank_pullback_ι_of_le_rankLocus E _ _
      (Scheme.Modules.connectedComponentOpens_le_rankStratum E a)
  have h₂ := GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact _ hS' _ _ h₁ h₃
  have h₂' : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (Z.connectedComponentOpens a).ι).obj N) (componentRank N a) :=
    isFiniteLocallyFreeOfRank_componentRank N a
  let y : (Z.connectedComponentOpens a : Scheme.{u}) :=
    ⟨(ConnectedComponents.surjective_coe a).choose,
      (ConnectedComponents.surjective_coe a).choose_spec⟩
  exact (Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank (h := h₂') _ _ y).symm.trans
    (Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank (h := h₂) _ _ y)

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {i : Z ⟶ X} [IsClosedImmersion i]
  (𝒩 𝒩' : VirtualNormalBundle i)

/-- **The factorization of the conormal surjection restricts to a connected component.** If the
conormal surjection `σ` of `𝒩` factors as `σ' ∘ (𝒩^∨ ⟶ (𝒩')^∨)` through that of `𝒩'`, then on a
connected component `Z_a` of `Z` the surjection of `𝒩|_{Z_a}` factors in the same way through that
of `𝒩'|_{Z_a}`, the restrictions of Stacks 0FBJ for `Z_a ⟶ U_a`. The dual base-change map is
natural in the module (`Stacks.Chow.pullbackDualMap_naturality`). -/
theorem VirtualNormalBundle.dualMap_comp_toComponent_surjection (inc : 𝒩'.bundle ⟶ 𝒩.bundle)
    (hsigma : dualMap inc ≫ 𝒩'.surjection = 𝒩.surjection) (a : _root_.ConnectedComponents Z) :
    dualMap ((modulePullback (Z.connectedComponentOpens a).ι.toLRSHom.toShHom).map inc) ≫
        (𝒩'.toComponent i a).surjection = (𝒩.toComponent i a).surjection := by
  refine dualMap_comp_surjection_eq_baseChange_surjection i (componentRestriction i a)
    (Z.connectedComponentOpens a).ι (componentNeighbourhood i a).ι
    (isPullback_componentRestriction i a) 𝒩 (𝒩'.toComponent i a) _ ?_
  have hnat := pullbackDualMap_naturality (Z.connectedComponentOpens a).ι inc
  have hinv := Iso.hom_inv_id_assoc (@asIso _ _ _ _
    (pullbackDualMap (Z.connectedComponentOpens a).ι 𝒩'.bundle)
    (pullbackDualMap_isIso (Z.connectedComponentOpens a).ι 𝒩'.bundle
      𝒩'.isFiniteLocallyFree))
    ((modulePullback (Z.connectedComponentOpens a).ι.toLRSHom.toShHom).map 𝒩'.surjection ≫
      Stacks.Immersion.immersionConormalSheafMap (componentRestriction i a) i
        (Z.connectedComponentOpens a).ι (componentNeighbourhood i a).ι
        (Stacks.Immersion.toShHom_square (isPullback_componentRestriction i a).w))
  calc _ = (modulePullback (Z.connectedComponentOpens a).ι.toLRSHom.toShHom).map (dualMap inc) ≫
        pullbackDualMap (Z.connectedComponentOpens a).ι 𝒩'.bundle ≫
          (𝒩'.toComponent i a).surjection :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ (𝒩'.toComponent i a).surjection) hnat.symm).trans (Category.assoc _ _ _))
    _ = (modulePullback (Z.connectedComponentOpens a).ι.toLRSHom.toShHom).map (dualMap inc) ≫
        (modulePullback (Z.connectedComponentOpens a).ι.toLRSHom.toShHom).map 𝒩'.surjection ≫
          Stacks.Immersion.immersionConormalSheafMap (componentRestriction i a) i
            (Z.connectedComponentOpens a).ι (componentNeighbourhood i a).ι
            (Stacks.Immersion.toShHom_square (isPullback_componentRestriction i a).w) :=
        congrArg (_ ≫ ·) hinv
    _ = _ :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
          (((modulePullback (Z.connectedComponentOpens a).ι.toLRSHom.toShHom).map_comp _
            _).symm.trans (congrArg _ hsigma)))

end Component

/-! ### The top Chern class on a connected component -/

section TopChern

variable (C : ChowSituation.{u}) {Z : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  [IsLocallyNoetherian Z] (Eb : Z.Modules) [SheafOfModules.IsFiniteLocallyFree.{u, u, u} Eb]

/-- **The top Chern class on a connected component.** On a connected component `Z_a` on which `ℰ`
has rank `e`, the degree-`e` part of `c_top(ℰ)` restricts (Stacks 0FDZ) to the Chern class
`c_e(ℰ|_{Z_a})` of Stacks 0B7H. The restriction is a class for the restriction of the identity
`Z_a ⟶ Z_{a'}`, where the index `a'` is equal, and not identical, to `a`; whence the heterogeneous
equality. -/
theorem bivariantConnectedComponentRestriction_topChernTotalClass_heq
    (a : _root_.ConnectedComponents Z) :
    haveI := isFiniteLocallyFreeOfRank_pullback_ι_of_le_rankLocus Eb _ _
      (Scheme.Modules.connectedComponentOpens_le_rankStratum Eb a)
    bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sZ sZ (𝟙 Z)
        (Category.id_comp sZ) _ (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (topChernTotalClass C sZ Eb (Scheme.Modules.rankOnConnectedComponent Eb a)) a ≍
      GenuineChern.chernClass C ((Z.connectedComponentOpens a).ι ≫ sZ)
        ((Scheme.Modules.pullback (Z.connectedComponentOpens a).ι).obj Eb)
        (Scheme.Modules.rankOnConnectedComponent Eb a) (Fin.last _) := by
  have := isFiniteLocallyFreeOfRank_pullback_ι_of_le_rankLocus Eb _ _
    (Scheme.Modules.connectedComponentOpens_le_rankStratum Eb a)
  rw [bivariantConnectedComponentRestriction_topChernTotalClass, ite_eq_left rfl]
  refine (bivariantPieceRestriction_heq_of_index C sZ sZ (𝟙 Z) (Category.id_comp sZ) _
    Z.connectedComponentOpens Z.connectedComponentOpens
    (Scheme.Hom.connectedComponentsMap_id Z) _ (opens_le_preimage_id _) a
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (totalChernOfFiniteLocallyFree C sZ Eb (Scheme.Modules.rankOnConnectedComponent Eb a))).trans
    ?_
  refine (bivariantClassCongr_heq_self (pieceMap_id _ (opens_le_preimage_id _) a) _
    (Category.id_comp _) _ _).symm.trans (heq_of_eq ?_)
  refine (chowCohomologyRestriction_eq_pieceIdentityCongr Z.connectedComponentOpens _ a).symm.trans
    ?_
  rw [← TotalChowClass.res_rfl_apply, res_totalChernOfFiniteLocallyFree_of_rank C sZ Eb _ rfl
    (Scheme.Modules.rankOnConnectedComponent Eb a)]
  exact totalChern_apply C _ _ _ (Fin.last _)

end TopChern

/-! ### Stacks 0FBL -/

section Main

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ)
  (𝒩 𝒩' : VirtualNormalBundle i) (Eb : Z.Modules)
  [SheafOfModules.IsFiniteLocallyFree.{u, u, u} Eb] (inc : 𝒩'.bundle ⟶ 𝒩.bundle)
  (pr : 𝒩.bundle ⟶ Eb)

/-- **Stacks 0FBL.** Let `(S, δ)` be the base situation of chapter 42, let `X` be locally of
finite type over `S`, let `i : Z ⟶ X` be a closed subscheme with virtual normal sheaf `𝒩`, and
let `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence of finite locally free `𝒪_Z`-modules, of
arbitrary ranks, such that the conormal surjection `σ : 𝒩^∨ ⟶ 𝒞_{Z/X}` factors as
`σ' ∘ (𝒩^∨ ⟶ (𝒩')^∨)` through that of `𝒩'`. Then

  `c(Z ⟶ X, 𝒩) = c_top(ℰ) ∘ c(Z ⟶ X, 𝒩')`

in the completed bivariant group `A^*(Z ⟶ X)^∧` of Stacks 0FE0, for the classes of Stacks 0FBK,
the top Chern class of Stacks 0FA4 and the composition on completions; the composite is a class
for `𝟙 Z ≫ i = i`.

On a connected component `Z_a` of `Z` both sides are concentrated in the degree `r_a` of `𝒩`, and
there this is Stacks 0FBL at constant rank for `Z_a ⟶ U_a` composed with `(U_a ⟶ X_b)^*`. -/
@[stacks 0FBL "c(Z → X, N) = c_top(E) ∘ c(Z → X, N') in A^*(Z → X)^∧ for a short exact sequence \
0 → N' → N → E → 0 of finite locally free modules of arbitrary rank whose surjection factors \
through that of N'"]
theorem completedVirtualNormalGysinClass_eq_of_isTopChernComposition
    (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)
    (hsigma : dualMap inc ≫ 𝒩'.surjection = 𝒩.surjection) :
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    completedVirtualNormalGysinClass C sZ sX i hi 𝒩 =
      completedBivariantGroup.copy C (Category.id_comp i) _ hi
        (completedBivariantCompositeOfInvertible C sZ sZ sX (𝟙 Z) i (Category.id_comp sZ) hi
          (topChernClassOfInvertible C sZ Eb)
          (completedVirtualNormalGysinClass C sZ sX i hi 𝒩')) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  refine eq_of_heq (HEq.trans ?_ (completedBivariantGroup.copy_heq C _ _ _ _).symm)
  refine completedBivariantGroup_heq_of_apply_heq C (Category.id_comp i).symm _ _ fun a n ↦ ?_
  refine HEq.symm ((completedBivariantCompositeOfInvertible_apply_heq_of_left C sZ sZ sX (𝟙 Z) i
    (Category.id_comp sZ) hi _ _ a _ _ rfl n).trans ?_)
  have ha : (𝟙 Z : Z ⟶ Z).continuous.connectedComponentsMap a = a :=
    congrFun (Scheme.Hom.connectedComponentsMap_id Z) a
  have := isFiniteLocallyFreeOfRank_pullback_ι_of_le_rankLocus Eb _ _
    (Scheme.Modules.connectedComponentOpens_le_rankStratum Eb a)
  refine (bivariantCompositeOfInvertible_heq_of_source_component C _ sZ sX i hi ha _ (𝟙 _)
    (Scheme.Hom.heq_of_comp_connectedComponentOpens_ι ha _ _ (by
      rw [Scheme.Hom.resConnectedComponent_comp_ι, Category.comp_id, Category.id_comp])) _
    (Category.id_comp _) _ _ _ _
    (bivariantConnectedComponentRestriction_topChernTotalClass_heq C sZ Eb a) _ _
    (congr_arg_heq (fun j ↦ completedVirtualNormalGysinClass C sZ sX i hi 𝒩' j
      (n - (Scheme.Modules.rankOnConnectedComponent Eb a : ℤ))) ha)).trans ?_
  have hrank := componentRank_eq_add_of_shortExact inc pr w hseq a
  by_cases hn : n = (componentRank 𝒩.bundle a : ℤ)
  · subst hn
    -- Stacks 0FBL at constant rank for `Z_a ⟶ U_a`
    have hN : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (𝒩.toComponent i a).bundle
        (componentRank 𝒩'.bundle a + Scheme.Modules.rankOnConnectedComponent Eb a) := by
      rw [← hrank]
      infer_instance
    have hSa := Scheme.Modules.shortExact_map_pullback_of_isFiniteLocallyFree
      (Z.connectedComponentOpens a).ι _ hseq
    have hL0 := virtualNormalBundleClass_eq_of_isTopChernComposition C
      ((Z.connectedComponentOpens a).ι ≫ sZ) ((componentNeighbourhood i a).ι ≫ sX)
      (componentRestriction i a) (componentRestriction_comp_structureMorphism C sZ sX i hi a)
      (𝒩.toComponent i a) (𝒩'.toComponent i a) (componentRank 𝒩'.bundle a)
      (Scheme.Modules.rankOnConnectedComponent Eb a)
      ((Scheme.Modules.pullback (Z.connectedComponentOpens a).ι).obj Eb)
      ((modulePullback (Z.connectedComponentOpens a).ι.toLRSHom.toShHom).map inc)
      ((Scheme.Modules.pullback (Z.connectedComponentOpens a).ι).map pr)
      ((ShortComplex.mk inc pr w).map
        (Scheme.Modules.pullback (Z.connectedComponentOpens a).ι)).zero
      hSa (VirtualNormalBundle.dualMap_comp_toComponent_surjection 𝒩 𝒩' inc hsigma a)
    -- the `a`-component of `c(Z ⟶ X, 𝒩')` is `c(Z_a ⟶ U_a, 𝒩'|_{Z_a}) ∘ (U_a ⟶ X_b)^*`
    refine (bivariantCompositeOfInvertible_heq_congr rfl
      (componentRestriction_comp_componentInclusion i a).symm rfl
      (q' := (componentRank 𝒩'.bundle a : ℤ) + -((0 : ℕ) : ℤ))
      (by simp only [Nat.cast_zero, neg_zero, add_zero]; omega) HEq.rfl
      ((directSum_of_apply_heq (by omega) _).trans
        (BivariantClass.copy_heq _ _ _ _ _))).trans ?_
    -- associativity of Stacks 0B75
    refine (bivariantCompositeOfInvertible_assoc C _ _ _ _ (𝟙 _) (componentRestriction i a)
      (componentInclusion i a) (Category.id_comp _)
      (componentRestriction_comp_structureMorphism C sZ sX i hi a)
      (by rw [← Category.assoc, Scheme.homOfLE_ι]) _ _ _ _ _ _).symm.trans ?_
    refine (bivariantCompositeOfInvertible_heq_congr (Category.id_comp _) rfl
      (p' := (componentRank 𝒩.bundle a : ℤ)) (by omega) rfl
      (((BivariantClass.copy_heq _ _ _ _ _).symm.trans (heq_of_eq hL0).symm).trans
        (virtualNormalGysinClass_heq_of_rank_eq C _ _ _ _ _ hrank.symm)) HEq.rfl).trans ?_
    rw [completedVirtualNormalGysinClass_apply, DirectSum.of_eq_same]
    exact (BivariantClass.copy_heq _ _ _ _ _).symm
  · -- in the other degrees both sides vanish
    have hne : n - (Scheme.Modules.rankOnConnectedComponent Eb a : ℤ) ≠
        (componentRank 𝒩'.bundle a : ℤ) := by
      omega
    have h0 : completedVirtualNormalGysinClass C sZ sX i hi 𝒩' a
        (n - (Scheme.Modules.rankOnConnectedComponent Eb a : ℤ)) = 0 := by
      rw [completedVirtualNormalGysinClass_apply, DirectSum.of_eq_of_ne _ _ _ hne]
    rw [h0, bivariantCompositeOfInvertible_zero_right, completedVirtualNormalGysinClass_apply,
      DirectSum.of_eq_of_ne _ _ _ hn]
    exact BivariantClass.zero_heq_of_eq (Category.id_comp _) (by ring)

end Main

end Stacks.Chow

end
