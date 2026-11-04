module

public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.Subbundle
public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.Statement
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceComposite
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceShrinkTarget
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0FBL for virtual normal sheaves of arbitrary rank

Let `i : Z ⟶ X` be a closed immersion with virtual normal sheaf `𝒩`, let
`0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence of finite locally free `𝒪_Z`-modules such that
`σ : 𝒩^∨ ⟶ 𝒞_{Z/X}` factors through `σ' : (𝒩')^∨ ⟶ 𝒞_{Z/X}`. Then

  `c(Z ⟶ X, 𝒩) = c_top(ℰ) ∘ c(Z ⟶ X, 𝒩')`   in   `A^*(Z ⟶ X)^∧`,

with the completed classes of Stacks 0FBK, the top Chern class of Stacks 0FA4 and the composition
of Stacks 0FE0 on the completed bivariant groups.

The ranks of `𝒩'`, `𝒩` and `ℰ` are constant on each connected component `Z_k` of `Z`; there the
identity is the constant-rank case
`Stacks.Chow.VirtualNormalBundle.virtualNormalClass_eq_composite` for the virtual normal sheaf
`𝒩|_{Z_k}` of `Z_k ⟶ W_k` (Stacks 0FBJ).

## Main results

* `Stacks.Chow.VirtualNormalBundle.componentClass_eq_composite` — the identity on the piece
  `Z_k ⟶ W_k` of a connected component of `Z`, where all ranks are constant.
* `Stacks.Chow.VirtualNormalBundle.completedClass_eq_topChernClassCompleted_comp` — the identity
  `c(Z ⟶ X, 𝒩) = c_top(ℰ) ∘ c(Z ⟶ X, 𝒩')` in `A^*(Z ⟶ X)^∧`, **Stacks 0FBL**.

## References

* [Stacks Project, Tag 0FBL](https://stacks.math.columbia.edu/tag/0FBL)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

/-! ### The completed group of two equal morphisms -/

section CompletedCongr

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- The completed bivariant groups (Stacks 0FE0) of two equal morphisms are the same group. -/
def completedBivariantGroupCongr {f f' : X ⟶ Y} [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    (hff : f = f') (hf : f ≫ sY = sX) (hf' : f' ≫ sY = sX) :
    completedBivariantGroup C G sX sY f hf ≃+ completedBivariantGroup C G sX sY f' hf' := by
  subst hff
  exact AddEquiv.refl _

/-- The degree `p` part of the transported element is the transported degree `p` part. -/
theorem completedBivariantSequence_completedBivariantGroupCongr {f f' : X ⟶ Y}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (hff : f = f') (hf : f ≫ sY = sX)
    (hf' : f' ≫ sY = sX) (hgysO : G.IsNaturalUnderOpenImmersion)
    (hgysR : G.IsNaturalUnderOpensRestriction) (hgysC : G.IsNaturalUnderPullbackComp)
    (c : completedBivariantGroup C G sX sY f hf) (p : ℤ) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    completedBivariantSequence C G sX sY f' hf' hgysO hgysR hgysC
        (completedBivariantGroupCongr C G sX sY hff hf hf' c) p =
      bivariantClassCongr C G sX sY hff hf hf' p
        (completedBivariantSequence C G sX sY f hf hgysO hgysR hgysC c p) := by
  subst hff
  rfl

end CompletedCongr

/-! ### Transports are heterogeneously the identity -/

section Transport

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X Y : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]

/-- Transporting a bivariant class along an equality of morphisms is heterogeneously the
identity. -/
theorem bivariantClassCongr_heq_self {f f' : X ⟶ Y} [LocallyOfFiniteType f]
    [LocallyOfFiniteType f'] (hff : f = f') (hf : f ≫ sY = sX) (hf' : f' ≫ sY = sX) (p : ℤ)
    (c : BivariantClass C G sX sY f hf p) : bivariantClassCongr C G sX sY hff hf hf' p c ≍ c := by
  subst hff
  rfl

/-- Transporting a bivariant class along an equality of degrees is heterogeneously the
identity. -/
theorem bivariantClassCongrDeg_heq_self {f : X ⟶ Y} [LocallyOfFiniteType f] (hf : f ≫ sY = sX)
    {p q : ℤ} (hpq : p = q) (c : BivariantClass C G sX sY f hf p) :
    bivariantClassCongrDeg C G sX sY f hf hpq c ≍ c := by
  subst hpq
  rfl

/-- Copying a bivariant class along equalities of morphisms and degrees is heterogeneously the
identity. -/
theorem BivariantClass.copy_heq_self {f f' : X ⟶ Y} [LocallyOfFiniteType f]
    [LocallyOfFiniteType f'] (hff : f = f') (hf : f ≫ sY = sX) (hf' : f' ≫ sY = sX) {p p' : ℤ}
    (hpp : p = p') (c : BivariantClass C G sX sY f hf p) :
    BivariantClass.copy C G sX sY hff hf hf' hpp c ≍ c := by
  subst hff hpp
  rfl

/-- Transporting a bivariant class along an equality of connected components `j₁ = j₂` is
heterogeneously the identity. -/
theorem bivariantClassComponentCongr_heq_self {W Z : Scheme.{u}} {sW : W ⟶ C.S}
    [LocallyOfFiniteType sW] {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] [LocallyConnectedSpace Z]
    {j₁ j₂ : _root_.ConnectedComponents Z} (hj : j₁ = j₂)
    (u₁ : W ⟶ (Z.connectedComponentOpens j₁ : Scheme.{u})) [LocallyOfFiniteType u₁]
    (u₂ : W ⟶ (Z.connectedComponentOpens j₂ : Scheme.{u})) [LocallyOfFiniteType u₂]
    (hu : u₁ ≍ u₂) (h₁ : u₁ ≫ ((Z.connectedComponentOpens j₁).ι ≫ sZ) = sW)
    (h₂ : u₂ ≫ ((Z.connectedComponentOpens j₂).ι ≫ sZ) = sW) (n : ℤ)
    (c : BivariantClass C G sW ((Z.connectedComponentOpens j₁).ι ≫ sZ) u₁ h₁ n) :
    bivariantClassComponentCongr C G sW sZ hj u₁ u₂ hu h₁ h₂ n c ≍ c := by
  subst hj
  obtain rfl := eq_of_heq hu
  rfl

/-- The `p`-th coordinate of a homogeneous element of degree `n = p`. -/
theorem directSum_of_apply_heq {β : ℤ → Type*} [∀ n, AddCommMonoid (β n)] {n p : ℤ} (h : n = p)
    (x : β n) : (DirectSum.of β n x) p ≍ x := by
  subst h
  exact heq_of_eq (DirectSum.of_eq_same _ _)

end Transport

/-! ### Restriction to pieces along equal data, and composites of equal classes -/

section PieceCongr

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {I J : Type u}
  (UX : I → X.Opens) (UY : J → Y.Opens) (hgysO : G.IsNaturalUnderOpenImmersion) (p : ℤ)

/-- Restriction to pieces along two equal index maps. -/
theorem bivariantPieceRestriction_heq_of_index_eq (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hf : f ≫ sY = sX) {a a' : I → J} (haa : a = a') (ha : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a i))
    (ha' : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a' i)) (i : I) (c : BivariantClass C G sX sY f hf p) :
    bivariantPieceRestriction C G sX sY f hf p UX UY a ha i hgysO c ≍
      bivariantPieceRestriction C G sX sY f hf p UX UY a' ha' i hgysO c := by
  subst haa
  rfl

/-- Restriction to pieces of a class read at an equal morphism. -/
theorem bivariantPieceRestriction_copy_heq {f f' : X ⟶ Y} [LocallyOfFiniteType f]
    [LocallyOfFiniteType f'] (hff : f = f') (hf : f ≫ sY = sX) (hf' : f' ≫ sY = sX) (a : I → J)
    (ha : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a i)) (ha' : ∀ i, UX i ≤ f' ⁻¹ᵁ UY (a i)) (i : I)
    (c : BivariantClass C G sX sY f hf p) :
    bivariantPieceRestriction C G sX sY f' hf' p UX UY a ha' i hgysO
        (bivariantClassCongr C G sX sY hff hf hf' p c) ≍
      bivariantPieceRestriction C G sX sY f hf p UX UY a ha i hgysO c := by
  subst hff
  rfl

end PieceCongr

section CompositeCongr

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X Y Z : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {sZ : Z ⟶ C.S}
  [LocallyOfFiniteType sZ]

/-- The composite of Stacks 0B75 of heterogeneously equal classes for equal morphisms. -/
theorem bivariantComposite_heq_congr {f f' : X ⟶ Y} [LocallyOfFiniteType f]
    [LocallyOfFiniteType f'] (hff : f = f') {g : Y ⟶ Z} [LocallyOfFiniteType g]
    (hf : f ≫ sY = sX) (hf' : f' ≫ sY = sX) (hg : g ≫ sZ = sY) {p p' q q' : ℤ} (hp : p = p')
    (hq : q = q') {a : BivariantClass C G sX sY f hf p} {a' : BivariantClass C G sX sY f' hf' p'}
    (ha : a ≍ a') {b : BivariantClass C G sY sZ g hg q} {b' : BivariantClass C G sY sZ g hg q'}
    (hb : b ≍ b') (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) :
    bivariantComposite C G sX sY sZ f g hf hg p q a b hgys hgysc ≍
      bivariantComposite C G sX sY sZ f' g hf' hg p' q' a' b' hgys hgysc := by
  subst hff hp hq
  obtain rfl := eq_of_heq ha
  obtain rfl := eq_of_heq hb
  rfl

end CompositeCongr

/-! ### Agreement on a larger target gives agreement on a smaller one -/

section Grow

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ)
  {I J J' : Type u} (UX : I → X.Opens) (UY : J → Y.Opens) (a : I → J)
  (ha : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a i)) (UY' : J' → Y.Opens) (a' : I → J')
  (ha' : ∀ i, UX i ≤ f ⁻¹ᵁ UY' (a' i)) (i : I) (hle : UY' (a' i) ≤ UY (a i))
  (hgysO : G.IsNaturalUnderOpenImmersion)

include hle in
/-- **Two classes agreeing on a larger target agree on a smaller one**: if the restrictions of
`c` and `d` to `X_i ⟶ V` coincide, so do their restrictions to `X_i ⟶ V'` for `f(X_i) ⊆ V' ⊆ V`.
-/
theorem bivariantPieceRestriction_eq_of_grow (c d : BivariantClass C G sX sY f hf p)
    (h : bivariantPieceRestriction C G sX sY f hf p UX UY a ha i hgysO c =
      bivariantPieceRestriction C G sX sY f hf p UX UY a ha i hgysO d) :
    bivariantPieceRestriction C G sX sY f hf p UX UY' a' ha' i hgysO c =
      bivariantPieceRestriction C G sX sY f hf p UX UY' a' ha' i hgysO d := by
  refine BivariantClass.ext C G _ _ _ _ p fun {T} s _ k β ↦ ?_
  rw [bivariantPieceRestriction_cap, bivariantPieceRestriction_cap,
    bivariantPieceRestrictionCap_grow C G sX sY f hf p UX UY a ha UY' a' ha' i hle s c k β,
    bivariantPieceRestrictionCap_grow C G sX sY f hf p UX UY a ha UY' a' ha' i hle s d k β,
    ← bivariantPieceRestriction_cap C G sX sY f hf p UX UY a ha i hgysO c,
    ← bivariantPieceRestriction_cap C G sX sY f hf p UX UY a ha i hgysO d, h]

end Grow

end Stacks.Chow

namespace Stacks.Chow.VirtualNormalBundle

/-! ### The class of a virtual normal bundle in two equal ranks -/

section RankCongr

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsImmersion i] (𝒩 : VirtualNormalBundle i)
  (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (hZ : i ≫ sX = sZ)

/-- The class `c(Z ⟶ X, 𝒩)` does not depend on how the constant rank of `𝒩` is written. -/
theorem virtualNormalClass_congr_rank {r r' : ℕ} (h : r = r')
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r'] :
    𝒩.virtualNormalClass C sX sZ hZ r =
      bivariantClassCongrDeg C (gysinSystemOfInvertible C) sZ sX i hZ (by rw [h])
        (𝒩.virtualNormalClass C sX sZ hZ r') := by
  subst h
  rfl

end RankCongr

/-! ### The identity on a connected component -/

section Component

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i] (𝒩 : VirtualNormalBundle i)
  (N' : Z.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  (inc : N' ⟶ 𝒩.bundle) (σ' : dualSheaf N' ⟶ Stacks.Thickenings.immersionConormalSheaf i)
  (hσ : dualMap inc ≫ σ' = 𝒩.surjection)
  (E : Z.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  (pr : 𝒩.bundle ⟶ E) (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)
  [IsLocallyNoetherian Z] [IsLocallyNoetherian X] (k : _root_.ConnectedComponents Z)

/-- `ℰ|_{Z_k}` has constant rank the rank of `ℰ` on `Z_k`. -/
instance isFiniteLocallyFreeOfRank_pullback_component :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (Z.connectedComponentOpens k).ι).obj E)
      (Scheme.Modules.rankOnConnectedComponent E k) :=
  Scheme.Modules.isFiniteLocallyFreeOfRank_pullback_of_fiberRank_eq E _ _ fun x hx => by
    rw [fiberRank_eq_moduleRank]
    obtain rfl : ConnectedComponents.mk x = k := hx
    exact (Scheme.Modules.rankOnConnectedComponent_mk E x).symm

/-- The map `𝒩|_{Z_k} ⟶ ℰ|_{Z_k}` of the restricted sequence. -/
def componentProjection : (𝒩.restrictComponent k).bundle ⟶
    (Scheme.Modules.pullback (Z.connectedComponentOpens k).ι).obj E :=
  (RingedSpaceModuleAdjunction.modulePullback
      (Z.connectedComponentOpens k).ι.toLRSHom.toShHom).map pr ≫
    (Stacks.ProjectiveBundleQuotients.pullbackIso (Z.connectedComponentOpens k).ι).inv.app E

/-- The map `𝒩'|_{Z_k} ⟶ 𝒩|_{Z_k}` of the restricted sequence. -/
abbrev componentInclusion :
    ((𝒩.ofFactor N' inc σ' hσ).restrictComponent k).bundle ⟶ (𝒩.restrictComponent k).bundle :=
  (RingedSpaceModuleAdjunction.modulePullback
    (Z.connectedComponentOpens k).ι.toLRSHom.toShHom).map inc

omit [SheafOfModules.IsFiniteLocallyFree E] in
include w in
/-- The composite `𝒩'|_{Z_k} ⟶ 𝒩|_{Z_k} ⟶ ℰ|_{Z_k}` of the restricted sequence is zero. -/
theorem componentInclusion_comp_componentProjection :
    𝒩.componentInclusion N' inc σ' hσ k ≫ 𝒩.componentProjection E pr k = 0 := by
  set e := Stacks.ProjectiveBundleQuotients.pullbackIso (Z.connectedComponentOpens k).ι
  have h1 : 𝒩.componentInclusion N' inc σ' hσ k ≫ 𝒩.componentProjection E pr k =
      e.inv.app N' ≫ (Scheme.Modules.pullback (Z.connectedComponentOpens k).ι).map (inc ≫ pr) := by
    rw [componentProjection, Functor.map_comp, ← Category.assoc, ← e.inv.naturality inc,
      Category.assoc, ← e.inv.naturality pr, ← Category.assoc]
    rfl
  rw [h1, w, Functor.map_zero, comp_zero]
  rfl

omit [SheafOfModules.IsFiniteLocallyFree E] in
include hseq in
/-- **The restricted sequence `0 ⟶ 𝒩'|_{Z_k} ⟶ 𝒩|_{Z_k} ⟶ ℰ|_{Z_k} ⟶ 0` is short exact**:
restriction to the open `Z_k` is exact. -/
theorem shortExact_component :
    (ShortComplex.mk (𝒩.componentInclusion N' inc σ' hσ k) (𝒩.componentProjection E pr k)
      (𝒩.componentInclusion_comp_componentProjection N' inc σ' hσ E pr w k)).ShortExact := by
  set e := Stacks.ProjectiveBundleQuotients.pullbackIso (Z.connectedComponentOpens k).ι
  let e1 : (Scheme.Modules.pullback (Z.connectedComponentOpens k).ι).obj N' ≅
      ((𝒩.ofFactor N' inc σ' hσ).restrictComponent k).bundle := e.app N'
  let e2 : (Scheme.Modules.pullback (Z.connectedComponentOpens k).ι).obj 𝒩.bundle ≅
      (𝒩.restrictComponent k).bundle := e.app 𝒩.bundle
  refine (ShortComplex.shortExact_iff_of_iso (ShortComplex.isoMk
    (S₁ := (ShortComplex.mk inc pr w).map (Scheme.Modules.pullback (Z.connectedComponentOpens k).ι))
    (S₂ := ShortComplex.mk (𝒩.componentInclusion N' inc σ' hσ k) (𝒩.componentProjection E pr k)
      (𝒩.componentInclusion_comp_componentProjection N' inc σ' hσ E pr w k))
    e1 e2 (Iso.refl _) ?_ ?_)).1
    (GenuineChern.shortExact_map_pullback (Z.connectedComponentOpens k).ι _ hseq)
  · exact (e.hom.naturality inc).symm
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ e.inv.app E)
      (e.hom.naturality pr).symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (e.hom_inv_id_app E)).trans
          ((Category.comp_id _).trans (Category.comp_id _).symm))))

include hseq in
/-- On a connected component `Z_k`, the rank of `𝒩` is the sum of the ranks of `𝒩'` and `ℰ`. -/
theorem componentRank_eq_add :
    𝒩.componentRank k = (𝒩.ofFactor N' inc σ' hσ).componentRank k +
      Scheme.Modules.rankOnConnectedComponent E k := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe k
  have hx : x ∈ Z.connectedComponentOpens (ConnectedComponents.mk x) := rfl
  exact subbundleRank_add _ _ _ _ _ _ (𝒩.componentInclusion N' inc σ' hσ _)
    (𝒩.componentProjection E pr _) (𝒩.componentInclusion_comp_componentProjection N' inc σ' hσ E
      pr w _) (𝒩.shortExact_component N' inc σ' hσ E pr w hseq _) ⟨x, hx⟩

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (hZ : i ≫ sX = sZ)

include hseq in
/-- **Stacks 0FBL on a connected component.** On `Z_k ⟶ W_k`, where `𝒩'` and `ℰ` have constant
ranks `a_k` and `b_k`,

  `c(Z_k ⟶ W_k, 𝒩|_{Z_k}) = c_{b_k}(ℰ|_{Z_k}) ∘ c(Z_k ⟶ W_k, 𝒩'|_{Z_k})`. -/
theorem componentClass_eq_composite :
    𝒩.componentClass C sX sZ hZ k =
      bivariantClassCongrDeg C (gysinSystemOfInvertible C) _ _ _ _
        (by rw [𝒩.componentRank_eq_add N' inc σ' hσ E pr w hseq k]; push_cast; ring)
        (BivariantClass.copy C (gysinSystemOfInvertible C) _ _ (Category.id_comp _)
          (comp_comp_structureMorphism_eq (Category.id_comp _)
            (baseChange_structure (isPullback_componentPiece i k) C sX sZ hZ))
          (baseChange_structure (isPullback_componentPiece i k) C sX sZ hZ) rfl
          (bivariantCompositeOfInvertible C ((Z.connectedComponentOpens k).ι ≫ sZ)
            ((Z.connectedComponentOpens k).ι ≫ sZ) ((componentAmbient i k).ι ≫ sX) (𝟙 _)
            (componentPiece i k) (Category.id_comp _)
            (baseChange_structure (isPullback_componentPiece i k) C sX sZ hZ)
            (Scheme.Modules.rankOnConnectedComponent E k)
            ((𝒩.ofFactor N' inc σ' hσ).componentRank k)
            (GenuineChern.chernClass C ((Z.connectedComponentOpens k).ι ≫ sZ)
              ((Scheme.Modules.pullback (Z.connectedComponentOpens k).ι).obj E)
              (Scheme.Modules.rankOnConnectedComponent E k) (Fin.last _))
            ((𝒩.ofFactor N' inc σ' hσ).componentClass C sX sZ hZ k))) := by
  have hrank := 𝒩.componentRank_eq_add N' inc σ' hσ E pr w hseq k
  have := isFiniteLocallyFreeOfRank_middle _ _ _ ((𝒩.ofFactor N' inc σ' hσ).componentRank k)
    (Scheme.Modules.rankOnConnectedComponent E k) (𝒩.componentInclusion N' inc σ' hσ k)
    (𝒩.componentProjection E pr k)
    (𝒩.componentInclusion_comp_componentProjection N' inc σ' hσ E pr w k)
    (𝒩.shortExact_component N' inc σ' hσ E pr w hseq k)
  have key := (𝒩.restrictComponent k).virtualNormalClass_eq_composite
    ((𝒩.ofFactor N' inc σ' hσ).restrictComponent k).bundle
    (𝒩.componentInclusion N' inc σ' hσ k)
    ((𝒩.ofFactor N' inc σ' hσ).restrictComponent k).surjection
    (𝒩.dualMap_pullback_comp_baseChange_surjection N' inc σ' hσ (isPullback_componentPiece i k))
    C ((componentAmbient i k).ι ≫ sX) ((𝒩.ofFactor N' inc σ' hσ).componentRank k)
    (Scheme.Modules.rankOnConnectedComponent E k) _ (𝒩.componentProjection E pr k)
    (𝒩.componentInclusion_comp_componentProjection N' inc σ' hσ E pr w k)
    (𝒩.shortExact_component N' inc σ' hσ E pr w hseq k) ((Z.connectedComponentOpens k).ι ≫ sZ)
    (baseChange_structure (isPullback_componentPiece i k) C sX sZ hZ)
  rw [componentClass, (𝒩.restrictComponent k).virtualNormalClass_congr_rank C _ _ _ hrank, key]
  refine BivariantClass.ext C _ _ _ _ _ _ fun {T} t _ m α ↦ eq_of_heq ?_
  rw [bivariantClassCongrDeg_cap, bivariantClassCongrDeg_cap]
  refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
  refine (BivariantClass.copy_cap C _ _ _ _ _ _ _ _ t m α).trans ?_
  refine HEq.trans ?_ (chowGroupDegreeEquiv_heq C _ _ _).symm
  exact (BivariantClass.copy_cap C _ _ _ _ _ _ _ _ t m α).symm

end Component

/-! ### The completed classes on a connected component -/

/-- The degree `p` part of the component `c_k` of a completed class whose sequence has degree `p`
term `d` is the restriction of `d` to the component. -/
private theorem completed_apply_eq_restriction {C : ChowSituation.{u}} {X Y : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
    {f : X ⟶ Y} [LocallyOfFiniteType f] (hf : f ≫ sY = sX) [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf)
    (p : ℤ) (d : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p)
    (hd : completedBivariantSequence C (gysinSystemOfInvertible C) sX sY f hf
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
      (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
      (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) c p = d)
    (k : _root_.ConnectedComponents X) :
    c k p = bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sY f hf p
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) d k :=
  (restriction_completedBivariantSequence C (gysinSystemOfInvertible C) sX sY f hf
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) c p k).symm.trans
    (congrArg (fun c ↦ bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sY f
      hf p (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) c k) hd)

section Concentration

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i] (𝒩 : VirtualNormalBundle i)
  (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (hZ : i ≫ sX = sZ)

/-- On a connected component `Z_k` of `Z`, the completed class `c(Z ⟶ X, 𝒩)` is concentrated in
the degree of the rank of `𝒩` on `Z_k`. -/
theorem completedClass_apply_eq_of (k : _root_.ConnectedComponents Z) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    𝒩.completedClass C sX sZ hZ k =
      DirectSum.of _ (𝒩.componentRank k : ℤ)
        (𝒩.completedClass C sX sZ hZ k (𝒩.componentRank k)) := by
  have := LocallyOfFiniteType.isLocallyNoetherian sZ
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  refine DirectSum.ext fun p ↦ ?_
  by_cases hp : p = (𝒩.componentRank k : ℤ)
  · subst hp
    exact (DirectSum.of_eq_same _ _).symm
  · refine Eq.trans ?_ (DirectSum.of_eq_of_ne _ _ _ hp).symm
    exact (completed_apply_eq_restriction hZ _ p _
      (𝒩.completedBivariantSequenceOfInvertible_completedClass C sX sZ hZ p) k).trans
      (𝒩.bivariantConnectedComponentRestriction_degreeClass_of_ne C sX sZ hZ (Ne.symm hp))

end Concentration

/-! ### The composite of the completed classes on a connected component -/

section Global

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i] (𝒩 : VirtualNormalBundle i)
  (N' : Z.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  (inc : N' ⟶ 𝒩.bundle) (σ' : dualSheaf N' ⟶ Stacks.Thickenings.immersionConormalSheaf i)
  (hσ : dualMap inc ≫ σ' = 𝒩.surjection)
  (E : Z.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (hZ : i ≫ sX = sZ)

/-- **The restriction to a connected component of `c_e(ℰ) ∘ c_a(Z ⟶ X, 𝒩')`** is the composite
of the restrictions, i.e. the composite of the components of the completed classes. -/
theorem connectedComponentRestriction_composite_heq (e a : ℕ) (k : _root_.ConnectedComponents Z) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sZ sX (𝟙 Z ≫ i)
        (comp_comp_structureMorphism_eq (Category.id_comp sZ) hZ) ((e : ℤ) + a)
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (bivariantCompositeOfInvertible C sZ sZ sX (𝟙 Z) i (Category.id_comp sZ) hZ e a
          (topChernClassComponent C sZ E e)
          ((𝒩.ofFactor N' inc σ' hσ).degreeClass C sX sZ hZ a)) k ≍
      bivariantCompositeOfInvertible C ((Z.connectedComponentOpens k).ι ≫ sZ)
        ((Z.connectedComponentOpens
          ((Scheme.Hom.continuous (𝟙 Z)).connectedComponentsMap k)).ι ≫ sZ)
        ((X.connectedComponentOpens (i.continuous.connectedComponentsMap
          ((Scheme.Hom.continuous (𝟙 Z)).connectedComponentsMap k))).ι ≫ sX)
        (Scheme.Hom.resConnectedComponent (𝟙 Z) k)
        (i.resConnectedComponent ((Scheme.Hom.continuous (𝟙 Z)).connectedComponentsMap k))
        (Scheme.Hom.resConnectedComponent_comp_ι_comp (𝟙 Z) (Category.id_comp sZ) k)
        (i.resConnectedComponent_comp_ι_comp hZ _) e a
        ((topChernClassCompleted C sZ E).1 k e)
        ((𝒩.ofFactor N' inc σ' hσ).completedClass C sX sZ hZ
          ((Scheme.Hom.continuous (𝟙 Z)).connectedComponentsMap k) a) := by
  have := LocallyOfFiniteType.isLocallyNoetherian sZ
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  refine (bivariantPieceRestriction_heq_of_index_eq C (gysinSystemOfInvertible C) sZ sX
    Z.connectedComponentOpens X.connectedComponentOpens
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) _ (𝟙 Z ≫ i) _
    (funext fun k ↦ Scheme.Hom.connectedComponentsMap_comp (𝟙 Z) i k) _
    (le_preimage_comp (𝟙 Z) i Z.connectedComponentOpens Z.connectedComponentOpens
      X.connectedComponentOpens (Scheme.Hom.continuous (𝟙 Z)).connectedComponentsMap
      i.continuous.connectedComponentsMap (Scheme.Hom.connectedComponentOpens_le_preimage (𝟙 Z))
      i.connectedComponentOpens_le_preimage) k _).trans ?_
  refine (heq_of_eq (bivariantPieceRestriction_bivariantComposite C (gysinSystemOfInvertible C)
    sZ sZ sX (𝟙 Z) i (Category.id_comp sZ) hZ e a (topChernClassComponent C sZ E e)
    ((𝒩.ofFactor N' inc σ' hσ).degreeClass C sX sZ hZ a) Z.connectedComponentOpens
    Z.connectedComponentOpens X.connectedComponentOpens
    (Scheme.Hom.continuous (𝟙 Z)).connectedComponentsMap i.continuous.connectedComponentsMap
    (Scheme.Hom.connectedComponentOpens_le_preimage (𝟙 Z)) i.connectedComponentOpens_le_preimage
    k (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C))).trans ?_
  refine (bivariantClassCongr_heq_self _ _ _ _ _).trans (heq_of_eq ?_)
  have h1 : (topChernClassCompleted C sZ E).1 k e =
      bivariantPieceRestriction C (gysinSystemOfInvertible C) sZ sZ (𝟙 Z) (Category.id_comp sZ) e
        Z.connectedComponentOpens Z.connectedComponentOpens
        (Scheme.Hom.continuous (𝟙 Z)).connectedComponentsMap
        (Scheme.Hom.connectedComponentOpens_le_preimage (𝟙 Z)) k
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (topChernClassComponent C sZ E e) :=
    completed_apply_eq_restriction (Category.id_comp sZ) _ e _
      (congrFun (completedBivariantSequenceOfInvertible_topChernClassCompleted C sZ E) e) k
  have h2 : (𝒩.ofFactor N' inc σ' hσ).completedClass C sX sZ hZ
        ((Scheme.Hom.continuous (𝟙 Z)).connectedComponentsMap k) a =
      bivariantPieceRestriction C (gysinSystemOfInvertible C) sZ sX i hZ a
        Z.connectedComponentOpens X.connectedComponentOpens
        i.continuous.connectedComponentsMap i.connectedComponentOpens_le_preimage
        ((Scheme.Hom.continuous (𝟙 Z)).connectedComponentsMap k)
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        ((𝒩.ofFactor N' inc σ' hσ).degreeClass C sX sZ hZ a) :=
    completed_apply_eq_restriction hZ _ a _
      ((𝒩.ofFactor N' inc σ' hσ).completedBivariantSequenceOfInvertible_completedClass C sX sZ
        hZ a) _
  rw [h1, h2]
  rfl

omit [LocallyOfFiniteType sZ] [LocallyOfFiniteType sX] in
/-- The restriction of `𝟙 Z ≫ i` to a piece is the restriction of `i`. -/
theorem pieceMap_id_comp [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
    (k : _root_.ConnectedComponents Z) :
    pieceMap (𝟙 Z ≫ i) Z.connectedComponentOpens (componentAmbient i) id
        (le_preimage_comp (𝟙 Z) i Z.connectedComponentOpens Z.connectedComponentOpens
          (componentAmbient i) id id (opens_le_preimage_id Z.connectedComponentOpens)
          (le_preimage_componentAmbient i)) k =
      componentPiece i k := by
  refine (cancel_mono (componentAmbient i k).ι).1 ?_
  refine (pieceMap_comp_ι (𝟙 Z ≫ i) Z.connectedComponentOpens (componentAmbient i) id _ k).trans
    (Eq.trans ?_ (pieceMap_comp_ι i Z.connectedComponentOpens (componentAmbient i) id
      (le_preimage_componentAmbient i) k).symm)
  exact congrArg ((Z.connectedComponentOpens k).ι ≫ ·) (Category.id_comp i)

/-- The family of the classes of the components, in the degree of the rank, is the class. -/
theorem componentFamily_heq [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
    {p : ℤ} {k : _root_.ConnectedComponents Z} (h : (𝒩.componentRank k : ℤ) = p) :
    𝒩.componentFamily C sX sZ hZ p k ≍ 𝒩.componentClass C sX sZ hZ k := by
  subst h
  rw [componentFamily_rank]

variable (pr : 𝒩.bundle ⟶ E) (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)

include hseq in
/-- **Stacks 0FBL.** Let `i : Z ⟶ X` be a closed immersion with virtual normal sheaf `𝒩`, let
`0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence of finite locally free `𝒪_Z`-modules, and let
`σ' : (𝒩')^∨ ⟶ 𝒞_{Z/X}` be such that `σ = σ' ∘ (𝒩^∨ ⟶ (𝒩')^∨)`. Then

  `c(Z ⟶ X, 𝒩) = c_top(ℰ) ∘ c(Z ⟶ X, 𝒩')`   in   `A^*(Z ⟶ X)^∧`,

where `c(Z ⟶ X, -)` is the class of Stacks 0FBK, `c_top(ℰ) ∈ A^*(Z)^∧` the top Chern class of
Stacks 0FA4, `∘` the composition `A^*(Z)^∧ × A^*(Z ⟶ X)^∧ ⟶ A^*(Z ⟶ X)^∧` of Stacks 0FE0, and the
composite, a class for `𝟙 Z ≫ i`, is read at `i`. -/
@[stacks 0FBL "c(Z → X, 𝒩) = c_top(ℰ) ∘ c(Z → X, 𝒩') in A^*(Z → X)^∧, for a short exact \
sequence 0 → 𝒩' → 𝒩 → ℰ → 0 of finite locally free O_Z-modules along which σ factors through \
σ' : (𝒩')^∨ → C_{Z/X}; ranks arbitrary, c(Z → X, -) the completed classes of Tag 0FBK, c_top(ℰ) \
the completed class of Tag 0FA4, ∘ the composition of Tag 0FE0"]
theorem completedClass_eq_topChernClassCompleted_comp :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    𝒩.completedClass C sX sZ hZ =
      completedBivariantGroupCongr C (gysinSystemOfInvertible C) sZ sX (Category.id_comp i)
        (comp_comp_structureMorphism_eq (Category.id_comp sZ) hZ) hZ
        (completedBivariantCompositeOfInvertible C sZ sZ sX (𝟙 Z) i (Category.id_comp sZ) hZ
          (topChernClassCompleted C sZ E).1
          ((𝒩.ofFactor N' inc σ' hσ).completedClass C sX sZ hZ)) := by
  have := LocallyOfFiniteType.isLocallyNoetherian sZ
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  refine (𝒩.eq_completedClass_of_restriction C sX sZ hZ _ fun p k ↦ ?_).symm
  have hk : (Scheme.Hom.continuous (𝟙 Z)).connectedComponentsMap k = k :=
    connectedComponentsMap_id_apply k
  have HA := le_preimage_comp (𝟙 Z) i Z.connectedComponentOpens Z.connectedComponentOpens
    (componentAmbient i) id id (opens_le_preimage_id Z.connectedComponentOpens)
    (le_preimage_componentAmbient i)
  set comp := completedBivariantCompositeOfInvertible C sZ sZ sX (𝟙 Z) i (Category.id_comp sZ) hZ
    (topChernClassCompleted C sZ E).1 ((𝒩.ofFactor N' inc σ' hσ).completedClass C sX sZ hZ)
  have hΦ := completedBivariantSequence_completedBivariantGroupCongr C (gysinSystemOfInvertible C)
    sZ sX (Category.id_comp i) (comp_comp_structureMorphism_eq (Category.id_comp sZ) hZ) hZ
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) comp p
  refine Eq.trans (congrArg (bivariantPieceRestrictionOfInvertible C sZ sX i hZ p
    Z.connectedComponentOpens (componentAmbient i) id (le_preimage_componentAmbient i) k) hΦ) ?_
  refine eq_of_heq ((bivariantPieceRestriction_copy_heq C (gysinSystemOfInvertible C) sZ sX
    Z.connectedComponentOpens (componentAmbient i)
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) p (Category.id_comp i)
    (comp_comp_structureMorphism_eq (Category.id_comp sZ) hZ) hZ id HA
    (le_preimage_componentAmbient i) k _).trans ?_)
  -- the ranks on `Z_k`
  have hak : (𝒩.ofFactor N' inc σ' hσ).componentRank k =
      ((𝒩.ofFactor N' inc σ' hσ).componentRank
        ((Scheme.Hom.continuous (𝟙 Z)).connectedComponentsMap k)) := by rw [hk]
  have hrk : (𝒩.componentRank k : ℤ) = ((Scheme.Modules.rankOnConnectedComponent E k) : ℤ) +
      (((𝒩.ofFactor N' inc σ' hσ).componentRank
        ((Scheme.Hom.continuous (𝟙 Z)).connectedComponentsMap k)) : ℤ) := by
    rw [𝒩.componentRank_eq_add N' inc σ' hσ E pr w hseq k, hak]; push_cast; ring
  -- `W_k` lies in the connected component of `X` that `Z_k` maps to
  have hle : componentAmbient i (id k) ≤
      X.connectedComponentOpens ((Scheme.Hom.continuous (𝟙 Z ≫ i)).connectedComponentsMap k) := by
    rw [Scheme.Hom.connectedComponentsMap_comp, hk]
    exact componentAmbient_le i k
  -- the restriction to `Z_k ⟶ X_{a(k)}` of the degree `p` part of the composite
  have hof := completedBivariantCompositeOfInvertible_of_of C sZ sZ sX (𝟙 Z) i
    (Category.id_comp sZ) hZ (topChernClassCompleted C sZ E).1
    ((𝒩.ofFactor N' inc σ' hσ).completedClass C sX sZ hZ) k
    (Scheme.Modules.rankOnConnectedComponent E k)
    ((𝒩.ofFactor N' inc σ' hσ).componentRank
      ((Scheme.Hom.continuous (𝟙 Z)).connectedComponentsMap k))
    (topChernClassCompleted_apply_eq_of C sZ E k)
    ((𝒩.ofFactor N' inc σ' hσ).completedClass_apply_eq_of C sX sZ hZ
      ((Scheme.Hom.continuous (𝟙 Z)).connectedComponentsMap k))
  -- agreement of `comp_k` with a class `v` after restriction passes to `Z_k ⟶ W_k`
  have hgrow : ∀ (q : ℤ) (v : BivariantClass C (gysinSystemOfInvertible C) sZ sX (𝟙 Z ≫ i)
      (comp_comp_structureMorphism_eq (Category.id_comp sZ) hZ) q),
      comp k q = bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sZ sX
        (𝟙 Z ≫ i) (comp_comp_structureMorphism_eq (Category.id_comp sZ) hZ) q
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) v k →
      bivariantPieceRestriction C (gysinSystemOfInvertible C) sZ sX (𝟙 Z ≫ i)
        (comp_comp_structureMorphism_eq (Category.id_comp sZ) hZ) q Z.connectedComponentOpens
        (componentAmbient i) id HA k (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (completedBivariantSequence C (gysinSystemOfInvertible C) sZ sX (𝟙 Z ≫ i)
          (comp_comp_structureMorphism_eq (Category.id_comp sZ) hZ)
          (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
          (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
          (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) comp q) =
        bivariantPieceRestriction C (gysinSystemOfInvertible C) sZ sX (𝟙 Z ≫ i)
          (comp_comp_structureMorphism_eq (Category.id_comp sZ) hZ) q Z.connectedComponentOpens
          (componentAmbient i) id HA k (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) v :=
    fun q v h ↦ bivariantPieceRestriction_eq_of_grow C (gysinSystemOfInvertible C) sZ sX (𝟙 Z ≫ i)
      (comp_comp_structureMorphism_eq (Category.id_comp sZ) hZ) _ Z.connectedComponentOpens
      X.connectedComponentOpens (Scheme.Hom.continuous (𝟙 Z ≫ i)).connectedComponentsMap
      (Scheme.Hom.connectedComponentOpens_le_preimage (𝟙 Z ≫ i)) (componentAmbient i) id HA k hle
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) _ _
      ((restriction_completedBivariantSequence C (gysinSystemOfInvertible C) sZ sX (𝟙 Z ≫ i) _
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
        (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) comp q k).trans h)
  by_cases hp : ((Scheme.Modules.rankOnConnectedComponent E k) : ℤ) +
      (((𝒩.ofFactor N' inc σ' hσ).componentRank
        ((Scheme.Hom.continuous (𝟙 Z)).connectedComponentsMap k)) : ℤ) = p
  · subst hp
    -- the restrictions to `Z_k ⟶ X_{a(k)}` of the degree part and of the composite agree
    have h2 := hgrow _ (bivariantCompositeOfInvertible C sZ sZ sX (𝟙 Z) i (Category.id_comp sZ) hZ
        (Scheme.Modules.rankOnConnectedComponent E k)
        ((𝒩.ofFactor N' inc σ' hσ).componentRank
          ((Scheme.Hom.continuous (𝟙 Z)).connectedComponentsMap k))
        (topChernClassComponent C sZ E (Scheme.Modules.rankOnConnectedComponent E k))
        ((𝒩.ofFactor N' inc σ' hσ).degreeClass C sX sZ hZ
          ((𝒩.ofFactor N' inc σ' hσ).componentRank
            ((Scheme.Hom.continuous (𝟙 Z)).connectedComponentsMap k))))
      (eq_of_heq ((heq_of_eq (congrFun (congrArg DFunLike.coe hof) _)).trans
        ((directSum_of_apply_heq rfl _).trans ((bivariantClassComponentCongr_heq_self _ _ _ _ _ _
          _ _).trans (𝒩.connectedComponentRestriction_composite_heq N' inc σ' hσ E C sX sZ hZ
            (Scheme.Modules.rankOnConnectedComponent E k)
            ((𝒩.ofFactor N' inc σ' hσ).componentRank
              ((Scheme.Hom.continuous (𝟙 Z)).connectedComponentsMap k)) k).symm))))
    refine (heq_of_eq h2).trans ?_
    -- restrict the composite to `Z_k ⟶ W_k` factor by factor
    refine (heq_of_eq (bivariantPieceRestriction_bivariantComposite C (gysinSystemOfInvertible C)
      sZ sZ sX (𝟙 Z) i
      (Category.id_comp sZ) hZ (Scheme.Modules.rankOnConnectedComponent E k)
      ((𝒩.ofFactor N' inc σ' hσ).componentRank
        ((Scheme.Hom.continuous (𝟙 Z)).connectedComponentsMap k))
      (topChernClassComponent C sZ E (Scheme.Modules.rankOnConnectedComponent E k))
      ((𝒩.ofFactor N' inc σ' hσ).degreeClass C sX sZ hZ
        ((𝒩.ofFactor N' inc σ' hσ).componentRank
          ((Scheme.Hom.continuous (𝟙 Z)).connectedComponentsMap k))) Z.connectedComponentOpens
      Z.connectedComponentOpens (componentAmbient i) id id
      (opens_le_preimage_id Z.connectedComponentOpens) (le_preimage_componentAmbient i) k
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C))).trans ?_
    refine (bivariantClassCongr_heq_self _ _ _ _ _).trans ?_
    have hU := connectedComponentOpens_le_rankLocus E k
    have hchern := pieceIdentityCongr_topChernClassComponent C sZ E Z.connectedComponentOpens k
      (Scheme.Modules.rankOnConnectedComponent E k) hU
    have hfam := (𝒩.ofFactor N' inc σ' hσ).bivariantPieceRestrictionOfInvertible_degreeClass C sX
      sZ hZ ((𝒩.ofFactor N' inc σ' hσ).componentRank
        ((Scheme.Hom.continuous (𝟙 Z)).connectedComponentsMap k)) k
    refine (bivariantComposite_heq_congr (pieceMap_id Z.connectedComponentOpens _ k) _
      (Category.id_comp _) _ rfl (congrArg Nat.cast hak).symm
      ((bivariantClassCongr_heq_self _ _ _ _ _).symm.trans (heq_of_eq hchern))
      ((heq_of_eq hfam).trans ((𝒩.ofFactor N' inc σ' hσ).componentFamily_heq C sX sZ hZ
        (congrArg Nat.cast hak)))
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C)).trans ?_
    -- the constant-rank identity on `Z_k ⟶ W_k`
    refine HEq.trans ?_ (𝒩.componentFamily_heq C sX sZ hZ hrk).symm
    rw [𝒩.componentClass_eq_composite N' inc σ' hσ E pr w hseq k C sX sZ hZ]
    exact ((bivariantClassCongrDeg_heq_self _ _ _).trans
      (BivariantClass.copy_heq_self _ _ _ _ _)).symm
  · have h2 := hgrow p 0 ((congrFun (congrArg DFunLike.coe hof) p).trans
      ((DirectSum.of_eq_of_ne (β := fun q ↦ BivariantClass C (gysinSystemOfInvertible C)
        ((Z.connectedComponentOpens k).ι ≫ sZ)
        ((X.connectedComponentOpens ((Scheme.Hom.continuous (𝟙 Z ≫ i)).connectedComponentsMap
          k)).ι ≫ sX) (Scheme.Hom.resConnectedComponent (𝟙 Z ≫ i) k)
        (Scheme.Hom.resConnectedComponent_comp_ι_comp (𝟙 Z ≫ i)
          (comp_comp_structureMorphism_eq (Category.id_comp sZ) hZ) k) q) _ _ _ (Ne.symm hp)).trans
        (bivariantPieceRestriction_zero C (gysinSystemOfInvertible C) sZ sX (𝟙 Z ≫ i)
          (comp_comp_structureMorphism_eq (Category.id_comp sZ) hZ) p Z.connectedComponentOpens
          X.connectedComponentOpens (Scheme.Hom.continuous (𝟙 Z ≫ i)).connectedComponentsMap
          (Scheme.Hom.connectedComponentOpens_le_preimage (𝟙 Z ≫ i)) k
          (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)).symm))
    refine (heq_of_eq (h2.trans (bivariantPieceRestriction_zero _ _ _ _ _ _ _ _ _ _ _ _ _))).trans
      (heq_of_eq ?_)
    exact (𝒩.componentFamily_of_ne C sX sZ hZ (fun h ↦ hp (hrk.symm.trans h))).symm

end Global

end Stacks.Chow.VirtualNormalBundle

end
