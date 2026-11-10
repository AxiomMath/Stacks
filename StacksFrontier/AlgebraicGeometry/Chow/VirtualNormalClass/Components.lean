module

public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.ComparisonComposite
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceShrinkTarget
public import StacksFrontier.AlgebraicGeometry.Chow.TopChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.RankLoci
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantRank
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import StacksFrontier.AlgebraicGeometry.Thickenings.OpenRestriction

/-!
# The class `c(Z ⟶ X, 𝒩)` of a virtual normal bundle of non-constant rank

Let `(S, δ)` be as in Situation 02QL, `i : Z ⟶ X` a closed immersion of schemes locally of finite
type over `S` and `𝒩` a virtual normal bundle for `i`. The rank of `𝒩` is locally constant, so it
is constant, say `r_k`, on each connected component `Z_k` of `Z` (which is open and closed, `Z`
being locally Noetherian). Let `X_{a(k)}` be the connected component of `X` containing `i(Z_k)`
and `W_k = X_{a(k)} ∖ i(Z ∖ Z_k)`, an open of `X` with `i⁻¹(W_k) = Z_k`. The square of
`Z_k ⟶ W_k` over `i` is cartesian, so `𝒩|_{Z_k}` is a virtual normal bundle for `Z_k ⟶ W_k`
(Stacks 0FBJ), of constant rank `r_k`, and the construction preceding Stacks 0FBK gives a class
`c(Z_k ⟶ W_k, 𝒩|_{Z_k}) ∈ A^{r_k}(Z_k ⟶ W_k)`.

By Stacks 0FDZ the families of these classes, placed in degree `r_k` and extended by zero in the
other degrees, assemble to classes `c_p ∈ A^p(Z ⟶ X)`, one for each `p`. On a connected
component `Z_k` the class `c_p` restricted to `Z_k ⟶ X_{a(k)}` vanishes unless `p = r_k`, since it
already vanishes on the smaller target `W_k`
(`Stacks.Chow.bivariantPieceRestriction_eq_zero_of_shrink`). So the tuple `(c_p)_p` is almost
vanishing on every connected component, and it is an element `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` of the
completed bivariant group of Stacks 0FE0.

## Main definitions

* `Stacks.Chow.VirtualNormalBundle.componentAmbient` — the open `W_k ⊆ X` cutting out `Z_k`.
* `Stacks.Chow.VirtualNormalBundle.restrictComponent` — the virtual normal bundle `𝒩|_{Z_k}` for
  `Z_k ⟶ W_k`.
* `Stacks.Chow.VirtualNormalBundle.componentFamily` — the family of the classes
  `c(Z_k ⟶ W_k, 𝒩|_{Z_k})` in degree `p`.
* `Stacks.Chow.VirtualNormalBundle.degreeClass` — the class `c_p ∈ A^p(Z ⟶ X)`.
* `Stacks.Chow.VirtualNormalBundle.completedClass` — `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧`.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow.VirtualNormalBundle

section Ambient

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The open `X ∖ i(Z ∖ V)` of `X`, which `i` pulls back to the open `V ⊆ Z`. -/
def clopenAmbient (V : Z.Opens) : X.Opens where
  carrier := (i.base '' (V : Set Z)ᶜ)ᶜ
  is_open' := by
    rw [isOpen_compl_iff]
    exact i.isClosedEmbedding.isClosedMap _ (isClosed_compl_iff.mpr V.2)

/-- `i⁻¹(X ∖ i(Z ∖ V)) = V`. -/
theorem preimage_clopenAmbient (V : Z.Opens) : i ⁻¹ᵁ clopenAmbient i V = V := by
  ext z
  change i.base z ∈ (i.base '' (V : Set Z)ᶜ)ᶜ ↔ z ∈ V
  rw [Set.mem_compl_iff, i.isClosedEmbedding.injective.mem_set_image, Set.mem_compl_iff,
    not_not]
  rfl

variable [LocallyConnectedSpace Z] [LocallyConnectedSpace X]

/-- The open `W_k = X_{a(k)} ∖ i(Z ∖ Z_k)` of `X` attached to a connected component `Z_k` of `Z`,
where `X_{a(k)}` is the connected component of `X` containing `i(Z_k)`. -/
def componentAmbient (k : _root_.ConnectedComponents Z) : X.Opens :=
  X.connectedComponentOpens (i.continuous.connectedComponentsMap k) ⊓
    clopenAmbient i (Z.connectedComponentOpens k)

/-- `i⁻¹(W_k) = Z_k`. -/
theorem preimage_componentAmbient (k : _root_.ConnectedComponents Z) :
    i ⁻¹ᵁ componentAmbient i k = Z.connectedComponentOpens k := by
  refine le_antisymm (fun z hz => (preimage_clopenAmbient i _).le hz.2) fun z hz => ?_
  exact ⟨i.connectedComponentOpens_le_preimage k hz, (preimage_clopenAmbient i _).ge hz⟩

/-- `W_k` is contained in the connected component `X_{a(k)}` of `X`. -/
theorem componentAmbient_le (k : _root_.ConnectedComponents Z) :
    componentAmbient i k ≤ X.connectedComponentOpens (i.continuous.connectedComponentsMap k) :=
  inf_le_left

/-- `Z_k ⊆ i⁻¹(W_k)`. -/
theorem le_preimage_componentAmbient (k : _root_.ConnectedComponents Z) :
    Z.connectedComponentOpens k ≤ i ⁻¹ᵁ componentAmbient i k :=
  (preimage_componentAmbient i k).ge

/-- The closed immersion `Z_k ⟶ W_k`. -/
abbrev componentPiece (k : _root_.ConnectedComponents Z) :
    (Z.connectedComponentOpens k : Scheme.{u}) ⟶ (componentAmbient i k : Scheme.{u}) :=
  pieceMap i Z.connectedComponentOpens (componentAmbient i) id (le_preimage_componentAmbient i) k

/-- The square of `Z_k ⟶ W_k` over `i` is cartesian. -/
theorem isPullback_componentPiece (k : _root_.ConnectedComponents Z) :
    IsPullback (componentPiece i k) (Z.connectedComponentOpens k).ι (componentAmbient i k).ι i :=
  Stacks.Thickenings.isPullback_resLE_of_preimage_eq i (preimage_componentAmbient i k)

/-- `Z_k ⟶ W_k` is a closed immersion. -/
instance isClosedImmersion_componentPiece (k : _root_.ConnectedComponents Z) :
    IsClosedImmersion (componentPiece i k) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_componentPiece i k).flip
    inferInstance

end Ambient

section Bundle

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i] [LocallyConnectedSpace Z]
  [LocallyConnectedSpace X] (𝒩 : VirtualNormalBundle i)

/-- The virtual normal bundle `𝒩|_{Z_k}` for `Z_k ⟶ W_k`, Stacks 0FBJ. -/
abbrev restrictComponent (k : _root_.ConnectedComponents Z) :
    VirtualNormalBundle (componentPiece i k) :=
  𝒩.baseChangeAlong (isPullback_componentPiece i k)

/-- The rank `r_k` of `𝒩` on the connected component `Z_k`. -/
abbrev componentRank (k : _root_.ConnectedComponents Z) : ℕ :=
  Scheme.Modules.rankOnConnectedComponent 𝒩.bundle k

omit [LocallyConnectedSpace X] in
/-- The fibre rank of `𝒩` at a point of `Z_k` is `r_k`. -/
theorem fiberRank_eq_componentRank (k : _root_.ConnectedComponents Z) (x : Z)
    (hx : x ∈ Z.connectedComponentOpens k) :
    Scheme.Modules.fiberRank 𝒩.bundle x = 𝒩.componentRank k := by
  rw [fiberRank_eq_moduleRank]
  obtain rfl : ConnectedComponents.mk x = k := hx
  exact (Scheme.Modules.rankOnConnectedComponent_mk 𝒩.bundle x).symm

/-- `𝒩|_{Z_k}` has constant rank `r_k`. -/
instance isFiniteLocallyFreeOfRank_restrictComponent (k : _root_.ConnectedComponents Z) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (𝒩.restrictComponent k).bundle
      (𝒩.componentRank k) :=
  SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    ((Stacks.ProjectiveBundleQuotients.pullbackIso (Z.connectedComponentOpens k).ι).app 𝒩.bundle)
    (Scheme.Modules.isFiniteLocallyFreeOfRank_pullback_of_fiberRank_eq 𝒩.bundle _ _
      (𝒩.fiberRank_eq_componentRank k))

end Bundle

section Chow

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i] (𝒩 : VirtualNormalBundle i)
  (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (hZ : i ≫ sX = sZ) [IsLocallyNoetherian Z] [IsLocallyNoetherian X]

/-- The class `c(Z_k ⟶ W_k, 𝒩|_{Z_k}) ∈ A^{r_k}(Z_k ⟶ W_k)` of a connected component. -/
def componentClass (k : _root_.ConnectedComponents Z) :
    BivariantClass C (gysinSystemOfInvertible C) ((Z.connectedComponentOpens k).ι ≫ sZ)
      ((componentAmbient i k).ι ≫ sX) (componentPiece i k)
      (pieceMap_comp_pieceStructureMorphism C sZ sX i hZ Z.connectedComponentOpens
        (componentAmbient i) id (le_preimage_componentAmbient i) k)
      (𝒩.componentRank k) :=
  (𝒩.restrictComponent k).virtualNormalClass C ((componentAmbient i k).ι ≫ sX)
    ((Z.connectedComponentOpens k).ι ≫ sZ)
    (baseChange_structure (isPullback_componentPiece i k) C sX sZ hZ) (𝒩.componentRank k)

/-- The family, over the connected components `Z_k`, of the classes `c(Z_k ⟶ W_k, 𝒩|_{Z_k})` in
degree `p`: the class itself on a component where `𝒩` has rank `p`, zero elsewhere. -/
def componentFamily (p : ℤ) (k : _root_.ConnectedComponents Z) :
    BivariantClass C (gysinSystemOfInvertible C) ((Z.connectedComponentOpens k).ι ≫ sZ)
      ((componentAmbient i k).ι ≫ sX) (componentPiece i k)
      (pieceMap_comp_pieceStructureMorphism C sZ sX i hZ Z.connectedComponentOpens
        (componentAmbient i) id (le_preimage_componentAmbient i) k) p :=
  if h : (𝒩.componentRank k : ℤ) = p then h ▸ 𝒩.componentClass C sX sZ hZ k else 0

/-- In degree `r_k` the family is `c(Z_k ⟶ W_k, 𝒩|_{Z_k})` on `Z_k`. -/
theorem componentFamily_rank (k : _root_.ConnectedComponents Z) :
    𝒩.componentFamily C sX sZ hZ (𝒩.componentRank k) k = 𝒩.componentClass C sX sZ hZ k := by
  rw [componentFamily, dite_eq_left rfl]

/-- In a degree `p ≠ r_k` the family vanishes on `Z_k`. -/
theorem componentFamily_of_ne {p : ℤ} {k : _root_.ConnectedComponents Z}
    (h : (𝒩.componentRank k : ℤ) ≠ p) : 𝒩.componentFamily C sX sZ hZ p k = 0 := by
  rw [componentFamily, dite_eq_right h]

/-- **The class `c_p ∈ A^p(Z ⟶ X)`**: the class whose restriction to `Z_k ⟶ W_k` is
`c(Z_k ⟶ W_k, 𝒩|_{Z_k})` when `𝒩` has rank `p` on `Z_k`, and zero otherwise (Stacks 0FDZ). -/
def degreeClass (p : ℤ) : BivariantClass C (gysinSystemOfInvertible C) sZ sX i hZ p :=
  (bivariantPieceEquivOfInvertible C sZ sX i hZ p Z.connectedComponentOpens (componentAmbient i) id
    (le_preimage_componentAmbient i) Z.isClopenDecomposition_connectedComponentOpens).symm
    (𝒩.componentFamily C sX sZ hZ p)

/-- The restriction of `c_p` to `Z_k ⟶ W_k`. -/
theorem bivariantPieceRestrictionOfInvertible_degreeClass (p : ℤ)
    (k : _root_.ConnectedComponents Z) :
    bivariantPieceRestrictionOfInvertible C sZ sX i hZ p Z.connectedComponentOpens
        (componentAmbient i) id (le_preimage_componentAmbient i) k (𝒩.degreeClass C sX sZ hZ p) =
      𝒩.componentFamily C sX sZ hZ p k :=
  congrFun ((bivariantPieceEquivOfInvertible C sZ sX i hZ p Z.connectedComponentOpens
    (componentAmbient i) id (le_preimage_componentAmbient i)
    Z.isClopenDecomposition_connectedComponentOpens).apply_symm_apply _) k

/-- The cap operation of the family in degree `p` is that of the restriction of `c_p`. -/
theorem componentFamily_cap (p : ℤ) (k : _root_.ConnectedComponents Z) {T : Scheme.{u}}
    (t : T ⟶ (componentAmbient i k : Scheme.{u})) [LocallyOfFiniteType t] (n : ℤ)
    (β : chowGroup C (t ≫ ((componentAmbient i k).ι ≫ sX)) n) :
    (𝒩.componentFamily C sX sZ hZ p k).cap t n β =
      bivariantPieceRestrictionCap C (gysinSystemOfInvertible C) sZ sX i hZ p
        Z.connectedComponentOpens (componentAmbient i) id (le_preimage_componentAmbient i) k
        (𝒩.degreeClass C sX sZ hZ p) t n β :=
  (congrArg (fun e => e.cap t n β)
    (𝒩.bivariantPieceRestrictionOfInvertible_degreeClass C sX sZ hZ p k)).symm

/-- On a connected component `Z_k` of `Z`, the class `c_p` restricted to `Z_k ⟶ X_{a(k)}` vanishes
unless `p` is the rank of `𝒩` on `Z_k`. -/
theorem bivariantConnectedComponentRestriction_degreeClass_of_ne {p : ℤ}
    {k : _root_.ConnectedComponents Z} (h : (𝒩.componentRank k : ℤ) ≠ p) :
    bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sZ sX i hZ p
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) (𝒩.degreeClass C sX sZ hZ p) k = 0 :=
  bivariantPieceRestriction_eq_zero_of_shrink C (gysinSystemOfInvertible C) sZ sX i hZ p
    Z.connectedComponentOpens X.connectedComponentOpens i.continuous.connectedComponentsMap
    i.connectedComponentOpens_le_preimage (componentAmbient i) id
    (le_preimage_componentAmbient i) k (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (𝒩.degreeClass C sX sZ hZ p)
    ((𝒩.bivariantPieceRestrictionOfInvertible_degreeClass C sX sZ hZ p k).trans
      (𝒩.componentFamily_of_ne C sX sZ hZ h))

/-- The tuple `(c_p)_p` lies in the completed bivariant group: on every connected component it
vanishes outside the single degree `r_k`. -/
theorem degreeClass_mem_completedBivariantSubgroupOfInvertible :
    (fun p => 𝒩.degreeClass C sX sZ hZ p) ∈
      completedBivariantSubgroupOfInvertible C sZ sX i hZ := fun k =>
  (Set.finite_singleton (𝒩.componentRank k : ℤ)).subset fun p hp => by
    by_contra hne
    exact hp (𝒩.bivariantConnectedComponentRestriction_degreeClass_of_ne C sX sZ hZ
      (Ne.symm hne))

omit [IsLocallyNoetherian Z] [IsLocallyNoetherian X] in
/-- **Stacks 0FBK.** The class `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` of a virtual normal bundle whose rank
need not be constant: the element of the completed bivariant group of Stacks 0FE0 whose degree
`p` part is the class `c_p ∈ A^p(Z ⟶ X)` restricting to `c(Z_k ⟶ W_k, 𝒩|_{Z_k})` on every connected
component `Z_k` on which `𝒩` has rank `p`, and to zero on the others. The schemes `Z` and `X`
are locally Noetherian, being locally of finite type over the base. -/
@[stacks 0FBK "the class c(Z → X, 𝒩) ∈ A^*(Z → X)^∧ of a virtual normal bundle of arbitrary rank; \
its degree p part restricts on each connected component Z_k to c(Z_k → W_k, 𝒩|Z_k) of the \
construction when 𝒩 has rank p there, and to zero otherwise"]
def completedClass : completedBivariantGroup C (gysinSystemOfInvertible C) sZ sX i hZ :=
  letI := LocallyOfFiniteType.isLocallyNoetherian sZ
  letI := LocallyOfFiniteType.isLocallyNoetherian sX
  (completedBivariantGroupEquivOfInvertible C sZ sX i hZ).symm
    ⟨fun p => 𝒩.degreeClass C sX sZ hZ p,
      𝒩.degreeClass_mem_completedBivariantSubgroupOfInvertible C sX sZ hZ⟩

/-- The degree `p` part of `c(Z ⟶ X, 𝒩)` is `c_p`. -/
theorem completedBivariantSequenceOfInvertible_completedClass (p : ℤ) :
    completedBivariantSequenceOfInvertible C sZ sX i hZ (𝒩.completedClass C sX sZ hZ) p =
      𝒩.degreeClass C sX sZ hZ p :=
  congrFun (congrArg Subtype.val ((completedBivariantGroupEquivOfInvertible C sZ sX i
    hZ).apply_symm_apply ⟨fun p => 𝒩.degreeClass C sX sZ hZ p,
      𝒩.degreeClass_mem_completedBivariantSubgroupOfInvertible C sX sZ hZ⟩)) p

end Chow

end Stacks.Chow.VirtualNormalBundle

end
