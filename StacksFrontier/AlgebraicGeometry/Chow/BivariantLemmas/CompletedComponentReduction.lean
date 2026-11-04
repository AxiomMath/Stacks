module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedConstantRank
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessNormalSheafBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.TopChernClassOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.GysinAtInfinityRestriction
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.RankReduction

/-!
# Reduction to the connected components, for the completed virtual normal class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `i : Z ⟶ X` be a
closed immersion of schemes locally of finite type over `S` and let `𝒩` be a virtual normal sheaf
for `i` of arbitrary rank, with class `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧`
(`Stacks.Chow.completedVirtualNormalGysinClass`, Stacks 0FBK). On a connected component `Z_a` of
`Z` the rank of `𝒩` is constant, and the class is built from the class at constant rank of
`Z_a ⟶ U_a` for an open `U_a ⊆ X` with `Z ×_X U_a = Z_a`. This file collects what is needed to
prove an identity of the completed class from the identity at constant rank, one connected
component at a time:

* on a test scheme over `U_a` the degree-`r_a` part of `c(Z ⟶ X, 𝒩)` caps as
  `c(Z_a ⟶ U_a, 𝒩|_{Z_a})`, and its other degree parts vanish over `Z_a`;
* for a cartesian square `Z' = Z ×_X Y`, the pieces `Z'_a ⊆ Z'` over the connected components
  `Z_a` are cartesian over `Z_a ⟶ U_a`, and a Chow class on `Z ×_X Y` is determined by its
  restrictions to them (Stacks 0FDZ).

These were proved for the excess intersection formula at arbitrary rank (Stacks 0FBM,
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedExcessIntersectionFormula`) and are
shared from here.

## Main results

* `Stacks.Chow.componentTestIso` — `Z_a ×_{U_a} T = Z ×_X T` for a test scheme over `U_a`.
* `Stacks.Chow.chowGroupRestrict_completedVirtualNormalGysinClass_cap` — on a test scheme over
  `U_a`, the degree-`r_a` part of `c(Z ⟶ X, 𝒩)` is `c(Z_a ⟶ U_a, 𝒩|_{Z_a})`.
* `Stacks.Chow.bivariantConnectedComponentRestriction_completedVirtualNormalGysinClass_eq_zero` —
  on `Z_a` the other degree parts vanish.
* `Stacks.Chow.isPullback_pieceProjection` — the piece `Z'_a` is the base change of
  `Z_a ⟶ U_a`.
* `Stacks.Chow.eq_of_chowGroupRestrict_piece_eq` — a class on `Z ×_X Y` is determined by its
  restrictions to the pieces.
* `Stacks.Chow.chowGroupRestrict_topChernCap`, `Stacks.Chow.topChernCap_congr` — the top Chern
  class on an open of constant rank, and for isomorphic modules.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

/-! ### Restriction along an open immersion which is the identity -/

/-- Restriction of Chow classes along an open immersion equal to the identity does not change the
class. -/
theorem chowGroupRestrict_heq_of_eq_id (C : ChowSituation.{u}) {A : Scheme.{u}} {sA sA' : A ⟶ C.S}
    [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] (v : A ⟶ A) [IsOpenImmersion v]
    (hv1 : v = 𝟙 A) (hv : v ≫ sA = sA') {k : ℤ} (x : chowGroup C sA k) :
    chowGroupRestrict C sA sA' v hv k x ≍ x :=
  (chowGroupRestrict_heq_congr C sA sA' sA v (𝟙 A) hv (Category.id_comp sA) hv1 k x).trans
    (heq_of_eq (chowGroupRestrict_id C sA k x))

/-- Restriction along an isomorphism undoes the pushforward along it. -/
theorem chowGroupRestrict_chowPushforwardOfIso (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (u : A ⟶ B)
    [IsIso u] (hu : u ≫ sB = sA) (k : ℤ) (x : chowGroup C sA k) :
    chowGroupRestrict C sB sA u hu k (chowPushforwardOfIso C sA sB u hu k x) = x := by
  rw [chowGroupRestrict_of_isIso, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_congr_apply C _ _ _ (𝟙 A) (IsIso.hom_inv_id u) _ (Category.id_comp _),
    chowPushforwardOfIso_id]

/-! ### Open subschemes: dimension and rank -/

/-- **An open subscheme has `δ`-dimension at most that of the scheme**: the `δ`-dimension is the
supremum of the relative dimensions of the generic points of the irreducible components, and an
open immersion does not change relative dimensions. -/
theorem schemeDeltaDimension_le_of_isOpenImmersion (C : ChowSituation.{u}) {V W : Scheme.{u}}
    (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (sV : V ⟶ C.S) [LocallyOfFiniteType sV]
    (v : V ⟶ W) [IsOpenImmersion v] (hv : v ≫ sW = sV) {k : ℤ}
    (hW : schemeDeltaDimension C sW ≤ (k : EInt)) : schemeDeltaDimension C sV ≤ (k : EInt) := by
  rw [schemeDeltaDimension_eq_iSup]
  refine iSup_le fun Zc => WithBotTop.coe_le_coe.mpr ?_
  have hgp := Zc.2.1.isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents (Zc : Set V) Zc.2)
  rw [deltaDimension_eq_of_isGenericPoint C sV _ _ hgp, ← hv,
    relativeDimension_comp_isOpenImmersion]
  exact relativeDimension_le_of_schemeDeltaDimension_le' C sW hW _

/-! ### The class on test schemes over the neighbourhood of a connected component -/

section ComponentCap

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ)
  [IsLocallyNoetherian Z] [IsLocallyNoetherian X] (𝒩 : VirtualNormalBundle i)
  (a : _root_.ConnectedComponents Z)

/-- **`Z_a ×_{U_a} T = Z ×_X T`** for a test morphism `t : T ⟶ X` factoring through the open
`U_a ⊆ X` of a connected component `Z_a` of `Z`, whose preimage in `Z` is `Z_a`. -/
def componentTestIso {T : Scheme.{u}} (h : T ⟶ componentNeighbourhood i a) (t : T ⟶ X)
    (ht : h ≫ (componentNeighbourhood i a).ι = t) :
    pullback (componentRestriction i a) h ≅ pullback i t where
  hom := pullback.lift (pullback.fst _ h ≫ (Z.connectedComponentOpens a).ι) (pullback.snd _ h)
    (by rw [Category.assoc, ← componentRestriction_ι, ← Category.assoc, pullback.condition,
      Category.assoc, ht])
  inv := pullback.lift ((isPullback_componentRestriction i a).lift (pullback.snd i t ≫ h)
      (pullback.fst i t) (by rw [Category.assoc, ht, pullback.condition]))
    (pullback.snd i t) (by rw [IsPullback.lift_fst])
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      refine (isPullback_componentRestriction i a).hom_ext ?_ ?_
      · rw [Category.assoc, IsPullback.lift_fst, ← Category.assoc, pullback.lift_snd]
        exact pullback.condition.symm
      · rw [Category.assoc, IsPullback.lift_snd, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
        IsPullback.lift_snd, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]

/-- The first projection of `componentTestIso` is the first projection of `Z_a ×_{U_a} T` followed
by the inclusion `Z_a ⟶ Z`. -/
@[reassoc (attr := simp)]
theorem componentTestIso_hom_fst {T : Scheme.{u}} (h : T ⟶ componentNeighbourhood i a)
    (t : T ⟶ X) (ht : h ≫ (componentNeighbourhood i a).ι = t) :
    (componentTestIso i a h t ht).hom ≫ pullback.fst i t =
      pullback.fst _ h ≫ (Z.connectedComponentOpens a).ι :=
  pullback.lift_fst _ _ _

/-- The second projection of `componentTestIso` is the second projection of `Z_a ×_{U_a} T`. -/
@[reassoc (attr := simp)]
theorem componentTestIso_hom_snd {T : Scheme.{u}} (h : T ⟶ componentNeighbourhood i a)
    (t : T ⟶ X) (ht : h ≫ (componentNeighbourhood i a).ι = t) :
    (componentTestIso i a h t ht).hom ≫ pullback.snd i t = pullback.snd _ h :=
  pullback.lift_snd _ _ _

/-- The restriction to `Z_a` of the degree `p` part of `c(Z ⟶ X, 𝒩)` is the degree `p` term of
its component at `a`. -/
private theorem restriction_completedVirtualNormalGysinClass (p : ℤ) :
    bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sZ sX i hi p
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
      (completedBivariantSequenceOfInvertible C sZ sX i hi
        (completedVirtualNormalGysinClass C sZ sX i hi 𝒩) p) a =
      completedVirtualNormalGysinClass C sZ sX i hi 𝒩 a p :=
  restriction_completedBivariantSequence C (gysinSystemOfInvertible C) sZ sX i hi
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C)
    (completedVirtualNormalGysinClass C sZ sX i hi 𝒩) p a

/-- **The cap operation of `c ∘ j^*`, read for an equal morphism.** For an open immersion
`j : U ⟶ X'` and a class `c ∈ A^p(Z ⟶ U)`, the composite `c ∘ j^*` read as a class for a morphism
`f'` equal to `i ≫ j` caps on a test scheme `s : T ⟶ X'` by restricting to `U ×_{X'} T`, capping
with `c`, and pushing forward along `Z ×_U (U ×_{X'} T) ≅ Z ×_{X'} T`. -/
theorem copy_openImmersionComposite_cap {Z' U X' : Scheme.{u}} (sZ' : Z' ⟶ C.S)
    [LocallyOfFiniteType sZ'] (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (sX' : X' ⟶ C.S)
    [LocallyOfFiniteType sX'] (f : Z' ⟶ U) [LocallyOfFiniteType f] (j : U ⟶ X') [IsOpenImmersion j]
    (hf : f ≫ sU = sZ') (hj : j ≫ sX' = sU) {f' : Z' ⟶ X'} [LocallyOfFiniteType f']
    (hff' : f ≫ j = f') (hf' : f' ≫ sX' = sZ') (p : ℤ) (hp : p + -((0 : ℕ) : ℤ) = p)
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ' sU f hf p) {T : Scheme.{u}}
    (s : T ⟶ X') [LocallyOfFiniteType s] (k : ℤ) (β : chowGroup C (s ≫ sX') k) :
    (BivariantClass.copy C (gysinSystemOfInvertible C) sZ' sX' hff'
        (comp_comp_structureMorphism_eq hf hj) hf' hp
        (openImmersionComposite C sZ' sU sX' f j hf hj p c)).cap s k β =
      chowPushforwardOfIso C (pullback.fst f (pullback.fst j s) ≫ sZ') (pullback.fst f' s ≫ sZ')
        ((pullbackRightPullbackFstIso j s f) ≪≫ pullback.congrHom hff' rfl).hom
        (by subst hff'; simp) (k - p)
        (c.cap (pullback.fst j s) k
          (chowGroupRestrict C (s ≫ sX') (pullback.fst j s ≫ sU) (pullback.snd j s)
            (pullbackSnd_comp_structureMorphism hj s) k β)) := by
  subst hff'
  refine eq_of_heq ((BivariantClass.copy_cap C _ _ _ _ _ _ _ _ s k β).trans
    ((openImmersionComposite_cap_heq C sZ' sU sX' f j hf hj p c s k β).trans (heq_of_eq ?_)))
  exact chowPushforwardOfIso_congr_apply C _ _ _ _ (by simp) _ _ _ _

/-- **Stacks 0FBK, the degree parts of `c(Z ⟶ X, 𝒩)` over the neighbourhood of a connected
component.** Let `Z_a` be a connected component of `Z`, on which `𝒩` has rank `m`, and let
`U_a ⊆ X` be the open of the construction of `Stacks.Chow.completedVirtualNormalGysinClass`, with
`Z ×_X U_a = Z_a`. On a test scheme `t : T ⟶ U_a`, the degree-`m` part of the completed class
caps, after restriction to the open `Z_a ×_{U_a} T = Z ×_X T`, as `c(Z_a ⟶ U_a, 𝒩|_{Z_a})`. -/
theorem chowGroupRestrict_completedVirtualNormalGysinClass_cap (m : ℕ)
    (hm : componentRank 𝒩.bundle a = m)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (𝒩.toComponent i a).bundle m]
    {T : Scheme.{u}} (t : T ⟶ componentNeighbourhood i a) [LocallyOfFiniteType t] (k : ℤ)
    (β : chowGroup C (t ≫ ((componentNeighbourhood i a).ι ≫ sX)) k) :
    chowGroupRestrict C (pullback.fst i (t ≫ (componentNeighbourhood i a).ι) ≫ sZ)
        (pullback.fst (componentRestriction i a) t ≫ ((Z.connectedComponentOpens a).ι ≫ sZ))
        (componentTestIso i a t _ rfl).hom (by rw [componentTestIso_hom_fst_assoc])
        (k - (m : ℤ))
        ((completedBivariantSequenceOfInvertible C sZ sX i hi
            (completedVirtualNormalGysinClass C sZ sX i hi 𝒩) (m : ℤ)).cap
          (t ≫ (componentNeighbourhood i a).ι) k
          (chowGroupCongr C (Category.assoc _ _ _).symm k β)) =
      (virtualNormalBundleClass C ((Z.connectedComponentOpens a).ι ≫ sZ)
        ((componentNeighbourhood i a).ι ≫ sX) (componentRestriction i a)
        (componentRestriction_comp_structureMorphism C sZ sX i hi a) (𝒩.toComponent i a)
        m).cap t k β := by
  subst hm
  -- `T = U_a ×_{X_b} T` along the open immersion `U_a ⟶ X_b`
  have hσ : pullback.snd (componentInclusion i a) (t ≫ componentInclusion i a) ≫ t =
      pullback.fst (componentInclusion i a) (t ≫ componentInclusion i a) := by
    rw [← cancel_mono (componentInclusion i a), Category.assoc]
    exact pullback.condition.symm
  have : IsIso (pullback.snd (componentInclusion i a) (t ≫ componentInclusion i a)) :=
    ⟨⟨pullback.lift t (𝟙 T) (Category.id_comp _).symm, by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, Category.id_comp, hσ]
      · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp],
      pullback.lift_snd _ _ _⟩⟩
  -- (A) the restriction of the degree-`r_a` part to `Z_a`
  have hA : bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sZ sX i hi
      (componentRank 𝒩.bundle a : ℤ) (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
      (completedBivariantSequenceOfInvertible C sZ sX i hi
        (completedVirtualNormalGysinClass C sZ sX i hi 𝒩) (componentRank 𝒩.bundle a)) a =
      BivariantClass.copy C (gysinSystemOfInvertible C) ((Z.connectedComponentOpens a).ι ≫ sZ)
        ((X.connectedComponentOpens (i.continuous.connectedComponentsMap a)).ι ≫ sX)
        (componentRestriction_comp_componentInclusion i a) _
        (i.resConnectedComponent_comp_ι_comp hi a) (by simp)
        (openImmersionComposite C ((Z.connectedComponentOpens a).ι ≫ sZ)
          ((componentNeighbourhood i a).ι ≫ sX)
          ((X.connectedComponentOpens (i.continuous.connectedComponentsMap a)).ι ≫ sX)
          (componentRestriction i a) (componentInclusion i a)
          (componentRestriction_comp_structureMorphism C sZ sX i hi a)
          (by rw [← Category.assoc, Scheme.homOfLE_ι]) (componentRank 𝒩.bundle a : ℤ)
          (virtualNormalBundleClass C ((Z.connectedComponentOpens a).ι ≫ sZ)
            ((componentNeighbourhood i a).ι ≫ sX) (componentRestriction i a)
            (componentRestriction_comp_structureMorphism C sZ sX i hi a) (𝒩.toComponent i a)
            (componentRank 𝒩.bundle a))) := by
    rw [restriction_completedVirtualNormalGysinClass, completedVirtualNormalGysinClass_apply,
      DirectSum.of_eq_same]
  -- (B) the cap operation of that restriction at `t ≫ (U_a ⟶ X_b)`
  have hs : (t ≫ componentInclusion i a) ≫
      (X.connectedComponentOpens (i.continuous.connectedComponentsMap a)).ι =
      t ≫ (componentNeighbourhood i a).ι := by
    rw [Category.assoc, Scheme.homOfLE_ι]
  have hβ : t ≫ (componentNeighbourhood i a).ι ≫ sX = (t ≫ componentInclusion i a) ≫
      (X.connectedComponentOpens (i.continuous.connectedComponentsMap a)).ι ≫ sX := by
    rw [Category.assoc, ← Category.assoc (componentInclusion i a), Scheme.homOfLE_ι]
  have hwfst : ((openRestrictionPullbackIso (i.resConnectedComponent a) (componentRestriction i a)
        (componentInclusion i a) (componentRestriction_comp_componentInclusion i a) t).inv ≫
        (componentTestIso i a t _ rfl).hom) ≫ pullback.fst i (t ≫ (componentNeighbourhood i a).ι) =
      pullback.fst (i.resConnectedComponent a) (t ≫ componentInclusion i a) ≫
        (Z.connectedComponentOpens a).ι := by
    rw [Category.assoc, componentTestIso_hom_fst, ← Category.assoc,
      ← openRestrictionPullbackIso_hom_fst (i.resConnectedComponent a) (componentRestriction i a)
        (componentInclusion i a) (componentRestriction_comp_componentInclusion i a) t,
      Iso.inv_hom_id_assoc]
  have hwsnd : ((openRestrictionPullbackIso (i.resConnectedComponent a) (componentRestriction i a)
        (componentInclusion i a) (componentRestriction_comp_componentInclusion i a) t).inv ≫
        (componentTestIso i a t _ rfl).hom) ≫ pullback.snd i (t ≫ (componentNeighbourhood i a).ι) =
      pullback.snd (i.resConnectedComponent a) (t ≫ componentInclusion i a) := by
    rw [Category.assoc, componentTestIso_hom_snd,
      ← openRestrictionPullbackIso_hom_snd (i.resConnectedComponent a) (componentRestriction i a)
        (componentInclusion i a) (componentRestriction_comp_componentInclusion i a) t,
      Iso.inv_hom_id_assoc]
  have hB : (bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sZ sX i hi
      (componentRank 𝒩.bundle a : ℤ) (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
      (completedBivariantSequenceOfInvertible C sZ sX i hi
        (completedVirtualNormalGysinClass C sZ sX i hi 𝒩) (componentRank 𝒩.bundle a)) a).cap
        (t ≫ componentInclusion i a) k (chowGroupCongr C hβ k β) =
      chowGroupRestrict C (pullback.fst i (t ≫ (componentNeighbourhood i a).ι) ≫ sZ)
        (pullback.fst (i.resConnectedComponent a) (t ≫ componentInclusion i a) ≫
          ((Z.connectedComponentOpens a).ι ≫ sZ))
        ((openRestrictionPullbackIso (i.resConnectedComponent a) (componentRestriction i a)
          (componentInclusion i a) (componentRestriction_comp_componentInclusion i a) t).inv ≫
          (componentTestIso i a t _ rfl).hom)
        (by rw [← Category.assoc, hwfst, Category.assoc]) (k - (componentRank 𝒩.bundle a : ℤ))
        ((completedBivariantSequenceOfInvertible C sZ sX i hi
            (completedVirtualNormalGysinClass C sZ sX i hi 𝒩) (componentRank 𝒩.bundle a)).cap
          (t ≫ (componentNeighbourhood i a).ι) k
          (chowGroupCongr C (Category.assoc _ _ _).symm k β)) := by
    have : @IsOpenImmersion (pullback (pieceMap i Z.connectedComponentOpens
        X.connectedComponentOpens i.continuous.connectedComponentsMap
        i.connectedComponentOpens_le_preimage a) (t ≫ componentInclusion i a))
        (pullback i (t ≫ (componentNeighbourhood i a).ι))
        ((openRestrictionPullbackIso (i.resConnectedComponent a)
        (componentRestriction i a) (componentInclusion i a)
        (componentRestriction_comp_componentInclusion i a) t).inv ≫
        (componentTestIso i a t _ rfl).hom) :=
      @IsOpenImmersion.of_isIso _ _ _ (Iso.isIso_hom ((openRestrictionPullbackIso
        (i.resConnectedComponent a) (componentRestriction i a) (componentInclusion i a)
        (componentRestriction_comp_componentInclusion i a) t).symm ≪≫
        componentTestIso i a t _ rfl))
    have hB0 := bivariantPieceRestrictionCap_eq C (gysinSystemOfInvertible C) sZ sX i hi
      (componentRank 𝒩.bundle a : ℤ) Z.connectedComponentOpens X.connectedComponentOpens
      i.continuous.connectedComponentsMap i.connectedComponentOpens_le_preimage a
      (completedBivariantSequenceOfInvertible C sZ sX i hi
        (completedVirtualNormalGysinClass C sZ sX i hi 𝒩) (componentRank 𝒩.bundle a))
      (t ≫ componentInclusion i a) (t ≫ (componentNeighbourhood i a).ι) hs
      (by rw [← hβ, Category.assoc])
      ((openRestrictionPullbackIso (i.resConnectedComponent a) (componentRestriction i a)
          (componentInclusion i a) (componentRestriction_comp_componentInclusion i a) t).inv ≫
        (componentTestIso i a t _ rfl).hom) hwfst hwsnd k
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ sZ) hwfst).trans
        (Category.assoc _ _ _))) (chowGroupCongr C hβ k β)
    rw [chowGroupCongr_chowGroupCongr] at hB0
    exact hB0
  rw [hA, copy_openImmersionComposite_cap] at hB
  -- (D) the cap operation of `c(Z_a ⟶ U_a, 𝒩|_{Z_a})` at `U_a ×_{X_b} T ⟶ U_a`
  have hD := BivariantClass.cap_chowGroupRestrict C (gysinSystemOfInvertible C)
    ((Z.connectedComponentOpens a).ι ≫ sZ) ((componentNeighbourhood i a).ι ≫ sX)
    (componentRestriction i a) (componentRestriction_comp_structureMorphism C sZ sX i hi a)
    (componentRank 𝒩.bundle a : ℤ)
    (virtualNormalBundleClass C ((Z.connectedComponentOpens a).ι ≫ sZ)
      ((componentNeighbourhood i a).ι ≫ sX) (componentRestriction i a)
      (componentRestriction_comp_structureMorphism C sZ sX i hi a) (𝒩.toComponent i a)
      (componentRank 𝒩.bundle a)) t
    (pullback.snd (componentInclusion i a) (t ≫ componentInclusion i a))
    (pullback.fst (componentInclusion i a) (t ≫ componentInclusion i a)) hσ
    (testBaseChangeIso (componentRestriction i a) t _ _ hσ).hom
    (isPullback_baseChangeMapOfEq (componentRestriction i a) t _ _ hσ)
    (testBaseChangeIso_hom_fst _ _ _ _ _) k (by rw [← Category.assoc, hσ])
    (by rw [testBaseChangeIso_hom_fst_assoc]) β
  rw [chowGroupRestrict_chowGroupCongr, ← hD,
    ← chowGroupRestrict_comp C _ (pullback.fst (componentRestriction i a) t ≫
      ((Z.connectedComponentOpens a).ι ≫ sZ)) (componentTestIso i a t _ rfl).hom
      (by rw [componentTestIso_hom_fst_assoc]) _ _ _ (by
        rw [← Category.assoc, ← openRestrictionPullbackIso_hom_fst (i.resConnectedComponent a)
          (componentRestriction i a) (componentInclusion i a)
          (componentRestriction_comp_componentInclusion i a) t, Iso.inv_hom_id_assoc])] at hB
  case hv => rw [← Category.assoc, hσ]
  -- the identifications compose to the identity of `Z_a ×_{U_a} T`
  have hE : (openRestrictionPullbackIso (i.resConnectedComponent a) (componentRestriction i a)
      (componentInclusion i a) (componentRestriction_comp_componentInclusion i a) t).hom ≫
      ((pullbackRightPullbackFstIso (componentInclusion i a) (t ≫ componentInclusion i a)
        (componentRestriction i a)) ≪≫
        pullback.congrHom (componentRestriction_comp_componentInclusion i a) rfl).inv ≫
      (testBaseChangeIso (componentRestriction i a) t
        (pullback.snd (componentInclusion i a) (t ≫ componentInclusion i a))
        (pullback.fst (componentInclusion i a) (t ≫ componentInclusion i a)) hσ).hom = 𝟙 _ := by
    rw [← cancel_mono (testBaseChangeIso (componentRestriction i a) t _ _ hσ).inv,
      Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp,
      Iso.comp_inv_eq]
    apply pullback.hom_ext
    · rw [openRestrictionPullbackIso_hom_fst]
      simp [testBaseChangeIso]
    · rw [openRestrictionPullbackIso_hom_snd]
      simp [testBaseChangeIso]
  rw [chowPushforwardOfIso_hom_eq_chowGroupRestrict, chowGroupRestrict_comp] at hB
  have h2 := congrArg (chowGroupRestrict C _ (pullback.fst (componentRestriction i a) t ≫
    ((Z.connectedComponentOpens a).ι ≫ sZ)) (openRestrictionPullbackIso
      (i.resConnectedComponent a) (componentRestriction i a) (componentInclusion i a)
      (componentRestriction_comp_componentInclusion i a) t).hom
    (by rw [← Category.assoc, openRestrictionPullbackIso_hom_fst])
    (k - (componentRank 𝒩.bundle a : ℤ))) hB
  rw [chowGroupRestrict_comp, chowGroupRestrict_comp] at h2
  exact eq_of_heq (((chowGroupRestrict_heq_of_eq_id C _ (Iso.hom_inv_id _) _ _).symm.trans
    (heq_of_eq h2.symm)).trans (chowGroupRestrict_heq_of_eq_id C _ hE _ _))

/-- **Stacks 0FBK, the degree parts of `c(Z ⟶ X, 𝒩)` over the neighbourhood of a connected
component**, for a test morphism `t' : T ⟶ X` presented by an equality `t ≫ (U_a ⟶ X) = t'`. -/
theorem chowGroupRestrict_completedVirtualNormalGysinClass_cap_of_eq (m : ℕ)
    (hm : componentRank 𝒩.bundle a = m)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (𝒩.toComponent i a).bundle m]
    {T : Scheme.{u}} (t : T ⟶ componentNeighbourhood i a) [LocallyOfFiniteType t] (t' : T ⟶ X)
    [LocallyOfFiniteType t'] (ht : t ≫ (componentNeighbourhood i a).ι = t') (k : ℤ)
    (β : chowGroup C (t ≫ ((componentNeighbourhood i a).ι ≫ sX)) k) :
    chowGroupRestrict C (pullback.fst i t' ≫ sZ)
        (pullback.fst (componentRestriction i a) t ≫ ((Z.connectedComponentOpens a).ι ≫ sZ))
        (componentTestIso i a t t' ht).hom (by rw [componentTestIso_hom_fst_assoc])
        (k - (m : ℤ))
        ((completedBivariantSequenceOfInvertible C sZ sX i hi
            (completedVirtualNormalGysinClass C sZ sX i hi 𝒩) (m : ℤ)).cap t' k
          (chowGroupCongr C (by rw [← ht, Category.assoc]) k β)) =
      (virtualNormalBundleClass C ((Z.connectedComponentOpens a).ι ≫ sZ)
        ((componentNeighbourhood i a).ι ≫ sX) (componentRestriction i a)
        (componentRestriction_comp_structureMorphism C sZ sX i hi a) (𝒩.toComponent i a)
        m).cap t k β := by
  subst ht
  exact chowGroupRestrict_completedVirtualNormalGysinClass_cap C sZ sX i hi 𝒩 a m hm t k β

/-- **Stacks 0FBK, the degree parts of `c(Z ⟶ X, 𝒩)` other than the rank vanish on a connected
component**: on `Z_a` the completed class is concentrated in the degree of the rank of `𝒩`
there. -/
theorem bivariantConnectedComponentRestriction_completedVirtualNormalGysinClass_eq_zero (p : ℤ)
    (hp : p ≠ (componentRank 𝒩.bundle a : ℤ)) :
    bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sZ sX i hi p
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
      (completedBivariantSequenceOfInvertible C sZ sX i hi
        (completedVirtualNormalGysinClass C sZ sX i hi 𝒩) p) a = 0 := by
  rw [restriction_completedVirtualNormalGysinClass, completedVirtualNormalGysinClass_apply]
  exact DirectSum.of_eq_of_ne _ _ _ hp

end ComponentCap

/-! ### The pieces of a base change over the connected components -/

section Piece

variable {Z X Z' Y : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i] [LocallyConnectedSpace Z]
  [LocallyConnectedSpace X] {g : Y ⟶ X} {i' : Z' ⟶ Y} {g' : Z' ⟶ Z}
  (sq : IsPullback i' g' g i) (a : _root_.ConnectedComponents Z)

include sq in
/-- The open of `Z' = Z ×_X Y` over the connected component `Z_a` of `Z` is the preimage of the
open `g⁻¹(U_a)` of `Y`, since `i⁻¹(U_a) = Z_a`. -/
theorem preimage_preimage_componentNeighbourhood :
    i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a) = g' ⁻¹ᵁ Z.connectedComponentOpens a := by
  rw [← preimage_componentNeighbourhood i a, ← Scheme.Hom.comp_preimage,
    ← Scheme.Hom.comp_preimage, sq.w]

/-- The projection `Z'_a ⟶ Z_a` of the piece `Z'_a = i'⁻¹(g⁻¹(U_a))` of `Z' = Z ×_X Y` over the
connected component `Z_a`. -/
abbrev pieceProjection : (i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a) : Scheme.{u}) ⟶
    (Z.connectedComponentOpens a : Scheme.{u}) :=
  g'.resLE _ _ (preimage_preimage_componentNeighbourhood sq a).le

/-- **The piece of the cartesian square over a connected component is cartesian**: `Z'_a` is the
base change of the closed immersion `Z_a ⟶ U_a` along `g⁻¹(U_a) ⟶ U_a`. -/
theorem isPullback_pieceProjection :
    IsPullback (i' ∣_ (g ⁻¹ᵁ componentNeighbourhood i a)) (pieceProjection sq a)
      (g ∣_ componentNeighbourhood i a) (componentRestriction i a) := by
  have hs := (isPullback_morphismRestrict i' (g ⁻¹ᵁ componentNeighbourhood i a)).paste_vert sq
  rw [← Scheme.Hom.resLE_comp_ι g' (preimage_preimage_componentNeighbourhood sq a).le,
    ← morphismRestrict_ι g (componentNeighbourhood i a)] at hs
  refine hs.of_bot ?_ (isPullback_componentRestriction i a)
  rw [← cancel_mono (componentNeighbourhood i a).ι, Category.assoc, morphismRestrict_ι,
    Category.assoc, componentRestriction_ι, ← Category.assoc, morphismRestrict_ι,
    Category.assoc, sq.w, ← Category.assoc, ← Category.assoc, Scheme.Hom.resLE_comp_ι]

end Piece

/-! ### The inclusion of a piece -/

section PieceInclusion

variable (C : ChowSituation.{u}) {Z X Z' Y : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ)
  [IsLocallyNoetherian Z] [IsLocallyNoetherian X] (𝒩 : VirtualNormalBundle i)
  (g : Y ⟶ X) [LocallyOfFiniteType g] (i' : Z' ⟶ Y) [IsClosedImmersion i'] (g' : Z' ⟶ Z)
  (sq : IsPullback i' g' g i) (sZ' : Z' ⟶ C.S) [LocallyOfFiniteType sZ']
  (hi' : i' ≫ (g ≫ sX) = sZ') (a : _root_.ConnectedComponents Z)

omit [LocallyOfFiniteType g] [IsClosedImmersion i'] [LocallyOfFiniteType sZ'] in
include hi hi' in
/-- The inclusion of the piece `Z'_a` of `Z' = Z ×_X Y` into the chosen fibre product is a
morphism over the base. -/
theorem pieceInclusion_comp_structureMorphism :
    ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sq.flip.isoPullback.hom) ≫
        (pullback.fst i g ≫ sZ) =
      (i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sZ' := by
  rw [Category.assoc, isoPullback_hom_comp_structureMorphism C sZ sX sq hi sZ' hi']

end PieceInclusion

/-! ### Classes on the base change, piece by piece -/

section Pieces

variable (C : ChowSituation.{u}) {Z X Z' Y : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ)
  (𝒩 : VirtualNormalBundle i) (g : Y ⟶ X) [LocallyOfFiniteType g] (i' : Z' ⟶ Y)
  [IsClosedImmersion i'] (g' : Z' ⟶ Z) (sq : IsPullback i' g' g i) (sZ' : Z' ⟶ C.S)
  [LocallyOfFiniteType sZ'] (hi' : i' ≫ (g ≫ sX) = sZ')

omit [IsClosedImmersion i'] in
/-- **A class on `Z ×_X Y` is determined by its restrictions to the pieces over the connected
components of `Z`.** The pieces `Z'_a = i'⁻¹(g⁻¹(U_a))` of `Z' ≅ Z ×_X Y` are the preimages of the
connected components of `Z`, a decomposition into open and closed subschemes (Stacks 0FDZ). -/
theorem eq_of_chowGroupRestrict_piece_eq [IsLocallyNoetherian Z] [IsLocallyNoetherian X] {k : ℤ}
    {x y : chowGroup C (pullback.fst i g ≫ sZ) k}
    (h : ∀ a : _root_.ConnectedComponents Z,
      chowGroupRestrict C (pullback.fst i g ≫ sZ)
          ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sZ')
          ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sq.flip.isoPullback.hom)
          (pieceInclusion_comp_structureMorphism C sZ sX i hi g i' g' sq sZ' hi' a) k x =
        chowGroupRestrict C (pullback.fst i g ≫ sZ)
          ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sZ')
          ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sq.flip.isoPullback.hom)
          (pieceInclusion_comp_structureMorphism C sZ sX i hi g i' g' sq sZ' hi' a) k y) :
    x = y := by
  have hdec : IsClopenDecomposition fun a ↦ i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a) := by
    have h₀ := IsClopenDecomposition.preimage
      (Scheme.isClopenDecomposition_connectedComponentOpens Z) g'
    have hfam : (fun a ↦ i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)) =
        fun a ↦ g' ⁻¹ᵁ Z.connectedComponentOpens a :=
      funext fun a ↦ preimage_preimage_componentNeighbourhood sq a
    rw [hfam]
    exact h₀
  have hinv : ∀ z : chowGroup C (pullback.fst i g ≫ sZ) k,
      chowGroupRestrict C sZ' (pullback.fst i g ≫ sZ) sq.flip.isoPullback.inv
          (by rw [← isoPullback_hom_comp_structureMorphism C sZ sX sq hi sZ' hi',
            Iso.inv_hom_id_assoc]) k
        (chowGroupRestrict C (pullback.fst i g ≫ sZ) sZ' sq.flip.isoPullback.hom
          (isoPullback_hom_comp_structureMorphism C sZ sX sq hi sZ' hi') k z) = z := by
    intro z
    rw [chowGroupRestrict_comp]
    exact eq_of_heq (chowGroupRestrict_heq_of_eq_id C _ (Iso.inv_hom_id _) _ _)
  rw [← hinv x, ← hinv y]
  refine congrArg _ ((chowGroupClopenEquiv C sZ' hdec k
    (rationalEquivalenceDecomposes_of_isClopenDecomposition C sZ' hdec k)).injective
      (funext fun a ↦ ?_))
  rw [chowGroupClopenEquiv_apply, chowGroupClopenEquiv_apply,
    chowGroupClopenRestrict_eq_chowGroupRestrict, chowGroupClopenRestrict_eq_chowGroupRestrict,
    chowGroupRestrict_comp, chowGroupRestrict_comp]
  exact h a

/-- **The degree parts of `c(Z ⟶ X, 𝒩)` on a piece of a base change.** For a cartesian square
`Z' = Z ×_X Y` and a connected component `Z_a` of `Z` on which `𝒩` has rank `m`, the restriction
of `c(Z ⟶ X, 𝒩)_m ∩ α` to the piece `Z'_a = Z_a ×_{U_a} g⁻¹(U_a)` is
`c(Z_a ⟶ U_a, 𝒩|_{Z_a}) ∩ α|_{g⁻¹(U_a)}`, read through the identification of the piece with the
chosen fibre product: on the open `g⁻¹(U_a)` of `Y` the completed class is the class of the
component (`Stacks.Chow.chowGroupRestrict_completedVirtualNormalGysinClass_cap_of_eq`), and the
cap operation commutes with restricting the test scheme to an open
(`Stacks.Chow.BivariantClass.cap_chowGroupRestrict`). -/
theorem chowGroupRestrict_piece_completedVirtualNormalGysinClass_cap [IsLocallyNoetherian Z]
    [IsLocallyNoetherian X] (a : _root_.ConnectedComponents Z) (m : ℕ)
    (hm : componentRank 𝒩.bundle a = m)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (𝒩.toComponent i a).bundle m]
    (n : ℤ) (α : chowGroup C (g ≫ sX) n) :
    chowGroupRestrict C (pullback.fst i g ≫ sZ)
        ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sZ')
        ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sq.flip.isoPullback.hom)
        (pieceInclusion_comp_structureMorphism C sZ sX i hi g i' g' sq sZ' hi' a) (n - m)
        ((completedBivariantSequenceOfInvertible C sZ sX i hi
          (completedVirtualNormalGysinClass C sZ sX i hi 𝒩) (m : ℤ)).cap g n α) =
      chowGroupRestrict C
        (pullback.fst (componentRestriction i a) (g ∣_ componentNeighbourhood i a) ≫
          ((Z.connectedComponentOpens a).ι ≫ sZ))
        ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sZ')
        (isPullback_pieceProjection sq a).flip.isoPullback.hom
        (isoPullback_hom_comp_structureMorphism C ((Z.connectedComponentOpens a).ι ≫ sZ)
          ((componentNeighbourhood i a).ι ≫ sX) (isPullback_pieceProjection sq a)
          (componentRestriction_comp_structureMorphism C sZ sX i hi a)
          ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sZ')
          (by rw [← Category.assoc (g ∣_ _), morphismRestrict_ι, Category.assoc, ← Category.assoc,
            morphismRestrict_ι, Category.assoc, hi']))
        (n - m)
        ((virtualNormalBundleClass C ((Z.connectedComponentOpens a).ι ≫ sZ)
          ((componentNeighbourhood i a).ι ≫ sX) (componentRestriction i a)
          (componentRestriction_comp_structureMorphism C sZ sX i hi a) (𝒩.toComponent i a) m).cap
          (g ∣_ componentNeighbourhood i a) n
          (chowGroupRestrict C (g ≫ sX)
            ((g ∣_ componentNeighbourhood i a) ≫ ((componentNeighbourhood i a).ι ≫ sX))
            (g ⁻¹ᵁ componentNeighbourhood i a).ι
            (by rw [← Category.assoc (g ∣_ _), morphismRestrict_ι, Category.assoc]) n α)) := by
  have hgU : (g ∣_ componentNeighbourhood i a) ≫ (componentNeighbourhood i a).ι =
      (g ⁻¹ᵁ componentNeighbourhood i a).ι ≫ g := morphismRestrict_ι g _
  have hi'a : (i' ∣_ (g ⁻¹ᵁ componentNeighbourhood i a)) ≫ ((g ∣_ componentNeighbourhood i a) ≫
      ((componentNeighbourhood i a).ι ≫ sX)) =
      (i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sZ' := by
    rw [← Category.assoc (g ∣_ _), hgU, Category.assoc, ← Category.assoc, morphismRestrict_ι,
      Category.assoc, hi']
  -- the class on the open `g⁻¹(U_a)` of `Y`
  have hC := chowGroupRestrict_completedVirtualNormalGysinClass_cap_of_eq C sZ sX i hi 𝒩 a
    m hm (g ∣_ componentNeighbourhood i a) ((g ⁻¹ᵁ componentNeighbourhood i a).ι ≫ g) hgU n
    (chowGroupRestrict C (g ≫ sX)
      ((g ∣_ componentNeighbourhood i a) ≫ ((componentNeighbourhood i a).ι ≫ sX))
      (g ⁻¹ᵁ componentNeighbourhood i a).ι
      (by rw [← Category.assoc (g ∣_ _), morphismRestrict_ι, Category.assoc]) n α)
  -- restricting the test scheme to `g⁻¹(U_a)`
  have : IsOpenImmersion (baseChangeMapOfEq i g (g ⁻¹ᵁ componentNeighbourhood i a).ι
      ((g ⁻¹ᵁ componentNeighbourhood i a).ι ≫ g) rfl) :=
    MorphismProperty.of_isPullback (isPullback_baseChangeMapOfEq i g _ _ rfl)
      (P := @IsOpenImmersion) inferInstance
  have h1 := BivariantClass.cap_chowGroupRestrict C (gysinSystemOfInvertible C) sZ sX i hi _
    (completedBivariantSequenceOfInvertible C sZ sX i hi
      (completedVirtualNormalGysinClass C sZ sX i hi 𝒩) (m : ℤ)) g
    (g ⁻¹ᵁ componentNeighbourhood i a).ι ((g ⁻¹ᵁ componentNeighbourhood i a).ι ≫ g) rfl
    (baseChangeMapOfEq i g (g ⁻¹ᵁ componentNeighbourhood i a).ι _ rfl)
    (isPullback_baseChangeMapOfEq i g _ _ rfl) (baseChangeMapOfEq_fst _ _ _ _ _) n
    (Category.assoc _ _ _).symm (baseChangeMapOfEq_comp_structure sZ i g _ _ rfl) α
  have hres : chowGroupRestrict C (g ≫ sX) (((g ⁻¹ᵁ componentNeighbourhood i a).ι ≫ g) ≫ sX)
      (g ⁻¹ᵁ componentNeighbourhood i a).ι (Category.assoc _ _ _).symm n α =
      chowGroupCongr C (by rw [← Category.assoc (g ∣_ _), hgU]) n
        (chowGroupRestrict C (g ≫ sX)
          ((g ∣_ componentNeighbourhood i a) ≫ ((componentNeighbourhood i a).ι ≫ sX))
          (g ⁻¹ᵁ componentNeighbourhood i a).ι
          (by rw [← Category.assoc (g ∣_ _), morphismRestrict_ι, Category.assoc]) n α) :=
    (chowGroupCongr_chowGroupRestrict C _ _ _ _ _ _ _ n α).symm
  rw [hres] at h1
  -- the inclusion of the piece factors through `Z ×_X g⁻¹(U_a)`
  have hw : (isPullback_pieceProjection sq a).flip.isoPullback.hom ≫
      (componentTestIso i a (g ∣_ componentNeighbourhood i a)
        ((g ⁻¹ᵁ componentNeighbourhood i a).ι ≫ g) hgU).hom ≫
      baseChangeMapOfEq i g (g ⁻¹ᵁ componentNeighbourhood i a).ι _ rfl =
      (i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sq.flip.isoPullback.hom := by
    apply pullback.hom_ext
    · simp
    · simp [morphismRestrict_ι]
  have hθ := isoPullback_hom_comp_structureMorphism C ((Z.connectedComponentOpens a).ι ≫ sZ)
    ((componentNeighbourhood i a).ι ≫ sX) (isPullback_pieceProjection sq a)
    (componentRestriction_comp_structureMorphism C sZ sX i hi a)
    ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sZ') hi'a
  have hEv : ((componentTestIso i a (g ∣_ componentNeighbourhood i a)
        ((g ⁻¹ᵁ componentNeighbourhood i a).ι ≫ g) hgU).hom ≫
      baseChangeMapOfEq i g (g ⁻¹ᵁ componentNeighbourhood i a).ι _ rfl) ≫
        (pullback.fst i g ≫ sZ) =
      pullback.fst (componentRestriction i a) (g ∣_ componentNeighbourhood i a) ≫
        ((Z.connectedComponentOpens a).ι ≫ sZ) := by
    rw [Category.assoc, baseChangeMapOfEq_comp_structure, componentTestIso_hom_fst_assoc]
  rw [← chowGroupRestrict_congr C (pullback.fst i g ≫ sZ)
      ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sZ') _
      (by rw [hw]; exact pieceInclusion_comp_structureMorphism C sZ sX i hi g i' g' sq sZ' hi' a)
      _ _ hw,
    ← chowGroupRestrict_comp C (pullback.fst i g ≫ sZ) _ _ hEv _ _ _ hθ,
    ← chowGroupRestrict_comp C (pullback.fst i g ≫ sZ) _ _
      (baseChangeMapOfEq_comp_structure sZ i g _ _ rfl) _ _ _
      (by rw [componentTestIso_hom_fst_assoc]),
    h1, hC]

omit [IsClosedImmersion i'] in
/-- **The left-hand side of the excess intersection formula vanishes on a piece in degrees
other than the rank of `𝒩` there**: the piece lies over the connected component `Z_a`, on which
the completed class is concentrated in that degree. -/
theorem chowGroupRestrict_completedVirtualNormalGysinCap_piece_eq_zero [IsLocallyNoetherian Z]
    [IsLocallyNoetherian X] (a : _root_.ConnectedComponents Z) (p : ℤ)
    (hp : p ≠ (componentRank 𝒩.bundle a : ℤ)) (n : ℤ) (α : chowGroup C (g ≫ sX) n) :
    chowGroupRestrict C (pullback.fst i g ≫ sZ)
        ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sZ')
        ((i' ⁻¹ᵁ (g ⁻¹ᵁ componentNeighbourhood i a)).ι ≫ sq.flip.isoPullback.hom)
        (pieceInclusion_comp_structureMorphism C sZ sX i hi g i' g' sq sZ' hi' a) (n - p)
        ((completedBivariantSequenceOfInvertible C sZ sX i hi
          (completedVirtualNormalGysinClass C sZ sX i hi 𝒩) p).cap g n α) = 0 :=
  chowGroupRestrict_cap_eq_zero_of_connectedComponentRestriction_eq_zero C
    (gysinSystemOfInvertible C) sZ sX i hi p
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) _ a
    (bivariantConnectedComponentRestriction_completedVirtualNormalGysinClass_eq_zero C sZ sX i hi
      𝒩 a p hp) g n α _ _ _ (pieceProjection sq a)
    (by rw [Scheme.Hom.resLE_comp_ι, Category.assoc, IsPullback.isoPullback_hom_fst])

end Pieces

/-! ### The top Chern class restricted to an open subscheme -/

section TopChern

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (U : X.Opens)

/-- The restriction of the cap product with the degree `e` top Chern class to an open subscheme
is the operation of that Chern class on the open. -/
private theorem chowGroupRestrict_topChernCap_eq_idRule (e : ℕ) (k : ℤ) (α : chowGroup C sX k) :
    chowGroupRestrict C sX (U.ι ≫ sX) U.ι rfl (k - e) (topChernCap C sX E k e α) =
      (topChernTotalClass C sX E e).idRule C sX (gysinSystemOfInvertible C) U.ι k
        (chowGroupRestrict C sX (U.ι ≫ sX) U.ι rfl k α) := by
  rw [topChernCap, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.coe_toAddMonoidHom, chowGroupRestrict_chowGroupCongr C (𝟙 X ≫ sX) sX (U.ι ≫ sX) U.ι
      (by rw [Category.id_comp]) rfl (Category.id_comp sX),
    BivariantClass.idRule_chowGroupRestrict (topChernTotalClass C sX E e) (𝟙 X) U.ι U.ι
      (Category.comp_id _),
    chowGroupRestrict_chowGroupCongr]

/-- **The cap product with the top Chern class, restricted to an open subscheme on which the
module has rank `e`**, is the cap product with the `e`-th Chern class of Stacks 0B7H of the
restricted module: `c_top(E) ∩ α` restricts to `c_e(E|_U) ∩ α|_U` (Stacks 0B76 (2) for the
degree-`e` part of `c_top(E)`, with `Stacks.Chow.idRule_topChernTotalClass_self`). -/
theorem chowGroupRestrict_topChernCap (e : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} ((Scheme.Modules.pullback U.ι).obj E) e]
    (k : ℤ) (α : chowGroup C sX k) :
    chowGroupRestrict C sX (U.ι ≫ sX) U.ι rfl (k - e) (topChernCap C sX E k e α) =
      GenuineChern.chernCap C e (U.ι ≫ sX) ((Scheme.Modules.pullback U.ι).obj E) k (Fin.last e)
        (chowGroupRestrict C sX (U.ι ≫ sX) U.ι rfl k α) := by
  rw [chowGroupRestrict_topChernCap_eq_idRule,
    idRule_topChernTotalClass_self C sX E e U.ι
      (mem_rankLocus_of_isFiniteLocallyFreeOfRank_pullback E U.ι e inferInstance)]

/-- **The cap product with the top Chern class in a degree other than the rank vanishes on an
open subscheme of constant rank.** -/
theorem chowGroupRestrict_topChernCap_of_ne (s e : ℕ) (hs : U ≤ rankLocus E s) (he : e ≠ s)
    (k : ℤ) (α : chowGroup C sX k) :
    chowGroupRestrict C sX (U.ι ≫ sX) U.ι rfl (k - e) (topChernCap C sX E k e α) = 0 := by
  rw [chowGroupRestrict_topChernCap_eq_idRule,
    idRule_topChernTotalClass_of_ne C sX E s e he U.ι (fun t ↦ hs t.2)]

end TopChern

/-! ### The top Chern class of isomorphic modules -/

section TopChernCongr

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  [IsLocallyNoetherian X]

/-- **Isomorphic modules have the same top Chern class cap products** (Stacks 0FA4). On a
connected component of `X` both modules have the same constant rank `s`, and there the cap
product with the degree-`e` part of `c_top` is `c_s ∩ -` if `e = s` and zero otherwise; for
isomorphic modules of constant rank these agree (`Stacks.Chow.GenuineChern.chernCap_congr`). A
Chow class is determined by its restrictions to the connected components (Stacks 0FDZ). -/
theorem topChernCap_congr {E E' : X.Modules} [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E'] (φ : E ≅ E') (k : ℤ) (e : ℕ)
    (α : chowGroup C sX k) : topChernCap C sX E k e α = topChernCap C sX E' k e α := by
  have hdec := Scheme.isClopenDecomposition_connectedComponentOpens X
  apply (chowGroupClopenEquiv C sX hdec (k - e)
    (rationalEquivalenceDecomposes_of_isClopenDecomposition C sX hdec (k - e))).injective
  funext a
  rw [chowGroupClopenEquiv_apply, chowGroupClopenEquiv_apply,
    chowGroupClopenRestrict_eq_chowGroupRestrict, chowGroupClopenRestrict_eq_chowGroupRestrict]
  have := isFiniteLocallyFreeOfRank_componentRank E a
  have φa := (Scheme.Modules.pullback (X.connectedComponentOpens a).ι).mapIso φ
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (X.connectedComponentOpens a).ι).obj E') (componentRank E a) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} φa inferInstance
  obtain ⟨x, hx⟩ := _root_.ConnectedComponents.surjective_coe a
  have hxa : x ∈ X.connectedComponentOpens a := (Scheme.mem_connectedComponentOpens X).2 hx
  by_cases he : e = componentRank E a
  · subst he
    rw [chowGroupRestrict_topChernCap C sX E _ (componentRank E a) k α,
      chowGroupRestrict_topChernCap C sX E' _ (componentRank E a) k α]
    exact GenuineChern.chernCap_congr C _ _ φa _ _ _
  · rw [chowGroupRestrict_topChernCap_of_ne C sX E _ (componentRank E a) e
        (fun y hy ↦ mem_rankLocus_of_isFiniteLocallyFreeOfRank_pullback E
          (X.connectedComponentOpens a).ι _ inferInstance ⟨y, hy⟩) he k α,
      chowGroupRestrict_topChernCap_of_ne C sX E' _ (componentRank E a) e
        (fun y hy ↦ mem_rankLocus_of_isFiniteLocallyFreeOfRank_pullback E'
          (X.connectedComponentOpens a).ι _ inferInstance ⟨y, hy⟩) he k α]

end TopChernCongr

end Stacks.Chow

end
