module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SmoothRelativeDimensionShift
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedAssociativity

/-!
# The unit of the completed bivariant cohomology ring

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `X` be a scheme
locally of finite type over `S`, with connected components `X = ∐_{i ∈ I} X_i`. The completed
bivariant cohomology ring `A^*(X)^∧ = ∏_i A^*(X_i)` of Stacks 0FE0 has a unit: the class `1`
whose component on every `X_i` is the unit `1 ∈ A^0(X_i)` of the bivariant classes of the
identity of `X_i` (the class of Stacks 0B76 acting as the identity on every test scheme).

This file constructs that unit and proves that it is a two-sided unit for the composition of
completed bivariant classes: for every morphism `f : X ⟶ Y` locally of finite type over `S` and
every `c ∈ A^*(X ⟶ Y)^∧`,

  `c ∘ 1_Y = c` and `1_X ∘ c = c` in `A^*(X ⟶ Y)^∧`.

## Main definitions

* `Stacks.Chow.completedIdentityClass` — the unit `1 ∈ A^*(X)^∧`.

## Main results

* `Stacks.Chow.bivariantCompositeOfInvertible_bivariantIdentityClassOfInvertible` and
  `Stacks.Chow.bivariantIdentityClassOfInvertible_bivariantCompositeOfInvertible` — the unit laws
  `c ∘ 1 = c` and `1 ∘ c = c` for the composition of Stacks 0B75.
* `Stacks.Chow.bivariantConnectedComponentRestriction_bivariantIdentityClassOfInvertible_heq` —
  the restriction of `1 ∈ A^0(Y)` to a connected component `Y_j` (Stacks 0FDZ) is
  `1 ∈ A^0(Y_j)`.
* `Stacks.Chow.completedBivariantCompositeOfInvertible_completedIdentityClass` and
  `Stacks.Chow.completedIdentityClass_completedBivariantCompositeOfInvertible` — the unit laws on
  the completions.

## Implementation notes

The composites `f ≫ 𝟙 Y` and `𝟙 X ≫ f` are equal to `f` but are not the same term, and the
degrees `p + 0` and `0 + p` are equal to `p` but are not the same term, so the unit laws are
heterogeneous equalities. On the completions the component of `Y` that a component `X_i` lands in
under `𝟙 Y` is equal, and not identical, to the one it lands in under `f`; the restriction of `1`
to a component is therefore compared with the unit of that component up to the same
identification, by `Stacks.Chow.bivariantPieceRestriction_bivariantIdentityClassOfInvertible_heq`.

## References

* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme.Hom

/-- The identity of a locally connected scheme induces the identity on its connected
components. -/
theorem connectedComponentsMap_id (X : Scheme.{u}) [LocallyConnectedSpace X] :
    (𝟙 X : X ⟶ X).continuous.connectedComponentsMap = id := by
  funext i
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe i
  exact (𝟙 X : X ⟶ X).continuous.connectedComponentsMap_mk x

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.Chow

/-! ### Convolution with a homogeneous left argument -/

/-- Evaluating the convolution of a bilinear pairing at a homogeneous left argument: the degree
`n` part of `x ⋆ y` for `x` of degree `p` is `m p (n - p) x (y_{n-p})`, up to the identification
`p + (n - p) = n` of degrees. -/
theorem directSumBilinear_of_left_apply_heq {A B D : ℤ → Type v} [∀ p, AddCommGroup (A p)]
    [∀ q, AddCommGroup (B q)] [∀ n, AddCommGroup (D n)] (m : ∀ p q, A p →+ B q →+ D (p + q))
    (p : ℤ) (x : A p) (y : DirectSum ℤ B) (n : ℤ) :
    directSumBilinear m (DirectSum.of A p x) y n ≍ m p (n - p) x (y (n - p)) := by
  have key : ∀ (n' : ℤ) (h : n' = p + (n - p)),
      directSumBilinear m (DirectSum.of A p x) y n' ≍ m p (n - p) x (y (n - p)) := by
    intro n' h
    subst h
    induction y using DirectSum.induction_on with
    | zero => simp
    | of q b =>
      rw [directSumBilinear_of_of]
      by_cases hq : q = n - p
      · subst hq
        rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
      · have hne : p + q ≠ p + (n - p) := fun h ↦ hq (by omega)
        rw [DirectSum.of_eq_of_ne (p + q) (p + (n - p)) _ (Ne.symm hne),
          DirectSum.of_eq_of_ne q (n - p) b (Ne.symm hq), map_zero]
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add, DirectSum.add_apply, DirectSum.add_apply, map_add]
      exact heq_of_eq (congrArg₂ (· + ·) (eq_of_heq h₁) (eq_of_heq h₂))
  exact key n (by omega)

/-! ### The unit laws for homogeneous classes -/

section Homogeneous

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX) (p : ℤ)

/-- **The cap operation of `1`.** Capping with `1 ∈ A^0(Y)` on a test scheme `t : T ⟶ Y` is
pushforward along the canonical isomorphism `T ≅ Y ×_Y T`, up to the transport of the degree
from `k` to `k - 0`. -/
theorem bivariantIdentityClassOfInvertible_cap_heq {T : Scheme.{u}} (t : T ⟶ Y)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sY) k) :
    (bivariantIdentityClassOfInvertible C sY).cap t k α ≍
      chowPushforwardOfIso C (t ≫ sY) (pullback.fst (𝟙 Y) t ≫ sY) (identityBaseChangeIso t).inv
        (identityBaseChangeIso_hom_comp C sY t) k α :=
  (heq_of_eq (identityCapRule_transport_apply C sY t k α)).trans
    (chowGroup_cast_heq _ (sub_zero k).symm _)

/-- The inverse of the identity base change isomorphism is a section of the first projection. -/
theorem identityBaseChangeIso_inv_fst {T : Scheme.{u}} (t : T ⟶ Y) :
    (identityBaseChangeIso t).inv ≫ pullback.fst (𝟙 Y) t = t := by
  rw [fst_eq_identityBaseChangeIso_hom, Iso.inv_hom_id_assoc]

/-- If capping with `a` after `b` is, up to a degree shift, the pushforward along an isomorphism
`u` of a class `x`, then the cap of the composite `a ∘ b` is the pushforward of `x` along `u`
followed by the associativity isomorphism, and pushing it further along `w` gives back `x` as soon
as the total isomorphism `u ≫ (X ×_Y Y ×_Z T ≅ X ×_Z T) ≫ w` is the identity. -/
private theorem bivariantCompositeOfInvertible_cap_pushforward_heq (C : ChowSituation.{u})
    {X Y Z T A : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] {f : X ⟶ Y}
    [LocallyOfFiniteType f] {g : Y ⟶ Z} [LocallyOfFiniteType g] {hf : f ≫ sY = sX}
    {hg : g ≫ sZ = sY} {p q : ℤ}
    (a : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p)
    (b : BivariantClass C (gysinSystemOfInvertible C) sY sZ g hg q) (t : T ⟶ Z)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sZ) k) {sA : A ⟶ C.S}
    [LocallyOfFiniteType sA] (u : A ⟶ pullback f (pullback.fst g t)) [IsIso u]
    (hu : u ≫ (pullback.fst f (pullback.fst g t) ≫ sX) = sA) (w : pullback (f ≫ g) t ⟶ A)
    [IsIso w] (hw : w ≫ sA = pullback.fst (f ≫ g) t ≫ sX)
    (huw : (u ≫ (pullbackRightPullbackFstIso g t f).hom) ≫ w = 𝟙 A) {m : ℤ} (x : chowGroup C sA m)
    (hm : k - q - p = m)
    (hc : a.cap (pullback.fst g t) (k - q) (b.cap t k α) ≍
      chowPushforwardOfIso C sA _ u hu m x) :
    chowPushforwardOfIso C (pullback.fst (f ≫ g) t ≫ sX) sA w hw (k - (p + q))
      ((bivariantCompositeOfInvertible C sX sY sZ f g hf hg p q a b).cap t k α) ≍ x := by
  subst hm
  have hL : ((bivariantCompositeOfInvertible C sX sY sZ f g hf hg p q a b).cap t k α) ≍
      chowPushforwardOfIso C sA (pullback.fst (f ≫ g) t ≫ sX)
        (u ≫ (pullbackRightPullbackFstIso g t f).hom) (by simp [← hu]) (k - q - p) x := by
    rw [bivariantCompositeOfInvertible, bivariantComposite_cap]
    refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
    rw [bivariantCompositeCap_apply]
    exact chowPushforwardOfIso_heq_comp_of_comp_eq _ _ _ rfl _ _ rfl rfl (by omega) _ _ hc
  refine (chowPushforwardOfIso_heq_comp_of_comp_eq _ _ _ rfl _ _ rfl rfl (by omega) _ _ hL).trans ?_
  exact chowPushforwardOfIso_heq_of_eq_id _ huw _ _

/-- **Stacks 0B75, composition with `1` on the right.** For `c ∈ A^p(X ⟶ Y)`, the composite
`c ∘ 1 ∈ A^{p+0}(X ⟶ Y)` with the unit `1 ∈ A^0(Y)` is `c`. The composite is a class for
`f ≫ 𝟙 Y` of degree `p + 0`, whence the heterogeneous equality. -/
theorem bivariantCompositeOfInvertible_bivariantIdentityClassOfInvertible
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) :
    bivariantCompositeOfInvertible C sX sY sY f (𝟙 Y) hf (Category.id_comp sY) p 0 c
        (bivariantIdentityClassOfInvertible C sY) ≍ c := by
  refine BivariantClass.heq_of_congrHom_cap_heq (Category.comp_id f) (add_zero p) _ _ ?_
  intro T t _ k α
  have hc := BivariantClass.cap_heq_chowPushforwardOfIso c (pullback.fst (𝟙 Y) t)
    (identityBaseChangeIso t).inv t (identityBaseChangeIso_inv_fst t) (sub_zero k).symm α
    ((bivariantIdentityClassOfInvertible C sY).cap t k α)
    (identityBaseChangeIso_hom_comp C sY t)
    (bivariantIdentityClassOfInvertible_cap_heq C sY t k α) α HEq.rfl
  refine bivariantCompositeOfInvertible_cap_pushforward_heq C c _ t k α _ _ _ _ ?_
    (c.cap t k α) (by omega) hc
  exact pullback.hom_ext (by simp) (by simp)

/-- **Stacks 0B75, composition with `1` on the left.** For `c ∈ A^p(X ⟶ Y)`, the composite
`1 ∘ c ∈ A^{0+p}(X ⟶ Y)` with the unit `1 ∈ A^0(X)` is `c`. The composite is a class for
`𝟙 X ≫ f` of degree `0 + p`, whence the heterogeneous equality. -/
theorem bivariantIdentityClassOfInvertible_bivariantCompositeOfInvertible
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) :
    bivariantCompositeOfInvertible C sX sX sY (𝟙 X) f (Category.id_comp sX) hf 0 p
        (bivariantIdentityClassOfInvertible C sX) c ≍ c := by
  refine BivariantClass.heq_of_congrHom_cap_heq (Category.id_comp f) (zero_add p) _ _ ?_
  intro T t _ k α
  refine bivariantCompositeOfInvertible_cap_pushforward_heq C _ _ t k α _ _ _ _ ?_
    (c.cap t k α) (by omega)
    (bivariantIdentityClassOfInvertible_cap_heq C sX (pullback.fst f t) (k - p) _)
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_fst,
      pullbackRightPullbackFstIso_hom_fst_assoc, Category.id_comp]
    exact identityBaseChangeIso_inv_fst (pullback.fst f t)
  · simp

end Homogeneous

/-! ### The restriction of `1` to a connected component -/

section Restriction

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- **The restriction of `1` to a piece is `1`.** Let `Y = ∐_j Y_j` be a decomposition into open
pieces and restrict `1 ∈ A^0(Y)` along the decomposition of the identity of `Y` which sends each
piece to itself (Stacks 0FDZ). Then on every piece the restriction is `1 ∈ A^0(Y_j)`. The index
map of the decomposition is equal, and not identical, to the identity, whence the heterogeneous
equality. -/
theorem bivariantPieceRestriction_bivariantIdentityClassOfInvertible_heq {J : Type u}
    (U : J → Y.Opens) (a : J → J) (ha' : a = id) (ha : ∀ j, U j ≤ (𝟙 Y) ⁻¹ᵁ U (a j)) (j : J) :
    bivariantPieceRestriction C (gysinSystemOfInvertible C) sY sY (𝟙 Y) (Category.id_comp sY) 0
        U U a ha j (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (bivariantIdentityClassOfInvertible C sY) ≍
      bivariantIdentityClassOfInvertible C ((U j).ι ≫ sY) := by
  subst ha'
  have hpm : pieceMap (𝟙 Y) U U id ha j = 𝟙 (U j : Scheme.{u}) := by
    rw [← cancel_mono (U j).ι]
    exact (pieceMap_comp_ι (𝟙 Y) U U id ha j).trans (by simp)
  refine BivariantClass.heq_of_cap_eq hpm _ _ fun {T} t _ k β ↦ ?_
  have : IsIso (pieceMap (𝟙 Y) U U id ha j) := by rw [hpm]; infer_instance
  have hsnd : pieceComparison (𝟙 Y) U U id ha j t ≫ pullback.snd (𝟙 Y) (t ≫ (U j).ι) =
      pullback.snd (pieceMap (𝟙 Y) U U id ha j) t :=
    opensPullbackComparison_snd _ _ _ _ _ _
  have : IsIso (pieceComparison (𝟙 Y) U U id ha j t ≫
      pullback.snd (𝟙 Y) (t ≫ (U j).ι)) := by rw [hsnd]; infer_instance
  have : IsIso (pieceComparison (𝟙 Y) U U id ha j t) :=
    IsIso.of_isIso_comp_right _ (pullback.snd (𝟙 Y) (t ≫ (U j).ι))
  refine eq_of_heq (HEq.trans ?_ (bivariantIdentityClassOfInvertible_cap_heq C _ t k β).symm)
  rw [bivariantPieceRestriction_cap, bivariantPieceRestrictionCap_apply,
    chowGroupRestrict_of_isIso]
  have h1 := bivariantIdentityClassOfInvertible_cap_heq C sY (t ≫ (U j).ι) k
    (chowGroupCongr C (Category.assoc t (U j).ι sY).symm k β)
  refine (chowPushforwardOfIso_heq_comp_of_comp_eq _ _ _ rfl _ _ rfl rfl (sub_zero k).symm _ _
    ((chowPushforwardOfIso_heq_comp_of_comp_eq _ _ _ rfl _ _ rfl rfl (sub_zero k).symm _ _
      h1))).trans ?_
  refine (heq_of_eq (chowPushforwardOfIso_congr_apply C _ _ _ (identityBaseChangeIso t).inv ?_ _
    ((identityBaseChangeIso_hom_comp C _ t).trans (Category.assoc _ _ _).symm) k _)).trans
    (chowPushforwardOfIso_heq _ _ _ (Category.assoc t (U j).ι sY) rfl rfl
      (chowGroupCongr_heq C _ k β))
  rw [← cancel_mono (pullback.snd (𝟙 (U j : Scheme.{u})) t)]
  have e1 : (pullback.congrHom hpm rfl).hom ≫ pullback.snd (𝟙 (U j : Scheme.{u})) t =
      pullback.snd (pieceMap (𝟙 Y) U U id ha j) t := by simp
  have e2 : inv (pieceComparison (𝟙 Y) U U id ha j t) ≫
      pullback.snd (pieceMap (𝟙 Y) U U id ha j) t = pullback.snd (𝟙 Y) (t ≫ (U j).ι) := by
    rw [IsIso.inv_comp_eq, hsnd]
  rw [Category.assoc, Category.assoc, e1, e2]
  exact ((identityBaseChangeIso _).inv_hom_id).trans ((identityBaseChangeIso t).inv_hom_id).symm

/-- **The restriction of `1` to a connected component is `1`.** Restricting
`1 ∈ A^0(Y)` to the connected component `Y_j` of `Y` (Stacks 0FDZ) gives `1 ∈ A^0(Y_j)`. The
restriction is a class for `(𝟙 Y).resConnectedComponent j : Y_j ⟶ Y_{j'}`, where the index
`j'` of the component `Y_j` lands in under `𝟙 Y` is equal, and not identical, to `j`; whence the
heterogeneous equality. -/
theorem bivariantConnectedComponentRestriction_bivariantIdentityClassOfInvertible_heq
    [IsLocallyNoetherian Y] (j : _root_.ConnectedComponents Y) :
    bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sY sY (𝟙 Y)
        (Category.id_comp sY) 0 (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (bivariantIdentityClassOfInvertible C sY) j ≍
      bivariantIdentityClassOfInvertible C ((Y.connectedComponentOpens j).ι ≫ sY) :=
  bivariantPieceRestriction_bivariantIdentityClassOfInvertible_heq C sY Y.connectedComponentOpens
    _ (Scheme.Hom.connectedComponentsMap_id Y) _ j

end Restriction

/-! ### The unit of `A^*(X)^∧` -/

section Completed

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  [IsLocallyNoetherian X]

/-- The unit `1 ∈ A^*(X)^∧` of the completed bivariant cohomology ring: on the connected
component `X_i` of `X` it is the restriction of `1 ∈ A^0(X)` to `X_i`, placed in degree `0`. By
`Stacks.Chow.completedIdentityClass_apply_heq` that restriction is `1 ∈ A^0(X_i)`. -/
@[stacks 0FE0 "the unit 1 of the completed bivariant cohomology ring A^*(X)^∧"]
def completedIdentityClass : completedChowCohomology C (gysinSystemOfInvertible C) sX :=
  fun i ↦ DirectSum.of _ 0
    (bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sX (𝟙 X)
      (Category.id_comp sX) 0 (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
      (bivariantIdentityClassOfInvertible C sX) i)

/-- On the connected component `X_i`, the unit of `A^*(X)^∧` is the restriction of `1` to `X_i`,
placed in degree `0`. -/
theorem completedIdentityClass_apply (i : _root_.ConnectedComponents X) :
    completedIdentityClass C sX i =
      DirectSum.of _ 0
        (bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sX (𝟙 X)
          (Category.id_comp sX) 0 (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
          (bivariantIdentityClassOfInvertible C sX) i) :=
  rfl

/-- In degree `0` on the connected component `X_i`, the unit of `A^*(X)^∧` is the unit
`1 ∈ A^0(X_i)`. -/
theorem completedIdentityClass_apply_heq (i : _root_.ConnectedComponents X) :
    completedIdentityClass C sX i 0 ≍
      bivariantIdentityClassOfInvertible C ((X.connectedComponentOpens i).ι ≫ sX) := by
  rw [completedIdentityClass_apply, DirectSum.of_eq_same]
  exact bivariantConnectedComponentRestriction_bivariantIdentityClassOfInvertible_heq C sX i

/-- In every nonzero degree the unit of `A^*(X)^∧` vanishes. -/
theorem completedIdentityClass_apply_of_ne (i : _root_.ConnectedComponents X) {n : ℤ}
    (hn : n ≠ 0) : completedIdentityClass C sX i n = 0 := by
  rw [completedIdentityClass_apply, DirectSum.of_eq_of_ne _ _ _ hn]

end Completed

/-! ### The unit laws on completions -/

section CompletedUnitLaws

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- **Stacks 0FE0, composition with `1` on the right.** For a completed class
`c ∈ A^*(X ⟶ Y)^∧`, the composite `c ∘ 1` with the unit `1 ∈ A^*(Y)^∧` is `c`. The composite is a
completed class for `f ≫ 𝟙 Y`, whence the heterogeneous equality. -/
theorem completedBivariantCompositeOfInvertible_completedIdentityClass
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf) :
    completedBivariantCompositeOfInvertible C sX sY sY f (𝟙 Y) hf (Category.id_comp sY) c
        (completedIdentityClass C sY) ≍ c := by
  refine completedBivariantGroup_heq_of_apply_heq C (Category.comp_id f) _ _ fun i n ↦ ?_
  rw [completedBivariantCompositeOfInvertible, completedBivariantComposite_apply,
    DFinsupp.mapRange.addEquiv_apply, DFinsupp.mapRange_apply, completedIdentityClass_apply]
  refine (bivariantClassComponentCongr_heq C _ _ _ _ _ _ _ _ n _).trans ?_
  refine (directSumBilinear_of_apply_heq _ _ _ _ n).trans ?_
  rw [bivariantCompositeBilinear_apply]
  set a := f.continuous.connectedComponentsMap i
  have ha : (𝟙 Y : Y ⟶ Y).continuous.connectedComponentsMap a = a :=
    congrFun (Scheme.Hom.connectedComponentsMap_id Y) a
  refine (bivariantCompositeOfInvertible_heq_of_target_component C (sW := sY) (hj := ha)
    (ψ₂ := 𝟙 _) (hψ := Scheme.Hom.heq_of_comp_connectedComponentOpens_ι ha _ _ (by
      rw [Scheme.Hom.resConnectedComponent_comp_ι, Category.comp_id, Category.id_comp]))
    (hψ₂ := Category.id_comp _)
    (hb := bivariantConnectedComponentRestriction_bivariantIdentityClassOfInvertible_heq C sY
      a) (a := c i (n - 0))).trans ?_
  refine (bivariantCompositeOfInvertible_bivariantIdentityClassOfInvertible C _ _ _ _ _ _).trans ?_
  exact congr_arg_heq (c i) (sub_zero n)

/-- **Stacks 0FE0, composition with `1` on the left.** For a completed class
`c ∈ A^*(X ⟶ Y)^∧`, the composite `1 ∘ c` with the unit `1 ∈ A^*(X)^∧` is `c`. The composite is a
completed class for `𝟙 X ≫ f`, whence the heterogeneous equality. -/
theorem completedIdentityClass_completedBivariantCompositeOfInvertible
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf) :
    completedBivariantCompositeOfInvertible C sX sX sY (𝟙 X) f (Category.id_comp sX) hf
        (completedIdentityClass C sX) c ≍ c := by
  refine completedBivariantGroup_heq_of_apply_heq C (Category.id_comp f) _ _ fun i n ↦ ?_
  rw [completedBivariantCompositeOfInvertible, completedBivariantComposite_apply,
    DFinsupp.mapRange.addEquiv_apply, DFinsupp.mapRange_apply, completedIdentityClass_apply]
  refine (bivariantClassComponentCongr_heq C _ _ _ _ _ _ _ _ n _).trans ?_
  refine (directSumBilinear_of_left_apply_heq _ _ _ _ n).trans ?_
  rw [bivariantCompositeBilinear_apply]
  have hi : (𝟙 X : X ⟶ X).continuous.connectedComponentsMap i = i :=
    congrFun (Scheme.Hom.connectedComponentsMap_id X) i
  refine (bivariantCompositeOfInvertible_heq_of_source_component C _ sX sY f hf hi _
    (𝟙 _) (Scheme.Hom.heq_of_comp_connectedComponentOpens_ι hi _ _ (by
      rw [Scheme.Hom.resConnectedComponent_comp_ι, Category.comp_id, Category.id_comp])) _
    (Category.id_comp _) _ _ _ _
    (bivariantConnectedComponentRestriction_bivariantIdentityClassOfInvertible_heq C sX i) _ _
    (congr_arg_heq (fun j ↦ c j (n - 0)) hi)).trans ?_
  refine (bivariantIdentityClassOfInvertible_bivariantCompositeOfInvertible C _ _ _ _ _ _).trans ?_
  exact congr_arg_heq (c i) (sub_zero n)

end CompletedUnitLaws

end Stacks.Chow

end
