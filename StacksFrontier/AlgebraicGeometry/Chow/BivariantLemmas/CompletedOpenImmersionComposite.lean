module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.OpenImmersionComposite
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.Completion

/-!
# Composing a completed bivariant class with flat pullback along an open immersion

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `j : U ⟶ X` be an open
immersion and `i : Z ⟶ U` a morphism of schemes locally of finite type over `S`. A completed
bivariant class `c ∈ A^*(Z ⟶ U)^∧` (Stacks 0FE0) composes with the flat-pullback class
`j^* ∈ A^0(U ⟶ X)` of Stacks 0B78, viewed in `A^*(U ⟶ X)^∧`, to `c ∘ j^* ∈ A^*(Z ⟶ X)^∧`. This is
the definition of Stacks 0FBQ (3) for a virtual normal bundle whose rank need not be constant,
`c(Z ⟶ X, 𝒩) = c(Z ⟶ U, 𝒩) ∘ (U ⟶ X)^*`.

The independence of the choice of `U` is proved here at this level, from its homogeneous form
`Stacks.Chow.openImmersionComposite_heq_of_isOpenRestriction`, connected component by connected
component of `Z`.

## Main definitions

* `Stacks.Chow.completedFlatPullbackOfIsOpenImmersion` — `j^* ∈ A^*(U ⟶ X)^∧`.
* `Stacks.Chow.completedOpenImmersionComposite` — `c ∘ j^* ∈ A^*(Z ⟶ X)^∧`, the composition of
  Stacks 0FE0.
* `Stacks.Chow.IsCompletedOpenRestriction` — on every connected component of `Z` and in every
  degree, `c_V` is the restriction of `c_U` in the sense of `Stacks.Chow.IsOpenRestriction`.

## Main results

* `Stacks.Chow.completedOpenImmersionComposite_heq_of_isCompletedOpenRestriction` — shrinking `U`
  to an open `V` through which `i` factors, and `c_U` to its restriction `c_V`, does not change
  `c ∘ j^*`.

## References

* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace Stacks.Chow

/-! ### Graded bookkeeping -/

/-- Evaluating the convolution of a bilinear pairing at a homogeneous right argument: the degree
`n` part of `x ⋆ y` for `y` of degree `q` is `m (n - q) q (x_{n-q}) y`, up to the identification
`n - q + q = n` of degrees. -/
theorem directSumBilinear_of_apply_heq {A B D : ℤ → Type v} [∀ p, AddCommGroup (A p)]
    [∀ q, AddCommGroup (B q)] [∀ n, AddCommGroup (D n)] (m : ∀ p q, A p →+ B q →+ D (p + q))
    (x : DirectSum ℤ A) (q : ℤ) (y : B q) (n : ℤ) :
    directSumBilinear m x (DirectSum.of B q y) n ≍ m (n - q) q (x (n - q)) y := by
  have key : ∀ (n' : ℤ) (h : n' = n - q + q),
      directSumBilinear m x (DirectSum.of B q y) n' ≍ m (n - q) q (x (n - q)) y := by
    intro n' h
    subst h
    induction x using DirectSum.induction_on with
    | zero => simp
    | of p a =>
      rw [directSumBilinear_of_of]
      by_cases hp : p = n - q
      · subst hp
        rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
      · have hne : p + q ≠ n - q + q := fun h ↦ hp (by omega)
        rw [DirectSum.of_eq_of_ne (p + q) (n - q + q) _ (Ne.symm hne),
          DirectSum.of_eq_of_ne p (n - q) a (Ne.symm hp),
          map_zero, AddMonoidHom.zero_apply]
    | add x₁ x₂ h₁ h₂ =>
      rw [map_add, AddMonoidHom.add_apply, DirectSum.add_apply, DirectSum.add_apply, map_add,
        AddMonoidHom.add_apply]
      exact heq_of_eq (congrArg₂ (· + ·) (eq_of_heq h₁) (eq_of_heq h₂))
  have := key n (by omega)
  exact this

/-- Restriction of Chow classes along an open immersion depends on its degree and its argument
only up to equality and heterogeneous equality. -/
theorem chowGroupRestrict_heq_of_heq (C : ChowSituation.{u}) {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (v : B ⟶ A)
    [IsOpenImmersion v] (hv : v ≫ sA = sB) {k k' : ℤ} (hk : k = k') (x : chowGroup C sA k)
    (y : chowGroup C sA k') (hxy : x ≍ y) :
    chowGroupRestrict C sA sB v hv k x ≍ chowGroupRestrict C sA sB v hv k' y := by
  subst hk
  obtain rfl := eq_of_heq hxy
  rfl

/-! ### The flat-pullback class of an open immersion on connected components -/

section Components

variable (C : ChowSituation.{u}) {U X : Scheme.{u}} (sU : U ⟶ C.S) [LocallyOfFiniteType sU]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (j : U ⟶ X) [IsOpenImmersion j] (hj : j ≫ sX = sU)
  [IsLocallyNoetherian U] [IsLocallyNoetherian X]

/-- The restriction `U_a ⟶ X_b` of an open immersion `j : U ⟶ X` to a connected component `U_a`
of `U` and the connected component `X_b` of `X` containing its image is an open immersion. -/
instance isOpenImmersion_resConnectedComponent (a : _root_.ConnectedComponents U) :
    IsOpenImmersion (j.resConnectedComponent a) := by
  have : IsOpenImmersion (j.resConnectedComponent a ≫
      (X.connectedComponentOpens (j.continuous.connectedComponentsMap a)).ι) := by
    rw [Scheme.Hom.resConnectedComponent_comp_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _
    (X.connectedComponentOpens (j.continuous.connectedComponentsMap a)).ι

/-- **The restriction of `j^*` to a connected component is `j^*` of the restricted open
immersion.** Restricting the flat-pullback class of an open immersion `j : U ⟶ X` to a connected
component `U_a` of `U` (Stacks 0FDZ) gives the flat-pullback class of `U_a ⟶ X_{b}`: both cap by
restricting a class on a test scheme to an open subscheme of it, and the two open subschemes are
the same. -/
theorem bivariantConnectedComponentRestriction_flatPullbackBivariantClassOfIsOpenImmersion
    (a : _root_.ConnectedComponents U) :
    bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sU sX j hj _
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (flatPullbackBivariantClassOfIsOpenImmersionOfInvertible C sU sX j hj) a =
      flatPullbackBivariantClassOfIsOpenImmersionOfInvertible C
        ((U.connectedComponentOpens a).ι ≫ sU)
        ((X.connectedComponentOpens (j.continuous.connectedComponentsMap a)).ι ≫ sX)
        (j.resConnectedComponent a) (j.resConnectedComponent_comp_ι_comp hj a) := by
  refine BivariantClass.ext C _ _ _ _ _ _ fun {T} g _ k β ↦ ?_
  change bivariantPieceRestrictionCap C _ sU sX j hj _ _ _ _ _ a _ g k β = _
  rw [bivariantPieceRestrictionCap_apply]
  have : LocallyOfFiniteType (pullback.fst (j.resConnectedComponent a) g) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (j.resConnectedComponent a) g).flip
      (P := @LocallyOfFiniteType) ‹_›
  refine eq_of_heq (HEq.trans ?_ (flatPullbackBivariantCap_heq_chowGroupRestrict C _ _
    (j.resConnectedComponent a) (j.resConnectedComponent_comp_ι_comp hj a) g k β).symm)
  refine (chowGroupRestrict_heq_of_heq C _ _ _ _ (hk := by simp) _ _
    (flatPullbackBivariantCap_heq_chowGroupRestrict C sU sX j hj _ k _)).trans ?_
  rw [chowGroupRestrict_comp, chowGroupRestrict_chowGroupCongr]
  · refine heq_of_eq ?_
    simp only [opensPullbackComparison_snd]
    rfl
  · rw [opensPullbackComparison_snd]
    exact pullbackSnd_comp_structureMorphism (j.resConnectedComponent_comp_ι_comp hj a) g

/-- **`j^* ∈ A^*(U ⟶ X)^∧`.** The flat-pullback class of an open immersion (Stacks 0B78), viewed in
the completed bivariant group of Stacks 0FE0: on each connected component of `U` it is the
restriction of `j^*`, placed in degree `0`. -/
def completedFlatPullbackOfIsOpenImmersion :
    completedBivariantGroup C (gysinSystemOfInvertible C) sU sX j hj :=
  fun a ↦ DirectSum.of _ (-((0 : ℕ) : ℤ))
    (bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sU sX j hj _
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
      (flatPullbackBivariantClassOfIsOpenImmersionOfInvertible C sU sX j hj) a)

/-- On a connected component of `U`, the completed class `j^*` is the flat-pullback class of the
restricted open immersion, placed in degree `0`. -/
theorem completedFlatPullbackOfIsOpenImmersion_apply (a : _root_.ConnectedComponents U) :
    completedFlatPullbackOfIsOpenImmersion C sU sX j hj a =
      DirectSum.of _ (-((0 : ℕ) : ℤ))
        (flatPullbackBivariantClassOfIsOpenImmersionOfInvertible C
          ((U.connectedComponentOpens a).ι ≫ sU)
          ((X.connectedComponentOpens (j.continuous.connectedComponentsMap a)).ι ≫ sX)
          (j.resConnectedComponent a) (j.resConnectedComponent_comp_ι_comp hj a)) := by
  rw [completedFlatPullbackOfIsOpenImmersion,
    bivariantConnectedComponentRestriction_flatPullbackBivariantClassOfIsOpenImmersion]

end Components

/-! ### The composite `c ∘ j^*` on completions -/

section Composite

variable (C : ChowSituation.{u}) {Z U X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i : Z ⟶ U) [LocallyOfFiniteType i] (j : U ⟶ X) [IsOpenImmersion j]
  (hi : i ≫ sU = sZ) (hj : j ≫ sX = sU)
  [IsLocallyNoetherian Z] [IsLocallyNoetherian U] [IsLocallyNoetherian X]

/-- **The composite `c ∘ j^*` of a completed class with flat pullback along an open
immersion**, for the composition of completed bivariant classes of Stacks 0FE0. -/
def completedOpenImmersionComposite
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sZ sU i hi) :
    completedBivariantGroup C (gysinSystemOfInvertible C) sZ sX (i ≫ j)
      (comp_comp_structureMorphism_eq hi hj) :=
  completedBivariantCompositeOfInvertible C sZ sU sX i j hi hj c
    (completedFlatPullbackOfIsOpenImmersion C sU sX j hj)

omit [IsLocallyNoetherian Z] [IsLocallyNoetherian U] [IsLocallyNoetherian X] in
/-- The transport of `Stacks.Chow.bivariantClassComponentCongr` changes nothing. -/
theorem bivariantClassComponentCongr_heq {G : GysinSystem C} {W Y : Scheme.{u}} (sW : W ⟶ C.S)
    [LocallyOfFiniteType sW] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [LocallyConnectedSpace Y]
    {j₁ j₂ : _root_.ConnectedComponents Y} (hj : j₁ = j₂)
    (u₁ : W ⟶ (Y.connectedComponentOpens j₁ : Scheme.{u})) [LocallyOfFiniteType u₁]
    (u₂ : W ⟶ (Y.connectedComponentOpens j₂ : Scheme.{u})) [LocallyOfFiniteType u₂]
    (hu : u₁ ≍ u₂) (h₁ : u₁ ≫ ((Y.connectedComponentOpens j₁).ι ≫ sY) = sW)
    (h₂ : u₂ ≫ ((Y.connectedComponentOpens j₂).ι ≫ sY) = sW) (n : ℤ)
    (x : BivariantClass C G sW ((Y.connectedComponentOpens j₁).ι ≫ sY) u₁ h₁ n) :
    bivariantClassComponentCongr C G sW sY hj u₁ u₂ hu h₁ h₂ n x ≍ x := by
  subst hj
  obtain rfl := eq_of_heq hu
  rfl

/-- **The composite on a connected component.** On the connected component `Z_z` of `Z`, in
degree `n`, the completed composite `c ∘ j^*` is the composite (Stacks 0B75) of the degree
`n - (-0)` part of `c` on `Z_z` with the flat-pullback class of the open immersion
`U_a ⟶ X_b` of the connected components `Z_z` lands in. -/
theorem completedOpenImmersionComposite_apply_heq
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sZ sU i hi)
    (z : _root_.ConnectedComponents Z) (n : ℤ) :
    completedOpenImmersionComposite C sZ sU sX i j hi hj c z n ≍
      openImmersionComposite C ((Z.connectedComponentOpens z).ι ≫ sZ)
        ((U.connectedComponentOpens (i.continuous.connectedComponentsMap z)).ι ≫ sU)
        ((X.connectedComponentOpens (j.continuous.connectedComponentsMap
          (i.continuous.connectedComponentsMap z))).ι ≫ sX)
        (i.resConnectedComponent z)
        (j.resConnectedComponent (i.continuous.connectedComponentsMap z))
        (i.resConnectedComponent_comp_ι_comp hi z)
        (j.resConnectedComponent_comp_ι_comp hj (i.continuous.connectedComponentsMap z))
        (n - -((0 : ℕ) : ℤ)) (c z (n - -((0 : ℕ) : ℤ))) := by
  rw [completedOpenImmersionComposite, completedBivariantCompositeOfInvertible,
    completedBivariantComposite_apply, DFinsupp.mapRange.addEquiv_apply, DFinsupp.mapRange_apply,
    completedFlatPullbackOfIsOpenImmersion_apply]
  refine (bivariantClassComponentCongr_heq C _ _ _ _ _ _ _ _ n _).trans ?_
  exact directSumBilinear_of_apply_heq _ _ _ _ n

end Composite

/-! ### Shrinking the open subscheme, on completions -/

section Shrink

variable (C : ChowSituation.{u}) {Z U V X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (sV : V ⟶ C.S) [LocallyOfFiniteType sV]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i : Z ⟶ U) [LocallyOfFiniteType i] (iV : Z ⟶ V) [LocallyOfFiniteType iV]
  (j : U ⟶ X) [IsOpenImmersion j] (jV : V ⟶ X) [IsOpenImmersion jV]
  (ι : V ⟶ U) [IsOpenImmersion ι]
  (hi : i ≫ sU = sZ) (hiV : iV ≫ sV = sZ) (hj : j ≫ sX = sU) (hjV : jV ≫ sX = sV)
  (hι : ι ≫ sU = sV) (hιi : iV ≫ ι = i) (hιj : ι ≫ j = jV)
  [IsLocallyNoetherian Z] [IsLocallyNoetherian U] [IsLocallyNoetherian V] [IsLocallyNoetherian X]

omit [LocallyOfFiniteType i] [LocallyOfFiniteType iV] [IsOpenImmersion ι] [IsLocallyNoetherian Z] in
include hιi in
/-- The connected component of `V` that a connected component `Z_z` of `Z` lands in is carried by
`ι` into the connected component of `U` that `Z_z` lands in. -/
theorem connectedComponentOpens_le_preimage_of_comp_eq (z : _root_.ConnectedComponents Z) :
    V.connectedComponentOpens (iV.continuous.connectedComponentsMap z) ≤
      ι ⁻¹ᵁ U.connectedComponentOpens (i.continuous.connectedComponentsMap z) := by
  have e : ι.continuous.connectedComponentsMap (iV.continuous.connectedComponentsMap z) =
      i.continuous.connectedComponentsMap z := by
    rw [← Scheme.Hom.connectedComponentsMap_comp, hιi]
  exact e ▸ ι.connectedComponentOpens_le_preimage _

/-- The open immersion `V_{a'} ⟶ U_a` of the connected components of `V` and of `U` that a
connected component `Z_z` of `Z` lands in, induced by `ι : V ⟶ U`. -/
abbrev componentShrinkMap (z : _root_.ConnectedComponents Z) :
    (V.connectedComponentOpens (iV.continuous.connectedComponentsMap z) : Scheme.{u}) ⟶
      (U.connectedComponentOpens (i.continuous.connectedComponentsMap z) : Scheme.{u}) :=
  ι.resLE _ _ (connectedComponentOpens_le_preimage_of_comp_eq i iV ι hιi z)

/-- The morphism `Stacks.Chow.componentShrinkMap` of connected components is an open immersion. -/
instance isOpenImmersion_componentShrinkMap (z : _root_.ConnectedComponents Z) :
    IsOpenImmersion (componentShrinkMap i iV ι hιi z) := by
  have : IsOpenImmersion (componentShrinkMap i iV ι hιi z ≫
      (U.connectedComponentOpens (i.continuous.connectedComponentsMap z)).ι) := by
    rw [Scheme.Hom.resLE_comp_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _ (U.connectedComponentOpens _).ι

omit [LocallyOfFiniteType sU] [LocallyOfFiniteType sV] [LocallyOfFiniteType i]
  [LocallyOfFiniteType iV] [IsOpenImmersion ι] [IsLocallyNoetherian Z] in
include hι in
/-- The open immersion `V_{a'} ⟶ U_a` of connected components commutes with the structure
morphisms of `V_{a'}` and `U_a` to `S`. -/
theorem componentShrinkMap_comp_structureMorphism (z : _root_.ConnectedComponents Z) :
    componentShrinkMap i iV ι hιi z ≫
        ((U.connectedComponentOpens (i.continuous.connectedComponentsMap z)).ι ≫ sU) =
      (V.connectedComponentOpens (iV.continuous.connectedComponentsMap z)).ι ≫ sV := by
  rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hι]

omit [LocallyOfFiniteType i] [LocallyOfFiniteType iV] [IsOpenImmersion ι] in
/-- On a connected component `Z_z` of `Z`, the restriction `Z_z ⟶ V_{a'}` of `iV` followed by the
open immersion `V_{a'} ⟶ U_a` is the restriction `Z_z ⟶ U_a` of `i`. -/
theorem resConnectedComponent_comp_componentShrinkMap (z : _root_.ConnectedComponents Z) :
    iV.resConnectedComponent z ≫ componentShrinkMap i iV ι hιi z = i.resConnectedComponent z := by
  rw [← cancel_mono (U.connectedComponentOpens (i.continuous.connectedComponentsMap z)).ι,
    Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resConnectedComponent_comp_ι_assoc,
    hιi, Scheme.Hom.resConnectedComponent_comp_ι]

/-- **`c_V` is the restriction of `c_U` on completions.** On every connected component `Z_z` of
`Z` and in every degree `p`, the part of `c_V` on `Z_z ⟶ V_{a'}` is the restriction, in the sense
of `Stacks.Chow.IsOpenRestriction`, of the part of `c_U` on `Z_z ⟶ U_a` along the open immersion
`Stacks.Chow.componentShrinkMap` of the two connected components. -/
def IsCompletedOpenRestriction
    (cU : completedBivariantGroup C (gysinSystemOfInvertible C) sZ sU i hi)
    (cV : completedBivariantGroup C (gysinSystemOfInvertible C) sZ sV iV hiV) : Prop :=
  ∀ (z : _root_.ConnectedComponents Z) (p : ℤ),
    IsOpenRestriction C ((Z.connectedComponentOpens z).ι ≫ sZ)
      ((U.connectedComponentOpens (i.continuous.connectedComponentsMap z)).ι ≫ sU)
      ((V.connectedComponentOpens (iV.continuous.connectedComponentsMap z)).ι ≫ sV)
      (i.resConnectedComponent z) (iV.resConnectedComponent z) (componentShrinkMap i iV ι hιi z)
      (i.resConnectedComponent_comp_ι_comp hi z) (iV.resConnectedComponent_comp_ι_comp hiV z)
      (componentShrinkMap_comp_structureMorphism C sU sV i iV ι hι hιi z)
      (resConnectedComponent_comp_componentShrinkMap i iV ι hιi z) p (cU z p) (cV z p)

/-- **Completed classes for equal morphisms.** Two completed classes for equal morphisms
`f = f'` are the same class as soon as their components agree, up to the transport of degrees
and of target connected components. -/
theorem completedBivariantGroup_heq_of_apply_heq {G : GysinSystem C} {W Y : Scheme.{u}}
    {sW : W ⟶ C.S} [LocallyOfFiniteType sW] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
    [IsLocallyNoetherian W] [IsLocallyNoetherian Y]
    {f f' : W ⟶ Y} [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (hff : f = f')
    {hf : f ≫ sY = sW} {hf' : f' ≫ sY = sW}
    (c : completedBivariantGroup C G sW sY f hf) (c' : completedBivariantGroup C G sW sY f' hf')
    (h : ∀ (w : _root_.ConnectedComponents W) (n : ℤ), c w n ≍ c' w n) :
    c ≍ c' := by
  subst hff
  exact heq_of_eq (funext fun w ↦ DirectSum.ext fun n ↦ eq_of_heq (h w n))

/-- `c ∘ u^*` for an open immersion `u` into a connected component of `Y` depends on the
component only through the composite of `u` with its inclusion. -/
theorem openImmersionComposite_heq_of_component {W V' Y : Scheme.{u}} (sW : W ⟶ C.S)
    [LocallyOfFiniteType sW] (sV' : V' ⟶ C.S) [LocallyOfFiniteType sV'] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] [LocallyConnectedSpace Y] (w : W ⟶ V') [LocallyOfFiniteType w]
    (hw : w ≫ sV' = sW) {b b' : _root_.ConnectedComponents Y} (hb : b = b')
    (u : V' ⟶ (Y.connectedComponentOpens b : Scheme.{u})) [IsOpenImmersion u]
    (u' : V' ⟶ (Y.connectedComponentOpens b' : Scheme.{u})) [IsOpenImmersion u']
    (hu : u ≫ (Y.connectedComponentOpens b).ι = u' ≫ (Y.connectedComponentOpens b').ι)
    (hu₁ : u ≫ ((Y.connectedComponentOpens b).ι ≫ sY) = sV')
    (hu₂ : u' ≫ ((Y.connectedComponentOpens b').ι ≫ sY) = sV') (p : ℤ)
    (c : BivariantClass C (gysinSystemOfInvertible C) sW sV' w hw p) :
    openImmersionComposite C sW sV' ((Y.connectedComponentOpens b).ι ≫ sY) w u hw hu₁ p c ≍
      openImmersionComposite C sW sV' ((Y.connectedComponentOpens b').ι ≫ sY) w u' hw hu₂ p c := by
  subst hb
  obtain rfl : u = u' := (cancel_mono _).1 hu
  rfl

/-- **Shrinking `U` does not change `c ∘ (U ⟶ X)^*`, on completions.** If `ι : V ⟶ U` is an open
immersion through which `i` factors as `iV ≫ ι`, with `ι ≫ j = jV`, and `c_V` is the restriction
of `c_U` on every connected component of `Z` and in every degree, then `c_U ∘ j^* = c_V ∘ jV^*`
in `A^*(Z ⟶ X)^∧`. This is `Stacks.Chow.openImmersionComposite_heq_of_isOpenRestriction` on each
connected component `Z_z`, for the connected components of `U`, `V` and `X` that `Z_z` lands
in. -/
theorem completedOpenImmersionComposite_heq_of_isCompletedOpenRestriction (hιj : ι ≫ j = jV)
    (cU : completedBivariantGroup C (gysinSystemOfInvertible C) sZ sU i hi)
    (cV : completedBivariantGroup C (gysinSystemOfInvertible C) sZ sV iV hiV)
    (H : IsCompletedOpenRestriction C sZ sU sV i iV ι hi hiV hι hιi cU cV) :
    completedOpenImmersionComposite C sZ sU sX i j hi hj cU ≍
      completedOpenImmersionComposite C sZ sV sX iV jV hiV hjV cV := by
  have hcomp : i ≫ j = iV ≫ jV := by rw [← hιi, ← hιj, Category.assoc]
  refine completedBivariantGroup_heq_of_apply_heq C hcomp _ _ fun z n ↦ ?_
  refine (completedOpenImmersionComposite_apply_heq C sZ sU sX i j hi hj cU z n).trans ?_
  refine HEq.trans ?_
    (completedOpenImmersionComposite_apply_heq C sZ sV sX iV jV hiV hjV cV z n).symm
  have hb : j.continuous.connectedComponentsMap (i.continuous.connectedComponentsMap z) =
      jV.continuous.connectedComponentsMap (iV.continuous.connectedComponentsMap z) := by
    rw [← Scheme.Hom.connectedComponentsMap_comp, ← Scheme.Hom.connectedComponentsMap_comp,
      hcomp]
  set a := i.continuous.connectedComponentsMap z
  set a' := iV.continuous.connectedComponentsMap z
  have hsj : componentShrinkMap i iV ι hιi z ≫ j.resConnectedComponent a ≫
      ((X.connectedComponentOpens (j.continuous.connectedComponentsMap a)).ι ≫ sX) =
      (V.connectedComponentOpens a').ι ≫ sV := by
    rw [j.resConnectedComponent_comp_ι_comp hj a,
      componentShrinkMap_comp_structureMorphism C sU sV i iV ι hι hιi z]
  refine (openImmersionComposite_heq_of_isOpenRestriction C _ _ _ _ _ _
    (j.resConnectedComponent a) (componentShrinkMap i iV ι hιi z ≫ j.resConnectedComponent a)
    (componentShrinkMap i iV ι hιi z) _ _ _ hsj
    (componentShrinkMap_comp_structureMorphism C sU sV i iV ι hι hιi z)
    (resConnectedComponent_comp_componentShrinkMap i iV ι hιi z) _ rfl _ _ (H z _)).trans ?_
  refine openImmersionComposite_heq_of_component C _ _ sX _ _ hb _ _ ?_ _ _ _ _
  rw [Category.assoc, Scheme.Hom.resConnectedComponent_comp_ι, Scheme.Hom.resLE_comp_ι_assoc,
    hιj, Scheme.Hom.resConnectedComponent_comp_ι]

/-- Completed bivariant classes for two equal morphisms `f = f'` are the same group. -/
def completedBivariantGroup.copy {G : GysinSystem C} {W Y : Scheme.{u}} {sW : W ⟶ C.S}
    [LocallyOfFiniteType sW] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f f' : W ⟶ Y}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (hff : f = f') (hf : f ≫ sY = sW)
    (hf' : f' ≫ sY = sW) (c : completedBivariantGroup C G sW sY f hf) :
    completedBivariantGroup C G sW sY f' hf' := by
  subst hff
  exact c

/-- The transport of `Stacks.Chow.completedBivariantGroup.copy` changes nothing. -/
theorem completedBivariantGroup.copy_heq {G : GysinSystem C} {W Y : Scheme.{u}} {sW : W ⟶ C.S}
    [LocallyOfFiniteType sW] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f f' : W ⟶ Y}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (hff : f = f') (hf : f ≫ sY = sW)
    (hf' : f' ≫ sY = sW) (c : completedBivariantGroup C G sW sY f hf) :
    completedBivariantGroup.copy C hff hf hf' c ≍ c := by
  subst hff
  rfl

end Shrink

end Stacks.Chow

end
