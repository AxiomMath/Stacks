module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalCapCohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.OpenImmersionComposite
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDimension
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedRestrictionFlatCommute
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedSmoothPullback
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleImmersionClass
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SmoothAscent
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalClassCharacterized

/-!
# The cap product with a fundamental class over Cohen–Macaulay test schemes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let
`c ∈ A^p(Z ⟶ X)` be a bivariant class for a morphism of schemes locally of finite type over `S`.
Stacks 0FEA shows that the class `c(Z ⟶ X, 𝒩)` of a virtual normal sheaf of rank `r` for a closed
immersion satisfies

  `c ∩ [T]_n = [Z ×_X T]_{n - p}`

for every `T ⟶ X` all of whose irreducible components have `δ`-dimension `n`, such that
`dim_δ(Z ×_X T) ≤ n - p` and `𝒪_{T, ξ}` is Cohen–Macaulay at the points `ξ` of `Z ×_X T` of
`δ`-dimension `n - p`. This file records that formula as a property of a class of arbitrary
integer degree (`Stacks.Chow.BivariantClass.CapFundamentalFormula`), and proves that it is
inherited by the composite `c ∘ g^*` with the flat pullback of a smooth morphism `g` of relative
dimension `d` (Stacks 0B78), in degree `n` from degree `n + d`. This is the computation in the
proof of Stacks 0FF7: `g^*[T] = [P ×_Y T]` (Stacks 02RB), the local rings of `P ×_Y T` at the
relevant points are Cohen–Macaulay because `P ×_Y T ⟶ T` is flat with regular fibres, and the
formula for `c` concludes.

## Main definitions

* `Stacks.Chow.BivariantClass.CapFundamentalFormula` — the formula
  `c ∩ [T]_n = [Z ×_X T]_{n - p}` over Cohen–Macaulay test schemes.
* `Stacks.Chow.completedBivariantGroup.HasCapFundamentalFormula` — a completed class (Stacks 0FE0)
  concentrated on each connected component in a single degree, where it satisfies the formula in
  every degree.

## Main results

* `Stacks.Chow.virtualNormalGysinClass_capFundamentalFormula` — Stacks 0FEA in this form.
* `Stacks.Chow.BivariantClass.capFundamentalFormula_bivariantCompositeOfInvertible` — the formula
  passes to `c ∘ g^*` for `g` smooth of relative dimension `d`.
* `Stacks.Chow.BivariantClass.capFundamentalFormula_openImmersionComposite` — the case of an open
  immersion.
* `Stacks.Chow.completedVirtualNormalGysinClassOfOpen_apply_eq_of` and
  `Stacks.Chow.capFundamentalFormula_completedVirtualNormalGysinClassOfOpen` — on a connected
  component `Z_a` of `Z`, the class `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` of Stacks 0FBQ (3) for an
  immersion is concentrated in the degree `r_a` of the rank of `𝒩` on `Z_a`, where it satisfies
  the formula in every degree.
* `Stacks.Chow.completedBivariantGroup.HasCapFundamentalFormula.comp_completedFlatPullbackOfSmooth`
  — the property passes to the composite `c ∘ g^*` on completions with the flat pullback of a
  smooth morphism, the degree on a component dropping by the relative dimension of `g` there.
* `Stacks.Chow.chowGroupRestrict_cap_fundamentalChowClass_of_capFundamentalFormula` — if the
  restriction of `c ∈ A^p(X ⟶ Y)` to a connected component `X_a` satisfies the formula, then
  `c ∩ [T]_n` restricts to the fundamental class on every open subscheme of `X ×_Y T` over
  `X_a`, under the hypotheses of the formula at the points of `X ×_Y T` over `X_a`.

## Implementation notes

Unlike `Stacks.Chow.BivariantClass.CapCohenMacaulayFormula`, the degree `p` is an integer, so
that the composite `c ∘ g^*` of degree `p - d` is covered, and the Cohen–Macaulay condition is
asked at the points `ξ` of `Z ×_X T` of `δ`-dimension `n - p`, with `δ` read on `Z ×_X T` itself
rather than at the image of `ξ` in `T`. For a closed immersion the two readings agree; for
`Z ⟶ P ⟶ Y` they do not, and the reading on `Z ×_X T` is the one hypothesis (4) of Stacks 0FF7
provides.

## References

* [Stacks Project, Tag 0FEA](https://stacks.math.columbia.edu/tag/0FEA)
* [Stacks Project, Tag 0FF7](https://stacks.math.columbia.edu/tag/0FF7)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Formula

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X)
  [LocallyOfFiniteType i] (hi : i ≫ sX = sZ)

/-- **The formula `c ∩ [T]_n = [Z ×_X T]_{n - p}` over Cohen–Macaulay test schemes.** A class
`c ∈ A^p(Z ⟶ X)` satisfies the formula in degree `n` when, for every `t : T ⟶ X` locally of
finite type such that every irreducible component of `T` has `δ`-dimension `n`,
`dim_δ(Z ×_X T) ≤ n - p`, and `𝒪_{T, ξ}` is Cohen–Macaulay at the image of every point `ξ` of
`Z ×_X T` of `δ`-dimension `n - p`, the cap product of `c` with `[T]_n` is `[Z ×_X T]_{n - p}`. -/
def BivariantClass.CapFundamentalFormula {p : ℤ} (c : BivariantClass C G sZ sX i hi p) (n : ℤ) :
    Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ X) [LocallyOfFiniteType t],
    (∀ W : irreducibleComponents T,
      deltaDimension C (t ≫ sX)
        ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set T) W.2⟩ = n) →
    schemeDeltaDimension C (pullback.fst i t ≫ sZ) ≤ ((n - p : ℤ) : EInt) →
    (∀ ξ : (pullback i t : Scheme.{u}),
      relativeDimension C.dimensionFunction (pullback.fst i t ≫ sZ) ξ = n - p →
      letI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (t ≫ sX)
      IsCohenMacaulayLocalRing (T.presheaf.stalk (pullback.snd i t ξ))) →
    c.cap t n (fundamentalChowClass C (t ≫ sX) n) =
      fundamentalChowClass C (pullback.fst i t ≫ sZ) (n - p)

/-- The formula is unchanged by reading the class for an equal morphism and degree
(`Stacks.Chow.BivariantClass.copy`). -/
theorem BivariantClass.capFundamentalFormula_copy {i' : Z ⟶ X} [LocallyOfFiniteType i']
    (hii' : i = i') (hi' : i' ≫ sX = sZ) {p p' : ℤ} (hpp' : p = p')
    (c : BivariantClass C G sZ sX i hi p) (n : ℤ) :
    (BivariantClass.copy C G sZ sX hii' hi hi' hpp' c).CapFundamentalFormula C G sZ sX i' hi' n ↔
      c.CapFundamentalFormula C G sZ sX i hi n := by
  subst hii' hpp'
  rfl

end Formula

/-- The formula is unchanged by the identification of `Stacks.Chow.bivariantClassComponentCongr`
of the groups of bivariant classes for two morphisms into connected components indexed by equal
components. -/
theorem BivariantClass.capFundamentalFormula_bivariantClassComponentCongr
    (C : ChowSituation.{u}) (G : GysinSystem C) {W Y : Scheme.{u}} (sW : W ⟶ C.S)
    [LocallyOfFiniteType sW] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [LocallyConnectedSpace Y]
    {j₁ j₂ : _root_.ConnectedComponents Y} (hj : j₁ = j₂)
    (u₁ : W ⟶ (Y.connectedComponentOpens j₁ : Scheme.{u})) [LocallyOfFiniteType u₁]
    (u₂ : W ⟶ (Y.connectedComponentOpens j₂ : Scheme.{u})) [LocallyOfFiniteType u₂]
    (hu : u₁ ≍ u₂) (h₁ : u₁ ≫ ((Y.connectedComponentOpens j₁).ι ≫ sY) = sW)
    (h₂ : u₂ ≫ ((Y.connectedComponentOpens j₂).ι ≫ sY) = sW) (p : ℤ)
    (x : BivariantClass C G sW ((Y.connectedComponentOpens j₁).ι ≫ sY) u₁ h₁ p) (n : ℤ) :
    (bivariantClassComponentCongr C G sW sY hj u₁ u₂ hu h₁ h₂ p x).CapFundamentalFormula C G sW
        _ u₂ h₂ n ↔
      x.CapFundamentalFormula C G sW _ u₁ h₁ n := by
  subst hj
  obtain rfl := eq_of_heq hu
  rfl

/-- The formula is unchanged by the identification
`Stacks.Chow.completedBivariantCompositeTransport` of the classes for the composite of the
restrictions to connected components with the classes for the restriction of the composite. -/
theorem capFundamentalFormula_completedBivariantCompositeTransport (C : ChowSituation.{u})
    (G : GysinSystem C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ Z) [LocallyOfFiniteType g] (hf : f ≫ sY = sX)
    (hg : g ≫ sZ = sY) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (i : _root_.ConnectedComponents X) (p : ℤ)
    (x : BivariantClass C G ((X.connectedComponentOpens i).ι ≫ sX)
      ((Z.connectedComponentOpens (g.continuous.connectedComponentsMap
        (f.continuous.connectedComponentsMap i))).ι ≫ sZ)
      (f.resConnectedComponent i ≫
        g.resConnectedComponent (f.continuous.connectedComponentsMap i))
      (comp_comp_structureMorphism_eq (f.resConnectedComponent_comp_ι_comp hf i)
        (g.resConnectedComponent_comp_ι_comp hg (f.continuous.connectedComponentsMap i))) p)
    (n : ℤ) :
    (completedBivariantCompositeTransport C G sX sY sZ f g hf hg i p x).CapFundamentalFormula C G
        _ _ ((f ≫ g).resConnectedComponent i)
        ((f ≫ g).resConnectedComponent_comp_ι_comp (comp_comp_structureMorphism_eq hf hg) i) n ↔
      x.CapFundamentalFormula C G _ _ _ _ n :=
  BivariantClass.capFundamentalFormula_bivariantClassComponentCongr C G _ sZ _ _ _ _ _ _ p x n

/-! ### Stacks 0FEA -/

section VirtualNormal

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i]
  (hi : i ≫ sX = sZ) (𝒩 : VirtualNormalBundle i) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]

/-- **Stacks 0FEA, as the formula over Cohen–Macaulay test schemes.** The class `c(Z ⟶ X, 𝒩)` of
a virtual normal sheaf of constant rank `r` for a closed immersion satisfies
`Stacks.Chow.BivariantClass.CapFundamentalFormula` in every degree: for a closed immersion the
`δ`-dimension of a point of `Z ×_X T` is that of its image in `T`, so this is
`Stacks.Chow.virtualNormalGysinClass_capCohenMacaulayFormula`. -/
theorem virtualNormalGysinClass_capFundamentalFormula (n : ℤ) :
    (virtualNormalBundleClass C sZ sX i hi 𝒩 r).CapFundamentalFormula C
      (gysinSystemOfInvertible C) sZ sX i hi n := by
  intro T t _ hT hZT hCM
  have hs : pullback.snd i t ≫ (t ≫ sX) = pullback.fst i t ≫ sZ :=
    pullbackSnd_comp_structureMorphism hi t
  refine virtualNormalGysinClass_capCohenMacaulayFormula C sZ sX i hi 𝒩 r n t hT
    (by simpa only [hs] using hZT) fun ξ hξ => hCM ξ ?_
  rw [← hs, relativeDimension_comp_closedImmersion]
  exact hξ

end VirtualNormal

/-- A scheme all of whose irreducible components have `δ`-dimension `n` has `δ`-dimension at
most `n`. -/
private theorem schemeDeltaDimension_le_of_forall_deltaDimension_eq (C : ChowSituation.{u})
    {X : Scheme.{u}} (s : X ⟶ C.S) [LocallyOfFiniteType s] {n : ℤ}
    (h : ∀ W : irreducibleComponents X,
      deltaDimension C s ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set X) W.2⟩ = n) :
    schemeDeltaDimension C s ≤ (n : EInt) :=
  iSup_le fun V ↦ (congrArg (fun z : ℤ ↦ (z : EInt)) (h V)).le

/-- A scheme all of whose points have relative dimension at most `k` has `δ`-dimension at
most `k`. -/
private theorem schemeDeltaDimension_le_of_forall_relativeDimension_le' (C : ChowSituation.{u})
    {X : Scheme.{u}} (s : X ⟶ C.S) [LocallyOfFiniteType s] {k : ℤ}
    (h : ∀ x : X, relativeDimension C.dimensionFunction s x ≤ k) :
    schemeDeltaDimension C s ≤ (k : EInt) := by
  simpa using schemeDeltaDimension_le_of_forall_relativeDimension_le C s (𝟙 _) (by simpa using h)

/-! ### Composite with the flat pullback of a smooth morphism -/

section Composite

variable (C : ChowSituation.{u}) {Z P Y : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (i : Z ⟶ P) [LocallyOfFiniteType i] (g : P ⟶ Y) [Smooth g] [LocallyOfFiniteType g]
  (hi : i ≫ sP = sZ) (hg : g ≫ sY = sP)

/-- **The formula passes to the composite with the flat pullback of a smooth morphism.** Let
`c ∈ A^p(Z ⟶ P)` satisfy `Stacks.Chow.BivariantClass.CapFundamentalFormula` in degree `n + d`
and let `g : P ⟶ Y` be smooth of relative dimension `d`. Then `c ∘ g^* ∈ A^{p - d}(Z ⟶ Y)`
satisfies the formula in degree `n`: for a test scheme `T ⟶ Y` pure of `δ`-dimension `n`, the
scheme `P ×_Y T` is pure of `δ`-dimension `n + d` (Stacks 02R8) and `g^*[T]_n = [P ×_Y T]_{n+d}`
(Stacks 02RB), the identification `Z ×_P (P ×_Y T) ≅ Z ×_Y T` carries the dimension bound and
the points of `δ`-dimension `n + d - p`, and the local rings of `P ×_Y T` there are
Cohen–Macaulay because `P ×_Y T ⟶ T` is smooth (Stacks 045J). -/
theorem BivariantClass.capFundamentalFormula_bivariantCompositeOfInvertible {p : ℤ} {d : ℕ}
    (hgd : AlgebraicGeometry.RelativeDimension g d)
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sP i hi p) {n : ℤ}
    (hc : c.CapFundamentalFormula C _ sZ sP i hi (n - -(d : ℤ))) :
    (bivariantCompositeOfInvertible C sZ sP sY i g hi hg p (-(d : ℤ)) c
      (flatPullbackBivariantClassOfInvertible C sP sY g hg d hgd)).CapFundamentalFormula C _ sZ sY
      (i ≫ g) (comp_comp_structureMorphism_eq hi hg) n := by
  intro T s _ hT hZT hCM
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (s ≫ sY)
  have : IsLocallyNoetherian (pullback g s) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst g s ≫ sP)
  have hTdim := schemeDeltaDimension_le_of_forall_deltaDimension_eq C (s ≫ sY) hT
  -- `g^*[T]_n = [P ×_Y T]_{n + d}`
  have hsmooth := IsBivariantFlatPullback.cap_fundamentalChowClass
      (hdesc := flatPullbackDescends C)
        (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C sP sY g hg d hgd)
      s n hTdim
  -- the identification `Z ×_P (P ×_Y T) ≅ Z ×_Y T`
  set e := pullbackRightPullbackFstIso g s i
  have hefst : e.hom ≫ (pullback.fst (i ≫ g) s ≫ sZ) = pullback.fst i (pullback.fst g s) ≫ sZ :=
    pullbackRightPullbackFstIso_hom_comp_fst_comp sZ i g s
  have hesnd : e.hom ≫ pullback.snd (i ≫ g) s =
      pullback.snd i (pullback.fst g s) ≫ pullback.snd g s :=
    pullbackRightPullbackFstIso_hom_snd g s i
  have hrel : ∀ ξ, relativeDimension C.dimensionFunction
      (pullback.fst i (pullback.fst g s) ≫ sZ) ξ =
        relativeDimension C.dimensionFunction (pullback.fst (i ≫ g) s ≫ sZ) (e.hom ξ) := by
    intro ξ
    rw [← hefst, relativeDimension_comp_isOpenImmersion]
  have hstr : pullback.snd g s ≫ (s ≫ sY) = pullback.fst g s ≫ sP :=
    pullbackSnd_comp_structureMorphism hg s
  have hpure : ∀ W : irreducibleComponents (pullback g s : Scheme.{u}),
      deltaDimension C (pullback.fst g s ≫ sP)
        ⟨W, W.2.1,
          isClosed_of_mem_irreducibleComponents (W : Set (pullback g s : Scheme.{u})) W.2⟩ =
          n - -(d : ℤ) := by
    intro W
    obtain ⟨V, hV⟩ := exists_irreducibleComponent_map_genericPoint (pullback.snd g s) W
    have h := deltaDimension_irreducibleComponent_eq_add C (pullback.snd g s) (s ≫ sY) d
      (relativeDimension_pullbackSnd g hgd s) W V hV
    rw [hT V] at h
    simp only [hstr] at h
    rw [h]
    ring
  have hdimZ : ∀ ξ, relativeDimension C.dimensionFunction
      (pullback.fst i (pullback.fst g s) ≫ sZ) ξ ≤ n - -(d : ℤ) - p := by
    intro ξ
    rw [hrel]
    exact (relativeDimension_le_of_schemeDeltaDimension_le' C _ hZT _).trans (le_of_eq (by ring))
  have hdimZ' : schemeDeltaDimension C (pullback.fst i (pullback.fst g s) ≫ sZ) ≤
      ((n - -(d : ℤ) - p : ℤ) : EInt) :=
    schemeDeltaDimension_le_of_forall_relativeDimension_le' C _ hdimZ
  have hform := hc (pullback.fst g s) hpure hdimZ'
    (fun ξ hξ => by
      have hξ' : relativeDimension C.dimensionFunction (pullback.fst (i ≫ g) s ≫ sZ) (e.hom ξ) =
          n - (p + -(d : ℤ)) := by
        rw [← hrel, hξ]
        ring
      have h := hCM (e.hom ξ) hξ'
      have hpt : pullback.snd (i ≫ g) s (e.hom ξ) =
          pullback.snd g s (pullback.snd i (pullback.fst g s) ξ) := by
        rw [← Scheme.Hom.comp_apply, hesnd, Scheme.Hom.comp_apply]
      exact isCohenMacaulayLocalRing_stalk_of_smooth (pullback.snd g s) _ (hpt ▸ h))
  rw [bivariantCompositeOfInvertible, bivariantComposite_cap, bivariantCompositeCap_apply, hsmooth,
    hform, properChowPushforward_eq_chowPushforwardOfIso,
    chowPushforwardOfIso_fundamentalChowClass, chowGroupDegreeEquiv_fundamentalChowClass]

end Composite

/-! ### Composite with the flat pullback of an open immersion -/

section OpenImmersion

variable (C : ChowSituation.{u}) {Z U X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i : Z ⟶ U) [LocallyOfFiniteType i] (j : U ⟶ X) [IsOpenImmersion j]
  (hi : i ≫ sU = sZ) (hj : j ≫ sX = sU)

/-- The flat-pullback class of an open immersion at the Gysin system of the first Chern class
rule is the class of Stacks 0B78 of relative dimension `0`: the two have the same cap
operation. -/
theorem flatPullbackBivariantClassOfIsOpenImmersionOfInvertible_eq :
    flatPullbackBivariantClassOfIsOpenImmersionOfInvertible C sU sX j hj =
      flatPullbackBivariantClassOfInvertible C sU sX j hj 0
        (relativeDimension_of_isOpenImmersion j) :=
  BivariantClass.ext C _ sU sX j hj _ fun _ _ _ _ => rfl

/-- **The formula passes to the composite with an open immersion.** If `c ∈ A^p(Z ⟶ U)`
satisfies `Stacks.Chow.BivariantClass.CapFundamentalFormula` in degree `n`, so does
`c ∘ j^* ∈ A^p(Z ⟶ X)` for an open immersion `j : U ⟶ X`: an open immersion is smooth of
relative dimension `0`. -/
theorem BivariantClass.capFundamentalFormula_openImmersionComposite {p : ℤ}
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sU i hi p) {n : ℤ}
    (hc : c.CapFundamentalFormula C _ sZ sU i hi n) :
    (openImmersionComposite C sZ sU sX i j hi hj p c).CapFundamentalFormula C _ sZ sX (i ≫ j)
      (comp_comp_structureMorphism_eq hi hj) n := by
  rw [openImmersionComposite, flatPullbackBivariantClassOfIsOpenImmersionOfInvertible_eq]
  exact c.capFundamentalFormula_bivariantCompositeOfInvertible C sZ sU sX i j hi hj
    (relativeDimension_of_isOpenImmersion j) (by simpa using hc)

end OpenImmersion

/-! ### The completed class of an immersion on a connected component -/

section Immersion

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsImmersion i] (hi : i ≫ sX = sZ)
  [IsLocallyNoetherian Z] [IsLocallyNoetherian X]

/-- An element of a graded group equal to a homogeneous element of degree `p` is the homogeneous
element of its own degree-`q` part, for every `q = p`. -/
private theorem directSum_eq_of_apply {β : ℤ → Type*} [∀ p, AddCommMonoid (β p)]
    (v : DirectSum ℤ β) {p q : ℤ} (x : β p) (hv : v = DirectSum.of β p x) (h : p = q) :
    v = DirectSum.of β q (v q) := by
  subst h
  rw [hv, DirectSum.of_eq_same]

/-- The degree-`q` part of a graded bivariant class equal to a homogeneous class `x` of degree
`p = q` satisfies the formula as soon as `x` does. -/
private theorem capFundamentalFormula_apply_of_eq_of {A B : Scheme.{u}} {sA : A ⟶ C.S}
    [LocallyOfFiniteType sA] {sB : B ⟶ C.S} [LocallyOfFiniteType sB] {f : A ⟶ B}
    [LocallyOfFiniteType f] {hf : f ≫ sB = sA}
    (v : DirectSum ℤ fun p ↦ BivariantClass C (gysinSystemOfInvertible C) sA sB f hf p) {p q : ℤ}
    (x : BivariantClass C (gysinSystemOfInvertible C) sA sB f hf p)
    (hv : v = DirectSum.of _ p x) (h : p = q) {n : ℤ}
    (hx : x.CapFundamentalFormula C _ sA sB f hf n) :
    (v q).CapFundamentalFormula C _ sA sB f hf n := by
  subst h
  rw [hv, DirectSum.of_eq_same]
  exact hx

/-- A completed class read for the equal morphism is itself. -/
private theorem completedBivariantGroup.copy_rfl {G : GysinSystem C} {W Y : Scheme.{u}}
    {sW : W ⟶ C.S} [LocallyOfFiniteType sW] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
    {f : W ⟶ Y} [LocallyOfFiniteType f] (hf hf' : f ≫ sY = sW)
    (c : completedBivariantGroup C G sW sY f hf) :
    completedBivariantGroup.copy C rfl hf hf' c = c :=
  rfl

/-- **The class of an immersion is homogeneous on each connected component.** On the connected
component `Z_a` of `Z`, the completed class `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` of Stacks 0FBQ (3),
built from an open `U` through which `i` factors as a closed immersion, is concentrated in the
degree `r_a` of the rank of `𝒩` on `Z_a`. -/
theorem completedVirtualNormalGysinClassOfOpen_apply_eq_of (U : X.Opens) (i' : Z ⟶ U.toScheme)
    [IsClosedImmersion i'] (hU : i' ≫ U.ι = i) (𝒩 : VirtualNormalBundle i)
    (a : _root_.ConnectedComponents Z) :
    completedVirtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩 a =
      DirectSum.of _ (componentRank (𝒩.toOpenFactor hU).bundle a : ℤ)
        (completedVirtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩 a
          (componentRank (𝒩.toOpenFactor hU).bundle a : ℤ)) := by
  subst hU
  have : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ sX)
  rw [completedVirtualNormalGysinClassOfOpen, completedBivariantGroup.copy_rfl,
    completedOpenImmersionComposite]
  refine directSum_eq_of_apply _ _ (completedBivariantCompositeOfInvertible_of_of C sZ
    (U.ι ≫ sX) sX i' U.ι _ rfl _ _ a _ (-((0 : ℕ) : ℤ)) ?_ ?_)
    (by rw [Nat.cast_zero, neg_zero, add_zero])
  · rw [completedVirtualNormalGysinClass_apply, DirectSum.of_eq_same]
  · rw [completedFlatPullbackOfIsOpenImmersion_apply, DirectSum.of_eq_same]

/-- **Stacks 0FEA for the class of an immersion, on a connected component.** On the connected
component `Z_a` of `Z`, the degree-`r_a` part of the completed class `c(Z ⟶ X, 𝒩)` of Stacks 0FBQ
(3) satisfies `Stacks.Chow.BivariantClass.CapFundamentalFormula` in every degree: it is
`c(Z_a ⟶ V_a, 𝒩|_{Z_a})` (Stacks 0FBK, constant rank `r_a`) composed with flat pullback along
the open immersions `V_a ⟶ U_b ⟶ X_c` of a neighbourhood of `Z_a` and of connected components,
so Stacks 0FEA and the case of open immersions apply. -/
theorem capFundamentalFormula_completedVirtualNormalGysinClassOfOpen (U : X.Opens)
    (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hU : i' ≫ U.ι = i)
    (𝒩 : VirtualNormalBundle i) (a : _root_.ConnectedComponents Z) (n : ℤ) :
    (completedVirtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩 a
      (componentRank (𝒩.toOpenFactor hU).bundle a : ℤ)).CapFundamentalFormula C _ _ _
        (i.resConnectedComponent a)
        (i.resConnectedComponent_comp_ι_comp hi a) n := by
  subst hU
  have : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ sX)
  rw [completedVirtualNormalGysinClassOfOpen, completedBivariantGroup.copy_rfl,
    completedOpenImmersionComposite]
  refine capFundamentalFormula_apply_of_eq_of C _ _ (completedBivariantCompositeOfInvertible_of_of
    C sZ (U.ι ≫ sX) sX i' U.ι _ rfl _ _ a (componentRank (𝒩.toOpenFactor rfl).bundle a : ℤ)
      (-((0 : ℕ) : ℤ))
      (by rw [completedVirtualNormalGysinClass_apply, DirectSum.of_eq_same])
      (by rw [completedFlatPullbackOfIsOpenImmersion_apply, DirectSum.of_eq_same]))
    (by rw [Nat.cast_zero, neg_zero, add_zero]) ?_
  rw [capFundamentalFormula_completedBivariantCompositeTransport,
    completedFlatPullbackOfIsOpenImmersion_apply, DirectSum.of_eq_same]
  refine BivariantClass.capFundamentalFormula_openImmersionComposite C _ _ _ _ _ _ _ _ ?_
  rw [completedVirtualNormalGysinClass_apply, DirectSum.of_eq_same,
    BivariantClass.capFundamentalFormula_copy]
  exact BivariantClass.capFundamentalFormula_openImmersionComposite C _ _ _ _ _ _ _ _
    (virtualNormalGysinClass_capFundamentalFormula C _ _ _ _ _ _ n)

end Immersion

/-! ### Completed classes -/

section Completed

/-- **A completed class satisfying the formula componentwise.** A completed class
`c ∈ A^*(X ⟶ Y)^∧` (Stacks 0FE0) has the property, for a function `d` on the connected components
of `X`, when on each connected component `X_a` it is concentrated in degree `d a`, and its part of
degree `d a` satisfies `Stacks.Chow.BivariantClass.CapFundamentalFormula` in every degree. -/
def completedBivariantGroup.HasCapFundamentalFormula (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
    {f : X ⟶ Y} [LocallyOfFiniteType f] {hf : f ≫ sY = sX}
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf)
    (d : _root_.ConnectedComponents X → ℤ) : Prop :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  ∀ a : _root_.ConnectedComponents X, c a = DirectSum.of _ (d a) (c a (d a)) ∧
    ∀ n : ℤ, (c a (d a)).CapFundamentalFormula C _ _ _ (f.resConnectedComponent a)
      (f.resConnectedComponent_comp_ι_comp hf a) n

/-- The property is unchanged by reading the completed class for an equal morphism. -/
theorem completedBivariantGroup.HasCapFundamentalFormula.copy (C : ChowSituation.{u})
    {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] {f f' : X ⟶ Y} [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    (hff : f = f') (hf : f ≫ sY = sX) (hf' : f' ≫ sY = sX)
    {c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf}
    {d : _root_.ConnectedComponents X → ℤ}
    (hc : completedBivariantGroup.HasCapFundamentalFormula C c d) :
    completedBivariantGroup.HasCapFundamentalFormula C
      (completedBivariantGroup.copy C hff hf hf' c) d := by
  subst hff
  exact hc

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsImmersion i] (hi : i ≫ sX = sZ)

/-- **Stacks 0FEA for the completed class of an immersion.** The completed class
`c(Z ⟶ X, 𝒩)` of Stacks 0FBQ (3) is concentrated on each connected component `Z_a` in the degree
`r_a` of the rank of `𝒩` there, where it satisfies the formula in every degree. -/
theorem hasCapFundamentalFormula_completedVirtualNormalGysinClassOfOpen (U : X.Opens)
    (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hU : i' ≫ U.ι = i)
    (𝒩 : VirtualNormalBundle i) :
    letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    completedBivariantGroup.HasCapFundamentalFormula C
      (completedVirtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩)
      fun a ↦ (componentRank (𝒩.toOpenFactor hU).bundle a : ℤ) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  exact fun a ↦ ⟨completedVirtualNormalGysinClassOfOpen_apply_eq_of C sZ sX i hi U i' hU 𝒩 a,
    capFundamentalFormula_completedVirtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩 a⟩

variable {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (g : X ⟶ Y) [Smooth g]
  [LocallyOfFiniteType g] (hg : g ≫ sY = sX)

omit [IsImmersion i] in
/-- **The property passes to the composite with the flat pullback of a smooth morphism, on
completions.** If `c ∈ A^*(Z ⟶ X)^∧` is concentrated on `Z_a` in degree `d a`, where it satisfies
the formula in every degree, then `c ∘ g^* ∈ A^*(Z ⟶ Y)^∧` (Stacks 0FE0) is concentrated on `Z_a`
in degree `d a - t`, for `t` the relative dimension of `g` on the connected component of `X`
containing the image of `Z_a`, where it satisfies the formula in every degree. -/
theorem completedBivariantGroup.HasCapFundamentalFormula.comp_completedFlatPullbackOfSmooth
    [LocallyOfFiniteType i] [IsLocallyNoetherian Z] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {c : completedBivariantGroup C (gysinSystemOfInvertible C) sZ sX i hi}
    {d : _root_.ConnectedComponents Z → ℤ}
    (hc : completedBivariantGroup.HasCapFundamentalFormula C c d) :
    completedBivariantGroup.HasCapFundamentalFormula C
      (Stacks.Chow.completedBivariantCompositeOfInvertible C sZ sX sY i g hi hg c
        (completedFlatPullbackOfSmooth C sX sY g hg))
      fun a ↦ d a + -(smoothComponentRelativeDimension g
        (i.continuous.connectedComponentsMap a) : ℤ) := by
  intro a
  have hd : completedFlatPullbackOfSmooth C sX sY g hg (i.continuous.connectedComponentsMap a) =
      DirectSum.of _ (-(smoothComponentRelativeDimension g
        (i.continuous.connectedComponentsMap a) : ℤ))
        (completedFlatPullbackOfSmooth C sX sY g hg (i.continuous.connectedComponentsMap a)
          (-(smoothComponentRelativeDimension g (i.continuous.connectedComponentsMap a) : ℤ))) := by
    rw [completedFlatPullbackOfSmooth_apply, DirectSum.of_eq_same]
  have hcomp := Stacks.Chow.completedBivariantCompositeOfInvertible_of_of C sZ sX sY i g hi hg c
    (completedFlatPullbackOfSmooth C sX sY g hg) a (d a) _ (hc a).1 hd
  refine ⟨directSum_eq_of_apply _ _ hcomp rfl, fun n ↦ ?_⟩
  refine capFundamentalFormula_apply_of_eq_of C _ _ hcomp rfl ?_
  rw [capFundamentalFormula_completedBivariantCompositeTransport,
    completedFlatPullbackOfSmooth_apply, DirectSum.of_eq_same]
  exact BivariantClass.capFundamentalFormula_bivariantCompositeOfInvertible C _ _ _ _ _ _ _
    (relativeDimension_smoothComponentRelativeDimension g _) _ ((hc a).2 _)

end Completed

/-! ### Restriction to a connected component -/

section ComponentRestriction

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- **The formula on a connected component, read on an open subscheme of the base change.** Let
`c ∈ A^p(X ⟶ Y)` be a class whose restriction to the connected component `X_a` of `X`
(Stacks 0FDZ) satisfies `Stacks.Chow.BivariantClass.CapFundamentalFormula` in degree `n`, and let
`t : T ⟶ Y` be pure of `δ`-dimension `n` such that the points of `X ×_Y T` over `X_a` have
`δ`-dimension at most `n - p`, with `𝒪_T` Cohen–Macaulay at the images of those of
`δ`-dimension `n - p`. Then `c ∩ [T]_n` restricts to `[W]_{n - p}` on every open subscheme `W` of
`X ×_Y T` lying over `X_a`.

Over the open subscheme `T_V = T ×_Y Y_b` of `T`, for `Y_b` the connected component containing
`f(X_a)`, the cap operation of `c` restricts to that of its restriction to `X_a` (Stacks 0B76 (2)
along the open immersion `T_V ⟶ T`), to which the formula applies; the hypotheses pass to
`X_a ×_{Y_b} T_V` through its open immersion into `X ×_Y T`. -/
theorem chowGroupRestrict_cap_fundamentalChowClass_of_capFundamentalFormula {p : ℤ}
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p)
    (i : _root_.ConnectedComponents X) {n : ℤ}
    (hc : (bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sY f hf p
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) c i).CapFundamentalFormula C _ _ _
        (f.resConnectedComponent i) (f.resConnectedComponent_comp_ι_comp hf i) n)
    {T : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t]
    (hT : ∀ W : irreducibleComponents T,
      deltaDimension C (t ≫ sY)
        ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set T) W.2⟩ = n)
    (hdim : ∀ ξ : (pullback f t : Scheme.{u}), pullback.fst f t ξ ∈ X.connectedComponentOpens i →
      relativeDimension C.dimensionFunction (pullback.fst f t ≫ sX) ξ ≤ n - p)
    (hCM : ∀ ξ : (pullback f t : Scheme.{u}), pullback.fst f t ξ ∈ X.connectedComponentOpens i →
      relativeDimension C.dimensionFunction (pullback.fst f t ≫ sX) ξ = n - p →
      letI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (t ≫ sY)
      IsCohenMacaulayLocalRing (T.presheaf.stalk (pullback.snd f t ξ)))
    {W : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (u : W ⟶ pullback f t)
    [IsOpenImmersion u] (hu : u ≫ (pullback.fst f t ≫ sX) = sW)
    (a : W ⟶ (X.connectedComponentOpens i : Scheme.{u}))
    (ha : a ≫ (X.connectedComponentOpens i).ι = u ≫ pullback.fst f t) :
    chowGroupRestrict C (pullback.fst f t ≫ sX) sW u hu (n - p)
        (c.cap t n (fundamentalChowClass C (t ≫ sY) n)) = fundamentalChowClass C sW (n - p) := by
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (t ≫ sY)
  set V := Y.connectedComponentOpens (f.continuous.connectedComponentsMap i)
  set v := pullback.fst t V.ι
  set g' := pullback.snd t V.ι
  have hg' : g' ≫ V.ι = v ≫ t := pullback.condition.symm
  have sq := isPullback_baseChangeMapOfEq f t v (v ≫ t) rfl
  have : IsOpenImmersion (baseChangeMapOfEq f t v (v ≫ t) rfl) :=
    MorphismProperty.of_isPullback sq (P := @IsOpenImmersion) inferInstance
  have hvY : v ≫ (t ≫ sY) = (v ≫ t) ≫ sY := (Category.assoc _ _ _).symm
  have hTdim := schemeDeltaDimension_le_of_forall_deltaDimension_eq C (t ≫ sY) hT
  -- restricting the test scheme to `T_V`
  have hcap := BivariantClass.cap_chowGroupRestrict C _ sX sY f hf p c t v (v ≫ t) rfl
    (baseChangeMapOfEq f t v (v ≫ t) rfl) sq (baseChangeMapOfEq_fst f t v (v ≫ t) rfl) n hvY
    (baseChangeMapOfEq_comp_structure sX f t v (v ≫ t) rfl) (fundamentalChowClass C (t ≫ sY) n)
  rw [chowGroupRestrict_fundamentalChowClass C _ _ v hvY n hTdim] at hcap
  -- the comparison `X_a ×_{Y_b} T_V ⟶ X ×_Y T_V ⟶ X ×_Y T`
  have hmY : g' ≫ (V.ι ≫ sY) = (v ≫ t) ≫ sY := by rw [← Category.assoc, hg']
  set φ := pieceMap f X.connectedComponentOpens Y.connectedComponentOpens
    f.continuous.connectedComponentsMap f.connectedComponentOpens_le_preimage i
  have hc' : BivariantClass.CapFundamentalFormula C (gysinSystemOfInvertible C)
      ((X.connectedComponentOpens i).ι ≫ sX) _ φ
      (pieceMap_comp_structureMorphism C sX sY f hf _ _ _ _ i)
      (bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sY f hf p
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) c i) n := hc
  set w := pieceComparisonCongr f X.connectedComponentOpens Y.connectedComponentOpens
    f.continuous.connectedComponentsMap f.connectedComponentOpens_le_preimage i g' (v ≫ t) hg'
  set M := w ≫ baseChangeMapOfEq f t v (v ≫ t) rfl
  have hMfst : M ≫ pullback.fst f t =
      pullback.fst φ g' ≫ (X.connectedComponentOpens i).ι := by
    rw [Category.assoc, baseChangeMapOfEq_fst]
    exact pieceComparisonCongr_fst _ _ _ _ _ _ _ _ _
  have hMsnd : M ≫ pullback.snd f t = pullback.snd φ g' ≫ v := by
    rw [Category.assoc, baseChangeMapOfEq_snd, ← Category.assoc]
    exact congrArg (· ≫ v) (pieceComparisonCongr_snd _ _ _ _ _ _ _ _ _)
  have hMbase : M ≫ (pullback.fst f t ≫ sX) =
      pullback.fst φ g' ≫ ((X.connectedComponentOpens i).ι ≫ sX) := by
    rw [← Category.assoc, hMfst, Category.assoc]
  have : IsOpenImmersion M := IsOpenImmersion.comp _ _
  have hrel : ∀ ζ, relativeDimension C.dimensionFunction
      (pullback.fst φ g' ≫ ((X.connectedComponentOpens i).ι ≫ sX)) ζ =
        relativeDimension C.dimensionFunction (pullback.fst f t ≫ sX) (M ζ) := fun ζ ↦ by
    rw [← hMbase, relativeDimension_comp_isOpenImmersion C.dimensionFunction M
      (pullback.fst f t ≫ sX) ζ]
  have hmem : ∀ ζ, pullback.fst f t (M ζ) ∈ X.connectedComponentOpens i := fun ζ ↦ by
    rw [← Scheme.Hom.comp_apply, hMfst, Scheme.Hom.comp_apply]
    exact (pullback.fst φ g' ζ).2
  -- the hypotheses of the formula over `T_V`
  have hpure : ∀ W : irreducibleComponents (pullback t V.ι : Scheme.{u}),
      deltaDimension C (g' ≫ (V.ι ≫ sY))
        ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents
          (W : Set (pullback t V.ι : Scheme.{u})) W.2⟩ = n := fun W ↦ by
    simpa only [hmY, Category.assoc] using
      deltaDimension_irreducibleComponents_of_isOpenImmersion C (t ≫ sY) hT v W
  have hdimZ : ∀ ζ, relativeDimension C.dimensionFunction
      (pullback.fst φ g' ≫ ((X.connectedComponentOpens i).ι ≫ sX)) ζ ≤
        n - p := fun ζ ↦ by
    rw [hrel]
    exact hdim _ (hmem ζ)
  have hdimZ' : schemeDeltaDimension C
      (pullback.fst φ g' ≫ ((X.connectedComponentOpens i).ι ≫ sX)) ≤
        ((n - p : ℤ) : EInt) :=
    schemeDeltaDimension_le_of_forall_relativeDimension_le' C _ hdimZ
  have hform := hc' g' hpure hdimZ' (fun ζ hζ ↦ by
    have h := hCM (M ζ) (hmem ζ) (by rwa [← hrel])
    have hpt : pullback.snd f t (M ζ) = v (pullback.snd φ g' ζ) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hMsnd]
    exact (isCohenMacaulayLocalRing_iff_of_ringEquiv
      (asIso (v.stalkMap (pullback.snd φ g' ζ))).commRingCatIsoToRingEquiv).mp
      (hpt ▸ h))
  -- the cap operation of the restriction to `X_a`, over `T_V`
  have hpiece := bivariantPieceRestrictionCap_eq C _ sX sY f hf p X.connectedComponentOpens
    Y.connectedComponentOpens f.continuous.connectedComponentsMap
    f.connectedComponentOpens_le_preimage i c g' (v ≫ t) hg' hmY w
    (pieceComparisonCongr_fst _ _ _ _ _ _ _ _ _) (pieceComparisonCongr_snd _ _ _ _ _ _ _ _ _) n
    (pieceComparisonCongr_comp_structureMorphism _ _ _ _ _ _ _ _ _ sX)
    (fundamentalChowClass C (g' ≫ (V.ι ≫ sY)) n)
  rw [chowGroupCongr_fundamentalChowClass] at hpiece
  have hform' : bivariantPieceRestrictionCap C _ sX sY f hf p X.connectedComponentOpens
      Y.connectedComponentOpens f.continuous.connectedComponentsMap
      f.connectedComponentOpens_le_preimage i c g' n
      (fundamentalChowClass C (g' ≫ (V.ι ≫ sY)) n) =
        fundamentalChowClass C
          (pullback.fst φ g' ≫ ((X.connectedComponentOpens i).ι ≫ sX))
          (n - p) := hform
  rw [hform', ← hcap, chowGroupRestrict_comp] at hpiece
  -- `W ⟶ X ×_Y T` factors through `X_a ×_{Y_b} T_V`
  have hT' : (u ≫ pullback.snd f t) ≫ t = (a ≫ φ) ≫ V.ι := by
    simp only [Category.assoc]
    rw [pieceMap_comp_ι, ← Category.assoc a, ha, Category.assoc, pullback.condition]
  have hW : a ≫ φ = pullback.lift _ _ hT' ≫ g' := by
    rw [pullback.lift_snd]
  have hfac : pullback.lift a (pullback.lift _ _ hT') hW ≫ M = u := by
    apply pullback.hom_ext
    · rw [Category.assoc, hMfst, pullback.lift_fst_assoc, ha]
    · rw [Category.assoc, hMsnd, pullback.lift_snd_assoc, pullback.lift_fst]
  have : IsOpenImmersion (pullback.lift a (pullback.lift _ _ hT') hW ≫ M) := by
    rw [hfac]
    infer_instance
  have : IsOpenImmersion (pullback.lift a (pullback.lift _ _ hT') hW) :=
    IsOpenImmersion.of_comp _ M
  have hbase₁ : pullback.lift a (pullback.lift _ _ hT') hW ≫
      (pullback.fst φ g' ≫ ((X.connectedComponentOpens i).ι ≫ sX)) = sW := by
    rw [← hMbase, ← Category.assoc, hfac, hu]
  calc chowGroupRestrict C (pullback.fst f t ≫ sX) sW u hu (n - p)
        (c.cap t n (fundamentalChowClass C (t ≫ sY) n))
      = chowGroupRestrict C _ sW (pullback.lift a (pullback.lift _ _ hT') hW) hbase₁ (n - p)
          (chowGroupRestrict C _ _ M hMbase (n - p)
            (c.cap t n (fundamentalChowClass C (t ≫ sY) n))) := by
        rw [chowGroupRestrict_comp]
        exact DFunLike.congr_fun (chowGroupRestrict_congr C _ _ _ _ _ _ hfac.symm _) _
    _ = fundamentalChowClass C sW (n - p) := by
        rw [← hpiece, chowGroupRestrict_fundamentalChowClass C _ _ _ _ _ hdimZ']

end ComponentRestriction

end Stacks.Chow

end
