module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionGysinFunctoriality
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionCycleClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalCorrespondence
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalCycle
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquarePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardRationalEquivalence.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.GysinChernCharacter
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescent
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.SmoothTransversalComposition
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DimensionDecompositionBasePoint

/-!
# The Gysin map on the class of a smooth closed subscheme meeting a morphism transversally

Let `f : X ⟶ Y` be a morphism of schemes smooth over a field `k`, with `X` and `Y` of constant
dimensions `d` and `e`, and let `Z ⊆ Y` be a closed subscheme smooth over `k` of constant dimension
`e - c`. If the scheme-theoretic inverse image `X ×_Y Z` is smooth over `k` of constant dimension
`d - c`, then the Gysin map of Stacks 0FF3, graded by codimension
(`Stacks.Chow.codimensionGysin`), carries `[Z] ∈ CH^c(Y)` to `[X ×_Y Z] ∈ CH^c(X)`:

  `f^![Z] = [f⁻¹Z]`.

The proof is that of Stacks 0FF7 with the test scheme `Z` in place of `Y`. On the piece of `X`
over the part `Y_e` of `Y` the Gysin map is the cap product with `f^! ∈ A^{e-d}(X ⟶ Y)` at the
test scheme `Y_e ⟶ Y`. The class `[Z]|_{Y_e}` is the pushforward of the fundamental class of
`Z_e = Z ×_Y Y_e` along the closed immersion `Z_e ⟶ Y_e`; a bivariant class commutes with proper
pushforward (Stacks 0B76 (1)), and at the test scheme `Z_e ⟶ Y` the Gysin map caps `[Z_e]` to the
fundamental class of `X ×_Y Z_e`, since `Z_e` is Cohen–Macaulay, being smooth over `k`, and
`X ×_Y Z_e` has the expected dimension
(`Stacks.Chow.cap_completedBivariantSequenceOfInvertible_lciGysinMap_fundamentalChowClass`).
Pushing forward and restricting to the piece gives the class of `X ×_Y Z` there.

This contains the flat case (a flat `f` meets every closed subscheme in the expected dimension)
only when the inverse image is smooth; it is the form in which the transversal intersections of
the chapter on Weil cohomology theories are met, e.g. the pullback of the diagonal of `X` along
`x × X ⟶ X × X` for a closed point `x`.

## Main results

* `Stacks.Chow.cycleGroupRestrict_cycleAssociatedToClosedSubscheme`: the cycle of a closed
  subscheme restricts, along an open immersion, to the cycle of its inverse image.
* `Stacks.Chow.smoothGysinClass_cap_mk_cycleAssociatedToClosedSubscheme`: the Gysin map caps the
  class of a smooth closed subscheme of a test scheme to the class of its inverse image.
* `Stacks.Chow.codimensionGysin_closedSubschemeClass_of_smooth`: `f^![Z] = [f⁻¹Z]`.
* `Stacks.WeilCohomology.codimensionGysin_prodHom_diagonal`: `(φ × ψ)^![Δ_X] = [Y ×_X W]`, the
  inverse image `Y ×_X W` of the diagonal being identified by
  `Stacks.WeilCohomology.pullbackDiagonalIso`.
* `Stacks.WeilCohomology.codimensionGysin_prodHom_id_diagonal`: `(i × 1)^![Δ_W] = [Γ_i]`.
* `Stacks.WeilCohomology.codimensionGysin_prodHom_diagonal_of_isIso`: `(iψ × ψ)^![Δ_X] = [Γ_i]`
  when `ψ : W ⟶ X` is an isomorphism over the image of `i`; for a blowup `ψ` and a point `i` off
  the exceptional divisor this is the comparison of the two diagonals in the proof of Stacks 0FIS.

## References

* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0FF7](https://stacks.math.columbia.edu/tag/0FF7)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Restricting the cycle of a closed subscheme to an open subscheme -/

section Restrict

variable (C : ChowSituation.{u}) {X U Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (j : U ⟶ X) [IsOpenImmersion j] (hj : j ≫ sX = sU)
  (i : Z ⟶ X) [IsClosedImmersion i]

include hj in
omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sU] [IsOpenImmersion j] [IsClosedImmersion i] in
/-- The inverse image of a closed subscheme along a morphism over the base is a scheme over the
base through either projection. -/
theorem pullbackSnd_comp_eq_pullbackFst_comp :
    pullback.snd i j ≫ sU = pullback.fst i j ≫ i ≫ sX := by
  rw [← hj, pullback.condition_assoc]

/-- **The cycle of a closed subscheme restricts to the cycle of its inverse image.** For an open
immersion `j : U ⟶ X` and a closed subscheme `Z ⊆ X`, `[Z]_k|_U = [U ×_X Z]_k`: the cycle of `Z`
is the pushforward of the fundamental cycle of `Z`, restriction commutes with proper pushforward
in the cartesian square over `j` (Stacks 02RG), and the fundamental cycle restricts to the
fundamental cycle. -/
theorem cycleGroupRestrict_cycleAssociatedToClosedSubscheme (k : ℤ) :
    cycleGroupRestrict C sX sU j hj k (cycleAssociatedToClosedSubscheme C sX i k) =
      cycleAssociatedToClosedSubscheme C sU (pullback.snd i j) k := by
  have hq' := pullbackSnd_comp_eq_pullbackFst_comp C sX sU j hj i
  rw [← properPushforward_cycleAssociatedToClosedSubscheme_id C (i ≫ sX) sX i rfl k,
    cycleGroupRestrict_properPushforward C (i ≫ sX) sX (pullback.fst i j ≫ i ≫ sX) sU i rfl
      (pullback.fst i j) rfl j hj (pullback.snd i j) hq' (IsPullback.of_hasPullback i j) k]
  have h := cycleGroupRestrict_fundamentalCycle C (i ≫ sX) (pullback.fst i j ≫ i ≫ sX)
    (pullback.fst i j) rfl k
  rw [fundamentalCycle] at h
  rw [h, fundamentalCycle,
    properPushforward_cycleAssociatedToClosedSubscheme_id C _ sU (pullback.snd i j) hq' k]

/-- `Stacks.Chow.cycleGroupRestrict_cycleAssociatedToClosedSubscheme` on Chow groups. -/
theorem chowGroupRestrict_mk_cycleAssociatedToClosedSubscheme (k : ℤ) :
    chowGroupRestrict C sX sU j hj k
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C sX i k)) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C sU (pullback.snd i j) k) := by
  show chowGroupRestrict C sX sU j hj k (QuotientAddGroup.mk' _ _) = QuotientAddGroup.mk' _ _
  rw [chowGroupRestrict_mk, cycleGroupRestrict_cycleAssociatedToClosedSubscheme]

/-- `Stacks.Chow.chowGroupRestrict_mk_cycleAssociatedToClosedSubscheme` for any cartesian square
presenting the inverse image. -/
theorem chowGroupRestrict_mk_cycleAssociatedToClosedSubscheme_of_isPullback {V : Scheme.{u}}
    (g' : V ⟶ Z) (i' : V ⟶ U) [IsClosedImmersion i'] (hsq : IsPullback g' i' i j) (k : ℤ) :
    chowGroupRestrict C sX sU j hj k
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C sX i k)) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C sU i' k) := by
  rw [chowGroupRestrict_mk_cycleAssociatedToClosedSubscheme,
    cycleAssociatedToClosedSubscheme_eq_of_iso C sU i' (pullback.snd i j) hsq.isoPullback
      hsq.isoPullback_hom_snd k]

/-- The class of a closed subscheme is the pushforward of its fundamental class. -/
theorem mk_cycleAssociatedToClosedSubscheme_eq_properChowPushforward (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (hi : i ≫ sX = sZ) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sZ sX i hi k) :
    (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C sX i k) : chowGroup C sX k) =
      properChowPushforward C sZ sX i hi k hfac (fundamentalChowClass C sZ k) := by
  subst hi
  rw [fundamentalChowClass, properChowPushforward_mk, fundamentalCycle,
    properPushforward_cycleAssociatedToClosedSubscheme_id]
  rfl

end Restrict

/-! ### The Gysin map on the class of a transversal closed subscheme -/

section Transversal

open Stacks.WeilCohomology (dimPart partBase relativeDimension_partBase isEmpty_dimPart_of_ne
  closedSubschemeClass closedSubschemeClass_apply
  deltaDimension_irreducibleComponent_of_relativeDimension
  deltaDimension_irreducibleComponent_of_relativeDimension_eq
  schemeDeltaDimension_le_of_relativeDimension
  isCohenMacaulayLocalRing_stalk_of_smooth)

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX]
  (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sY] {f : X ⟶ Y} [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX)

/-- The inverse image `X ×_Y Z` of `Z` restricted to `X ×_Y Y'` is `X ×_Y (Z ×_Y Y')`, for an open
subscheme `Y' ⊆ Y`, compatibly with the maps to `X ×_Y Y'`. -/
def pullbackFstPullbackFstIso (i : Z ⟶ Y) {Y' : Scheme.{u}} (ι : Y' ⟶ Y) :
    pullback (pullback.fst f i) (pullback.fst f ι) ≅ pullback f (pullback.snd i ι ≫ ι) := by
  let P := pullback (pullback.fst f i) (pullback.fst f ι)
  let a : P ⟶ X := pullback.fst _ _ ≫ pullback.fst f i
  have ha : pullback.snd (pullback.fst f i) (pullback.fst f ι) ≫ pullback.fst f ι = a :=
    pullback.condition.symm
  have h1 : (pullback.fst (pullback.fst f i) (pullback.fst f ι) ≫ pullback.snd f i) ≫ i =
      (pullback.snd (pullback.fst f i) (pullback.fst f ι) ≫ pullback.snd f ι) ≫ ι := by
    rw [Category.assoc, Category.assoc, ← pullback.condition, ← pullback.condition,
      ← Category.assoc, ← Category.assoc, pullback.condition]
  let b : P ⟶ pullback i ι := pullback.lift _ _ h1
  have h2 : a ≫ f = b ≫ pullback.snd i ι ≫ ι := by
    simp only [b, a, pullback.lift_snd_assoc, Category.assoc]
    rw [← pullback.condition, ← Category.assoc, ← Category.assoc, pullback.condition]
  refine
    { hom := pullback.lift a b h2
      inv := pullback.lift
        (pullback.map f (pullback.snd i ι ≫ ι) f i (𝟙 X) (pullback.fst i ι) (𝟙 Y) (by simp)
          (by simp [pullback.condition]))
        (pullback.map f (pullback.snd i ι ≫ ι) f ι (𝟙 X) (pullback.snd i ι) (𝟙 Y) (by simp)
          (by simp))
        (by simp)
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst_assoc]
        simp only [pullback.map]
        rw [pullback.lift_fst, Category.comp_id, pullback.lift_fst, Category.id_comp]
      · rw [Category.assoc, Category.assoc, pullback.lift_fst_assoc]
        simp only [pullback.map]
        rw [pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.id_comp]
        simp only [b, pullback.lift_fst]
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_snd_assoc]
        simp only [pullback.map]
        rw [pullback.lift_fst, Category.comp_id, pullback.lift_fst, Category.id_comp, ha]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd_assoc]
        simp only [pullback.map]
        rw [pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.id_comp]
        simp only [b, pullback.lift_snd]
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      simp
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_snd_assoc, pullback.lift_fst,
          pullback.lift_fst_assoc]
        simp
      · rw [Category.assoc, Category.assoc, pullback.lift_snd_assoc, pullback.lift_snd,
          pullback.lift_snd_assoc]
        simp

omit [LocallyOfFiniteType f] in
/-- Under `Stacks.Chow.pullbackFstPullbackFstIso`, the second projection to `X ×_Y Y'` is the base
change of `Z ×_Y Y' ⟶ Y'`. -/
@[reassoc (attr := simp)]
theorem pullbackFstPullbackFstIso_hom_bivariantBaseChangeMap (i : Z ⟶ Y) {Y' : Scheme.{u}}
    (ι : Y' ⟶ Y) :
    (pullbackFstPullbackFstIso (f := f) i ι).hom ≫ bivariantBaseChangeMap f ι (pullback.snd i ι) =
      pullback.snd (pullback.fst f i) (pullback.fst f ι) := by
  apply pullback.hom_ext
  · simp only [pullbackFstPullbackFstIso, bivariantBaseChangeMap, Category.assoc, pullback.map]
    rw [pullback.lift_fst, Category.comp_id, pullback.lift_fst, pullback.condition]
  · simp only [pullbackFstPullbackFstIso, bivariantBaseChangeMap, Category.assoc, pullback.map]
    rw [pullback.lift_snd, ← Category.assoc, pullback.lift_snd, pullback.lift_snd]

set_option maxHeartbeats 800000 in
/-- **The Gysin map caps the class of a smooth closed subscheme of a test scheme to the class of
its inverse image.** Let `X`, `Y` be smooth over `k` of constant dimensions `d`, `e`, let
`g : T ⟶ Y` be a test scheme and `Z ⊆ T` a closed subscheme smooth over `k` of constant dimension
`m'`. If `X ×_Y Z` has `δ` at most `m' - (e - d)` everywhere, then the degree `e - d` part of the
Gysin map of `f` caps `[Z]_{m'} ∈ CH_{m'}(T)` to `[X ×_Y Z]_{m' - (e - d)} ∈ CH(X ×_Y T)`. This is
Stacks 0FF7 at the test scheme `Z`, transported to `T` along the closed immersion by Stacks 0B76
(1). -/
theorem smoothGysinClass_cap_mk_cycleAssociatedToClosedSubscheme {d e : ℕ}
    (hX : RelativeDimension sX d) (hY : RelativeDimension sY e) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (i : Z ⟶ T) [IsClosedImmersion i] {qZ : Z ⟶ (fieldChowSituation k).S}
    [Smooth qZ] (hqZ : (i ≫ g) ≫ sY = qZ) {n : ℕ} (hZ : RelativeDimension qZ n) {m' : ℤ}
    (hn : (n : ℤ) = m')
    (hdim : ∀ ξ : (pullback f (i ≫ g) : Scheme.{u}),
      relativeDimension (fieldChowSituation k).dimensionFunction (pullback.fst f (i ≫ g) ≫ sX) ξ ≤
        m' - ((e : ℤ) - d)) :
    haveI : IsClosedImmersion (bivariantBaseChangeMap f g i) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap f g i)
        (P := @IsClosedImmersion) inferInstance
    (smoothGysinClass (fieldChowSituation k) sX sY hf ((e : ℤ) - d)).cap g m'
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) (g ≫ sY) i
          m')) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (pullback.fst f g ≫ sX) (bivariantBaseChangeMap f g i) (m' - ((e : ℤ) - d))) := by
  have : IsClosedImmersion (bivariantBaseChangeMap f g i) :=
    MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap f g i)
      (P := @IsClosedImmersion) inferInstance
  subst hqZ
  have hlci := isLocalCompleteIntersectionMorphism_of_smooth_of_smooth f sY sX hf
  have hex := GysinMapExists.of_smooth_source f sY sX hf
  have hfst := bivariantBaseChangeMap_fst f g i
  rw [mk_cycleAssociatedToClosedSubscheme_eq_properChowPushforward (fieldChowSituation k) (g ≫ sY)
      i ((i ≫ g) ≫ sY) (by simp) m'
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ i (by simp) m'),
    BivariantClass.cap_properPushforward _ g i (bivariantBaseChangeMap f g i)
      (isPullback_bivariantBaseChangeMap f g i) hfst m']
  have h0FF7 := cap_completedBivariantSequenceOfInvertible_lciGysinMap_fundamentalChowClass
    (fieldChowSituation k) sX sY hf hlci hex (i ≫ g) (n := d) (m := e) (m' := m')
    (deltaDimension_irreducibleComponent_of_relativeDimension k sX d hX)
    (deltaDimension_irreducibleComponent_of_relativeDimension k sY e hY)
    (deltaDimension_irreducibleComponent_of_relativeDimension_eq k _ hZ hn) hdim
    (fun ξ _ ↦ isCohenMacaulayLocalRing_stalk_of_smooth k ((i ≫ g) ≫ sY) _)
  show (properChowPushforward _ _ _ _ _ _ _
    ((smoothGysinClass (fieldChowSituation k) sX sY hf ((e : ℤ) - d)).cap (i ≫ g) m'
      (fundamentalChowClass _ ((i ≫ g) ≫ sY) m'))) = _
  rw [h0FF7, mk_cycleAssociatedToClosedSubscheme_eq_properChowPushforward (fieldChowSituation k)
    (pullback.fst f g ≫ sX) (bivariantBaseChangeMap f g i) (pullback.fst f (i ≫ g) ≫ sX)
    (by rw [← Category.assoc, hfst])]

/-- **`f^![Z] = [f⁻¹Z]` for a smooth closed subscheme meeting `f` in a smooth inverse image.** Let
`f : X ⟶ Y` be a morphism of schemes smooth over `k`, of constant dimensions `d` and `e`, and let
`i : Z ⟶ Y` be a closed immersion with `Z` smooth over `k` of constant dimension `e - c`. If the
scheme-theoretic inverse image `X ×_Y Z` is smooth over `k` of constant dimension `d - c`, then the
Gysin map of Stacks 0FF3, graded by codimension, carries the class `[Z] ∈ CH^c(Y)` to the class
`[X ×_Y Z] ∈ CH^c(X)`. -/
theorem codimensionGysin_closedSubschemeClass_of_smooth {d e : ℕ}
    (hX : RelativeDimension sX d) (hY : RelativeDimension sY e) (i : Z ⟶ Y) [IsClosedImmersion i]
    (c : ℤ) [Smooth (i ≫ sY)] {nZ : ℕ} (hZ : RelativeDimension (i ≫ sY) nZ)
    (hnZ : (nZ : ℤ) = e - c) [Smooth (pullback.fst f i ≫ sX)] {nF : ℕ}
    (hF : RelativeDimension (pullback.fst f i ≫ sX) nF) (hnF : (nF : ℤ) = d - c) :
    codimensionGysin sX sY hf c (closedSubschemeClass sY i c) =
      closedSubschemeClass sX (pullback.fst f i) c := by
  funext d'
  rcases eq_or_ne d' d with rfl | hd
  swap
  · have := isEmpty_dimPart_of_ne sX hX hd
    have := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k) (partBase sX d')
      ((d' : ℤ) - c)
    exact Subsingleton.elim _ _
  refine (chowGroupDimPartPieceEquiv sX sY (f := f) d' ((d' : ℤ) - c)).injective
    (funext fun e' ↦ ?_)
  obtain ⟨e'⟩ := e'
  rw [chowGroupDimPartPieceEquiv_apply, chowGroupDimPartPieceEquiv_apply,
    chowGroupRestrict_codimensionGysin]
  rcases eq_or_ne e' e with rfl | he
  swap
  · have hemp := isEmpty_dimPart_of_ne sY hY he
    have : IsEmpty (dimPartPiece sX sY f d' e').toScheme :=
      ⟨fun w ↦ hemp.false ⟨_, w.2⟩⟩
    have := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k)
      (dimPartPieceBase sX sY f d' e') ((d' : ℤ) - c)
    exact Subsingleton.elim _ _
  -- notation
  set ιY := (dimPart sY e').ι with hιY
  set h := pullback.snd i ιY with hh
  set h' := bivariantBaseChangeMap f ιY h with hh'
  have : IsClosedImmersion h' :=
    MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap f ιY h)
      (P := @IsClosedImmersion) inferInstance
  have hqZ : (h ≫ ιY) ≫ sY = pullback.fst i ιY ≫ i ≫ sY := by
    rw [Category.assoc, ← pullback.condition_assoc]
  have hZe : RelativeDimension (pullback.fst i ιY ≫ i ≫ sY) nZ :=
    RelativeDimension.comp_isOpenImmersion _ _ hZ
  -- `X ×_Y Z_e` has the expected dimension, being open in `X ×_Y Z`
  have hdim : ∀ ξ : (pullback f (h ≫ ιY) : Scheme.{u}),
      relativeDimension (fieldChowSituation k).dimensionFunction (pullback.fst f (h ≫ ιY) ≫ sX) ξ ≤
        ((e' : ℤ) - c) - ((e' : ℤ) - d') := by
    intro ξ
    have hE : pullback.fst f (h ≫ ιY) = (pullbackFstPullbackFstIso (f := f) i ιY).inv ≫
        pullback.fst (pullback.fst f i) (pullback.fst f ιY) ≫ pullback.fst f i := by
      rw [Iso.eq_inv_comp]
      exact pullback.lift_fst _ _ _
    rw [hE, Category.assoc, Category.assoc, relativeDimension_comp_isOpenImmersion,
      relativeDimension_comp_isOpenImmersion]
    refine (relativeDimension_le_of_schemeDeltaDimension_le' _ _
      (schemeDeltaDimension_le_of_relativeDimension _ hF) _).trans ?_
    omega
  -- the left side: `f^!` on the piece is the cap of `f^!` at `Y_e`, restricted to the piece
  have hL := dimPartPieceGysinClass_capTarget_heq sX sY hf d' e' ((e' : ℤ) - c)
    (closedSubschemeClass sY i c e')
  rw [closedSubschemeClass_apply, chowGroupRestrict_mk_cycleAssociatedToClosedSubscheme] at hL
  have hcap := smoothGysinClass_cap_mk_cycleAssociatedToClosedSubscheme sX sY hf hX hY ιY h hqZ
    hZe hnZ hdim
  have hL' := hL.trans (heq_of_eq (congrArg (chowGroupRestrict (fieldChowSituation k)
    (pullback.fst f (dimPart sY e').ι ≫ sX) (dimPartPieceBase sX sY f d' e')
    (dimPartPieceToPullback sX sY f d' e') (dimPartPieceToPullback_comp_base sX sY f d' e')
    (((e' : ℤ) - c) - ((e' : ℤ) - d'))) hcap))
  have hLHS : dimPartPieceGysin sX sY hf d' e' c (closedSubschemeClass sY i c e') ≍
      chowGroupRestrict (fieldChowSituation k) (pullback.fst f ιY ≫ sX)
        (dimPartPieceBase sX sY f d' e') (dimPartPieceToPullback sX sY f d' e')
        (dimPartPieceToPullback_comp_base sX sY f d' e') (((e' : ℤ) - c) - ((e' : ℤ) - d'))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (pullback.fst f ιY ≫ sX) h' (((e' : ℤ) - c) - ((e' : ℤ) - d')))) := by
    refine (chowGroupDegreeEquiv_heq _ _ _ _).trans ?_
    rw [closedSubschemeClass_apply, chowGroupRestrict_mk_cycleAssociatedToClosedSubscheme]
    exact hL'
  -- the right side: `[X ×_Y Z]` restricted to the piece through `X ×_Y Y_e`
  have hRHS : chowGroupRestrict (fieldChowSituation k) (partBase sX d')
        (dimPartPieceBase sX sY f d' e') (dimPartPiece sX sY f d' e').ι rfl ((d' : ℤ) - c)
        (closedSubschemeClass sX (pullback.fst f i) c d') =
      chowGroupRestrict (fieldChowSituation k) (pullback.fst f ιY ≫ sX)
        (dimPartPieceBase sX sY f d' e') (dimPartPieceToPullback sX sY f d' e')
        (dimPartPieceToPullback_comp_base sX sY f d' e') ((d' : ℤ) - c)
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (pullback.fst f ιY ≫ sX) h' ((d' : ℤ) - c))) := by
    rw [closedSubschemeClass_apply, chowGroupRestrict_comp,
      chowGroupRestrict_congr _ _ _ _ _ _ (dimPartPieceToPullback sX sY f d' e' ≫
        pullback.fst f ιY) (dimPartPieceToPullback_fst sX sY f d' e').symm
        (by rw [Category.assoc]; exact dimPartPieceToPullback_comp_base sX sY f d' e'),
      ← chowGroupRestrict_comp _ sX (pullback.fst f ιY ≫ sX) (pullback.fst f ιY) rfl,
      chowGroupRestrict_mk_cycleAssociatedToClosedSubscheme,
      ← cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ h'
        (pullbackFstPullbackFstIso (f := f) i ιY)
        (pullbackFstPullbackFstIso_hom_bivariantBaseChangeMap i ιY)]
  rw [hRHS]
  refine eq_of_heq (hLHS.trans ?_)
  have key : ∀ n m : ℤ, n = m →
      chowGroupRestrict (fieldChowSituation k) (pullback.fst f ιY ≫ sX)
        (dimPartPieceBase sX sY f d' e') (dimPartPieceToPullback sX sY f d' e')
        (dimPartPieceToPullback_comp_base sX sY f d' e') n
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (pullback.fst f ιY ≫ sX) h' n)) ≍
      chowGroupRestrict (fieldChowSituation k) (pullback.fst f ιY ≫ sX)
        (dimPartPieceBase sX sY f d' e') (dimPartPieceToPullback sX sY f d' e')
        (dimPartPieceToPullback_comp_base sX sY f d' e') m
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (pullback.fst f ιY ≫ sX) h' m)) := by
    intro n m hnm
    subst hnm
    rfl
  exact key _ _ (by ring)

end Transversal

end Stacks.Chow

/-! ### The pullback of the diagonal along a product of two morphisms -/

namespace Stacks.WeilCohomology

open Stacks.Chow

section Diagonal

variable {S X Y W : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) (sW : W ⟶ S) (φ : Y ⟶ X) (ψ : W ⟶ X)
  (hφ : φ ≫ sX = sY) (hψ : ψ ≫ sX = sW)

/-- The fibre product `Y ×_X W` as a scheme over `Y ×_S W`, `(y, w) ↦ (y, w)`. -/
abbrev pullbackToProd : Limits.pullback φ ψ ⟶ Limits.pullback sY sW :=
  pullback.lift (pullback.fst φ ψ) (pullback.snd φ ψ) (by
    rw [← hφ, ← hψ, pullback.condition_assoc])

/-- **The inverse image of the diagonal `Δ_X` under `φ × ψ : Y ×_S W ⟶ X ×_S X` is `Y ×_X W`**,
embedded in `Y ×_S W` by `(y, w) ↦ (y, w)`. -/
def pullbackDiagonalIso :
    Limits.pullback (prodHom sX sX sY sW φ ψ hφ hψ) (pullback.diagonal sX) ≅
      Limits.pullback φ ψ := by
  have hsnd : pullback.snd (prodHom sX sX sY sW φ ψ hφ hψ) (pullback.diagonal sX) =
      pullback.fst (prodHom sX sX sY sW φ ψ hφ hψ) (pullback.diagonal sX) ≫
        pullback.fst sY sW ≫ φ := by
    have h := congrArg (· ≫ pullback.fst sX sX) (pullback.condition
      (f := prodHom sX sX sY sW φ ψ hφ hψ) (g := pullback.diagonal sX))
    simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, prodHom,
      pullback.lift_fst] at h
    exact h.symm
  have hsnd' : pullback.snd (prodHom sX sX sY sW φ ψ hφ hψ) (pullback.diagonal sX) =
      pullback.fst (prodHom sX sX sY sW φ ψ hφ hψ) (pullback.diagonal sX) ≫
        pullback.snd sY sW ≫ ψ := by
    have h := congrArg (· ≫ pullback.snd sX sX) (pullback.condition
      (f := prodHom sX sX sY sW φ ψ hφ hψ) (g := pullback.diagonal sX))
    simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, prodHom,
      pullback.lift_snd] at h
    exact h.symm
  have hcond : (pullback.fst (prodHom sX sX sY sW φ ψ hφ hψ) (pullback.diagonal sX) ≫
      pullback.fst sY sW) ≫ φ = (pullback.fst (prodHom sX sX sY sW φ ψ hφ hψ)
        (pullback.diagonal sX) ≫ pullback.snd sY sW) ≫ ψ := by
    rw [Category.assoc, Category.assoc, ← hsnd, ← hsnd']
  have hinv : pullbackToProd sX sY sW φ ψ hφ hψ ≫ prodHom sX sX sY sW φ ψ hφ hψ =
      (pullback.fst φ ψ ≫ φ) ≫ pullback.diagonal sX := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.diagonal_fst, Category.comp_id, prodHom,
        pullback.lift_fst, pullback.lift_fst_assoc]
    · rw [Category.assoc, Category.assoc, pullback.diagonal_snd, Category.comp_id, prodHom,
        pullback.lift_snd, pullback.lift_snd_assoc, pullback.condition]
  refine
    { hom := pullback.lift _ _ hcond
      inv := pullback.lift (pullbackToProd sX sY sW φ ψ hφ hψ) (pullback.fst φ ψ ≫ φ) hinv
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst,
          pullback.lift_fst, Category.id_comp]
      · rw [Category.assoc, Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd,
          pullback.lift_snd, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_fst,
        Category.id_comp, hsnd, Category.assoc]
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst,
        Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd,
        Category.id_comp]

/-- The isomorphism `pullbackDiagonalIso` followed by the embedding `pullbackToProd` of
`Y ×_X W` in `Y ×_S W` is the first projection of the inverse image of the diagonal. -/
@[reassoc (attr := simp)]
theorem pullbackDiagonalIso_hom_pullbackToProd :
    (pullbackDiagonalIso sX sY sW φ ψ hφ hψ).hom ≫ pullbackToProd sX sY sW φ ψ hφ hψ =
      pullback.fst _ _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, pullback.lift_snd]
    exact pullback.lift_snd _ _ _

/-- The embedding `pullbackToProd` of `Y ×_X W` in `Y ×_S W` is the inverse of
`pullbackDiagonalIso` followed by the base change of the diagonal of `X` along `φ × ψ`. -/
theorem pullbackToProd_eq :
    pullbackToProd sX sY sW φ ψ hφ hψ =
      (pullbackDiagonalIso sX sY sW φ ψ hφ hψ).inv ≫ pullback.fst _ _ := by
  rw [Iso.eq_inv_comp, pullbackDiagonalIso_hom_pullbackToProd]

/-- If `X` is separated over `S`, then `Y ×_X W ⟶ Y ×_S W` is a closed immersion. -/
instance [IsSeparated sX] : IsClosedImmersion (pullbackToProd sX sY sW φ ψ hφ hψ) := by
  rw [pullbackToProd_eq]
  infer_instance

/-- The graph `Y ⟶ Y ×_S W`, `y ↦ (y, i(y))`, of a morphism `i : Y ⟶ W` over `S`. -/
abbrev graphToProd {S Y W : Scheme.{u}} (sY : Y ⟶ S) (sW : W ⟶ S) (i : Y ⟶ W)
    (hi : i ≫ sW = sY) : Y ⟶ Limits.pullback sY sW :=
  pullback.lift (𝟙 Y) i (by rw [Category.id_comp, hi])

/-- If `pr₁ : Y ×_X W ⟶ Y` is an isomorphism and `φ = i ≫ ψ`, then `Y ×_X W ⊆ Y × W` is the graph
of `i`. -/
theorem pullbackFst_comp_graphToProd {S X Y W : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    (sW : W ⟶ S) (φ : Y ⟶ X) (ψ : W ⟶ X) (hφ : φ ≫ sX = sY) (hψ : ψ ≫ sX = sW) (i : Y ⟶ W)
    (hi : i ≫ sW = sY) (hiψ : i ≫ ψ = φ) [IsIso (pullback.fst φ ψ)] :
    pullback.fst φ ψ ≫ graphToProd sY sW i hi = pullbackToProd sX sY sW φ ψ hφ hψ := by
  have hs : pullback.lift (𝟙 Y) i (by rw [Category.id_comp, hiψ]) = inv (pullback.fst φ ψ) :=
    IsIso.eq_inv_of_inv_hom_id (pullback.lift_fst _ _ _)
  have hsnd : pullback.fst φ ψ ≫ i = pullback.snd φ ψ := by
    have h : inv (pullback.fst φ ψ) ≫ pullback.snd φ ψ = i := by
      rw [← hs, pullback.lift_snd]
    rw [← h, IsIso.hom_inv_id_assoc]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.comp_id, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, hsnd, pullback.lift_snd]

/-- If `W` is separated over `S`, then the graph `Y ⟶ Y ×_S W` of a morphism `Y ⟶ W` over `S`
is a closed immersion. -/
instance {S Y W : Scheme.{u}} (sY : Y ⟶ S) (sW : W ⟶ S) [IsSeparated sW] (i : Y ⟶ W)
    (hi : i ≫ sW = sY) : IsClosedImmersion (graphToProd sY sW i hi) := by
  have h := pullbackFst_comp_graphToProd sW sY sW i (𝟙 W) hi (Category.id_comp _) i hi
    (Category.comp_id _)
  rw [show graphToProd sY sW i hi = inv (pullback.fst i (𝟙 W)) ≫
      pullbackToProd sW sY sW i (𝟙 W) hi (Category.id_comp _) by
    rw [← h, IsIso.inv_hom_id_assoc]]
  infer_instance

end Diagonal

section DiagonalGysin

variable {k : Type u} [Field k] {X Y W : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [Smooth sX] [IsSeparated sX] (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sY]
  (sW : W ⟶ (fieldChowSituation k).S) [Smooth sW] (φ : Y ⟶ X) (ψ : W ⟶ X)
  (hφ : φ ≫ sX = sY) (hψ : ψ ≫ sX = sW)

/-- The product `φ × ψ : Y × W ⟶ X × X` of morphisms of schemes locally of finite type over `k`
is locally of finite type. -/
instance : LocallyOfFiniteType (prodHom sX sX sY sW φ ψ hφ hψ) := by
  have : LocallyOfFiniteType (prodHom sX sX sY sW φ ψ hφ hψ ≫ prodBase sX sX) := by
    rw [prodHom_comp_prodBase]
    infer_instance
  exact LocallyOfFiniteType.of_comp this

/-- Relative dimension along an equality of morphisms. -/
theorem relativeDimension_congr {A B : Scheme.{u}} {p q : A ⟶ B} [LocallyOfFiniteType p]
    [LocallyOfFiniteType q] (h : p = q) {n : ℕ} (hp : RelativeDimension p n) :
    RelativeDimension q n := by
  subst h
  exact hp

/-- **`(φ × ψ)^![Δ_X] = [Y ×_X W]`.** For morphisms `φ : Y ⟶ X`, `ψ : W ⟶ X` of schemes smooth
over `k`, of constant dimensions `a`, `b` and `d`, if `Y ×_X W` is smooth over `k` of constant
dimension `n = a + b - d`, then the Gysin map of `φ × ψ : Y × W ⟶ X × X` carries the class of the
diagonal `[Δ_X] ∈ CH^d(X × X)` to the class of `Y ×_X W ⊆ Y × W`. For `ψ = 𝟙` this is the
class of the graph of `φ`. -/
theorem codimensionGysin_prodHom_diagonal {a b d n : ℕ} (hY : RelativeDimension sY a)
    (hW : RelativeDimension sW b) (hX : RelativeDimension sX d)
    [Smooth (pullback.fst φ ψ ≫ sY)] (hF : RelativeDimension (pullback.fst φ ψ ≫ sY) n)
    (hn : n + d = a + b) :
    codimensionGysin (prodBase sY sW) (prodBase sX sX)
        (prodHom_comp_prodBase sX sX sY sW φ ψ hφ hψ) d
        (closedSubschemeClass (prodBase sX sX) (pullback.diagonal sX) d) =
      closedSubschemeClass (prodBase sY sW) (pullbackToProd sX sY sW φ ψ hφ hψ) d := by
  set E := pullbackDiagonalIso sX sY sW φ ψ hφ hψ
  have hE1 : E.hom ≫ pullback.fst φ ψ =
      pullback.fst (prodHom sX sX sY sW φ ψ hφ hψ) (pullback.diagonal sX) ≫ pullback.fst sY sW :=
    pullback.lift_fst _ _ _
  have hE : pullback.fst (prodHom sX sX sY sW φ ψ hφ hψ) (pullback.diagonal sX) ≫
      prodBase sY sW = E.hom ≫ pullback.fst φ ψ ≫ sY := by
    rw [← Category.assoc E.hom, hE1, Category.assoc]
  have hΔ : pullback.diagonal sX ≫ prodBase sX sX = sX := pullback.diagonal_fst_assoc _ _
  have : Smooth (pullback.diagonal sX ≫ prodBase sX sX) := by
    rw [hΔ]
    infer_instance
  have : Smooth (pullback.fst (prodHom sX sX sY sW φ ψ hφ hψ) (pullback.diagonal sX) ≫
      prodBase sY sW) := by
    rw [hE]
    infer_instance
  rw [codimensionGysin_closedSubschemeClass_of_smooth (prodBase sY sW) (prodBase sX sX)
      (prodHom_comp_prodBase sX sX sY sW φ ψ hφ hψ) (relativeDimension_prodBase k sY sW hY hW)
      (relativeDimension_prodBase k sX sX hX hX) (pullback.diagonal sX) d
      (relativeDimension_congr hΔ.symm hX) (by push_cast; ring)
      (relativeDimension_congr hE.symm (RelativeDimension.comp_isOpenImmersion _ _ hF))
      (by push_cast; omega)]
  funext e
  rw [closedSubschemeClass_apply, closedSubschemeClass_apply,
    cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _ E
      (pullbackDiagonalIso_hom_pullbackToProd sX sY sW φ ψ hφ hψ)]

/-- The inverse image of the diagonal of `X` is the graph of `i : Y ⟶ W` when
`pr₁ : Y ×_X W ⟶ Y` is an isomorphism and `φ = i ≫ ψ`. -/
private theorem codimensionGysin_prodHom_diagonal_of_isIso_fst [IsSeparated sW] (i : Y ⟶ W)
    (hi : i ≫ sW = sY) (hiψ : i ≫ ψ = φ) [IsIso (pullback.fst φ ψ)] {a d : ℕ}
    (hY : RelativeDimension sY a) (hW : RelativeDimension sW d) (hX : RelativeDimension sX d) :
    codimensionGysin (prodBase sY sW) (prodBase sX sX)
        (prodHom_comp_prodBase sX sX sY sW φ ψ hφ hψ) d
        (closedSubschemeClass (prodBase sX sX) (pullback.diagonal sX) d) =
      closedSubschemeClass (prodBase sY sW) (graphToProd sY sW i hi) d := by
  have : Smooth (pullback.fst φ ψ ≫ sY) := inferInstance
  rw [codimensionGysin_prodHom_diagonal sX sY sW φ ψ hφ hψ hY hW hX
    (RelativeDimension.comp_isOpenImmersion _ _ hY) (by omega)]
  funext e
  rw [closedSubschemeClass_apply, closedSubschemeClass_apply,
    cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ (graphToProd sY sW i hi)
      (asIso (pullback.fst φ ψ))]
  exact pullbackFst_comp_graphToProd sX sY sW φ ψ hφ hψ i hi hiψ

/-- **The graph of `i : Y ⟶ W` is the inverse image of the diagonal of `W`**, on Chow groups:
`(i × 1)^![Δ_W] = [Γ_i]` in `CH^d(Y × W)`, for `Y`, `W` smooth over `k` of constant dimensions
`a`, `d`. -/
theorem codimensionGysin_prodHom_id_diagonal [IsSeparated sW] (i : Y ⟶ W) (hi : i ≫ sW = sY)
    {a d : ℕ} (hY : RelativeDimension sY a) (hW : RelativeDimension sW d) :
    codimensionGysin (prodBase sY sW) (prodBase sW sW)
        (prodHom_comp_prodBase sW sW sY sW i (𝟙 W) hi (Category.id_comp _)) d
        (closedSubschemeClass (prodBase sW sW) (pullback.diagonal sW) d) =
      closedSubschemeClass (prodBase sY sW) (graphToProd sY sW i hi) d :=
  codimensionGysin_prodHom_diagonal_of_isIso_fst sW sY sW i (𝟙 W) hi (Category.id_comp _) i hi
    (Category.comp_id _) hY hW hW

/-- **`(iψ × ψ)^![Δ_X] = [Γ_i]`** when `ψ : W ⟶ X` is an isomorphism over the image of `i`, in the
sense that `pr₁ : Y ×_X W ⟶ Y` (for the map `i ≫ ψ`) is an isomorphism. Together with
`Stacks.WeilCohomology.codimensionGysin_prodHom_id_diagonal` this says that the diagonals of `W`
and of `X` have the same inverse image in `Y × W`. -/
theorem codimensionGysin_prodHom_diagonal_of_isIso [IsSeparated sW] (i : Y ⟶ W) (ψ : W ⟶ X)
    (hi : i ≫ sW = sY) (hψ : ψ ≫ sX = sW) [IsIso (pullback.fst (i ≫ ψ) ψ)] {a d : ℕ}
    (hY : RelativeDimension sY a) (hW : RelativeDimension sW d) (hX : RelativeDimension sX d) :
    codimensionGysin (prodBase sY sW) (prodBase sX sX)
        (prodHom_comp_prodBase sX sX sY sW (i ≫ ψ) ψ (by rw [Category.assoc, hψ, hi]) hψ) d
        (closedSubschemeClass (prodBase sX sX) (pullback.diagonal sX) d) =
      closedSubschemeClass (prodBase sY sW) (graphToProd sY sW i hi) d :=
  codimensionGysin_prodHom_diagonal_of_isIso_fst sX sY sW (i ≫ ψ) ψ _ hψ i hi rfl hY hW hX

end DiagonalGysin

end Stacks.WeilCohomology

end
