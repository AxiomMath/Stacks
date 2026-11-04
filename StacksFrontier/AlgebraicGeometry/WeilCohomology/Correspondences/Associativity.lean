module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.BasePointComposition
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Composition

/-!
# Associativity of composition of correspondences

Let `k` be a field and let `X`, `Y`, `Z`, `W` be schemes locally of finite type over `k`, of
constant dimensions `d`, `e`, `f`, `g`, with `Y` and `Z` proper. For correspondences
`c ∈ Corrʳ(X, Y)`, `c' ∈ Corrˢ(Y, Z)` and `c'' ∈ Corrᵗ(Z, W)`, Stacks 0FG0 (1) asserts

  `c'' ∘ (c' ∘ c) = (c'' ∘ c') ∘ c`.

The source's proof computes both sides on the fourfold product `X × Y × Z × W`:

  `c'' ∘ (c' ∘ c) = p_{14,*}((p_{12}^* c · p_{23}^* c') · p_{34}^* c'')`,
  `(c'' ∘ c') ∘ c = p_{14,*}(p_{12}^* c · (p_{23}^* c' · p_{34}^* c''))`,

using that flat pullback commutes with proper pushforward in a cartesian square (Stacks 02RG),
that flat pullback is multiplicative (Stacks 0FFB), the projection formula (Stacks 0FFC) and
functoriality of proper pushforward (Stacks 02R5), and concludes by associativity of the
intersection product (Stacks 0FC1).

The intersection products here are those formed with a family of diagonal classes
(`Stacks.WeilCohomology.DiagonalClassFamily`). The three properties of the genuine product the
argument uses are recorded as properties of the family, and associativity of composition is
proved from them.

## Main definitions

* `Stacks.WeilCohomology.quadrupleProduct`: the product `((X ×_S Y) ×_S Z) ×_S W`, with the
  projections `pr₁₂₃`, `pr₁₃₄`, `pr₁₂₄` and `pr₂₃₄` onto the four triple products.
* `Stacks.WeilCohomology.DiagonalClassFamily.FlatPullbackMul`: flat pullback is multiplicative
  for the products formed with the family (Stacks 0FFB for a flat morphism).
* `Stacks.WeilCohomology.DiagonalClassFamily.ProjectionFormula`: the projection formula for a
  flat proper morphism (Stacks 0FFC), on both sides.
* `Stacks.WeilCohomology.DiagonalClassFamily.IntersectionAssoc`: the product is associative
  (Stacks 0FC1 with all four schemes equal).

## Main results

* `Stacks.WeilCohomology.isPullback_pr₁₂₃_pr₁₃₄` and
  `Stacks.WeilCohomology.isPullback_pr₂₃₄_pr₁₂₄`: the two cartesian squares on which Stacks 02RG
  is applied.
* `Stacks.WeilCohomology.compositionInt_assoc`: associativity of composition on integral Chow
  groups.
* `Stacks.WeilCohomology.DiagonalClassFamily.compositionAssoc_of`: associativity of composition
  of rational correspondences, `Stacks.WeilCohomology.DiagonalClassFamily.CompositionAssoc`, for
  every family with the three properties.

## Implementation notes

For a flat morphism `f : W' ⟶ W` of relative dimension `t` between schemes of constant
dimensions `t + N` and `N`, the Gysin map `f^!` of Stacks 0FF3 is flat pullback `f^*`, so
Stacks 0FFB and Stacks 0FFC are stated with `f^*`. Every product, pullback and pushforward
changes the degree by a fixed integer, and the two sides of each identity live in degrees that
are equal integers written differently; they are compared through
`Stacks.Chow.chowGroupDegreeEquiv`.

The projection formula is stated in the source as `p_*(α · p^*β) = p_*α · β`. The computation
of `(c'' ∘ c') ∘ c` uses it with the factors in the other order, `p_*(p^*β · α) = β · p_*α`;
this is the same formula read through the symmetry of the product noted in Section 0FC0, and the
source's proof of Stacks 0FFC proves it verbatim with the two factors exchanged. Both forms are
part of `Stacks.WeilCohomology.DiagonalClassFamily.ProjectionFormula`.

The three properties quantify over all schemes locally of finite type and of constant dimension
over `k`, because `Stacks.WeilCohomology.DiagonalClassFamily.CompositionAssoc` does and the
products of the argument are formed on `X × Y × Z × W` and its projections. The source states
Stacks 0FFB, 0FFC and 0FC1 for schemes smooth over `k`, which covers the case of smooth
projective `X`, `Y`, `Z`, `W` in which correspondences are used.

## References

* [Stacks Project, Tag 0FG0](https://stacks.math.columbia.edu/tag/0FG0)
* [Stacks Project, Tag 0FFB](https://stacks.math.columbia.edu/tag/0FFB)
* [Stacks Project, Tag 0FFC](https://stacks.math.columbia.edu/tag/0FFC)
* [Stacks Project, Tag 0FC1](https://stacks.math.columbia.edu/tag/0FC1)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

/-! ### The fourfold product and its projections -/

section Quadruple

variable {S X Y Z W : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) (sZ : Z ⟶ S) (sW : W ⟶ S)

/-- The fourfold product `((X ×_S Y) ×_S Z) ×_S W`. -/
abbrev quadrupleProduct : Scheme.{u} := pullback (tripleBase sX sY sZ) sW

/-- The structure morphism of the fourfold product. -/
abbrev quadrupleBase : quadrupleProduct sX sY sZ sW ⟶ S :=
  pullback.fst (tripleBase sX sY sZ) sW ≫ tripleBase sX sY sZ

/-- The projection `pr₁₂₃ : X × Y × Z × W ⟶ X × Y × Z`. -/
abbrev pr₁₂₃ : quadrupleProduct sX sY sZ sW ⟶ tripleProduct sX sY sZ :=
  pullback.fst (tripleBase sX sY sZ) sW

/-- The projection `pr₁₃₄ : X × Y × Z × W ⟶ X × Z × W`. -/
def pr₁₃₄ : quadrupleProduct sX sY sZ sW ⟶ tripleProduct sX sZ sW :=
  pullback.lift (pr₁₂₃ sX sY sZ sW ≫ pr₁₃ sX sY sZ) (pullback.snd (tripleBase sX sY sZ) sW)
    (by rw [Category.assoc, pr₁₃_comp_prodBase]; exact pullback.condition)

/-- The projection `pr₁₂₄ : X × Y × Z × W ⟶ X × Y × W`. -/
def pr₁₂₄ : quadrupleProduct sX sY sZ sW ⟶ tripleProduct sX sY sW :=
  pullback.lift (pr₁₂₃ sX sY sZ sW ≫ pr₁₂ sX sY sZ) (pullback.snd (tripleBase sX sY sZ) sW)
    (by rw [Category.assoc, pr₁₂_comp_prodBase]; exact pullback.condition)

/-- The projection `pr₂₃₄ : X × Y × Z × W ⟶ Y × Z × W`. -/
def pr₂₃₄ : quadrupleProduct sX sY sZ sW ⟶ tripleProduct sY sZ sW :=
  pullback.lift (pr₁₂₃ sX sY sZ sW ≫ pr₂₃ sX sY sZ) (pullback.snd (tripleBase sX sY sZ) sW)
    (by rw [Category.assoc, pr₂₃_comp_prodBase]; exact pullback.condition)

/-- The composite of `pr₁₃₄` with the projection `X × Z × W ⟶ X × Z` is the composite of
`pr₁₂₃` with the projection `X × Y × Z ⟶ X × Z`. -/
@[reassoc (attr := simp)]
theorem pr₁₃₄_fst :
    pr₁₃₄ sX sY sZ sW ≫ pr₁₂ sX sZ sW = pr₁₂₃ sX sY sZ sW ≫ pr₁₃ sX sY sZ :=
  pullback.lift_fst _ _ _

/-- The composite of `pr₁₃₄` with the projection `X × Z × W ⟶ W` is the projection
`X × Y × Z × W ⟶ W`. -/
@[reassoc (attr := simp)]
theorem pr₁₃₄_snd :
    pr₁₃₄ sX sY sZ sW ≫ pullback.snd (prodBase sX sZ) sW =
      pullback.snd (tripleBase sX sY sZ) sW :=
  pullback.lift_snd _ _ _

/-- The composite of `pr₁₂₄` with the projection `X × Y × W ⟶ X × Y` is the composite of
`pr₁₂₃` with the projection `X × Y × Z ⟶ X × Y`. -/
@[reassoc (attr := simp)]
theorem pr₁₂₄_fst :
    pr₁₂₄ sX sY sZ sW ≫ pr₁₂ sX sY sW = pr₁₂₃ sX sY sZ sW ≫ pr₁₂ sX sY sZ :=
  pullback.lift_fst _ _ _

/-- The composite of `pr₁₂₄` with the projection `X × Y × W ⟶ W` is the projection
`X × Y × Z × W ⟶ W`. -/
@[reassoc (attr := simp)]
theorem pr₁₂₄_snd :
    pr₁₂₄ sX sY sZ sW ≫ pullback.snd (prodBase sX sY) sW =
      pullback.snd (tripleBase sX sY sZ) sW :=
  pullback.lift_snd _ _ _

/-- The composite of `pr₂₃₄` with the projection `Y × Z × W ⟶ Y × Z` is the composite of
`pr₁₂₃` with the projection `X × Y × Z ⟶ Y × Z`. -/
@[reassoc (attr := simp)]
theorem pr₂₃₄_fst :
    pr₂₃₄ sX sY sZ sW ≫ pr₁₂ sY sZ sW = pr₁₂₃ sX sY sZ sW ≫ pr₂₃ sX sY sZ :=
  pullback.lift_fst _ _ _

/-- The composite of `pr₂₃₄` with the projection `Y × Z × W ⟶ W` is the projection
`X × Y × Z × W ⟶ W`. -/
@[reassoc (attr := simp)]
theorem pr₂₃₄_snd :
    pr₂₃₄ sX sY sZ sW ≫ pullback.snd (prodBase sY sZ) sW =
      pullback.snd (tripleBase sX sY sZ) sW :=
  pullback.lift_snd _ _ _

/-- `pr₁₂₃` commutes with the structure morphisms to `S`. -/
theorem pr₁₂₃_comp_tripleBase :
    pr₁₂₃ sX sY sZ sW ≫ tripleBase sX sY sZ = quadrupleBase sX sY sZ sW :=
  rfl

/-- `pr₁₃₄` commutes with the structure morphisms to `S`. -/
theorem pr₁₃₄_comp_tripleBase :
    pr₁₃₄ sX sY sZ sW ≫ tripleBase sX sZ sW = quadrupleBase sX sY sZ sW := by
  rw [← pr₁₂_comp_prodBase, pr₁₃₄_fst_assoc, pr₁₃_comp_prodBase]

/-- `pr₁₂₄` commutes with the structure morphisms to `S`. -/
theorem pr₁₂₄_comp_tripleBase :
    pr₁₂₄ sX sY sZ sW ≫ tripleBase sX sY sW = quadrupleBase sX sY sZ sW := by
  rw [← pr₁₂_comp_prodBase, pr₁₂₄_fst_assoc, pr₁₂_comp_prodBase]

/-- `pr₂₃₄` commutes with the structure morphisms to `S`. -/
theorem pr₂₃₄_comp_tripleBase :
    pr₂₃₄ sX sY sZ sW ≫ tripleBase sY sZ sW = quadrupleBase sX sY sZ sW := by
  rw [← pr₁₂_comp_prodBase, pr₂₃₄_fst_assoc, pr₂₃_comp_prodBase]

/-- The two ways of projecting `X × Y × Z × W` to `Z × W`, through `X × Z × W` and through
`Y × Z × W`, agree. -/
theorem pr₁₃₄_pr₂₃_eq :
    pr₁₃₄ sX sY sZ sW ≫ pr₂₃ sX sZ sW = pr₂₃₄ sX sY sZ sW ≫ pr₂₃ sY sZ sW := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pr₂₃_fst, pr₁₃₄_fst_assoc, pr₂₃₄_fst_assoc, pr₁₃_snd, pr₂₃_snd]
  · simp only [Category.assoc, pr₂₃_snd, pr₁₃₄_snd, pr₂₃₄_snd]

/-- The two ways of projecting `X × Y × Z × W` to `X × W`, through `X × Z × W` and through
`X × Y × W`, agree. -/
theorem pr₁₃₄_pr₁₃_eq :
    pr₁₃₄ sX sY sZ sW ≫ pr₁₃ sX sZ sW = pr₁₂₄ sX sY sZ sW ≫ pr₁₃ sX sY sW := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pr₁₃_fst, pr₁₃₄_fst_assoc, pr₁₂₄_fst_assoc]
  · simp only [Category.assoc, pr₁₃_snd, pr₁₃₄_snd, pr₁₂₄_snd]

/-- `pr₁₃₄` is the base change of `pr₁₃ : X × Y × Z ⟶ X × Z` along
`pr₁₂ : X × Z × W ⟶ X × Z`. -/
theorem isPullback_pr₁₂₃_pr₁₃₄ :
    IsPullback (pr₁₂₃ sX sY sZ sW) (pr₁₃₄ sX sY sZ sW) (pr₁₃ sX sY sZ) (pr₁₂ sX sZ sW) := by
  refine (IsPullback.of_right (h₁₂ := pullback.snd (prodBase sX sZ) sW) (v₁₃ := sW)
    (h₂₂ := prodBase sX sZ) ?_ (pr₁₃₄_fst sX sY sZ sW) (isPullback_snd_pr₁₂ sX sZ sW)).flip
  rw [pr₁₃₄_snd, pr₁₃_comp_prodBase]
  exact (IsPullback.of_hasPullback (tripleBase sX sY sZ) sW).flip

/-- `pr₁₂₃` is the base change of `pr₂₃ : X × Y × Z ⟶ Y × Z` along
`pr₁₂ : Y × Z × W ⟶ Y × Z`. -/
theorem isPullback_pr₂₃₄_pr₁₂₃ :
    IsPullback (pr₂₃₄ sX sY sZ sW) (pr₁₂₃ sX sY sZ sW) (pr₁₂ sY sZ sW) (pr₂₃ sX sY sZ) := by
  refine IsPullback.of_right (h₁₂ := pullback.snd (prodBase sY sZ) sW) (v₁₃ := sW)
    (h₂₂ := prodBase sY sZ) ?_ (pr₂₃₄_fst sX sY sZ sW) (isPullback_snd_pr₁₂ sY sZ sW)
  rw [pr₂₃₄_snd, pr₂₃_comp_prodBase]
  exact (IsPullback.of_hasPullback (tripleBase sX sY sZ) sW).flip

/-- `pr₁₂₄` is the base change of `pr₁₃ : Y × Z × W ⟶ Y × W` along
`pr₂₃ : X × Y × W ⟶ Y × W`. -/
theorem isPullback_pr₂₃₄_pr₁₂₄ :
    IsPullback (pr₂₃₄ sX sY sZ sW) (pr₁₂₄ sX sY sZ sW) (pr₁₃ sY sZ sW) (pr₂₃ sX sY sW) := by
  refine IsPullback.of_bot (v₂₁ := pr₁₂ sX sY sW) (v₂₂ := pullback.fst sY sW)
    (h₃₁ := pullback.snd sX sY) ?_ ?_ (isPullback_pr₁₂_pr₂₃ sX sY sW).flip
  · rw [pr₁₂₄_fst, pr₁₃_fst]
    exact (isPullback_pr₂₃₄_pr₁₂₃ sX sY sZ sW).paste_vert (isPullback_pr₁₂_pr₂₃ sX sY sZ).flip
  · refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pr₁₃_fst, pr₂₃_fst, pr₂₃₄_fst_assoc, pr₁₂₄_fst_assoc]
    · simp only [Category.assoc, pr₁₃_snd, pr₂₃_snd, pr₂₃₄_snd, pr₁₂₄_snd]

end Quadruple

/-! ### Flatness, properness and relative dimension of the projections -/

section Field

variable (k : Type u) [Field k] {X Y Z W : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)
  (sZ : Z ⟶ (fieldChowSituation k).S) (sW : W ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sX] [Smooth sX] [IsSeparated sX] [LocallyOfFiniteType sY] [Smooth sY]
  [IsSeparated sY]
  [LocallyOfFiniteType sZ] [Smooth sZ] [IsSeparated sZ]
  [LocallyOfFiniteType sW] [Smooth sW] [IsSeparated sW]

/-- The projection `pr₁₃ : X × Y × Z ⟶ X × Z` is locally of finite type. -/
instance : LocallyOfFiniteType (pr₁₃ sX sY sZ) :=
  MorphismProperty.of_isPullback (isPullback_pr₁₂_pr₁₃ sX sY sZ) inferInstance

/-- The projection `pr₁₃ : X × Y × Z ⟶ X × Z` is flat. -/
instance : Flat (pr₁₃ sX sY sZ) :=
  MorphismProperty.of_isPullback (isPullback_pr₁₂_pr₁₃ sX sY sZ) inferInstance

/-- The projection `pr₁₃₄ : X × Y × Z × W ⟶ X × Z × W` is locally of finite type. -/
instance : LocallyOfFiniteType (pr₁₃₄ sX sY sZ sW) :=
  MorphismProperty.of_isPullback (isPullback_pr₁₂₃_pr₁₃₄ sX sY sZ sW) inferInstance

/-- The projection `pr₁₃₄ : X × Y × Z × W ⟶ X × Z × W` is flat. -/
instance : Flat (pr₁₃₄ sX sY sZ sW) :=
  MorphismProperty.of_isPullback (isPullback_pr₁₂₃_pr₁₃₄ sX sY sZ sW) inferInstance

/-- The projection `pr₁₃₄ : X × Y × Z × W ⟶ X × Z × W` is proper when `Y` is proper. -/
instance [IsProper sY] : IsProper (pr₁₃₄ sX sY sZ sW) :=
  MorphismProperty.of_isPullback (isPullback_pr₁₂₃_pr₁₃₄ sX sY sZ sW) inferInstance

/-- The projection `pr₁₂₄ : X × Y × Z × W ⟶ X × Y × W` is locally of finite type. -/
instance : LocallyOfFiniteType (pr₁₂₄ sX sY sZ sW) :=
  MorphismProperty.of_isPullback (isPullback_pr₂₃₄_pr₁₂₄ sX sY sZ sW) inferInstance

/-- The projection `pr₁₂₄ : X × Y × Z × W ⟶ X × Y × W` is flat. -/
instance : Flat (pr₁₂₄ sX sY sZ sW) :=
  MorphismProperty.of_isPullback (isPullback_pr₂₃₄_pr₁₂₄ sX sY sZ sW) inferInstance

/-- The projection `pr₁₂₄ : X × Y × Z × W ⟶ X × Y × W` is proper when `Z` is proper. -/
instance [IsProper sZ] : IsProper (pr₁₂₄ sX sY sZ sW) :=
  MorphismProperty.of_isPullback (isPullback_pr₂₃₄_pr₁₂₄ sX sY sZ sW) inferInstance

/-- The projection `pr₂₃₄ : X × Y × Z × W ⟶ Y × Z × W` is locally of finite type. -/
instance : LocallyOfFiniteType (pr₂₃₄ sX sY sZ sW) :=
  MorphismProperty.of_isPullback (isPullback_pr₂₃₄_pr₁₂₄ sX sY sZ sW).flip inferInstance

/-- The projection `pr₂₃₄ : X × Y × Z × W ⟶ Y × Z × W` is flat. -/
instance : Flat (pr₂₃₄ sX sY sZ sW) :=
  MorphismProperty.of_isPullback (isPullback_pr₂₃₄_pr₁₂₄ sX sY sZ sW).flip inferInstance

omit [LocallyOfFiniteType sX] [Smooth sX] [IsSeparated sX] [Smooth sY] [IsSeparated sY]
    [LocallyOfFiniteType sZ] [Smooth sZ] [IsSeparated sZ] in
/-- `pr₁₃ : X × Y × Z ⟶ X × Z` has relative dimension `e` when `Y` has dimension `e`. -/
theorem relativeDimension_pr₁₃ {e : ℕ} (hY : RelativeDimension sY e) :
    RelativeDimension (pr₁₃ sX sY sZ) e :=
  RelativeDimension.of_isPullback (isPullback_pr₁₂_pr₁₃ sX sY sZ)
    (relativeDimension_fst k sX sY hY)

omit [LocallyOfFiniteType sX] [Smooth sX] [IsSeparated sX] [LocallyOfFiniteType sY] [Smooth sY]
    [IsSeparated sY] [LocallyOfFiniteType sZ] [Smooth sZ] [IsSeparated sZ] [Smooth sW]
    [IsSeparated sW] in
/-- `pr₁₂₃ : X × Y × Z × W ⟶ X × Y × Z` has relative dimension `g` when `W` has dimension
`g`. -/
theorem relativeDimension_pr₁₂₃ {g : ℕ} (hW : RelativeDimension sW g) :
    RelativeDimension (pr₁₂₃ sX sY sZ sW) g :=
  relativeDimension_pr₁₂ k (prodBase sX sY) sZ sW hW

omit [LocallyOfFiniteType sX] [Smooth sX] [IsSeparated sX] [Smooth sY] [IsSeparated sY]
    [LocallyOfFiniteType sZ] [Smooth sZ] [IsSeparated sZ] [LocallyOfFiniteType sW] [Smooth sW]
    [IsSeparated sW] in
/-- `pr₁₃₄ : X × Y × Z × W ⟶ X × Z × W` has relative dimension `e` when `Y` has dimension
`e`. -/
theorem relativeDimension_pr₁₃₄ {e : ℕ} (hY : RelativeDimension sY e) :
    RelativeDimension (pr₁₃₄ sX sY sZ sW) e :=
  RelativeDimension.of_isPullback (isPullback_pr₁₂₃_pr₁₃₄ sX sY sZ sW)
    (relativeDimension_pr₁₃ k sX sY sZ hY)

omit [LocallyOfFiniteType sX] [Smooth sX] [IsSeparated sX] [LocallyOfFiniteType sY] [Smooth sY]
    [IsSeparated sY] [Smooth sZ] [IsSeparated sZ] [LocallyOfFiniteType sW] [Smooth sW]
    [IsSeparated sW] in
/-- `pr₁₂₄ : X × Y × Z × W ⟶ X × Y × W` has relative dimension `f` when `Z` has dimension
`f`. -/
theorem relativeDimension_pr₁₂₄ {f : ℕ} (hZ : RelativeDimension sZ f) :
    RelativeDimension (pr₁₂₄ sX sY sZ sW) f :=
  RelativeDimension.of_isPullback (isPullback_pr₂₃₄_pr₁₂₄ sX sY sZ sW)
    (relativeDimension_pr₁₃ k sY sZ sW hZ)

omit [Smooth sX] [IsSeparated sX] [Smooth sY] [IsSeparated sY] [LocallyOfFiniteType sZ] [Smooth sZ]
    [IsSeparated sZ] [Smooth sW] [IsSeparated sW] in
/-- `pr₂₃₄ : X × Y × Z × W ⟶ Y × Z × W` has relative dimension `d` when `X` has dimension
`d`. -/
theorem relativeDimension_pr₂₃₄ {d : ℕ} (hX : RelativeDimension sX d) :
    RelativeDimension (pr₂₃₄ sX sY sZ sW) d :=
  RelativeDimension.of_isPullback (isPullback_pr₂₃₄_pr₁₂₄ sX sY sZ sW).flip
    (relativeDimension_pr₂₃ k sX sY sW hX)

end Field

/-! ### Three properties of a family of diagonal classes -/

/-- **Flat pullback is multiplicative** (Stacks 0FFB for a flat morphism) for the intersection
products formed with the family `Δ`: for `f : W' ⟶ W` over `k`, flat of relative dimension `t`,
with `W` of dimension `N` and `W'` of dimension `t + N`, and for `a ∈ CH_n(W)`, `b ∈ CH_m(W)`,

  `f^*(a · b) = f^*a · f^*b`  in  `CH_{n+m-N+t}(W') = CH_{(n+t)+(m+t)-(t+N)}(W')`. -/
def DiagonalClassFamily.FlatPullbackMul {k : Type u} [Field k] (Δ : DiagonalClassFamily k) :
    Prop :=
  ∀ {W W' : Scheme.{u}} (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW]
    [Smooth sW] (sW' : W' ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW']
    [Smooth sW']
    (f : W' ⟶ W)
    [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sW = sW') {t N : ℕ}
    (ht : RelativeDimension f t) (hN : RelativeDimension sW N)
    (hN' : RelativeDimension sW' (t + N)) (n m : ℤ)
    (a : chowGroup (fieldChowSituation k) sW n) (b : chowGroup (fieldChowSituation k) sW m),
    chowGroupDegreeEquiv (fieldChowSituation k) sW' (by push_cast; ring)
        (flatPullbackChow (fieldChowSituation k) sW' sW f hf t ht (n + m - N)
          (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
          (selfIntersectionProduct (fieldChowSituation k)
              (fieldChowSituation_dimensionFunction_of_isClosed k)
            (fieldGysinSystem k) sW N (Δ sW N hN) n m a b)) =
      selfIntersectionProduct (fieldChowSituation k)
          (fieldChowSituation_dimensionFunction_of_isClosed k)
        (fieldGysinSystem k) sW' ((t + N : ℕ) : ℤ) (Δ sW' (t + N) hN') (n + t) (m + t)
        (flatPullbackChow (fieldChowSituation k) sW' sW f hf t ht n
          (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) a)
        (flatPullbackChow (fieldChowSituation k) sW' sW f hf t ht m
          (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) b)

/-- **The projection formula** (Stacks 0FFC for a flat proper morphism) for the intersection
products formed with the family `Δ`: for `p : W' ⟶ W` over `k`, proper and flat of relative
dimension `t`, with `W` of dimension `N` and `W'` of dimension `t + N`, and for
`x ∈ CH_n(W')`, `y ∈ CH_m(W)`,

  `p_*(x · p^*y) = p_*x · y`  and  `p_*(p^*y · x) = y · p_*x`  in  `CH_{n+m-N}(W)`.

The second identity is the first with the factors exchanged; see the implementation notes. -/
def DiagonalClassFamily.ProjectionFormula {k : Type u} [Field k] (Δ : DiagonalClassFamily k) :
    Prop :=
  ∀ {W W' : Scheme.{u}} (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW]
    [Smooth sW] (sW' : W' ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW']
    [Smooth sW']
    (p : W' ⟶ W)
    [IsProper p] [Flat p] (hp : p ≫ sW = sW') {t N : ℕ}
    (ht : RelativeDimension p t) (hN : RelativeDimension sW N)
    (hN' : RelativeDimension sW' (t + N)) (n m : ℤ)
    (x : chowGroup (fieldChowSituation k) sW' n) (y : chowGroup (fieldChowSituation k) sW m),
    chowGroupDegreeEquiv (fieldChowSituation k) sW (by push_cast; ring)
        (properChowPushforward (fieldChowSituation k) sW' sW p hp (n + (m + t) - (t + N : ℕ))
          (properPushforwardDescends _ _ _ _ _ _)
          (selfIntersectionProduct (fieldChowSituation k)
              (fieldChowSituation_dimensionFunction_of_isClosed k)
            (fieldGysinSystem k) sW' ((t + N : ℕ) : ℤ) (Δ sW' (t + N) hN') n (m + t) x
            (flatPullbackChow (fieldChowSituation k) sW' sW p hp t ht m
              (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) y))) =
      selfIntersectionProduct (fieldChowSituation k)
          (fieldChowSituation_dimensionFunction_of_isClosed k)
        (fieldGysinSystem k) sW N (Δ sW N hN) n m
        (properChowPushforward (fieldChowSituation k) sW' sW p hp n
          (properPushforwardDescends _ _ _ _ _ _) x) y ∧
    chowGroupDegreeEquiv (fieldChowSituation k) sW (by push_cast; ring)
        (properChowPushforward (fieldChowSituation k) sW' sW p hp (m + t + n - (t + N : ℕ))
          (properPushforwardDescends _ _ _ _ _ _)
          (selfIntersectionProduct (fieldChowSituation k)
              (fieldChowSituation_dimensionFunction_of_isClosed k)
            (fieldGysinSystem k) sW' ((t + N : ℕ) : ℤ) (Δ sW' (t + N) hN') (m + t) n
            (flatPullbackChow (fieldChowSituation k) sW' sW p hp t ht m
              (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) y) x)) =
      selfIntersectionProduct (fieldChowSituation k)
          (fieldChowSituation_dimensionFunction_of_isClosed k)
        (fieldGysinSystem k) sW N (Δ sW N hN) m n y
        (properChowPushforward (fieldChowSituation k) sW' sW p hp n
          (properPushforwardDescends _ _ _ _ _ _) x)

/-- **Associativity of the intersection product** (Stacks 0FC1 with `Y = Z = W = X`) for the
products formed with the family `Δ`: on a scheme `W` of dimension `N` over `k`, for
`a ∈ CH_n(W)`, `b ∈ CH_m(W)` and `c ∈ CH_l(W)`,

  `(a · b) · c = a · (b · c)`  in  `CH_{n+m+l-2N}(W)`. -/
def DiagonalClassFamily.IntersectionAssoc {k : Type u} [Field k] (Δ : DiagonalClassFamily k) :
    Prop :=
  ∀ {W : Scheme.{u}} (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Smooth sW]
    {N : ℕ}
    (hN : RelativeDimension sW N) (n m l : ℤ) (a : chowGroup (fieldChowSituation k) sW n)
    (b : chowGroup (fieldChowSituation k) sW m) (c : chowGroup (fieldChowSituation k) sW l),
    chowGroupDegreeEquiv (fieldChowSituation k) sW (by ring)
        (selfIntersectionProduct (fieldChowSituation k)
            (fieldChowSituation_dimensionFunction_of_isClosed k)
          (fieldGysinSystem k) sW N (Δ sW N hN) (n + m - N) l
          (selfIntersectionProduct (fieldChowSituation k)
              (fieldChowSituation_dimensionFunction_of_isClosed k)
            (fieldGysinSystem k) sW N (Δ sW N hN) n m a b) c) =
      selfIntersectionProduct (fieldChowSituation k)
          (fieldChowSituation_dimensionFunction_of_isClosed k)
        (fieldGysinSystem k) sW N (Δ sW N hN) n (m + l - N) a
        (selfIntersectionProduct (fieldChowSituation k)
            (fieldChowSituation_dimensionFunction_of_isClosed k)
          (fieldGysinSystem k) sW N (Δ sW N hN) m l b c)

/-! ### The chain of identities -/

section Chain

variable {k : Type u} [Field k] {Δ : DiagonalClassFamily k}

local notation "𝒞" => fieldChowSituation k

local notation "μ" =>
  selfIntersectionProduct (fieldChowSituation k)
      (fieldChowSituation_dimensionFunction_of_isClosed k)
    (fieldGysinSystem k)

local notation "pb[" sA ", " sB ", " v ", " hv ", " r ", " hr ", " n "]" =>
  flatPullbackChow (fieldChowSituation k) sA sB v hv r hr n
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)

local notation "pf[" sA ", " sB ", " v ", " hv ", " n "]" =>
  properChowPushforward (fieldChowSituation k) sA sB v hv n
    (properPushforwardDescends _ _ _ _ _ _)

/-- Proper pushforward on Chow groups, up to equality of degrees and heterogeneous equality of
the argument. -/
private theorem pf_heq_congr {A B : Scheme.{u}} {sA : A ⟶ (fieldChowSituation k).S}
    [LocallyOfFiniteType sA] {sB : B ⟶ (fieldChowSituation k).S} [LocallyOfFiniteType sB]
    {p : A ⟶ B} [IsProper p] {hp : p ≫ sB = sA} {j j' : ℤ} (hj : j = j')
    {x : chowGroup (fieldChowSituation k) sA j} {x' : chowGroup (fieldChowSituation k) sA j'}
    (hx : x ≍ x') : pf[sA, sB, p, hp, j] x ≍ pf[sA, sB, p, hp, j'] x' :=
  properChowPushforward_heq_congr _ _ _ _ _ hj (properPushforwardDescends _ _ _ _ _ _)
    (properPushforwardDescends _ _ _ _ _ _) _ _ hx

/-- `Stacks.WeilCohomology.DiagonalClassFamily.FlatPullbackMul` up to heterogeneous equality,
with the dimension of the source written freely. -/
theorem DiagonalClassFamily.FlatPullbackMul.heq (hmul : Δ.FlatPullbackMul) {T T' : Scheme.{u}}
    (sT : T ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sT] [Smooth sT]
    (sT' : T' ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sT'] [Smooth sT']
    (φ : T' ⟶ T)
    [LocallyOfFiniteType φ] [Flat φ] (hφ : φ ≫ sT = sT') {t N M : ℕ} (hM : M = t + N)
    (ht : RelativeDimension φ t) (hN : RelativeDimension sT N)
    (hM' : RelativeDimension sT' M) (n m : ℤ)
    (a : chowGroup (fieldChowSituation k) sT n) (b : chowGroup (fieldChowSituation k) sT m) :
    pb[sT', sT, φ, hφ, t, ht, n + m - N] (μ sT N (Δ sT N hN) n m a b) ≍
      μ sT' M (Δ sT' M hM') (n + t) (m + t) (pb[sT', sT, φ, hφ, t, ht, n] a)
        (pb[sT', sT, φ, hφ, t, ht, m] b) := by
  subst hM
  exact (chowGroupDegreeEquiv_heq _ _ _ _).symm.trans
    (heq_of_eq (hmul sT sT' φ hφ ht hN hM' n m a b))

/-- The first identity of `Stacks.WeilCohomology.DiagonalClassFamily.ProjectionFormula` up to
heterogeneous equality, with the dimension of the source written freely. -/
theorem DiagonalClassFamily.ProjectionFormula.heq_right (hproj : Δ.ProjectionFormula)
    {T T' : Scheme.{u}} (sT : T ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sT] [Smooth sT]
    (sT' : T' ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sT'] [Smooth sT']
    (p : T' ⟶ T) [IsProper p]
    [Flat p] (hp : p ≫ sT = sT') {t N M : ℕ} (hM : M = t + N) (ht : RelativeDimension p t)
    (hN : RelativeDimension sT N) (hM' : RelativeDimension sT' M) (n m : ℤ)
    (x : chowGroup (fieldChowSituation k) sT' n) (y : chowGroup (fieldChowSituation k) sT m) :
    μ sT N (Δ sT N hN) n m (pf[sT', sT, p, hp, n] x) y ≍
      pf[sT', sT, p, hp, n + (m + t) - M]
        (μ sT' M (Δ sT' M hM') n (m + t) x (pb[sT', sT, p, hp, t, ht, m] y)) := by
  subst hM
  exact (heq_of_eq (hproj sT sT' p hp ht hN hM' n m x y).1).symm.trans
    (chowGroupDegreeEquiv_heq _ _ _ _)

/-- The second identity of `Stacks.WeilCohomology.DiagonalClassFamily.ProjectionFormula` up to
heterogeneous equality, with the dimension of the source written freely. -/
theorem DiagonalClassFamily.ProjectionFormula.heq_left (hproj : Δ.ProjectionFormula)
    {T T' : Scheme.{u}} (sT : T ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sT] [Smooth sT]
    (sT' : T' ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sT'] [Smooth sT']
    (p : T' ⟶ T) [IsProper p]
    [Flat p] (hp : p ≫ sT = sT') {t N M : ℕ} (hM : M = t + N) (ht : RelativeDimension p t)
    (hN : RelativeDimension sT N) (hM' : RelativeDimension sT' M) (n m : ℤ)
    (x : chowGroup (fieldChowSituation k) sT' n) (y : chowGroup (fieldChowSituation k) sT m) :
    μ sT N (Δ sT N hN) m n y (pf[sT', sT, p, hp, n] x) ≍
      pf[sT', sT, p, hp, m + t + n - M]
        (μ sT' M (Δ sT' M hM') (m + t) n (pb[sT', sT, p, hp, t, ht, m] y) x) := by
  subst hM
  exact (heq_of_eq (hproj sT sT' p hp ht hN hM' n m x y).2).symm.trans
    (chowGroupDegreeEquiv_heq _ _ _ _)

/-- `Stacks.WeilCohomology.DiagonalClassFamily.IntersectionAssoc` up to heterogeneous
equality. -/
theorem DiagonalClassFamily.IntersectionAssoc.heq (hassoc : Δ.IntersectionAssoc)
    {T : Scheme.{u}} (sT : T ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sT] [Smooth sT]
    {N : ℕ}
    (hN : RelativeDimension sT N) (n m l : ℤ) (a : chowGroup (fieldChowSituation k) sT n)
    (b : chowGroup (fieldChowSituation k) sT m) (c : chowGroup (fieldChowSituation k) sT l) :
    μ sT N (Δ sT N hN) (n + m - N) l (μ sT N (Δ sT N hN) n m a b) c ≍
      μ sT N (Δ sT N hN) n (m + l - N) a (μ sT N (Δ sT N hN) m l b c) :=
  (chowGroupDegreeEquiv_heq _ _ _ _).symm.trans (heq_of_eq (hassoc sT hN n m l a b c))

variable (k) {X Y Z W : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)
  (sZ : Z ⟶ (fieldChowSituation k).S) (sW : W ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sX] [Smooth sX] [IsSeparated sX] [LocallyOfFiniteType sY] [Smooth sY]
  [IsSeparated sY]
  [LocallyOfFiniteType sZ] [Smooth sZ] [IsSeparated sZ]
  [LocallyOfFiniteType sW] [Smooth sW] [IsSeparated sW]

omit [IsSeparated sX] [IsSeparated sY] [IsSeparated sZ] in
variable (Δ) in
/-- Composition of correspondences, unfolded: `c' ∘ c = pr₁₃,*(pr₁₂^* c · pr₂₃^* c')`, up to the
transport of degrees. -/
theorem compositionInt_heq [IsProper sY] {d e f : ℕ} (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) (hZ : RelativeDimension sZ f) (r s : ℤ)
    (c : chowGroup (fieldChowSituation k) (prodBase sX sY) ((e : ℤ) - r))
    (c' : chowGroup (fieldChowSituation k) (prodBase sY sZ) ((f : ℤ) - s)) :
    compositionInt k sX sY sZ Δ hX hY hZ r s c c' ≍
      pf[tripleBase sX sY sZ, prodBase sX sZ, pr₁₃ sX sY sZ, pr₁₃_comp_prodBase sX sY sZ, _]
        (μ (tripleBase sX sY sZ) _ (Δ _ _ (relativeDimension_tripleBase k sX sY sZ hX hY hZ))
          ((e : ℤ) - r + f) ((f : ℤ) - s + d)
          (pb[tripleBase sX sY sZ, prodBase sX sY, pr₁₂ sX sY sZ, pr₁₂_comp_prodBase sX sY sZ,
            f, relativeDimension_pr₁₂ k sX sY sZ hZ, (e : ℤ) - r] c)
          (pb[tripleBase sX sY sZ, prodBase sY sZ, pr₂₃ sX sY sZ, pr₂₃_comp_prodBase sX sY sZ,
            d, relativeDimension_pr₂₃ k sX sY sZ hX, (f : ℤ) - s] c')) :=
  pf_heq_congr (by push_cast; ring) (chowGroupDegreeEquiv_heq _ _ _ _)

omit [Smooth sX] [IsSeparated sX] [Smooth sY] [IsSeparated sY] [Smooth sZ] [IsSeparated sZ]
    [IsSeparated sW] in
/-- **Stacks 02RG on the first square**: `pr₁₂^* pr₁₃,* = pr₁₃₄,* pr₁₂₃^*` from `A_j(X × Y × Z)`
to `A_{j+g}(X × Z × W)`. -/
theorem flatPullbackChow_pr₁₂_properChowPushforward_pr₁₃ [IsProper sY] {g : ℕ}
    (hW : RelativeDimension sW g) (j : ℤ)
    (z : chowGroup (fieldChowSituation k) (tripleBase sX sY sZ) j) :
    pb[tripleBase sX sZ sW, prodBase sX sZ, pr₁₂ sX sZ sW, pr₁₂_comp_prodBase sX sZ sW, g,
        relativeDimension_pr₁₂ k sX sZ sW hW, j]
        (pf[tripleBase sX sY sZ, prodBase sX sZ, pr₁₃ sX sY sZ, pr₁₃_comp_prodBase sX sY sZ, j] z) =
      pf[quadrupleBase sX sY sZ sW, tripleBase sX sZ sW, pr₁₃₄ sX sY sZ sW,
          pr₁₃₄_comp_tripleBase sX sY sZ sW, j + g]
        (pb[quadrupleBase sX sY sZ sW, tripleBase sX sY sZ, pr₁₂₃ sX sY sZ sW,
          pr₁₂₃_comp_tripleBase sX sY sZ sW, g, relativeDimension_pr₁₂₃ k sX sY sZ sW hW, j] z) :=
  flatPullbackChow_properChowPushforward_of_isProper (fieldChowSituation k) _ _ _ _
    (pr₁₃ sX sY sZ) (pr₁₂ sX sZ sW) (pr₁₂₃ sX sY sZ sW) (pr₁₃₄ sX sY sZ sW)
    (isPullback_pr₁₂₃_pr₁₃₄ sX sY sZ sW) _ _ _ g _ j z

omit [Smooth sX] [IsSeparated sX] [Smooth sY] [IsSeparated sY] [Smooth sZ] [IsSeparated sZ]
    [Smooth sW] [IsSeparated sW] in
/-- **Stacks 02RG on the second square**: `pr₂₃^* pr₁₃,* = pr₁₂₄,* pr₂₃₄^*` from
`A_j(Y × Z × W)` to `A_{j+d}(X × Y × W)`. -/
theorem flatPullbackChow_pr₂₃_properChowPushforward_pr₁₃ [IsProper sZ] {d : ℕ}
    (hX : RelativeDimension sX d) (j : ℤ)
    (z : chowGroup (fieldChowSituation k) (tripleBase sY sZ sW) j) :
    pb[tripleBase sX sY sW, prodBase sY sW, pr₂₃ sX sY sW, pr₂₃_comp_prodBase sX sY sW, d,
        relativeDimension_pr₂₃ k sX sY sW hX, j]
        (pf[tripleBase sY sZ sW, prodBase sY sW, pr₁₃ sY sZ sW, pr₁₃_comp_prodBase sY sZ sW, j] z) =
      pf[quadrupleBase sX sY sZ sW, tripleBase sX sY sW, pr₁₂₄ sX sY sZ sW,
          pr₁₂₄_comp_tripleBase sX sY sZ sW, j + d]
        (pb[quadrupleBase sX sY sZ sW, tripleBase sY sZ sW, pr₂₃₄ sX sY sZ sW,
          pr₂₃₄_comp_tripleBase sX sY sZ sW, d, relativeDimension_pr₂₃₄ k sX sY sZ sW hX, j] z) :=
  flatPullbackChow_properChowPushforward_of_isProper (fieldChowSituation k) _ _ _ _
    (pr₁₃ sY sZ sW) (pr₂₃ sX sY sW) (pr₂₃₄ sX sY sZ sW) (pr₁₂₄ sX sY sZ sW)
    (isPullback_pr₂₃₄_pr₁₂₄ sX sY sZ sW) _ _ _ d _ j z

omit [IsSeparated sY] in
/-- **The left bracketing on the fourfold product**: `c'' ∘ (c' ∘ c)` is
`pr₁₃,* pr₁₃₄,*((p₁₂^* c · p₂₃^* c') · p₃₄^* c'')`, where `p₁₂^* c` and `p₂₃^* c'` are pulled
back through `pr₁₂₃` and `p₃₄^* c''` through `pr₁₃₄`. This is the first four steps of the source's
computation: the definition, Stacks 02RG, Stacks 0FFB and Stacks 0FFC. -/
theorem compositionInt_compositionInt_heq_left (hmul : Δ.FlatPullbackMul)
    (hproj : Δ.ProjectionFormula) [IsProper sY] [IsProper sZ] {d e f g : ℕ}
    (hX : RelativeDimension sX d) (hY : RelativeDimension sY e) (hZ : RelativeDimension sZ f)
    (hW : RelativeDimension sW g) (r s t : ℤ)
    (c : chowGroup (fieldChowSituation k) (prodBase sX sY) ((e : ℤ) - r))
    (c' : chowGroup (fieldChowSituation k) (prodBase sY sZ) ((f : ℤ) - s))
    (c'' : chowGroup (fieldChowSituation k) (prodBase sZ sW) ((g : ℤ) - t)) :
    compositionInt k sX sZ sW Δ hX hZ hW (r + s) t
        (compositionInt k sX sY sZ Δ hX hY hZ r s c c') c'' ≍
      pf[tripleBase sX sZ sW, prodBase sX sW, pr₁₃ sX sZ sW, pr₁₃_comp_prodBase sX sZ sW, _]
        (pf[quadrupleBase sX sY sZ sW, tripleBase sX sZ sW, pr₁₃₄ sX sY sZ sW,
          pr₁₃₄_comp_tripleBase sX sY sZ sW, _]
          (μ (quadrupleBase sX sY sZ sW) _ (Δ _ (g + (f + (e + d)))
              (relativeDimension_tripleBase k (prodBase sX sY) sZ sW
                (relativeDimension_prodBase k sX sY hX hY) hZ hW)) _ _
            (μ (quadrupleBase sX sY sZ sW) _ (Δ _ (g + (f + (e + d)))
                (relativeDimension_tripleBase k (prodBase sX sY) sZ sW
                  (relativeDimension_prodBase k sX sY hX hY) hZ hW)) _ _
              (pb[quadrupleBase sX sY sZ sW, tripleBase sX sY sZ, pr₁₂₃ sX sY sZ sW,
                  pr₁₂₃_comp_tripleBase sX sY sZ sW, g, relativeDimension_pr₁₂₃ k sX sY sZ sW hW,
                  (e : ℤ) - r + f]
                (pb[tripleBase sX sY sZ, prodBase sX sY, pr₁₂ sX sY sZ,
                  pr₁₂_comp_prodBase sX sY sZ, f, relativeDimension_pr₁₂ k sX sY sZ hZ,
                  (e : ℤ) - r] c))
              (pb[quadrupleBase sX sY sZ sW, tripleBase sX sY sZ, pr₁₂₃ sX sY sZ sW,
                  pr₁₂₃_comp_tripleBase sX sY sZ sW, g, relativeDimension_pr₁₂₃ k sX sY sZ sW hW,
                  (f : ℤ) - s + d]
                (pb[tripleBase sX sY sZ, prodBase sY sZ, pr₂₃ sX sY sZ,
                  pr₂₃_comp_prodBase sX sY sZ, d, relativeDimension_pr₂₃ k sX sY sZ hX,
                  (f : ℤ) - s] c')))
            (pb[quadrupleBase sX sY sZ sW, tripleBase sX sZ sW, pr₁₃₄ sX sY sZ sW,
                pr₁₃₄_comp_tripleBase sX sY sZ sW, e, relativeDimension_pr₁₃₄ k sX sY sZ sW hY,
                (g : ℤ) - t + d]
              (pb[tripleBase sX sZ sW, prodBase sZ sW, pr₂₃ sX sZ sW,
                pr₂₃_comp_prodBase sX sZ sW, d, relativeDimension_pr₂₃ k sX sZ sW hX,
                (g : ℤ) - t] c'')))) := by
  have hQ := relativeDimension_tripleBase k (prodBase sX sY) sZ sW
    (relativeDimension_prodBase k sX sY hX hY) hZ hW
  have h1 := (flatPullbackChow_heq_congr (fieldChowSituation k) _ _ (pr₁₂ sX sZ sW)
      (pr₁₂ sX sZ sW) (pr₁₂_comp_prodBase sX sZ sW) (pr₁₂_comp_prodBase sX sZ sW) rfl rfl
      (relativeDimension_pr₁₂ k sX sZ sW hW) (relativeDimension_pr₁₂ k sX sZ sW hW)
      (by push_cast; ring) (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) _ _
      (compositionInt_heq k sX sY sZ (Δ := Δ) hX hY hZ r s c c')).trans
    ((heq_of_eq (flatPullbackChow_pr₁₂_properChowPushforward_pr₁₃ k sX sY sZ sW hW _ _)).trans
      (pf_heq_congr (by push_cast; ring)
        (hmul.heq _ _ (pr₁₂₃ sX sY sZ sW) (pr₁₂₃_comp_tripleBase sX sY sZ sW) rfl
          (relativeDimension_pr₁₂₃ k sX sY sZ sW hW)
          (relativeDimension_tripleBase k sX sY sZ hX hY hZ) hQ _ _ _ _)))
  refine (compositionInt_heq k sX sZ sW (Δ := Δ) hX hZ hW (r + s) t _ c'').trans ?_
  refine pf_heq_congr (by push_cast; ring) ?_
  refine (selfIntersectionProduct_heq _ _ _ _ rfl HEq.rfl (by push_cast; ring) rfl h1
    HEq.rfl).trans ?_
  exact hproj.heq_right _ _ (pr₁₃₄ sX sY sZ sW) (pr₁₃₄_comp_tripleBase sX sY sZ sW)
    (by ring) (relativeDimension_pr₁₃₄ k sX sY sZ sW hY)
    (relativeDimension_tripleBase k sX sZ sW hX hZ hW) hQ _ _ _ _

omit [IsSeparated sZ] in
/-- **The right bracketing on the fourfold product**: `(c'' ∘ c') ∘ c` is
`pr₁₃,* pr₁₂₄,*(p₁₂^* c · (p₂₃^* c' · p₃₄^* c''))`, where `p₁₂^* c` is pulled back through
`pr₁₂₄` and `p₂₃^* c'` and `p₃₄^* c''` through `pr₂₃₄`. This is the source's computation for the
other bracketing: the definition, Stacks 02RG, Stacks 0FFB and Stacks 0FFC. -/
theorem compositionInt_compositionInt_heq_right (hmul : Δ.FlatPullbackMul)
    (hproj : Δ.ProjectionFormula) [IsProper sY] [IsProper sZ] {d e f g : ℕ}
    (hX : RelativeDimension sX d) (hY : RelativeDimension sY e) (hZ : RelativeDimension sZ f)
    (hW : RelativeDimension sW g) (r s t : ℤ)
    (c : chowGroup (fieldChowSituation k) (prodBase sX sY) ((e : ℤ) - r))
    (c' : chowGroup (fieldChowSituation k) (prodBase sY sZ) ((f : ℤ) - s))
    (c'' : chowGroup (fieldChowSituation k) (prodBase sZ sW) ((g : ℤ) - t)) :
    compositionInt k sX sY sW Δ hX hY hW r (s + t) c
        (compositionInt k sY sZ sW Δ hY hZ hW s t c' c'') ≍
      pf[tripleBase sX sY sW, prodBase sX sW, pr₁₃ sX sY sW, pr₁₃_comp_prodBase sX sY sW, _]
        (pf[quadrupleBase sX sY sZ sW, tripleBase sX sY sW, pr₁₂₄ sX sY sZ sW,
          pr₁₂₄_comp_tripleBase sX sY sZ sW, _]
          (μ (quadrupleBase sX sY sZ sW) _ (Δ _ (g + (f + (e + d)))
              (relativeDimension_tripleBase k (prodBase sX sY) sZ sW
                (relativeDimension_prodBase k sX sY hX hY) hZ hW)) _ _
            (pb[quadrupleBase sX sY sZ sW, tripleBase sX sY sW, pr₁₂₄ sX sY sZ sW,
                pr₁₂₄_comp_tripleBase sX sY sZ sW, f, relativeDimension_pr₁₂₄ k sX sY sZ sW hZ,
                (e : ℤ) - r + g]
              (pb[tripleBase sX sY sW, prodBase sX sY, pr₁₂ sX sY sW,
                pr₁₂_comp_prodBase sX sY sW, g, relativeDimension_pr₁₂ k sX sY sW hW,
                (e : ℤ) - r] c))
            (μ (quadrupleBase sX sY sZ sW) _ (Δ _ (g + (f + (e + d)))
                (relativeDimension_tripleBase k (prodBase sX sY) sZ sW
                  (relativeDimension_prodBase k sX sY hX hY) hZ hW)) _ _
              (pb[quadrupleBase sX sY sZ sW, tripleBase sY sZ sW, pr₂₃₄ sX sY sZ sW,
                  pr₂₃₄_comp_tripleBase sX sY sZ sW, d, relativeDimension_pr₂₃₄ k sX sY sZ sW hX,
                  (f : ℤ) - s + g]
                (pb[tripleBase sY sZ sW, prodBase sY sZ, pr₁₂ sY sZ sW,
                  pr₁₂_comp_prodBase sY sZ sW, g, relativeDimension_pr₁₂ k sY sZ sW hW,
                  (f : ℤ) - s] c'))
              (pb[quadrupleBase sX sY sZ sW, tripleBase sY sZ sW, pr₂₃₄ sX sY sZ sW,
                  pr₂₃₄_comp_tripleBase sX sY sZ sW, d, relativeDimension_pr₂₃₄ k sX sY sZ sW hX,
                  (g : ℤ) - t + e]
                (pb[tripleBase sY sZ sW, prodBase sZ sW, pr₂₃ sY sZ sW,
                  pr₂₃_comp_prodBase sY sZ sW, e, relativeDimension_pr₂₃ k sY sZ sW hY,
                  (g : ℤ) - t] c''))))) := by
  have hQ := relativeDimension_tripleBase k (prodBase sX sY) sZ sW
    (relativeDimension_prodBase k sX sY hX hY) hZ hW
  have h1 := (flatPullbackChow_heq_congr (fieldChowSituation k) _ _ (pr₂₃ sX sY sW)
      (pr₂₃ sX sY sW) (pr₂₃_comp_prodBase sX sY sW) (pr₂₃_comp_prodBase sX sY sW) rfl rfl
      (relativeDimension_pr₂₃ k sX sY sW hX) (relativeDimension_pr₂₃ k sX sY sW hX)
      (by push_cast; ring) (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) _ _
      (compositionInt_heq k sY sZ sW (Δ := Δ) hY hZ hW s t c' c'')).trans
    ((heq_of_eq (flatPullbackChow_pr₂₃_properChowPushforward_pr₁₃ k sX sY sZ sW hX _ _)).trans
      (pf_heq_congr (by push_cast; ring)
        (hmul.heq _ _ (pr₂₃₄ sX sY sZ sW) (pr₂₃₄_comp_tripleBase sX sY sZ sW) (by ring)
          (relativeDimension_pr₂₃₄ k sX sY sZ sW hX)
          (relativeDimension_tripleBase k sY sZ sW hY hZ hW) hQ _ _ _ _)))
  refine (compositionInt_heq k sX sY sW (Δ := Δ) hX hY hW r (s + t) c _).trans ?_
  refine pf_heq_congr (by push_cast; ring) ?_
  refine (selfIntersectionProduct_heq _ _ _ _ rfl HEq.rfl rfl (by push_cast; ring) HEq.rfl
    h1).trans ?_
  exact hproj.heq_left _ _ (pr₁₂₄ sX sY sZ sW) (pr₁₂₄_comp_tripleBase sX sY sZ sW)
    (by ring) (relativeDimension_pr₁₂₄ k sX sY sZ sW hZ)
    (relativeDimension_tripleBase k sX sY sW hX hY hW) hQ _ _ _ _

/-- **Associativity of composition on integral Chow groups**: for `c ∈ A_{e-r}(X × Y)`,
`c' ∈ A_{f-s}(Y × Z)` and `c'' ∈ A_{g-t}(Z × W)`,

  `c'' ∘ (c' ∘ c) = (c'' ∘ c') ∘ c`  in  `A_{g-(r+s+t)}(X × W)`,

for a family of diagonal classes with the three properties of Stacks 0FFB, 0FFC and 0FC1. -/
theorem compositionInt_assoc (hmul : Δ.FlatPullbackMul) (hproj : Δ.ProjectionFormula)
    (hassoc : Δ.IntersectionAssoc) [IsProper sY] [IsProper sZ] {d e f g : ℕ}
    (hX : RelativeDimension sX d) (hY : RelativeDimension sY e) (hZ : RelativeDimension sZ f)
    (hW : RelativeDimension sW g) (r s t : ℤ)
    (c : chowGroup (fieldChowSituation k) (prodBase sX sY) ((e : ℤ) - r))
    (c' : chowGroup (fieldChowSituation k) (prodBase sY sZ) ((f : ℤ) - s))
    (c'' : chowGroup (fieldChowSituation k) (prodBase sZ sW) ((g : ℤ) - t)) :
    chowGroupDegreeEquiv (fieldChowSituation k) (prodBase sX sW) (by rw [add_assoc])
        (compositionInt k sX sZ sW Δ hX hZ hW (r + s) t
          (compositionInt k sX sY sZ Δ hX hY hZ r s c c') c'') =
      compositionInt k sX sY sW Δ hX hY hW r (s + t) c
        (compositionInt k sY sZ sW Δ hY hZ hW s t c' c'') := by
  have hQ := relativeDimension_tripleBase k (prodBase sX sY) sZ sW
    (relativeDimension_prodBase k sX sY hX hY) hZ hW
  -- the three pullbacks to the fourfold product, computed through either triple product
  have ha := flatPullbackChow_comm_of_comp_eq (fieldChowSituation k) _ _ _ _
    (pr₁₂₃ sX sY sZ sW) (pr₁₂ sX sY sZ) (pr₁₂₄ sX sY sZ sW) (pr₁₂ sX sY sW)
    (pr₁₂₃_comp_tripleBase sX sY sZ sW) (pr₁₂_comp_prodBase sX sY sZ)
    (pr₁₂₄_comp_tripleBase sX sY sZ sW) (pr₁₂_comp_prodBase sX sY sW) g f
    (relativeDimension_pr₁₂₃ k sX sY sZ sW hW) (relativeDimension_pr₁₂ k sX sY sZ hZ)
    (relativeDimension_pr₁₂₄ k sX sY sZ sW hZ) (relativeDimension_pr₁₂ k sX sY sW hW)
    (pr₁₂₄_fst sX sY sZ sW).symm _
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) c
  have hb := flatPullbackChow_comm_of_comp_eq (fieldChowSituation k) _ _ _ _
    (pr₁₂₃ sX sY sZ sW) (pr₂₃ sX sY sZ) (pr₂₃₄ sX sY sZ sW) (pr₁₂ sY sZ sW)
    (pr₁₂₃_comp_tripleBase sX sY sZ sW) (pr₂₃_comp_prodBase sX sY sZ)
    (pr₂₃₄_comp_tripleBase sX sY sZ sW) (pr₁₂_comp_prodBase sY sZ sW) g d
    (relativeDimension_pr₁₂₃ k sX sY sZ sW hW) (relativeDimension_pr₂₃ k sX sY sZ hX)
    (relativeDimension_pr₂₃₄ k sX sY sZ sW hX) (relativeDimension_pr₁₂ k sY sZ sW hW)
    (pr₂₃₄_fst sX sY sZ sW).symm _
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) c'
  have hc := flatPullbackChow_comm_of_comp_eq (fieldChowSituation k) _ _ _ _
    (pr₁₃₄ sX sY sZ sW) (pr₂₃ sX sZ sW) (pr₂₃₄ sX sY sZ sW) (pr₂₃ sY sZ sW)
    (pr₁₃₄_comp_tripleBase sX sY sZ sW) (pr₂₃_comp_prodBase sX sZ sW)
    (pr₂₃₄_comp_tripleBase sX sY sZ sW) (pr₂₃_comp_prodBase sY sZ sW) e d
    (relativeDimension_pr₁₃₄ k sX sY sZ sW hY) (relativeDimension_pr₂₃ k sX sZ sW hX)
    (relativeDimension_pr₂₃₄ k sX sY sZ sW hX) (relativeDimension_pr₂₃ k sY sZ sW hY)
    (pr₁₃₄_pr₂₃_eq sX sY sZ sW) _
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) c''
  rw [chowGroupDegreeEquiv_eq_iff_heq]
  refine (compositionInt_compositionInt_heq_left k sX sY sZ sW hmul hproj hX hY hZ hW r s t c c'
    c'').trans (HEq.trans ?_ (compositionInt_compositionInt_heq_right k sX sY sZ sW hmul hproj
    hX hY hZ hW r s t c c' c'').symm)
  -- Stacks 02R5: both sides are pushforwards along `X × Y × Z × W ⟶ X × W`
  refine (heq_of_eq (properChowPushforward_comp_eq (fieldChowSituation k) _ _ _ _
    (pr₁₃₄ sX sY sZ sW) (pr₁₃ sX sZ sW) (pr₁₂₄ sX sY sZ sW) (pr₁₃ sX sY sW)
    (pr₁₃₄_pr₁₃_eq sX sY sZ sW) (pr₁₃₄_comp_tripleBase sX sY sZ sW)
    (pr₁₃_comp_prodBase sX sZ sW) (pr₁₂₄_comp_tripleBase sX sY sZ sW)
    (pr₁₃_comp_prodBase sX sY sW) _ (properPushforwardDescends _ _ _ _ _ _)
    (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)
    (properPushforwardDescends _ _ _ _ _ _) _)).trans ?_
  refine pf_heq_congr (by push_cast; ring) ?_
  refine pf_heq_congr (by push_cast; ring) ?_
  -- Stacks 0FC1 on the fourfold product
  refine (hassoc.heq _ hQ _ _ _ _ _ _).trans ?_
  exact selfIntersectionProduct_heq _ _ _ _ rfl HEq.rfl (by ring)
    (by push_cast; ring) ha
    (selfIntersectionProduct_heq _ _ _ _ rfl HEq.rfl (by ring) (by ring)
      hb hc)

end Chain

/-! ### Associativity of composition of correspondences -/

/-- **Associativity of composition of correspondences** (the second half of Stacks 0FG0 (1)):
for a family of diagonal classes whose intersection products satisfy Stacks 0FFB for flat
morphisms, the projection formula of Stacks 0FFC for flat proper morphisms, and the associativity
of Stacks 0FC1, composition of correspondences is associative. -/
theorem DiagonalClassFamily.compositionAssoc_of {k : Type u} [Field k] {Δ : DiagonalClassFamily k}
    (hmul : Δ.FlatPullbackMul) (hproj : Δ.ProjectionFormula) (hassoc : Δ.IntersectionAssoc) :
    Δ.CompositionAssoc := by
  intro X Y Z W sX sY sZ sW _ _ _ _ _ _ _ _ _ _ _ _ _ _ d e f g hX hY hZ hW r s t c c' c''
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul q a =>
    induction c' using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    | tmul q' b =>
      induction c'' using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul q'' z =>
        rw [composition_tmul, composition_tmul, composition_tmul, composition_tmul,
          correspondenceCongr_tmul, mul_assoc,
          compositionInt_assoc k sX sY sZ sW hmul hproj hassoc hX hY hZ hW r s t a b z]

end Stacks.WeilCohomology
