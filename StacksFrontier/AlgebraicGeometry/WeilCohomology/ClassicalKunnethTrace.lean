module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.PreconnectedRelativeDimension
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalChowCycleData
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalTraceDegree
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalTraceProduct
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ClosedImmersionClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionGysinFlat
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionIntersectionUnit
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalDiagonalFlat
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalTheoryChow

/-!
# The trace map of a product in a classical Weil cohomology theory

Let `H^*` be a classical Weil cohomology theory over an algebraically closed field `k`, with cycle
class maps on the Chow groups of Chapter 42
(`Stacks.WeilCohomology.ChowClassicalWeilCohomologyTheory`), and let `X` and `Y` be smooth
projective varieties. Stacks 0FGX asserts `∫_{X × Y} = ∫_X ⊗ ∫_Y`. Here `X × Y` is any smooth
projective variety `P` with projections `p`, `q` exhibiting it as the fibre product of `X` and
`Y` over `k`, as in the Künneth axiom.

The top pieces `H^{2 dim X}(X)` and `H^{2 dim Y}(Y)` are lines, so the identity needs checking on
one pair of classes
(`Stacks.WeilCohomology.PoincareDualityPushforwardSetup.integration_mul_pullback_of_eq_one`). For a
`k`-point `x` of `X` the class `γ([x])` has trace `1`, and the fibre `x × Y` of `p`, the image of
the section `i : Y ⟶ P`, `y ↦ (x, y)`, computes `∫_P p^*γ([x]) ∪ q^*v = ∫_Y v`:
`p^*γ([x]) = γ(p^![x])` by axiom `(C)(a)`, `p^![x] = i_*[Y]` in `CH^*(P)` because `p` is flat
and `p⁻¹(x) = x × Y`, `γ(i_*[Y]) = i_*γ([Y]) = i_*1` by axiom `(C)(b)` and `γ([Y]) = 1`, and
`∫_P q^*v ∪ i_*1 = ∫_Y i^*q^*v = ∫_Y v` by the trace equation defining `i_*`.

## Main results

* `Stacks.WeilCohomology.SmoothProjective.nonempty_hom_point`: a smooth projective variety over an
  algebraically closed field has a `k`-point.
* `Stacks.WeilCohomology.SmoothProjective.isNonemptyEquidimensional`: a smooth projective variety
  of dimension `d` is nonempty and equidimensional of dimension `d`.
* `Stacks.WeilCohomology.SmoothProjective.gysin_pushforward_point`: the Chow identity
  `p^![x] = i_*[Y]` of the fibre of a projection over a point.
* `Stacks.WeilCohomology.ChowClassicalWeilCohomologyTheory.cycleClass_fundamental`: `γ([W]) = 1`.
* `Stacks.WeilCohomology.ChowClassicalWeilCohomologyTheory.integration_mul_pullback`:
  Stacks 0FGX, `∫_P p^*a ∪ q^*b = ∫_X a · ∫_Y b` on top classes.
* `Stacks.WeilCohomology.ChowClassicalWeilCohomologyTheory.integration_comp_kunnethMap`:
  Stacks 0FGX as an identity of linear maps `H^*(X) ⊗_F H^*(Y) → F`.

## Implementation notes

The source evaluates on the class `γ([(x, y)])` of a point of `X × Y`, using the Chow identity
`[(x, y)] = pr₁^![x] · pr₂^![y]`. The route through the fibre `x × Y` needs only the Gysin map of
the flat projection `p`, for which the class of an inverse image is computed in Chapter 42, and
no intersection product beyond `[Spec k] · [Spec k] = [Spec k]`.

## References

* [Stacks Project, Tag 0FGX](https://stacks.math.columbia.edu/tag/0FGX)
* [Stacks Project, Tag 0FGW](https://stacks.math.columbia.edu/tag/0FGW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u v w

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

/-! ### Smooth projective varieties -/

namespace SmoothProjective

/-- A smooth projective variety whose underlying space has dimension `d` has relative dimension
`d` over `k`: it is irreducible, so its structure morphism, being smooth, has pure relative
dimension, which is then the dimension of the space. -/
theorem relativeDimension_hom (X : (SmoothProjective k).FullSubcategory) {d : ℕ}
    (hd : topologicalKrullDim X.obj.left = (d : WithBot ℕ∞)) : RelativeDimension X.obj.hom d := by
  obtain ⟨d', hd'⟩ := exists_relativeDimension_of_smooth_of_preconnectedSpace X.obj.hom
  have h := topologicalKrullDim_eq_of_relativeDimension X.obj.hom hd'
  rw [hd] at h
  obtain rfl : d = d' := by exact_mod_cast h
  exact hd'

/-- A smooth projective variety whose underlying space has dimension `d` is nonempty and
equidimensional of dimension `d`. -/
theorem isNonemptyEquidimensional (X : (SmoothProjective k).FullSubcategory) {d : ℕ}
    (hd : topologicalKrullDim X.obj.left = (d : WithBot ℕ∞)) :
    IsNonemptyEquidimensional ((toSchemeCat k).obj X) d :=
  ⟨inferInstanceAs (Nonempty X.obj.left), relativeDimension_hom X hd⟩

/-- **A smooth projective variety over an algebraically closed field has a `k`-point**: a closed
point, which exists as the space is quasi-compact and nonempty, has residue field `k`. -/
theorem nonempty_hom_point [IsAlgClosed k] (X : (SmoothProjective k).FullSubcategory) :
    Nonempty (SmoothProjective.specPoint k ⟶ X) := by
  have : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
  obtain ⟨x, -, hx⟩ := isClosed_univ.exists_closed_singleton
    (Set.univ_nonempty (α := X.obj.left))
  exact ⟨ObjectProperty.homMk (Over.homMk (pointOfClosedPoint X.obj.hom x hx)
    (pointOfClosedPoint_comp X.obj.hom x hx))⟩

/-- A `k`-point of a smooth projective variety is a closed immersion. -/
instance isClosedImmersion_point_hom_left {X : (SmoothProjective k).FullSubcategory}
    (x : SmoothProjective.specPoint k ⟶ X) : IsClosedImmersion x.hom.left :=
  haveI : Subsingleton (Spec (.of k)) := inferInstance
  isClosedImmersion_of_comp_eq_id X.obj.hom x.hom.left (Over.w x.hom)

/-! ### The fibre of a projection over a point -/

/-- The class of a closed subscheme depends only on the closed subscheme: two closed immersions
identified by an isomorphism of their sources have the same class. -/
theorem _root_.Stacks.WeilCohomology.closedSubschemeClass_congr_iso {Y A B : Scheme.{u}}
    (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sY] (jA : A ⟶ Y) [IsClosedImmersion jA]
    (jB : B ⟶ Y) [IsClosedImmersion jB] (e : A ≅ B) (h : e.hom ≫ jB = jA) (c : ℤ) :
    closedSubschemeClass sY jA c = closedSubschemeClass sY jB c := by
  funext d
  simp only [closedSubschemeClass_apply,
    cycleAssociatedToClosedSubscheme_eq_of_iso _ sY jA jB e h]

variable {X Y P : (SmoothProjective k).FullSubcategory} {p : P ⟶ X} {q : P ⟶ Y}
  (hP : IsPullback p.hom.left q.hom.left X.obj.hom Y.obj.hom) (x : SmoothProjective.specPoint k ⟶ X)

/-- **The fibre `x × Y` of `p` over a `k`-point `x` of `X`**, as the section `Y ⟶ P` of `q`
through `x`: the morphism `y ↦ (x, y)`. -/
def fibreSection : Y ⟶ P :=
  ObjectProperty.homMk (Over.homMk (hP.lift (Y.obj.hom ≫ x.hom.left) (𝟙 _)
      (by rw [Category.assoc, Over.w x.hom]; simp))
    (by rw [← Over.w p.hom, hP.lift_fst_assoc, Category.assoc, Over.w x.hom]; simp))

/-- The fibre section is a section of the second projection `q`. -/
@[simp]
theorem fibreSection_left_snd : (fibreSection hP x).hom.left ≫ q.hom.left = 𝟙 _ :=
  hP.lift_snd _ _ _

/-- The fibre section followed by the first projection `p` is the constant morphism to `x`. -/
@[simp]
theorem fibreSection_left_fst :
    (fibreSection hP x).hom.left ≫ p.hom.left = Y.obj.hom ≫ x.hom.left :=
  hP.lift_fst _ _ _

/-- The fibre section is a section of `q` in the category of smooth projective varieties. -/
theorem fibreSection_comp : fibreSection hP x ≫ q = 𝟙 Y := by
  ext
  exact fibreSection_left_snd hP x

/-- The square exhibiting `Y`, through `fibreSection`, as the fibre of `p` over `x`. -/
theorem isPullback_fibreSection :
    IsPullback (fibreSection hP x).hom.left Y.obj.hom p.hom.left x.hom.left := by
  refine IsPullback.of_right (h₁₂ := q.hom.left) (h₂₂ := X.obj.hom) (v₁₃ := Y.obj.hom) ?_
    (fibreSection_left_fst hP x) hP.flip
  rw [fibreSection_left_snd, Over.w x.hom]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- The fibre section `Y ⟶ P` through a `k`-point of `X` is a closed immersion. -/
instance isClosedImmersion_fibreSection : IsClosedImmersion (fibreSection hP x).hom.left :=
  MorphismProperty.of_isPullback (isPullback_fibreSection hP x).flip inferInstance

/-- **The Chow identity of the fibre**: for a `k`-point `x` of `X`, the Gysin pullback along
`p : P ⟶ X` of the class `[x] = x_*[Spec k]` of the point is the class `[x × Y]` of the fibre,
`p^![x] = i_*[Y]` for `i : Y ⟶ P` the section `y ↦ (x, y)`. The projection `p` is flat, so its
Gysin map takes the class of a closed subscheme to the class of its inverse image
(Stacks 0FF4, 02RB), and the inverse image of `x` is `x × Y`. -/
theorem gysin_pushforward_point {dZ dX dY dP : ℕ}
    (hdX : topologicalKrullDim X.obj.left = (dX : WithBot ℕ∞))
    (hdY : topologicalKrullDim Y.obj.left = (dY : WithBot ℕ∞))
    (hdP : topologicalKrullDim P.obj.left = (dP : WithBot ℕ∞)) (hdim : dP = dX + dY)
    (h0 : topologicalKrullDim (SmoothProjective.specPoint k).obj.left = (dZ : WithBot ℕ∞)) :
    (chowCycleData k).gysin p _ ((chowCycleData k).pushforward x dZ dX h0 hdX 0
        ((chowCycleData k).fundamental _)) ≍
      (chowCycleData k).pushforward (fibreSection hP x) dY dP hdY hdP 0
        ((chowCycleData k).fundamental Y) := by
  obtain rfl : dZ = 0 := by
    have h := h0.symm.trans (SmoothProjective.topologicalKrullDim_specPoint k)
    exact_mod_cast h
  have hX := SmoothProjective.isNonemptyEquidimensional X hdX
  have hY := SmoothProjective.isNonemptyEquidimensional Y hdY
  have hPd := SmoothProjective.isNonemptyEquidimensional P hdP
  have hpt := SmoothProjective.isNonemptyEquidimensional (SmoothProjective.specPoint k) h0
  have : IsClosedImmersion ((SmoothProjective.toSchemeCat k).map x).hom.left :=
    inferInstanceAs (IsClosedImmersion x.hom.left)
  have : IsClosedImmersion ((SmoothProjective.toSchemeCat k).map (fibreSection hP x)).hom.left :=
    inferInstanceAs (IsClosedImmersion (fibreSection hP x).hom.left)
  have : Flat p.hom.left := MorphismProperty.of_isPullback hP.flip inferInstance
  have : LocallyOfFiniteType p.hom.left := MorphismProperty.of_isPullback hP.flip inferInstance
  have hrel : RelativeDimension p.hom.left dY :=
    RelativeDimension.of_isPullback hP.flip hY.relativeDimension
  rw [chowCycleData_gysin, chowCycleData_pushforward, chowCycleData_pushforward,
    chowCycleData_fundamental, chowCycleData_fundamental,
    equidimensionalPushforward_fundamentalClass _ hpt hX,
    equidimensionalPushforward_fundamentalClass _ hY hPd]
  refine (heq_of_eq (codimensionGysin_closedSubschemeClass_of_flat P.obj.hom X.obj.hom _
    hPd.relativeDimension hX.relativeDimension hrel (by omega) x.hom.left _ ?_)).trans ?_
  · have : IsIso (x.hom.left ≫ X.obj.hom) := by
      rw [Over.w x.hom]; infer_instance
    refine (schemeDeltaDimension_le_of_relativeDimension (k := k) _
      (relativeDimension_of_isIso (x.hom.left ≫ X.obj.hom))).trans (le_of_eq ?_)
    congr 1
    ring
  · rw [closedSubschemeClass_congr_iso P.obj.hom _ (fibreSection hP x).hom.left
      (isPullback_fibreSection hP x).isoPullback.symm (by simp)]
    exact congr_arg_heq (closedSubschemeClass P.obj.hom (fibreSection hP x).hom.left)
      (by omega)

end SmoothProjective

/-! ### Chow identities of the fundamental class -/

/-- **`[W] · β = β`**: the fundamental class is a unit for the intersection product. -/
theorem chowCycleData_mul_fundamental_left (W : (SmoothProjective k).FullSubcategory) (j : ℤ)
    (β : (chowCycleData k).group W j) :
    (chowCycleData k).mul 0 j ((chowCycleData k).fundamental W) β ≍ β := by
  refine Function.hfunext rfl fun d d' hd ↦ ?_
  cases hd
  exact (heq_of_eq (codimensionIntersectionProduct_fundamentalClass_left
    ((SmoothProjective.toSchemeCat k).obj W) j β d)).trans (chowGroupDegreeEquiv_heq _ _ _ _)

/-- **`p^![Spec k] = [W]`**: the Gysin pullback of the class of the point along the structure
morphism is the fundamental class. -/
theorem chowCycleData_gysin_toPoint (W : (SmoothProjective k).FullSubcategory) :
    (chowCycleData k).gysin (SmoothProjective.toSpecPoint W) 0
        ((chowCycleData k).fundamental (SmoothProjective.specPoint k)) =
      (chowCycleData k).fundamental W :=
  codimensionGysin_fundamentalClass_point
    ((SmoothProjective.toSchemeCat k).map (SmoothProjective.toSpecPoint W))

/-! ### The trace map of a product -/

namespace ChowClassicalWeilCohomologyTheory

variable [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]
  (T : ChowClassicalWeilCohomologyTheory.{u, v, w} k F)

/-- **`γ([Spec k]) = 1`**, from axioms `(C)(c)` and `(C)(d)`: `γ([Spec k])` is idempotent, as
`[Spec k] · [Spec k] = [Spec k]`, and nonzero, as its trace is `1`, in the line
`H^0(Spec k) ≅ F`. -/
theorem cycleClass_fundamental_point :
    T.cycleClass (SmoothProjective.specPoint k) 0
        ((chowCycleData k).fundamental (SmoothProjective.specPoint k)) ≍
      (T.H (SmoothProjective.specPoint k)).one := by
  have h0 := T.dimension_specPoint
  have hmul : T.cycleClass (SmoothProjective.specPoint k) 0
      ((chowCycleData k).fundamental (SmoothProjective.specPoint k)) ≍
      (T.H (SmoothProjective.specPoint k)).mul (2 * 0) (2 * 0)
        (T.cycleClass _ 0 ((chowCycleData k).fundamental _))
        (T.cycleClass _ 0 ((chowCycleData k).fundamental _)) :=
    (T.cycleClass_heq _ (by ring) (chowCycleData_mul_fundamental_left _ 0 _)).symm.trans
      ((heq_of_eq (T.cycleClass_mul _ 0 0 _ _)).trans (by
        simp only [ExternallyGradedAlgebra.evenCup, LinearMap.compr₂_apply]
        exact ExternallyGraded.degreeCast_heq _ _))
  have hnorm := T.integration_cycleClass_fundamental (SmoothProjective.specPoint k) inferInstance h0
  generalize T.cycleClass (SmoothProjective.specPoint k) 0
    ((chowCycleData k).fundamental (SmoothProjective.specPoint k)) = g at hmul hnorm ⊢
  let φ : (T.H (SmoothProjective.specPoint k)).piece (2 * 0) →ₗ[F] F :=
    (T.integration _).toLinearMap ∘ₗ
      ExternallyGraded.degreeCast (R := F) (X := (T.H (SmoothProjective.specPoint k)).piece)
        (show (2 * 0 : ℤ) = 2 * (T.dimension (SmoothProjective.specPoint k) : ℤ) by rw [h0]; rfl)
  have hinj : Function.Injective φ := fun a b hab ↦
    eq_of_heq ((ExternallyGraded.degreeCast_heq _ a).symm.trans
      ((heq_of_eq ((T.integration _).injective hab)).trans (ExternallyGraded.degreeCast_heq _ b)))
  have hφg : φ g = 1 := hnorm
  set one' : (T.H (SmoothProjective.specPoint k)).piece (2 * 0) :=
    ExternallyGraded.degreeCast (R := F) (X := (T.H (SmoothProjective.specPoint k)).piece)
      (show (0 : ℤ) = 2 * 0 by ring) (T.H (SmoothProjective.specPoint k)).one with hone'
  have hone : ∀ a : (T.H (SmoothProjective.specPoint k)).piece (2 * 0),
      (T.H (SmoothProjective.specPoint k)).mul _ _ one' a ≍ a := fun a ↦
    (ExternallyGradedAlgebra.mul_congr_left_heq (by ring) (ExternallyGraded.degreeCast_heq _ _)
      a).trans ((T.H (SmoothProjective.specPoint k)).one_mul _ a)
  have hz : ∀ {n n' : ℤ}, n = n' →
      ((0 : (T.H (SmoothProjective.specPoint k)).piece n) ≍
        (0 : (T.H (SmoothProjective.specPoint k)).piece n')) := by
    intro n n' h
    subst h
    rfl
  have hφone : φ one' ≠ 0 := by
    intro h
    have h1 : one' = 0 := hinj (by rw [h, map_zero])
    have h2 := hone g
    rw [h1, map_zero, LinearMap.zero_apply] at h2
    have hg : g = 0 := eq_of_heq (h2.symm.trans (hz (by ring)))
    rw [hg, map_zero] at hφg
    exact zero_ne_one hφg
  set c := φ g / φ one' with hc
  have hgc : g = c • one' := hinj (by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hφone])
  have hgg : g = c • g := by
    refine eq_of_heq (hmul.trans ?_)
    have e1 : (T.H (SmoothProjective.specPoint k)).mul (2 * 0) (2 * 0) g g =
        c • (T.H (SmoothProjective.specPoint k)).mul (2 * 0) (2 * 0) one' g := by
      nth_rw 1 [hgc]
      rw [map_smul, LinearMap.smul_apply]
    rw [e1]
    exact ExternallyGraded.scalar_heq (by ring) rfl (hone g)
  have hc1 : c = 1 := by
    have := congrArg φ hgg
    rw [map_smul, smul_eq_mul, hφg, mul_one] at this
    exact this.symm
  rw [hgc, hc1, one_smul]
  exact ExternallyGraded.degreeCast_heq _ _

/-- **`γ([W]) = 1`** for every smooth projective variety `W`: `[W]` is the Gysin pullback of
`[Spec k]` along the structure morphism, so by axiom `(C)(a)` its class is the pullback of
`γ([Spec k]) = 1`. -/
theorem cycleClass_fundamental (W : (SmoothProjective k).FullSubcategory) :
    T.cycleClass W 0 ((chowCycleData k).fundamental W) ≍ (T.H W).one := by
  rw [← chowCycleData_gysin_toPoint, T.cycleClass_gysin,
    show T.cycleClass (SmoothProjective.specPoint k) 0
        ((chowCycleData k).fundamental (SmoothProjective.specPoint k)) =
      ExternallyGraded.degreeCast (R := F) (X := (T.H _).piece) (show (0 : ℤ) = 2 * 0 by ring)
        (T.H (SmoothProjective.specPoint k)).one from
      eq_of_heq (T.cycleClass_fundamental_point.trans (ExternallyGraded.degreeCast_heq _ _).symm),
    PoincareDualityPushforwardSetup.pullback_degreeCast, T.pullback_one]
  exact ExternallyGraded.degreeCast_heq _ _

variable {X Y P : (SmoothProjective k).FullSubcategory} {p : P ⟶ X} {q : P ⟶ Y}

/-- Cup product respects heterogeneous equality of its right factor. -/
private theorem mul_congr_right_heq {V : (SmoothProjective k).FullSubcategory} (i : ℤ)
    {j j' : ℤ} (h : j = j') (a : (T.H V).piece i) {b : (T.H V).piece j}
    {b' : (T.H V).piece j'} (hb : b ≍ b') : (T.H V).mul i j a b ≍ (T.H V).mul i j' a b' := by
  subst h
  rw [eq_of_heq hb]

/-- Transporting both factors of a product along equalities of degrees does not change the
product, heterogeneously. -/
private theorem mul_degreeCast_degreeCast_heq {V : (SmoothProjective k).FullSubcategory}
    {i i' j j' : ℤ} (hi : i = i') (hj : j = j') (a : (T.H V).piece i) (b : (T.H V).piece j) :
    (T.H V).mul i' j' (ExternallyGraded.degreeCast (R := F) hi a)
      (ExternallyGraded.degreeCast (R := F) hj b) ≍ (T.H V).mul i j a b :=
  (ExternallyGradedAlgebra.mul_congr_left_heq hi.symm (ExternallyGraded.degreeCast_heq _ _) _).trans
    (ExternallyGradedAlgebra.mul_degreeCast_heq _ _ _ _ _ _)

/-- **The trace of `P` against the class of a point of `X`.** Let `x` be a `k`-point of `X` and
`u = γ([x])`. Then `∫_P p^*u ∪ q^*v = ∫_Y v` for every top class `v` of `Y`. Indeed
`p^*γ([x]) = γ(p^![x]) = γ(i_*[Y]) = i_*γ([Y]) = i_*1` for the section `i : Y ⟶ P` through `x`,
by axioms `(C)(a)`, `(C)(b)`, `γ([Y]) = 1` and the Chow identity `p^![x] = i_*[Y]`; and
`∫_P q^*v ∪ i_*1 = ∫_Y i^*q^*v = ∫_Y v` by the trace equation defining `i_*`. -/
theorem integration_mul_pullback_cycleClass_point
    (hP : IsPullback p.hom.left q.hom.left X.obj.hom Y.obj.hom)
    (x : SmoothProjective.specPoint k ⟶ X) (v : (T.H Y).piece (2 * (T.dimension Y : ℤ))) :
    T.integration P (ExternallyGraded.degreeCast (R := F) (X := (T.H P).piece)
        (show 2 * (T.dimension X : ℤ) + 2 * (T.dimension Y : ℤ) = 2 * (T.dimension P : ℤ) by
          rw [T.dimension_eq_add p q hP]; push_cast; ring)
        ((T.H P).mul _ _ (T.pullback p _
          (ExternallyGraded.degreeCast (R := F) (X := (T.H X).piece)
            (show 2 * (0 + (T.dimension X : ℤ) - (T.dimension (SmoothProjective.specPoint k) : ℤ)) =
              2 * (T.dimension X : ℤ) by rw [T.dimension_specPoint]; ring)
            (T.cycleClass X _ ((chowCycleData k).pushforward x _ (T.dimension X) (T.dimension_eq _)
              (T.dimension_eq X) 0 ((chowCycleData k).fundamental _)))))
          (T.pullback q _ v))) =
      T.integration Y v := by
  have hdim := T.dimension_eq_add p q hP
  have h0 := T.dimension_specPoint
  have key := T.integration_pullback_mul (SmoothProjective.fibreSection hP x)
    (2 * (T.dimension Y : ℤ) - 2 * 0)
    (ExternallyGraded.degreeCast (R := F) (X := (T.H P).piece)
      (show 2 * (T.dimension Y : ℤ) = 2 * (T.dimension Y : ℤ) - 2 * 0 by ring) (T.pullback q _ v))
    (ExternallyGraded.degreeCast (R := F) (X := (T.H Y).piece)
      (show 2 * (0 : ℤ) = 2 * (T.dimension Y : ℤ) - (2 * (T.dimension Y : ℤ) - 2 * 0) by ring)
      (T.cycleClass Y 0 ((chowCycleData k).fundamental Y)))
  rw [ExternallyGradedAlgebra.tracePairing_eq_traceExtension,
    ExternallyGradedAlgebra.tracePairing_eq_traceExtension,
    PoincareDualityPushforwardSetup.pullback_degreeCast,
    T.cycleClass_pushforward (SmoothProjective.fibreSection hP x) 0
      ((chowCycleData k).fundamental Y)] at key
  have hiq : T.pullback (SmoothProjective.fibreSection hP x) _
      (T.pullback q (2 * (T.dimension Y : ℤ)) v) = v := by
    rw [← LinearMap.comp_apply, ← T.pullback_comp, SmoothProjective.fibreSection_comp,
      T.pullback_id]
    rfl
  rw [hiq] at key
  refine (ExternallyGradedAlgebra.traceExtension_of_eq (T.H P) (T.dimension P)
    (T.integration P).toLinearMap (by rw [hdim]; push_cast; ring) _).symm.trans ?_
  refine Eq.trans ?_ (ExternallyGradedAlgebra.traceExtension_self (T.H Y) (T.dimension Y)
    (T.integration Y).toLinearMap v)
  refine (ExternallyGradedAlgebra.traceExtension_congr _ _ _
    (by rw [hdim]; push_cast; ring) ?_).trans
      (key.symm.trans (ExternallyGradedAlgebra.traceExtension_congr _ _ _ (by ring) ?_))
  · have hγ := T.cycleClass_heq P (by rw [hdim, h0]; push_cast; ring)
      (SmoothProjective.gysin_pushforward_point hP x (T.dimension_eq X) (T.dimension_eq Y)
        (T.dimension_eq P) hdim (T.dimension_eq _))
    rw [T.cycleClass_gysin] at hγ
    rw [PoincareDualityPushforwardSetup.pullback_degreeCast]
    refine (ExternallyGradedAlgebra.mul_congr_left_heq (by rw [h0]; ring)
      (ExternallyGraded.degreeCast_heq _ _) _).trans ?_
    have hc := (T.gradedComm P).graded_comm _ _ (T.pullback q (2 * (T.dimension Y : ℤ)) v)
      (T.pullback p _ (T.cycleClass X _ ((chowCycleData k).pushforward x _ (T.dimension X)
        (T.dimension_eq _) (T.dimension_eq X) 0 ((chowCycleData k).fundamental _))))
    rw [mul_assoc, DifferentialGraded.gradedSign_two_mul, one_smul] at hc
    refine hc.symm.trans ?_
    refine (T.mul_congr_right_heq _ (by rw [hdim, h0]; push_cast; ring) _ hγ).trans ?_
    exact (T.mul_degreeCast_degreeCast_heq (by ring) (by ring) _ _).symm
  · exact (T.mul_degreeCast_degreeCast_heq (by ring) (by ring) _ _).trans
      ((T.mul_congr_right_heq _ (by ring) _ (T.cycleClass_fundamental Y)).trans
        ((T.H Y).mul_one _ v))

/-- **Stacks Project, Tag 0FGX.** Let `H^*` be a classical Weil cohomology theory and let `X` and
`Y` be smooth projective varieties. Then `∫_{X × Y} = ∫_X ⊗ ∫_Y`: for `P` a fibre product of `X`
and `Y` over `k`, with projections `p` and `q`, and classes `a ∈ H^{2 dim X}(X)`,
`b ∈ H^{2 dim Y}(Y)`, `∫_P p^*a ∪ q^*b = ∫_X a · ∫_Y b`.

The source reads `∫_X ⊗ ∫_Y` through the Künneth isomorphism `H^*(X) ⊗ H^*(Y) ≅ H^*(X × Y)`,
`a ⊗ b ↦ p^*a ∪ q^*b`, on the top piece `H^{2 dim X}(X) ⊗ H^{2 dim Y}(Y)` of
`H^{2(dim X + dim Y)}(X × Y)`, which is this identity. The extension to the other Künneth
components, where `∫_X ⊗ ∫_Y` vanishes, is
`Stacks.WeilCohomology.PoincareDualityPushforwardSetup.traceExtension_mul_pullback`.

As in the source, `H^{2 dim X}(X)` and `H^{2 dim Y}(Y)` are lines, so it suffices to evaluate on
one pair of classes. The proof takes `γ([x])` for a `k`-point `x` of `X` and any class `v` with
`∫_Y v = 1`, and computes `∫_P p^*γ([x]) ∪ q^*v = ∫_Y v` through the fibre `x × Y`
(`integration_mul_pullback_cycleClass_point`); the source instead uses the class
`γ([(x, y)]) = p^*γ([x]) ∪ q^*γ([y])` of a point of `X × Y`. -/
@[stacks 0FGX]
theorem integration_mul_pullback (hP : IsPullback p.hom.left q.hom.left X.obj.hom Y.obj.hom)
    (a : (T.H X).piece (2 * (T.dimension X : ℤ))) (b : (T.H Y).piece (2 * (T.dimension Y : ℤ))) :
    T.integration P (ExternallyGraded.degreeCast (R := F) (X := (T.H P).piece)
        (show 2 * (T.dimension X : ℤ) + 2 * (T.dimension Y : ℤ) = 2 * (T.dimension P : ℤ) by
          rw [T.dimension_eq_add p q hP]; push_cast; ring)
        ((T.H P).mul _ _ (T.pullback p _ a) (T.pullback q _ b))) =
      T.integration X a * T.integration Y b := by
  obtain ⟨x⟩ := SmoothProjective.nonempty_hom_point X
  exact T.integration_mul_pullback_of_eq_one p q (T.dimension_eq_add p q hP) _
    ((T.integration Y).symm 1)
    (T.integration_cycleClass_pushforward_fundamental _ inferInstance T.dimension_specPoint x)
    (by simp) (by rw [T.integration_mul_pullback_cycleClass_point hP x]; simp) a b

/-- **Stacks Project, Tag 0FGX**, as an identity of linear maps
`H^*(X) ⊗_F H^*(Y) → F`. Let `∫_X : H^*(X) → F` be the trace map on the piece of degree
`2 dim X`, extended by zero to the other pieces. Then `∫_{X × Y}`, composed with the Künneth map
`H^*(X) ⊗_F H^*(Y) → H^*(X × Y)`, `a ⊗ b ↦ p^*a ∪ q^*b`, is `∫_X ⊗ ∫_Y`. -/
@[stacks 0FGX "as linear maps on H^*(X) ⊗ H^*(Y), through the Künneth map"]
theorem integration_comp_kunnethMap
    (hP : IsPullback p.hom.left q.hom.left X.obj.hom Y.obj.hom) :
    ((T.integration P).toLinearMap ∘ₗ
        DirectSum.component F ℤ (T.H P).piece (2 * (T.dimension P : ℤ))) ∘ₗ
      kunnethMap (T.H X) (T.H Y) (T.H P) (fun i ↦ T.pullback p i) (fun j ↦ T.pullback q j) =
    TensorProduct.lift ((LinearMap.mul F F).compl₁₂
      ((T.integration X).toLinearMap ∘ₗ
        DirectSum.component F ℤ (T.H X).piece (2 * (T.dimension X : ℤ)))
      ((T.integration Y).toLinearMap ∘ₗ
        DirectSum.component F ℤ (T.H Y).piece (2 * (T.dimension Y : ℤ)))) := by
  refine TensorProduct.ext' fun x y ↦ ?_
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']
  | of i a =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [TensorProduct.tmul_add, map_add, hy, hy']
    | of j b =>
      rw [← DirectSum.lof_eq_of F, ← DirectSum.lof_eq_of F, LinearMap.comp_apply,
        kunnethMap_lof_tmul_lof, TensorProduct.lift.tmul]
      exact T.traceExtension_mul_pullback p q (T.dimension_eq_add p q hP)
        (T.integration_mul_pullback hP) i j a b

end ChowClassicalWeilCohomologyTheory

end Stacks.WeilCohomology

end
