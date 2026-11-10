module

public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeProjectionFormulaPointwise
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormula

/-!
# The base-change coherence, discharged

`StacksFrontier/CategoryTheory/Adjunction/BaseChangeProjectionFormulaPointwise.lean` reduces
[Stacks, Tag 08IB] over an affine base to a projection-formula map, on data it does not produce:
three identifications `ι₁`, `ι₂`, `ι₃` of the two endofunctors `Lg ⋙ Rg` and `Lg' ⋙ Rg'` with
tensor products, the compatibility `hcompat` of those identifications with the canonical
comparison `Stacks.CategoryTheory.BaseChange.pullbackPushforwardSquare`, and its counit clause
`hcounit`.  This file produces all five.

## The shape of the argument

Read at an object `E`, `pullbackPushforwardSquare` is the base change morphism of the
*transposed* square followed by the comparison of the two composites
(`pullbackPushforwardSquare_natTrans_app`), so `hcompat` is a statement about the base change map
of the transposed square — and that statement is the diagram of [Stacks, Tag 0B6B], which
`Stacks.AffineProjectionFormula.adjunctionTensorMap_baseChange_square` proves over abstract
adjunctions from the compatibility `Stacks.AffineProjectionFormula.TensorComparisonCompatible`
of the four tensor comparisons around the square alone.

Instantiating that diagram needs a *unit-like* object: one at which the projection-formula map of
`Lg ⊣ Rg` becomes an identification of `Lg ⋙ Rg` with a tensor product.  The object chosen here
is `Lg J`, the image under `Lg` of an object `J` downstairs, and the three identifications are
built from

* the projection-formula map of `Lg ⊣ Rg` at `(Lg J, Rf K)`, which is [Stacks, Tag 08EU] at `g`;
* the projection-formula map of `Lg' ⊣ Rg'` at `(Lf' (Lg J), W)`, which is [Stacks, Tag 08EU]
  at `g'`;
* the base change morphism of the transposed square at `Lg J`, whose invertibility is the Tor
  independence of the geometric statement;
* and **one** trivialization `v : TB(Lf J, K) ⟶ K` of the tensor product by `Lf J`, at the single
  object `K`.

That `Lg J` is the image of an object downstairs is what makes the argument go through with no
further input.  The two trivializations the diagram needs upstairs — one on `A'` at `Lg (Rf K)`
and one on `B'` at `Lg' W` — are both obtained from the single `v` by transport along the
comparisons `αf`, `αg`, `αg'`, which are isomorphisms, and the compatibility of the two
transports is `TensorComparisonCompatible` at `(J, Rf K)`.  **No unit coherence of the comparison
is used**; see the implementation notes.

## Main definitions

All in the namespace `Stacks.CategoryTheory.BaseChange`.

* `unitDescent` — the trivialization `TA(J, Rf K) ⟶ Rf K` obtained from `v` as its transpose
  under `Lf ⊣ Rf`, through the interchanged-order projection-formula map at `(J, K)`.
* `pulledBackUnit` — `v` transported to `TB(Lf J, Lf (Rf K)) ⟶ Lf (Rf K)` along `αf`.
* `sourceUnit`, `sourceTensorMap` — the trivialization on `A'` at `Lg (Rf K)`, and the resulting
  identification `TA(Rg (Lg J), Rf K) ⟶ (Lg ⋙ Rg)(Rf K)`, which is `ι₁` read backwards.
* `targetUnit`, `targetTensorMap` — the trivialization on `B'` at `Lg' W`, and the resulting
  identification `TB(Lf (Rg (Lg J)), W) ⟶ (Lg' ⋙ Rg')(W)`, which is `ι₂` at `W = Lf (Rf K)`
  and `ι₃` at `W = K`, both read backwards.

## Main results

* `pullbackPushforwardSquare_natTrans_app` — the canonical comparison at an object is the base
  change map of the transposed square followed by the comparison of the two composites.  No
  hypothesis.
* `pulledBackUnit_comp_counit` — the clause that makes the counit bookkeeping work: the
  transported trivialization at `Lf (Rf K)`, followed by the counit, is tensoring the counit and
  then `v`.  This is where the definition of `unitDescent` pays: the equation holds **by
  construction**, with no naturality hypothesis on `v`.
* `targetUnit_comp_map_counit` and `targetTensorMap_comp_map_counit` — **`hcounit`**, before and
  after the projection-formula map of `Lg' ⊣ Rg'`.
* `αf'_app_comp_targetUnit` — the two trivializations upstairs agree; this is where
  `TensorComparisonCompatible` is used.
* `αf_app_comp_targetTensorMap` — **`hcompat`**: the comparison `αf` at `(Rg (Lg J), Rf K)`
  followed by the identification upstairs is `Lf` of the identification downstairs followed by
  `pullbackPushforwardSquare`.
* `isIso_sourceTensorMap`, `isIso_targetTensorMap` — the identifications are isomorphisms.
* `pushforward_map_eq_adjunctionTensorMapRight` — **the coherence solved for the pushed-forward
  base change map**: the pointwise, interchanged-order form of
  `Stacks.CategoryTheory.BaseChange.pushforward_map_eq_adjunctionTensorMap`, with `hcompat` and
  `hcounit` discharged.
* `isIso_pushforward_map_of_isIso_adjunctionTensorMapRight` — **the conclusion**: `Rg` applied to
  the base change map at `K` is invertible, with no coherence left to supply.

## Implementation notes

*Why no unit coherence of the comparison is needed, and why that is not obvious.*  The
identification of [Stacks, Tag 08I9] is the projection-formula map at the source complex
`𝒪_{S'}[0]` followed by the **left unit law of `⊗^𝐋` on `S'`**, and its companion at `g'` uses
the left unit law on `X'`.  Comparing the two under `L(f')^*` is precisely the left-unit
coherence of the comparison of [Stacks, Tag 079U], which this library does not prove: its
right-hand form is the hypothesis `hcoh` of
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitObject`, reduced to
K-flat representatives by `…rightUnitorCoherence_of_kFlat` and discharged nowhere.  Running the
diagram of [Stacks, Tag 0B6B] at `E := 𝒪_{S'}[0]`, which is the only route to `hcompat` at those
two isomorphisms, reduces it to exactly that coherence at the one object `Lg^*(Rf_*K)` and no
further; so `hcompat` stated at the two isomorphisms of [Stacks, Tag 08I9] *as that development
builds them* is out of reach here.  It does not have to be reached: `hcompat` is a statement
about three identifications, and any three will do.  Taking the unit-like object upstairs to be
`Lg J` rather than the tensor unit of `A'`, and transporting one trivialization on `B` to both of
the ones needed upstairs along the comparisons, replaces the unit coherence by
`TensorComparisonCompatible`, which *is* a theorem for ringed spaces
(`Stacks.Cohomology.DerivedRelativeCupProduct.derivedPullbackTensorIso_comparison_square`).  The
price is that `A'` and `B'` carry no unit laws at all here, and that the geometric reading of `J`
is `𝒪_S[0]`, not `𝒪_{S'}[0]`.

*Why the counit clause is free.*  `hcounit` compares the identification at `Lf (Rf K)` with the
one at `K` along the counit, so a trivialization natural in the object would discharge it — and
the left unit law of `⊗^𝐋` is natural
(`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso_naturality`).  Nothing that
strong is used.  Only one instance of naturality is needed, at the single morphism
`ε_K : Lf (Rf K) ⟶ K`, and `unitDescent` is *defined* so that the instance holds: it is the
transpose of `v` under `Lf ⊣ Rf`, and
`Stacks.CategoryTheory.BaseChange.map_adjunctionTensorMapRight_comp_counit` says exactly that
transposing it back gives `v` after tensoring the counit.

*Everything is over variables, and every invertibility input is an explicit argument.*  As in
`StacksFrontier/CategoryTheory/Adjunction/BaseChangeProjectionFormula.lean`: in the intended
application the eight functors are total derived functors, which are reducible abbreviations over
localizations, and a goal mentioning several of them at once builds a proof term the kernel
cannot check in its budget.  For the same reason no `IsIso` is left to instance search.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08I9](https://stacks.math.columbia.edu/tag/08I9)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 0B6B](https://stacks.math.columbia.edu/tag/0B6B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.TwoSquare
open scoped CategoryTheory.Prod

namespace Stacks.CategoryTheory.BaseChange

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

/-! ### Invertibility in a bifunctor, with the witness explicit -/

section Aux

variable {C₁ : Type u₁} {C₂ : Type u₂} [Category.{v₁} C₁] [Category.{v₂} C₂]

/-- A bifunctor carries an invertible morphism in its first argument and an identity in its
second to an invertible morphism, with the witness an explicit argument. -/
theorem isIso_bifunctor_map_left (F : C₁ × C₁ ⥤ C₂) {X Y : C₁} (u : X ⟶ Y) (hu : IsIso u)
    (W : C₁) : IsIso (F.map (u ×ₘ 𝟙 W)) := by
  have := hu
  exact (F.mapIso (Iso.prod (asIso u) (Iso.refl W))).isIso_hom

/-- A morphism in one argument of a bifunctor and one in the other commute, taken in the order
"first argument first".  Stated in the form a right-associated composite can be rewritten with,
and `@[reassoc]` so that it applies in the middle of one. -/
@[reassoc]
theorem bifunctorSplitRight (F : C₁ × C₁ ⥤ C₂) {X Y Z W : C₁} (u : X ⟶ Y) (x : Z ⟶ W) :
    F.map (u ×ₘ 𝟙 Z) ≫ F.map (𝟙 Y ×ₘ x) = F.map (u ×ₘ x) := by
  rw [← F.map_comp, prod_comp]
  simp

/-- The same with the two morphisms taken in the other order. -/
@[reassoc]
theorem bifunctorSplitLeft (F : C₁ × C₁ ⥤ C₂) {X Y Z W : C₁} (u : X ⟶ Y) (x : Z ⟶ W) :
    F.map (𝟙 X ×ₘ x) ≫ F.map (u ×ₘ 𝟙 W) = F.map (u ×ₘ x) := by
  rw [← F.map_comp, prod_comp]
  simp

/-- A bifunctor carries a pair of identities to an identity. -/
theorem bifunctorMapProdId (F : C₁ × C₁ ⥤ C₂) (X Y : C₁) :
    F.map (𝟙 X ×ₘ 𝟙 Y) = 𝟙 (F.obj (X, Y)) := by
  rw [← CategoryTheory.prod_id]
  exact F.map_id _

/-- A composite in each argument of a bifunctor splits. -/
@[reassoc]
theorem bifunctorSplitBoth (F : C₁ × C₁ ⥤ C₂) {X Y Y' Z W W' : C₁} (u : X ⟶ Y) (u' : Y ⟶ Y')
    (x : Z ⟶ W) (x' : W ⟶ W') :
    F.map (u ×ₘ x) ≫ F.map (u' ×ₘ x') = F.map ((u ≫ u') ×ₘ (x ≫ x')) := by
  rw [← F.map_comp, prod_comp]

end Aux

section Square

variable {A : Type u₁} {B : Type u₂} {A' : Type u₃} {B' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
  {Lg : A ⥤ A'} {Rg : A' ⥤ A} {Lg' : B ⥤ B'} {Rg' : B' ⥤ B} {Lc : A ⥤ B'}

/-! ### The canonical comparison at an object -/

/-- **The base change 2-square of the transposed square is the base change map of the transposed
square.**  `Stacks.CategoryTheory.BaseChange.transposedTwoSquare` is the mate, under `Lg ⊣ Rg`
and `Lg' ⊣ Rg'`, of the inverse comparison of the two composites; and that is by definition
`Stacks.CategoryTheory.BaseChange.twoSquare` for the square read with `f` horizontal and `g`
vertical. -/
theorem transposedTwoSquare_natTrans_app (adjg : Lg ⊣ Rg) (adjg' : Lg' ⊣ Rg')
    (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc) (W : A') :
    (transposedTwoSquare adjg adjg' eg ef).app W = map adjg adjg' ef eg W :=
  rfl

/-- The comparison of the two composites, read through
`Stacks.AffineProjectionFormula.squareCompositeIso` of the transposed square. -/
theorem squareCompositeIso_inv_app_eq (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc) (E : A) :
    (Stacks.AffineProjectionFormula.squareCompositeIso ef eg).inv.app E =
      (pullbackComparisonIso eg ef).hom.app E :=
  rfl

/-- The inverse comparison of the two composites, read the same way. -/
theorem squareCompositeIso_hom_app_eq (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc) (E : A) :
    (Stacks.AffineProjectionFormula.squareCompositeIso ef eg).hom.app E =
      (pullbackComparisonIso eg ef).inv.app E :=
  rfl

/-- **The canonical comparison at an object.**  `pullbackPushforwardSquare` is a horizontal
pasting, and a horizontal pasting at an object is the second square at the image of the object
followed by the bottom-right functor applied to the first square.  So at `E` the comparison is
the base change map of the transposed square at `Lg E`, followed by `Rg'` of the comparison of
the two composites at `E`. -/
theorem pullbackPushforwardSquare_natTrans_app (adjg : Lg ⊣ Rg) (adjg' : Lg' ⊣ Rg')
    (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc) (E : A) :
    (pullbackPushforwardSquare adjg adjg' eg ef).app E =
      map adjg adjg' ef eg (Lg.obj E) ≫ Rg'.map ((pullbackComparisonIso eg ef).hom.app E) := by
  rw [pullbackPushforwardSquare, TwoSquare.hComp]
  simp only [NatTrans.comp_app, CategoryTheory.Functor.associator_hom_app,
    CategoryTheory.Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  rfl

/-! ### The three identifications -/

/-- **The trivialization carried down to `A`.**  Given a trivialization `v : TB(Lf J, K) ⟶ K` of
the tensor product by `Lf J` at `K`, its transpose under `Lf ⊣ Rf`: the interchanged-order
projection-formula map at `(J, K)` followed by `Rf v`. -/
def unitDescent (adjf : Lf ⊣ Rf) (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (αf : TA ⋙ Lf ⟶ Lf.prod Lf ⋙ TB) (J : A) (K : B) (v : TB.obj (Lf.obj J, K) ⟶ K) :
    TA.obj (J, Rf.obj K) ⟶ Rf.obj K :=
  Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight adjf TA TB αf J K ≫ Rf.map v

/-- **The trivialization transported to `Lf (Rf K)`**: `Lf` of `unitDescent`, read through the
comparison `αf` at `(J, Rf K)`. -/
def pulledBackUnit (adjf : Lf ⊣ Rf) (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (αf : TA ⋙ Lf ⟶ Lf.prod Lf ⋙ TB) (J : A) (K : B) (v : TB.obj (Lf.obj J, K) ⟶ K)
    (hαf : IsIso (αf.app (J, Rf.obj K))) :
    TB.obj (Lf.obj J, Lf.obj (Rf.obj K)) ⟶ Lf.obj (Rf.obj K) :=
  haveI := hαf
  inv (αf.app (J, Rf.obj K)) ≫ Lf.map (unitDescent adjf TA TB αf J K v)

/-- **The trivialization transported to `A'` at `Lg (Rf K)`**: `Lg` of `unitDescent`, read
through the comparison `αg` at `(J, Rf K)`. -/
def sourceUnit (adjf : Lf ⊣ Rf) (TA : A × A ⥤ A) (TB : B × B ⥤ B) (TA' : A' × A' ⥤ A')
    (αf : TA ⋙ Lf ⟶ Lf.prod Lf ⋙ TB) (αg : TA ⋙ Lg ⟶ Lg.prod Lg ⋙ TA') (J : A) (K : B)
    (v : TB.obj (Lf.obj J, K) ⟶ K) (hαg : IsIso (αg.app (J, Rf.obj K))) :
    TA'.obj (Lg.obj J, Lg.obj (Rf.obj K)) ⟶ Lg.obj (Rf.obj K) :=
  haveI := hαg
  inv (αg.app (J, Rf.obj K)) ≫ Lg.map (unitDescent adjf TA TB αf J K v)

/-- **The identification downstairs**, `ι₁` read backwards: the projection-formula map of
`Lg ⊣ Rg` at `(Lg J, Rf K)` followed by `Rg` of the trivialization on `A'`. -/
def sourceTensorMap (adjf : Lf ⊣ Rf) (adjg : Lg ⊣ Rg) (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (TA' : A' × A' ⥤ A') (αf : TA ⋙ Lf ⟶ Lf.prod Lf ⋙ TB)
    (αg : TA ⋙ Lg ⟶ Lg.prod Lg ⋙ TA') (J : A) (K : B) (v : TB.obj (Lf.obj J, K) ⟶ K)
    (hαg : IsIso (αg.app (J, Rf.obj K))) :
    TA.obj (Rg.obj (Lg.obj J), Rf.obj K) ⟶ (Lg ⋙ Rg).obj (Rf.obj K) :=
  CategoryTheory.adjunctionTensorMap adjg TA TA' αg (Lg.obj J) (Rf.obj K) ≫
    Rg.map (sourceUnit adjf TA TB TA' αf αg J K v hαg)

/-- **The trivialization transported to `B'` at `Lg' W`**: the comparison of the two composites
at `J` in the first tensor factor, then the inverse of the comparison `αg'` at `(Lf J, W)`, then
`Lg'` of a trivialization at `W`. -/
def targetUnit (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc) (TB : B × B ⥤ B)
    (TB' : B' × B' ⥤ B') (αg' : TB ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ TB') (J : A) (W : B)
    (w : TB.obj (Lf.obj J, W) ⟶ W) (hαg' : IsIso (αg'.app (Lf.obj J, W))) :
    TB'.obj (Lf'.obj (Lg.obj J), Lg'.obj W) ⟶ Lg'.obj W :=
  haveI := hαg'
  TB'.map ((pullbackComparisonIso eg ef).hom.app J ×ₘ 𝟙 (Lg'.obj W)) ≫
    inv (αg'.app (Lf.obj J, W)) ≫ Lg'.map w

/-- **The identification upstairs**, `ι₂` and `ι₃` read backwards: the base change map of the
transposed square at `Lg J` in the first tensor factor, then the projection-formula map of
`Lg' ⊣ Rg'` at `(Lf' (Lg J), W)`, then `Rg'` of the trivialization on `B'`. -/
def targetTensorMap (adjg : Lg ⊣ Rg) (adjg' : Lg' ⊣ Rg') (eg : Lg ⋙ Lf' ≅ Lc)
    (ef : Lf ⋙ Lg' ≅ Lc) (TB : B × B ⥤ B) (TB' : B' × B' ⥤ B')
    (αg' : TB ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ TB') (J : A) (W : B) (w : TB.obj (Lf.obj J, W) ⟶ W)
    (hαg' : IsIso (αg'.app (Lf.obj J, W))) :
    TB.obj (Lf.obj (Rg.obj (Lg.obj J)), W) ⟶ (Lg' ⋙ Rg').obj W :=
  TB.map (map adjg adjg' ef eg (Lg.obj J) ×ₘ 𝟙 W) ≫
    CategoryTheory.adjunctionTensorMap adjg' TB TB' αg' (Lf'.obj (Lg.obj J)) W ≫
      Rg'.map (targetUnit eg ef TB TB' αg' J W w hαg')

/-! ### The counit clause -/

/-- **The one instance of naturality the counit clause needs, by construction.**  The
trivialization transported to `Lf (Rf K)`, followed by the counit at `K`, is tensoring the counit
into the second factor and then `v`.

No naturality is assumed of `v`: `unitDescent` is the transpose of `v` under `Lf ⊣ Rf`, and
`Stacks.CategoryTheory.BaseChange.map_adjunctionTensorMapRight_comp_counit` is the statement that
transposing it back is `v` after tensoring the counit. -/
theorem pulledBackUnit_comp_counit (adjf : Lf ⊣ Rf) (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (αf : TA ⋙ Lf ⟶ Lf.prod Lf ⋙ TB) (J : A) (K : B) (v : TB.obj (Lf.obj J, K) ⟶ K)
    (hαf : IsIso (αf.app (J, Rf.obj K))) :
    pulledBackUnit adjf TA TB αf J K v hαf ≫ adjf.counit.app K =
      TB.map (𝟙 (Lf.obj J) ×ₘ adjf.counit.app K) ≫ v := by
  have := hαf
  have key : Lf.map (unitDescent adjf TA TB αf J K v) ≫ adjf.counit.app K =
      αf.app (J, Rf.obj K) ≫ TB.map (𝟙 (Lf.obj J) ×ₘ adjf.counit.app K) ≫ v := by
    have hc : Lf.map (Rf.map v) ≫ adjf.counit.app K =
        adjf.counit.app (TB.obj (Lf.obj J, K)) ≫ v := adjf.counit_naturality v
    rw [unitDescent, CategoryTheory.Functor.map_comp, Category.assoc, hc,
      map_adjunctionTensorMapRight_comp_counit_assoc adjf TA TB αf J K v]
  rw [pulledBackUnit, Category.assoc, key, IsIso.inv_hom_id_assoc]

/-- **`hcounit` for the trivializations on `B'`.**  The trivialization at `Lf (Rf K)` followed by
`Lg'` of the counit is tensoring `Lg'` of the counit and then the trivialization at `K`.  The
whole of the proof is naturality of the comparison `αg'` in its second argument together with
`pulledBackUnit_comp_counit`. -/
theorem targetUnit_comp_map_counit (adjf : Lf ⊣ Rf) (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) (TB' : B' × B' ⥤ B')
    (αf : TA ⋙ Lf ⟶ Lf.prod Lf ⋙ TB) (αg' : TB ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ TB') (J : A) (K : B)
    (v : TB.obj (Lf.obj J, K) ⟶ K) (hαf : IsIso (αf.app (J, Rf.obj K)))
    (hαg'₁ : IsIso (αg'.app (Lf.obj J, Lf.obj (Rf.obj K))))
    (hαg'₂ : IsIso (αg'.app (Lf.obj J, K))) :
    targetUnit eg ef TB TB' αg' J (Lf.obj (Rf.obj K))
          (pulledBackUnit adjf TA TB αf J K v hαf) hαg'₁ ≫
        Lg'.map (adjf.counit.app K) =
      TB'.map (𝟙 (Lf'.obj (Lg.obj J)) ×ₘ Lg'.map (adjf.counit.app K)) ≫
        targetUnit eg ef TB TB' αg' J K v hαg'₂ := by
  have := hαg'₁
  have := hαg'₂
  have h0 : Lg'.map (TB.map (𝟙 (Lf.obj J) ×ₘ adjf.counit.app K)) ≫
      αg'.app (Lf.obj J, K) =
      αg'.app (Lf.obj J, Lf.obj (Rf.obj K)) ≫
        TB'.map (𝟙 (Lg'.obj (Lf.obj J)) ×ₘ Lg'.map (adjf.counit.app K)) := by
    have h := αg'.naturality
      (X := ((Lf.obj J, Lf.obj (Rf.obj K)) : B × B)) (Y := ((Lf.obj J, K) : B × B))
      (𝟙 (Lf.obj J) ×ₘ adjf.counit.app K)
    simpa only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.prod_map,
      CategoryTheory.Functor.map_id] using h
  have hnat : inv (αg'.app (Lf.obj J, Lf.obj (Rf.obj K))) ≫
      Lg'.map (TB.map (𝟙 (Lf.obj J) ×ₘ adjf.counit.app K)) =
      TB'.map (𝟙 (Lg'.obj (Lf.obj J)) ×ₘ Lg'.map (adjf.counit.app K)) ≫
        inv (αg'.app (Lf.obj J, K)) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
    exact h0
  rw [targetUnit, targetUnit]
  simp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.id_obj, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp Lg' (pulledBackUnit adjf TA TB αf J K v hαf)
      (adjf.counit.app K),
    pulledBackUnit_comp_counit adjf TA TB αf J K v hαf,
    CategoryTheory.Functor.map_comp Lg' (TB.map (𝟙 (Lf.obj J) ×ₘ adjf.counit.app K)) v,
    reassoc_of% hnat, bifunctorSplitRight_assoc, bifunctorSplitLeft_assoc]

/-- **`hcounit`.**  The identification upstairs at `Lf (Rf K)` followed by `Lg' ⋙ Rg'` of the
counit is tensoring the counit and then the identification at `K`.  The projection-formula map of
`Lg' ⊣ Rg'` is natural in its second argument, so this is `targetUnit_comp_map_counit`. -/
theorem targetTensorMap_comp_map_counit (adjf : Lf ⊣ Rf) (adjg : Lg ⊣ Rg) (adjg' : Lg' ⊣ Rg')
    (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) (TB' : B' × B' ⥤ B')
    (αf : TA ⋙ Lf ⟶ Lf.prod Lf ⋙ TB) (αg' : TB ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ TB') (J : A) (K : B)
    (v : TB.obj (Lf.obj J, K) ⟶ K) (hαf : IsIso (αf.app (J, Rf.obj K)))
    (hαg'₁ : IsIso (αg'.app (Lf.obj J, Lf.obj (Rf.obj K))))
    (hαg'₂ : IsIso (αg'.app (Lf.obj J, K))) :
    targetTensorMap adjg adjg' eg ef TB TB' αg' J (Lf.obj (Rf.obj K))
          (pulledBackUnit adjf TA TB αf J K v hαf) hαg'₁ ≫
        (Lg' ⋙ Rg').map (adjf.counit.app K) =
      TB.map (𝟙 (Lf.obj (Rg.obj (Lg.obj J))) ×ₘ adjf.counit.app K) ≫
        targetTensorMap adjg adjg' eg ef TB TB' αg' J K v hαg'₂ := by
  have hnat : TB.map (𝟙 (Rg'.obj (Lf'.obj (Lg.obj J))) ×ₘ adjf.counit.app K) ≫
      CategoryTheory.adjunctionTensorMap adjg' TB TB' αg' (Lf'.obj (Lg.obj J)) K =
      CategoryTheory.adjunctionTensorMap adjg' TB TB' αg'
          (Lf'.obj (Lg.obj J)) (Lf.obj (Rf.obj K)) ≫
        Rg'.map (TB'.map (𝟙 (Lf'.obj (Lg.obj J)) ×ₘ Lg'.map (adjf.counit.app K))) := by
    have h := CategoryTheory.adjunctionTensorMap_natural adjg' TB TB' αg'
      (𝟙 (Lf'.obj (Lg.obj J)))
      (show Lf.obj (Rf.obj K) ⟶ K from adjf.counit.app K)
    simpa only [CategoryTheory.Functor.map_id] using h
  rw [targetTensorMap, targetTensorMap]
  simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.id_obj, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp Rg'
      (targetUnit eg ef TB TB' αg' J (Lf.obj (Rf.obj K))
        (pulledBackUnit adjf TA TB αf J K v hαf) hαg'₁) (Lg'.map (adjf.counit.app K)),
    targetUnit_comp_map_counit adjf eg ef TA TB TB' αf αg' J K v hαf hαg'₁ hαg'₂,
    CategoryTheory.Functor.map_comp Rg'
      (TB'.map (𝟙 (Lf'.obj (Lg.obj J)) ×ₘ Lg'.map (adjf.counit.app K)))
      (targetUnit eg ef TB TB' αg' J K v hαg'₂),
    ← reassoc_of% hnat, bifunctorSplitRight_assoc, bifunctorSplitLeft_assoc]

end Square

/-! ### The coherence -/

section Coherence

variable {A : Type u₁} {B : Type u₂} {A' : Type u₃} {B' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'}
  {Lg : A ⥤ A'} {Rg : A' ⥤ A} {Lg' : B ⥤ B'} {Rg' : B' ⥤ B} {Lc : A ⥤ B'}

/-- **The two trivializations upstairs agree.**  The comparison `αf'` at `(Lg J, Lg (Rf K))`, the
comparison of the two composites in the second tensor factor, and the trivialization on `B'`
compose to `Lf'` of the trivialization on `A'` followed by the comparison of the two composites.

This is the only place the compatibility of the four tensor comparisons around the square is
used, and it is what replaces a unit coherence: the two trivializations upstairs are transports of
one trivialization `v` on `B`, along `αg` and along `αf` respectively, and
`Stacks.AffineProjectionFormula.TensorComparisonCompatible` at `(J, Rf K)` says the transports
agree after `Lf'`. -/
theorem αf'_app_comp_targetUnit (adjf : Lf ⊣ Rf)
    (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) (TA' : A' × A' ⥤ A') (TB' : B' × B' ⥤ B')
    (αf : TA ⋙ Lf ⟶ Lf.prod Lf ⋙ TB) (αf' : TA' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ TB')
    (αg : TA ⋙ Lg ⟶ Lg.prod Lg ⋙ TA') (αg' : TB ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ TB')
    (J : A) (K : B) (v : TB.obj (Lf.obj J, K) ⟶ K)
    (hαf : IsIso (αf.app (J, Rf.obj K))) (hαg : IsIso (αg.app (J, Rf.obj K)))
    (hαg'₁ : IsIso (αg'.app (Lf.obj J, Lf.obj (Rf.obj K))))
    (hsq : Stacks.AffineProjectionFormula.TensorComparisonCompatible ef eg
      TA TB TA' TB' αg αg' αf αf' J (Rf.obj K)) :
    αf'.app (Lg.obj J, Lg.obj (Rf.obj K)) ≫
        TB'.map (𝟙 (Lf'.obj (Lg.obj J)) ×ₘ
          (pullbackComparisonIso eg ef).hom.app (Rf.obj K)) ≫
          targetUnit eg ef TB TB' αg' J (Lf.obj (Rf.obj K))
            (pulledBackUnit adjf TA TB αf J K v hαf) hαg'₁ =
      Lf'.map (sourceUnit adjf TA TB TA' αf αg J K v hαg) ≫
        (pullbackComparisonIso eg ef).hom.app (Rf.obj K) := by
  have := hαf
  have := hαg
  have := hαg'₁
  -- The compatibility of the four comparisons, solved for the comparison along `f'`.
  have hmain : Lf'.map (αg.app (J, Rf.obj K)) ≫ αf'.app (Lg.obj J, Lg.obj (Rf.obj K)) =
      (pullbackComparisonIso eg ef).hom.app (TA.obj (J, Rf.obj K)) ≫
        (Lg'.map (αf.app (J, Rf.obj K)) ≫
          αg'.app (Lf.obj J, Lf.obj (Rf.obj K)) ≫
            TB'.map ((pullbackComparisonIso eg ef).inv.app J ×ₘ
              (pullbackComparisonIso eg ef).inv.app (Rf.obj K))) := by
    rw [Stacks.AffineProjectionFormula.TensorComparisonCompatible] at hsq
    simp only [squareCompositeIso_hom_app_eq] at hsq
    rw [hsq, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  -- Naturality of the comparison of the two composites at the descended trivialization.
  have hc : Lf'.map (Lg.map (unitDescent adjf TA TB αf J K v)) ≫
      (pullbackComparisonIso eg ef).hom.app (Rf.obj K) =
      (pullbackComparisonIso eg ef).hom.app (TA.obj (J, Rf.obj K)) ≫
        Lg'.map (Lf.map (unitDescent adjf TA TB αf J K v)) := by
    have h := (pullbackComparisonIso eg ef).hom.naturality
      (unitDescent adjf TA TB αf J K v)
    simpa only [CategoryTheory.Functor.comp_map] using h
  rw [sourceUnit, CategoryTheory.Functor.map_comp, Category.assoc, hc,
    CategoryTheory.Functor.map_inv, IsIso.eq_inv_comp, targetUnit]
  simp only [CategoryTheory.Functor.comp_obj]
  rw [bifunctorSplitLeft_assoc, reassoc_of% hmain, bifunctorSplitBoth_assoc,
    Iso.inv_hom_id_app, Iso.inv_hom_id_app, bifunctorMapProdId]
  simp only [CategoryTheory.Functor.comp_obj, Category.id_comp]
  rw [IsIso.hom_inv_id_assoc, ← CategoryTheory.Functor.map_comp, pulledBackUnit,
    IsIso.hom_inv_id_assoc]

/-- **`hcompat`.**  The comparison `αf` at `(Rg (Lg J), Rf K)` followed by the identification
upstairs at `Lf (Rf K)` is `Lf` of the identification downstairs followed by the canonical
comparison `pullbackPushforwardSquare` at `Rf K`.

The proof is the diagram of [Stacks, Tag 0B6B] over abstract adjunctions,
`Stacks.AffineProjectionFormula.adjunctionTensorMap_baseChange_square` for the transposed square
at the object `Lg J`, followed by `αf'_app_comp_targetUnit` and naturality of the base change map
of the transposed square. -/
theorem αf_app_comp_targetTensorMap (adjf : Lf ⊣ Rf) (adjg : Lg ⊣ Rg) (adjg' : Lg' ⊣ Rg')
    (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) (TA' : A' × A' ⥤ A') (TB' : B' × B' ⥤ B')
    (αf : TA ⋙ Lf ⟶ Lf.prod Lf ⋙ TB) (αf' : TA' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ TB')
    (αg : TA ⋙ Lg ⟶ Lg.prod Lg ⋙ TA') (αg' : TB ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ TB')
    (J : A) (K : B) (v : TB.obj (Lf.obj J, K) ⟶ K)
    (hαf : IsIso (αf.app (J, Rf.obj K))) (hαg : IsIso (αg.app (J, Rf.obj K)))
    (hαg'₁ : IsIso (αg'.app (Lf.obj J, Lf.obj (Rf.obj K))))
    (hsq₁ : Stacks.AffineProjectionFormula.TensorComparisonCompatible ef eg
      TA TB TA' TB' αg αg' αf αf' (Rg.obj (Lg.obj J)) (Rf.obj K))
    (hsq₂ : Stacks.AffineProjectionFormula.TensorComparisonCompatible ef eg
      TA TB TA' TB' αg αg' αf αf' J (Rf.obj K)) :
    αf.app (Rg.obj (Lg.obj J), Rf.obj K) ≫
        targetTensorMap adjg adjg' eg ef TB TB' αg' J (Lf.obj (Rf.obj K))
          (pulledBackUnit adjf TA TB αf J K v hαf) hαg'₁ =
      Lf.map (sourceTensorMap adjf adjg TA TB TA' αf αg J K v hαg) ≫
        (pullbackPushforwardSquare adjg adjg' eg ef).app (Rf.obj K) := by
  have h0 := Stacks.AffineProjectionFormula.adjunctionTensorMap_baseChange_square
    adjg adjg' ef eg TA TB TA' TB' αg αg' αf αf' (Lg.obj J) (Rf.obj K) hsq₁
  simp only [squareCompositeIso_inv_app_eq] at h0
  have hstar := αf'_app_comp_targetUnit adjf eg ef TA TB TA' TB' αf αf' αg αg'
    J K v hαf hαg hαg'₁ hsq₂
  have hnat := map_naturality adjg adjg' ef eg (sourceUnit adjf TA TB TA' αf αg J K v hαg)
  rw [targetTensorMap, sourceTensorMap, pullbackPushforwardSquare_natTrans_app]
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.comp_obj,
    Category.assoc]
  rw [reassoc_of% h0, ← CategoryTheory.Functor.map_comp Rg', Category.assoc, hstar,
    CategoryTheory.Functor.map_comp Rg', ← reassoc_of% hnat]

end Coherence

/-! ### Invertibility, and the conclusion -/

section Conclusion

variable {A : Type u₁} {B : Type u₂} {A' : Type u₃} {B' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
  {Lg : A ⥤ A'} {Rg : A' ⥤ A} {Lg' : B ⥤ B'} {Rg' : B' ⥤ B} {Lc : A ⥤ B'}

/-- The trivialization carried down to `A` is invertible when `v` is and the interchanged-order
projection-formula map of `Lf ⊣ Rf` at `(J, K)` is. -/
theorem isIso_unitDescent (adjf : Lf ⊣ Rf) (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (αf : TA ⋙ Lf ⟶ Lf.prod Lf ⋙ TB) (J : A) (K : B) (v : TB.obj (Lf.obj J, K) ⟶ K)
    (hv : IsIso v)
    (hd : IsIso (Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight adjf TA TB αf J K)) :
    IsIso (unitDescent adjf TA TB αf J K v) := by
  have := hd
  have := hv
  rw [unitDescent]
  infer_instance

/-- The trivialization transported to `Lf (Rf K)` is invertible. -/
theorem isIso_pulledBackUnit (adjf : Lf ⊣ Rf) (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (αf : TA ⋙ Lf ⟶ Lf.prod Lf ⋙ TB) (J : A) (K : B) (v : TB.obj (Lf.obj J, K) ⟶ K)
    (hv : IsIso v)
    (hd : IsIso (Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight adjf TA TB αf J K))
    (hαf : IsIso (αf.app (J, Rf.obj K))) :
    IsIso (pulledBackUnit adjf TA TB αf J K v hαf) := by
  have := hαf
  have := isIso_unitDescent adjf TA TB αf J K v hv hd
  rw [pulledBackUnit]
  infer_instance

/-- **The identification downstairs is an isomorphism.** -/
theorem isIso_sourceTensorMap (adjf : Lf ⊣ Rf) (adjg : Lg ⊣ Rg) (TA : A × A ⥤ A)
    (TB : B × B ⥤ B) (TA' : A' × A' ⥤ A') (αf : TA ⋙ Lf ⟶ Lf.prod Lf ⋙ TB)
    (αg : TA ⋙ Lg ⟶ Lg.prod Lg ⋙ TA') (J : A) (K : B) (v : TB.obj (Lf.obj J, K) ⟶ K)
    (hv : IsIso v)
    (hd : IsIso (Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight adjf TA TB αf J K))
    (hαg : IsIso (αg.app (J, Rf.obj K)))
    (hp : IsIso (CategoryTheory.adjunctionTensorMap adjg TA TA' αg (Lg.obj J) (Rf.obj K))) :
    IsIso (sourceTensorMap adjf adjg TA TB TA' αf αg J K v hαg) := by
  have := hαg
  have := hp
  have := isIso_unitDescent adjf TA TB αf J K v hv hd
  have : IsIso (sourceUnit adjf TA TB TA' αf αg J K v hαg) := by
    rw [sourceUnit]; infer_instance
  rw [sourceTensorMap]
  infer_instance

/-- **The identification upstairs is an isomorphism**, at any object `W` and any invertible
trivialization there. -/
theorem isIso_targetTensorMap (adjg : Lg ⊣ Rg) (adjg' : Lg' ⊣ Rg') (eg : Lg ⋙ Lf' ≅ Lc)
    (ef : Lf ⋙ Lg' ≅ Lc) (TB : B × B ⥤ B) (TB' : B' × B' ⥤ B')
    (αg' : TB ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ TB') (J : A) (W : B) (w : TB.obj (Lf.obj J, W) ⟶ W)
    (hw : IsIso w) (hαg' : IsIso (αg'.app (Lf.obj J, W)))
    (hθ : IsIso (map adjg adjg' ef eg (Lg.obj J)))
    (hp' : IsIso
      (CategoryTheory.adjunctionTensorMap adjg' TB TB' αg' (Lf'.obj (Lg.obj J)) W)) :
    IsIso (targetTensorMap adjg adjg' eg ef TB TB' αg' J W w hαg') := by
  have := hαg'
  have := hp'
  have := isIso_bifunctor_map_left TB (map adjg adjg' ef eg (Lg.obj J)) hθ W
  have := isIso_bifunctor_map_left TB' ((pullbackComparisonIso eg ef).hom.app J)
    (((pullbackComparisonIso eg ef).app J).isIso_hom) (Lg'.obj W)
  have := hw
  have : IsIso (targetUnit eg ef TB TB' αg' J W w hαg') := by
    rw [targetUnit]; infer_instance
  rw [targetTensorMap]
  infer_instance

variable (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (adjg : Lg ⊣ Rg) (adjg' : Lg' ⊣ Rg')
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  (TA : A × A ⥤ A) (TB : B × B ⥤ B) (TA' : A' × A' ⥤ A') (TB' : B' × B' ⥤ B')
  (αf : TA ⋙ Lf ⟶ Lf.prod Lf ⋙ TB) (αf' : TA' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ TB')
  (αg : TA ⋙ Lg ⟶ Lg.prod Lg ⋙ TA') (αg' : TB ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ TB')
  (J : A) (K : B) (v : TB.obj (Lf.obj J, K) ⟶ K)

/-- **The coherence, solved for the pushed-forward base change map, with no coherence left to
supply.**  The identification downstairs followed by `Rg` of the base
change map at `K` is the interchanged-order projection-formula map of `Lf ⊣ Rf` at
`(Rg (Lg J), K)`, followed by `Rf` of the identification upstairs at `K` and by the conjugate
isomorphism `Rg' ⋙ Rf ≅ Rf' ⋙ Rg` of the two iterated right adjoints.

This is
`Stacks.CategoryTheory.BaseChange.pushforward_map_eq_adjunctionTensorMap` — in the pointwise,
interchanged-order form the geometric application consumes — with its hypotheses `hcompat` and
`hcounit` discharged.

The hypotheses are: the invertibility of the trivialization `v`; of the interchanged-order
projection-formula map of `Lf ⊣ Rf` at `(J, K)`; of the projection-formula map of `Lg ⊣ Rg` at
`(Lg J, Rf K)` and of the one of `Lg' ⊣ Rg'` at `(Lf' (Lg J), W)` for the two objects `W` where
it is needed; of the four components of the tensor comparisons `αf`, `αg`, `αg'` where they are
needed; of the base change map of the transposed square at `Lg J`; and the compatibility of the
four tensor comparisons around the square at the two pairs `(Rg (Lg J), Rf K)` and `(J, Rf K)`.

In the geometric situation of [Stacks, Tag 08IB] with `J = 𝒪_S[0]` all of these are available:
the projection-formula maps are [Stacks, Tag 08EU] and its interchanged-order companion, the
components of the comparisons are [Stacks, Tag 079U], which is an isomorphism, the compatibility
is the coherence of [Stacks, Tag 079U] around a commutative square, the trivialization is the
left unit law of `⊗^𝐋` composed with `Lf^*(𝒪_S[0]) ≅ 𝒪_X[0]`, and the invertibility of the
transposed base change map at `Lg^*(𝒪_S[0])` is where Tor independence enters. -/
theorem pushforward_map_eq_adjunctionTensorMapRight (hv : IsIso v)
    (hd : IsIso (Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight adjf TA TB αf J K))
    (hαf : IsIso (αf.app (J, Rf.obj K))) (hαg : IsIso (αg.app (J, Rf.obj K)))
    (hαg'₁ : IsIso (αg'.app (Lf.obj J, Lf.obj (Rf.obj K))))
    (hαg'₂ : IsIso (αg'.app (Lf.obj J, K)))
    (hp : IsIso (CategoryTheory.adjunctionTensorMap adjg TA TA' αg (Lg.obj J) (Rf.obj K)))
    (hp'₁ : IsIso (CategoryTheory.adjunctionTensorMap adjg' TB TB' αg'
      (Lf'.obj (Lg.obj J)) (Lf.obj (Rf.obj K))))
    (hp'₂ : IsIso
      (CategoryTheory.adjunctionTensorMap adjg' TB TB' αg' (Lf'.obj (Lg.obj J)) K))
    (hθ : IsIso (map adjg adjg' ef eg (Lg.obj J)))
    (hsq₁ : Stacks.AffineProjectionFormula.TensorComparisonCompatible ef eg
      TA TB TA' TB' αg αg' αf αf' (Rg.obj (Lg.obj J)) (Rf.obj K))
    (hsq₂ : Stacks.AffineProjectionFormula.TensorComparisonCompatible ef eg
      TA TB TA' TB' αg αg' αf αf' J (Rf.obj K)) :
    sourceTensorMap adjf adjg TA TB TA' αf αg J K v hαg ≫ Rg.map (map adjf adjf' eg ef K) =
      Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight adjf TA TB αf
          (Rg.obj (Lg.obj J)) K ≫
        Rf.map (targetTensorMap adjg adjg' eg ef TB TB' αg' J K v hαg'₂) ≫
          (rightCompositeIso adjf adjf' adjg adjg' eg ef).hom.app (Lg'.obj K) := by
  have h₁ := isIso_sourceTensorMap adjf adjg TA TB TA' αf αg J K v hv hd hαg hp
  have h₂ := isIso_targetTensorMap adjg adjg' eg ef TB TB' αg' J (Lf.obj (Rf.obj K))
    (pulledBackUnit adjf TA TB αf J K v hαf)
    (isIso_pulledBackUnit adjf TA TB αf J K v hv hd hαf) hαg'₁ hθ hp'₁
  have h₃ := isIso_targetTensorMap adjg adjg' eg ef TB TB' αg' J K v hv hαg'₂ hθ hp'₂
  have hcompat : (pullbackPushforwardSquare adjg adjg' eg ef).app (Rf.obj K) =
      Lf.map (asIso (sourceTensorMap adjf adjg TA TB TA' αf αg J K v hαg)).symm.hom ≫
        αf.app (Rg.obj (Lg.obj J), Rf.obj K) ≫
          (asIso (targetTensorMap adjg adjg' eg ef TB TB' αg' J (Lf.obj (Rf.obj K))
            (pulledBackUnit adjf TA TB αf J K v hαf) hαg'₁)).symm.inv := by
    rw [Iso.symm_hom, asIso_inv, Iso.symm_inv, asIso_hom,
      αf_app_comp_targetTensorMap adjf adjg adjg' eg ef TA TB TA' TB' αf αf' αg αg' J K v
        hαf hαg hαg'₁ hsq₁ hsq₂,
      ← Category.assoc, ← CategoryTheory.Functor.map_comp, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hcounit : (Lg' ⋙ Rg').map (adjf.counit.app K) ≫
        (asIso (targetTensorMap adjg adjg' eg ef TB TB' αg' J K v hαg'₂)).symm.hom =
      (asIso (targetTensorMap adjg adjg' eg ef TB TB' αg' J (Lf.obj (Rf.obj K))
          (pulledBackUnit adjf TA TB αf J K v hαf) hαg'₁)).symm.hom ≫
        TB.map (𝟙 (Lf.obj (Rg.obj (Lg.obj J))) ×ₘ adjf.counit.app K) := by
    rw [Iso.symm_hom, asIso_inv, Iso.symm_hom, asIso_inv, IsIso.comp_inv_eq, Category.assoc,
      IsIso.eq_inv_comp]
    exact targetTensorMap_comp_map_counit adjf adjg adjg' eg ef TA TB TB' αf αg' J K v
      hαf hαg'₁ hαg'₂
  have heq := mateEquiv_app_eq_adjunctionTensorMapRight_of_app adjf
    (pullbackPushforwardSquare adjg adjg' eg ef) TA TB αf (Rg.obj (Lg.obj J)) K
    (asIso (sourceTensorMap adjf adjg TA TB TA' αf αg J K v hαg)).symm
    (asIso (targetTensorMap adjg adjg' eg ef TB TB' αg' J (Lf.obj (Rf.obj K))
      (pulledBackUnit adjf TA TB αf J K v hαf) hαg'₁)).symm
    (asIso (targetTensorMap adjg adjg' eg ef TB TB' αg' J K v hαg'₂)).symm hcompat hcounit
  rw [pushforward_map_eq adjf adjf' adjg adjg' eg ef K, projectionTwoSquare, heq]
  simp only [Iso.symm_hom, asIso_inv, Iso.symm_inv, asIso_hom, Category.assoc]
  rw [IsIso.hom_inv_id_assoc]

/-- **The conclusion: `Rg` applied to the base change map at `K` is invertible, with no coherence
left to supply.**  This is the form the reduction of [Stacks, Tag 08IB] over an affine base
consumes: the three transports in `pushforward_map_eq_adjunctionTensorMapRight` are
isomorphisms, so only the interchanged-order projection-formula map at `(Rg (Lg J), K)` —
[Stacks, Tag 08EU] — matters. -/
theorem isIso_pushforward_map_of_isIso_adjunctionTensorMapRight (hv : IsIso v)
    (hd : IsIso (Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight adjf TA TB αf J K))
    (hαf : IsIso (αf.app (J, Rf.obj K))) (hαg : IsIso (αg.app (J, Rf.obj K)))
    (hαg'₁ : IsIso (αg'.app (Lf.obj J, Lf.obj (Rf.obj K))))
    (hαg'₂ : IsIso (αg'.app (Lf.obj J, K)))
    (hp : IsIso (CategoryTheory.adjunctionTensorMap adjg TA TA' αg (Lg.obj J) (Rf.obj K)))
    (hp'₁ : IsIso (CategoryTheory.adjunctionTensorMap adjg' TB TB' αg'
      (Lf'.obj (Lg.obj J)) (Lf.obj (Rf.obj K))))
    (hp'₂ : IsIso
      (CategoryTheory.adjunctionTensorMap adjg' TB TB' αg' (Lf'.obj (Lg.obj J)) K))
    (hθ : IsIso (map adjg adjg' ef eg (Lg.obj J)))
    (hsq₁ : Stacks.AffineProjectionFormula.TensorComparisonCompatible ef eg
      TA TB TA' TB' αg αg' αf αf' (Rg.obj (Lg.obj J)) (Rf.obj K))
    (hsq₂ : Stacks.AffineProjectionFormula.TensorComparisonCompatible ef eg
      TA TB TA' TB' αg αg' αf αf' J (Rf.obj K))
    (h : IsIso (Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight adjf TA TB αf
      (Rg.obj (Lg.obj J)) K)) :
    IsIso (Rg.map (map adjf adjf' eg ef K)) := by
  have h₁ := isIso_sourceTensorMap adjf adjg TA TB TA' αf αg J K v hv hd hαg hp
  have h₃ := isIso_targetTensorMap adjg adjg' eg ef TB TB' αg' J K v hv hαg'₂ hθ hp'₂
  have := h
  have : IsIso (sourceTensorMap adjf adjg TA TB TA' αf αg J K v hαg ≫
      Rg.map (map adjf adjf' eg ef K)) := by
    rw [pushforward_map_eq_adjunctionTensorMapRight adjf adjf' adjg adjg' eg ef
      TA TB TA' TB' αf αf' αg αg' J K v hv hd hαf hαg hαg'₁ hαg'₂ hp hp'₁ hp'₂ hθ hsq₁ hsq₂]
    infer_instance
  exact IsIso.of_isIso_comp_left (sourceTensorMap adjf adjg TA TB TA' αf αg J K v hαg)
    (Rg.map (map adjf adjf' eg ef K))

end Conclusion

end Stacks.CategoryTheory.BaseChange

end
