module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ExtendedIntegers
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.FibreDimension
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute

/-!
# Delta-dimension along a flat morphism of constant relative dimension

Let `C = (S, δ)` be the base situation of chapter 42 of the Stacks Project, let `Z` be a scheme
locally of finite type over `S` and let `p : P ⟶ Z` be flat, locally of finite type and of
relative dimension `r`. Stacks 02R8 computes the delta-dimension of `P` from that of `Z`:

* every irreducible component of `P` dominates an irreducible component of `Z` and has
  delta-dimension `r` more than it;
* consequently, if every irreducible component of `Z` meets the image of `p`, then
  `dim_δ(P) = dim_δ(Z) + r`;
* and if `Z` is irreducible, every irreducible component of `P` dominates `Z` itself.

The mechanism is the dimension formula of Stacks 02FX. At the generic point `ξ` of an
irreducible component of `P` the fibre of `p` has Krull dimension zero in its local ring — `ξ`
is a maximal point of that fibre, because a specialization inside the fibre is a specialization
inside `P` and `ξ` is the generic point of a component. The fibre has dimension `r` at `ξ`
because it is equidimensional of dimension `r`, so Stacks 02FX gives transcendence degree `r`
for the residue-field extension of `p` at `ξ`, and `Stacks.Chow.relativeDimension` grows by
exactly that transcendence degree along `p`. Flatness enters only through the lifting of
generalizations, which is what makes the generic point of a component of `P` lie over the
generic point of a component of `Z`.

## Main results

* `Stacks.Chow.exists_irreducibleComponent_map_genericPoint` — along a flat morphism the generic
  point of an irreducible component maps to the generic point of an irreducible component.
* `Stacks.Chow.toNat_residueTrdeg_genericPoint` — the residue-field extension of `p` at the
  generic point of an irreducible component has transcendence degree `r`.
* `Stacks.Chow.deltaDimension_irreducibleComponent_eq_add` — the delta-dimension of an
  irreducible component of `P` is `r` more than that of the component of `Z` beneath it.
* `Stacks.Chow.schemeDeltaDimension_comp_eq_add` — **Stacks 02R8**: `dim_δ(P) = dim_δ(Z) + r`.
* `Stacks.Chow.dense_image_irreducibleComponent` — over an irreducible base every irreducible
  component of `P` dominates it.
* `Stacks.Chow.dense_image_irreducibleComponent_pullback` — **Stacks 02R8**: the same for the
  scheme-theoretic inverse image of an irreducible closed subscheme along a flat morphism.
* `Stacks.Chow.deltaDimension_irreducibleComponent_eq_add_of_irreducible` — over an irreducible
  base each irreducible component of `P` has delta-dimension `dim_δ(Z) + r`.
* `Stacks.Chow.relativeDimension_pullback_snd` — relative dimension is stable under base change.
* `Stacks.Chow.schemeDeltaDimension_pullback_snd_comp` — **Stacks 02R8**: the dimension formula
  for the scheme-theoretic inverse image of a closed subscheme along a flat morphism.
* `Stacks.Chow.deltaDimension_irreducibleComponent_pullback_snd_comp` — **Stacks 02R8**: the
  same for each irreducible component of that inverse image over an irreducible subscheme.

## Implementation notes

The source states the result for the scheme-theoretic inverse image `X ×_Y Z` of a closed
subscheme `i : Z ⟶ Y` along a flat `f : X ⟶ Y` of relative dimension `r`. The statements here
are instead about an arbitrary flat morphism `p : P ⟶ Z` of relative dimension `r` over the
base, which is strictly more general: the inverse image is recovered by taking
`p = pullback.snd f i`, which is flat by base change. What that specialization additionally
needs is that `pullback.snd f i` again has relative dimension `r`, which is Stacks 02NK.

## References

* [Stacks Project, Tag 02R8](https://stacks.math.columbia.edu/tag/02R8)
* [Stacks Project, Tag 02FX](https://stacks.math.columbia.edu/tag/02FX)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Generic points along a flat morphism -/

/-- The generic point of an irreducible component generates it. -/
private theorem isGenericPoint_genericPoint_component {P : Scheme.{u}}
    (W : irreducibleComponents P) : IsGenericPoint W.2.1.genericPoint (W : Set P) :=
  W.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents (W : Set P) W.2)

/-- A generization of the generic point of an irreducible component generates that component. -/
private theorem isGenericPoint_of_specializes_genericPoint {P : Scheme.{u}}
    (W : irreducibleComponents P) {y : P} (h : y ⤳ W.2.1.genericPoint) :
    IsGenericPoint y (W : Set P) := by
  have hsub : (W : Set P) ⊆ closure ({y} : Set P) := by
    rw [← isGenericPoint_genericPoint_component W]
    exact closure_minimal (Set.singleton_subset_iff.mpr h.mem_closure) isClosed_closure
  exact Set.Subset.antisymm (W.2.2 isIrreducible_singleton.closure hsub) hsub

/-- Along a flat morphism the generic point of an irreducible component maps to the generic
point of an irreducible component: a flat morphism lifts generalizations, so the generization
of the image lifts to a generization of the point, which must be the point itself. -/
@[ega "IV 2.3.5" "(ii), special case"]
theorem exists_irreducibleComponent_map_genericPoint {P Z : Scheme.{u}} (p : P ⟶ Z) [Flat p]
    (W : irreducibleComponents P) :
    ∃ V : irreducibleComponents Z,
      p.base W.2.1.genericPoint = genericPoints.ofComponent V := by
  set ξ : P := W.2.1.genericPoint with hξdef
  set V : irreducibleComponents Z :=
    ⟨irreducibleComponent (p.base ξ), irreducibleComponent_mem_irreducibleComponents _⟩ with hVdef
  have hξW : IsGenericPoint ξ (W : Set P) := isGenericPoint_genericPoint_component W
  have hηx : (genericPoints.ofComponent V : Z) ⤳ p.base ξ :=
    (genericPoints.isGenericPoint_ofComponent V).specializes mem_irreducibleComponent
  obtain ⟨ξ', hξ'ξ, hξ'η⟩ := Flat.generalizingMap p hηx
  exact ⟨V, by rw [← (isGenericPoint_of_specializes_genericPoint W hξ'ξ).eq hξW]; exact hξ'η⟩

/-- Over an irreducible base, the generic point of an irreducible component of the source of a
flat morphism maps to the generic point of the base: there is only one irreducible component
downstairs. -/
theorem map_genericPoint_irreducibleComponent_eq_genericPoint {P Z : Scheme.{u}} (p : P ⟶ Z)
    [Flat p] [IrreducibleSpace Z] (W : irreducibleComponents P) :
    p.base W.2.1.genericPoint = genericPoint Z := by
  obtain ⟨V, hV⟩ := exists_irreducibleComponent_map_genericPoint p W
  have hVU : (V : Set Z) = Set.univ :=
    Set.eq_univ_of_univ_subset (V.2.2 (IrreducibleSpace.isIrreducible_univ Z) (Set.subset_univ _))
  have hg : IsGenericPoint (genericPoints.ofComponent V : Z) (Set.univ : Set Z) := by
    simpa only [hVU] using genericPoints.isGenericPoint_ofComponent V
  exact hV.trans (hg.eq (genericPoint_spec Z))

/-- Over an irreducible base, the image of an irreducible component of the source of a flat
morphism is dense: the component's generic point lies over the generic point of the base, which
is dense. -/
theorem dense_image_irreducibleComponent {P Z : Scheme.{u}} (p : P ⟶ Z) [Flat p]
    [IrreducibleSpace Z] (W : irreducibleComponents P) :
    closure (p.base '' (W : Set P)) = Set.univ := by
  have hmem : genericPoint Z ∈ p.base '' (W : Set P) :=
    ⟨W.2.1.genericPoint,
      (isGenericPoint_genericPoint_component W).mem,
      map_genericPoint_irreducibleComponent_eq_genericPoint p W⟩
  refine Set.eq_univ_iff_forall.mpr fun z ↦ ?_
  exact (genericPoint_specializes z).mem_closed isClosed_closure (subset_closure hmem)

/-- **Stacks 02R8.** Every irreducible component of the scheme-theoretic inverse image of an
irreducible closed subscheme along a flat morphism dominates that subscheme: the inverse image
is flat over the subscheme by base change. -/
@[stacks 02R8 "dominance of components",
  ega "IV 2.3.4" "(iii), special case",
  ega "IV 4.4.1" "special case", sga "7 VIII 5.2" "partial"]
theorem dense_image_irreducibleComponent_pullback {X Y Z : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (i : Z ⟶ Y) [IrreducibleSpace Z]
    (W : irreducibleComponents (pullback f i : Scheme.{u})) :
    closure ((pullback.snd f i).base '' (W : Set (pullback f i : Scheme.{u}))) = Set.univ :=
  letI : Flat (pullback.snd f i) :=
    Flat.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f i) inferInstance
  dense_image_irreducibleComponent (pullback.snd f i) W

/-! ### The transcendence degree at the generic point of a component -/

/-- The local ring of a fibre at the generic point of an irreducible component of the source is
zero-dimensional: that point is maximal in the fibre, since a specialization inside the fibre is
in particular a specialization inside the source. -/
@[ega "IV 5.5.2" "special case"]
theorem ringKrullDim_stalk_fiber_genericPoint {P Z : Scheme.{u}} (p : P ⟶ Z)
    (W : irreducibleComponents P) :
    ringKrullDim ((p.fiber (p.base W.2.1.genericPoint)).presheaf.stalk
      (p.asFiber W.2.1.genericPoint)) = 0 := by
  set ξ : P := W.2.1.genericPoint with hξdef
  have hξW : IsGenericPoint ξ (W : Set P) := isGenericPoint_genericPoint_component W
  have hmax : IsMax (p.asFiber ξ) := by
    intro y hy
    have hspec : (p.fiberι (p.base ξ)).base y ⤳ ξ := by
      have h' : y ⤳ p.asFiber ξ := hy
      simpa [hξdef] using h'.map (p.fiberι (p.base ξ)).continuous
    refine le_of_eq ((p.fiberι (p.base ξ)).isEmbedding.injective ?_)
    rw [(isGenericPoint_of_specializes_genericPoint W hspec).eq hξW]
    exact (Scheme.Hom.fiberι_asFiber p ξ).symm
  rw [ringKrullDim_stalk_eq_coheight]
  exact_mod_cast Order.coheight_eq_zero.mpr hmax

/-- The residue-field extension of a flat morphism of relative dimension `r` has transcendence
degree `r` at the generic point of an irreducible component of the source: by Stacks 02FX the
dimension of the fibre at that point is the dimension of the local ring of the fibre plus that
transcendence degree, the former is zero and the latter is `r` because the fibre is
equidimensional of dimension `r`. -/
@[ega "IV 5.6.5" "special case"]
theorem toNat_residueTrdeg_genericPoint {P Z : Scheme.{u}} (p : P ⟶ Z) [LocallyOfFiniteType p]
    (W : irreducibleComponents P) (r : ℕ) (hrel : AlgebraicGeometry.RelativeDimension p r) :
    Cardinal.toNat (residueTrdeg p W.2.1.genericPoint) = r := by
  set ξ : P := W.2.1.genericPoint with hξdef
  have hq : LocallyOfFiniteType (p.fiberToSpecResidueField (p.base ξ)) := by
    change LocallyOfFiniteType (pullback.snd p (Z.fromSpecResidueField (p.base ξ)))
    infer_instance
  have hrelη := hrel (p.base ξ) ⟨p.asFiber ξ⟩
  have hAt := @topologicalKrullDimAt_eq_of_equidimensional _ _ (p.fiber (p.base ξ))
    (p.fiberToSpecResidueField (p.base ξ)) hq r hrelη.1 hrelη.2 (p.asFiber ξ)
  have hzero := ringKrullDim_stalk_fiber_genericPoint p W
  have hfx := topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg p ξ
  change topologicalKrullDimAt (p.fiber (p.base ξ)) (p.asFiber ξ) =
    ringKrullDim ((p.fiber (p.base ξ)).presheaf.stalk (p.asFiber ξ)) +
      (Cardinal.toENat (residueTrdeg p ξ) : WithBot ℕ∞) at hfx
  rw [hAt, hzero, zero_add] at hfx
  have hENat : Cardinal.toENat (residueTrdeg p ξ) = r := (WithBot.coe_eq_coe.mp hfx).symm
  simpa [Cardinal.toNat_toENat] using congrArg ENat.toNat hENat

/-! ### Delta-dimension along a flat morphism -/

/-- The delta-dimension of an irreducible component of the source of a morphism of relative
dimension `r` is `r` more than that of an irreducible closed subset whose generic point is the
image of its generic point. -/
private theorem deltaDimension_comp_eq_add_of_map_eq (C : ChowSituation.{u}) {P Z : Scheme.{u}}
    (p : P ⟶ Z) [LocallyOfFiniteType p] (q : Z ⟶ C.S) [LocallyOfFiniteType q] (r : ℕ)
    (hrel : AlgebraicGeometry.RelativeDimension p r) (W : irreducibleComponents P)
    (T : IrreducibleCloseds Z) (z : Z) (hz : IsGenericPoint z (T : Set Z))
    (hη : p.base W.2.1.genericPoint = z) :
    deltaDimension C (p ≫ q)
        ⟨(W : Set P), W.2.1, isClosed_of_mem_irreducibleComponents (W : Set P) W.2⟩ =
      deltaDimension C q T + (r : ℤ) := by
  have hδ := relativeDimension_comp_eq_add_trdeg C.dimensionFunction q p W.2.1.genericPoint
  rw [toNat_residueTrdeg_genericPoint p W r hrel, hη] at hδ
  rw [deltaDimension_eq_of_isGenericPoint C (p ≫ q) _ W.2.1.genericPoint
      (isGenericPoint_genericPoint_component W), deltaDimension_eq_of_isGenericPoint C q _ z hz]
  exact hδ

/-- The delta-dimension of an irreducible component of the source of a flat morphism of relative
dimension `r` is `r` more than the delta-dimension of the component of the target beneath it. -/
theorem deltaDimension_irreducibleComponent_eq_add (C : ChowSituation.{u}) {P Z : Scheme.{u}}
    (p : P ⟶ Z) [LocallyOfFiniteType p] (q : Z ⟶ C.S) [LocallyOfFiniteType q] (r : ℕ)
    (hrel : AlgebraicGeometry.RelativeDimension p r) (W : irreducibleComponents P)
    (V : irreducibleComponents Z)
    (hη : p.base W.2.1.genericPoint = genericPoints.ofComponent V) :
    deltaDimension C (p ≫ q)
        ⟨(W : Set P), W.2.1, isClosed_of_mem_irreducibleComponents (W : Set P) W.2⟩ =
      deltaDimension C q
          ⟨(V : Set Z), V.2.1, isClosed_of_mem_irreducibleComponents (V : Set Z) V.2⟩ +
        (r : ℤ) := by
  exact deltaDimension_comp_eq_add_of_map_eq C p q r hrel W _ _
    (genericPoints.isGenericPoint_ofComponent V) hη

/-- **Stacks 02R8.** For a flat morphism `p : P ⟶ Z` of relative dimension `r` whose image meets
every irreducible component of `Z`, the delta-dimension of `P` is that of `Z` plus `r`.

Every component of `P` contributes the delta-dimension of a component of `Z` plus `r`, and
every component of `Z` is contributed by some component of `P`: a point of `P` over a point of
the component generizes, by flatness, to a point over the component's generic point, and the
component of `P` through it is then one lying over that component of `Z`. -/
theorem schemeDeltaDimension_comp_eq_add (C : ChowSituation.{u}) {P Z : Scheme.{u}}
    (q : Z ⟶ C.S) [LocallyOfFiniteType q] (p : P ⟶ Z) [LocallyOfFiniteType p] [Flat p] (r : ℕ)
    (hrel : AlgebraicGeometry.RelativeDimension p r)
    (hmeets : ∀ V : irreducibleComponents Z, ∃ x : P, p.base x ∈ (V : Set Z)) :
    schemeDeltaDimension C (p ≫ q) = schemeDeltaDimension C q + ((r : ℤ) : EInt) := by
  set α : irreducibleComponents P → EInt := fun W ↦
    (deltaDimension C (p ≫ q)
      ⟨(W : Set P), W.2.1, isClosed_of_mem_irreducibleComponents (W : Set P) W.2⟩ : EInt)
    with hαdef
  set β : irreducibleComponents Z → EInt := fun V ↦
    (deltaDimension C q
      ⟨(V : Set Z), V.2.1, isClosed_of_mem_irreducibleComponents (V : Set Z) V.2⟩ : EInt)
    with hβdef
  have hstep (W : irreducibleComponents P) (V : irreducibleComponents Z)
      (hη : p.base W.2.1.genericPoint = genericPoints.ofComponent V) :
      α W = β V + ((r : ℤ) : EInt) := by
    rw [hαdef, hβdef, ← coe_add_coe_eq_coe_add]
    exact congrArg (fun z : ℤ ↦ (z : EInt))
      (deltaDimension_irreducibleComponent_eq_add C p q r hrel W V hη)
  have hsource (W : irreducibleComponents P) :
      ∃ V : irreducibleComponents Z, α W = β V + ((r : ℤ) : EInt) := by
    obtain ⟨V, hη⟩ := exists_irreducibleComponent_map_genericPoint p W
    exact ⟨V, hstep W V hη⟩
  have htarget (V : irreducibleComponents Z) :
      ∃ W : irreducibleComponents P, α W = β V + ((r : ℤ) : EInt) := by
    obtain ⟨x, hxV⟩ := hmeets V
    have hηx : (genericPoints.ofComponent V : Z) ⤳ p.base x :=
      (genericPoints.isGenericPoint_ofComponent V).specializes hxV
    obtain ⟨y, hyx, hpy⟩ := Flat.generalizingMap p hηx
    obtain ⟨T, hT, hyT⟩ := Set.mem_sUnion.mp
      (show y ∈ ⋃₀ irreducibleComponents P by rw [sUnion_irreducibleComponents]; simp)
    set W : irreducibleComponents P := ⟨T, hT⟩ with hWdef
    have hξy : W.2.1.genericPoint ⤳ y :=
      (W.2.1.isGenericPoint_genericPoint
        (isClosed_of_mem_irreducibleComponents (W : Set P) W.2)).specializes hyT
    obtain ⟨V', hV'⟩ := exists_irreducibleComponent_map_genericPoint p W
    have hmem : (genericPoints.ofComponent V : Z) ∈ (V' : Set Z) := by
      have h := (hpy ▸ hξy.map p.continuous : p.base W.2.1.genericPoint ⤳
        (genericPoints.ofComponent V : Z)).mem_closure
      rw [hV', (genericPoints.isGenericPoint_ofComponent V').def] at h
      exact h
    have hVV' : (V : Set Z) ⊆ (V' : Set Z) := by
      rw [← (genericPoints.isGenericPoint_ofComponent V).def]
      exact closure_minimal (Set.singleton_subset_iff.mpr hmem)
        (isClosed_of_mem_irreducibleComponents (V' : Set Z) V'.2)
    have hVeq : V' = V := Subtype.ext (Set.Subset.antisymm (V.2.2 V'.2.1 hVV') hVV')
    exact ⟨W, hstep W V (by rw [hV', hVeq])⟩
  rw [schemeDeltaDimension_eq_iSup, schemeDeltaDimension_eq_iSup, ← hαdef, ← hβdef,
    iSup_add_coe β (r : ℤ)]
  refine le_antisymm (iSup_le fun W ↦ ?_) (iSup_le fun V ↦ ?_)
  · obtain ⟨V, hWV⟩ := hsource W
    rw [hWV]
    exact le_iSup (fun V ↦ β V + ((r : ℤ) : EInt)) V
  · obtain ⟨W, hWV⟩ := htarget V
    rw [← hWV]
    exact le_iSup α W

/-- **Stacks 02R8.** Over an irreducible base, every irreducible component of the source of a
flat morphism of relative dimension `r` has delta-dimension `dim_δ(Z) + r`. -/
theorem deltaDimension_irreducibleComponent_eq_add_of_irreducible (C : ChowSituation.{u})
    {P Z : Scheme.{u}} (p : P ⟶ Z) [LocallyOfFiniteType p] [Flat p] (q : Z ⟶ C.S)
    [LocallyOfFiniteType q] [IrreducibleSpace Z] (r : ℕ)
    (hrel : AlgebraicGeometry.RelativeDimension p r) (W : irreducibleComponents P) :
    deltaDimension C (p ≫ q)
        ⟨(W : Set P), W.2.1, isClosed_of_mem_irreducibleComponents (W : Set P) W.2⟩ =
      deltaDimension C q ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩ +
        (r : ℤ) := by
  exact deltaDimension_comp_eq_add_of_map_eq C p q r hrel W _ _ (genericPoint_spec Z)
    (map_genericPoint_irreducibleComponent_eq_genericPoint p W)

/-! ### The scheme-theoretic inverse image of a closed subscheme -/

/-- Relative dimension is stable under base change: the second projection of the fibre product
of a morphism locally of finite type of relative dimension `r` with any morphism again has
relative dimension `r`. -/
theorem relativeDimension_pullback_snd {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (i : Z ⟶ Y) (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) :
    AlgebraicGeometry.RelativeDimension (pullback.snd f i) r :=
  (MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := AlgebraicGeometry.locallyOfFiniteTypeRelativeDimension r)
    (IsPullback.of_hasPullback f i) ⟨inferInstance, hf⟩).2

/-- **Stacks 02R8.** The scheme-theoretic inverse image of a closed subscheme `i : Z ⟶ Y` along
a flat morphism `f : X ⟶ Y` of relative dimension `r` has delta-dimension `dim_δ(Z) + r`, as
soon as its projection to `Z` meets every irreducible component of `Z`. -/
@[stacks 02R8 "dimension of the inverse image"]
theorem schemeDeltaDimension_pullback_snd_comp (C : ChowSituation.{u}) {X Y Z : Scheme.{u}}
    (g : Y ⟶ C.S) [LocallyOfFiniteType g] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f] (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (i : Z ⟶ Y) [IsClosedImmersion i]
    (hmeets : ∀ V : irreducibleComponents Z,
      ∃ x : (pullback f i : Scheme.{u}), (pullback.snd f i).base x ∈ (V : Set Z)) :
    schemeDeltaDimension C (pullback.snd f i ≫ i ≫ g) =
      schemeDeltaDimension C (i ≫ g) + ((r : ℤ) : EInt) :=
  have : Flat (pullback.snd f i) :=
    Flat.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f i) inferInstance
  schemeDeltaDimension_comp_eq_add C (i ≫ g) (pullback.snd f i) r
    (relativeDimension_pullback_snd f i r hf) hmeets

/-- **Stacks 02R8.** Over an irreducible closed subscheme `i : Z ⟶ Y`, every irreducible
component of the scheme-theoretic inverse image along a flat morphism `f : X ⟶ Y` of relative
dimension `r` has delta-dimension `dim_δ(Z) + r`. -/
@[stacks 02R8 "dimension of components"]
theorem deltaDimension_irreducibleComponent_pullback_snd_comp (C : ChowSituation.{u})
    {X Y Z : Scheme.{u}} (g : Y ⟶ C.S) [LocallyOfFiniteType g] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Flat f] (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r)
    (i : Z ⟶ Y) [IsClosedImmersion i] [IrreducibleSpace Z]
    (W : irreducibleComponents (pullback f i : Scheme.{u})) :
    deltaDimension C (pullback.snd f i ≫ i ≫ g)
        ⟨(W : Set (pullback f i : Scheme.{u})), W.2.1,
          isClosed_of_mem_irreducibleComponents (W : Set (pullback f i : Scheme.{u})) W.2⟩ =
      deltaDimension C (i ≫ g)
          ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩ + (r : ℤ) :=
  have : Flat (pullback.snd f i) :=
    Flat.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f i) inferInstance
  deltaDimension_irreducibleComponent_eq_add_of_irreducible C (pullback.snd f i) (i ≫ g) r
    (relativeDimension_pullback_snd f i r hf) W

end Stacks.Chow

end
