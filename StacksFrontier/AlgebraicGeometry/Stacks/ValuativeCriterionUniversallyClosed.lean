module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosureImageValuativePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFieldValuedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDecent
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedSmoothLocal
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeExistenceUniversallyClosed

/-!
# A quasi-compact morphism satisfying valuative existence is universally closed (Stacks 0CLW)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which is quasi-compact
(**Stacks 050U**) and satisfies the existence part of the valuative criterion
(**Stacks 0CLK**). Then `f` is universally closed (**Stacks 0513**, part (2)).

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isClosed_of_isAffine`: a quasi-compact 1-morphism
  into a represented algebraic stack with affine underlying scheme which satisfies the existence
  part of the valuative criterion is closed on points.
* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.universallyClosed_of_isQuasiCompactMorphism_of_valuativeCriterionExistence`:
  **Stacks 0CLW**.

## Implementation notes

Both hypotheses are stable under base change — quasi-compactness by **Stacks 050V** and the
existence part by **Stacks 0CLL** — and universal closedness is closedness of every base change
to an affine scheme of the site by **Stacks 0CL3**, so the statement reduces to the case of a
quasi-compact `f : 𝒳 ⟶ U` with `U` an affine scheme of the site. There `𝒳` is a quasi-compact
algebraic stack, so **Stacks 04YC** gives a surjective smooth presentation `a : V ⟶ 𝒳` by an
affine scheme `V` of the site.

The source gives a closed subset `T ⊆ |𝒳|` the reduced induced *algebraic stack* structure
(**Stacks 0509**) and concludes from the case `T = |𝒳|`. That lemma is not in this library, so
the reduced induced structure is taken on the chart instead: `|a|` is surjective, so
`|f|(T) = |f|(|a|(|a|⁻¹T))`, and the closed subset `|a|⁻¹T` of the affine scheme `V` carries the
reduced induced closed subscheme `Z ⊆ V` of **Stacks 01J3**. Since `Z` and `U` are affine the
composite `Z ⟶ 𝒳 ⟶ U` is quasi-compact, its image on points is exactly `|f|(T)`, and
**Stacks 0CL2** produces, over a point `y` in the closure of that image, a valuative square whose
generic point factors through `Z` and whose special point hits `y`. The existence part applied to
that square — read as a square for `f` by composing its generic point with `Z ⟶ 𝒳` — yields a
dominating valuation ring `A'` and a lift `Spec A' ⟶ 𝒳`. Its closed point lies over `y`, because
`A' ⟶ 𝒴` dominates, and lies in `T`, because the closed point of `Spec A'` specializes every
point of `Spec A'` while the generic point of the lift lands in the image of `|Z| → |𝒳|`, which is
contained in the closed set `T`.

## References

* [Stacks Project, Tag 0CLW](https://stacks.math.columbia.edu/tag/0CLW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

namespace AlgebraicGeometry

universe u w

/-- The closed point of the spectrum of a local ring lies in the closure of every point: every
prime ideal is contained in the maximal one. -/
private theorem closedPoint_mem_closure_singleton (R : Type u) [CommRing R] [IsLocalRing R]
    (z : (Spec (.of R) : Scheme.{u})) :
    (IsLocalRing.closedPoint R : (Spec (.of R) : Scheme.{u})) ∈
      closure ({z} : Set (Spec (.of R))) := by
  have h : ∀ z' : PrimeSpectrum R,
      IsLocalRing.closedPoint R ∈ closure ({z'} : Set (PrimeSpectrum R)) := by
    intro z'
    rw [PrimeSpectrum.closure_singleton]
    exact IsLocalRing.le_maximalIdeal z'.isPrime.ne_top
  exact h z

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The morphism of the site underlying a 1-morphism of represented categories fibred in
groupoids whose based functor is postcomposition with a morphism `g` of the site is `g`. -/
theorem schemeMapOfFunctor_eq_of_toFunctor_eq {W U : BigFppfOver B S hS}
    (b : (schemeFibredCategory B S hS W).based ⥤ᵇ (schemeFibredCategory B S hS U).based)
    (g : W ⟶ U) (h : b.toFunctor = Over.map g) :
    schemeMapOfFunctor B S hS b = g := by
  have hb : b = overMapBased B S hS g := by
    cases b
    cases h
    rfl
  rw [hb, schemeMapOfFunctor_overMapBased]

/-- **A 1-morphism of represented algebraic stacks with quasi-compact underlying morphism of
schemes is quasi-compact.** Such a 1-morphism is 2-isomorphic to the one induced by the morphism
`AlgebraicGeometry.Stack.schemeMapOfFunctor` of the site underlying it, for which
quasi-compactness in the sense of **Stacks 050U** is
`AlgebraicGeometry.Stack.isQuasiCompactMorphism_schemeAlgebraicStackMap`. -/
theorem isQuasiCompactMorphism_of_represented {W U : BigFppfOver B S hS}
    (g : schemeStack.{u, w} B S hS W ⟶ schemeStack.{u, w} B S hS U)
    (hg : QuasiCompact ((BigFppfOver.toScheme B S hS).map
      (schemeMapOfFunctor B S hS g.hom.hom))) :
    IsQuasiCompactMorphism.{u, w} B S hS g := by
  set c := schemeMapOfFunctor B S hS g.hom.hom
  let η : g.hom ⟶ schemeFibredCategoryMap B S hS c :=
    Bicategory.InducedBicategory.mkHom₂ (basedNatTransOfSchemeMapEq B S hS g.hom.hom
      (overMapBased B S hS c) (schemeMapOfFunctor_overMapBased B S hS c).symm)
  exact isQuasiCompactMorphism_of_comp_of_isSurjective B S hS (𝟙 _)
    (schemeAlgebraicStackMap.{u, w} B S hS c) g
    ((λ_ g) ≪≫ Bicategory.InducedBicategory.isoMk
      (@asIso _ _ _ _ η ((CatFiberedInGroupoids.homGroupoid _ _).all_isIso η)))
    (isSurjective_id.{u, w} B S hS _)
    (isQuasiCompactMorphism_schemeAlgebraicStackMap.{u, w} B S hS c
      (Space.isQuasiCompact_yoneda_map_of_quasiCompact B S hS c hg))

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

namespace ValuativeSquare

/-- The object of the site carrying the special point of a valuative square: the spectrum of its
valuation ring, with its structure morphism to `S`. -/
noncomputable abbrev specialObject {f : 𝒳 ⟶ 𝒴} (q : ValuativeSquare B S hS f) :
    BigFppfOver B S hS :=
  siteObject B S hS q.ring_mem q.base

/-- The object of the site carrying the generic point of a valuative square: the spectrum of the
fraction field of its valuation ring, with its structure morphism to `S`. -/
noncomputable abbrev genericObject {f : 𝒳 ⟶ 𝒴} (q : ValuativeSquare B S hS f) :
    BigFppfOver B S hS :=
  siteObject B S hS q.field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)

end ValuativeSquare

/-- **The existence part of the valuative criterion, read on points.** Let `q` be a valuative
square for a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` satisfying the existence part of
the valuative criterion (**Stacks 0CLK**). Then there are a point `pR` of the spectrum of the
valuation ring of `q` at its closed point and a point `x` of `|𝒳|` such that `|f|(x)` is the image
of `pR` under the special point of `q`, and `x` lies in the closure of the image of the generic
point of `q`. -/
theorem exists_point_of_valuativeSquare (f : 𝒳 ⟶ 𝒴)
    (hex : ValuativeCriterion.Existence B S hS f) (q : ValuativeSquare B S hS f) :
    ∃ (pR : points B S hS
        (schemeFibredCategory B S hS (q.specialObject B S hS)).val
        (schemeFibredCategory B S hS (q.specialObject B S hS)).property)
      (x : points B S hS 𝒳.val.val 𝒳.val.property),
      schemePoint B S hS (q.specialObject B S hS) pR = IsLocalRing.closedPoint q.R ∧
        pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒴.val.property f.hom.hom x =
          pointsMap B S hS _ _ 𝒴.val.property q.y.hom pR ∧
        x ∈ @closure _ (pointTopology B S hS 𝒳.val)
          (Set.range (pointsMap B S hS
            (schemeFibredCategory B S hS (q.genericObject B S hS)).val
            (schemeFibredCategory B S hS (q.genericObject B S hS)).property
            𝒳.val.property q.x.hom)) := by
  obtain ⟨e, ⟨d⟩⟩ := hex q
  have hloc := e.isLocalHom
  obtain ⟨pc, hpc⟩ := schemePoint_surjective B S hS
    (siteObject B S hS e.ring_mem (Spec.map (CommRingCat.ofHom e.ringMap) ≫ q.base))
    (IsLocalRing.closedPoint e.R')
  refine ⟨pointsMap B S hS _ _ _ e.a.hom pc,
    pointsMap B S hS _ _ 𝒳.val.property d.a.hom pc, ?_, ?_, ?_⟩
  · rw [schemePoint_naturality, hpc,
      schemeMapOfFunctor_eq_of_toFunctor_eq B S hS e.a.hom e.specialOver e.a_canonical]
    show (B.inclusion).map e.specialOver.left _ = _
    rw [e.specialOver_left]
    exact AlgebraicGeometry.Spec_closedPoint
  · rw [pointsMap_comp, pointsMap_comp]
    exact congrFun (pointsMap_eq_of_basedNatTrans B S hS _ _ 𝒴.val.property d.β.hom).symm pc
  · obtain ⟨pg, -⟩ := schemePoint_surjective B S hS
      (siteObject B S hS e.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap e.R' e.K')) ≫
          Spec.map (CommRingCat.ofHom e.ringMap) ≫ q.base))
      (IsLocalRing.closedPoint e.K')
    let _ : TopologicalSpace (points B S hS
        (schemeFibredCategory B S hS (siteObject B S hS e.ring_mem
          (Spec.map (CommRingCat.ofHom e.ringMap) ≫ q.base))).val
        (schemeFibredCategory B S hS (siteObject B S hS e.ring_mem
          (Spec.map (CommRingCat.ofHom e.ringMap) ≫ q.base))).property) :=
      pointTopology B S hS (schemeFibredCategory B S hS (siteObject B S hS e.ring_mem
          (Spec.map (CommRingCat.ofHom e.ringMap) ≫ q.base)))
    let _ : TopologicalSpace (points B S hS 𝒳.val.val 𝒳.val.property) :=
      pointTopology B S hS 𝒳.val
    set hh := pointsHomeomorphScheme B S hS (siteObject B S hS e.ring_mem
      (Spec.map (CommRingCat.ofHom e.ringMap) ≫ q.base)) with hhdef
    set w := pointsMap B S hS _ _ _ e.j.hom pg with hwdef
    have key : hh pc ∈ closure ({hh w} : Set _) := by
      rw [hhdef, pointsHomeomorphScheme_eq_schemePoint B S hS _ pc,
        pointsHomeomorphScheme_eq_schemePoint B S hS _ w, hpc]
      exact AlgebraicGeometry.closedPoint_mem_closure_singleton e.R' _
    have hmem : pc ∈ closure ({w} : Set _) := by
      rwa [hh.isInducing.closure_eq_preimage_closure_image, Set.image_singleton]
    have himg := image_closure_subset_closure_image
      (continuous_pointsMap B S hS
        (schemeFibredCategory B S hS (siteObject B S hS e.ring_mem
          (Spec.map (CommRingCat.ofHom e.ringMap) ≫ q.base))) 𝒳.val d.a.hom)
      (Set.mem_image_of_mem _ hmem)
    rw [Set.image_singleton] at himg
    refine closure_mono ?_ himg
    rw [Set.singleton_subset_iff]
    refine ⟨pointsMap B S hS _ _ _ e.k.hom pg, ?_⟩
    rw [hwdef, pointsMap_comp, pointsMap_comp]
    exact (congrFun (pointsMap_eq_of_basedNatTrans B S hS _ _ 𝒳.val.property d.α.hom) pg).symm

end Stack

namespace Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Affine

variable {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS} {U : BigFppfOver B S hS}

/-- A closed subset of the scheme underlying an object `V` of the site is the image of a closed
immersion from an object of the site: its reduced induced closed subscheme. -/
private theorem exists_isClosedImmersion_toScheme_map_range_eq {V : BigFppfOver B S hS}
    (TV : Set ((BigFppfOver.toScheme B S hS).obj V)) (hTV : _root_.IsClosed TV) :
    ∃ (Z : BigFppfOver B S hS) (zi : Z ⟶ V),
      AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map zi) ∧
        Set.range ((BigFppfOver.toScheme B S hS).map zi).base = TV := by
  set I : Scheme.IdealSheafData ((BigFppfOver.toScheme B S hS).obj V) :=
    Scheme.IdealSheafData.vanishingIdeal ⟨TV, hTV⟩
  have hZ : B.Contains I.subscheme :=
    Scheme.size_lt_of_isClosedImmersion I.subschemeι V.left.property
  exact ⟨Over.mk (⟨I.subschemeι ≫ V.hom.1⟩ : B.obj hZ ⟶ B.obj hS),
    Over.homMk (⟨I.subschemeι⟩ : B.obj hZ ⟶ V.left),
    by exact inferInstanceAs (AlgebraicGeometry.IsClosedImmersion I.subschemeι),
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal (X :=
      (BigFppfOver.toScheme B S hS).obj V) ⟨TV, hTV⟩⟩

/-- The composite of the 1-morphism induced by a closed immersion `zi` into an affine scheme `V`
with any `aa ≫ f` to an affine scheme is quasi-compact. -/
private theorem isQuasiCompactMorphism_schemeStackMap_comp
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (f : 𝒳 ⟶ Stack.schemeStack.{u, w} B S hS U) {Z V : BigFppfOver B S hS}
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) (zi : Z ⟶ V)
    [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map zi)]
    (aa : Stack.schemeStack.{u, w} B S hS V ⟶ 𝒳) :
    Stack.IsQuasiCompactMorphism.{u, w} B S hS
      ((Stack.schemeStackMap.{u, w} B S hS zi ≫ aa) ≫ f) := by
  have hmap : Stack.schemeMapOfFunctor B S hS
      ((Stack.schemeStackMap.{u, w} B S hS zi ≫ aa) ≫ f).hom.hom
      = zi ≫ Stack.schemeMapOfFunctor B S hS ((aa ≫ f).hom.hom) :=
    Stack.schemeMapOfFunctor_comp_overMapBased B S hS zi ((aa ≫ f).hom.hom)
  have h1 : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := hV
  have h2 : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  exact Stack.isQuasiCompactMorphism_of_represented B S hS _
    (by rw [hmap, Functor.map_comp]; infer_instance)

/-- The image on points of a composite of 1-morphisms of algebraic stacks is the image under the
second map of the image of the first. -/
private theorem range_pointsMap_comp {𝒜 ℬ 𝒞 : Stack.AlgebraicStacks.{u, w} B S hS}
    (g : 𝒜 ⟶ ℬ) (f : ℬ ⟶ 𝒞) :
    Set.range (Stack.pointsMap B S hS 𝒜.val.val 𝒜.val.property 𝒞.val.property (g ≫ f).hom.hom) =
      Stack.pointsMap B S hS ℬ.val.val ℬ.val.property 𝒞.val.property f.hom.hom ''
        Set.range (Stack.pointsMap B S hS 𝒜.val.val 𝒜.val.property ℬ.val.property g.hom.hom) := by
  rw [← Set.range_comp]
  exact congrArg Set.range (funext fun z =>
    (Stack.pointsMap_comp B S hS _ _ _ 𝒞.val.property _ _ z).symm)

/-- Given a surjective chart `aa` of `𝒳` by an affine scheme `V` and a quasi-compact `f` to an
affine scheme, every closed subset `T` of the points of `𝒳` is the image on points of a
1-morphism `h0` from an object of the site with `h0 ≫ f` quasi-compact: the reduced induced
closed subscheme of the chart over `T`. -/
private theorem exists_isQuasiCompactMorphism_comp_range_eq
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (f : 𝒳 ⟶ Stack.schemeStack.{u, w} B S hS U) {V : BigFppfOver B S hS}
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (aa : Stack.schemeStack.{u, w} B S hS V ⟶ 𝒳)
    (hasurj : Function.Surjective (Stack.pointsMap B S hS
      (Stack.schemeFibredCategory B S hS V).val
      (Stack.schemeFibredCategory B S hS V).property 𝒳.val.property aa.hom.hom))
    (T : Set (Stack.points B S hS 𝒳.val.val 𝒳.val.property))
    (hT : @_root_.IsClosed _ (Stack.pointTopology B S hS 𝒳.val) T) :
    ∃ (Z : BigFppfOver B S hS) (h0 : Stack.schemeStack.{u, w} B S hS Z ⟶ 𝒳),
      Stack.IsQuasiCompactMorphism.{u, w} B S hS (h0 ≫ f) ∧
        Set.range (Stack.pointsMap B S hS
          (Stack.schemeFibredCategory B S hS Z).val
          (Stack.schemeFibredCategory B S hS Z).property 𝒳.val.property h0.hom.hom) = T := by
  let _ : TopologicalSpace (Stack.points B S hS
      (Stack.schemeFibredCategory B S hS V).val
      (Stack.schemeFibredCategory B S hS V).property) :=
    Stack.pointTopology B S hS (Stack.schemeFibredCategory B S hS V)
  let _ : TopologicalSpace (Stack.points B S hS 𝒳.val.val 𝒳.val.property) :=
    Stack.pointTopology B S hS 𝒳.val
  -- the closed subset of the chart over the given closed subset of the points of `𝒳`, and
  -- its reduced induced closed subscheme, as an object of the site over `S`
  obtain ⟨Z, zi, _, hrange⟩ := exists_isClosedImmersion_toScheme_map_range_eq B S hS
    (Stack.pointsHomeomorphScheme B S hS V '' (Stack.pointsMap B S hS _ _ 𝒳.val.property
      aa.hom.hom ⁻¹' T))
    ((Stack.pointsHomeomorphScheme B S hS V).isClosedMap _
      (hT.preimage (Stack.continuous_pointsMap B S hS _ _ aa.hom.hom)))
  have hszi : Set.range (Stack.pointsMap B S hS
        (Stack.schemeFibredCategory B S hS Z).val
        (Stack.schemeFibredCategory B S hS Z).property
        (Stack.schemeFibredCategory B S hS V).property
        (Stack.schemeStackMap.{u, w} B S hS zi).hom.hom)
      = Stack.pointsMap B S hS _ _ 𝒳.val.property aa.hom.hom ⁻¹' T := by
    refine Set.image_injective.2 (Stack.pointsHomeomorphScheme B S hS V).injective ?_
    rw [← hrange, ← Set.range_comp]
    let _ := Stack.pointTopology B S hS (Stack.schemeFibredCategory B S hS Z)
    exact (congrArg Set.range
      (funext (Stack.pointsHomeomorphScheme_naturality B S hS zi))).trans
      ((Stack.pointsHomeomorphScheme B S hS Z).surjective.range_comp _)
  -- the subscheme of the chart, mapping to `𝒳` and quasi-compactly to the affine target
  refine ⟨Z, Stack.schemeStackMap.{u, w} B S hS zi ≫ aa,
    isQuasiCompactMorphism_schemeStackMap_comp B S hS hU f hV zi aa, ?_⟩
  -- its image on points is the given closed subset
  refine (range_pointsMap_comp B S hS (Stack.schemeStackMap.{u, w} B S hS zi) aa).trans ?_
  rw [hszi, Set.image_preimage_eq _ hasurj]

/-- **A quasi-compact 1-morphism to an affine scheme of the site satisfying the existence part of
the valuative criterion is closed on points.** This is the affine-target case of
**Stacks 0CLW**. -/
theorem isClosed_of_isAffine (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (f : 𝒳 ⟶ Stack.schemeStack.{u, w} B S hS U)
    (hqc : Stack.IsQuasiCompactMorphism B S hS f)
    (hex : Stack.ValuativeCriterion.Existence B S hS f) :
    IsClosed B S hS f := by
  have hXqc : Stack.IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property :=
    Stack.isQuasiCompactStack_of_isQuasiCompactMorphism.{u, w} B S hS f hqc
      (Stack.isQuasiCompactStack_schemeStack_of_isAffine.{u, w} B S hS U hU)
  obtain ⟨V, hV, aa, hasurj, -⟩ :=
    (Stack.isQuasiCompactStack_iff_hasAffineSmoothPresentation.{u, w} B S hS 𝒳).1 hXqc
  intro T hT
  let _ : TopologicalSpace (Stack.points B S hS 𝒳.val.val 𝒳.val.property) :=
    Stack.pointTopology B S hS 𝒳.val
  let _ : TopologicalSpace (Stack.points B S hS
      (Stack.schemeFibredCategory B S hS U).val
      (Stack.schemeFibredCategory B S hS U).property) :=
    Stack.pointTopology B S hS (Stack.schemeFibredCategory B S hS U)
  obtain ⟨Z, h0, hg0qc, hrh⟩ :=
    exists_isQuasiCompactMorphism_comp_range_eq B S hS hU f hV aa hasurj T hT
  -- `|f|` carries that image to the goal
  have hgoal : Set.range (Stack.pointsMap B S hS
        (Stack.schemeFibredCategory B S hS Z).val
        (Stack.schemeFibredCategory B S hS Z).property
        (Stack.schemeFibredCategory B S hS U).property (h0 ≫ f).hom.hom)
      = Stack.pointsMap B S hS 𝒳.val.val 𝒳.val.property
          (Stack.schemeFibredCategory B S hS U).property f.hom.hom '' T := by
    rw [← hrh]
    exact range_pointsMap_comp B S hS h0 f
  -- the valuative argument at a point of the closure of that image
  rw [← closure_subset_iff_isClosed]
  intro yy hyy
  rw [← hgoal] at hyy
  obtain ⟨q, hzres, hq⟩ :=
    Stack.exists_valuationRing_of_mem_closure_range_pointsMap B S hS (h0 ≫ f) hg0qc yy hyy
  set qq := Stack.ValuativeSquare.compRight B S hS q
  obtain ⟨pR, x, hpRpt, hfx, hxcl⟩ := Stack.exists_point_of_valuativeSquare B S hS f hex qq
  have hsub : Set.range (Stack.pointsMap B S hS
      (Stack.schemeFibredCategory B S hS
        (Stack.ValuativeSquare.genericObject B S hS qq)).val
      (Stack.schemeFibredCategory B S hS
        (Stack.ValuativeSquare.genericObject B S hS qq)).property
      𝒳.val.property qq.x.hom) ⊆ T := by
    rw [← hrh]
    rintro - ⟨z, rfl⟩
    exact ⟨Stack.pointsMap B S hS _ _ _ q.x.hom z,
      Stack.pointsMap_comp B S hS _ _ _ 𝒳.val.property _ _ z⟩
  refine ⟨x, closure_minimal hsub hT hxcl, ?_⟩
  rwa [hfx, Stack.schemePoint_injective B S hS _
    (hpRpt.trans (Stack.schemePoint_closedPointFieldValuedPoint B S hS
      (Stack.ValuativeSquare.specialObject B S hS qq) (IsLocalRing.closedPoint qq.R) hzres).symm),
    Stack.pointsMap_class]

end Affine

/-- **Stacks 0CLW.** A 1-morphism of algebraic stacks over `S` which is quasi-compact
(**Stacks 050U**) and satisfies the existence part of the valuative criterion (**Stacks 0CLK**)
is universally closed (**Stacks 0513**, part (2)). -/
@[stacks 0CLW]
theorem universallyClosed_of_isQuasiCompactMorphism_of_valuativeCriterionExistence
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hqc : Stack.IsQuasiCompactMorphism B S hS f)
    (hex : Stack.ValuativeCriterion.Existence B S hS f) :
    UniversallyClosed B S hS f := by
  refine ((universallyClosed_tfae B S hS f).out 3 1).1 fun U hU g => ?_
  exact isClosed_of_isAffine B S hS hU _
    (Stack.isQuasiCompactMorphism_baseChange B S hS f g _
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f) hqc)
    (Stack.valuativeCriterionExistence_baseChange B S hS f g _
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f) hex)

end Stack.AlgebraicStacks

end AlgebraicGeometry

end
