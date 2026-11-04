module

public import Mathlib.Logic.Small.Set
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubstackSchemeStackTop
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeTheoreticImage
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.GenericDominantDimensionFormula
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionChartComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeTheoreticImageDense
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionJacobsonPseudoCatenary
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.IrreducibleSchemeChart
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionSubstackFactorization
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImageDominant
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackPropertyBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImageExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubstackIntersection
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickenedOriginsScheme
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet

/-!
# Stacks 0DS4 without quasi-compactness is false

The upstream statement of Stacks 0DS4 reads: *let `f : 𝒯 → 𝒳` be a locally of finite type
morphism of Jacobson, pseudo-catenary, and locally Noetherian algebraic stacks, whose source is
irreducible and whose target is quasi-separated, and let `𝒵 ↪ 𝒳` denote the scheme-theoretic
image of `𝒯`. Then for all `t ∈ |𝒯|`, `dim_t(𝒯_{f(t)}) ≥ dim 𝒯 − dim 𝒵`, and there is a non-empty
(equivalently, dense) open subset of `|𝒯|` over which equality holds.* It does not ask `f` to be
quasi-compact, and the equality clause is then false. This file proves so, for algebraic stacks
over a big fppf site exactly as the statement is formalized in this library.

The witness is the affine line `T` with infinitely many origins, the `n`-th thickened to order
`n`, with its morphism `f : T ⟶ 𝔸¹` given by the global nilpotent function `ε`, viewed as a
1-morphism of algebraic stacks over the big fppf site of `𝔸¹`. Every hypothesis holds. The scheme
theoretic image of `f` is all of `𝔸¹`, so `dim 𝒵 ≥ 1`, while `dim 𝒯 = 1` and every fibre
dimension is `1`; the equality `dim 𝒯 = dim 𝒵 + dim_t(𝒯_{f(t)})` holds at no point.

## Main results

* `AlgebraicGeometry.ThickenedOrigin.exists_counterexample`: the witness, with all hypotheses.
* `AlgebraicGeometry.Stack.not_forall_dimension_le_add_and_exists_isOpen_dense_eq`: the statement
  of Stacks 0DS4 with quasi-compactness of `f` omitted is false.

## Implementation notes

The subtraction of the source is an addition here, the dimensions being extended integers, as in
the form of Stacks 0DS4 for quasi-compact `f` in the namespace `AlgebraicGeometry.Stack`, whose
statement the refuted proposition repeats with its quasi-compactness hypothesis removed.
The universes are arbitrary; the field is `ULift ℚ`.

## References

* [Stacks Project, Tag 0CMI](https://stacks.math.columbia.edu/tag/0CMI)
* [Stacks Project, Tag 0DS4](https://stacks.math.columbia.edu/tag/0DS4)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.ThickenedOrigin

open Stack

universe u w

variable (k : Type u) [Field k]

/-- Some big fppf site contains both the line `𝔸¹_k` and the scheme `T`. -/
theorem exists_bigFppfSite :
    ∃ B : BigFppfSite.{u}, B.Contains (Spec (lineRing k)) ∧ B.Contains (T k) := by
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing ({Spec (lineRing k), T k} : Set Scheme.{u})
  exact ⟨B, hB _ (Set.mem_insert _ _), hB _ (Set.mem_insert_of_mem _ rfl)⟩

section Site

variable (B : BigFppfSite.{u}) (hS : B.Contains (Spec (lineRing k))) (hT : B.Contains (T k))

/-- The line `𝔸¹_k`, as the terminal object of the big fppf site over itself. -/
abbrev lineObject : BigFppfOver B (Spec (lineRing k)) hS := Over.mk (𝟙 (B.obj hS))

/-- The scheme `T`, as an object of the big fppf site over the line through `f`. -/
abbrev TObject : BigFppfOver B (Spec (lineRing k)) hS :=
  Over.mk (ObjectProperty.homMk (toLine k) : B.obj hT ⟶ B.obj hS)

/-- The morphism `f` of the site. -/
abbrev toLineObject : TObject k B hS hT ⟶ lineObject k B hS :=
  Over.homMk (ObjectProperty.homMk (toLine k)) (Category.comp_id _)

/-- The morphism `f` of the site is locally of finite type. -/
instance : LocallyOfFiniteType ((BigFppfOver.toScheme B _ hS).map (toLineObject k B hS hT)) :=
  inferInstanceAs (LocallyOfFiniteType (toLine k))

/-- The scheme `T`, as an object of the site, is locally Noetherian. -/
instance : IsLocallyNoetherian ((BigFppfOver.toScheme B _ hS).obj (TObject k B hS hT)) :=
  inferInstanceAs (IsLocallyNoetherian (T k))

/-- The scheme `T`, as an object of the site, is a Jacobson space. -/
instance : JacobsonSpace ((BigFppfOver.toScheme B _ hS).obj (TObject k B hS hT)) :=
  inferInstanceAs (JacobsonSpace (T k))

/-- The scheme `T`, as an object of the site, is irreducible. -/
instance : IrreducibleSpace ((BigFppfOver.toScheme B _ hS).obj (TObject k B hS hT)) :=
  inferInstanceAs (IrreducibleSpace (T k))

/-- The scheme `T`, as an object of the site, is nonempty. -/
instance : Nonempty ((BigFppfOver.toScheme B _ hS).obj (TObject k B hS hT)) :=
  inferInstanceAs (Nonempty (T k))

/-- The line `𝔸¹_k`, as an object of the site, is locally Noetherian. -/
instance : IsLocallyNoetherian ((BigFppfOver.toScheme B _ hS).obj (lineObject k B hS)) :=
  inferInstanceAs (IsLocallyNoetherian (Spec (lineRing k)))

/-- The line `𝔸¹_k`, as an object of the site, is a Jacobson space. -/
instance : JacobsonSpace ((BigFppfOver.toScheme B _ hS).obj (lineObject k B hS)) :=
  inferInstanceAs (JacobsonSpace (Spec (lineRing k)))

/-- **The equality clause of Stacks 0DS4 fails for `f : T ⟶ 𝔸¹`.** For the scheme theoretic
image `𝒵` of the induced 1-morphism of algebraic stacks, `dim(𝒯) = dim(𝒵) + dim_t(𝒯_{f(t)})`
holds at no point `t`: the left side is `1`, while `dim(𝒵) ≥ 1` and the fibre dimension is `1`. -/
theorem dimension_ne_closedSubstackDimension_add_relativeStackDimensionAt
    {P : ObjectProperty (schemeStack.{u, w} B _ hS (lineObject k B hS)).val.val.obj}
    (hP : IsSchemeTheoreticImage (schemeStackMap.{u, w} B _ hS (toLineObject k B hS hT)) P)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B _ hS
      (schemeStackMap.{u, w} B _ hS (toLineObject k B hS hT)))
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B _ hS (schemeStack.{u, w} B _ hS (TObject k B hS hT)))
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B _ hS (schemeStack.{u, w} B _ hS (lineObject k B hS)))
    (t : points B _ hS (schemeStack.{u, w} B _ hS (TObject k B hS hT)).val.val
      (schemeStack.{u, w} B _ hS (TObject k B hS hT)).val.property) :
    dimension B _ hS (schemeStack.{u, w} B _ hS (TObject k B hS hT)) h𝒯 ≠
      closedSubstackDimension B _ hS (schemeStack.{u, w} B _ hS (lineObject k B hS)) P hP.1
          hP.isAlgebraicStack h𝒳 +
        relativeStackDimensionAt.{u, w} B _ hS
          (schemeStackMap.{u, w} B _ hS (toLineObject k B hS hT)) hf h𝒯 h𝒳 t := by
  have hdim : dimension B _ hS (schemeStack.{u, w} B _ hS (TObject k B hS hT)) h𝒯 = 1 :=
    (dimension_schemeStack_of_forall B _ hS _ h𝒯 1 (topologicalKrullDimAt_T k)).trans rfl
  have hrel : relativeStackDimensionAt.{u, w} B _ hS
      (schemeStackMap.{u, w} B _ hS (toLineObject k B hS hT)) hf h𝒯 h𝒳 t = 1 :=
    (relativeStackDimensionAt_schemeStackMap_of_forall B _ hS _ hf h𝒯 h𝒳 1
      (topologicalKrullDimAt_fiber_toLine k) t).trans rfl
  have hA := hP.isAlgebraicStack
  have := hP.1.1
  have hγ : P (Over.mk (toLineObject k B hS hT)) :=
    P.prop_of_iso (Over.isoMk (Iso.refl _) (by rfl))
      ((factorsThroughSubstack_iff_forall _).1 hP.2.1 (Over.mk (𝟙 _)))
  have hall := forall_prop_of_isClosedSubstack_schemeStack hP.1 _ hγ
    (fun {W} i hi h hh => by
      have := hi
      exact isIso_of_isClosedImmersion k ((BigFppfOver.toScheme B _ hS).map i)
        ((BigFppfOver.toScheme B _ hS).map h) (by rw [← Functor.map_comp, hh]; rfl))
  have hZ : 1 ≤ closedSubstackDimension B _ hS (schemeStack.{u, w} B _ hS (lineObject k B hS)) P
      hP.1 hA h𝒳 := by
    let z0 := AlgebraicStacks.pointsMap B _ hS (factorsThroughSubstackHom _ hA hP.2.1) t
    refine le_trans (le_of_eq ?_) (le_iSup _ z0)
    rw [dimensionAtPoint_fullSubcategory_eq_of_forall _ hP.1 hA hall h𝒳 z0,
      dimensionAtPoint_schemeStack_of_forall B _ hS _ h𝒳 1 (topologicalKrullDimAt_line k)]
    rfl
  rw [hdim, hrel]
  intro h
  generalize closedSubstackDimension B _ hS (schemeStack.{u, w} B _ hS (lineObject k B hS)) P
      hP.1 hA h𝒳 = c at h hZ
  have h1 : (0 : EInt) + ((1 : ℤ) : EInt) = c + ((1 : ℤ) : EInt) := h
  rw [← eq_of_add_intCast_eq_add_intCast h1] at hZ
  exact absurd hZ (by decide)

end Site

/-- **The thickened origins satisfy every hypothesis of Stacks 0DS4 and violate its equality
clause.** For the 1-morphism `f : 𝒯 ⟶ 𝒳` of algebraic stacks induced by `T ⟶ 𝔸¹`, locally of
finite type between Jacobson, pseudo-catenary, locally Noetherian algebraic stacks with `|𝒯|`
irreducible and `𝒳` quasi-separated, there is no point of `|𝒯|` — so a fortiori no nonempty open
subset of `|𝒯|` — at which `dim(𝒯) = dim(𝒵) + dim_t(𝒯_{f(t)})` for the scheme theoretic image `𝒵`
of `f`. -/
theorem exists_counterexample :
    ∃ (B : BigFppfSite.{u}) (hS : B.Contains (Spec (lineRing k)))
      (𝒯 𝒳 : AlgebraicStacks.{u, w} B _ hS) (f : 𝒯 ⟶ 𝒳)
      (hf : AlgebraicStacks.IsLocallyOfFiniteType B _ hS f)
      (h𝒯 : IsLocallyNoetherianStack.{u, w} B _ hS 𝒯)
      (h𝒳 : IsLocallyNoetherianStack.{u, w} B _ hS 𝒳),
      AlgebraicStacks.IsJacobson B _ hS 𝒯 ∧ AlgebraicStacks.IsJacobson B _ hS 𝒳 ∧
      AlgebraicStacks.IsPseudoCatenary B _ hS 𝒯 ∧ AlgebraicStacks.IsPseudoCatenary B _ hS 𝒳 ∧
      @IrreducibleSpace _ (pointTopology B _ hS 𝒯.val) ∧
      IsQuasiSeparatedAbs.{u, w, w} B _ hS 𝒳 ∧
      ∀ {P : ObjectProperty 𝒳.val.val.obj} (hP : IsSchemeTheoreticImage f P)
        (t : points B _ hS 𝒯.val.val 𝒯.val.property),
        dimension B _ hS 𝒯 h𝒯 ≠
          closedSubstackDimension B _ hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳 +
            relativeStackDimensionAt.{u, w} B _ hS f hf h𝒯 h𝒳 t := by
  obtain ⟨B, hS, hT⟩ := exists_bigFppfSite k
  exact ⟨B, hS, schemeStack.{u, w} B _ hS (TObject k B hS hT),
    schemeStack.{u, w} B _ hS (lineObject k B hS), schemeStackMap B _ hS (toLineObject k B hS hT),
    isLocallyOfFiniteType_schemeStackMap B _ hS _, isLocallyNoetherianStack_schemeStack B _ hS _,
    isLocallyNoetherianStack_schemeStack B _ hS _, isJacobson_schemeStack B _ hS _,
    isJacobson_schemeStack B _ hS _,
    isPseudoCatenary_schemeStack B _ hS _ (isUniversallyCatenary_T k),
    isPseudoCatenary_schemeStack B _ hS _
      (Scheme.isUniversallyCatenary_of_locallyOfFiniteType_over_field k (lineToBase k)),
    irreducibleSpace_points_schemeStack B _ hS _,
    isQuasiSeparatedAbs_schemeStack_of_isAffine B _ hS, fun hP t =>
      dimension_ne_closedSubstackDimension_add_relativeStackDimensionAt k B hS hT hP _ _ _ t⟩

end AlgebraicGeometry.ThickenedOrigin

namespace AlgebraicGeometry.Stack

universe u w

/-- **Stacks 0DS4 as stated is false.** The statement asks of `f : 𝒯 ⟶ 𝒳` only that it be
locally of finite type, between Jacobson, pseudo-catenary, locally Noetherian algebraic stacks
with `|𝒯|` irreducible and `𝒳` quasi-separated, and concludes, for the scheme theoretic image `𝒵`
of `f`, that `dim(𝒯) ≤ dim(𝒵) + dim_t(𝒯_{f(t)})` at every `t ∈ |𝒯|` with equality on a nonempty,
equivalently dense, open subset of `|𝒯|`. The 1-morphism induced by the affine line with
infinitely many origins, the `n`-th thickened to order `n`, mapping to `𝔸¹` by the global
nilpotent function `ε`, is a counterexample to the equality clause:
`AlgebraicGeometry.ThickenedOrigin.exists_counterexample`. -/
theorem not_forall_dimension_le_add_and_exists_isOpen_dense_eq :
    ¬ ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
      {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
      (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
      (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
      (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
      (_h𝒯Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒯)
      (_h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
      (_h𝒯Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒯)
      (_h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
      (_h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
      (_h𝒳QuasiSeparated : IsQuasiSeparatedAbs.{u, w, w} B S hS 𝒳)
      {P : ObjectProperty 𝒳.val.val.obj} (hP : IsSchemeTheoreticImage f P),
      (∀ t : points B S hS 𝒯.val.val 𝒯.val.property,
          dimension B S hS 𝒯 h𝒯 ≤
            closedSubstackDimension B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳 +
              relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t) ∧
        ∃ W : Set (points B S hS 𝒯.val.val 𝒯.val.property),
          @IsOpen _ (pointTopology B S hS 𝒯.val) W ∧ W.Nonempty ∧
            @Dense _ (pointTopology B S hS 𝒯.val) W ∧
            ∀ t ∈ W, dimension B S hS 𝒯 h𝒯 =
              closedSubstackDimension B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳 +
                relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t := by
  intro h
  obtain ⟨B, hS, 𝒯, 𝒳, f, hf, h𝒯, h𝒳, hJ𝒯, hJ𝒳, hC𝒯, hC𝒳, hI, hQS, hne⟩ :=
    ThickenedOrigin.exists_counterexample.{u, w} (ULift.{u} ℚ)
  obtain ⟨P, hP⟩ := hasSchemeTheoreticImage f
  obtain ⟨-, W, -, ⟨t, ht⟩, -, hW⟩ := h B _ hS f hf h𝒯 h𝒳 hJ𝒯 hJ𝒳 hC𝒯 hC𝒳 hI hQS hP
  exact hne hP t (hW t ht)

end AlgebraicGeometry.Stack

end
