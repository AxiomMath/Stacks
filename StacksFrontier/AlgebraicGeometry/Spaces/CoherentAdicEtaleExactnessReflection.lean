module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicEtaleLocalExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.HomDescent

/-!
# Exactness in `Coh(X, 𝓘)` can be checked étale locally

Let `X` be a Noetherian algebraic space over a scheme `S` and let `𝓘 ⊆ 𝒪_X` be a quasi-coherent
sheaf of ideals.  **This file proves that a short complex of coherent `𝓘`-adic systems on `X` is
exact exactly when its restriction to each member of a covering of `X` by affine étale charts is
exact.**  The ideal on each chart is a binder here, together with the compatibility of the
inverse image with it; part (2) of Stacks 089P is the instance at the inverse-image ideals,
`AlgebraicGeometry.Space.exact_iff_forall_exact_coherentAdicChartRestriction`.

The two directions are the two halves of the statement.  That restriction *preserves* exactness is
part (3) of the same tag at the chart morphism, which is flat because it is étale; it is
`AlgebraicGeometry.Space.coherentAdicRestrictToChart_exact` of
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicChartRestriction`.  That restriction along the
whole family *reflects* exactness is the content proved here, and it has two inputs.

The first is that the family of restriction functors is jointly faithful.  A morphism of coherent
adic systems is a morphism of `𝒪_X`-modules at each level; restriction to a chart is termwise
inverse image along the chart morphism
(`AlgebraicGeometry.Space.coherentAdicPullback_map_hom_app`); and a morphism of `𝒪_X`-modules is
determined by its inverse images along an étale covering, which is the faithfulness half of
Stacks 04W6 —
`AlgebraicGeometry.Space.QuasiCoherentDescent.modulePullback_map_injective_of_isEtaleCovering`.
That lemma is the sheaf condition on the small étale site of `X` read through Equation 03LW, so
no quasi-coherence and no comparison of sites enters.

The second is that exactness of a short complex of an abelian category is the vanishing of its
homology, and that an exact functor carries the homology of a complex to the homology of the
restricted complex (`CategoryTheory.ShortComplex.mapHomologyIso`).  So if every restriction of
the complex is exact, the homology of the complex restricts to zero on every chart of the
family, and joint faithfulness applied to its identity morphism makes it zero.

## Main definitions

* `AlgebraicGeometry.Space.coherentAdicRestrictToChartShortComplex` — the restriction of a short
  complex of coherent adic systems to an affine étale chart, the short complex
  `(f^*E ⟶ f^*G ⟶ f^*H)` of `Coh(U, 𝓘𝒪_U)`.

## Main results

* `AlgebraicGeometry.Space.coherentAdicRestrictToChart_map_injective` — **the restriction
  functors of a covering by affine étale charts are jointly faithful.**
* `AlgebraicGeometry.Space.exact_iff_forall_exact_coherentAdicRestrictToChart` — **a short
  complex of coherent adic systems is exact exactly when its restriction to each member of a
  covering of `X` by affine étale charts is exact**; part (2) of Stacks 089P is its instance at
  the inverse-image ideals,
  `AlgebraicGeometry.Space.exact_iff_forall_exact_coherentAdicChartRestriction`.

## Implementation notes

The charts of the covering family are affine, and that is the correct statement rather than a
restriction of it: an étale chart of a Noetherian algebraic space is an arbitrary scheme étale
over it and need not be quasi-compact, so the Noetherian condition of Stacks 03EA fails for a
general chart, and the restriction functor to a chart is exact only when the chart is Noetherian.
The affine charts cover the small étale site of `X`, so no étale covering is lost; see the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicChartRestriction`.

The ideal `𝓘' i` on each chart and the compatibility `hw i` of the inverse image with it are
binders, as they are on `AlgebraicGeometry.Space.coherentAdicPullback` itself: the restriction
functor cannot be written without naming its target category, and `𝓘' i` is what names it.  At
the inverse-image ideals `𝓘' i = 𝓘 · 𝒪_{U i}` both the quasi-coherence and the compatibility are
proved, and the statement there is part (2) of Stacks 089P,
`AlgebraicGeometry.Space.exact_iff_forall_exact_coherentAdicChartRestriction`.

`AlgebraicGeometry.Space.coherentAdicRestrictToChartShortComplex` is the restricted complex
spelled out with `CategoryTheory.ShortComplex.mk` rather than
`CategoryTheory.ShortComplex.map`, so that no instance has to be in scope for the statement of
the reflection to be written; its three objects and its two morphisms are those of
`CategoryTheory.ShortComplex.map` on the nose, by
`AlgebraicGeometry.Space.coherentAdicRestrictToChartShortComplex_f` and the four lemmas beside
it.

## References

* [Stacks Project, Tag 089P](https://stacks.math.columbia.edu/tag/089P)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 041E](https://stacks.math.columbia.edu/tag/041E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ X.1)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)

/-! ### Restriction of a short complex to a single affine chart -/

section OneChart

variable (V : SmallEtale B S hS X.1)
    (𝓙 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (chartSpace B S hS X V).1 (chartSpace B S hS X V).2).O))).Submodule)
    (hV : IsAffine (chartScheme V))
    (hJcart : IsCartesianOnAffineCharts 𝓙.toSheafOfModules)
    (hwV : IdealPowerMultipleCompatible B S hS
      (modulePullback B S hS (chartToSpace B S hS X V)) 𝓘 𝓙)

include hJcart in
/-- **`Coh(U, 𝓘𝒪_U)` at an affine étale chart of a Noetherian algebraic space is abelian**,
part (1) of Stacks 089P at the chart, which is a Noetherian algebraic space by
`AlgebraicGeometry.Space.isNoetherian_chartSpace_of_isAffine`. -/
@[instance_reducible]
def abelian_coherentAdicSystems_chartSpace :
    Abelian (CoherentAdicSystems B S hS (chartSpace B S hS X V).1
      (chartSpace B S hS X V).2 𝓙) :=
  abelian_coherentAdicSystems B S hS (chartSpace B S hS X V).1 (chartSpace B S hS X V).2 𝓙 hZ
    (isNoetherian_chartSpace_of_isAffine B S hS X V hZ hN hV) hJcart

include hIcart hJcart in
/-- **Restriction to an affine étale chart preserves finite colimits**, the half of
`AlgebraicGeometry.Space.coherentAdicRestrictToChart_exact` which right exactness of the inverse
image supplies. -/
theorem preservesFiniteColimits_coherentAdicRestrictToChart :
    PreservesFiniteColimits (coherentAdicRestrictToChart B S hS X V 𝓘 𝓙 hZ hN hV hwV) :=
  ((exactFunctor_iff _).1
    (coherentAdicRestrictToChart_exact B S hS X V 𝓘 𝓙 hZ hN hV hIcart hJcart hwV)).2

/-- **Restriction to an affine étale chart preserves zero morphisms.**  Restriction acts on a
morphism of coherent adic systems by termwise inverse image, and inverse image of modules
preserves zero morphisms, being a left adjoint. -/
theorem preservesZeroMorphisms_coherentAdicRestrictToChart :
    (coherentAdicRestrictToChart B S hS X V 𝓘 𝓙 hZ hN hV hwV).PreservesZeroMorphisms where
  map_zero _ _ :=
    ObjectProperty.hom_ext _ (NatTrans.ext (funext fun _ =>
      (preservesZeroMorphisms_modulePullback B S hS
        (chartToSpace B S hS X V)).map_zero _ _))

variable (T : ShortComplex (CoherentAdicSystems B S hS X.1 X.2 𝓘))

/-- **The restriction of a short complex of coherent adic systems to an affine étale chart**, the
short complex `f^*E ⟶ f^*G ⟶ f^*H` of `Coh(U, 𝓘𝒪_U)` obtained by applying
`AlgebraicGeometry.Space.coherentAdicRestrictToChart` to `E ⟶ G ⟶ H`.

The composite of the two restricted morphisms vanishes because restriction is a functor which
preserves zero morphisms. -/
def coherentAdicRestrictToChartShortComplex :
    ShortComplex (CoherentAdicSystems B S hS (chartSpace B S hS X V).1
      (chartSpace B S hS X V).2 𝓙) :=
  ShortComplex.mk ((coherentAdicRestrictToChart B S hS X V 𝓘 𝓙 hZ hN hV hwV).map T.f)
    ((coherentAdicRestrictToChart B S hS X V 𝓘 𝓙 hZ hN hV hwV).map T.g)
    (((coherentAdicRestrictToChart B S hS X V 𝓘 𝓙 hZ hN hV hwV).map_comp T.f T.g).symm.trans
      ((congrArg (coherentAdicRestrictToChart B S hS X V 𝓘 𝓙 hZ hN hV hwV).map T.zero).trans
        ((preservesZeroMorphisms_coherentAdicRestrictToChart
          B S hS X 𝓘 hZ hN V 𝓙 hV hwV).map_zero _ _)))

/-- The first term of the restricted complex is the restriction of the first term. -/
theorem coherentAdicRestrictToChartShortComplex_X₁ :
    (coherentAdicRestrictToChartShortComplex B S hS X 𝓘 hZ hN V 𝓙 hV hwV T).X₁ =
      (coherentAdicRestrictToChart B S hS X V 𝓘 𝓙 hZ hN hV hwV).obj T.X₁ :=
  rfl

/-- The second term of the restricted complex is the restriction of the second term. -/
theorem coherentAdicRestrictToChartShortComplex_X₂ :
    (coherentAdicRestrictToChartShortComplex B S hS X 𝓘 hZ hN V 𝓙 hV hwV T).X₂ =
      (coherentAdicRestrictToChart B S hS X V 𝓘 𝓙 hZ hN hV hwV).obj T.X₂ :=
  rfl

/-- The third term of the restricted complex is the restriction of the third term. -/
theorem coherentAdicRestrictToChartShortComplex_X₃ :
    (coherentAdicRestrictToChartShortComplex B S hS X 𝓘 hZ hN V 𝓙 hV hwV T).X₃ =
      (coherentAdicRestrictToChart B S hS X V 𝓘 𝓙 hZ hN hV hwV).obj T.X₃ :=
  rfl

/-- The first morphism of the restricted complex is the restriction of the first morphism. -/
theorem coherentAdicRestrictToChartShortComplex_f :
    (coherentAdicRestrictToChartShortComplex B S hS X 𝓘 hZ hN V 𝓙 hV hwV T).f =
      (coherentAdicRestrictToChart B S hS X V 𝓘 𝓙 hZ hN hV hwV).map T.f :=
  rfl

/-- The second morphism of the restricted complex is the restriction of the second morphism. -/
theorem coherentAdicRestrictToChartShortComplex_g :
    (coherentAdicRestrictToChartShortComplex B S hS X 𝓘 hZ hN V 𝓙 hV hwV T).g =
      (coherentAdicRestrictToChart B S hS X V 𝓘 𝓙 hZ hN hV hwV).map T.g :=
  rfl

/-- The restricted complex is the image of the complex under the restriction functor. -/
theorem coherentAdicRestrictToChartShortComplex_eq_map :
    letI := preservesZeroMorphisms_coherentAdicRestrictToChart B S hS X 𝓘 hZ hN V 𝓙 hV hwV
    coherentAdicRestrictToChartShortComplex B S hS X 𝓘 hZ hN V 𝓙 hV hwV T =
      T.map (coherentAdicRestrictToChart B S hS X V 𝓘 𝓙 hZ hN hV hwV) :=
  rfl

include hIcart hJcart in
/-- The restricted complex is exact exactly when the restriction of the homology vanishes. -/
private theorem exact_coherentAdicRestrictToChartShortComplex_iff_isZero :
    letI := abelian_coherentAdicSystems B S hS X.1 X.2 𝓘 hZ hN hIcart
    haveI : T.HasHomology := hasHomology_shortComplex B S hS X.1 X.2 𝓘 hZ hN hIcart T
    (coherentAdicRestrictToChartShortComplex B S hS X 𝓘 hZ hN V 𝓙 hV hwV T).Exact ↔
      IsZero ((coherentAdicRestrictToChart B S hS X V 𝓘 𝓙 hZ hN hV hwV).obj T.homology) := by
  let := abelian_coherentAdicSystems B S hS X.1 X.2 𝓘 hZ hN hIcart
  have : T.HasHomology := hasHomology_shortComplex B S hS X.1 X.2 𝓘 hZ hN hIcart T
  let := preservesZeroMorphisms_coherentAdicRestrictToChart B S hS X 𝓘 hZ hN V 𝓙 hV hwV
  let := abelian_coherentAdicSystems_chartSpace B S hS X hZ hN V 𝓙 hV hJcart
  have := preservesFiniteLimits_coherentAdicRestrictToChart B S hS X V 𝓘 𝓙 hZ hN hV
    hIcart hJcart hwV
  have := preservesFiniteColimits_coherentAdicRestrictToChart B S hS X 𝓘 hZ hN hIcart V 𝓙 hV
    hJcart hwV
  exact (ShortComplex.exact_iff_isZero_homology
    (T.map (coherentAdicRestrictToChart B S hS X V 𝓘 𝓙 hZ hN hV hwV))).trans
      (ShortComplex.mapHomologyIso T _).isZero_iff

end OneChart

/-! ### Joint faithfulness of a covering family of affine charts -/

variable {I : Type v} (U : I → SmallEtale B S hS X.1)
    (𝓘' : ∀ i, (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (chartSpace B S hS X (U i)).1 (chartSpace B S hS X (U i)).2).O))).Submodule)
    (hU : ∀ i, IsAffine (chartScheme (U i)))
    (hIcart' : ∀ i, IsCartesianOnAffineCharts (𝓘' i).toSheafOfModules)
    (hw : ∀ i, IdealPowerMultipleCompatible B S hS
      (modulePullback B S hS (chartToSpace B S hS X (U i))) 𝓘 (𝓘' i))
    (hcov : IsEtaleCovering B S hS (fun i => (chartSpace B S hS X (U i)).1)
      (fun i => (chartToSpace B S hS X (U i)).hom))

include hcov in
/-- **The restriction functors of a covering of `X` by affine étale charts are jointly
faithful**: two morphisms of coherent adic systems whose restrictions to every member of the
family agree are equal.

A morphism of coherent adic systems is a morphism of `𝒪_X`-modules at each level, restriction to
a chart is termwise inverse image along the chart morphism, and a morphism of `𝒪_X`-modules is
determined by its inverse images along an étale covering by the faithfulness half of
Stacks 04W6. -/
theorem coherentAdicRestrictToChart_map_injective
    {E E' : CoherentAdicSystems B S hS X.1 X.2 𝓘} (φ ψ : E ⟶ E')
    (h : ∀ i, (coherentAdicRestrictToChart B S hS X (U i) 𝓘 (𝓘' i) hZ hN (hU i) (hw i)).map φ =
      (coherentAdicRestrictToChart B S hS X (U i) 𝓘 (𝓘' i) hZ hN (hU i) (hw i)).map ψ) :
    φ = ψ := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n => ?_))
  refine QuasiCoherentDescent.modulePullback_map_injective_of_isEtaleCovering B S hS
    (fun i => chartSpace B S hS X (U i)) (fun i => chartToSpace B S hS X (U i)) hcov
    (φ.hom.app n) (ψ.hom.app n) fun i => ?_
  exact congrArg
    (fun a : (coherentAdicRestrictToChart B S hS X (U i) 𝓘 (𝓘' i) hZ hN (hU i) (hw i)).obj E ⟶
        (coherentAdicRestrictToChart B S hS X (U i) 𝓘 (𝓘' i) hZ hN (hU i) (hw i)).obj E' =>
      a.hom.app n) (h i)

include hcov in
/-- **An object of `Coh(X, 𝓘)` whose restriction to every member of a covering of `X` by affine
étale charts is zero is itself zero**, which is joint faithfulness applied to its identity
morphism. -/
theorem isZero_of_forall_isZero_coherentAdicRestrictToChart
    (E : CoherentAdicSystems B S hS X.1 X.2 𝓘)
    (hE : ∀ i, IsZero ((coherentAdicRestrictToChart B S hS X (U i) 𝓘 (𝓘' i) hZ hN (hU i)
      (hw i)).obj E)) :
    IsZero E :=
  (IsZero.iff_id_eq_zero E).2
    (coherentAdicRestrictToChart_map_injective B S hS X 𝓘 hZ hN U 𝓘' hU hw hcov (𝟙 E) 0 fun i =>
      ((coherentAdicRestrictToChart B S hS X (U i) 𝓘 (𝓘' i) hZ hN (hU i) (hw i)).map_id E).trans
        (((IsZero.iff_id_eq_zero _).1 (hE i)).trans
          ((preservesZeroMorphisms_coherentAdicRestrictToChart B S hS X 𝓘 hZ hN (U i) (𝓘' i)
            (hU i) (hw i)).map_zero E E).symm))

/-! ### Exactness is reflected by restriction to affine étale charts -/

include hIcart hIcart' hcov in
/-- **Exactness in `Coh(X, 𝓘)` can be checked étale locally.**  For a Noetherian algebraic space
`X`, a quasi-coherent sheaf of ideals `𝓘 ⊆ 𝒪_X` and a covering of `X` by affine étale charts
`U i`, a short complex of coherent `𝓘`-adic systems on `X` is exact exactly when its restriction
to `Coh(U i, 𝓘' i)` is exact for every `i`, for any quasi-coherent ideals `𝓘' i` with which the
inverse image along the chart morphism is compatible.  Part (2) of Stacks 089P is the instance
`𝓘' i = 𝓘 · 𝒪_{U i}`,
`AlgebraicGeometry.Space.exact_iff_forall_exact_coherentAdicChartRestriction`.

Restriction preserves exactness because the chart morphism is étale, hence flat, and the chart is
a Noetherian algebraic space, so part (3) of this tag applies to it:
`AlgebraicGeometry.Space.coherentAdicRestrictToChart_exact`.  Restriction along the family
reflects exactness because the family is jointly faithful,
`AlgebraicGeometry.Space.coherentAdicRestrictToChart_map_injective`, and an exact functor carries
the homology of the complex to the homology of the restricted complex: the homology of a complex
all of whose restrictions are exact restricts to zero everywhere, so its identity morphism
restricts to zero everywhere, so it is zero. -/
theorem exact_iff_forall_exact_coherentAdicRestrictToChart
    (T : ShortComplex (CoherentAdicSystems B S hS X.1 X.2 𝓘)) :
    T.Exact ↔ ∀ i, (coherentAdicRestrictToChartShortComplex B S hS X 𝓘 hZ hN (U i) (𝓘' i)
      (hU i) (hw i) T).Exact := by
  let := abelian_coherentAdicSystems B S hS X.1 X.2 𝓘 hZ hN hIcart
  have : T.HasHomology := hasHomology_shortComplex B S hS X.1 X.2 𝓘 hZ hN hIcart T
  rw [T.exact_iff_isZero_homology]
  have key := fun i => exact_coherentAdicRestrictToChartShortComplex_iff_isZero B S hS X 𝓘 hZ hN
    hIcart (U i) (𝓘' i) (hU i) (hIcart' i) (hw i) T
  refine ⟨fun hT i => ?_, fun hloc => isZero_of_forall_isZero_coherentAdicRestrictToChart
    B S hS X 𝓘 hZ hN U 𝓘' hU hw hcov T.homology fun i => (key i).1 (hloc i)⟩
  let := preservesZeroMorphisms_coherentAdicRestrictToChart
    B S hS X 𝓘 hZ hN (U i) (𝓘' i) (hU i) (hw i)
  exact (key i).2 (Functor.map_isZero _ hT)

end AlgebraicGeometry.Space

end
