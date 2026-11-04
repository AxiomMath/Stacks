module

public import StacksFrontier.Deformation.Artin.Obstruction.DualNotionTag
public import StacksFrontier.Deformation.Artin.Obstruction.DualSituationTransport
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveTheoryGeometricReduction
public import StacksFrontier.Deformation.Artin.Versality.Openness

/-!
# Openness of versality from dual deformation situations at every chart

[Stacks, Tag 07YZ] is a statement at one object: in Situation 07YX — an object `x` over
`U = Spec A` with `A` of finite type over the ring `Λ` of an affine open `Spec Λ ⊆ S`, whose
deformation theory is presented by a complex `K` of `A`-modules — if `K` is perfect and condition
(iv) of [Stacks, Tag 07YY] holds, then versality of `x` at a *closed* point of `U` propagates to
every finite type point of an open neighbourhood. A user of the lemma, such as the first proof of
[Stacks, Tag 08WA] or [Stacks, Remark 0D1P], wants openness of versality for the whole category
(Definition 07XQ): an arbitrary base `U` locally of finite type over `S` and an arbitrary finite
type point. The two are joined by the reduction those proofs open with: "After shrinking `U` we
may assume that `u₀` is a closed point (Morphisms, Lemma 01TA) and `U = Spec(A)` with `U → S`
mapping into an affine open `Spec(Λ)` of `S`."

This file carries out that reduction once, for every category fibred in groupoids over the big
fppf site of a locally Noetherian scheme: if every charted object `(A, x)` with `A` of finite
type over the chart carries a dual deformation situation whose complex is perfect and which
satisfies condition (iv), then openness of versality holds.

## Main results

* `Deformation.Artin.DualNotion.isOpenVersality_of_dualDeformationSituation` — the reduction.
* `Deformation.Artin.DualNotion.isOpenVersality_of_functorDeformationTheory` — the same, with
  the per-chart input in the form the first proof of [Stacks, Tag 08WA] and
  [Stacks, Remark 0D1P] produce it: a deformation theory valued in a pair of functors `T¹, T²`
  (`Ext`-groups in the source) and a perfect `K` with `H^i(K ⊗ᴸ_A −) ≅ T^i` for `i = 1, 2`
  compatibly with connecting maps (what [Stacks, Tag 08JR] provides).

## Implementation notes

The geometric reduction is the one already used for [Stacks, Tag 07YU]
(`Deformation.Artin.exists_chartedData`, `Deformation.Artin.exists_restrictedLift` and
`Deformation.Artin.isVersalAt_iff_restrict`); only the per-chart input differs: here it is
[Stacks, Tag 07YZ], `Deformation.Artin.DualNotion.exists_isOpen_isVersalAt_of_isPerfect`.

The hypothesis provides, for each charted object, a dual deformation situation together with the
equation identifying its object with the given one; the situation's own affine open, fibredness
and (RS*) fields are arbitrary, since 07YZ's conclusion depends on none of them.

The conclusion is the body of `Deformation.Artin.IsOpenVersality`, written out, for the reason
recorded in `StacksFrontier.Deformation.Artin.Obstruction.NaiveTheoryVersalityOpenness`: that
predicate takes an argument asserting that `p ⋙ Over.post B.inclusion` is fibred in groupoids
over all of `Over S`, which fails for size reasons; the `example` at the end checks the two are
the same proposition.

## References

* [Stacks Project, Tag 07YZ](https://stacks.math.columbia.edu/tag/07YZ)
* [Stacks Project, Tag 07XQ](https://stacks.math.columbia.edu/tag/07XQ)
* [Stacks Project, Tag 01TA](https://stacks.math.columbia.edu/tag/01TA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Deformation.Artin.DualNotion

-- `Deformation.Artin.DualDeformationSituation` and
-- `Deformation.Artin.DualNotion.exists_isOpen_isVersalAt_of_isPerfect` are stated in the
-- standard model of `D(A)`, so the statement below has to be as well.
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS}

/-- Versality only depends on the object, not on the proof that it lies over the base. -/
private theorem isVersalAt_congr_obj {U : Over S} {u : U.left} {x x' : X} (h : x = x')
    (hx : (p ⋙ Over.post B.inclusion).obj x = U) (hx' : (p ⋙ Over.post B.inclusion).obj x' = U) :
    IsVersalAt U (p ⋙ Over.post B.inclusion) u x hx ↔
      IsVersalAt U (p ⋙ Over.post B.inclusion) u x' hx' := by
  subst h
  rfl

/-- **[Stacks, Tag 07YZ] at every chart gives openness of versality.** Let `S` be a locally
Noetherian scheme and `𝒳` a category fibred in groupoids over the big fppf site of `S`. Assume
that for every affine open `Spec Λ ⊆ S` and every object `x` of `𝒳` over `Spec A` with `A` of
finite type over `Λ` there is a dual deformation situation (Situation 07YX) for `x` whose complex
`K` is perfect and which satisfies condition (iv) of [Stacks, Tag 07YY]. Then openness of
versality holds for `𝒳`: if `U` is a scheme locally of finite type over `S`, `x` an object of
`𝒳` over `U` and `u₀` a finite type point of `U` at which `x` is versal, then `x` is versal at
every finite type point of an open neighbourhood of `u₀`. -/
public theorem isOpenVersality_of_dualDeformationSituation [IsLocallyNoetherian S]
    (hp : p.IsFiberedInGroupoids)
    (dual : ∀ (c : AffineChart S) (P : ChartedObject B S hS p c),
      Algebra.FiniteType c.ring P.ring →
      ∃ sit : DualDeformationSituation P.ring c.ring B S hS P.obj.alg.toScheme P.obj.alg.mem X p,
        sit.x = P.point ∧ StacksDraft.Perfect.IsPerfect sit.K ∧
          ObstructionBoundaryCondition c.ring P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem X p
            sit)
    (U : Over S) (hUft : LocallyOfFiniteType U.hom) (x : X)
    (hx : (p ⋙ Over.post B.inclusion).obj x = U) (u₀ : U.left)
    (hu₀ : IsFiniteTypePoint u₀)
    (hversal : IsVersalAt U (p ⋙ Over.post B.inclusion) u₀ x hx) :
    ∃ V : U.left.Opens, u₀ ∈ V.1 ∧
      ∀ u ∈ V.1, IsFiniteTypePoint u →
        IsVersalAt U (p ⋙ Over.post B.inclusion) u x hx := by
  subst hx
  have : LocallyOfFiniteType (B.inclusion.map (p.obj x).hom) := hUft
  obtain ⟨D, w₀, hw₀, hw₀c⟩ := exists_chartedData B S hS p x (p.obj x).left.2 u₀ hu₀
  obtain ⟨obj, ρ, hρ⟩ := exists_restrictedLift B S hS p x D.mem D.immersion hp
  let P : ChartedObject B S hS p D.chart :=
    restrictedChartedObject B S hS p x D.mem D.immersion D.mapsIntoAffineOpen D.chart
      D.factorization obj
  have hPfin : Algebra.FiniteType D.chart.ring P.ring := D.finiteType
  -- every point of `Spec A` has its image in `S` inside the chart
  have hrange : ∀ t : Spec (CommRingCat.of D.ring),
      (B.inclusion.map (p.obj x).hom).base (D.immersion.base t) ∈
        Set.range D.chart.immersion.base := fun t =>
    ⟨(Spec.map (CommRingCat.ofHom (algebraMap D.chart.ring D.ring))).base t,
      congrArg (fun m : Spec (CommRingCat.of D.ring) ⟶ S => m.base t) D.factorization⟩
  have hH : ∀ t : Spec (CommRingCat.of D.ring),
      Set.range (((p ⋙ Over.post B.inclusion).obj x).left.fromSpecResidueField
          (D.immersion.base t) ≫ ((p ⋙ Over.post B.inclusion).obj x).hom).base ⊆
        Set.range D.chart.immersion.base := fun t =>
    range_residuePoint_subset S _ _ D.chart.immersion (hrange t)
  have htoS : P.obj.alg.toScheme = D.immersion ≫ B.inclusion.map (p.obj x).hom :=
    toScheme_restrictedSiteAlgebra B S hS p x D.mem D.immersion
  have hH' : ∀ t : Spec (CommRingCat.of D.ring),
      Set.range ((Over.mk P.obj.alg.toScheme).left.fromSpecResidueField t ≫
          (Over.mk P.obj.alg.toScheme).hom).base ⊆
        Set.range D.chart.immersion.base := by
    intro t
    refine range_residuePoint_subset S P.obj.alg.toScheme t D.chart.immersion ?_
    rw [htoS]
    exact hrange t
  -- versality at a point of `Spec A` is versality at its image in `U`
  have hiff : ∀ t : Spec (CommRingCat.of D.ring),
      IsVersalAt (Over.mk P.obj.alg.toScheme) (p ⋙ Over.post B.inclusion) t P.point
          P.overScheme_eq ↔
        IsVersalAt ((p ⋙ Over.post B.inclusion).obj x) (p ⋙ Over.post B.inclusion)
          (D.immersion.base t) x rfl := fun t =>
    isVersalAt_iff_restrict B S hS p hp D.chart.immersion rfl P.overScheme_eq ρ D.immersion
      D.isOpenImmersion hρ t (hH t) (hH' t)
  -- the dual deformation situation at the chart, and Stacks 07YZ there
  obtain ⟨sit, hsitx, hperf, hiv⟩ := dual D.chart P hPfin
  have hsit : ∀ t : Spec (CommRingCat.of D.ring),
      IsVersalAt (Over.mk P.obj.alg.toScheme) (p ⋙ Over.post B.inclusion) t sit.x
          (versalityBase D.chart.ring P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem X p sit) ↔
        IsVersalAt (Over.mk P.obj.alg.toScheme) (p ⋙ Over.post B.inclusion) t P.point
          P.overScheme_eq := fun t =>
    isVersalAt_congr_obj hsitx _ _
  have hversal' : IsVersalAt (Over.mk P.obj.alg.toScheme) (p ⋙ Over.post B.inclusion) w₀
      sit.x
        (versalityBase D.chart.ring P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem X p sit) := by
    rw [hsit w₀, hiff w₀, hw₀]
    exact hversal
  obtain ⟨V', hV'open, hw₀V', hV'⟩ :=
    exists_isOpen_isVersalAt_of_isPerfect D.chart.ring P.ring B S hS P.obj.alg.toScheme
      P.obj.alg.mem X p sit hiv hperf w₀ hw₀c hversal'
  refine ⟨⟨D.immersion.base '' V', D.immersion.isOpenEmbedding.isOpenMap V' hV'open⟩,
    ⟨w₀, hw₀V', hw₀⟩, ?_⟩
  rintro u ⟨t, htV', rfl⟩ hft
  exact (hiff t).mp ((hsit t).mp
    (hV' t htV' (isFiniteTypePoint_of_isOpenImmersion D.immersion t hft)))

/-- **Openness of versality from a functor deformation theory and a perfect complex at every
chart.** Let `S` be a locally Noetherian scheme and `𝒳` a category fibred in groupoids over the
big fppf site of `S` satisfying (RS*). Assume that every object `x` of `𝒳` over `Spec A`, with
`A` of finite type over the ring `Λ` of an affine open `Spec Λ ⊆ S`, carries a deformation
theory valued in a pair of functors `T¹, T²` of `A`-modules with connecting maps
(`Deformation.Artin.FunctorDeformationTheory`, condition (iv) of [Stacks, Tag 07YY] included),
and that there is a perfect `K ∈ D(A)` with isomorphisms `H^i(K ⊗ᴸ_A −) ≅ T^i` for `i = 1, 2`
carrying the connecting map of `K` to that of `T`. Then openness of versality holds for `𝒳`.

This is the shape of the first proof of [Stacks, Tag 08WA] and of the `07YZ` route of
[Stacks, Remark 0D1P]: `T^i = Ext^i_{𝒪_X}(E, 𝒢 ⊗ f^*−)` and `K` is supplied by
[Stacks, Tag 08JR]. -/
public theorem isOpenVersality_of_functorDeformationTheory [IsLocallyNoetherian S]
    (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
    (theory : ∀ (c : AffineChart S) (P : ChartedObject B S hS p c),
      Algebra.FiniteType c.ring P.ring →
      ∃ (T : FunctorDeformationTheory P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem X p P.point
          P.obj.obj.2 hp hRS) (K : DerivedCategory (ModuleCat.{u} P.ring))
        (e₁ : derivedCohomology P.ring K 1 ≅ T.T₁) (e₂ : derivedCohomology P.ring K 2 ≅ T.T₂),
        StacksDraft.Perfect.IsPerfect K ∧
          ∀ {Sq : ShortComplex (ModuleCat.{u} P.ring)} (hSq : Sq.ShortExact),
            boundaryMap P.ring K hSq ≫ e₂.hom.app Sq.X₁ = e₁.hom.app Sq.X₃ ≫ T.δ hSq)
    (U : Over S) (hUft : LocallyOfFiniteType U.hom) (x : X)
    (hx : (p ⋙ Over.post B.inclusion).obj x = U) (u₀ : U.left)
    (hu₀ : IsFiniteTypePoint u₀)
    (hversal : IsVersalAt U (p ⋙ Over.post B.inclusion) u₀ x hx) :
    ∃ V : U.left.Opens, u₀ ∈ V.1 ∧
      ∀ u ∈ V.1, IsFiniteTypePoint u →
        IsVersalAt U (p ⋙ Over.post B.inclusion) u x hx := by
  refine isOpenVersality_of_dualDeformationSituation hp (fun c P hPfin => ?_) U hUft x hx u₀ hu₀
    hversal
  obtain ⟨T, K, e₁, e₂, hK, he⟩ := theory c P hPfin
  exact ⟨T.toDualDeformationSituation c.ring K e₁ e₂ hPfin c.immersion inferInstance
      P.factorization, rfl, hK,
    T.obstructionBoundaryCondition_toDualDeformationSituation c.ring K e₁ e₂ hPfin c.immersion
      inferInstance P.factorization he⟩

/-- The conclusion of `isOpenVersality_of_dualDeformationSituation` is the predicate
`Deformation.Artin.IsOpenVersality` of Stacks 07XQ, written out. -/
example (hq : (p ⋙ Over.post B.inclusion).IsFiberedInGroupoids) :
    IsOpenVersality (p ⋙ Over.post B.inclusion) hq =
      ∀ (U : Over S), LocallyOfFiniteType U.hom →
        ∀ (x : X) (hx : (p ⋙ Over.post B.inclusion).obj x = U) (u₀ : U.left),
          IsFiniteTypePoint u₀ →
          IsVersalAt U (p ⋙ Over.post B.inclusion) u₀ x hx →
          ∃ V : U.left.Opens, u₀ ∈ V.1 ∧
            ∀ u ∈ V.1, IsFiniteTypePoint u →
              IsVersalAt U (p ⋙ Over.post B.inclusion) u x hx :=
  rfl

end Deformation.Artin.DualNotion

end
