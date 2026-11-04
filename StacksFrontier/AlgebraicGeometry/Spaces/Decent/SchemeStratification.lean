module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.BoundedPointFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.EmptyOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.Reasonable

/-!
# Stratifying an algebraic space by schemes

A stratification of an algebraic space `X` over a scheme `S` is a descending chain of open
subspaces `X = U₀ ⊇ U₁ ⊇ U₂ ⊇ …` whose reduced strata `Tₚ`, supported on the difference of the
point sets of `Uₚ` and `Uₚ₊₁`, each receive an isomorphism from the part of a separated scheme `Vₚ`
lying over them, with `Vₚ → Uₚ` surjective and étale. Both the chain and the strata are indexed
from zero. Each stratum is a scheme; for a reasonable `X` such a chain reaches the empty subspace
after finitely many steps; and a terminating chain with quasi-compact charts is a finite filtration
of `X` whose strata have quasi-compact separated schemes as surjective étale neighbourhoods.

## Main definitions

* `AlgebraicGeometry.Space.SchemeStratification`: the stratification data of `X`.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_of_isIso_pullback_fst`: a closed subspace which a chart
  meets in an isomorphism is a scheme.
* `AlgebraicGeometry.Space.SchemeStratification.isRepresentable_stratum`: each stratum is a scheme.
* `AlgebraicGeometry.Space.exists_pos_eq_sheafify_bot_of_hasUniversallyBoundedFibers`: a descending
  chain of open subspaces whose `p`-th member only contains points over which an étale chart has at
  least `p` points reaches the empty open subspace, as soon as the fibres of that chart are
  universally bounded.
* `AlgebraicGeometry.Space.exists_pos_eq_sheafify_bot_of_isReasonableSpace`: the same for a
  reasonable algebraic space and an affine étale chart.
* `AlgebraicGeometry.Space.SchemeStratification.exists_finiteFiltration_of_compactSpace`: a
  stratification whose chain terminates and whose charts are quasi-compact gives a finite
  filtration of `X` by open subspaces with quasi-compact separated étale charts over its strata.

## References

* [Stacks Project, Tag 0BBN](https://stacks.math.columbia.edu/tag/0BBN)
* [Stacks Project, Tag 07S9](https://stacks.math.columbia.edu/tag/07S9)
* [Stacks Project, Tag 07SA](https://stacks.math.columbia.edu/tag/07SA)
* [Stacks Project, Tag 07ST](https://stacks.math.columbia.edu/tag/07ST)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Closed subspaces met isomorphically by a chart -/

/-- A closed subspace which a morphism from a representable presheaf meets in an isomorphism is a
scheme. -/
theorem isRepresentable_of_isIso_pullback_fst
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : Subfunctor Y}
    (hT : IsClosedSubspace B S hS T) {V : BigFppfOver B S hS}
    (f : yoneda.obj V ⟶ Y) (hiso : IsIso (pullback.fst T.ι f)) :
    T.toFunctor.IsRepresentable := by
  obtain ⟨b, snd, fst, hpb⟩ := hT.2.rep f
  have : IsIso fst := by rw [← hpb.isoPullback_hom_fst]; infer_instance
  exact Functor.IsRepresentable.mk' (asIso fst)

/-! ### The stratification data -/

/-- Stratification data of `X`: a descending chain of open subspaces of `X` beginning at `X`
itself, together with, for each `p`, a reduced closed subspace `stratum p` of `openPart p`
supported on the points of `openPart p` which are not points of `openPart (p + 1)`, a separated
scheme `chart p`, and a surjective étale morphism from it to `openPart p` whose restriction over
`stratum p` is an isomorphism. -/
structure SchemeStratification (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  /-- The descending chain of open subspaces. -/
  openPart : ℕ → Subfunctor X
  /-- The reduced closed stratum inside the `p`-th open subspace. -/
  stratum : ∀ p, Subfunctor (openPart p).toFunctor
  /-- The separated scheme étale over the `p`-th open subspace. -/
  chart : ℕ → BigFppfOver B S hS
  /-- The surjective étale morphism from the `p`-th chart. -/
  chartHom : ∀ p, yoneda.obj (chart p) ⟶ (openPart p).toFunctor
  /-- The chain starts at the whole space. -/
  openPart_zero : openPart 0 = ⊤
  /-- The chain is descending. -/
  openPart_succ_le : ∀ p, openPart (p + 1) ≤ openPart p
  /-- Each member of the chain is an open subspace. -/
  isOpenSubspace_openPart : ∀ p, IsOpenSubspace B S hS (openPart p)
  /-- Each stratum is a closed subspace of its open subspace. -/
  isClosedSubspace_stratum : ∀ p, IsClosedSubspace B S hS (stratum p)
  /-- Each stratum is reduced, étale locally. -/
  isReduced_stratum : ∀ p, HasEtaleLocalProperty B S hS (stratum p).toFunctor
    (fun Y : Scheme.{u} => IsReduced Y)
  /-- The `p`-th stratum is supported on the points of the `p`-th member of the chain which are not
  points of the next one. -/
  range_stratum : ∀ p, Set.range (pointsMap B S hS (stratum p).toFunctor
      ((stratum p).ι ≫ (openPart p).ι)) =
    Set.range (pointsMap B S hS (openPart p).toFunctor (openPart p).ι) \
      Set.range (pointsMap B S hS (openPart (p + 1)).toFunctor (openPart (p + 1)).ι)
  /-- Each chart is a separated scheme. -/
  isSeparated_chart : ∀ p, Scheme.IsSeparated ((BigFppfOver.toScheme B S hS).obj (chart p))
  /-- Each chart morphism is surjective. -/
  surjective_chartHom : ∀ p, (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf (chartHom p)
  /-- Each chart morphism is étale. -/
  isEtale_chartHom : ∀ p, IsEtale B S hS (chartHom p)
  /-- The part of the `p`-th chart lying over the `p`-th stratum maps isomorphically to it. -/
  isIso_pullback_stratum : ∀ p, IsIso (pullback.fst (stratum p).ι (chartHom p))

namespace SchemeStratification

variable {B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Each stratum of a stratification is a scheme. -/
theorem isRepresentable_stratum (strat : SchemeStratification B S hS X) (p : ℕ) :
    (strat.stratum p).toFunctor.IsRepresentable :=
  isRepresentable_of_isIso_pullback_fst B S hS (strat.isClosedSubspace_stratum p)
    (strat.chartHom p) (strat.isIso_pullback_stratum p)

/-- Each member of the chain, read as an open subspace of `X`, has a point set containing the next
one's. -/
theorem range_pointsMap_openPart_succ_subset (strat : SchemeStratification B S hS X) (p : ℕ) :
    Set.range (pointsMap B S hS (strat.openPart (p + 1)).toFunctor
        (strat.openPart (p + 1)).ι) ⊆
      Set.range (pointsMap B S hS (strat.openPart p).toFunctor (strat.openPart p).ι) := by
  rw [← Subfunctor.homOfLe_ι (strat.openPart_succ_le p), pointsMap_comp]
  exact Set.range_comp_subset_range _ _

end SchemeStratification

/-! ### Termination of the chain -/

/-- Let `X` be an algebraic space over `S` and let `a : h_V ⟶ X` be a morphism from a representable
presheaf whose fibres are universally bounded. A descending chain of open subspaces of `X` whose
`p`-th member contains only points over which `a` has at least `p` points reaches the empty open
subspace: the `n`-th member is the sheafified bottom subfunctor for some `n > 0`. -/
theorem exists_pos_eq_sheafify_bot_of_hasUniversallyBoundedFibers
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {V : BigFppfOver B S hS} {a : yoneda.obj V ⟶ X}
    (ha : HasUniversallyBoundedFibers B S hS V a)
    (U : ℕ → Subfunctor X) (hUopen : ∀ p, IsOpenSubspace B S hS (U p))
    (hdeg : ∀ (p : ℕ) (x : points B S hS X),
      x ∈ Set.range (pointsMap B S hS (U p).toFunctor (U p).ι) →
        ((p : ℕ) : Cardinal.{u + 1}) ≤
          Cardinal.mk (pointsMap B S hS (yoneda.obj V) a ⁻¹' {x})) :
    ∃ n : ℕ, 0 < n ∧ U n = (⊥ : Subfunctor X).sheafify (BigFppfOver.topology B S hS) := by
  obtain ⟨n, hn⟩ := cardinalMk_pointFiber_le_of_hasUniversallyBoundedFibers B S hS V a ha
  refine ⟨n + 1, Nat.succ_pos n,
    eq_sheafify_bot_of_range_pointsMap_ι_eq_empty B S hS X hX (hUopen _) ?_⟩
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx ↦ n.not_succ_le_self ?_
  exact_mod_cast (hdeg (n + 1) x hx).trans (hn x)

/-- A descending chain of open subspaces of a reasonable algebraic space whose `p`-th member
contains only points over which a fixed affine étale chart has at least `p` points reaches the
empty open subspace. -/
theorem exists_pos_eq_sheafify_bot_of_isReasonableSpace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hr : IsReasonableSpace B S hS X)
    {V : BigFppfOver B S hS} (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    {a : yoneda.obj V ⟶ X} (ha : IsEtale B S hS a)
    (U : ℕ → Subfunctor X) (hUopen : ∀ p, IsOpenSubspace B S hS (U p))
    (hdeg : ∀ (p : ℕ) (x : points B S hS X),
      x ∈ Set.range (pointsMap B S hS (U p).toFunctor (U p).ι) →
        ((p : ℕ) : Cardinal.{u + 1}) ≤
          Cardinal.mk (pointsMap B S hS (yoneda.obj V) a ⁻¹' {x})) :
    ∃ n : ℕ, 0 < n ∧ U n = (⊥ : Subfunctor X).sheafify (BigFppfOver.topology B S hS) :=
  exists_pos_eq_sheafify_bot_of_hasUniversallyBoundedFibers B S hS hX
    (hr V hV a ((isEtale_iff_presheaf_of_yoneda B S hS a).1 ha)) U hUopen hdeg

/-! ### The finite filtration of Stacks 07ST -/

namespace SchemeStratification

variable {B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Stratification data whose chain reaches the empty open subspace at a positive index and whose
charts are quasi-compact gives a finite descending filtration of `X` by open subspaces, starting at
`X` and ending at the empty open subspace, whose reduced strata have quasi-compact separated
schemes as surjective étale neighbourhoods, isomorphic above the stratum. -/
theorem exists_finiteFiltration_of_compactSpace (strat : SchemeStratification B S hS X)
    (hcompact : ∀ p, CompactSpace ((BigFppfOver.toScheme B S hS).obj (strat.chart p)))
    {m : ℕ} (hm : 0 < m)
    (hterm : strat.openPart m = (⊥ : Subfunctor X).sheafify (BigFppfOver.topology B S hS)) :
    ∃ (n : ℕ) (U : ℕ → Subfunctor X),
      0 < n ∧ U 0 = ⊤ ∧
      U n = (⊥ : Subfunctor X).sheafify (BigFppfOver.topology B S hS) ∧
      (∀ p ≤ n, IsOpenSubspace B S hS (U p)) ∧
      (∀ p < n, U (p + 1) ≤ U p) ∧
      ∃ (T : (p : Fin n) → Subfunctor (U p.val).toFunctor)
        (V : Fin n → BigFppfOver B S hS)
        (f : ∀ p : Fin n, yoneda.obj (V p) ⟶ (U p.val).toFunctor),
        ∀ p : Fin n,
          IsClosedSubspace B S hS (T p) ∧
          (Set.range (pointsMap B S hS (T p).toFunctor ((T p).ι ≫ (U p.val).ι)) =
            Set.range (pointsMap B S hS (U p.val).toFunctor (U p.val).ι) \
              Set.range (pointsMap B S hS (U (p.val + 1)).toFunctor (U (p.val + 1)).ι)) ∧
          HasEtaleLocalProperty B S hS (T p).toFunctor (fun Y : Scheme.{u} => IsReduced Y) ∧
          CompactSpace ((BigFppfOver.toScheme B S hS).obj (V p)) ∧
          Scheme.IsSeparated ((BigFppfOver.toScheme B S hS).obj (V p)) ∧
          (MorphismProperty.inverseImage
            (@Surjective.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)).presheaf (f p) ∧
          IsEtale B S hS (f p) ∧
          IsIso (pullback.fst (T p).ι (f p)) :=
  ⟨m, strat.openPart, hm, strat.openPart_zero, hterm,
    fun p _ ↦ strat.isOpenSubspace_openPart p, fun p _ ↦ strat.openPart_succ_le p,
    fun p ↦ strat.stratum p.val, fun p ↦ strat.chart p.val, fun p ↦ strat.chartHom p.val,
    fun p ↦ ⟨strat.isClosedSubspace_stratum p.val, strat.range_stratum p.val,
      strat.isReduced_stratum p.val, hcompact p.val, strat.isSeparated_chart p.val,
      strat.surjective_chartHom p.val, strat.isEtale_chartHom p.val,
      strat.isIso_pullback_stratum p.val⟩⟩

end SchemeStratification

end AlgebraicGeometry.Space

end
