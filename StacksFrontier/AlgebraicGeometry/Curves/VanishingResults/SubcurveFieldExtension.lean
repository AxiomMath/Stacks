module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.SubcurveGlobalGeneration
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeFieldExtension
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.GlobalGeneration
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.FieldExtension
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedProduct
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.RingTheory.GeometricallyIntegral.GenericPointIrreducible
public import StacksFrontier.RingTheory.GeometricallyIntegral.FibreLocusSchemeBridge
public import StacksFrontier.RingTheory.GeometricallyIntegral.ReducedFibre
public import StacksFrontier.Topology.Dimension.DimensionLEOne
public import StacksFrontier.RingTheory.GeometricallyReduced.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import StacksCore.Tactic.StacksAttribute

/-!
# Global generation from degree bounds on subcurves over an arbitrary field

Let `k` be a field and `X` a proper reduced scheme of dimension one over `k`, and let `ℒ` be an
invertible `𝒪_X`-module with `deg(ℒ|_Y) ≥ 2 dim_k H¹(Y, 𝒪_Y)` for every reduced connected closed
subscheme `Y ⊆ X` of dimension one. [Stacks, Tag 0E3F] asserts that `ℒ` is globally generated.
For an infinite field this is `AlgebraicGeometry.isGeneratedByGlobalSections_of_infinite`; this
file removes that assumption by extending the ground field to `K = k(t)`, as the source does.

## Main results

* `AlgebraicGeometry.exists_mem_irreducibleComponents_subset_of_isPreconnected`: in a Noetherian
  sober space of dimension at most one, a connected closed set of positive dimension is the union
  of the irreducible components of the space it contains.
* `AlgebraicGeometry.exists_isPullback_vanishingIdeal_preimage`: the reduced structure on the
  preimage of a closed set is the base change of the reduced structure, when that base change is
  reduced.
* `AlgebraicGeometry.isGeneratedByGlobalSections_of_forall_subcurve_lt`: global generation from
  `-2 χ(Y, 𝒪_Y) < deg(ℒ|_Y)` and `h¹(Y, 𝒪_Y) < deg(ℒ|_Y) + χ(Y, 𝒪_Y)` on every subcurve `Y`.
* `AlgebraicGeometry.isGeneratedByGlobalSections_of_subcurve_bounds`: global generation from the
  bound of the tag on proper subcurves and these two inequalities on `X`.
* `AlgebraicGeometry.isGeneratedByGlobalSections_of_forall_subcurve`: **[Stacks, Tag 0E3F]**.

## The argument

`K = k(t)` is infinite, geometrically irreducible and geometrically reduced over `k`, so for
`p : X_K ⟶ X` the irreducible components of `X_K` are the preimages of those of `X`
([Stacks, Tag 038F]) and `X_K` is reduced ([Stacks, Tag 035Z]). A connected closed subset `T'` of
`X_K` of dimension one is a union of irreducible components, hence the preimage of the connected
closed set `T = p(T')`, and the reduced structure on `T'` is the base change of the reduced
structure `Y` on `T`. Flat base change ([Stacks, Tag 02KH]) and [Stacks, Tag 0B59] identify
`h¹(𝒪)` and the degree of `ℒ` on the two, so the hypothesis on `X` gives the hypothesis on `X_K`.
Global generation of `ℒ_K` descends to `ℒ` ([Stacks, Tag 0B57]).

## References

* [Stacks Project, Tag 0E3F](https://stacks.math.columbia.edu/tag/0E3F)
* [Stacks Project, Tag 0B57](https://stacks.math.columbia.edu/tag/0B57)
* [Stacks Project, Tag 0B59](https://stacks.math.columbia.edu/tag/0B59)
* [Stacks Project, Tag 035Z](https://stacks.math.columbia.edu/tag/035Z)
* [Stacks Project, Tag 038F](https://stacks.math.columbia.edu/tag/038F)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-! ### Connected closed sets in a space of dimension at most one -/

/-- **In a Noetherian sober `T0` space of dimension at most one, a connected closed set of positive
dimension is the union of the irreducible components it contains.** Write the closed set as a
finite union of irreducible closed sets; each is an irreducible component or a closed point, and a
closed point lying on no irreducible component inside the set would be an isolated point of it. -/
theorem exists_mem_irreducibleComponents_subset_of_isPreconnected {α : Type*}
    [TopologicalSpace α] [T0Space α] [NoetherianSpace α] [QuasiSober α]
    (hdim : topologicalKrullDim α ≤ 1) {T : Set α} (hT : IsClosed T)
    (hTc : IsPreconnected T) (hT0 : ¬ topologicalKrullDim T ≤ 0) {x : α} (hx : x ∈ T) :
    ∃ C ∈ irreducibleComponents α, C ⊆ T ∧ x ∈ C := by
  obtain ⟨S, hSf, hScl, hSi, hST⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hT
  by_contra hno
  push Not at hno
  have hpt : ∀ t ∈ S, x ∈ t → t = {x} := fun t ht hxt => by
    have htT : t ⊆ T := hST ▸ Set.subset_sUnion_of_mem ht
    have hTc' : ∀ C ∈ irreducibleComponents α, ¬ C ⊆ t := fun C hC hCt => by
      obtain ⟨C', hC', htC'⟩ :=
        exists_mem_irreducibleComponents_subset_of_isIrreducible t (hSi t ht)
      have hCC' : C' ⊆ C := hC.2 hC'.1 (hCt.trans htC')
      have htC : t = C := hCt.antisymm' (htC'.trans hCC')
      exact hno t (htC ▸ hC) htT hxt
    obtain ⟨η, hη⟩ := QuasiSober.sober (hSi t ht) (hScl t ht)
    have hηc : closure ({η} : Set α) = t := isGenericPoint_def.1 hη
    rw [(Stacks.Topology.Dimension.isClosed_singleton_of_not_irreducibleComponent_subset
      hdim (hScl t ht) hTc' hη.mem).closure_eq] at hηc
    rw [← hηc] at hxt ⊢
    rw [Set.mem_singleton_iff.mp hxt]
  obtain ⟨t₀, ht₀, hxt₀⟩ := Set.mem_sUnion.mp (show x ∈ ⋃₀ S from hST ▸ hx)
  have hxcl : IsClosed ({x} : Set α) := hpt t₀ ht₀ hxt₀ ▸ hScl t₀ ht₀
  let R := ⋃₀ {t ∈ S | x ∉ t}
  have hRcl : IsClosed R :=
    (hSf.subset (Set.sep_subset _ _)).isClosed_sUnion fun t ht => hScl t ht.1
  have hxR : x ∉ R := fun h => by
    obtain ⟨t, ht, hxt⟩ := Set.mem_sUnion.mp h
    exact ht.2 hxt
  have hcov : T ⊆ {x} ∪ R := fun y hy => by
    obtain ⟨t, ht, hyt⟩ := Set.mem_sUnion.mp (show y ∈ ⋃₀ S from hST ▸ hy)
    by_cases hxt : x ∈ t
    · rw [hpt t ht hxt] at hyt
      exact Or.inl hyt
    · exact Or.inr (Set.mem_sUnion.mpr ⟨t, ⟨ht, hxt⟩, hyt⟩)
  have hsub : T ⊆ {x} := by
    intro y hy
    rcases hcov hy with h | h
    · exact h
    · obtain ⟨z, -, hz1, hz2⟩ := isPreconnected_closed_iff.mp hTc {x} R hxcl hRcl hcov
        ⟨x, hx, rfl⟩ ⟨y, hy, h⟩
      exact absurd (Set.mem_singleton_iff.mp hz1 ▸ hz2) hxR
  have : Subsingleton T := ⟨fun a b => Subtype.ext ((hsub a.2).trans (hsub b.2).symm)⟩
  exact hT0 topologicalKrullDim_nonpos_of_subsingleton

/-! ### The rational function field -/

section RationalFunctions

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (k : Type u) [Field k]

/-- Base change of a reduced algebra along `k ⟶ k(t)` is reduced: `k(t) ⊗[k] S` is a localization
of `k[t] ⊗[k] S = S[t]`. -/
theorem isReduced_tensorProduct_fractionRing_polynomial (S : Type u) [CommRing S] [Algebra k S]
    [_root_.IsReduced S] : _root_.IsReduced (FractionRing (Polynomial k) ⊗[k] S) := by
  have := isReduced_polynomial S
  have h : _root_.IsReduced (Polynomial k ⊗[k] S) :=
    isReduced_of_injective
      ((Algebra.TensorProduct.comm k (Polynomial k) S).trans
        ((polyEquivTensor k S).symm.restrictScalars k)) (AlgEquiv.injective _)
  rw [isReduced_congr (Algebra.TensorProduct.cancelBaseChange k (Polynomial k)
    (FractionRing (Polynomial k)) (FractionRing (Polynomial k)) S).symm.toRingEquiv]
  exact isReduced_localizationPreserves
    (Algebra.algebraMapSubmonoid (Polynomial k ⊗[k] S) (nonZeroDivisors (Polynomial k))) _ h

/-- `k(t)` is geometrically reduced over `k`. -/
theorem geometricallyReduced_specMap_fractionRing_polynomial :
    GeometricallyReduced (Spec.map (CommRingCat.ofHom
      (algebraMap k (FractionRing (Polynomial k))))) := by
  rw [geometricallyReduced_algebraMap_iff_isGeometricallyReduced,
    Algebra.isGeometricallyReduced_iff_forall_isReduced_tensorProduct]
  exact fun K _ _ => isReduced_tensorProduct_fractionRing_polynomial k K

/-- `k(t)` is geometrically irreducible over `k`. -/
theorem geometricallyIrreducible_specMap_fractionRing_polynomial :
    GeometricallyIrreducible (Spec.map (CommRingCat.ofHom
      (algebraMap k (FractionRing (Polynomial k))))) :=
  (Algebra.isGeometricallyIrreducible_iff_isFractionRing k (Polynomial k)
    (FractionRing (Polynomial k))).mp (Algebra.isGeometricallyIrreducible_polynomial k)

/-- `k(t)` is infinite. -/
theorem infinite_fractionRing_polynomial : Infinite (FractionRing (Polynomial k)) :=
  Infinite.of_injective _ (IsFractionRing.injective (Polynomial k) (FractionRing (Polynomial k)))

end RationalFunctions

/-! ### Reduced closed subschemes under base change -/

open Scheme.IdealSheafData in
/-- **The reduced structure on the preimage of a closed set is the base change of the reduced
structure on the closed set**, when that base change is reduced: the pulled back ideal sheaf
then cuts out a reduced closed subscheme with the right support. -/
theorem exists_isPullback_vanishingIdeal_preimage {X X' : Scheme.{u}} (p : X' ⟶ X)
    (T : Closeds X) (hred : IsReduced (pullback p (vanishingIdeal T).subschemeι)) :
    ∃ q : (vanishingIdeal (T.preimage p.continuous)).subscheme ⟶ (vanishingIdeal T).subscheme,
      IsPullback q (vanishingIdeal (T.preimage p.continuous)).subschemeι
        (vanishingIdeal T).subschemeι p := by
  have : IsReduced ((vanishingIdeal T).comap p).subscheme :=
    isReduced_of_isOpenImmersion ((vanishingIdeal T).comapIso p).hom
  have hsupp : ((vanishingIdeal T).comap p).support = T.preimage p.continuous := by
    rw [support_comap]
    congr 1
  have hpb : ∃ q : ((vanishingIdeal T).comap p).subscheme ⟶ (vanishingIdeal T).subscheme,
      IsPullback q ((vanishingIdeal T).comap p).subschemeι (vanishingIdeal T).subschemeι p := by
    refine ⟨((vanishingIdeal T).comapIso p).hom ≫ pullback.snd _ _, ?_⟩
    refine (isPullback_of_isClosedImmersion _ _ _ _ ?_ ?_).flip
    · rw [← comapIso_hom_fst, Category.assoc, pullback.condition, Category.assoc]
    · simp only [ker_subschemeι]
  rwa [eq_vanishingIdeal_of_isReduced_subscheme _ _ hsupp] at hpb

/-- A space of topological Krull dimension one is nonempty. -/
private theorem nonempty_of_topologicalKrullDim_eq_one {Z : Type*} [TopologicalSpace Z]
    (h : topologicalKrullDim Z = 1) : Nonempty Z := by
  by_contra hne
  rw [not_nonempty_iff, ← topologicalKrullDim_eq_bot_iff_isEmpty] at hne
  exact absurd (hne.symm.trans h) (by decide)

/-! ### Extending the ground field to `k(t)` -/

section FieldExtension

open Scheme.IdealSheafData

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The base change map `Spec k(t) ⟶ Spec k`. -/
abbrev specFractionRingPolynomial (k : Type u) [Field k] :
    Spec (.of (FractionRing (Polynomial k))) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (FractionRing (Polynomial k))))

/-- **Base change to `k(t)` preserves the dimension, `h¹(𝒪)` and the degree of `ℒ` on the reduced
structure of a closed set and of its preimage.** The reduced structure `Y'` on the preimage of `T`
in `X_{k(t)}` is the base change of the reduced structure `Y` on `T`
(`AlgebraicGeometry.exists_isPullback_vanishingIdeal_preimage`, the base change being reduced by
[Stacks, Tag 035Z]), so [Stacks, Tag 0BY9], flat base change and [Stacks, Tag 0B59] apply. -/
theorem baseChange_fractionRing_polynomial_vanishingIdeal [IsProper f] (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (T : Closeds X) :
    topologicalKrullDim (vanishingIdeal (T.preimage
        (pullback.snd (specFractionRingPolynomial k) f).continuous)).subscheme =
        topologicalKrullDim (vanishingIdeal T).subscheme ∧
      (∀ n, Module.finrank (FractionRing (Polynomial k)) (cohomologyOverField
          (FractionRing (Polynomial k))
          ((vanishingIdeal (T.preimage
            (pullback.snd (specFractionRingPolynomial k) f).continuous)).subschemeι ≫
            pullback.fst (specFractionRingPolynomial k) f)
          (SheafOfModules.unit (vanishingIdeal (T.preimage
            (pullback.snd (specFractionRingPolynomial k) f).continuous)).subscheme.ringCatSheaf)
            n) =
        Module.finrank k (cohomologyOverField k ((vanishingIdeal T).subschemeι ≫ f)
          (SheafOfModules.unit (vanishingIdeal T).subscheme.ringCatSheaf) n)) ∧
      ∀ (hY : topologicalKrullDim (vanishingIdeal T).subscheme ≤ 1)
        (hY' : topologicalKrullDim (vanishingIdeal (T.preimage
          (pullback.snd (specFractionRingPolynomial k) f).continuous)).subscheme ≤ 1),
        letI := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback
          (vanishingIdeal T).subschemeι L hL
        letI := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback
          (vanishingIdeal (T.preimage
            (pullback.snd (specFractionRingPolynomial k) f).continuous)).subschemeι
          ((Scheme.Modules.pullback (pullback.snd (specFractionRingPolynomial k) f)).obj L)
          (Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback
            (pullback.snd (specFractionRingPolynomial k) f) L hL)
        haveI : IsProper ((vanishingIdeal (T.preimage
            (pullback.snd (specFractionRingPolynomial k) f).continuous)).subschemeι ≫
            pullback.fst (specFractionRingPolynomial k) f) := by
          have : IsProper (pullback.fst (specFractionRingPolynomial k) f) :=
            MorphismProperty.of_isPullback (P := @IsProper)
              (IsPullback.of_hasPullback (specFractionRingPolynomial k) f).flip inferInstance
          infer_instance
        invertibleCurveDegree (FractionRing (Polynomial k))
            ((vanishingIdeal (T.preimage
              (pullback.snd (specFractionRingPolynomial k) f).continuous)).subschemeι ≫
              pullback.fst (specFractionRingPolynomial k) f) hY'
            ((Scheme.Modules.pullback (vanishingIdeal (T.preimage
              (pullback.snd (specFractionRingPolynomial k) f).continuous)).subschemeι).obj
              ((Scheme.Modules.pullback (pullback.snd (specFractionRingPolynomial k) f)).obj L)) =
          invertibleCurveDegree k ((vanishingIdeal T).subschemeι ≫ f) hY
            ((Scheme.Modules.pullback (vanishingIdeal T).subschemeι).obj L) := by
  have := geometricallyReduced_specMap_fractionRing_polynomial k
  have hP : IsPullback (pullback.snd (specFractionRingPolynomial k) f)
      (pullback.fst (specFractionRingPolynomial k) f) f (specFractionRingPolynomial k) :=
    (IsPullback.of_hasPullback (specFractionRingPolynomial k) f).flip
  have := isReduced_pullback (specFractionRingPolynomial k) ((vanishingIdeal T).subschemeι ≫ f)
  have hred : IsReduced (pullback (pullback.snd (specFractionRingPolynomial k) f)
      (vanishingIdeal T).subschemeι) :=
    isReduced_of_isOpenImmersion
      (pullbackLeftPullbackSndIso (specFractionRingPolynomial k) f
        (vanishingIdeal T).subschemeι).hom
  obtain ⟨q, hq⟩ :=
    exists_isPullback_vanishingIdeal_preimage (pullback.snd (specFractionRingPolynomial k) f) T hred
  have H : IsPullback q ((vanishingIdeal (T.preimage
        (pullback.snd (specFractionRingPolynomial k) f).continuous)).subschemeι ≫
        pullback.fst (specFractionRingPolynomial k) f)
      ((vanishingIdeal T).subschemeι ≫ f) (specFractionRingPolynomial k) := hq.paste_vert hP
  have : IsProper ((vanishingIdeal T).subschemeι ≫ f) := inferInstance
  refine ⟨topologicalKrullDim_baseChange k (FractionRing (Polynomial k)) q _ _ H, fun n => ?_,
    fun hY hY' => ?_⟩
  · exact (finrank_cohomologyOverField_eq_of_iso _ _
      (Scheme.Modules.pullbackUnitIso q) n).symm.trans <|
      finrank_cohomologyOverField_baseChange_field k (FractionRing (Polynomial k)) q _ _ H
      (SheafOfModules.unit (vanishingIdeal T).subscheme.ringCatSheaf) n
  · have := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback
      (vanishingIdeal T).subschemeι L hL
    have := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback q
      ((Scheme.Modules.pullback (vanishingIdeal T).subschemeι).obj L) inferInstance
    have := Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme _
      ((Scheme.Modules.pullback (vanishingIdeal T).subschemeι).obj L)
    have := isFiniteLocallyFreeOfRank_pullback q
      ((Scheme.Modules.pullback (vanishingIdeal T).subschemeι).obj L) 1
    let e : (Scheme.Modules.pullback q).obj
        ((Scheme.Modules.pullback (vanishingIdeal T).subschemeι).obj L) ≅
        (Scheme.Modules.pullback (vanishingIdeal (T.preimage
          (pullback.snd (specFractionRingPolynomial k) f).continuous)).subschemeι).obj
          ((Scheme.Modules.pullback (pullback.snd (specFractionRingPolynomial k) f)).obj L) :=
      (Scheme.Modules.pullbackComp q (vanishingIdeal T).subschemeι).app L ≪≫
        (Scheme.Modules.pullbackCongr hq.w).app L ≪≫
        ((Scheme.Modules.pullbackComp _ _).app L).symm
    rw [← invertibleCurveDegree_eq_of_iso _ _ hY' e, invertibleCurveDegree_eq_curveDegree,
      invertibleCurveDegree_eq_curveDegree]
    exact curveDegree_baseChange_field k (FractionRing (Polynomial k)) q _ _ H hY
      ((Scheme.Modules.pullback (vanishingIdeal T).subschemeι).obj L) 1

/-- **The subcurve degree bound passes to `X_{k(t)}`.** A connected closed subset `T'` of
`X_{k(t)}` of dimension one is a union of irreducible components
(`AlgebraicGeometry.exists_mem_irreducibleComponents_subset_of_isPreconnected`), each the preimage
of its image ([Stacks, Tag 038F]), so `T'` is the preimage of the connected closed set
`T = \overline{p(T')}`; `AlgebraicGeometry.baseChange_fractionRing_polynomial_vanishingIdeal`
identifies the dimension, `h¹(𝒪)` and the degree of `ℒ` on the reduced structures of `T` and
`T'`. -/
theorem baseChange_fractionRing_polynomial_subcurve_bound [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (h : ∀ (Y : X.IdealSheafData) [IsReduced Y.subscheme] [ConnectedSpace Y.subscheme]
      (hY : topologicalKrullDim Y.subscheme = 1),
      letI := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback Y.subschemeι L hL
      2 * (Module.finrank k (cohomologyOverField k (Y.subschemeι ≫ f)
          (SheafOfModules.unit Y.subscheme.ringCatSheaf) 1) : ℤ) -
          2 * (Module.finrank k (cohomologyOverField k (Y.subschemeι ≫ f)
            (SheafOfModules.unit Y.subscheme.ringCatSheaf) 0) : ℤ) <
        invertibleCurveDegree k (Y.subschemeι ≫ f) hY.le
          ((Scheme.Modules.pullback Y.subschemeι).obj L) ∧
      2 * (Module.finrank k (cohomologyOverField k (Y.subschemeι ≫ f)
          (SheafOfModules.unit Y.subscheme.ringCatSheaf) 1) : ℤ) <
        invertibleCurveDegree k (Y.subschemeι ≫ f) hY.le
          ((Scheme.Modules.pullback Y.subschemeι).obj L) +
        (Module.finrank k (cohomologyOverField k (Y.subschemeι ≫ f)
          (SheafOfModules.unit Y.subscheme.ringCatSheaf) 0) : ℤ))
    (T' : Closeds (pullback (specFractionRingPolynomial k) f : Scheme.{u}))
    (hT'c : _root_.IsPreconnected
      (T' : Set (pullback (specFractionRingPolynomial k) f : Scheme.{u})))
    (hY' : topologicalKrullDim (vanishingIdeal T').subscheme = 1) :
    letI := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback
      (vanishingIdeal T').subschemeι
      ((Scheme.Modules.pullback (pullback.snd (specFractionRingPolynomial k) f)).obj L)
      (Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback
        (pullback.snd (specFractionRingPolynomial k) f) L hL)
    haveI : IsProper ((vanishingIdeal T').subschemeι ≫
        pullback.fst (specFractionRingPolynomial k) f) := by
      have : IsProper (pullback.fst (specFractionRingPolynomial k) f) :=
        MorphismProperty.of_isPullback (P := @IsProper)
          (IsPullback.of_hasPullback (specFractionRingPolynomial k) f).flip inferInstance
      infer_instance
    2 * (Module.finrank (FractionRing (Polynomial k)) (cohomologyOverField
        (FractionRing (Polynomial k))
        ((vanishingIdeal T').subschemeι ≫ pullback.fst (specFractionRingPolynomial k) f)
        (SheafOfModules.unit (vanishingIdeal T').subscheme.ringCatSheaf) 1) : ℤ) -
      2 * (Module.finrank (FractionRing (Polynomial k)) (cohomologyOverField
        (FractionRing (Polynomial k))
        ((vanishingIdeal T').subschemeι ≫ pullback.fst (specFractionRingPolynomial k) f)
        (SheafOfModules.unit (vanishingIdeal T').subscheme.ringCatSheaf) 0) : ℤ) <
      invertibleCurveDegree (FractionRing (Polynomial k))
        ((vanishingIdeal T').subschemeι ≫ pullback.fst (specFractionRingPolynomial k) f) hY'.le
        ((Scheme.Modules.pullback (vanishingIdeal T').subschemeι).obj
          ((Scheme.Modules.pullback (pullback.snd (specFractionRingPolynomial k) f)).obj L)) ∧
      2 * (Module.finrank (FractionRing (Polynomial k)) (cohomologyOverField
        (FractionRing (Polynomial k))
        ((vanishingIdeal T').subschemeι ≫ pullback.fst (specFractionRingPolynomial k) f)
        (SheafOfModules.unit (vanishingIdeal T').subscheme.ringCatSheaf) 1) : ℤ) <
      invertibleCurveDegree (FractionRing (Polynomial k))
        ((vanishingIdeal T').subschemeι ≫ pullback.fst (specFractionRingPolynomial k) f) hY'.le
        ((Scheme.Modules.pullback (vanishingIdeal T').subschemeι).obj
          ((Scheme.Modules.pullback (pullback.snd (specFractionRingPolynomial k) f)).obj L)) +
      (Module.finrank (FractionRing (Polynomial k)) (cohomologyOverField
        (FractionRing (Polynomial k))
        ((vanishingIdeal T').subschemeι ≫ pullback.fst (specFractionRingPolynomial k) f)
        (SheafOfModules.unit (vanishingIdeal T').subscheme.ringCatSheaf) 0) : ℤ) := by
  have := geometricallyIrreducible_specMap_fractionRing_polynomial k
  have hP : IsPullback (pullback.snd (specFractionRingPolynomial k) f)
      (pullback.fst (specFractionRingPolynomial k) f) f (specFractionRingPolynomial k) :=
    (IsPullback.of_hasPullback (specFractionRingPolynomial k) f).flip
  have : IsProper (pullback.fst (specFractionRingPolynomial k) f) :=
    MorphismProperty.of_isPullback (P := @IsProper) hP inferInstance
  have : IsNoetherian (pullback (specFractionRingPolynomial k) f : Scheme.{u}) :=
    isNoetherian_of_locallyOfFiniteType (pullback.fst (specFractionRingPolynomial k) f)
  have hdim' : topologicalKrullDim (pullback (specFractionRingPolynomial k) f : Scheme.{u}) ≤ 1 :=
    (topologicalKrullDim_baseChange k (FractionRing (Polynomial k)) _ _ f hP).trans_le hdim
  have hgi : GeometricallyIrreducible (pullback.snd (specFractionRingPolynomial k) f) :=
    MorphismProperty.of_isPullback (P := @GeometricallyIrreducible)
      (IsPullback.of_hasPullback (specFractionRingPolynomial k) f) inferInstance
  have hopen : IsOpenMap (pullback.snd (specFractionRingPolynomial k) f) :=
    (pullback.snd (specFractionRingPolynomial k) f).isOpenMap
  -- `T'` is the preimage of `T = closure (p '' T')`.
  have hT'd : ¬ topologicalKrullDim
      (T' : Set (pullback (specFractionRingPolynomial k) f : Scheme.{u})) ≤ 0 := by
    rw [← Scheme.IdealSheafData.topologicalKrullDim_support, coe_support_vanishingIdeal] at hY'
    rw [hY']
    decide
  have hpre : (⇑(pullback.snd (specFractionRingPolynomial k) f)) ⁻¹'
      ((⇑(pullback.snd (specFractionRingPolynomial k) f)) '' T') = T' := by
    refine Set.Subset.antisymm (fun y hy => ?_) (Set.subset_preimage_image _ _)
    obtain ⟨x, hxT, hxy⟩ := hy
    obtain ⟨C, hC, hCT, hxC⟩ := exists_mem_irreducibleComponents_subset_of_isPreconnected hdim'
      T'.isClosed hT'c hT'd hxT
    let e := (pullback.snd (specFractionRingPolynomial k) f).irreducibleComponentsEquiv hopen
    have hCe : (⇑(pullback.snd (specFractionRingPolynomial k) f)) ⁻¹'
        ((⇑(pullback.snd (specFractionRingPolynomial k) f)) '' C) = C :=
      congrArg Subtype.val (e.symm_apply_apply ⟨C, hC⟩)
    exact hCT (hCe ▸ (show y ∈ (⇑(pullback.snd (specFractionRingPolynomial k) f)) ⁻¹'
      ((⇑(pullback.snd (specFractionRingPolynomial k) f)) '' C) from ⟨x, hxC, hxy⟩))
  obtain ⟨T, hTeq, hTc⟩ : ∃ T : Closeds X,
      T.preimage (pullback.snd (specFractionRingPolynomial k) f).continuous = T' ∧
      _root_.IsPreconnected (T : Set X) := by
    refine ⟨⟨closure ((⇑(pullback.snd (specFractionRingPolynomial k) f)) '' T'),
        isClosed_closure⟩, Closeds.ext ?_,
      (hT'c.image _
        (pullback.snd (specFractionRingPolynomial k) f).continuous.continuousOn).closure⟩
    change (⇑(pullback.snd (specFractionRingPolynomial k) f)) ⁻¹'
      closure ((⇑(pullback.snd (specFractionRingPolynomial k) f)) '' T') = T'
    rw [hopen.preimage_closure_eq_closure_preimage
      (pullback.snd (specFractionRingPolynomial k) f).continuous, hpre, T'.isClosed.closure_eq]
  subst hTeq
  obtain ⟨hdimeq, hh1, hdeg⟩ := baseChange_fractionRing_polynomial_vanishingIdeal f L T
  have hYT : topologicalKrullDim (vanishingIdeal T).subscheme = 1 := hdimeq ▸ hY'
  have hYne : Nonempty (vanishingIdeal T).subscheme :=
    nonempty_of_topologicalKrullDim_eq_one hYT
  have hYconn : ConnectedSpace (vanishingIdeal T).subscheme := by
    have hrange : Set.range (vanishingIdeal T).subschemeι.base = T := by
      rw [(vanishingIdeal T).range_subschemeι, coe_support_vanishingIdeal]
    have hpc : _root_.IsPreconnected (Set.range (vanishingIdeal T).subschemeι.base) := hrange ▸ hTc
    rw [← Set.image_univ] at hpc
    have hu := ((vanishingIdeal T).subschemeι.isClosedEmbedding.isInducing.isPreconnected_image).mp
      hpc
    exact { toPreconnectedSpace := ⟨hu⟩, toNonempty := hYne }
  rw [hh1 1, hh1 0, hdeg hYT.le hY'.le]
  exact h (vanishingIdeal T) hYT

/-! ### Global generation over an arbitrary field -/

/-- **Global generation from two inequalities on every subcurve.** Let `X` be a proper reduced
scheme of dimension at most one over a field `k` and `ℒ` an invertible `𝒪_X`-module such that
every reduced connected closed subscheme `Y ⊆ X` of dimension one satisfies
`-2 χ(Y, 𝒪_Y) < deg(ℒ|_Y)` and `h¹(Y, 𝒪_Y) < deg(ℒ|_Y) + χ(Y, 𝒪_Y)`. Then `ℒ` is globally
generated. These are the two consequences of the bound of [Stacks, Tag 0E3F] which its proof
uses; over an infinite field this is `AlgebraicGeometry.isGeneratedByGlobalSections_of_infinite`,
and in general the hypothesis passes to `X_{k(t)}`
(`AlgebraicGeometry.baseChange_fractionRing_polynomial_subcurve_bound`), which is proper, reduced
([Stacks, Tag 035Z]) and of dimension one over the infinite field `k(t)`, while global generation
of the base change of `ℒ` descends to `ℒ` ([Stacks, Tag 0B57]). -/
theorem isGeneratedByGlobalSections_of_forall_subcurve_lt (f : X ⟶ Spec (.of k)) [IsProper f]
    [IsReduced X] (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (h : ∀ (Y : X.IdealSheafData) [IsReduced Y.subscheme] [ConnectedSpace Y.subscheme]
      (hY : topologicalKrullDim Y.subscheme = 1),
      letI := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback Y.subschemeι L hL
      2 * (Module.finrank k (cohomologyOverField k (Y.subschemeι ≫ f)
          (SheafOfModules.unit Y.subscheme.ringCatSheaf) 1) : ℤ) -
          2 * (Module.finrank k (cohomologyOverField k (Y.subschemeι ≫ f)
            (SheafOfModules.unit Y.subscheme.ringCatSheaf) 0) : ℤ) <
        invertibleCurveDegree k (Y.subschemeι ≫ f) hY.le
          ((Scheme.Modules.pullback Y.subschemeι).obj L) ∧
      2 * (Module.finrank k (cohomologyOverField k (Y.subschemeι ≫ f)
          (SheafOfModules.unit Y.subscheme.ringCatSheaf) 1) : ℤ) <
        invertibleCurveDegree k (Y.subschemeι ≫ f) hY.le
          ((Scheme.Modules.pullback Y.subschemeι).obj L) +
        (Module.finrank k (cohomologyOverField k (Y.subschemeι ≫ f)
          (SheafOfModules.unit Y.subscheme.ringCatSheaf) 0) : ℤ)) :
    _root_.SheafOfModules.IsGeneratedByGlobalSections L := by
  have := geometricallyReduced_specMap_fractionRing_polynomial k
  have := geometricallyIrreducible_specMap_fractionRing_polynomial k
  have := infinite_fractionRing_polynomial k
  have hP : IsPullback (pullback.snd (specFractionRingPolynomial k) f)
      (pullback.fst (specFractionRingPolynomial k) f) f (specFractionRingPolynomial k) :=
    (IsPullback.of_hasPullback (specFractionRingPolynomial k) f).flip
  have : IsProper (pullback.fst (specFractionRingPolynomial k) f) :=
    MorphismProperty.of_isPullback (P := @IsProper) hP inferInstance
  have : IsReduced (pullback (specFractionRingPolynomial k) f : Scheme.{u}) :=
    isReduced_pullback (specFractionRingPolynomial k) f
  have hdim' : topologicalKrullDim (pullback (specFractionRingPolynomial k) f : Scheme.{u}) ≤ 1 :=
    (topologicalKrullDim_baseChange k (FractionRing (Polynomial k)) _ _ f hP).trans_le hdim
  have hL' := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback
    (pullback.snd (specFractionRingPolynomial k) f) L hL
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : L.IsQuasicoherent := @isQuasicoherent_of_isCoherent _ _ _ _
    (Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X L)
  exact (Stacks.AlgebraicGeometry.FlatBaseChange.nonempty_generatingSections_pullback_iff hP L).mpr
    (isGeneratedByGlobalSections_of_infinite (pullback.fst (specFractionRingPolynomial k) f) hdim'
      ((Scheme.Modules.pullback (pullback.snd (specFractionRingPolynomial k) f)).obj L)
      (baseChange_fractionRing_polynomial_subcurve_bound f hdim L h))

/-- The cohomology of the structure sheaf of the closed subscheme `⊥`, which is `X`, is that of
`X`. -/
theorem finrank_cohomologyOverField_bot_unit [IsProper f] (n : ℕ) :
    Module.finrank k (cohomologyOverField k ((⊥ : X.IdealSheafData).subschemeι ≫ f)
      (SheafOfModules.unit (⊥ : X.IdealSheafData).subscheme.ringCatSheaf) n) =
      Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n) :=
  (finrank_cohomologyOverField_pushforward_of_isClosedImmersion k _ f _ n).trans
    (finrank_cohomologyOverField_eq_of_iso k f (closedSubschemeStructureSheafBotIso X) n)

/-- The degree of `ℒ` on the closed subscheme `⊥`, which is `X`, is the degree of `ℒ`. -/
theorem invertibleCurveDegree_bot [IsProper f] (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hY : topologicalKrullDim (⊥ : X.IdealSheafData).subscheme ≤ 1) :
    letI := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback
      (⊥ : X.IdealSheafData).subschemeι L hL
    invertibleCurveDegree k ((⊥ : X.IdealSheafData).subschemeι ≫ f) hY
      ((Scheme.Modules.pullback (⊥ : X.IdealSheafData).subschemeι).obj L) =
      invertibleCurveDegree k f hdim L := by
  have := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback
    (⊥ : X.IdealSheafData).subschemeι L hL
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hχ := eulerCharacteristic_tensorLeft_closedSubschemeStructureSheaf f L ⊥
    (isCoherent_tensorLeft_closedSubschemeStructureSheaf L (⊥ : X.IdealSheafData))
  let e : (Scheme.Modules.tensorLeft L).obj (closedSubschemeStructureSheaf ⊥) ≅ L :=
    (Scheme.Modules.tensorLeft L).mapIso (closedSubschemeStructureSheafBotIso X) ≪≫
      tensorSheafUnitRight X.toRingedSpace L
  unfold invertibleCurveDegree
  rw [← hχ, eulerCharacteristic_eq_finsum]
  congr 1
  · exact finsum_congr fun n => by rw [finrank_cohomologyOverField_eq_of_iso k f e n]
  · exact finsum_congr fun n => by rw [finrank_cohomologyOverField_bot_unit f n]

/-- **Global generation from a degree bound on proper subcurves and two inequalities on `X`.**
Let `X` be a proper reduced scheme of dimension at most one over a field `k` and `ℒ` an
invertible `𝒪_X`-module with `deg(ℒ|_Y) ≥ 2 h¹(Y, 𝒪_Y)` for every reduced connected closed
subscheme `Y ⊊ X` of dimension one, and with `-2 χ(X, 𝒪_X) < deg(ℒ)` and
`h¹(X, 𝒪_X) < deg(ℒ) + χ(X, 𝒪_X)`. Then `ℒ` is globally generated
(`AlgebraicGeometry.isGeneratedByGlobalSections_of_forall_subcurve_lt`; the reduced closed
subscheme with support `X` is `⊥`, whose invariants are those of `X`). -/
theorem isGeneratedByGlobalSections_of_subcurve_bounds (f : X ⟶ Spec (.of k)) [IsProper f]
    [IsReduced X] (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (ha : ∀ (Y : X.IdealSheafData) [IsReduced Y.subscheme] [ConnectedSpace Y.subscheme]
      (hY : topologicalKrullDim Y.subscheme = 1), Y ≠ ⊥ →
      letI := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback Y.subschemeι L hL
      2 * (Module.finrank k (cohomologyOverField k (Y.subschemeι ≫ f)
        (SheafOfModules.unit Y.subscheme.ringCatSheaf) 1) : ℤ) ≤
        invertibleCurveDegree k (Y.subschemeι ≫ f) hY.le
          ((Scheme.Modules.pullback Y.subschemeι).obj L))
    (hb₁ : 2 * (Module.finrank k (cohomologyOverField k f
        (SheafOfModules.unit X.ringCatSheaf) 1) : ℤ) -
      2 * (Module.finrank k (cohomologyOverField k f
        (SheafOfModules.unit X.ringCatSheaf) 0) : ℤ) < invertibleCurveDegree k f hdim L)
    (hb₂ : 2 * (Module.finrank k (cohomologyOverField k f
        (SheafOfModules.unit X.ringCatSheaf) 1) : ℤ) < invertibleCurveDegree k f hdim L +
      (Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) : ℤ)) :
    _root_.SheafOfModules.IsGeneratedByGlobalSections L := by
  refine isGeneratedByGlobalSections_of_forall_subcurve_lt f hdim L fun Y _ _ hY => ?_
  by_cases hY0 : Y = ⊥
  · subst hY0
    rw [finrank_cohomologyOverField_bot_unit f 0, finrank_cohomologyOverField_bot_unit f 1,
      invertibleCurveDegree_bot f hdim L hY.le]
    exact ⟨hb₁, hb₂⟩
  · have hYne : Nonempty Y.subscheme := nonempty_of_topologicalKrullDim_eq_one hY
    have hpos := finrank_cohomologyOverField_unit_zero_pos k (Y.subschemeι ≫ f)
    have := ha Y hY hY0
    constructor <;> omega

/-! ### Tag 0E3F -/

/-- **Stacks Project, Tag 0E3F.** Let `k` be a field and `X` a proper scheme over `k` which is
reduced and of dimension `1`, and let `ℒ` be an invertible `𝒪_X`-module such that
`deg(ℒ|_Y) ≥ 2 dim_k H¹(Y, 𝒪_Y)` for every reduced connected closed subscheme `Y ⊆ X` of
dimension `1`. Then `ℒ` is globally generated. The source's hypothesis that `X` is connected is
not needed.

As `h⁰(Y, 𝒪_Y) ≥ 1`, the bound gives `-2 χ(Y, 𝒪_Y) < deg(ℒ|_Y)` and
`h¹(Y, 𝒪_Y) < deg(ℒ|_Y) + χ(Y, 𝒪_Y)`, and
`AlgebraicGeometry.isGeneratedByGlobalSections_of_forall_subcurve_lt` applies. -/
@[stacks 0E3F]
theorem isGeneratedByGlobalSections_of_forall_subcurve (f : X ⟶ Spec (.of k)) [IsProper f]
    [IsReduced X] (hdim : topologicalKrullDim X = 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (h : ∀ (Y : X.IdealSheafData) [IsReduced Y.subscheme] [ConnectedSpace Y.subscheme]
      (hY : topologicalKrullDim Y.subscheme = 1),
      letI := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback Y.subschemeι L hL
      2 * (Module.finrank k (cohomologyOverField k (Y.subschemeι ≫ f)
        (SheafOfModules.unit Y.subscheme.ringCatSheaf) 1) : ℤ) ≤
        invertibleCurveDegree k (Y.subschemeι ≫ f) hY.le
          ((Scheme.Modules.pullback Y.subschemeι).obj L)) :
    _root_.SheafOfModules.IsGeneratedByGlobalSections L := by
  refine isGeneratedByGlobalSections_of_forall_subcurve_lt f hdim.le L fun Y _ _ hY => ?_
  have hYne : Nonempty Y.subscheme := nonempty_of_topologicalKrullDim_eq_one hY
  have hpos := finrank_cohomologyOverField_unit_zero_pos k (Y.subschemeι ≫ f)
  have := h Y hY
  constructor <;> omega

end FieldExtension

end AlgebraicGeometry

end
