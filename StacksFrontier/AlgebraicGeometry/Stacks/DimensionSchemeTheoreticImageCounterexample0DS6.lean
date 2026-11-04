module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.Jacobson.Ring
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenaryExamples
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleChartDiagramTest
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedStackClosedSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.RingTheory.NagataMonicLocalization
public import StacksFrontier.RingTheory.Polynomial.MonicLocalizationJacobson
public import StacksFrontier.Topology.Dimension.LocalKrullDim
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The affine line over an infinite-dimensional Noetherian Jacobson domain

Stacks 0DS6 says, for a quasi-compact, locally of finite type, quasi-DM 1-morphism `f : 𝒯 ⟶ 𝒳`
of Jacobson, pseudo-catenary, locally Noetherian algebraic stacks with `|𝒯|` irreducible and `𝒳`
quasi-separated, with scheme theoretic image `𝒵`, that exactly one of (1) `dim_t(𝒯_{f(t)}) > 0`
at every finite type point `t`, in which case `dim 𝒵 < dim 𝒯`, and (2) `dim 𝒯 = dim 𝒵` holds.

This file shows that the clause fails for the projection `f : 𝔸¹_R ⟶ Spec R` whenever `R` is a
Noetherian, Jacobson, universally catenary domain of infinite Krull dimension: every hypothesis
of Stacks 0DS6 holds, every fibre has dimension `1`, and `dim 𝒯 = dim 𝒵 = ∞`, so (1) and (2) both
hold.

## Main results

* `AlgebraicGeometry.Stack.exists_not_xor_relativeDimension_pos_of_ringKrullDim_eq_top`: the
  stack-level reduction, for any such ring `R` and any big fppf site containing `Spec R`.
* `AlgebraicGeometry.Stack.not_forall_xor_relativeDimension_pos`: Stacks 0DS6 without a
  finiteness hypothesis on `dim 𝒯` is false, at `R = N⟨X⟩` for Nagata's ring `N`
  (Brewer–Heinzer for the Jacobson property).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

/-! ### Extended integer arithmetic -/

/-- An extended integer bounding every natural number is `⊤`. -/
theorem eq_top_of_forall_natCast_le {E : EInt} (h : ∀ n : ℕ, (((n : ℤ) : ℤ) : EInt) ≤ E) :
    E = ⊤ := by
  induction E using WithBot.recBotCoe with
  | bot => exact absurd (h 0) (not_le.2 (WithBot.bot_lt_coe _))
  | coe E' =>
    induction E' using WithTop.recTopCoe with
    | top => rfl
    | coe z =>
      have h' := h (z.toNat + 1)
      have hz : ((((z.toNat + 1 : ℕ) : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) ≤
          (((z : WithTop ℤ)) : WithBot (WithTop ℤ)) := h'
      rw [WithBot.coe_le_coe, WithTop.coe_le_coe] at hz
      omega

/-- If a family of local dimensions has supremum `∞`, so does the family of the extended
integers `δ - 0` of Stacks 0AFN. -/
theorem iSup_dimensionSubNat_zero_eq_top {ι : Type*} {δ : ι → WithBot ℕ∞}
    (h : ⨆ i, δ i = ⊤) : ⨆ i, dimensionSubNat (δ i) 0 = ⊤ := by
  refine eq_top_of_forall_natCast_le fun n => ?_
  have hn : ((n : ℕ∞) : WithBot ℕ∞) < ⨆ i, δ i := by
    rw [h]
    exact WithBot.coe_lt_coe.2 (ENat.natCast_lt_top n)
  obtain ⟨i, hi⟩ := lt_iSup_iff.1 hn
  refine le_trans ?_ (le_iSup (fun i => dimensionSubNat (δ i) 0) i)
  generalize δ i = d at hi ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact absurd hi (not_lt.2 bot_le)
  | coe d' =>
    induction d' using WithTop.recTopCoe with
    | top => exact le_top
    | coe m =>
      show (((n : ℤ) : ℤ) : EInt) ≤ (((m : ℤ) - ((0 : ℕ) : ℤ) : ℤ) : EInt)
      rw [WithBotTop.coe_le_coe]
      have h1 : ((n : ℕ∞) : WithBot ℕ∞) < (((m : ℕ∞)) : WithBot ℕ∞) := hi
      have : n < m := by
        rw [WithBot.coe_lt_coe] at h1
        exact_mod_cast h1
      omega

/-- `D + 1 = ⊤` forces `D = ⊤` in the extended integers. -/
theorem eq_top_of_add_one_eq_top {D : EInt} (h : D + (((1 : ℤ) : ℤ) : EInt) = ⊤) : D = ⊤ := by
  have h1 : (((1 : ℤ) : ℤ) : EInt) = ((((1 : ℤ) : WithTop ℤ)) : WithBot (WithTop ℤ)) := rfl
  rw [h1] at h
  induction D using WithBot.recBotCoe with
  | bot => exact absurd h (by rw [WithBot.bot_add]; exact bot_ne_top)
  | coe D' =>
    induction D' using WithTop.recTopCoe with
    | top => rfl
    | coe z =>
      rw [← WithBot.coe_add, ← WithTop.coe_add] at h
      exact absurd h (fun h' => WithTop.coe_ne_top (WithBot.coe_injective h'))

/-! ### Stacks represented by schemes -/

section SchemeStack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Every point of the algebraic stack of a scheme of the site is the point named by a point of
the scheme through the chart of Stacks 04SW. -/
theorem representedChartPointMap_pointsEquivScheme_symm_pointsHomeomorphScheme
    (U : BigFppfOver B S hS)
    (t : points B S hS (schemeFibredCategory B S hS U).val
      (schemeFibredCategory B S hS U).property) :
    representedChartPointMap B S hS U ((Space.pointsEquivScheme B S hS U).symm
      (pointsHomeomorphScheme B S hS U t)) = t := by
  let := pointTopology B S hS (schemeFibredCategory B S hS U)
  refine (pointsHomeomorphScheme B S hS U).injective ?_
  rw [pointsHomeomorphScheme_representedChartPointMap_pointsEquivScheme_symm]

/-- A scheme of the site has the same points as its algebraic stack, so a property of all the
points of the stack is a property of all the points of the scheme read through the chart. -/
theorem forall_points_schemeStack (U : BigFppfOver B S hS)
    {Q : points B S hS (schemeFibredCategory B S hS U).val
      (schemeFibredCategory B S hS U).property → Prop}
    (h : ∀ a : (BigFppfOver.toScheme B S hS).obj U,
      Q (representedChartPointMap B S hS U ((Space.pointsEquivScheme B S hS U).symm a)))
    (t : points B S hS (schemeFibredCategory B S hS U).val
      (schemeFibredCategory B S hS U).property) : Q t := by
  rw [← representedChartPointMap_pointsEquivScheme_symm_pointsHomeomorphScheme B S hS U t]
  exact h _

/-- **The algebraic stack of a scheme of infinite dimension has infinite dimension.** The
dimension of Stacks 0AFN of `schemeStack U` at the point named by `a ∈ U` is the local dimension
`dim_a(U)`, and the supremum of the local dimensions is the dimension of `U` (Stacks 0B7I). -/
theorem dimension_schemeStack_eq_top (U : BigFppfOver B S hS)
    (hU : IsLocallyNoetherianStack.{u, w} B S hS (schemeStack.{u, w} B S hS U))
    (h : topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj U) = ⊤) :
    dimension B S hS (schemeStack.{u, w} B S hS U) hU = ⊤ := by
  have hsup : ⨆ a : (BigFppfOver.toScheme B S hS).obj U,
      topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U) a = ⊤ := by
    rw [← h, TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
    exact iSup_congr fun a => TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim _ a
  refine top_unique ((iSup_dimensionSubNat_zero_eq_top hsup).symm.le.trans (iSup_le fun a => ?_))
  refine le_trans (le_of_eq ?_) (le_iSup (fun t => dimensionAtPoint B S hS
    (schemeStack.{u, w} B S hS U) hU t)
    (representedChartPointMap B S hS U ((Space.pointsEquivScheme B S hS U).symm a)))
  rw [dimensionAtPoint_schemeStack_eq_dimensionSubNat B S hS U hU,
    Space.pointsToScheme_pointsEquivScheme_symm]

/-- The algebraic stack of a scheme of the site has a property of schemes as soon as the scheme
has it: the identity is a smooth surjective scheme atlas. -/
theorem hasPropertyOnSomeSchemeAtlas_schemeStack (U : BigFppfOver B S hS)
    (P : Scheme.{u} → Prop) (hP : P ((BigFppfOver.toScheme B S hS).obj U)) :
    HasPropertyOnSomeSchemeAtlas B S hS P (schemeStack.{u, w} B S hS U) :=
  ⟨U, 𝟙 _, isSurjective_id B S hS _, AlgebraicStacks.isSmooth_id B S hS _, hP⟩

/-- The point space of the algebraic stack of an irreducible scheme of the site is irreducible,
the two being homeomorphic (Stacks 04XL). -/
theorem irreducibleSpace_points_schemeStack (U : BigFppfOver B S hS)
    [IrreducibleSpace ((BigFppfOver.toScheme B S hS).obj U)] :
    @IrreducibleSpace _ (pointTopology B S hS (schemeStack.{u, w} B S hS U).val) := by
  let := pointTopology B S hS (schemeFibredCategory B S hS U)
  have h := (IrreducibleSpace.isIrreducible_univ ((BigFppfOver.toScheme B S hS).obj U)).image
    (pointsHomeomorphScheme B S hS U).symm
    (pointsHomeomorphScheme B S hS U).symm.continuous.continuousOn
  rw [Set.image_univ, (pointsHomeomorphScheme B S hS U).symm.surjective.range_eq] at h
  exact (irreducibleSpace_def _).2 h

end SchemeStack

/-! ### The affine line over `Spec R` -/

section AffineLine

variable (R : Type u) [CommRing R] (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of R)))

/-- The affine line `𝔸¹_R` over `Spec R`. -/
@[ega "IV 20.5.4" "special case"]
abbrev affineLineScheme : Scheme.{u} := 𝔸(ULift.{u} (Fin 1); Spec (.of R))

include hS in
/-- The affine line over a scheme of the site is in the site: it is the spectrum of a finitely
generated `R`-algebra (Stacks 000R (9)(b)). -/
theorem contains_affineLineScheme : B.Contains (affineLineScheme R) :=
  lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact
      (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of R)).hom)
    (Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit R
      (MvPolynomial (ULift.{u} (Fin 1)) R) hS)

/-- The affine line over `Spec R`, as an object of the big fppf site of `Spec R`. -/
abbrev affineLineObj : BigFppfOver B (Spec (.of R)) hS :=
  siteObject B (Spec (.of R)) hS (contains_affineLineScheme R B hS)
    (𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R))

/-- The projection of the affine line to the base, as a morphism of the site to its final
object. -/
abbrev affineLineProj :
    affineLineObj R B hS ⟶ (Over.mk (𝟙 (B.obj hS)) : BigFppfOver B (Spec (.of R)) hS) :=
  Over.homMk (affineLineObj R B hS).hom (Category.comp_id _)

/-- The morphism of schemes underlying the projection is the projection `𝔸¹_R ⟶ Spec R`. -/
theorem toScheme_map_affineLineProj :
    (BigFppfOver.toScheme B (Spec (.of R)) hS).map (affineLineProj R B hS) =
      𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R) :=
  rfl

/-- The projection `f : 𝔸¹_R ⟶ Spec R`, as a 1-morphism of algebraic stacks. -/
abbrev affineLineStackMap :
    schemeStack.{u, w} B (Spec (.of R)) hS (affineLineObj R B hS) ⟶
      schemeStack.{u, w} B (Spec (.of R)) hS (Over.mk (𝟙 (B.obj hS))) :=
  schemeStackMap.{u, w} B (Spec (.of R)) hS (affineLineProj R B hS)

/-- The projection `𝔸¹_R ⟶ Spec R` is locally of finite type. -/
theorem locallyOfFiniteType_affineLine :
    LocallyOfFiniteType (𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R)) :=
  inferInstance

/-- The projection `𝔸¹_R ⟶ Spec R` is locally of finite type, as a 1-morphism of algebraic
stacks (Stacks 06FS). -/
theorem isLocallyOfFiniteType_affineLineStackMap :
    AlgebraicStacks.IsLocallyOfFiniteType B (Spec (.of R)) hS (affineLineStackMap.{u, w} R B hS) :=
  isLocallyOfFiniteType_schemeFibredCategoryMap.{u, w} B (Spec (.of R)) hS
    (affineLineProj R B hS) (locallyOfFiniteType_affineLine R)

/-- The projection `𝔸¹_R ⟶ Spec R` is quasi-DM: its source is the algebraic stack of a scheme,
which is quasi-DM. -/
theorem isQuasiDM_affineLineStackMap :
    AlgebraicStacks.IsQuasiDM B (Spec (.of R)) hS (affineLineStackMap.{u, w} R B hS) :=
  isQuasiDM_of_isQuasiDMOver B (Spec (.of R)) hS _
    (isQuasiDMOver_of_isQuasiDMAbs B (Spec (.of R)) hS _
      (isQuasiDMAbs_schemeStack B (Spec (.of R)) hS _))

/-- The projection `𝔸¹_R ⟶ Spec R` is quasi-compact: it is the structure morphism of the
algebraic stack of the affine scheme `𝔸¹_R` over the affine, hence quasi-separated, base. -/
theorem isQuasiCompactMorphism_affineLineStackMap :
    IsQuasiCompactMorphism B (Spec (.of R)) hS (affineLineStackMap.{u, w} R B hS) := by
  rw [eq_structureMorphism B (Spec (.of R)) hS _ (affineLineStackMap.{u, w} R B hS)]
  exact isQuasiCompactMorphism_structureMorphism B (Spec (.of R)) hS inferInstance _
    (isQuasiCompactStack_schemeStack_of_compactSpace B (Spec (.of R)) hS _
      (inferInstanceAs (CompactSpace (affineLineScheme R))))

/-- The projection `𝔸¹_R ⟶ Spec R` is surjective on points. -/
theorem isSurjective_affineLineStackMap :
    IsSurjective B (Spec (.of R)) hS (affineLineStackMap.{u, w} R B hS) :=
  isSurjective_schemeStackMap.{u, w} B (Spec (.of R)) hS (affineLineProj R B hS)
    (show Surjective (𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R)) from inferInstance).1

/-- **The scheme theoretic image of `𝔸¹_R ⟶ Spec R` is all of `Spec R`**, for `R` reduced. The
whole of `Spec R` is a closed substack, the essential image of the identity, and a closed substack
through which the projection factors is surjective on points, the projection being surjective,
so it is everything by Stacks 050A, `Spec R` being reduced. -/
theorem isSchemeTheoreticImage_affineLineStackMap [IsReduced (Spec (.of R))] :
    IsSchemeTheoreticImage (affineLineStackMap.{u, w} R B hS) ⊤ := by
  set 𝒳 := schemeStack.{u, w} B (Spec (.of R)) hS (Over.mk (𝟙 (B.obj hS)))
  set f := affineLineStackMap.{u, w} R B hS
  have hclosed : IsClosedSubstack 𝒳 ⊤ := by
    have h := AlgebraicStacks.isClosedSubstack_essImage (𝟙 𝒳)
      (isThickening_id_schemeStack.{u, w} B (Spec (.of R)) hS _).1
    have hess : (CatFiberedInGroupoids.homFunctor (𝟙 𝒳 : 𝒳 ⟶ 𝒳).hom).essImage = ⊤ := by
      ext x
      exact iff_of_true ⟨x, ⟨Iso.refl _⟩⟩ trivial
    rwa [hess] at h
  have := hclosed.1
  refine ⟨hclosed, (factorsThroughSubstack_iff_forall _).2 fun _ => trivial,
    fun Q hQ hfac => ?_⟩
  have : Q.IsClosedUnderIsomorphisms := hQ.1
  have hA := hQ.2.choose
  have hall : ∀ X, Q (f.hom.hom.obj X) := (factorsThroughSubstack_iff_forall f).1 hfac
  have hsurj : IsSurjective B (Spec (.of R)) hS
      (fullSubcategoryInclusion 𝒳 Q hQ.2.choose) := by
    intro y
    obtain ⟨x, rfl⟩ := isSurjective_affineLineStackMap.{u, w} R B hS y
    refine ⟨AlgebraicStacks.pointsMap B (Spec (.of R)) hS
      (substackLift B (Spec (.of R)) hS f hQ.2.choose hall) x, ?_⟩
    rw [← Function.comp_apply (f := AlgebraicStacks.pointsMap B (Spec (.of R)) hS _),
      ← AlgebraicStacks.pointsMap_comp, substackLift_comp]
  have hred : IsReducedStack B (Spec (.of R)) hS 𝒳 :=
    hasPropertyOnSomeSchemeAtlas_schemeStack B (Spec (.of R)) hS (Over.mk (𝟙 (B.obj hS)))
      (fun X : Scheme.{u} => IsReduced X) (inferInstanceAs (IsReduced (Spec (.of R))))
  rw [eq_top_of_isClosedSubstack_of_isReducedStack B (Spec (.of R)) hS Q hQ hsurj hred]

/-- The affine line over `Spec R` has the dimension of `R[x]`, which is at least that of `R`. -/
theorem topologicalKrullDim_affineLineScheme_eq_top (hdim : ringKrullDim R = ⊤) :
    topologicalKrullDim (affineLineScheme R) = ⊤ := by
  refine (IsHomeomorph.topologicalKrullDim_eq _ (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso
    (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of R)))).isHomeomorph).trans ?_
  refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim
    (MvPolynomial (ULift.{u} (Fin 1)) R)).trans (top_unique ?_)
  rw [← hdim]
  exact ringKrullDim_le_of_surjective (MvPolynomial.constantCoeff (σ := ULift.{u} (Fin 1)) (R := R))
    fun r => ⟨MvPolynomial.C r, MvPolynomial.constantCoeff_C _ r⟩

/-- **Every fibre of `𝔸¹_R ⟶ Spec R` has dimension `1`**: the relative dimension of Stacks 0DRL
of the projection is `1` at every point, the projection having relative dimension `1` in the
sense of Stacks 02NJ. -/
theorem relativeStackDimensionAt_affineLineStackMap
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B (Spec (.of R)) hS
      (schemeStack.{u, w} B (Spec (.of R)) hS (affineLineObj R B hS)))
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B (Spec (.of R)) hS
      (schemeStack.{u, w} B (Spec (.of R)) hS (Over.mk (𝟙 (B.obj hS)))))
    (t : points B (Spec (.of R)) hS
      (schemeStack.{u, w} B (Spec (.of R)) hS (affineLineObj R B hS)).val.val
      (schemeStack.{u, w} B (Spec (.of R)) hS (affineLineObj R B hS)).val.property) :
    relativeStackDimensionAt.{u, w} B (Spec (.of R)) hS (affineLineStackMap.{u, w} R B hS)
      (isLocallyOfFiniteType_affineLineStackMap.{u, w} R B hS) h𝒯 h𝒳 t =
        (((1 : ℤ) : ℤ) : EInt) := by
  have : LocallyOfFiniteType
      ((BigFppfOver.toScheme B (Spec (.of R)) hS).map (affineLineProj R B hS)) :=
    locallyOfFiniteType_affineLine R
  refine forall_points_schemeStack B (Spec (.of R)) hS (affineLineObj R B hS)
    (Q := fun t => relativeStackDimensionAt.{u, w} B (Spec (.of R)) hS
      (affineLineStackMap.{u, w} R B hS)
      (isLocallyOfFiniteType_affineLineStackMap.{u, w} R B hS) h𝒯 h𝒳 t =
        (((1 : ℤ) : ℤ) : EInt)) (fun a => ?_) t
  rw [relativeStackDimensionAt_schemeStackMap_eq_dimensionSubNat B (Spec (.of R)) hS
      (affineLineProj R B hS) (isLocallyOfFiniteType_affineLineStackMap.{u, w} R B hS) h𝒯 h𝒳 a,
    RelativeDimension.topologicalKrullDimAt_fiber_eq
      ((BigFppfOver.toScheme B (Spec (.of R)) hS).map (affineLineProj R B hS)) (d := 1)
      (Stacks.Chow.relativeDimension_affineSpaceOver (Spec (.of R)) 1) _ _]
  rfl

end AffineLine

/-! ### The reduction -/

section Reduction

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsJacobsonRing R]
  (hUC : Ring.IsUniversallyCatenary R) (hdim : ringKrullDim R = ⊤)
  (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of R)))

include hUC hdim in
/-- **The exactly-one clause of Stacks 0DS6 fails for `𝔸¹_R ⟶ Spec R`** when `R` is a Noetherian,
Jacobson, universally catenary domain of infinite Krull dimension, for every big fppf site
containing `Spec R`.

The projection `f` is quasi-compact, locally of finite type and quasi-DM; `𝔸¹_R` and `Spec R` are
Jacobson, pseudo-catenary and locally Noetherian; `|𝔸¹_R|` is irreducible and `Spec R` is
quasi-separated; and the scheme theoretic image of `f` is all of `Spec R`. So every hypothesis
of Stacks 0DS6 holds. But every fibre has dimension `1`, so alternative (1) holds, and
`dim 𝔸¹_R = ∞`. The 0DS4 equality `dim 𝒯 = dim 𝒵 + dim_t(𝒯_{f(t)})` at a point of its locus then
reads `∞ = dim 𝒵 + 1`, so `dim 𝒵 = ∞` and alternative (2) holds too. -/
theorem exists_not_xor_relativeDimension_pos_of_ringKrullDim_eq_top :
    ∃ (𝒯 𝒳 : AlgebraicStacks.{u, w} B (Spec (.of R)) hS) (f : 𝒯 ⟶ 𝒳)
      (_hfQC : IsQuasiCompactMorphism B (Spec (.of R)) hS f)
      (hf : AlgebraicStacks.IsLocallyOfFiniteType B (Spec (.of R)) hS f)
      (_hDM : AlgebraicStacks.IsQuasiDM B (Spec (.of R)) hS f)
      (h𝒯 : IsLocallyNoetherianStack.{u, w} B (Spec (.of R)) hS 𝒯)
      (h𝒳 : IsLocallyNoetherianStack.{u, w} B (Spec (.of R)) hS 𝒳)
      (_h𝒯Jacobson : AlgebraicStacks.IsJacobson B (Spec (.of R)) hS 𝒯)
      (_h𝒳Jacobson : AlgebraicStacks.IsJacobson B (Spec (.of R)) hS 𝒳)
      (_h𝒯Catenary : AlgebraicStacks.IsPseudoCatenary B (Spec (.of R)) hS 𝒯)
      (_h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B (Spec (.of R)) hS 𝒳)
      (_h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B (Spec (.of R)) hS 𝒯.val))
      (_h𝒳QuasiSeparated : IsQuasiSeparatedAbs.{u, w, w} B (Spec (.of R)) hS 𝒳)
      (P : ObjectProperty 𝒳.val.val.obj) (hP : IsSchemeTheoreticImage f P),
      ¬ (Xor (∀ t, IsFiniteTypePoint.{u, w} B (Spec (.of R)) hS 𝒯 t →
            0 < relativeStackDimensionAt B (Spec (.of R)) hS f hf h𝒯 h𝒳 t)
          (dimension B (Spec (.of R)) hS 𝒯 h𝒯 =
            closedSubstackDimension B (Spec (.of R)) hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳) ∧
        ((∀ t, IsFiniteTypePoint.{u, w} B (Spec (.of R)) hS 𝒯 t →
            0 < relativeStackDimensionAt B (Spec (.of R)) hS f hf h𝒯 h𝒳 t) →
          closedSubstackDimension B (Spec (.of R)) hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳 <
            dimension B (Spec (.of R)) hS 𝒯 h𝒯)) := by
  have : IsLocallyNoetherian (affineLineScheme R) :=
    LocallyOfFiniteType.isLocallyNoetherian (𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R))
  have : JacobsonSpace (affineLineScheme R) :=
    LocallyOfFiniteType.jacobsonSpace (𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R))
  have : IrreducibleSpace (affineLineScheme R) := inferInstance
  set V := affineLineObj R B hS
  set X₀ : BigFppfOver B (Spec (.of R)) hS := Over.mk (𝟙 (B.obj hS))
  have h𝒯 : IsLocallyNoetherianStack.{u, w} B (Spec (.of R)) hS (schemeStack.{u, w} B _ hS V) :=
    hasPropertyOnSomeSchemeAtlas_schemeStack B _ hS V _
      (inferInstanceAs (IsLocallyNoetherian (affineLineScheme R)))
  have h𝒳 : IsLocallyNoetherianStack.{u, w} B (Spec (.of R)) hS (schemeStack.{u, w} B _ hS X₀) :=
    hasPropertyOnSomeSchemeAtlas_schemeStack B _ hS X₀ (fun X : Scheme.{u} => IsLocallyNoetherian X)
      (inferInstanceAs (IsLocallyNoetherian (Spec (.of R))))
  have hP := isSchemeTheoreticImage_affineLineStackMap.{u, w} R B hS
  have hf := isLocallyOfFiniteType_affineLineStackMap.{u, w} R B hS
  have hfQC := isQuasiCompactMorphism_affineLineStackMap.{u, w} R B hS
  have h𝒯J : AlgebraicStacks.IsJacobson B (Spec (.of R)) hS (schemeStack.{u, w} B _ hS V) :=
    hasPropertyOnSomeSchemeAtlas_schemeStack B _ hS V (fun X : Scheme.{u} => JacobsonSpace X)
      (inferInstanceAs (JacobsonSpace (affineLineScheme R)))
  have h𝒳J : AlgebraicStacks.IsJacobson B (Spec (.of R)) hS (schemeStack.{u, w} B _ hS X₀) :=
    hasPropertyOnSomeSchemeAtlas_schemeStack B _ hS X₀ (fun X : Scheme.{u} => JacobsonSpace X)
      (inferInstanceAs (JacobsonSpace (Spec (.of R))))
  have h𝒯C : AlgebraicStacks.IsPseudoCatenary B (Spec (.of R)) hS (schemeStack.{u, w} B _ hS V) :=
    hasPropertyOnSomeSchemeAtlas_schemeStack B _ hS V
      (fun X : Scheme.{u} => ∃ h : IsLocallyNoetherian X, @Scheme.IsUniversallyCatenary X h)
      ⟨_, Scheme.isUniversallyCatenary_of_locallyOfFiniteType_over_spec R hUC
        (𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R))⟩
  have h𝒳C : AlgebraicStacks.IsPseudoCatenary B (Spec (.of R)) hS (schemeStack.{u, w} B _ hS X₀) :=
    hasPropertyOnSomeSchemeAtlas_schemeStack B _ hS X₀
      (fun X : Scheme.{u} => ∃ h : IsLocallyNoetherian X, @Scheme.IsUniversallyCatenary X h)
      ⟨inferInstanceAs (IsLocallyNoetherian (Spec (.of R))),
        Scheme.isUniversallyCatenary_spec R hUC⟩
  have hIrr : @IrreducibleSpace _
      (pointTopology B (Spec (.of R)) hS (schemeStack.{u, w} B _ hS V).val) :=
    have : IrreducibleSpace ((BigFppfOver.toScheme B (Spec (.of R)) hS).obj V) :=
      inferInstanceAs (IrreducibleSpace (affineLineScheme R))
    irreducibleSpace_points_schemeStack.{u, w} B _ hS V
  have hQS : IsQuasiSeparatedAbs.{u, w, w} B (Spec (.of R)) hS (schemeStack.{u, w} B _ hS X₀) :=
    isQuasiSeparatedAbs_schemeStack_base.{u, w, w} B (Spec (.of R)) hS
  refine ⟨_, _, affineLineStackMap.{u, w} R B hS, hfQC, hf,
    isQuasiDM_affineLineStackMap.{u, w} R B hS, h𝒯, h𝒳, h𝒯J, h𝒳J, h𝒯C, h𝒳C, hIrr, hQS, ⊤, hP, ?_⟩
  have hrd := relativeStackDimensionAt_affineLineStackMap.{u, w} R B hS h𝒯 h𝒳
  have hT : dimension B (Spec (.of R)) hS (schemeStack.{u, w} B _ hS V) h𝒯 = ⊤ :=
    dimension_schemeStack_eq_top B _ hS V h𝒯 (topologicalKrullDim_affineLineScheme_eq_top R hdim)
  obtain ⟨-, W, -, ⟨t, ht⟩, -, hWeq⟩ :=
    dimension_le_add_and_exists_isOpen_dense_eq_add_relativeStackDimensionAt_of_isQuasiCompactMorphism.{u, w}
      B (Spec (.of R)) hS (affineLineStackMap.{u, w} R B hS) hf hfQC h𝒯 h𝒳 h𝒯J h𝒳J h𝒯C h𝒳C hIrr
      hQS hP
  have hZ : closedSubstackDimension B (Spec (.of R)) hS (schemeStack.{u, w} B _ hS X₀) ⊤ hP.1
      hP.isAlgebraicStack h𝒳 = ⊤ := by
    refine eq_top_of_add_one_eq_top ?_
    rw [← hrd t, ← hWeq t ht, hT]
  have hA : ∀ t, IsFiniteTypePoint.{u, w} B (Spec (.of R)) hS (schemeStack.{u, w} B _ hS V) t →
      0 < relativeStackDimensionAt B (Spec (.of R)) hS (affineLineStackMap.{u, w} R B hS) hf h𝒯
        h𝒳 t := fun t _ => by
    rw [hrd t, show (0 : EInt) = ((0 : ℤ) : EInt) from rfl, WithBotTop.coe_lt_coe]
    omega
  rintro ⟨hxor, -⟩
  rcases hxor with ⟨-, hne⟩ | ⟨-, hnA⟩
  · exact hne (hT.trans hZ.symm)
  · exact hnA hA

end Reduction

/-! ### The counterexample -/

/-- **Stacks 0DS6 is false as written, without a finiteness hypothesis on `dim 𝒯`.** It is not
the case that for every quasi-compact, locally of finite type, quasi-DM 1-morphism `f : 𝒯 ⟶ 𝒳` of
Jacobson, pseudo-catenary, locally Noetherian algebraic stacks with `|𝒯|` irreducible and `𝒳`
quasi-separated, with scheme theoretic image `𝒵`, exactly one of (1)
`dim_t(𝒯_{f(t)}) > 0` at every finite type point `t` and (2) `dim 𝒯 = dim 𝒵` holds, (1) forcing
`dim 𝒵 < dim 𝒯`.

The counterexample is `f : 𝔸¹_D ⟶ Spec D` for `D = N⟨X⟩`, the localization at the monic
polynomials of the polynomial ring over Nagata's ring `N` of infinite dimension (Stacks 02JC),
over a big fppf site containing `Spec D`. `D` is a Noetherian domain of infinite Krull dimension
and universally catenary (`NagataRing.ringKrullDim_monicLocalization_eq_top`,
`NagataRing.isUniversallyCatenary_monicLocalization`), and Jacobson by the theorem of Brewer and
Heinzer, *R Noetherian implies R⟨X⟩ is a Hilbert ring*, J. Algebra 67 (1980)
(`Polynomial.isJacobsonRing_monicLocalization`). The failure is
`AlgebraicGeometry.Stack.exists_not_xor_relativeDimension_pos_of_ringKrullDim_eq_top`. -/
theorem not_forall_xor_relativeDimension_pos :
    ¬ ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
        (𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒯 ⟶ 𝒳)
        (_hfQC : IsQuasiCompactMorphism B S hS f)
        (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
        (_hDM : AlgebraicStacks.IsQuasiDM B S hS f)
        (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
        (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
        (_h𝒯Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒯)
        (_h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
        (_h𝒯Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒯)
        (_h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
        (_h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
        (_h𝒳QuasiSeparated : IsQuasiSeparatedAbs.{u, w, w} B S hS 𝒳)
        (P : ObjectProperty 𝒳.val.val.obj) (hP : IsSchemeTheoreticImage f P),
      Xor (∀ t, IsFiniteTypePoint.{u, w} B S hS 𝒯 t →
            0 < relativeStackDimensionAt B S hS f hf h𝒯 h𝒳 t)
          (dimension B S hS 𝒯 h𝒯 =
            closedSubstackDimension B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳) ∧
        ((∀ t, IsFiniteTypePoint.{u, w} B S hS 𝒯 t →
            0 < relativeStackDimensionAt B S hS f hf h𝒯 h𝒳 t) →
          closedSubstackDimension B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳 <
            dimension B S hS 𝒯 h𝒯) := by
  intro h
  let D := Polynomial.MonicLocalization (NagataRing (ULift.{u} ℚ))
  obtain ⟨B, hS⟩ := BigFppfSite.exists_contains (Spec (.of D))
  obtain ⟨𝒯, 𝒳, f, hfQC, hf, hDM, h𝒯, h𝒳, h𝒯J, h𝒳J, h𝒯C, h𝒳C, hIrr, hQS, P, hP, hnot⟩ :=
    exists_not_xor_relativeDimension_pos_of_ringKrullDim_eq_top.{u, w} D
      (NagataRing.isUniversallyCatenary_monicLocalization (ULift.{u} ℚ))
      (NagataRing.ringKrullDim_monicLocalization_eq_top (ULift.{u} ℚ)) B hS
  exact hnot (h B _ hS 𝒯 𝒳 f hfQC hf hDM h𝒯 h𝒳 h𝒯J h𝒳J h𝒯C h𝒳C hIrr hQS P hP)

end AlgebraicGeometry.Stack

end
