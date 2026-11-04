module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CurveBridges
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.FieldFibreCondition
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension

/-!
# Condition (2)(c) of Stacks 0B9Q for `Pic⁰` of a curve, from Stacks 0B9Y

Condition (2)(c) of the group-scheme criterion ([Stacks, Tag 0B9Q]) asks that every field-valued
point of `Pic⁰_{X/k,σ}` be moved into the chart by a `k`-rational point. The proof of
[Stacks, Tag 0B9Z] obtains it from [Stacks, Tag 0B9Y]: for a degree-zero class `c` on `X_K` there
is a degree-zero class `c₀` on `X` such that `c + c₀ + θ` has `H⁰ = K` and `H¹ = 0`, and then
`Rf_{K,*}` of it is invertible in degree `0`. This file is that deduction; [Stacks, Tag 0B9Y] in
the form used is the hypothesis `h0B9Y`.

## Main results

* `Stacks.RigidifiedPicard.exists_translate_mem_cohomologySubfunctorZero` — condition (2)(c).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

universe u

namespace Stacks.RigidifiedPicard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Flat f]
  [LocallyOfFinitePresentation f] [IsProper f] [SmoothOfRelativeDimension 1 f]
  [LocallyOfFiniteType f] (hdimX : topologicalKrullDim X ≤ 1)
  (hdim : ∀ s : Spec (.of k), topologicalKrullDim ↥(f.fiber s) ≤ 1)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _)

/-- The Picard class of `X_T` of an element of `Pic⁰_{X/k,σ}(T)`. -/
def classOfZero {T : Over (Spec (.of k))}
    (x : (functorZero f hdim σ hσ ⋙ forget GrpCat).obj (op T)) : Stacks.Picard.ofScheme (bc f T) :=
  smallEquiv _ ((((Multiplicative.toAdd x : groupZero f hdim σ hσ T) : group f σ hσ T)) :
    Stacks.Picard.smallOfScheme (bc f T))

omit [Flat f] [LocallyOfFinitePresentation f] [SmoothOfRelativeDimension 1 f] in
/-- `classOfZero` commutes with pullback along a morphism `T' ⟶ T`. -/
theorem classOfZero_map {T T' : Over (Spec (.of k))} (g : T' ⟶ T)
    (x : (functorZero f hdim σ hσ ⋙ forget GrpCat).obj (op T)) :
    classOfZero f hdim σ hσ ((functorZero f hdim σ hσ ⋙ forget GrpCat).map g.op x) =
      Stacks.Picard.schemePullbackClass (bcMap f g) (classOfZero f hdim σ hσ x) :=
  functorZero_map_val f hdim σ hσ g x

omit [Flat f] [LocallyOfFinitePresentation f] [SmoothOfRelativeDimension 1 f] in
/-- `classOfZero` commutes with pullback along a morphism `T' ⟶ T`, stated for the group
homomorphism `(functorZero f hdim σ hσ).map g.op`. -/
theorem classOfZero_map' {T T' : Over (Spec (.of k))} (g : T' ⟶ T)
    (x : (functorZero f hdim σ hσ ⋙ forget GrpCat).obj (op T)) :
    classOfZero f hdim σ hσ (ConcreteCategory.hom ((functorZero f hdim σ hσ).map g.op) x) =
      Stacks.Picard.schemePullbackClass (bcMap f g) (classOfZero f hdim σ hσ x) :=
  functorZero_map_val f hdim σ hσ g x

omit [Flat f] [LocallyOfFinitePresentation f] [SmoothOfRelativeDimension 1 f] in
/-- `classOfZero` sends the product in `Pic⁰_{X/k,σ}(T)` to the sum of Picard classes. -/
theorem classOfZero_mul {T : Over (Spec (.of k))}
    (x y : (functorZero f hdim σ hσ ⋙ forget GrpCat).obj (op T)) :
    classOfZero f hdim σ hσ (x * y) = classOfZero f hdim σ hσ x + classOfZero f hdim σ hσ y :=
  map_add (smallEquiv (bc f T)) _ _

omit [Flat f] [LocallyOfFinitePresentation f] [SmoothOfRelativeDimension 1 f] in
/-- The Picard class of the element `mkZero f hdim σ hσ c hc hdeg` is `c`. -/
theorem classOfZero_mkZero {T : Over (Spec (.of k))} (c : Stacks.Picard.ofScheme (bc f T))
    (hc : Stacks.Picard.schemePullbackClass (bcSection f σ hσ T) c = 0)
    (hdeg : ∀ t : T.left, relativeInvertibleDegreeHomAt (bcProj f T)
      (topologicalKrullDim_fiber_bcProj_le f hdim T) t c = 0) :
    classOfZero f hdim σ hσ (mkZero f hdim σ hσ c hc hdeg) = c :=
  smallEquiv_mkZero f hdim σ hσ c hc hdeg

omit [Flat f] [LocallyOfFinitePresentation f] [SmoothOfRelativeDimension 1 f] in
/-- The Picard class of an element of `Pic⁰_{X/k,σ}(T)` has degree zero on the fibre over every
point `t` of `T`. -/
theorem relativeInvertibleDegreeHomAt_classOfZero {T : Over (Spec (.of k))}
    (x : (functorZero f hdim σ hσ ⋙ forget GrpCat).obj (op T)) (t : T.left) :
    relativeInvertibleDegreeHomAt (bcProj f T) (topologicalKrullDim_fiber_bcProj_le f hdim T) t
      (classOfZero f hdim σ hσ x) = 0 := by
  have h := (mem_groupZero_iff f hdim σ hσ T _).1 (Multiplicative.toAdd x).2 t
  rwa [degree_apply] at h

omit [SmoothOfRelativeDimension 1 f] in
/-- An element of `Pic⁰_{X/k,σ}(T)` lies in `cohomologySubfunctorZero` if and only if its Picard
class satisfies `IsCohomologyClass f θ T`. -/
theorem mem_cohomologySubfunctorZero_iff (h0B91 : PerfectDerivedPushforward.{u})
    (hbc : BaseChangeDerivedPushforward.{u}) (θ : Stacks.Picard.ofScheme X)
    {T : Over (Spec (.of k))} (x : (functorZero f hdim σ hσ ⋙ forget GrpCat).obj (op T)) :
    x ∈ (cohomologySubfunctorZero f hdim σ hσ h0B91 hbc θ).obj (op T) ↔
      IsCohomologyClass f θ T (classOfZero f hdim σ hσ x) :=
  Iff.rfl

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] [SmoothOfRelativeDimension 1 f] in
include hdimX in
/-- The base change of `X` to a field extension has dimension at most one. -/
theorem topologicalKrullDim_bc_fieldExtensionPoint_le (K : Type u) [Field K] [Algebra k K] :
    topologicalKrullDim ↥(bc f (fieldExtensionPoint k K)) ≤ 1 :=
  (topologicalKrullDim_baseChange k K _ _ f (IsPullback.of_hasPullback f _)).le.trans hdimX

omit [SmoothOfRelativeDimension 1 f] in
include hdimX in
/-- **Condition (2)(c) of [Stacks, Tag 0B9Q] for `Pic⁰_{X/k,σ}`, from [Stacks, Tag 0B9Y].** -/
theorem exists_translate_mem_cohomologySubfunctorZero (θ : Stacks.Picard.ofScheme X)
    (h0B9Y : ∀ (K : Type u) [Field K] [Algebra k K]
      (c : Stacks.Picard.ofScheme (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))),
      invertibleCurveDegreeHom K (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (topologicalKrullDim_bc_fieldExtensionPoint_le f hdimX K) c = 0 →
      ∃ c₀ : Stacks.Picard.ofScheme X, invertibleCurveDegreeHom k f hdimX c₀ = 0 ∧
        Module.finrank K (cohomologyOverField K
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Stacks.Picard.picardRepresentative _ (c +
            Stacks.Picard.schemePullbackClass
              (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) c₀ +
            Stacks.Picard.schemePullbackClass
              (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) θ)).obj 0) = 1 ∧
        IsZero (cohomologyOverField K
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Stacks.Picard.picardRepresentative _ (c +
            Stacks.Picard.schemePullbackClass
              (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) c₀ +
            Stacks.Picard.schemePullbackClass
              (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) θ)).obj 1))
    (K : Type u) [Field K] [Algebra k K]
    (x : (functorZero f hdim σ hσ ⋙ forget GrpCat).obj (op (fieldExtensionPoint k K))) :
    ∃ r : (functorZero f hdim σ hσ ⋙ forget GrpCat).obj (op (Over.mk (𝟙 (Spec (.of k))))),
      (functorZero f hdim σ hσ).map (Over.homMk (fieldExtensionPoint k K).hom).op r * x ∈
        (cohomologySubfunctorZero f hdim σ hσ
          (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward)
          baseChangeDerivedPushforward θ).obj (op (fieldExtensionPoint k K)) := by
  have hcdeg : invertibleCurveDegreeHom K (bcProj f (fieldExtensionPoint k K))
      (topologicalKrullDim_bc_fieldExtensionPoint_le f hdimX K)
        (classOfZero f hdim σ hσ x) = 0 := by
    have hpt : Nonempty (fieldExtensionPoint k K).left := by
      show Nonempty (PrimeSpectrum K); infer_instance
    obtain ⟨pt⟩ := hpt
    rw [← relativeInvertibleDegreeHomAt_spec (bcProj f (fieldExtensionPoint k K))
      (topologicalKrullDim_bc_fieldExtensionPoint_le f hdimX K)
      (topologicalKrullDim_fiber_bcProj_le f hdim (fieldExtensionPoint k K)) pt]
    exact relativeInvertibleDegreeHomAt_classOfZero f hdim σ hσ x pt
  set c := classOfZero f hdim σ hσ x with hcdef
  obtain ⟨c₀, hc₀deg, h0, h1⟩ := h0B9Y K c hcdeg
  have hr₀deg : ∀ t : (Over.mk (𝟙 (Spec (.of k)))).left,
      relativeInvertibleDegreeHomAt (bcProj f (Over.mk (𝟙 (Spec (.of k)))))
      (topologicalKrullDim_fiber_bcProj_le f hdim (Over.mk (𝟙 (Spec (.of k))))) t
        (normalize f σ hσ (Over.mk (𝟙 (Spec (.of k)))) (Stacks.Picard.schemePullbackClass
          (pullback.fst f (Over.mk (𝟙 (Spec (.of k)))).hom) c₀)) = 0 := by
    intro t
    rw [normalize, map_sub, relativeInvertibleDegreeHomAt_bcProj f hdim _ t,
      relativeInvertibleDegreeHomAt_fst f hdim c₀ _ t,
      relativeInvertibleDegreeHomAt_spec f hdimX hdim, hc₀deg, sub_zero]
  let r := mkZero f hdim σ hσ _ (schemePullbackClass_bcSection_normalize f σ hσ _ _) hr₀deg
  refine ⟨r, ?_⟩
  have hT0 : ∀ n : Stacks.Picard.ofScheme (fieldExtensionPoint k K).left, n = 0 :=
    Stacks.Picard.eq_zero_of_isField K
  rw [mem_cohomologySubfunctorZero_iff, classOfZero_mul, classOfZero_map', classOfZero_mkZero,
    ← hcdef, normalize_bcMap, Stacks.Picard.schemePullbackClass_comp, bcMap_fst,
    normalize_eq_self f σ hσ _ _ (hT0 _), isCohomologyClass_iff,
    add_comm (Stacks.Picard.schemePullbackClass _ c₀) c]
  have hfpT : FinitePresentation (bcProj f (fieldExtensionPoint k K)) :=
    finitePresentation_bcProj f (fieldExtensionPoint k K)
  obtain ⟨hF, hflat⟩ :=
    isFinitePresentation_and_isFlatOver_of_isInvertible (bcProj f (fieldExtensionPoint k K)) _
      (Stacks.Picard.picardRepresentative (bc f (fieldExtensionPoint k K)).toRingedSpace
        (c + Stacks.Picard.schemePullbackClass (pullback.fst f (fieldExtensionPoint k K).hom) c₀ +
          Stacks.Picard.schemePullbackClass (pullback.fst f (fieldExtensionPoint k K).hom)
            θ)).property
  have hfinrank : ∀ {M : ModuleCat K}, IsZero M → Module.finrank K M = 0 := fun h => by
    have := ModuleCat.subsingleton_of_isZero h
    exact Module.finrank_zero_of_subsingleton
  refine hasDerivedPushforwardRank_of_finrank K (bcProj f (fieldExtensionPoint k K)) hfpT _ hF
    hflat 0 1 h0 fun j hj => ?_
  rcases j with _ | _ | j
  · exact absurd rfl hj
  · exact hfinrank h1
  · exact hfinrank
      (isZero_cohomologyOverField_of_topologicalKrullDim_le K (bcProj f (fieldExtensionPoint k K))
        (Stacks.Picard.picardRepresentative (bc f (fieldExtensionPoint k K)).toRingedSpace
          (c + Stacks.Picard.schemePullbackClass (pullback.fst f (fieldExtensionPoint k K).hom) c₀ +
            Stacks.Picard.schemePullbackClass (pullback.fst f (fieldExtensionPoint k K).hom)
              θ)).obj (d := 1)
        (by exact_mod_cast topologicalKrullDim_bc_fieldExtensionPoint_le f hdimX K)
        (by omega : 1 < j + 2))

end Stacks.RigidifiedPicard

end
