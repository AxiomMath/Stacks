module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectTensorSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.UniformChartCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.ChartSliceTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSupportInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.IntervalDescent

/-!
# `E ⊗^L 𝒢` is bounded, for `E` perfect and `𝒢` bounded with support in a compact set

Let `X` be an algebraic space, `E` a perfect object of `D(𝒪_X)` and `𝒢` a bounded complex of
`𝒪_X`-modules all of whose terms have support in a closed compact subset `T ⊆ |X|`.  Then
`E ⊗^L_{𝒪_X} 𝒢` has only finitely many nonzero cohomology sheaves.  This is the boundedness
clause of the proof of Stacks 0DKJ.

## Main results

* `AlgebraicGeometry.Space.isZero_over_of_forall_notMem_supportOfSheaf`: a module restricts to
  zero on an étale chart all of whose points lie outside its support.
* `AlgebraicGeometry.Space.exists_coversTop_uniform_tensor_models`: a family covering the final
  object each member of which either carries a local model `Tot(P ⊗ 𝒢|_W)` of `E ⊗^L 𝒢` with `P`
  strictly perfect in a fixed range of degrees, or has all its points outside `T`.
* `AlgebraicGeometry.Space.exists_isZero_homology_derivedTensor_of_isPerfect`: the boundedness
  clause.

## References

* [Stacks Project, Tag 0DKJ](https://stacks.math.columbia.edu/tag/0DKJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] smallEtaleRingedSite_essentiallySmall
  Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective pointTopology

open Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall
  (restrictTensorComplex restrictDerivedTensorIsoOfModel exists_model_of_map
    isZero_restrict_homology_of_model)
open Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall (restriction restrictionComplex)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The derived category of the modules on a slice of the small étale site, for the abelian
structure `AlgebraicGeometry.Space.smallEtaleRingedSite_over_abelian`. -/
local instance (priority := 20000) sliceHasDerivedCategory
    (U : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    HasDerivedCategory.{u + 1}
      (RingedSite.Modules.{u + 1, u, u} ((smallEtaleRingedSite B S hS X.1 X.2).over U)) :=
  @HasDerivedCategory.standard _ _ (smallEtaleRingedSite_over_abelian B S hS X.1 X.2 U)

/-- A module restricts to zero on an étale chart all of whose points lie outside its support. -/
theorem isZero_over_of_forall_notMem_supportOfSheaf (M : Modules.{u, u} B S hS X.1 X.2)
    (W : SmallEtale B S hS X.1)
    (h : ∀ z : chartScheme W, chartSchemeToPoints B S hS X.1 W z ∉
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M)) :
    IsZero ((SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X) W).obj M) := by
  have hP : supportOfSheaf B S hS (chartSpace B S hS X W).1
      ((SheafOfModules.toSheaf _).obj ((etaleModulePullback B S hS
        (chartToSpace B S hS X W) (isEtale_chartToSpace B S hS X W)).obj M)) = ∅ := by
    rw [supportOfSheaf_chartToSpace]
    refine Set.eq_empty_of_forall_notMem fun p hp => ?_
    refine h (pointsToScheme B S hS ((SmallEtale.toOver B S hS X.1).obj W) p) ?_
    rwa [chartSchemeToPoints_eq B S hS X W p]
  have hz := (supportOfSheaf_eq_empty_iff_isZero B S hS (chartSpace B S hS X W) _).1 hP
  exact (Functor.map_isZero (chartModuleSliceEquiv B S hS X W).inverse hz).of_iso
    ((chartSliceOverIso B S hS X W).app M)

/-- A strictly perfect complex vanishes outside a bounded interval. -/
theorem exists_bound_of_isStrictlyPerfect (W : SmallEtale B S hS X.1)
    (P : CochainComplex (SheafOfModules.{u} ((structureRingSheaf B S hS X).over W)) ℤ)
    (hP : IsStrictlyPerfect ((structureRingSheaf B S hS X).over W) P) :
    ∃ N : ℕ, ∀ n : ℤ, n < -N ∨ (N : ℤ) < n → IsZero (P.X n) := by
  classical
  have hs : {p : ℤ | ¬ IsZero (P.X p)}.Finite := hP.bounded
  obtain ⟨a, ha⟩ := hs.bddBelow
  obtain ⟨b, hb⟩ := hs.bddAbove
  refine ⟨a.natAbs + b.natAbs, fun n hn => ?_⟩
  by_contra hz
  have := ha hz
  have := hb hz
  omega

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck in
/-- **Local models of `E ⊗^L 𝒢` in a uniform range of degrees near a compact set.**  For `E`
perfect and `Z ⊆ |X|` compact and closed there are an integer `N` and a family of objects covering
the final object of the small étale site, each member `W` of which either carries a strictly
perfect complex `P`, zero outside `[-N, N]`, with `(E ⊗^L 𝒢)|_W ≅ Q(Tot(P ⊗ 𝒢|_W))`, or has all its
points outside `Z`. -/
theorem exists_coversTop_uniform_tensor_models
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, u + 1}
      (smallEtaleRingedSite B S hS X.1 X.2))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E)
    (G : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (Z : Set (points B S hS X.1))
    (hZc : IsCompact Z) (hZcl : IsClosed Z) :
    ∃ (N : ℕ) (I : Type (u + 1)) (W : I → (smallEtaleRingedSite B S hS X.1 X.2).C),
      (smallEtaleRingedSite B S hS X.1 X.2).J.CoversTop W ∧ ∀ i,
        (∃ P : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O).over (W i))) ℤ,
          IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O).over (W i)) P ∧
          (∀ n : ℤ, n < -N ∨ (N : ℤ) < n → IsZero (P.X n)) ∧
          Nonempty ((RingedSite.derivedRestriction.{u + 1, u, u, u + 1}
              (smallEtaleRingedSite B S hS X.1 X.2) (W i)).obj
                ((T.tensor.obj E).obj (DerivedCategory.Q.obj G)) ≅
            DerivedCategory.Q.obj
              (restrictTensorComplex (smallEtaleRingedSite B S hS X.1 X.2) (W i) P G))) ∨
        ∀ z : chartScheme (W i), chartSchemeToPoints B S hS X.1 (W i) z ∉ Z := by
  classical
  let Xs := smallEtaleRingedSite B S hS X.1 X.2
  obtain ⟨E', hE', ⟨eE⟩⟩ := hE
  obtain ⟨K, V, hV, hmod⟩ := Xs.exists_coversTop_isStrictlyPerfect_of_isPerfectComplex E' hE'
  choose P hP q hq using hmod
  choose Nk hNk using fun k => exists_bound_of_isStrictlyPerfect B S hS X (V k) (P k) (hP k)
  obtain ⟨F, I, W, hW, hkind⟩ := exists_coversTop_finite_near B S hS X hV Z hZc hZcl
  refine ⟨F.sup Nk, I, W, hW, fun i => ?_⟩
  let Wi : (smallEtaleRingedSite B S hS X.1 X.2).C := W i
  rcases hkind i with ⟨k, hk, ⟨g⟩⟩ | hout
  · obtain ⟨P', hP', hz, q', hq'⟩ := exists_model_of_map Xs E' g (P k) (hP k) (q k) (hq k)
    have hle : Nk k ≤ F.sup Nk := Finset.le_sup hk
    refine Or.inl ⟨P', hP', fun n hn => hz n (hNk k n (by omega)),
      ⟨restrictDerivedTensorIsoOfModel Xs T E E' eE Wi P' hP' q' hq' G⟩⟩
  · exact Or.inr hout

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck in
/-- **The boundedness clause of Stacks 0DKJ.**  For `E` perfect and `𝒢` a bounded complex all of
whose terms have support in a compact closed set, `E ⊗^L_{𝒪_X} 𝒢` has only finitely many nonzero
cohomology sheaves. -/
theorem exists_isZero_homology_derivedTensor_of_isPerfect
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, u + 1}
      (smallEtaleRingedSite B S hS X.1 X.2))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E)
    (G : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (g₀ g₁ : ℤ)
    (hGb : ∀ q : ℤ, q < g₀ ∨ g₁ < q → IsZero (G.X q)) (Z : Set (points B S hS X.1))
    (hZc : IsCompact Z) (hZcl : IsClosed Z)
    (hGZ : ∀ q : ℤ, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (G.X q)) ⊆ Z) :
    ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n →
      IsZero ((DerivedCategory.homologyFunctor _ n).obj
        ((T.tensor.obj E).obj (DerivedCategory.Q.obj G))) := by
  obtain ⟨N, I, W, hW, hmodel⟩ :=
    exists_coversTop_uniform_tensor_models B S hS X T E hE G Z hZc hZcl
  refine ⟨-N + g₀, N + g₁, fun n hn => ?_⟩
  refine Stacks.SheafOfModules.isZero_of_coversTop hW _ fun i => ?_
  rcases hmodel i with ⟨P, -, hPz, ⟨e⟩⟩ | hout
  · exact isZero_restrict_homology_of_model (smallEtaleRingedSite B S hS X.1 X.2) (W i) _ P G e
      (-N) N g₀ g₁ hPz hGb n hn
  · refine isZero_over_of_forall_notMem_supportOfSheaf B S hS X _ (W i) fun z hz => hout z ?_
    exact cohomologySupportedOn_derivedTensor B S hS X T E G Z hGZ n hz

end AlgebraicGeometry.Space

end
