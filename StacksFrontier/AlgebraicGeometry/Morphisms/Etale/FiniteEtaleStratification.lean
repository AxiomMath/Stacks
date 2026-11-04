module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.Topology.Constructible
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.DegreeStratification
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.Separated
public import StacksFrontier.Topology.Stratification.Partition
import StacksFrontier.AlgebraicGeometry.Properties.DimensionZero

/-!
# Finite étale stratification of an étale morphism

Let `f : U ⟶ X` be an étale morphism of quasi-compact and quasi-separated schemes. Then `X` is
partitioned into constructible locally closed subschemes over each of which `f` becomes finite
étale.

For a *separated* `f` this is the stratification of the target by the degree of the fibres,
[Stacks Project, Tag 07RZ]: the morphism is flat, locally of finite presentation and locally
quasi-finite, so the locus where the fibre degree is `r` is the difference of two closed subsets
and carries an immersed subscheme whose inclusion is quasi-compact; the base change to it is
finite locally free of degree `r`, hence finite. Quasi-compactness of the source bounds the
fibre degrees, [Stacks Project, Tag 03JA], so only finitely many strata are nonempty and the
complement of each step of the filtration is retrocompact — which is what makes the strata
constructible and not merely locally closed.

In general `f` is covered by finitely many affine opens, each separated over `X`, and the
separated case applies to every pairwise intersection of the members of that cover. Passing to
the common refinement of the resulting partitions gives a partition over whose strata all those
pairwise intersections become finite. Over such a stratum the base change of `f` is separated,
by the affine-intersection criterion [Stacks Project, Tag 01KP], and universally closed, so being
also locally quasi-finite it is finite.

## Main results

* `AlgebraicGeometry.exists_constructible_partition_finite_etale`: a partition of `X` into
  constructible locally closed strata over each of which `f` is finite étale.

## Implementation notes

A stratum is recorded by an immersion into `X` with the prescribed image, rather than as a
subset alone, so that the base change of `f` to it is a morphism of schemes. The partition is a
`Set (Set X)` satisfying `IsTopologicalPartition`, whose covering clause is the statement that
every point of `X` lies in exactly one part.

## References

* [Stacks Project, Tag 03S0](https://stacks.math.columbia.edu/tag/03S0)
* [Stacks Project, Tag 07RZ](https://stacks.math.columbia.edu/tag/07RZ)
* [Stacks Project, Tag 03JA](https://stacks.math.columbia.edu/tag/03JA)
* [Stacks Project, Tag 01KP](https://stacks.math.columbia.edu/tag/01KP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### The separated case -/

/-- The image of a quasi-compact immersion is retrocompact. -/
private lemma isRetrocompact_range_of_isImmersion_of_quasiCompact {T S : Scheme.{u}}
    (i : T ⟶ S) [IsImmersion i] [QuasiCompact i] : IsRetrocompact (Set.range i.base) := by
  intro K hKcompact hKopen
  have hpre : IsCompact (i.base ⁻¹' K) :=
    (Scheme.Hom.isSpectralMap i).isCompact_preimage_of_isOpen hKopen hKcompact
  have himg : IsCompact (i.base '' (i.base ⁻¹' K)) := hpre.image i.continuous
  rwa [Set.image_preimage_eq_inter_range, Set.inter_comm] at himg

/-- The case of a separated `f`: the strata are the loci of constant fibre degree,
[Stacks Project, Tag 07RZ]. -/
private theorem exists_constructible_partition_finite_etale_of_isSeparated
    {U X : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U]
    [CompactSpace X] [QuasiSeparatedSpace X] (f : U ⟶ X) [Etale f] [IsSeparated f] :
    ∃ P : Set (Set X), IsTopologicalPartition P ∧
      (∀ S ∈ P, Topology.IsConstructible S) ∧
      (∀ S ∈ P, ∃ (Y : Scheme.{u}) (i : Y ⟶ X),
        IsImmersion i ∧ Set.range i.base = S ∧
          IsFinite (pullback.fst i f) ∧ Etale (pullback.fst i f)) := by
  classical
  obtain ⟨_, _⟩ := locallyQuasiFinite_of_etale f
  obtain ⟨N, hN⟩ := hasUniversallyBoundedFibers_of_locallyQuasiFinite f
  obtain ⟨Z, Y, i, hZclosed, hZ0, hZstep, hZunion, himm, hqc, hrange, huniv⟩ :=
    exists_quasiCompact_stratification_of_finiteLocallyFree_rank f
  have hZmono : Monotone Z := monotone_nat_of_le_succ hZstep
  have hmem : ∀ (x : X) (r : ℕ),
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank (f.fiberToSpecResidueField x) r ↔
        x ∈ Z (r + 1) \ Z r := by
    intro x r
    have h := huniv r (Spec (X.residueField x)) (X.fromSpecResidueField x)
    rwa [show Set.range (X.fromSpecResidueField x).base = {x} from
      X.range_fromSpecResidueField x, Set.singleton_subset_iff] at h
  have hcov : ∀ x : X, ∃ r : ℕ, r ≤ N.toNat ∧ x ∈ Z (r + 1) \ Z r := by
    intro x
    obtain ⟨r, hle, hrank⟩ := hN x
    exact ⟨r, by omega, (hmem x r).mp hrank⟩
  have hdisj : ∀ {r r' : ℕ} {x : X}, x ∈ Z (r + 1) \ Z r → x ∈ Z (r' + 1) \ Z r' → r = r' := by
    intro r r' x hx hx'
    by_contra hne
    rcases Nat.lt_or_ge r r' with h | h
    · exact hx'.2 (hZmono (by omega) hx.1)
    · exact hx.2 (hZmono (by omega : r' + 1 ≤ r) hx'.1)
  have hretro : ∀ r : ℕ, IsRetrocompact (Z (r + 1) \ Z r) := by
    intro r
    have := himm r
    have := hqc r
    rw [← hrange r]
    exact isRetrocompact_range_of_isImmersion_of_quasiCompact (i r)
  have hcompl : ∀ k : ℕ, (Z k)ᶜ = ⋃ r ∈ Set.Ico k (N.toNat + 1), (Z (r + 1) \ Z r) := by
    intro k
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_Ico, exists_prop]
    constructor
    · intro hx
      obtain ⟨r, hrn, hxr⟩ := hcov x
      refine ⟨r, ⟨?_, by omega⟩, hxr⟩
      by_contra hlt
      exact hx (hZmono (by omega) hxr.1)
    · rintro ⟨r, ⟨hkr, -⟩, hxr⟩
      exact fun hxk => hxr.2 (hZmono hkr hxk)
  have hconstrZ : ∀ k : ℕ, Topology.IsConstructible (Z k) := by
    intro k
    refine Topology.IsConstructible.of_compl ?_
    refine IsRetrocompact.isConstructible (hZclosed k).isOpen_compl ?_
    rw [hcompl k]
    exact IsRetrocompact.biUnion (Set.finite_Ico k (N.toNat + 1)) fun r _ => hretro r
  refine ⟨{S | ∃ r : ℕ, S = Z (r + 1) \ Z r ∧ S.Nonempty}, ⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · rintro ⟨r, -, hne⟩
    exact Set.not_nonempty_empty hne
  · intro x
    obtain ⟨r, -, hxr⟩ := hcov x
    refine ⟨Z (r + 1) \ Z r, ⟨⟨r, rfl, ⟨x, hxr⟩⟩, hxr⟩, ?_⟩
    rintro S ⟨⟨r', rfl, -⟩, hxs⟩
    rw [hdisj hxs hxr]
  · rintro S ⟨r, rfl, -⟩
    have := himm r
    rw [← hrange r]
    exact (i r).isLocallyClosed_range
  · rintro S ⟨r, rfl, -⟩
    exact (hconstrZ (r + 1)).sdiff (hconstrZ r)
  · rintro S ⟨r, rfl, -⟩
    have h₁ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.fst (i r) f) r :=
      (rank_pullback_symmetry f (i r) r).mpr ((huniv r (Y r) (i r)).mpr (hrange r).le)
    have hlf : Stacks.Morphisms.IsFiniteLocallyFree (pullback.fst (i r) f) :=
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ r
    have hfin :=
      (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
        (pullback.fst (i r) f)).mp hlf
    exact ⟨Y r, i r, himm r, hrange r, hfin.1, inferInstance⟩

/-! ### Reduction of the general case to the separated one -/

/-- A closed-map property can be checked on a finite open cover of the source. -/
private theorem isClosedMap_of_finite_openCover
    {U X : Scheme.{u}} (f : U ⟶ X) (𝒰 : U.OpenCover) [Finite 𝒰.I₀]
    (hclosed : ∀ i, IsClosedMap (𝒰.f i ≫ f).base) : IsClosedMap f.base := by
  intro C hC
  have himage : f.base '' C = ⋃ i, (𝒰.f i ≫ f).base '' ((𝒰.f i).base ⁻¹' C) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz⟩ := 𝒰.covers y
      exact Set.mem_iUnion.2 ⟨𝒰.idx y, z, by simpa [hz] using hy, by simp [hz]⟩
    · intro hx
      obtain ⟨i, z, hzC, hzx⟩ := Set.mem_iUnion.1 hx
      exact ⟨𝒰.f i z, hzC, hzx⟩
  rw [himage]
  exact isClosed_iUnion_of_finite fun i => hclosed i _
    (hC.preimage (Scheme.Hom.continuous (𝒰.f i)))

/-- Universal closedness can be checked on a finite open cover of the source. -/
private theorem universallyClosed_of_finite_openCover
    {U X : Scheme.{u}} (f : U ⟶ X) (𝒰 : U.OpenCover) [Finite 𝒰.I₀]
    (hfinite : ∀ i, IsFinite (𝒰.f i ≫ f)) : UniversallyClosed f := by
  rw [universallyClosed_eq]
  intro U' X' i₁ i₂ f' hpb
  let 𝒱 := 𝒰.pullback₁ i₁
  have : Finite 𝒱.I₀ := inferInstanceAs (Finite 𝒰.I₀)
  have (i : 𝒱.I₀) : IsFinite (𝒱.f i ≫ f') := by
    have hpb₁ : IsPullback (𝒱.f i) (pullback.snd i₁ (𝒰.f i)) i₁ (𝒰.f i) :=
      IsPullback.of_hasPullback i₁ (𝒰.f i)
    exact MorphismProperty.of_isPullback (hpb₁.paste_horiz hpb).flip (hfinite i)
  exact isClosedMap_of_finite_openCover f' 𝒱 fun i => Scheme.Hom.isClosedMap _

/-- A morphism with quasi-compact source has a finite open cover of its source on which the
restrictions are separated. The members of the cover are chosen affine and over affine opens of
the target. -/
private theorem exists_finite_openCover_separated_restrictions
    {U X : Scheme.{u}} [CompactSpace U] (f : U ⟶ X) :
    ∃ 𝒰 : Scheme.OpenCover.{u} U, Finite 𝒰.I₀ ∧
      (∀ i, IsAffine (𝒰.X i)) ∧ ∀ i, IsSeparated (𝒰.f i ≫ f) := by
  classical
  let V := X.affineCover
  let C := V.pullback₁ f
  let A := Scheme.OpenCover.affineRefinement C
  let B := A.openCover
  let 𝒰 := B.finiteSubcover
  let e := Scheme.OpenCover.fromAffineRefinement C
  refine ⟨𝒰, inferInstance, ?_, ?_⟩
  · intro i
    let l := B.idx i.1
    show IsAffine (B.X l)
    exact Scheme.isAffine_affineOpenCover _ A l
  · intro i
    let l := B.idx i.1
    let j : V.I₀ := e.s₀ l
    let h : B.X l ⟶ V.X j := e.h₀ l ≫ V.pullbackHom f j
    have hfactor : h ≫ V.f j = 𝒰.f i ≫ f := by
      dsimp [h]
      rw [Category.assoc, Scheme.Cover.pullbackHom_map, ← Category.assoc, e.w₀ l]
      rfl
    have : IsAffine (B.X l) := Scheme.isAffine_affineOpenCover _ A _
    have : IsAffine (V.X j) := Scheme.isAffine_affineOpenCover X X.affineOpenCover j
    have : IsSeparated h := IsSeparated.of_isAffineHom h
    have : IsSeparated (X.affineCover.f j) := inferInstance
    have : IsSeparated (V.f j) := inferInstance
    rw [← hfactor]
    exact (IsSeparated.comp_iff (f := h) (g := V.f j)).2 inferInstance

/-- The common refinement of a finite family of partitions, omitting empty intersections. -/
private def topologicalCommonRefinement {T : Type*} [TopologicalSpace T]
    {ι : Type*} [Fintype ι] (P : ι → Set (Set T)) : Set (Set T) :=
  {S | ∃ t : ι → Set T, (∀ i, t i ∈ P i) ∧ S = ⋂ i, t i ∧ S.Nonempty}

/-- The common refinement of finitely many topological partitions is a topological
partition. -/
private theorem isTopologicalPartition_topologicalCommonRefinement
    {T : Type*} [TopologicalSpace T] {ι : Type*} [Fintype ι]
    (P : ι → Set (Set T)) (hP : ∀ i, IsTopologicalPartition (P i)) :
    IsTopologicalPartition (topologicalCommonRefinement P) := by
  classical
  have hempty : ∅ ∉ topologicalCommonRefinement P := by
    rintro ⟨t, -, -, hne⟩
    exact Set.not_nonempty_empty hne
  have huniq : ∀ x : T, ∃! S ∈ topologicalCommonRefinement P, x ∈ S := by
    intro x
    choose t htmem hxt using fun i => ((hP i).1.2 x).exists
    refine ⟨⋂ i, t i, ⟨⟨t, htmem, rfl, ⟨x, Set.mem_iInter.mpr hxt⟩⟩,
      Set.mem_iInter.mpr hxt⟩, ?_⟩
    rintro S ⟨⟨t', ht'mem, hEq, -⟩, hxS⟩
    have htt' : t = t' := by
      funext i
      exact ((hP i).1.2 x).unique ⟨htmem i, hxt i⟩
        ⟨ht'mem i, (Set.mem_iInter.mp (hEq ▸ hxS)) i⟩
    rw [hEq, htt']
  have hlocallyClosed : ∀ S ∈ topologicalCommonRefinement P, IsLocallyClosed S := by
    rintro S ⟨t, ht, rfl, hne⟩
    choose O Z hO hZ htOZ using fun i => (hP i).2 (t i) (ht i)
    refine ⟨⋂ i, O i, ⋂ i, Z i, isOpen_iInter_of_finite hO, isClosed_iInter hZ, ?_⟩
    ext x
    simp [htOZ, forall_and]
  exact ⟨⟨hempty, huniq⟩, hlocallyClosed⟩

/-- A finite intersection of immersion ranges is represented by an immersion, with its canonical
maps to all the factors. -/
private theorem exists_common_intersection_immersion
    {X : Scheme.{u}} {ι : Type*} (T : ι → Set X) (Y : ι → Scheme.{u})
    (j : ∀ i, Y i ⟶ X) (hj : ∀ i, IsImmersion (j i))
    (hrange : ∀ i, Set.range (j i).base = T i) (I : Finset ι) :
    ∃ (Z : Scheme.{u}) (k : Z ⟶ X), IsImmersion k ∧
      Set.range k.base = Set.iInter (fun i : {i // i ∈ I} => T i.1) ∧
      ∀ i, i ∈ I → ∃ h : Z ⟶ Y i, h ≫ j i = k := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      refine ⟨X, 𝟙 X, inferInstance, ?_, ?_⟩
      · ext x
        simp
      · simp
  | @insert a I ha hI =>
      obtain ⟨Z, k, hk, hr, hfac⟩ := hI
      let Z' := pullback k (j a)
      let k' : Z' ⟶ X := pullback.fst k (j a) ≫ k
      refine ⟨Z', k', inferInstance, ?_, ?_⟩
      · show Set.range (pullback.fst k (j a) ≫ k).base = _
        rw [Scheme.Pullback.range_fst_comp, hr, hrange a]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_iInter]
        constructor
        · rintro ⟨hxI, hxa⟩ i
          rcases Finset.mem_insert.mp i.2 with hia | hi
          · rw [hia]
            exact hxa
          · exact hxI ⟨i.1, hi⟩
        · intro hx
          refine ⟨?_, hx ⟨a, Finset.mem_insert_self ..⟩⟩
          intro i
          exact hx ⟨i.1, Finset.mem_insert_of_mem i.2⟩
      · intro i hi
        by_cases hia : i = a
        · subst i
          refine ⟨pullback.snd k (j a), ?_⟩
          simpa [k'] using (pullback.condition (f := k) (g := j a)).symm
        · have hiI : i ∈ I := (Finset.mem_insert.mp hi).resolve_left hia
          obtain ⟨h, hh⟩ := hfac i hiI
          refine ⟨pullback.fst k (j a) ≫ h, ?_⟩
          simp [k', Category.assoc, hh]

/-- Pullback along a composite agrees with the iterated pullback for finiteness. -/
private lemma isFinite_pullback_comp
    {A B C D : Scheme.{u}} (f : A ⟶ C) (g : B ⟶ C) (h : D ⟶ B)
    [IsFinite (pullback.fst g f)] : IsFinite (pullback.fst (h ≫ g) f) := by
  let q := pullback.fst h (pullback.fst g f)
  let r := pullback.snd h (pullback.fst g f) ≫ pullback.snd g f
  have H : IsPullback q r (h ≫ g) f :=
    (IsPullback.of_hasPullback h (pullback.fst g f)).paste_vert
      (IsPullback.of_hasPullback g f)
  let e := H.isoPullback
  have he : e.hom ≫ pullback.fst (h ≫ g) f = q := H.isoPullback_hom_fst
  have hq : IsFinite q := inferInstance
  have : IsFinite e.inv := inferInstance
  have hcomp : IsFinite (e.inv ≫ q) := inferInstance
  have he' : e.inv ≫ q = pullback.fst (h ≫ g) f := by
    rw [← he]
    simp
  rwa [he'] at hcomp

/-- Finiteness of the pullback over an open chart gives finiteness of the corresponding member
of the pulled-back open cover. -/
private lemma isFinite_openPullback_chart
    {U X Z : Scheme.{u}} (f : U ⟶ X) (k : Z ⟶ X) (V : U.Opens)
    [IsFinite (pullback.fst k (V.ι ≫ f))] :
    IsFinite (pullback.fst (pullback.snd k f) V.ι ≫ pullback.fst k f) := by
  let qP := pullback.fst (pullback.snd k f) V.ι
  let qV := pullback.snd (pullback.snd k f) V.ι
  let qZ := qP ≫ pullback.fst k f
  have H : IsPullback qZ qV k (V.ι ≫ f) :=
    (((IsPullback.of_hasPullback (pullback.snd k f) V.ι).flip).paste_vert
      (IsPullback.of_hasPullback k f).flip).flip
  let e := H.isoPullback
  have he : e.hom ≫ pullback.fst k (V.ι ≫ f) = qZ := H.isoPullback_hom_fst
  have hcomp : IsFinite (e.hom ≫ pullback.fst k (V.ι ≫ f)) := inferInstance
  rwa [he] at hcomp

/-- An open chart inside a finite scheme over the same base is closed in that chart: the finite
map to the base cancels across the finite, hence separated, chart map. -/
private lemma isClosedImmersion_of_isOpenImmersion_of_finite_comp
    {A B C : Scheme.{u}} (g : A ⟶ B) (h : B ⟶ C)
    [IsOpenImmersion g] [IsFinite (g ≫ h)] [IsSeparated h] :
    IsClosedImmersion g :=
  (IsClosedImmersion.iff_isFinite_and_mono g).2 ⟨IsFinite.of_comp g h, inferInstance⟩

/-- If all pairwise overlaps of an open cover are finite over the base, so is each member. -/
private lemma isFinite_pullback_opensRange_of_pairwise
    {U X T : Scheme.{u}} (f : U ⟶ X) (k : T ⟶ X) (𝒰 : U.OpenCover)
    (hfinite : ∀ i j, IsFinite
      (pullback.fst k (((𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange).ι ≫ f))) (i : 𝒰.I₀) :
    IsFinite (pullback.fst k ((𝒰.f i).opensRange.ι ≫ f)) := by
  rw [← inf_idem (𝒰.f i).opensRange]
  exact hfinite i i

/-- Pairwise finite chart overlaps make an étale map separated over an affine base: the chart
intersections are finite over the base, hence closed in each finite chart, and the
affine-intersection criterion then applies. -/
private lemma separated_of_pairwise_finite_affineTarget
    {U X T : Scheme.{u}} (f : U ⟶ X) (k : T ⟶ X)
    (𝒰 : U.OpenCover) [Finite 𝒰.I₀] [IsAffine T]
    (hfinite : ∀ i j, IsFinite
      (pullback.fst k (((𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange).ι ≫ f))) :
    IsSeparated (pullback.fst k f) := by
  classical
  let V := pullback k f
  let p := pullback.fst k f
  let q := pullback.snd k f
  apply isSeparated_of_affine_intersections p
  intro x y hxy
  let i := 𝒰.idx (q x)
  let j := 𝒰.idx (q y)
  let A : U.Opens := (𝒰.f i).opensRange
  let B : U.Opens := (𝒰.f j).opensRange
  let A' : V.Opens := q ⁻¹ᵁ A
  let B' : V.Opens := q ⁻¹ᵁ B
  let C' : V.Opens := A' ⊓ B'
  have hfi : IsFinite (pullback.fst k (A.ι ≫ f)) :=
    isFinite_pullback_opensRange_of_pairwise f k 𝒰 hfinite i
  have hfj : IsFinite (pullback.fst k (B.ι ≫ f)) :=
    isFinite_pullback_opensRange_of_pairwise f k 𝒰 hfinite j
  have hfij : IsFinite (pullback.fst k ((A ⊓ B).ι ≫ f)) := hfinite i j
  have hfinι : ∀ {Y : Scheme.{u}} (a : Y ⟶ V) [IsOpenImmersion a], IsFinite (a ≫ p) →
      ∀ {W : V.Opens}, a.opensRange = W → IsFinite (W.ι ≫ p) := by
    intro Y a _ hfin W ha
    have hrange : Set.range a.base = Set.range W.ι.base := by
      rw [← Scheme.Hom.coe_opensRange, ha]
      simp
    let e := IsOpenImmersion.isoOfRangeEq a W.ι hrange
    have he : e.hom ≫ W.ι = a := IsOpenImmersion.isoOfRangeEq_hom_fac a W.ι hrange
    have : IsFinite (e.hom ≫ W.ι ≫ p) := by
      rwa [← Category.assoc, he]
    simpa using (inferInstance : IsFinite (e.inv ≫ e.hom ≫ W.ι ≫ p))
  have hpre : ∀ O : U.Opens, IsFinite (pullback.fst k (O.ι ≫ f)) →
      IsAffineOpen (q ⁻¹ᵁ O) ∧ IsFinite ((q ⁻¹ᵁ O).ι ≫ p) := by
    intro O _
    let a := pullback.fst q O.ι
    have ha : a.opensRange = q ⁻¹ᵁ O := by
      simp [a, Scheme.Hom.opensRange_pullbackFst]
    have hfin : IsFinite (a ≫ p) := isFinite_openPullback_chart f k O
    have : IsAffineHom (a ≫ p) := inferInstance
    have : IsAffine (pullback q O.ι) := isAffine_of_isAffineHom (a ≫ p)
    refine ⟨?_, hfinι a hfin ha⟩
    rw [← ha]
    exact isAffineOpen_opensRange a
  have hA : IsAffineOpen A' ∧ IsFinite (A'.ι ≫ p) := hpre A hfi
  have hBaff : IsAffineOpen B' := (hpre B hfj).1
  have hC : IsAffineOpen C' ∧ IsFinite (C'.ι ≫ p) := hpre (A ⊓ B) hfij
  let g : C'.toScheme ⟶ A'.toScheme := V.homOfLE (U := C') (V := A') inf_le_left
  let h : A'.toScheme ⟶ T := A'.ι ≫ p
  have hcomp : IsFinite (g ≫ h) := by
    have hgh : g ≫ A'.ι = C'.ι := V.homOfLE_ι inf_le_left
    have hgh' : g ≫ h = C'.ι ≫ p := by
      simpa [h] using congrArg (fun t => t ≫ p) hgh
    rw [hgh']
    exact hC.2
  have : IsFinite (A'.ι ≫ p) := hA.2
  have : IsSeparated h := by infer_instance
  have hgClosed : IsClosedImmersion g :=
    isClosedImmersion_of_isOpenImmersion_of_finite_comp g h
  have hclosed : IsClosed ((A'.ι ⁻¹ᵁ C' : A'.toScheme.Opens) : Set A'.toScheme) := by
    rw [← Scheme.opensRange_homOfLE]
    simpa [Scheme.Hom.coe_opensRange] using hgClosed.isClosedEmbedding.isClosed_range
  have hsec : Function.Surjective (sectionTensorMap V A' B') :=
    sectionTensorMap_surjective_of_isClosed_inf V hA.1 hC.1 hclosed
  exact ⟨A', B', ⊤, 𝒰.covers (q x), 𝒰.covers (q y), hA.1, hBaff, isAffineOpen_top T, le_top,
    le_top, hC.1, hsec⟩

/-- The affine-base separatedness argument is local on the target. -/
private lemma separated_of_pairwise_finite
    {U X T : Scheme.{u}} (f : U ⟶ X) (k : T ⟶ X)
    (𝒰 : U.OpenCover) [Finite 𝒰.I₀]
    (hfinite : ∀ i j, IsFinite
      (pullback.fst k (((𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange).ι ≫ f))) :
    IsSeparated (pullback.fst k f) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := @IsSeparated) (fun W : T.affineOpens => W.1) (iSup_affineOpens_eq_top T)]
  intro W
  let kW := W.1.ι ≫ k
  have hfiniteW (i j : 𝒰.I₀) : IsFinite
      (pullback.fst kW (((𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange).ι ≫ f)) := by
    let g := ((𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange).ι ≫ f
    have : IsFinite (pullback.fst k g) := hfinite i j
    exact isFinite_pullback_comp g k W.1.ι
  have hsep : IsSeparated (pullback.fst kW f) :=
    separated_of_pairwise_finite_affineTarget f kW 𝒰 hfiniteW
  let p := pullback.fst k f
  let q := pullback.snd k f
  let e₁ : Arrow.mk (pullback.snd p W.1.ι) ≅ Arrow.mk (pullback.fst W.1.ι p) :=
    Arrow.isoMk (pullbackSymmetry p W.1.ι) (Iso.refl _) (pullbackSymmetry_hom_comp_fst _ _)
  have H : IsPullback (pullback.fst W.1.ι p) (pullback.snd W.1.ι p ≫ q) kW f :=
    (IsPullback.of_hasPullback W.1.ι p).paste_vert (IsPullback.of_hasPullback k f)
  let e₂ : Arrow.mk (pullback.fst W.1.ι p) ≅ Arrow.mk (pullback.fst kW f) :=
    Arrow.isoMk H.isoPullback (Iso.refl _) H.isoPullback_hom_fst
  let e₃ := morphismRestrictOpensRange p W.1.ι
  have hEq : W.1.ι.opensRange = W.1 := by
    ext x
    simp
  let e₄ := morphismRestrictEq p hEq
  have hlocalRange : IsSeparated (p ∣_ W.1.ι.opensRange) :=
    (MorphismProperty.arrow_mk_iso_iff (P := @IsSeparated)
      (e₃.trans (e₁.trans e₂))).mpr hsep
  exact (MorphismProperty.arrow_mk_iso_iff (P := @IsSeparated) e₄).mp hlocalRange

/-- Simultaneously stratify all the affine source charts and their pairwise intersections so
that each chart intersection becomes finite over every stratum. -/
private theorem exists_pairwise_finite_partition
    {U X : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U]
    [CompactSpace X] [QuasiSeparatedSpace X] (f : U ⟶ X) [Etale f] :
    ∃ 𝒰 : Scheme.OpenCover.{u} U, Finite 𝒰.I₀ ∧
      (∀ i, IsAffine (𝒰.X i)) ∧
      ∃ P : Set (Set X), IsTopologicalPartition P ∧
        (∀ S ∈ P, Topology.IsConstructible S) ∧
        ∀ S ∈ P, ∃ (T : Scheme.{u}) (k : T ⟶ X), IsImmersion k ∧
          Set.range k.base = S ∧
          ∀ i j, IsFinite
            (pullback.fst k ((((𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange).ι) ≫ f)) := by
  classical
  obtain ⟨𝒰, hfinite, haffine, hsep⟩ := exists_finite_openCover_separated_restrictions f
  let κ := 𝒰.I₀ × 𝒰.I₀
  have : Fintype κ := Fintype.ofFinite κ
  let W (a : κ) : U.Opens := (𝒰.f a.1).opensRange ⊓ (𝒰.f a.2).opensRange
  let g (a : κ) : (W a).toScheme ⟶ X := (W a).ι ≫ f
  have hcompactRange (i : 𝒰.I₀) : IsCompact ((𝒰.f i).opensRange : Set U) := by
    have : IsAffine (𝒰.X i) := haffine i
    have : CompactSpace (𝒰.X i) := Scheme.compactSpace_of_isAffine _
    simpa only [Scheme.Hom.coe_opensRange] using isCompact_range (𝒰.f i).continuous
  have hlocal (a : κ) :
      CompactSpace (W a).toScheme ∧ QuasiSeparatedSpace (W a).toScheme ∧
        IsSeparated (g a) ∧ Etale (g a) := by
    have : CompactSpace (W a).toScheme := isCompact_iff_compactSpace.mp <|
      QuasiSeparatedSpace.inter_isCompact _ _ (𝒰.f a.1).opensRange.2
        (hcompactRange a.1) (𝒰.f a.2).opensRange.2 (hcompactRange a.2)
    have : QuasiSeparatedSpace (W a).toScheme := quasiSeparatedSpace_of_quasiSeparated (W a).ι
    have hrange : Set.range ((W a).ι).base ⊆ Set.range (𝒰.f a.1).base := by
      rintro y ⟨w, rfl⟩
      exact Scheme.Hom.mem_opensRange.mp w.2.1
    let h : (W a).toScheme ⟶ 𝒰.X a.1 := IsOpenImmersion.lift (𝒰.f a.1) (W a).ι hrange
    have hfac : h ≫ 𝒰.f a.1 = (W a).ι := IsOpenImmersion.lift_fac _ _ _
    have hg : g a = h ≫ (𝒰.f a.1 ≫ f) := by
      dsimp [g]
      rw [← hfac, Category.assoc]
    have : IsSeparated (𝒰.f a.1 ≫ f) := hsep a.1
    have : IsSeparated (g a) := by rw [hg]; infer_instance
    have : Etale (g a) := by rw [hg]; infer_instance
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have hP (a : κ) : ∃ P : Set (Set X), IsTopologicalPartition P ∧
      (∀ S ∈ P, Topology.IsConstructible S) ∧
      ∀ S ∈ P, ∃ (Y : Scheme.{u}) (j : Y ⟶ X), IsImmersion j ∧
        Set.range j.base = S ∧ IsFinite (pullback.fst j (g a)) ∧
          Etale (pullback.fst j (g a)) := by
    obtain ⟨_, _, _, _⟩ := hlocal a
    exact exists_constructible_partition_finite_etale_of_isSeparated (g a)
  choose P hPpart hPcons hPdata using hP
  refine ⟨𝒰, hfinite, haffine, topologicalCommonRefinement P,
    isTopologicalPartition_topologicalCommonRefinement P hPpart, ?_, ?_⟩
  · rintro S ⟨T, hT, rfl, -⟩
    exact Topology.IsConstructible.iInter fun a => hPcons a (T a) (hT a)
  rintro S ⟨T, hT, rfl, -⟩
  choose Y j hjimm hjrange hjfinite using fun a => hPdata a (T a) (hT a)
  obtain ⟨Z, k, hkimm, hkrange, hfactor⟩ :=
    exists_common_intersection_immersion T Y j hjimm hjrange Finset.univ
  refine ⟨Z, k, hkimm, ?_, fun i j' => ?_⟩
  · rw [hkrange]
    ext x
    simp
  let a : κ := (i, j')
  obtain ⟨z, hz⟩ := hfactor a (Finset.mem_univ a)
  have : IsFinite (pullback.fst (j a) (g a)) := (hjfinite a).1
  have hfin := isFinite_pullback_comp (g a) (j a) z
  rwa [hz] at hfin

/-- If all pairwise overlaps of a finite open chart cover are finite over the base, then the
whole étale pullback is finite over the base. -/
private theorem isFinite_of_pairwise_finite_chart_intersections
    {U X T : Scheme.{u}} (f : U ⟶ X) [Etale f] (k : T ⟶ X)
    (𝒰 : U.OpenCover) [Finite 𝒰.I₀]
    (hfinite : ∀ i j, IsFinite
      (pullback.fst k (((𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange).ι ≫ f))) :
    IsFinite (pullback.fst k f) := by
  classical
  let p := pullback.fst k f
  have : IsSeparated p := separated_of_pairwise_finite f k 𝒰 hfinite
  let A : 𝒰.I₀ → U.Opens := fun i => (𝒰.f i).opensRange
  let W : U.OpenCover := U.openCoverOfIsOpenCover A 𝒰.isOpenCover_opensRange
  have hWf (i : 𝒰.I₀) : W.f i = (A i).ι := by
    dsimp [W]
    exact Scheme.openCoverOfIsOpenCover_f U A 𝒰.isOpenCover_opensRange i
  let V : (pullback k f).OpenCover := Scheme.Pullback.openCoverOfRight W k f
  have : Finite W.I₀ := inferInstanceAs (Finite 𝒰.I₀)
  have hidx : V.I₀ = W.I₀ := Scheme.Pullback.openCoverOfRight_I₀ W k f
  have : Finite V.I₀ := Finite.of_equiv W.I₀ (Equiv.cast hidx).symm
  have hchart := isFinite_pullback_opensRange_of_pairwise f k 𝒰 hfinite
  have hVfinite : ∀ i : W.I₀, IsFinite (V.f i ≫ p) := by
    intro i
    have hcomp : V.f i ≫ p = pullback.fst k (W.f i ≫ f) := by
      simp only [V, p, Scheme.Pullback.openCoverOfRight_f]
      exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    rw [hcomp]
    exact hchart i
  have : Etale p := inferInstanceAs (Etale (pullback.fst k f))
  have : LocallyOfFiniteType p := inferInstance
  have : LocallyQuasiFinite p := (locallyQuasiFinite_of_etale p).2
  have : UniversallyClosed p := universallyClosed_of_finite_openCover p V hVfinite
  have : IsProper p := IsProper.mk
  exact IsFinite.of_isProper_of_locallyQuasiFinite p

/-- Let `f : U ⟶ X` be an étale morphism of quasi-compact and quasi-separated schemes. Then `X`
has a partition into constructible locally closed subschemes over each of which the base change
of `f` is finite étale. -/
@[stacks 03S0]
public theorem exists_constructible_partition_finite_etale
    {U X : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U]
    [CompactSpace X] [QuasiSeparatedSpace X] (f : U ⟶ X) [Etale f] :
    ∃ P : Set (Set X), IsTopologicalPartition P ∧
      (∀ S ∈ P, Topology.IsConstructible S) ∧
      (∀ S ∈ P, ∃ (Y : Scheme.{u}) (i : Y ⟶ X),
        IsImmersion i ∧ Set.range i.base = S ∧
          IsFinite (pullback.fst i f) ∧ Etale (pullback.fst i f)) := by
  obtain ⟨𝒰, _, -, P, hP, hconstructible, hfiniteCharts⟩ := exists_pairwise_finite_partition f
  refine ⟨P, hP, hconstructible, fun S hS => ?_⟩
  obtain ⟨T, k, hkimm, hkrange, hpairwise⟩ := hfiniteCharts S hS
  exact ⟨T, k, hkimm, hkrange,
    isFinite_of_pairwise_finite_chart_intersections f k 𝒰 hpairwise, inferInstance⟩

end AlgebraicGeometry

end
