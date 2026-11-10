module

public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IotaRealizableSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SurjectiveClosedImmersionWeights
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.Topology.Dimension.DimensionLEOne
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# The dévissage of the weight bound of Weil II

The reduction of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Deligne, Weil II 3.3; Kedlaya, *Fourier
transforms and p-adic Weil II*, §6) to curves proves, for a scheme `X` separated of finite type
over a finite field `k` with `q = p ^ n` elements, the statement

  `S(X)`: for every compactification `j` of `X`, every lisse ℓ-adic sheaf `F` on `X` which is
  pointwise `ι`-mixed of weights `≤ w` and `ι`-realizable, and every `i`, the complex roots of the
  characteristic polynomial of the geometric Frobenius on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`, read along `ι`,
  have absolute values `q ^ (w' / 2)` with `w' ≤ w + i`

(`Stacks.EtaleCohomology.LAdicSheaf.SatisfiesWeightBound`).  All three hypotheses on `F` pass to
open and closed subschemes (`AlgebraicGeometry.SmallEtale.LAdicSheaf.IsLisse.inverseImage`,
`Stacks.EtaleCohomology.LAdicSheaf.IsPointwiseMixedOfWeightLE.inverseImage`,
`Stacks.EtaleCohomology.LAdicSheaf.IsIotaRealizable.inverseImage`: closed points of an open of a
scheme of finite type over a field are closed), so the excision sequence gives `S(X)` from `S(U)`
and `S(Z)` for `X = U ⊔ Z`, and noetherian induction on the closed subsets of `X` reduces `S(X)`
to: every nonempty closed subscheme of `X` has a nonempty open subscheme `U` with `S(U)`.

The finiteness of the cohomology groups (Tag 03V3 at the finite levels, and the finite
dimensionality of `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`) is an input of the excision sequence; it is recorded as
`Stacks.EtaleCohomology.LAdicSheaf.HasFiniteCompactSupportCohomology` and assumed here.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.HasFiniteCompactSupportCohomology`.
* `Stacks.EtaleCohomology.LAdicSheaf.SatisfiesWeightBound`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.satisfiesWeightBound_of_openClosed`: excision.
* `Stacks.EtaleCohomology.LAdicSheaf.satisfiesWeightBound_of_forall_exists_open`: noetherian
  induction.
* `Stacks.EtaleCohomology.LAdicSheaf.satisfiesWeightBound_of_topologicalKrullDim_le_zero`: the
  weight bound in dimension zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q) (ι : ℚ_[ℓ] →+* ℂ)

/-- **Finiteness of compactly supported ℓ-adic cohomology on `X`** (Tag 03V3 and its ℓ-adic
consequence): for every compactification and every ℓ-adic sheaf, the groups `Hⁱ_c(X_k̄, Fₙ)` at
the finite levels are finite and `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is finite dimensional. -/
def LAdicSheaf.HasFiniteCompactSupportCohomology (X : B.Scheme) [IsNoetherian X.1]
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] : Prop :=
  ∀ (j : CompactificationOf (Over.mk f)) (F : LAdicSheaf.{u, u + 1} B X ℓ) (i : ℤ),
    FiniteDimensional ℚ_[ℓ]
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) ∧
      ∀ n, Finite ((compactSupportSheafCohomology ℤ_[ℓ] f j kbar i).obj
        ((LAdicSheaf.padicTower B X ℓ F).obj n))

/-- **The weight bound of Weil II on `X`** (Weil II 3.3.1 for lisse sheaves): for every
compactification `j` of `X`, every lisse ℓ-adic sheaf `F` on `X` which is pointwise `ι`-mixed of
weights `≤ w` and `ι`-realizable, and every `i`, the complex roots of the characteristic
polynomial of the geometric Frobenius on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`, read along `ι`, have absolute
values `q ^ (w' / 2)` with `w' ≤ w + i`. -/
def LAdicSheaf.SatisfiesWeightBound (X : B.Scheme) [IsNoetherian X.1]
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] : Prop :=
  ∀ (j : CompactificationOf (Over.mk f)) (F : LAdicSheaf.{u, u + 1} B X ℓ) (w : ℤ), F.IsLisse →
    LAdicSheaf.IsPointwiseMixedOfWeightLE B X ℓ f F (p ^ q) ι w →
    LAdicSheaf.IsIotaRealizable B X ℓ f F ι →
    ∀ (i : ℤ) [FiniteDimensional ℚ_[ℓ]
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)],
      IsCharpolyNormMixedOfWeightLE (p ^ q) ι (w + i)
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i).hom

variable {B ℓ kbar p q hcard ι}

/-- The weight bound only depends on the structure morphism. -/
theorem LAdicSheaf.SatisfiesWeightBound.congr {X : B.Scheme} [IsNoetherian X.1]
    {f g : X.1 ⟶ Spec (.of k)} [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g] (h : f = g)
    (hf : LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι X f) :
    LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι X g := by
  subst h
  exact hf

/-- On an empty scheme the weight bound holds. -/
theorem LAdicSheaf.satisfiesWeightBound_of_isEmpty (X : B.Scheme) [IsNoetherian X.1]
    [IsEmpty X.1] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f] : LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι X f :=
  fun j F _ _ _ _ i _ =>
    LAdicSheaf.isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_of_isEmpty
      B ℓ f j kbar p q hcard F i

omit [Fintype k] in
/-- Closed points of a scheme of finite type over a field stay closed in any scheme of finite type
over the field into which it immerses openly (a Jacobson scheme). -/
theorem mem_closedPoints_of_isOpenImmersion {U X : Scheme.{u}} (g : U ⟶ X)
    [IsOpenImmersion g] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (y : closedPoints U) :
    g.base y.1 ∈ closedPoints X := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have h : y.1 ∈ g.base ⁻¹' closedPoints X := by
    rw [g.isOpenEmbedding.preimage_closedPoints]
    exact y.2
  exact h

/-- A closed immersion sends closed points to closed points. -/
theorem mem_closedPoints_of_isClosedImmersion {Z X : Scheme.{u}} (g : Z ⟶ X)
    [IsClosedImmersion g] (y : closedPoints Z) : g.base y.1 ∈ closedPoints X := by
  have h := g.isClosedEmbedding.isClosedMap _ y.2
  rwa [Set.image_singleton] at h

/-- Every ideal sheaf on a noetherian `B`-scheme cuts out a noetherian `B`-scheme with a closed
immersion into it, with the range of the ideal sheaf's subscheme. -/
private theorem exists_closedSubscheme (X : B.Scheme) [IsNoetherian X.1]
    (I : X.1.IdealSheafData) : ∃ (Z : B.Scheme) (_ : IsNoetherian Z.1) (iZ : Z ⟶ X)
      (_ : IsClosedImmersion (B.inclusion.map iZ)),
      Set.range (B.inclusion.map iZ).base = Set.range I.subschemeι.base ∧
        (IsReduced I.subscheme → IsReduced Z.1) := by
  have hZB : B.Contains I.subscheme :=
    Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit I.subschemeι X.property
  have hIc : IsClosedImmersion I.subschemeι := inferInstance
  have hXl : IsLocallyNoetherian X.1 := ‹AlgebraicGeometry.IsNoetherian X.1›.toIsLocallyNoetherian
  have hIl : IsLocallyNoetherian I.subscheme :=
    @isLocallyNoetherian_of_isClosedImmersion _ _ I.subschemeι hIc hXl
  have hIq : CompactSpace I.subscheme := I.subschemeι.isClosedEmbedding.compactSpace
  have hIn : IsNoetherian I.subscheme := { }
  exact ⟨B.obj I.subscheme hZB, hIn, ObjectProperty.homMk I.subschemeι, hIc, rfl, id⟩

/-- **Excision for the weight bound**: for `X = U ⊔ Z` with `U` open and `Z` closed, the weight
bound on `U` and on `Z` gives the weight bound on `X`, given the finiteness of the cohomology of
`U` and `Z`. -/
theorem LAdicSheaf.satisfiesWeightBound_of_openClosed {X : B.Scheme} [IsNoetherian X.1]
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    {U Z : B.Scheme} [IsNoetherian U.1] [IsNoetherian Z.1] (jU : U ⟶ X) (iZ : Z ⟶ X)
    [IsOpenImmersion (B.inclusion.map jU)] [IsClosedImmersion (B.inclusion.map iZ)]
    [QuasiCompact (B.inclusion.map jU ≫ f)]
    (hij : Set.range (B.inclusion.map jU).base = (Set.range (B.inclusion.map iZ).base)ᶜ)
    (hfinU : LAdicSheaf.HasFiniteCompactSupportCohomology B ℓ kbar U (B.inclusion.map jU ≫ f))
    (hfinZ : LAdicSheaf.HasFiniteCompactSupportCohomology B ℓ kbar Z (B.inclusion.map iZ ≫ f))
    (hU : LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι U (B.inclusion.map jU ≫ f))
    (hZ : LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι Z (B.inclusion.map iZ ≫ f)) :
    LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι X f := by
  intro j F w hl hm hr i _
  set jU' := B.inclusion.map jU
  set iZ' := B.inclusion.map iZ
  have hgU : ∀ y : closedPoints U.1, jU'.base y.1 ∈ closedPoints X.1 :=
    mem_closedPoints_of_isOpenImmersion jU' f
  have hgZ : ∀ y : closedPoints Z.1, iZ'.base y.1 ∈ closedPoints X.1 :=
    mem_closedPoints_of_isClosedImmersion iZ'
  obtain ⟨hU1, hU2⟩ := hfinU (j.restrictOpen jU') (LAdicSheaf.inverseImage jU F) i
  obtain ⟨hZ1, -⟩ := hfinZ (j.restrictClosed iZ') (LAdicSheaf.inverseImage iZ F) i
  -- the open part of the tower of `X` has finite cohomology at every level
  let T := LAdicSheaf.padicTower B X ℓ F
  let eU : T ⋙ etaleModuleRestriction.{u, 0} ℤ_[ℓ] jU' ≅
      LAdicSheaf.padicTower B U ℓ (LAdicSheaf.inverseImage jU F) :=
    Functor.isoWhiskerLeft T (etaleModuleInverseImageRestrictionIso.{u, 0} ℤ_[ℓ] jU').symm ≪≫
      LAdicSheaf.padicTowerInverseImageIso B ℓ jU F
  let EU := towerOpenPartCohomologyIso f j kbar jU' T i ≪≫ Functor.isoWhiskerRight eU
    (compactSupportSheafCohomology ℤ_[ℓ] (jU' ≫ f) (j.restrictOpen jU') kbar i)
  have hfin : ∀ n, Finite ((compactSupportSheafCohomology ℤ_[ℓ] f j kbar i).obj
      ((etaleModuleOpenPart ℤ_[ℓ] jU').obj (T.obj n))) := fun n => by
    exact @Finite.of_equiv _ _ (hU2 n) (EU.app n).toLinearEquiv.toEquiv.symm
  exact isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_of_openClosed
    B ℓ f j kbar p q hcard F i jU iZ hij hfin
    (hU (j.restrictOpen jU') (LAdicSheaf.inverseImage jU F) w (hl.inverseImage jU)
      (LAdicSheaf.IsPointwiseMixedOfWeightLE.inverseImage X ℓ jU f hm hgU)
      (LAdicSheaf.IsIotaRealizable.inverseImage ℓ f jU hr hgU) i)
    (hZ (j.restrictClosed iZ') (LAdicSheaf.inverseImage iZ F) w (hl.inverseImage iZ)
      (LAdicSheaf.IsPointwiseMixedOfWeightLE.inverseImage X ℓ iZ f hm hgZ)
      (LAdicSheaf.IsIotaRealizable.inverseImage ℓ f iZ hr hgZ) i)

/-- **Noetherian induction for the weight bound.**  If every nonempty closed subscheme `Z` of `X`
has a nonempty open subscheme `U` satisfying the weight bound, then `X` satisfies the weight
bound, given the finiteness of compactly supported cohomology: removing `U` from `Z` leaves a
closed subscheme with strictly smaller underlying closed set, and excision glues. -/
theorem LAdicSheaf.satisfiesWeightBound_of_forall_exists_open (X : B.Scheme) [IsNoetherian X.1]
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (hfin : ∀ (Y : B.Scheme) [IsNoetherian Y.1] (g : Y.1 ⟶ Spec (.of k)) [LocallyOfFiniteType g]
      [QuasiCompact g] [IsSeparated g], topologicalKrullDim Y.1 ≤ topologicalKrullDim X.1 →
        LAdicSheaf.HasFiniteCompactSupportCohomology B ℓ kbar Y g)
    (hloc : ∀ (Z : B.Scheme) [IsNoetherian Z.1] (iZ : Z ⟶ X)
        [IsClosedImmersion (B.inclusion.map iZ)],
      Nonempty Z.1 → ∃ (U : B.Scheme) (_ : IsNoetherian U.1) (jU : U ⟶ Z)
        (_ : IsOpenImmersion (B.inclusion.map jU))
        (_ : QuasiCompact (B.inclusion.map jU ≫ B.inclusion.map iZ ≫ f)), Nonempty U.1 ∧
        LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι U
          (B.inclusion.map jU ≫ B.inclusion.map iZ ≫ f)) :
    LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι X f := by
  suffices H : ∀ (C : TopologicalSpace.Closeds X.1) (Z : B.Scheme) [IsNoetherian Z.1]
      (iZ : Z ⟶ X) [IsClosedImmersion (B.inclusion.map iZ)],
      Set.range (B.inclusion.map iZ).base = (C : Set X.1) →
      LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι Z (B.inclusion.map iZ ≫ f) by
    have : IsClosedImmersion (B.inclusion.map (𝟙 X)) := by
      rw [CategoryTheory.Functor.map_id]
      infer_instance
    exact (H ⊤ X (𝟙 X) (by rw [CategoryTheory.Functor.map_id]; exact Set.range_id)).congr
      (by simp)
  intro C
  induction C using WellFoundedLT.induction with
  | _ C ih =>
  intro Z _ iZ _ hC
  set iZ' := B.inclusion.map iZ
  rcases isEmpty_or_nonempty Z.1 with hZ | hZ
  · exact LAdicSheaf.satisfiesWeightBound_of_isEmpty Z _
  obtain ⟨U, _, jU, _, _, hUne, hUw⟩ := hloc Z iZ hZ
  set jU' := B.inclusion.map jU
  -- the complement of `U` in `Z`, with its reduced structure
  let C' : TopologicalSpace.Closeds Z.1 :=
    ⟨(Set.range jU'.base)ᶜ, jU'.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let I := Scheme.IdealSheafData.vanishingIdeal C'
  obtain ⟨Z', _, iZZ', _, hrange, -⟩ := exists_closedSubscheme Z I
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    at hrange
  replace hrange : Set.range (B.inclusion.map iZZ').base = (Set.range jU'.base)ᶜ := hrange
  -- the complement is a closed subscheme of `X` with strictly smaller support
  have : IsClosedImmersion (B.inclusion.map (iZZ' ≫ iZ)) := by
    rw [CategoryTheory.Functor.map_comp]
    infer_instance
  have hcomp : ∀ z, iZ'.base ((B.inclusion.map iZZ').base z) =
      (B.inclusion.map (iZZ' ≫ iZ)).base z := fun z => by
    rw [CategoryTheory.Functor.map_comp]
    rfl
  have hlt : (⟨Set.range (B.inclusion.map (iZZ' ≫ iZ)).base,
      (B.inclusion.map (iZZ' ≫ iZ)).isClosedEmbedding.isClosed_range⟩ :
        TopologicalSpace.Closeds X.1) < C := by
    refine lt_of_le_of_ne ?_ ?_
    · change Set.range (B.inclusion.map (iZZ' ≫ iZ)).base ⊆ (C : Set X.1)
      rw [← hC]
      rintro _ ⟨z, rfl⟩
      exact ⟨(B.inclusion.map iZZ').base z, hcomp z⟩
    · intro heq
      obtain ⟨u⟩ := hUne
      have hz : iZ'.base (jU'.base u) ∈ (C : Set X.1) := hC ▸ Set.mem_range_self _
      rw [← heq] at hz
      obtain ⟨z', hz'⟩ := hz
      rw [← hcomp z'] at hz'
      have hz'' := iZ'.isClosedEmbedding.injective hz'
      have hmem : (B.inclusion.map iZZ').base z' ∈ Set.range (B.inclusion.map iZZ').base :=
        Set.mem_range_self _
      rw [hrange, hz''] at hmem
      exact hmem (Set.mem_range_self _)
  have hZ'w := (ih _ hlt Z' (iZZ' ≫ iZ) rfl).congr
    (g := B.inclusion.map iZZ' ≫ iZ' ≫ f) (by rw [CategoryTheory.Functor.map_comp, Category.assoc])
  have hdZ : topologicalKrullDim Z.1 ≤ topologicalKrullDim X.1 :=
    iZ'.isClosedEmbedding.isInducing.topologicalKrullDim_le
  exact LAdicSheaf.satisfiesWeightBound_of_openClosed (iZ' ≫ f) jU iZZ'
    (by rw [hrange, compl_compl])
    (hfin U _ (jU'.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hdZ))
    (hfin Z' _
      ((B.inclusion.map iZZ').isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdZ))
    hUw hZ'w

/-- **Weil II in dimension zero.**  A scheme of finite type over `k` of Krull dimension `≤ 0` is
finite over `k`, and its reduction is finite étale; the weight bound holds, given finite
dimensionality of the cohomology of the reduction. -/
theorem LAdicSheaf.satisfiesWeightBound_of_topologicalKrullDim_le_zero [IsAlgClosed kbar]
    [CharP kbar p] (X : B.Scheme) [IsNoetherian X.1] (f : X.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (hdim : topologicalKrullDim X.1 ≤ 0)
    (hfin : ∀ (Y : B.Scheme) [IsNoetherian Y.1] (g : Y.1 ⟶ Spec (.of k)) [LocallyOfFiniteType g]
      [QuasiCompact g] [IsSeparated g], topologicalKrullDim Y.1 ≤ topologicalKrullDim X.1 →
        LAdicSheaf.HasFiniteCompactSupportCohomology B ℓ kbar Y g) :
    LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι X f := by
  have hX : (Set.univ : Set X.1).Finite :=
    Stacks.Topology.Dimension.finite_of_topologicalKrullDim_le_zero hdim
  have : LocallyQuasiFinite f :=
    .of_finite_preimage_singleton f fun _ => hX.subset (Set.subset_univ _)
  have : IsFinite f := IsFinite.of_locallyQuasiFinite f
  let I := X.1.nilradical
  obtain ⟨Z, _, iZ, _, hrange, hred⟩ := exists_closedSubscheme X I
  have : IsReduced Z.1 := hred (isReduced_nilradical_subscheme X.1)
  have hsurj : Function.Surjective (B.inclusion.map iZ).base := by
    rw [← Set.range_eq_univ, hrange, Scheme.IdealSheafData.range_subschemeι]
    rfl
  intro j F w _ hm _ i _
  have := (hfin Z (B.inclusion.map iZ ≫ f)
    (B.inclusion.map iZ).isClosedEmbedding.isInducing.topologicalKrullDim_le
    (j.restrictClosed (B.inclusion.map iZ)) (LAdicSheaf.inverseImage iZ F) i).1
  exact isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_of_isFinite
    B ℓ f j kbar p q hcard F ι w hm i iZ hsurj

end Stacks.EtaleCohomology
