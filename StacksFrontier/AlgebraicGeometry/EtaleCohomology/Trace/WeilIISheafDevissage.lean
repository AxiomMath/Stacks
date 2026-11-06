module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicExcisionWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIDevissage

/-!
# The dévissage of the weight bound of Weil II, one sheaf at a time

In dimension at least two the reduction of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Deligne, Weil II 3.3) to curves fibres an
open of the scheme over an affine space and uses the open of the base over which the higher direct
images with compact support of the sheaf are lisse. That open depends on the sheaf, so the
noetherian induction of `LAdicSheaf.satisfiesWeightBound_of_forall_exists_open` is run here for
one sheaf at a time: the weight bound for a sheaf `F` on `X`
(`Stacks.EtaleCohomology.LAdicSheaf.CompactSupportWeightLE`) follows from the weight bound for `F`
restricted to an open `U` and to the closed complement (excision), and every lisse, pointwise
mixed, realizable sheaf on every closed subscheme having a nonempty open on which its restriction
satisfies the bound gives the weight bound on `X`.

The bound only depends on the tower of levels of the sheaf up to isomorphism
(`Stacks.EtaleCohomology.LAdicSheaf.compactSupportWeightLE_iff_of_padicTowerIso`), so iterated
inverse images along equal composites may be exchanged
(`Stacks.EtaleCohomology.LAdicSheaf.padicTowerInverseImageCompIso`).

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.CompactSupportWeightLE`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.compactSupportWeightLE_of_openClosed`: excision.
* `LAdicSheaf.satisfiesWeightBound_of_forall_exists_open_compactSupportWeightLE`:
  noetherian induction with a good open depending on the sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

-- instances of `Stacks.Models.RegularModelSituation` whose conclusions (`QuasiCompact ?f`, ...)
-- match every goal and send instance search into a loop; they are irrelevant here
attribute [-instance] Stacks.Models.RegularModelSituation.commRingR
  Stacks.Models.RegularModelSituation.isDomainR
  Stacks.Models.RegularModelSituation.isDiscreteValuationRingR
  Stacks.Models.RegularModelSituation.fieldK Stacks.Models.RegularModelSituation.algebraRK
  Stacks.Models.RegularModelSituation.isFractionRingRK Stacks.Models.RegularModelSituation.fieldk
  Stacks.Models.RegularModelSituation.algebraRk Stacks.Models.RegularModelSituation.isCurve
  Stacks.Models.RegularModelSituation.smooth Stacks.Models.RegularModelSituation.flat
  Stacks.Models.RegularModelSituation.locallyOfFiniteType
  Stacks.Models.RegularModelSituation.quasiCompact

/-- A closed immersion is locally of finite type; stated directly because instance search for it
times out on the composites below. -/
local instance (priority := high) locallyOfFiniteType_of_isClosedImmersion_weilIISheafDevissage
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] : LocallyOfFiniteType f :=
  ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mp
    ((IsClosedImmersion.iff_isFinite_and_mono (f := f)).mp ‹_›).1).2

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

/-- **The weight bound of Weil II for one sheaf**: for every compactification `j` of `X` and every
`i`, the complex roots of the characteristic polynomial of the geometric Frobenius on
`Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`, read along `ι`, have absolute values `q ^ (w' / 2)` with `w' ≤ w + i`. -/
def LAdicSheaf.CompactSupportWeightLE (X : B.Scheme) [IsNoetherian X.1]
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (F : LAdicSheaf.{u, u + 1} B X ℓ) (w : ℤ) : Prop :=
  ∀ (j : CompactificationOf (Over.mk f)) (i : ℤ) [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)],
    IsCharpolyNormMixedOfWeightLE (p ^ q) ι (w + i)
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i).hom

variable {B ℓ kbar p q hcard ι}

/-- The weight bound on `X` is the weight bound for every lisse, pointwise mixed, realizable
sheaf. -/
theorem LAdicSheaf.satisfiesWeightBound_iff_forall_compactSupportWeightLE (X : B.Scheme)
    [IsNoetherian X.1] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f] :
    LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι X f ↔
      ∀ (F : LAdicSheaf.{u, u + 1} B X ℓ) (w : ℤ), F.IsLisse →
        LAdicSheaf.IsPointwiseMixedOfWeightLE B X ℓ f F (p ^ q) ι w →
        LAdicSheaf.IsIotaRealizable B X ℓ f F ι →
        LAdicSheaf.CompactSupportWeightLE B ℓ kbar p q hcard ι X f F w :=
  ⟨fun h F w hl hm hr j i _ => h j F w hl hm hr i, fun h j F w hl hm hr i _ => h F w hl hm hr j i⟩

/-- **The weight bound for one sheaf only depends on its tower of levels**, given the finite
dimensionality of the cohomology: an isomorphism of towers induces Frobenius-equivariant
isomorphisms of the rational cohomology groups. -/
theorem LAdicSheaf.compactSupportWeightLE_iff_of_padicTowerIso {X : B.Scheme} [IsNoetherian X.1]
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    {F F' : LAdicSheaf.{u, u + 1} B X ℓ}
    (e : LAdicSheaf.padicTower B X ℓ F ≅ LAdicSheaf.padicTower B X ℓ F')
    (hfin : LAdicSheaf.HasFiniteCompactSupportCohomology B ℓ kbar X f) (w : ℤ) :
    LAdicSheaf.CompactSupportWeightLE B ℓ kbar p q hcard ι X f F w ↔
      LAdicSheaf.CompactSupportWeightLE B ℓ kbar p q hcard ι X f F' w := by
  have key : ∀ {F F' : LAdicSheaf.{u, u + 1} B X ℓ}
      (e : LAdicSheaf.padicTower B X ℓ F ≅ LAdicSheaf.padicTower B X ℓ F'),
      LAdicSheaf.CompactSupportWeightLE B ℓ kbar p q hcard ι X f F w →
        LAdicSheaf.CompactSupportWeightLE B ℓ kbar p q hcard ι X f F' w := by
    intro F F' e hF j i _
    have hfd : ∀ G : LAdicSheaf.{u, u + 1} B X ℓ, FiniteDimensional ℚ_[ℓ]
        ((rationalLim.{u + 1} (ℓ := ℓ)).obj
          (LAdicSheaf.padicTower B X ℓ G ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i)) :=
      fun G => finiteDimensional_rationalLim_of_iso.{u + 1} (hA := (hfin j G i).1)
        (LAdicSheaf.padicTowerCohomologyIso B X ℓ f j kbar G i).symm
    have := (hfin j F i).1
    have h := hF j i
    rw [LAdicSheaf.isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_iff]
      at h ⊢
    refine (isCharpolyNormMixedOfWeightLE_rationalLimMap_iff_of_iso.{u + 1}
      (Functor.isoWhiskerRight e (compactSupportSheafCohomology ℤ_[ℓ] f j kbar i)) _ _ ?_
      (hA := hfd F) (hA' := hfd F')).1 h
    exact NatTrans.ext <| funext fun n =>
      ((compactSupportSheafFrobenius ℤ_[ℓ] f j kbar p q hcard i).naturality (e.hom.app n)).symm
  exact ⟨key e, key e.symm⟩

/-- **The towers of two iterated inverse images along equal composites are isomorphic.** -/
def LAdicSheaf.padicTowerInverseImageCompIso {X Y Z : B.Scheme} [IsNoetherian X.1]
    [IsNoetherian Y.1] [IsNoetherian Z.1] (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (h : a ≫ b = c)
    (F : LAdicSheaf.{u, u + 1} B Z ℓ) :
    LAdicSheaf.padicTower B X ℓ (LAdicSheaf.inverseImage a (LAdicSheaf.inverseImage b F)) ≅
      LAdicSheaf.padicTower B X ℓ (LAdicSheaf.inverseImage c F) :=
  (LAdicSheaf.padicTowerInverseImageIso B ℓ a (LAdicSheaf.inverseImage b F)).symm ≪≫
    Functor.isoWhiskerRight (LAdicSheaf.padicTowerInverseImageIso B ℓ b F).symm
      (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map a)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (LAdicSheaf.padicTower B Z ℓ F)
      ((etaleModuleInverseImageCompIso.{u, 0} ℤ_[ℓ] (B.inclusion.map a)
        (B.inclusion.map b)).symm ≪≫
        eqToIso (congrArg (etaleModuleInverseImage.{u, 0} ℤ_[ℓ])
          (by rw [← h, Functor.map_comp]))) ≪≫
    LAdicSheaf.padicTowerInverseImageIso B ℓ c F

/-- **Excision for the weight bound of one sheaf**: for `X = U ⊔ Z` with `U` open and `Z` closed,
the weight bound for `F|_U` and for `F|_Z` gives the weight bound for `F`, given the finiteness of
the cohomology of `U` and `Z`. -/
theorem LAdicSheaf.compactSupportWeightLE_of_openClosed {X : B.Scheme} [IsNoetherian X.1]
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    {U Z : B.Scheme} [IsNoetherian U.1] [IsNoetherian Z.1] (jU : U ⟶ X) (iZ : Z ⟶ X)
    [IsOpenImmersion (B.inclusion.map jU)] [IsClosedImmersion (B.inclusion.map iZ)]
    [QuasiCompact (B.inclusion.map jU ≫ f)]
    (hij : Set.range (B.inclusion.map jU).base = (Set.range (B.inclusion.map iZ).base)ᶜ)
    (hfinU : LAdicSheaf.HasFiniteCompactSupportCohomology B ℓ kbar U (B.inclusion.map jU ≫ f))
    (hfinZ : LAdicSheaf.HasFiniteCompactSupportCohomology B ℓ kbar Z (B.inclusion.map iZ ≫ f))
    {F : LAdicSheaf.{u, u + 1} B X ℓ} {w : ℤ}
    (hU : LAdicSheaf.CompactSupportWeightLE B ℓ kbar p q hcard ι U (B.inclusion.map jU ≫ f)
      (LAdicSheaf.inverseImage jU F) w)
    (hZ : LAdicSheaf.CompactSupportWeightLE B ℓ kbar p q hcard ι Z (B.inclusion.map iZ ≫ f)
      (LAdicSheaf.inverseImage iZ F) w) :
    LAdicSheaf.CompactSupportWeightLE B ℓ kbar p q hcard ι X f F w := by
  intro j i _
  set jU' := B.inclusion.map jU
  set iZ' := B.inclusion.map iZ
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
    B ℓ f j kbar p q hcard F i jU iZ hij hfin (hU (j.restrictOpen jU') i)
    (hZ (j.restrictClosed iZ') i)

/-- **The weight bound for one sheaf along a surjective closed immersion**: if `Z ⟶ X` is a
surjective closed immersion, the weight bound for `F|_Z` gives the weight bound for `F`, given the
finite dimensionality of the cohomology of `Z`. -/
theorem LAdicSheaf.compactSupportWeightLE_of_surjective {X : B.Scheme} [IsNoetherian X.1]
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    {Z : B.Scheme} [IsNoetherian Z.1] (iZ : Z ⟶ X) [IsClosedImmersion (B.inclusion.map iZ)]
    (hsurj : Function.Surjective (B.inclusion.map iZ).base)
    (hfinZ : LAdicSheaf.HasFiniteCompactSupportCohomology B ℓ kbar Z (B.inclusion.map iZ ≫ f))
    {F : LAdicSheaf.{u, u + 1} B X ℓ} {w : ℤ}
    (hZ : LAdicSheaf.CompactSupportWeightLE B ℓ kbar p q hcard ι Z (B.inclusion.map iZ ≫ f)
      (LAdicSheaf.inverseImage iZ F) w) :
    LAdicSheaf.CompactSupportWeightLE B ℓ kbar p q hcard ι X f F w := by
  intro j i _
  have := (hfinZ (j.restrictClosed (B.inclusion.map iZ)) (LAdicSheaf.inverseImage iZ F) i).1
  exact isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_of_surjective
    B ℓ f j kbar p q hcard F i iZ hsurj (hZ (j.restrictClosed (B.inclusion.map iZ)) i)

/-- **Noetherian induction for the weight bound, with a good open depending on the sheaf.**  If
for every nonempty closed subscheme `Z` of `X` and every lisse, pointwise mixed, realizable sheaf
`G` on `Z` there is a nonempty open subscheme `U` of `Z` on which `G` satisfies the weight bound,
then `X` satisfies the weight bound, given the finiteness of compactly supported cohomology. -/
theorem LAdicSheaf.satisfiesWeightBound_of_forall_exists_open_compactSupportWeightLE
    (X : B.Scheme) [IsNoetherian X.1]
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (hfin : ∀ (Y : B.Scheme) [IsNoetherian Y.1] (g : Y.1 ⟶ Spec (.of k)) [LocallyOfFiniteType g]
      [QuasiCompact g] [IsSeparated g], topologicalKrullDim Y.1 ≤ topologicalKrullDim X.1 →
        LAdicSheaf.HasFiniteCompactSupportCohomology B ℓ kbar Y g)
    (hloc : ∀ (Z : B.Scheme) [IsNoetherian Z.1] (iZ : Z ⟶ X)
        [IsClosedImmersion (B.inclusion.map iZ)],
      Nonempty Z.1 → ∀ (G : LAdicSheaf.{u, u + 1} B Z ℓ) (w : ℤ), G.IsLisse →
        LAdicSheaf.IsPointwiseMixedOfWeightLE B Z ℓ (B.inclusion.map iZ ≫ f) G (p ^ q) ι w →
        LAdicSheaf.IsIotaRealizable B Z ℓ (B.inclusion.map iZ ≫ f) G ι →
        ∃ (U : B.Scheme) (_ : IsNoetherian U.1) (jU : U ⟶ Z)
          (_ : IsOpenImmersion (B.inclusion.map jU))
          (_ : QuasiCompact (B.inclusion.map jU ≫ B.inclusion.map iZ ≫ f)), Nonempty U.1 ∧
          LAdicSheaf.CompactSupportWeightLE B ℓ kbar p q hcard ι U
            (B.inclusion.map jU ≫ B.inclusion.map iZ ≫ f) (LAdicSheaf.inverseImage jU G) w) :
    LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι X f := by
  suffices H : ∀ (C : TopologicalSpace.Closeds X.1) (Z : B.Scheme) [IsNoetherian Z.1]
      (iZ : Z ⟶ X) [IsClosedImmersion (B.inclusion.map iZ)],
      Set.range (B.inclusion.map iZ).base = (C : Set X.1) →
      ∀ (fZ : Z.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fZ] [QuasiCompact fZ] [IsSeparated fZ],
      fZ = B.inclusion.map iZ ≫ f → ∀ (G : LAdicSheaf.{u, u + 1} B Z ℓ) (w : ℤ), G.IsLisse →
        LAdicSheaf.IsPointwiseMixedOfWeightLE B Z ℓ fZ G (p ^ q) ι w →
        LAdicSheaf.IsIotaRealizable B Z ℓ fZ G ι →
        LAdicSheaf.CompactSupportWeightLE B ℓ kbar p q hcard ι Z fZ G w by
    have : IsClosedImmersion (B.inclusion.map (𝟙 X)) := by
      rw [CategoryTheory.Functor.map_id]
      infer_instance
    exact (LAdicSheaf.satisfiesWeightBound_iff_forall_compactSupportWeightLE X f).2
      (H ⊤ X (𝟙 X) (by rw [CategoryTheory.Functor.map_id]; exact Set.range_id) f (by simp))
  intro C
  induction C using WellFoundedLT.induction with
  | _ C ih =>
  intro Z _ iZ _ hC fZ _ _ _ hfZ G w hl hm hr
  subst hfZ
  set iZ' := B.inclusion.map iZ
  rcases isEmpty_or_nonempty Z.1 with hZ | hZ
  · exact fun j i _ =>
      isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_of_isEmpty
        B ℓ _ j kbar p q hcard G i
  obtain ⟨U, _, jU, _, _, hUne, hUw⟩ := hloc Z iZ hZ G w hl hm hr
  set jU' := B.inclusion.map jU
  -- the complement of `U` in `Z`, with its reduced structure
  let C' : TopologicalSpace.Closeds Z.1 :=
    ⟨(Set.range jU'.base)ᶜ, jU'.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let I := Scheme.IdealSheafData.vanishingIdeal C'
  have hZ'B : B.Contains I.subscheme :=
    Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit I.subschemeι Z.property
  let Z' : B.Scheme := B.obj I.subscheme hZ'B
  let iZZ' : Z' ⟶ Z := ObjectProperty.homMk I.subschemeι
  have hIc : IsClosedImmersion I.subschemeι := inferInstance
  have : IsClosedImmersion (B.inclusion.map iZZ') := hIc
  have hZl : IsLocallyNoetherian Z.1 := ‹AlgebraicGeometry.IsNoetherian Z.1›.toIsLocallyNoetherian
  have hIl : IsLocallyNoetherian I.subscheme :=
    @isLocallyNoetherian_of_isClosedImmersion _ _ I.subschemeι hIc hZl
  have hIq : CompactSpace I.subscheme := I.subschemeι.isClosedEmbedding.compactSpace
  have hIn : IsNoetherian I.subscheme := { }
  have : IsNoetherian Z'.1 := hIn
  have hrange : Set.range (B.inclusion.map iZZ').base = (Set.range jU'.base)ᶜ := by
    change Set.range I.subschemeι.base = _
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
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
  have hgZ' : ∀ y : closedPoints Z'.1, (B.inclusion.map iZZ').base y.1 ∈ closedPoints Z.1 :=
    mem_closedPoints_of_isClosedImmersion (B.inclusion.map iZZ')
  have hZ'w := ih _ hlt Z' (iZZ' ≫ iZ) rfl (B.inclusion.map iZZ' ≫ iZ' ≫ f)
    (by rw [CategoryTheory.Functor.map_comp, Category.assoc]) (LAdicSheaf.inverseImage iZZ' G) w
    (hl.inverseImage iZZ') (LAdicSheaf.IsPointwiseMixedOfWeightLE.inverseImage Z ℓ iZZ' _ hm hgZ')
    (LAdicSheaf.IsIotaRealizable.inverseImage ℓ _ iZZ' hr hgZ')
  have hdZ : topologicalKrullDim Z.1 ≤ topologicalKrullDim X.1 :=
    iZ'.isClosedEmbedding.isInducing.topologicalKrullDim_le
  exact LAdicSheaf.compactSupportWeightLE_of_openClosed (iZ' ≫ f) jU iZZ'
    (by rw [hrange, compl_compl])
    (hfin U _ (jU'.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hdZ))
    (hfin Z' _
      ((B.inclusion.map iZZ').isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdZ))
    hUw hZ'w

end Stacks.EtaleCohomology
