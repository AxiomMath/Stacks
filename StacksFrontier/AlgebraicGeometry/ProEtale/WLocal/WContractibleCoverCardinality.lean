module

public import Mathlib.RingTheory.Spectrum.Maximal.Localization
public import Mathlib.SetTheory.Cardinal.Finite
public import StacksFrontier.Topology.ExtremallyDisconnected.Cover
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtaleConstruction.IteratedColimit
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtaleConstruction.StrictlyHenselianFromRetractions
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.AlgebraicResidueExtension
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.AlgebraicResidueExtensionWLocal
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationColimitCardinality
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationColimitIndZariski
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationLimitClosedPoints
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.WContractibleCover
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.RingTheory.WeaklyEtale.ResidueField
public import StacksCore.Tactic.StacksAttribute

/-!
# Cardinality of a w-contractible cover

A ring `A` of cardinality at most an infinite cardinal `κ` has a faithfully flat ind-étale
w-contractible extension of cardinality at most `κ ^ (2 ^ (2 ^ (2 ^ κ)))`.

The bound tracks the construction of the cover. The w-localization `A → A_w` does not increase
cardinality beyond `κ`, nor does the extension `A_w → C'` splitting faithfully flat étale
algebras, nor the w-local ind-Zariski extension `C' → C` along the closed points: the latter
leaves the quotient by the ideal cutting out those closed points unchanged, so the closed points
of `Spec C` inject into the ideals of a ring of cardinality at most `κ` and there are at most
`2 ^ κ` of them. The space `π₀(Spec C)` has the same cardinality as that set of closed points,
and is covered by the space `T` of ultrafilters on it, which is extremally disconnected and of
cardinality at most `2 ^ (2 ^ (2 ^ κ))`. Finally `Spec D` is the fibre product
`Spec C ×_{π₀(Spec C)} T`, so a maximal ideal of `D` is determined by a closed point of `Spec C`
and a point of `T`, and `D` embeds into the product of its localizations at maximal ideals, each
of which is a localization of `C'` and hence of cardinality at most `κ`.

## Main results

* `AlgebraicGeometry.ProEtale.exists_small_faithfullyFlat_ind_etale_wContractible`: the bounded
  w-contractible cover.

## Implementation notes

The cover is the one of Tag 0983; the intermediate cardinality estimates are part of the
construction of the bounded witness rather than extra properties of the result, so the
construction is carried out again here with the estimates attached, in two stages: the extension
`A → C` with w-local spectrum and strictly henselian local rings, and the ind-Zariski extension
`C → D` making `π₀` extremally disconnected.

## References

* [Stacks Project, Tag 0984](https://stacks.math.columbia.edu/tag/0984)
-/

@[expose] public noncomputable section

open Cardinal CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

universe u

/-- The ideals of a ring are no more numerous than its subsets. -/
private theorem mk_ideal_le_powerset {R : Type u} [Semiring R] :
    Cardinal.mk (Ideal R) ≤ (2 : Cardinal.{u}) ^ Cardinal.mk R :=
  calc
    Cardinal.mk (Ideal R) ≤ Cardinal.mk (Set R) :=
      Cardinal.mk_le_of_injective (f := fun I : Ideal R => (I : Set R))
        fun _ _ h => Ideal.ext (Set.ext_iff.mp h)
    _ = (2 : Cardinal.{u}) ^ Cardinal.mk R := Cardinal.mk_set

/-- An element of a commutative ring is determined by the family of its images in the
localizations at the maximal ideals: an element killed by every such map is annihilated by an
ideal meeting every maximal ideal, hence by a unit. -/
private theorem algebraMap_maximalSpectrum_injective (R : Type u) [CommRing R] :
    Function.Injective fun x : R => fun m : MaximalSpectrum R =>
      algebraMap R (Localization.AtPrime m.asIdeal) x := by
  classical
  intro x y hxy
  by_contra hne
  have hxy' : x - y ≠ 0 := sub_ne_zero.mpr hne
  let J : Ideal R := (Submodule.span R ({x - y} : Set R)).annihilator
  have hJ : J ≠ ⊤ := by
    intro htop
    have hone : (1 : R) ∈ J := by rw [htop]; trivial
    have hmul := (Submodule.mem_annihilator_span_singleton (x - y) 1).mp hone
    exact hxy' (by simpa using hmul)
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
  have : m.IsMaximal := hm
  have hloc : algebraMap R (Localization.AtPrime m) (x - y) = 0 := by
    have hh : algebraMap R (Localization.AtPrime m) x =
        algebraMap R (Localization.AtPrime m) y :=
      congrFun hxy (⟨m, hm⟩ : MaximalSpectrum R)
    rw [map_sub, hh, sub_self]
  obtain ⟨s, hs⟩ :=
    (IsLocalization.map_eq_zero_iff m.primeCompl (Localization.AtPrime m) (x - y)).mp hloc
  have hsJ : (s : R) ∈ J := by
    rw [Submodule.mem_annihilator_span_singleton]
    simpa [smul_eq_mul, mul_comm] using hs
  exact s.2 (hJm hsJ)

/-- A commutative ring whose localizations at maximal ideals all have cardinality at most `κ` has
cardinality at most `κ` raised to the number of its maximal ideals. -/
private theorem mk_le_power_mk_maximalSpectrum {R : Type u} [CommRing R] (κ : Cardinal.{u})
    (hLoc : ∀ m : MaximalSpectrum R, Cardinal.mk (Localization.AtPrime m.asIdeal) ≤ κ) :
    Cardinal.mk R ≤ κ ^ Cardinal.mk (MaximalSpectrum R) := by
  classical
  calc
    Cardinal.mk R ≤ Cardinal.mk ((m : MaximalSpectrum R) → Localization.AtPrime m.asIdeal) :=
      Cardinal.mk_le_of_injective (algebraMap_maximalSpectrum_injective R)
    _ = Cardinal.prod fun m : MaximalSpectrum R =>
        Cardinal.mk (Localization.AtPrime m.asIdeal) := by rw [Cardinal.mk_pi]
    _ ≤ Cardinal.prod fun _ : MaximalSpectrum R => κ := Cardinal.prod_le_prod _ _ hLoc
    _ = κ ^ Cardinal.mk (MaximalSpectrum R) := by rw [Cardinal.prod_const']

/-- The w-localization of Tag 0975 of a ring of cardinality at most `κ`: a faithfully flat
ind-Zariski extension with w-local spectrum and cardinality at most `κ`. -/
private theorem exists_wLocalization_le (A : Type u) [CommRing A] (κ : Cardinal.{u})
    (hκ : ℵ₀ ≤ κ) (hA : Cardinal.mk A ≤ κ) :
    ∃ (Aw : Type u) (_ : CommRing Aw) (_ : Algebra A Aw),
      (algebraMap A Aw).FaithfullyFlat ∧
        IsIndZariski.{u, u, u} A Aw ∧
          WLocalSpace (PrimeSpectrum Aw) ∧ Cardinal.mk Aw ≤ κ := by
  refine ⟨stratificationColimitRing (A := A), inferInstance, inferInstance, ?_,
    stratificationColimit_isIndZariski (A := A), stratificationLimitScheme_wLocal (A := A),
    mk_stratificationColimitRing_le (A := A) κ hκ hA⟩
  have hmap : algebraMap A (stratificationColimitRing (A := A)) =
      stratificationColimitAlgebraMap (A := A) := RingHom.algebraMap_toAlgebra _
  exact hmap ▸ stratificationColimit_faithfullyFlat (A := A)

/-- The first stage of the bounded w-contractible cover of a ring `A` of cardinality at most an
infinite `κ`: a faithfully flat ind-étale extension `A → C` whose spectrum is w-local, whose
local rings at maximal ideals are strictly henselian, which has at most `2 ^ κ` closed points,
and all of whose localizations at primes have cardinality at most `κ`.

The extension is the composite `A → A_w → C' → C` of the w-localization of Tag 0975, the
extension of Tag 097S splitting faithfully flat étale algebras, and the w-local ind-Zariski
extension of Tag 097A along the closed points of `Spec A_w`. -/
private theorem exists_wLocal_strictlyHenselian_extension_le (A : Type u) [CommRing A]
    (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hA : Cardinal.mk A ≤ κ) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
      (algebraMap A C).FaithfullyFlat ∧
        StacksDraft.IndEtale A C ∧
          WLocalSpace (PrimeSpectrum C) ∧
            (∀ (m : Ideal C) [m.IsMaximal],
              StrictlyHenselianLocalRing (Localization.AtPrime m)) ∧
              Cardinal.mk (closedPoints (PrimeSpectrum C)) ≤ (2 : Cardinal.{u}) ^ κ ∧
                ∀ (q : Ideal C) [q.IsPrime], Cardinal.mk (Localization.AtPrime q) ≤ κ := by
  classical
  obtain ⟨Aw, hAwR, algAAw, hAwff, hAwIndZ, hAwW, hAwCard⟩ := exists_wLocalization_le A κ hκ hA
  let : CommRing Aw := hAwR
  let : Algebra A Aw := algAAw
  let : WLocalSpace (PrimeSpectrum Aw) := hAwW
  obtain ⟨C', hC'R, algAwC', hC'card, hC'ff, hC'ind, hC'splits⟩ :=
    exists_small_faithfullyFlat_ind_etale_algebra_splitting_etale Aw κ hκ hAwCard
  let : CommRing C' := hC'R
  let : Algebra Aw C' := algAwC'
  have hAwC'indEtale : StacksDraft.IndEtale Aw C' := indEtale_of_indEtaleUnder Aw C' hC'ind
  have hAwC'weak : Algebra.WeaklyEtale Aw C' := Algebra.weaklyEtale_of_ind_etale hAwC'indEtale
  have hres : ∀ q : Ideal C', ∀ [q.IsPrime],
      let := (Ideal.ResidueField.map (q.comap (algebraMap Aw C')) q
        (algebraMap Aw C') rfl).toAlgebra
      Algebra.IsAlgebraic (q.comap (algebraMap Aw C')).ResidueField q.ResidueField :=
    fun q _ => (isSeparable_and_isAlgebraic_residueField_of_weaklyEtale Aw C' hAwC'weak
      (q.comap (algebraMap Aw C')) q rfl).2
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp
    (WLocalSpace.isClosed_closedPoints (X := PrimeSpectrum Aw))
  have hIbase : PrimeSpectrum.zeroLocus (I : Set Aw) = closedPoints (PrimeSpectrum Aw) := hI.symm
  obtain ⟨C, hCR, algC'C, hCindZ, hCquot, hCw, -, hCclosed⟩ :=
    exists_isIndZariski_wLocal_of_isAlgebraic_residueField (algebraMap Aw C') I hIbase hres
  let : CommRing C := hCR
  let : Algebra C' C := algC'C
  let : Algebra Aw C := ((algebraMap C' C).comp (algebraMap Aw C')).toAlgebra
  let : IsScalarTower Aw C' C := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A C' := ((algebraMap Aw C').comp (algebraMap A Aw)).toAlgebra
  let : IsScalarTower A Aw C' := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A C := ((algebraMap Aw C).comp (algebraMap A Aw)).toAlgebra
  let : IsScalarTower A Aw C := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A C' C := IsScalarTower.of_algebraMap_eq' (RingHom.ext fun _ => rfl)
  let : WLocalSpace (PrimeSpectrum C) := hCw
  have hC'ident : Algebra.IdentifiesLocalRings C' C :=
    identifiesLocalRings_of_isIndZariski C' C hCindZ
  -- Faithful flatness of `A → C`.
  have hC'Cflat : (algebraMap C' C).Flat :=
    RingHom.flat_algebraMap_iff.mpr (flat_of_identifiesLocalRings C' C hC'ident)
  have hAwCflat : (algebraMap Aw C).Flat :=
    (RingHom.FaithfullyFlat.flat hC'ff).comp hC'Cflat
  have hAwCff : Module.FaithfullyFlat Aw C :=
    faithfullyFlat_of_quotient_bijective Aw C' C I hIbase
      (RingHom.faithfullyFlat_algebraMap_iff.mp hC'ff) hCquot
      (RingHom.flat_algebraMap_iff.mp hAwCflat)
  have hACff : (algebraMap A C).FaithfullyFlat :=
    RingHom.FaithfullyFlat.stableUnderComposition _ _ hAwff
      (RingHom.faithfullyFlat_algebraMap_iff.mpr hAwCff)
  -- Ind-étaleness of `A → C`.
  have hACindEtale : StacksDraft.IndEtale A C :=
    StacksDraft.indEtale_comp
      (StacksDraft.indEtale_comp (indEtale_of_isIndZariski A Aw hAwIndZ) hAwC'indEtale)
      (indEtale_of_isIndZariski C' C hCindZ)
  -- The ideal `I·C` and the closed points of `Spec C` above it.
  let I' : Ideal C' := Ideal.map (algebraMap Aw C') I
  let J : Ideal C := Ideal.map (algebraMap C' C) I'
  let mkJ : C →+* C ⧸ J := Ideal.Quotient.mk J
  have hquotCard : Cardinal.mk (C ⧸ J) ≤ κ := by
    calc
      Cardinal.mk (C ⧸ J) ≤ Cardinal.mk (C' ⧸ I') :=
        Cardinal.mk_le_of_injective (RingEquiv.ofBijective _ hCquot).symm.injective
      _ ≤ Cardinal.mk C' := Cardinal.mk_quotient_le
      _ ≤ κ := hC'card
  have hJle : ∀ p : PrimeSpectrum C, p ∈ closedPoints (PrimeSpectrum C) → J ≤ p.asIdeal := by
    intro p hp
    have hpAw : PrimeSpectrum.comap (algebraMap Aw C) p ∈ closedPoints (PrimeSpectrum Aw) := by
      rw [hCclosed] at hp
      exact hp
    have hpI : I ≤ (PrimeSpectrum.comap (algebraMap Aw C) p).asIdeal := by
      rw [← hIbase] at hpAw
      exact hpAw
    refine Ideal.map_le_iff_le_comap.mpr (Ideal.map_le_iff_le_comap.mpr ?_)
    rw [Ideal.comap_comap]
    exact hpI
  have hclosedCCard :
      Cardinal.mk (closedPoints (PrimeSpectrum C)) ≤ (2 : Cardinal.{u}) ^ κ := by
    have henc : Function.Injective fun p : closedPoints (PrimeSpectrum C) =>
        Ideal.map mkJ p.1.asIdeal := by
      intro p q hpq
      refine Subtype.ext (PrimeSpectrum.ext ?_)
      calc p.1.asIdeal = Ideal.comap mkJ (Ideal.map mkJ p.1.asIdeal) :=
            (Ideal.comap_map_mk (hJle p.1 p.2)).symm
        _ = Ideal.comap mkJ (Ideal.map mkJ q.1.asIdeal) := congrArg (Ideal.comap mkJ) hpq
        _ = q.1.asIdeal := Ideal.comap_map_mk (hJle q.1 q.2)
    calc
      Cardinal.mk (closedPoints (PrimeSpectrum C)) ≤ Cardinal.mk (Ideal (C ⧸ J)) :=
        Cardinal.mk_le_of_injective henc
      _ ≤ (2 : Cardinal.{u}) ^ Cardinal.mk (C ⧸ J) := mk_ideal_le_powerset
      _ ≤ (2 : Cardinal.{u}) ^ κ := Cardinal.power_le_power_left two_ne_zero hquotCard
  -- Strict henselianity at the maximal ideals of `C`.
  have hCstrict : ∀ (m : Ideal C) [m.IsMaximal],
      StrictlyHenselianLocalRing (Localization.AtPrime m) := by
    intro m hm
    have : m.IsMaximal := hm
    let p : PrimeSpectrum C := ⟨m, hm.isPrime⟩
    have hJm : J ≤ m :=
      hJle p (mem_closedPoints_iff.mpr ((PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mpr hm))
    have hq'prime : (m.comap (algebraMap C' C)).IsPrime := Ideal.IsPrime.comap (algebraMap C' C)
    have hq'closed : (⟨m.comap (algebraMap C' C), hq'prime⟩ : PrimeSpectrum C') ∈
        closedPoints (PrimeSpectrum C') :=
      closedPoints_of_mem_zeroLocus_map (algebraMap Aw C') I hIbase hres
        (Ideal.map_le_iff_le_comap.mp hJm)
    have hq'max : (m.comap (algebraMap C' C)).IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp (mem_closedPoints_iff.mp hq'closed)
    have : (m.comap (algebraMap C' C)).IsMaximal := hq'max
    have hsplit : ∀ (B : Type u) [CommRing B] [Algebra C' B] [Algebra.Etale C' B]
        [Module.FaithfullyFlat C' B], Nonempty (B →ₐ[C'] C') := fun B _ _ _ hBff =>
      hC'splits B (RingHom.faithfullyFlat_algebraMap_iff.mpr hBff) inferInstance
    let : StrictlyHenselianLocalRing (Localization.AtPrime (m.comap (algebraMap C' C))) :=
      localizationAtPrime_strictlyHenselian_of_etale_faithfullyFlat_retracts C' hsplit
        (m.comap (algebraMap C' C))
    exact strictlyHenselianLocalRing_of_ringEquiv
      (RingEquiv.ofBijective
        (Localization.localRingHom (m.comap (algebraMap C' C)) m (algebraMap C' C) rfl)
        (hC'ident m))
  -- The localizations of `C` are localizations of `C'`.
  have hCloc : ∀ (q : Ideal C) [q.IsPrime], Cardinal.mk (Localization.AtPrime q) ≤ κ := by
    intro q hq
    have : q.IsPrime := hq
    have : (q.comap (algebraMap C' C)).IsPrime := Ideal.IsPrime.comap (algebraMap C' C)
    calc
      Cardinal.mk (Localization.AtPrime q) =
          Cardinal.mk (Localization.AtPrime (q.comap (algebraMap C' C))) :=
        Cardinal.mk_congr (RingEquiv.ofBijective _ (hC'ident q)).toEquiv.symm
      _ ≤ max ℵ₀ (Cardinal.mk C') :=
        Cardinal.mk_le_of_isLocalization (R := C') (q.comap (algebraMap C' C)).primeCompl _
      _ ≤ κ := max_le hκ hC'card
  exact ⟨C, inferInstance, inferInstance, hACff, hACindEtale, hCw, hCstrict, hclosedCCard, hCloc⟩

/-- **Stacks 0984.** A ring of cardinality at most an infinite cardinal `κ` has a faithfully flat
ind-étale w-contractible extension of cardinality at most `κ ^ (2 ^ (2 ^ (2 ^ κ)))`. -/
@[stacks 0984]
theorem exists_small_faithfullyFlat_ind_etale_wContractible (A : Type u) [CommRing A]
    (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hA : Cardinal.mk A ≤ κ) :
    ∃ (D : Type u) (_ : CommRing D) (f : A →+* D),
      f.FaithfullyFlat ∧
        ObjectProperty.ind.{u}
          (fun C : Under (CommRingCat.of A) ↦ C.hom.hom.Etale)
          (Under.mk (CommRingCat.ofHom f)) ∧
        ProetaleWContractible.IsWContractible.{u, u} D ∧
        Cardinal.mk D ≤
          κ ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ))) := by
  classical
  obtain ⟨C, hCR, algAC, hACff, hACindEtale, hCw, hCstrict, hclosedCCard, hCloc⟩ :=
    exists_wLocal_strictlyHenselian_extension_le A κ hκ hA
  let : CommRing C := hCR
  let : Algebra A C := algAC
  let : WLocalSpace (PrimeSpectrum C) := hCw
  have : T2Space (ConnectedComponents (PrimeSpectrum C)) :=
    (connectedComponents_isProfinite (PrimeSpectrum C)).1
  have hXcard : Cardinal.mk (ConnectedComponents (PrimeSpectrum C)) ≤ (2 : Cardinal.{u}) ^ κ := by
    rw [← Cardinal.mk_congr
      (closedPointsHomeomorphConnectedComponents (PrimeSpectrum C)).toEquiv]
    exact hclosedCCard
  -- The ultrafilter space of `π₀(Spec C)` is an extremally disconnected cover of it.
  let T := Ultrafilter (ConnectedComponents (PrimeSpectrum C))
  have hTproj : CompactT2.Projective T := ultrafilter_projective _
  let : ExtremallyDisconnected T := hTproj.extremallyDisconnected
  let π : T → ConnectedComponents (PrimeSpectrum C) := Ultrafilter.extend id
  have hπcont : Continuous π := continuous_ultrafilter_extend id
  have hπsurj : Function.Surjective π := fun x => ⟨pure x, by simp [π]⟩
  have hTprof : IsProfiniteStacks T :=
    (isProfiniteStacks_iff_compact_t2_totallyDisconnected T).2
      ⟨inferInstance, inferInstance, inferInstance⟩
  have hTcard : Cardinal.mk T ≤
      (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ)) := by
    have hUF : Cardinal.mk T ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^
        Cardinal.mk (ConnectedComponents (PrimeSpectrum C))) := by
      calc
        Cardinal.mk T ≤ Cardinal.mk (Filter (ConnectedComponents (PrimeSpectrum C))) :=
          Cardinal.mk_le_of_injective (f := fun U : T => (U : Filter _))
            Ultrafilter.coe_injective
        _ ≤ Cardinal.mk (Set (Set (ConnectedComponents (PrimeSpectrum C)))) :=
          Cardinal.mk_le_of_injective (f := fun F : Filter _ => F.sets)
            fun _ _ h => Filter.ext fun s =>
              Iff.of_eq (congrArg (fun V : Set (Set _) => s ∈ V) h)
        _ = (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^
            Cardinal.mk (ConnectedComponents (PrimeSpectrum C))) := by
          rw [Cardinal.mk_set, Cardinal.mk_set]
    exact hUF.trans (Cardinal.power_le_power_left two_ne_zero
      (Cardinal.power_le_power_left two_ne_zero hXcard))
  -- Realize the cover by an ind-Zariski extension `C → D`.
  obtain ⟨D, hDR, algCD, g, hCDff, hCDind, hDw, ⟨eT⟩, hDclosed, hDinj⟩ :=
    exists_indZariski_wLocal_of_profinite_component_cover C T hTprof ⟨π, hπcont⟩ hπsurj
  let : CommRing D := hDR
  let : Algebra C D := algCD
  let : Algebra A D := ((algebraMap C D).comp (algebraMap A C)).toAlgebra
  let : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq' rfl
  have hDident : Algebra.IdentifiesLocalRings C D := identifiesLocalRings_of_isIndZariski C D hCDind
  have hADff : (algebraMap A D).FaithfullyFlat :=
    RingHom.FaithfullyFlat.stableUnderComposition _ _ hACff hCDff
  have hADindEtale : StacksDraft.IndEtale A D :=
    StacksDraft.indEtale_comp hACindEtale (indEtale_of_isIndZariski C D hCDind)
  have hDstrict : ∀ (m : Ideal D) [m.IsMaximal],
      StrictlyHenselianLocalRing (Localization.AtPrime m) := fun m _ =>
    strictlyHenselianLocalRing_of_isIndZariski_of_closedPoints C D hCDind hDclosed.subset
      hCstrict m
  have hDED : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum D)) :=
    extremallyDisconnected_of_homeo eT.symm
  -- The maximal ideals of `D` are indexed by closed points of `Spec C` and points of `T`.
  have hmaxD : Cardinal.mk (MaximalSpectrum D) ≤
      Cardinal.mk (closedPoints (PrimeSpectrum C)) * Cardinal.mk T := by
    have hclosedOf (m : MaximalSpectrum D) :
        PrimeSpectrum.comap (algebraMap C D) m.toPrimeSpectrum ∈
          closedPoints (PrimeSpectrum C) :=
      hDclosed.subset (mem_closedPoints_iff.mpr
        ((PrimeSpectrum.isClosed_singleton_iff_isMaximal m.toPrimeSpectrum).mpr m.2))
    refine Cardinal.mk_le_of_injective (f := fun m : MaximalSpectrum D =>
      ((⟨PrimeSpectrum.comap (algebraMap C D) m.toPrimeSpectrum, hclosedOf m⟩ :
        closedPoints (PrimeSpectrum C)), g m.toPrimeSpectrum)) ?_
    intro m n hmn
    have h1 : PrimeSpectrum.comap (algebraMap C D) m.toPrimeSpectrum =
        PrimeSpectrum.comap (algebraMap C D) n.toPrimeSpectrum :=
      congrArg (fun z : closedPoints (PrimeSpectrum C) × T => z.1.1) hmn
    have h2 : g m.toPrimeSpectrum = g n.toPrimeSpectrum :=
      congrArg (fun z : closedPoints (PrimeSpectrum C) × T => z.2) hmn
    exact MaximalSpectrum.toPrimeSpectrum_injective (hDinj (Prod.ext h1 h2))
  have hDloc : ∀ m : MaximalSpectrum D, Cardinal.mk (Localization.AtPrime m.asIdeal) ≤ κ := by
    intro m
    have : m.asIdeal.IsPrime := m.2.isPrime
    have : (m.asIdeal.comap (algebraMap C D)).IsPrime := Ideal.IsPrime.comap (algebraMap C D)
    calc
      Cardinal.mk (Localization.AtPrime m.asIdeal) =
          Cardinal.mk (Localization.AtPrime (m.asIdeal.comap (algebraMap C D))) :=
        Cardinal.mk_congr (RingEquiv.ofBijective _ (hDident m.asIdeal)).toEquiv.symm
      _ ≤ κ := hCloc (m.asIdeal.comap (algebraMap C D))
  -- Assemble the bound.
  have hκle2κ : κ ≤ (2 : Cardinal.{u}) ^ κ := (Cardinal.cantor κ).le
  have hκle2pow2κ : κ ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ) :=
    hκle2κ.trans (Cardinal.power_le_power_left two_ne_zero hκle2κ)
  have htwoκleBound : (2 : Cardinal.{u}) ^ κ ≤
      (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ)) :=
    Cardinal.power_le_power_left two_ne_zero hκle2pow2κ
  have hBoundInf : ℵ₀ ≤
      (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ)) :=
    hκ.trans (hκle2κ.trans htwoκleBound)
  have hmaxDle : Cardinal.mk (MaximalSpectrum D) ≤
      (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ)) :=
    hmaxD.trans ((mul_le_mul' (hclosedCCard.trans htwoκleBound) hTcard).trans
      (Cardinal.mul_eq_self hBoundInf).le)
  have hDcard : Cardinal.mk D ≤
      κ ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ))) :=
    (mk_le_power_mk_maximalSpectrum κ hDloc).trans
      (Cardinal.power_le_power_left
        (ne_of_gt (lt_of_lt_of_le Cardinal.aleph0_pos hκ)) hmaxDle)
  have hDprops : WLocalSpace (PrimeSpectrum D) ∧
      ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum D)) ∧
        ∀ (m : Ideal D) [m.IsMaximal],
          StrictlyHenselianLocalRing (Localization.AtPrime m) :=
    ⟨hDw, hDED, hDstrict⟩
  exact ⟨D, inferInstance, algebraMap A D, hADff,
    indEtaleUnder_of_indEtale A D hADindEtale,
    ((wContractible_tfae D).out 3 1).mp hDprops, hDcard⟩

end AlgebraicGeometry.ProEtale

end
