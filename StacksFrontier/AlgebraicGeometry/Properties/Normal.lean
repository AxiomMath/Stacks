module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FunctionField.SectionsIntersectionStalks
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.IntegrallyClosed.ProductOfDomains

/-!
# Normal schemes

A scheme is normal when each of its local rings is a normal domain. Normality can be checked on
affine opens: it holds exactly when the ring of sections on every affine open is a normal ring,
or on one affine open covering, or on some open covering by normal open subschemes. Normal
schemes are reduced, their open subschemes are normal, and for an integral scheme the condition
reduces to normality of the section ring of each nonempty affine open.

The ring of global sections of an integral normal scheme is a normal domain, and a scheme whose
quasi-compact opens have finitely many irreducible components is normal exactly when it
decomposes as a disjoint union of normal integral schemes.

## Main definitions

* `AlgebraicGeometry.IsNormal` is the predicate that every stalk of the structure sheaf is a
  normal domain.

## Main results

* `AlgebraicGeometry.isNormal_iff_stalk_normal` characterizes normal schemes stalkwise.
* `AlgebraicGeometry.isNormal_tfae` gives the four equivalent local criteria.
* `AlgebraicGeometry.isNormal_open` makes every open subscheme of a normal scheme normal.
* `AlgebraicGeometry.isReduced_of_isNormal` supplies reducedness for a normal scheme.
* `AlgebraicGeometry.isNormal_iff_forall_affineOpen_normal` treats the integral case.
* `AlgebraicGeometry.normal_globalSections`: the global sections of an integral normal scheme
  form a normal domain.
* `AlgebraicGeometry.component_eq_of_open_irreducible_nhd`: two irreducible components meeting
  one irreducible open set are equal.
* `AlgebraicGeometry.isNormal_of_openCover`: normality is local on an open cover.
* `AlgebraicGeometry.isNormal_iff_exists_iso_coproduct` is the decomposition into normal
  integral schemes.
* `AlgebraicGeometry.isNormal_sigma`: a coproduct of normal schemes is normal.

## Implementation notes

Normality is a typeclass, as are the analogous scheme properties in Mathlib, and the domain
structure of each stalk is registered as an instance. Normality of that domain is expressed using
`IsIntegrallyClosed`, the definition of a normal domain from Stacks Project Tag 0309. The
characterizing equivalence supports construction from stalkwise witnesses, projection back to
those witnesses, and rewriting of scheme normality into its pointwise form.

The entries of `isNormal_tfae` follow the order of the source: an affine open is an element of
`Scheme.affineOpens`, an open subscheme is `U.toScheme`, covers are families of opens satisfying
`IsOpenCover`, and the ring condition is `IsNormalRing`. For a nonempty open of an
integral scheme the domain structure on its ring of sections is the canonical one supplied by
integrality, so the affine-open condition only needs to assert `IsIntegrallyClosed` with respect
to that structure. A disjoint-union decomposition is represented by an isomorphism from the
scheme to the categorical coproduct of a family of schemes, with the normality and integrality
assumptions on the members bundled as instance-valued witnesses.

## References

* [Stacks Project, Tag 033I](https://stacks.math.columbia.edu/tag/033I)
* [Stacks Project, Tag 033J](https://stacks.math.columbia.edu/tag/033J)
* [Stacks Project, Tag 033K](https://stacks.math.columbia.edu/tag/033K)
* [Stacks Project, Tag 033L](https://stacks.math.columbia.edu/tag/033L)
* [Stacks Project, Tag 0357](https://stacks.math.columbia.edu/tag/0357)
* [Stacks Project, Tag 0358](https://stacks.math.columbia.edu/tag/0358)
* [Grothendieck and Dieudonné, *Éléments de géométrie algébrique*][EGA], 0, 4.1.4
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A scheme is normal if each stalk of its structure sheaf is a normal domain. -/
@[stacks 033I] class IsNormal (X : Scheme.{u}) : Prop where
  /-- Every local ring of a normal scheme is a domain. -/
  stalk_isDomain (x : X) : IsDomain (X.presheaf.stalk x)
  /-- Every local ring of a normal scheme is normal. -/
  stalk_normal (x : X) :
    IsIntegrallyClosed (X.presheaf.stalk x)

attribute [instance] IsNormal.stalk_isDomain

/-- A scheme is normal exactly when each stalk of its structure sheaf admits a domain structure
with respect to which it is normal. -/
@[simp] theorem isNormal_iff_stalk_normal (X : Scheme.{u}) :
    IsNormal X ↔
      ∀ x : X, ∃ _h : IsDomain (X.presheaf.stalk x),
        IsIntegrallyClosed (X.presheaf.stalk x) :=
  ⟨fun hX x ↦ ⟨hX.stalk_isDomain x, hX.stalk_normal x⟩,
    fun hX ↦ ⟨fun x ↦ (hX x).choose, fun x ↦ (hX x).choose_spec⟩⟩

/-- Being a normal domain transports along a ring isomorphism. -/
private theorem normal_of_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (h : ∃ _ : IsDomain R, IsIntegrallyClosed R) :
    ∃ _ : IsDomain S, IsIntegrallyClosed S := by
  obtain ⟨_, _⟩ := h
  have : IsDomain S := Function.Injective.isDomain e.symm e.symm.injective
  exact ⟨inferInstance, .of_equiv e⟩

/-- The stalk at the point of an affine open corresponding to a prime ideal of its section ring is
the localization at that prime. -/
private theorem nonempty_localization_equiv_stalk {X : Scheme.{u}} (U : X.affineOpens)
    (y : PrimeSpectrum Γ(X, U)) (x : X) (hx : U.2.fromSpec y = x) :
    Nonempty (Localization.AtPrime y.asIdeal ≃+* X.presheaf.stalk x) := by
  subst hx
  let x' : U.1 := ⟨U.2.fromSpec y, (U.2.isoSpec.inv y).2⟩
  let : Algebra Γ(X, U) (X.presheaf.stalk x') :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf x'
  have : IsLocalization.AtPrime (X.presheaf.stalk x') y.asIdeal :=
    U.2.isLocalization_stalk' y x'.2
  exact ⟨(IsLocalization.algEquiv y.asIdeal.primeCompl _ _).toRingEquiv⟩

/-- Normality of the section ring of an affine open gives normality of the stalk at each of its
points. -/
private theorem normalStalk_of_normalAffineSections {X : Scheme.{u}}
    (U : X.affineOpens) (x : U.1)
    (hU : IsNormalRing Γ(X, U)) :
    ∃ _h : IsDomain (X.presheaf.stalk x),
      IsIntegrallyClosed (X.presheaf.stalk x) := by
  let y := U.2.primeIdealOf x
  have : y.asIdeal.IsPrime := y.isPrime
  obtain ⟨e⟩ := nonempty_localization_equiv_stalk U y x (U.2.fromSpec_primeIdealOf x)
  exact normal_of_equiv e ⟨(hU y.asIdeal).1, (hU y.asIdeal).2⟩

/-- A normal scheme has normal section ring on every affine open. -/
private theorem normalAffineSections_of_normal {X : Scheme.{u}}
    (hX : IsNormal X) (U : X.affineOpens) :
    IsNormalRing Γ(X, U) := by
  rw [isNormalRing_iff]
  intro p hp
  obtain ⟨e⟩ := nonempty_localization_equiv_stalk U ⟨p, hp⟩ _ rfl
  obtain ⟨hd, hc⟩ := normal_of_equiv e.symm ⟨hX.stalk_isDomain _, hX.stalk_normal _⟩
  exact ⟨hd, hc⟩

/-- Every open subscheme of a normal scheme is normal. -/
private theorem isNormal_open_of_isNormal {X : Scheme.{u}}
    (hX : IsNormal X) (U : X.Opens) :
    IsNormal U.toScheme :=
  (isNormal_iff_stalk_normal _).2 fun x => normal_of_equiv
    (U.stalkIso x).commRingCatIsoToRingEquiv.symm ⟨hX.stalk_isDomain x.1, hX.stalk_normal x.1⟩

/-- **Stacks Project, Tag 033J.** Normality of a scheme is equivalent to normality of the
section ring on every affine open, on one affine open covering, or to the existence of an
open covering by normal open subschemes. -/
@[stacks 033J "equivalent conditions"]
public theorem isNormal_tfae (X : Scheme.{u}) :
    List.TFAE [
      IsNormal X,
      ∀ U : X.affineOpens, IsNormalRing Γ(X, U),
      ∃ (I : Type u) (U : I → X.affineOpens),
        IsOpenCover (fun i ↦ (U i : X.Opens)) ∧
          ∀ i, IsNormalRing Γ(X, U i),
      ∃ (I : Type u) (U : I → X.Opens),
        IsOpenCover U ∧ ∀ i, IsNormal (U i).toScheme] := by
  classical
  tfae_have 1 → 2 := normalAffineSections_of_normal
  tfae_have 2 → 3 := fun hX => ⟨X.affineOpens, id, .mk (iSup_affineOpens_eq_top X), hX⟩
  tfae_have 3 → 1 := by
    rintro ⟨I, U, hU, hN⟩
    refine (isNormal_iff_stalk_normal X).2 fun x => ?_
    obtain ⟨i, hxi⟩ := hU.exists_mem x
    exact normalStalk_of_normalAffineSections (U i) ⟨x, hxi⟩ (hN i)
  tfae_have 1 → 4 := fun hX =>
    ⟨PUnit, fun _ => ⊤, .mk (by simp), fun _ => isNormal_open_of_isNormal hX ⊤⟩
  tfae_have 4 → 1 := by
    rintro ⟨I, U, hU, hN⟩
    refine (isNormal_iff_stalk_normal X).2 fun x => ?_
    obtain ⟨i, hxi⟩ := hU.exists_mem x
    let xi : U i := ⟨x, hxi⟩
    exact normal_of_equiv ((U i).stalkIso xi).commRingCatIsoToRingEquiv
      ((isNormal_iff_stalk_normal _).mp (hN i) xi)
  tfae_finish

/-- **Stacks Project, Tag 033J.** Every open subscheme of a normal scheme is normal. -/
@[stacks 033J "open subschemes"]
public instance isNormal_open {X : Scheme.{u}} [IsNormal X]
    (U : X.Opens) : IsNormal U.toScheme :=
  isNormal_open_of_isNormal (inferInstance : IsNormal X) U

/-- A normal scheme is reduced. -/
@[stacks 033K, ega "II 7.3.7" "partial", ega "IV 20.4.12" "partial"]
instance isReduced_of_isNormal (X : Scheme.{u}) [IsNormal X] : IsReduced X :=
  isReduced_of_isReduced_stalk X

/-- **Stacks Project, Tag 033L.** An integral scheme is normal if and only if the ring of
sections on every nonempty affine open is a normal domain. -/
@[stacks 033L]
public theorem isNormal_iff_forall_affineOpen_normal (X : Scheme.{u}) [IsIntegral X] :
    IsNormal X ↔
      ∀ U : X.affineOpens, ∀ _hU : Nonempty U.1,
        letI : IsDomain Γ(X, U.1) := IsIntegral.component_integral U.1
        IsIntegrallyClosed Γ(X, U.1) := by
  rw [isNormal_iff_stalk_normal]
  constructor
  · intro hX U hU
    apply IsIntegrallyClosed.of_localization_maximal
    intro P hP hPmax
    obtain ⟨e⟩ := nonempty_localization_equiv_stalk U ⟨P, hPmax.isPrime⟩ _ rfl
    obtain ⟨_, _⟩ := normal_of_equiv e.symm (hX _)
    assumption
  · intro hX x
    let U : X.affineOpens :=
      ⟨(X.affineCover.f (X.affineCover.idx x)).opensRange,
        isAffineOpen_opensRange (X.affineCover.f (X.affineCover.idx x))⟩
    let xU : U.1 := ⟨x, X.affineCover.covers x⟩
    let y := U.2.primeIdealOf xU
    have : Nonempty U.1 := ⟨xU⟩
    have : IsIntegrallyClosed Γ(X, U.1) := hX U ⟨xU⟩
    have : y.asIdeal.IsPrime := y.isPrime
    obtain ⟨e⟩ := nonempty_localization_equiv_stalk U y x (U.2.fromSpec_primeIdealOf xU)
    have : IsDomain (Localization.AtPrime y.asIdeal) :=
      IsLocalization.isDomain_localization y.asIdeal.primeCompl_le_nonZeroDivisors
    exact normal_of_equiv e ⟨inferInstance,
      isIntegrallyClosed_of_isLocalization _ y.asIdeal.primeCompl
        y.asIdeal.primeCompl_le_nonZeroDivisors⟩

/-- A section of the function field lying in every local ring comes from a global section.
This is the `⊤` case of
`AlgebraicGeometry.exists_germToFunctionField_eq_of_forall_mem_range`. -/
private lemma exists_global_of_mem_all_stalks (X : Scheme.{u}) [IsIntegral X]
    (z : X.functionField)
    (hz : ∀ x : X, ∃ a : X.presheaf.stalk x,
      algebraMap (X.presheaf.stalk x) X.functionField a = z) :
    ∃ a : Γ(X, ⊤), X.presheaf.Γgerm (genericPoint X) a = z :=
  let : Nonempty (⊤ : X.Opens) := ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
  exists_germToFunctionField_eq_of_forall_mem_range X ⊤ z fun x => hz x.1

/-- The ring of global sections of an integral normal scheme is a normal domain. -/
@[stacks 0358, ega "II 8.8.6.1"]
theorem normal_globalSections (X : Scheme.{u}) [IsIntegral X] [IsNormal X] :
    IsIntegrallyClosed Γ(X, ⊤) := by
  classical
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
  let φ : FractionRing Γ(X, ⊤) →+* X.functionField :=
    IsFractionRing.lift (g := (X.germToFunctionField ⊤).hom)
      (X.germToFunctionField_injective ⊤)
  have hφ (a : Γ(X, ⊤)) : φ (algebraMap Γ(X, ⊤) (FractionRing Γ(X, ⊤)) a) =
      X.presheaf.Γgerm (genericPoint X) a :=
    IsFractionRing.lift_algebraMap (X.germToFunctionField_injective ⊤) a
  rw [isIntegrallyClosed_iff (FractionRing Γ(X, ⊤))]
  intro z hz
  have hz' : _root_.IsIntegral Γ(X, ⊤) (φ z) := by
    show (algebraMap Γ(X, ⊤) X.functionField).IsIntegralElem (φ z)
    simpa only [show φ.comp (algebraMap Γ(X, ⊤) (FractionRing Γ(X, ⊤))) =
      algebraMap Γ(X, ⊤) X.functionField from by ext a; exact hφ a] using
      RingHom.IsIntegralElem.map hz φ
  have hz_stalk : ∀ x : X, ∃ a : X.presheaf.stalk x,
      algebraMap (X.presheaf.stalk x) X.functionField a = φ z := by
    intro x
    let : Algebra Γ(X, ⊤) (X.presheaf.stalk x) :=
      (X.presheaf.germ ⊤ x trivial).hom.toAlgebra
    have : IsScalarTower Γ(X, ⊤) (X.presheaf.stalk x) X.functionField :=
      functionField_isScalarTower X ⊤ ⟨x, trivial⟩
    exact (isIntegrallyClosed_iff X.functionField).mp (IsNormal.stalk_normal x) hz'.tower_top
  obtain ⟨a, ha⟩ := exists_global_of_mem_all_stalks X (φ z) hz_stalk
  exact ⟨a, φ.injective ((hφ a).trans ha)⟩

/-- On a normal scheme whose quasi-compact opens have finitely many irreducible components,
every point has an irreducible open neighbourhood. -/
private theorem exists_open_irreducible_nhds {X : Scheme.{u}}
    [IsNormal X]
    (hX : ∀ (U : X.Opens), IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) : ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ IsIrreducible V := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let R := Γ(X, U)
  let eSpec := hU.isoSpec.hom.homeomorph
  have hfinSpec : (irreducibleComponents (PrimeSpectrum R)).Finite := by
    refine ((hX U hU.isCompact).image (eSpec '' ·)).subset fun Z hZ => ?_
    obtain ⟨z, hz⟩ := hZ.1.nonempty
    exact ⟨eSpec ⁻¹' Z, preimage_mem_irreducibleComponents hZ eSpec.isOpenEmbedding
      ⟨z, hz, eSpec.surjective z⟩, Set.image_preimage_eq Z eSpec.surjective⟩
  have : Finite (irreducibleComponents (PrimeSpectrum R)) := hfinSpec.to_subtype
  have : Finite (minimalPrimes R) := Finite.of_equiv (irreducibleComponents (PrimeSpectrum R))
    ((minimalPrimes.equivIrreducibleComponents R).toEquiv).symm
  have hnormalR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) :=
    normalAffineSections_of_normal ‹_› ⟨U, hU⟩
  obtain ⟨n, A, hComm, hDomain, hClosed, ⟨eRing⟩⟩ :=
    ((isIntegrallyClosed_tfae_of_finite_minimalPrimes (R := R) (Set.toFinite _)).out 1 3).mp
      hnormalR
  let : TopologicalSpace (Fin n) := ⊥
  let : DiscreteTopology (Fin n) := ⟨rfl⟩
  let eTop : PrimeSpectrum R ≃ₜ (Σ i, PrimeSpectrum (A i)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv eRing).trans
      (PrimeSpectrum.sigmaToPiHomeo A).symm
  let p := hU.primeIdealOf ⟨x, hxU⟩
  let i := (eTop p).1
  have : IsDomain (A i) := hDomain i
  let W : Set (PrimeSpectrum R) := eTop.symm '' (Sigma.fst ⁻¹' {i})
  have hWopen : IsOpen W := eTop.symm.isOpenMap _ (isOpen_sigma_fst_preimage _)
  have hSirred : IsIrreducible (Sigma.fst ⁻¹' {i} : Set (Σ j, PrimeSpectrum (A j))) := by
    rw [← Set.range_sigmaMk, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ (PrimeSpectrum (A i))).image _
      continuous_sigmaMk.continuousOn
  have hWirred : IsIrreducible W := hSirred.image eTop.symm eTop.symm.continuous.continuousOn
  have : IsOpenImmersion hU.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec hU
  exact ⟨hU.fromSpec.base '' W, hU.fromSpec.isOpenEmbedding.isOpenMap _ hWopen,
    ⟨p, ⟨eTop p, rfl, eTop.symm_apply_apply p⟩, hU.fromSpec_primeIdealOf ⟨x, hxU⟩⟩,
    hWirred.image _ hU.fromSpec.isOpenEmbedding.continuous.continuousOn⟩

/-- Two irreducible components of a topological space that both meet one irreducible open set
are equal. An irreducible component meeting an open set is dense in its intersection with that
open set, so both components are contained in the irreducible component containing the open set,
and maximality forces equality. -/
@[ega "0 2.1.6" "special case"]
theorem component_eq_of_open_irreducible_nhd {X : Type*} [TopologicalSpace X]
    (Z W : Set X) (hZ : Z ∈ irreducibleComponents X) (hW : W ∈ irreducibleComponents X)
    (V : Set X) (hVopen : IsOpen V) (hVirr : IsIrreducible V)
    (hZV : (Z ∩ V).Nonempty) (hWV : (W ∩ V).Nonempty) : Z = W := by
  obtain ⟨C, hC, hVC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible V hVirr
  have aux (A : Set X) (hA : A ∈ irreducibleComponents X) (hAV : (A ∩ V).Nonempty) : A = C := by
    have hAdense : A ⊆ closure (A ∩ V) :=
      subset_closure_inter_of_isPreirreducible_of_isOpen hA.1.2 hVopen hAV
    have hAC : A ⊆ C := hAdense.trans (closure_minimal
      (Set.inter_subset_right.trans hVC) (isClosed_of_mem_irreducibleComponents C hC))
    exact Set.Subset.antisymm hAC (hA.2 hC.1 hAC)
  exact (aux Z hZ hZV).trans (aux W hW hWV).symm

/-- When every point has an irreducible open neighbourhood, irreducible components are open. -/
private theorem component_open_of_local_irreducible {X : Type*} [TopologicalSpace X]
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X)
    (hLocal : ∀ x : X, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ IsIrreducible V) : IsOpen Z := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨V, hVopen, hxV, hVirr⟩ := hLocal x
  obtain ⟨C, hC, hVC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible V hVirr
  have hZeq : Z = C := component_eq_of_open_irreducible_nhd Z C hZ hC V hVopen hVirr
    ⟨x, hx, hxV⟩ ⟨x, hVC hxV, hxV⟩
  exact ⟨V, by simpa [hZeq] using hVC, hVopen, hxV⟩

/-- Normality is local on an open cover: a scheme covered by normal schemes is normal. Each
stalk of the covered scheme is isomorphic to a stalk of a member of the cover, and normality of
a local ring only depends on its isomorphism class. -/
theorem isNormal_of_openCover {X : Scheme.{u}} (𝒰 : X.OpenCover)
    (h𝒰 : ∀ i, IsNormal (𝒰.X i)) : IsNormal X := by
  refine (isNormal_iff_stalk_normal X).2 fun x => ?_
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  exact normal_of_equiv (asIso ((𝒰.f i).stalkMap y)).commRingCatIsoToRingEquiv.symm
    ((isNormal_iff_stalk_normal (𝒰.X i)).mp (h𝒰 i) y)

/-- A scheme whose quasi-compact open subspaces have finitely many irreducible components is
normal if and only if it is isomorphic to a coproduct of normal integral schemes. -/
@[stacks 0357]
public theorem isNormal_iff_exists_iso_coproduct
    {X : Scheme.{u}}
    (hX : ∀ (U : X.Opens), IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    IsNormal X ↔
      ∃ (ι : Type u) (Y : ι → Scheme.{u})
          (_ : ∀ i, IsNormal (Y i)) (_ : ∀ i, IsIntegral (Y i)),
        Nonempty (X ≅ ∐ Y) := by
  classical
  refine ⟨fun _ => ?_, fun ⟨_, Y, hnormalY, _, ⟨e⟩⟩ =>
    isNormal_of_openCover ((sigmaOpenCover Y).pushforwardIso e.inv) hnormalY⟩
  have hLocal := exists_open_irreducible_nhds hX
  have hOpen (C : irreducibleComponents X) : IsOpen (C : Set X) :=
    component_open_of_local_irreducible C C.property hLocal
  let Y : irreducibleComponents X → Scheme.{u} := fun C =>
    Scheme.Opens.toScheme (⟨(C : Set X), hOpen C⟩ : X.Opens)
  let α (C : irreducibleComponents X) : Y C ⟶ X :=
    Scheme.Opens.ι (⟨(C : Set X), hOpen C⟩ : X.Opens)
  have (C : irreducibleComponents X) : IsOpenImmersion (α C) := inferInstance
  have hcover : ⨆ C, (α C).opensRange = ⊤ := by
    apply top_unique
    intro x hx
    rw [Opens.mem_iSup]
    refine ⟨⟨irreducibleComponent x,
      irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
    show x ∈ (α ⟨irreducibleComponent x,
      irreducibleComponent_mem_irreducibleComponents x⟩).opensRange
    rw [Scheme.Hom.mem_opensRange]
    exact ⟨⟨x, mem_irreducibleComponent⟩, rfl⟩
  have hdisj : Pairwise (fun C D : irreducibleComponents X =>
      Disjoint (α C).opensRange (α D).opensRange) := by
    intro C D hCD
    apply disjoint_iff.mpr
    rw [Opens.ext_iff]
    apply Set.ext
    intro x
    simp only [Opens.coe_inf, Opens.coe_bot, Set.mem_inter_iff,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro hxC hxD
    obtain ⟨yC, rfl⟩ := Scheme.Hom.mem_opensRange.mp hxC
    obtain ⟨yD, heq⟩ := Scheme.Hom.mem_opensRange.mp hxD
    obtain ⟨V, hVopen, hxV, hVirr⟩ := hLocal (α C yC)
    have hCmem : α C yC ∈ (C : Set X) := yC.property
    have hDmem : α C yC ∈ (D : Set X) := by
      rw [← heq]
      exact yD.property
    exact hCD (Subtype.ext (component_eq_of_open_irreducible_nhd (C : Set X) (D : Set X)
      C.property D.property V hVopen hVirr ⟨α C yC, hCmem, hxV⟩ ⟨α C yC, hDmem, hxV⟩))
  have hcol : Nonempty (IsColimit (Cofan.mk X α)) :=
    nonempty_isColimit_cofanMk_of α hcover hdisj
  have hnormalY (C) : IsNormal (Y C) := isNormal_open (⟨(C : Set X), hOpen C⟩ : X.Opens)
  have hintegralY : ∀ C, IsIntegral (Y C) := by
    intro C
    have : IsNormal (Y C) := hnormalY C
    have : IrreducibleSpace (Y C) := by
      show IrreducibleSpace (↑(C : Set X))
      exact Subtype.irreducibleSpace C.property.1
    exact isIntegral_of_irreducibleSpace_of_isReduced (Y C)
  exact ⟨irreducibleComponents X, Y, hnormalY, hintegralY,
    ⟨(Classical.choice hcol).coconePointUniqueUpToIso (colimit.isColimit _)⟩⟩

/-- A coproduct of normal schemes is normal. The summands form an open cover of the coproduct,
and normality is local on an open cover. -/
theorem isNormal_sigma {ι : Type u} [Small.{u} ι] (Y : ι → Scheme.{u})
    (hY : ∀ i, IsNormal (Y i)) : IsNormal (∐ Y) :=
  isNormal_of_openCover (sigmaOpenCover Y) hY

end AlgebraicGeometry

end
