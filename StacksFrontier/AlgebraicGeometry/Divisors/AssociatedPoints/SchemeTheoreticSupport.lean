module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.PushforwardFinite
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Embedded
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.Pushforward
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.AnnihilatorSupport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.RingTheory.AssociatedPrime.Spellings
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Embedded
public import StacksFrontier.Topology.Sheaves.Modules.InvertibleAndOperators.AnnihilatorCoherent
import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.BaseChange

/-!
# The scheme-theoretic support of a coherent module with no embedded associated points

The annihilator ideal sheaf of a coherent module `F` on a locally Noetherian scheme `X` cuts
out the scheme-theoretic support of `F`.  If `F` has no embedded associated points, then that
closed subscheme has no embedded points, and `F` descends along it to a coherent module with
full support which again has no embedded associated points.

## Main results

* `AlgebraicGeometry.isAssociatedPrime_map_of_ringEquiv` and
  `AlgebraicGeometry.hasNoEmbeddedAssociatedPrimes_of_ringEquiv`: associated primes of a
  Noetherian ring over itself, and the absence of embedded ones, transport along a ring
  isomorphism.
* `AlgebraicGeometry.hasNoEmbeddedAssociatedPrimes_sections`: on an affine open, the module of
  sections of a module with no embedded associated points has no embedded associated primes.
* `AlgebraicGeometry.hasNoEmbeddedPoints_annihilatorIdeal_subscheme`: the closed subscheme cut
  out by the annihilator has no embedded points.
* `AlgebraicGeometry.exists_isCoherent_submodule_eq_annihilatorIdeal`: the defining ideals are
  the sections of a coherent subsheaf of the structure sheaf.
* `AlgebraicGeometry.isCoherent_of_pushforward_iso_annihilatorIdeal_subscheme` and
  `AlgebraicGeometry.hasNoEmbeddedAssociatedPoints_of_pushforward_iso`: every quasi-coherent
  descent of `F` to that subscheme is coherent and has no embedded associated points.
* `AlgebraicGeometry.supp_eq_univ_of_pushforward_iso`: every such descent has full support.
* `AlgebraicGeometry.exists_coherent_module_on_annihilatorIdeal_subscheme`: a descent exists,
  and it is coherent, has no embedded associated points and has full support.

## Implementation notes

The ideal sheaf itself and the identification of its support with the support of the module are
`AlgebraicGeometry.annihilatorIdeal'` and
`AlgebraicGeometry.supp_eq_annihilatorIdeal_support`, which this file imports rather than
reproves; coherence of the annihilator as a subsheaf of the structure sheaf is
`Stacks.SheafOfModules.isCoherent_annihilatorSheaf`.

The descent is *constructed*, not merely shown to exist: it is the pullback `i^*F` along the
closed immersion `i`, which is coherent by [Stacks, Tag 0EBF] because the subscheme is locally
Noetherian, and whose pushforward is identified with `F` by the essential-image half of
[Stacks, Tag 08KS] (`Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero`), the hypothesis of
which is exactly that the annihilator kills the sections of `F`.  No separate quasi-coherent
descent statement is needed.

The absence of embedded points on the subscheme is the affine-local statement
[Stacks, Tag 02M8] about `R ⧸ Ann_R(M)`, transported to `Γ(Z, i⁻¹U)` along the ring isomorphism
`Scheme.IdealSheafData.subschemeObjIso`.  The transport of associated primes along a ring
isomorphism is `AlgebraicGeometry.isAssociatedPrime_map_of_ringEquiv`, stated for Mathlib's
`IsAssociatedPrime` so that the colon ideals involved never have to be rewritten between their
`Ideal` and `Submodule` spellings; it routes through `Ideal.map_comap_of_equiv`, so that the
underlying ring map appears at a single spelling and no lemma has to be key-matched against a
goal mixing `e` with `(e : R →+* S)`.

## References

* [Stacks Project, Tag 02OM](https://stacks.math.columbia.edu/tag/02OM)
* [Stacks Project, Tag 02M8](https://stacks.math.columbia.edu/tag/02M8)
* [Stacks Project, Tag 02OK](https://stacks.math.columbia.edu/tag/02OK)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
* [Stacks Project, Tag 0H2H](https://stacks.math.columbia.edu/tag/0H2H)
* [Stacks Project, Tag 0H2L](https://stacks.math.columbia.edu/tag/0H2L)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Transport of associated primes along a ring isomorphism -/

/-- The associated primes of a Noetherian commutative ring, viewed as a module over itself, are
carried to one another by a ring isomorphism. -/
theorem isAssociatedPrime_map_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] (e : R ≃+* S) {p : Ideal R}
    (hp : IsAssociatedPrime p R) : IsAssociatedPrime (p.map (e : R →+* S)) S := by
  obtain ⟨hprime, a, hpa⟩ := isAssociatedPrime_iff.mp hp
  have hmemR (r : R) : r ∈ p ↔ r * a = 0 := by
    rw [hpa, Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul]
  rw [Ideal.map_comap_of_equiv e]
  refine isAssociatedPrime_iff.mpr
    ⟨Ideal.comap_isPrime (H := hprime) (e.symm : S →+* R) p, e a, ?_⟩
  ext s
  rw [Ideal.mem_comap, Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul]
  refine (hmemR _).trans ⟨fun h => ?_, fun h => e.injective ?_⟩
  · simpa only [map_mul, map_zero, RingEquiv.coe_toRingHom, e.apply_symm_apply] using
      congrArg e h
  · simpa only [map_mul, map_zero, RingEquiv.coe_toRingHom, e.apply_symm_apply] using h

/-- Absence of embedded associated primes of a Noetherian commutative ring over itself is
invariant under ring isomorphism. -/
theorem hasNoEmbeddedAssociatedPrimes_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] (e : R ≃+* S)
    (hS : HasNoEmbeddedAssociatedPrimes S S) : HasNoEmbeddedAssociatedPrimes R R := by
  intro p hp q hq hqp
  have hmap : p.map (e : R →+* S) = q.map (e : R →+* S) :=
    (hS (isAssociatedPrime_map_of_ringEquiv e hp) (isAssociatedPrime_map_of_ringEquiv e hq)
      (Ideal.map_mono hqp)).symm
  have hback (I : Ideal R) : (I.map (e : R →+* S)).map (e.symm : S →+* R) = I := by
    rw [Ideal.map_map, show (e.symm : S →+* R).comp (e : R →+* S) = RingHom.id R from
      RingHom.ext e.symm_apply_apply, Ideal.map_id]
  simpa only [hback] using (congrArg (Ideal.map (e.symm : S →+* R)) hmap).symm

/-! ### Absence of embedded points on the scheme-theoretic support -/

variable {X : Scheme.{u}}

/-- On an affine open of a locally Noetherian scheme, the sections of a quasi-coherent module
with no embedded associated points have no embedded associated primes.  This is the affine
translation of the hypothesis of [Stacks, Tag 02OM] through [Stacks, Tag 02OK]. -/
theorem hasNoEmbeddedAssociatedPrimes_sections [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] (hF : HasNoEmbeddedAssociatedPoints F)
    {U : X.Opens} (hU : IsAffineOpen U) :
    HasNoEmbeddedAssociatedPrimes Γ(X, U) Γ(F, U) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  intro p hp q hq hqp
  set xp : PrimeSpectrum Γ(X, U) := ⟨p, hp.isPrime⟩
  set xq : PrimeSpectrum Γ(X, U) := ⟨q, hq.isPrime⟩
  have hmemU (z : PrimeSpectrum Γ(X, U)) : hU.fromSpec z ∈ U :=
    hU.range_fromSpec.le ⟨z, rfl⟩
  have hpoint (z : PrimeSpectrum Γ(X, U)) :
      hU.primeIdealOf ⟨hU.fromSpec z, hmemU z⟩ = z :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)
  have hAssoc (z : PrimeSpectrum Γ(X, U)) (hz : z.asIdeal ∈ associatedPrimes Γ(X, U) Γ(F, U)) :
      Stacks.Divisors.IsAssociatedPoint F (hU.fromSpec z) :=
    (isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian F U hU
      (hmemU z)).mp
      (by rw [hpoint z]; exact (isAssociatedPrimeStacks_iff_mem_associatedPrimes _).mpr hz)
  by_contra hne
  exact hF (hU.fromSpec xp) ⟨hAssoc xp hp, hU.fromSpec xq, hAssoc xq hq,
    ((PrimeSpectrum.le_iff_specializes xq xp).mp hqp).map hU.fromSpec.continuous,
    fun hfs => hne (congrArg PrimeSpectrum.asIdeal
      (hU.fromSpec.isOpenEmbedding.injective hfs : xq = xp))⟩

/-- **[Stacks, Tag 02OM].** The closed subscheme cut out by the annihilator of a coherent module
with no embedded associated points has no embedded points. -/
@[stacks 02OM "absence of embedded points on the support"]
theorem hasNoEmbeddedPoints_annihilatorIdeal_subscheme [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (hF : HasNoEmbeddedAssociatedPoints F) :
    HasNoEmbeddedPoints (annihilatorIdeal' F).subscheme := by
  obtain ⟨_, _⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  set I := annihilatorIdeal' F
  set i := I.subschemeι
  have : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian i
  intro z hz
  obtain ⟨hzAss, y, hyAss, hspec, hne⟩ := hz
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (i.base z)) isOpen_univ
  have hVaff : IsAffineOpen (i ⁻¹ᵁ U) := hU.preimage i
  have hzV : z ∈ i ⁻¹ᵁ U := hxU
  have hyV : y ∈ i ⁻¹ᵁ U := (hspec.map i.continuous).mem_open U.2 hxU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hfin : Module.Finite Γ(X, U) Γ(F, U) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F hU
  have hNoQuot : HasNoEmbeddedAssociatedPrimes
      (Γ(X, U) ⧸ Module.annihilator Γ(X, U) Γ(F, U))
      (Γ(X, U) ⧸ Module.annihilator Γ(X, U) Γ(F, U)) :=
    hasNoEmbeddedAssociatedPrimes_quotient_annihilator Γ(X, U) Γ(F, U)
      (hasNoEmbeddedAssociatedPrimes_sections F hF hU)
  have hideal : I.ideal ⟨U, hU⟩ = Module.annihilator Γ(X, U) Γ(F, U) :=
    annihilatorIdeal_ideal F ⟨U, hU⟩
  have : IsNoetherianRing Γ(I.subscheme, i ⁻¹ᵁ U) :=
    IsLocallyNoetherian.component_noetherian ⟨i ⁻¹ᵁ U, hVaff⟩
  have hNoV : HasNoEmbeddedAssociatedPrimes
      Γ(I.subscheme, i ⁻¹ᵁ U) Γ(I.subscheme, i ⁻¹ᵁ U) :=
    hasNoEmbeddedAssociatedPrimes_of_ringEquiv
      ((I.subschemeObjIso ⟨U, hU⟩).commRingCatIsoToRingEquiv.trans
        (Ideal.quotientEquivAlgOfEq Γ(X, U) hideal).toRingEquiv) hNoQuot
  have hO : (SheafOfModules.unit I.subscheme.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent I.subscheme
  have : (SheafOfModules.unit I.subscheme.ringCatSheaf).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
      (SheafOfModules.unit I.subscheme.ringCatSheaf)).1
  have hAss (w : I.subscheme) (hwV : w ∈ i ⁻¹ᵁ U)
      (hw : w ∈ Stacks.Divisors.associatedPoints (SheafOfModules.unit I.subscheme.ringCatSheaf)) :
      (hVaff.primeIdealOf ⟨w, hwV⟩).asIdeal ∈
        associatedPrimes Γ(I.subscheme, i ⁻¹ᵁ U) Γ(I.subscheme, i ⁻¹ᵁ U) :=
    (isAssociatedPrimeStacks_iff_mem_associatedPrimes _).mp
      ((isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian
        (SheafOfModules.unit I.subscheme.ringCatSheaf) _ hVaff hwV).mpr hw)
  have hqle : (hVaff.primeIdealOf ⟨y, hyV⟩).asIdeal ≤
      (hVaff.primeIdealOf ⟨z, hzV⟩).asIdeal := by
    refine (PrimeSpectrum.le_iff_specializes _ _).mpr
      (hVaff.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp ?_)
    simpa only [IsAffineOpen.fromSpec_primeIdealOf] using hspec
  have hpq : hVaff.primeIdealOf ⟨y, hyV⟩ = hVaff.primeIdealOf ⟨z, hzV⟩ :=
    PrimeSpectrum.ext (hNoV (hAss z hzV hzAss) (hAss y hyV hyAss) hqle)
  exact hne (by
    simpa only [IsAffineOpen.fromSpec_primeIdealOf] using congrArg hVaff.fromSpec hpq)

/-! ### The ideal sheaf and its coherence -/

add_to_stacks 02OM "the ideal sheaf cutting out the support" AlgebraicGeometry.annihilatorIdeal'

add_to_stacks 02OM "coherence of the annihilator"
  Stacks.SheafOfModules.isCoherent_annihilatorSheaf

section DefiningIdeal

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  PresheafOfModules.presheaf TopCat.Sheaf structureSheafRing
  ModuleCat.restrictScalars

/-- The annihilator of the sections of a quasi-coherent module of finite type over an affine
open restricts into the annihilator of the sections over any smaller open.

The affine open is covered by the basic opens `X.basicOpen g` it contains, and on each of those
the statement is the compatibility of the annihilator ideals with passage to a basic open, which
is `Scheme.IdealSheafData.map_ideal_basicOpen` for `AlgebraicGeometry.annihilatorIdeal'`.  The
conclusion is then local on the smaller open, so the sheaf condition on `F` finishes it. -/
private theorem map_mem_annihilator_of_le (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (U : X.affineOpens) {V : X.Opens} (hVU : V ≤ U.1) (r : Γ(X, U.1))
    (hr : r ∈ Module.annihilator Γ(X, U.1) Γ(F, U.1)) :
    X.presheaf.map (homOfLE hVU).op r ∈ Module.annihilator Γ(X, V) Γ(F, V) := by
  classical
  rw [Module.mem_annihilator]
  intro m
  let e (x : V) : Γ(X, U.1) := Classical.choose (U.2.exists_basicOpen_le x (hVU x.2))
  have heV (x : V) : X.basicOpen (e x) ≤ V :=
    (Classical.choose_spec (U.2.exists_basicOpen_le x (hVU x.2))).1
  have hex (x : V) : (x : X) ∈ X.basicOpen (e x) :=
    (Classical.choose_spec (U.2.exists_basicOpen_le x (hVU x.2))).2
  have hcover : V ≤ ⨆ x : V, X.basicOpen (e x) := fun x hx =>
    TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hex ⟨x, hx⟩⟩
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨F.presheaf, F.isSheaf⟩
    (fun x => X.basicOpen (e x)) V (fun x => homOfLE (heV x)) hcover _ 0 fun x => ?_
  have hWU : X.basicOpen (e x) ≤ U.1 := X.basicOpen_le (e x)
  have hcomp : (homOfLE hVU).op ≫ (homOfLE (heV x)).op = (homOfLE hWU).op :=
    Subsingleton.elim _ _
  have hres : X.presheaf.map (homOfLE (heV x)).op (X.presheaf.map (homOfLE hVU).op r) =
      X.presheaf.map (homOfLE hWU).op r := by
    have h := congrArg (fun φ : Γ(X, U.1) ⟶ Γ(X, X.basicOpen (e x)) =>
      CommRingCat.Hom.hom φ r)
      (X.presheaf.map_comp (homOfLE hVU).op (homOfLE (heV x)).op).symm
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, hcomp] using h
  have hbas : X.presheaf.map (homOfLE hWU).op r ∈
      Module.annihilator Γ(X, X.basicOpen (e x)) Γ(F, X.basicOpen (e x)) := by
    have h := (annihilatorIdeal' F).map_ideal_basicOpen U (e x)
    rw [annihilatorIdeal_ideal F U, annihilatorIdeal_ideal F (X.affineBasicOpen (e x))] at h
    exact h.le (Ideal.mem_map_of_mem _ hr)
  rw [F.map_smul, hres, Module.mem_annihilator.mp hbas, map_zero]

/-- On an affine open the annihilator sheaf of [Stacks, Tag 0H2H] has as its sections exactly
the annihilator of the module of sections.  One inclusion is the restriction along the identity;
the other is `AlgebraicGeometry.map_mem_annihilator_of_le`. -/
private theorem annihilatorSheaf_sections_affine (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (U : X.affineOpens) :
    (show Ideal Γ(X, U.1) from
        (Stacks.SheafOfModules.annihilatorSheaf X.toRingedSpace F).toSubmodule.obj (op U.1)) =
      Module.annihilator Γ(X, U.1) Γ(F, U.1) := by
  refine SetLike.ext fun r => ⟨fun hr => Module.mem_annihilator.mpr fun m => ?_,
    fun hr V f m => ?_⟩
  · have h := hr (op U.1) (𝟙 _) m
    rw [CategoryTheory.Functor.map_id] at h
    exact h
  · exact Module.mem_annihilator.mp (map_mem_annihilator_of_le F U f.unop.le r hr) m

/-- **[Stacks, Tag 02OM].** The ideals cutting out the scheme-theoretic support over the affine
opens are the sections of a coherent subsheaf of the structure sheaf, namely the annihilator
sheaf of [Stacks, Tag 0H2H]. -/
@[stacks 02OM "coherence of the defining ideal"]
theorem exists_isCoherent_submodule_eq_annihilatorIdeal [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] :
    ∃ I : (SheafOfModules.unit X.ringCatSheaf).Submodule,
      I.toSheafOfModules.IsCoherent ∧
        I = Stacks.SheafOfModules.annihilatorSheaf X.toRingedSpace F ∧
          ∀ U : X.affineOpens, (annihilatorIdeal' F).ideal U =
            (show Ideal Γ(X, U.1) from I.toSubmodule.obj (op U.1)) := by
  obtain ⟨_, _⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  have hO : Stacks.SheafOfModules.IsCoherent (SheafOfModules.unit
      (structureSheafRing X.toRingedSpace)) :=
    CoherentAbelian.stacksIsCoherent_of_isCoherent
      (Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent X)
  refine ⟨Stacks.SheafOfModules.annihilatorSheaf X.toRingedSpace F, ?_, rfl, fun U => ?_⟩
  · -- The two coherence predicates of the library agree; 0H2L is proved for the other one.
    exact CoherentAbelian.isCoherent_of_stacksIsCoherent
      (@Stacks.SheafOfModules.isCoherent_annihilatorSheaf.{u} X.toRingedSpace F hO
        (CoherentAbelian.stacksIsCoherent_of_isCoherent (inferInstanceAs F.IsCoherent)))
  · rw [annihilatorIdeal_ideal F U]
    exact (annihilatorSheaf_sections_affine F U).symm

end DefiningIdeal

/-! ### Properties of a descent to the scheme-theoretic support -/

/-- Isomorphic `𝒪_X`-modules have the same associated points.
Alias of `AlgebraicGeometry.associatedPoints_eq_of_moduleIso`. -/
private alias associatedPoints_eq_of_iso := associatedPoints_eq_of_moduleIso

/-- **[Stacks, Tag 02OM].** Every quasi-coherent module on the scheme-theoretic support whose
direct image is `F` is itself coherent. -/
@[stacks 02OM "coherence of the descended sheaf"]
theorem isCoherent_of_pushforward_iso_annihilatorIdeal_subscheme [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (G : (annihilatorIdeal' F).subscheme.Modules)
    [G.IsQuasicoherent]
    (e : (Scheme.Modules.pushforward (annihilatorIdeal' F).subschemeι).obj G ≅ F) :
    G.IsCoherent := by
  obtain ⟨_, _⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  have : IsLocallyNoetherian (annihilatorIdeal' F).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (annihilatorIdeal' F).subschemeι
  have : G.IsFiniteType :=
    (isFiniteType_iff_pushforward_isFiniteType (annihilatorIdeal' F).subschemeι G).2
      (isFiniteType_of_scheme_iso e.symm)
  exact Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isQuasicoherent_isFiniteType G

/-- **[Stacks, Tag 02OM].** Every quasi-coherent module on the scheme-theoretic support whose
direct image is `F` inherits from `F` the absence of embedded associated points. -/
@[stacks 02OM "absence of embedded associated points on the descended sheaf"]
theorem hasNoEmbeddedAssociatedPoints_of_pushforward_iso [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (hF : HasNoEmbeddedAssociatedPoints F)
    (G : (annihilatorIdeal' F).subscheme.Modules) [G.IsQuasicoherent]
    (e : (Scheme.Modules.pushforward (annihilatorIdeal' F).subschemeι).obj G ≅ F) :
    HasNoEmbeddedAssociatedPoints G := by
  obtain ⟨_, _⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  set i := (annihilatorIdeal' F).subschemeι
  have : IsLocallyNoetherian (annihilatorIdeal' F).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian i
  have himg : i '' Stacks.Divisors.associatedPoints G =
      Stacks.Divisors.associatedPoints F := by
    rw [image_associatedPoints_eq_associatedPoints_pushforward i G]
    exact associatedPoints_eq_of_iso e
  intro x hx
  obtain ⟨hxAss, y, hyAss, hspec, hne⟩ := hx
  exact hF (i.base x) ⟨himg.le ⟨x, hxAss, rfl⟩, i.base y, himg.le ⟨y, hyAss, rfl⟩,
    hspec.map i.continuous, fun hxy => hne (i.isClosedEmbedding.injective hxy)⟩

/-- **[Stacks, Tag 02OM].** Every module on the scheme-theoretic support whose direct image is
`F` has full support: the scheme-theoretic support is exactly the support of `F`. -/
theorem supp_eq_univ_of_pushforward_iso (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (G : (annihilatorIdeal' F).subscheme.Modules)
    (e : (Scheme.Modules.pushforward (annihilatorIdeal' F).subschemeι).obj G ≅ F) :
    SheafOfModules.supp G = Set.univ := by
  refine Set.eq_univ_of_forall fun z => ?_
  have hx : (annihilatorIdeal' F).subschemeι.base z ∈ SheafOfModules.supp F := by
    rw [supp_eq_annihilatorIdeal_support F]
    exact (annihilatorIdeal' F).range_subschemeι.le (Set.mem_range_self z)
  -- A stalk of `F` at a point of the support is nontrivial, and `i` is a closed embedding,
  -- so the stalk of `G` at `z` is nontrivial too: it is the stalk of `i_* G ≅ F` at `i z`.
  let T := Scheme.Modules.toPresheaf X ⋙
    TopCat.Presheaf.stalkFunctor Ab.{u} ((annihilatorIdeal' F).subschemeι.base z)
  have hF : Nontrivial (T.obj F) :=
    (SheafOfModules.mem_supp_iff_nontrivial_stalk F _).mp hx
  have hpush : Nontrivial
      (T.obj ((Scheme.Modules.pushforward (annihilatorIdeal' F).subschemeι).obj G)) := by
    exact (ConcreteCategory.bijective_of_isIso (T.mapIso e.symm).hom).1.nontrivial
  let P := (Scheme.Modules.toPresheaf (annihilatorIdeal' F).subscheme).obj G
  let α := P.stalkPushforward Ab (annihilatorIdeal' F).subschemeι.base z
  have hα : IsIso α :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing Ab
      (annihilatorIdeal' F).subschemeι.isClosedEmbedding.isInducing P z
  exact (SheafOfModules.mem_supp_iff_nontrivial_stalk (show SheafOfModules _ from G) z).mpr
    (@Function.Injective.nontrivial _ _ hpush _ (ConcreteCategory.bijective_of_isIso α).1)

/-! ### Existence of the descent -/

/-- The annihilator ideal sheaf kills the sections of `F`: a section of the structure sheaf that
dies under the comorphism of the inclusion of the scheme-theoretic support annihilates every
section of `F`.  This is the hypothesis of the essential-image half of [Stacks, Tag 08KS]. -/
private theorem annihilatorIdeal_smul_eq_zero (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (U : X.Opens) (a : Γ(X, U))
    (ha : ((annihilatorIdeal' F).subschemeι.app U).hom a = 0) (m : Γ(F, U)) : a • m = 0 := by
  classical
  refine TopCat.Presheaf.IsSheaf.section_ext F.isSheaf (U := op U) fun x hx => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  refine ⟨V, hVU, hxV, ?_⟩
  -- Naturality of the comorphism carries the vanishing of `a` from `U` down to `V`.
  have happ : ((annihilatorIdeal' F).subschemeι.app V).hom
      (X.presheaf.map (homOfLE hVU).op a) = 0 := by
    have h := congrArg (fun φ : Γ(X, U) ⟶
        Γ((annihilatorIdeal' F).subscheme, (annihilatorIdeal' F).subschemeι ⁻¹ᵁ V) =>
      CommRingCat.Hom.hom φ a) ((annihilatorIdeal' F).subschemeι.naturality (homOfLE hVU).op)
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, ha, map_zero] using h
  have hmemAnn : X.presheaf.map (homOfLE hVU).op a ∈
      Module.annihilator Γ(X, V) Γ(F, V) := by
    rw [← annihilatorIdeal_ideal F ⟨V, hV⟩,
      ← (annihilatorIdeal' F).ker_subschemeι_app ⟨V, hV⟩]
    exact RingHom.mem_ker.mpr happ
  rw [F.map_smul, map_zero]
  exact Module.mem_annihilator.mp hmemAnn _

/-- **[Stacks, Tag 02OM].** A coherent module with no embedded associated points on a locally
Noetherian scheme descends along the inclusion of its scheme-theoretic support to a coherent
module with full support and again no embedded associated points. -/
@[stacks 02OM "existence and properties of the descended sheaf"]
theorem exists_coherent_module_on_annihilatorIdeal_subscheme [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (hF : HasNoEmbeddedAssociatedPoints F) :
    ∃ G : (annihilatorIdeal' F).subscheme.Modules,
      G.IsCoherent ∧ HasNoEmbeddedAssociatedPoints G ∧
        SheafOfModules.supp G = Set.univ ∧
          Nonempty ((Scheme.Modules.pushforward
            (annihilatorIdeal' F).subschemeι).obj G ≅ F) := by
  obtain ⟨_, _⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  set i := (annihilatorIdeal' F).subschemeι
  have : IsLocallyNoetherian (annihilatorIdeal' F).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian i
  have hunit : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F) :=
    Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero i F
      (annihilatorIdeal_smul_eq_zero F)
  have hGcoh : ((Scheme.Modules.pullback i).obj F).IsCoherent := isCoherent_pullback i F
  have : ((Scheme.Modules.pullback i).obj F).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
      ((Scheme.Modules.pullback i).obj F)).1
  set e := (asIso ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F)).symm
  exact ⟨(Scheme.Modules.pullback i).obj F, hGcoh,
    hasNoEmbeddedAssociatedPoints_of_pushforward_iso F hF _ e,
    supp_eq_univ_of_pushforward_iso F _ e, ⟨e⟩⟩

end AlgebraicGeometry

end
