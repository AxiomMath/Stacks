module

public import StacksFrontier.RingTheory.Length.RingEquiv
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic

/-!
# A local lower bound for the colength of a finite-support quotient

Let `I` be a quasi-coherent ideal sheaf on a scheme `X` over an affine base `Spec A`, and
suppose the closed subscheme it cuts out is supported at finitely many closed points. Then the
length over `A` of the global sections of that subscheme is at least the sum, over those
points, of the colengths of the stalks of `I`.

The subscheme is then finite and discrete, so it is affine and its ring of sections splits as
the finite product of its localizations
(`PrimeSpectrum.toPiLocalizationEquiv`). Each factor is the local ring of the subscheme at a
point, which is the quotient of the local ring of `X` by the stalk of the ideal sheaf; and the
length of a module over a ring is at most its length over a subring acting through it. Summing
the factors gives the bound.

## Main results

* `Stacks.Blowup.Colength.length_globalSections_ge_sum_length_stalkQuotient` — the local
  colength bound.

## Implementation notes

The quotient sheaf is represented by the structure sheaf of the closed subscheme defined by the
ideal, and the stalk ideal is `AlgebraicGeometry.IdealSheafData.stalk`. The regular local
surface and the blowup that the source works with are unnecessary for this length comparison:
only finite closed support and a morphism to the affine base are used, so the statement is for
an arbitrary scheme over an arbitrary base ring.

The `A`-algebra structure on the global sections of the subscheme is the one induced by the
composite `I.subscheme ⟶ X ⟶ Spec A`, introduced by a `letI` inside the statement so that no
instance has to be carried by callers.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.Blowup.Colength

universe u

private noncomputable def idealSheafStalkMap
    {X : Scheme.{u}} (I : X.IdealSheafData) (y : I.subscheme)
    (x : X) (h : I.subschemeι.base y = x) :
    X.presheaf.stalk x →+* I.subscheme.presheaf.stalk y :=
  (I.subschemeι.stalkMap y).hom.comp
    (X.presheaf.stalkCongr (.of_eq h.symm)).hom.hom

private theorem idealSheafStalkMap_rfl {X : Scheme.{u}} (I : X.IdealSheafData)
    (y : I.subscheme) :
    idealSheafStalkMap I y (I.subschemeι y) rfl = (I.subschemeι.stalkMap y).hom := by
  ext a
  simp [idealSheafStalkMap]

/-- Ring isomorphisms intertwining two ring homomorphisms carry the kernel of one onto the
kernel of the other. -/
private theorem map_ker_eq_ker_of_comp_eq {R S R' S' : Type*} [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] (φ : R →+* S) (g : R' →+* S') (eR : R ≃+* R') (eS : S ≃+* S')
    (h : g.comp eR.toRingHom = eS.toRingHom.comp φ) :
    (RingHom.ker φ).map eR.toRingHom = RingHom.ker g := by
  have key (a : R) : g (eR a) = eS (φ a) := RingHom.congr_fun h a
  ext z
  obtain ⟨a, rfl⟩ := eR.surjective z
  rw [Ideal.mem_map_iff_of_surjective eR.toRingHom eR.surjective]
  simp [RingHom.mem_ker, key]

/-- The kernel of the map of localizations induced by a surjective ring homomorphism is the
extension of its kernel. -/
private theorem ker_localRingHom_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : p = q.comap f) :
    RingHom.ker (Localization.localRingHom p q f hpq) =
      (RingHom.ker f).map (algebraMap R (Localization.AtPrime p)) := by
  have hT : Submonoid.map f p.primeCompl = q.primeCompl := by
    simpa only [← hpq] using q.map_primeCompl_comap_of_surjective f hf
  simpa [Localization.localRingHom] using
    IsLocalization.ker_map (Q := Localization.AtPrime q) f hT

private theorem stalk_eq_ker_stalkMap_of_isAffineOpen
    {X : Scheme.{u}} (I : X.IdealSheafData) (y : I.subscheme) (U : X.affineOpens)
    (hxU : I.subschemeι y ∈ U.1) :
    IdealSheafData.stalk I (I.subschemeι y) = RingHom.ker (I.subschemeι.stalkMap y).hom := by
  let x : X := I.subschemeι y
  have hU : IsAffineOpen U.1 := U.2
  let V : I.subscheme.Opens := I.subschemeι ⁻¹ᵁ U.1
  have hV : IsAffineOpen V := hU.preimage I.subschemeι
  have hyV : y ∈ V := hxU
  have hVU : V ≤ I.subschemeι ⁻¹ᵁ U.1 := le_rfl
  let p := hU.primeIdealOf ⟨x, hxU⟩
  let q := hV.primeIdealOf ⟨y, hyV⟩
  let f : Γ(X, U.1) →+* Γ(I.subscheme, V) := (I.subschemeι.appLE U.1 V le_rfl).hom
  have hf : Function.Surjective f := by
    dsimp [f, V]
    simpa only [Scheme.Hom.appLE_eq_app] using I.subschemeι_app_surjective U
  have hfker : RingHom.ker f = I.ideal U := by
    dsimp [f, V]
    simpa only [Scheme.Hom.appLE_eq_app] using I.ker_subschemeι_app U
  have hqcomap : q.asIdeal.comap f = p.asIdeal := congrArg PrimeSpectrum.asIdeal
    (IsAffineOpen.comap_primeIdealOf_appLE (f := I.subschemeι) U.1 hU V hV hVU hyV)
  let g : Localization.AtPrime p.asIdeal →+* Localization.AtPrime q.asIdeal :=
    Localization.localRingHom p.asIdeal q.asIdeal f hqcomap.symm
  let : Algebra Γ(X, U.1) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal := hU.isLocalization_stalk ⟨x, hxU⟩
  let : Algebra Γ(I.subscheme, V) (I.subscheme.presheaf.stalk y) :=
    I.subscheme.presheaf.algebra_section_stalk ⟨y, hyV⟩
  let : IsLocalization.AtPrime (I.subscheme.presheaf.stalk y) q.asIdeal :=
    hV.isLocalization_stalk ⟨y, hyV⟩
  let eR : X.presheaf.stalk x ≃+* Localization.AtPrime p.asIdeal :=
    (IsLocalization.algEquiv p.asIdeal.primeCompl _ _).toRingEquiv
  let eS : I.subscheme.presheaf.stalk y ≃+* Localization.AtPrime q.asIdeal :=
    (IsLocalization.algEquiv q.asIdeal.primeCompl _ _).toRingEquiv
  have hcomm : g.comp eR.toRingHom = eS.toRingHom.comp (I.subschemeι.stalkMap y).hom :=
    congrArg CommRingCat.Hom.hom (IsAffineOpen.arrowStalkMapIso (f := I.subschemeι) (x := y)
      (U := U.1) hU (V := V) hV (hVU := hVU) (hx := hyV)).hom.w
  have hkerLoc : RingHom.ker g =
      (RingHom.ker f).map (algebraMap Γ(X, U.1) (Localization.AtPrime p.asIdeal)) :=
    ker_localRingHom_of_surjective f hf _ _ _
  have hstalkMap : (IdealSheafData.stalk I x).map eR.toRingHom =
      (I.ideal U).map (algebraMap Γ(X, U.1) (Localization.AtPrime p.asIdeal)) := by
    rw [IdealSheafData.stalk_eq_map_germ I x U hxU, Ideal.map_map]
    congr 1
    ext a
    exact (IsLocalization.algEquiv p.asIdeal.primeCompl (X.presheaf.stalk x)
      (Localization.AtPrime p.asIdeal)).commutes a
  apply eR.idealComapOrderIso.symm.injective
  change (IdealSheafData.stalk I x).map eR.toRingHom =
    (RingHom.ker (I.subschemeι.stalkMap y).hom).map eR.toRingHom
  rw [hstalkMap, map_ker_eq_ker_of_comp_eq _ _ eR eS hcomm, hkerLoc, hfker]

private theorem stalk_eq_ker_stalkMap
    {X : Scheme.{u}} (I : X.IdealSheafData) (x : X)
    (y : I.subscheme) (h : I.subschemeι.base y = x) :
    IdealSheafData.stalk I x =
      RingHom.ker (idealSheafStalkMap I y x h) := by
  subst x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (I.subschemeι y)) isOpen_univ
  exact (stalk_eq_ker_stalkMap_of_isAffineOpen I y ⟨U, hU⟩ hxU).trans
    (congrArg RingHom.ker (idealSheafStalkMap_rfl I y)).symm

private theorem length_idealStalk_quotient_eq_subschemeStalk
    {X : Scheme.{u}} (I : X.IdealSheafData) (y : I.subscheme) :
    Module.length (X.presheaf.stalk (I.subschemeι y))
      (X.presheaf.stalk (I.subschemeι y) ⧸ IdealSheafData.stalk I (I.subschemeι y)) =
    Module.length (I.subscheme.presheaf.stalk y) (I.subscheme.presheaf.stalk y) := by
  let x : X := I.subschemeι y
  let φ : X.presheaf.stalk x →+* I.subscheme.presheaf.stalk y :=
    (I.subschemeι.stalkMap y).hom
  have hsurj : Function.Surjective φ := I.subschemeι.stalkMap_surjective y
  have hker : RingHom.ker φ = IdealSheafData.stalk I x :=
    ((stalk_eq_ker_stalkMap I x y rfl).trans
      (congrArg RingHom.ker (idealSheafStalkMap_rfl I y))).symm
  let : Algebra (X.presheaf.stalk x) (I.subscheme.presheaf.stalk y) := φ.toAlgebra
  let eLin : (X.presheaf.stalk x ⧸ IdealSheafData.stalk I x) ≃ₗ[X.presheaf.stalk x]
      I.subscheme.presheaf.stalk y := by
    rw [← hker]
    exact LinearMap.quotKerEquivOfSurjective
      (Algebra.linearMap (X.presheaf.stalk x) (I.subscheme.presheaf.stalk y)) hsurj
  calc
    Module.length (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸ IdealSheafData.stalk I x) =
      Module.length (X.presheaf.stalk x) (I.subscheme.presheaf.stalk y) := eLin.length_eq
    _ = Module.length (I.subscheme.presheaf.stalk y) (I.subscheme.presheaf.stalk y) :=
      Module.length_eq_of_surjective (S := X.presheaf.stalk x)
        (R := I.subscheme.presheaf.stalk y) (M := I.subscheme.presheaf.stalk y) hsurj

private theorem length_subschemeStalk_eq_localization
    {Z : Scheme.{u}} [IsAffine Z] (z : Z)
    [((Scheme.isoSpec Z).hom z).asIdeal.IsPrime] :
    Module.length (Z.presheaf.stalk z) (Z.presheaf.stalk z) =
      Module.length (Localization ((Scheme.isoSpec Z).hom z).asIdeal.primeCompl)
        (Localization ((Scheme.isoSpec Z).hom z).asIdeal.primeCompl) := by
  let p : PrimeSpectrum Γ(Z, ⊤) := (Scheme.isoSpec Z).hom z
  let e₁ : (Spec (.of Γ(Z, ⊤))).presheaf.stalk p ≅ CommRingCat.of
      (Localization.AtPrime p.asIdeal) := AlgebraicGeometry.Spec.stalkIso (.of Γ(Z, ⊤)) p
  let e₂ : (Spec (.of Γ(Z, ⊤))).presheaf.stalk p ≅
      CommRingCat.of (Z.presheaf.stalk z) := asIso ((Scheme.isoSpec Z).hom.stalkMap z)
  let e : Z.presheaf.stalk z ≃+* Localization.AtPrime p.asIdeal :=
    (e₂.symm ≪≫ e₁).commRingCatIsoToRingEquiv
  simpa [p, Localization.AtPrime] using Module.length_eq_of_ringEquiv e

private theorem length_sum_localizations_le_length
    {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    [DiscreteTopology (PrimeSpectrum R)] [Fintype (PrimeSpectrum R)] :
    (∑ p : PrimeSpectrum R,
      Module.length (Localization p.asIdeal.primeCompl)
        (Localization p.asIdeal.primeCompl)) ≤ Module.length A R := by
  classical
  let eA : R ≃ₗ[A] PrimeSpectrum.PiLocalization R :=
    LinearEquiv.restrictScalars A (PrimeSpectrum.toPiLocalizationEquiv R).toLinearEquiv
  rw [eA.length_eq, Module.length_pi_of_fintype]
  refine Finset.sum_le_sum fun p _ => ?_
  let pTop : Submodule (Localization p.asIdeal.primeCompl)
      (Localization p.asIdeal.primeCompl) := ⊤
  let eTop : pTop ≃ₗ[Localization p.asIdeal.primeCompl]
      Localization p.asIdeal.primeCompl := Submodule.topEquiv
  let eA : pTop.restrictScalars A ≃ₗ[A] pTop :=
    LinearEquiv.restrictScalars A (Submodule.restrictScalarsEquiv A
      (Localization p.asIdeal.primeCompl) (Localization p.asIdeal.primeCompl) pTop)
  calc
    Module.length (Localization p.asIdeal.primeCompl)
        (Localization p.asIdeal.primeCompl) =
      Module.length (Localization p.asIdeal.primeCompl) pTop := eTop.length_eq.symm
    _ ≤ Module.length A (pTop.restrictScalars A) :=
      Submodule.length_le_length_restrictScalars A pTop
    _ = Module.length A pTop := eA.length_eq
    _ = Module.length A (Localization p.asIdeal.primeCompl) :=
      (LinearEquiv.restrictScalars A eTop).length_eq

private theorem subschemeι_injective {X : Scheme.{u}} (I : X.IdealSheafData) :
    Function.Injective (fun z : I.subscheme => (I.subschemeι z : X)) :=
  (inferInstance : IsClosedImmersion I.subschemeι).isClosedEmbedding.injective

private theorem subschemeι_mem_of_support_eq {X : Scheme.{u}} (I : X.IdealSheafData)
    (T : Finset X) (hT : (I.support : Set X) = (T : Set X)) (z : I.subscheme) :
    I.subschemeι z ∈ T := by
  rw [← Finset.mem_coe, ← hT, ← I.range_subschemeι]
  exact ⟨z, rfl⟩

/-- A closed subscheme supported on a finite set of points is in bijection with that set. -/
private noncomputable def subschemeEquivOfSupportEq {X : Scheme.{u}} (I : X.IdealSheafData)
    (T : Finset X) (hT : (I.support : Set X) = (T : Set X)) : I.subscheme ≃ T :=
  Equiv.ofBijective (fun z => ⟨I.subschemeι z, subschemeι_mem_of_support_eq I T hT z⟩)
    ⟨fun _ _ h => subschemeι_injective I (congrArg Subtype.val h :), fun x => by
      obtain ⟨z, hz⟩ : (x : X) ∈ Set.range I.subschemeι := by
        rw [I.range_subschemeι, hT]
        exact x.2
      exact ⟨z, Subtype.ext hz⟩⟩

/-- A closed subscheme supported on a finite set of points is finite. -/
private theorem finite_subscheme_of_support_eq {X : Scheme.{u}} (I : X.IdealSheafData)
    (T : Finset X) (hT : (I.support : Set X) = (T : Set X)) : Finite I.subscheme :=
  Finite.of_equiv T (subschemeEquivOfSupportEq I T hT).symm

/-- A closed subscheme supported on a finite set of closed points is discrete. -/
private theorem discreteTopology_subscheme_of_support_eq {X : Scheme.{u}}
    (I : X.IdealSheafData) (T : Finset X) (hT : (I.support : Set X) = (T : Set X))
    (hclosed : ∀ x ∈ T, IsClosed ({x} : Set X)) : DiscreteTopology I.subscheme := by
  have := finite_subscheme_of_support_eq I T hT
  refine DiscreteTopology.of_finite_of_isClosed_singleton fun z => ?_
  have hpre : I.subschemeι ⁻¹' ({I.subschemeι z} : Set X) = ({z} : Set I.subscheme) := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact (subschemeι_injective I).eq_iff
  rw [← hpre]
  exact (hclosed _ (subschemeι_mem_of_support_eq I T hT z)).preimage I.subschemeι.continuous

/-- The length over the base ring of a finite-support quotient is bounded
below by the sum of the colengths of its stalks. -/
@[stacks 0AGT "clause (3), the second inequality: the length over the base ring of the \
global sections of the quotient is at least the sum over the support points \
of the colengths of the stalks"]
public theorem length_globalSections_ge_sum_length_stalkQuotient
    {A : Type*} [CommRing A] {X : Scheme}
    (f : X ⟶ Spec (.of A)) (I : X.IdealSheafData)
    (T : Finset X)
    (hT : (I.support : Set X) = (T : Set X))
    (hclosed : ∀ x ∈ T, IsClosed ({x} : Set X)) :
    letI : Algebra A Γ(I.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of A)).inv ≫ (I.subschemeι ≫ f).appTop).hom.toAlgebra
    (∑ x ∈ T,
      Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ IdealSheafData.stalk I x)) ≤
      Module.length A Γ(I.subscheme, ⊤) := by
  classical
  let : Algebra A Γ(I.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of A)).inv ≫ (I.subschemeι ≫ f).appTop).hom.toAlgebra
  have := finite_subscheme_of_support_eq I T hT
  have := discreteTopology_subscheme_of_support_eq I T hT hclosed
  let eSpec : I.subscheme ≃ₜ PrimeSpectrum Γ(I.subscheme, ⊤) :=
    (Scheme.isoSpec I.subscheme).hom.homeomorph
  have : DiscreteTopology (PrimeSpectrum Γ(I.subscheme, ⊤)) := eSpec.discreteTopology
  have : Finite (PrimeSpectrum Γ(I.subscheme, ⊤)) :=
    (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp inferInstance).1
  let : Fintype (PrimeSpectrum Γ(I.subscheme, ⊤)) := Fintype.ofFinite _
  let eZT := subschemeEquivOfSupportEq I T hT
  let : Fintype I.subscheme := Fintype.ofFinite _
  let : Fintype T := Fintype.ofFinite _
  let targetLength : X → ℕ∞ := fun x =>
    Module.length (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ IdealSheafData.stalk I x)
  let localLength : PrimeSpectrum Γ(I.subscheme, ⊤) → ℕ∞ := fun p =>
    Module.length (Localization p.asIdeal.primeCompl) (Localization p.asIdeal.primeCompl)
  have htermZ (z : I.subscheme) :
      localLength (eSpec z) = targetLength (eZT z : X) := by
    let : ((Scheme.isoSpec I.subscheme).hom z).asIdeal.IsPrime :=
      (Scheme.isoSpec I.subscheme).hom z |>.isPrime
    calc
      localLength (eSpec z) =
          Module.length (I.subscheme.presheaf.stalk z) (I.subscheme.presheaf.stalk z) :=
        (length_subschemeStalk_eq_localization z).symm
      _ = targetLength (eZT z : X) := (length_idealStalk_quotient_eq_subschemeStalk I z).symm
  have hsum :
      (∑ p : PrimeSpectrum Γ(I.subscheme, ⊤), localLength p) =
      ∑ x ∈ T, targetLength x := by
    calc
      _ = ∑ z : I.subscheme, localLength (eSpec z) := eSpec.toEquiv.sum_comp localLength |>.symm
      _ = ∑ z : I.subscheme, targetLength (eZT z : X) :=
        Finset.sum_congr rfl fun z _ => htermZ z
      _ = ∑ x : T, targetLength x := eZT.sum_comp (fun x : T => targetLength x)
      _ = ∑ x ∈ T, targetLength x := (Finset.sum_subtype T (fun _ => Iff.rfl) targetLength).symm
  exact hsum.symm.trans_le (length_sum_localizations_le_length (A := A) (R := Γ(I.subscheme, ⊤)))

end Stacks.Blowup.Colength

end
