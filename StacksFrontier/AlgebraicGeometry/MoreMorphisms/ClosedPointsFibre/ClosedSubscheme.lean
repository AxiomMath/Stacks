module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.QuasiFinite.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ClosedPointsFibre.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageValuativeDiagram
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Criteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksFrontier.RingTheory.EssentialFiniteness.Defs
public import StacksFrontier.RingTheory.Noetherian.Spec

/-!
# A quasi-finite closed subscheme through a closed point of a fibre

Let `f : X ⟶ S` be locally of finite type with `S` locally Noetherian, and let `x` be a point of
`X` which is closed in its fibre. If `x` is a specialization of a point of an open subscheme `U`
lying over a different point of `S`, then there is a closed subscheme `Z ⊆ X` through `x` which is
quasi-finite over `S` at `x` and still meets `U` at a generalization of `x` lying over a different
point of `S`. The same conclusion holds when `x` only lies in the closure of an open subscheme
none of whose points lies over `f x`.

## Main results

* `Stacks.ClosedPointsFibre.exists_closedSubscheme_quasiFiniteAt_meeting_open`: a closed point
  of a fibre which is a specialization of a point of `U` over a different point of `S` lies on a
  closed subscheme quasi-finite over `S` at that point and meeting `U` at a generalization of it
  over a different point of `S`.
* `Stacks.ClosedPointsFibre.exists_closedSubscheme_quasiFiniteAt_meeting_open_of_mem_closure`:
  the same conclusion for a closed point of a fibre lying in the closure of an open subscheme
  disjoint from that fibre.

## References

* [Stacks Project, Tag 05GU](https://stacks.math.columbia.edu/tag/05GU)
* [Stacks Project, Tag 05GW](https://stacks.math.columbia.edu/tag/05GW)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.ClosedPointsFibre

/-- A point of `Spec` of a stalk maps to the closed point of the base stalk iff its image in `X`
lies over `f x`. -/
private theorem specMap_stalkMap_eq_closedPoint_iff {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (p : Spec (X.presheaf.stalk x)) :
    Spec.map (f.stalkMap x) p =
        (IsLocalRing.closedPoint (S.presheaf.stalk (f x)) : Spec (S.presheaf.stalk (f x))) ↔
      f (X.fromSpecStalk x p) = f x := by
  have h := congrArg (fun g : Spec (X.presheaf.stalk x) ⟶ S => g p)
    (Scheme.SpecMap_stalkMap_fromSpecStalk (f := f) (x := x))
  change S.fromSpecStalk (f x) (Spec.map (f.stalkMap x) p) = f (X.fromSpecStalk x p) at h
  have e := Scheme.fromSpecStalk_closedPoint (X := S) (x := f x)
  exact ⟨fun hp => by rw [← h, hp, e],
    fun hp => (S.fromSpecStalk (f x)).isEmbedding.injective (h.trans (hp.trans e.symm))⟩

/-- Let `f : X ⟶ S` be locally of finite type with `S` locally Noetherian, and let `x` be closed
in its fibre. If some point of the open `U` specializes to `x` and lies over a point other than
`f x`, then there are a closed immersion `i : Z ⟶ X` and a point `xZ` of `Z` over `x` at which
`i ≫ f` is quasi-finite, together with a generalization `zZ` of `xZ` mapping into `U` and lying
over a point other than `f x`. -/
@[stacks 05GU]
theorem exists_closedSubscheme_quasiFiniteAt_meeting_open
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (x : X) (U : X.Opens)
    (hx : IsClosed ({f.asFiber x} : Set (f.fiber (f x))))
    (hU : ∃ x' : X, x' ∈ U.1 ∧ x' ⤳ x ∧ f x' ≠ f x) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧
      ∃ xZ : Z, i xZ = x ∧ quasiFiniteAt (i ≫ f) xZ ∧
        ∃ zZ : Z, i zZ ∈ U.1 ∧ zZ ⤳ xZ ∧ f (i zZ) ≠ f x := by
  classical
  let A := S.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let φ : A →+* B := (f.stalkMap x).hom
  let : Algebra A B := φ.toAlgebra
  let : IsLocalHom φ := inferInstance
  have : Algebra.EssFiniteType A B := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  have hess : IsEssentiallyOfFiniteType A B φ := by
    show IsEssentiallyOfFiniteType A B (algebraMap A B)
    rcases (Algebra.essFiniteType_iff_exists_subalgebra A B).mp inferInstance with
      ⟨T, M, hT, hLoc⟩
    exact ⟨T, inferInstance, (algebraMap A T).toAlgebra, hT, M,
      (algebraMap T B).toAlgebra,
      ⟨IsScalarTower.of_algebraMap_eq' rfl, hLoc⟩⟩
  have hres :
      let := (IsLocalRing.ResidueField.map φ).toAlgebra
      let : Module (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
        (IsLocalRing.ResidueField.map φ).toAlgebra.toModule
      Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) := by
    let : Module (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
      (IsLocalRing.ResidueField.map φ).toAlgebra.toModule
    let : Algebra (S.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    exact (isClosed_asFiber_iff_finite_residueField f x).mp hx
  let V : Set (PrimeSpectrum B) := (X.fromSpecStalk x).base ⁻¹' U.1
  have hV : IsOpen V := U.2.preimage (X.fromSpecStalk x).continuous
  obtain ⟨x', hx'U, hspec, hfx'⟩ := hU
  obtain ⟨p, hp⟩ : x' ∈ Set.range (X.fromSpecStalk x) := by rwa [Scheme.range_fromSpecStalk]
  have hpV : p ∈ V := by
    change X.fromSpecStalk x p ∈ U.1
    simpa [hp] using hx'U
  have hpnot : p.asIdeal.comap φ ≠ IsLocalRing.maximalIdeal A := by
    intro heq
    have := (specMap_stalkMap_eq_closedPoint_iff f x p).mp (PrimeSpectrum.ext heq)
    exact hfx' (by simpa [hp] using this)
  obtain ⟨q, hqV, hqnot, C, hCcomm, hCalg, hCft, hCqf, M, hDalg, hTower, hLoc⟩ :=
    exists_quotient_isLocalization_quasiFinite_of_isOpen
      φ (inferInstance : IsLocalHom φ) hess hres V hV
      ⟨p, hpV, hpnot⟩
  let z : X := X.fromSpecStalk x q
  have hzx : z ⤳ x := by
    have hzrange : z ∈ Set.range (X.fromSpecStalk x) := ⟨q, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at hzrange
  let T : Closeds X := Closeds.closure ({z} : Set X)
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal T
  let Z : Scheme := I.subscheme
  let i : Z ⟶ X := I.subschemeι
  obtain ⟨xZ, hxZ⟩ : x ∈ Set.range i := by
    rw [I.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact specializes_iff_mem_closure.mp hzx
  obtain ⟨zZ, hzZ⟩ : z ∈ Set.range i := by
    rw [I.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact subset_closure (Set.mem_singleton z)
  have hspecXZ : zZ ⤳ xZ := by
    apply i.isEmbedding.isInducing.specializes_iff.mp
    simpa [hzZ, hxZ] using hzx
  have hzU : i zZ ∈ U.1 := by
    rw [hzZ]
    exact hqV
  have hfxneq : f (i zZ) ≠ f x := by
    intro hEq
    have hqmax := (specMap_stalkMap_eq_closedPoint_iff f x q).mpr (by rw [← hEq, hzZ])
    exact hqnot (congrArg PrimeSpectrum.asIdeal hqmax)
  have hqfinite : quasiFiniteAt (i ≫ f) xZ := by
    let g := i ≫ f
    have : LocallyOfFiniteType g := inferInstance
    have hgx : g xZ = f x := by simp [g, hxZ]
    let D := B ⧸ q.asIdeal
    let π : B →+* D := Ideal.Quotient.mk q.asIdeal
    let ψ : A →+* D := π.comp φ
    let : Algebra A D := ψ.toAlgebra
    let : Algebra A C := hCalg
    let : Algebra C D := hDalg
    let : IsScalarTower A C D := hTower
    let : IsLocalization M D := hLoc
    let : Algebra.QuasiFinite A C := hCqf
    have : Algebra.QuasiFinite A D :=
      @Algebra.QuasiFinite.of_isLocalization A C D _ _ _ hCalg ψ.toAlgebra hDalg
        hTower M hLoc hCqf
    let : Nontrivial D := Ideal.Quotient.nontrivial_iff.mpr q.isPrime.ne_top
    let : IsLocalRing D := IsLocalRing.of_surjective' π Ideal.Quotient.mk_surjective
    let : IsLocalHom π := IsLocalHom.of_surjective π Ideal.Quotient.mk_surjective
    have hfib : ∀ w : g.fiber (g xZ), f (i (g.fiberι (g xZ) w)) = f x := fun w => by
      have hfac := congrArg (fun k : g.fiber (g xZ) ⟶ S => k w) (g.fiber_fac (g xZ))
      change f (i (g.fiberι (g xZ) w)) =
        S.fromSpecResidueField (g xZ) (g.fiberToSpecResidueField (g xZ) w) at hfac
      rw [Scheme.fromSpecResidueField_apply] at hfac
      exact hfac.trans hgx
    have hclosed : IsClosed ({g.asFiber xZ} : Set (g.fiber (g xZ))) := by
      let j : g.fiber (g xZ) → f.fiber (f x) := fun w =>
        (f.fiberHomeo (f x)).symm ⟨i (g.fiberι (g xZ) w), hfib w⟩
      have hjcont : Continuous j := by
        apply (f.fiberHomeo (f x)).symm.continuous.comp
        exact (i.continuous.comp (g.fiberι (g xZ)).continuous).subtype_mk _
      have hjpre : j ⁻¹' {f.asFiber x} = {g.asFiber xZ} := by
        ext w
        constructor
        · intro hw
          have hiy : i (g.fiberι (g xZ) w) = x := by
            have hw' : j w = f.asFiber x := by
              simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hw
            have h := congrArg (f.fiberι (f x)) hw'
            simpa [j] using h
          have hy : g.fiberι (g xZ) w = xZ :=
            i.isEmbedding.injective (by simpa [hxZ] using hiy)
          exact Set.mem_singleton_iff.mpr <| (g.fiberι (g xZ)).isEmbedding.injective <| by
            simpa [Scheme.Hom.fiberι_asFiber] using hy
        · intro hw
          rw [Set.mem_singleton_iff] at hw
          subst w
          apply (f.fiberι (f x)).isEmbedding.injective
          simp [j, hxZ]
      exact hjpre ▸ hx.preimage hjcont
    have hnoSpec :
        ¬ ∃ w : g.fiber (g xZ), w ≠ g.asFiber xZ ∧ w ⤳ g.asFiber xZ := by
      rintro ⟨w, hne, hspec⟩
      let yZ := g.fiberι (g xZ) w
      have hybase : f (i yZ) = f x := hfib w
      have hySpec : yZ ⤳ xZ := by
        simpa [yZ, Scheme.Hom.fiberι_asFiber] using
          hspec.map (g.fiberι (g xZ)).continuous
      have hiSpec : i yZ ⤳ x := by
        simpa [hxZ] using hySpec.map i.continuous
      obtain ⟨p, hp⟩ : ∃ p : PrimeSpectrum B, X.fromSpecStalk x p = i yZ := by
        have hrange : i yZ ∈ Set.range (X.fromSpecStalk x) := by rwa [Scheme.range_fromSpecStalk]
        exact hrange
      have hiyT : i yZ ∈ T := by
        have hmem : i yZ ∈ (I.support : Set X) := by
          rw [← I.range_subschemeι]
          exact ⟨yZ, rfl⟩
        simpa [I, Scheme.IdealSheafData.coe_support_vanishingIdeal] using hmem
      have hqle : q.asIdeal ≤ p.asIdeal := by
        have hspeczy : z ⤳ i yZ := specializes_iff_mem_closure.mpr hiyT
        have hspecqp : q ⤳ p :=
          (Scheme.Hom.isEmbedding (X.fromSpecStalk x)).isInducing.specializes_iff.mp
            (by simpa [z, hp] using hspeczy)
        exact (PrimeSpectrum.asIdeal_le_asIdeal q p).mpr
          ((PrimeSpectrum.le_iff_specializes q p).mpr hspecqp)
      have hpc : p.asIdeal.comap φ = IsLocalRing.maximalIdeal A := by
        exact congrArg PrimeSpectrum.asIdeal
          ((specMap_stalkMap_eq_closedPoint_iff f x p).mpr (by rw [hp, hybase]))
      let r : Ideal D := p.asIdeal.map π
      let : r.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hqle
      have hrle : r ≤ IsLocalRing.maximalIdeal D :=
        IsLocalRing.le_maximalIdeal_of_isPrime r
      have hrpre : r.comap π = p.asIdeal := by
        rw [Ideal.comap_map_of_surjective' π Ideal.Quotient.mk_surjective, sup_eq_left]
        exact fun b hb => hqle (Ideal.Quotient.eq_zero_iff_mem.mp hb)
      let : IsLocalHom ψ := RingHom.isLocalHom_comp π φ
      have hrunder : Ideal.under A r = Ideal.under A (IsLocalRing.maximalIdeal D) := by
        show r.comap ψ = (IsLocalRing.maximalIdeal D).comap ψ
        calc
          r.comap ψ = (r.comap π).comap φ := by simp [ψ, Ideal.comap_comap]
          _ = IsLocalRing.maximalIdeal A := by rw [hrpre, hpc]
          _ = (IsLocalRing.maximalIdeal D).comap ψ := (IsLocalRing.maximalIdeal_comap ψ).symm
      have hrmax : r = IsLocalRing.maximalIdeal D :=
        Algebra.QuasiFinite.eq_of_le_of_under_eq r (IsLocalRing.maximalIdeal D) hrle hrunder
      have hpmax := congrArg (Ideal.comap π) hrmax
      rw [hrpre, IsLocalRing.maximalIdeal_comap] at hpmax
      have hpclosed : p = IsLocalRing.closedPoint B := PrimeSpectrum.ext hpmax
      have hiy : i yZ = x := by
        rw [← hp, hpclosed, Scheme.fromSpecStalk_closedPoint]
      have hyEq : yZ = xZ := i.isEmbedding.injective (by simpa [hxZ] using hiy)
      apply hne
      apply (g.fiberι (g xZ)).isEmbedding.injective
      simpa [yZ, Scheme.Hom.fiberι_asFiber] using hyEq
    have hcond : IsClosed ({g.asFiber xZ} : Set (g.fiber (g xZ))) ∧
        ¬ ∃ w : g.fiber (g xZ), w ≠ g.asFiber xZ ∧ w ⤳ g.asFiber xZ :=
      ⟨hclosed, hnoSpec⟩
    exact ((quasiFiniteAt_tfae g xZ).out 3 1).mp hcond
  exact ⟨Z, i, inferInstance, xZ, by simpa [Scheme.IdealSheafData.subschemeι_apply] using hxZ,
    hqfinite, zZ, hzU, hspecXZ, hfxneq⟩

/-- Let `f : X ⟶ S` be locally of finite type with `S` locally Noetherian, and let `x` be closed
in its fibre. If `x` lies in the closure of an open `U` no point of which lies over `f x`, then
there are a closed immersion `i : Z ⟶ X` and a point `xZ` of `Z` over `x` at which `i ≫ f` is
quasi-finite, together with a generalization `zZ` of `xZ` mapping into `U` and lying over a point
other than `f x`. -/
@[stacks 05GW]
theorem exists_closedSubscheme_quasiFiniteAt_meeting_open_of_mem_closure
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (x : X) (U : X.Opens)
    (hx : IsClosed ({f.asFiber x} : Set (f.fiber (f x))))
    (hU : ∀ y : X, y ∈ U.1 → f y ≠ f x)
    (hclosure : x ∈ closure (U.1 : Set X)) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧
      ∃ xZ : Z, i xZ = x ∧ quasiFiniteAt (i ≫ f) xZ ∧
        ∃ zZ : Z, i zZ ∈ U.1 ∧ zZ ⤳ xZ ∧ f (i zZ) ≠ f x := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let g : U.toScheme ⟶ X := U.ι
  have : QuasiCompact g := inferInstance
  have hrange : Set.range g.base ⊆ Set.range g.imageι.base := by
    rintro y ⟨y', rfl⟩
    exact ⟨g.toImage y', congrArg (fun k : U.toScheme ⟶ X => k y') g.toImage_imageι⟩
  obtain ⟨z, hz⟩ : x ∈ Set.range g.imageι.base := by
    apply (g.imageι.isClosedEmbedding.isClosed_range.closure_subset_iff.mpr hrange)
    simpa [show Set.range g = (U.1 : Set X) from U.range_ι] using hclosure
  obtain ⟨y, hspec⟩ := exists_specializes_of_image_point g z
  exact exists_closedSubscheme_quasiFiniteAt_meeting_open f x U hx
    ⟨g y, y.2, by simpa [hz] using hspec, hU (g y) y.2⟩

end Stacks.ClosedPointsFibre

end
