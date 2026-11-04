module

public import StacksFrontier.AlgebraicGeometry.Discriminant.TraceElement
public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.CommonFactorization
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.Pairing
public import StacksFrontier.RingTheory.ZariskisMainTheorem

/-!
# Refining and relocating a finite-open factorization

A quasi-finite algebra admits many finite-open factorizations, and comparing constructions made
from two of them means moving between them. This file collects the four moves that are needed:
refining two factorizations to a common one, cutting a factorization down to the image of its
intermediate algebra, transporting a factorization along an isomorphism of the target, and
pushing a factorization forward along an away localization of the target.

The last of these rests on a ring-theoretic observation: if a basic open of the intermediate
algebra lands inside the image of the spectrum of an away localization of the target, then the
localizing element is already invertible on that basic open, so the away localizations of the
target and of its localization agree.

## Main definitions

* `Stacks.Discriminant.identityFactorization` is the finite-open factorization of a finite
  algebra through itself.
* `Stacks.Discriminant.retargetFactorization` transports a finite-open factorization along an
  algebra isomorphism of its target.
* `Stacks.Discriminant.locFact` is the finite-open factorization of an away localization of the
  target obtained from one of the target itself, with the same intermediate algebra.

## Main results

* `Stacks.Discriminant.unit_image_of_range_localization`: the localizing element becomes a unit
  after inverting an element of the intermediate algebra whose basic open lies in the image of
  the spectrum of the localization.
* `Stacks.Discriminant.awayMap_bijective_if_unit`: inverting an element of the target is
  unaffected by first localizing away from an element that is already invertible there.
* `Stacks.Discriminant.awayMap_bijective_refinement_at`: the away-localization condition passes
  to a refinement of the intermediate algebra.
* `Stacks.Discriminant.exists_common_finite_open_factorization`: two finite-open factorizations
  are both refined by a third one whose intermediate algebra injects into the target.
* `Stacks.Discriminant.exists_image_factorization`: a finite-open factorization may be replaced
  by the image of its intermediate algebra in the target.

## Implementation notes

`exists_common_finite_open_factorization` goes through the scheme-theoretic refinement of Tag
0BT0, which lives in one universe; the two intermediate algebras are therefore lifted to a
common universe first, and `Stacks.Discriminant.specMap_ulift_isOpenImmersion` converts the
ring-theoretic open-immersion data across that lift.

## References

* [Stacks Project, Tag 0BT2](https://stacks.math.columbia.edu/tag/0BT2)
-/

@[expose] public section

namespace Stacks.Discriminant

universe u v w x y

open Topology

/-- A finite algebra is its own finite-open factorization, through the identity. -/
noncomputable def identityFactorization
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] : FiniteOpenFactorization.{u, v, v} A B := by
  let : Algebra B B := Algebra.id B
  let : IsScalarTower A B B := IsScalarTower.of_algebraMap_eq' (by
    ext a
    rfl)
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ?_, ?_⟩
  · change IsOpenEmbedding (id : PrimeSpectrum B → PrimeSpectrum B)
    exact Topology.IsOpenEmbedding.id
  · intro g hg
    change Function.Bijective (Localization.awayMap (RingHom.id B) g)
    apply Function.bijective_iff_has_inverse.mpr
    refine ⟨RingHom.id _, ?_, ?_⟩ <;>
      intro x <;>
      change IsLocalization.map (M := Submonoid.powers g) (T := Submonoid.powers g)
        (Localization.Away g) (RingHom.id B) le_rfl x = x <;>
      exact IsLocalization.map_id x

/-- If the basic open of an element `c` of the intermediate algebra lies inside the image of the
spectrum of an away localization `Bg` of the target, then the localizing element `g` becomes a
unit in the away localization of the target at `c`. -/
lemma unit_image_of_range_localization
    {A : Type u} {B : Type v} {Bg : Type w}
    [CommRing A] [CommRing B] [CommRing Bg]
    [Algebra A B] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
    (g : B) [IsLocalization.Away g Bg]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    [Algebra F.middle Bg] [IsScalarTower F.middle B Bg]
    (c : F.middle)
    (hc : (PrimeSpectrum.basicOpen c : Set (PrimeSpectrum F.middle)) ⊆
        Set.range (PrimeSpectrum.comap (algebraMap F.middle Bg))) :
    IsUnit (algebraMap B (Localization.Away (algebraMap F.middle B c)) g) := by
  let Bc := Localization.Away (algebraMap F.middle B c)
  by_contra hnot
  obtain ⟨M, hM, hMg⟩ := exists_max_ideal_of_mem_nonunits hnot
  let q : PrimeSpectrum B := ⟨M.comap (algebraMap B Bc), hM.isPrime.comap _⟩
  let p : PrimeSpectrum F.middle := PrimeSpectrum.comap (algebraMap F.middle B) q
  have hpc : p ∈ PrimeSpectrum.basicOpen c := by
    show c ∉ p.asIdeal
    intro hcp
    have : algebraMap B Bc (algebraMap F.middle B c) ∈ M := hcp
    exact hM.ne_top (Ideal.eq_top_of_isUnit_mem _ this
      (IsLocalization.Away.algebraMap_isUnit _))
  obtain ⟨q', hq'⟩ := hc hpc
  let q0 : PrimeSpectrum B := PrimeSpectrum.comap (algebraMap B Bg) q'
  have hq0 : PrimeSpectrum.comap (algebraMap F.middle B) q0 = p := by
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap F.middle B)
      (Ideal.comap (algebraMap B Bg) q'.asIdeal) = p.asIdeal
    rw [Ideal.comap_comap]
    have htower : (algebraMap B Bg).comp (algebraMap F.middle B) =
        algebraMap F.middle Bg := by
      ext d
      exact (IsScalarTower.algebraMap_apply F.middle B Bg d).symm
    rw [htower]
    exact congrArg PrimeSpectrum.asIdeal hq'
  have hqeq : q0 = q := F.isOpenEmbedding_comap.injective hq0
  have hnotq : g ∉ q.asIdeal := by
    rw [← hqeq]
    intro hgm
    apply q'.2.ne_top
    change algebraMap B Bg g ∈ q'.asIdeal at hgm
    exact Ideal.eq_top_of_isUnit_mem _ hgm (IsLocalization.Away.algebraMap_isUnit g)
  exact hnotq hMg

/-- Inverting an element `c` of a ring is unaffected by first inverting an element `g` that is
already a unit after inverting `c`: the induced map of away localizations is bijective. -/
lemma awayMap_bijective_if_unit
    {B : Type v} {Bg : Type w}
    [CommRing B] [CommRing Bg] [Algebra B Bg]
    (g c : B) [IsLocalization.Away g Bg]
    (hg : IsUnit (algebraMap B (Localization.Away c) g)) :
    Function.Bijective (Localization.awayMap (algebraMap B Bg) c) := by
  let Bc := Localization.Away c
  let T := Localization.Away (algebraMap B Bg c)
  let φ := Localization.awayMap (algebraMap B Bg) c
  let ψ₁ : Bg →+* Bc := IsLocalization.Away.lift g (g := algebraMap B Bc) hg
  have hcunit : IsUnit (ψ₁ (algebraMap B Bg c)) := by
    rw [IsLocalization.Away.lift_eq g hg]
    exact IsLocalization.Away.algebraMap_isUnit c
  let ψ : T →+* Bc := IsLocalization.Away.lift (algebraMap B Bg c) (g := ψ₁) hcunit
  have hy : Submonoid.powers c ≤
      Submonoid.comap (algebraMap B Bg) (Submonoid.powers (algebraMap B Bg c)) := by
    intro t ht
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff t c).mp ht
    exact ⟨n, by simp⟩
  have hmap : φ.comp (algebraMap B Bc) =
      (algebraMap Bg T).comp (algebraMap B Bg) := by
    show (IsLocalization.map T (algebraMap B Bg) hy).comp (algebraMap B Bc) = _
    exact IsLocalization.map_comp hy
  have hBg : φ.comp ψ₁ = algebraMap Bg T := by
    apply IsLocalization.ringHom_ext (.powers g)
    calc
      (φ.comp ψ₁).comp (algebraMap B Bg) =
          φ.comp (ψ₁.comp (algebraMap B Bg)) := by rw [RingHom.comp_assoc]
      _ = φ.comp (algebraMap B Bc) := by rw [IsLocalization.Away.lift_comp]
      _ = (algebraMap Bg T).comp (algebraMap B Bg) := hmap
  have hleft : ψ.comp φ = RingHom.id Bc := by
    apply IsLocalization.ringHom_ext (.powers c)
    calc
      (ψ.comp φ).comp (algebraMap B Bc) =
          ψ.comp (φ.comp (algebraMap B Bc)) := by rw [RingHom.comp_assoc]
      _ = ψ.comp ((algebraMap Bg T).comp (algebraMap B Bg)) := by rw [hmap]
      _ = (ψ.comp (algebraMap Bg T)).comp (algebraMap B Bg) := by rw [← RingHom.comp_assoc]
      _ = ψ₁.comp (algebraMap B Bg) := by rw [IsLocalization.Away.lift_comp]
      _ = algebraMap B Bc := by rw [IsLocalization.Away.lift_comp]
      _ = (RingHom.id Bc).comp (algebraMap B Bc) := by rfl
  have hright : φ.comp ψ = RingHom.id T := by
    apply IsLocalization.ringHom_ext (.powers (algebraMap B Bg c))
    calc
      (φ.comp ψ).comp (algebraMap Bg T) =
          φ.comp (ψ.comp (algebraMap Bg T)) := by rw [RingHom.comp_assoc]
      _ = φ.comp ψ₁ := by rw [IsLocalization.Away.lift_comp]
      _ = algebraMap Bg T := hBg
      _ = (RingHom.id T).comp (algebraMap Bg T) := by rfl
  constructor
  · intro a b hab
    have hla : ψ (φ a) = a := (DFunLike.congr_fun hleft a).trans rfl
    have hlb : ψ (φ b) = b := (DFunLike.congr_fun hleft b).trans rfl
    calc
      a = ψ (φ a) := hla.symm
      _ = ψ (φ b) := congrArg ψ hab
      _ = b := hlb
  · intro b
    exact ⟨ψ b, (DFunLike.congr_fun hright b).trans rfl⟩

/-- The away-localization map sends the image of `a` to the image of `f a`. -/
private theorem awayMap_algebraMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (c a : R) :
    Localization.awayMap f c (algebraMap R (Localization.Away c) a) =
      algebraMap S (Localization.Away (f c)) (f a) :=
  IsLocalization.map_eq _ _

/-- The away-localization condition of a finite-open factorization passes to a refinement: if
the intermediate algebra maps to a further algebra `C` injecting into the target, then the away
localization of the target at the image of an admissible element is again bijective. -/
theorem awayMap_bijective_refinement_at
    {A : Type u} {B : Type v} {C : Type x}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra C B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (r : F.middle →ₐ[A] C)
    (hcomp : (algebraMap C B).comp r.toRingHom = algebraMap F.middle B)
    (hinj : Function.Injective (algebraMap C B))
    (g : F.middle)
    (hFaway : Function.Bijective (Localization.awayMap (algebraMap F.middle B) g)) :
    Function.Bijective (Localization.awayMap (algebraMap C B) (r g)) := by
  let gC := r g
  have hden : algebraMap C B gC = algebraMap F.middle B g := by
    exact congrArg (fun φ : F.middle →+* B => φ g) hcomp
  let : IsLocalization.Away (algebraMap C B gC)
      (Localization.Away (algebraMap F.middle B g)) := by
    rw [hden]
    infer_instance
  let eTarget : Localization.Away (algebraMap C B gC) ≃ₐ[B]
      Localization.Away (algebraMap F.middle B g) :=
    IsLocalization.algEquiv (Submonoid.powers (algebraMap C B gC)) _ _
  have hcast (b : B) :
      eTarget (algebraMap B (Localization.Away (algebraMap C B gC)) b) =
        algebraMap B (Localization.Away (algebraMap F.middle B g)) b := by
    exact eTarget.commutes b
  have hcompAway :
      (eTarget.toRingHom.comp (Localization.awayMap (algebraMap C B) gC)).comp
        (Localization.awayMap r.toRingHom g) =
      Localization.awayMap (algebraMap F.middle B) g := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers g)
    ext a
    have hscalar : algebraMap C B (r a) = algebraMap F.middle B a :=
      congrArg (fun φ : F.middle →+* B => φ a) hcomp
    calc
      eTarget (Localization.awayMap (algebraMap C B) gC
          (Localization.awayMap r.toRingHom g
            (algebraMap F.middle (Localization.Away g) a))) =
        eTarget (algebraMap B (Localization.Away (algebraMap C B gC))
          (algebraMap C B (r a))) := by
        rw [awayMap_algebraMap r.toRingHom g a]
        exact congrArg eTarget (awayMap_algebraMap (algebraMap C B) gC (r a))
      _ = algebraMap B (Localization.Away (algebraMap F.middle B g))
          (algebraMap F.middle B a) := by rw [hscalar, hcast]
      _ = Localization.awayMap (algebraMap F.middle B) g
          (algebraMap F.middle (Localization.Away g) a) := by
        exact (awayMap_algebraMap _ _ _).symm
  have hginj : Function.Injective
      (Localization.awayMap (algebraMap C B) gC) := by
    unfold Localization.awayMap IsLocalization.Away.map
    exact IsLocalization.map_injective_of_injective _ _ _ hinj
  have hgsurj : Function.Surjective
      (Localization.awayMap (algebraMap C B) gC) := by
    intro z
    obtain ⟨z', hz'⟩ := hFaway.2 (eTarget z)
    refine ⟨Localization.awayMap r.toRingHom g z', ?_⟩
    apply eTarget.injective
    calc
      eTarget (Localization.awayMap (algebraMap C B) gC
          (Localization.awayMap r.toRingHom g z')) =
        Localization.awayMap (algebraMap F.middle B) g z' :=
          congrArg (fun φ : Localization.Away g →+*
            Localization.Away (algebraMap F.middle B g) => φ z') hcompAway
      _ = eTarget z := hz'
  exact ⟨hginj, hgsurj⟩

/-- An algebra `C` between the intermediate algebra of a finite-open factorization and the
target, injecting into the target, inherits the away-localization condition at every element
whose basic open lies in the image of the spectrum of the target. -/
private theorem awayMap_bijective_of_factorization_refinement
    {A : Type u} {B : Type v} {C : Type x}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra C B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (r : F.middle →ₐ[A] C)
    (hcomp : (algebraMap C B).comp r.toRingHom =
      algebraMap F.middle B)
    (hinj : Function.Injective (algebraMap C B))
    (c : C)
    (hc : (PrimeSpectrum.basicOpen c : Set (PrimeSpectrum C)) ⊆
      Set.range (PrimeSpectrum.comap (algebraMap C B))) :
    Function.Bijective (Localization.awayMap (algebraMap C B) c) := by
  let : CommRing F.middle := F.commRingMiddle
  let : Algebra A F.middle := F.algebraMiddle
  let : Algebra F.middle B := F.algebraTarget
  let : IsScalarTower A F.middle B := F.scalarTower
  have hlocal : ∀ q : PrimeSpectrum B, ∃ c : C,
      algebraMap C B c ∉ q.asIdeal ∧
        Function.Bijective (Localization.awayMap (algebraMap C B) c) := by
    intro q
    let p := PrimeSpectrum.comap (algebraMap F.middle B) q
    obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hpg, hg⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
        (show p ∈ Set.range (PrimeSpectrum.comap (algebraMap F.middle B)) from ⟨q, rfl⟩)
        F.isOpenEmbedding_comap.isOpen_range
    have hfg : algebraMap F.middle B g ∉ q.asIdeal := by
      simpa [p, PrimeSpectrum.comap_asIdeal] using hpg
    have hFaway := F.awayMap_bijective g hg
    have hden : algebraMap C B (r g) = algebraMap F.middle B g :=
      congrArg (fun φ : F.middle →+* B => φ g) hcomp
    exact ⟨r g, by simpa only [hden] using hfg,
      awayMap_bijective_refinement_at F r hcomp hinj g hFaway⟩
  exact awayMap_bijective_of_basicOpen_subset_range
    (algebraMap C B) hinj hlocal c hc

/-- Two finite-open factorizations of the same algebra are refined by a third one whose
intermediate algebra injects into the target, with algebra maps from both given intermediate
algebras compatible with the maps to the target. -/
theorem exists_common_finite_open_factorization
    {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (G : FiniteOpenFactorization.{u, v, y} A B) :
    ∃ H : FiniteOpenFactorization.{u, v, max v x} A B,
      ∃ rF : F.middle →ₐ[A] H.middle,
      ∃ rG : G.middle →ₐ[A] H.middle,
        Function.Injective (algebraMap H.middle B) ∧
        (∀ c, algebraMap H.middle B (rF c) = algebraMap F.middle B c) ∧
        ∀ c, algebraMap H.middle B (rG c) = algebraMap G.middle B c := by
  let : CommRing F.middle := F.commRingMiddle
  let : Algebra A F.middle := F.algebraMiddle
  let : Algebra F.middle B := F.algebraTarget
  let : IsScalarTower A F.middle B := F.scalarTower
  let : Module.Finite A F.middle := F.finite_middle
  let : CommRing G.middle := G.commRingMiddle
  let : Algebra A G.middle := G.algebraMiddle
  let : Algebra G.middle B := G.algebraTarget
  let : IsScalarTower A G.middle B := G.scalarTower
  let : Module.Finite A G.middle := G.finite_middle
  let B₁ := F.middle
  let B₂ := G.middle
  let B' := ULift.{max v x, v} B
  let B₁' := ULift.{max v x, x} B₁
  let eB : B' ≃+* B := ULift.ringEquiv
  let fF : B₁ →ₐ[A] B := IsScalarTower.toAlgHom A B₁ B
  let fG : B₂ →ₐ[A] B := IsScalarTower.toAlgHom A B₂ B
  let fF' : B₁' →ₐ[A] B' := {
    toRingHom := fF.toRingHom.ulift.{max v x, max v x}
    commutes' := by
      intro a
      apply ULift.ext
      exact fF.commutes a }
  let fG' : B₂ →ₐ[A] B' := {
    toRingHom := eB.symm.toRingHom.comp fG.toRingHom
    commutes' := by
      intro a
      apply ULift.ext
      exact fG.commutes a }
  have hOpenF : Topology.IsOpenEmbedding (PrimeSpectrum.comap fF.toRingHom) := by
    show Topology.IsOpenEmbedding (PrimeSpectrum.comap (algebraMap F.middle B))
    exact F.isOpenEmbedding_comap
  have hAwayF : ∀ g : B₁,
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum B₁)) ⊆
        Set.range (PrimeSpectrum.comap fF.toRingHom) →
      Function.Bijective (Localization.awayMap fF.toRingHom g) := by
    intro g hg
    show Function.Bijective (Localization.awayMap (algebraMap F.middle B) g)
    exact F.awayMap_bijective g hg
  let : AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom fF'.toRingHom)) :=
    specMap_ulift_isOpenImmersion fF.toRingHom hOpenF hAwayF
  obtain ⟨C, hfin, hopenC, hdom⟩ :=
    exists_finite_subalgebra_dominating fF' fG'
  obtain ⟨gF, hgF⟩ := hdom.1
  obtain ⟨gG, hgG⟩ := hdom.2
  let fC : C →+* B := eB.toRingHom.comp C.val.toRingHom
  let upF : B₁ →ₐ[A] B₁' := {
    toRingHom := (ULift.ringEquiv : B₁' ≃+* B₁).symm.toRingHom
    commutes' := by intro a; rfl }
  let rF : B₁ →ₐ[A] C := gF.comp upF
  let rG : B₂ →ₐ[A] C := gG
  have hcompF : fC.comp rF.toRingHom = fF.toRingHom := by
    ext b
    have h := congrArg (fun φ : B₁' →ₐ[A] B' => eB (φ (ULift.up b))) hgF
    simpa [fC, fF, fF', rF, upF, eB, ULift.ringEquiv, RingHom.ulift] using h
  have hcompG : fC.comp rG.toRingHom = fG.toRingHom := by
    ext b
    have h := congrArg (fun φ : B₂ →ₐ[A] B' => eB (φ b)) hgG
    simpa [fC, fG, fG', rG, eB, ULift.ringEquiv] using h
  let : CommRing C := inferInstance
  let : Algebra A C := inferInstance
  let : Algebra C B := fC.toAlgebra
  let hscalar : IsScalarTower A C B := IsScalarTower.of_algebraMap_eq' (by
    ext a
    show fC (algebraMap A C a) = algebraMap A B a
    calc
      fC (algebraMap A C a) = fC (rF (algebraMap A B₁ a)) := by rw [rF.commutes]
      _ = fF (algebraMap A B₁ a) :=
        congrArg (fun φ : B₁ →+* B => φ (algebraMap A B₁ a)) hcompF
      _ = algebraMap A B a := fF.commutes a)
  let : IsScalarTower A C B := hscalar
  have hinj : Function.Injective fC := by
    intro a b hab
    apply Subtype.ext
    exact eB.injective hab
  have hEmbedC : Topology.IsOpenEmbedding (PrimeSpectrum.comap fC) := by
    have : AlgebraicGeometry.IsOpenImmersion
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom C.val.toRingHom)) := hopenC
    have h0 : Topology.IsOpenEmbedding (PrimeSpectrum.comap C.val.toRingHom) := by
      show Topology.IsOpenEmbedding (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom C.val.toRingHom)).base
      exact (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom C.val.toRingHom)).isOpenEmbedding
    let hB := PrimeSpectrum.homeomorphOfRingEquiv eB
    have hmap : PrimeSpectrum.comap fC =
        (PrimeSpectrum.comap C.val.toRingHom) ∘ (PrimeSpectrum.comap eB.toRingHom) := by
      rw [PrimeSpectrum.comap_comp]
    rw [hmap]
    exact h0.comp hB.symm.isOpenEmbedding
  let H : FiniteOpenFactorization.{u, v, max v x} A B := {
    middle := C
    commRingMiddle := inferInstance
    algebraMiddle := inferInstance
    algebraTarget := fC.toAlgebra
    scalarTower := hscalar
    finite_middle := hfin
    isOpenEmbedding_comap := hEmbedC
    awayMap_bijective := by
      intro c hc
      exact awayMap_bijective_of_factorization_refinement F rF hcompF hinj c hc }
  refine ⟨H, rF, rG, hinj, ?_, ?_⟩
  · intro c
    exact congrArg (fun φ : B₁ →+* B => φ c) hcompF
  · intro c
    exact congrArg (fun φ : B₂ →+* B => φ c) hcompG

/-- A finite-open factorization may be replaced by the one through the image of its intermediate
algebra in the target, by a surjection compatible with the maps to the target. -/
theorem exists_image_factorization
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) :
    ∃ K : FiniteOpenFactorization.{u, v, v} A B,
      ∃ q : F.middle →ₐ[A] K.middle,
        Function.Surjective q ∧ Function.Injective (algebraMap K.middle B) ∧
          ∀ c, algebraMap K.middle B (q c) = algebraMap F.middle B c := by
  let f := IsScalarTower.toAlgHom A F.middle B
  let C := f.range
  let q : F.middle →ₐ[A] C := f.rangeRestrict
  have hq : Function.Surjective q := f.rangeRestrict_surjective
  have hc : (algebraMap C B).comp q.toRingHom = algebraMap F.middle B := rfl
  have he := PrimeSpectrum.isEmbedding_comap_of_surjective C q.toRingHom hq
  have hi : Function.Injective (PrimeSpectrum.comap (algebraMap C B)) := by
    intro p p' h
    exact F.isOpenEmbedding_comap.injective (congrArg (PrimeSpectrum.comap q.toRingHom) h)
  have ho : Topology.IsOpenEmbedding (PrimeSpectrum.comap (algebraMap C B)) := by
    apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact PrimeSpectrum.continuous_comap _
    · exact hi
    · intro U hU
      have hset : PrimeSpectrum.comap (algebraMap C B) '' U =
          PrimeSpectrum.comap q.toRingHom ⁻¹'
            (PrimeSpectrum.comap (algebraMap F.middle B) '' U) := by
        ext p
        constructor
        · rintro ⟨p', hp', rfl⟩
          exact ⟨p', hp', rfl⟩
        · rintro ⟨p', hp', h⟩
          exact ⟨p', hp', he.injective h⟩
      rw [hset]
      exact (F.isOpenEmbedding_comap.isOpenMap U hU).preimage he.continuous
  let K : FiniteOpenFactorization.{u, v, v} A B := {
    middle := C
    commRingMiddle := inferInstance
    algebraMiddle := inferInstance
    algebraTarget := inferInstance
    scalarTower := inferInstance
    finite_middle := Module.Finite.of_surjective q.toLinearMap hq
    isOpenEmbedding_comap := ho
    awayMap_bijective := fun c hc' =>
      awayMap_bijective_of_factorization_refinement F q hc Subtype.val_injective c hc' }
  exact ⟨K, q, hq, Subtype.val_injective, fun _ => rfl⟩

/-- The finite-open factorization obtained by transporting one along an algebra isomorphism of
its target.  The intermediate algebra is unchanged, and is reducibly so: constructions on
relative dualizing modules need that equality to be visible to unification. -/
abbrev retargetFactorization
    {A : Type u} {D : Type v} {B : Type w}
    [CommRing A] [CommRing D] [CommRing B] [Algebra A D] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, x} A D) (e : D ≃ₐ[A] B) :
    FiniteOpenFactorization.{u, w, x} A B := by
  let : Algebra F.middle D := F.algebraTarget
  let : IsScalarTower A F.middle D := F.scalarTower
  let target : F.middle →+* B := e.toRingHom.comp (algebraMap F.middle D)
  let : Algebra F.middle B := target.toAlgebra
  have hTower : IsScalarTower A F.middle B := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change algebraMap A B a = target (algebraMap A F.middle a)
    calc
      algebraMap A B a = e (algebraMap A D a) := (e.commutes a).symm
      _ = e (algebraMap F.middle D (algebraMap A F.middle a)) := by
        rw [IsScalarTower.algebraMap_apply A F.middle D a]
      _ = target (algebraMap A F.middle a) := rfl)
  have hOpen : Topology.IsOpenEmbedding (PrimeSpectrum.comap target) := by
    have hHome : IsHomeomorph (PrimeSpectrum.comap e.toRingHom) :=
      PrimeSpectrum.isHomeomorph_comap_of_bijective e.bijective
    have hcomp : PrimeSpectrum.comap target =
        (PrimeSpectrum.comap (algebraMap F.middle D)) ∘
          (PrimeSpectrum.comap e.toRingHom) := by
      rw [PrimeSpectrum.comap_comp]
    rw [hcomp]
    exact F.isOpenEmbedding_comap.comp hHome.isOpenEmbedding
  refine {
    middle := F.middle
    commRingMiddle := F.commRingMiddle
    algebraMiddle := F.algebraMiddle
    algebraTarget := target.toAlgebra
    scalarTower := hTower
    finite_middle := F.finite_middle
    isOpenEmbedding_comap := hOpen
    awayMap_bijective := ?_ }
  intro c hc
  let d := algebraMap F.middle D c
  let b := algebraMap F.middle B c
  have hdb : e d = b := rfl
  let TD := Localization.Away d
  let TB := Localization.Away b
  have : IsLocalization.Away (e d) TB := by
    rw [show e d = b from hdb]
    infer_instance
  let eAway : TD →+* TB := IsLocalization.Away.map TD TB e.toRingHom d
  have hAwayBij : Function.Bijective eAway := by
    constructor
    · change Function.Injective (IsLocalization.map TB e.toRingHom _)
      exact IsLocalization.map_injective_of_injective _ _ _ e.bijective.1
    · change Function.Surjective (IsLocalization.map TB e.toRingHom _)
      exact IsLocalization.map_surjective_of_surjective _ _ _ e.bijective.2
  have hAwayComp : eAway.comp
      (Localization.awayMap (algebraMap F.middle D) c) =
      Localization.awayMap (algebraMap F.middle B) c := by
    apply IsLocalization.ringHom_ext (.powers c)
    ext a
    have hleft : Localization.awayMap (algebraMap F.middle D) c
        (algebraMap F.middle (Localization.Away c) a) =
        algebraMap D TD (algebraMap F.middle D a) := by
      rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
    have hright : Localization.awayMap (algebraMap F.middle B) c
        (algebraMap F.middle (Localization.Away c) a) =
        algebraMap B TB (algebraMap F.middle B a) := by
      rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
    have hmap (x : D) :
        eAway (algebraMap D TD x) = algebraMap B TB (e.toRingHom x) := by
      change IsLocalization.map TB e.toRingHom _ (algebraMap D TD x) = _
      rw [IsLocalization.map_eq]
    change eAway (Localization.awayMap (algebraMap F.middle D) c
        (algebraMap F.middle (Localization.Away c) a)) =
      Localization.awayMap (algebraMap F.middle B) c
        (algebraMap F.middle (Localization.Away c) a)
    rw [hleft, hmap, hright]
    rfl
  have hcOld : (PrimeSpectrum.basicOpen c : Set (PrimeSpectrum F.middle)) ⊆
      Set.range (PrimeSpectrum.comap (algebraMap F.middle D)) := by
    intro p hp
    obtain ⟨q, hq⟩ := hc hp
    refine ⟨PrimeSpectrum.comap e.toRingHom q, ?_⟩
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap F.middle D)
        (Ideal.comap e.toRingHom q.asIdeal) = p.asIdeal
    rw [Ideal.comap_comap]
    change Ideal.comap target q.asIdeal = p.asIdeal
    exact congrArg PrimeSpectrum.asIdeal hq
  rw [← hAwayComp]
  exact hAwayBij.comp (F.awayMap_bijective c hcOld)

/-- The finite-open factorization of an away localization `Bg` of the target induced by one of
the target itself.  The intermediate algebra is unchanged; the spectrum of `Bg` is an open
subspace of that of the target, hence again of that of the intermediate algebra. -/
noncomputable def locFact
    {A : Type u} {B : Type v} {Bg : Type w}
    [CommRing A] [CommRing B] [CommRing Bg]
    [Algebra A B] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
    (g : B) [IsLocalization.Away g Bg]
    (F : FiniteOpenFactorization.{u, v, x} A B) :
    FiniteOpenFactorization.{u, w, x} A Bg := by
  let : Algebra F.middle Bg := Algebra.compHom Bg (algebraMap F.middle B)
  let : IsScalarTower F.middle B Bg := IsScalarTower.of_algebraMap_eq'
    (by rw [Algebra.compHom_algebraMap_eq])
  let : IsScalarTower A F.middle Bg := IsScalarTower.of_algebraMap_eq' (by
    ext a
    calc
      algebraMap A Bg a = algebraMap B Bg (algebraMap A B a) :=
        IsScalarTower.algebraMap_apply A B Bg a
      _ = algebraMap B Bg (algebraMap F.middle B (algebraMap A F.middle a)) := by
        rw [IsScalarTower.algebraMap_apply A F.middle B])
  refine {
    middle := F.middle
    commRingMiddle := F.commRingMiddle
    algebraMiddle := F.algebraMiddle
    algebraTarget := inferInstance
    scalarTower := inferInstance
    finite_middle := F.finite_middle
    isOpenEmbedding_comap := by
      convert F.isOpenEmbedding_comap.comp
        (PrimeSpectrum.localization_away_isOpenEmbedding Bg g) using 1
      rw [← PrimeSpectrum.comap_comp]
      rfl
    awayMap_bijective := by
      intro c hc
      have hcb : (PrimeSpectrum.basicOpen c : Set (PrimeSpectrum F.middle)) ⊆
          Set.range (PrimeSpectrum.comap (algebraMap F.middle B)) := by
        intro p hp
        obtain ⟨q, hq⟩ := hc hp
        refine ⟨PrimeSpectrum.comap (algebraMap B Bg) q, ?_⟩
        apply PrimeSpectrum.ext
        change Ideal.comap (algebraMap F.middle B)
          (Ideal.comap (algebraMap B Bg) q.asIdeal) = p.asIdeal
        rw [Ideal.comap_comap]
        rw [← IsScalarTower.algebraMap_eq F.middle B Bg]
        exact congrArg PrimeSpectrum.asIdeal hq
      have hF := F.awayMap_bijective c hcb
      have hunit := unit_image_of_range_localization (g := g) (F := F) c hc
      have hB := awayMap_bijective_if_unit (B := B) (Bg := Bg) g
        (algebraMap F.middle B c) hunit
      let T₁ := Localization.Away (algebraMap B Bg (algebraMap F.middle B c))
      let T₂ := Localization.Away (algebraMap F.middle Bg c)
      have heq : algebraMap B Bg (algebraMap F.middle B c) =
          algebraMap F.middle Bg c :=
        (IsScalarTower.algebraMap_apply F.middle B Bg c).symm
      have : IsLocalization.Away (algebraMap F.middle Bg c) T₁ := by
        rw [← heq]
        infer_instance
      let e : T₁ ≃ₐ[Bg] T₂ := IsLocalization.algEquiv
        (.powers (algebraMap F.middle Bg c)) T₁ T₂
      have hcomp :
          e.toRingEquiv.toRingHom.comp
            ((Localization.awayMap (algebraMap B Bg) (algebraMap F.middle B c)).comp
              (Localization.awayMap (algebraMap F.middle B) c)) =
          Localization.awayMap (algebraMap F.middle Bg) c := by
        apply IsLocalization.ringHom_ext (.powers c)
        ext d
        simpa [T₁, T₂, e, heq, Localization.awayMap, IsLocalization.Away.map] using
          (congrArg (algebraMap Bg T₂)
            (IsScalarTower.algebraMap_apply F.middle B Bg d)).symm
      rw [← hcomp]
      exact e.toRingEquiv.bijective.comp (hB.comp hF)
  }

end Stacks.Discriminant
