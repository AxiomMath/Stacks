module

public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.LocalIsomorphism
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.ClopenRefinement
public import StacksFrontier.RingTheory.Localization.UniquePrimeOver
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Topology.Connected.TotallyDisconnected
public import StacksCore.Tactic.StacksAttribute

/-!
# Isomorphisms of w-local spectra identifying local rings

A ring map identifying all local rings is an isomorphism when its source and target spectra are
w-local, the induced map of spectra is w-local, and it bijects their connected components.

## Main results

* `AlgebraicGeometry.ProEtale.bijective_of_wLocalMap_identifiesLocalRings` gives bijectivity of
  the ring map.

## Implementation notes

The ring-map isomorphism is expressed as bijectivity of its underlying function. The map on
connected components is the canonical map induced by continuity of contraction on prime spectra.

## References

* [Stacks Project, Lemma 61.3.6 (Tag 097E)](https://stacks.math.columbia.edu/tag/097E)
-/

@[expose] public section

namespace AlgebraicGeometry.ProEtale

/-- In a w-local space, every point specializes to a unique closed point, read in the subtype of
closed points. -/
private theorem existsUnique_closedPoint_specializes_subtype
    {X : Type*} [TopologicalSpace X] [WLocalSpace X] (x : X) :
    ∃! c : closedPoints X, Specializes x c.1 := by
  obtain ⟨c, ⟨hc, hxc⟩, hcu⟩ := WLocalSpace.existsUnique_closedPoint_specializes x
  exact ⟨⟨c, hc⟩, hxc, fun c' hc' => Subtype.ext (hcu c'.1 ⟨c'.2, hc'⟩)⟩

/-- A w-local map of w-local spaces that bijects connected components bijects closed points. -/
private theorem closedPoints_map_bijective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [WLocalSpace X] [WLocalSpace Y]
    {f : X → Y} (hf : IsWLocalMap f)
    (hcomp : Function.Bijective hf.toIsSpectralMap.continuous.connectedComponentsMap) :
    Function.Bijective (fun x : closedPoints X =>
      (⟨f x.1, hf.closedPoints_subset_preimage_closedPoints x.2⟩ : closedPoints Y)) := by
  let fc : closedPoints X → closedPoints Y := fun x =>
    ⟨f x.1, hf.closedPoints_subset_preimage_closedPoints x.2⟩
  have hx := closedPoints_to_connectedComponents_bijective_of_unique_specialization
    (WLocalSpace.isClosed_closedPoints (X := X)) (existsUnique_closedPoint_specializes_subtype)
  have hy := closedPoints_to_connectedComponents_bijective_of_unique_specialization
    (WLocalSpace.isClosed_closedPoints (X := Y)) (existsUnique_closedPoint_specializes_subtype)
  let cx : closedPoints X → ConnectedComponents X := fun x => ConnectedComponents.mk x.1
  let cy : closedPoints Y → ConnectedComponents Y := fun y => ConnectedComponents.mk y.1
  have hcompat : ∀ x : closedPoints X,
      cy (fc x) = hf.toIsSpectralMap.continuous.connectedComponentsMap (cx x) := by
    intro x
    simp [cx, cy, fc, Continuous.connectedComponentsMap_mk]
  refine ⟨fun a b hab => hx.injective <| hcomp.injective <|
    (hcompat a).symm.trans ((congrArg cy hab).trans (hcompat b)), fun y => ?_⟩
  obtain ⟨c, hc⟩ := hcomp.surjective (cy y)
  obtain ⟨x, hxcomp⟩ := hx.surjective c
  exact ⟨x, hy.injective ((hcompat x).trans ((congrArg _ hxcomp).trans hc))⟩

/-- Contracting a prime of a local ring of `B` to `A` can be done through `B` or directly. -/
private theorem primeSpectrum_comap_localization
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (q : Ideal B) [q.IsPrime]
    (z : PrimeSpectrum (Localization.AtPrime q)) :
    PrimeSpectrum.comap (algebraMap A B)
      (PrimeSpectrum.comap (algebraMap B (Localization.AtPrime q)) z) =
        PrimeSpectrum.comap (algebraMap A (Localization.AtPrime q)) z :=
  rfl

/-- The contraction to `A` of a prime of a local ring of `B` factors through the local ring of
`A` at the contracted prime. -/
private theorem localRingHom_comap_comm
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (q : Ideal B) [q.IsPrime]
    (z : PrimeSpectrum (Localization.AtPrime q)) :
    PrimeSpectrum.comap (algebraMap A (Localization.AtPrime q)) z =
      PrimeSpectrum.comap (algebraMap A (Localization.AtPrime (q.comap (algebraMap A B))))
        (PrimeSpectrum.comap
          (Localization.localRingHom (q.comap (algebraMap A B)) q (algebraMap A B) rfl) z) := by
  rw [← PrimeSpectrum.comap_comp_apply]
  congr 1
  ext x
  simp [IsScalarTower.algebraMap_apply A B (Localization.AtPrime q)]

/-- Under the hypotheses of the main result, the induced map of prime spectra is bijective. -/
private theorem primeSpectrum_comap_bijective
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [WLocalSpace (PrimeSpectrum A)]
    [WLocalSpace (PrimeSpectrum B)]
    (hlocal : Algebra.IdentifiesLocalRings A B)
    (hwlocal : IsWLocalMap (PrimeSpectrum.comap (algebraMap A B)))
    (hcomponents : Function.Bijective
      (PrimeSpectrum.continuous_comap (algebraMap A B)).connectedComponentsMap) :
    Function.Bijective (PrimeSpectrum.comap (algebraMap A B)) := by
  let f := PrimeSpectrum.comap (algebraMap A B)
  have hclosed := closedPoints_map_bijective hwlocal hcomponents
  constructor
  · intro q₁ q₂ hq
    obtain ⟨c₁, ⟨hc₁, hq₁c₁⟩, _⟩ :=
      WLocalSpace.existsUnique_closedPoint_specializes q₁
    obtain ⟨c₂, ⟨hc₂, hq₂c₂⟩, _⟩ :=
      WLocalSpace.existsUnique_closedPoint_specializes q₂
    have hq₁le : q₁ ≤ c₁ := (PrimeSpectrum.le_iff_specializes q₁ c₁).2 hq₁c₁
    have hq₂le : q₂ ≤ c₂ := (PrimeSpectrum.le_iff_specializes q₂ c₂).2 hq₂c₂
    let r₁ := f c₁
    let r₂ := f c₂
    have hp₁le : f q₁ ≤ r₁ := Ideal.comap_mono hq₁le
    have hp₂le : f q₂ ≤ r₂ := Ideal.comap_mono hq₂le
    have hr₁closed : r₁ ∈ closedPoints (PrimeSpectrum A) :=
      hwlocal.closedPoints_subset_preimage_closedPoints hc₁
    have hr₂closed : r₂ ∈ closedPoints (PrimeSpectrum A) :=
      hwlocal.closedPoints_subset_preimage_closedPoints hc₂
    obtain ⟨a, ⟨ha, hpa⟩, huniq⟩ :=
      WLocalSpace.existsUnique_closedPoint_specializes (f q₁)
    have hr₁ : r₁ = a := huniq r₁ ⟨hr₁closed,
      (PrimeSpectrum.le_iff_specializes (f q₁) r₁).1 (by simpa [f] using hp₁le)⟩
    have hr₂ : r₂ = a := huniq r₂ ⟨hr₂closed,
      (PrimeSpectrum.le_iff_specializes (f q₁) r₂).1 (by simpa [f, hq] using hp₂le)⟩
    have hc₁c₂ : c₁ = c₂ := congrArg Subtype.val (hclosed.injective
      (Subtype.ext (hr₁.trans hr₂.symm)) : (⟨c₁, hc₁⟩ : closedPoints (PrimeSpectrum B)) = ⟨c₂, hc₂⟩)
    subst c₂
    let r : PrimeSpectrum A :=
      ⟨c₁.asIdeal.comap (algebraMap A B), inferInstance⟩
    let g := Localization.localRingHom (c₁.asIdeal.comap (algebraMap A B)) c₁.asIdeal
      (algebraMap A B) rfl
    let e : Localization.AtPrime r.asIdeal ≃+* Localization.AtPrime c₁.asIdeal :=
      RingEquiv.ofBijective g (hlocal c₁.asIdeal)
    let eA := IsLocalization.AtPrime.primeSpectrumOrderIso
      (Localization.AtPrime r.asIdeal) r.asIdeal
    let eB := IsLocalization.AtPrime.primeSpectrumOrderIso
      (Localization.AtPrime c₁.asIdeal) c₁.asIdeal
    let q₁loc := eB.symm ⟨q₁, hq₁le⟩
    let q₂loc := eB.symm ⟨q₂, hq₂le⟩
    let ploc := eA.symm ⟨f q₁, hp₁le⟩
    have hploc :
        PrimeSpectrum.comap (algebraMap A (Localization.AtPrime r.asIdeal)) ploc = f q₁ :=
      congrArg Subtype.val (eA.apply_symm_apply ⟨f q₁, hp₁le⟩)
    have hmap : ∀ (q' : PrimeSpectrum B) (h : q' ≤ c₁), f q' = f q₁ →
        PrimeSpectrum.comap g (eB.symm ⟨q', h⟩) = ploc := by
      intro q' h hq'
      apply PrimeSpectrum.localization_comap_injective
        (Localization.AtPrime r.asIdeal) r.asIdeal.primeCompl
      calc
        PrimeSpectrum.comap (algebraMap A (Localization.AtPrime r.asIdeal))
            (PrimeSpectrum.comap g (eB.symm ⟨q', h⟩)) =
              PrimeSpectrum.comap (algebraMap A (Localization.AtPrime c₁.asIdeal))
                (eB.symm ⟨q', h⟩) :=
                (localRingHom_comap_comm (A := A) (B := B) c₁.asIdeal _).symm
        _ = f q' := (primeSpectrum_comap_localization (A := A) (B := B) c₁.asIdeal _).symm.trans
          (congrArg f (congrArg Subtype.val (eB.apply_symm_apply ⟨q', h⟩)))
        _ = f q₁ := hq'
        _ = PrimeSpectrum.comap (algebraMap A (Localization.AtPrime r.asIdeal)) ploc := hploc.symm
    have hq₁map := hmap q₁ hq₁le rfl
    have hq₂map := hmap q₂ hq₂le hq.symm
    have hloc : q₁loc = q₂loc := (PrimeSpectrum.comapEquiv e.symm).injective
      (hq₁map.trans hq₂map.symm)
    simpa [q₁loc, q₂loc] using congrArg (fun x => (eB x).1) hloc
  · intro p
    obtain ⟨c, ⟨hc, hpc⟩, _⟩ :=
      WLocalSpace.existsUnique_closedPoint_specializes p
    obtain ⟨d, hd⟩ := hclosed.surjective ⟨c, hc⟩
    have hdc : f d.1 = c := congrArg Subtype.val hd
    let r : PrimeSpectrum A :=
      ⟨d.1.asIdeal.comap (algebraMap A B), inferInstance⟩
    have hrc : r = c := by
      apply PrimeSpectrum.ext
      simpa [r, f] using congrArg PrimeSpectrum.asIdeal hdc
    let g := Localization.localRingHom (d.1.asIdeal.comap (algebraMap A B)) d.1.asIdeal
      (algebraMap A B) rfl
    let e : Localization.AtPrime r.asIdeal ≃+* Localization.AtPrime d.1.asIdeal :=
      RingEquiv.ofBijective g (hlocal d.1.asIdeal)
    let eA := IsLocalization.AtPrime.primeSpectrumOrderIso
      (Localization.AtPrime r.asIdeal) r.asIdeal
    have hpr : p ≤ r := hrc ▸ (PrimeSpectrum.le_iff_specializes p c).2 hpc
    let ploc := eA.symm ⟨p, hpr⟩
    let qloc := (PrimeSpectrum.comapEquiv e.symm).symm ploc
    let q := PrimeSpectrum.comap (algebraMap B (Localization.AtPrime d.1.asIdeal)) qloc
    have hploc :
        PrimeSpectrum.comap (algebraMap A (Localization.AtPrime r.asIdeal)) ploc = p :=
      congrArg Subtype.val (eA.apply_symm_apply ⟨p, hpr⟩)
    have hqmap : f q = p := by
      have heq : PrimeSpectrum.comap g qloc = ploc :=
        (PrimeSpectrum.comapEquiv e.symm).apply_symm_apply ploc
      calc
        f q = PrimeSpectrum.comap (algebraMap A (Localization.AtPrime d.1.asIdeal)) qloc :=
          primeSpectrum_comap_localization (A := A) (B := B) d.1.asIdeal qloc
        _ = PrimeSpectrum.comap (algebraMap A (Localization.AtPrime r.asIdeal))
            (PrimeSpectrum.comap g qloc) :=
              by simpa [r, g] using
                (localRingHom_comap_comm (A := A) (B := B) d.1.asIdeal qloc)
        _ = p := by rw [heq, hploc]
    exact ⟨q, hqmap⟩

/-- Under the hypotheses of the main result, the ring map becomes bijective after localizing at
a maximal ideal of the source. -/
private theorem localized_algebraMap_bijective
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (hlocal : Algebra.IdentifiesLocalRings A B)
    (hspec : Function.Bijective (PrimeSpectrum.comap (algebraMap A B)))
    (hflat : Module.Flat A B)
    (P : Ideal A) [P.IsMaximal] :
    Function.Bijective
      (algebraMap (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid B P.primeCompl))) := by
  let p₀ : PrimeSpectrum A := ⟨P, inferInstance⟩
  obtain ⟨q₀, hq₀⟩ := hspec.surjective p₀
  let q := q₀.asIdeal
  have hqP : q.comap (algebraMap A B) = P := by
    simpa [p₀, q] using congrArg PrimeSpectrum.asIdeal hq₀
  cases hqP
  let Bp := Localization (Algebra.algebraMapSubmonoid B (q.comap (algebraMap A B)).primeCompl)
  have huniq : ∀ q' : Ideal B, q'.IsPrime → q'.LiesOver (q.comap (algebraMap A B)) → q' = q := by
    intro q' hq' hq'over
    have hpoint : PrimeSpectrum.comap (algebraMap A B) ⟨q', hq'⟩ = p₀ := by
      apply PrimeSpectrum.ext
      simpa [q] using hq'over.over.symm
    exact congrArg PrimeSpectrum.asIdeal (hspec.injective hpoint)
  have hsame : ∀ (q₁ q₂ : Ideal B), q₁.IsPrime → q₂.IsPrime →
      q₁.under A = q₂.under A → q₁ = q₂ := by
    intro q₁ q₂ hq₁ hq₂ hunder
    exact congrArg PrimeSpectrum.asIdeal (hspec.injective (PrimeSpectrum.ext hunder :
      PrimeSpectrum.comap (algebraMap A B) ⟨q₁, hq₁⟩ =
        PrimeSpectrum.comap (algebraMap A B) ⟨q₂, hq₂⟩))
  let : IsLocalization q.primeCompl Bp :=
    localization_eq_of_unique_prime_over (q.comap (algebraMap A B)) q huniq
      (Or.inr ⟨Algebra.HasGoingDown.of_flat (R := A) (S := B), hsame⟩)
  let : q.LiesOver (q.comap (algebraMap A B)) := ⟨rfl⟩
  let eB : Bp ≃ₐ[B] Localization.AtPrime q :=
    IsLocalization.algEquiv q.primeCompl Bp (Localization.AtPrime q)
  let l : Localization.AtPrime (q.comap (algebraMap A B)) →+* Bp :=
    algebraMap (Localization.AtPrime (q.comap (algebraMap A B))) Bp
  let g := Localization.localRingHom (q.comap (algebraMap A B)) q (algebraMap A B) rfl
  have hABp : algebraMap A Bp = (algebraMap B Bp).comp (algebraMap A B) := by
    ext x
    rfl
  have heq : eB.toRingHom.comp l = g := by
    apply IsLocalization.ringHom_ext (q.comap (algebraMap A B)).primeCompl
    ext x
    change eB.toRingHom
        ((algebraMap (Localization.AtPrime (q.comap (algebraMap A B))) Bp)
          (algebraMap A (Localization.AtPrime (q.comap (algebraMap A B))) x)) =
      g (algebraMap A (Localization.AtPrime (q.comap (algebraMap A B))) x)
    rw [← IsScalarTower.algebraMap_apply A
      (Localization.AtPrime (q.comap (algebraMap A B))) Bp x, hABp]
    simp [g, eB, Localization.localRingHom_to_map]
  refine (eB.bijective.of_comp_iff' l).mp ?_
  rw [show ⇑eB ∘ ⇑l = ⇑g from funext fun z => DFunLike.congr_fun heq z]
  exact hlocal q

/-- A ring map whose map of spectra is a w-local map of w-local spaces, which identifies all
local rings and bijects connected components, is bijective. -/
@[stacks 097E]
theorem bijective_of_wLocalMap_identifiesLocalRings
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [WLocalSpace (PrimeSpectrum A)]
    [WLocalSpace (PrimeSpectrum B)]
    (hlocal : Algebra.IdentifiesLocalRings A B)
    (hwlocal : IsWLocalMap (PrimeSpectrum.comap (algebraMap A B)))
    (hcomponents : Function.Bijective
      (PrimeSpectrum.continuous_comap (algebraMap A B)).connectedComponentsMap) :
    Function.Bijective (algebraMap A B) := by
  have hspec := primeSpectrum_comap_bijective hlocal hwlocal hcomponents
  have hflat : Module.Flat A B := by
    apply Module.flat_of_isLocalized_maximal B B
      (fun q => Localization.AtPrime q)
      (fun q => Algebra.linearMap B (Localization.AtPrime q))
    intro q hq
    let p := q.comap (algebraMap A B)
    let g := Localization.localRingHom p q (algebraMap A B) rfl
    let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) := g.toAlgebra
    have hst : IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime q) :=
      IsScalarTower.of_algebraMap_eq fun x =>
        (Localization.localRingHom_to_map p q (algebraMap A B) rfl x).symm
    have hlocalFlat : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
      RingHom.flat_algebraMap_iff.mp (RingHom.Flat.of_bijective (hlocal q))
    exact Module.Flat.trans A (Localization.AtPrime p) (Localization.AtPrime q)
  let Mₚ : (P : Ideal A) → [P.IsMaximal] → Type _ := fun P => Localization.AtPrime P
  let Nₚ : (P : Ideal A) → [P.IsMaximal] → Type _ := fun P =>
    Localization (Algebra.algebraMapSubmonoid B P.primeCompl)
  let fₚ : (P : Ideal A) → [P.IsMaximal] → A →ₗ[A] Mₚ P := fun P =>
    Algebra.linearMap A (Localization.AtPrime P)
  let gₚ : (P : Ideal A) → [P.IsMaximal] → B →ₗ[A] Nₚ P := fun P =>
    (Algebra.linearMap B (Nₚ P)).restrictScalars A
  refine @bijective_of_isLocalized_maximal A A B
    inferInstance inferInstance inferInstance inferInstance inferInstance
    Mₚ (by intro P hP; infer_instance) (by intro P hP; infer_instance) fₚ
    (by intro P hP; infer_instance)
    Nₚ (by intro P hP; infer_instance) (by intro P hP; infer_instance) gₚ
    (by
      intro P hP
      exact IsLocalizedModule.restrictScalars (R := A) (A := B) P.primeCompl
        (Algebra.linearMap B (Nₚ P)))
    (Algebra.linearMap A B) ?_
  intro P hP
  let : IsLocalizedModule.AtPrime P (fₚ P) := inferInstance
  let : IsLocalizedModule.AtPrime P (gₚ P) :=
    IsLocalizedModule.restrictScalars (R := A) (A := B) P.primeCompl
      (Algebra.linearMap B (Nₚ P))
  have hlocalMap :
      IsLocalizedModule.map P.primeCompl (fₚ P) (gₚ P) (Algebra.linearMap A B) =
        (Algebra.linearMap (Localization.AtPrime P) (Nₚ P)).restrictScalars A := by
    apply IsLocalizedModule.linearMap_ext P.primeCompl (fₚ P) (gₚ P)
    rw [IsLocalizedModule.map_comp]
    ext
    simp [fₚ, gₚ, Algebra.linearMap]
  rw [hlocalMap]
  exact localized_algebraMap_bijective hlocal hspec hflat P

end AlgebraicGeometry.ProEtale
