module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.FieldTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedBaseChange
public import StacksFrontier.RingTheory.Artinian.FibreDimensionBound

/-!
# Bounds on the fibre degrees of a composite

The product of bounds on the degrees of the fibres of two morphisms of schemes bounds the degrees
of the fibres of their composite.

## Main results

* `AlgebraicGeometry.boundsFiberDegrees_comp` gives the product bound for a composite.
* `AlgebraicGeometry.hasUniversallyBoundedFibers_comp`: a composition of morphisms with
  universally bounded fibres has universally bounded fibres.
* `AlgebraicGeometry.locallyQuasiFinite_of_boundsFiberDegrees`: a morphism whose fibre degrees are
  bounded is locally quasi-finite.

## Implementation notes

Composition is written in categorical order: `f ≫ g` is the morphism denoted `g ∘ f` in the source.
Bounds are integers, as in `AlgebraicGeometry.BoundsFiberDegrees`, so the nonnegativity of the
bound for the first morphism is assumed explicitly; the bound for the second morphism needs no
such assumption, because a bound on its fibres already produces a nonnegative rank below it.

Over a point `z` of the final target the fibre of `g` is a finite discrete affine scheme, and so
is every fibre of the base change of `f` to it; hence the fibre of the composite is a finite
discrete, therefore affine, scheme. The degrees then become dimensions of rings of global sections
and the statement is the commutative-algebra bound
`Algebra.finite_and_finrank_le_of_finrank_fiber_le`: an algebra whose fibres over the maximal
ideals of a finite algebra have dimension at most `n` has dimension at most `n` times that of the
finite algebra. The individual fibre dimensions are read off the bound for the base change of `f`
through the field-valued base-change characterisation
`AlgebraicGeometry.boundsFiberDegrees_iff_field_baseChange` together with
`AlgebraicGeometry.pullbackSpecIso`, which identifies a field-valued base change of a morphism of
affine schemes with the spectrum of the corresponding fibre of the algebra.

## References

* [Stacks Project, Tag 03J6](https://stacks.math.columbia.edu/tag/03J6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A scheme finite locally free over the spectrum of a field is a finite discrete space. -/
@[ega "I 6.4.4" "(e) ⇒ (c′) and (b)", ega "II 6.1.7" "special case"]
private lemma finite_and_discreteTopology_of_isFiniteLocallyFreeOfRank {K : Type u} [Field K]
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of K)) (r : ℕ)
    (h : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r) : Finite Z ∧ DiscreteTopology Z := by
  have : IsAffineHom p := h.toIsAffineHom
  have : IsAffine Z := isAffine_of_isAffineHom p
  let : Algebra K ↑Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom.toAlgebra
  obtain ⟨hfin, -⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_finrank_of_specTarget p r rfl).mp h
  have : IsArtinianRing ↑Γ(Z, ⊤) := IsArtinianRing.of_finite K ↑Γ(Z, ⊤)
  have hdim : Ring.KrullDimLE 0 ↑Γ(Z, ⊤) :=
    Ring.krullDimLE_zero_iff.mpr fun I hI ↦ (IsArtinianRing.isPrime_iff_isMaximal I).mp hI
  have hdisc : DiscreteTopology (PrimeSpectrum ↑Γ(Z, ⊤)) :=
    PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mpr ⟨inferInstance, hdim⟩
  have : Finite (Spec Γ(Z, ⊤) : Scheme.{u}) := inferInstanceAs (Finite (PrimeSpectrum ↑Γ(Z, ⊤)))
  exact ⟨Finite.of_equiv _ Z.isoSpec.hom.homeomorph.toEquiv.symm,
    Z.isoSpec.hom.homeomorph.discreteTopology_iff.mpr hdisc⟩

/-- A map to a finite type with finite fibres has a finite domain. -/
private lemma finite_of_finite_fibers {A B : Type*} [Finite B] (f : A → B)
    (hf : ∀ b, Finite {a // f a = b}) : Finite A :=
  Finite.of_equiv (Σ b : B, {a // f a = b}) (Equiv.sigmaFiberEquiv f)

/-- A morphism to a discrete scheme with discrete fibres has a discrete source. -/
private lemma discreteTopology_of_discreteTopology_fibers {X Y : Scheme.{u}} (p : X ⟶ Y)
    [DiscreteTopology Y] (h : ∀ y, DiscreteTopology (p.fiber y)) : DiscreteTopology X := by
  apply isDiscrete_univ_iff.mp
  simpa using (IsDiscrete.univ (X := Y)).preimage' p.continuous.continuousOn
    fun y ↦ isDiscrete_iff_discreteTopology.mpr
      ((p.fiberHomeo y).discreteTopology_iff.mp (h y))

/-- A morphism to a finite discrete scheme with finite discrete fibres has an affine source. -/
private lemma isAffine_of_finite_discrete_fibers {X Y : Scheme.{u}} (p : X ⟶ Y) [Finite Y]
    [DiscreteTopology Y] (hfin : ∀ y, Finite (p.fiber y))
    (hdisc : ∀ y, DiscreteTopology (p.fiber y)) : IsAffine X := by
  have : Finite X := finite_of_finite_fibers p fun y ↦ by
    have : Finite (p.fiber y) := hfin y
    exact Finite.of_equiv (p.fiber y) (p.fiberHomeo y).toEquiv
  have : DiscreteTopology X := discreteTopology_of_discreteTopology_fibers p hdisc
  infer_instance

/-- A bound on the degrees of the fibres of a morphism of affine schemes is a bound on the degrees
of the fibres of the induced morphism of the spectra of their global sections. -/
private lemma boundsFiberDegrees_specMap_appTop {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (p : X ⟶ Y) (n : ℤ) (h : BoundsFiberDegrees p n) :
    BoundsFiberDegrees (Spec.map p.appTop) n :=
  boundsFiberDegrees_of_isPullback
    (IsPullback.of_horiz_isIso (CommSq.mk (by
      rw [Iso.inv_comp_eq, ← Category.assoc, Scheme.isoSpec_hom_naturality p, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]))) h

/-- A bound on the degrees of the fibres of the morphism of spectra induced by an algebra bounds
the dimension of the fibre of that algebra at each maximal ideal of its base. -/
private lemma finite_and_finrank_fiber_le_of_boundsFiberDegrees {B A : Type u} [CommRing B]
    [CommRing A] [Algebra B A] (n : ℕ)
    (h : BoundsFiberDegrees (Spec.map (CommRingCat.ofHom (algebraMap B A))) (n : ℤ))
    (m : MaximalSpectrum B) :
    Module.Finite m.asIdeal.ResidueField (m.asIdeal.Fiber A) ∧
      Module.finrank m.asIdeal.ResidueField (m.asIdeal.Fiber A) ≤ n := by
  obtain ⟨r, hr, hrank⟩ := (boundsFiberDegrees_iff_field_baseChange _ (n : ℤ)).mp h
    m.asIdeal.ResidueField
    (Spec.map (CommRingCat.ofHom (algebraMap B m.asIdeal.ResidueField)))
  have h1 : Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r
      ((pullbackSpecIso B m.asIdeal.ResidueField A).inv ≫ pullback.fst _ _) :=
    MorphismProperty.RespectsIso.precomp _ _ _ hrank
  rw [pullbackSpecIso_inv_fst'] at h1
  obtain ⟨hfin, hfr⟩ :=
    ((Stacks.Morphisms.isFiniteLocallyFreeOfRank_specMap_iff_module
      m.asIdeal.ResidueField (m.asIdeal.Fiber A) r).mp h1).finite_and_finrank_eq
  exact ⟨hfin, by rw [hfr]; exact_mod_cast hr⟩

/-- The degree of a composite over the spectrum of a field, from a bound on the fibre degrees of
the first morphism and the degree of the second. -/
private lemma exists_isFiniteLocallyFreeOfRank_comp {K : Type u} [Field K] {W T : Scheme.{u}}
    [IsAffine W] (p : W ⟶ T) (p₀ : T ⟶ Spec (.of K)) (n s : ℕ)
    (h₀ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p₀ s)
    (hp : BoundsFiberDegrees p (n : ℤ)) :
    ∃ r ≤ n * s, Stacks.Morphisms.IsFiniteLocallyFreeOfRank (p ≫ p₀) r := by
  have : IsAffineHom p₀ := h₀.toIsAffineHom
  have : IsAffine T := isAffine_of_isAffineHom p₀
  let : Algebra K ↑Γ(T, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ p₀.appTop).hom.toAlgebra
  let : Algebra ↑Γ(T, ⊤) ↑Γ(W, ⊤) := p.appTop.hom.toAlgebra
  let : Algebra K ↑Γ(W, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ (p ≫ p₀).appTop).hom.toAlgebra
  have : IsScalarTower K ↑Γ(T, ⊤) ↑Γ(W, ⊤) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    change (p ≫ p₀).appTop.hom ((Scheme.ΓSpecIso (.of K)).inv.hom x) =
      p.appTop.hom (p₀.appTop.hom ((Scheme.ΓSpecIso (.of K)).inv.hom x))
    rw [show (p ≫ p₀).appTop = p₀.appTop ≫ p.appTop from Scheme.Hom.comp_appTop p p₀]
    rfl
  obtain ⟨hTfin, hTrank⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_finrank_of_specTarget p₀ s rfl).mp h₀
  have hpSpec : BoundsFiberDegrees
      (Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(T, ⊤) ↑Γ(W, ⊤)))) (n : ℤ) :=
    boundsFiberDegrees_specMap_appTop p (n : ℤ) hp
  obtain ⟨hWfin, hWle⟩ := Algebra.finite_and_finrank_le_of_finrank_fiber_le (k := K)
    (B := ↑Γ(T, ⊤)) (A := ↑Γ(W, ⊤)) n
    fun mm ↦ finite_and_finrank_fiber_le_of_boundsFiberDegrees n hpSpec mm
  exact ⟨Module.finrank K ↑Γ(W, ⊤), by rw [← hTrank]; exact hWle,
    (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_finrank_of_specTarget (p ≫ p₀) _
      rfl).mpr ⟨hWfin, rfl⟩⟩

/-- Enlarging the bound preserves a bound on the fibre degrees. -/
private lemma boundsFiberDegrees_mono {X Y : Scheme.{u}} {f : X ⟶ Y} {n n' : ℤ} (hnn : n ≤ n')
    (h : BoundsFiberDegrees f n) : BoundsFiberDegrees f n' := by
  intro y
  obtain ⟨r, hr, hrank⟩ := h y
  exact ⟨r, hr.trans hnn, hrank⟩

/-- A bound on the fibre degrees makes a morphism locally quasi-finite. -/
theorem locallyQuasiFinite_of_boundsFiberDegrees {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℤ)
    (h : BoundsFiberDegrees f n) : LocallyQuasiFinite f := by
  refine LocallyQuasiFinite.of_fiberToSpecResidueField f fun y => ?_
  obtain ⟨r, -, hrank⟩ := h y
  let : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (f.fiberToSpecResidueField y) r := hrank
  have : IsFinite (f.fiberToSpecResidueField y) :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_of_specTarget
      (f.fiberToSpecResidueField y)).mp
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ r)).1
  infer_instance

/-- **Stacks Project, Tag 03J6.** If a nonnegative integer `n` bounds the degrees of the fibres of
`f` and an integer `m` bounds the degrees of the fibres of `g`, then `n * m` bounds the degrees of
the fibres of the composite `f ≫ g`. -/
@[stacks 03J6]
theorem boundsFiberDegrees_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n m : ℤ)
    (hn : 0 ≤ n) (hf : BoundsFiberDegrees f n) (hg : BoundsFiberDegrees g m) :
    BoundsFiberDegrees (f ≫ g) (n * m) := by
  intro z
  obtain ⟨s, hs, hgs⟩ := hg z
  have hgsI : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (g.fiberToSpecResidueField z) s := hgs
  obtain ⟨hTfinite, hTdiscrete⟩ :=
    finite_and_discreteTopology_of_isFiniteLocallyFreeOfRank (g.fiberToSpecResidueField z) s hgsI
  have hp : BoundsFiberDegrees (pullback.snd f (g.fiberι z)) n :=
    boundsFiberDegrees_of_isPullback (IsPullback.of_hasPullback f (g.fiberι z)) hf
  have hpN : BoundsFiberDegrees (pullback.snd f (g.fiberι z)) ((n.toNat : ℕ) : ℤ) := by
    rwa [Int.toNat_of_nonneg hn]
  have hfib (t : (g.fiber z : Scheme.{u})) :
      Finite ((pullback.snd f (g.fiberι z)).fiber t) ∧
        DiscreteTopology ((pullback.snd f (g.fiberι z)).fiber t) := by
    obtain ⟨r, -, hr⟩ := hp t
    exact finite_and_discreteTopology_of_isFiniteLocallyFreeOfRank
      ((pullback.snd f (g.fiberι z)).fiberToSpecResidueField t) r hr
  have : IsAffine (pullback f (g.fiberι z)) :=
    isAffine_of_finite_discrete_fibers (pullback.snd f (g.fiberι z))
      (fun t ↦ (hfib t).1) fun t ↦ (hfib t).2
  obtain ⟨r, hrle, hrank⟩ := exists_isFiniteLocallyFreeOfRank_comp
    (pullback.snd f (g.fiberι z)) (g.fiberToSpecResidueField z) n.toNat s hgsI hpN
  refine ⟨r, ?_, ?_⟩
  · calc
      (r : ℤ) ≤ (n.toNat : ℤ) * (s : ℤ) := by exact_mod_cast hrle
      _ = n * (s : ℤ) := by rw [Int.toNat_of_nonneg hn]
      _ ≤ n * m := mul_le_mul_of_nonneg_left hs hn
  · have h1 : Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r
        ((pullbackRightPullbackFstIso g (Z.fromSpecResidueField z) f).inv ≫
          pullback.snd f (pullback.fst g (Z.fromSpecResidueField z)) ≫
            pullback.snd g (Z.fromSpecResidueField z)) :=
      MorphismProperty.RespectsIso.precomp _ _ _ hrank
    rwa [pullbackRightPullbackFstIso_inv_snd_snd] at h1

/-- **Stacks Project, Tag 03J6.** A composition of morphisms with universally bounded fibres has
universally bounded fibres. -/
@[stacks 03J6]
theorem hasUniversallyBoundedFibers_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : HasUniversallyBoundedFibers f) (hg : HasUniversallyBoundedFibers g) :
    HasUniversallyBoundedFibers (f ≫ g) := by
  obtain ⟨n, hn⟩ := hf
  obtain ⟨m, hm⟩ := hg
  exact ⟨max n 0 * m, boundsFiberDegrees_comp f g (max n 0) m (le_max_right n 0)
    (boundsFiberDegrees_mono (le_max_left n 0) hn) hm⟩

end AlgebraicGeometry

end
