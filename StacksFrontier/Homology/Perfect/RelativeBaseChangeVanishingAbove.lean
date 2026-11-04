module

public import StacksFrontier.Homology.Perfect.BaseChangeVanishingAbove
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.PseudoCoherent.Homology
public import StacksFrontier.Homology.PseudoCoherent.Relative.Defs
public import StacksFrontier.Homology.Tor.IndependenceBaseChange
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatAlgebraBaseChange
public import StacksFrontier.RingTheory.Flat.BlowupFiniteTypeReduction
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingEquivTransport
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsAdjunctionComp

/-!
# The local step of [Stacks, Tag 0CX9] for a relatively pseudo-coherent complex

Let `B` be a finite type `R`-algebra, `π : R → R₀` a surjective ring map, and `E` an object of
`D(B)` pseudo-coherent relative to `R` ([Stacks, Tag 065I]). This file proves the two ring
statements of the proof of [Stacks, Tag 0CX9]:

* if `Hⁱ(E ⊗^𝐋_R R₀) = 0` for `i > b`, then for every prime `p` of `B` lying over
  `V(ker π) = Spec(R₀)` there is `g ∉ p` such that every element of `Hⁱ(E)`, `i > b`, is killed
  by a power of `g`;
* if `Hⁱ(E) = 0` for `i > 0`, then `H⁰(E)` is a finitely presented `B`-module.

The source argues with a bounded above complex `F•` of finite free `P`-modules representing `E`
over a polynomial presentation `P = R[x₁, …, xₙ] ↠ B`, shortening it on principal opens of
`Spec P`. Here the same presentation is used, and the shortening is replaced by
`StacksDraft.Perfect.exists_away_forall_subsingleton_localizedModule_of_baseChange`
([Stacks, Tag 068U] degree by degree) applied to `P → P₀ = R₀[x₁, …, xₙ]`; the vanishing of
`Hⁱ(E|_P ⊗^𝐋_P P₀)` is read off `Hⁱ(E|_R ⊗^𝐋_R R₀)` by Tor independent base change
([Stacks, Tag 0661]), `P` being flat over `R`.

## Main results

* `StacksDraft.Perfect.exists_forall_pow_smul_eq_zero_of_isRelativelyPseudoCoherent`.
* `StacksDraft.Perfect.finitePresentation_homology_zero_of_isRelativelyPseudoCoherent`.

## References

* [Stacks Project, Tag 0CX9](https://stacks.math.columbia.edu/tag/0CX9)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 064S](https://stacks.math.columbia.edu/tag/064S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars

universe u

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

/-- A section of `Hⁱ(E)` read in `Hⁱ(E|_P)` and back: restriction of scalars along `α : P → B`
commutes with cohomology, so an element of `Hⁱ(E)` killed by `α(g₀)ᵏ` is the image of an element
of `Hⁱ(E|_P)` killed by `g₀ᵏ`. -/
theorem exists_pow_smul_eq_zero_of_restrictScalars {P B : Type u} [CommRing P] [CommRing B]
    (α : P →+* B) (E : DerivedCategory (ModuleCat.{u} B)) (i : ℤ) (g₀ : P)
    (h : Subsingleton (LocalizedModule (Submonoid.powers g₀)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} P) i).obj
        ((ModuleCat.restrictScalars α).mapDerivedCategory.obj E))))
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj E) :
    ∃ k : ℕ, α g₀ ^ k • x = 0 := by
  let e := ((ModuleCat.restrictScalars α).mapDerivedCategoryHomologyIso i).app E
  rw [LocalizedModule.subsingleton_iff] at h
  obtain ⟨r, ⟨k, rfl⟩, hr⟩ := h (e.inv.hom x)
  refine ⟨k, ?_⟩
  have h1 := congrArg e.hom.hom hr
  rw [map_zero, LinearMap.map_smul] at h1
  have h2 : e.hom.hom (e.inv.hom x) = x := by
    show (e.inv ≫ e.hom).hom x = x
    rw [e.inv_hom_id]
    rfl
  rw [h2] at h1
  rw [← map_pow]
  exact h1

/-- **The spreading out of [Stacks, Tag 0CX9], for a relatively pseudo-coherent complex.** Let
`B` be a finite type `R`-algebra, `π : R → R₀` surjective, and `E ∈ D(B)` pseudo-coherent relative
to `R` with `Hⁱ(E|_R ⊗^𝐋_R R₀) = 0` for `i > b`. For every prime `p` of `B` lying over
`V(ker π)` there is `g ∉ p` such that every element of `Hⁱ(E)`, `i > b`, is killed by a power of
`g`. -/
theorem exists_forall_pow_smul_eq_zero_of_isRelativelyPseudoCoherent {R B R₀ : Type u}
    [CommRing R] [CommRing B] [CommRing R₀] [Algebra R B] [Algebra.FiniteType R B]
    (E : DerivedCategory (ModuleCat.{u} B))
    (hE : ∀ m : ℤ, _root_.PseudoCoherence.IsRelativelyPseudoCoherentFrom (R := R) E m)
    (π : R →+* R₀) (hπ : Function.Surjective π) (b : ℤ)
    (hb : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R₀) i).obj
      ((totalDerivedExtensionScalars.{u, u, u} π).functor.obj
        ((ModuleCat.restrictScalars (algebraMap R B)).mapDerivedCategory.obj E))))
    (p : Ideal B) [p.IsPrime] (hp : RingHom.ker π ≤ p.comap (algebraMap R B)) :
    ∃ g : B, g ∉ p ∧ ∀ i : ℤ, b < i →
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj E,
        ∃ k : ℕ, g ^ k • x = 0 := by
  obtain ⟨n, α, hα⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := B)).mp inferInstance
  let : Algebra R R₀ := π.toAlgebra
  let : Algebra (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R₀) :=
    MvPolynomial.algebraMvPolynomial
  let K' := (ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj E
  have hK' : StacksDraft.PseudoCoherence.IsPseudoCoherent K' :=
    (StacksDraft.PseudoCoherence.pseudoCoherent_iff_all K').2 fun m => hE m n α hα
  let f : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R₀ :=
    algebraMap (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R₀)
  -- Tor independent base change along `R → R₀` for the flat `R`-algebra `P = R[x]`.
  have hpush : Algebra.IsPushout R (MvPolynomial (Fin n) R) R₀ (MvPolynomial (Fin n) R₀) :=
    Algebra.IsPushout.symm inferInstance
  have hTor : RingTheory.TorIndependence.TorIndependent R (MvPolynomial (Fin n) R) R₀ :=
    RingTheory.TorIndependence.torIndependent_of_flat_left
  let Dg := totalDerivedExtensionScalars.{u, u, u} π
  let Dh := totalDerivedExtensionScalars.{u, u, u} f
  have hcomp := @RingTheory.TorIndependence.derivedBaseChangeComparison_isIso_of_torIndependent.{
      u, u, u, u, u} R (MvPolynomial (Fin n) R) R₀ (MvPolynomial (Fin n) R₀) _ _ _ _ _ _ _ _ _
    _ _ hpush _ _ _ _ hTor Dg.functor Dh.functor Dg.comparison Dh.comparison Dg.isLeftDerived
    Dh.isLeftDerived
  let comparison := @RingTheory.TorIndependence.derivedBaseChangeComparison.{u, u, u, u, u}
    R (MvPolynomial (Fin n) R) R₀ (MvPolynomial (Fin n) R₀) _ _ _ _ _ _ _ _
    (algebraMap R (MvPolynomial (Fin n) R)) π f
    (algebraMap R₀ (MvPolynomial (Fin n) R₀))
    (IsScalarTower.algebraMap_eq R (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R₀) ▸
      IsScalarTower.algebraMap_eq R R₀ (MvPolynomial (Fin n) R₀))
    Dg.functor Dh.functor Dg.comparison Dh.comparison Dg.isLeftDerived Dh.isLeftDerived
  have hiso : IsIso comparison.2.1 := hcomp
  have hαR : α.toRingHom.comp (algebraMap R (MvPolynomial (Fin n) R)) = algebraMap R B :=
    α.comp_algebraMap
  have hb' : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
      (Dh.functor.obj K')) := by
    intro i hi
    refine StacksDraft.isZero_homology_of_isZero_homology_restrictScalars
      (algebraMap R₀ (MvPolynomial (Fin n) R₀)) _ i ?_
    refine ((hb i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
      (Dg.functor.mapIso
        (((CochainComplex.DerivedExtensionScalars.derivedRestrictScalarsCompIso.{u, u}
          (algebraMap R (MvPolynomial (Fin n) R)) α.toRingHom).app E).trans
          (eqToIso (by rw [hαR])))))).of_iso ?_
    exact (DerivedCategory.homologyFunctor _ i).mapIso (asIso (comparison.2.1.app K')).symm
  -- The prime of `P₀` over `p`.
  have hfsurj : Function.Surjective f := MvPolynomial.map_surjective π hπ
  have hker : RingHom.ker f ≤ p.comap α.toRingHom := by
    show RingHom.ker (MvPolynomial.map π) ≤ _
    rw [MvPolynomial.ker_map, Ideal.map_le_iff_le_comap]
    intro a ha
    have := hp ha
    simpa [Ideal.mem_comap] using this
  have : (p.comap α.toRingHom).IsPrime := Ideal.comap_isPrime _ _
  let q' := (p.comap α.toRingHom).map f
  have : q'.IsPrime := Ideal.map_isPrime_of_surjective hfsurj hker
  have hq' : q'.comap f = p.comap α.toRingHom := by
    rw [Ideal.comap_map_of_surjective f hfsurj, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.2 hker
  obtain ⟨g₀, hg₀, hloc⟩ :=
    exists_away_forall_subsingleton_localizedModule_of_baseChange f q' K' hK' b hb'
  refine ⟨α g₀, ?_, fun i hi x => ?_⟩
  · rw [hq'] at hg₀
    exact hg₀
  · exact exists_pow_smul_eq_zero_of_restrictScalars α.toRingHom E i g₀ (hloc i hi) x

/-- **Finite presentation in the top degree, for a relatively pseudo-coherent complex.** If
`E ∈ D(B)` is pseudo-coherent relative to `R`, `B` of finite type over `R`, and `Hⁱ(E) = 0` for
`i > 0`, then `H⁰(E)` is a finitely presented `B`-module ([Stacks, Tag 064S] over a polynomial
presentation, then [Stacks, Tag 0561]). -/
theorem finitePresentation_homology_zero_of_isRelativelyPseudoCoherent {R B : Type u}
    [CommRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (E : DerivedCategory (ModuleCat.{u} B))
    (hE : _root_.PseudoCoherence.IsRelativelyPseudoCoherentFrom (R := R) E (-1))
    (hvan : ∀ i : ℤ, 0 < i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj E)) :
    Module.FinitePresentation B ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).obj E) := by
  obtain ⟨n, α, hα⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := B)).mp inferInstance
  let K' := (ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj E
  have h := _root_.PseudoCoherence.finitePresentation_homology_succ_of_isPseudoCoherentFrom K' (-1)
    (hE n α hα) fun i hi => StacksDraft.isZero_homology_restrictScalars α.toRingHom E i
      (hvan i (by omega))
  rw [show (-1 : ℤ) + 1 = 0 by norm_num] at h
  let e := ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategoryHomologyIso 0).app E
  let : Algebra (MvPolynomial (Fin n) R) B := α.toRingHom.toAlgebra
  have : Algebra.FiniteType (MvPolynomial (Fin n) R) B :=
    Algebra.FiniteType.of_surjective (Algebra.ofId _ B) hα
  let M := (DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).obj E
  let : Module (MvPolynomial (Fin n) R) M := Module.compHom M α.toRingHom
  have : IsScalarTower (MvPolynomial (Fin n) R) B M :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e' : (ModuleCat.restrictScalars α.toRingHom).obj M ≃ₗ[MvPolynomial (Fin n) R] M :=
    { toFun := fun x => x
      invFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have : Module.FinitePresentation (MvPolynomial (Fin n) R)
      (((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory ⋙
        DerivedCategory.homologyFunctor (ModuleCat (MvPolynomial (Fin n) R)) 0).obj E) := h
  have : Module.FinitePresentation (MvPolynomial (Fin n) R) M :=
    Module.FinitePresentation.of_equiv (e.toLinearEquiv.trans e')
  exact Module.FinitePresentation.of_restrictScalars_of_finiteType (MvPolynomial (Fin n) R) B
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).obj E)

end StacksDraft.Perfect

end
