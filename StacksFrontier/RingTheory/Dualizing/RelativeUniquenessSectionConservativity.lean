module

public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessConservativity
public import StacksFrontier.Homology.HomComplex.RHom

/-!
# Conservativity of `Δ^! ∘ p^*` along an arbitrary section

Let `Δ : S → A` be a homomorphism of commutative rings with finitely generated kernel and let
`p : A → S` be a section of it, `Δ ∘ p = id`. If derived Hom along `Δ` kills the termwise extension
of scalars along `p` of a complex `P` of `A`-modules, then `P` is acyclic. This extends the
statement of `StacksFrontier.RingTheory.Dualizing.RelativeUniquenessConservativity` for the left
coprojection of `A ⊗[R] A` to an arbitrary section.

It also gives a chain-level criterion for that vanishing: when `N` is a bounded-above complex of
projective `S`-modules representing `A` (restricted along `Δ`), derived Hom along `Δ` kills `Y`
as soon as every cohomology class of the Hom complex `Hom^•(N, Y)` vanishes.

## Main results

All names are in the namespace `Dualizing.SectionConservativity`.

* `acyclic_of_isZero_derivedHom`: conservativity of `Δ^! ∘ p^*` along a section.
* `isZero_derivedHom_of_cohomologyClass_eq_zero`: the chain-level criterion for the vanishing of
  derived Hom along `Δ`.

## References

* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated Dualizing.Conservativity

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing.SectionConservativity

variable {A S : Type u} [CommRing A] [CommRing S]

/-- **Conservativity of `Δ^! ∘ p^*` along a section.** If `Δ : S → A` has finitely generated
kernel and `p` is a section of it, then a complex of `A`-modules whose termwise extension of
scalars along `p` is killed by derived Hom along `Δ` is acyclic. -/
theorem acyclic_of_isZero_derivedHom (Δ : S →+* A) (p : A →+* S)
    (hΔ : Δ.comp p = RingHom.id A) (hker : (RingHom.ker Δ).FG)
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hD : IsZero ((derivedHom.{u, u} Δ).obj
      (DerivedCategory.Q.obj ((CochainComplex.extendScalars p).obj P)))) :
    P.Acyclic := by
  let X₀ := (CochainComplex.extendScalars p).obj P
  obtain ⟨s, hs⟩ := hker
  let ts := s.toList
  have hspan : Ideal.span {x | x ∈ ts} = RingHom.ker Δ := by
    have : {x | x ∈ ts} = (s : Set S) := by ext x; simp [ts]
    rw [this, hs]
  obtain ⟨adj⟩ := restrictScalarsDerived_adj_derivedHom.{u, u, u} Δ
  have hbase : Vanish (RingHom.ker Δ) (DerivedCategory.Q.obj X₀) := by
    intro M hM q φ
    let W := (ModuleCat.restrictScalars p).obj M
    have hsmul : ∀ (b : S) (m : M), p (Δ b) • m = b • m := by
      intro b m
      have hb : b - p (Δ b) ∈ RingHom.ker Δ := by
        rw [RingHom.mem_ker, map_sub, sub_eq_zero]
        exact (RingHom.congr_fun hΔ (Δ b)).symm
      have := hM _ hb m
      rw [sub_smul, sub_eq_zero] at this
      exact this.symm
    let iM : (ModuleCat.restrictScalars Δ).obj W ≅ M :=
      (AddEquiv.toLinearEquiv (M := ↑((ModuleCat.restrictScalars Δ).obj W)) (M₂ := ↑M)
        (AddEquiv.refl _) (fun b x => hsmul b x)).toModuleIso
    let L := (ModuleCat.restrictScalars.{u} Δ).mapDerivedCategory
    let e₁ : L.obj (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj W)⟦q⟧) ≅
        ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj M)⟦q⟧ :=
      (L.commShiftIso q).app _ ≪≫ (shiftFunctor _ q).mapIso
        (((ModuleCat.restrictScalars.{u} Δ).mapDerivedCategorySingleFunctor 0).app W ≪≫
          (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).mapIso iM)
    have h0 : e₁.hom ≫ φ = 0 :=
      (adj.homEquiv _ _).injective (hD.eq_of_tgt _ _ |>.trans (adj.homAddEquiv_zero _ _).symm)
    simpa using h0
  have hcone : Vanish ⊥ (DerivedCategory.Q.obj (coneSeq X₀ ts)) := by
    refine Vanish.coneSeq ts ⊥ X₀ ?_
    rwa [bot_sup_eq, hspan]
  have hac := (isZero_Q_obj_iff _).mp (isZero_of_vanish_bot hcone)
  exact acyclic_of_acyclic_coneSeq p Δ hΔ P ts
    (fun t ht => by
      rw [← RingHom.mem_ker, ← hspan]
      exact Ideal.subset_span ht) hac

/-- **A chain-level criterion for `Δ^!(Y) = 0`.** Let `N` be a bounded-above complex of projective
`S`-modules representing `A`, restricted along `Δ`, in `D(S)`. If every cohomology class of the
Hom complex `Hom^•(N, Y)` vanishes, then derived Hom along `Δ` kills `Y`. -/
theorem isZero_derivedHom_of_cohomologyClass_eq_zero (Δ : S →+* A)
    (N : CochainComplex (ModuleCat.{u} S) ℤ) (d : ℤ) [N.IsStrictlyLE d]
    [∀ i, Projective (N.X i)]
    (eN : DerivedCategory.Q.obj N ≅ (ModuleCat.restrictScalars.{u} Δ).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)))
    (Y : CochainComplex (ModuleCat.{u} S) ℤ)
    (hY : ∀ (q : ℤ) (c : CochainComplex.HomComplex.CohomologyClass N Y q), c = 0) :
    IsZero ((derivedHom.{u, u} Δ).obj (DerivedCategory.Q.obj Y)) := by
  obtain ⟨adj⟩ := restrictScalarsDerived_adj_derivedHom.{u, u, u} Δ
  let Z := (derivedHom.{u, u} Δ).obj (DerivedCategory.Q.obj Y)
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  intro n
  have : Projective (ModuleCat.of A A) :=
    ModuleCat.projective_of_free (Module.Basis.singleton PUnit.{1} A)
  have hφ : ∀ φ : (DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj (ModuleCat.of A A) ⟶ Z,
      φ = 0 := by
    intro φ
    let L := (ModuleCat.restrictScalars.{u} Δ).mapDerivedCategory
    let eA := ((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso (-n) n 0
      (neg_add_cancel n)).app (ModuleCat.of A A)
    let e : L.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj (ModuleCat.of A A)) ≅
        (DerivedCategory.Q.obj N)⟦-n⟧ :=
      L.mapIso eA.symm ≪≫ (L.commShiftIso (-n)).app _ ≪≫ (shiftFunctor _ (-n)).mapIso eN.symm
    let ψ := (adj.homEquiv _ _).symm φ
    let ψ' : DerivedCategory.Q.obj N ⟶ DerivedCategory.Q.obj (Y⟦n⟧) :=
      (shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{u} S)) (-n) n
          (neg_add_cancel n)).inv.app (DerivedCategory.Q.obj N) ≫
        (e.inv ≫ ψ)⟦n⟧' ≫ ((DerivedCategory.Q.commShiftIso n).app Y).inv
    let κ := DerivedCategory.quotientCompQhIso (ModuleCat.{u} S)
    obtain ⟨c, hc⟩ := (cohomologyClassRHomAddEquiv N Y d n).surjective
      ((κ.app N).hom ≫ ψ' ≫ (κ.app (Y⟦n⟧)).inv)
    have hψ' : ψ' = 0 := by
      have h0 : (κ.app N).hom ≫ ψ' ≫ (κ.app (Y⟦n⟧)).inv = 0 := by
        rw [← hc, hY n c, map_zero]
      simpa using h0
    have h1 : (e.inv ≫ ψ)⟦n⟧' = 0 := by
      simpa [ψ'] using congrArg (fun g => (shiftFunctorCompIsoId
          (DerivedCategory (ModuleCat.{u} S)) (-n) n (neg_add_cancel n)).hom.app
            (DerivedCategory.Q.obj N) ≫ g ≫ ((DerivedCategory.Q.commShiftIso n).app Y).hom) hψ'
    have hψ : e.inv ≫ ψ = 0 :=
      (shiftFunctor (DerivedCategory (ModuleCat.{u} S)) n).map_injective
        (by rw [h1, Functor.map_zero])
    exact (adj.homEquiv _ _).symm.injective
      ((by simpa using hψ : ψ = 0).trans (adj.homAddEquiv_symm_zero _ _).symm)
  suffices h : ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj Z, x = 0 by
    have : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj Z) :=
      ⟨fun x y => by rw [h x, h y]⟩
    exact ModuleCat.isZero_of_subsingleton _
  intro x
  let χ : ModuleCat.of A A ⟶ (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj Z :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton A _ x)
  obtain ⟨φ, hφχ⟩ :=
    (DerivedCategory.homologyFromSingleAddEquiv (ModuleCat.of A A) Z n).surjective χ
  have h0 : χ = 0 := by rw [← hφχ, hφ φ, map_zero]
  simpa [χ] using congrArg (fun g => g.hom (1 : A)) h0

end Dualizing.SectionConservativity
