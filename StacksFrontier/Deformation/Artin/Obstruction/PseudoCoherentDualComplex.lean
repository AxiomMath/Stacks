module

public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.CategoryTheory.Shift.ShiftedHomConj
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso
public import StacksFrontier.Deformation.Artin.Obstruction.PerfectDualShiftedHom
public import StacksFrontier.Homology.DerivedCategory.HomBijectiveOfHomologyIso

/-!
# A perfect complex computing low Ext groups out of a pseudo-coherent object

Let `L` be a `(-3)`-pseudo-coherent object of `D(A)` (Stacks 064Q). The functors
`M ↦ Ext^n_A(L, M)` for `n = 1, 2` are computed by a perfect complex: there is a perfect `K` of
`D(A)` with

`Hⁿ(K ⊗ᴸ_A M) ≅ Ext^n_A(L, M)`, `n = 1, 2`,

naturally in the `A`-module `M`, carrying the connecting map `H¹(K ⊗ᴸ M₃) ⟶ H²(K ⊗ᴸ M₁)` of a
short exact sequence `0 → M₁ → M₂ → M₃ → 0` to composition with its class in
`Ext¹_A(M₃, M₁)`.

In the first proof of Stacks 08WA this produces the complex `K` of the dual deformation
situation (Stacks 07YX) of a coherent sheaf over `Spec A`, from the pseudo-coherent object `L`
of part (B) of Stacks 08JR, whose Ext groups are the Ext groups `Ext^n(ℱ, ℱ ⊗ M)` on the base
change. Part (A) of 08JR, which the source quotes, gives the same `K` directly. The route
through part (B) keeps every comparison inside `D(A)`.

## Main results

* `Deformation.Artin.exists_perfect_shiftedHomEquiv_of_isPseudoCoherentFrom`.
* `Deformation.Artin.exists_perfect_shiftedHomEquiv_of_isPseudoCoherentFrom_of_ringEquiv`: the
  same with `L` given over a ring `R` isomorphic to `A`, the Ext groups being taken in `D(R)`.

## Implementation notes

The source of an `m`-pseudo-coherent approximation `α : Q(E) ⟶ L` is perfect. Precomposition
with `α` is bijective on morphisms into objects in degrees `≥ m + 1`
(`DerivedCategory.bijective_precomp_of_isIso_homology_of_epi`), and `M[n]` lies in degrees
`≥ -2` for `n ≤ 2`. The complex `K` is the one of perfect duality for `Q(E)`
(`Deformation.Artin.exists_perfect_shiftedHomEquiv`).

## References

* [Stacks Project, Tag 064Q](https://stacks.math.columbia.edu/tag/064Q)
* [Stacks Project, Tag 07VI](https://stacks.math.columbia.edu/tag/07VI)
* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Deformation.Artin

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A]

/-- Precomposition with a morphism `α : P ⟶ L`, as an additive map of shifted morphisms. -/
def shiftedHomPrecompAddHom {P L Y : DerivedCategory (ModuleCat.{u} A)} (α : P ⟶ L) (n : ℤ) :
    ShiftedHom L Y n →+ ShiftedHom P Y n where
  toFun f := α ≫ f
  map_zero' := Limits.comp_zero
  map_add' _ _ := Preadditive.comp_add _ _ _ _ _ _

/-- **A perfect complex computing `Ext¹` and `Ext²` out of a `(-3)`-pseudo-coherent object.**
For a `(-3)`-pseudo-coherent `L` in `D(A)` there are a perfect `K` and additive bijections
`Hⁿ(K ⊗ᴸ M) ≃+ Ext^n(L, M)` for `n = 1, 2`, natural in the module `M`, carrying the connecting
map of a short exact sequence of modules to composition with its class in `Ext¹`. -/
theorem exists_perfect_shiftedHomEquiv_of_isPseudoCoherentFrom
    (L : DerivedCategory (ModuleCat.{u} A))
    (hL : StacksDraft.PseudoCoherence.IsPseudoCoherentFrom L (-3)) :
    ∃ (K : DerivedCategory (ModuleCat.{u} A)), StacksDraft.Perfect.IsPerfect K ∧
      ∃ (Ψ₁ : ∀ N : ModuleCat.{u} A, ((derivedCohomology A K 1).obj N : Type u) ≃+
          ShiftedHom L ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) 1)
        (Ψ₂ : ∀ N : ModuleCat.{u} A, ((derivedCohomology A K 2).obj N : Type u) ≃+
          ShiftedHom L ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) 2),
        (∀ {N N' : ModuleCat.{u} A} (g : N ⟶ N') (c : (derivedCohomology A K 1).obj N),
          Ψ₁ N' ((derivedCohomology A K 1).map g c) =
            (Ψ₁ N c).comp (ShiftedHom.mk₀ (0 : ℤ) rfl
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map g)) (zero_add 1)) ∧
        (∀ {N N' : ModuleCat.{u} A} (g : N ⟶ N') (c : (derivedCohomology A K 2).obj N),
          Ψ₂ N' ((derivedCohomology A K 2).map g c) =
            (Ψ₂ N c).comp (ShiftedHom.mk₀ (0 : ℤ) rfl
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map g)) (zero_add 2)) ∧
        (∀ {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact)
          (c : (derivedCohomology A K 1).obj Sq.X₃),
          Ψ₂ Sq.X₁ (boundaryMap A K hSq c) = (Ψ₁ Sq.X₃ c).comp hSq.singleδ (by omega)) := by
  obtain ⟨E, hE, α, hiso, hepi⟩ := hL
  obtain ⟨a, ha⟩ := hE.lowerBound
  obtain ⟨b, hb⟩ := hE.upperBound
  have hP : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj E) :=
    ⟨E, a, b, ha, hb, fun i => (hE.finiteFree i).1,
      fun i => have := (hE.finiteFree i).2; Module.Projective.of_free, ⟨Iso.refl _⟩⟩
  obtain ⟨K, hK, Ψ, hnat, hδ⟩ := exists_perfect_shiftedHomEquiv (DerivedCategory.Q.obj E) hP
  -- precomposition with `α` is bijective in the degrees that matter
  have hbij : ∀ (n : ℤ), n ≤ 2 → ∀ N : ModuleCat.{u} A,
      Function.Bijective (shiftedHomPrecompAddHom (A := A)
        (Y := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) α n) := by
    intro n hn N
    have h0 : ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N).IsGE 0 :=
      inferInstance
    have h1 : (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)⟦n⟧).IsGE (-n) :=
      DerivedCategory.TStructure.t.isGE_shift _ 0 n (-n) (by omega)
    have h2 : (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)⟦n⟧).IsGE (-3 + 1) :=
      DerivedCategory.TStructure.t.isGE_of_ge _ (-3 + 1) (-n) (by omega)
    exact DerivedCategory.bijective_precomp_of_isIso_homology_of_epi α (-3) hiso hepi _
  let β : ∀ (n : ℤ), n ≤ 2 → ∀ N : ModuleCat.{u} A,
      ShiftedHom L ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) n ≃+
        ShiftedHom (DerivedCategory.Q.obj E)
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) n := fun n hn N =>
    AddEquiv.ofBijective _ (hbij n hn N)
  have hβ : ∀ (n : ℤ) (hn : n ≤ 2) (N : ModuleCat.{u} A)
      (f : ShiftedHom L ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) n),
      β n hn N f = α ≫ f := fun _ _ _ _ => rfl
  let Ψ₁ : ∀ N : ModuleCat.{u} A, ((derivedCohomology A K 1).obj N : Type u) ≃+
      ShiftedHom L ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) (1 : ℤ) := fun N =>
    (Ψ 1 ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)).trans
      (β 1 (by omega) N).symm
  let Ψ₂ : ∀ N : ModuleCat.{u} A, ((derivedCohomology A K 2).obj N : Type u) ≃+
      ShiftedHom L ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) (2 : ℤ) := fun N =>
    (Ψ 2 ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)).trans
      (β 2 le_rfl N).symm
  -- precomposition with `α` commutes with composition on the right
  have hcomp : ∀ {n p q : ℤ} {Y Z : DerivedCategory (ModuleCat.{u} A)}
      (f : ShiftedHom L Y n) (g : ShiftedHom Y Z p) (h : p + n = q),
      α ≫ f.comp g h =
        ShiftedHom.comp (show ShiftedHom (DerivedCategory.Q.obj E) Y n from α ≫ f) g h := by
    intro n p q Y Z f g h
    simp only [ShiftedHom.comp, Category.assoc]
  refine ⟨K, hK, Ψ₁, Ψ₂, ?_, ?_, ?_⟩
  · intro N N' g c
    apply (β 1 (by omega) N').injective
    simp only [Ψ₁, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
    rw [hβ 1 (by omega) N', hcomp, ← hβ 1 (by omega) N, AddEquiv.apply_symm_apply]
    exact hnat 1 _ _ _ c
  · intro N N' g c
    apply (β 2 le_rfl N').injective
    simp only [Ψ₂, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
    rw [hβ 2 le_rfl N', hcomp, ← hβ 2 le_rfl N, AddEquiv.apply_symm_apply]
    exact hnat 2 _ _ _ c
  · intro Sq hSq c
    apply (β 2 le_rfl Sq.X₁).injective
    simp only [Ψ₁, Ψ₂, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
    rw [hβ 2 le_rfl Sq.X₁, hcomp, ← hβ 1 (by omega) Sq.X₃, AddEquiv.apply_symm_apply]
    exact hδ hSq.singleTriangle c

/-- A short complex of `A`-modules read over an isomorphic ring `R`, written with
`ShortComplex.mk` so that its terms are syntactically the terms of the sequence read over `R`. -/
abbrev ringEquivShortComplex {R : Type u} [CommRing R] (e : A ≃+* R)
    (Sq : ShortComplex (ModuleCat.{u} A)) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (X₁ := (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.obj Sq.X₁)
    (X₂ := (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.obj Sq.X₂)
    (X₃ := (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.obj Sq.X₃)
    ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.map Sq.f)
    ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.map Sq.g)
    (by rw [← Functor.map_comp, Sq.zero, Functor.map_zero])

/-- A short exact sequence of `A`-modules read over an isomorphic ring is short exact. -/
theorem ringEquivShortComplex_shortExact {R : Type u} [CommRing R] (e : A ≃+* R)
    {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact) :
    (ringEquivShortComplex e Sq).ShortExact :=
  hSq.map_of_exact (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor

/-- **The same, with the pseudo-coherent object over an isomorphic ring.** For a ring
isomorphism `e : A ≃+* R` and a `(-3)`-pseudo-coherent `L` in `D(R)` there are a perfect `K` in
`D(A)` and additive bijections `Hⁿ(K ⊗ᴸ_A M) ≃+ Ext^n_R(L, M)` for `n = 1, 2`, where an
`A`-module `M` is read as an `R`-module along `e`, natural in `M` and carrying the connecting
map of a short exact sequence of `A`-modules to composition with the class of the sequence read
over `R`. -/
theorem exists_perfect_shiftedHomEquiv_of_isPseudoCoherentFrom_of_ringEquiv
    {R : Type u} [CommRing R] (e : A ≃+* R) (L : DerivedCategory (ModuleCat.{u} R))
    (hL : StacksDraft.PseudoCoherence.IsPseudoCoherentFrom L (-3)) :
    ∃ (K : DerivedCategory (ModuleCat.{u} A)), StacksDraft.Perfect.IsPerfect K ∧
      ∃ (Ψ₁ : ∀ N : ModuleCat.{u} A, ((derivedCohomology A K 1).obj N : Type u) ≃+
          ShiftedHom L ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
            ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.obj N)) 1)
        (Ψ₂ : ∀ N : ModuleCat.{u} A, ((derivedCohomology A K 2).obj N : Type u) ≃+
          ShiftedHom L ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
            ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.obj N)) 2),
        (∀ {N N' : ModuleCat.{u} A} (g : N ⟶ N') (c : (derivedCohomology A K 1).obj N),
          Ψ₁ N' ((derivedCohomology A K 1).map g c) =
            (Ψ₁ N c).comp (ShiftedHom.mk₀ (0 : ℤ) rfl
              ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
                ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.map g)))
              (zero_add 1)) ∧
        (∀ {N N' : ModuleCat.{u} A} (g : N ⟶ N') (c : (derivedCohomology A K 2).obj N),
          Ψ₂ N' ((derivedCohomology A K 2).map g c) =
            (Ψ₂ N c).comp (ShiftedHom.mk₀ (0 : ℤ) rfl
              ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
                ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor.map g)))
              (zero_add 2)) ∧
        (∀ {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact)
          (c : (derivedCohomology A K 1).obj Sq.X₃),
          Ψ₂ Sq.X₁ (boundaryMap A K hSq c) = (Ψ₁ Sq.X₃ c).comp
            (ringEquivShortComplex_shortExact e hSq).singleδ (by omega)) := by
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, u} e.symm
  let G := E.functor
  let F := StacksDraft.PseudoCoherence.coefficientRestriction.{u, u, u} e
  let ED : DerivedCategory (ModuleCat.{u} A) ≌ DerivedCategory (ModuleCat.{u} R) :=
    StacksDraft.DerivedRingIso.mapDerivedCategoryEquivalence G F E.unitIso E.counitIso
  let LA := F.mapDerivedCategory.obj L
  have hLA : StacksDraft.PseudoCoherence.IsPseudoCoherentFrom LA (-3) :=
    ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_of_ringEquiv e L).1 (-3)).1 hL
  obtain ⟨K, hK, Ψ₁, Ψ₂, h₁, h₂, hδ⟩ :=
    exists_perfect_shiftedHomEquiv_of_isPseudoCoherentFrom LA hLA
  let ε : G.mapDerivedCategory.obj LA ≅ L := ED.counitIso.app L
  let σ : ∀ N : ModuleCat.{u} A, G.mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (G.obj N) := fun N =>
    (G.mapDerivedCategorySingleFunctor 0).app N
  let hG : G.mapDerivedCategory.FullyFaithful := ED.fullyFaithfulFunctor
  let Θ : ∀ (N : ModuleCat.{u} A) (n : ℤ),
      ShiftedHom LA ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) n ≃+
        ShiftedHom L ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (G.obj N)) n :=
    fun N n => ShiftedHom.conjMapAddEquiv G.mapDerivedCategory hG ε (σ N) n
  refine ⟨K, hK, fun N => (Ψ₁ N).trans (Θ N 1), fun N => (Ψ₂ N).trans (Θ N 2), ?_, ?_, ?_⟩
  · intro N N' g c
    simp only [AddEquiv.trans_apply]
    rw [h₁ g c]
    exact ShiftedHom.conjMapAddEquiv_comp_mk₀ _ _ _ _ _ _ _
      ((G.mapDerivedCategorySingleFunctor 0).hom.naturality g) 1 _
  · intro N N' g c
    simp only [AddEquiv.trans_apply]
    rw [h₂ g c]
    exact ShiftedHom.conjMapAddEquiv_comp_mk₀ _ _ _ _ _ _ _
      ((G.mapDerivedCategorySingleFunctor 0).hom.naturality g) 2 _
  · intro Sq hSq c
    simp only [AddEquiv.trans_apply]
    rw [hδ hSq c]
    exact ShiftedHom.conj_map_comp G.mapDerivedCategory ε (σ Sq.X₃) (σ Sq.X₁) _ hSq.singleδ _
      (hSq.mapShiftedHom_singleδ G) _

end Deformation.Artin

end
