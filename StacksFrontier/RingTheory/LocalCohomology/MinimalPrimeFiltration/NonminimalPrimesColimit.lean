module

public import
    StacksFrontier.RingTheory.LocalCohomology.MinimalPrimeFiltration.ClosedSupportRepresentative
public import StacksFrontier.RingTheory.LocalCohomology.MinimalPrimeFiltration.LocalizationKernel
public import
    StacksFrontier.RingTheory.LocalCohomology.MinimalPrimeFiltration.PrincipalCutFirstCohomology

/-!
# The colimit term of Tag 0EF8

Let `A` be a Noetherian ring, let `T ⊆ Spec(A)` be stable under specialization and let `T'` be
the set of primes of `T` that are not minimal in `T`. The left-hand term of the exact sequence
of Tag 0EF8 is the colimit
$$ \operatorname*{colim}_{Z, f} H^1_f(H^{i-1}_Z(M)) $$
over the closed subsets `Z = V(I) ⊆ T` and the elements `f ∈ A` with `V(f) ∩ Z ⊆ T'`.

This file builds that colimit and the map out of it. The pairs `(Z, f)` form a filtered index
category `FirstIndex`, each stage is identified with the kernel of the widening map
`Hⁱ_{Z ∩ V(f)}(M) ⟶ Hⁱ_Z(M)`, and the colimit of those kernels maps to `Hⁱ_{T'}(M)` by the
widening maps along `Z ∩ V(f) ⊆ T'`. That map is injective, and its image is the kernel of
`Hⁱ_{T'}(M) ⟶ Hⁱ_T(M)`.

## Main definitions

* `Stacks.LocalCohomology.FirstIndex` — the index category of admissible pairs `(Z, f)`.
* `Stacks.LocalCohomology.firstStage` — the iterated group `H¹_f(Hⁱ⁻¹_Z(M))` at a pair.
* `Stacks.LocalCohomology.principalCutToAmbient` — the natural transformation whose kernel is
  the diagram of the colimit.
* `Stacks.LocalCohomology.principalCutKernelColimitMap` — the map out of the colimit.

## Main results

* `Stacks.LocalCohomology.firstIndex_isFiltered` — the index category is filtered.
* `Stacks.LocalCohomology.nonempty_firstStage_iso_kernel` — each stage is the kernel of the
  widening map at its pair.
* `Stacks.LocalCohomology.principalCut_kernel_colimit_injective` — the map out of the colimit is
  injective.
* `Stacks.LocalCohomology.principalCut_kernel_colimit_range` — its image is the kernel of
  `Hⁱ_{T'}(K) ⟶ Hⁱ_T(K)`.

## Implementation notes

A transition in `FirstIndex` is required to enlarge both the closed support and its intersection
with the principal cut; it is *not* required to enlarge the cut itself, since different equations
may cut out the same closed subset of a given support. Filteredness then comes from prime
avoidance: given two pairs, intersect the supports and choose a single equation lying in both
cuts yet outside the finitely many primes of the intersected support that are minimal in `T`.

Injectivity of the map out of the colimit is checked elementwise: a class of a stage dying in
`Hⁱ_{T'}(K)` dies already at a larger pair, because it dies at a larger closed subset of `T'`,
and prime avoidance produces a pair whose cut contains that closed subset. The image is computed
from the exactness statement at `Hⁱ_{T'}(K)` in
`StacksFrontier/RingTheory/LocalCohomology/MinimalPrimeFiltration/LocalizationKernel.lean`.

## References

* [Stacks Project, Tag 0EF8](https://stacks.math.columbia.edu/tag/0EF8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-! ### Prime avoidance -/

/-- **Prime avoidance for principal cuts.** Over a Noetherian ring, let `V(I) ⊆ T` be closed and
let `V(D)` be a closed subset of the nonminimal primes of `T`. Then some `f ∈ D` cuts `V(I)`
down into those nonminimal primes while `V(D)` still lies in `V(f)`. -/
theorem exists_principalCut_containing {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (I D : Ideal A)
    (hI : PrimeSpectrum.zeroLocus (I : Set A) ⊆ T)
    (hD : PrimeSpectrum.zeroLocus (D : Set A) ⊆ PrimeSpectrum.nonminimalPrimes T) :
    ∃ f : A, PrimeSpectrum.zeroLocus (D : Set A) ⊆ PrimeSpectrum.zeroLocus ({f} : Set A) ∧
      PrimeSpectrum.zeroLocus (I : Set A) ∩ PrimeSpectrum.zeroLocus ({f} : Set A) ⊆
        PrimeSpectrum.nonminimalPrimes T := by
  classical
  have havoid : ¬ (D : Set A) ⊆ ⋃ P ∈ PrimeSpectrum.asIdeal ''
      {p : PrimeSpectrum A | p ∈ T \ PrimeSpectrum.nonminimalPrimes T ∧
        p ∈ PrimeSpectrum.zeroLocus (I : Set A)}, (P : Set A) := by
    intro hsub
    obtain ⟨P, hP, hDP⟩ := (Ideal.subset_union_prime_finite
      ((finite_minimalSupportPrimes_in_closedSupport T I hI).image _)
      (f := fun P : Ideal A => P) ⊤ ⊤ (by rintro P ⟨p, hp, rfl⟩ _ _; exact p.isPrime)).mp hsub
    obtain ⟨p, hp, rfl⟩ := hP
    exact hp.1.2 (hD ((PrimeSpectrum.mem_zeroLocus p _).2 hDP))
  obtain ⟨f, hfD, hfavoid⟩ := Set.not_subset.mp havoid
  refine ⟨f, PrimeSpectrum.zeroLocus_anti_mono (Set.singleton_subset_iff.mpr hfD), ?_⟩
  intro p hp
  by_contra hpn
  exact hfavoid (Set.mem_iUnion.2 ⟨p.asIdeal, Set.mem_iUnion.2
    ⟨Set.mem_image_of_mem _ ⟨⟨hI hp.1, hpn⟩, hp.1⟩,
      (PrimeSpectrum.mem_zeroLocus p _).1 hp.2 (by simp)⟩⟩)

/-! ### The index category of admissible pairs -/

/-- A pair `(Z, f)` occurring in the first colimit of Tag 0EF8: a closed subset `Z = V(I) ⊆ T`
together with an element `f` whose zero locus cuts `Z` down into the nonminimal primes of `T`. -/
structure FirstIndex (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A)) where
  /-- The ideal cutting out the closed subset `Z ⊆ T`. -/
  I : Ideal A
  /-- The equation cutting `Z` down into the nonminimal primes. -/
  f : A
  /-- The closed subset lies in `T`. -/
  closed : PrimeSpectrum.zeroLocus (I : Set A) ⊆ T
  /-- The cut lands in the nonminimal primes of `T`. -/
  admissible : PrimeSpectrum.zeroLocus (I : Set A) ∩
    PrimeSpectrum.zeroLocus ({f} : Set A) ⊆ PrimeSpectrum.nonminimalPrimes T

/-- The closed subset cut out of the support of a pair by its equation. -/
abbrev principalCut {A : Type u} [CommRing A] {T : Set (PrimeSpectrum A)}
    (j : FirstIndex A T) : Set (PrimeSpectrum A) :=
  PrimeSpectrum.zeroLocus ((j.I : Ideal A) : Set A) ∩
    PrimeSpectrum.zeroLocus ({j.f} : Set A)

/-- The cut of a pair is the zero locus of its ideal enlarged by its equation. -/
theorem FirstIndex.zeroLocus_sup_span {A : Type u} [CommRing A] {T : Set (PrimeSpectrum A)}
    (j : FirstIndex A T) :
    PrimeSpectrum.zeroLocus ((j.I ⊔ Ideal.span ({j.f} : Set A) : Ideal A) : Set A) =
      principalCut j := by
  rw [PrimeSpectrum.zeroLocus_sup, PrimeSpectrum.zeroLocus_span]

/-- A transition between pairs enlarges both the closed support and its cut. It need not enlarge
the cut `V(f)` itself: different equations may cut out the same closed subset of a given
support. -/
instance firstIndexPreorder (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A)) :
    Preorder (FirstIndex A T) where
  le j k := k.I ≤ j.I ∧ principalCut j ⊆ principalCut k
  le_refl j := ⟨le_refl _, Set.Subset.rfl⟩
  le_trans _ _ _ hjk hkl := ⟨hkl.1.trans hjk.1, hjk.2.trans hkl.2⟩

/-- A transition of pairs enlarges the ambient closed support. -/
theorem FirstIndex.ambient_subset {A : Type u} [CommRing A] {T : Set (PrimeSpectrum A)}
    {j k : FirstIndex A T} (h : j ≤ k) :
    PrimeSpectrum.zeroLocus ((j.I : Ideal A) : Set A) ⊆
      PrimeSpectrum.zeroLocus ((k.I : Ideal A) : Set A) :=
  PrimeSpectrum.zeroLocus_anti_mono_ideal h.1

/-- **The pairs of Tag 0EF8 are filtered.** Two pairs are dominated by the pair whose support is
the intersection of the two supports and whose equation is produced by prime avoidance inside
the intersection of the two cuts. -/
instance firstIndex_isFiltered {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) : IsFiltered (FirstIndex A T) where
  nonempty := ⟨⟨⊤, 0, by simp, by simp⟩⟩
  cocone_objs j k := by
    classical
    have hL : PrimeSpectrum.zeroLocus ((j.I ⊓ k.I : Ideal A) : Set A) ⊆ T := by
      rw [PrimeSpectrum.zeroLocus_inf]
      exact Set.union_subset j.closed k.closed
    have hcutj := j.zeroLocus_sup_span
    have hcutk := k.zeroLocus_sup_span
    have hD : PrimeSpectrum.zeroLocus
        (((j.I ⊔ Ideal.span ({j.f} : Set A)) ⊓ (k.I ⊔ Ideal.span ({k.f} : Set A)) :
          Ideal A) : Set A) ⊆ PrimeSpectrum.nonminimalPrimes T := by
      rw [PrimeSpectrum.zeroLocus_inf, hcutj, hcutk]
      exact Set.union_subset j.admissible k.admissible
    obtain ⟨f, hfD, hnew⟩ := exists_principalCut_containing T (j.I ⊓ k.I) _ hL hD
    refine ⟨⟨j.I ⊓ k.I, f, hL, hnew⟩, homOfLE ⟨inf_le_left, fun p hp ↦ ?_⟩,
      homOfLE ⟨inf_le_right, fun p hp ↦ ?_⟩, trivial⟩
    · refine ⟨PrimeSpectrum.zeroLocus_anti_mono_ideal
        (inf_le_left : j.I ⊓ k.I ≤ j.I) hp.1, hfD ?_⟩
      rw [PrimeSpectrum.zeroLocus_inf]
      exact Or.inl (hcutj.ge hp)
    · refine ⟨PrimeSpectrum.zeroLocus_anti_mono_ideal
        (inf_le_right : j.I ⊓ k.I ≤ k.I) hp.1, hfD ?_⟩
      rw [PrimeSpectrum.zeroLocus_inf]
      exact Or.inr (hcutk.ge hp)
  cocone_maps _ _ _ _ := ⟨_, 𝟙 _, Subsingleton.elim _ _⟩

/-! ### The diagram of kernels -/

/-- The local cohomology of the cut of a pair, as a diagram over the pairs. -/
def principalCutCohomologyDiagram (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    FirstIndex A T ⥤ ModuleCat.{max u v} A where
  obj j := localCohomologyWithSupportIn.{u, v} A (principalCut j) K i
  map φ := changeOfSupport A (leOfHom φ).2 K i
  map_id _ := changeOfSupport_refl A _ K i
  map_comp φ ψ := (changeOfSupport_trans A (leOfHom φ).2 (leOfHom ψ).2 K i).symm

/-- The local cohomology of the ambient closed support of a pair, as a diagram over the pairs. -/
def ambientCohomologyDiagram (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    FirstIndex A T ⥤ ModuleCat.{max u v} A where
  obj j := localCohomologyWithSupportIn.{u, v} A
    (PrimeSpectrum.zeroLocus ((j.I : Ideal A) : Set A)) K i
  map φ := changeOfSupport A (FirstIndex.ambient_subset (leOfHom φ)) K i
  map_id _ := changeOfSupport_refl A _ K i
  map_comp φ ψ := (changeOfSupport_trans A (FirstIndex.ambient_subset (leOfHom φ))
    (FirstIndex.ambient_subset (leOfHom ψ)) K i).symm

/-- The widening maps from the cut of a pair to its ambient closed support. Its kernel is the
diagram whose colimit is the left-hand term of Tag 0EF8. -/
def principalCutToAmbient (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    principalCutCohomologyDiagram.{u, v} A T K i ⟶ ambientCohomologyDiagram.{u, v} A T K i where
  app _ := changeOfSupport A Set.inter_subset_left K i
  naturality _ _ φ :=
    (changeOfSupport_trans A (leOfHom φ).2 Set.inter_subset_left K i).trans
      (changeOfSupport_trans A Set.inter_subset_left
        (FirstIndex.ambient_subset (leOfHom φ)) K i).symm

/-- The widening maps from the cut of a pair into the nonminimal primes of `T`. -/
def principalCutCocone (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    Cocone (principalCutCohomologyDiagram.{u, v} A T K i) where
  pt := localCohomologyWithSupportIn.{u, v} A (PrimeSpectrum.nonminimalPrimes T) K i
  ι :=
    { app j := changeOfSupport A j.admissible K i
      naturality j k φ :=
        (changeOfSupport_trans A (leOfHom φ).2 k.admissible K i).trans
          (Category.comp_id (changeOfSupport A j.admissible K i)).symm }

/-- The cocone on the diagram of kernels obtained from `principalCutCocone`. -/
def principalCutKernelCocone (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    Cocone (kernel (principalCutToAmbient.{u, v} A T K i)) where
  pt := localCohomologyWithSupportIn.{u, v} A (PrimeSpectrum.nonminimalPrimes T) K i
  ι := kernel.ι (principalCutToAmbient.{u, v} A T K i) ≫ (principalCutCocone.{u, v} A T K i).ι

/-- **The left-hand map of the exact sequence of Tag 0EF8**: the map from the colimit
`colim_{Z,f} H¹_f(Hⁱ⁻¹_Z(K))`, presented as a colimit of kernels, to `Hⁱ_{T'}(K)`. -/
def principalCutKernelColimitMap (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    colimit (kernel (principalCutToAmbient.{u, v} A T K i)) ⟶
      localCohomologyWithSupportIn.{u, v} A (PrimeSpectrum.nonminimalPrimes T) K i :=
  colimit.desc _ (principalCutKernelCocone.{u, v} A T K i)

/-- The map out of the colimit, read on the class coming from a pair. -/
theorem principalCutKernelColimitMap_ι_apply (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ)
    (j : FirstIndex A T) (z : (kernel (principalCutToAmbient.{u, v} A T K i)).obj j) :
    (principalCutKernelColimitMap.{u, v} A T K i).hom
        ((colimit.ι (kernel (principalCutToAmbient.{u, v} A T K i)) j).hom z) =
      (changeOfSupport A j.admissible K i).hom
        (((kernel.ι (principalCutToAmbient.{u, v} A T K i)).app j).hom z) := by
  have hdesc := congrArg (fun φ => ModuleCat.Hom.hom φ z)
    (colimit.ι_desc (principalCutKernelCocone.{u, v} A T K i) j)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hdesc
  exact hdesc

/-! ### Injectivity and the image -/

/-- A class of the cut of a pair which dies in local cohomology with support in the nonminimal
primes already dies at a larger pair. -/
theorem exists_principalCut_map_eq_zero (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) (j : FirstIndex A T)
    (y : localCohomologyWithSupportIn.{u, v} A (principalCut j) K i)
    (hy : (changeOfSupport A j.admissible K i).hom y = 0) :
    ∃ (k : FirstIndex A T) (hjk : j ≤ k), (changeOfSupport A hjk.2 K i).hom y = 0 := by
  classical
  have hC := j.zeroLocus_sup_span
  have hz : (changeOfSupport A (hC.subset.trans j.admissible) K i).hom
      ((changeOfSupport A hC.ge K i).hom y) = 0 :=
    (changeOfSupport_trans_apply.{u, v} A hC.ge (hC.subset.trans j.admissible) K i y).trans hy
  obtain ⟨L, hJL, hzL⟩ := exists_closedSupport_map_eq_zero.{u, v} A
    (PrimeSpectrum.nonminimalPrimes T)
    (PrimeSpectrum.stableUnderSpecialization_nonminimalPrimes hT) K i
    (OrderDual.toDual ⟨j.I ⊔ Ideal.span ({j.f} : Set A), hC.subset.trans j.admissible⟩)
    ((changeOfSupport A hC.ge K i).hom y) hz
  obtain ⟨D, hDT, hCD, hzD⟩ : ∃ (D : Ideal A)
      (_ : PrimeSpectrum.zeroLocus (D : Set A) ⊆ PrimeSpectrum.nonminimalPrimes T)
      (hCD : PrimeSpectrum.zeroLocus ((j.I ⊔ Ideal.span ({j.f} : Set A) : Ideal A) : Set A) ⊆
        PrimeSpectrum.zeroLocus (D : Set A)),
      (changeOfSupport A hCD K i).hom ((changeOfSupport A hC.ge K i).hom y) = 0 :=
    ⟨(OrderDual.ofDual L).1, (OrderDual.ofDual L).2,
      PrimeSpectrum.zeroLocus_anti_mono_ideal hJL, hzL⟩
  have hI : PrimeSpectrum.zeroLocus ((j.I ⊓ D : Ideal A) : Set A) ⊆ T := by
    rw [PrimeSpectrum.zeroLocus_inf]
    exact Set.union_subset j.closed
      (hDT.trans (PrimeSpectrum.nonminimalPrimes_subset T))
  obtain ⟨f, hf, hadm⟩ := exists_principalCut_containing T (j.I ⊓ D) D hI hDT
  have hDk : PrimeSpectrum.zeroLocus ((D : Ideal A) : Set A) ⊆
      principalCut (⟨j.I ⊓ D, f, hI, hadm⟩ : FirstIndex A T) :=
    Set.subset_inter (PrimeSpectrum.zeroLocus_anti_mono_ideal inf_le_right) hf
  have hcut : principalCut j ⊆ principalCut (⟨j.I ⊓ D, f, hI, hadm⟩ : FirstIndex A T) :=
    hC.ge.trans (hCD.trans hDk)
  refine ⟨⟨j.I ⊓ D, f, hI, hadm⟩, ⟨inf_le_left, hcut⟩, ?_⟩
  have key : (changeOfSupport A hcut K i).hom y = 0 := by
    rw [← changeOfSupport_trans_apply.{u, v} A hC.ge (hCD.trans hDk) K i,
      ← changeOfSupport_trans_apply.{u, v} A hCD hDk K i, hzD, map_zero]
  exact key

/-- A map out of a filtered colimit of modules is injective as soon as every class of a stage
which dies in the target already dies at a later stage. -/
private theorem colimit_desc_injective_of_eventually_zero {A : Type u} [CommRing A] {J : Type u}
    [SmallCategory J] [IsFiltered J] (F : J ⥤ ModuleCat.{max u v} A) (c : Cocone F)
    (h : ∀ j (x : F.obj j), (c.ι.app j).hom x = 0 →
      ∃ (k : J) (φ : j ⟶ k), (F.map φ).hom x = 0) :
    Function.Injective (colimit.desc F c).hom := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
  obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep F (colimit.isColimit F) x
  have hy : (c.ι.app j).hom y = 0 := by
    have hdesc := congrArg (fun φ => ModuleCat.Hom.hom φ y) (colimit.ι_desc c j)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hdesc
    exact hdesc.symm.trans hx
  obtain ⟨k, φ, hk⟩ := h j y hy
  have hw := congrArg (fun ψ => ModuleCat.Hom.hom ψ y) (colimit.w F φ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hw
  exact hw.symm.trans (by rw [hk, map_zero])

/-- The kernel of a natural transformation of diagrams of modules is computed degreewise. -/
theorem kernel_app_exact {A : Type u} [CommRing A] {J : Type*} [Category J]
    {F G : J ⥤ ModuleCat.{max u v} A} (η : F ⟶ G) (j : J) (y : F.obj j) :
    (η.app j).hom y = 0 ↔ ∃ z, ((kernel.ι η).app j).hom z = y :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((ShortComplex.exact_kernel η).map ((evaluation J (ModuleCat.{max u v} A)).obj j)) y

/-- **The map out of the colimit is injective.** This is the leading zero of the exact sequence
of Tag 0EF8. -/
theorem principalCut_kernel_colimit_injective (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    Function.Injective (principalCutKernelColimitMap.{u, v} A T K i).hom := by
  refine colimit_desc_injective_of_eventually_zero.{u, v}
    (kernel (principalCutToAmbient.{u, v} A T K i))
    (principalCutKernelCocone.{u, v} A T K i) fun j x hx ↦ ?_
  obtain ⟨k, hjk, hk⟩ := exists_principalCut_map_eq_zero.{u, v} A T hT K i j
    (((kernel.ι (principalCutToAmbient.{u, v} A T K i)).app j).hom x) hx
  refine ⟨k, homOfLE hjk, ?_⟩
  refine (ModuleCat.mono_iff_injective
    ((kernel.ι (principalCutToAmbient.{u, v} A T K i)).app k)).mp inferInstance ?_
  rw [map_zero]
  have hnat := congrArg (fun ψ => ModuleCat.Hom.hom ψ x)
    ((kernel.ι (principalCutToAmbient.{u, v} A T K i)).naturality (homOfLE hjk))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  exact hnat.trans hk

/-- **The image of the map out of the colimit is the kernel of `Hⁱ_{T'}(K) ⟶ Hⁱ_T(K)`.** This is
exactness of the sequence of Tag 0EF8 at `Hⁱ_{T'}(K)`. -/
theorem principalCut_kernel_colimit_range (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ)
    (x : localCohomologyWithSupportIn.{u, v} A (PrimeSpectrum.nonminimalPrimes T) K i) :
    (changeOfSupport A (PrimeSpectrum.nonminimalPrimes_subset T) K i).hom x = 0 ↔
      ∃ z, (principalCutKernelColimitMap.{u, v} A T K i).hom z = x := by
  rw [kernel_changeOfSupport_eq_closedSupportImages.{u, v} A T hT K i x]
  constructor
  · rintro ⟨I, f, hI, hadm, y, hy, hyzero⟩
    obtain ⟨z, hz⟩ := (kernel_app_exact.{u, v} (principalCutToAmbient.{u, v} A T K i)
      (⟨I, f, hI, hadm⟩ : FirstIndex A T) y).mp hyzero
    refine ⟨(colimit.ι (kernel (principalCutToAmbient.{u, v} A T K i)) _).hom z,
      (principalCutKernelColimitMap_ι_apply.{u, v} A T K i ⟨I, f, hI, hadm⟩ z).trans ?_⟩
    rwa [hz]
  · rintro ⟨z, rfl⟩
    obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep
      (kernel (principalCutToAmbient.{u, v} A T K i)) (colimit.isColimit _) z
    exact ⟨j.I, j.f, j.closed, j.admissible,
      ((kernel.ι (principalCutToAmbient.{u, v} A T K i)).app j).hom y,
      (principalCutKernelColimitMap_ι_apply.{u, v} A T K i j y).symm,
      (kernel_app_exact.{u, v} _ j _).mpr ⟨y, rfl⟩⟩

/-! ### The stages of the colimit -/

/-- The iterated local cohomology group `H¹_f(Hⁱ⁻¹_Z(M))` at a pair `(Z, f)`: the left-hand term
of Tag 0EF8 is the colimit of these. -/
def firstStage (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))
    (M : ModuleCat.{max u v} A) (i : ℤ) (j : FirstIndex A T) : ModuleCat.{max u v} A :=
  localCohomologyWithSupportIn.{u, v} A (PrimeSpectrum.zeroLocus ({j.f} : Set A))
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
      (localCohomologyWithSupportIn.{u, v} A
        (PrimeSpectrum.zeroLocus ((j.I : Ideal A) : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) (i - 1))) 1

/-- **Each stage of the colimit is a kernel.** The iterated group `H¹_f(Hⁱ⁻¹_Z(M))` at a pair is
the kernel of the widening map `Hⁱ_{Z ∩ V(f)}(M) ⟶ Hⁱ_Z(M)`, evaluated at that pair. -/
theorem nonempty_firstStage_iso_kernel (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (M : ModuleCat.{max u v} A) (i : ℤ) (j : FirstIndex A T) :
    Nonempty (firstStage.{u, v} A T M i j ≅
      (kernel (principalCutToAmbient.{u, v} A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)).obj j) := by
  obtain ⟨e⟩ := nonempty_iteratedPrincipalCut_iso_kernel_changeOfSupport.{u, v} A j.I j.f
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i
  exact ⟨e ≪≫ (PreservesKernel.iso ((evaluation (FirstIndex A T) (ModuleCat.{max u v} A)).obj j)
    (principalCutToAmbient.{u, v} A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)).symm⟩

end Stacks.LocalCohomology

end
