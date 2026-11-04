module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import StacksFrontier.Algebra.Module.Matlis
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.Triangulated

/-!
# Local cohomology modules are `A`-linear in the coefficients and supported in `T`

Three structural facts about the local cohomology modules `H^i_T(M)` of an `A`-module `M`, all of
which the computations with the long exact sequence need and none of which is in the library:

* `H^i_T(-)` is `A`-linear, so that the map induced by multiplication by `r ∈ A` on `M` is
  multiplication by `r` on `H^i_T(M)`;
* `H^i_T(M) = 0` for `i < 0`;
* `H^i_T(K)` is supported in `T` for every object `K` of the derived category.

The first is proved by reducing, through the canonical comparison
`derivedSectionsWithSupportInUnit`, to the `A`-linearity of sections with support on a K-injective
complex, where the comparison is invertible. The other two are read off the same K-injective
presentation: for `M` a module one may take the K-injective complex to be a bounded-below complex
of injectives, which has no terms in negative degrees, and the complex of `T`-supported sections of
any complex has `T`-supported terms, so its homology, a subquotient, is `T`-supported because the
modules supported in `T` form a Serre subcategory.

## Main results

* `Stacks.LocalCohomology.sectionsWithSupportInFunctor_linear`,
  `Stacks.LocalCohomology.derivedSectionsWithSupportIn_linear`,
  `Stacks.LocalCohomology.derivedHomologyFunctor_linear` — the three `A`-linearity statements.
* `Stacks.LocalCohomology.localCohomologyMap_smul_id` — **multiplication by `r` on `M` induces
  multiplication by `r` on `H^i_T(M)`.**
* `Stacks.LocalCohomology.nonempty_localCohomology_iso_homology_of_isKInjective` — local
  cohomology read off a K-injective presentation.
* `Stacks.LocalCohomology.isZero_localCohomologyWithSupportIn_of_neg` — **`H^i_T(M) = 0` for
  `i < 0`.**
* `Stacks.LocalCohomology.support_localCohomologyWithSupportIn_subset` — **`H^i_T(K)` is
  supported in `T`.**
* `Stacks.LocalCohomology.isZero_of_mono_smul_id` — a module supported in `V(I)` on which some
  `f ∈ I` acts injectively is zero.

## Implementation notes

`Functor.Linear` for a functor out of the derived category is checked on the scalar multiples of
the identities (`Functor.linear_iff`), and transported along an isomorphism of objects by
`Stacks.LocalCohomology.map_smul_id_of_iso`; this is the argument of Mathlib's
`CategoryTheory.Localization.functor_linear_iff`, which does not apply directly to
`derivedSectionsWithSupportIn` because its composition with `Qh` is not known to be linear — only
the canonical comparison to it from the linear functor on complexes is available, and that
comparison is invertible exactly on the K-injective complexes.

No Stacks attribute is placed: none of these statements is a tagged statement of the Stacks
project.

## References

* [Stacks Project, Tag 0EF4](https://stacks.math.columbia.edu/tag/0EF4)
* [Stacks Project, Tag 0EEZ](https://stacks.math.columbia.edu/tag/0EEZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-! ### `A`-linearity -/

section Linear

variable (A : Type u) [CommRing A]

/-- Scalar multiples of identities are transported along an isomorphism of objects: if a functor
sends `r • 𝟙 X` to `r • 𝟙`, it does the same at every object isomorphic to `X`. This is the
computation inside Mathlib's `CategoryTheory.Localization.functor_linear_iff`, isolated so that it
can be used where that lemma does not apply. -/
lemma map_smul_id_of_iso {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] [Linear A C] [Linear A D] (F : C ⥤ D) {X Y : C} (e : X ≅ Y) (r : A)
    (h : F.map (r • 𝟙 X) = r • 𝟙 (F.obj X)) : F.map (r • 𝟙 Y) = r • 𝟙 (F.obj Y) := by
  have he : r • 𝟙 Y = e.inv ≫ (r • 𝟙 X) ≫ e.hom := by simp
  have hs : F.map e.inv ≫ (r • 𝟙 (F.obj X)) ≫ F.map e.hom =
      r • (F.map e.inv ≫ F.map e.hom) := by simp
  rw [he, F.map_comp, F.map_comp, h, hs, ← F.map_comp, e.inv_hom_id, F.map_id]

/-- Taking homology of a cochain complex is `A`-linear. -/
lemma homologyMap_smul {K L : CochainComplex (ModuleCat.{max u v} A) ℤ} (φ : K ⟶ L) (n : ℤ)
    (r : A) :
    HomologicalComplex.homologyMap (r • φ) n = r • HomologicalComplex.homologyMap φ n := by
  rw [HomologicalComplex.homologyMap, HomologicalComplex.homologyMap,
    show (HomologicalComplex.shortComplexFunctor (ModuleCat.{max u v} A)
        (ComplexShape.up ℤ) n).map (r • φ) =
      r • (HomologicalComplex.shortComplexFunctor (ModuleCat.{max u v} A)
        (ComplexShape.up ℤ) n).map φ from rfl,
    ShortComplex.homologyMap_smul]
  rfl

/-- The homology functor on the derived category of `A`-modules is `A`-linear. -/
instance derivedHomologyFunctor_linear (n : ℤ) :
    Functor.Linear A (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n) := by
  have hcx : Functor.Linear A (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} A)
      (ComplexShape.up ℤ) n) := ⟨fun {_ _} φ r ↦ homologyMap_smul A φ n r⟩
  let hlift : Localization.Lifting (DerivedCategory.Q (C := ModuleCat.{max u v} A))
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} A) (ComplexShape.up ℤ) n)
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n) :=
    ⟨DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} A) n⟩
  exact (Localization.functor_linear_iff DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)) A _ _).mp hcx

/-- Sections with support in `T` is an `A`-linear functor. -/
instance sectionsWithSupportInFunctor_linear (T : Set (PrimeSpectrum A)) :
    Functor.Linear A (sectionsWithSupportInFunctor.{u, v} A T) where
  map_smul {M N} f r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl

/-- If `q : X ⟶ L` is a quasi-isomorphism and `Q X ≅ K`, then `L` has image `K` in the derived
category. -/
private lemma nonempty_Qh_iso_of_quasiIso {X L : CochainComplex (ModuleCat.{max u v} A) ℤ}
    (q : X ⟶ L) [QuasiIso q] {K : DerivedCategory (ModuleCat.{max u v} A)}
    (e : DerivedCategory.Q.obj X ≅ K) :
    Nonempty (DerivedCategory.Qh.obj ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
      (ComplexShape.up ℤ)).obj L) ≅ K) :=
  ⟨(DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).app L ≪≫
    (asIso (DerivedCategory.Q.map q)).symm ≪≫ e⟩

/-- Every object of the derived category of `A`-modules is the image of a K-injective complex. -/
lemma exists_isKInjective_Qh_iso (K : DerivedCategory (ModuleCat.{max u v} A)) :
    ∃ L : CochainComplex (ModuleCat.{max u v} A) ℤ, L.IsKInjective ∧
      Nonempty (DerivedCategory.Qh.obj ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
        (ComplexShape.up ℤ)).obj L) ≅ K) := by
  obtain ⟨L, q, hL, hq⟩ := exists_quasiIso_isKInjective_moduleCat.{u, v} (A := A)
    (DerivedCategory.Q.objPreimage K)
  have := hq
  exact ⟨L, hL, nonempty_Qh_iso_of_quasiIso.{u, v} A q (DerivedCategory.Q.objObjPreimageIso K)⟩

/-- Derived sections with support in `T` is an `A`-linear functor.

A scalar multiple of an identity is checked on a K-injective complex, where the canonical
comparison from sections with support to its derived functor is invertible, and sections with
support on complexes is `A`-linear. -/
instance derivedSectionsWithSupportIn_linear (T : Set (PrimeSpectrum A)) :
    Functor.Linear A (derivedSectionsWithSupportIn.{u, v} A T) := by
  rw [Functor.linear_iff]
  intro K r
  obtain ⟨L, hL, ⟨e⟩⟩ := exists_isKInjective_Qh_iso.{u, v} A K
  have := hL
  refine map_smul_id_of_iso A _ e r ?_
  set X := (HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj L
  rw [show (r • 𝟙 (DerivedCategory.Qh.obj X)) = DerivedCategory.Qh.map (r • 𝟙 X) by simp]
  have hnat := (derivedSectionsWithSupportInUnit.{u, v} A T).naturality (r • 𝟙 X)
  simp only [Functor.comp_map] at hnat
  refine (cancel_epi ((derivedSectionsWithSupportInUnit.{u, v} A T).app X)).mp ?_
  rw [← hnat]
  simp

/-- **Multiplication by `r` on `M` induces multiplication by `r` on `H^i_T(M)`.** -/
lemma localCohomologyMap_smul_id (T : Set (PrimeSpectrum A)) (i : ℤ)
    (M : ModuleCat.{max u v} A) (r : A) :
    localCohomologyMap.{u, v} A T i (r • 𝟙 M) =
      r • 𝟙 (localCohomologyWithSupportIn A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i) := by
  rw [localCohomologyMap, Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_smul,
    CategoryTheory.Functor.map_id, Functor.map_smul, CategoryTheory.Functor.map_id]

end Linear

/-! ### Vanishing in negative degrees, and supportedness -/

section Vanishing

variable {A : Type u} [CommRing A]

/-- Local cohomology read off a K-injective presentation: if `L` is a K-injective complex whose
image in the derived category is `K`, then `H^i_T(K)` is the degree-`i` cohomology of the complex
of `T`-supported sections of `L`. -/
lemma nonempty_localCohomology_iso_homology_of_isKInjective
    (T : Set (PrimeSpectrum A)) (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ)
    (L : CochainComplex (ModuleCat.{max u v} A) ℤ) [L.IsKInjective]
    (e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
      (ComplexShape.up ℤ)).obj L) ≅ K) :
    Nonempty (localCohomologyWithSupportIn A T K i ≅
      ((Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A T)
        (ComplexShape.up ℤ)).obj L).homology i) :=
  ⟨(DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).mapIso
      ((derivedSectionsWithSupportIn A T).mapIso e.symm) ≪≫
    localCohomologyWithSupportInIsoOfKInjective.{u, v} T i L⟩

/-- **Local cohomology of a module vanishes in negative degrees.** A bounded-below injective
resolution is K-injective and has no terms in negative degrees, so neither has its complex of
`T`-supported sections. -/
theorem isZero_localCohomologyWithSupportIn_of_neg (T : Set (PrimeSpectrum A))
    (M : ModuleCat.{max u v} A) (i : ℤ) (hi : i < 0) :
    IsZero (localCohomologyWithSupportIn A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i) := by
  have : EnoughInjectives (ModuleCat.{max u v} A) := ModuleCat.enoughInjectives A
  obtain ⟨L, q, hq, hinj, hGE⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
      ((CochainComplex.singleFunctor (ModuleCat.{max u v} A) 0).obj M) 0
  have := hq
  have : ∀ n : ℤ, CategoryTheory.Injective (L.X n) := hinj
  have := hGE
  have : L.IsKInjective := CochainComplex.isKInjective_of_injective L 0
  obtain ⟨e⟩ := nonempty_Qh_iso_of_quasiIso.{u, v} A q
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} A) 0).app M).symm
  obtain ⟨iso⟩ := nonempty_localCohomology_iso_homology_of_isKInjective.{u, v} T _ i L e
  exact IsZero.of_iso (HomologicalComplex.ExactAt.of_isZero
    ((sectionsWithSupportInFunctor.{u, v} A T).map_isZero
      (L.isZero_of_isStrictlyGE 0 i hi))).isZero_homology iso

/-- **Local cohomology modules with support in `T` are supported in `T`.** The complex of
`T`-supported sections of a K-injective representative has `T`-supported terms, and its homology
is a subquotient of one of them. -/
theorem support_localCohomologyWithSupportIn_subset (T : Set (PrimeSpectrum A))
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    Module.support A (localCohomologyWithSupportIn A T K i) ⊆ T := by
  obtain ⟨L, hL, ⟨e⟩⟩ := exists_isKInjective_Qh_iso.{u, v} A K
  have := hL
  obtain ⟨iso⟩ := nonempty_localCohomology_iso_homology_of_isKInjective.{u, v} T K i L e
  set C := (Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A T)
    (ComplexShape.up ℤ)).obj L
  have hX : (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A)) (C.X i) :=
    support_sectionsWithSupportIn_subset T (L.X i)
  have hcyc : (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A))
      (C.cycles i) := ObjectProperty.prop_of_mono _ (C.iCycles i) hX
  have hhom : (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A))
      (C.homology i) := ObjectProperty.prop_of_epi _ (C.homologyπ i) hcyc
  exact (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A)).prop_of_iso
    iso.symm hhom

end Vanishing

/-! ### Supported modules with an injective scalar action -/

section Regular

variable {A : Type u} [CommRing A]

/-- If `f ^ n` kills an element and `f` acts injectively, the element is zero. -/
private lemma eq_zero_of_pow_smul_eq_zero {M : Type*} [AddCommGroup M] [Module A M] {f : A}
    (hf : Function.Injective fun x : M ↦ f • x) :
    ∀ (n : ℕ) (x : M), f ^ n • x = 0 → x = 0 := by
  intro n
  induction n with
  | zero =>
    intro x hx
    simpa using hx
  | succ n ih =>
    intro x hx
    have h1 : f ^ n • (f • x) = 0 := by rw [smul_smul, ← pow_succ, hx]
    exact hf (show f • x = f • (0 : M) by rw [ih (f • x) h1, smul_zero])

/-- **A module supported in `V(I)` on which some `f ∈ I` acts injectively is zero.** Over a
Noetherian ring every element of such a module is killed by a power of `I`, hence by a power of
`f`, hence is zero. -/
theorem isZero_of_mono_smul_id [IsNoetherianRing A] (I : Ideal A) {f : A} (hf : f ∈ I)
    (X : ModuleCat.{max u v} A)
    (hX : Module.support A X ⊆ PrimeSpectrum.zeroLocus (I : Set A))
    (hmono : Mono (f • 𝟙 X)) : IsZero X := by
  have hinj : Function.Injective fun x : X ↦ f • x := by
    have h := (ModuleCat.mono_iff_injective (f • 𝟙 X)).mp hmono
    intro x y hxy
    exact h (show (f • 𝟙 X).hom x = (f • 𝟙 X).hom y from hxy)
  suffices hall : ∀ z : (X : Type (max u v)), z = 0 by
    have : Subsingleton (X : Type (max u v)) := subsingleton_of_forall_eq 0 hall
    exact ModuleCat.isZero_of_subsingleton X
  intro z
  have hz : z ∈ sectionsWithSupportIn A (PrimeSpectrum.zeroLocus (I : Set A)) X := by
    rw [(sectionsWithSupportIn_eq_top_iff A (PrimeSpectrum.zeroLocus (I : Set A))
      (X : Type (max u v))).mpr hX]
    exact Submodule.mem_top
  rw [mem_sectionsWithSupportIn_iff, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at hz
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hz (Ideal.fg_of_isNoetherianRing I)
  exact eq_zero_of_pow_smul_eq_zero hinj n z
    ((Ideal.mem_torsionOf_iff z (f ^ n)).mp (hn (Ideal.pow_mem_pow hf n)))

end Regular

end Stacks.LocalCohomology

end
