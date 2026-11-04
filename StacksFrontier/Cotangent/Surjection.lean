module

public import Mathlib.Algebra.Homology.AlternatingConst
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.RingTheory.Extension.ExtendScalars
public import Mathlib.RingTheory.Kaehler.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.HomologyZero
public import StacksFrontier.Cotangent.StandardResolutionExactness
public import StacksFrontier.Cotangent.Triangle.Distinguished
public import StacksFrontier.RingTheory.Cotangent.StandardResolution

/-!
# The cotangent complex of a surjective ring map

For a surjective map of commutative rings `A → B` with kernel `I`, the cotangent complex
`L_{B/A}` has vanishing degree-zero homology, and its degree `-1` homology is the conormal
module `I/I²`.

The argument is the one in the Stacks Project. Writing `P•` for the standard simplicial
resolution of `B` over `A` and `J• = ker(P• → B)`, surjectivity of `A → B` makes
`0 → I/I² → J•/J•² → Ω[P•⁄A] ⊗[P•] B → 0`
a short exact sequence of simplicial `B`-modules, with the first term constant. Its first and
second terms have no homotopy in degrees `0` and `1`, so the connecting homomorphism identifies
`H⁻¹(L_{B/A})` with `I/I²`.

## Main definitions

* `CommAlgCat.resolutionExtension`: the terms of the standard resolution as presentations of `B`.
* `CommAlgCat.conormalSimplicialModule`: the simplicial conormal module `J•/J•²`.
* `CommAlgCat.surjectionExtension`: the presentation of `B` by `A` itself; its conormal module is
  `I/I²`, identified with `Ideal.Cotangent I` by
  `CommAlgCat.surjectionKerCotangentEquiv`.
* `CommAlgCat.conormalShortComplex` and `CommAlgCat.conormalCochainComplexes`: the short exact
  sequence above, as simplicial modules and as cochain complexes.

## Main results

* `CommAlgCat.cotangentComplex_isZero_homology_zero`: **Stacks 08RA**, `H⁰(L_{B/A}) = 0`.
* `CommAlgCat.cotangentComplex_homologyNegOneIso`: **Stacks 08RA**, `H⁻¹(L_{B/A}) = I/I²`.
* `CommAlgCat.conormalShortComplex_shortExact_app`: the local statement of the Stacks proof.
* `CommAlgCat.isZero_conormalMooreComplex_homology_zero` and
  `CommAlgCat.isZero_conormalMooreComplex_homology_one`: the two vanishing statements the
  connecting homomorphism needs.

## Implementation notes

The conormal module of a presentation is Mathlib's `Algebra.Extension.Cotangent`, which is
already a `B`-module, and the degreewise exactness is read off from Mathlib's
`Algebra.Extension.H1Cotangent`: the kernel of `J/J² → Ω[Pₙ⁄A] ⊗[Pₙ] B` is the first cotangent
homology of the presentation, and comparing with the presentation `A → B` — possible in both
directions because every `Pₙ` is a polynomial algebra and `A → B` is surjective — shows that
kernel is constant in `n` and equal to `I/I²`.

The vanishing of the degree-one homotopy of `J•/J•²` is where the two inputs enter: `J₀²`
consists of boundaries `δ₀ w - δ₁ w` with `w ∈ J₁²` (`CommAlgCat.exists_sq_of_mem_sq`), and the
standard resolution has no homotopy in degree one
(`CommAlgCat.standardResolution_exists_of_delta_sub_delta_eq_zero`).

The source states in addition that the degree `-1` isomorphism is the one induced by the
comparison map of Tag 08R9 evaluated at the object `A → B`. The isomorphism below is produced
instead as the connecting homomorphism of the short exact sequence the source itself uses, so it
is a second description of the same module. The source's own description is
`CommAlgCat.cotangentComplexHomologyNegOneIsoComparison` of
`StacksFrontier/Cotangent/SurjectionComparisonMap.lean`, which is built from the comparison map and
carries the tag with that closing clause; the two descriptions are not identified with one
another, and nothing here or there claims they are.

The comparison map itself is in the library, as `Stacks.Cotangent.comparison` of
`StacksFrontier/Cotangent/NaiveComparisonMap.lean`, at the object `(A → B)` of `C_{B/A}`, and
`Stacks.Cotangent.comparison_eq_comparisonOfHom` of
`StacksFrontier/Cotangent/NaiveComparisonIndependence.lean` says the map does not depend on the
morphism `(A → B) ⟶ (A[B] → B)` the construction chooses, so it can be computed at the
canonical `A ⟶ A[B]`.

Identifying the two descriptions of `H^{-1}(L_{B/A}) ≅ I/I²` with one another — the connecting
homomorphism of `0 → I/I² → 𝒥•/𝒥•² → Ω[P•⁄A] ⊗[P•] B → 0`, which is how
`CommAlgCat.cotangentComplex_homologyNegOneIso` below is built, and the map on `H^{-1}` induced
by `Stacks.Cotangent.comparison` — would mean comparing Mathlib's snake-lemma connecting map
`ShortComplex.ShortExact.δ` for the *epimorphism* `𝒥•/𝒥•² ↠ Ω[P•⁄A] ⊗[P•] B` of that sequence
with the mapping cone of the same epimorphism, whereas
`CochainComplex.mappingCone.homologySequenceδ_triangleh` relates `δ` to the mapping cone of the
sequence's *monomorphism*. The source asserts only the second description, and that one is
proved; this one is not asserted by any tag attribute.

## References

* [Stacks Project, Tag 08RA](https://stacks.math.columbia.edu/tag/08RA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u v

namespace CommAlgCat

/-- **Stacks Project, Tag 08RA.** The degree-zero homology of the cotangent complex of a
surjective ring map vanishes: it is the module of Kähler differentials, which is zero. -/
@[stacks 08RA "the degree-zero conclusion H⁰(L_{B/A}) = 0"]
public theorem cotangentComplex_isZero_homology_zero (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (h : Function.Surjective (algebraMap A B)) :
    IsZero ((cotangentComplex A B).homology 0) := by
  have := KaehlerDifferential.subsingleton_of_surjective A B h
  exact (ModuleCat.isZero_of_subsingleton
    (ModuleCat.of B (KaehlerDifferential A B))).of_iso (cotangentComplex_homologyZeroIso A B)

section Surjective

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)
  (h : Function.Surjective (algebraMap A B))

/-- The `n`-th term of the standard resolution, viewed as a presentation of `B` over `A`. It is a
presentation because the augmentation is surjective, which for a surjective `A → B` already holds
on the image of `A`. -/
public noncomputable def resolutionExtension (n : SimplexCategoryᵒᵖ) :
    Algebra.Extension.{max u v} A B :=
  Algebra.Extension.ofSurjective ((standardResolution A B).hom.app n).hom (by
    intro b
    obtain ⟨a, rfl⟩ := h b
    exact ⟨algebraMap A _ a, AlgHom.commutes _ a⟩)

/-- The cotangent space of the presentation `Pₙ → B` is the `n`-th term of the cotangent
simplicial module. -/
public theorem resolutionExtension_cotangentSpace (n : SimplexCategoryᵒᵖ) :
    ModuleCat.of B (resolutionExtension A B h n).CotangentSpace = cotangentTerm A B n := rfl

/-- The morphism of presentations attached to a simplicial operator. -/
public noncomputable def resolutionExtensionHom {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) :
    (resolutionExtension A B h i).Hom (resolutionExtension A B h j) :=
  Algebra.Extension.Hom.ofAlgHom ((standardResolution A B).left.map f).hom <|
    AlgHom.ext fun p => RingHom.congr_fun (standardResolutionAugmentationHom_naturality A B f) p

@[simp]
public theorem resolutionExtensionHom_toAlgHom {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j)
    (p : (standardResolution A B).left.obj i) :
    (resolutionExtensionHom A B h f).toAlgHom p = (standardResolution A B).left.map f p := rfl

public theorem resolutionExtensionHom_id (i : SimplexCategoryᵒᵖ) :
    resolutionExtensionHom A B h (𝟙 i) = Algebra.Extension.Hom.id _ := by
  apply Algebra.Extension.Hom.ext
  apply RingHom.ext
  intro p
  show ((standardResolution A B).left.map (𝟙 i)) p = p
  rw [CategoryTheory.Functor.map_id]
  rfl

public theorem resolutionExtensionHom_comp {i j k : SimplexCategoryᵒᵖ} (f : i ⟶ j) (g : j ⟶ k) :
    resolutionExtensionHom A B h (f ≫ g) =
      (resolutionExtensionHom A B h g).comp (resolutionExtensionHom A B h f) := by
  apply Algebra.Extension.Hom.ext
  apply RingHom.ext
  intro p
  show ((standardResolution A B).left.map (f ≫ g)) p =
    ((standardResolution A B).left.map g) (((standardResolution A B).left.map f) p)
  rw [CategoryTheory.Functor.map_comp]
  rfl

/-- The simplicial conormal module `J•/J•²` of the standard resolution, where
`Jₙ = ker(Pₙ → B)`. -/
@[reducible] public noncomputable def conormalSimplicialModule :
    SimplicialObject (ModuleCat.{max u v} B) where
  obj n := ModuleCat.of B (resolutionExtension A B h n).Cotangent
  map f := ModuleCat.ofHom (Algebra.Extension.Cotangent.map (resolutionExtensionHom A B h f))
  map_id i := by
    rw [resolutionExtensionHom_id, Algebra.Extension.Cotangent.map_id]
    rfl
  map_comp f g := by
    rw [resolutionExtensionHom_comp, Algebra.Extension.Cotangent.map_comp]
    rfl

/-- The map `J/J² → B ⊗[Pₙ] Ω[Pₙ⁄A]` of the presentation `Pₙ → B`, in simplicial degree `n`. -/
public noncomputable def conormalToCotangentApp (n : SimplexCategoryᵒᵖ) :
    ModuleCat.of B (resolutionExtension A B h n).Cotangent ⟶ cotangentTerm A B n :=
  ModuleCat.ofHom (Y := cotangentTerm A B n) (resolutionExtension A B h n).cotangentComplex

/-- The conormal class of `y` maps to the pure differential `1 ⊗ d y`. -/
public theorem conormalToCotangentApp_mk (n : SimplexCategoryᵒᵖ)
    (y : (resolutionExtension A B h n).ker) :
    conormalToCotangentApp A B h n (Algebra.Extension.Cotangent.mk y) =
      cotangentTermDifferential A B n y.1 := rfl

/-- The map from the simplicial conormal module to the cotangent simplicial module. -/
public noncomputable def conormalToCotangent :
    conormalSimplicialModule A B h ⟶ (cotangentSimplicialModule A B).object where
  app n := conormalToCotangentApp A B h n
  naturality {i j} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
    change conormalToCotangentApp A B h j
        (Algebra.Extension.Cotangent.map (resolutionExtensionHom A B h f)
          (Algebra.Extension.Cotangent.mk y)) =
      cotangentMap A B f (conormalToCotangentApp A B h i (Algebra.Extension.Cotangent.mk y))
    exact (cotangentMap_D A B f y.1).symm

/-! ### The presentation of `B` by `A` itself -/

/-- The presentation of `B` by `A` itself, available because `A → B` is surjective, with the
source universe-lifted so that it lives in the universe of the standard resolution. Its conormal
module is `I/I²` for `I = ker(A → B)`. -/
public noncomputable def surjectionExtension : Algebra.Extension.{max u v} A B :=
  Algebra.Extension.ofSurjective
    ((Algebra.ofId A B).comp (ULift.algEquiv (R := A) (A := A)).toAlgHom) (by
      intro b
      obtain ⟨a, ha⟩ := h b
      exact ⟨ULift.up a, by simpa using ha⟩)

public theorem surjectionExtension_algebraMap_surjective :
    Function.Surjective (algebraMap A (surjectionExtension A B h).Ring) :=
  fun a => ⟨a.down, rfl⟩

/-- Since `Ω[A⁄A] = 0`, the conormal module of the presentation `A → B` is the whole of its first
cotangent homology. -/
public noncomputable def surjectionH1CotangentEquiv :
    (surjectionExtension A B h).H1Cotangent ≃ₗ[B] (surjectionExtension A B h).Cotangent :=
  Algebra.Extension.h1CotangentEquivOfSurjective _
    (surjectionExtension_algebraMap_surjective A B h)

/-- The kernel of the presentation `A → B` is the kernel `I` of `A → B`, transported along the
universe lift; so its conormal module is `I/I²`. -/
public noncomputable def surjectionKerCotangentEquiv :
    (surjectionExtension A B h).ker.Cotangent ≃ₗ[A]
      (RingHom.ker (algebraMap A B)).Cotangent :=
  LinearEquiv.ofLinearMap
    (Ideal.mapCotangent _ _ (ULift.algEquiv (R := A) (A := A)).toAlgHom fun _ hx => hx)
    (Ideal.mapCotangent _ _ (ULift.algEquiv (R := A) (A := A)).symm.toAlgHom fun _ hx => hx)
    (by
      apply LinearMap.ext
      intro x
      obtain ⟨y, rfl⟩ := (RingHom.ker (algebraMap A B)).toCotangent_surjective x
      rfl)
    (by
      apply LinearMap.ext
      intro x
      obtain ⟨y, rfl⟩ := (surjectionExtension A B h).ker.toCotangent_surjective x
      rfl)

/-- The canonical morphism from the presentation `A → B` to the `n`-th term of the standard
resolution. -/
public noncomputable def surjectionToResolution (n : SimplexCategoryᵒᵖ) :
    (surjectionExtension A B h).Hom (resolutionExtension A B h n) :=
  Algebra.Extension.Hom.ofAlgHom
    ((Algebra.ofId A ((standardResolution A B).left.obj n)).comp
      (ULift.algEquiv (R := A) (A := A)).toAlgHom) <|
    AlgHom.ext fun x => by
      rw [show x = algebraMap A (surjectionExtension A B h).Ring x.down from rfl,
        AlgHom.commutes, AlgHom.commutes]

/-- Comparing the presentation `A → B` with a term of the standard resolution is an isomorphism
on first cotangent homology: the terms of the standard resolution are polynomial algebras, so
they receive a morphism from, and map to, every presentation. -/
public theorem bijective_h1Cotangent_map_surjectionToResolution (n : SimplexCategoryᵒᵖ) :
    Function.Bijective
      (Algebra.Extension.H1Cotangent.map (surjectionToResolution A B h n)) := by
  obtain ⟨ι, ⟨e⟩⟩ := standardResolution_obj_isPolynomialAlgebra A B n
  set P := resolutionExtension A B h n with hP
  set E := surjectionExtension A B h with hE
  have hrev : P.Hom E := Algebra.Extension.Hom.ofAlgHom
    ((MvPolynomial.aeval
        (fun i => E.σ (algebraMap P.Ring B (e (MvPolynomial.X i))))).comp
      e.symm.toAlgHom) (by
        have hh : ((IsScalarTower.toAlgHom A E.Ring B).comp
              ((MvPolynomial.aeval
                  (fun i => E.σ (algebraMap P.Ring B (e (MvPolynomial.X i))))).comp
                e.symm.toAlgHom)).comp e.toAlgHom =
            ((IsScalarTower.toAlgHom A B B).comp
              (IsScalarTower.toAlgHom A P.Ring B)).comp e.toAlgHom := by
          ext i
          simp [Algebra.Extension.algebraMap_σ]
          rfl
        apply AlgHom.ext
        intro p
        obtain ⟨q, rfl⟩ := e.surjective p
        exact AlgHom.congr_fun hh q)
  exact (Algebra.Extension.H1Cotangent.equiv (surjectionToResolution A B h n) hrev).bijective

/-! ### The degreewise short exact sequence `0 → I/I² → J/J² → Ω ⊗ B → 0` -/

/-- Since `Ω[B⁄A] = 0`, the conormal module of each presentation `Pₙ → B` surjects onto the
base-changed differentials. -/
public theorem surjective_resolutionExtension_cotangentComplex (n : SimplexCategoryᵒᵖ) :
    Function.Surjective (resolutionExtension A B h n).cotangentComplex := by
  have := KaehlerDifferential.subsingleton_of_surjective A B h
  intro x
  exact ((resolutionExtension A B h n).exact_cotangentComplex_toKaehler x).mp
    (Subsingleton.elim _ _)

/-- The inclusion of the constant simplicial module `I/I²` as the kernel of the simplicial
conormal module. In simplicial degree `n` it is the comparison with the presentation `A → B`
followed by the inclusion of the first cotangent homology. -/
public noncomputable def conormalKernelInclusion :
    (Functor.const SimplexCategoryᵒᵖ).obj
        (ModuleCat.of B (surjectionExtension A B h).Cotangent) ⟶
      conormalSimplicialModule A B h where
  app n := ModuleCat.ofHom
    ((resolutionExtension A B h n).h1Cotangentι.comp
      (((Algebra.Extension.H1Cotangent.map (surjectionToResolution A B h n)).comp
        (surjectionH1CotangentEquiv A B h).symm.toLinearMap)))
  naturality {i j} φ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    set u := (surjectionH1CotangentEquiv A B h).symm x with hu
    change (resolutionExtension A B h j).h1Cotangentι
        (Algebra.Extension.H1Cotangent.map (surjectionToResolution A B h j) u) =
      Algebra.Extension.Cotangent.map (resolutionExtensionHom A B h φ)
        ((resolutionExtension A B h i).h1Cotangentι
          (Algebra.Extension.H1Cotangent.map (surjectionToResolution A B h i) u))
    have key := LinearMap.congr_fun
      (Algebra.Extension.Cotangent.map_comp_h1Cotangentι (resolutionExtensionHom A B h φ))
      (Algebra.Extension.H1Cotangent.map (surjectionToResolution A B h i) u)
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars] at key
    rw [key, ← Algebra.Extension.H1Cotangent.map_comp_apply,
      Algebra.Extension.H1Cotangent.map_eq
        ((resolutionExtensionHom A B h φ).comp (surjectionToResolution A B h i))
        (surjectionToResolution A B h j)]

/-- The short complex of simplicial `B`-modules `I/I² → J•/J•² → Ω[P•⁄A] ⊗[P•] B`, whose short
exactness is the local statement in the Stacks proof of Tag 08RA. -/
public noncomputable def conormalShortComplex :
    ShortComplex (SimplicialObject (ModuleCat.{max u v} B)) :=
  ShortComplex.mk (conormalKernelInclusion A B h) (conormalToCotangent A B h) (by
    apply NatTrans.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (resolutionExtension A B h n).cotangentComplex
        ((resolutionExtension A B h n).h1Cotangentι
          (Algebra.Extension.H1Cotangent.map (surjectionToResolution A B h n)
            ((surjectionH1CotangentEquiv A B h).symm x))) = 0
    exact ((Algebra.Extension.H1Cotangent.map (surjectionToResolution A B h n))
      ((surjectionH1CotangentEquiv A B h).symm x)).2)

/-- The inclusion of `I/I²` in the conormal module is injective in each simplicial degree. -/
public theorem mono_conormalKernelInclusion_app (n : SimplexCategoryᵒᵖ) :
    Mono ((conormalKernelInclusion A B h).app n) :=
  (ModuleCat.mono_iff_injective _).2 fun _ _ hxy =>
    (surjectionH1CotangentEquiv A B h).symm.injective
      ((bijective_h1Cotangent_map_surjectionToResolution A B h n).1 (Subtype.ext hxy))

/-- The conormal module surjects onto the base-changed differentials in each simplicial
degree. -/
public theorem epi_conormalToCotangent_app (n : SimplexCategoryᵒᵖ) :
    Epi ((conormalToCotangent A B h).app n) :=
  (ModuleCat.epi_iff_surjective (conormalToCotangentApp A B h n)).2
    (surjective_resolutionExtension_cotangentComplex A B h n)

/-- In each simplicial degree the kernel of `J/J² → Ω[Pₙ⁄A] ⊗[Pₙ] B` is exactly the image of
`I/I²`. -/
public theorem range_conormalKernelInclusion_app (n : SimplexCategoryᵒᵖ)
    (x : (resolutionExtension A B h n).Cotangent)
    (hx : (resolutionExtension A B h n).cotangentComplex x = 0) :
    ∃ y, (conormalKernelInclusion A B h).app n y = x := by
  obtain ⟨y, hy⟩ := (bijective_h1Cotangent_map_surjectionToResolution A B h n).2 ⟨x, hx⟩
  exact ⟨surjectionH1CotangentEquiv A B h y, by
    show ((Algebra.Extension.H1Cotangent.map (surjectionToResolution A B h n))
      ((surjectionH1CotangentEquiv A B h).symm
        (surjectionH1CotangentEquiv A B h y))).1 = x
    rw [LinearEquiv.symm_apply_apply]
    exact congrArg Subtype.val hy⟩

/-- **The local statement in the Stacks proof of Tag 08RA.** Because `A → B` is surjective, the
sequence `0 → I/I² → J/J² → Ω[Pₙ⁄A] ⊗[Pₙ] B → 0` is exact for every term of the standard
resolution. -/
public theorem conormalShortComplex_shortExact_app (n : SimplexCategoryᵒᵖ) :
    ((conormalShortComplex A B h).map
      ((evaluation SimplexCategoryᵒᵖ (ModuleCat.{max u v} B)).obj n)).ShortExact where
  exact := by
    refine (ShortComplex.moduleCat_exact_iff _).2 ?_
    exact fun x hx => range_conormalKernelInclusion_app A B h n x hx
  mono_f := mono_conormalKernelInclusion_app A B h n
  epi_g := epi_conormalToCotangent_app A B h n

/-- The short complex of cochain complexes of `B`-modules obtained from the conormal short
complex; its third term is the cotangent complex `L_{B/A}`. -/
public noncomputable def conormalCochainComplexes :
    ShortComplex (CochainComplex (ModuleCat.{max u v} B) ℤ) :=
  (conormalShortComplex A B h).map
    (AlgebraicTopology.alternatingFaceMapCochainComplex (ModuleCat.{max u v} B))

/-- The third term of the conormal short complex of cochain complexes is `L_{B/A}`. -/
public theorem conormalCochainComplexes_X₃ :
    (conormalCochainComplexes A B h).X₃ = cotangentComplex A B := rfl

/-- The conormal short complex of cochain complexes is short exact. -/
public theorem conormalCochainComplexes_shortExact :
    (conormalCochainComplexes A B h).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  by_cases hi : ∃ n : ℕ, (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = i
  · obtain ⟨n, rfl⟩ := hi
    rw [conormalCochainComplexes, ← ShortComplex.map_comp]
    refine (ShortComplex.shortExact_iff_of_iso ((conormalShortComplex A B h).mapNatIso
      (AlgebraicTopology.alternatingFaceMapCochainComplexCompEvalIso
        (ModuleCat.{max u v} B) n))).2 ?_
    exact conormalShortComplex_shortExact_app A B h (op ⦋n⦌)
  · refine (ShortComplex.Splitting.ofIsZero _ ?_ ?_ ?_).shortExact
    all_goals exact HomologicalComplex.isZero_extend_X _ _ i (by tauto)

/-! ### Vanishing of the homotopy of the conormal module in degrees `0` and `1` -/

/-- The Moore complex of the simplicial conormal module. -/
public noncomputable abbrev conormalMooreComplex : ChainComplex (ModuleCat.{max u v} B) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} B)).obj
    (conormalSimplicialModule A B h)

/-- The augmentation is compatible with every face map. -/
public theorem standardResolution_augmentation_δ (n : ℕ) (i : Fin (n + 2))
    (p : (standardResolution A B).left.obj (op ⦋n + 1⦌)) :
    (standardResolution A B).hom.app (op ⦋n⦌) ((standardResolution A B).left.δ i p) =
      (standardResolution A B).hom.app (op ⦋n + 1⦌) p := by
  have hnat : (standardResolution A B).left.δ i ≫ (standardResolution A B).hom.app (op ⦋n⦌) =
      (standardResolution A B).hom.app (op ⦋n + 1⦌) :=
    (standardResolution A B).hom.naturality (SimplexCategory.δ i).op
  rw [← hnat, CommAlgCat.comp_apply]

/-- The augmentation ideal `Jₙ = ker(Pₙ → B)` of the `n`-th term of the standard resolution. -/
public noncomputable def augmentationIdeal (n : SimplexCategoryᵒᵖ) :
    Ideal ((standardResolution A B).left.obj n) :=
  RingHom.ker ((standardResolution A B).hom.app n).hom.toRingHom

public theorem mem_augmentationIdeal_iff (n : SimplexCategoryᵒᵖ)
    (p : (standardResolution A B).left.obj n) :
    p ∈ augmentationIdeal A B n ↔ (standardResolution A B).hom.app n p = 0 := Iff.rfl

/-- The kernel of the presentation `Pₙ → B` is the augmentation ideal. -/
public theorem resolutionExtension_ker (n : SimplexCategoryᵒᵖ) :
    (resolutionExtension A B h n).ker = augmentationIdeal A B n := rfl

/-- A face map preserves the augmentation ideal. -/
public theorem delta_mem_augmentationIdeal (n : ℕ) (i : Fin (n + 2))
    (p : (standardResolution A B).left.obj (op ⦋n + 1⦌))
    (hp : p ∈ augmentationIdeal A B (op ⦋n + 1⦌)) :
    (standardResolution A B).left.δ i p ∈ augmentationIdeal A B (op ⦋n⦌) :=
  (standardResolution_augmentation_δ A B n i p).trans hp

/-- The first differential of the Moore complex is the difference of the two faces. -/
public theorem conormalMooreComplex_d_one_zero :
    (conormalMooreComplex A B h).d 1 0 =
      (conormalSimplicialModule A B h).δ (0 : Fin 2) -
        (conormalSimplicialModule A B h).δ (1 : Fin 2) := by
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, Fin.sum_univ_two, sub_eq_add_neg]
  simp

/-- The second differential of the Moore complex is the alternating sum of the three faces. -/
public theorem conormalMooreComplex_d_two_one :
    (conormalMooreComplex A B h).d 2 1 =
      (conormalSimplicialModule A B h).δ (0 : Fin 3) -
        (conormalSimplicialModule A B h).δ (1 : Fin 3) +
        (conormalSimplicialModule A B h).δ (2 : Fin 3) := by
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, Fin.sum_univ_three, sub_eq_add_neg]
  simp

/-- The value of a face map of the simplicial conormal module on a conormal class: it is the
class of the image, whichever representative of that image is supplied. -/
public theorem conormalSimplicialModule_map_mk {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j)
    (y : (resolutionExtension A B h i).ker) (z : (resolutionExtension A B h j).ker)
    (hz : (z : (resolutionExtension A B h j).Ring) =
      (resolutionExtensionHom A B h f).toAlgHom (y : (resolutionExtension A B h i).Ring)) :
    (conormalSimplicialModule A B h).map f (Algebra.Extension.Cotangent.mk y) =
      Algebra.Extension.Cotangent.mk z := by
  show Algebra.Extension.Cotangent.map (resolutionExtensionHom A B h f)
    (Algebra.Extension.Cotangent.mk y) = _
  rw [Algebra.Extension.Cotangent.map_mk]
  congr 1
  exact Subtype.ext hz.symm

/-- The value of a face map of the simplicial conormal module on a conormal class. -/
public theorem conormalSimplicialModule_delta_mk (n : ℕ) (i : Fin (n + 2))
    (y : (resolutionExtension A B h (op ⦋n + 1⦌)).ker)
    (z : (resolutionExtension A B h (op ⦋n⦌)).ker)
    (hz : z.1 = (standardResolution A B).left.δ i y.1) :
    (conormalSimplicialModule A B h).δ i (Algebra.Extension.Cotangent.mk y) =
      Algebra.Extension.Cotangent.mk z :=
  conormalSimplicialModule_map_mk A B h (SimplexCategory.δ i).op y z hz

/-- For `p` in the augmentation ideal, the faces of `[p] - [0]` are `p` and `0`. -/
private theorem delta_varOne_sub_eq (p : (standardResolution A B).left.obj (op ⦋0⦌))
    (hp : p ∈ augmentationIdeal A B (op ⦋0⦌)) :
    (standardResolution A B).left.δ (0 : Fin 2)
        (standardResolutionVarOne A B p - standardResolutionVarOne A B 0) = p ∧
      (standardResolution A B).left.δ (1 : Fin 2)
        (standardResolutionVarOne A B p - standardResolutionVarOne A B 0) = 0 := by
  simp [(mem_augmentationIdeal_iff A B _ p).1 hp]

/-- If `p` lies in the augmentation ideal, so does the degree-one element `[p] - [0]`. -/
public theorem varOne_sub_mem_augmentationIdeal (p : (standardResolution A B).left.obj (op ⦋0⦌))
    (hp : p ∈ augmentationIdeal A B (op ⦋0⦌)) :
    standardResolutionVarOne A B p - standardResolutionVarOne A B 0 ∈
      augmentationIdeal A B (op ⦋1⦌) := by
  show (standardResolution A B).hom.app (op ⦋1⦌) _ = 0
  rw [← standardResolution_augmentation_δ A B 0 (0 : Fin 2), (delta_varOne_sub_eq A B p hp).1]
  exact hp

/-- The boundary of `[p] - [0]` is `p`, for `p` in the augmentation ideal. This is the
computation behind the vanishing of `H₀` of the conormal module. -/
public theorem delta_varOne_sub (p : (standardResolution A B).left.obj (op ⦋0⦌))
    (hp : p ∈ augmentationIdeal A B (op ⦋0⦌)) :
    (standardResolution A B).left.δ (0 : Fin 2)
        (standardResolutionVarOne A B p - standardResolutionVarOne A B 0) -
      (standardResolution A B).left.δ (1 : Fin 2)
        (standardResolutionVarOne A B p - standardResolutionVarOne A B 0) = p := by
  rw [(delta_varOne_sub_eq A B p hp).1, (delta_varOne_sub_eq A B p hp).2, sub_zero]

/-- The alternating sum of the two faces, computed on conormal classes. -/
public theorem conormalDelta_sub_mk (w : (resolutionExtension A B h (op ⦋0 + 1⦌)).ker)
    (z₀ z₁ z : (resolutionExtension A B h (op ⦋0⦌)).ker)
    (h₀ : z₀.1 = (standardResolution A B).left.δ (0 : Fin 2) w.1)
    (h₁ : z₁.1 = (standardResolution A B).left.δ (1 : Fin 2) w.1)
    (hz : z.1 = z₀.1 - z₁.1) :
    (conormalSimplicialModule A B h).δ (0 : Fin 2) (Algebra.Extension.Cotangent.mk w) -
        (conormalSimplicialModule A B h).δ (1 : Fin 2) (Algebra.Extension.Cotangent.mk w) =
      Algebra.Extension.Cotangent.mk z := by
  rw [conormalSimplicialModule_delta_mk A B h 0 (0 : Fin 2) w z₀ h₀,
    conormalSimplicialModule_delta_mk A B h 0 (1 : Fin 2) w z₁ h₁, ← map_sub]
  congr 1
  exact Subtype.ext hz.symm

/-- The alternating sum of the three faces, computed on conormal classes. -/
public theorem conormalDelta_alt_mk (w : (resolutionExtension A B h (op ⦋1 + 1⦌)).ker)
    (z₀ z₁ z₂ z : (resolutionExtension A B h (op ⦋1⦌)).ker)
    (h₀ : z₀.1 = (standardResolution A B).left.δ (0 : Fin 3) w.1)
    (h₁ : z₁.1 = (standardResolution A B).left.δ (1 : Fin 3) w.1)
    (h₂ : z₂.1 = (standardResolution A B).left.δ (2 : Fin 3) w.1)
    (hz : z.1 = z₀.1 - z₁.1 + z₂.1) :
    (conormalSimplicialModule A B h).δ (0 : Fin 3) (Algebra.Extension.Cotangent.mk w) -
        (conormalSimplicialModule A B h).δ (1 : Fin 3) (Algebra.Extension.Cotangent.mk w) +
        (conormalSimplicialModule A B h).δ (2 : Fin 3) (Algebra.Extension.Cotangent.mk w) =
      Algebra.Extension.Cotangent.mk z := by
  rw [conormalSimplicialModule_delta_mk A B h 1 (0 : Fin 3) w z₀ h₀,
    conormalSimplicialModule_delta_mk A B h 1 (1 : Fin 3) w z₁ h₁,
    conormalSimplicialModule_delta_mk A B h 1 (2 : Fin 3) w z₂ h₂, ← map_sub, ← map_add]
  congr 1
  exact Subtype.ext hz.symm

/-- **The square of the augmentation ideal consists of boundaries.** Every element of `J₀²` is
`δ₀ w - δ₁ w` for some `w` in `J₁²`. -/
public theorem exists_sq_of_mem_sq (z : (standardResolution A B).left.obj (op ⦋0⦌))
    (hz : z ∈ augmentationIdeal A B (op ⦋0⦌) ^ 2) :
    ∃ w : (standardResolution A B).left.obj (op ⦋1⦌),
      w ∈ augmentationIdeal A B (op ⦋1⦌) ^ 2 ∧
        (standardResolution A B).left.δ (0 : Fin 2) w -
          (standardResolution A B).left.δ (1 : Fin 2) w = z := by
  rw [pow_two] at hz
  refine Submodule.mul_induction_on hz ?_ ?_
  · intro a ha b hb
    refine ⟨(standardResolutionVarOne A B a - standardResolutionVarOne A B 0) *
      (standardResolutionVarOne A B b - standardResolutionVarOne A B 0), ?_, ?_⟩
    · rw [pow_two]
      exact Ideal.mul_mem_mul (varOne_sub_mem_augmentationIdeal A B a ha)
        (varOne_sub_mem_augmentationIdeal A B b hb)
    · rw [map_mul, map_mul, (delta_varOne_sub_eq A B a ha).1, (delta_varOne_sub_eq A B a ha).2,
        (delta_varOne_sub_eq A B b hb).1, (delta_varOne_sub_eq A B b hb).2]
      ring
  · rintro x y ⟨wx, hwx, hx⟩ ⟨wy, hwy, hy⟩
    refine ⟨wx + wy, Ideal.add_mem _ hwx hwy, ?_⟩
    rw [map_add, map_add, ← hx, ← hy]
    ring

/-! ### The two vanishing theorems -/

/-- **`H₀` of the simplicial conormal module vanishes.** Every conormal class in degree zero is
the boundary of the class of `[p] - [0]`. -/
public theorem surjective_conormalMooreComplex_d_one_zero :
    Function.Surjective ((conormalMooreComplex A B h).d 1 0) := by
  rw [conormalMooreComplex_d_one_zero]
  intro c
  obtain ⟨y, hy⟩ := Algebra.Extension.Cotangent.mk_surjective c
  have hw := varOne_sub_mem_augmentationIdeal A B y.1 y.2
  refine ⟨Algebra.Extension.Cotangent.mk ⟨standardResolutionVarOne A B y.1 -
    standardResolutionVarOne A B 0, hw⟩, ?_⟩
  rw [← hy]
  exact conormalDelta_sub_mk A B h ⟨_, hw⟩
    ⟨_, delta_mem_augmentationIdeal A B 0 (0 : Fin 2) _ hw⟩
    ⟨_, delta_mem_augmentationIdeal A B 0 (1 : Fin 2) _ hw⟩ y rfl rfl
    (delta_varOne_sub A B y.1 y.2).symm

/-- The degree-zero homology of the Moore complex of the simplicial conormal module vanishes. -/
public theorem isZero_conormalMooreComplex_homology_zero :
    IsZero ((conormalMooreComplex A B h).homology 0) := by
  have hepi : Epi ((conormalMooreComplex A B h).d 1 0) :=
    (ModuleCat.epi_iff_surjective _).2 (surjective_conormalMooreComplex_d_one_zero A B h)
  refine IsZero.of_iso ?_ (conormalMooreComplex A B h).isoHomologyι₀
  rw [IsZero.iff_id_eq_zero]
  have hp : (conormalMooreComplex A B h).pOpcycles 0 = 0 := by
    rw [← cancel_epi ((conormalMooreComplex A B h).d 1 0), Limits.comp_zero]
    exact (conormalMooreComplex A B h).d_pOpcycles 1 0
  rw [← cancel_epi ((conormalMooreComplex A B h).pOpcycles 0), Category.comp_id,
    Limits.comp_zero, hp]

/-- A `2`-simplex of the standard resolution whose alternating face sum lies in the augmentation
ideal lies in the augmentation ideal itself. -/
public theorem mem_augmentationIdeal_of_alternating_delta_mem
    (y : (standardResolution A B).left.obj (op ⦋2⦌))
    {q : (standardResolution A B).left.obj (op ⦋1⦌)}
    (hy : (standardResolution A B).left.δ (0 : Fin 3) y
        - (standardResolution A B).left.δ (1 : Fin 3) y
        + (standardResolution A B).left.δ (2 : Fin 3) y = q)
    (hq : q ∈ augmentationIdeal A B (op ⦋1⦌)) : y ∈ augmentationIdeal A B (op ⦋2⦌) := by
  have key : (standardResolution A B).hom.app (op ⦋1⦌)
      ((standardResolution A B).left.δ (0 : Fin 3) y -
        (standardResolution A B).left.δ (1 : Fin 3) y +
        (standardResolution A B).left.δ (2 : Fin 3) y) =
      (standardResolution A B).hom.app (op ⦋2⦌) y := by
    rw [map_add, map_sub, standardResolution_augmentation_δ A B 1 (0 : Fin 3) y,
      standardResolution_augmentation_δ A B 1 (1 : Fin 3) y,
      standardResolution_augmentation_δ A B 1 (2 : Fin 3) y]
    ring
  rw [hy, show (standardResolution A B).hom.app (op ⦋1⦌) q = 0 from hq] at key
  exact key.symm

/-- **`H₁` of the simplicial conormal module vanishes.** A degree-one conormal cycle differs by
an element of `J₁²` from a cycle of the standard resolution, which is a boundary because the
standard resolution is a resolution; the correcting element is itself a boundary because `J₀²`
consists of boundaries. -/
public theorem exact_conormalDelta (c : (conormalSimplicialModule A B h).obj (op ⦋0 + 1⦌))
    (hc : ((conormalSimplicialModule A B h).δ (0 : Fin 2) -
      (conormalSimplicialModule A B h).δ (1 : Fin 2)) c = 0) :
    ∃ c' : (conormalSimplicialModule A B h).obj (op ⦋1 + 1⦌),
      ((conormalSimplicialModule A B h).δ (0 : Fin 3) -
        (conormalSimplicialModule A B h).δ (1 : Fin 3) +
        (conormalSimplicialModule A B h).δ (2 : Fin 3)) c' = c := by
  obtain ⟨w, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective c
  set p : (standardResolution A B).left.obj (op ⦋1⦌) := w.1 with hp
  have hpker : p ∈ augmentationIdeal A B (op ⦋1⦌) := w.2
  have hd₀ := delta_mem_augmentationIdeal A B 0 (0 : Fin 2) p hpker
  have hd₁ := delta_mem_augmentationIdeal A B 0 (1 : Fin 2) p hpker
  have hc1 : Algebra.Extension.Cotangent.mk (P := resolutionExtension A B h (op ⦋0⦌))
      ⟨(standardResolution A B).left.δ (0 : Fin 2) p -
        (standardResolution A B).left.δ (1 : Fin 2) p,
        Ideal.sub_mem _ hd₀ hd₁⟩ = 0 :=
    (conormalDelta_sub_mk A B h w ⟨_, hd₀⟩ ⟨_, hd₁⟩ ⟨_, Ideal.sub_mem _ hd₀ hd₁⟩
      rfl rfl rfl).symm.trans hc
  have hsq := (Algebra.Extension.Cotangent.mk_eq_zero_iff _).1 hc1
  obtain ⟨v, hvmem, hv⟩ := exists_sq_of_mem_sq A B _ hsq
  have hvker : v ∈ augmentationIdeal A B (op ⦋1⦌) := Ideal.pow_le_self two_ne_zero hvmem
  have hv' : (standardResolution A B).left.δ (0 : Fin 2) v -
      (standardResolution A B).left.δ (1 : Fin 2) v =
      (standardResolution A B).left.δ (0 : Fin 2) p -
        (standardResolution A B).left.δ (1 : Fin 2) p := hv
  have hcycle : (standardResolution A B).left.δ (0 : Fin 2) (p - v) -
      (standardResolution A B).left.δ (1 : Fin 2) (p - v) = 0 := by
    rw [map_sub, map_sub, sub_sub_sub_comm, hv', sub_self]
  obtain ⟨y, hy⟩ := standardResolution_exists_of_delta_sub_delta_eq_zero A B (p - v) hcycle
  have hyker := mem_augmentationIdeal_of_alternating_delta_mem A B y hy
    (Ideal.sub_mem _ hpker hvker)
  have he₀ := delta_mem_augmentationIdeal A B 1 (0 : Fin 3) y hyker
  have he₁ := delta_mem_augmentationIdeal A B 1 (1 : Fin 3) y hyker
  have he₂ := delta_mem_augmentationIdeal A B 1 (2 : Fin 3) y hyker
  have hvzero : Algebra.Extension.Cotangent.mk
      (P := resolutionExtension A B h (op ⦋1⦌)) ⟨v, hvker⟩ = 0 :=
    (Algebra.Extension.Cotangent.mk_eq_zero_iff _).2 hvmem
  refine ⟨Algebra.Extension.Cotangent.mk ⟨y, hyker⟩, ?_⟩
  have halt := conormalDelta_alt_mk A B h ⟨y, hyker⟩ ⟨_, he₀⟩ ⟨_, he₁⟩ ⟨_, he₂⟩
    ⟨p - v, Ideal.sub_mem _ hpker hvker⟩ rfl rfl rfl hy.symm
  rw [show (⟨p - v, Ideal.sub_mem _ hpker hvker⟩ :
      (resolutionExtension A B h (op ⦋1⦌)).ker) = w - ⟨v, hvker⟩ from Subtype.ext rfl,
    map_sub, hvzero, sub_zero] at halt
  exact halt

/-- The Moore complex of the simplicial conormal module is exact in degree one. -/
public theorem exactAt_conormalMooreComplex_one :
    (conormalMooreComplex A B h).ExactAt 1 := by
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  have hg : (HomologicalComplex.sc' (conormalMooreComplex A B h) 2 1 0).g =
      (conormalSimplicialModule A B h).δ (0 : Fin 2) -
        (conormalSimplicialModule A B h).δ (1 : Fin 2) :=
    conormalMooreComplex_d_one_zero A B h
  have hf : (HomologicalComplex.sc' (conormalMooreComplex A B h) 2 1 0).f =
      (conormalSimplicialModule A B h).δ (0 : Fin 3) -
        (conormalSimplicialModule A B h).δ (1 : Fin 3) +
        (conormalSimplicialModule A B h).δ (2 : Fin 3) :=
    conormalMooreComplex_d_two_one A B h
  rw [hg, hf]
  exact fun c hc => exact_conormalDelta A B h c hc

/-- The degree-one homology of the Moore complex of the simplicial conormal module vanishes. -/
public theorem isZero_conormalMooreComplex_homology_one :
    IsZero ((conormalMooreComplex A B h).homology 1) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (exactAt_conormalMooreComplex_one A B h)

/-! ### The degree `-1` homology of the cotangent complex -/

/-- The middle term of the conormal short complex of cochain complexes has no homology in
cohomological degree `0`. -/
public theorem isZero_conormalCochainComplexes_homology_zero :
    IsZero ((conormalCochainComplexes A B h).X₂.homology 0) :=
  (isZero_conormalMooreComplex_homology_zero A B h).of_iso
    (HomologicalComplex.extendHomologyIso (conormalMooreComplex A B h)
      (ComplexShape.embeddingUpIntLE 0) (j := 0) (j' := 0) (by simp))

/-- The middle term of the conormal short complex of cochain complexes has no homology in
cohomological degree `-1`. -/
public theorem isZero_conormalCochainComplexes_homology_negOne :
    IsZero ((conormalCochainComplexes A B h).X₂.homology (-1)) :=
  (isZero_conormalMooreComplex_homology_one A B h).of_iso
    (HomologicalComplex.extendHomologyIso (conormalMooreComplex A B h)
      (ComplexShape.embeddingUpIntLE 0) (j := 1) (j' := -1) (by simp))

/-- The degree-zero homology of the constant cochain complex on `I/I²` is `I/I²`. -/
public noncomputable def conormalCochainComplexes_homologyZeroIso :
    (conormalCochainComplexes A B h).X₁.homology 0 ≅
      ModuleCat.of B (surjectionExtension A B h).Cotangent :=
  HomologicalComplex.extendHomologyIso
      ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} B)).obj
        ((Functor.const SimplexCategoryᵒᵖ).obj
          (ModuleCat.of B (surjectionExtension A B h).Cotangent)))
      (ComplexShape.embeddingUpIntLE 0) (j := 0) (j' := 0) (by simp) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} B) (ComplexShape.down ℕ) 0).mapIso
      (AlgebraicTopology.alternatingFaceMapComplexConst.app
        (ModuleCat.of B (surjectionExtension A B h).Cotangent)) ≪≫
    ChainComplex.alternatingConstHomologyZero _

/-- **Stacks Project, Tag 08RA.** For a surjective ring map `A → B` with kernel `I`, the
degree `-1` homology of the cotangent complex `L_{B/A}` is the conormal module `I/I²`. The
isomorphism is the connecting homomorphism of the short exact sequence
`0 → I/I² → J•/J•² → Ω[P•⁄A] ⊗[P•] B → 0` of simplicial modules, which is the sequence used in
the Stacks proof. -/
@[stacks 08RA "the degree-minus-one conclusion H⁻¹(L_{B/A}) = I/I², with I/I² the conormal
module of the presentation A → B, the isomorphism being the connecting homomorphism of the
short exact sequence 0 → I/I² → J•/J•² → Ω[P•⁄A] ⊗[P•] B → 0 of the Stacks proof"]
public noncomputable def cotangentComplex_homologyNegOneIso :
    (cotangentComplex A B).homology (-1) ≅
      ModuleCat.of B (surjectionExtension A B h).Cotangent :=
  (conormalCochainComplexes_shortExact A B h).δIso (-1) 0 (by simp)
      (isZero_conormalCochainComplexes_homology_negOne A B h)
      (isZero_conormalCochainComplexes_homology_zero A B h) ≪≫
    conormalCochainComplexes_homologyZeroIso A B h

end Surjective

end CommAlgCat

end
