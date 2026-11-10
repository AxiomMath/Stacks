module

public import StacksFrontier.AlgebraicGeometry.Cohomology.CountableExtAndTensor
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryModel
public import StacksFrontier.Homology.Perfect.ModelIndependence
public import Mathlib.LinearAlgebra.Countable

/-!
# Perfect complexes have countable sections of cohomology over countable affines

Let `X` be a scheme such that the ring of sections of `𝒪_X` over every affine open is countable,
and let `E` be a perfect object of `D(𝒪_X)`. Then every cohomology sheaf `H^i(E)` has a countable
set of sections over every affine open. This is the input of [Stacks, Tag 0CRQ] that the source
phrases as *"a perfect complex is locally isomorphic to a finite complex of finite free
`𝒪_X`-modules and therefore satisfies (2) by assumption on `X`"*.

## Main results

* `Stacks.Cohomology.CountableSections.countable_homology_of_isPerfect_ring`: over a countable
  ring, a perfect complex has countable cohomology modules.
* `Stacks.Cohomology.CountableSections.countable_sections_homology_of_isPerfect`: the
  statement above, for every model of the derived category.
* `Stacks.Cohomology.CountableSections.isPerfect_modelEquiv_functor_obj_iff`: perfectness of an
  object of `D(𝒪_X)` does not depend on the model of the derived category.

## The proof

Over an affine open `V`, the restriction of `E` is the sheafification of a perfect complex `P`
of `Γ(X, V)`-modules ([Stacks, Tags 06Z0, 08EB]); the cohomology sheaves of `E|_V` are then the
sheafifications of the cohomology modules of `P`, and the sections over `V` of a sheafification
`M^~` are `M`. A perfect complex is a bounded complex of finite projective modules, whose
cohomology modules are subquotients of finite modules over the countable ring `Γ(X, V)`, hence
countable.

## Implementation notes

The computation over an affine open is done at `HasDerivedCategory.standard`, the model of the
affine presentation `ComplexAndDivisorSituation.exists_isPerfect_presentation`; the statements
are made at an arbitrary model and carried to the standard one by the comparison equivalence
`StacksDraft.DerivedModel.modelEquiv`, which commutes with cohomology
(`StacksDraft.DerivedModel.modelHomologyFunctorIso`) and with perfectness.

## References

* [Stacks Project, Tag 0CRQ](https://stacks.math.columbia.edu/tag/0CRQ)
* [Stacks Project, Tag 0657](https://stacks.math.columbia.edu/tag/0657)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w z u

namespace Stacks.Cohomology.CountableSections

/-! ### Perfect complexes over a countable ring -/

/-- A module admitting a monomorphism into a countable module is countable. -/
private theorem countable_of_mono {R : Type u} [Ring R] {M N : ModuleCat.{u} R} (f : M ⟶ N)
    [Mono f] [Countable N] : Countable M :=
  Function.Injective.countable ((ModuleCat.mono_iff_injective f).1 inferInstance)

/-- **A perfect complex over a countable ring has countable cohomology.** It is isomorphic to a
bounded complex of finite projective modules, and the cohomology of such a complex is a
subquotient of a finite module, which is countable over a countable ring. -/
theorem countable_homology_of_isPerfect_ring {R : Type u} [Ring R] [Countable R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (K : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.Perfect.IsPerfect K) (i : ℤ) :
    Countable ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K) := by
  obtain ⟨P, a, b, -, -, hfin, -, ⟨e⟩⟩ := hK
  have : Module.Finite R (P.X i) := hfin i
  have hX : Countable (P.X i) := Finsupp.Countable.of_moduleFinite (R := R) (M := P.X i)
  have hcyc : Countable (P.cycles i) := countable_of_mono (P.iCycles i)
  have hhom : Countable (P.homology i) :=
    Function.Surjective.countable ((ModuleCat.epi_iff_surjective (P.homologyπ i)).1 inferInstance)
  let φ : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K ≅ P.homology i :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app P
  exact countable_of_mono φ.hom

/-! ### Transport between models -/

/-- **Perfectness does not depend on the model.** An object of `D(𝒪_X)` at one model is perfect
if and only if its image at another model under the comparison equivalence is. -/
theorem isPerfect_modelEquiv_functor_obj_iff {X : Scheme.{u}}
    (h₁ : HasDerivedCategory.{w} X.Modules) (h₂ : HasDerivedCategory.{z} X.Modules)
    (K : @DerivedCategory X.Modules _ _ h₁) :
    @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h₂
        ((StacksDraft.DerivedModel.modelEquiv h₁ h₂).functor.obj K) ↔
      @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h₁ K := by
  let C := (@DerivedCategory.Q X.Modules _ _ h₁).objPreimage K
  let e₁ : (@DerivedCategory.Q X.Modules _ _ h₁).obj C ≅ K :=
    (@DerivedCategory.Q X.Modules _ _ h₁).objObjPreimageIso K
  let e₂ : (@DerivedCategory.Q X.Modules _ _ h₂).obj C ≅
      (StacksDraft.DerivedModel.modelEquiv h₁ h₂).functor.obj K :=
    ((StacksDraft.DerivedModel.modelCompQIso h₁ h₂).app C).symm ≪≫
      (StacksDraft.DerivedModel.modelEquiv h₁ h₂).functor.mapIso e₁
  exact (Stacks.Cohomology.PerfectComplexes.isPerfect_iff_of_model h₁ h₂ e₁ e₂).symm

/-- Countability of the sections of a sheaf of modules passes along an isomorphism. -/
theorem countable_sections_of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (V : X.Opens)
    (h : Countable Γ(M, V)) : Countable Γ(N, V) :=
  Function.Injective.countable (f := (Scheme.Modules.Hom.app e.inv V).hom)
    ((AddCommGrpCat.mono_iff_injective _).1 inferInstance)

/-! ### The affine computation at the standard model -/

section Affine

variable {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)

/-- Sections over the whole affine scheme `V` of `(M^~)|_V` are `M`, so they are countable when
`M` is. -/
theorem countable_sections_tildeRestrict_of_countable (M : ModuleCat.{u} Γ(X, V))
    (h : Countable M) : Countable Γ((tilde.functor Γ(X, V) ⋙
      Scheme.Modules.restrictFunctor hV.isoSpec.hom).obj M, ⊤) := by
  have h' : Countable ((modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op ⊤)) :=
    countable_of_mono (tilde.isoTop M).inv
  change Countable Γ((tilde.functor Γ(X, V)).obj M, hV.isoSpec.hom ''ᵁ ⊤)
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  exact h'

include hV in
/-- The affine case at the standard model: a perfect `E` has countable sections of cohomology
over the affine open `V` when `Γ(X, V)` is countable. Over `V`, `E` is the sheafification of a
perfect complex `ω` of `Γ(X, V)`-modules, the cohomology sheaves of `E|_V` are the
sheafifications of the cohomology modules of `ω`, and those are countable. -/
theorem countable_sections_homology_of_isPerfect_standard [Countable Γ(X, V)] :
    letI := HasDerivedCategory.standard X.Modules
    ∀ (E : DerivedCategory X.Modules),
      @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace
        (HasDerivedCategory.standard X.Modules) E →
      ∀ i : ℤ, Countable Γ((DerivedCategory.homologyFunctor X.Modules i).obj E, V) := by
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard V.toScheme.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, V))
  intro E hE i
  obtain ⟨ω, hω, ⟨eω⟩⟩ := ComplexAndDivisorSituation.exists_isPerfect_presentation hE ⟨V, hV⟩
  let φ : (Scheme.Modules.restrictFunctor V.ι).obj
        ((DerivedCategory.homologyFunctor X.Modules i).obj E) ≅
      (tilde.functor Γ(X, V) ⋙ Scheme.Modules.restrictFunctor hV.isoSpec.hom).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, V)) i).obj ω) :=
    derivedHomologyMapIso (Scheme.Modules.restrictFunctor V.ι) E i ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso eω ≪≫
        (derivedHomologyMapIso _ ω i).symm
  have := countable_sections_tildeRestrict_of_countable hV _
    (countable_homology_of_isPerfect_ring ω hω i)
  have h₁ : Countable Γ((Scheme.Modules.restrictFunctor V.ι).obj
      ((DerivedCategory.homologyFunctor X.Modules i).obj E), ⊤) :=
    countable_sections_of_iso φ.symm ⊤ this
  have h₀ : Countable Γ((DerivedCategory.homologyFunctor X.Modules i).obj E, V.ι ''ᵁ ⊤) := h₁
  rwa [Scheme.Opens.ι_image_top] at h₀

end Affine

/-! ### The statement at every model -/

/-- **Perfect complexes have countable sections of cohomology over affine opens.** Let `X` be a
scheme such that `Γ(V, 𝒪_X)` is countable for every affine open `V`, and let `E` be a perfect
object of `D(𝒪_X)`. Then every cohomology sheaf `H^i(E)` has a countable set of sections over
every affine open. -/
theorem countable_sections_homology_of_isPerfect {X : Scheme.{u}}
    [h : HasDerivedCategory.{w} X.Modules]
    (hO : ∀ V : X.Opens, IsAffineOpen V → Countable Γ(X, V))
    (E : DerivedCategory X.Modules)
    (hE : @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h E)
    (V : X.Opens) (hV : IsAffineOpen V) (i : ℤ) :
    Countable Γ((DerivedCategory.homologyFunctor X.Modules i).obj E, V) := by
  let s := HasDerivedCategory.standard X.Modules
  let e := StacksDraft.DerivedModel.modelEquiv h s
  have hE' : @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace s (e.functor.obj E) :=
    (isPerfect_modelEquiv_functor_obj_iff h s E).2 hE
  have := hO V hV
  exact countable_sections_of_iso
    ((StacksDraft.DerivedModel.modelHomologyFunctorIso h s i).app E) V
    (countable_sections_homology_of_isPerfect_standard hV _ hE' i)

end Stacks.Cohomology.CountableSections

end
