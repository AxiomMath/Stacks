module

public import StacksFrontier.AlgebraicGeometry.AffineOpenSectionsBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.LocalModule
public import StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.ModuleValued
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine

/-!
# The affine case of part (2) of Tag 0EMF

Let `X` be a scheme whose weakly associated points are generic points of irreducible components
and whose quasi-compact opens have finitely many irreducible components, let `F` be a
quasi-coherent `𝒪_X`-module, and let `U` be an affine open. Part (2) of [Stacks, Tag 0EMF]
asserts that the sheaf `K_X(F)` of meromorphic sections of `F` is the product over the generic
points `η` of the contributions `j_{η, *} F_η`. Over the affine open `U = Spec A` the content of
that assertion is the statement proved here: the canonical map

  `Γ(F, U) ⟶ ∏_{η ∈ X⁰} Γ(j_{η, *} F_η, U)`

exhibits the product as a localization of `Γ(F, U)` at the nonzerodivisors of `A`, that is, as
`Q(A) ⊗_A Γ(F, U)`.

The proof is the one in the source, in its module-valued form. The factor at a generic point
`η ∈ U` is the sections of `j_η^* F` over `j_η^{-1} U = Spec 𝒪_{X, η}`, which by the affine
base-change description of the sections of a pullback is `𝒪_{X, η} ⊗_A Γ(F, U)`; since
`𝒪_{X, η}` is the localization of `A` at the minimal prime `𝔮_η` corresponding to `η`, that
factor is the localization of `Γ(F, U)` at `𝔮_η`. The factors at generic points outside `U` have
no sections at all. So the product is a finite product of localizations of `Γ(F, U)` at the
minimal primes of `A`, and `isLocalizedModule_pi_of_bijOn_minimalPrimes` — the module-valued
form of Tag 02LX — identifies it with the localization at the nonzerodivisors.

## Main definitions

* `AlgebraicGeometry.toGenericPointStalkSections`: the canonical `Γ(X, U)`-linear map
  `Γ(F, U) ⟶ Γ(j_{η, *} j_η^* F, U)`, namely the unit of `j_η^* ⊣ j_{η, *}` on sections.
* `AlgebraicGeometry.specStalkSectionsModule`: the sections of `j_η^* F` over `j_η^{-1} U`,
  read as a module over the sections of `𝒪_{Spec 𝒪_{X, η}}` there, at the type ascribed at
  `Γ(j_{η, *} j_η^* F, U)`.
* `piSubtypeLinearEquivOfSubsingleton`: restricting a product of modules to a subfamily of the
  factors, when the discarded factors are trivial.

## Main results

* `AlgebraicGeometry.isLocalizedModule_toGenericPointStalkSections`: the factor at a generic
  point lying in `U` is the localization of `Γ(F, U)` at the corresponding minimal prime.
* `AlgebraicGeometry.isLocalizedModule_pi_toGenericPointStalkSections`: **the affine case of
  part (2) of Tag 0EMF.** The product of all the factors is the localization of `Γ(F, U)` at the
  nonzerodivisors of `Γ(X, U)`.

## Implementation notes

The two module structures involved — over `Γ(X, U)` and over
`Γ(Spec 𝒪_{X, η}, j_η^{-1} U)` — sit on one and the same type of sections, but each is found by
instance search only at its own spelling of that type: the first at
`Γ(j_{η, *} j_η^* F, U)`, the second at `Γ(j_η^* F, j_η^{-1} U)`. They are definitionally equal
types, so `specStalkSectionsModule` and `specStalkSectionsIsScalarTower` transport the second
structure to the first spelling; but they are not *syntactically* equal, so instance search does
not find the transported structures either and every lemma that needs both module structures at
once receives them as explicit arguments. That is why
`AlgebraicGeometry.ModuleCat.isBaseChange_of_extendScalarsIso` and
`isLocalizedModule_pi_of_bijOn_minimalPrimes` are applied here with their instance arguments
written out.

What this file does *not* do is pass from the affine open to the whole of `X`. The comparison
morphism of sheaves is `AlgebraicGeometry.genericPointComparisonPi` of
`StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.Globalization`, and its
invertibility is not proved here: the step still missing is that the presheaf whose
sheafification is `K_X(F)` — the sectionwise extension of scalars `U ↦ K_X(U) ⊗_{𝒪_X(U)} F(U)` of
`Stacks.Sheaves.ChangeOfRings.changeOfRings` — maps to the product by a map which on an affine
open is the map proved here to be bijective, after which the stalk argument of
`AlgebraicGeometry.isIso_toGenericPointStalkProduct` applies verbatim.

## References

* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
* [Stacks Project, Tag 02LX](https://stacks.math.columbia.edu/tag/02LX)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite TensorProduct
open Stacks.AlgebraicGeometry.GenericPointDecomposition (genericPointStalkModuleOf)

universe u v w

noncomputable section

/-- Restricting a product of modules to a subfamily of the factors is a linear equivalence when
all the discarded factors are trivial. This is the module-valued form of
`piSubtypeAlgEquivOfSubsingleton`. -/
def piSubtypeLinearEquivOfSubsingleton {A : Type u} [CommRing A] {ι : Type v}
    (P : ι → Prop) (C : ι → Type w) [∀ i, AddCommGroup (C i)] [∀ i, Module A (C i)]
    (h : ∀ i, ¬ P i → Subsingleton (C i)) :
    (∀ i, C i) ≃ₗ[A] (∀ i : {i // P i}, C i.1) := by
  classical
  refine LinearEquiv.ofBijective
    (LinearMap.pi fun i : {i // P i} ↦ LinearMap.proj (R := A) (φ := C) i.1) ⟨?_, ?_⟩
  · intro f g hfg
    funext i
    by_cases hi : P i
    · exact congrFun hfg ⟨i, hi⟩
    · exact (h i hi).elim _ _
  · intro g
    refine ⟨fun i => if hi : P i then g ⟨i, hi⟩ else 0, ?_⟩
    funext i
    change (if hi : P i.1 then g ⟨i.1, hi⟩ else 0) = g i
    rw [dite_eq_left_of_eq_true (by simp [i.2])]

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### The canonical map on sections at one generic point -/

/-- The canonical `Γ(X, U)`-linear map `Γ(F, U) ⟶ Γ(j_{η, *} j_η^* F, U)`: the unit of
`j_η^* ⊣ j_{η, *}` evaluated on sections over `U`. -/
def toGenericPointStalkSections (F : X.Modules) (η : genericPoints X) (U : X.Opens) :
    Γ(F, U) →ₗ[Γ(X, U)] Γ(genericPointStalkModuleOf X F η, U) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction (X.fromSpecStalk η.1)).unit.app F).val.app
    (op U)).hom

/-- The canonical map on sections is the pullback of a section, in the sense of
`AlgebraicGeometry.Scheme.Modules.pullbackSection`, over the full preimage of `U`. -/
lemma toGenericPointStalkSections_eq_pullbackSection
    (F : X.Modules) (η : genericPoints X) (U : X.Opens) (a : Γ(F, U)) :
    toGenericPointStalkSections F η U a =
      Scheme.Modules.pullbackSection (X.fromSpecStalk η.1) F U
        (X.fromSpecStalk η.1 ⁻¹ᵁ U) le_rfl a := by
  unfold Scheme.Modules.pullbackSection toGenericPointStalkSections
  rw [show (homOfLE (le_refl (X.fromSpecStalk η.1 ⁻¹ᵁ U))).op = 𝟙 _ from Subsingleton.elim _ _]
  simp
  rfl

/-- The sections of `j_η^* F` over `j_η^{-1} U`, read as a module over the sections of the
structure sheaf of `Spec 𝒪_{X, η}` there but at the type spelled `Γ(j_{η, *} j_η^* F, U)`. The
two spellings are definitionally equal types and this is the identity, but instance search finds
the module structure only at the first of them. -/
@[instance_reducible]
def specStalkSectionsModule (F : X.Modules) (η : genericPoints X) (U : X.Opens) :
    Module Γ(Spec (X.presheaf.stalk η.1), X.fromSpecStalk η.1 ⁻¹ᵁ U)
      Γ(genericPointStalkModuleOf X F η, U) :=
  inferInstanceAs (Module Γ(Spec (X.presheaf.stalk η.1), X.fromSpecStalk η.1 ⁻¹ᵁ U)
    Γ((Scheme.Modules.pullback (X.fromSpecStalk η.1)).obj F, X.fromSpecStalk η.1 ⁻¹ᵁ U))

/-- The two module structures on the sections of `j_{η, *} j_η^* F` over `U` form a scalar tower
over the structure map of `j_η` on sections. -/
lemma specStalkSectionsIsScalarTower (F : X.Modules) (η : genericPoints X) (U : X.Opens) :
    letI := specStalkSectionsModule F η U
    IsScalarTower Γ(X, U) Γ(Spec (X.presheaf.stalk η.1), X.fromSpecStalk η.1 ⁻¹ᵁ U)
      Γ(genericPointStalkModuleOf X F η, U) := by
  let _inst := specStalkSectionsModule F η U
  constructor
  intro r b n
  show ((((X.fromSpecStalk η.1).app U).hom r) * b) • n = _
  rw [mul_smul]
  rfl

/-- The preimage of an open containing a generic point, under the canonical morphism from the
spectrum of the local ring there, is an affine open: it is the whole of a spectrum. -/
lemma isAffineOpen_fromSpecStalk_preimage (η : genericPoints X) {U : X.Opens}
    (hηU : (η : X) ∈ U) : IsAffineOpen (X.fromSpecStalk η.1 ⁻¹ᵁ U) := by
  rw [fromSpecStalk_preimage_eq_top η.2 hηU]
  exact isAffineOpen_top _

/-- On an affine open containing a generic point, the sections of the pushed-forward structure
sheaf of the spectrum of the local ring there are the localization of the ring of sections at the
corresponding minimal prime. -/
lemma isLocalization_specStalkSections (η : genericPoints X) {U : X.Opens}
    (hU : IsAffineOpen U) (hηU : (η : X) ∈ U) :
    IsLocalization (hU.primeIdealOf ⟨(η : X), hηU⟩).asIdeal.primeCompl
      Γ(Spec (X.presheaf.stalk η.1), X.fromSpecStalk η.1 ⁻¹ᵁ U) := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk η.1) :=
    X.presheaf.algebra_section_stalk ⟨η.1, hηU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk η.1)
      (hU.primeIdealOf ⟨(η : X), hηU⟩).asIdeal := hU.isLocalization_stalk ⟨(η : X), hηU⟩
  exact IsLocalization.isLocalization_of_algEquiv _ (specStalkSectionsAlgEquiv η hηU).symm

/-- **The factor of part (2) of Stacks 0EMF at one generic point, on an affine open.** For a
quasi-coherent module `F` and a generic point `η` of an irreducible component lying in an affine
open `U`, the sections of `j_{η, *} j_η^* F` over `U` are the localization of `Γ(F, U)` at the
minimal prime of `Γ(X, U)` corresponding to `η`.

The sections of the pullback over `j_η^{-1} U` are `𝒪_{X, η} ⊗_{Γ(X, U)} Γ(F, U)` by the affine
base-change description of the sections of a pullback, and `𝒪_{X, η}` is the localization of
`Γ(X, U)` at that prime. -/
lemma isLocalizedModule_toGenericPointStalkSections
    (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
    (η : genericPoints X) (hηU : (η : X) ∈ U) :
    IsLocalizedModule (hU.primeIdealOf ⟨(η : X), hηU⟩).asIdeal.primeCompl
      (toGenericPointStalkSections F η U) := by
  have hloc := isLocalization_specStalkSections η hU hηU
  let hmod := specStalkSectionsModule F η U
  let htow := specStalkSectionsIsScalarTower F η U
  refine (@isLocalizedModule_iff_isBaseChange _ _
    (hU.primeIdealOf ⟨(η : X), hηU⟩).asIdeal.primeCompl
    Γ(Spec (X.presheaf.stalk η.1), X.fromSpecStalk η.1 ⁻¹ᵁ U) _ _ hloc
    _ _ _ _ _ _ hmod htow
    (toGenericPointStalkSections F η U)).mpr ?_
  refine @ModuleCat.isBaseChange_of_extendScalarsIso
    Γ(X, U) Γ(Spec (X.presheaf.stalk η.1), X.fromSpecStalk η.1 ⁻¹ᵁ U)
    Γ(F, U) Γ(genericPointStalkModuleOf X F η, U)
    _ _ _ _ _ _ hmod _ htow
    ((X.fromSpecStalk η.1).appLE U (X.fromSpecStalk η.1 ⁻¹ᵁ U) le_rfl).hom
    (congrArg (fun φ : Γ(X, U) ⟶ _ => (CommRingCat.Hom.hom φ).toAlgebra)
      (Scheme.Hom.appLE_preimage_self (X.fromSpecStalk η.1) U).symm)
    (affinePullbackSectionsBaseChangeIso (X.fromSpecStalk η.1) F hU
      (isAffineOpen_fromSpecStalk_preimage η hηU) le_rfl)
    (toGenericPointStalkSections F η U) (fun a => ?_)
  exact (affinePullbackSectionsBaseChangeIso_one_tmul (X.fromSpecStalk η.1) F hU
    (isAffineOpen_fromSpecStalk_preimage η hηU) le_rfl a).trans
    (toGenericPointStalkSections_eq_pullbackSection F η U a).symm

/-! ### The product over all the generic points -/

/-- A generic point of an irreducible component outside an open set contributes no sections
there. -/
lemma subsingleton_genericPointStalkSections (F : X.Modules) (η : genericPoints X)
    {U : X.Opens} (hηU : (η : X) ∉ U) :
    Subsingleton Γ(genericPointStalkModuleOf X F η, U) :=
  subsingleton_sections_of_eq_bot ((Scheme.Modules.pullback (X.fromSpecStalk η.1)).obj F)
    (fromSpecStalk_preimage_eq_bot η.2 hηU)

/-- **The affine case of part (2) of Stacks 0EMF.** Let `X` be a scheme whose weakly associated
points are generic points of irreducible components and whose quasi-compact opens have finitely
many irreducible components, let `F` be a quasi-coherent `𝒪_X`-module and let `U` be an affine
open. Then the canonical map from `Γ(F, U)` to the product over all the generic points `η` of
the sections of `j_{η, *} j_η^* F` over `U` exhibits that product as the localization of
`Γ(F, U)` at the nonzerodivisors of `Γ(X, U)`, that is, as `Q(Γ(X, U)) ⊗_{Γ(X, U)} Γ(F, U)`. -/
theorem isLocalizedModule_pi_toGenericPointStalkSections
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) :
    IsLocalizedModule (nonZeroDivisors Γ(X, U))
      (LinearMap.pi fun η : genericPoints X ↦ toGenericPointStalkSections F η U) := by
  have hfinι : Finite {η : genericPoints X // (η : X) ∈ U} :=
    finite_genericPoints_mem_of_isCompact X U hU.isCompact hfinite
  -- the enumeration of the minimal primes of `Γ(X, U)` by the generic points lying in `U`
  let E := genericPointsInOpenEquivMinimalPrimes hU
  let q : {η : genericPoints X // (η : X) ∈ U} → Ideal Γ(X, U) :=
    fun η ↦ (hU.primeIdealOf ⟨η.1.1, η.2⟩).asIdeal
  have hqE : ∀ η, q η = ((E η : minimalPrimes Γ(X, U)) : Ideal Γ(X, U)) := fun η ↦
    (genericPointsInOpenEquivMinimalPrimes_asIdeal hU η).symm
  have hmem : ∀ η, q η ∈ minimalPrimes Γ(X, U) := fun η ↦ hqE η ▸ (E η).2
  have hinj : Function.Injective q := by
    intro a b hab
    apply E.injective
    apply Subtype.ext
    rw [← hqE, ← hqE, hab]
  have hsurj : ∀ p ∈ minimalPrimes Γ(X, U), ∃ η, q η = p := by
    intro p hp
    refine ⟨E.symm ⟨p, hp⟩, ?_⟩
    rw [hqE, E.apply_symm_apply]
  -- the restriction of the product to the factors at the generic points lying in `U`
  let e := piSubtypeLinearEquivOfSubsingleton (A := Γ(X, U))
    (fun η : genericPoints X ↦ (η : X) ∈ U)
    (fun η : genericPoints X ↦ Γ(genericPointStalkModuleOf X F η, U))
    fun η hη ↦ subsingleton_genericPointStalkSections F η hη
  have hsub : IsLocalizedModule (nonZeroDivisors Γ(X, U))
      (LinearMap.pi fun η : {η : genericPoints X // (η : X) ∈ U} ↦
        toGenericPointStalkSections F η.1 U) :=
    @isLocalizedModule_pi_of_bijOn_minimalPrimes Γ(X, U) _
      {η : genericPoints X // (η : X) ∈ U}
      (fun η ↦ Γ(Spec (X.presheaf.stalk η.1.1), X.fromSpecStalk η.1.1 ⁻¹ᵁ U)) _ _
      Γ(F, U) _ _
      (fun η ↦ Γ(genericPointStalkModuleOf X F η.1, U)) _ _
      (fun η ↦ specStalkSectionsModule F η.1 U)
      (fun η ↦ specStalkSectionsIsScalarTower F η.1 U)
      (fun _ hx ↦ exists_minimalPrimes_mem_of_notMem_nonZeroDivisors hass hU hx)
      hfinι q _ hmem hinj hsurj
      (fun η ↦ isLocalization_specStalkSections η.1 hU η.2)
      (fun η ↦ toGenericPointStalkSections F η.1 U)
      (fun η ↦ isLocalizedModule_toGenericPointStalkSections F hU η.1 η.2)
  have hcomp : (e.symm : _ →ₗ[Γ(X, U)] _) ∘ₗ
      (LinearMap.pi fun η : {η : genericPoints X // (η : X) ∈ U} ↦
        toGenericPointStalkSections F η.1 U) =
      LinearMap.pi fun η : genericPoints X ↦ toGenericPointStalkSections F η U := by
    refine LinearMap.ext fun a ↦ e.injective ?_
    show e (e.symm ((LinearMap.pi fun η : {η : genericPoints X // (η : X) ∈ U} ↦
        toGenericPointStalkSections F η.1 U) a)) =
      e ((LinearMap.pi fun η : genericPoints X ↦ toGenericPointStalkSections F η U) a)
    rw [e.apply_symm_apply]
    funext i
    rfl
  exact hcomp ▸ IsLocalizedModule.of_linearEquiv _ _ e.symm

end AlgebraicGeometry

end

end
