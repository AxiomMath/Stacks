module

public import StacksFrontier.Deformation.Artin.Obstruction.KeyExampleCotangentClass
public import StacksFrontier.RingTheory.NaiveCotangent.ExtensionQuasiIso

/-!
# The naive cotangent complex of a square-zero surjection

Let `A' → A` be a surjection of rings whose kernel `I` has square zero. Then `NL_{A/A'}` is
`I` placed in cohomological degree `-1`: the source writes this identification
`NL_{A/A'} = I[1]`, and uses it to turn a class on `NL_{A/Λ}` into an obstruction element in
`H²(K ⊗ᴸ I)`.

This file proves that the canonical morphism
`Deformation.Artin.squareZeroCotangentClass : NL_{A/A'} ⟶ I[1]` is an isomorphism.

## Main results

* `Deformation.Artin.isIso_relativeNaiveCotangentSurjectionMap` — the comparison of the
  canonical presentation of `A` over `A'` with the presentation given by the surjection
  `A' → A` itself is an isomorphism in `D(A)`.
* `Deformation.Artin.isIso_squareZeroCotangentClass` — **`NL_{A/A'} = I[1]`**: the canonical
  morphism `NL_{A/A'} ⟶ I[1]` of a square-zero surjection is an isomorphism.
* `Deformation.Artin.comp_cotangentExtensionClass_eq_zero_iff` — consequently, a morphism out
  of an object of `D(A)` into `NL_{A/Λ}` is killed by the base-change map to `NL_{A/A'}`
  exactly when it is killed by the extension class `NL_{A/Λ} ⟶ I[1]`.

## Implementation notes

The presentation of `A` over `A'` given by the surjection itself is
`Deformation.Artin.squareZeroExtension`, that is `Algebra.Extension.ofSurjective`. Its ring is
`A'`, so its module of differentials over `A'` vanishes and its cotangent space is therefore
zero; its conormal module is `I/I² = I` because `I² = 0`. The comparison with the canonical
presentation is an isomorphism not by Stacks 00S1 for *polynomial* presentations — the ring of
this extension is not a polynomial ring — but by `NaiveCotangent.nlExtensionMap_isHomotopyEquiv`,
the version of 00S1(4) for arbitrary extensions, whose hypothesis is a morphism of extensions
in each direction. One direction is `Algebra.Extension.defaultHom`; the other is the structure
map `A' ⟶ A'[A]` of the polynomial ring of the canonical presentation.

With that comparison an isomorphism, the second factor of
`Deformation.Artin.squareZeroCotangentClass` is a morphism of cochain complexes which is an
isomorphism in every degree — the conormal identification in degree `-1`, and a morphism
between zero objects in every other degree — so it too becomes an isomorphism.

## References

* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1)
* [Stacks Project, Tag 07BP](https://stacks.math.columbia.edu/tag/07BP)
* [Stacks Project, Tag 07YX](https://stacks.math.columbia.edu/tag/07YX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex NaiveCotangent
open ComplexShape (upIntRelNegOneZero)

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] NaiveCotangent.nlOfExtension

namespace Deformation.Artin

/-! ### A two-term complex whose degree-zero term vanishes -/

section DoubleSingle

variable {R : Type u} [CommRing R] {U V W : ModuleCat.{u} R}

/-- **A two-term complex whose degree-zero term vanishes is its degree `-1` term.** If the
target of the differential is a zero module and `g` is an isomorphism, the chain map
`[U → V] ⟶ W[1]` determined by `g` is an isomorphism of cochain complexes. -/
public theorem isIso_doubleToSingleNegOne [Subsingleton V] (d : U ⟶ V) (g : U ⟶ W)
    (hg : IsIso g) : IsIso (doubleToSingleNegOne d g) := by
  have := hg
  have h : ∀ i, IsIso ((doubleToSingleNegOne d g).f i) := by
    intro i
    by_cases hi : i = -1
    · subst hi
      rw [doubleToSingleNegOne_f_neg_one]
      infer_instance
    · apply Limits.IsZero.isIso
      · by_cases hi0 : i = 0
        · subst hi0
          exact (ModuleCat.isZero_of_subsingleton V).of_iso
            (doubleXIso₁ d upIntRelNegOneZero (by omega))
        · exact isZero_double_X d upIntRelNegOneZero i hi hi0
      · exact isZero_single_obj_X (ComplexShape.up ℤ) (-1) W i hi
  exact HomologicalComplex.Hom.isIso_of_components _

end DoubleSingle

/-! ### The presentation of `A` over `A'` given by the surjection itself -/

section SquareZero

variable (A' A : Type u) [CommRing A'] [CommRing A] [Algebra A' A]
  (hq : Function.Surjective (algebraMap A' A))

/-- The morphism of extensions from the presentation of `A` over `A'` given by the surjection
`A' → A` itself to the canonical presentation of `A` over `A'`: the structure map of the
polynomial ring. -/
public def squareZeroCompareHomInv :
    (squareZeroExtension A' A hq).Hom (Algebra.Generators.self A' A).toExtension :=
  Algebra.Extension.Hom.ofAlgHom
    (Algebra.ofId A' (Algebra.Generators.self A' A).toExtension.Ring) (by ext)

/-- **The cotangent space of the presentation given by the surjection vanishes.** Its ring is
`A'` itself, and `Ω_{A'/A'} = 0`. -/
public theorem subsingleton_cotangentSpace_squareZeroExtension :
    Subsingleton (squareZeroExtension A' A hq).CotangentSpace := by
  have : Subsingleton (Ω[(squareZeroExtension A' A hq).Ring⁄A']) :=
    KaehlerDifferential.subsingleton_of_surjective A' A' Function.surjective_id
  unfold Algebra.Extension.CotangentSpace
  infer_instance

/-- The chain map comparing the two presentations of `A` over `A'` is the one induced by the
morphism of extensions between them. -/
public theorem squareZeroCompareChainMap_eq :
    squareZeroCompareChainMap A' A hq =
      twoTermHom (nlExtensionMap (squareZeroCompareHom A' A hq)) :=
  rfl

/-- **The comparison of presentations of `A` over `A'` is an isomorphism.** The presentation
given by the surjection `A' → A` itself receives a morphism of extensions from the canonical
presentation and maps back to it, so the two naive cotangent complexes are homotopy
equivalent. -/
public theorem isIso_relativeNaiveCotangentSurjectionMap :
    IsIso (relativeNaiveCotangentSurjectionMap A' A hq) := by
  rw [relativeNaiveCotangentSurjectionMap_eq_Q_map, squareZeroCompareChainMap_eq]
  exact isIso_Q_map_twoTermHom
    (nlExtensionMap_isHomotopyEquiv (squareZeroCompareHom A' A hq)
      (squareZeroCompareHomInv A' A hq))

variable (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)

/-- The second factor of `Deformation.Artin.squareZeroCotangentClass`: the chain map from the
two-term complex of the presentation given by the surjection onto its conormal module, which
is the kernel `I`. -/
public theorem squareZeroCotangentClass_eq_comp :
    letI := Stacks.Smooth.kerModule hq hsq
    squareZeroCotangentClass A' A hq hsq =
      relativeNaiveCotangentSurjectionMap A' A hq ≫
        DerivedCategory.Q.map (doubleToSingleNegOne
          (ModuleCat.ofHom (squareZeroExtension A' A hq).cotangentComplex)
          (ModuleCat.ofHom (squareZeroKernelCotangentEquiv A' A hq hsq).symm.toLinearMap)) :=
  rfl

/-- **`NL_{A/A'} = I[1]`.** For a surjection `A' → A` whose kernel `I` has square zero the
canonical morphism `NL_{A/A'} ⟶ I[1]` is an isomorphism of `D(A)`. -/
public theorem isIso_squareZeroCotangentClass :
    letI := Stacks.Smooth.kerModule hq hsq
    IsIso (squareZeroCotangentClass A' A hq hsq) := by
  let := Stacks.Smooth.kerModule hq hsq
  have := subsingleton_cotangentSpace_squareZeroExtension A' A hq
  have := isIso_relativeNaiveCotangentSurjectionMap A' A hq
  have := isIso_doubleToSingleNegOne
    (ModuleCat.ofHom (squareZeroExtension A' A hq).cotangentComplex)
    (ModuleCat.ofHom (squareZeroKernelCotangentEquiv A' A hq hsq).symm.toLinearMap)
    (squareZeroKernelCotangentEquiv A' A hq hsq).symm.toModuleIso.isIso_hom
  rw [squareZeroCotangentClass_eq_comp A' A hq hsq]
  infer_instance

end SquareZero

/-! ### Killing the base-change map and killing the extension class -/

section Tower

variable (Λ A' A : Type u) [CommRing Λ] [CommRing A'] [CommRing A]
  [Algebra Λ A'] [Algebra Λ A] [Algebra A' A] [IsScalarTower Λ A' A]
  (hq : Function.Surjective (algebraMap A' A))
  (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)

attribute [local instance 10000] HasDerivedCategory.standard

/-- **A morphism into `NL_{A/Λ}` is killed by the base change to `NL_{A/A'}` exactly when it
is killed by the extension class.** The extension class is the base-change map followed by the
identification `NL_{A/A'} = I[1]`, which is an isomorphism. -/
public theorem comp_cotangentExtensionClass_eq_zero_iff
    {E : DerivedCategory (ModuleCat.{u} A)} (ξ : E ⟶ derivedNaiveCotangentComplex Λ A) :
    letI := Stacks.Smooth.kerModule hq hsq
    ξ ≫ cotangentExtensionClass Λ A' A hq hsq = 0 ↔
      ξ ≫ naiveCotangentBaseMap Λ A' A = 0 := by
  let := Stacks.Smooth.kerModule hq hsq
  have := isIso_squareZeroCotangentClass A' A hq hsq
  rw [show cotangentExtensionClass Λ A' A hq hsq =
    naiveCotangentBaseMap Λ A' A ≫ squareZeroCotangentClass A' A hq hsq from rfl,
    ← Category.assoc]
  refine ⟨fun h => ?_, fun h => by rw [h, Limits.zero_comp]⟩
  rwa [← cancel_mono (squareZeroCotangentClass A' A hq hsq), Limits.zero_comp]

end Tower

end Deformation.Artin

end
