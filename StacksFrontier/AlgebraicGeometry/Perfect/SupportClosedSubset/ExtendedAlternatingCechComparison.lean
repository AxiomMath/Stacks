module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.Augmentation
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.DerivedSupportInvertsAugmentation

/-!
# The two constructions of the extended alternating Čech complex agree

A finite family `f : Fin c → Γ(X, 𝒪_X)` of global functions on a scheme and an `𝒪_X`-module `F`
determine the extended alternating Čech complex of [Stacks, Tag 0G7I].  This repository carries
two constructions of it, `AlgebraicGeometry.ExtendedAlternatingCech.data` and
`Stacks.Perfect.ExtendedAlternatingCech.extendedAlternatingCech`, each specified by the same data
— the identification of degree `0` with `F`, the identification of degree `p + 1` with the
product of the direct images `F_{i₀…i_p}`, and the sectionwise formulas for the differentials.
This file shows that those specifications determine the complex: the two are isomorphic, by a
unique isomorphism compatible with both sets of identifications.

Consequently every statement proved about one of them holds for the other.  The one transported
here is [Stacks, Tag 0G7M]: derived sections with support on the common zero locus of the
equations invert the augmentation of [Stacks, Tag 0G7L].

## Main definitions

* `Stacks.Perfect.CechComparison.complexIso`: the isomorphism between the two constructions of
  the extended alternating Čech complex.

## Main results

* `Stacks.Perfect.CechComparison.complexIso_hom_f_zero_zeroIso`: the isomorphism is compatible
  with the degree-zero identifications of the two constructions.
* `Stacks.Perfect.CechComparison.augmentation_eq`: the augmentations of [Stacks, Tag 0G7L] of the
  two constructions correspond under the isomorphism.
* `Stacks.Perfect.CechComparison.isIso_derivedSupportedSectionsOnClosed_map_augmentation`:
  [Stacks, Tag 0G7M] for `AlgebraicGeometry.ExtendedAlternatingCech.data`, the construction on
  which the well-definedness of the fraction class of [Stacks, Tag 0G7Q] and the acyclicity of
  [Stacks, Tag 0G7K] are stated.

## Implementation notes

The degree-`0` component of the isomorphism is the composite of the two identifications of
degree `0` with `F`, and the degree-`(p + 1)` component the composite of the two identifications
of degree `p + 1` with the product of the direct images.  That these commute with the
differentials is read off the sectionwise formulas: those determine a differential, because the
sectionwise identifications are injective.

The two constructions name the direct images `F_{i₀…i_p}` and their sections by different
constants, `restrictedModule` and `restrictedModuleSection` of two namespaces, which have the
same definition and are therefore equal by `rfl` but not syntactically equal.  Rewriting cannot
see through that, so the second construction's term isomorphism and its compatibility with the
sectionwise identification are restated here against the first construction's spelling, by
`termIsoFst` and `sectionsIso_compat_fst`; after that every rewrite takes place in a single
vocabulary.

The transport of [Stacks, Tag 0G7M] is through the augmentation: the augmentation is the
projection onto degree `0`, so the isomorphism carries one augmentation to the other, and a
functor sends the isomorphism to an isomorphism.

## References

* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.ExtendedAlternatingCech (data restrictedModule restrictedModuleSection)
open Stacks.Perfect.ExtendedAlternatingCech (extendedAlternatingCech)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.CechComparison

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤)) (F : X.Modules)

/-! ### The isomorphism of the two complexes -/

/-- The degree-`(p + 1)` term of the second construction, identified with the product of the
direct images spelled as in the first construction. -/
def termIsoFst (p : ℕ) :
    (extendedAlternatingCech f F).complex.X (p + 1) ≅
      ∏ᶜ fun s : CechCochains.OrdIndex (I := Fin c) p => restrictedModule f F p s :=
  (extendedAlternatingCech f F).termIso p

/-- The sectionwise identification of the second construction is the componentwise one, spelled
as in the first construction. -/
private theorem sectionsIso_compat_fst (p : ℕ) (V : X.Opens)
    (x : Γ((extendedAlternatingCech f F).complex.X (p + 1), V))
    (s : CechCochains.OrdIndex (I := Fin c) p) :
    (extendedAlternatingCech f F).sectionsIso p V x s =
      restrictedModuleSection f F p s V (((termIsoFst f F p).hom ≫ Pi.π _ s).app V x) :=
  (extendedAlternatingCech f F).sectionsIso_compat p V x s

/-- The degree-`(p + 1)` component of the comparison isomorphism. -/
def termBridge (p : ℕ) :
    (data f F).complex.X (p + 1) ≅ (extendedAlternatingCech f F).complex.X (p + 1) :=
  (data f F).termIso p ≪≫ (termIsoFst f F p).symm

/-- The degree-`0` component of the comparison isomorphism. -/
def zeroBridge : (data f F).complex.X 0 ≅ (extendedAlternatingCech f F).complex.X 0 :=
  (data f F).zeroIso ≪≫ (extendedAlternatingCech f F).zeroIso.symm

/-- The degree-`(p + 1)` component of the comparison respects the sectionwise identifications. -/
private theorem sectionsIso_termBridge (p : ℕ) (V : X.Opens)
    (x : Γ((data f F).complex.X (p + 1), V)) :
    (extendedAlternatingCech f F).sectionsIso p V ((termBridge f F p).hom.app V x) =
      (data f F).sectionsIso p V x := by
  funext s
  rw [sectionsIso_compat_fst, AlgebraicGeometry.ExtendedAlternatingCech.Data.sectionsIso_compat]
  refine congrArg (fun y => restrictedModuleSection f F p s V y) ?_
  have h : (termBridge f F p).hom ≫ ((termIsoFst f F p).hom ≫ Pi.π _ s) =
      ((data f F).termIso p).hom ≫ Pi.π _ s := by
    rw [termBridge, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun g => (Scheme.Modules.Hom.app g V).hom x) h

/-- The degree-`0` component of the comparison is compatible with the two identifications of
degree `0` with `F`. -/
private theorem zeroBridge_hom_comp_zeroIso :
    (zeroBridge f F).hom ≫ (extendedAlternatingCech f F).zeroIso.hom =
      (data f F).zeroIso.hom := by
  rw [zeroBridge, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- The degree-`0` component of the comparison respects the identifications of degree `0`
with `F`. -/
private theorem zeroIso_zeroBridge (V : X.Opens) (x : Γ((data f F).complex.X 0, V)) :
    ((extendedAlternatingCech f F).zeroIso.hom).app V ((zeroBridge f F).hom.app V x) =
      ((data f F).zeroIso.hom).app V x :=
  congrArg (fun g => (Scheme.Modules.Hom.app g V).hom x) (zeroBridge_hom_comp_zeroIso f F)

/-- The comparison commutes with the differential out of degree `0`. -/
theorem comm_zero :
    (zeroBridge f F).hom ≫ (extendedAlternatingCech f F).complex.d 0 1 =
      (data f F).complex.d 0 1 ≫ (termBridge f F 0).hom := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  refine ConcreteCategory.hom_ext _ _ fun x => ?_
  refine ((extendedAlternatingCech f F).sectionsIso 0 V).injective ?_
  funext s
  show (extendedAlternatingCech f F).sectionsIso 0 V
      (((extendedAlternatingCech f F).complex.d 0 1).app V ((zeroBridge f F).hom.app V x)) s = _
  rw [Stacks.Perfect.ExtendedAlternatingCech.ExtendedAlternatingCechData.differential_zero,
    zeroIso_zeroBridge]
  show _ = (extendedAlternatingCech f F).sectionsIso 0 V
      ((termBridge f F 0).hom.app V (((data f F).complex.d 0 1).app V x)) s
  rw [sectionsIso_termBridge, AlgebraicGeometry.ExtendedAlternatingCech.Data.differential_zero]

/-- The comparison commutes with the differentials in positive degrees. -/
theorem comm_succ (p : ℕ) :
    (termBridge f F p).hom ≫ (extendedAlternatingCech f F).complex.d (p + 1) (p + 2) =
      (data f F).complex.d (p + 1) (p + 2) ≫ (termBridge f F (p + 1)).hom := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  refine ConcreteCategory.hom_ext _ _ fun x => ?_
  refine ((extendedAlternatingCech f F).sectionsIso (p + 1) V).injective ?_
  show (extendedAlternatingCech f F).sectionsIso (p + 1) V
      (((extendedAlternatingCech f F).complex.d (p + 1) (p + 2)).app V
        ((termBridge f F p).hom.app V x)) = _
  rw [Stacks.Perfect.ExtendedAlternatingCech.ExtendedAlternatingCechData.differential_succ,
    sectionsIso_termBridge]
  show _ = (extendedAlternatingCech f F).sectionsIso (p + 1) V
      ((termBridge f F (p + 1)).hom.app V
        (((data f F).complex.d (p + 1) (p + 2)).app V x))
  rw [sectionsIso_termBridge, AlgebraicGeometry.ExtendedAlternatingCech.Data.differential_succ]

/-- The degreewise components of the comparison isomorphism. -/
def bridge (n : ℕ) :
    (data f F).complex.X n ≅ (extendedAlternatingCech f F).complex.X n :=
  match n with
  | 0 => zeroBridge f F
  | (p + 1) => termBridge f F p

/-- **Stacks Project, Tag 0G7I.** The two constructions of the extended alternating Čech complex
of a family of global equations and a coefficient module are isomorphic: in degree `0` by the two
identifications with the coefficient module, and in degree `p + 1` by the two identifications
with the product of the direct images of its restrictions to the principal intersections. -/
@[stacks 0G7I "the complex is determined by the data specifying it"]
def complexIso : (data f F).complex ≅ (extendedAlternatingCech f F).complex :=
  HomologicalComplex.Hom.isoOfComponents (bridge f F) (by
    rintro i j hij
    obtain rfl : j = i + 1 := hij.symm
    match i with
    | 0 => exact comm_zero f F
    | (p + 1) => exact comm_succ f F p)

/-- The comparison isomorphism is compatible with the two identifications of degree `0` with the
coefficient module. -/
theorem complexIso_hom_f_zero_zeroIso :
    (complexIso f F).hom.f 0 ≫ (extendedAlternatingCech f F).zeroIso.hom =
      (data f F).zeroIso.hom := by
  exact zeroBridge_hom_comp_zeroIso f F

/-! ### Transport of the augmentation and of Stacks 0G7M -/

/-- The comparison isomorphism of the complexes extended by zero from `ℕ`-degrees to
`ℤ`-degrees. -/
def extendBridge :
    (data f F).complex.extend ComplexShape.embeddingUpNat ≅
      (extendedAlternatingCech f F).complex.extend ComplexShape.embeddingUpNat where
  hom := HomologicalComplex.extendMap (complexIso f F).hom ComplexShape.embeddingUpNat
  inv := HomologicalComplex.extendMap (complexIso f F).inv ComplexShape.embeddingUpNat
  hom_inv_id := by
    rw [← HomologicalComplex.extendMap_comp, Iso.hom_inv_id, HomologicalComplex.extendMap_id]
  inv_hom_id := by
    rw [← HomologicalComplex.extendMap_comp, Iso.inv_hom_id, HomologicalComplex.extendMap_id]

/-- The comparison isomorphism carries the projection onto degree `0` of one construction to the
projection onto degree `0` of the other. -/
private theorem complexIso_comp_augmentationComplex :
    (complexIso f F).hom ≫
        Stacks.Perfect.ExtendedAlternatingCech.Augmentation.augmentationComplex f F =
      AlgebraicGeometry.ExtendedAlternatingCech.augmentationComplex f F := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  match n with
  | 0 =>
      have h2 : (Stacks.Perfect.ExtendedAlternatingCech.Augmentation.augmentationComplex
            f F).f 0 =
          (extendedAlternatingCech f F).zeroIso.hom ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).inv := by
        simp [Stacks.Perfect.ExtendedAlternatingCech.Augmentation.augmentationComplex,
          CochainComplex.toSingle₀Equiv_symm_apply_f_zero]
      have h1 : (AlgebraicGeometry.ExtendedAlternatingCech.augmentationComplex f F).f 0 =
          (data f F).zeroIso.hom ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).inv := by
        simp [AlgebraicGeometry.ExtendedAlternatingCech.augmentationComplex,
          CochainComplex.toSingle₀Equiv_symm_apply_f_zero]
      rw [HomologicalComplex.comp_f, h1, h2, ← Category.assoc, complexIso_hom_f_zero_zeroIso]
  | (p + 1) =>
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 F (p + 1)
        (by omega)).eq_of_tgt _ _

/-- **Stacks Project, Tag 0G7L.** The augmentations of the two constructions of the extended
alternating Čech complex correspond under the comparison isomorphism. -/
@[stacks 0G7L "the augmentations of the two constructions agree"]
theorem augmentation_eq :
    AlgebraicGeometry.ExtendedAlternatingCech.augmentation f F =
      DerivedCategory.Q.map (extendBridge f F).hom ≫
        Stacks.Perfect.ExtendedAlternatingCech.Augmentation.augmentation f F := by
  rw [AlgebraicGeometry.ExtendedAlternatingCech.augmentation,
    Stacks.Perfect.ExtendedAlternatingCech.Augmentation.augmentation, ← DerivedCategory.Q.map_comp]
  refine congrArg DerivedCategory.Q.map ?_
  show HomologicalComplex.extendMap
      (AlgebraicGeometry.ExtendedAlternatingCech.augmentationComplex f F)
        ComplexShape.embeddingUpNat ≫ _ =
    HomologicalComplex.extendMap (complexIso f F).hom ComplexShape.embeddingUpNat ≫ _
  rw [← Category.assoc, ← HomologicalComplex.extendMap_comp,
    complexIso_comp_augmentationComplex]

/-- **Stacks Project, Tag 0G7M.** With `X` a scheme, `f₁, …, f_c ∈ Γ(X, 𝒪_X)` global functions,
`Z` their common zero locus and `F` a quasi-coherent `𝒪_X`-module, the chosen derived functor of
sections supported on `Z` inverts the augmentation of
`AlgebraicGeometry.ExtendedAlternatingCech.data`.

This is `Stacks.Perfect.CechDerivedSupport.isIso_derivedSupportedSectionsOnClosed_map_augmentation`
for the construction of the complex on which [Stacks, Tag 0G7K] and the well-definedness of the
fraction class of [Stacks, Tag 0G7Q] are stated. -/
@[stacks 0G7M "the derived sections with support invert the augmentation"]
theorem isIso_derivedSupportedSectionsOnClosed_map_augmentation [F.IsQuasicoherent] :
    IsIso ((Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsOnClosed
      X.toRingedSpace (Stacks.Perfect.CechDerivedSupport.equationsClosedSet f)
      (Stacks.Perfect.CechDerivedSupport.isClosed_equationsClosedSet f)).map
        (AlgebraicGeometry.ExtendedAlternatingCech.augmentation f F)) := by
  rw [augmentation_eq]
  erw [Functor.map_comp]
  exact IsIso.comp_isIso'
    ((Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsOnClosed
      X.toRingedSpace (Stacks.Perfect.CechDerivedSupport.equationsClosedSet f)
      (Stacks.Perfect.CechDerivedSupport.isClosed_equationsClosedSet f)).mapIso
        (DerivedCategory.Q.mapIso (extendBridge f F))).isIso_hom
    (Stacks.Perfect.CechDerivedSupport.isIso_derivedSupportedSectionsOnClosed_map_augmentation f F)

end Stacks.Perfect.CechComparison

end
