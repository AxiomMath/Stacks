module

public import StacksFrontier.Homology.KFlat.ChosenResolution
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeStrong
public import StacksFrontier.RingTheory.Dualizing.RelativeCompositionUntwisted
public import StacksFrontier.RingTheory.Dualizing.TrivialDualityInvertibleKernel
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.DerivedTensor
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormula

/-!
# The composite dualizing complex of [stacks 0E2H] as a tensor product over `B`

Let `g : A → B` be a homomorphism of commutative rings, `K_{A/R}` an object of `D(A)` and
`K_{B/A}` an object of `D(B)`. The derived change-of-rings tensor product of [stacks 06Y6],
`Dualizing.derivedTensorProductOver g K_{B/A} |>.obj K_{A/R}`, is a tensor product over `B`, in
the tensor--Hom vocabulary of [stacks 0A63], of `K_{B/A}` with the derived base change of
`K_{A/R}`:

`K_{A/R} ⊗ᴸ_A K_{B/A} ≅ K_{B/A} ⊗ᴸ_B (K_{A/R} ⊗ᴸ_A B)`.

As a consequence the `A`-restricted isomorphism (*) of [stacks 0E2H] holds for the composite
object `K_{A/R} ⊗ᴸ_A K_{B/A}`.

## Main definitions

* `Dualizing.diagonalDerivedExtensionTensorIso`: [stacks 068I] at the left coprojection
  `B → B ⊗[R] B`, the isomorphism exhibiting derived base change along it as strongly monoidal.

## Main results

* `Dualizing.nonempty_derivedTensorProductOver_iso_extension_comp_tensorRight`: the
  identification as functors `D(A) ⥤ D(B)`:
  `- ⊗ᴸ_A K_{B/A} ≅ (- ⊗ᴸ_A B) ⋙ (- ⊗ᴸ_B K_{B/A})`.
* `Dualizing.nonempty_derivedTensorProductOver_obj_iso_tensor_derivedExtension`: the
  identification at an object, `K_{A/R} ⊗ᴸ_A K_{B/A} ≅ K_{B/A} ⊗ᴸ_B (K_{A/R} ⊗ᴸ_A B)`.
* `Dualizing.nonempty_derivedExtension_tensor_iso_composite`: the derived base change of
  `K_{A/R} ⊗ᴸ_A K_{B/A}` to `B ⊗[R] B` is the tensor product of the base changes of `K_{B/A}` and
  of `K_{A/R} ⊗ᴸ_A B`.
* `Dualizing.nonempty_restrict_diagonalQuotientDerivedHom_composite`: the `A`-restricted
  isomorphism (*) of [stacks 0E2H] for the composite object.

## References

* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0BYK](https://stacks.math.columbia.edu/tag/0BYK)
* [Stacks Project, Tag 0E2H](https://stacks.math.columbia.edu/tag/0E2H)
-/

@[expose] public noncomputable section

open CategoryTheory
open CochainComplex CochainComplex.DerivedTensor
open CochainComplex.DerivedExtensionScalars
open StacksDraft.DerivedHom
open scoped TensorProduct

universe u

namespace Dualizing

attribute [local instance] HasDerivedCategory.standard

section ChangeOfRings

variable {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B)

/-- The derived change-of-rings tensor product of [stacks 06Y6] is derived extension of scalars
followed by the tensor product of [stacks 0A63]: for a homomorphism `g : A → B` and an object
`KB` of `D(B)`, the functor `Dualizing.derivedTensorProductOver g KB`, which is `- ⊗ᴸ_A KB`
valued in `D(B)`, is derived extension of scalars along `g` followed by tensoring with `KB` over
`B`. -/
theorem nonempty_derivedTensorProductOver_iso_extension_comp_tensorRight
    (KB : DerivedCategory (ModuleCat.{u} B)) :
    Nonempty (derivedTensorProductOver.{u, u} g KB ≅
      (totalDerivedExtensionScalars.{u, u, u} g).functor ⋙
        ProjectionFormula.tensorRightDerived.{u, u} B KB) := by
  let WA := HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)
  let WB := HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)
  let N₀ := ((DerivedCategory.Qh (C := ModuleCat.{u} B)).objPreimage KB).as
  let res := CochainComplex.KFlat.chosenResolution.{u, u} N₀
  let P := res.complex
  have hP : CochainComplex.KFlat.{u, u} P := res.kFlat
  have hpi : QuasiIso res.π := res.quasiIso
  let T := canonicalDerivedTensorChangeOfRings.{u, u, u} g P
  let T₀ := canonicalDerivedTensorChangeOfRings.{u, u, u} g N₀
  let eF : T₀.F ≅ T.F :=
    InvertibleKernel.derivedTensorIsoOfDerivedIso.{u, u} g
      (asIso (DerivedCategory.Q.map res.π)).symm T₀ T
  let eB : T.B ≅ (totalDerivedExtensionScalars.{u, u, u} g).functor :=
    Functor.leftDerivedNatIso T.B (totalDerivedExtensionScalars.{u, u, u} g).functor
      T.alphaB (totalDerivedExtensionScalars.{u, u, u} g).comparison WA (Iso.refl _)
  let eRight := ProjectionFormula.derivedTensorRightNatIso.{u, u} B P hP
  have := Functor.isLeftDerivedFunctor_of_inverts WB
    (ProjectionFormula.tensorRightDerived.{u, u} B (DerivedCategory.Q.obj P)) eRight
  let eG : T.G ≅ ProjectionFormula.tensorRightDerived.{u, u} B (DerivedCategory.Q.obj P) :=
    Functor.leftDerivedNatIso T.G
      (ProjectionFormula.tensorRightDerived.{u, u} B (DerivedCategory.Q.obj P))
      T.alphaG eRight.hom WB (Iso.refl _)
  let eP : DerivedCategory.Q.obj P ≅ KB :=
    asIso (DerivedCategory.Q.map res.π) ≪≫
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} B)).app N₀).symm ≪≫
      DerivedCategory.Qh.objObjPreimageIso KB
  exact ⟨eF ≪≫ T.changeOfRings ≪≫ Functor.isoWhiskerRight eB T.G ≪≫
    Functor.isoWhiskerLeft (totalDerivedExtensionScalars.{u, u, u} g).functor
      (eG ≪≫ (Functor.curry.obj
        (derivedHomAdjunctionOverRing.{u, u, u + 1} B).tensor).flip.mapIso eP)⟩

/-- The composite object of [stacks 0E2H] is a tensor product over `B`: for `g : A → B` and
objects `KA` of `D(A)` and `KB` of `D(B)`,

`KA ⊗ᴸ_A KB ≅ KB ⊗ᴸ_B (KA ⊗ᴸ_A B)`,

the left side being `Dualizing.derivedTensorProductOver g KB` at `KA` and the right side the
tensor product of the [stacks 0A63] bundle over `B` of `KB` with the derived base change of `KA`.
-/
theorem nonempty_derivedTensorProductOver_obj_iso_tensor_derivedExtension
    (KA : DerivedCategory (ModuleCat.{u} A)) (KB : DerivedCategory (ModuleCat.{u} B)) :
    Nonempty ((derivedTensorProductOver.{u, u} g KB).obj KA ≅
      (derivedHomAdjunctionOverRing.{u, u, u + 1} B).tensor.obj
        (KB, (totalDerivedExtensionScalars.{u, u, u} g).functor.obj KA)) := by
  obtain ⟨e⟩ := nonempty_derivedTensorProductOver_iso_extension_comp_tensorRight g KB
  exact ⟨e.app KA ≪≫ (derivedHomAdjunctionOverRing.{u, u, u + 1} B).tensorSwap _ _⟩

end ChangeOfRings

section Diagonal

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] [Module.Flat R B]

/-- [stacks 068I] at the left coprojection `B → B ⊗[R] B`: derived base change
`Dualizing.diagonalDerivedExtension R B` along the left coprojection is strongly monoidal for the
tensor products of the [stacks 0A63] bundles,

`(X ⊗ᴸ_B C) ⊗ᴸ_C (Y ⊗ᴸ_B C) ≅ (X ⊗ᴸ_B Y) ⊗ᴸ_B C`,  `C = B ⊗[R] B`. -/
def diagonalDerivedExtensionTensorIso (X Y : DerivedCategory (ModuleCat.{u} B)) :
    (derivedHomAdjunctionOverRing.{u, u, u + 1} (B ⊗[R] B)).tensor.obj
        ((diagonalDerivedExtension R B).obj X, (diagonalDerivedExtension R B).obj Y) ≅
      (diagonalDerivedExtension R B).obj
        ((derivedHomAdjunctionOverRing.{u, u, u + 1} B).tensor.obj (X, Y)) :=
  (derivedHomAdjunctionOverRing.{u, u, u + 1} (B ⊗[R] B)).tensor.mapIso
      (((diagonalDerivedExtensionIsoTotalDerived R B).app X).symm.prod
        ((diagonalDerivedExtensionIsoTotalDerived R B).app Y).symm) ≪≫
    asIso (derivedTensorBaseChange.{u, u, u}
      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] B)
      (totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] B)).functor
      (ProjectionFormula.modelComparison.{u, u}
        (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] B)
        (totalDerivedExtensionScalars.{u, u, u}
          (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] B))) X Y) ≪≫
    (diagonalDerivedExtensionIsoTotalDerived R B).app
      ((derivedHomAdjunctionOverRing.{u, u, u + 1} B).tensor.obj (X, Y))

end Diagonal

section Composite

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  [Module.Flat R A] [Algebra.FinitePresentation R A]
  [Module.Flat A B] [Algebra.FinitePresentation A B]

omit [Algebra.FinitePresentation R A] [Algebra.FinitePresentation A B] in
/-- Let `R → A → B` be flat, write `C = B ⊗[R] B`, `K = K_{A/R} ⊗ᴸ_A K_{B/A}` for the object
[stacks 0E2H] forms, `Y = K_{B/A} ⊗ᴸ_B C` and `X = (K_{A/R} ⊗ᴸ_A B) ⊗ᴸ_B C`. Then

`K ⊗ᴸ_B C ≅ Y ⊗ᴸ_C X`. -/
theorem nonempty_derivedExtension_tensor_iso_composite
    (KA : DerivedCategory (ModuleCat.{u} A)) (KB : DerivedCategory (ModuleCat.{u} B)) :
    letI : Module.Flat R B := Module.Flat.trans R A B
    Nonempty
      ((diagonalDerivedExtension R B).obj
          ((derivedTensorProductOver.{u, u} (algebraMap A B) KB).obj KA) ≅
        (derivedHomAdjunctionOverRing (B ⊗[R] B)).tensor.obj
          ((diagonalDerivedExtension R B).obj KB,
            (diagonalDerivedExtension R B).obj
              ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A B)).functor.obj KA))) := by
  let : Module.Flat R B := Module.Flat.trans R A B
  obtain ⟨e⟩ :=
    nonempty_derivedTensorProductOver_obj_iso_tensor_derivedExtension (algebraMap A B) KA KB
  exact ⟨(diagonalDerivedExtension R B).mapIso e ≪≫
    (diagonalDerivedExtensionTensorIso R B KB
      ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A B)).functor.obj KA)).symm⟩

/-- The `A`-restricted isomorphism (*) of [stacks 0E2H] for the composite object. Let
`R → A → B` be flat of finite presentation, let `K_{A/R}` be a relative dualizing complex for
`R → A` and let `K_{B/A}` be perfect relative to `A` in `D(B)`. Writing `C' = B ⊗[A] B`,
`C = B ⊗[R] B` and `K = K_{A/R} ⊗ᴸ_A K_{B/A}` for the object [stacks 0E2H] forms, the
restriction to `A` of

`RHom_C(C', K ⊗ᴸ_B C) ≅ K_{B/A} ⊗ᴸ_B C'`

holds. -/
theorem nonempty_restrict_diagonalQuotientDerivedHom_composite
    (KA : DerivedCategory (ModuleCat.{u} A)) (KB : DerivedCategory (ModuleCat.{u} B))
    (hKA : IsRelativeDualizingComplex R A KA)
    (hKB : PseudoCoherence.IsRelativelyPerfect.{u, u, u}
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison A)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived A) KB) :
    letI := diagonalAlgebra R A B
    letI := diagonalAlgebraSelf R A
    letI := diagonalQuotientAlgebra R A B
    letI := diagonalAlgebraQuot R A B
    letI := diagonalIsScalarTower R A B
    letI := diagonalIsScalarTowerSelf R A B
    letI : Module.Flat R B := Module.Flat.trans R A B
    Nonempty
      ((ModuleCat.restrictScalars.{u}
            (algebraMap A (B ⊗[A] B))).mapDerivedCategory.obj
          ((derivedHom.{u, u, u} (diagonalQuotient R A B).toRingHom).obj
            ((diagonalDerivedExtension R B).obj
              ((derivedTensorProductOver.{u, u} (algebraMap A B) KB).obj KA))) ≅
        (ModuleCat.restrictScalars.{u}
            (algebraMap A (B ⊗[A] B))).mapDerivedCategory.obj
          ((diagonalDerivedExtension A B).obj KB)) :=
  nonempty_restrict_diagonalQuotientDerivedHom_of_derivedExtension_tensor_iso R A B KA KB
    ((derivedTensorProductOver.{u, u} (algebraMap A B) KB).obj KA) hKA hKB
    (nonempty_derivedExtension_tensor_iso_composite R A B KA KB).some

end Composite

end Dualizing

end
