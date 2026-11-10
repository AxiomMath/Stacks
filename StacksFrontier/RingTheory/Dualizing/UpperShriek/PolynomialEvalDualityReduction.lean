module

public import StacksFrontier.RingTheory.Dualizing.TrivialDualityInvertibleKernelPerfect
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Independence
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.DerivedCompletion
import all StacksFrontier.RingTheory.Dualizing.UpperShriek.DerivedTensor
import all StacksFrontier.RingTheory.Dualizing.UpperShriek.Independence

/-!
# Reducing the polynomial evaluation duality to the comparison of Stacks 0BZE

`Dualizing.PolynomialEvalDuality` is the conclusion of [Stacks, Tag 0BZH] at the evaluation
surjections `B[x] ↠ B`, phrased as an isomorphism between derived coextension of scalars
`RHom_{B[x]}(B, -)` and an arbitrary total left derived functor of extension of scalars, shifted
by `-1`. This file proves that it follows from the model-free conclusion of Stacks 0BZH at those
surjections, and from [Stacks, Tag 0BZE] in the form of invertibility of `Stacks0BZE.comparison`
at every K-flat complex.

The content is the tensor side of Stacks 0BZH. For a surjection
`R → A` whose kernel is *free of rank one* the inverse `N` of the conormal module is `A` itself, so
the tensor factor `N[-1]` of Stacks 0BZH is the monoidal unit of `D(A)` shifted by `-1`; derived
tensoring with it is therefore derived extension of scalars followed by that shift. Two
identifications carry this out: the tensor factor may be replaced by any complex with the same
class in `D(A)`, and a shift of the tensor factor may be moved out past the derived tensor functor.

## Main results

* `Dualizing.InvertibleKernel.conormalInverseEquivSelf` — the inverse of the conormal module of a
  surjection with kernel free of rank one is the target ring.
* `Dualizing.InvertibleKernel.derivedTensorUnitComplexIsoDerivedExtension` — **derived tensoring
  along `f` with the monoidal unit is derived extension of scalars along `f`**, for any total left
  derived model of the latter, and with no flatness hypothesis.
* `Dualizing.InvertibleKernel.nonempty_derivedTensorConormalInverseShiftIso` — **derived tensoring
  with the tensor factor `N[-1]` of Stacks 0BZH is derived extension of scalars shifted by `-1`**,
  when the kernel is free of rank one.
* `Dualizing.InvertibleKernel.nonempty_derivedHom_iso_shiftedDerivedExtension_of_freeKernel` — the
  model-free conclusion of Stacks 0BZH at a kernel free of rank one gives the shifted-extension
  form.
* `Dualizing.polynomialEvalDuality_of_nonempty_derivedHom_iso` —
  **`Dualizing.PolynomialEvalDuality` follows from the model-free conclusion of Stacks 0BZH at the
  evaluation surjections, and from nothing else.** Neither statement needs the canonical
  comparison morphism of Stacks 0BZE.
* `Dualizing.polynomialEvalDuality_of_nonempty_bundle_iso` — **the same from Stacks 0BZE in the
  bundle shape**, that is from `RHom_{S[x]}(S, -) ≅ (Stacks0BZE.bundle _).F`. Again no
  comparison morphism is pinned.
* `Dualizing.polynomialEvalDuality_of_isIso_comparison` — the same with the hypothesis in a
  model-pinned form of Stacks 0BZE: invertibility of `Stacks0BZE.comparison` at the evaluation
  surjections.

## Implementation notes

The identification of the derived tensor product with derived extension of scalars uses the
factorisation `F ≅ B ⋙ G` carried as the field `changeOfRings` of
`CochainComplex.DerivedTensor.DerivedTensorChangeOfRings`, not the field `directTensor`: at the
monoidal unit the second factor `G` is the left derived functor of a functor isomorphic to the
identity, hence is the identity, and the first factor `B` is a total left derived functor of
extension of scalars, hence is identified with any other by uniqueness of left derived functors.
Going through `directTensor` instead would need flatness of `f`, which the evaluation surjections
do not have; that is why `Rig.flatDerivedTensorIso` is not used.

`Dualizing.PolynomialEvalDuality` states the universal property of its derived model on the
homotopy category, through `DerivedCategory.Qh`, whereas
`CochainComplex.DerivedTensor.DerivedTensorChangeOfRings` states it on complexes, through
`DerivedCategory.Q`. The translation is `Dualizing.Independence.homotopyCategoryDerivedComparison`
together with `Dualizing.Independence.leftDerivedFunctor_of_homotopyCategory`, which are private to
`StacksFrontier/RingTheory/Dualizing/UpperShriek/Independence.lean` and reached here by
`import all`;
so is the shift identification `Dualizing.derivedTensorPostcomposeShiftIso` of
`StacksFrontier/RingTheory/Dualizing/UpperShriek/DerivedTensor.lean`. Everything in this file that
mentions them is therefore private, except the final theorem, whose statement does not.

## References

* [Stacks Project, Tag 0BZH](https://stacks.math.columbia.edu/tag/0BZH)
* [Stacks Project, Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE)
* [Stacks Project, Tag 0BZJ](https://stacks.math.columbia.edu/tag/0BZJ)
* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [Stacks Project, Tag 0BYK](https://stacks.math.columbia.edu/tag/0BYK)
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial CochainComplex.DerivedTensor

-- `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` installs a locally small model of
-- `D(Mod R)` as a global instance, and the statements imported here are all read at the standard
-- model; the priority settles which of the two a bare `DerivedCategory (ModuleCat R)` means.
attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing.InvertibleKernel

/-! ### The tensor factor of Stacks 0BZH at a kernel free of rank one -/

section FreeKernel

variable {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]

/-- **The inverse of the conormal module of a surjection whose kernel is free of rank one is the
target ring.** A basis of the kernel `I` gives `I ⊗_S T ≅ T`, and the `T`-linear dual of `T` is
`T`. -/
def conormalInverseEquivSelf (eI : RingHom.ker (algebraMap S T) ≃ₗ[S] S) :
    conormalInverse.{u, u} S T ≃ₗ[T] T :=
  let e : conormal.{u, u} S T ≃ₗ[T] T :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl T T)
        (ULift.moduleEquiv.trans eI)).trans
      (TensorProduct.AlgebraTensorModule.rid S T T)
  (e.arrowCongr (LinearEquiv.refl T T)).trans (LinearMap.ringLmapEquivSelf T T T)

/-- When the kernel is free of rank one, the tensor factor `N[-1]` of Stacks 0BZH is the monoidal
unit of the complexes of `T`-modules, shifted by `-1`. -/
def conormalInverseShiftIsoUnitShift (eI : RingHom.ker (algebraMap S T) ≃ₗ[S] S) :
    conormalInverseShift.{u, u} S T ≅
      (shiftFunctor (CochainComplex (ModuleCat.{u} T) ℤ) (-1 : ℤ)).obj
        (Stacks0BZE.unitComplex.{u, u} T) :=
  (shiftFunctor (CochainComplex (ModuleCat.{u} T) ℤ) (-1 : ℤ)).mapIso
    ((CochainComplex.singleFunctor (ModuleCat.{u} T) 0).mapIso
      (((conormalInverseEquivSelf eI).trans
        (ULift.moduleEquiv (R := T) (M := T)).symm)).toModuleIso)

end FreeKernel

/-! ### Derived tensoring with the unit is derived extension of scalars -/

/-- **Derived tensoring along `f` with the monoidal unit of the complexes of `A`-modules is derived
extension of scalars along `f`.** The hypothesis is only that `LF` with its counit `alpha` is a
total left derived functor of extension of scalars; in particular `f` is not assumed flat.

The derived change-of-rings bundle of Stacks 06Y6 factors its derived tensor product as derived
extension of scalars followed by derived tensoring over `A` with the tensor factor. At the unit the
second factor is the left derived functor of a functor isomorphic to the identity, hence is the
identity; and the first factor is identified with `LF` because a total left derived functor is
unique. -/
def derivedTensorUnitComplexIsoDerivedExtension {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A)
    (LF : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
    (alpha : DerivedCategory.Q ⋙ LF ⟶
      (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    (hLF : LF.IsLeftDerivedFunctor alpha
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))) :
    (canonicalDerivedTensorChangeOfRings f (Stacks0BZE.unitComplex.{u, u} A)).F ≅ LF := by
  let T := canonicalDerivedTensorChangeOfRings f (Stacks0BZE.unitComplex.{u, u} A)
  let WA := HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)
  let eU : CochainComplex.tensorRightLarge.{u, u} (Stacks0BZE.unitComplex.{u, u} A) ≅
      𝟭 (CochainComplex (ModuleCat.{u} A) ℤ) := Rig.tensorRightLargeUnitIso.{u, u} A
  let eId : DerivedCategory.Q (C := ModuleCat.{u} A) ⋙ 𝟭 _ ≅
      𝟭 (CochainComplex (ModuleCat.{u} A) ℤ) ⋙ DerivedCategory.Q := Iso.refl _
  have : (𝟭 (DerivedCategory (ModuleCat.{u} A))).IsLeftDerivedFunctor eId.hom WA :=
    Functor.isLeftDerivedFunctor_of_inverts WA _ eId
  have := T.isLeftDerivedG
  have := T.isLeftDerivedB
  let eG : 𝟭 (DerivedCategory (ModuleCat.{u} A)) ≅ T.G :=
    Functor.leftDerivedNatIso (𝟭 _) T.G eId.hom T.alphaG WA
      (Functor.isoWhiskerRight eU.symm DerivedCategory.Q)
  exact T.changeOfRings ≪≫ Functor.isoWhiskerLeft T.B eG.symm ≪≫ Functor.rightUnitor T.B ≪≫
    Functor.leftDerivedNatIso T.B LF T.alphaB alpha
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) (Iso.refl _)

/-- **The tensor side of Stacks 0BZH for a kernel free of rank one.** Derived tensoring along
`f : S → T` with the tensor factor `N[-1]` of Stacks 0BZH is derived extension of scalars along
`f`, shifted by `-1`.

The tensor factor is replaced by the shifted unit along
`Dualizing.InvertibleKernel.conormalInverseShiftIsoUnitShift`, which is legitimate because derived
tensoring depends on the factor only through its class in `D(T)` (Stacks 0BYK); the shift is then
moved out past the derived tensor functor, and the unit factor is
`Dualizing.InvertibleKernel.derivedTensorUnitComplexIsoDerivedExtension`.

This is private because the shift identification it uses is private to
`StacksFrontier/RingTheory/Dualizing/UpperShriek/DerivedTensor.lean`;
`Dualizing.InvertibleKernel.nonempty_derivedTensorConormalInverseShiftIso` is the public form. -/
private def derivedTensorConormalInverseShiftIso
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (eI : RingHom.ker (algebraMap S T) ≃ₗ[S] S)
    (LF : DerivedCategory (ModuleCat.{u} S) ⥤ DerivedCategory (ModuleCat.{u} T))
    (alpha : DerivedCategory.Q ⋙ LF ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap S T)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (hLF : LF.IsLeftDerivedFunctor alpha
      (HomologicalComplex.quasiIso (ModuleCat.{u} S) (ComplexShape.up ℤ))) :
    (canonicalDerivedTensorChangeOfRings (algebraMap S T)
        (conormalInverseShift.{u, u} S T)).F ≅
      LF ⋙ shiftFunctor (DerivedCategory (ModuleCat.{u} T)) (-1 : ℤ) :=
  derivedTensorIsoOfDerivedIso.{u, u} (algebraMap S T)
      (DerivedCategory.Q.mapIso (conormalInverseShiftIsoUnitShift eI)) _ _ ≪≫
    (Dualizing.derivedTensorPostcomposeShiftIso.{u, u} (algebraMap S T)
      (Stacks0BZE.unitComplex.{u, u} T) _ (-1 : ℤ) rfl).symm ≪≫
    Functor.isoWhiskerRight
      (derivedTensorUnitComplexIsoDerivedExtension (algebraMap S T) LF alpha hLF)
      (shiftFunctor (DerivedCategory (ModuleCat.{u} T)) (-1 : ℤ))

/-- **The tensor side of Stacks 0BZH for a kernel free of rank one.** The public form of
`Dualizing.InvertibleKernel.derivedTensorConormalInverseShiftIso`: derived tensoring along
`f : S → T` with the tensor factor `N[-1]` of Stacks 0BZH is derived extension of scalars along
`f`, shifted by `-1`, whenever the kernel of `f` is free of rank one. -/
theorem nonempty_derivedTensorConormalInverseShiftIso
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (eI : RingHom.ker (algebraMap S T) ≃ₗ[S] S)
    (LF : DerivedCategory (ModuleCat.{u} S) ⥤ DerivedCategory (ModuleCat.{u} T))
    (alpha : DerivedCategory.Q ⋙ LF ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap S T)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (hLF : LF.IsLeftDerivedFunctor alpha
      (HomologicalComplex.quasiIso (ModuleCat.{u} S) (ComplexShape.up ℤ))) :
    Nonempty ((canonicalDerivedTensorChangeOfRings (algebraMap S T)
        (conormalInverseShift.{u, u} S T)).F ≅
      LF ⋙ shiftFunctor (DerivedCategory (ModuleCat.{u} T)) (-1 : ℤ)) :=
  ⟨derivedTensorConormalInverseShiftIso eI LF alpha hLF⟩

/-- **The model-free conclusion of Stacks 0BZH, read at a kernel free of rank one, gives the
shifted-extension form.** Stacks 0BZH asserts only that `RHom_S(T, -)` *is isomorphic to*
`K ↦ K ⊗ᴸ_S N[-1]`; no canonical map is part of its statement. Given any such isomorphism, and a
basis of the kernel, derived coextension of scalars is any total left derived functor of extension
of scalars, shifted by `-1`.

The second factor is `Dualizing.InvertibleKernel.nonempty_derivedTensorConormalInverseShiftIso`.
-/
theorem nonempty_derivedHom_iso_shiftedDerivedExtension_of_freeKernel
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (eI : RingHom.ker (algebraMap S T) ≃ₗ[S] S)
    (LF : DerivedCategory (ModuleCat.{u} S) ⥤ DerivedCategory (ModuleCat.{u} T))
    (alpha : DerivedCategory.Q ⋙ LF ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap S T)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (hLF : LF.IsLeftDerivedFunctor alpha
      (HomologicalComplex.quasiIso (ModuleCat.{u} S) (ComplexShape.up ℤ)))
    (hBZH : Nonempty (Dualizing.derivedHom.{u, u} (algebraMap S T) ≅
      (canonicalDerivedTensorChangeOfRings (algebraMap S T)
        (conormalInverseShift.{u, u} S T)).F)) :
    Nonempty (Dualizing.derivedHom.{u, u} (algebraMap S T) ≅
      LF ⋙ shiftFunctor (DerivedCategory (ModuleCat.{u} T)) (-1 : ℤ)) :=
  hBZH.map (· ≪≫ derivedTensorConormalInverseShiftIso eI LF alpha hLF)

end Dualizing.InvertibleKernel

namespace Dualizing

/-- **`Dualizing.PolynomialEvalDuality` follows from the model-free conclusion of Stacks 0BZH at
the evaluation surjections, and from nothing else.**

The hypothesis is only that the two functors of Stacks 0BZH *are isomorphic* at each evaluation
surjection `S[x] ↠ S`, which is what the tag asserts. In particular neither
`Dualizing.PolynomialEvalDuality` nor Stacks 0BZH needs the canonical comparison morphism
`Stacks0BZE.comparison`; see `Dualizing.polynomialEvalDuality_of_isIso_comparison` for the weaker
reduction that does go through it.

The kernel of an evaluation map is generated by the nonzerodivisor `x - b`, hence free of rank one,
so `Dualizing.InvertibleKernel.nonempty_derivedHom_iso_shiftedDerivedExtension_of_freeKernel`
turns the hypothesis into the conclusion of `Dualizing.PolynomialEvalDuality`; the translation of
the universal property from the homotopy category to complexes is the only other step. -/
theorem polynomialEvalDuality_of_nonempty_derivedHom_iso
    (hBZH : ∀ (S : Type u) [CommRing S] (c : S) [Algebra S[X] S],
      algebraMap S[X] S = Polynomial.evalRingHom c →
      Nonempty (derivedHom.{u, u} (algebraMap S[X] S) ≅
        (canonicalDerivedTensorChangeOfRings (algebraMap S[X] S)
          (InvertibleKernel.conormalInverseShift.{u, u} S[X] S)).F)) :
    PolynomialEvalDuality.{u} := by
  intro B _ b LF alpha hLF
  let : Algebra B[X] B := (Polynomial.evalRingHom b).toAlgebra
  have hmap : algebraMap B[X] B = Polynomial.evalRingHom b := rfl
  let eI : RingHom.ker (algebraMap B[X] B) ≃ₗ[B[X]] B[X] :=
    (LinearEquiv.ofEq _ _ (hmap ▸ Polynomial.ker_evalRingHom b)).trans
      (InvertibleKernel.spanSingletonEquiv (X - C b)
        fun _ h => (monic_X_sub_C b).mul_left_eq_zero_iff.mp h).symm
  let alphaQ := Independence.homotopyCategoryDerivedComparison
    (ModuleCat.extendScalars.{u, u, u} (algebraMap B[X] B)) LF alpha
  have : LF.IsLeftDerivedFunctor alpha
      (HomotopyCategory.quasiIso (ModuleCat.{u} B[X]) (ComplexShape.up ℤ)) := hLF
  have hLFQ : LF.IsLeftDerivedFunctor alphaQ
      (HomologicalComplex.quasiIso (ModuleCat.{u} B[X]) (ComplexShape.up ℤ)) :=
    Independence.leftDerivedFunctor_of_homotopyCategory
      (ModuleCat.extendScalars.{u, u, u} (algebraMap B[X] B)) LF alpha
  exact InvertibleKernel.nonempty_derivedHom_iso_shiftedDerivedExtension_of_freeKernel
    eI LF alphaQ hLFQ (hBZH B b hmap)

/-- **`Dualizing.PolynomialEvalDuality` follows from the bundle-shape conclusion of Stacks 0BZE at
the evaluation surjections, and from nothing else.**

The hypothesis is Stacks 0BZE in the bundle shape: derived coextension of scalars along the
evaluation surjection is isomorphic to the canonical derived change-of-rings tensor product of
Stacks 06Y6 with the chosen representative `Stacks0BZE.dualComplex` of `RHom_{S[x]}(S, S[x])` —
that is, to `(Stacks0BZE.bundle _).F`. No comparison morphism is pinned: unlike
`Dualizing.polynomialEvalDuality_of_isIso_comparison`, this does not ask that
`Stacks0BZE.comparison` be the isomorphism.

This is the adapter between the two spellings of the tensor factor. The chosen representative of
`RHom_{S[x]}(S, S[x])` is replaced by the conormal inverse shift `N[-1]` along
`Dualizing.InvertibleKernel.derivedHomUnitObjectIsoSingle`, which is legitimate because derived
tensoring depends on the factor only through its class in `D(S)` (Stacks 0BYK, in the bundle form
`Dualizing.InvertibleKernel.derivedTensorIsoOfDerivedIso`); the kernel of an evaluation map is
generated by the nonzerodivisor `x - b`, so the hypotheses of Stacks 0BZH are met and
`Dualizing.polynomialEvalDuality_of_nonempty_derivedHom_iso` finishes. -/
theorem polynomialEvalDuality_of_nonempty_bundle_iso
    (hBZE : ∀ (S : Type u) [CommRing S] (c : S) [Algebra S[X] S],
      algebraMap S[X] S = Polynomial.evalRingHom c →
      Nonempty (derivedHom.{u, u} (algebraMap S[X] S) ≅
        (Stacks0BZE.bundle.{u, u} (algebraMap S[X] S)).F)) :
    PolynomialEvalDuality.{u} := by
  refine polynomialEvalDuality_of_nonempty_derivedHom_iso (fun S _ c _ hmap => ?_)
  obtain ⟨hf, hI⟩ := InvertibleKernel.surjective_and_invertible_ker_evalRingHom c hmap
  obtain ⟨e⟩ := hBZE S c hmap
  exact ⟨e ≪≫ InvertibleKernel.derivedTensorIsoOfDerivedIso.{u, u} (algebraMap S[X] S)
    (Stacks0BZE.dualComplexIso.{u, u} (algebraMap S[X] S) ≪≫
      InvertibleKernel.derivedHomUnitObjectIsoSingle.{u, u} hf hI ≪≫
      (InvertibleKernel.conormalInverseShiftIso.{u, u} S[X] S).symm)
    (Stacks0BZE.bundle.{u, u} (algebraMap S[X] S)) _⟩

/-- **`Dualizing.PolynomialEvalDuality` follows from Stacks 0BZE at the evaluation surjections**,
in the form of invertibility of `Stacks0BZE.comparison` at every K-flat complex.

That hypothesis pins the model, which is more than Stacks 0BZH asks for. The proof feeds
`Dualizing.InvertibleKernel.derivedHomIsoCanonicalDerivedTensorConormalInverseShift` into
`Dualizing.polynomialEvalDuality_of_nonempty_derivedHom_iso`. -/
theorem polynomialEvalDuality_of_isIso_comparison
    (hBZE : ∀ (S : Type u) [CommRing S] (c : S)
      (K : CochainComplex (ModuleCat.{u} S[X]) ℤ) (hK : CochainComplex.KFlat.{u, u} K),
      IsIso (Stacks0BZE.comparison.{u, u} (Polynomial.evalRingHom c) K hK)) :
    PolynomialEvalDuality.{u} := by
  refine polynomialEvalDuality_of_nonempty_derivedHom_iso (fun S _ c _ hmap => ?_)
  obtain ⟨hf, hI⟩ := InvertibleKernel.surjective_and_invertible_ker_evalRingHom c hmap
  exact ⟨InvertibleKernel.derivedHomIsoCanonicalDerivedTensorConormalInverseShift.{u, u}
    hf hI (fun K hK => hmap ▸ hBZE S c K hK)⟩

end Dualizing

end
