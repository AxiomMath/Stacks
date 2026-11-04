module

public import StacksFrontier.Homology.TorAmplitude.NilpotentCertified
import all StacksFrontier.Homology.TorAmplitude.NilpotentCertified

/-!
# A Stacks 0652 certificate at a module universe independent of the ring's

`StacksDraft.TorAmplitude.CertifiedDerivedTensoring R` bundles the datum Stacks 0652 reads Tor
amplitude off: a bifunctor on `D(ModuleCat.{v} R)`, its comparison with termwise tensoring by a
module placed in degree zero, and the `Functor.IsLeftDerivedFunctor` certificate.  Its ring
universe `u` and module universe `v` are independent.

`StacksFrontier.Homology.TorAmplitude.CanonicalCertificate` constructs one, but only at `v = u`:
the canonical derived tensor product of Stacks 0BYI exists on `D(ModuleCat.{u} R)` because
`ModuleCat.{w} R` carries Mathlib's monoidal structure only when the module universe agrees with
the ring's.  Every statement quantified over a certificate at a module universe strictly larger
than the ring's was therefore of unverified non-vacuity.

This file removes that gap: for `R : Type u` and any `v`, it exhibits a certificate at module
universe `max u v`.

## Main definitions

* `StacksDraft.TorAmplitude.unliftedCanonicalTensor`: the canonical derived tensor product of the
  lifted ring `ULift.{v} R`, transported along the equivalence of derived categories induced by
  the change of coefficient ring `StacksDraft.TorAmplitude.scalarLift`.
* `StacksDraft.TorAmplitude.unliftedCanonicalComparison`: its comparison with termwise tensoring.
* `StacksDraft.TorAmplitude.mixedCertifiedDerivedTensoring`: the certificate
  `CertifiedDerivedTensoring.{u, max u v} R`.

## Main results

* `StacksDraft.TorAmplitude.unliftedCanonicalComparison_isLeftDerived`: the comparison exhibits
  each `- ⊗ᴸ M[0]` as the total left derived functor of `- ⊗ M`, which is the third field of the
  certificate.
* `StacksDraft.TorAmplitude.hasTorAmplitudeIn_mixedCertified_iff`: Tor amplitude read off the
  certificate is the canonical Tor amplitude of the lifted ring, transported.  This is the check
  that the transported datum computes the intended derived tensor product and not some other
  functor with the same universal property on paper.
* `StacksDraft.TorAmplitude.moduleHasFiniteTorDimension_mixedCertified_of_flat`: a flat module has
  finite Tor dimension at this certificate, so the finite-Tor-dimension condition read off it is
  satisfiable and not merely well-typed.
* `StacksDraft.TorAmplitude.hasTorAmplitudeIn_derivedExtensionScalars_mixed_iff`: Stacks 0H75 with
  both certificates supplied, so that nothing in its statement is quantified over an unexhibited
  structure.

## Implementation notes

`scalarLift` restricts scalars along `ULift.ringEquiv : ULift.{v} R ≃+* R`, carrying
`ModuleCat.{max u v} R` to `ModuleCat.{max u v} (ULift.{v} R)`.  The module universe is unchanged;
what changes is that the target ring lives in the universe of its own modules, so the canonical
derived tensor product of Stacks 0BYI is available over it.  The construction here is that
transport read backwards:

* `scalarLift` is an equivalence of module categories, hence of cochain complexes, hence of
  derived categories — all three instances are in
  `StacksFrontier.Homology.TorAmplitude.DerivedComparison` — so `unliftedCanonicalTensor` is obtained
  by precomposing both variables of the canonical bifunctor with `scalarLift.mapDerivedCategory`
  and postcomposing with its inverse.
* the universal property survives both operations.  Precomposition with the equivalence is
  `CategoryTheory.Functor.isRightKanExtension_iff_precomp_equivalence`, applied to the square
  `scalarLift.mapHomologicalComplex ⋙ Q ≅ Q ⋙ scalarLift.mapDerivedCategory`, which is the
  defining property `Functor.mapDerivedCategoryFactors` of the induced functor.  Postcomposition
  with the inverse is the Mathlib instance for postcomposing a left derived functor with a right
  adjoint.
* the two ends are then matched to the shape the certificate asks for by
  `CategoryTheory.Functor.isRightKanExtension_iff_of_iso₂`: on the source by
  `Functor.mapDerivedCategorySingleFunctor`, which identifies the image of `M[0]` with
  `(scalarLift.obj M)[0]`; on the target by `StacksDraft.TorAmplitude.tensorScalarLiftIso`, which
  says ordinary tensoring commutes with the change of coefficient ring.

Nothing here raises a `set_option`, and nothing is proved about the canonical derived tensor
product that `StacksFrontier.Homology.TorAmplitude.CanonicalCertificate` had not already proved: the
whole content is the transport.

No `@[stacks]` attribute is attached to anything in this file.  Stacks 0652 is registered by
`StacksFrontier.Homology.TorAmplitude.Defs`, Stacks 0BYI by
`StacksFrontier.Homology.Tor.DerivedTensor` and Stacks 0H75 by
`StacksFrontier.Homology.TorAmplitude.NilpotentCertified`; this file supplies a witness for a
structure those statements quantify over and states no new source result.

## References

* [Stacks Project, Tag 0652](https://stacks.math.columbia.edu/tag/0652)
* [Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
* [Stacks Project, Tag 0H75](https://stacks.math.columbia.edu/tag/0H75)
-/

open CategoryTheory CategoryTheory.Functor CochainComplex.DerivedTensor

namespace StacksDraft.TorAmplitude

universe u v w

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-! ### The coefficient change on derived categories -/

/-- Tensoring with the module `N` placed in degree zero, in the canonical derived tensor product
of Stacks 0BYI over the lifted ring.  This is the functor whose universal property is transported
below. -/
public noncomputable abbrev liftedCanonTensorMod (N : ModuleCat.{max u v} (ULift.{v} R)) :
    DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)) ⥤
      DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)) :=
  (canonicalDerivedTensorProduct (ULift.{v} R)).tensor.flip.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).obj N)

/-! ### The transported bifunctor -/

/-- **The canonical derived tensor product of the lifted ring, transported back to `R`.** For
`R : Type u` and any `v`, this is a bifunctor on `D(ModuleCat.{max u v} R)`: precompose both
variables of the canonical derived tensor product of `ULift.{v} R` with the coefficient change and
postcompose with its inverse.

Mathlib's monoidal structure on `ModuleCat.{max u v} R` is unavailable for `v` outside `u`, which
is why the canonical construction cannot be performed on `R` itself; the coefficient change moves
the ring into the module universe without changing the module categories up to equivalence. -/
public noncomputable def unliftedCanonicalTensor (R : Type u) [CommRing R] :
    DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory (ModuleCat.{max u v} R) ⥤
      DerivedCategory (ModuleCat.{max u v} R) :=
  scalarLiftDerived.{u, v} (R := R) ⋙ (canonicalDerivedTensorProduct (ULift.{v} R)).tensor ⋙
    ((whiskeringLeft (DerivedCategory (ModuleCat.{max u v} R))
        (DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)))
        (DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)))).obj
          (scalarLiftDerived.{u, v} (R := R)) ⋙
      (whiskeringRight (DerivedCategory (ModuleCat.{max u v} R))
        (DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)))
        (DerivedCategory (ModuleCat.{max u v} R))).obj
          (scalarLiftDerived.{u, v} (R := R)).inv)

/-! ### Transporting the universal property

The three steps are the three isomorphisms and the two transport lemmas described in the
implementation notes.  Everything in this section is auxiliary to
`unliftedCanonicalComparison_isLeftDerived`. -/

/-- The canonical comparison over the lifted ring, precomposed with the coefficient change on
derived categories.  Its target is the termwise tensor product over the lifted ring, read on
complexes over `R`. -/
private noncomputable def scalarLiftPrecomposedComparison (M : ModuleCat.{max u v} R) :
    DerivedCategory.Q ⋙ (scalarLiftDerived.{u, v} (R := R) ⋙
        liftedCanonTensorMod.{u, v} ((scalarLift.{u, v} (R := R)).obj M)) ⟶
      (scalarLift.{u, v} (R := R)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (tensorModuleRight ((scalarLift.{u, v} (R := R)).obj M)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).inv ≫
    whiskerRight (scalarLift.{u, v} (R := R)).mapDerivedCategoryFactors.hom
      (liftedCanonTensorMod.{u, v} ((scalarLift.{u, v} (R := R)).obj M)) ≫
    (Functor.associator _ _ _).hom ≫
    whiskerLeft _ (canonicalTensorComparison (ULift.{v} R) ((scalarLift.{u, v} (R := R)).obj M))

/-- Precomposition with the coefficient change preserves the universal property: the coefficient
change is an equivalence on complexes and on derived categories, and the square relating the two
is `Functor.mapDerivedCategoryFactors`. -/
private instance scalarLiftPrecomposedComparison_isLeftDerived (M : ModuleCat.{max u v} R) :
    (scalarLiftDerived.{u, v} (R := R) ⋙
        liftedCanonTensorMod.{u, v} ((scalarLift.{u, v} (R := R)).obj M)).IsLeftDerivedFunctor
      (scalarLiftPrecomposedComparison.{u, v} M)
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) := by
  rw [isLeftDerivedFunctor_iff_isRightKanExtension]
  refine (isRightKanExtension_iff_precomp_equivalence
    (scalarLiftPrecomposedComparison.{u, v} M)
    (canonicalTensorComparison (ULift.{v} R) ((scalarLift.{u, v} (R := R)).obj M))
    (G := (scalarLift.{u, v} (R := R)).mapHomologicalComplex (ComplexShape.up ℤ))
    (G' := scalarLiftDerived.{u, v} (R := R))
    (scalarLift.{u, v} (R := R)).mapDerivedCategoryFactors.symm (Iso.refl _) (Iso.refl _) ?_).1 ?_
  · simp [scalarLiftPrecomposedComparison]
  · rw [← isLeftDerivedFunctor_iff_isRightKanExtension _ _
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} (ULift.{v} R)) (ComplexShape.up ℤ))]
    infer_instance

/-- Termwise tensoring commutes with the coefficient change, read on cochain complexes and
followed by the localization.  This is `tensorScalarLiftIso` applied termwise, glued to
`Functor.mapDerivedCategoryFactors`. -/
private noncomputable def scalarLiftTermwiseSquare (M : ModuleCat.{max u v} R) :
    ((tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
        scalarLiftDerived.{u, v} (R := R) ≅
      (scalarLift.{u, v} (R := R)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (tensorModuleRight ((scalarLift.{u, v} (R := R)).obj M)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (scalarLift.{u, v} (R := R)).mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso (tensorScalarLiftIso.{u, v} M)
          (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso
          (Iso.refl (scalarLift.{u, v} (R := R) ⋙
            tensorModuleRight ((scalarLift.{u, v} (R := R)).obj M)))
          (ComplexShape.up ℤ)).symm) _ ≪≫
    Functor.associator _ _ _

/-- The target of the transported comparison, identified with termwise tensoring by `M` over `R`:
cancel the coefficient change against its inverse in `scalarLiftTermwiseSquare`. -/
private noncomputable def scalarUnliftTermwiseIso (M : ModuleCat.{max u v} R) :
    ((scalarLift.{u, v} (R := R)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (tensorModuleRight ((scalarLift.{u, v} (R := R)).obj M)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
        (scalarLiftDerived.{u, v} (R := R)).inv ≅
      (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  isoWhiskerRight (scalarLiftTermwiseSquare.{u, v} M).symm
      (scalarLiftDerived.{u, v} (R := R)).inv ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (scalarLiftDerived.{u, v} (R := R)).asEquivalence.unitIso.symm ≪≫
    Functor.rightUnitor _

/-- The source of the transported comparison, identified with the second variable of
`unliftedCanonicalTensor` at `M[0]`: the coefficient change carries `M[0]` to
`(scalarLift.obj M)[0]`, by `Functor.mapDerivedCategorySingleFunctor`. -/
private noncomputable def unliftedCanonicalTensorFlipIso (M : ModuleCat.{max u v} R) :
    (scalarLiftDerived.{u, v} (R := R) ⋙
        liftedCanonTensorMod.{u, v} ((scalarLift.{u, v} (R := R)).obj M)) ⋙
        (scalarLiftDerived.{u, v} (R := R)).inv ≅
      (unliftedCanonicalTensor.{u, v} R).flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M) :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (scalarLiftDerived.{u, v} (R := R))
      (isoWhiskerRight
        ((canonicalDerivedTensorProduct (ULift.{v} R)).tensor.flip.mapIso
          (((scalarLift.{u, v} (R := R)).mapDerivedCategorySingleFunctor 0).app M).symm)
        (scalarLiftDerived.{u, v} (R := R)).inv) ≪≫
    Iso.refl _

/-- Whiskering an isomorphism and its inverse on the left cancels. -/
public lemma whiskerLeft_hom_inv_comp {C D H : Type*} [Category C] [Category D] [Category H]
    (L : C ⥤ D) {F G : D ⥤ H} (e : F ≅ G) {X : C ⥤ H} (f : L ⋙ F ⟶ X) :
    whiskerLeft L e.hom ≫ whiskerLeft L e.inv ≫ f = f := by
  rw [← Category.assoc, ← Functor.whiskerLeft_comp, Iso.hom_inv_id, Functor.whiskerLeft_id',
    Category.id_comp]

/-! ### The certificate -/

/-- **The comparison map of `unliftedCanonicalTensor` with termwise tensoring.** For a module `M`
in `ModuleCat.{max u v} R`, the natural transformation from `- ⊗ᴸ M[0]`, read on complexes through
the localization `Q`, to termwise tensoring by `M` followed by `Q`.

It is the canonical comparison of the lifted ring, transported along the coefficient change, with
its two ends matched to the spelling over `R`. -/
public noncomputable def unliftedCanonicalComparison (M : ModuleCat.{max u v} R) :
    DerivedCategory.Q ⋙ (unliftedCanonicalTensor.{u, v} R).flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M) ⟶
      (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  whiskerLeft DerivedCategory.Q (unliftedCanonicalTensorFlipIso.{u, v} M).inv ≫
    ((Functor.associator _ _ _).inv ≫
      whiskerRight (scalarLiftPrecomposedComparison.{u, v} M)
        (scalarLiftDerived.{u, v} (R := R)).inv) ≫ (scalarUnliftTermwiseIso.{u, v} M).hom

/-- **The universal property, transported.** Tensoring with `M[0]` in `unliftedCanonicalTensor` is
the total left derived functor of termwise tensoring by `M`, with counit
`unliftedCanonicalComparison`.

The coefficient change is an equivalence, so precomposing with it preserves the property and
postcomposing with its inverse — a right adjoint — preserves it as well. -/
public instance unliftedCanonicalComparison_isLeftDerived (M : ModuleCat.{max u v} R) :
    ((unliftedCanonicalTensor.{u, v} R).flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M)).IsLeftDerivedFunctor
      (unliftedCanonicalComparison.{u, v} M)
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) := by
  have h0 : ((scalarLiftDerived.{u, v} (R := R) ⋙
      liftedCanonTensorMod.{u, v} ((scalarLift.{u, v} (R := R)).obj M)) ⋙
      (scalarLiftDerived.{u, v} (R := R)).inv).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        whiskerRight (scalarLiftPrecomposedComparison.{u, v} M)
          (scalarLiftDerived.{u, v} (R := R)).inv)
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) :=
    inferInstance
  rw [isLeftDerivedFunctor_iff_isRightKanExtension] at h0 ⊢
  exact (isRightKanExtension_iff_of_iso₂ _ (unliftedCanonicalComparison.{u, v} M)
    (scalarUnliftTermwiseIso.{u, v} M) (unliftedCanonicalTensorFlipIso.{u, v} M)
    (whiskerLeft_hom_inv_comp DerivedCategory.Q
      (unliftedCanonicalTensorFlipIso.{u, v} M) _)).1 h0

/-- **A Stacks 0652 certificate at a module universe independent of the ring's.** For
`R : Type u` and any `v`, the three fields of `CertifiedDerivedTensoring.{u, max u v} R`: the
bifunctor `unliftedCanonicalTensor`, its comparison with termwise tensoring, and the
`Functor.IsLeftDerivedFunctor` certificate.

`StacksDraft.TorAmplitude.canonicalCertifiedDerivedTensoring` is the same datum at module universe
equal to the ring universe; this is the mixed-universe witness, and it is what makes a statement
quantified over `CertifiedDerivedTensoring.{u, max u v w} R` non-vacuous. -/
public noncomputable def mixedCertifiedDerivedTensoring (R : Type u) [CommRing R] :
    CertifiedDerivedTensoring.{u, max u v} R where
  tensor := unliftedCanonicalTensor.{u, v} R
  comparison := unliftedCanonicalComparison.{u, v}
  isLeftDerived := fun M => unliftedCanonicalComparison_isLeftDerived.{u, v} M

/-- Tor amplitude read off `mixedCertifiedDerivedTensoring` is the canonical Tor amplitude of the
lifted ring, read at the transported object.

This is the check that the transport computes the intended derived tensor product: the certificate
is not merely *a* structure of the right type, it is the canonical derived tensor product of
Stacks 0BYI moved across an equivalence, and the predicate of Stacks 0652 reads the same on both
sides. -/
public theorem hasTorAmplitudeIn_mixedCertified_iff (R : Type u) [CommRing R]
    (X : DerivedCategory (ModuleCat.{max u v} R)) (a b : ℤ) :
    (mixedCertifiedDerivedTensoring.{u, v} R).HasTorAmplitudeIn X a b ↔
      HasTorAmplitude (canonicalDerivedTensorProduct (ULift.{v} R)).tensor
        (canonicalTensorComparison (ULift.{v} R)) (canonicalTensorIsLeftDerived (ULift.{v} R))
        ((scalarLiftDerived.{u, v} (R := R)).obj X) a b :=
  ((mixedCertifiedDerivedTensoring.{u, v} R).hasTorAmplitudeIn_iff X a b).trans
    (hasTorAmplitude_iff_scalarLift.{u, v} (unliftedCanonicalTensor.{u, v} R)
      (unliftedCanonicalComparison.{u, v})
      (fun M => unliftedCanonicalComparison_isLeftDerived.{u, v} M) X a b)

/-- **A flat module has finite Tor dimension at the mixed-universe certificate.** So the
finite-Tor-dimension hypothesis of Stacks 0BZM, read at `mixedCertifiedDerivedTensoring`, is
satisfiable and not merely well-typed: it holds, with Tor amplitude in `[0, 0]`, at every flat
module.

The proof is the chain of public translations: Tor amplitude at this certificate is the canonical
Tor amplitude of the lifted ring (`hasTorAmplitudeIn_mixedCertified_iff`), the coefficient change
carries `M[0]` to `(scalarLift.obj M)[0]` (`Functor.mapDerivedCategorySingleFunctor`), Tor
amplitude in `[0, 0]` of a module over the lifted ring is its flatness
(`hasTorDimensionLECanonical_iff_hasFlatRepresentative`), and flatness is unchanged by the
coefficient change (`Module.Flat.ulift_left_iff`). -/
public theorem moduleHasFiniteTorDimension_mixedCertified_of_flat (R : Type u) [CommRing R]
    (M : ModuleCat.{max u v} R) (hM : Module.Flat R M) :
    ModuleHasFiniteTorDimension (mixedCertifiedDerivedTensoring.{u, v} R).tensor
      (mixedCertifiedDerivedTensoring.{u, v} R).comparison
      (mixedCertifiedDerivedTensoring.{u, v} R).isLeftDerived M := by
  refine ⟨0, 0, ?_⟩
  refine (hasTorAmplitudeIn_mixedCertified_iff.{u, v} R
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M) 0 0).2 ?_
  refine (hasTorAmplitude_of_iso
    (((scalarLift.{u, v} (R := R)).mapDerivedCategorySingleFunctor 0).app M) 0 0).2 ?_
  refine (hasTorAmplitudeIn_iff_hasTorAmplitude (canonicalDerivedTensorProduct (ULift.{v} R))
    (canonicalTensorComparison (ULift.{v} R)) (canonicalTensorIsLeftDerived (ULift.{v} R))
    _ 0 0).1 ?_
  refine (hasTorAmplitudeIn_canonical_iff (ULift.{v} R) _ 0 0).2 ?_
  refine ((hasTorDimensionLECanonical_iff_hasFlatRepresentative (ULift.{v} R)
    ((scalarLift.{u, v} (R := R)).obj M) 0).2).2 ?_
  show Module.Flat (ULift.{v} R) (M : Type (max u v))
  rw [Module.Flat.ulift_left_iff]
  exact hM

/-- **Stacks 0H75 with both certificates supplied.** Let `f : R' → R` be a surjective map of
commutative rings with nilpotent kernel and let `L` be the derived base change along `f`.  For
every object `K` of `D(R')` and every finite interval `[a, b]`, the object `L.obj K` has Tor
amplitude in `[a, b]` if and only if `K` does — with both Tor amplitudes read off the
mixed-universe certificates of this file rather than off quantified ones.

`StacksDraft.TorAmplitude.hasTorAmplitudeIn_derivedExtensionScalars_certified_iff` is the
statement with the two certificates quantified; the universes of `R'`, of `R` and of the module
carriers are independent there, so until now nothing exhibited either certificate. -/
public theorem hasTorAmplitudeIn_derivedExtensionScalars_mixed_iff
    {R' : Type u} {R : Type v} [CommRing R'] [CommRing R] (f : R' →+* R)
    (hf : Function.Surjective f) (hnil : IsNilpotent (RingHom.ker f))
    (L : DerivedCategory (ModuleCat.{max u v w} R') ⥤ DerivedCategory (ModuleCat.{max u v w} R))
    (comparison : DerivedCategory.Q (C := ModuleCat.{max u v w} R') ⋙ L ⟶
      (ModuleCat.extendScalars.{u, v, max u v w} f).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q (C := ModuleCat.{max u v w} R))
    [L.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max u v w} R') (ComplexShape.up ℤ))]
    (K : DerivedCategory (ModuleCat.{max u v w} R')) (a b : ℤ) :
    (mixedCertifiedDerivedTensoring.{v, max u w} R).HasTorAmplitudeIn (L.obj K) a b ↔
      (mixedCertifiedDerivedTensoring.{u, max v w} R').HasTorAmplitudeIn K a b :=
  hasTorAmplitudeIn_derivedExtensionScalars_certified_iff.{u, v, w} f hf hnil L comparison
    (mixedCertifiedDerivedTensoring.{u, max v w} R')
    (mixedCertifiedDerivedTensoring.{v, max u w} R) K a b

end StacksDraft.TorAmplitude
