module

public import Mathlib.Algebra.Ring.Shrink
public import StacksFrontier.Homology.TorAmplitude.MixedUniverseCertificate

/-!
# A Stacks 0652 certificate at a module universe that need not contain the ring's

`StacksDraft.TorAmplitude.CertifiedDerivedTensoring R` bundles the datum Stacks 0652 reads Tor
amplitude off: a bifunctor on `D(ModuleCat.{v} R)`, its comparison with termwise tensoring by a
module placed in degree zero, and the `Functor.IsLeftDerivedFunctor` certificate.  Its ring
universe `u` and module universe `v` are independent.

`StacksFrontier.Homology.TorAmplitude.CanonicalCertificate` constructs one at `v = u`, and
`StacksFrontier.Homology.TorAmplitude.MixedUniverseCertificate` one at `v = max u w`.  Both leave
the module universes *below* the ring universe untouched: a statement quantified over
`CertifiedDerivedTensoring.{u, w} R` with `w` unrelated to `u` was still of unverified
non-vacuity.

This file removes that gap under the only hypothesis that can make it true, namely that `R` is
`w`-small: for `R : Type u` with `[Small.{w} R]` it exhibits a certificate at module universe
exactly `w`.

## Main definitions

* `StacksDraft.TorAmplitude.ringEquivLift`: change of coefficient ring along a ring equivalence
  `e : S ≃+* R`, carrying `ModuleCat.{w} R` to `ModuleCat.{w} S`.
* `StacksDraft.TorAmplitude.ringEquivCanonicalTensor`: the canonical derived tensor product of
  Stacks 0BYI over `S`, transported along `e`.
* `StacksDraft.TorAmplitude.ringEquivCertifiedDerivedTensoring`: the certificate
  `CertifiedDerivedTensoring.{u, w} R` obtained from a ring equivalence `S ≃+* R` with
  `S : Type w`.
* `StacksDraft.TorAmplitude.smallCertifiedDerivedTensoring`: the certificate
  `CertifiedDerivedTensoring.{u, w} R` for a `w`-small ring `R`, obtained from the previous one
  at `Shrink.ringEquiv R`.

## Main results

* `StacksDraft.TorAmplitude.ringEquivCanonicalComparison_isLeftDerived`: the comparison exhibits
  each `- ⊗ᴸ M[0]` as the total left derived functor of `- ⊗ M`, which is the third field of the
  certificate.
* `StacksDraft.TorAmplitude.hasTorAmplitudeIn_smallCertified_iff`: Tor amplitude read off the
  small-universe certificate is the canonical Tor amplitude of `Shrink.{w} R`, transported.  This
  is the check that the datum computes the intended derived tensor product and not some other
  functor with the same universal property on paper.
* `StacksDraft.TorAmplitude.moduleHasFiniteTorDimension_smallCertified_of_flat`: a flat module has
  finite Tor dimension at this certificate, so the finite-Tor-dimension condition read off it is
  satisfiable and not merely well-typed.

## Implementation notes

The construction is the one of
`StacksFrontier.Homology.TorAmplitude.MixedUniverseCertificate` with `ULift.ringEquiv` replaced by
an arbitrary ring equivalence, which is what lets the small ring `Shrink.{w} R` be used in place of
the large ring `ULift.{w} R`.  Everything in the first section is therefore stated for a ring
equivalence `e : S ≃+* R` with `S : Type w`; the point of the hypothesis is that `S` lives in the
universe of its own modules, so the canonical derived tensor product of Stacks 0BYI is available
over `S`, while `ModuleCat.{w} R` carries Mathlib's monoidal structure only when `w = u`.

Two things in that generalisation are *not* a transcription, because `ULift` has global instances
that an arbitrary ring equivalence does not.

* The `ULift` module category comes with `Module (ULift R) M` for every `R`-module `M`, so the
  comparison `tensorScalarLiftIso` of
  `StacksFrontier.Homology.TorAmplitude.DerivedComparison` could be read off
  `TensorProduct.equivOfCompatibleSMul` with every instance found automatically.  For a general
  `e` there is no `Module S M`, only the restricted structure on the *object*
  `(ringEquivLift e).obj M`, and the three instances
  `TensorProduct.CompatibleSMul` needs — `smulCommClass_ringEquivLift`,
  `compatibleSMul_ringEquivLift_base` and `compatibleSMul_ringEquivLift_lift` — have to be
  supplied.  They are proved here and used as local instances.
* Flatness transports by `Module.Flat.ulift_left_iff` in the `ULift` case.  For a general `e` it
  is `flat_ringEquivLift`, proved from `Module.Flat.trans` through the algebra structure that `e`
  puts on `R` over `S`.

The transport of the universal property is unchanged from the `ULift` case: precomposition with
an equivalence is `CategoryTheory.Functor.isRightKanExtension_iff_precomp_equivalence`,
postcomposition with its inverse is Mathlib's instance for a right adjoint, and the two ends are
matched by `CategoryTheory.Functor.isRightKanExtension_iff_of_iso₂`.  Nothing here raises a
`set_option`.

No `@[stacks]` attribute is attached to anything in this file.  Stacks 0652 is registered by
`StacksFrontier.Homology.TorAmplitude.Defs` and Stacks 0BYI by
`StacksFrontier.Homology.Tor.DerivedTensor`; this file supplies a witness for a structure those
statements quantify over and states no new source result.

## References

* [Stacks Project, Tag 0652](https://stacks.math.columbia.edu/tag/0652)
* [Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
-/

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open CochainComplex.DerivedTensor

namespace StacksDraft.TorAmplitude

universe u w

attribute [local instance] HasDerivedCategory.standard

section RingEquiv

variable {R : Type u} [CommRing R] {S : Type w} [CommRing S]

/-! ### The coefficient change along a ring equivalence -/

/-- Change coefficients along a ring equivalence `e : S ≃+* R` without changing the module
carriers.  Both module categories have the same fixed universe `w`; this is an equivalence of
coefficient rings, not an enlargement of the module universe.

Its point is that `S` may live in the universe of its own modules even when `R` does not, so the
shared-universe theory of Stacks 0BYI applies over `S`. -/
public noncomputable abbrev ringEquivLift (e : S ≃+* R) :
    ModuleCat.{w} R ⥤ ModuleCat.{w} S :=
  ModuleCat.restrictScalars e.toRingHom

/-- Restricting scalars along a ring equivalence is an equivalence of module categories. -/
public instance ringEquivLift_isEquivalence (e : S ≃+* R) :
    (ringEquivLift e).IsEquivalence :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).isEquivalence_functor

/-- An equivalence of module categories induces an equivalence on cochain complexes. -/
public instance ringEquivLift_mapHomologicalComplex_isEquivalence (e : S ≃+* R) :
    ((ringEquivLift e).mapHomologicalComplex (ComplexShape.up ℤ)).IsEquivalence :=
  ((ringEquivLift e).asEquivalence.mapHomologicalComplex
    (ComplexShape.up ℤ)).isEquivalence_functor

/-- The localizer morphism of the coefficient change, between the quasi-isomorphism localizers
on cochain complexes, has an underlying functor that is an equivalence. -/
public instance ringEquivLift_localizerMorphism_functor_isEquivalence (e : S ≃+* R) :
    ((ringEquivLift e).mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).functor.IsEquivalence :=
  inferInstanceAs
    (((ringEquivLift e).mapHomologicalComplex (ComplexShape.up ℤ)).IsEquivalence)

/-- The localizer morphism of the coefficient change is induced: a map of cochain complexes over
`R` is a quasi-isomorphism exactly when its image over `S` is, because the coefficient change
preserves homology. -/
public instance ringEquivLift_localizerMorphism_isInduced (e : S ≃+* R) :
    ((ringEquivLift e).mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).IsInduced where
  inverseImage_eq := by
    ext K L f
    exact HomologicalComplex.quasiIso_map_iff_of_preservesHomology f (ringEquivLift e)

/-- The localizer morphism of the coefficient change is a localized equivalence: an induced
localizer morphism whose functor is an equivalence is one. -/
public instance ringEquivLift_localizerMorphism_isLocalizedEquivalence (e : S ≃+* R) :
    ((ringEquivLift e).mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).IsLocalizedEquivalence :=
  LocalizerMorphism.isLocalizedEquivalence_of_isInduced _

/-- Changing coefficients along a ring equivalence induces an equivalence of derived
categories. -/
public instance ringEquivLift_mapDerivedCategory_isEquivalence (e : S ≃+* R) :
    (ringEquivLift e).mapDerivedCategory.IsEquivalence := by
  let G := ringEquivLift e
  let : CatCommSq (G.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).functor DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  exact (G.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)).isEquivalence
    DerivedCategory.Q DerivedCategory.Q _

/-- The coefficient change read on derived categories.  It is an equivalence, by
`ringEquivLift_mapDerivedCategory_isEquivalence`. -/
public noncomputable abbrev ringEquivLiftDerived (e : S ≃+* R) :
    DerivedCategory (ModuleCat.{w} R) ⥤ DerivedCategory (ModuleCat.{w} S) :=
  (ringEquivLift e).mapDerivedCategory

/-! ### Termwise tensoring across the coefficient change

The three instances below are what `TensorProduct.equivOfCompatibleSMul` asks for.  In the
`ULift` case they are global; here the `S`-module structure exists only on the restricted object,
so each has to be produced from the defining property `s • x = e s • x` of that structure. -/

/-- On a module restricted along `e`, the `R`-action and the `S`-action commute: the `S`-action is
the `R`-action through `e`, and `R` is commutative. -/
public theorem smulCommClass_ringEquivLift (e : S ≃+* R) (N : ModuleCat.{w} R) :
    SMulCommClass R S ((ringEquivLift e).obj N) where
  smul_comm r s x := smul_comm r (e s) x

attribute [local instance] smulCommClass_ringEquivLift

/-- An `S`-scalar can be moved across a tensor product over `R` of modules restricted along `e`:
it acts as an `R`-scalar. -/
public theorem compatibleSMul_ringEquivLift_base (e : S ≃+* R) (N M : ModuleCat.{w} R) :
    TensorProduct.CompatibleSMul R S ((ringEquivLift e).obj N) ((ringEquivLift e).obj M) where
  smul_tmul s x y := TensorProduct.smul_tmul (R := R) (R' := R) (e s) x y

/-- An `R`-scalar can be moved across a tensor product over `S` of modules restricted along `e`:
every element of `R` is `e s` for a unique `s`, and then it acts as the `S`-scalar `s`. -/
public theorem compatibleSMul_ringEquivLift_lift (e : S ≃+* R) (N M : ModuleCat.{w} R) :
    TensorProduct.CompatibleSMul S R ((ringEquivLift e).obj N) ((ringEquivLift e).obj M) where
  smul_tmul r x y := by
    obtain ⟨s, rfl⟩ : ∃ s : S, e s = r := ⟨e.symm r, e.apply_symm_apply r⟩
    exact TensorProduct.smul_tmul (R := S) (R' := S) s x y

attribute [local instance] compatibleSMul_ringEquivLift_base compatibleSMul_ringEquivLift_lift

/-- Ordinary tensoring commutes with the change of coefficient ring: tensoring over `R` and then
restricting scalars agrees with restricting scalars and then tensoring over `S`. -/
public noncomputable def tensorRingEquivLiftIso (e : S ≃+* R) (M : ModuleCat.{w} R) :
    tensorModuleRight M ⋙ ringEquivLift e ≅
      ringEquivLift e ⋙ tensorModuleRight ((ringEquivLift e).obj M) := by
  refine NatIso.ofComponents
    (fun N => (TensorProduct.equivOfCompatibleSMul R S S
      ((ringEquivLift e).obj N : Type w)
      ((ringEquivLift e).obj M : Type w)).toModuleIso.symm)
    fun f => ModuleCat.hom_ext <| LinearMap.ext fun z => ?_
  induction z using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans
      (map_add _ x y).symm)

/-- Restriction of scalars along a ring equivalence preserves flatness.

Through `e`, the ring `R` is an `S`-algebra isomorphic to `S` as an `S`-module, hence flat, and a
flat module over a flat algebra is flat over the base. -/
public theorem flat_ringEquivLift (e : S ≃+* R) (M : ModuleCat.{w} R) (hM : Module.Flat R M) :
    Module.Flat S ((ringEquivLift e).obj M) := by
  let : Algebra S R := e.toRingHom.toAlgebra
  have : IsScalarTower S R ((ringEquivLift e).obj M) := ⟨fun s r m => mul_smul (e s) r m⟩
  have : Module.Flat S R :=
    Module.Flat.of_linearEquiv (M := S) (N := R)
      { e.symm.toEquiv with
        map_add' := e.symm.map_add
        map_smul' := fun s r => by
          change e.symm (e s * r) = s * e.symm r
          rw [map_mul, e.symm_apply_apply] }
  have : Module.Flat R ((ringEquivLift e).obj M) := hM
  exact Module.Flat.trans S R ((ringEquivLift e).obj M)

/-! ### Vanishing of derived cohomology across the coefficient change -/

/-- Vanishing of the cohomology of an object of the derived category can be read on any complex
representing it. -/
private theorem isZero_homologyFunctor_iff_isZero_homology {T : Type*} [CommRing T]
    (X : DerivedCategory (ModuleCat.{w} T)) (K : CochainComplex (ModuleCat.{w} T) ℤ)
    (ε : DerivedCategory.Q.obj K ≅ X) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} T) i).obj X) ↔
      IsZero (K.homology i) :=
  ((DerivedCategory.homologyFunctor (ModuleCat.{w} T) i).mapIso ε.symm ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{w} T) i).app K).isZero_iff

/-- The coefficient change preserves vanishing of derived cohomology: it is exact and does not
change the underlying abelian groups, so it commutes with taking cohomology. -/
public theorem ringEquivLift_map_isZero_homology (e : S ≃+* R)
    (X : DerivedCategory (ModuleCat.{w} R)) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) i).obj X)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} S) i).obj
      ((ringEquivLiftDerived e).obj X)) := by
  let G := ringEquivLift e
  let K := DerivedCategory.Q.objPreimage X
  let ε := DerivedCategory.Q.objObjPreimageIso X
  have hz : IsZero (K.homology i) := (isZero_homologyFunctor_iff_isZero_homology X K ε i).1 h
  exact (isZero_homologyFunctor_iff_isZero_homology _ ((G.mapHomologicalComplex _).obj K)
    ((G.mapDerivedCategoryFactors.app K).symm ≪≫ G.mapDerivedCategory.mapIso ε) i).2
    ((G.map_isZero hz).of_iso ((K.sc i).mapHomologyIso G))

/-- The coefficient change reflects vanishing of derived cohomology: it is full and faithful, so a
complex whose image has vanishing cohomology already had it. -/
public theorem ringEquivLift_reflects_isZero_homology (e : S ≃+* R)
    (X : DerivedCategory (ModuleCat.{w} R)) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} S) i).obj
      ((ringEquivLiftDerived e).obj X))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) i).obj X) := by
  let G := ringEquivLift e
  let K := DerivedCategory.Q.objPreimage X
  let ε := DerivedCategory.Q.objObjPreimageIso X
  have hz := (isZero_homologyFunctor_iff_isZero_homology _ ((G.mapHomologicalComplex _).obj K)
    ((G.mapDerivedCategoryFactors.app K).symm ≪≫ G.mapDerivedCategory.mapIso ε) i).1 h
  exact (isZero_homologyFunctor_iff_isZero_homology X K ε i).2
    (IsZero.of_full_of_faithful_of_isZero G _ (hz.of_iso ((K.sc i).mapHomologyIso G).symm))

/-- The coefficient change preserves and reflects vanishing of derived cohomology. -/
public theorem ringEquivLift_map_isZero_homology_iff (e : S ≃+* R)
    (X : DerivedCategory (ModuleCat.{w} R)) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} S) i).obj
      ((ringEquivLiftDerived e).obj X)) ↔
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) i).obj X) :=
  ⟨ringEquivLift_reflects_isZero_homology e X i, ringEquivLift_map_isZero_homology e X i⟩

/-- The *inverse* of the coefficient change preserves and reflects vanishing of derived
cohomology: compose `ringEquivLift_map_isZero_homology_iff` with the counit of the equivalence. -/
public theorem ringEquivLiftDerived_inv_isZero_homology_iff (e : S ≃+* R)
    (Y : DerivedCategory (ModuleCat.{w} S)) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) i).obj
      ((ringEquivLiftDerived e).inv.obj Y)) ↔
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} S) i).obj Y) :=
  (ringEquivLift_map_isZero_homology_iff e ((ringEquivLiftDerived e).inv.obj Y) i).symm.trans
    ((DerivedCategory.homologyFunctor (ModuleCat.{w} S) i).mapIso
      ((ringEquivLiftDerived e).asEquivalence.counitIso.app Y)).isZero_iff

/-! ### The transported bifunctor -/

/-- Tensoring with the module `N` placed in degree zero, in the canonical derived tensor product
of Stacks 0BYI over `S`.  This is the functor whose universal property is transported below. -/
public noncomputable abbrev canonTensorModOver (S : Type w) [CommRing S] (N : ModuleCat.{w} S) :
    DerivedCategory (ModuleCat.{w} S) ⥤ DerivedCategory (ModuleCat.{w} S) :=
  (canonicalDerivedTensorProduct S).tensor.flip.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{w} S) 0).obj N)

/-- **The canonical derived tensor product of `S`, transported to `R` along `e : S ≃+* R`.**
Precompose both variables of the canonical derived tensor product of `S` with the coefficient
change and postcompose with its inverse.

Mathlib's monoidal structure on `ModuleCat.{w} R` is unavailable unless `w` is the universe of
`R`, which is why the canonical construction cannot be performed on `R` itself; the coefficient
change moves the ring into the universe of its own modules without changing the module categories
up to equivalence. -/
public noncomputable def ringEquivCanonicalTensor (e : S ≃+* R) :
    DerivedCategory (ModuleCat.{w} R) ⥤ DerivedCategory (ModuleCat.{w} R) ⥤
      DerivedCategory (ModuleCat.{w} R) :=
  ringEquivLiftDerived e ⋙ (canonicalDerivedTensorProduct S).tensor ⋙
    ((whiskeringLeft (DerivedCategory (ModuleCat.{w} R))
        (DerivedCategory (ModuleCat.{w} S))
        (DerivedCategory (ModuleCat.{w} S))).obj (ringEquivLiftDerived e) ⋙
      (whiskeringRight (DerivedCategory (ModuleCat.{w} R))
        (DerivedCategory (ModuleCat.{w} S))
        (DerivedCategory (ModuleCat.{w} R))).obj (ringEquivLiftDerived e).inv)

/-! ### Transporting the universal property -/

/-- The canonical comparison over `S`, precomposed with the coefficient change on derived
categories.  Its target is the termwise tensor product over `S`, read on complexes over `R`. -/
private noncomputable def ringEquivPrecomposedComparison (e : S ≃+* R) (M : ModuleCat.{w} R) :
    DerivedCategory.Q ⋙ (ringEquivLiftDerived e ⋙
        canonTensorModOver S ((ringEquivLift e).obj M)) ⟶
      (ringEquivLift e).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (tensorModuleRight ((ringEquivLift e).obj M)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).inv ≫
    whiskerRight (ringEquivLift e).mapDerivedCategoryFactors.hom
      (canonTensorModOver S ((ringEquivLift e).obj M)) ≫
    (Functor.associator _ _ _).hom ≫
    whiskerLeft _ (canonicalTensorComparison S ((ringEquivLift e).obj M))

/-- Precomposition with the coefficient change preserves the universal property: the coefficient
change is an equivalence on complexes and on derived categories, and the square relating the two
is `Functor.mapDerivedCategoryFactors`. -/
private instance ringEquivPrecomposedComparison_isLeftDerived (e : S ≃+* R)
    (M : ModuleCat.{w} R) :
    (ringEquivLiftDerived e ⋙
        canonTensorModOver S ((ringEquivLift e).obj M)).IsLeftDerivedFunctor
      (ringEquivPrecomposedComparison e M)
      (HomologicalComplex.quasiIso (ModuleCat.{w} R) (ComplexShape.up ℤ)) := by
  rw [isLeftDerivedFunctor_iff_isRightKanExtension]
  refine (isRightKanExtension_iff_precomp_equivalence
    (ringEquivPrecomposedComparison e M)
    (canonicalTensorComparison S ((ringEquivLift e).obj M))
    (G := (ringEquivLift e).mapHomologicalComplex (ComplexShape.up ℤ))
    (G' := ringEquivLiftDerived e)
    (ringEquivLift e).mapDerivedCategoryFactors.symm (Iso.refl _) (Iso.refl _) ?_).1 ?_
  · simp [ringEquivPrecomposedComparison]
  · rw [← isLeftDerivedFunctor_iff_isRightKanExtension _ _
      (HomologicalComplex.quasiIso (ModuleCat.{w} S) (ComplexShape.up ℤ))]
    infer_instance

/-- Termwise tensoring commutes with the coefficient change, read on cochain complexes and
followed by the localization.  This is `tensorRingEquivLiftIso` applied termwise, glued to
`Functor.mapDerivedCategoryFactors`. -/
private noncomputable def ringEquivTermwiseSquare (e : S ≃+* R) (M : ModuleCat.{w} R) :
    ((tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
        ringEquivLiftDerived e ≅
      (ringEquivLift e).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (tensorModuleRight ((ringEquivLift e).obj M)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (ringEquivLift e).mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso (tensorRingEquivLiftIso e M)
          (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso
          (Iso.refl (ringEquivLift e ⋙
            tensorModuleRight ((ringEquivLift e).obj M)))
          (ComplexShape.up ℤ)).symm) _ ≪≫
    Functor.associator _ _ _

/-- The target of the transported comparison, identified with termwise tensoring by `M` over `R`:
cancel the coefficient change against its inverse in `ringEquivTermwiseSquare`. -/
private noncomputable def ringEquivUnliftTermwiseIso (e : S ≃+* R) (M : ModuleCat.{w} R) :
    ((ringEquivLift e).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (tensorModuleRight ((ringEquivLift e).obj M)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
        (ringEquivLiftDerived e).inv ≅
      (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  isoWhiskerRight (ringEquivTermwiseSquare e M).symm (ringEquivLiftDerived e).inv ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (ringEquivLiftDerived e).asEquivalence.unitIso.symm ≪≫
    Functor.rightUnitor _

/-- The source of the transported comparison, identified with the second variable of
`ringEquivCanonicalTensor` at `M[0]`: the coefficient change carries `M[0]` to
`((ringEquivLift e).obj M)[0]`, by `Functor.mapDerivedCategorySingleFunctor`. -/
private noncomputable def ringEquivCanonicalTensorFlipIso (e : S ≃+* R) (M : ModuleCat.{w} R) :
    (ringEquivLiftDerived e ⋙ canonTensorModOver S ((ringEquivLift e).obj M)) ⋙
        (ringEquivLiftDerived e).inv ≅
      (ringEquivCanonicalTensor e).flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj M) :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (ringEquivLiftDerived e)
      (isoWhiskerRight
        ((canonicalDerivedTensorProduct S).tensor.flip.mapIso
          (((ringEquivLift e).mapDerivedCategorySingleFunctor 0).app M).symm)
        (ringEquivLiftDerived e).inv) ≪≫
    Iso.refl _

/-! ### The certificate -/

/-- **The comparison map of `ringEquivCanonicalTensor` with termwise tensoring.** For a module `M`
in `ModuleCat.{w} R`, the natural transformation from `- ⊗ᴸ M[0]`, read on complexes through the
localization `Q`, to termwise tensoring by `M` followed by `Q`.

It is the canonical comparison over `S`, transported along the coefficient change, with its two
ends matched to the spelling over `R`. -/
public noncomputable def ringEquivCanonicalComparison (e : S ≃+* R) (M : ModuleCat.{w} R) :
    DerivedCategory.Q ⋙ (ringEquivCanonicalTensor e).flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj M) ⟶
      (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  whiskerLeft DerivedCategory.Q (ringEquivCanonicalTensorFlipIso e M).inv ≫
    ((Functor.associator _ _ _).inv ≫
      whiskerRight (ringEquivPrecomposedComparison e M)
        (ringEquivLiftDerived e).inv) ≫ (ringEquivUnliftTermwiseIso e M).hom

/-- **The universal property, transported.** Tensoring with `M[0]` in
`ringEquivCanonicalTensor` is the total left derived functor of termwise tensoring by `M`, with
counit `ringEquivCanonicalComparison`.

The coefficient change is an equivalence, so precomposing with it preserves the property and
postcomposing with its inverse — a right adjoint — preserves it as well. -/
public instance ringEquivCanonicalComparison_isLeftDerived (e : S ≃+* R)
    (M : ModuleCat.{w} R) :
    ((ringEquivCanonicalTensor e).flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj M)).IsLeftDerivedFunctor
      (ringEquivCanonicalComparison e M)
      (HomologicalComplex.quasiIso (ModuleCat.{w} R) (ComplexShape.up ℤ)) := by
  have h0 : ((ringEquivLiftDerived e ⋙
      canonTensorModOver S ((ringEquivLift e).obj M)) ⋙
      (ringEquivLiftDerived e).inv).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        whiskerRight (ringEquivPrecomposedComparison e M) (ringEquivLiftDerived e).inv)
      (HomologicalComplex.quasiIso (ModuleCat.{w} R) (ComplexShape.up ℤ)) :=
    inferInstance
  rw [isLeftDerivedFunctor_iff_isRightKanExtension] at h0 ⊢
  exact (isRightKanExtension_iff_of_iso₂ _ (ringEquivCanonicalComparison e M)
    (ringEquivUnliftTermwiseIso e M) (ringEquivCanonicalTensorFlipIso e M)
    (whiskerLeft_hom_inv_comp DerivedCategory.Q
      (ringEquivCanonicalTensorFlipIso e M) _)).1 h0

/-- **A Stacks 0652 certificate transported along a ring equivalence.** For `R : Type u` and a
ring equivalence `e : S ≃+* R` with `S : Type w`, the three fields of
`CertifiedDerivedTensoring.{u, w} R`: the bifunctor `ringEquivCanonicalTensor`, its comparison
with termwise tensoring, and the `Functor.IsLeftDerivedFunctor` certificate.

The module universe `w` is the universe of `S`, and is otherwise unrelated to the universe of
`R`. -/
public noncomputable def ringEquivCertifiedDerivedTensoring (e : S ≃+* R) :
    CertifiedDerivedTensoring.{u, w} R where
  tensor := ringEquivCanonicalTensor e
  comparison := ringEquivCanonicalComparison e
  isLeftDerived := fun M => ringEquivCanonicalComparison_isLeftDerived e M

/-- Tor amplitude read off `ringEquivCertifiedDerivedTensoring` is the canonical Tor amplitude
of `S`, read at the transported object.

This is the check that the transport computes the intended derived tensor product: the
certificate is not merely *a* structure of the right type, it is the canonical derived tensor
product of Stacks 0BYI moved across an equivalence, and the predicate of Stacks 0652 reads the
same on both sides. -/
public theorem hasTorAmplitudeIn_ringEquivCertified_iff (e : S ≃+* R)
    (X : DerivedCategory (ModuleCat.{w} R)) (a b : ℤ) :
    (ringEquivCertifiedDerivedTensoring e).HasTorAmplitudeIn X a b ↔
      HasTorAmplitude (canonicalDerivedTensorProduct S).tensor
        (canonicalTensorComparison S) (canonicalTensorIsLeftDerived S)
        ((ringEquivLiftDerived e).obj X) a b := by
  have hM : ∀ (M : ModuleCat.{w} R) (i : ℤ),
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) i).obj
          (((ringEquivCanonicalTensor e).obj X).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj M))) ↔
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} S) i).obj
          (((canonicalDerivedTensorProduct S).tensor.obj
              ((ringEquivLiftDerived e).obj X)).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{w} S) 0).obj
              ((ringEquivLift e).obj M)))) := fun M i =>
    (ringEquivLiftDerived_inv_isZero_homology_iff e _ i).trans
      ((DerivedCategory.homologyFunctor (ModuleCat.{w} S) i).mapIso
        (((canonicalDerivedTensorProduct S).tensor.obj
            ((ringEquivLiftDerived e).obj X)).mapIso
          (((ringEquivLift e).mapDerivedCategorySingleFunctor 0).app M))).isZero_iff
  refine ⟨fun h N i hi => ((hM ((ringEquivLift e).objPreimage N) i).1 (h _ i hi)).of_iso ?_,
    fun h M i hi => (hM M i).2 (h _ i hi)⟩
  exact ((DerivedCategory.homologyFunctor (ModuleCat.{w} S) i).mapIso
    (((canonicalDerivedTensorProduct S).tensor.obj
        ((ringEquivLiftDerived e).obj X)).mapIso
      ((DerivedCategory.singleFunctor (ModuleCat.{w} S) 0).mapIso
        ((ringEquivLift e).objObjPreimageIso N)))).symm

/-- **A flat module has finite Tor dimension at the transported certificate.** So the
finite-Tor-dimension hypothesis of Stacks 0BZM, read at
`ringEquivCertifiedDerivedTensoring`, is satisfiable and not merely well-typed: it holds, with
Tor amplitude in `[0, 0]`, at every flat module. -/
public theorem moduleHasFiniteTorDimension_ringEquivCertified_of_flat (e : S ≃+* R)
    (M : ModuleCat.{w} R) (hM : Module.Flat R M) :
    ModuleHasFiniteTorDimension (ringEquivCertifiedDerivedTensoring e).tensor
      (ringEquivCertifiedDerivedTensoring e).comparison
      (ringEquivCertifiedDerivedTensoring e).isLeftDerived M := by
  refine ⟨0, 0, ?_⟩
  refine (hasTorAmplitudeIn_ringEquivCertified_iff e
    ((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj M) 0 0).2 ?_
  refine (hasTorAmplitude_of_iso
    (((ringEquivLift e).mapDerivedCategorySingleFunctor 0).app M) 0 0).2 ?_
  refine (hasTorAmplitudeIn_iff_hasTorAmplitude (canonicalDerivedTensorProduct S)
    (canonicalTensorComparison S) (canonicalTensorIsLeftDerived S) _ 0 0).1 ?_
  refine (hasTorAmplitudeIn_canonical_iff S _ 0 0).2 ?_
  exact ((hasTorDimensionLECanonical_iff_hasFlatRepresentative S
    ((ringEquivLift e).obj M) 0).2).2 (flat_ringEquivLift e M hM)

end RingEquiv

/-! ### The small-ring certificate -/

section Small

variable (R : Type u) [CommRing R] [Small.{w} R]

/-- **A Stacks 0652 certificate at module universe exactly `w`, for a `w`-small ring.** For
`R : Type u` with `[Small.{w} R]` and `w` in no relation to `u`, the three fields of
`CertifiedDerivedTensoring.{u, w} R`.

`StacksDraft.TorAmplitude.canonicalCertifiedDerivedTensoring` is the same datum at module
universe equal to the ring universe and
`StacksDraft.TorAmplitude.mixedCertifiedDerivedTensoring` at module universe `max u w`; both
require the module universe to contain the ring universe.  This one does not: it goes through
`Shrink.{w} R`, which is a ring in `Type w` isomorphic to `R`, so the canonical derived tensor
product of Stacks 0BYI is available over it. -/
public noncomputable def smallCertifiedDerivedTensoring :
    CertifiedDerivedTensoring.{u, w} R :=
  ringEquivCertifiedDerivedTensoring (Shrink.ringEquiv R)

/-- Tor amplitude read off `smallCertifiedDerivedTensoring` is the canonical Tor amplitude of
`Shrink.{w} R`, read at the transported object.  This is the faithfulness check: the datum is the
canonical derived tensor product of Stacks 0BYI moved across the equivalence of module categories
induced by `Shrink.ringEquiv R`, and the predicate of Stacks 0652 reads the same on both sides. -/
public theorem hasTorAmplitudeIn_smallCertified_iff
    (X : DerivedCategory (ModuleCat.{w} R)) (a b : ℤ) :
    (smallCertifiedDerivedTensoring.{u, w} R).HasTorAmplitudeIn X a b ↔
      HasTorAmplitude (canonicalDerivedTensorProduct (Shrink.{w} R)).tensor
        (canonicalTensorComparison (Shrink.{w} R))
        (canonicalTensorIsLeftDerived (Shrink.{w} R))
        ((ringEquivLiftDerived (Shrink.ringEquiv R)).obj X) a b :=
  hasTorAmplitudeIn_ringEquivCertified_iff (Shrink.ringEquiv R) X a b

/-- **A flat module has finite Tor dimension at the small-universe certificate.** So the
finite-Tor-dimension hypothesis of Stacks 0BZM, read at `smallCertifiedDerivedTensoring`, is
satisfiable at a module universe that need not contain the ring universe. -/
public theorem moduleHasFiniteTorDimension_smallCertified_of_flat
    (M : ModuleCat.{w} R) (hM : Module.Flat R M) :
    ModuleHasFiniteTorDimension (smallCertifiedDerivedTensoring.{u, w} R).tensor
      (smallCertifiedDerivedTensoring.{u, w} R).comparison
      (smallCertifiedDerivedTensoring.{u, w} R).isLeftDerived M :=
  moduleHasFiniteTorDimension_ringEquivCertified_of_flat (Shrink.ringEquiv R) M hM

end Small

end StacksDraft.TorAmplitude
