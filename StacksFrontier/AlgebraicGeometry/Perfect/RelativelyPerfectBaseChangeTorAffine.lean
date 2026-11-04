module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineEssentialSurjectivity
public import StacksFrontier.Homology.RelativelyPerfect.BaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectArrowIso
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of relative perfectness for spectra of rings

Let `R → A` be a flat ring map of finite presentation and `R → R'` arbitrary, and put
`A' = A ⊗_R R'`. An object of `D(𝒪_{Spec A})` perfect relative to `Spec R` has `Spec R'`-perfect
derived pullback along `Spec A' ⟶ Spec A`. The same holds for any cartesian square of affine
schemes along a flat morphism locally of finite presentation.

## Main results

* `AlgebraicGeometry.AffinePerfectDescent.isPerfectRelativeTo_derivedPullback_includeLeft`: the
  statement for spectra of rings.
* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_derivedPullback_fst_of_isAffine`: the
  statement for a cartesian square of affine schemes.

## References

* [Stacks Project, Lemma 36.35.6 (Tag 0DI5)](https://stacks.math.columbia.edu/tag/0DI5)
* [Stacks Project, Lemma 15.85.5 (Tag 0DHW)](https://stacks.math.columbia.edu/tag/0DHW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry StrictlyPerfect
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.AffinePerfectDescent

open AlgebraicGeometry.AffineRelativeTorAmplitude

variable (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R'] [Algebra R A]
  [Algebra R R'] [Module.Flat R A] [Algebra.FinitePresentation R A]

/-- The `R'`-algebra structure of `A ⊗_R R'`. -/
abbrev baseChangeAlgebra : Algebra R' (A ⊗[R] R') := Algebra.TensorProduct.rightAlgebra

/-- The algebra isomorphism `R' ⊗_R A ≃ A ⊗_R R'` over `R'`. -/
def baseChangeCommEquiv :
    letI := baseChangeAlgebra R A R'
    (R' ⊗[R] A) ≃ₐ[R'] (A ⊗[R] R') :=
  letI := baseChangeAlgebra R A R'
  AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R R' A).toRingEquiv)
    (fun r' => Algebra.TensorProduct.comm_tmul (R := R) r' (1 : A))

/-- `A ⊗_R R'` is flat over `R'`. -/
instance baseChange_flat :
    letI := baseChangeAlgebra R A R'
    Module.Flat R' (A ⊗[R] R') :=
  letI := baseChangeAlgebra R A R'
  Module.Flat.of_linearEquiv (baseChangeCommEquiv R A R').symm.toLinearEquiv

/-- `A ⊗_R R'` is of finite presentation over `R'`. -/
instance baseChange_finitePresentation :
    letI := baseChangeAlgebra R A R'
    Algebra.FinitePresentation R' (A ⊗[R] R') :=
  letI := baseChangeAlgebra R A R'
  Algebra.FinitePresentation.equiv (baseChangeCommEquiv R A R')

/-- Relative perfectness of a complex of modules depends only on its isomorphism class. -/
private theorem isRelativelyPerfect_canonical_of_iso {S B : Type u} [CommRing S] [CommRing B]
    [Algebra S B] [Module.Flat S B] [Algebra.FinitePresentation S B]
    {K K' : DerivedCategory (ModuleCat.{u} B)} (e : K ≅ K')
    (h : PseudoCoherence.IsRelativelyPerfect.{u, u, u}
      (PseudoCoherence.canonicalDerivedTensoringDatum S).tensor
      (PseudoCoherence.canonicalDerivedTensoringDatum S).comparison
      (PseudoCoherence.canonicalDerivedTensoringDatum S).isLeftDerived K) :
    PseudoCoherence.IsRelativelyPerfect.{u, u, u}
      (PseudoCoherence.canonicalDerivedTensoringDatum S).tensor
      (PseudoCoherence.canonicalDerivedTensoringDatum S).comparison
      (PseudoCoherence.canonicalDerivedTensoringDatum S).isLeftDerived K' := by
  refine ⟨h.1.ofIso e, ?_⟩
  obtain ⟨a, b, hab⟩ := h.2
  exact ⟨a, b, fun M i hi => (hab M i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).mapIso
      (((PseudoCoherence.canonicalDerivedTensoringDatum S).tensor.mapIso
        ((ModuleCat.restrictScalars (algebraMap S B)).mapDerivedCategory.mapIso e)).app
          ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj M))).symm⟩

/-- Relative perfectness along a morphism of schemes depends only on the isomorphism class. -/
private theorem isPerfectRelativeTo_canonical_of_iso_aux {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] {E E' : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    (e : E ≅ E')
    (h : f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E) :
    f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E' :=
  have := Scheme.Hom.isClosedUnderIsomorphisms_isPerfectRelativeTo f
    (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
  (Scheme.Hom.isPerfectRelativeTo f
    (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)).prop_of_iso e h

/-- The isomorphism `tildeObj B M ≅ E` obtained from `Q.obj M ≅ K` and `tilde K ≅ E`. -/
private def tildeObjIsoOfIso (B : Type u) [CommRing B] {M : CochainComplex (ModuleCat.{u} B) ℤ}
    {K : DerivedCategory (ModuleCat.{u} B)} {E : DerivedCategory (OXMod.{u, u}
      (Spec (CommRingCat.of B)).toRingedSpace)} (eM : DerivedCategory.Q.obj M ≅ K)
    (eK : (tilde.functor (CommRingCat.of B)).mapDerivedCategory.obj K ≅ E) : tildeObj B M ≅ E :=
  ((tilde.functor (CommRingCat.of B)).mapDerivedCategoryFactors.app M).symm ≪≫
    (tilde.functor (CommRingCat.of B)).mapDerivedCategory.mapIso eM ≪≫ eK

/-- **Base change of relative perfectness along `Spec (A ⊗_R R') ⟶ Spec A`.** For a flat ring map
`R → A` of finite presentation and any `R → R'`, the derived pullback along
`Spec (A ⊗_R R') ⟶ Spec A` of an object of `D(𝒪_{Spec A})` perfect relative to `Spec R` is
perfect relative to `Spec R'`. -/
theorem isPerfectRelativeTo_derivedPullback_includeLeft
    (E : DerivedCategory (OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace))
    (hE : (specMap R A).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E) :
    letI := baseChangeAlgebra R A R'
    (specMap R' (A ⊗[R] R')).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((derivedPullback (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R'))).toLRSHom.toShHom).obj
        E) := by
  let := baseChangeAlgebra R A R'
  have hqc : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (Spec (CommRingCat.of A)).Modules n).obj E).IsQuasicoherent :=
    isQuasicoherentDerived_of_isPseudoCoherent (Spec (CommRingCat.of A)) E hE.1
  obtain ⟨K, ⟨eK⟩⟩ := StandardModel.exists_iso_mapDerivedCategory (CommRingCat.of A) E hqc
  obtain ⟨M, ⟨eM⟩⟩ : (DerivedCategory.Q (C := ModuleCat.{u} A)).essImage K :=
    Functor.EssSurj.mem_essImage (F := DerivedCategory.Q) K
  have eE : tildeObj A M ≅ E := tildeObjIsoOfIso A eM eK
  have hM := (isPerfectRelativeTo_tildeObj_iff R A M).1
    (isPerfectRelativeTo_canonical_of_iso_aux (specMap R A) eE.symm hE)
  have hext := PseudoCoherence.derivedExtensionScalars_isRelativelyPerfect
    (R := R) (A := A) (R' := R')
    (PseudoCoherence.canonicalDerivedTensoringDatum R).tensor
    (PseudoCoherence.canonicalDerivedTensoringDatum R).comparison
    (PseudoCoherence.canonicalDerivedTensoringDatum R).isLeftDerived
    (PseudoCoherence.canonicalDerivedTensoringDatum R').tensor
    (PseudoCoherence.canonicalDerivedTensoringDatum R').comparison
    (PseudoCoherence.canonicalDerivedTensoringDatum R').isLeftDerived
    (DerivedCategory.Q.obj M) hM
  let φ : A →+* A ⊗[R] R' := Algebra.TensorProduct.includeLeftRingHom
  obtain ⟨M', ⟨eM'⟩⟩ : (DerivedCategory.Q (C := ModuleCat.{u} (A ⊗[R] R'))).essImage
      ((totalDerivedExtensionScalars.{u, u, u} φ).functor.obj (DerivedCategory.Q.obj M)) :=
    Functor.EssSurj.mem_essImage (F := DerivedCategory.Q) _
  have hT := (isPerfectRelativeTo_tildeObj_iff R' (A ⊗[R] R') M').2
    (isRelativelyPerfect_canonical_of_iso (S := R') eM'.symm hext)
  refine isPerfectRelativeTo_canonical_of_iso_aux (specMap R' (A ⊗[R] R'))
    (tildeObjIsoOfIso _ eM' ?_) hT
  exact (derivedPullbackTildeObjIso φ M (DerivedCategory.Q.obj M) (Iso.refl _)).symm ≪≫
    (derivedPullback (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).mapIso eE

end AlgebraicGeometry.AffinePerfectDescent

namespace AlgebraicGeometry.Scheme.Hom

open AlgebraicGeometry.AffinePerfectDescent AlgebraicGeometry.AffineRelativeTorAmplitude

/-- Relative perfectness is invariant under isomorphism of objects. -/
theorem isPerfectRelativeTo_canonical_of_iso {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] {E E' : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    (e : E ≅ E')
    (h : f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E) :
    f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E' :=
  AffinePerfectDescent.isPerfectRelativeTo_canonical_of_iso_aux f e h

/-- Relative perfectness along equal morphisms. -/
theorem isPerfectRelativeTo_canonical_congr {X S : Scheme.{u}} {f f' : X ⟶ S} (h : f = f')
    [Flat f] [LocallyOfFinitePresentation f] [Flat f'] [LocallyOfFinitePresentation f']
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E ↔
      f'.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E := by
  subst h
  rfl

variable {V W W' : Scheme.{u}} [IsAffine V] [IsAffine W] [IsAffine W'] (f : V ⟶ W) (g : W' ⟶ W)
  [Flat f] [LocallyOfFinitePresentation f]

/-- The naturality square of `AlgebraicGeometry.Scheme.isoSpec`. -/
theorem pullbackIsoSpecTensor_aux₁ {Y : Scheme.{u}} [IsAffine Y] (h : Y ⟶ W) :
    h ≫ W.isoSpec.hom = Y.isoSpec.hom ≫ Spec.map h.appTop := by
  simp [Scheme.isoSpec_hom, Scheme.toSpecΓ_naturality]

/-- The cartesian square of affine schemes read on spectra:
`V ×_W W' ≅ Spec (Γ(V) ⊗_{Γ(W)} Γ(W'))`. -/
def pullbackIsoSpecTensor :
    letI : Algebra Γ(W, ⊤) Γ(V, ⊤) := f.appTop.hom.toAlgebra
    letI : Algebra Γ(W, ⊤) Γ(W', ⊤) := g.appTop.hom.toAlgebra
    pullback f g ≅ Spec (CommRingCat.of (Γ(V, ⊤) ⊗[Γ(W, ⊤)] Γ(W', ⊤))) :=
  letI : Algebra Γ(W, ⊤) Γ(V, ⊤) := f.appTop.hom.toAlgebra
  letI : Algebra Γ(W, ⊤) Γ(W', ⊤) := g.appTop.hom.toAlgebra
  asIso (pullback.map f g (Spec.map f.appTop) (Spec.map g.appTop) V.isoSpec.hom W'.isoSpec.hom
      W.isoSpec.hom (pullbackIsoSpecTensor_aux₁ f) (pullbackIsoSpecTensor_aux₁ g)) ≪≫
    pullbackSpecIso Γ(W, ⊤) Γ(V, ⊤) Γ(W', ⊤)

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- Under `pullbackIsoSpecTensor`, the map `Spec (Γ(V) ⊗_{Γ(W)} Γ(W')) ⟶ Spec Γ(V)` is the first
projection followed by `V.isoSpec`. -/
theorem pullbackIsoSpecTensor_hom_fst :
    letI : Algebra Γ(W, ⊤) Γ(V, ⊤) := f.appTop.hom.toAlgebra
    letI : Algebra Γ(W, ⊤) Γ(W', ⊤) := g.appTop.hom.toAlgebra
    (pullbackIsoSpecTensor f g).hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : Γ(V, ⊤) →+* Γ(V, ⊤) ⊗[Γ(W, ⊤)] Γ(W', ⊤))) =
      pullback.fst f g ≫ V.isoSpec.hom :=
  let : Algebra Γ(W, ⊤) Γ(V, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(W, ⊤) Γ(W', ⊤) := g.appTop.hom.toAlgebra
  (Category.assoc (pullback.map f g (Spec.map f.appTop) (Spec.map g.appTop) V.isoSpec.hom
      W'.isoSpec.hom W.isoSpec.hom (pullbackIsoSpecTensor_aux₁ f) (pullbackIsoSpecTensor_aux₁ g))
    (pullbackSpecIso Γ(W, ⊤) Γ(V, ⊤) Γ(W', ⊤)).hom _).trans
    ((congrArg (_ ≫ ·) (pullbackSpecIso_hom_fst Γ(W, ⊤) Γ(V, ⊤) Γ(W', ⊤))).trans
      (pullback.lift_fst _ _ _))

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- Under `pullbackIsoSpecTensor`, the map `Spec (Γ(V) ⊗_{Γ(W)} Γ(W')) ⟶ Spec Γ(W')` is the second
projection followed by `W'.isoSpec`. -/
theorem pullbackIsoSpecTensor_hom_snd :
    letI : Algebra Γ(W, ⊤) Γ(V, ⊤) := f.appTop.hom.toAlgebra
    letI : Algebra Γ(W, ⊤) Γ(W', ⊤) := g.appTop.hom.toAlgebra
    letI := baseChangeAlgebra Γ(W, ⊤) Γ(V, ⊤) Γ(W', ⊤)
    (pullbackIsoSpecTensor f g).hom ≫ specMap Γ(W', ⊤) (Γ(V, ⊤) ⊗[Γ(W, ⊤)] Γ(W', ⊤)) =
      pullback.snd f g ≫ W'.isoSpec.hom :=
  let : Algebra Γ(W, ⊤) Γ(V, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(W, ⊤) Γ(W', ⊤) := g.appTop.hom.toAlgebra
  (Category.assoc (pullback.map f g (Spec.map f.appTop) (Spec.map g.appTop) V.isoSpec.hom
      W'.isoSpec.hom W.isoSpec.hom (pullbackIsoSpecTensor_aux₁ f) (pullbackIsoSpecTensor_aux₁ g))
    (pullbackSpecIso Γ(W, ⊤) Γ(V, ⊤) Γ(W', ⊤)).hom _).trans
    ((congrArg (_ ≫ ·) (pullbackSpecIso_hom_snd Γ(W, ⊤) Γ(V, ⊤) Γ(W', ⊤))).trans
      (pullback.lift_snd _ _ _))

/-- The cartesian square of affine schemes as an isomorphism of arrows onto the spectrum of the
tensor product over the spectrum of `Γ(W')`. -/
@[sga "3 VIA 2.1.2" "special case"]
def pullbackSndArrowIsoSpec :
    letI : Algebra Γ(W, ⊤) Γ(V, ⊤) := f.appTop.hom.toAlgebra
    letI : Algebra Γ(W, ⊤) Γ(W', ⊤) := g.appTop.hom.toAlgebra
    letI := baseChangeAlgebra Γ(W, ⊤) Γ(V, ⊤) Γ(W', ⊤)
    ringedArrow (pullback.snd f g) ≅
      ringedArrow (specMap Γ(W', ⊤) (Γ(V, ⊤) ⊗[Γ(W, ⊤)] Γ(W', ⊤))) :=
  letI : Algebra Γ(W, ⊤) Γ(V, ⊤) := f.appTop.hom.toAlgebra
  letI : Algebra Γ(W, ⊤) Γ(W', ⊤) := g.appTop.hom.toAlgebra
  letI := baseChangeAlgebra Γ(W, ⊤) Γ(V, ⊤) Γ(W', ⊤)
  Arrow.isoMk (Scheme.forgetToRingedSpace.mapIso (pullbackIsoSpecTensor f g))
    (Scheme.forgetToRingedSpace.mapIso W'.isoSpec)
    ((Scheme.forgetToRingedSpace.map_comp _ _).symm.trans
      ((congrArg Scheme.forgetToRingedSpace.map (pullbackIsoSpecTensor_hom_snd f g)).trans
        (Scheme.forgetToRingedSpace.map_comp _ _)))

/-- The `W`-perfect object `K` of `D(𝒪_V)`, transported to `Spec Γ(V)`, is `Spec Γ(W)`-perfect. -/
theorem isPerfectRelativeTo_specMap_of_isAffine
    (K : DerivedCategory (OXMod.{u, u} V.toRingedSpace))
    (hK : f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) K) :
    letI : Algebra Γ(W, ⊤) Γ(V, ⊤) := f.appTop.hom.toAlgebra
    haveI : Module.Flat Γ(W, ⊤) Γ(V, ⊤) := HasRingHomProperty.appTop (P := @Flat) f ‹_›
    haveI : Algebra.FinitePresentation Γ(W, ⊤) Γ(V, ⊤) :=
      HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) f ‹_›
    (specMap Γ(W, ⊤) Γ(V, ⊤)).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((derivedPullback (Scheme.forgetToRingedSpace.mapIso V.isoSpec).inv).obj K) := by
  let : Algebra Γ(W, ⊤) Γ(V, ⊤) := f.appTop.hom.toAlgebra
  have : Module.Flat Γ(W, ⊤) Γ(V, ⊤) := HasRingHomProperty.appTop (P := @Flat) f ‹_›
  have : Algebra.FinitePresentation Γ(W, ⊤) Γ(V, ⊤) :=
    HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) f ‹_›
  have : Flat (Spec.map f.appTop) := flat_specMap Γ(W, ⊤) Γ(V, ⊤)
  have : LocallyOfFinitePresentation (Spec.map f.appTop) :=
    locallyOfFinitePresentation_specMap Γ(W, ⊤) Γ(V, ⊤)
  exact (isPerfectRelativeTo_arrowIso_iff f (Spec.map f.appTop) (ringedArrowIsoSpec f) _).1
    (isPerfectRelativeTo_canonical_of_iso f
      ((Stacks.Cohomology.TorAmplitude.derivedPullbackHomCompInvIso
        (Scheme.forgetToRingedSpace.mapIso V.isoSpec).symm).app K).symm hK)

/-- For a `W`-perfect object `K` of `D(𝒪_V)`, its derived pullback to `Spec Γ(V)`, then to
`Spec (Γ(V) ⊗_{Γ(W)} Γ(W'))` and then to `V ×_W W'` through `pullbackIsoSpecTensor`, is perfect
relative to the second projection. -/
theorem isPerfectRelativeTo_pullbackIsoSpecTensor
    (K : DerivedCategory (OXMod.{u, u} V.toRingedSpace))
    (hK : f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) K) :
    letI : Algebra Γ(W, ⊤) Γ(V, ⊤) := f.appTop.hom.toAlgebra
    letI : Algebra Γ(W, ⊤) Γ(W', ⊤) := g.appTop.hom.toAlgebra
    (pullback.snd f g).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((derivedPullback (Scheme.forgetToRingedSpace.map (pullbackIsoSpecTensor f g).hom)).obj
        ((derivedPullback (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          Γ(V, ⊤) →+* Γ(V, ⊤) ⊗[Γ(W, ⊤)] Γ(W', ⊤)))).toLRSHom.toShHom).obj
          ((derivedPullback (Scheme.forgetToRingedSpace.mapIso V.isoSpec).inv).obj K))) := by
  let : Algebra Γ(W, ⊤) Γ(V, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(W, ⊤) Γ(W', ⊤) := g.appTop.hom.toAlgebra
  have : Module.Flat Γ(W, ⊤) Γ(V, ⊤) := HasRingHomProperty.appTop (P := @Flat) f ‹_›
  have : Algebra.FinitePresentation Γ(W, ⊤) Γ(V, ⊤) :=
    HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) f ‹_›
  let := baseChangeAlgebra Γ(W, ⊤) Γ(V, ⊤) Γ(W', ⊤)
  exact (isPerfectRelativeTo_arrowIso_iff (pullback.snd f g)
    (specMap Γ(W', ⊤) (Γ(V, ⊤) ⊗[Γ(W, ⊤)] Γ(W', ⊤))) (pullbackSndArrowIsoSpec f g) _).2
    (isPerfectRelativeTo_derivedPullback_includeLeft Γ(W, ⊤) Γ(V, ⊤) Γ(W', ⊤) _
      (isPerfectRelativeTo_specMap_of_isAffine f K hK))

/-- The derived pullback of `K` to `Spec Γ(V)`, then to `Spec (Γ(V) ⊗_{Γ(W)} Γ(W'))` and then to
`V ×_W W'` through `pullbackIsoSpecTensor`, is isomorphic to its derived pullback along the first
projection. -/
def pullbackIsoSpecTensorObjIso (K : DerivedCategory (OXMod.{u, u} V.toRingedSpace)) :
    letI : Algebra Γ(W, ⊤) Γ(V, ⊤) := f.appTop.hom.toAlgebra
    letI : Algebra Γ(W, ⊤) Γ(W', ⊤) := g.appTop.hom.toAlgebra
    (derivedPullback (Scheme.forgetToRingedSpace.map (pullbackIsoSpecTensor f g).hom)).obj
        ((derivedPullback (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          Γ(V, ⊤) →+* Γ(V, ⊤) ⊗[Γ(W, ⊤)] Γ(W', ⊤)))).toLRSHom.toShHom).obj
          ((derivedPullback (Scheme.forgetToRingedSpace.mapIso V.isoSpec).inv).obj K)) ≅
      (derivedPullback (pullback.fst f g).toLRSHom.toShHom).obj K :=
  letI : Algebra Γ(W, ⊤) Γ(V, ⊤) := f.appTop.hom.toAlgebra
  letI : Algebra Γ(W, ⊤) Γ(W', ⊤) := g.appTop.hom.toAlgebra
  (Stacks.DerivedPullback.schemeFactorIso (pullbackIsoSpecTensor f g).hom
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        Γ(V, ⊤) →+* Γ(V, ⊤) ⊗[Γ(W, ⊤)] Γ(W', ⊤))))
      (pullback.fst f g ≫ V.isoSpec.hom) (pullbackIsoSpecTensor_hom_fst f g)).app _ ≪≫
    ((Stacks.DerivedPullback.schemeFactorIso (pullback.fst f g) V.isoSpec.hom
      (pullback.fst f g ≫ V.isoSpec.hom) rfl).app _).symm ≪≫
    (derivedPullback (pullback.fst f g).toLRSHom.toShHom).mapIso
      ((Stacks.Cohomology.TorAmplitude.derivedPullbackHomCompInvIso
        (Scheme.forgetToRingedSpace.mapIso V.isoSpec).symm).app K)

/-- **Base change of relative perfectness along a cartesian square of affine schemes.** For a
flat morphism `f : V ⟶ W` locally of finite presentation between affine schemes and a morphism
`g : W' ⟶ W` from an affine scheme, the derived pullback along `V ×_W W' ⟶ V` of a `W`-perfect
object of `D(𝒪_V)` is `W'`-perfect. -/
theorem isPerfectRelativeTo_derivedPullback_fst_of_isAffine
    (K : DerivedCategory (OXMod.{u, u} V.toRingedSpace))
    (hK : f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) K) :
    (pullback.snd f g).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((derivedPullback (pullback.fst f g).toLRSHom.toShHom).obj K) :=
  isPerfectRelativeTo_canonical_of_iso (pullback.snd f g) (pullbackIsoSpecTensorObjIso f g K)
    (isPerfectRelativeTo_pullbackIsoSpecTensor f g K hK)

end AlgebraicGeometry.Scheme.Hom

end
