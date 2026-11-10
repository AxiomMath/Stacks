module

public import Mathlib.Algebra.Category.Ring.Epi
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHom
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeMate
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# Inverse image after direct image along an affine monomorphism

Let `j : X' ⟶ X` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B`
which is affine and a monomorphism, and let `F` be a quasi-coherent `𝒪_{X'}`-module.  Then the
counit `j^*j_*F ⟶ F` of the adjunction of Stacks 03LU is an isomorphism.

The proof is affine base change.  Because `j` is a monomorphism, the square

```
X' --𝟙--> X'
|𝟙         |j
v          v
X' --j-->  X
```

is cartesian, so by the base change clause of Stacks 07U8 the base change map
`j^*j_*F ⟶ (𝟙)_*(𝟙)^*F` is an isomorphism, and that map is the counit of `j` read through the
identifications of the inverse and direct images along an identity with the identity.

The case of interest is the inclusion `j : X_K ⟶ X` of the generic fibre of an algebraic space
`X` over a valuation ring `R` with fraction field `K`, used in the proofs of Stacks 0DM0 and
Stacks 0DM4: `j` is the base change of `Spec K ⟶ Spec R`, which is affine and, `R ⟶ K` being an
epimorphism of rings, a monomorphism.  There the identification `j^*j_*F_K = F_K` is the "small
detail omitted" of the source.  It is stated here for the morphism `X_h : X_U ⟶ X_T` of base
changes of `f : X ⟶ Y` along any morphism `h : U ⟶ T` of test schemes over `Y` lying over
`Spec A ⟶ Spec R` for an epimorphism of rings `R ⟶ A`, which covers every localization of `R`
and in particular its fraction field.

## Main results

* `AlgebraicGeometry.Space.isIso_modulePullbackAdjunction_counit_app_of_mono_of_isAffineHom`:
  for an affine monomorphism `j` and a quasi-coherent `F`, the counit `j^*j_*F ⟶ F` is an
  isomorphism.
* `AlgebraicGeometry.Space.modulePullbackModulePushforwardIsoOfMonoOfIsAffineHom`: the resulting
  isomorphism `j^*j_*F ≅ F`.
* `AlgebraicGeometry.Space.isAffineHom_baseChangeMap_of_isHomLift`,
  `AlgebraicGeometry.Space.mono_baseChangeMap_of_isHomLift`: the morphism `X_h : X_U ⟶ X_T` of
  base changes along a morphism of test schemes lying over `Spec A ⟶ Spec R` is affine, and a
  monomorphism when `R ⟶ A` is an epimorphism.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_baseChangeMap_of_isHomLift`:
  the direct image along that `X_h` preserves quasi-coherence (Stacks 07U8).
* `AlgebraicGeometry.Space.isIso_modulePullbackAdjunction_counit_app_baseChangeMap_of_epi` and
  `AlgebraicGeometry.Space.baseChangeMapCounitIsoOfIsFractionRing`: `j^*j_*F ≅ F` for
  `j = X_h` and `F` quasi-coherent, in particular for the generic fibre over a valuation ring.

## Implementation notes

The test schemes and the morphism `h` are stated in the form of the extension problem
`AlgebraicGeometry.Space.CoherentSituation.ExtendsOverValuationRings`: `h` lifts the morphism
of the site underlying `Spec A ⟶ Spec R` along the projection of the test schemes over `Y`.

## References

* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 0DM0](https://stacks.math.columbia.edu/tag/0DM0)
* [Stacks Project, Tag 0DM4](https://stacks.math.columbia.edu/tag/0DM4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The counit of the adjunction of Stacks 03LU along an identity is an isomorphism: the direct
image along an identity is isomorphic to the identity functor, hence fully faithful. -/
instance isIso_modulePullbackAdjunction_id_counit (X : AlgebraicSpaces B S hS) :
    IsIso (modulePullbackAdjunction B S hS (𝟙 X)).counit :=
  haveI : (modulePushforward B S hS (𝟙 X)).Full :=
    Functor.Full.of_iso (modulePushforwardIdIso B S hS X).symm
  haveI : (modulePushforward B S hS (𝟙 X)).Faithful :=
    Functor.Faithful.of_iso (modulePushforwardIdIso B S hS X).symm
  inferInstance

/-- **Inverse image after direct image along an affine monomorphism.**  For an affine
monomorphism `j : X' ⟶ X` of algebraic spaces and a quasi-coherent `𝒪_{X'}`-module `F`, the
counit `j^*j_*F ⟶ F` of the adjunction of Stacks 03LU is an isomorphism.

The square with `j` on the right and at the bottom and identities on the left and at the top is
cartesian because `j` is a monomorphism, so the base change clause of Stacks 07U8 makes its base
change map `j^*j_*F ⟶ (𝟙)_*(𝟙)^*F` invertible; under the adjunction of the identity that map is
the inverse image along the identity of the counit of `j`. -/
theorem isIso_modulePullbackAdjunction_counit_app_of_mono_of_isAffineHom
    {X' X : AlgebraicSpaces B S hS} (j : X' ⟶ X) [Mono j] (hj : IsAffineHom B S hS j.hom)
    (F : Modules.{u, u} B S hS X'.1 X'.2) (hF : F.IsQuasicoherentOnSite) :
    IsIso ((modulePullbackAdjunction B S hS j).counit.app F) := by
  have sq : IsPullback (𝟙 X') (𝟙 X') j j := IsKernelPair.id_of_mono j
  have := isIso_moduleBaseChangeMap_app_of_isAffineHom sq hj F hF
  have h := moduleBaseChangeMap_adjoint_split j j (𝟙 X') (𝟙 X') sq.w F
  rw [Adjunction.homEquiv_counit] at h
  have : IsIso ((modulePullback B S hS (𝟙 X')).map
      ((modulePullbackAdjunction B S hS j).counit.app F)) := IsIso.of_isIso_fac_left h.symm
  exact isIso_of_reflects_iso _ (modulePullback B S hS (𝟙 X'))

/-- **`j^*j_*F ≅ F` for an affine monomorphism `j`**, by the counit of the adjunction of
Stacks 03LU, for every quasi-coherent `𝒪_{X'}`-module `F`. -/
def modulePullbackModulePushforwardIsoOfMonoOfIsAffineHom
    {X' X : AlgebraicSpaces B S hS} (j : X' ⟶ X) [Mono j] (hj : IsAffineHom B S hS j.hom)
    (F : Modules.{u, u} B S hS X'.1 X'.2) (hF : F.IsQuasicoherentOnSite) :
    (modulePullback B S hS j).obj ((modulePushforward B S hS j).obj F) ≅ F :=
  haveI := isIso_modulePullbackAdjunction_counit_app_of_mono_of_isAffineHom j hj F hF
  asIso ((modulePullbackAdjunction B S hS j).counit.app F)

/-! ### Base change of a monomorphism of affine test schemes -/

/-- A morphism of the big fppf site of `S` whose underlying morphism of schemes is a
monomorphism is a monomorphism of algebraic spaces: the functor to schemes is faithful, so the
morphism is a monomorphism of the site, and the Yoneda embedding preserves monomorphisms. -/
theorem mono_schemeSpaceFunctor_map {U V : BigFppfOver B S hS} (g : U ⟶ V)
    [Mono ((BigFppfOver.toScheme B S hS).map g)] :
    Mono ((schemeSpaceFunctor B S hS).map g) := by
  have : Mono g := (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  have : Mono ((ObjectProperty.ι _).map ((schemeSpaceFunctor B S hS).map g)) :=
    inferInstanceAs (Mono (yoneda.map g))
  exact (ObjectProperty.ι _).mono_of_mono_map this

/-- The morphism `X_h : X_U ⟶ X_T` of base changes of `f : X ⟶ Y` along a morphism `h : U ⟶ T`
of test schemes over `Y` with affine underlying schemes is affine: it is the base change of the
morphism of algebraic spaces represented by `h`, which is affine. -/
theorem isAffineHom_baseChangeMap_of_isAffine {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {U T : SchemesOver Y} (h : U ⟶ T)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U.left)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T.left)] :
    IsAffineHom B S hS (baseChangeMap f h).hom :=
  isAffineHom_of_isPullback' B S hS
    (AlgebraicSpaces.isPullback_hom B S hS (isPullback_baseChangeMap f h)).flip
    (isAffineHom_yoneda_map B S hS h.left)

/-- The morphism `X_h : X_U ⟶ X_T` of base changes of `f : X ⟶ Y` along a morphism `h : U ⟶ T`
of test schemes over `Y` whose underlying morphism of schemes is a monomorphism is a
monomorphism: it is the base change of the morphism of algebraic spaces represented by `h`. -/
theorem mono_baseChangeMap_of_mono {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {U T : SchemesOver Y} (h : U ⟶ T) [Mono ((BigFppfOver.toScheme B S hS).map h.left)] :
    Mono (baseChangeMap f h) :=
  have := mono_schemeSpaceFunctor_map (B := B) (S := S) (hS := hS) h.left
  (isPullback_baseChangeMap f h).mono_fst_of_mono

/-- **Inverse image after direct image along the base change of a monomorphism of affine test
schemes.**  Let `f : X ⟶ Y` be a morphism of algebraic spaces and `h : U ⟶ T` a morphism of
test schemes over `Y` whose underlying schemes are affine and whose underlying morphism of
schemes is a monomorphism.  Then for every quasi-coherent `𝒪_{X_U}`-module `F` the counit
`X_h^*X_{h,*}F ⟶ F` along the morphism `X_h : X_U ⟶ X_T` of base changes is an isomorphism. -/
theorem isIso_modulePullbackAdjunction_counit_app_baseChangeMap_of_mono
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {U T : SchemesOver Y} (h : U ⟶ T)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U.left)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T.left)]
    [Mono ((BigFppfOver.toScheme B S hS).map h.left)]
    (F : Modules.{u, u} B S hS (baseChangeSpace f U).1 (baseChangeSpace f U).2)
    (hF : F.IsQuasicoherentOnSite) :
    IsIso ((modulePullbackAdjunction B S hS (baseChangeMap f h)).counit.app F) :=
  have := mono_baseChangeMap_of_mono f h
  isIso_modulePullbackAdjunction_counit_app_of_mono_of_isAffineHom _
    (isAffineHom_baseChangeMap_of_isAffine f h) F hF

/-! ### The generic fibre over a ring epimorphism -/

section Generic

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
  (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  {hR : B.Contains (Spec (.of R))} {hA : B.Contains (Spec (.of A))} {b : Spec (.of R) ⟶ S}
  {U T : SchemesOver Y} (h : U ⟶ T)

/-- The underlying schemes of a morphism `h : U ⟶ T` of test schemes lying over
`Spec A ⟶ Spec R` are affine. -/
theorem isAffine_left_of_isHomLift
    (hh : (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y).IsHomLift
      (Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
        siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ b) ⟶
          siteObject B S hS hR b) h) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj U.left) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj T.left) := by
  let φ : siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ b) ⟶
      siteObject B S hS hR b :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))))
  have hU : U.left = siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ b) :=
    IsHomLift.domain_eq (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y) φ h
  have hT : T.left = siteObject B S hS hR b :=
    IsHomLift.codomain_eq (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y) φ h
  rw [hU, hT]
  exact ⟨inferInstanceAs (IsAffine (Spec (.of A))), inferInstanceAs (IsAffine (Spec (.of R)))⟩

/-- **The inclusion of the generic fibre is affine.**  For a morphism `h : U ⟶ T` of test
schemes over `Y` lying over `Spec A ⟶ Spec R`, the morphism `X_h : X_U ⟶ X_T` of base changes
is affine, as a base change of the affine morphism `Spec A ⟶ Spec R`. -/
theorem isAffineHom_baseChangeMap_of_isHomLift
    (hh : (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y).IsHomLift
      (Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
        siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ b) ⟶
          siteObject B S hS hR b) h) :
    IsAffineHom B S hS (baseChangeMap f h).hom :=
  have h₁ := isAffine_left_of_isHomLift R A h hh
  have := h₁.1
  have := h₁.2
  isAffineHom_baseChangeMap_of_isAffine f h

/-- **The direct image along the inclusion of the generic fibre is quasi-coherent.**  For a
morphism `h : U ⟶ T` of test schemes over `Y` lying over `Spec A ⟶ Spec R` and a quasi-coherent
`𝒪_{X_U}`-module `F`, the direct image `j_*F` along `j = X_h : X_U ⟶ X_T` is quasi-coherent:
`j` is affine, and the direct image along an affine morphism is quasi-coherent by
Stacks 07U8. -/
theorem isQuasicoherentOnSite_modulePushforward_baseChangeMap_of_isHomLift
    (hh : (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y).IsHomLift
      (Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
        siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ b) ⟶
          siteObject B S hS hR b) h)
    (F : Modules.{u, u} B S hS (baseChangeSpace f U).1 (baseChangeSpace f U).2)
    (hF : F.IsQuasicoherentOnSite) :
    ((modulePushforward B S hS (baseChangeMap f h)).obj F).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePushforward_isAffineHom B S hS _
    (isAffineHom_baseChangeMap_of_isHomLift f R A h hh) F hF

/-- **The inclusion of the generic fibre is a monomorphism.**  For an epimorphism of rings
`R ⟶ A` and a morphism `h : U ⟶ T` of test schemes over `Y` lying over `Spec A ⟶ Spec R`, the
morphism `X_h : X_U ⟶ X_T` of base changes is a monomorphism, as a base change of the
monomorphism `Spec A ⟶ Spec R`. -/
theorem mono_baseChangeMap_of_isHomLift [Algebra.IsEpi R A]
    (hh : (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y).IsHomLift
      (Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
        siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ b) ⟶
          siteObject B S hS hR b) h) :
    Mono (baseChangeMap f h) := by
  have : Epi (CommRingCat.ofHom (algebraMap R A)) := CommRingCat.epi_iff_epi.mpr inferInstance
  have : Mono (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    inferInstanceAs (Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R A)).op))
  have : Mono ((BigFppfOver.toScheme B S hS).map h.left) := by
    let φ : siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ b) ⟶
        siteObject B S hS hR b :=
      Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    have hfac := IsHomLift.fac' (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y) φ h
    change Mono ((BigFppfOver.toScheme B S hS).map
      ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y).map h))
    rw [hfac, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
    exact inferInstanceAs (Mono (_ ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ _))
  exact mono_baseChangeMap_of_mono f h

/-- **`j^*j_*F ≅ F` for the inclusion of the generic fibre**, the identification the proofs of
Stacks 0DM0 and Stacks 0DM4 use ("small detail omitted").  Let `f : X ⟶ Y` be a morphism of
algebraic spaces, `R ⟶ A` an epimorphism of commutative rings (for instance the inclusion of a
domain `R` in its fraction field `A`, or any localization of `R`), `b : Spec R ⟶ S`, and
`h : U ⟶ T` a morphism of test schemes over `Y` lying over `Spec A ⟶ Spec R`.  Then for every
quasi-coherent `𝒪_{X_U}`-module `F` the counit `j^*j_*F ⟶ F` along `j = X_h : X_U ⟶ X_T` is an
isomorphism. -/
theorem isIso_modulePullbackAdjunction_counit_app_baseChangeMap_of_epi [Algebra.IsEpi R A]
    (hh : (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y).IsHomLift
      (Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
        siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ b) ⟶
          siteObject B S hS hR b) h)
    (F : Modules.{u, u} B S hS (baseChangeSpace f U).1 (baseChangeSpace f U).2)
    (hF : F.IsQuasicoherentOnSite) :
    IsIso ((modulePullbackAdjunction B S hS (baseChangeMap f h)).counit.app F) :=
  have := mono_baseChangeMap_of_isHomLift f R A h hh
  isIso_modulePullbackAdjunction_counit_app_of_mono_of_isAffineHom _
    (isAffineHom_baseChangeMap_of_isHomLift f R A h hh) F hF

end Generic

/-- **`j^*j_*F_K ≅ F_K` for the inclusion `j : X_K ⟶ X_R` of the generic fibre** over a test
scheme lying over the fraction field `K` of a domain `R` (in particular a valuation ring), by
the counit of the adjunction of Stacks 03LU, for every quasi-coherent `𝒪_{X_K}`-module `F_K`.
This is `AlgebraicGeometry.Space.isIso_modulePullbackAdjunction_counit_app_baseChangeMap_of_epi`
for the epimorphism `R ⟶ K`. -/
def baseChangeMapCounitIsoOfIsFractionRing
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (R : Type u) [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K]
    (hR : B.Contains (Spec (.of R))) (hK : B.Contains (Spec (.of K))) (b : Spec (.of R) ⟶ S)
    {U T : SchemesOver Y} (h : U ⟶ T)
    (hh : (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y).IsHomLift
      (Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
        siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b) ⟶
          siteObject B S hS hR b) h)
    (F : Modules.{u, u} B S hS (baseChangeSpace f U).1 (baseChangeSpace f U).2)
    (hF : F.IsQuasicoherentOnSite) :
    (modulePullback B S hS (baseChangeMap f h)).obj
        ((modulePushforward B S hS (baseChangeMap f h)).obj F) ≅ F :=
  haveI := isIso_modulePullbackAdjunction_counit_app_baseChangeMap_of_epi f R K h hh F hF
  asIso ((modulePullbackAdjunction B S hS (baseChangeMap f h)).counit.app F)

end AlgebraicGeometry.Space

end
