module

public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.RepresentedZariski
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.EtaleLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleEtalePullback
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.Affine
public import StacksFrontier.Homology.PseudoCoherent.Basic

/-!
# The model of a pseudo-coherent complex on an affine étale chart

Let `X` be an algebraic space over a scheme `S` and let `φ : h_U ⟶ X` be an étale chart whose
underlying scheme is `Spec A`. If `E` is a pseudo-coherent object of `D(𝒪_X)`, then the
restriction `E|_U = φ^*E` is `ε^*(P~)` for a bounded above complex `P` of finite free
`A`-modules.

## Main definitions

* `AlgebraicGeometry.Space.specFppfOver`: `Spec A` with a structure morphism to `S`, as an object
  of the big fppf site over `S`.
* `AlgebraicGeometry.Space.specFppfOverMap`: the morphism `Spec A ⟶ Spec R` of an `R`-algebra
  `A`, as a morphism of the big fppf site over `S`.

## Main results

* `AlgebraicGeometry.Space.exists_isBoundedAboveFiniteFree_tilde_iso`: an object of
  `D(𝒪_{Spec A})` with quasi-coherent cohomology, represented by a complex that is
  `m`-pseudo-coherent for every `m`, is `P~` for a bounded above complex `P` of finite free
  `A`-modules.
* `AlgebraicGeometry.Space.exists_isBoundedAboveFiniteFree_etaleModulePullback_iso`: the
  restriction of a pseudo-coherent object of `D(𝒪_X)` to an affine étale chart `Spec A` is
  `ε^*(P~)` for a bounded above complex `P` of finite free `A`-modules.

## References

* [Stacks Project, Lemma 76.54.5 (0DL5)](https://stacks.math.columbia.edu/tag/0DL5)
* [Stacks Project, Tag 08JL](https://stacks.math.columbia.edu/tag/08JL)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance 10000] HasDerivedCategory.standard

/-- The object of the big fppf site over `S` given by `Spec A` with a structure morphism to `S`. -/
abbrev specFppfOver {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
    (g : B.obj hA ⟶ B.obj hS) : BigFppfOver B S hS :=
  Over.mk g

/-- The morphism `Spec A ⟶ Spec R` of the structure map of an `R`-algebra `A`, as a morphism of
the big fppf site over `S` between the two spectra, given that it commutes with the structure
morphisms to `S`. -/
abbrev specFppfOverMap {R : Type u} [CommRing R] (hR : B.Contains (Spec (CommRingCat.of R)))
    (gR : B.obj hR ⟶ B.obj hS) {A : Type u} [CommRing A] [Algebra R A]
    (hA : B.Contains (Spec (CommRingCat.of A))) (gA : B.obj hA ⟶ B.obj hS)
    (w : (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))) :
      B.obj hA ⟶ B.obj hR) ≫ gR = gA) :
    specFppfOver B S hS hA gA ⟶ specFppfOver B S hS hR gR :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) w

/-- An object `ω` of `D(𝒪_{Spec A})` with quasi-coherent cohomology, represented by a complex
which is `m`-pseudo-coherent on `Spec A` for every `m`, is `P~` for a bounded above complex `P`
of finite free `A`-modules. -/
theorem exists_isBoundedAboveFiniteFree_tilde_iso {A : Type u} [CommRing A]
    (ω : DerivedCategory (Spec (CommRingCat.of A)).Modules)
    (hω : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of A)).Modules n).obj
      ω).IsQuasicoherent)
    (L : CochainComplex (Spec (CommRingCat.of A)).Modules ℤ) (eL : DerivedCategory.Q.obj L ≅ ω)
    (hL : ∀ m : ℤ, RingedSpace.PseudoCoherence.IsPseudoCoherentComplexFrom
      (X := (Spec (CommRingCat.of A)).toRingedSpace) L m) :
    ∃ P : CochainComplex (ModuleCat.{u} A) ℤ,
      StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree P ∧
      Nonempty ((tilde.functor (CommRingCat.of A)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj P) ≅ ω) := by
  obtain ⟨M, ⟨eM⟩⟩ := StandardModel.exists_iso_mapDerivedCategory (CommRingCat.of A) ω hω
  let M' := DerivedCategory.Q.objPreimage M
  let eM' : DerivedCategory.Q.obj M' ≅ M := DerivedCategory.Q.objObjPreimageIso M
  have hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj M') := by
    refine (StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _).2 fun m => ?_
    refine (RingedSpace.isPseudoCoherentFrom_tilde_iff M' m).1 ?_
    exact ⟨L, hL m, ⟨eL ≪≫ eM.symm ≪≫
      (tilde.functor (CommRingCat.of A)).mapDerivedCategory.mapIso eM'.symm ≪≫
      (tilde.functor (CommRingCat.of A)).mapDerivedCategoryFactors.app M'⟩⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hpc
  exact ⟨P, hP, ⟨(tilde.functor (CommRingCat.of A)).mapDerivedCategory.mapIso (eP ≪≫ eM') ≪≫ eM⟩⟩

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable {X : AlgebraicSpaces B S hS}

/-- Let `φ : h_U ⟶ X` be an étale chart whose underlying scheme is `Spec A`, and let `E` be a
pseudo-coherent object of `D(𝒪_X)`. Then `φ^*E` is `ε^*(P~)` for a bounded above complex `P` of
finite free `A`-modules. -/
theorem exists_isBoundedAboveFiniteFree_etaleModulePullback_iso {A : Type u} [CommRing A]
    (hA : B.Contains (Spec (CommRingCat.of A))) (g : B.obj hA ⟶ B.obj hS)
    (φ : (⟨yoneda.obj (specFppfOver B S hS hA g), isAlgebraicSpace_yoneda B S hS _⟩ :
      AlgebraicSpaces B S hS) ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E) :
    letI := etaleModulePullback_additive.{u, u} B S hS φ hφ
    letI := preservesFiniteLimits_etaleModulePullback B S hS φ hφ
    letI := preservesFiniteColimits_etaleModulePullback B S hS φ hφ
    ∃ P : CochainComplex (ModuleCat.{u} A) ℤ,
      StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree P ∧
      Nonempty ((etaleModulePullback.{u, u} B S hS φ hφ).mapDerivedCategory.obj E ≅
        (representedDerivedAssociatedModule B S hS (specFppfOver B S hS hA g)).obj
          ((tilde.functor (CommRingCat.of A) ⋙
            Scheme.Modules.restrictFunctor
              (Iso.refl ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA g))).hom
            ).mapDerivedCategory.obj (DerivedCategory.Q.obj P))) := by
  let := etaleModulePullback_additive.{u, u} B S hS φ hφ
  let := preservesFiniteLimits_etaleModulePullback B S hS φ hφ
  let := preservesFiniteColimits_etaleModulePullback B S hS φ hφ
  let V := specFppfOver B S hS hA g
  let E' := (etaleModulePullback.{u, u} B S hS φ hφ).mapDerivedCategory.obj E
  obtain ⟨K, hK, ⟨eK⟩⟩ := hE
  let φK := ((etaleModulePullback.{u, u} B S hS φ hφ).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  have hφK : ∀ m : ℤ, RingedSite.IsPseudoCoherentComplexFrom.{u + 1, u, u, u}
      (smallEtaleRingedSite B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)) φK m :=
    fun m => isPseudoCoherentComplexFrom_etaleModulePullback B S hS φ hφ K m (hK m)
  let eφK : DerivedCategory.Q.obj φK ≅ E' :=
    ((etaleModulePullback.{u, u} B S hS φ hφ).mapDerivedCategoryFactors.app K).symm ≪≫
      (etaleModulePullback.{u, u} B S hS φ hφ).mapDerivedCategory.mapIso eK
  have hE' : (smallEtaleRingedSite B S hS (yoneda.obj V)
      (isAlgebraicSpace_yoneda B S hS V)).IsPseudoCoherent E' := ⟨φK, hφK, ⟨eφK⟩⟩
  obtain ⟨ω, hω, ⟨eω⟩⟩ := exists_representedDerivedAssociatedModule_iso B S hS V E'
    (derivedCategoryB_of_isPseudoCoherent_unconditional B S hS (yoneda.obj V)
      (isAlgebraicSpace_yoneda B S hS V) E' hE')
  let L := DerivedCategory.Q.objPreimage ω
  let eL : DerivedCategory.Q.obj L ≅ ω := DerivedCategory.Q.objObjPreimageIso ω
  let εL := ((representedAssociatedModule B S hS V
    (isAlgebraicSpace_yoneda B S hS V)).mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  let eεL : DerivedCategory.Q.obj εL ≅ E' :=
    ((representedAssociatedModule B S hS V
      (isAlgebraicSpace_yoneda B S hS V)).mapDerivedCategoryFactors.app L).symm ≪≫
      (representedDerivedAssociatedModule B S hS V).mapIso eL ≪≫ eω
  have hL : ∀ m : ℤ, RingedSpace.PseudoCoherence.IsPseudoCoherentComplexFrom
      (X := (Spec (CommRingCat.of A)).toRingedSpace) L m := fun m =>
    (isPseudoCoherentComplexFrom_representedAssociatedModule_iff B S hS V L m).1
      ((smallEtaleRingedSite B S hS (yoneda.obj V)
        (isAlgebraicSpace_yoneda B S hS V)).isPseudoCoherentComplexFrom_of_iso_general E' m
          ⟨φK, hφK m, ⟨eφK⟩⟩ εL eεL)
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_isBoundedAboveFiniteFree_tilde_iso ω hω L eL hL
  exact ⟨P, hP, ⟨eω.symm ≪≫ (representedDerivedAssociatedModule B S hS V).mapIso
    (eP.symm ≪≫ (Stacks.DerivedGlueing.mapDerivedCategoryCongr
      ((Functor.rightUnitor (tilde.functor (CommRingCat.of A))).symm ≪≫
        Functor.isoWhiskerLeft (tilde.functor (CommRingCat.of A))
          Scheme.Modules.restrictFunctorId.symm)).app _)⟩⟩

end AlgebraicGeometry.Space

end
