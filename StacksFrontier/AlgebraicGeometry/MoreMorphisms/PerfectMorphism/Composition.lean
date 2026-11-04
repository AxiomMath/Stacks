module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineLocal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.Flat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.Composition
public import StacksFrontier.Homology.PseudoCoherent.Relative.Composition
public import StacksFrontier.Homology.TorAmplitude.CompositionCanonical

/-!
# Composition of perfect morphisms

A composition of perfect morphisms of schemes is perfect.

## Main results

* `AlgebraicGeometry.perfect_comp`: Stacks 0689, closure of perfectness under composition.
* `AlgebraicGeometry.Perfect.isStableUnderComposition`: Stacks 0689 as a
  `CategoryTheory.MorphismProperty.IsStableUnderComposition`.
* `AlgebraicGeometry.Perfect.respectsLeft_etale` and
  `AlgebraicGeometry.Perfect.respectsRight_etale`: composing a perfect morphism with an étale
  morphism on either side leaves it perfect.

## Implementation notes

The statement is affine-local, so by Stacks 0686 it reduces to the ring-theoretic statement that
a composition of perfect ring maps is perfect. Pseudo-coherence composes by Stacks 0681
(`Algebra.PseudoCoherent.trans`), and the Tor amplitudes add by
`StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_derivedTensorProduct`: for an `R`-module
`M` the base change `M ⊗ᴸ_R C` is `(M ⊗ᴸ_R A) ⊗ᴸ_A C`, so the amplitude of `C` over `R` is
contained in the sum of the two intervals.

The affine cover of the composite is assembled from an affine cover of `Z`, an affine cover of
each `g`-preimage, and the affine opens of `X` inside the `f`-preimages of those — the last step
is needed because an affine open of `X` lying over an affine open of `Y` need not come from the
cover chosen for `g`.

The result is registered as an instance, so perfectness of a composite is available to typeclass
inference.

An étale morphism is flat and locally of finite presentation, hence perfect by the implication
(2) `⇒` (1) of Stacks 068A, so composing with an étale morphism on either side is a special case
of closure under composition.

## References

* [The Stacks Project, Lemma 37.61.3 (0689)](https://stacks.math.columbia.edu/tag/0689)
* [The Stacks Project, Lemma 37.61.1 (0686)](https://stacks.math.columbia.edu/tag/0686)
* [The Stacks Project, Lemma 37.60.2 (0681)](https://stacks.math.columbia.edu/tag/0681)
-/

public section

open CategoryTheory TopologicalSpace CochainComplex.DerivedTensor
open StacksDraft.TorAmplitude
open StacksDraft.TorAmplitude.FaithfullyFlat
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

/-- Canonical Tor amplitude only depends on the isomorphism class in the derived category. -/
private lemma hasTorAmplitudeCanonical_of_iso (R : Type u) [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)} (e : K ≅ L) (a b : ℤ)
    (h : HasTorAmplitudeCanonical R K a b) : HasTorAmplitudeCanonical R L a b :=
  (hasTorAmplitudeCanonical_iff_hasFlatRepresentative R L a b).2
    (hasFlatRepresentative_of_iso e
      ((hasTorAmplitudeCanonical_iff_hasFlatRepresentative R K a b).1 h))

private theorem perfectRingMap_comp
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (hRA : ∀ D : CertifiedDerivedTensoring R,
      RingHom.IsPerfectRingMap R A D.tensor D.comparison D.isLeftDerived)
    (hAB : ∀ D : CertifiedDerivedTensoring A,
      RingHom.IsPerfectRingMap A B D.tensor D.comparison D.isLeftDerived)
    (D : CertifiedDerivedTensoring R) :
    RingHom.IsPerfectRingMap R B D.tensor D.comparison D.isLeftDerived := by
  have hRAcan := hRA (canonicalCertifiedDerivedTensoring R)
  have hABcan := hAB (canonicalCertifiedDerivedTensoring A)
  refine ⟨hRAcan.1.trans hABcan.1, ?_⟩
  change ∃ a b : ℤ, HasTorAmplitude D.tensor D.comparison D.isLeftDerived
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R B)) a b
  let TA := canonicalDerivedTensorProduct A
  obtain ⟨a, b, hRAamp⟩ := hRAcan.2
  obtain ⟨c, d, hABamp⟩ := hABcan.2
  have hRAampCan : HasTorAmplitudeCanonical R
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R A)) a b :=
    (hasTorAmplitudeIn_canonicalCertified_iff R _ a b).mp hRAamp
  have hABampCan : HasTorAmplitudeCanonical A
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A B)) c d :=
    (hasTorAmplitudeIn_canonicalCertified_iff A _ c d).mp hABamp
  let K := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A B)
  let L := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  let RD := (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory
  have eQ (M : ModuleCat.{u} A) : DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app M).symm
  let eK := eQ (ModuleCat.of A B)
  let eL := eQ (ModuleCat.of A A)
  have hK : HasTorAmplitudeCanonical A (DerivedCategory.Q.obj K) c d :=
    hasTorAmplitudeCanonical_of_iso A eK.symm c d hABampCan
  have hL : HasTorAmplitudeCanonical R
      (RD.obj (DerivedCategory.Q.obj L)) a b := by
    have eL' : RD.obj (DerivedCategory.Q.obj L) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R A) :=
      RD.mapIso eL ≪≫
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategorySingleFunctor 0).app
          (ModuleCat.of A A)
        ≪≫ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).mapIso
          (restrictScalarsSelfEquiv R A).toModuleIso
    exact hasTorAmplitudeCanonical_of_iso R eL'.symm a b hRAampCan
  have hcomp := hasTorAmplitudeCanonical_derivedTensorProduct R A K L c d a b hK hL
  let eUnit : (TA.tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj K :=
    ((TA.tensor.obj (DerivedCategory.Q.obj K)).mapIso eL).symm ≪≫
      TA.rightUnitor.app (DerivedCategory.Q.obj K)
  have eK' : RD.obj (DerivedCategory.Q.obj K) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A B)) :=
    (RD.mapIso eK).symm ≪≫
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategorySingleFunctor 0).app
        (ModuleCat.of A B)
  have eRB : (ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A B) ≅
      ModuleCat.of R B := by
    let eAB : (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) ≅
        ModuleCat.of A B := (restrictScalarsSelfEquiv A B).toModuleIso
    let eComp := ModuleCat.restrictScalarsComp'App
      (algebraMap R A) (algebraMap A B) (algebraMap R B)
      (IsScalarTower.algebraMap_eq R A B) (ModuleCat.of B B)
    let eAB' := (ModuleCat.restrictScalars (algebraMap R A)).mapIso eAB
    exact eAB'.symm ≪≫ eComp.symm ≪≫ (restrictScalarsSelfEquiv R B).toModuleIso
  exact ⟨c + a, d + b,
    (hasTorAmplitude_iff_hasFlatRepresentative D.comparison D.isLeftDerived _ _ _).2
      (hasFlatRepresentative_of_iso
        ((RD.mapIso eUnit) ≪≫ eK' ≪≫
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).mapIso eRB))
        ((hasTorAmplitudeCanonical_iff_hasFlatRepresentative R _ _ _).1 hcomp))⟩

/-- **Stacks Project, Tag 0689.** A composition of perfect morphisms of schemes is perfect. -/
@[stacks 0689, instance]
public theorem perfect_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Perfect f] [Perfect g] : Perfect (f ≫ g) := by
  have : LocallyOfFiniteType (f ≫ g) := locallyOfFiniteType_comp f g
  obtain ⟨J, V, hVcover, hVaffine, hVpreimage⟩ :=
    (exists_affine_openCover_perfect_iff_forall g).mpr (Perfect.perfect_appLE (f := g))
  have hcover :
      ∃ (J : Type u) (V : J → Z.Opens),
        IsOpenCover V ∧
          (∀ j, IsAffineOpen (V j)) ∧
          ∀ j, ∃ (I : Type u) (U : I → X.Opens)
            (hU : (⨆ i, U i) = (f ≫ g) ⁻¹ᵁ (V j)),
            (∀ i, IsAffineOpen (U i)) ∧
              ∀ i,
                let q := ((f ≫ g).appLE (V j) (U i) ((le_iSup U i).trans hU.le)).hom
                letI := q.toAlgebra
                ∀ D : CertifiedDerivedTensoring Γ(Z, V j),
                  RingHom.IsPerfectRingMap Γ(Z, V j) Γ(X, U i)
                    D.tensor D.comparison D.isLeftDerived := by
    refine ⟨J, V, hVcover, hVaffine, fun j => ?_⟩
    obtain ⟨I, W, hWcover, hWaffine, hWperfect⟩ := hVpreimage j
    have hW : ∀ i, (W i : Y.Opens) ≤ g ⁻¹ᵁ (V j) := fun i => by
      rw [← hWcover]
      exact le_iSup (fun i => (W i : Y.Opens)) i
    let K := Σ i : I, {U : X.affineOpens // (U : X.Opens) ≤ f ⁻¹ᵁ (W i)}
    let U : K → X.affineOpens := fun k => k.2.1
    have hUcover : ⨆ k : K, (U k : X.Opens) = (f ≫ g) ⁻¹ᵁ (V j) := by
      refine le_antisymm (iSup_le fun k => k.2.2.trans (f.preimage_mono (hW k.1))) fun x hx => ?_
      have hxW : f.base x ∈ ⨆ i, (W i : Y.Opens) := by
        rw [hWcover]
        simpa using hx
      obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxW
      obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAU⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open
          (show x ∈ f ⁻¹ᵁ (W i : Y.Opens) from hxi) (f ⁻¹ᵁ (W i : Y.Opens)).2
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, ⟨⟨A, hA⟩, hAU⟩⟩, hxA⟩
    refine ⟨K, fun k => (U k : X.Opens), hUcover, fun k => (U k).2, fun k => ?_⟩
    have hX : (U k : X.Opens) ≤ f ⁻¹ᵁ (W k.1 : Y.Opens) := k.2.2
    let : Algebra Γ(Z, V j) Γ(Y, W k.1) := (g.appLE (V j) (W k.1) (hW k.1)).hom.toAlgebra
    let : Algebra Γ(Y, W k.1) Γ(X, U k) := (f.appLE (W k.1) (U k) hX).hom.toAlgebra
    let : Algebra Γ(Z, V j) Γ(X, U k) :=
      ((f.appLE (W k.1) (U k) hX).hom.comp
        (g.appLE (V j) (W k.1) (hW k.1)).hom).toAlgebra
    let : IsScalarTower Γ(Z, V j) Γ(Y, W k.1) Γ(X, U k) :=
      IsScalarTower.of_algebraMap_eq' (by simp [RingHom.algebraMap_toAlgebra])
    have hAlg :
        ((f ≫ g).appLE (V j) (U k) (hX.trans (f.preimage_mono (hW k.1)))).hom.toAlgebra =
        ((f.appLE (W k.1) (U k) hX).hom.comp
            (g.appLE (V j) (W k.1) (hW k.1)).hom).toAlgebra :=
      congrArg (fun φ : Γ(Z, V j) →+* Γ(X, U k) => φ.toAlgebra)
        (congrArg CommRingCat.Hom.hom
          (Scheme.Hom.appLE_comp_appLE f g (V j) (W k.1) (U k) (hW k.1) hX).symm)
    intro q Dcert
    rw [hAlg]
    exact perfectRingMap_comp (hWperfect k.1) (Perfect.perfect_appLE (f := f)
      (U k : X.Opens) (U k).2 (W k.1 : Y.Opens) (hWaffine k.1) hX) Dcert
  exact { perfect_appLE := (exists_affine_openCover_perfect_iff_forall (f ≫ g)).mp hcover }

/-- **Stacks 0689** as a morphism-property statement: perfectness of morphisms of schemes is
stable under composition. -/
public instance Perfect.isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition (@Perfect.{u}) where
  comp_mem f g hf hg :=
    let : Perfect f := hf
    let : Perfect g := hg
    inferInstance

/-- Precomposing a perfect morphism of schemes with an étale morphism leaves it perfect, an
étale morphism being flat and locally of finite presentation and hence perfect. -/
public theorem Perfect.respectsLeft_etale :
    MorphismProperty.RespectsLeft (@Perfect.{u}) (@Etale.{u}) where
  precomp i hi f hf :=
    let : Etale i := hi
    let : Perfect f := hf
    inferInstance

/-- Postcomposing a perfect morphism of schemes with an étale morphism leaves it perfect, an
étale morphism being flat and locally of finite presentation and hence perfect. -/
public theorem Perfect.respectsRight_etale :
    MorphismProperty.RespectsRight (@Perfect.{u}) (@Etale.{u}) where
  postcomp i hi f hf :=
    let : Etale i := hi
    let : Perfect f := hf
    inferInstance

end AlgebraicGeometry

end
