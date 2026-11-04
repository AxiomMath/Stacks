module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.Perfect.Morphism
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.RestrictHomology
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Homology.Perfect.LargeUniverse
public import StacksFrontier.Homology.PseudoCoherent.Characterization
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.RingTheory.PseudoCoherentMap.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LocalCriterion
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.AffineFiniteProjective
public import StacksCore.Tactic.StacksAttribute

/-!
# The direct image of the structure sheaf under a perfect closed immersion

Let `i : Z ⟶ X` be a closed immersion of schemes which is perfect, that is, locally of finite
type and such that the induced map on sections over any compatible pair of affine opens is a
perfect ring map. Then `i_*𝒪_Z` is a perfect `𝒪_X`-module: the complex consisting of it in
degree zero is a perfect object of the derived category of `𝒪_X`-modules.

## Main results

* `AlgebraicGeometry.isPerfectModule_sections_of_perfect_isClosedImmersion`: over an affine open
  `V` of `X`, the ring `Γ(Z, i⁻¹V)` is a perfect `Γ(X, V)`-module.
* `AlgebraicGeometry.isPerfect_pushforward_structureSheaf`: the direct image `i_*𝒪_Z` is a
  perfect object of `D(𝒪_X)`.

## Implementation notes

The proof is the local one: on an affine open `V ⊆ X` the preimage `i⁻¹V` is again affine, and
the map on sections `Γ(X, V) ⟶ Γ(Z, i⁻¹V)` is both surjective — because `i` is a closed
immersion — and a perfect ring map — because `i` is perfect. A surjective perfect ring map
presents its target as a perfect module over its source, so `Γ(Z, i⁻¹V)` admits a finite
resolution by finite projective `Γ(X, V)`-modules; the associated complex of modules on
`Spec Γ(X, V)` is strictly perfect, and transporting it along `V ≅ Spec Γ(X, V)` produces a
strictly perfect model of `(i_*𝒪_Z)|_V`. The local criterion for perfectness then concludes.

Surjectivity of the map on sections is used through a presentation with no variables: the
polynomial algebra on the empty type over `Γ(X, V)` surjects onto `Γ(Z, i⁻¹V)`, which is what
pseudo-coherence of a ring map refers to, and the empty polynomial algebra is identified with the
base ring. This is why no base change of the perfectness of `i` along the open immersion
`V ⟶ X` is needed: the defining condition of a perfect morphism already speaks about the affine
opens `i⁻¹V ⊆ Z` and `V ⊆ X` of the original schemes, and the comparison of `V` with
`Spec Γ(X, V)` is `AlgebraicGeometry.Scheme.Opens.toSpecΓ_naturality`.

Two derived categories of modules are in play and they use different models. The derived
categories of modules over a ring, and those of modules on the affine schemes and open subspaces
occurring locally, are the standard ones, since that is the model in which perfectness of a ring
map and of a module over a ring are stated. The derived category of `𝒪_X`-modules, in which the
conclusion lives, is left arbitrary, exactly as in the local criterion for perfectness; the two
meet only where that criterion is applied.

The modules on an open subscheme and the modules on the corresponding open subspace of the
underlying ringed space are identified by
`Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict`, and the direct image
along `i` commutes with restriction to `V` by
`Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`.

## References

* [Stacks Project, Tag 0G2E](https://stacks.math.columbia.edu/tag/0G2E)
* [Stacks Project, Tag 0687](https://stacks.math.columbia.edu/tag/0687)
* [Stacks Project, Tag 068Y](https://stacks.math.columbia.edu/tag/068Y)
* [Stacks Project, Tag 08CN](https://stacks.math.columbia.edu/tag/08CN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open AlgebraicGeometry.RingedSpace (restrictModules)

namespace AlgebraicGeometry

universe u d

attribute [local instance] HasDerivedCategory.standard

/-! ### A surjective perfect ring map presents a perfect module -/

/-- **A surjective perfect ring map makes its target a perfect module over its source.**
Pseudo-coherence of the ring map, read through the presentation with no variables that
surjectivity provides, says that the target is pseudo-coherent as a module; finite Tor dimension
supplies a flat representative in a bounded range, and the two together are perfectness. -/
private theorem isPerfectModule_of_surjective_isPerfectRingMap
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f)
    (D : StacksDraft.TorAmplitude.CertifiedDerivedTensoring R)
    (hD : letI := f.toAlgebra
      RingHom.IsPerfectRingMap R S D.tensor D.comparison D.isLeftDerived) :
    letI : Algebra R S := f.toAlgebra
    StacksDraft.Perfect.IsPerfectModule (R := R) S := by
  let : Algebra R S := f.toAlgebra
  obtain ⟨hpcm, htor⟩ := hD
  obtain ⟨_, hpc⟩ :=
    Algebra.pseudoCoherent_iff_exists_isModuleRelativelyPseudoCoherent.mp hpcm
  let eA := MvPolynomial.isEmptyAlgEquiv R (Fin 0)
  let fAlg : R →ₐ[R] S := AlgHom.mk f fun _ => rfl
  let α : MvPolynomial (Fin 0) R →ₐ[R] S := fAlg.comp eA
  have hα : Function.Surjective α := fun b =>
    let ⟨r, hr⟩ := hf b
    ⟨eA.symm r, by simp [α, fAlg, hr]⟩
  let Kₛ := (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj
    (ModuleCat.of S S)
  have hpcα : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj Kₛ) :=
    (StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _).2 fun m => hpc m 0 α hα
  let Kᵣ := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
    (ModuleCat.of R S)
  let G := ModuleCat.restrictScalars.{u} f
  let H := ModuleCat.restrictScalars.{u} eA.toRingHom
  let F := ModuleCat.restrictScalars.{u} α.toRingHom
  let : Module R S := Module.compHom S f
  let eMod : G.obj (ModuleCat.of S S) ≅ ModuleCat.of R S := eqToIso rfl
  let eG := (G.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of S S) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).mapIso eMod
  have hcompRing : α.toRingHom = f.comp eA.toRingHom := by
    ext x <;> simp [α, fAlg]
  let eFun := ModuleCat.restrictScalarsComp' eA.toRingHom f α.toRingHom hcompRing
  have eF : F.mapDerivedCategory.obj Kₛ ≅ H.mapDerivedCategory.obj Kᵣ :=
    (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryIsoOfNatIso
        F (G ⋙ H) eFun).app Kₛ ≪≫
      (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso G H).app Kₛ ≪≫
      H.mapDerivedCategory.mapIso eG
  have hpcR : StacksDraft.PseudoCoherence.IsPseudoCoherent Kᵣ :=
    (StacksDraft.PseudoCoherence.pseudoCoherent_iff_of_ringEquiv eA.toRingEquiv Kᵣ).2.mpr
      ((PseudoCoherence.pseudoCoherent_iso eF).2 hpcα)
  obtain ⟨a, b, hamp⟩ := htor
  show StacksDraft.Perfect.IsPerfect Kᵣ
  exact (StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension Kᵣ).1.mpr
    ⟨hpcR, a, b, (StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasFlatRepresentative
      D.comparison D.isLeftDerived Kᵣ a b).mp hamp⟩

/-! ### Sections over an affine open -/

/-- **Over an affine open of the target, a perfect closed immersion makes the sections of the
source a perfect module over the sections of the target.** The preimage of an affine open under a
closed immersion is affine, and the map on sections over that pair of affine opens is both
surjective and a perfect ring map. -/
theorem isPerfectModule_sections_of_perfect_isClosedImmersion {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [Perfect i] (V : X.Opens) (hV : IsAffineOpen V) :
    letI : Algebra Γ(X, V) Γ(Z, i ⁻¹ᵁ V) := (i.app V).hom.toAlgebra
    StacksDraft.Perfect.IsPerfectModule (R := Γ(X, V)) Γ(Z, i ⁻¹ᵁ V) := by
  let D := StacksDraft.TorAmplitude.canonicalCertifiedDerivedTensoring Γ(X, V)
  have hperfect := (inferInstance : Perfect i).perfect_appLE (i ⁻¹ᵁ V) (hV.preimage i) V hV
    le_rfl D
  rw [Scheme.Hom.appLE_eq_app] at hperfect
  exact isPerfectModule_of_surjective_isPerfectRingMap (i.app V).hom
    (i.app_surjective V hV) D hperfect

/-- A finite free module sheaf on a ringed space is the coproduct of copies of the structure
sheaf indexed by a universe-lifted finite type. -/
private def finiteFreeIsoFree (X : RingedSpace.{u, u}) (n : ℕ) :
    StrictlyPerfect.finiteFree X n ≅
      SheafOfModules.free (R := StrictlyPerfect.structureSheafOfRings X)
        (ULift.{u} (Fin n)) := by
  change (⨁ fun _ : Fin n => StrictlyPerfect.structureModule X) ≅
    (∐ fun _ : ULift.{u} (Fin n) => StrictlyPerfect.structureModule X)
  exact (biproduct.whiskerEquiv
      (Equiv.ulift.{u, 0}.symm : Fin n ≃ ULift.{u} (Fin n))
      (fun _ => Iso.refl _)).trans
    (biproduct.isoCoproduct (fun _ : ULift.{u} (Fin n) =>
      StrictlyPerfect.structureModule X))

/-! ### Strictly perfect local models -/

/-- **Strict perfection is preserved by the inverse image along an isomorphism of schemes.**
The inverse image is a left adjoint, hence preserves the finite coproducts and the retracts
witnessing that a module is a direct summand of a finite free one. -/
private theorem isStrictlyPerfect_pullback_of_iso
    {A B : Scheme.{u}} (e : A ≅ B)
    (P : CochainComplex (OXMod.{u, u} B.toRingedSpace) ℤ)
    (hP : IsStrictlyPerfect P) :
    IsStrictlyPerfect (((Scheme.Modules.pullback e.hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P) := by
  let F := Scheme.Modules.pullback e.hom
  let adj := Scheme.Modules.pullbackPushforwardAdjunction e.hom
  let : F.Additive := by infer_instance
  let : F.IsLeftAdjoint := adj.isLeftAdjoint
  let eUnit : F.obj (SheafOfModules.unit B.ringCatSheaf) ≅
      SheafOfModules.unit A.ringCatSheaf :=
    (Scheme.Modules.restrictFunctorIsoPullback e.hom).symm.app _ ≪≫
      Scheme.Modules.restrictUnitIso e.hom
  refine ⟨?_, ?_⟩
  · exact hP.bounded.subset fun i hi hzero => hi (F.map_isZero hzero)
  · intro i
    show StrictlyPerfect.IsDirectSummandOfFiniteFree (F.obj (P.X i))
    obtain ⟨n, ⟨r⟩⟩ := (StrictlyPerfect.isDirectSummandOfFiniteFree_iff_retract
      (X := B.toRingedSpace) (E := P.X i)).mp (hP.directSummand i)
    let : PreservesColimitsOfShape (Discrete (ULift.{u} (Fin n))) F :=
      adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
    let fam : Discrete (ULift.{u} (Fin n)) ⥤ OXMod.{u, u} B.toRingedSpace :=
      Discrete.functor (fun _ : ULift.{u} (Fin n) => SheafOfModules.unit B.ringCatSheaf)
    let fam' : Discrete (ULift.{u} (Fin n)) ⥤ OXMod.{u, u} A.toRingedSpace :=
      Discrete.functor (fun _ : ULift.{u} (Fin n) => SheafOfModules.unit A.ringCatSheaf)
    let : HasColimitsOfShape (Discrete (ULift.{u} (Fin n)))
        (OXMod.{u, u} B.toRingedSpace) := inferInstance
    let eFam : fam ⋙ F ≅ fam' := Discrete.natIso (fun _ => eUnit)
    let eCop := IsColimit.coconePointsIsoOfNatIso
      (colimit.isColimit (fam ⋙ F)) (colimit.isColimit fam') eFam
    let eFree : F.obj (StrictlyPerfect.finiteFree B.toRingedSpace n) ≅
        StrictlyPerfect.finiteFree A.toRingedSpace n :=
      F.mapIso (StrictlyPerfect.finiteFreeIsoFree B.toRingedSpace n) ≪≫
      (@preservesColimitIso _ _ _ _ F _ _ fam
        (adj.leftAdjoint_preservesColimits.preservesColimitsOfShape.preservesColimit)
        (HasColimitsOfShape.has_colimit fam)) ≪≫ eCop ≪≫
      (StrictlyPerfect.finiteFreeIsoFree A.toRingedSpace n).symm
    exact (StrictlyPerfect.isDirectSummandOfFiniteFree_iff_retract
      (X := A.toRingedSpace) (E := F.obj (P.X i))).mpr
      ⟨n, ⟨(r.map F).trans eFree.retract⟩⟩

/-- **A perfect module over a ring has a strictly perfect model on the spectrum.** A bounded
resolution of the module by finite projective modules becomes, under `M ↦ M^~`, a strictly
perfect complex representing the module placed in degree zero. -/
private theorem exists_isStrictlyPerfect_tilde_model
    {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (hM : StacksDraft.Perfect.IsPerfectModule (R := R) M) :
    ∃ P : CochainComplex (OXMod.{u, u} (Spec R).toRingedSpace) ℤ,
      IsStrictlyPerfect P ∧ Nonempty (DerivedCategory.Q.obj P ≅
        (DerivedCategory.singleFunctor
          (OXMod.{u, u} (Spec R).toRingedSpace) 0).obj
            ((AlgebraicGeometry.tilde.functor R).obj M)) := by
  change StacksDraft.Perfect.IsPerfect
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) at hM
  obtain ⟨P, a, b, hGE, hLE, hfinite, hprojective, ⟨e⟩⟩ := hM
  let F : ModuleCat.{u} R ⥤ OXMod.{u, u} ((Spec R).toRingedSpace) :=
    AlgebraicGeometry.tilde.functor R
  let : P.IsStrictlyGE a := hGE
  let : P.IsStrictlyLE b := hLE
  let : F.Additive := inferInstanceAs (AlgebraicGeometry.tilde.functor R).Additive
  let : PreservesFiniteLimits F :=
    AlgebraicGeometry.tilde.preservesFiniteLimits R
  let : PreservesFiniteColimits F :=
    Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor R
  let T := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hbdd : {i : ℤ | ¬ IsZero (P.X i)}.Finite := by
    apply Set.Finite.subset (Set.finite_Icc a b)
    intro i hi
    simp only [Set.mem_ofPred_eq] at hi
    have hia : ¬ i < a := fun hia => hi (P.isZero_of_isStrictlyGE a i hia)
    have hib : ¬ b < i := fun hib => hi (P.isZero_of_isStrictlyLE b i hib)
    exact ⟨le_of_not_gt hia, le_of_not_gt hib⟩
  have hT : IsStrictlyPerfect T :=
    Stacks.AffineTilde.isStrictlyPerfect_tildeComplex_of_projective P hbdd
      (fun i => ⟨hfinite i, hprojective i⟩)
  let eSingle := (F.mapDerivedCategorySingleFunctor 0).app M
  let eTilde : F.mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ≅
      DerivedCategory.Q.obj T :=
      F.mapDerivedCategory.mapIso e ≪≫ (F.mapDerivedCategoryFactors.app P)
  exact ⟨T, hT, ⟨eTilde.symm ≪≫ eSingle⟩⟩

/-! ### Comparison of the direct image with a tilde -/

/-- **Restriction of modules along an open immersion preserves finite limits.** The underlying
presheaf of the restriction is the restriction of the underlying presheaf, and restricting a
presheaf along a functor on opens is computed sectionwise. -/
private lemma preservesFiniteLimits_restrictFunctor {A B : Scheme.{u}}
    (f : A ⟶ B) [IsOpenImmersion f] :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) := by
  have : PreservesLimitsOfSize.{0, 0} (Scheme.Modules.toPresheaf B) :=
    preservesLimitsOfSize_shrink _
  have : PreservesFiniteLimits (Scheme.Modules.toPresheaf B) := inferInstance
  have : PreservesFiniteLimits
      ((Functor.whiskeringLeft _ _ Ab.{u}).obj f.opensFunctor.op) := inferInstance
  have e : Scheme.Modules.restrictFunctor f ⋙ Scheme.Modules.toPresheaf A ≅
      Scheme.Modules.toPresheaf B ⋙
        (Functor.whiskeringLeft _ _ _).obj f.opensFunctor.op := Iso.refl _
  have : PreservesFiniteLimits
      (Scheme.Modules.restrictFunctor f ⋙ Scheme.Modules.toPresheaf A) :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (Scheme.Modules.toPresheaf A)

/-- The direct image of the structure sheaf along an isomorphism of schemes is the structure
sheaf: the canonical map is an isomorphism because it is one on sections. -/
private def pushforwardUnitIsoOfIso
    {A B : Scheme.{u}} (e : A ≅ B) :
      (Scheme.Modules.pushforward e.hom).obj (SheafOfModules.unit A.ringCatSheaf) ≅
      SheafOfModules.unit B.ringCatSheaf := by
  let p := SheafOfModules.unitToPushforwardObjUnit e.hom.toRingCatSheafHom
  have hp : IsIso p := Scheme.Modules.Hom.isIso_iff_isIso_app.2 fun U => by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact (ConcreteCategory.isIso_iff_bijective (e.hom.app U)).mp inferInstance
  exact (asIso p).symm

/-- **The direct image of the structure sheaf along a morphism of affine schemes is a tilde.**
Presenting both schemes as spectra compatibly with a ring map `φ`, the direct image of `𝒪_A`
becomes the inverse image along `B ≅ Spec R` of the module associated to the target ring viewed
as a module over the source ring. -/
private def pushforwardUnitIsoTilde
    {A B : Scheme.{u}} {R S : CommRingCat.{u}} (f : A ⟶ B)
    (eA : A ≅ Spec S) (eB : B ≅ Spec R) (φ : R ⟶ S)
    (hc : eA.hom ≫ Spec.map φ = f ≫ eB.hom) :
    letI : Algebra R S := φ.hom.toAlgebra
    (Scheme.Modules.pushforward f).obj (SheafOfModules.unit A.ringCatSheaf) ≅
      (Scheme.Modules.pullback eB.hom).obj
        ((AlgebraicGeometry.tilde.functor R).obj (ModuleCat.of R S)) := by
  letI : Algebra R S := φ.hom.toAlgebra
  let F := AlgebraicGeometry.tilde.functor R
  let eMod : (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S) ≅
      ModuleCat.of R S := eqToIso rfl
  let k := Spec.map φ
  let ePush : (Scheme.Modules.pushforward eB.hom).obj
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit A.ringCatSheaf)) ≅
      (Scheme.Modules.pushforward k).obj (SheafOfModules.unit (Spec S).ringCatSheaf) :=
    (Scheme.Modules.pushforwardComp f eB.hom).app _ ≪≫
      (Scheme.Modules.pushforwardCongr hc.symm).app _ ≪≫
      (Scheme.Modules.pushforwardComp eA.hom k).app _ ≪≫
      (Scheme.Modules.pushforward k).mapIso (pushforwardUnitIsoOfIso eA)
  let eTilde : (Scheme.Modules.pushforward k).obj
      (SheafOfModules.unit (Spec S).ringCatSheaf) ≅ F.obj (ModuleCat.of R S) :=
    (Scheme.Modules.pushforward k).mapIso
        (AlgebraicGeometry.tildeSelf (R := S)).symm ≪≫
      (AlgebraicGeometry.pushforwardTildeIso R S φ).app (ModuleCat.of S S) ≪≫
      F.mapIso eMod
  let Mloc := (Scheme.Modules.pushforward f).obj (SheafOfModules.unit A.ringCatSheaf)
  let ePull : Mloc ≅ (Scheme.Modules.pullback eB.hom).obj
      ((Scheme.Modules.pushforward eB.hom).obj Mloc) :=
    ((Scheme.Modules.restrictFunctorAdjCounitIso eB.hom).app Mloc).symm ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback eB.hom).app
        ((Scheme.Modules.pushforward eB.hom).obj Mloc)
  exact ePull ≪≫ (Scheme.Modules.pullback eB.hom).mapIso (ePush ≪≫ eTilde)

/-- **The restriction of `i_*𝒪_Z` to an affine open is a tilde.** Restriction commutes with the
direct image, the restriction of `𝒪_Z` is the structure sheaf of the open subscheme, and the
morphism of open subschemes induced by `i` is a morphism of affine schemes presented by the map
on sections. -/
private def restrictPushforwardUnitIsoTilde {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (V : X.Opens) (hV : IsAffineOpen V) :
    letI : Algebra Γ(X, V) Γ(Z, i ⁻¹ᵁ V) := (i.app V).hom.toAlgebra
    (restrictModules X.toRingedSpace V).obj
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)) ≅
      (Scheme.Modules.pullback hV.isoSpec.hom).obj
        ((AlgebraicGeometry.tilde.functor Γ(X, V)).obj
          (ModuleCat.of Γ(X, V) Γ(Z, i ⁻¹ᵁ V))) := by
  have hW : IsAffineOpen (i ⁻¹ᵁ V) := hV.preimage i
  letI : IsAffine V.toScheme := hV
  letI : IsAffine (i ⁻¹ᵁ V).toScheme := hW
  letI : Algebra Γ(X, V) Γ(Z, i ⁻¹ᵁ V) := (i.app V).hom.toAlgebra
  exact (Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict X V).app _ ≪≫
    (Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso i V).app _ ≪≫
    (Scheme.Modules.pushforward (i ∣_ V)).mapIso
      (Scheme.Modules.restrictUnitIso (i ⁻¹ᵁ V).ι) ≪≫
    pushforwardUnitIsoTilde (i ∣_ V) hW.isoSpec hV.isoSpec (i.app V)
      (Scheme.Opens.toSpecΓ_naturality i V)

/-! ### The theorem -/

/-- **Stacks 0G2E.** If `i : Z ⟶ X` is a perfect closed immersion of schemes then `i_*𝒪_Z` is a
perfect `𝒪_X`-module, that is, a perfect object of the derived category of `𝒪_X`-modules. -/
@[stacks 0G2E]
theorem isPerfect_pushforward_structureSheaf {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [Perfect i]
    [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)] :
    RingedSpace.IsPerfect
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))) := by
  classical
  let E : OXMod.{u, u} X.toRingedSpace :=
    (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  let K := (DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj E
  let F : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ :=
    (CochainComplex.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj E
  refine RingedSpace.isPerfect_of_strictlyPerfect_local_models X.toRingedSpace K
    ⟨F, ⟨Iso.refl _⟩, X.affineOpens, (fun W => (W : X.Opens)), iSup_affineOpens_eq_top X, ?_⟩
  rintro ⟨V, hV⟩
  let : IsAffine V.toScheme := hV
  let R := Γ(X, V)
  let : Algebra Γ(X, V) Γ(Z, i ⁻¹ᵁ V) := (i.app V).hom.toAlgebra
  let M : ModuleCat.{u} R := ModuleCat.of Γ(X, V) Γ(Z, i ⁻¹ᵁ V)
  obtain ⟨P₀, hP₀, ⟨e₀⟩⟩ := exists_isStrictlyPerfect_tilde_model M
    (isPerfectModule_sections_of_perfect_isClosedImmersion i V hV)
  let eV := hV.isoSpec
  let H := Scheme.Modules.pullback eV.hom
  let : H.Additive := by infer_instance
  let : H.IsLeftAdjoint := (Scheme.Modules.pullbackPushforwardAdjunction eV.hom).isLeftAdjoint
  let : PreservesFiniteColimits H := ⟨fun _ _ _ => inferInstance⟩
  let : PreservesFiniteLimits (Scheme.Modules.restrictFunctor eV.hom) :=
    preservesFiniteLimits_restrictFunctor eV.hom
  let : PreservesFiniteLimits H := preservesFiniteLimits_of_natIso
    (F := Scheme.Modules.restrictFunctor eV.hom) (G := H)
    (Scheme.Modules.restrictFunctorIsoPullback eV.hom)
  let G := restrictModules X.toRingedSpace V
  let P : CochainComplex (OXMod.{u, u} (X.toRingedSpace.restrict V.isOpenEmbedding)) ℤ :=
    (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj P₀
  let eLocal : G.obj E ≅ H.obj ((AlgebraicGeometry.tilde.functor R).obj M) :=
    restrictPushforwardUnitIsoTilde i V hV
  refine ⟨P, isStrictlyPerfect_pullback_of_iso eV P₀ hP₀, ⟨?_⟩⟩
  exact (H.mapDerivedCategoryFactors.app P₀).symm ≪≫
    H.mapDerivedCategory.mapIso e₀ ≪≫
    (H.mapDerivedCategorySingleFunctor 0).app
      ((AlgebraicGeometry.tilde.functor R).obj M) ≪≫
    (DerivedCategory.singleFunctor
      (OXMod.{u, u} (X.toRingedSpace.restrict V.isOpenEmbedding)) 0).mapIso eLocal.symm ≪≫
    DerivedCategory.Q.mapIso ((G.mapCochainComplexSingleFunctor 0).app E).symm

end AlgebraicGeometry

end
