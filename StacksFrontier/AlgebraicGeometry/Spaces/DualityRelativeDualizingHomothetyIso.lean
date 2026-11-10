module

public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRelativeDualizingHomothety
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRightAdjointBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedSheafHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectCompact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.RightAdjointCoproducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DistinguishedTrianglesGeneral

/-!
# The homothety map of `a(𝒪_Y)` is an isomorphism once `R𝓗om(a(𝒪_Y), a(𝒪_Y))` is quasi-coherent

Let `f : X ⟶ Y` be a proper, flat morphism of finite presentation of quasi-compact and
quasi-separated algebraic spaces and `ω = a(𝒪_Y)` for the right adjoint `a` of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` (Stacks 0E55). For every perfect `E`, postcomposition with
the homothety map `h : 𝒪_X ⟶ R𝓗om(ω, ω)` is a bijection `Hom(E, 𝒪_X) ⟶ Hom(E, R𝓗om(ω, ω))`.
If `R𝓗om(ω, ω)` lies in `D_QCoh(𝒪_X)`, the cone of `h` is then right orthogonal to the shifts of
a perfect weak generator of `D_QCoh(𝒪_X)` (Stacks 09IY), hence zero: this is the Yoneda step of
the proof of Stacks 0E5V (3).

When `ω` is pseudo-coherent, `R𝓗om(ω, ω)` is quasi-coherent by Stacks 0A8A, since `ω` lies in
`D^+_QCoh(𝒪_X)` by Stacks 0E56.

## Main results

* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedHomothety_rightAdjoint_of_qcohDerived`
* `AlgebraicGeometry.Space.qcohDerived_smallEtaleDerivedSheafHom_rightAdjoint_of_isPseudoCoherent`
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedHomothety_rightAdjoint_of_isPseudoCoherent`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

-- No global `HasDerivedCategory` instance applies to the categories of modules here: the global
-- `SheafOfModules.hasDerivedCategory` needs a `SmallCategory`, and small étale sites are not.
attribute [local instance] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **The homothety map of `a(𝒪_Y)` is invertible when `R𝓗om(a(𝒪_Y), a(𝒪_Y))` is
quasi-coherent** (the Yoneda step of the proof of Stacks 0E5V (3)). Let `f : X ⟶ Y` be proper,
flat and of finite presentation, with `X` and `Y` quasi-compact and quasi-separated, and let
`ω = a(𝒪_Y)`. If `R𝓗om(ω, ω)` lies in `D_QCoh(𝒪_X)`, then `𝒪_X ⟶ R𝓗om(ω, ω)` is an
isomorphism. -/
theorem isIso_smallEtaleDerivedHomothety_rightAdjoint_of_qcohDerived
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1) (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom)
    (hq : QcohDerived B S hS X (((smallEtaleDerivedSheafHom B S hS X).obj
      (op ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj
        (derivedStructureSheaf B S hS Y.1 Y.2)).obj)).obj
      ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj
        (derivedStructureSheaf B S hS Y.1 Y.2)).obj)) :
    IsIso (smallEtaleDerivedHomothety B S hS X ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs
      hYqs).obj (derivedStructureSheaf B S hS Y.1 Y.2)).obj) := by
  obtain ⟨G, hGc, hG⟩ :=
    exists_isCompactObject_isWeakTriangulatedGenerator_of_qcqs B S hS hZ X hXqc hXqs
  let ι := ObjectProperty.ι (QcohDerived B S hS X)
  let src : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 :=
    ⟨_, (derivedStructureSheaf B S hS X.1 X.2).property⟩
  let tgt : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 := ⟨_, hq⟩
  let m : src ⟶ tgt := ObjectProperty.homMk (smallEtaleDerivedHomothety B S hS X
    ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj
      (derivedStructureSheaf B S hS Y.1 Y.2)).obj)
  have hm : IsIso m := by
    refine Pretriangulated.isIso_of_generator_hom_bijective G hG m fun P hP => ?_
    obtain ⟨G', n, e, hG'⟩ := (ObjectProperty.prop_shiftClosure_iff _ _).1 hP
    have heq : G' = G := ((ObjectProperty.singleton_iff _ _).1 hG').symm
    subst heq
    have hPp : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P.obj := by
      obtain ⟨E, hE, ⟨i⟩⟩ :=
        RingedSite.isPerfect_shift_general _ (isPerfect_of_isCompactObject X hXqs G' hGc) n
      exact ⟨E, hE, ⟨i ≪≫ ((ι.commShiftIso n).app G').symm ≪≫ ι.mapIso e.symm⟩⟩
    have hb := bijective_comp_smallEtaleDerivedHomothety_rightAdjoint hZ f hXqc hXqs hYqs hYqc
      hf hfl hfp P.obj hPp
    let e (Z : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :=
      (ObjectProperty.fullyFaithfulι (QcohDerived B S hS X)).homEquiv (X := P) (Y := Z)
    have key : (fun φ : P ⟶ src => φ ≫ m) = (e tgt).symm ∘
        (fun φ : P.obj ⟶ src.obj => φ ≫ smallEtaleDerivedHomothety B S hS X
          ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj
            (derivedStructureSheaf B S hS Y.1 Y.2)).obj) ∘ e src := by
      funext φ
      exact ObjectProperty.hom_ext _ rfl
    rw [key]
    exact (e tgt).symm.bijective.comp (hb.comp (e src).bijective)
  exact (inferInstance : IsIso (ι.map m))

/-- **`R𝓗om(a(𝒪_Y), a(𝒪_Y))` is quasi-coherent when `a(𝒪_Y)` is pseudo-coherent**: `a(𝒪_Y)`
lies in `D^+_QCoh(𝒪_X)` (Stacks 0E56), so Stacks 0A8A applies. -/
theorem qcohDerived_smallEtaleDerivedSheafHom_rightAdjoint_of_isPseudoCoherent
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1) (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hω : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent
      ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj
        (derivedStructureSheaf B S hS Y.1 Y.2)).obj) :
    QcohDerived B S hS X (((smallEtaleDerivedSheafHom B S hS X).obj
      (op ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj
        (derivedStructureSheaf B S hS Y.1 Y.2)).obj)).obj
      ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj
        (derivedStructureSheaf B S hS Y.1 Y.2)).obj) := by
  have hO : DerivedCategoryB.IsBoundedBelow (derivedStructureSheaf B S hS Y.1 Y.2).obj := by
    refine ⟨0, fun n hn => ?_⟩
    change IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj _))
    exact DerivedCategory.isZero_of_isGE _ 0 n hn
  exact qcohDerived_smallEtaleDerivedSheafHom X _ _ (Or.inl ⟨hω,
    (quasicoherentDerivedRightAdjoint_boundedBelow hZ f hXqc hXqs hYqs hYqc).1 _ hO,
    ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj
      (derivedStructureSheaf B S hS Y.1 Y.2)).property⟩)

/-- **The homothety map of `a(𝒪_Y)` is invertible when `a(𝒪_Y)` is pseudo-coherent** (the proof
of Stacks 0E5V (3), granted the pseudo-coherence that Stacks 0E5V (1) provides). -/
theorem isIso_smallEtaleDerivedHomothety_rightAdjoint_of_isPseudoCoherent
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1) (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom)
    (hω : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent
      ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj
        (derivedStructureSheaf B S hS Y.1 Y.2)).obj) :
    IsIso (smallEtaleDerivedHomothety B S hS X ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs
      hYqs).obj (derivedStructureSheaf B S hS Y.1 Y.2)).obj) :=
  isIso_smallEtaleDerivedHomothety_rightAdjoint_of_qcohDerived hZ f hXqc hXqs hYqs hYqc hf hfl hfp
    (qcohDerived_smallEtaleDerivedSheafHom_rightAdjoint_of_isPseudoCoherent hZ f hXqc hXqs hYqs
      hYqc hω)

end AlgebraicGeometry.Space

end
