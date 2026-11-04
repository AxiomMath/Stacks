module

public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceQuasiCoherentCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.QcqsDerivedCoherator
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPushforwardTrace
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRightAdjointBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedSheafHomQuasicoherent
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedStrictlyPerfectModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedFibreBettiRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSetBaseChangeMateIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.InterfaceUnitNaturality

/-!
# When the trace map `Rf_*R𝓗om(L, a(K)) ⟶ R𝓗om(Rf_*L, K)` is an isomorphism

Let `f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated algebraic spaces, `a` the
right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, `L` in `D_QCoh(𝒪_X)` and `K` in
`D_QCoh(𝒪_Y)`. By Stacks 0CR5, `DQ_Y(Rf_*R𝓗om(L, a(K))) = Rf_*DQ_X(R𝓗om(L, a(K)))`. If
`R𝓗om(L, a(K))` has quasi-coherent cohomology the coherator may be erased on the source of the
map of Stacks 0E58, and if `R𝓗om(Rf_*L, K)` has, on its target; if both, the map of Stacks 0E57
is an isomorphism. With Stacks 0A8A this happens if `L` and `Rf_*L` are perfect, or if `K` is
bounded below and `L` and `Rf_*L` are pseudo-coherent (Stacks 0GG4).

## Main results

* `AlgebraicGeometry.Space.coheratorPushforwardSheafHomIso`,
  `AlgebraicGeometry.Space.isIso_coherator_counit_pushforward_sheafHom`,
  `AlgebraicGeometry.Space.isIso_coherator_counit_sheafHom_pushforward`,
  `AlgebraicGeometry.Space.isIso_smallEtalePushforwardTrace_of_qcohDerived`,
  `AlgebraicGeometry.Space.isIso_smallEtalePushforwardTrace_of_isPerfect`,
  `AlgebraicGeometry.Space.isIso_smallEtalePushforwardTrace_of_isPseudoCoherent`:
  **Stacks 0GG4**.

## References

* [Stacks Project, Tag 0GG4](https://stacks.math.columbia.edu/tag/0GG4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}
  (hZ : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y) (hXqc : IsQuasiCompactSpace B S hS X.1)
  (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
  (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)

/-- **Stacks 0GG4, the identification of the coherators.** For right adjoints `DQ_X`, `DQ_Y` of
the inclusions `D_QCoh ⟶ D`, `DQ_Y(Rf_*R𝓗om(L, a(K))) ≅ Rf_*DQ_X(R𝓗om(L, a(K)))` (Stacks 0CR5). -/
@[stacks 0GG4 "the identification of the coherators by Stacks 0CR5"]
def coheratorPushforwardSheafHomIso
    {DQX : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2}
    {DQY : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2}
    (adjX : (QcohDerived B S hS X).ι ⊣ DQX) (adjY : (QcohDerived B S hS Y).ι ⊣ DQY)
    (L : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    DQY.obj ((derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedSheafHom B S hS X).obj (op L.obj)).obj
          ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K).obj)) ≅
      (quasicoherentDerivedPushforward B S hS f
          (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom)
          (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs f.hom)).obj
        (DQX.obj (((smallEtaleDerivedSheafHom B S hS X).obj (op L.obj)).obj
          ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K).obj)) :=
  ((quasicoherentDerivedPushforwardCompCoheratorIso B S hS f
    (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom)
    (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs f.hom)
    adjX adjY).app _).symm

/-- **Stacks 0GG4, erasing the coherator on the source.** If `R𝓗om(L, a(K))` has
quasi-coherent cohomology, then `DQ_Y(Rf_*R𝓗om(L, a(K))) ⟶ Rf_*R𝓗om(L, a(K))` is an
isomorphism. -/
@[stacks 0GG4 "erasing the coherator on the source of the map of Stacks 0E58"]
theorem isIso_coherator_counit_pushforward_sheafHom
    {DQ : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2}
    (adjQ : (QcohDerived B S hS Y).ι ⊣ DQ)
    (L : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2)
    (h : QcohDerived B S hS X (((smallEtaleDerivedSheafHom B S hS X).obj (op L.obj)).obj
      ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K).obj)) :
    IsIso (adjQ.counit.app ((derivedModulePushforward B S hS f).obj
      (((smallEtaleDerivedSheafHom B S hS X).obj (op L.obj)).obj
        ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K).obj))) :=
  Stacks.Duality.isIso_counit_app_of_prop adjQ
    (qcohDerived_derivedModulePushforward_obj B S hS f
      (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom)
      (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs f.hom) _ h)

/-- **Stacks 0GG4, erasing the coherator on the target.** If `R𝓗om(Rf_*L, K)` has
quasi-coherent cohomology, then `DQ_Y(R𝓗om(Rf_*L, K)) ⟶ R𝓗om(Rf_*L, K)` is an isomorphism. -/
@[stacks 0GG4 "erasing the coherator on the target of the map of Stacks 0E58"]
theorem isIso_coherator_counit_sheafHom_pushforward
    {DQ : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2}
    (adjQ : (QcohDerived B S hS Y).ι ⊣ DQ)
    (L : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2)
    (h : QcohDerived B S hS Y (((smallEtaleDerivedSheafHom B S hS Y).obj
      (op ((derivedModulePushforward B S hS f).obj L.obj))).obj K.obj)) :
    IsIso (adjQ.counit.app (((smallEtaleDerivedSheafHom B S hS Y).obj
      (op ((derivedModulePushforward B S hS f).obj L.obj))).obj K.obj)) :=
  Stacks.Duality.isIso_counit_app_of_prop adjQ h

/-- **Stacks 0GG4, the quasi-coherence criterion.** If `R𝓗om(L, a(K))` and `R𝓗om(Rf_*L, K)` both
have quasi-coherent cohomology, then the map `Rf_*R𝓗om(L, a(K)) ⟶ R𝓗om(Rf_*L, K)` of
Stacks 0E57 is an isomorphism. -/
@[stacks 0GG4 "the map of Stacks 0E57 is an isomorphism if both sides have quasi-coherent \
cohomology"]
theorem isIso_smallEtalePushforwardTrace_of_qcohDerived
    (L : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2)
    (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hA : QcohDerived B S hS X (((smallEtaleDerivedSheafHom B S hS X).obj (op L.obj)).obj
      ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K).obj))
    (hB : QcohDerived B S hS Y (((smallEtaleDerivedSheafHom B S hS Y).obj
      (op ((derivedModulePushforward B S hS f).obj L.obj))).obj K.obj)) :
    IsIso (smallEtalePushforwardTrace hZ f hXqc hXqs hYqs L K) := by
  have := isLeftAdjoint_ι_qcohDerived hZ Y hYqc hYqs
  let adjQ := Adjunction.ofIsLeftAdjoint (QcohDerived B S hS Y).ι
  exact Stacks.Duality.isIso_of_isIso_rightAdjoint_map adjQ _
    (isIso_coherator_counit_pushforward_sheafHom hZ f hXqc hXqs hYqs adjQ L K hA)
    (isIso_coherator_counit_sheafHom_pushforward f adjQ L K hB)
    (isIso_coherator_map_smallEtalePushforwardTrace hZ f hXqc hXqs hYqs adjQ L K)

/-- **Stacks 0GG4 (1).** If `L` and `Rf_*L` are perfect, then the map
`Rf_*R𝓗om(L, a(K)) ⟶ R𝓗om(Rf_*L, K)` of Stacks 0E57 is an isomorphism. -/
@[stacks 0GG4 "(1)"]
theorem isIso_smallEtalePushforwardTrace_of_isPerfect
    (L : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2)
    (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hL : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) L.obj)
    (hfL : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
      ((derivedModulePushforward B S hS f).obj L.obj)) :
    IsIso (smallEtalePushforwardTrace hZ f hXqc hXqs hYqs L K) :=
  isIso_smallEtalePushforwardTrace_of_qcohDerived hZ f hXqc hXqs hYqs L K hYqc
    (qcohDerived_smallEtaleDerivedSheafHom X _ _
      (Or.inr ⟨hL, ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K).property⟩))
    (qcohDerived_smallEtaleDerivedSheafHom Y _ _ (Or.inr ⟨hfL, K.property⟩))

/-- **Stacks 0GG4 (2).** If `K` is bounded below and `L` and `Rf_*L` are pseudo-coherent, then
the map `Rf_*R𝓗om(L, a(K)) ⟶ R𝓗om(Rf_*L, K)` of Stacks 0E57 is an isomorphism. -/
@[stacks 0GG4 "(2)"]
theorem isIso_smallEtalePushforwardTrace_of_isPseudoCoherent
    (L : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2)
    (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hK : DerivedCategoryB.IsBoundedBelow K.obj)
    (hL : RingedSite.IsPseudoCoherent (smallEtaleRingedSite B S hS X.1 X.2) L.obj)
    (hfL : RingedSite.IsPseudoCoherent (smallEtaleRingedSite B S hS Y.1 Y.2)
      ((derivedModulePushforward B S hS f).obj L.obj)) :
    IsIso (smallEtalePushforwardTrace hZ f hXqc hXqs hYqs L K) :=
  isIso_smallEtalePushforwardTrace_of_qcohDerived hZ f hXqc hXqs hYqs L K hYqc
    (qcohDerived_smallEtaleDerivedSheafHom X _ _ (Or.inl ⟨hL,
      ⟨(quasicoherentDerivedRightAdjoint_boundedBelow hZ f hXqc hXqs hYqs hYqc).1 K hK,
        ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K).property⟩⟩))
    (qcohDerived_smallEtaleDerivedSheafHom Y _ _ (Or.inl ⟨hfL, ⟨hK, K.property⟩⟩))

end AlgebraicGeometry.Space

end
