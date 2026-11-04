module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.FlatPullback
public import StacksFrontier.Homology.Injectives.DerivedCategory.ArbitraryModel

/-!
# Flat pushforward and the coherator

Let `f : X ⟶ Y` be a quasi-compact, quasi-separated and flat morphism of schemes.  Pushforward
preserves quasi-coherence, so it restricts to `f_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`, whose total right
derived functor is written `Φ`; and the inclusion of the quasi-coherent modules has a right
adjoint, the coherator `Q_X`, whose total right derived functor is written `RQ_X`.  [Stacks, Tag
08D8] identifies the two composites: `RQ_Y ∘ Rf_* = Φ ∘ RQ_X`.

## Main results

* `AlgebraicGeometry.flatPushforwardCoheratorIso`: the natural isomorphism
  `Rf_* ⋙ RQ_Y ≅ RQ_X ⋙ Φ`.

## Implementation notes

The derived categories are instance arguments and the three total right derived functors are
*hypotheses*: each is an arbitrary functor equipped with its derivation unit relative to an
arbitrary chosen localization of the cochain complexes of quasi-coherent modules.  So the
statement says nothing about any particular model of `D(QCoh(𝒪_X))` nor about any particular
choice of K-injective resolutions, and the source's equality of functors becomes a natural
isomorphism.

## References

* [Stacks Project, Tag 08D8](https://stacks.math.columbia.edu/tag/08D8)
* [Stacks Project, Tag 077P](https://stacks.math.columbia.edu/tag/077P)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe w w' u

/-! ### The inclusion of the quasi-coherent modules, in the `Scheme.Modules` spelling -/

/-- The inclusion `QCoh(𝒪_X) ⥤ Mod(𝒪_X)` of the quasi-coherent modules, with codomain spelled
`AlgebraicGeometry.Scheme.Modules X`. -/
public noncomputable def quasicoherentModulesι (X : Scheme.{u}) :
    Scheme.QuasicoherentModules X ⥤ X.Modules :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι

/-- `AlgebraicGeometry.quasicoherentModulesι` is additive. -/
public instance quasicoherentModulesι_additive (X : Scheme.{u}) :
    (quasicoherentModulesι X).Additive :=
  inferInstanceAs ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.Additive)

/-- `AlgebraicGeometry.quasicoherentModulesι` is left exact, the quasi-coherent modules being a
weak Serre subcategory. -/
public instance quasicoherentModulesι_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (quasicoherentModulesι X) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι)

/-- `AlgebraicGeometry.quasicoherentModulesι` is right exact, the quasi-coherent modules being a
weak Serre subcategory. -/
public instance quasicoherentModulesι_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (quasicoherentModulesι X) :=
  inferInstanceAs (PreservesFiniteColimits (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι)

/-- **The coherator adjunction.**  The inclusion of the quasi-coherent modules is left adjoint to
the coherator ([Stacks, Tag 077P]). -/
public noncomputable def coheratorAdjunction (X : Scheme.{u}) :
    quasicoherentModulesι X ⊣ coherator X :=
  have := quasicoherentInclusion_isLeftAdjoint X
  Adjunction.ofIsLeftAdjoint (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι

/-- **Pullback commutes with the inclusion of the quasi-coherent modules.**  Restricting pullback
to quasi-coherent modules and then forgetting quasi-coherence is pullback of all modules. -/
public noncomputable def quasicoherentPullbackCompιIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    quasicoherentPullback f ⋙ quasicoherentModulesι X ≅
      quasicoherentModulesι Y ⋙ Scheme.Modules.pullback f :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).liftCompιIso _ _

/-! ### The comparison of Stacks 08D8 -/

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [Flat f]
  [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]
  [HasDerivedCategory.{w'} (Scheme.QuasicoherentModules X)]
  [HasDerivedCategory.{w'} (Scheme.QuasicoherentModules Y)]
  (QX : CochainComplex (Scheme.QuasicoherentModules X) ℤ ⥤
    DerivedCategory (Scheme.QuasicoherentModules X))
  [QX.IsLocalization
    (HomologicalComplex.quasiIso (Scheme.QuasicoherentModules X) (ComplexShape.up ℤ))]
  (QY : CochainComplex (Scheme.QuasicoherentModules Y) ℤ ⥤
    DerivedCategory (Scheme.QuasicoherentModules Y))
  [QY.IsLocalization
    (HomologicalComplex.quasiIso (Scheme.QuasicoherentModules Y) (ComplexShape.up ℤ))]
  (Rf : DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules)
  (RfUnit : (Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q (C := Y.Modules) ⟶ DerivedCategory.Q (C := X.Modules) ⋙ Rf)
  [Rf.IsRightDerivedFunctor RfUnit
    (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))]
  (RQX : DerivedCategory X.Modules ⥤ DerivedCategory (Scheme.QuasicoherentModules X))
  (RQXUnit : (coherator X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QX ⟶
      DerivedCategory.Q (C := X.Modules) ⋙ RQX)
  [RQX.IsRightDerivedFunctor RQXUnit
    (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))]
  (RQY : DerivedCategory Y.Modules ⥤ DerivedCategory (Scheme.QuasicoherentModules Y))
  (RQYUnit : (coherator Y).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QY ⟶
      DerivedCategory.Q (C := Y.Modules) ⋙ RQY)
  [RQY.IsRightDerivedFunctor RQYUnit
    (HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ))]
  (Φ : DerivedCategory (Scheme.QuasicoherentModules X) ⥤
    DerivedCategory (Scheme.QuasicoherentModules Y))
  (ΦUnit : (quasicoherentPushforward f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QY ⟶
      QX ⋙ Φ)
  [Φ.IsRightDerivedFunctor ΦUnit
    (HomologicalComplex.quasiIso (Scheme.QuasicoherentModules X) (ComplexShape.up ℤ))]

/-- Let `f : X ⟶ Y` be a quasi-compact, quasi-separated and flat morphism of schemes. Let `Rf_*`
be a total right derived functor of pushforward of all modules, let `RQ_X`, `RQ_Y` be total right
derived functors of the coherators, and let `Φ` be a total right derived functor of pushforward
restricted to quasi-coherent modules. Then `Rf_* ⋙ RQ_Y ≅ RQ_X ⋙ Φ`. -/
@[stacks 08D8]
public noncomputable def flatPushforwardCoheratorIso : Rf ⋙ RQY ≅ RQX ⋙ Φ := by
  have : PreservesFiniteLimits (Scheme.Modules.pullback f) :=
    preservesFiniteLimits_modulesPullback_of_flat f
  have : PreservesFiniteColimits (Scheme.Modules.pullback f) :=
    preservesFiniteColimits_modulesPullback f
  have : PreservesFiniteLimits (quasicoherentPullback f) :=
    quasicoherentPullback_preservesFiniteLimits f
  have : PreservesFiniteColimits (quasicoherentPullback f) :=
    quasicoherentPullback_preservesFiniteColimits f
  let adjRQX := Stacks.DerivedModel.adjunctionOfExact (quasicoherentModulesι X)
    (DerivedCategory.Q (C := X.Modules)) QX (coheratorAdjunction X) RQX RQXUnit
  let adjRQY := Stacks.DerivedModel.adjunctionOfExact (quasicoherentModulesι Y)
    (DerivedCategory.Q (C := Y.Modules)) QY (coheratorAdjunction Y) RQY RQYUnit
  let adjRf := Stacks.DerivedModel.adjunctionOfExact (Scheme.Modules.pullback f)
    (DerivedCategory.Q (C := X.Modules)) (DerivedCategory.Q (C := Y.Modules))
    (Scheme.Modules.pullbackPushforwardAdjunction f) Rf RfUnit
  let adjPhi := Stacks.DerivedModel.adjunctionOfExact (quasicoherentPullback f) QX QY
    (quasicoherentPullbackPushforwardAdjunction f) Φ ΦUnit
  let c := ComplexShape.up ℤ
  let QtY := Stacks.DerivedModel.homotopyLocalization QY
  let QtX := Stacks.DerivedModel.homotopyLocalization QX
  let QtXall := Stacks.DerivedModel.homotopyLocalization (DerivedCategory.Q (C := X.Modules))
  let LincY := Stacks.DerivedModel.derivedFunctorOfExact (quasicoherentModulesι Y)
    (DerivedCategory.Q (C := Y.Modules)) QY
  let Lpb := Stacks.DerivedModel.derivedFunctorOfExact (Scheme.Modules.pullback f)
    (DerivedCategory.Q (C := X.Modules)) (DerivedCategory.Q (C := Y.Modules))
  let LqcPB := Stacks.DerivedModel.derivedFunctorOfExact (quasicoherentPullback f) QX QY
  let LincX := Stacks.DerivedModel.derivedFunctorOfExact (quasicoherentModulesι X)
    (DerivedCategory.Q (C := X.Modules)) QX
  let eIncY := Stacks.DerivedModel.derivedFunctorOfExactFac (quasicoherentModulesι Y)
    (DerivedCategory.Q (C := Y.Modules)) QY
  let ePB := Stacks.DerivedModel.derivedFunctorOfExactFac (Scheme.Modules.pullback f)
    (DerivedCategory.Q (C := X.Modules)) (DerivedCategory.Q (C := Y.Modules))
  let eQcPB := Stacks.DerivedModel.derivedFunctorOfExactFac (quasicoherentPullback f) QX QY
  let eIncX := Stacks.DerivedModel.derivedFunctorOfExactFac (quasicoherentModulesι X)
    (DerivedCategory.Q (C := X.Modules)) QX
  let L1 := LincY ⋙ Lpb
  let L2 := LqcPB ⋙ LincX
  let H1 := ((quasicoherentModulesι Y).mapHomotopyCategory c ⋙
    (Scheme.Modules.pullback f).mapHomotopyCategory c) ⋙ QtXall
  let H2 := ((quasicoherentPullback f).mapHomotopyCategory c ⋙
    (quasicoherentModulesι X).mapHomotopyCategory c) ⋙ QtXall
  let h1 : QtY ⋙ L1 ≅ H1 :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eIncY Lpb ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ ePB ≪≫
      (Functor.associator _ _ _).symm
  let h2 : QtY ⋙ L2 ≅ H2 :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eQcPB LincX ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ eIncX ≪≫
      (Functor.associator _ _ _).symm
  let eBase : H2 ≅ H1 :=
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso (quasicoherentPullbackCompιIso f) c) QtXall ≪≫
    Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (quasicoherentModulesι Y ⋙ Scheme.Modules.pullback f)) c).symm QtXall
  let W := HomotopyCategory.quasiIso (Scheme.QuasicoherentModules Y) c
  let : Localization.Lifting QtY W H1 L1 := ⟨h1⟩
  let : Localization.Lifting QtY W H2 L2 := ⟨h2⟩
  let eLeft : L2 ≅ L1 := Localization.liftNatIso QtY W H2 H1 L2 L1 eBase
  exact (adjRQY.comp adjRf).rightAdjointUniq ((adjPhi.comp adjRQX).ofNatIsoLeft eLeft)

end

end AlgebraicGeometry

end
