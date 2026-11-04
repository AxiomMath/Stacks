module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperFlatDualizing.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ExceptionalDualizingSheafIdentification

/-!
# The twisted inverse image at the two models

Let `f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated schemes. The derived category
of `𝒪_X`-modules is used at two models, the locally small one and
`CategoryTheory.HasDerivedCategory.standard`, compared by the restriction
`Stacks.Duality.StandardModel.quasiCoherentModelEquiv` of `StacksDraft.DerivedModel.modelEquiv`
to `D_QCoh`. At both models `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` has a right adjoint `a`
([Stacks, Tag 0A9E]). The comparison equivalences intertwine the two derived direct images, so
by uniqueness of adjoints they intertwine the two right adjoints:

`a_std(K)` read at the locally small model is `a_ls(K read at the locally small model)`,

naturally in `K`. In particular the relative dualizing complex `a(𝒪_Y)` of [Stacks, Remark 0B6S]
is the same object at the two models.

## Main definitions

* `Stacks.Duality.StandardModel.quasiCoherentDerivedPushforwardModelIso` — `Rf_*` on `D_QCoh`
  at the two models.
* `Stacks.Duality.StandardModel.twistedInverseImageModelIso` — `a` at the two models.
* `Stacks.Duality.StandardModel.structureSheafModelIso` — `𝒪_Y[0]` at the two models.
* `Stacks.Duality.StandardModel.relativeDualizingComplexModelIso` — `a(𝒪_Y)` at the two models.

## References

* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Remark 0B6S](https://stacks.math.columbia.edu/tag/0B6S)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty

universe u

namespace CategoryTheory.Adjunction

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  {F : A ⥤ B} {G : B ⥤ A} {F' : A' ⥤ B'} {G' : B' ⥤ A'}

/-- **Right adjoints of conjugate left adjoints are conjugate.** If equivalences `EA`, `EB`
intertwine the left adjoints `F ⊣ G` and `F' ⊣ G'`, then they intertwine the right adjoints. -/
def rightAdjointConjugateIso (adj : F ⊣ G) (adj' : F' ⊣ G') (EA : A ≌ A') (EB : B ≌ B')
    (e : F ⋙ EB.functor ≅ EA.functor ⋙ F') : G ⋙ EA.functor ≅ EB.functor ⋙ G' :=
  let eL : EA.inverse ⋙ F ⋙ EB.functor ≅ F' :=
    Functor.isoWhiskerLeft EA.inverse e ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight EA.counitIso F' ≪≫ F'.leftUnitor
  let adj'' : F' ⊣ (EB.inverse ⋙ G) ⋙ EA.functor :=
    (EA.symm.toAdjunction.comp (adj.comp EB.toAdjunction)).ofNatIsoLeft eL
  (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight EB.unitIso _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft EB.functor
      ((Functor.associator _ _ _).symm ≪≫ adj''.rightAdjointUniq adj')

end CategoryTheory.Adjunction

namespace Stacks.Duality.StandardModel

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- **`Rf_*` on `D_QCoh` at the two models.** The derived direct image at the standard model,
followed by the comparison of `D_QCoh(𝒪_Y)`, is the derived direct image at the locally small
model preceded by the comparison of `D_QCoh(𝒪_X)`: both are total right derived functors of
degreewise direct image (`Stacks.Duality.StandardModel.derivedPushforwardModelIso`). -/
def quasiCoherentDerivedPushforwardModelIso :
    @quasiCoherentDerivedPushforward X Y f (HasDerivedCategory.standard X.Modules)
        (HasDerivedCategory.standard Y.Modules) (isQuasicoherent_homology_derivedPushforward f) ⋙
      (quasiCoherentModelEquiv Y).functor ≅
    (quasiCoherentModelEquiv X).functor ⋙
      quasiCoherentDerivedPushforward f (isQuasicoherent_homology_derivedPushforward_of_qcqs f) :=
  ((fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (ι _) (derivedPushforwardModelIso f))

/-- **The twisted inverse image at the two models.** The right adjoint `a` of `Rf_*` on `D_QCoh`
at the standard model, followed by the comparison of `D_QCoh(𝒪_X)`, is the right adjoint at the
locally small model preceded by the comparison of `D_QCoh(𝒪_Y)`, by uniqueness of adjoints. -/
def twistedInverseImageModelIso :
    @twistedInverseImage X Y f (HasDerivedCategory.standard X.Modules)
        (HasDerivedCategory.standard Y.Modules) (isQuasicoherent_homology_derivedPushforward f)
        (isLeftAdjoint_quasiCoherentDerivedPushforward f) ⋙
      (quasiCoherentModelEquiv X).functor ≅
    (quasiCoherentModelEquiv Y).functor ⋙
      twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f) :=
  Adjunction.rightAdjointConjugateIso
    (@twistedInverseImageAdjunction X Y f (HasDerivedCategory.standard X.Modules)
      (HasDerivedCategory.standard Y.Modules) (isQuasicoherent_homology_derivedPushforward f)
      (isLeftAdjoint_quasiCoherentDerivedPushforward f))
    (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
    (quasiCoherentModelEquiv X) (quasiCoherentModelEquiv Y)
    (quasiCoherentDerivedPushforwardModelIso f)

variable (Y) in
/-- **`𝒪_Y[0]` at the two models.** The comparison of `D_QCoh(𝒪_Y)` carries the structure sheaf
in degree zero to the structure sheaf in degree zero. -/
def structureSheafModelIso :
    (quasiCoherentModelEquiv Y).functor.obj (structureSheaf Y) ≅
      DerivedPushforward.derivedStructureSheaf Y :=
  (fullyFaithfulι _).preimageIso
    ((StacksDraft.DerivedModel.modelSingleFunctorIso (HasDerivedCategory.standard Y.Modules)
      (Scheme.Modules.hasDerivedCategory Y) 0).app (SheafOfModules.unit Y.ringCatSheaf))

/-- **The relative dualizing complex `a(𝒪_Y)` at the two models**
([Stacks, Remark 0B6S]): the comparison of `D_QCoh(𝒪_X)` carries `a(𝒪_Y)` at the standard model
to `a(𝒪_Y)` at the locally small model. -/
def relativeDualizingComplexModelIso :
    (quasiCoherentModelEquiv X).functor.obj (relativeDualizingComplex f) ≅
      (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
        (DerivedPushforward.derivedStructureSheaf Y) :=
  (twistedInverseImageModelIso f).app (structureSheaf Y) ≪≫
    (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).mapIso
      (structureSheafModelIso Y)

end Stacks.Duality.StandardModel

end
