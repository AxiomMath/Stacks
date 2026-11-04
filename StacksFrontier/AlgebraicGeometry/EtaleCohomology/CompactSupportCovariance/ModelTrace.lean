module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceDerivedConstruction
public import StacksFrontier.AlgebraicGeometry.Etale.DerivedLowerShriekCompactification
public import StacksFrontier.AlgebraicGeometry.Etale.ModuleSheafDirectImageAcyclicComplexes
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.ExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Etale.EtaleUpperShriekRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLiftAdjunction
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence

/-!
# The weighted trace of a finite compactification, on Mathlib's small étale sites

Let `f : X ⟶ Y` be a morphism of schemes with a compactification `j : X ⟶ X̄`, `f = j ≫ f̄`, whose
structure morphism `f̄ : X̄ ⟶ Y` is finite, let `w` be a weighting of `f` and let `Λ` be a ring.
The trace map `Tr_{f, w} : f_! f^{-1} ⟶ id` of [Stacks, Tag 0GKG] is constructed on the small
étale sites of Tag 021B inside a big étale site
(`AlgebraicGeometry.SmallEtale.weightedTraceModTrans`), whereas the derived lower shriek
`Rf_! = Rf̄_* ∘ j_!` and the cohomology with compact support of [Stacks, Tag 0GJZ] live on
Mathlib's small étale sites. Here the trace is carried across: on Mathlib's sites,
`f_! = f̄_* ∘ j_!` ([Stacks, Tag 0F52]) and the trace is a natural transformation

`Tr_{f, w} : f^{-1} ⋙ j_! ⋙ f̄_* ⟶ 𝟭`

of functors on sheaves of `Λ`-modules on `Y_étale`.

The transport is along the equivalences `AlgebraicGeometry.SmallEtale.moduleSheafEquiv` of the
sheaf categories of the two presentations of the small étale site, which commute with inverse
image (`AlgebraicGeometry.SmallEtale.moduleSheafEquivInverseImageIso`), with extension by zero
(`AlgebraicGeometry.SmallEtale.moduleSheafEquivExtensionByZeroIso`) and with direct image
(`AlgebraicGeometry.SmallEtale.etalePushforwardModSheafEquivIso`). On the side of the big étale
site, `f_! = f̄_* ∘ j_!` is `AlgebraicGeometry.SmallEtale.fShriekModIsoCompactificationHom`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.moduleSheafEquivInverseImageIso`: inverse image commutes with the
  comparison of the two presentations, for sheaves of `Λ`-modules.
* `AlgebraicGeometry.SmallEtale.moduleSheafEquivExtensionByZeroIso`: so does extension by zero
  along an open immersion.
* `Stacks.EtaleCohomology.etaleModuleCompactificationTrace`: the trace
  `f^{-1} ⋙ j_! ⋙ f̄_* ⟶ 𝟭` on Mathlib's small étale site of `Y`.

## Implementation notes

The coefficient ring lives in the universe of the schemes, `Λ : Type u`, which is where the
identification of Stacks 0F52 for `Λ`-modules
(`AlgebraicGeometry.SmallEtale.fShriekModIsoCompactificationHom`) is available.

## References

* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
* [Stacks Project, Tag 0F52](https://stacks.math.columbia.edu/tag/0F52)
* [Stacks Project, Tag 0GKS](https://stacks.math.columbia.edu/tag/0GKS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (Λ : Type u) [Ring Λ]

/-- **Inverse image commutes with the comparison of the two small étale sites**, for sheaves of
`Λ`-modules: transporting to Mathlib's site and taking `g⁻¹` there is taking the `Λ`-linear
`g⁻¹` of the big étale site (`AlgebraicGeometry.SmallEtale.pullbackMod`) and transporting. Both
composites are left adjoint to the same functor. -/
def moduleSheafEquivInverseImageIso {S T : B.Scheme} (g : T ⟶ S) :
    (moduleSheafEquiv B Λ S).functor ⋙
        Stacks.EtaleCohomology.etaleModuleInverseImage.{u, u} Λ (B.inclusion.map g) ≅
      pullbackMod.{u, u, u} B Λ g ⋙ (moduleSheafEquiv B Λ T).functor :=
  letI : (abPullback.{u, u} B g).Additive := additive_abPullback.{u, u} B g
  @sheafEquivPullbackBaseChangeIso.{u + 1, u + 2, u} B S T g (ModuleCat.{u + 1} Λ) _
    (ModuleCat.hasLimitsOfSize.{u, u, u + 1, u}) _ _
    (Stacks.EtaleCohomology.etaleModuleInverseImageAdj.{u, u} Λ (B.inclusion.map g))
    (Stacks.ModuleCatLift.moduleLiftAdjunction.{u + 1, u, _, _, _, _} Λ _ _ _ _
      (abPullbackAdjunction.{u, u} B g))

/-- **Extension by zero along an open immersion commutes with the comparison of the two small
étale sites**, for sheaves of `Λ`-modules: on the big étale site extension by zero is the
`Λ`-linear direct image with compact support `fShriekMod` of the open immersion
([Stacks, Tag 0F6Q]), left adjoint to restriction. -/
def moduleSheafEquivExtensionByZeroIso {X Xb : B.Scheme} (j : X ⟶ Xb)
    [IsOpenImmersion (B.inclusion.map j)] :
    (moduleSheafEquiv B Λ X).functor ⋙
        Stacks.EtaleCohomology.etaleModuleExtensionByZero.{u, u} Λ (B.inclusion.map j) ≅
      fShriekMod.{u, u, u} B Λ j ⋙ (moduleSheafEquiv B Λ Xb).functor :=
  @sheafEquivExtensionByZeroIso.{u, u + 1, u + 2} B Xb.obj Xb.property
    (SmallEtale.ofEtaleHom B j) (ModuleCat.{u + 1} Λ) _
    (ModuleCat.hasLimitsOfSize.{u, u, u + 1, u}) _ _
    (Stacks.EtaleCohomology.etaleModuleExtensionByZeroAdj.{u, u} Λ (B.inclusion.map j))
    (Stacks.ModuleCatLift.moduleLiftAdjunction.{u + 1, u, _, _, _, _} Λ _ _ _ _
      (fShriekAdjunctionRestriction B Xb.obj Xb.property (SmallEtale.ofEtaleHom B j)))

section Trace

variable {X Xb Y : B.Scheme} (j : X ⟶ Xb) (fbar : Xb ⟶ Y) [IsOpenImmersion (B.inclusion.map j)]
  [IsFinite (B.inclusion.map fbar)] {w : X.obj → ℤ}
  (hw : IsWeighting (B.inclusion.map (j ≫ fbar)) w)

include hw in
/-- The trace of `(j ≫ f̄, w)` read on Mathlib's small étale site, before the comparison of the
two presentations is undone: transporting to Mathlib's site and applying
`(j ≫ f̄)^{-1} ⋙ j_! ⋙ f̄_*` there is transporting `f_! f^{-1}` of the big étale site, and the
trace of Stacks 0GKG maps that to the transport. -/
def etaleModuleCompactificationTraceAux :
    (moduleSheafEquiv B Λ Y).functor ⋙
        (Stacks.EtaleCohomology.etaleModuleInverseImage.{u, u} Λ (B.inclusion.map (j ≫ fbar)) ⋙
          Stacks.EtaleCohomology.etaleModuleExtensionByZero.{u, u} Λ (B.inclusion.map j) ⋙
            Stacks.EtaleCohomology.etaleModuleDirectImage.{u, u} Λ (B.inclusion.map fbar)) ⟶
      (moduleSheafEquiv B Λ Y).functor :=
  haveI : LocallyOfFiniteType (B.inclusion.map (j ≫ fbar)) :=
    inferInstanceAs (LocallyOfFiniteType (B.inclusion.map j ≫ B.inclusion.map fbar))
  haveI : LocallyQuasiFinite (B.inclusion.map (j ≫ fbar)) :=
    inferInstanceAs (LocallyQuasiFinite (B.inclusion.map j ≫ B.inclusion.map fbar))
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (moduleSheafEquivInverseImageIso B Λ (j ≫ fbar)).hom _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (pullbackMod.{u, u, u} B Λ (j ≫ fbar))
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (moduleSheafEquivExtensionByZeroIso B Λ j).hom _ ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (fShriekMod.{u, u, u} B Λ j)
          (etalePushforwardModSheafEquivIso B Λ fbar).inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (fShriekModIsoCompactificationHom B Λ j fbar).inv _) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (weightedTraceModTrans.{u, u, u} B Λ (j ≫ fbar) hw) _ ≫
    (Functor.leftUnitor _).hom

end Trace

end AlgebraicGeometry.SmallEtale

open AlgebraicGeometry AlgebraicGeometry.SmallEtale

namespace Stacks.EtaleCohomology

variable (Λ : Type u) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
  (jf : CompactificationOf (Over.mk f))

/-- A big étale site containing `X`, the space `X̄` of a compactification of `f : X ⟶ Y`, and
`Y`. -/
def compactificationBigEtaleSite : BigEtaleSite.{u} :=
  BigEtaleSite.ofSet {X, jf.space, Y}

/-- The site `compactificationBigEtaleSite f jf` contains `X`. -/
lemma contains_compactificationBigEtaleSite_source :
    (compactificationBigEtaleSite f jf).Contains X :=
  BigEtaleSite.contains_ofSet _ (by simp)

/-- The site `compactificationBigEtaleSite f jf` contains the space `X̄` of the
compactification `jf`. -/
lemma contains_compactificationBigEtaleSite_space :
    (compactificationBigEtaleSite f jf).Contains jf.space :=
  BigEtaleSite.contains_ofSet _ (by simp)

/-- The site `compactificationBigEtaleSite f jf` contains `Y`. -/
lemma contains_compactificationBigEtaleSite_target :
    (compactificationBigEtaleSite f jf).Contains Y :=
  BigEtaleSite.contains_ofSet _ (by simp)

variable [IsFinite jf.toBase] {w : X → ℤ} (hw : IsWeighting f w)

include hw in
/-- **The trace map `Tr_{f, w} : f_! f^{-1} ⟶ id` of [Stacks, Tag 0GKG] on Mathlib's small étale
site**, for a morphism `f : X ⟶ Y` with a compactification `j : X ⟶ X̄` finite over `Y`, so that
`f_! = f̄_* ∘ j_!` ([Stacks, Tag 0F52]), and a weighting `w` of `f`. It is the trace
`AlgebraicGeometry.SmallEtale.weightedTraceModTrans` of the big étale site
`Stacks.EtaleCohomology.compactificationBigEtaleSite`, carried to Mathlib's small étale sites
along the comparison `AlgebraicGeometry.SmallEtale.moduleSheafEquiv` of the two presentations. -/
def etaleModuleCompactificationTrace :
    etaleModuleInverseImage.{u, u} Λ f ⋙ etaleModuleExtensionByZero.{u, u} Λ jf.immersion ⋙
        etaleModuleDirectImage.{u, u} Λ jf.toBase ⟶ 𝟭 (EtaleModules.{u, u} Λ Y) :=
  let B := compactificationBigEtaleSite f jf
  let Xb := B.objOfContains X (contains_compactificationBigEtaleSite_source f jf)
  let Xbb := B.objOfContains jf.space (contains_compactificationBigEtaleSite_space f jf)
  let Yb := B.objOfContains Y (contains_compactificationBigEtaleSite_target f jf)
  let jb : Xb ⟶ Xbb := ObjectProperty.homMk jf.immersion
  let fb : Xbb ⟶ Yb := ObjectProperty.homMk jf.toBase
  haveI : IsOpenImmersion (B.inclusion.map jb) := inferInstanceAs (IsOpenImmersion jf.immersion)
  haveI : IsFinite (B.inclusion.map fb) := inferInstanceAs (IsFinite jf.toBase)
  have hfac := CompactificationOf.immersion_toBase jf
  have hw' : IsWeighting (B.inclusion.map (jb ≫ fb)) w :=
    (by rw [hfac]; exact hw : IsWeighting (jf.immersion ≫ jf.toBase) w)
  let E := moduleSheafEquiv B Λ Yb
  Functor.whiskerRight (eqToHom (congrArg (etaleModuleInverseImage.{u, u} Λ) hfac.symm)) _ ≫
    (Functor.leftUnitor _).inv ≫ Functor.whiskerRight E.counitIso.inv _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft E.inverse (etaleModuleCompactificationTraceAux B Λ jb fb hw') ≫
    E.counitIso.hom

end Stacks.EtaleCohomology

end
