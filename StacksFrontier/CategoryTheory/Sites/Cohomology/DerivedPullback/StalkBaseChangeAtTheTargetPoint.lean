module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafStalkBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorAlongASiteMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.StalkOfInverseImageAtTheTargetPoint
public import StacksFrontier.Homology.ExtendScalars.AlongARingIsomorphism
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The stalk of a pullback at the point of the target site, and the K-flatness of a pullback

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi whose underlying functor
`u : C' ⥤ C` of the sites is a morphism of sites, let `Φ` be a point of `C`, and let `Ψ` be the
point of `C'` attached to `Φ` by part (2) of Stacks 00YA, so that the stalk functor of `Ψ` is
the inverse image along `f` followed by the stalk functor of `Φ`.

This file proves the comparison of Stacks 05V5 at that point,

`(f^*G)_Φ ≅ G_Ψ ⊗_{O'_Ψ} O_Φ`,

naturally in the sheaf of `O'`-modules `G`, and with it the K-flatness assertion of Stacks
0DEP: if `C` has a conservative family of points, then the degreewise pullback along `f` of a
K-flat complex of `O'`-modules is a K-flat complex of `O`-modules.

The pullback of Stacks 03D6 is the inverse image of Stacks 03D2 followed by extension of
scalars along the inverse-image form `f⁻¹O' ⟶ O` of the structure map, so its stalk at `Φ` is
computed in two steps.  The inverse image contributes Stacks 05V1 at `Ψ`: the identification
`G_Ψ ≅ (f⁻¹G)_Φ`, semilinear over an isomorphism `O'_Ψ ≅ (f⁻¹O')_Φ` of stalk rings.  The
extension of scalars of Stacks 03CZ contributes the stalkwise formula for a sectionwise tensor
product — the stalk does not see the sheafification that extension of scalars performs — which
reads `(O ⊗_{f⁻¹O'} F)_Φ ≅ O_Φ ⊗_{(f⁻¹O')_Φ} F_Φ`.

What remains is formal.  Restriction of scalars along the isomorphism `O'_Ψ ≅ (f⁻¹O')_Φ`
followed by extension of scalars along `(f⁻¹O')_Φ ⟶ O_Φ` is a single extension of scalars
along the composite `O'_Ψ ⟶ O_Φ`, because restricting and then extending scalars along a ring
isomorphism is the identity functor.  That reconciliation is
`ModuleCat.restrictExtendScalarsCompIso`.

The map of stalk rings so produced is `stalkRingMap`, and no compatibility of it with `f` is
needed downstream: Stacks 06Y1 preserves K-flatness along an arbitrary ring homomorphism.

## Main definitions

* `Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites.targetCommRingStalkEquiv`: the
  isomorphism `O'_Ψ ≅ (f⁻¹O')_Φ` of stalk rings, read between `CommRingCat`-valued stalks.
* `Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites.stalkRingMap`: the map
  `O'_Ψ ⟶ O_Φ` of stalk rings along which the comparison extends scalars.

## Main results

* `Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites.stalkFunctorIso`: **Stacks 05V5
  at the point `Ψ`**, as a natural isomorphism of stalk functors.
* `Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites.stalkComplexIso`: the same
  comparison for a cochain complex of sheaves of modules.
* `Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites.stalkBaseChange`: the comparison
  `StalkBaseChange` at the named point of the target site holds.
* `Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites.kFlat_pullbackComplex`:
  **Stacks 0DEP**, the K-flatness of the degreewise pullback of a K-flat complex along `f`, for
  a source site with a conservative family of points.

## Implementation notes

**Three spellings of the stalk functor on sheaves of modules.**  Over a sheaf of rings `R` the
stalk at `Φ` is `Stacks.sheafModuleFiber Φ R`, valued in modules over the `RingCat`-valued
stalk of `R`.  For the structure sheaf of a ringed topos one wants modules over the
`CommRingCat`-valued stalk instead, and the passage is restriction of scalars along
`Stacks.toRingFiber`; that composite is spelled `Stacks.sheafModuleFiberOfCommRing Φ O`, the
functor `Stacks.Sheaves.KFlatStalkCriterion.stalkComplex` is built from, and
`Stacks.SitePointBaseChange.sheafStalk Φ A h`, the functor the base-change interchange is
stated for.  The latter two agree on the nose for the structure sheaf of a ringed topos: both
sides are built from the same presheaf of commutative rings, and the only remaining difference
is the sheaf condition, which is a proposition.  All three identifications hold by `rfl` and
are used silently in the chain below.

**The chain is written out link by link.**  Each of `stalkIsoStepOne` to `stalkIsoStepFive`
states its own source and target, and `stalkFunctorIso` is their composite.  Consecutive links
differ only by associativity of composition of functors and by the unfolding of one definition,
so writing the statements out keeps each definitional unfolding small and local rather than
leaving a single long composite for the elaborator to reconcile in one step.

**Universes.**  Both ringed topoi are taken at `AlgebraicGeometry.RingedTopos.{u, u, u}`, as
they are for `kFlat_pullbackComplex_of_morphismOfSites`; the base-change interchange at a point
of a site and `ModuleCat.extendScalarsComp` are likewise stated with all rings and all modules
in one universe.

## References

* [Stacks Project, Tag 0DEP](https://stacks.math.columbia.edu/tag/0DEP)
* [Stacks Project, Tag 0DEN](https://stacks.math.columbia.edu/tag/0DEN)
* [Stacks Project, Tag 00YA](https://stacks.math.columbia.edu/tag/00YA)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 05V1](https://stacks.math.columbia.edu/tag/05V1)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.DerivedPullback
open Stacks.Sheaves.DerivedPullback.KFlatPullbackEnoughPoints
open Stacks.Sheaves.KFlatStalkCriterion (structureStalk stalkComplex)

noncomputable section

universe u

namespace Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : AlgebraicGeometry.RingedToposSiteHom X Y) (hu : f.u.IsMorphismOfSites.{u} Y.J X.J)
  (Φ : X.J.Point.{u})

/-- The inverse image `f⁻¹O'` of the structure sheaf of the target, as a presheaf of
commutative rings on the source site. -/
abbrev inverseImageStructure : X.Cᵒᵖ ⥤ CommRingCat.{u} :=
  inverseImageStructureCommRing (modulesHomOfSiteHom f hu)

/-- The inverse image `f⁻¹O'` of the structure sheaf of the target, as a sheaf of rings on the
source site. -/
abbrev inverseImageStructureRing : Sheaf X.J RingCat.{u} :=
  inverseImageRingSheaf (f.toToposHom hu) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)

/-- The inverse image of sheaves of modules along `f`, Stacks 03D2. -/
abbrev inverseImageFunctor :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{u} (inverseImageStructureRing f hu) :=
  inverseImageModules (f.toToposHom hu) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)

/-- The stalk at `Φ` of a sheaf of `f⁻¹O'`-modules, over the `RingCat`-valued stalk of
`f⁻¹O'`. -/
abbrev inverseImageStalkFunctor := Stacks.sheafModuleFiber Φ (inverseImageStructureRing f hu)

/-- The comparison of the `CommRingCat`-valued stalk of `f⁻¹O'` at `Φ` with its
`RingCat`-valued stalk. -/
abbrev toInverseImageStalkRing := Stacks.toRingFiber Φ (inverseImageStructure f hu)

/-- The comparison of the `CommRingCat`-valued stalk `O'_Ψ` with the `RingCat`-valued stalk of
the sheaf of rings underlying `O'`. -/
abbrev toTargetStalkRing := Stacks.toRingFiber (targetPoint f hu Φ) Y.O.obj

/-- The stalk at `Φ` of the inverse-image form of the structure map of `f`. -/
abbrev fSharpStalk :=
  Stacks.SitePointBaseChange.stalkRingHom (fSharpCommRing (modulesHomOfSiteHom f hu)) Φ

/-- **The isomorphism `O'_Ψ ≅ (f⁻¹O')_Φ` of `CommRingCat`-valued stalk rings.**  It is
`targetStalkRingEquiv`, which compares the `RingCat`-valued stalks, conjugated by the
comparison of the `RingCat`-valued stalk of a presheaf of commutative rings with its
`CommRingCat`-valued one at either end. -/
def targetCommRingStalkEquiv :
    structureStalk Y.O (targetPoint f hu Φ) ≃+* Stacks.ringFiber Φ (inverseImageStructure f hu) :=
  ((Stacks.commRingPresheafFiberIso (targetPoint f hu Φ)
          Y.O.obj).ringCatIsoToRingEquiv.symm.trans (targetStalkRingEquiv f hu Φ)).trans
    (Stacks.commRingPresheafFiberIso Φ (inverseImageStructure f hu)).ringCatIsoToRingEquiv

/-- **The map `O'_Ψ ⟶ O_Φ` of stalk rings.**  It is the isomorphism `O'_Ψ ≅ (f⁻¹O')_Φ` followed
by the stalk at `Φ` of the inverse-image form `f⁻¹O' ⟶ O` of the structure map of `f`. -/
def stalkRingMap : structureStalk Y.O (targetPoint f hu Φ) →+* structureStalk X.O Φ :=
  (fSharpStalk f hu Φ).comp (targetCommRingStalkEquiv f hu Φ).toRingHom

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The isomorphism `O'_Ψ ≅ (f⁻¹O')_Φ` of `CommRingCat`-valued stalks is compatible with the
comparisons to the `RingCat`-valued stalks and with `targetStalkRingEquiv`. -/
lemma toInverseImageStalkRing_comp_targetCommRingStalkEquiv :
    (toInverseImageStalkRing f hu Φ).comp (targetCommRingStalkEquiv f hu Φ).toRingHom =
      (targetStalkRingEquiv f hu Φ).toRingHom.comp (toTargetStalkRing f hu Φ) := by
  refine RingHom.ext fun x => ?_
  exact RingEquiv.symm_apply_apply
    (Stacks.commRingPresheafFiberIso Φ (inverseImageStructure f hu)).ringCatIsoToRingEquiv _

/-- The pullback of sheaves of modules along `f` is the pullback along the four-field morphism
of ringed topoi attached to `f`, read after taking stalks at `Φ`. -/
def stalkIsoStepOne :
    f.pullbackTopos ⋙ Stacks.sheafModuleFiberOfCommRing Φ X.O ≅
      (modulesHomOfSiteHom f hu).pullbackModules ⋙
        Stacks.sheafModuleFiberOfCommRing Φ X.O :=
  Functor.isoWhiskerRight (pullbackModulesSiteIso f hu).symm _

/-- The stalk at `Φ` of the extension of scalars along `f⁻¹O' ⟶ O` is the extension of scalars
along the stalk of that map: Stacks 05V5 for the second half of the pullback. -/
def stalkIsoStepTwo :
    (modulesHomOfSiteHom f hu).pullbackModules ⋙
        Stacks.sheafModuleFiberOfCommRing Φ X.O ≅
      inverseImageFunctor f hu ⋙ inverseImageStalkFunctor f hu Φ ⋙
        ModuleCat.restrictScalars (toInverseImageStalkRing f hu Φ) ⋙
          ModuleCat.extendScalars (fSharpStalk f hu Φ) :=
  Functor.isoWhiskerLeft (inverseImageFunctor f hu)
    (Stacks.SitePointBaseChange.extendScalarsSheafStalkNatIso Φ
      (fSharpCommRing (modulesHomOfSiteHom f hu))
      (inverseImageStructureRing f hu).property
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)

/-- Precomposing the restriction and the extension of scalars with the isomorphism
`O'_Ψ ≅ (f⁻¹O')_Φ` of stalk rings leaves their composite unchanged. -/
def stalkIsoStepThree :
    inverseImageFunctor f hu ⋙ inverseImageStalkFunctor f hu Φ ⋙
        ModuleCat.restrictScalars (toInverseImageStalkRing f hu Φ) ⋙
          ModuleCat.extendScalars (fSharpStalk f hu Φ) ≅
      inverseImageFunctor f hu ⋙ inverseImageStalkFunctor f hu Φ ⋙
        ModuleCat.restrictScalars ((toInverseImageStalkRing f hu Φ).comp
            (targetCommRingStalkEquiv f hu Φ).toRingHom) ⋙
          ModuleCat.extendScalars (stalkRingMap f hu Φ) :=
  Functor.isoWhiskerLeft (inverseImageFunctor f hu ⋙ inverseImageStalkFunctor f hu Φ)
    (ModuleCat.restrictExtendScalarsCompIso (toInverseImageStalkRing f hu Φ)
      (fSharpStalk f hu Φ) (targetCommRingStalkEquiv f hu Φ)).symm

/-- The restriction of scalars along the composite `O'_Ψ ⟶ (f⁻¹O')_Φ` of the two comparisons of
stalk rings is the successive restriction along each of them. -/
def stalkIsoStepFour :
    inverseImageFunctor f hu ⋙ inverseImageStalkFunctor f hu Φ ⋙
        ModuleCat.restrictScalars ((toInverseImageStalkRing f hu Φ).comp
            (targetCommRingStalkEquiv f hu Φ).toRingHom) ⋙
          ModuleCat.extendScalars (stalkRingMap f hu Φ) ≅
      inverseImageFunctor f hu ⋙ inverseImageStalkFunctor f hu Φ ⋙
        (ModuleCat.restrictScalars (targetStalkRingEquiv f hu Φ).toRingHom ⋙
            ModuleCat.restrictScalars (toTargetStalkRing f hu Φ)) ⋙
          ModuleCat.extendScalars (stalkRingMap f hu Φ) :=
  Functor.isoWhiskerLeft (inverseImageFunctor f hu ⋙ inverseImageStalkFunctor f hu Φ)
    (Functor.isoWhiskerRight
      (ModuleCat.restrictScalarsComp' (toTargetStalkRing f hu Φ)
        (targetStalkRingEquiv f hu Φ).toRingHom _
        (toInverseImageStalkRing_comp_targetCommRingStalkEquiv f hu Φ))
      (ModuleCat.extendScalars (stalkRingMap f hu Φ)))

/-- Stacks 05V1 at the point `Ψ`: the stalk functor at `Ψ` is the inverse image followed by the
stalk functor at `Φ` and restriction of scalars. -/
def stalkIsoStepFive :
    inverseImageFunctor f hu ⋙ inverseImageStalkFunctor f hu Φ ⋙
        (ModuleCat.restrictScalars (targetStalkRingEquiv f hu Φ).toRingHom ⋙
            ModuleCat.restrictScalars (toTargetStalkRing f hu Φ)) ⋙
          ModuleCat.extendScalars (stalkRingMap f hu Φ) ≅
      Stacks.sheafModuleFiberOfCommRing (targetPoint f hu Φ) Y.O ⋙
        ModuleCat.extendScalars (stalkRingMap f hu Φ) :=
  (Functor.isoWhiskerRight (targetStalkNatIso f hu Φ)
    (ModuleCat.restrictScalars (toTargetStalkRing f hu Φ) ⋙
      ModuleCat.extendScalars (stalkRingMap f hu Φ))).symm

/-- **Stacks 05V5 at the point `Ψ` of the target site**, as a natural isomorphism of stalk
functors: the stalk at `Φ` of the pullback of a sheaf of `O'`-modules is the extension of
scalars along `O'_Ψ ⟶ O_Φ` of its stalk at `Ψ`.

This is the clause of Stacks 05V5 that
`AlgebraicGeometry.RingedToposHom.pullbackModulesSquareIso` names as missing: there the formula
is proved for a commutative square of morphisms of ringed topoi, with the square over a point
`p` and the point `q = f ∘ p` left unconstructed, and `Ψ = targetPoint f hu Φ` is that point. -/
@[stacks 05V5 "the formula `(f^*F)_p ≅ F_q ⊗_{O'_q} O_p` at a point `p` of the source site,
naturally in the `O'`-module `F`, with `q = f ∘ p` the point of the target site induced by `p`;
for a morphism of ringed topoi whose underlying functor is a morphism of the underlying sites,
at `RingedTopos.{u, u, u}`", ega "0 4.3.1" "more general"]
def stalkFunctorIso :
    f.pullbackTopos ⋙ Stacks.sheafModuleFiberOfCommRing Φ X.O ≅
      Stacks.sheafModuleFiberOfCommRing (targetPoint f hu Φ) Y.O ⋙
        ModuleCat.extendScalars (stalkRingMap f hu Φ) :=
  stalkIsoStepOne f hu Φ ≪≫ stalkIsoStepTwo f hu Φ ≪≫ stalkIsoStepThree f hu Φ ≪≫
    stalkIsoStepFour f hu Φ ≪≫ stalkIsoStepFive f hu Φ

/-- **Stacks 05V5 at the level of complexes, at the point `Ψ`.**  The stalk complex at `Φ` of
the degreewise pullback of a complex of `O'`-modules is the extension of scalars along
`O'_Ψ ⟶ O_Φ` of its stalk complex at `Ψ`.

The two `PreservesZeroMorphisms` instances are supplied by hand, as they are in
`Stacks.Sheaves.DerivedPullback.StalkBaseChangeOfToposHom.stalkComplexIso`.  The middle
category of the source functor is `Mod(O)` spelled `Stacks.SheafOfModules.Tensor.ringSheaf
X.O`, the way `pullbackTopos` names it, while `sheafModuleFiberOfCommRing` names it
`Stacks.commRingSheafToRingSheaf X.O`; the two agree definitionally but not at the
transparency instance search runs at, so the additivity of the stalk functor is not found
through the composition instance.  Both factors' instances already exist, so naming them is
all that is needed. -/
def stalkComplexIso
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    stalkComplex X.O Φ ((KFlatPullback.pullbackComplex f).obj K) ≅
      (CochainComplex.extendScalars (stalkRingMap f hu Φ)).obj
        (stalkComplex Y.O (targetPoint f hu Φ) K) :=
  (@NatIso.mapHomologicalComplex _ _ _ _ _ _ _ _ _
    (@Functor.preservesZeroMorphisms_comp _ _ _ _ _ _ _ _ _ _ _
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
        (AlgebraicGeometry.RingedToposSiteHom.pullbackTopos_additive f))
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
        (Stacks.additive_sheafModuleFiberOfCommRing Φ X.O)))
    (@Functor.preservesZeroMorphisms_comp _ _ _ _ _ _ _ _ _ _ _
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
        (Stacks.additive_sheafModuleFiberOfCommRing (targetPoint f hu Φ) Y.O))
      inferInstance)
    (stalkFunctorIso f hu Φ) (ComplexShape.up ℤ)).app K

omit [HasWeakSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Stacks 05V5 at the level of complexes holds at the named point `Ψ`.**  The hypothesis
`StalkBaseChange` of the K-flatness assertion of Stacks 0DEP is inhabited, with the map of
stalk rings `stalkRingMap`. -/
theorem stalkBaseChange : StalkBaseChange f hu :=
  fun Φ K => ⟨stalkRingMap f hu Φ, ⟨stalkComplexIso f hu Φ K⟩⟩

/-! ### Stacks 0DEP -/

section Main

variable [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

include hu in
/-- **Stacks 0DEP.**  Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi whose
underlying functor of the sites is a morphism of sites, and suppose the site `C` has a
conservative family of points.  Then the degreewise pullback along `f` of a K-flat complex of
`O'`-modules is a K-flat complex of `O`-modules.

The proof is the source's.  K-flatness of `f^*K` is tested at the points of `C` by part (2) of
Stacks 0DEN, which applies because `C` has a conservative family of points.  At a point `Φ` of
`C` the stalk complex of `f^*K` is the extension of scalars, along a map `O'_Ψ ⟶ O_Φ` of stalk
rings, of the stalk complex of `K` at the point `Ψ = f ∘ Φ` of `C'` produced by part (2) of
Stacks 00YA; that is `stalkComplexIso`, which is Stacks 05V5 at the level of complexes, built
from Stacks 05V1 for the inverse image and the stalkwise formula for the extension of scalars
along `f⁻¹O' ⟶ O`.  The stalk complexes of `K` are K-flat by part (1) of Stacks 0DEN on the
target, and extension of scalars preserves K-flatness by Stacks 06Y1. -/
@[stacks 0DEP]
theorem kFlat_pullbackComplex (hX : X.J.HasConservativeFamily.{u})
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.IsKFlat Y.O K) :
    Stacks.SheafOfModules.IsKFlat X.O ((KFlatPullback.pullbackComplex f).obj K) :=
  kFlat_pullbackComplex_of_morphismOfSites f hu hX (stalkBaseChange f hu) K hK

end Main

end Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites

end

end
