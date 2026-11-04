module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.StalkBaseChangeAtTheTargetPoint

/-!
# The stalk of a pullback along an arbitrary morphism of ringed topoi, and Stacks 0DEP

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi in the sense of Stacks 01D3 —
a morphism of the underlying topoi together with the structure map, and nothing about the
underlying sites — and let `Φ` be a point of the site `C`.  Composing the point of the topos
`Sh(C)` attached to `Φ` by part (1) of Stacks 00YA with the morphism of topoi of `f` gives a
point of the topos `Sh(C')`, and part (2) of Stacks 00YA produces from it a **point `Ψ` of the
site `C'`** whose stalk functor is the inverse image along `f` followed by the stalk functor of
`Φ`.  That `Ψ` is the point the source calls `q = f ∘ Φ`.

This file proves the comparison of Stacks 05V5 at that point,

`(f^*G)_Φ ≅ G_Ψ ⊗_{O'_Ψ} O_Φ`,

naturally in the sheaf of `O'`-modules `G`, and with it **Stacks 0DEP**: if `C` has a
conservative family of points, then the degreewise pullback along `f` of a K-flat complex of
`O'`-modules is a K-flat complex of `O`-modules.

## Main definitions

* `Stacks.Sheaves.DerivedPullback.StalkBaseChangeOfToposHom.targetPoint`: the point `Ψ` of the
  target site attached to `Φ`.
* `Stacks.Sheaves.DerivedPullback.StalkBaseChangeOfToposHom.stalkRingMap`: the map `O'_Ψ ⟶ O_Φ`
  of stalk rings along which the comparison extends scalars.

## Main results

* `Stacks.Sheaves.DerivedPullback.StalkBaseChangeOfToposHom.stalkFunctorIso`: **Stacks 05V5 at
  the point `Ψ`**, as a natural isomorphism of stalk functors, for an arbitrary morphism of
  ringed topoi.
* `Stacks.Sheaves.DerivedPullback.StalkBaseChangeOfToposHom.stalkComplexIso`: the same
  comparison for a cochain complex of sheaves of modules.
* `Stacks.Sheaves.DerivedPullback.StalkBaseChangeOfToposHom.kFlat_pullbackComplex`:
  **Stacks 0DEP** for an arbitrary morphism of ringed topoi.

## Implementation notes

**What the morphism is, and why no hypothesis on the sites is left.**  The companion development
`Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites` proves the same two statements for
an `AlgebraicGeometry.RingedToposSiteHom` whose underlying functor of the sites is a morphism of
sites.  That hypothesis is an artefact of the *presentation*, exactly as it is for Stacks 0G7E:
`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos` is an abstract left adjoint, and
identifying its geometric factor with the inverse image of sheaves of sets is a
Beck--Chevalley comparison that needs a morphism of sites.  For the pullback
`AlgebraicGeometry.RingedToposHom.pullbackModules` of Stacks 03D6 part (2) the factorization

`f^* = (O ⊗_{f⁻¹O'} -) ∘ f⁻¹`

is how the functor is *built*, so the comparison is definitional and the hypothesis disappears;
left exactness of `f⁻¹`, which is what the point of the target site is constructed from, is a
field of `MorphismOfTopoi`.  Nothing here is assumed about the underlying sites of `f` beyond
the standing smallness of a `AlgebraicGeometry.RingedTopos.{u, u, u}`, which part (2) of
Stacks 00YA needs in order to produce a point of a site at all.

**The chain, and what each link is.**  The statements are made for the four-field morphism of
ringed topoi `Stacks.Sheaves.RingedToposModules.RingedToposHom`, which records the structure map
in both its forms; `AlgebraicGeometry.RingedToposHom.toModulesHom` produces one from a morphism
in the sense of Stacks 01D3, and `AlgebraicGeometry.RingedToposHom.pullbackModules` is by
definition the pullback along it.  The four links of the comparison are:

* `stalkIsoStepOne`, the stalkwise formula for the extension of scalars along `f⁻¹O' ⟶ O`: the
  stalk does not see the sheafification that extension of scalars performs, so
  `(O ⊗_{f⁻¹O'} F)_Φ ≅ O_Φ ⊗_{(f⁻¹O')_Φ} F_Φ`.  This is Stacks 03CZ read at a point.
* `stalkIsoStepTwo` and `stalkIsoStepThree`, the reconciliation of restricting and then
  extending scalars along the isomorphism `O'_Ψ ≅ (f⁻¹O')_Φ` with a single extension of scalars
  along the composite `O'_Ψ ⟶ O_Φ`, which is `ModuleCat.restrictExtendScalarsCompIso`.
* `stalkIsoStepFour`, Stacks 05V1 for sheaves of modules at `Ψ`: the identification
  `G_Ψ ≅ (f⁻¹G)_Φ`, semilinear over `O'_Ψ ≅ (f⁻¹O')_Φ`.

The site-presented development spends a fifth link, `stalkIsoStepOne` there, on identifying its
abstract pullback with the pullback along the four-field morphism; that link is what is absent
here.

**Three spellings of the stalk functor on sheaves of modules**, as in the site-presented
development: over a sheaf of rings `R` the stalk at `Φ` is `Stacks.sheafModuleFiber Φ R`, valued
in modules over the `RingCat`-valued stalk of `R`; for the structure sheaf one wants modules
over the `CommRingCat`-valued stalk instead, which is `Stacks.sheafModuleFiberOfCommRing Φ O`,
the functor `Stacks.Sheaves.KFlatStalkCriterion.stalkComplex` is built from; and
`Stacks.SitePointBaseChange.sheafStalk Φ A h` is the functor the base-change interchange is
stated for.  The last two agree on the nose for the structure sheaf of a ringed topos, both
sides being built from the same presheaf of commutative rings.  All three identifications hold
by `rfl` and are used silently below.

**Universes.**  Both ringed topoi are taken at `AlgebraicGeometry.RingedTopos.{u, u, u}`: the
objects, morphisms and sections universes agree.  The narrowing is forced independently by
`SheafOfModules.pullback`, by both parts of Stacks 0DEN, and by part (2) of Stacks 00YA, whose
reconstruction of a point of the site is stated for a site small in the universe of the sheaves
of sets.

## References

* [Stacks Project, Tag 0DEP](https://stacks.math.columbia.edu/tag/0DEP)
* [Stacks Project, Tag 0DEN](https://stacks.math.columbia.edu/tag/0DEN)
* [Stacks Project, Tag 00YA](https://stacks.math.columbia.edu/tag/00YA)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
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
open Stacks.Sheaves.StalkInverseImage
open Stacks.Sheaves.KFlatStalkCriterion (structureStalk stalkComplex)

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

noncomputable section

universe u

namespace Stacks.Sheaves.DerivedPullback.StalkBaseChangeOfToposHom

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (g : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y) (Φ : X.J.Point.{u})

/-! ### The point of the target site attached to a point of the source site -/

/-- **The composite point of the target topos.**  A point of the topos `Sh(C)` composed with the
morphism of topoi underlying `g` is a point of the topos `Sh(C')`.  This is the point the source
writes `q = f ∘ Φ`. -/
def toposPoint : PointOfTopos.{u, u, u} Y.J :=
  MorphismOfTopoi.comp g.toToposHom Φ.pointOfTopos

/-- **The point `Ψ` of the target site.**  The point of the site `C'` underlying the composite
point of the topos `Sh(C')`, by Stacks 00YA part (2). -/
def targetPoint : Y.J.Point.{u} :=
  (toposPoint g Φ).sitePoint

/-- **The stalk functor at `Ψ` is the inverse image along `g` followed by the stalk functor at
`Φ`.**  This is the identification of Stacks 00YA part (2) for the composite point, and it is
the sheaf-of-sets shadow of the comparison of Stacks 05V5. -/
def targetPointStalkIso :
    (targetPoint g Φ).sheafFiber (A := Type u) ≅
      g.toToposHom.inverseImage ⋙ Φ.sheafFiber (A := Type u) :=
  (toposPoint g Φ).sheafFiberIsoInverseImage

/-! ### The ingredients of the comparison -/

/-- The inverse image `f⁻¹O'` of the structure sheaf of the target, as a presheaf of commutative
rings on the source site. -/
abbrev inverseImageStructure : X.Cᵒᵖ ⥤ CommRingCat.{u} :=
  inverseImageStructureCommRing g

/-- The inverse image `f⁻¹O'` of the structure sheaf of the target, as a sheaf of rings on the
source site. -/
abbrev inverseImageStructureRing : Sheaf X.J RingCat.{u} :=
  inverseImageRingSheaf g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)

/-- The inverse image of sheaves of modules along `g`, Stacks 03D2. -/
abbrev inverseImageFunctor :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{u} (inverseImageStructureRing g) :=
  inverseImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)

/-- The stalk at `Φ` of a sheaf of `f⁻¹O'`-modules, over the `RingCat`-valued stalk of
`f⁻¹O'`. -/
abbrev inverseImageStalkFunctor := Stacks.sheafModuleFiber Φ (inverseImageStructureRing g)

/-- The comparison of the `CommRingCat`-valued stalk of `f⁻¹O'` at `Φ` with its `RingCat`-valued
stalk. -/
abbrev toInverseImageStalkRing := Stacks.toRingFiber Φ (inverseImageStructure g)

/-- The comparison of the `CommRingCat`-valued stalk `O'_Ψ` with the `RingCat`-valued stalk of
the sheaf of rings underlying `O'`. -/
abbrev toTargetStalkRing := Stacks.toRingFiber (targetPoint g Φ) Y.O.obj

/-- The stalk at `Φ` of the inverse-image form of the structure map of `g`. -/
abbrev fSharpStalk := Stacks.SitePointBaseChange.stalkRingHom (fSharpCommRing g) Φ

/-- **The isomorphism `O'_Ψ ≅ (f⁻¹O')_Φ` of stalk rings**, read between the `RingCat`-valued
stalks.  This is the ring half of Stacks 05V1 at `Ψ`. -/
def targetStalkRingEquiv :
    ((targetPoint g Φ).presheafFiber (A := RingCat.{u})).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj ≃+*
      (Φ.presheafFiber (A := RingCat.{u})).obj (inverseImageStructureRing g).obj :=
  stalkRingEquiv g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ (targetPoint g Φ)
    (targetPointStalkIso g Φ)

/-- **Module-level Stacks 05V1 at the point `Ψ`, as a natural isomorphism of stalk functors.**
The stalk functor at `Ψ` is the inverse image of sheaves of modules followed by the stalk
functor at `Φ` and restriction of scalars along the isomorphism of stalk rings. -/
def targetStalkNatIso :
    Stacks.sheafModuleFiber (targetPoint g Φ) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≅
      inverseImageFunctor g ⋙ inverseImageStalkFunctor g Φ ⋙
        ModuleCat.restrictScalars (targetStalkRingEquiv g Φ).toRingHom :=
  stalkNatIso g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) Φ (targetPoint g Φ)
    (targetPointStalkIso g Φ)

/-- **The isomorphism `O'_Ψ ≅ (f⁻¹O')_Φ` of `CommRingCat`-valued stalk rings.**  It is
`targetStalkRingEquiv`, which compares the `RingCat`-valued stalks, conjugated by the comparison
of the `RingCat`-valued stalk of a presheaf of commutative rings with its `CommRingCat`-valued
one at either end. -/
def targetCommRingStalkEquiv :
    structureStalk Y.O (targetPoint g Φ) ≃+* Stacks.ringFiber Φ (inverseImageStructure g) :=
  ((Stacks.commRingPresheafFiberIso (targetPoint g Φ)
          Y.O.obj).ringCatIsoToRingEquiv.symm.trans (targetStalkRingEquiv g Φ)).trans
    (Stacks.commRingPresheafFiberIso Φ (inverseImageStructure g)).ringCatIsoToRingEquiv

/-- **The map `O'_Ψ ⟶ O_Φ` of stalk rings.**  It is the isomorphism `O'_Ψ ≅ (f⁻¹O')_Φ` followed
by the stalk at `Φ` of the inverse-image form `f⁻¹O' ⟶ O` of the structure map of `g`. -/
def stalkRingMap : structureStalk Y.O (targetPoint g Φ) →+* structureStalk X.O Φ :=
  (fSharpStalk g Φ).comp (targetCommRingStalkEquiv g Φ).toRingHom

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})] in
/-- The isomorphism `O'_Ψ ≅ (f⁻¹O')_Φ` of `CommRingCat`-valued stalks is compatible with the
comparisons to the `RingCat`-valued stalks and with `targetStalkRingEquiv`. -/
lemma toInverseImageStalkRing_comp_targetCommRingStalkEquiv :
    (toInverseImageStalkRing g Φ).comp (targetCommRingStalkEquiv g Φ).toRingHom =
      (targetStalkRingEquiv g Φ).toRingHom.comp (toTargetStalkRing g Φ) := by
  refine RingHom.ext fun x => ?_
  exact RingEquiv.symm_apply_apply
    (Stacks.commRingPresheafFiberIso Φ (inverseImageStructure g)).ringCatIsoToRingEquiv _

/-! ### The comparison of Stacks 05V5 at the point of the target site -/

/-- The stalk at `Φ` of the extension of scalars along `f⁻¹O' ⟶ O` is the extension of scalars
along the stalk of that map: Stacks 05V5 for the second half of the pullback. -/
def stalkIsoStepOne :
    g.pullbackModules ⋙ Stacks.sheafModuleFiberOfCommRing Φ X.O ≅
      inverseImageFunctor g ⋙ inverseImageStalkFunctor g Φ ⋙
        ModuleCat.restrictScalars (toInverseImageStalkRing g Φ) ⋙
          ModuleCat.extendScalars (fSharpStalk g Φ) :=
  Functor.isoWhiskerLeft (inverseImageFunctor g)
    (Stacks.SitePointBaseChange.extendScalarsSheafStalkNatIso Φ (fSharpCommRing g)
      (inverseImageStructureRing g).property (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)

/-- Precomposing the restriction and the extension of scalars with the isomorphism
`O'_Ψ ≅ (f⁻¹O')_Φ` of stalk rings leaves their composite unchanged. -/
def stalkIsoStepTwo :
    inverseImageFunctor g ⋙ inverseImageStalkFunctor g Φ ⋙
        ModuleCat.restrictScalars (toInverseImageStalkRing g Φ) ⋙
          ModuleCat.extendScalars (fSharpStalk g Φ) ≅
      inverseImageFunctor g ⋙ inverseImageStalkFunctor g Φ ⋙
        ModuleCat.restrictScalars ((toInverseImageStalkRing g Φ).comp
            (targetCommRingStalkEquiv g Φ).toRingHom) ⋙
          ModuleCat.extendScalars (stalkRingMap g Φ) :=
  Functor.isoWhiskerLeft (inverseImageFunctor g ⋙ inverseImageStalkFunctor g Φ)
    (ModuleCat.restrictExtendScalarsCompIso (toInverseImageStalkRing g Φ)
      (fSharpStalk g Φ) (targetCommRingStalkEquiv g Φ)).symm

/-- The restriction of scalars along the composite `O'_Ψ ⟶ (f⁻¹O')_Φ` of the two comparisons of
stalk rings is the successive restriction along each of them. -/
def stalkIsoStepThree :
    inverseImageFunctor g ⋙ inverseImageStalkFunctor g Φ ⋙
        ModuleCat.restrictScalars ((toInverseImageStalkRing g Φ).comp
            (targetCommRingStalkEquiv g Φ).toRingHom) ⋙
          ModuleCat.extendScalars (stalkRingMap g Φ) ≅
      inverseImageFunctor g ⋙ inverseImageStalkFunctor g Φ ⋙
        (ModuleCat.restrictScalars (targetStalkRingEquiv g Φ).toRingHom ⋙
            ModuleCat.restrictScalars (toTargetStalkRing g Φ)) ⋙
          ModuleCat.extendScalars (stalkRingMap g Φ) :=
  Functor.isoWhiskerLeft (inverseImageFunctor g ⋙ inverseImageStalkFunctor g Φ)
    (Functor.isoWhiskerRight
      (ModuleCat.restrictScalarsComp' (toTargetStalkRing g Φ)
        (targetStalkRingEquiv g Φ).toRingHom _
        (toInverseImageStalkRing_comp_targetCommRingStalkEquiv g Φ))
      (ModuleCat.extendScalars (stalkRingMap g Φ)))

/-- Stacks 05V1 at the point `Ψ`: the stalk functor at `Ψ` is the inverse image followed by the
stalk functor at `Φ` and restriction of scalars. -/
def stalkIsoStepFour :
    inverseImageFunctor g ⋙ inverseImageStalkFunctor g Φ ⋙
        (ModuleCat.restrictScalars (targetStalkRingEquiv g Φ).toRingHom ⋙
            ModuleCat.restrictScalars (toTargetStalkRing g Φ)) ⋙
          ModuleCat.extendScalars (stalkRingMap g Φ) ≅
      Stacks.sheafModuleFiberOfCommRing (targetPoint g Φ) Y.O ⋙
        ModuleCat.extendScalars (stalkRingMap g Φ) :=
  (Functor.isoWhiskerRight (targetStalkNatIso g Φ)
    (ModuleCat.restrictScalars (toTargetStalkRing g Φ) ⋙
      ModuleCat.extendScalars (stalkRingMap g Φ))).symm

/-- **Stacks 05V5 at the point `Ψ` of the target site, for an arbitrary morphism of ringed
topoi**, as a natural isomorphism of stalk functors: the stalk at `Φ` of the pullback of a sheaf
of `O'`-modules is the extension of scalars along `O'_Ψ ⟶ O_Φ` of its stalk at `Ψ`.

Nothing is assumed about the underlying sites: the pullback of Stacks 03D6 part (2) is built
from the inverse image of Stacks 03D2, so the geometric half of the comparison is the one of
Stacks 05V1 at `Ψ` and the algebraic half is the stalkwise formula for the extension of
scalars. -/
@[stacks 05V5 "the formula `(f^*F)_p ≅ F_q ⊗_{O'_q} O_p` at a point `p` of the source site,
naturally in the `O'`-module `F`, with `q = f ∘ p` the point of the target site induced by `p`;
for an arbitrary morphism of ringed topoi, at `RingedTopos.{u, u, u}`"]
def stalkFunctorIso :
    g.pullbackModules ⋙ Stacks.sheafModuleFiberOfCommRing Φ X.O ≅
      Stacks.sheafModuleFiberOfCommRing (targetPoint g Φ) Y.O ⋙
        ModuleCat.extendScalars (stalkRingMap g Φ) :=
  stalkIsoStepOne g Φ ≪≫ stalkIsoStepTwo g Φ ≪≫ stalkIsoStepThree g Φ ≪≫ stalkIsoStepFour g Φ

end Stacks.Sheaves.DerivedPullback.StalkBaseChangeOfToposHom

/-! ### Stacks 0DEP -/

namespace Stacks.Sheaves.DerivedPullback.StalkBaseChangeOfToposHom

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : AlgebraicGeometry.RingedToposHom X Y) (Φ : X.J.Point.{u})

/-- **Stacks 05V5 at the level of complexes, at the point `Ψ`.**  The stalk complex at `Φ` of
the degreewise pullback of a complex of `O'`-modules is the extension of scalars along
`O'_Ψ ⟶ O_Φ` of its stalk complex at `Ψ`. -/
def stalkComplexIso
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    stalkComplex X.O Φ ((KFlatPullbackOfToposHom.pullbackComplex f).obj K) ≅
      (CochainComplex.extendScalars (stalkRingMap f.toModulesHom Φ)).obj
        (stalkComplex Y.O (targetPoint f.toModulesHom Φ) K) :=
  (@NatIso.mapHomologicalComplex _ _ _ _ _ _ _ _ _
    (@Functor.preservesZeroMorphisms_comp _ _ _ _ _ _ _ _ _ _ _
      (@Functor.preservesZeroMorphisms_of_isLeftAdjoint _ _ _ _ _ _ _
        (pullbackAdjPushforwardModules f.toModulesHom).isLeftAdjoint)
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
        (Stacks.additive_sheafModuleFiberOfCommRing Φ X.O)))
    (@Functor.preservesZeroMorphisms_comp _ _ _ _ _ _ _ _ _ _ _
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
        (Stacks.additive_sheafModuleFiberOfCommRing (targetPoint f.toModulesHom Φ) Y.O))
      inferInstance)
    (stalkFunctorIso f.toModulesHom Φ) (ComplexShape.up ℤ)).app K

section Main

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]

/-- **Stacks 0DEP.**  Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi and
suppose the site `C` has a conservative family of points.  Then the degreewise pullback along
`f` of a K-flat complex of `O'`-modules is a K-flat complex of `O`-modules.

The proof is the source's.  K-flatness of `f^*K` is tested at the points of `C` by part (2) of
Stacks 0DEN, which applies because `C` has a conservative family of points.  At a point `Φ` of
`C` the stalk complex of `f^*K` is the extension of scalars, along the map `O'_Ψ ⟶ O_Φ` of stalk
rings, of the stalk complex of `K` at the point `Ψ = f ∘ Φ` of `C'` produced by part (2) of
Stacks 00YA; that is `stalkComplexIso`, which is Stacks 05V5 at the level of complexes.  The
stalk complexes of `K` are K-flat by part (1) of Stacks 0DEN on the target, and extension of
scalars preserves K-flatness by Stacks 06Y1. -/
@[stacks 0DEP]
theorem kFlat_pullbackComplex (hX : X.J.HasConservativeFamily.{u})
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.IsKFlat Y.O K) :
    Stacks.SheafOfModules.IsKFlat X.O ((KFlatPullbackOfToposHom.pullbackComplex f).obj K) := by
  refine Stacks.SheafOfModules.SitePointStalkSheafify.kFlat_of_stalks X.O hX _ fun Φ => ?_
  exact CochainComplex.KFlat.of_iso (stalkComplexIso f Φ K).symm
    (kFlat_baseChange (stalkRingMap f.toModulesHom Φ) _
      (Stacks.Sheaves.KFlatStalkCriterion.kFlatStalk_of_kFlat_unconditional Y.O
        (targetPoint f.toModulesHom Φ) K hK))

end Main

end Stacks.Sheaves.DerivedPullback.StalkBaseChangeOfToposHom

end

end
