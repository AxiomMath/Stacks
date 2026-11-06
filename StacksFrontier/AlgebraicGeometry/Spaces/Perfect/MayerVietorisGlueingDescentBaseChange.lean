module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisGlueingDescent

/-!
# Base changes of an elementary distinguished square and descent of objects between them

Let `(U₀ ⊆ W₀, f₀ : V₀ ⟶ W₀)` be an elementary distinguished square and let `p : W ⟶ W₀` and
`p' : W' ⟶ W₀` be morphisms of algebraic spaces with a morphism `q : W' ⟶ W` over `W₀`.  By
Stacks 08GN, part (2), the square pulls back to elementary distinguished squares of `W` and of
`W'` (`AlgebraicGeometry.Space.isElementaryDistinguishedSquare_preimage`), and `q` induces a
morphism between them: maps of the open subspaces, of the étale algebraic spaces and of the
intersections, making the cube commute.  This file constructs that morphism and specializes
`AlgebraicGeometry.Space.exists_glue_derivedPullback_iso_of_eds` to it.

This is the shape in which the square step of Stacks 0DKW is used: `W₀` is étale over the initial
space `X₀` of Situation 0DKU, `W` and `W'` are its base changes to a stage and to the limit, and
`q` is the projection.

## Main definitions

* `AlgebraicGeometry.Space.edsPreimageOpenMap`, `edsPreimageEtaleMap`, `edsPreimageInterMap`:
  the three maps of the cube.

## Main results

* `AlgebraicGeometry.Space.edsPreimageOpenMap_comp`, `edsPreimageEtaleMap_comp`,
  `edsFst_comp_edsPreimageOpenMap`, `edsSnd_comp_edsPreimageEtaleMap`: the faces commute.
* `AlgebraicGeometry.Space.exists_glue_derivedPullback_iso_of_edsPreimage`: the descent of an
  object along `q` between the two base changes of the square.

## References

* [Stacks Project, Tag 08GN](https://stacks.math.columbia.edu/tag/08GN)
* [Stacks Project, Tag 0DKW](https://stacks.math.columbia.edu/tag/0DKW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_MayerVietorisGlueingDescentBaseChange
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_MayerVietorisGlueingDescentBaseChange
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {W₀ : AlgebraicSpaces B S hS} {V₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {U₀ : Subfunctor W₀.1} {f₀ : V₀ ⟶ W₀.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W₀.2 U₀ f₀)
  {W W' : AlgebraicSpaces B S hS} (p : W ⟶ W₀) (p' : W' ⟶ W₀) (q : W' ⟶ W)
  (hq : q ≫ p = p')

/-- The elementary distinguished square of `W` obtained by base change along `p : W ⟶ W₀`. -/
abbrev edsPreimage : IsElementaryDistinguishedSquare B S hS W.2 (U₀.preimage p.hom)
    (pullback.snd f₀ p.hom) :=
  isElementaryDistinguishedSquare_preimage B S hS W₀.2 W.2 U₀ f₀ hsq p.hom

/-- The map of the open subspaces of the two base changes induced by `q`. -/
def edsPreimageOpenMap :
    edsOpen B S hS (edsPreimage hsq p') ⟶ edsOpen B S hS (edsPreimage hsq p) :=
  ObjectProperty.homMk (Subfunctor.lift ((U₀.preimage p'.hom).ι ≫ q.hom) (by
    rw [Subfunctor.range_comp, Subfunctor.range_ι, Subfunctor.image_le_iff,
      ← Subfunctor.preimage_comp]
    exact le_of_eq (congrArg U₀.preimage (congrArg (fun φ => φ.hom) hq)).symm))

/-- The map of the étale algebraic spaces of the two base changes induced by `q`. -/
def edsPreimageEtaleMap :
    edsEtale B S hS (edsPreimage hsq p') ⟶ edsEtale B S hS (edsPreimage hsq p) :=
  ObjectProperty.homMk (pullback.lift (pullback.fst f₀ p'.hom) (pullback.snd f₀ p'.hom ≫ q.hom)
    (pullback.condition.trans (((Category.assoc _ _ _).trans
      (congrArg (pullback.snd f₀ p'.hom ≫ ·) (congrArg (fun φ => φ.hom) hq))).symm)))

/-- The inclusion of the open subspace of the base change to `W'`, followed by `q`, equals
`edsPreimageOpenMap` followed by the inclusion of the open subspace of the base change to `W`. -/
theorem edsPreimageOpenMap_comp :
    edsOpenHom B S hS (edsPreimage hsq p') ≫ q =
      edsPreimageOpenMap hsq p p' q hq ≫ edsOpenHom B S hS (edsPreimage hsq p) :=
  ObjectProperty.hom_ext _ rfl

/-- The étale map of the base change to `W'`, followed by `q`, equals `edsPreimageEtaleMap`
followed by the étale map of the base change to `W`. -/
theorem edsPreimageEtaleMap_comp :
    edsEtaleHom B S hS (edsPreimage hsq p') ≫ q =
      edsPreimageEtaleMap hsq p p' q hq ≫ edsEtaleHom B S hS (edsPreimage hsq p) :=
  ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _).symm

/-- The map of the intersections of the two base changes induced by `q`. -/
def edsPreimageInterMap :
    edsInter B S hS (edsPreimage hsq p') ⟶ edsInter B S hS (edsPreimage hsq p) :=
  ObjectProperty.homMk (pullback.lift
    ((edsFst B S hS (edsPreimage hsq p')).hom ≫ (edsPreimageOpenMap hsq p p' q hq).hom)
    ((edsSnd B S hS (edsPreimage hsq p')).hom ≫ (edsPreimageEtaleMap hsq p p' q hq).hom) (by
      have h := (isPullback_edsInter B S hS (edsPreimage hsq p')).w =≫ q
      rw [Category.assoc, Category.assoc, edsPreimageOpenMap_comp hsq p p' q hq,
        edsPreimageEtaleMap_comp hsq p p' q hq] at h
      exact congrArg (fun φ => φ.hom) h))

/-- The projections of the intersections to the open subspaces commute with `edsPreimageInterMap`
and `edsPreimageOpenMap`. -/
theorem edsFst_comp_edsPreimageOpenMap :
    edsFst B S hS (edsPreimage hsq p') ≫ edsPreimageOpenMap hsq p p' q hq =
      edsPreimageInterMap hsq p p' q hq ≫ edsFst B S hS (edsPreimage hsq p) :=
  ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _).symm

/-- The projections of the intersections to the étale algebraic spaces commute with
`edsPreimageInterMap` and `edsPreimageEtaleMap`. -/
theorem edsSnd_comp_edsPreimageEtaleMap :
    edsSnd B S hS (edsPreimage hsq p') ≫ edsPreimageEtaleMap hsq p p' q hq =
      edsPreimageInterMap hsq p p' q hq ≫ edsSnd B S hS (edsPreimage hsq p) :=
  ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _).symm

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

/-- **Descent of an object along `q` between two base changes of an elementary distinguished
square.**  Let `E` be an object of `D(𝒪_{W'})` whose restrictions to the open subspace and to the
étale algebraic space of the base change to `W'` are derived pullbacks of objects `A`, `Bo` on the
corresponding pieces of the base change to `W`, and let `c : A|_P ≅ Bo|_P` be compatible with them
over the intersection (`hc`).  Then `A` and `Bo` glue to an object `F` of `D(𝒪_W)` with
`Lq^* F ≅ E`. -/
theorem exists_glue_derivedPullback_iso_of_edsPreimage
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W')))
    (A : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsOpen B S hS (edsPreimage hsq p)))))
    (Bo : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsEtale B S hS (edsPreimage hsq p)))))
    (αU : (smallEtaleDerivedModulePullback B S hS (edsPreimageOpenMap hsq p p' q hq)).obj A ≅
      (smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS (edsPreimage hsq p'))).obj E)
    (αV : (smallEtaleDerivedModulePullback B S hS (edsPreimageEtaleMap hsq p p' q hq)).obj Bo ≅
      (smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS (edsPreimage hsq p'))).obj E)
    (c : (smallEtaleDerivedModulePullback B S hS (edsFst B S hS (edsPreimage hsq p))).obj A ≅
      (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS (edsPreimage hsq p))).obj Bo)
    (hc : (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq p p' q hq)).map c.hom =
      ((DerivedPullbackComposition.canonical B S hS).squareIso
          (edsFst B S hS (edsPreimage hsq p')) (edsPreimageOpenMap hsq p p' q hq)
          (edsPreimageInterMap hsq p p' q hq) (edsFst B S hS (edsPreimage hsq p))
          (edsFst_comp_edsPreimageOpenMap hsq p p' q hq)).hom.app A ≫
        (smallEtaleDerivedModulePullback B S hS (edsFst B S hS (edsPreimage hsq p'))).map
          αU.hom ≫
        ((DerivedPullbackComposition.canonical B S hS).squareIso
          (edsSnd B S hS (edsPreimage hsq p')) (edsEtaleHom B S hS (edsPreimage hsq p'))
          (edsFst B S hS (edsPreimage hsq p')) (edsOpenHom B S hS (edsPreimage hsq p'))
          (isPullback_edsInter B S hS (edsPreimage hsq p')).flip.w).hom.app E ≫
        (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS (edsPreimage hsq p'))).map
          αV.inv ≫
        ((DerivedPullbackComposition.canonical B S hS).squareIso
          (edsSnd B S hS (edsPreimage hsq p')) (edsPreimageEtaleMap hsq p p' q hq)
          (edsPreimageInterMap hsq p p' q hq) (edsSnd B S hS (edsPreimage hsq p))
          (edsSnd_comp_edsPreimageEtaleMap hsq p p' q hq)).inv.app Bo) :
    ∃ (F : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W)))
      (_ : (smallEtaleDerivedModulePullback B S hS
        (edsOpenHom B S hS (edsPreimage hsq p))).obj F ≅ A)
      (_ : (smallEtaleDerivedModulePullback B S hS
        (edsEtaleHom B S hS (edsPreimage hsq p))).obj F ≅ Bo),
      Nonempty ((smallEtaleDerivedModulePullback B S hS q).obj F ≅ E) :=
  exists_glue_derivedPullback_iso_of_eds (edsPreimage hsq p) (edsPreimage hsq p') q
    (edsPreimageOpenMap hsq p p' q hq) (edsPreimageEtaleMap hsq p p' q hq)
    (edsPreimageInterMap hsq p p' q hq) (edsPreimageOpenMap_comp hsq p p' q hq)
    (edsPreimageEtaleMap_comp hsq p p' q hq) (edsFst_comp_edsPreimageOpenMap hsq p p' q hq)
    (edsSnd_comp_edsPreimageEtaleMap hsq p p' q hq) E A Bo αU αV c hc

end AlgebraicGeometry.Space

end
