module

public import StacksFrontier.Deformation.RingedSpaceThickening.DerivedExtensionClassCriterion
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentExactSequence
import StacksCore.Tactic.StacksAttribute

/-!
# The two maps of naive cotangent complexes of a ringed space deformation

Let `t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})` be a first order thickening with ideal `𝒥`, let
`f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces, let `𝒢` be an `𝒪_X`-module and let
`c : f^*𝒥 ⟶ 𝒢`.  In this situation **Stacks 0GQ4** displays two maps of complexes

`Lf^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'} ⟶ 𝖭𝖫_{X/S}`

and observes that they are *close to* forming a distinguished triangle, by the canonical map of
**Stacks 0E1Z**; it then draws a conclusion under the assumption that they do form one.

The source does not claim that the two maps form a distinguished triangle, and neither does
this file: the triangle appears only as a hypothesis, and the obstruction statement below is the
conditional "if this were a distinguished triangle, then ...".

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.baseInverseImageRingMap`: the map
  `(f ≫ t)^{-1}𝒪_{S'} ⟶ f^{-1}𝒪_S` of sheaves of rings on `X` through which the structure map
  of `f ≫ t` factors, which is what makes `f^{-1}𝒪_S` a middle term of a tower on `X`.
* `AlgebraicGeometry.RingedSpaceThickening.naiveCotangentCompComplexMap`: the second map of
  the remark, `𝖭𝖫_{X/S'} ⟶ 𝖭𝖫_{X/S}`, as a map of complexes of `𝒪_X`-modules, and
  `relativeNaiveCotangentObjMap` its image in `D(𝒪_X)`.
* `AlgebraicGeometry.RingedSpaceThickening.derivedPullbackNaiveCotangentChain`: the composite
  of the remark's two maps in `D(𝒪_X)`.
* `AlgebraicGeometry.RingedSpaceThickening.obstructionExtClass`: the image of a class of
  `Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{S/S'}, 𝒢)` in `Ext²_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` along the connecting map of a
  triangle on the remark's two maps.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.nonempty_deformationSolution_iff_obstruction_eq_zero`:
  the conditional of the remark.  *Given* that the remark's two maps form a distinguished
  triangle with connecting map `w`, a solution of **Stacks 08U7** exists if and only if the
  image of `ξ` in `Ext²_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` vanishes, so that image is the obstruction.

## Implementation notes

Only the second of the two displayed maps is constructed here.  The first,
`q : Lf^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'}`, is an argument, as it is in
`AlgebraicGeometry.RingedSpaceThickening.solutionsEquivDerivedExtFibre` (**Stacks 0GQ3**): the
degreewise pullback of `𝖭𝖫_{S/S'}` in the spelling the comparison `Lf^*K ⟶ f^*K` of
**Stacks 06YJ** uses is not identified with the spelling the base change map of **Stacks 0E1Z**
uses.

The second map is the map `𝖭𝖫_{C/A} ⟶ 𝖭𝖫_{C/B}` of a tower `A ⟶ B ⟶ C` of sheaves of rings on
`X`, taken at `(f ≫ t)^{-1}𝒪_{S'} ⟶ f^{-1}𝒪_S ⟶ 𝒪_X`.  Its source is `𝖭𝖫` of the *composite*
of the two ring maps, and `baseInverseImageRingMap_comp` identifies that composite with the
structure map of `f ≫ t`, so that the source is `𝖭𝖫_{X/S'}` on the nose; the identification
enters as an `eqToHom`.

The exactness used for the conditional is contravariant Yoneda exactness of a distinguished
triangle, applied after one rotation, together with the fullness and faithfulness of the shift:
a class of `Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{S/S'}, 𝒢)` is a restriction along `q` exactly when its Yoneda
product with the connecting map vanishes.  Composition of `Ext` classes is
`CategoryTheory.ShiftedHom.comp`, degrees adding, so that product is literally the image in
`Ext²`.

## References

* [Stacks Project, Tag 0GQ4](https://stacks.math.columbia.edu/tag/0GQ4)
* [Stacks Project, Tag 0GQ3](https://stacks.math.columbia.edu/tag/0GQ3)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
* [Stacks Project, Tag 0E1Z](https://stacks.math.columbia.edu/tag/0E1Z)
* [Stacks Project, Tag 08TN](https://stacks.math.columbia.edu/tag/08TN)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Sheaves.RingedSpaceDifferentials (sheafAdjunction structureSheafMap
  structureSheafMap_comp inverseImageSheaf homEquiv_inverseImageStructureMap)

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S S' : RingedSpace.{u, u}}

/-! ### The map `𝖭𝖫_{X/S'} ⟶ 𝖭𝖫_{X/S}` -/

/-- The map `(f ≫ t)^{-1}𝒪_{S'} ⟶ f^{-1}𝒪_S` of sheaves of rings on `X`: the map adjoint to
the structure map of `t` followed by the unit of `f^{-1} ⊣ f_*`.  It exhibits `f^{-1}𝒪_S` as a
middle term of a tower `(f ≫ t)^{-1}𝒪_{S'} ⟶ f^{-1}𝒪_S ⟶ 𝒪_X` on `X`. -/
public def baseInverseImageRingMap (f : X ⟶ S) (t : S ⟶ S') :
    inverseImageSheaf (f ≫ t) ⟶ inverseImageSheaf f :=
  ((sheafAdjunction (f ≫ t)).homEquiv S'.sheaf (inverseImageSheaf f)).symm
    (structureSheafMap t ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).map
        ((sheafAdjunction f).unit.app S.sheaf))

/-- The tower `(f ≫ t)^{-1}𝒪_{S'} ⟶ f^{-1}𝒪_S ⟶ 𝒪_X` composes to the structure map of
`f ≫ t`, so its naive cotangent complex over the outer ring is `𝖭𝖫_{X/S'}`. -/
public theorem baseInverseImageRingMap_comp (f : X ⟶ S) (t : S ⟶ S') :
    baseInverseImageRingMap f t ≫
        Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f =
      Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap (f ≫ t) := by
  apply ((sheafAdjunction (f ≫ t)).homEquiv S'.sheaf X.sheaf).injective
  rw [Adjunction.homEquiv_naturality_right, homEquiv_inverseImageStructureMap,
    baseInverseImageRingMap, Equiv.apply_symm_apply]
  change (structureSheafMap t ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).map
        ((sheafAdjunction f).unit.app S.sheaf)) ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} t.hom.base).map
        ((TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
          (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f)) =
    structureSheafMap (f ≫ t)
  rw [structureSheafMap_comp f t, Category.assoc, ← Functor.map_comp,
    ← Adjunction.homEquiv_unit, homEquiv_inverseImageStructureMap]

/-- `𝖭𝖫_{X/S'}` is the naive cotangent complex of the composite of the tower
`(f ≫ t)^{-1}𝒪_{S'} ⟶ f^{-1}𝒪_S ⟶ 𝒪_X`. -/
public theorem naiveCotangentComplex_comp_eq (f : X ⟶ S) (t : S ⟶ S') :
    RingedSpace.naiveCotangentComplex (f ≫ t) =
      Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u}
        (Opens.grothendieckTopology X.carrier) (inverseImageSheaf (f ≫ t)) X.sheaf
        (baseInverseImageRingMap f t ≫
          Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f) :=
  congrArg
    (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u}
      (Opens.grothendieckTopology X.carrier) (inverseImageSheaf (f ≫ t)) X.sheaf)
    (baseInverseImageRingMap_comp f t).symm

/-- The map of complexes `𝖭𝖫_{X/S'} ⟶ 𝖭𝖫_{X/S}`: the canonical map of a tower of sheaves of
rings on `X`, taken at `(f ≫ t)^{-1}𝒪_{S'} ⟶ f^{-1}𝒪_S ⟶ 𝒪_X`. -/
@[stacks 0GQ4 "the second map of complexes of the remark, 𝖭𝖫_{X/S'} ⟶ 𝖭𝖫_{X/S}"]
public def naiveCotangentCompComplexMap (f : X ⟶ S) (t : S ⟶ S') :
    RingedSpace.naiveCotangentComplex (f ≫ t) ⟶ RingedSpace.naiveCotangentComplex f :=
  eqToHom (naiveCotangentComplex_comp_eq f t) ≫
    Stacks.SheafOfModules.spaceRelativeNaiveCotangentComplexMap
      (inverseImageSheaf (f ≫ t)) (inverseImageSheaf f) X.sheaf
      (baseInverseImageRingMap f t)
      (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f)

/-- The map `𝖭𝖫_{X/S'} ⟶ 𝖭𝖫_{X/S}`, read in `D(𝒪_X)`. -/
public def relativeNaiveCotangentObjMap (f : X ⟶ S) (t : S ⟶ S') :
    relativeNaiveCotangentObj (f ≫ t) ⟶ relativeNaiveCotangentObj f :=
  DerivedCategory.Q.map (naiveCotangentCompComplexMap f t)

/-- The chain `Lf^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'} ⟶ 𝖭𝖫_{X/S}`, composed in `D(𝒪_X)`: the first map
is the given comparison `q`, the second is `relativeNaiveCotangentObjMap`. -/
@[stacks 0GQ4 "the remark's chain Lf^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'} ⟶ 𝖭𝖫_{X/S}, with q carried"]
public def derivedPullbackNaiveCotangentChain {f : X ⟶ S} {t : S ⟶ S'}
    (q : derivedPullbackNaiveCotangent f t ⟶ relativeNaiveCotangentObj (f ≫ t)) :
    derivedPullbackNaiveCotangent f t ⟶ relativeNaiveCotangentObj f :=
  q ≫ relativeNaiveCotangentObjMap f t

/-! ### The conditional obstruction -/

/-- **Contravariant Yoneda exactness of a distinguished triangle**, in degree one: a shifted
morphism out of `T.obj₁` is a restriction along `T.mor₁` exactly when its Yoneda product with
the connecting morphism `T.mor₃` vanishes. -/
public theorem exists_comp_eq_iff_shiftedHom_comp_eq_zero' {C : Type*} [Category C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Triangle C) (hT : T ∈ distTriang C) {G : C} (η : ShiftedHom T.obj₁ G 1) :
    (∃ z : ShiftedHom T.obj₂ G 1, η = T.mor₁ ≫ z) ↔
      ShiftedHom.comp T.mor₃ η (show (1 : ℤ) + 1 = 2 by omega) = 0 := by
  constructor
  · rintro ⟨z, rfl⟩
    rw [ShiftedHom.comp, Functor.map_comp, ← Category.assoc, ← Category.assoc,
      comp_distTriang_mor_zero₃₁ T hT, zero_comp, zero_comp]
  · intro h
    have h' : T.mor₃ ≫ η⟦(1 : ℤ)⟧' = 0 := by
      rw [← cancel_mono ((shiftFunctorAdd' C (1 : ℤ) 1 2 (by omega)).inv.app G), zero_comp]
      rwa [ShiftedHom.comp, ← Category.assoc] at h
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ T.rotate (rot_of_distTriang T hT)
      (η⟦(1 : ℤ)⟧') h'
    obtain ⟨z, rfl⟩ := (shiftFunctor C (1 : ℤ)).map_surjective
      (show (T.obj₂)⟦(1 : ℤ)⟧ ⟶ (G⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧ from g)
    refine ⟨-z, (shiftFunctor C (1 : ℤ)).map_injective ?_⟩
    rw [hg]
    simp only [Triangle.rotate_mor₃, Functor.map_comp, Functor.map_neg,
      Preadditive.comp_neg]
    exact Preadditive.neg_comp _ _

/-- The image of a class of `Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{S/S'}, 𝒢)` in `Ext²_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` along
a connecting morphism `w : 𝖭𝖫_{X/S} ⟶ (Lf^*𝖭𝖫_{S/S'})[1]`: the Yoneda product with `w`. -/
public def obstructionExtClass {f : X ⟶ S} {t : S ⟶ S'}
    {G : SheafOfModules.{u} (structureSheafRing X)}
    (w : relativeNaiveCotangentObj f ⟶ (derivedPullbackNaiveCotangent f t)⟦(1 : ℤ)⟧)
    (η : extOnePulledNaiveCotangent f t G) :
    DerivedCategory.Ext (relativeNaiveCotangentObj f)
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj G) 2 :=
  ShiftedHom.comp w η (show (1 : ℤ) + 1 = 2 by omega)

section Conditional

variable {t : S ⟶ S'} (ht : IsFirstOrderThickening t) {f : X ⟶ S}
  {G : SheafOfModules.{u} (structureSheafRing X)}
  (c : (modulePullback f).obj (baseIdealOnReduction t) ⟶ G)
  (r : Setoid (ExtensionOverBase f t G))

/-- In the situation of **Stacks 0GQ3**, *given* that the two maps
`Lf^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'} ⟶ 𝖭𝖫_{X/S}` form a distinguished triangle with connecting morphism
`w`, the deformation problem of **Stacks 08U7** has a solution exactly when the image of `ξ` in
`Ext²_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` vanishes; that image is therefore the obstruction.

The triangle is a hypothesis, not a claim: the source only says that the two maps are close to
forming a distinguished triangle, and its conclusion is drawn under that assumption.  The
remaining arguments are those of `solutionsEquivDerivedExtFibre`, which supplies the bijection
of **Stacks 0GQ3** between isomorphism classes of solutions and the fibre over the image of
`ξ`. -/
@[stacks 0GQ4 "the conditional: given the triangle, ξ's image in Ext² obstructs 08U7"]
public theorem nonempty_deformationSolution_iff_obstruction_eq_zero
    (E : Quotient r ≃ extOneNaiveCotangent (f ≫ t) G)
    (q : derivedPullbackNaiveCotangent f t ⟶ relativeNaiveCotangentObj (f ≫ t))
    (xi : extOneNaiveCotangent t (baseIdealOnReduction t))
    (P : NaiveCotangentTwoTerm
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0))
    (hP : P.obj = derivedPullbackNaiveCotangent f t)
    (δ : Quotient r → (P.conormal ⟶ G))
    (e : ∀ p : Quotient r, SolutionInClass ht c r p ≃
      {θ : P.base ⟶ G // P.d ≫ θ = δ p})
    (hcompat : ∀ p : Quotient r, eqToHom hP ≫
      (pullbackExtClass f t c xi - restrictDerivedExtClass q (E p)) =
        P.conormalExtClass G (δ p))
    (w : relativeNaiveCotangentObj f ⟶ (derivedPullbackNaiveCotangent f t)⟦(1 : ℤ)⟧)
    (htri : Triangle.mk q (relativeNaiveCotangentObjMap f t) w ∈
      distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))) :
    Nonempty (DeformationSolution t ht f G c) ↔
      obstructionExtClass w (pullbackExtClass f t c xi) = 0 := by
  refine Iff.trans ?_ (exists_comp_eq_iff_shiftedHom_comp_eq_zero'
    (Triangle.mk q (relativeNaiveCotangentObjMap f t) w) htri (pullbackExtClass f t c xi))
  refine Iff.trans ?_ (exists_congr fun _ => eq_comm)
  refine Iff.trans ?_ nonempty_subtype
  refine Iff.trans ?_ (Equiv.nonempty_congr
    (solutionsEquivDerivedExtFibre ht c r E q xi P hP δ e hcompat))
  exact ⟨fun h => h.elim fun Q => ⟨Quotient.mk _ Q⟩, fun h => h.elim fun s => ⟨s.out⟩⟩

end Conditional

end AlgebraicGeometry.RingedSpaceThickening

end
