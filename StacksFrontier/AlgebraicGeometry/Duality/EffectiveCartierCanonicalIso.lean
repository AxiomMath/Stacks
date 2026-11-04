module

public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierDerivedSheafHomIso
public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierTraceDescription
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportBifunctorModel
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedPushforwardConservative
public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierDerivedSheafHomSupplement
public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierDualTriangleFirstMapSectionsCore

/-!
# The canonical comparison morphism of Tag 0B4B is an isomorphism

Let `X` be a scheme and `D ⊆ X` an effective Cartier divisor, with closed immersion
`i : D ⟶ X`, ideal sheaf `ℐ_D`, associated invertible sheaf `𝒪_X(D) = ℐ_D^∨` and normal sheaf
`𝒩 = 𝒩_{D/X} = i^* 𝒪_X(D)`.

`StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierDerivedSheafHom` builds the canonical
comparison morphism `𝒩[-1] ⟶ R ℰom(𝒪_D, 𝒪_X)` of
[Stacks, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B), and
`StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierDerivedSheafHomIso` proves separately
that *some* isomorphism `𝒩[-1] ≅ R ℰom(𝒪_D, 𝒪_X)` exists. This file is where the two meet.

## Main definitions

* `Stacks.Divisors.derivedDivisorQuotientMap`: the **derived unit** `𝒪_X ⟶ Ri_* 𝒪_D` in
  `D(𝒪_X)`, the underived restriction map `𝒪_X ⟶ i_* 𝒪_D` read through the identification of
  `(i_* 𝒪_D)[0]` with `Ri_* 𝒪_D`.
* `Stacks.Divisors.pushforwardDerivedSheafHomIdealDualIso`: the identification
  `Ri_* R ℰom(𝒪_D, 𝒪_X) ≅ R ℰom_{𝒪_X}(i_* 𝒪_D, 𝒪_X)` with the first term of the triangle of
  [Stacks, Tag 08I0].

## Main results

* `Stacks.Divisors.derivedDivisorQuotientMap_comp`: the derived unit, followed by the
  identification `Ri_* 𝒪_D ≅ (i_* 𝒪_D)[0]`, is the underived restriction map in degree zero.
  This is what pins the derived unit down.
* `Stacks.Divisors.pushforwardDerivedSheafHomIdealDualIso_trace`: **the trace description.** The
  counit of [Stacks, Tag 0A76] at `𝒪_X` is that identification followed by the first map of the
  triangle of [Stacks, Tag 08I0] and by `R ℰom_{𝒪_X}(𝒪_X, 𝒪_X) ≅ 𝒪_X`.
* `Stacks.Divisors.isIso_normalShiftToDerivedSheafHomExactSupport` and
  `Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport`: **the whole of
  [Stacks, Tag 0B4B] for the canonical comparison morphism**, unconditionally — the morphism
  `𝒩[-1] ⟶ R ℰom(𝒪_D, 𝒪_X)` built in
  `StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierDerivedSheafHom` *is* an isomorphism.

## Implementation notes

**Why the library's isomorphism of [Stacks, Tag 0A77] is not the one used.** That isomorphism,
`…derivedSheafHomExactSupportPushforwardNatIso`, is pinned only through
`derivedSheafHomExactSupportPushforwardNatIso_app`, which reduces it to [Stacks, Tag 0E2I]'s
`derivedSheafHomPushforwardNatIso`, whose components are conjugated by
`DerivedCategory.Q.objObjPreimageIso`, that is, by a *chosen* cochain representative of the
source object `Ri_* 𝒪_D`. Reading the trace through it would therefore need naturality of the
bifunctor model in its *source* variable, and a bridge across that chosen representative.

Neither is needed, because that isomorphism is never used for its own sake: it enters
only through `Stacks.Divisors.pushforwardNormalShiftToIdealDual`, where any isomorphism
`Ri_* R ℰom(𝒪_D, 𝒪_X) ≅ R ℰom_{𝒪_X}(i_* 𝒪_D, 𝒪_X)` carrying the trace would do. So
`Stacks.Divisors.pushforwardDerivedSheafHomIdealDualIso` is *built* with the trace, out of
`…ClosedQuotientMorphismOfRingedSpaces.structureBifunctorModelIso`: the identification at the
class of a K-injective complex — four identifications, none of them a choice — transported along
the chosen K-injective resolution of `𝒪_X[0]`. The trace description then reduces to the
degreewise one, `…exactSupportHomComplexIso_comp_evaluation`, which is "evaluate a local
homomorphism at the section `1`" on both sides.

The target variable is the only one that moves, and the first map of the triangle of
[Stacks, Tag 08I0] *is* precomposition with the restriction map `𝒪_X ⟶ i_* 𝒪_D` placed in degree
zero, so it is literally the map the bifunctor supplies; no identification of the two is needed,
and `Stacks.Divisors.derivedDivisorQuotientMap` — the derived unit in `D(𝒪_X)` — is not used in
the proof, only recorded.

## References

* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 08I0](https://stacks.math.columbia.edu/tag/08I0)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite RingedSpaceModuleAdjunction

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace CategoryTheory.Pretriangulated

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] [Limits.HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Precomposition with the first map of a distinguished triangle is injective** as soon as
there is no nonzero morphism from the source into the third object shifted down by one.

Inverse rotation puts `T.obj₃⟦-1⟧ ⟶ T.obj₁ ⟶ T.obj₂` into a distinguished triangle, so a
morphism into `T.obj₁` killed by `T.mor₁` factors through `T.obj₃⟦-1⟧` by
`CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₂`; the hypothesis makes that factor
zero. -/
theorem eq_of_comp_mor₁_eq (T : Triangle C) (hT : T ∈ distTriang C) {W : C}
    (hW : Subsingleton (W ⟶ T.obj₃⟦(-1 : ℤ)⟧)) {a b : W ⟶ T.obj₁}
    (h : a ≫ T.mor₁ = b ≫ T.mor₁) : a = b := by
  have hf : (a - b) ≫ T.invRotate.mor₂ = 0 :=
    (Preadditive.sub_comp a b T.invRotate.mor₂).trans (sub_eq_zero.mpr h)
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ T.invRotate (inv_rot_of_distTriang T hT) (a - b) hf
  rw [← sub_eq_zero, hg, hW.allEq g 0]
  exact Limits.zero_comp

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- The negative of an isomorphism is an isomorphism. -/
theorem isIso_neg {A B : C} (f : A ⟶ B) [IsIso f] : IsIso (-f) :=
  ⟨⟨-(inv f), (Preadditive.neg_comp_neg f (inv f)).trans (IsIso.hom_inv_id (f := f)),
    (Preadditive.neg_comp_neg (inv f) f).trans (IsIso.inv_hom_id (f := f))⟩⟩

end CategoryTheory.Pretriangulated

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

/-! ### The derived unit -/

/-- **The derived unit `𝒪_X ⟶ Ri_* 𝒪_D` in `D(𝒪_X)`** of the closed immersion of an effective
Cartier divisor.

Pushforward of modules along a closed immersion is exact, so `Ri_* 𝒪_D` is `(i_* 𝒪_D)[0]`
(`Stacks.Divisors.pushforwardStructureSheafIso`); the derived unit is the underived restriction
map `𝒪_X ⟶ i_* 𝒪_D` of the ideal sequence (`Stacks.IdealSheafSequence.divisorQuotientMap`,
the second map of `Stacks.Divisors.idealShortComplex`) placed in degree zero and read through
that identification. Nothing is chosen, and
`Stacks.Divisors.derivedDivisorQuotientMap_comp` says exactly that. -/
def derivedDivisorQuotientMap :
    AlgebraicGeometry.RingedSite.derivedStructureSheaf
        (Stacks.SheafOfModules.ringedSite X.sheaf) ⟶
      (modulePushforward (closedQuotient D).i).mapDerivedCategory.obj
        (AlgebraicGeometry.RingedSite.derivedStructureSheaf
          (Stacks.SheafOfModules.ringedSite (closedQuotient D).Z.sheaf)) :=
  (DerivedCategory.singleFunctor X.Modules 0).map (idealShortComplex D).g ≫
    (pushforwardStructureSheafIso D).inv

/-! ### The triangle of Tag 08I0 at the ideal sequence -/

/-- The connecting morphism of the triangle which contravariant exactness of the derived
internal Hom ([Stacks, Tag 08I0]) attaches to the ideal sequence
`0 ⟶ ℐ_D ⟶ 𝒪_X ⟶ i_* 𝒪_D ⟶ 0`. [Stacks, Tag 08I0] quantifies it existentially — the objects
and the two induced maps are named — so it is chosen here once and for all, and nothing below
depends on which choice is made. -/
def idealDualδ :
    (derivedDual D).obj (op (idealShortComplex_shortExact D).singleTriangle.obj₁) ⟶
      ((derivedDual D).obj
        (op (idealShortComplex_shortExact D).singleTriangle.obj₃))⟦(1 : ℤ)⟧ :=
  (Stacks.SheafOfModules.exists_distinguished_derivedSheafHom_first X.sheaf
    ((DerivedCategory.singleFunctor X.Modules 0).obj ((normalShortComplex D).X₁))
    (idealShortComplex_shortExact D).singleTriangle
    (idealShortComplex_shortExact D).singleTriangle_distinguished).choose

/-- **The triangle of [Stacks, Tag 08I0] at the ideal sequence**, namely

`R ℰom(i_* 𝒪_D, 𝒪_X) ⟶ R ℰom(𝒪_X, 𝒪_X) ⟶ R ℰom(ℐ_D, 𝒪_X) ⟶ R ℰom(i_* 𝒪_D, 𝒪_X)⟦1⟧`,

its first map being precomposition with the restriction map `𝒪_X ⟶ i_* 𝒪_D` and its second
precomposition with the ideal inclusion `ℐ_D ⟶ 𝒪_X`. -/
def idealDualTriangle : Triangle (DerivedCategory X.Modules) :=
  Triangle.mk ((derivedDual D).map (idealShortComplex_shortExact D).singleTriangle.mor₂.op)
    ((derivedDual D).map (idealShortComplex_shortExact D).singleTriangle.mor₁.op)
    (idealDualδ D)

/-- The triangle of [Stacks, Tag 08I0] at the ideal sequence is distinguished. -/
theorem idealDualTriangle_distinguished :
    idealDualTriangle D ∈ distTriang (DerivedCategory X.Modules) :=
  (Stacks.SheafOfModules.exists_distinguished_derivedSheafHom_first X.sheaf
    ((DerivedCategory.singleFunctor X.Modules 0).obj ((normalShortComplex D).X₁))
    (idealShortComplex_shortExact D).singleTriangle
    (idealShortComplex_shortExact D).singleTriangle_distinguished).choose_spec

/-- **The comparison of the rotated triangle of [Stacks, Tag 08I0] with the normal short exact
sequence.** The two agree on their first two terms and their first map — the identifications
being `Stacks.Divisors.structureDualIso` and `Stacks.Divisors.idealDualIso`, and the agreement
`Stacks.Divisors.structureDualIso_comp` — so
`CategoryTheory.Pretriangulated.isoTriangleOfIso₁₂` compares the whole triangles.

This is the comparison `Stacks.Divisors.idealDerivedSheafHomIso` is built from, here with the
triangle and the comparison named rather than consumed inside a proof. -/
def idealDualTriangleIso :
    (idealDualTriangle D).rotate ≅ (normalShortComplex_shortExact D).singleTriangle :=
  isoTriangleOfIso₁₂ _ _ (rot_of_distTriang _ (idealDualTriangle_distinguished D))
    (normalShortComplex_shortExact D).singleTriangle_distinguished
    (structureDualIso D) (idealDualIso D) (structureDualIso_comp D)

/-! ### The vanishing that makes the comparison unique -/

/-- **An invertible sheaf has no sections supported on `D`, read in degree `n` of the derived
category.** This is `Stacks.Divisors.subsingleton_singleFunctor_hom_pushforward_of_isInvertible`
with the degree free; `DerivedCategory.singleFunctor` is fully faithful in every degree, so it
is again the underived statement `Stacks.Divisors.hom_pushforward_eq_zero_of_isInvertible`. -/
theorem subsingleton_singleFunctor_hom_pushforward_of_isInvertible_ofDegree (n : ℤ)
    (G : D.subscheme.Modules) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L] :
    Subsingleton ((DerivedCategory.singleFunctor X.Modules n).obj
        ((Scheme.Modules.pushforward D.subschemeι).obj G) ⟶
      (DerivedCategory.singleFunctor X.Modules n).obj L) := by
  refine ⟨fun f g => ?_⟩
  obtain ⟨f', rfl⟩ := (DerivedCategory.singleFunctor X.Modules n).map_surjective f
  obtain ⟨g', rfl⟩ := (DerivedCategory.singleFunctor X.Modules n).map_surjective g
  rw [hom_pushforward_eq_zero_of_isInvertible D f',
    hom_pushforward_eq_zero_of_isInvertible D g']

omit [IsEffectiveCartierDivisor D] in
/-- **The derived unit is the underived restriction map `𝒪_X ⟶ i_* 𝒪_D`.** Composed with the
identification `Ri_* 𝒪_D ≅ (i_* 𝒪_D)[0]` of `Stacks.Divisors.pushforwardStructureSheafIso` it is
the second map of the ideal sequence, placed in degree zero. -/
@[reassoc]
theorem derivedDivisorQuotientMap_comp :
    derivedDivisorQuotientMap D ≫ (pushforwardStructureSheafIso D).hom =
      (DerivedCategory.singleFunctor X.Modules 0).map (idealShortComplex D).g :=
  Eq.trans (Category.assoc _ _ _)
    (Eq.trans
      (congrArg
        (fun t => (DerivedCategory.singleFunctor X.Modules 0).map (idealShortComplex D).g ≫ t)
        (pushforwardStructureSheafIso D).inv_hom_id)
      (Category.comp_id _))

/-- **`Ri_*(𝒩[-1])` is `(i_* 𝒩)[-1]`**: derived pushforward along the closed immersion is
pushforward, which is exact, so it carries a single complex to a single complex. -/
def pushforwardNormalShiftSingleIso :
    (modulePushforward (closedQuotient D).i).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor D.subscheme.Modules 1).obj
          ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D))) ≅
      (DerivedCategory.singleFunctor X.Modules 1).obj (normalShortComplex D).X₃ :=
  ((modulePushforward (closedQuotient D).i).mapDerivedCategorySingleFunctor 1).app
    ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D))

/-- **`R ℰom_{𝒪_X}(ℐ_D, 𝒪_X)⟦-1⟧ ≅ 𝒪_X(D)[-1]`**: the third term of the triangle of
[Stacks, Tag 08I0], shifted down by one, is the invertible sheaf of the divisor placed in
degree one. -/
def idealDualTriangleObj₃ShiftIso :
    ((idealDualTriangle D).obj₃)⟦(-1 : ℤ)⟧ ≅
      (DerivedCategory.singleFunctor X.Modules 1).obj (normalShortComplex D).X₂ :=
  (shiftFunctor (DerivedCategory X.Modules) (-1 : ℤ)).mapIso (idealDualIso D) ≪≫
    ((DerivedCategory.singleFunctors X.Modules).shiftIso (-1) 1 0 (by ring)).app
      (normalShortComplex D).X₂

/-- **The vanishing that pins the comparison down.** There is no nonzero morphism from
`Ri_*(𝒩[-1])` into the third term of the triangle of [Stacks, Tag 08I0] shifted down by one:
the source is `(i_* 𝒩)[-1]` and the target is `𝒪_X(D)[-1]`, and an invertible sheaf has no
sections supported on `D`
(`Stacks.Divisors.subsingleton_singleFunctor_hom_pushforward_of_isInvertible_ofDegree`).

Through `CategoryTheory.Pretriangulated.eq_of_comp_mor₁_eq` this is what makes a morphism
`Ri_*(𝒩[-1]) ⟶ R ℰom_{𝒪_X}(i_* 𝒪_D, 𝒪_X)` determined by its composite with the first map of
that triangle. -/
theorem subsingleton_hom_idealDualTriangle_obj₃_shift :
    Subsingleton ((modulePushforward (closedQuotient D).i).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor D.subscheme.Modules 1).obj
          ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D))) ⟶
      ((idealDualTriangle D).obj₃)⟦(-1 : ℤ)⟧) :=
  @Equiv.subsingleton _ _
    ((pushforwardNormalShiftSingleIso D).homCongr (idealDualTriangleObj₃ShiftIso D))
    (subsingleton_singleFunctor_hom_pushforward_of_isInvertible_ofDegree D 1
      ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D)) (divisorSheaf D))

/-! ### The comparison supplied by the triangle -/

/-- `Ri_*(𝒩[-1]) ≅ ((i_* 𝒩)[0])⟦-1⟧`: the three identifications that
`Stacks.Divisors.pushforwardNormalShiftToStructureSheaf` is built from, assembled into one
isomorphism. -/
def pushforwardNormalShiftShiftIso :
    (modulePushforward (closedQuotient D).i).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor D.subscheme.Modules 1).obj
          ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D))) ≅
      ((DerivedCategory.singleFunctor X.Modules 0).obj (normalShortComplex D).X₃)⟦(-1 : ℤ)⟧ :=
  ((modulePushforward (closedQuotient D).i).mapDerivedCategory.mapIso
        (((DerivedCategory.singleFunctors D.subscheme.Modules).shiftIso (-1) 1 0 (by ring)).app
          ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D))).symm ≪≫
      ((modulePushforward (closedQuotient D).i).mapDerivedCategory.commShiftIso (-1 : ℤ)).app
        ((DerivedCategory.singleFunctor D.subscheme.Modules 0).obj
          ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D)))) ≪≫
    (shiftFunctor (DerivedCategory X.Modules) (-1 : ℤ)).mapIso
      (((modulePushforward (closedQuotient D).i).mapDerivedCategorySingleFunctor 0).app
        ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D)))

/-- The morphism `Ri_*(𝒩[-1]) ⟶ 𝒪_X` determined by the normal extension class is the
connecting morphism shifted down by one, read through
`Stacks.Divisors.pushforwardNormalShiftShiftIso`. This is its definition, regrouped; the
regrouping is pure associativity, written in term mode because the goal mixes the two spellings
of the category of `𝒪_X`-modules and `rewrite` refuses such a target. -/
theorem pushforwardNormalShiftToStructureSheaf_eq :
    pushforwardNormalShiftToStructureSheaf D =
      (pushforwardNormalShiftShiftIso D).hom ≫ (normalExtensionClass D)⟦(-1 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId (DerivedCategory X.Modules) (1 : ℤ) (-1) (by ring)).hom.app
          ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X)) :=
  ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).symm

/-- **The triangle of [Stacks, Tag 08I0] carries the normal extension class.** The first map of
that triangle, read through `R ℰom_{𝒪_X}(𝒪_X, 𝒪_X) ≅ 𝒪_X` and shifted down by one, is minus the
connecting morphism of the normal short exact sequence transported along the triangle
comparison.

This is the third commutative square of `Stacks.Divisors.idealDualTriangleIso`, whose third
map is minus the shift of the first map of the triangle, shifted down by one through the counit
of the shift. -/
theorem shiftFunctorCompIsoId_comp_idealDualTriangle_mor₁ :
    (shiftFunctorCompIsoId (DerivedCategory X.Modules) (1 : ℤ) (-1) (by ring)).hom.app
          ((idealDualTriangle D).obj₁) ≫
        (idealDualTriangle D).mor₁ ≫ (structureDualIso D).hom =
      -(((Triangle.π₃.mapIso (idealDualTriangleIso D)).hom)⟦(-1 : ℤ)⟧' ≫
        ((normalExtensionClass D)⟦(-1 : ℤ)⟧' ≫
          (shiftFunctorCompIsoId (DerivedCategory X.Modules) (1 : ℤ) (-1) (by ring)).hom.app
            ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X)))) :=
  have hsq : ((idealDualTriangle D).mor₁ ≫ (structureDualIso D).hom)⟦(1 : ℤ)⟧' =
      -((Triangle.π₃.mapIso (idealDualTriangleIso D)).hom ≫ normalExtensionClass D) :=
    ((shiftFunctor (DerivedCategory X.Modules) (1 : ℤ)).map_comp _ _).trans
      (neg_eq_iff_eq_neg.mp
        ((Preadditive.neg_comp _ _).symm.trans (idealDualTriangleIso D).hom.comm₃))
  ((shiftFunctorCompIsoId (DerivedCategory X.Modules) (1 : ℤ) (-1) (by ring)).hom.naturality
        ((idealDualTriangle D).mor₁ ≫ (structureDualIso D).hom)).symm.trans
    ((congrArg
        (fun z => z ≫ (shiftFunctorCompIsoId (DerivedCategory X.Modules) (1 : ℤ) (-1)
          (by ring)).hom.app
            ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X)))
        (((shiftFunctor (DerivedCategory X.Modules) (-1 : ℤ)).congr_map hsq).trans
          ((shiftFunctor (DerivedCategory X.Modules) (-1 : ℤ)).map_neg.trans
            (congrArg Neg.neg
              ((shiftFunctor (DerivedCategory X.Modules) (-1 : ℤ)).map_comp _ _))))).trans
      ((Preadditive.neg_comp _ _).trans (congrArg Neg.neg (Category.assoc _ _ _))))

/-- **Minus the trace that the triangle of [Stacks, Tag 08I0] supplies on its own**: the first
map of that triangle, read through `R ℰom_{𝒪_X}(𝒪_X, 𝒪_X) ≅ 𝒪_X`, negated.

The sign is carried here rather than on the morphism determined by the normal extension class
because both ends of this morphism are spelled in `X.Modules`, where the additive structure of
the Hom group is found by instance search; the source of that other morphism is a derived
pushforward, spelled over `structureSheafRing (closedQuotient D).X`, and negating there costs an
unfolding of the two spellings at every step. -/
def idealDualTriangleNegTrace :
    (idealDualTriangle D).obj₁ ⟶
      (DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X) :=
  -((idealDualTriangle D).mor₁ ≫ (structureDualIso D).hom)

/-- `Stacks.Divisors.shiftFunctorCompIsoId_comp_idealDualTriangle_mor₁` with the sign moved onto
the trace. -/
theorem shiftFunctorCompIsoId_comp_idealDualTriangleNegTrace :
    (shiftFunctorCompIsoId (DerivedCategory X.Modules) (1 : ℤ) (-1) (by ring)).hom.app
          ((idealDualTriangle D).obj₁) ≫ idealDualTriangleNegTrace D =
      ((Triangle.π₃.mapIso (idealDualTriangleIso D)).hom)⟦(-1 : ℤ)⟧' ≫
        ((normalExtensionClass D)⟦(-1 : ℤ)⟧' ≫
          (shiftFunctorCompIsoId (DerivedCategory X.Modules) (1 : ℤ) (-1) (by ring)).hom.app
            ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X))) :=
  (Preadditive.comp_neg _ _).trans
    (neg_eq_iff_eq_neg.mpr (shiftFunctorCompIsoId_comp_idealDualTriangle_mor₁ D))

/-- **The comparison isomorphism `Ri_*(𝒩[-1]) ≅ R ℰom_{𝒪_X}(i_* 𝒪_D, 𝒪_X)`** that the triangle
of [Stacks, Tag 08I0] supplies: `Ri_*(𝒩[-1])` is `(i_* 𝒩)[0]` shifted down by one, which the
triangle comparison identifies with the first term of that triangle shifted up and back down. -/
def pushforwardNormalShiftIsoIdealDual :
    (modulePushforward (closedQuotient D).i).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor D.subscheme.Modules 1).obj
          ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D))) ≅
      (idealDualTriangle D).obj₁ :=
  (pushforwardNormalShiftShiftIso D ≪≫
      ((shiftFunctor (DerivedCategory X.Modules) (-1 : ℤ)).mapIso
        (Triangle.π₃.mapIso (idealDualTriangleIso D))).symm) ≪≫
    (shiftFunctorCompIsoId (DerivedCategory X.Modules) (1 : ℤ) (-1) (by ring)).app
      ((idealDualTriangle D).obj₁)

/-- **The comparison isomorphism, read through minus the trace of the triangle of
[Stacks, Tag 08I0], is the morphism determined by the normal extension class.** -/
theorem pushforwardNormalShiftIsoIdealDual_comp :
    (pushforwardNormalShiftIsoIdealDual D).hom ≫ idealDualTriangleNegTrace D =
      pushforwardNormalShiftToStructureSheaf D :=
  (Category.assoc _ _ _).trans
    ((whisker_eq _ (shiftFunctorCompIsoId_comp_idealDualTriangleNegTrace D)).trans
      ((Category.assoc _ _ _).trans
        ((whisker_eq _ (Iso.inv_hom_id_assoc _ _)).trans
          (pushforwardNormalShiftToStructureSheaf_eq D).symm)))

/-- The comparison isomorphism of `Stacks.Divisors.pushforwardNormalShiftIsoIdealDual`
composed with minus the identity, so that its composite with the trace of the triangle of
[Stacks, Tag 08I0] — rather than with minus that trace — is the morphism determined by the
normal extension class. -/
def pushforwardNormalShiftIsoIdealDualNeg :
    (modulePushforward (closedQuotient D).i).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor D.subscheme.Modules 1).obj
          ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D))) ≅
      (idealDualTriangle D).obj₁ :=
  pushforwardNormalShiftIsoIdealDual D ≪≫
    @asIso _ _ _ _ _ (Pretriangulated.isIso_neg (𝟙 ((idealDualTriangle D).obj₁)))

/-- Minus the identity of the first term of the triangle of [Stacks, Tag 08I0], followed by the
trace of that triangle, is minus that trace.

It is stated separately because both ends of it are spelled in `X.Modules`, where the additive
structure of the Hom group is found by instance search; inside
`Stacks.Divisors.pushforwardNormalShiftIsoIdealDualNeg_comp` the composite is read in the
category of modules over the ringed space `X`, the spelling in which a derived pushforward is
stated, and the negation is then not found. -/
theorem negIdComp_idealDualTriangle_mor₁ :
    (-(𝟙 ((idealDualTriangle D).obj₁))) ≫
        ((idealDualTriangle D).mor₁ ≫ (structureDualIso D).hom) =
      idealDualTriangleNegTrace D :=
  (Preadditive.neg_comp _ _).trans (congrArg Neg.neg (Category.id_comp _))

/-- **The negated comparison isomorphism, read through the trace of the triangle of
[Stacks, Tag 08I0], is the morphism determined by the normal extension class.** -/
theorem pushforwardNormalShiftIsoIdealDualNeg_comp :
    (pushforwardNormalShiftIsoIdealDualNeg D).hom ≫
        ((idealDualTriangle D).mor₁ ≫ (structureDualIso D).hom) =
      pushforwardNormalShiftToStructureSheaf D :=
  (Category.assoc _ _ _).trans
    ((whisker_eq _ (negIdComp_idealDualTriangle_mor₁ D)).trans
      (pushforwardNormalShiftIsoIdealDual_comp D))

/-- **Precomposition with the derived unit is the first map of the triangle of
[Stacks, Tag 08I0]**, once `Ri_* 𝒪_D` is identified with `(i_* 𝒪_D)[0]`. This is where the
derived unit of `Stacks.Divisors.derivedDivisorQuotientMap` meets that triangle. -/
theorem idealDualTriangleObj₁Iso_inv_comp_mor₁ :
    ((derivedDual D).mapIso (pushforwardStructureSheafIso D).op).inv ≫
        (idealDualTriangle D).mor₁ =
      (derivedDual D).map (derivedDivisorQuotientMap D).op :=
  ((derivedDual D).map_comp _ _).symm

/-! ### The bifunctor model of Tag 0A77 carrying the trace -/

/-- **`Ri_* R ℰom(𝒪_D, 𝒪_X) ≅ R ℰom_{𝒪_X}(i_* 𝒪_D, 𝒪_X)`**, the first term of the triangle of
[Stacks, Tag 08I0].

It is the bifunctor model of [Stacks, Tag 0A77] at the structure sheaf,
`…ClosedQuotientMorphismOfRingedSpaces.structureBifunctorModelIso`: the identification at the
class of a K-injective complex, transported along the chosen K-injective resolution of `𝒪_X[0]`.
Unlike the library's isomorphism of [Stacks, Tag 0A77] it carries the trace of [Stacks, Tag 0A76]
in the form the triangle of [Stacks, Tag 08I0] needs, which is
`Stacks.Divisors.pushforwardDerivedSheafHomIdealDualIso_trace`. -/
def pushforwardDerivedSheafHomIdealDualIso :
    (modulePushforward (closedQuotient D).i).mapDerivedCategory.obj
        ((closedQuotient D).derivedSheafHomExactSupport.obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X))) ≅
      (idealDualTriangle D).obj₁ :=
  (closedQuotient D).structureBifunctorModelIso

/-- **The trace description of `Stacks.Divisors.pushforwardDerivedSheafHomIdealDualIso`**: it is
the identification through which the counit of [Stacks, Tag 0A76] at `𝒪_X` — the trace of
[Stacks, Tag 0A77] — becomes the first map of the triangle of [Stacks, Tag 08I0] followed by the
identification `R ℰom_{𝒪_X}(𝒪_X, 𝒪_X) ≅ 𝒪_X` of `Stacks.Divisors.structureDualIso`.

This is the statement that used to be carried as a hypothesis of
`Stacks.Divisors.isIso_normalShiftToDerivedSheafHomExactSupport`.  It is
`…ClosedQuotientMorphismOfRingedSpaces.structureBifunctorModelIso_trace` at the restriction map
`𝒪_X ⟶ i_* 𝒪_D` of the ideal sequence, which carries the unit section to the unit section by
`Stacks.Divisors.divisorQuotientSingle_one`, and at
`Stacks.Divisors.structureDualIso`, which the comparison to the derived internal Hom turns into
evaluation at the unit section by
`Stacks.Divisors.strictlyPerfectHomComparison_comp_structureDualIso`.  The first map of the
triangle of [Stacks, Tag 08I0] *is* precomposition with the restriction map placed in degree
zero, so no further identification is needed. -/
theorem pushforwardDerivedSheafHomIdealDualIso_trace :
    (pushforwardDerivedSheafHomIdealDualIso D).hom ≫
        (idealDualTriangle D).mor₁ ≫ (structureDualIso D).hom =
      (closedQuotient D).derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app
        ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X)) :=
  have hepi : Epi (AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison (siteOf X)
      (Stacks.SheafOfModules.derivedInternalHom X.sheaf) (structureComplexOf X)
      (structureComplexOf X)) := inferInstance
  (closedQuotient D).structureBifunctorModelIso_trace (divisorQuotientSingle D)
    (divisorQuotientSingle_one D) (structureDualIso D).hom hepi
    (strictlyPerfectHomComparison_comp_structureDualIso D)

/-- The pushforward of the canonical comparison morphism of [Stacks, Tag 0B4B], carried into the
first term of the triangle of [Stacks, Tag 08I0] by the bifunctor model of [Stacks, Tag 0A77]
and the identification `Ri_* 𝒪_D ≅ (i_* 𝒪_D)[0]`. -/
def pushforwardNormalShiftToIdealDual :
    (modulePushforward (closedQuotient D).i).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor D.subscheme.Modules 1).obj
          ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D))) ⟶
      (idealDualTriangle D).obj₁ :=
  (modulePushforward (closedQuotient D).i).mapDerivedCategory.map
      (normalShiftToDerivedSheafHomExactSupport D) ≫
    (pushforwardDerivedSheafHomIdealDualIso D).hom

/-- **The pushforward of the canonical comparison morphism of [Stacks, Tag 0B4B] is an
isomorphism** as soon as it agrees, in the first term of the triangle of [Stacks, Tag 08I0],
with the comparison isomorphism that triangle supplies: it is then that isomorphism followed by
the inverse of `Stacks.Divisors.pushforwardDerivedSheafHomIdealDualIso`. -/
theorem isIso_mapDerivedCategory_map_normalShift
    (heq : pushforwardNormalShiftToIdealDual D =
      (pushforwardNormalShiftIsoIdealDualNeg D).hom) :
    IsIso ((modulePushforward (closedQuotient D).i).mapDerivedCategory.map
      (normalShiftToDerivedSheafHomExactSupport D)) :=
  let v := pushforwardNormalShiftIsoIdealDualNeg D ≪≫
    (pushforwardDerivedSheafHomIdealDualIso D).symm
  have h : (modulePushforward (closedQuotient D).i).mapDerivedCategory.map
      (normalShiftToDerivedSheafHomExactSupport D) = v.hom :=
    ((pushforwardDerivedSheafHomIdealDualIso D).eq_comp_inv).mpr heq
  ⟨v.inv, (congrArg (fun t => t ≫ v.inv) h).trans v.hom_inv_id,
    (congrArg (fun t => v.inv ≫ t) h).trans v.inv_hom_id⟩

/-- **[Stacks, Tag 0B4B]: the canonical comparison morphism `𝒩[-1] ⟶ R ℰom(𝒪_D, 𝒪_X)` is an
isomorphism.**

The argument is the source's. Push the comparison morphism forward and carry it into the first
term of the triangle of [Stacks, Tag 08I0]; its composite with the trace of that triangle is the
morphism `Ri_*(𝒩[-1]) ⟶ 𝒪_X` determined by the normal extension class, by
`Stacks.Divisors.pushforward_normalShiftToDerivedSheafHomExactSupport_comp` and the trace
description `Stacks.Divisors.pushforwardDerivedSheafHomIdealDualIso_trace`. The isomorphism
`Stacks.Divisors.pushforwardNormalShiftIsoIdealDualNeg`, which the triangle supplies from its
comparison with the normal short exact sequence, has the same composite. Precomposition with the
first map of that triangle is injective on morphisms out of `Ri_*(𝒩[-1])`, by
`Stacks.Divisors.subsingleton_hom_idealDualTriangle_obj₃_shift` through
`CategoryTheory.Pretriangulated.eq_of_comp_mor₁_eq`, so the two morphisms agree and the
pushforward of the comparison morphism is an isomorphism. Derived pushforward along a closed
immersion reflects isomorphisms, so the comparison morphism itself is one. -/
theorem isIso_normalShiftToDerivedSheafHomExactSupport :
    IsIso (normalShiftToDerivedSheafHomExactSupport D) := by
  have hcounit := (closedQuotient D)
    |>.derivedSheafHomExactSupportPushforwardNatIso_hom_app_comp_bifunctorEvaluationAtOne
      ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X))
  have hadj : (modulePushforward (closedQuotient D).i).mapDerivedCategory.map
          (normalShiftToDerivedSheafHomExactSupport D) ≫
        (closedQuotient D).derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app
          ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X)) =
      pushforwardNormalShiftToStructureSheaf D :=
    (whisker_eq _ hcounit.symm).trans
      (pushforward_normalShiftToDerivedSheafHomExactSupport_comp D)
  have hα : pushforwardNormalShiftToIdealDual D ≫
        ((idealDualTriangle D).mor₁ ≫ (structureDualIso D).hom) =
      pushforwardNormalShiftToStructureSheaf D :=
    (Category.assoc _ _ _).trans
      ((whisker_eq _ (pushforwardDerivedSheafHomIdealDualIso_trace D)).trans hadj)
  have heq : pushforwardNormalShiftToIdealDual D =
      (pushforwardNormalShiftIsoIdealDualNeg D).hom :=
    Pretriangulated.eq_of_comp_mor₁_eq (idealDualTriangle D)
      (idealDualTriangle_distinguished D) (subsingleton_hom_idealDualTriangle_obj₃_shift D)
      ((cancel_mono (structureDualIso D).hom).mp
        ((Category.assoc _ _ _).trans
          (hα.trans ((pushforwardNormalShiftIsoIdealDualNeg_comp D).symm.trans
            (Category.assoc _ _ _).symm))))
  have := isIso_mapDerivedCategory_map_normalShift D heq
  exact Functor.ReflectsIsomorphisms.reflects
    (modulePushforward (closedQuotient D).i).mapDerivedCategory
    (normalShiftToDerivedSheafHomExactSupport D)

end Stacks.Divisors

end
