module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraSliceRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionCohomologyProduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionSliceRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexHomologySliceRestriction

/-!
# The graded algebra of a complex restricts to the graded algebra of its restriction

Let `X` be a ringed site, `U` an object of its underlying category and `P` a complex of
`O`-modules. The cohomology sheaves of `SheafHom^•(P, P)` carry the composition product, and so
form a sheaf of graded `O`-algebras
(`AlgebraicGeometry.RingedSite.homologyGradedAlgebra`). This file proves that the comparison

`Hⁿ(SheafHom(P, P))|_U ≅ Hⁿ(SheafHom(P|_U, P|_U))`

of `AlgebraicGeometry.RingedSite.sheafHomHomologyOverIso` is a **homomorphism of sheaves of
graded algebras** from the restriction of the graded algebra of `P` to the graded algebra of the
restriction of `P`, and that it is an isomorphism in every degree.

## Main definitions

* `AlgebraicGeometry.RingedSite.homologyGradedAlgebraOverHom`: **the comparison as a unital
  homomorphism of sheaves of graded algebras**
  `(homologyGradedAlgebra X P).over U ⟶ homologyGradedAlgebra (X.over U) (P|_U)`.

## Main results

* `AlgebraicGeometry.RingedSite.idSection_sheafHomRestrictionComplexIso`: restriction to a slice
  site carries the identity section to the identity section.
* `AlgebraicGeometry.RingedSite.homologyMul_sheafHomHomologyOverIso_of_cycles`: **the comparison
  is multiplicative on classes of cocycles**, which is where the mathematics is.
* `AlgebraicGeometry.RingedSite.homologyMul_sheafHomHomologyOverIso`: the same for arbitrary
  local sections, by lifting them to cocycles on a common refinement.
* `AlgebraicGeometry.RingedSite.isIso_homologyGradedAlgebraOverHom_app`: every degree of the
  comparison is an isomorphism — it is `sheafHomHomologyOverIso` by construction.

## Implementation notes

**Why the proof runs on local sections and not on morphisms.** The multiplication of
`AlgebraicGeometry.RingedSite.homologyGradedAlgebra` is `homologyMul`, a bilinear map on local
sections rather than a morphism out of a tensor product, and this is the shape the
`SheafOfModules.GradedAlgebra.UnitalHom` structure asks for. Read that way the statement needs no
comparison of the *tensor* products involved: each side is computed by
`AlgebraicGeometry.RingedSite.homologyMul_app_homologyπ` followed by
`AlgebraicGeometry.RingedSite.iCycles_cycleComposition_pureSection`, which reduce it to
`AlgebraicGeometry.RingedSite.compositionSection` on the two sites separately, and there the
identity is `AlgebraicGeometry.RingedSite.compositionSection_sheafHomRestrictionComplexIso`. The
alternative — comparing `AlgebraicGeometry.RingedSite.homologyComposition` on the two sites —
would additionally need the slice compatibility of
`AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex`, because
`AlgebraicGeometry.RingedSite.homologyMap_compositionMap_over` is a statement about
`compositionMap` on `tensorTotal` and not about `compositionTotalMap`.

**What makes the reduction to cocycles legitimate.** The value of the comparison on the class of
a cocycle is `AlgebraicGeometry.RingedSite.sheafHomHomologyOverIso_hom_app_homologyπ`, and an
arbitrary pair of local sections of the two cohomology sheaves is lifted to a pair of cocycles on
a common refinement by `AlgebraicGeometry.RingedSite.eq_of_forall_lift₃` applied over the
*slice* site: restriction preserves epimorphisms, so the restriction of the projection from
cycles is still an epimorphism and hence locally surjective there.

## References

* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local implicit_reducible]
  HomologicalComplex.homologyFunctor
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

/-- Two cycles of the restricted complex with the same image in `SheafHom(P|_U, P|_U)` have the
same class. -/
private theorem homologyπ_app_eq_of_iCycles_app_eq (X : RingedSite.{u, u, u}) (U : X.C)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) (V : Over U)
    (a b : ((endComplex (X.over U) (restrictComplex X P U)).cycles n).val.obj (op V))
    (h : ((endComplex (X.over U) (restrictComplex X P U)).iCycles n).val.app (op V) a =
      ((endComplex (X.over U) (restrictComplex X P U)).iCycles n).val.app (op V) b) :
    ((endComplex (X.over U) (restrictComplex X P U)).homologyπ n).val.app (op V) a =
      ((endComplex (X.over U) (restrictComplex X P U)).homologyπ n).val.app (op V) b :=
  congrArg _ (_root_.Stacks.SheafOfModules.injective_app_of_mono _ (op V) h)

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

-- Restriction to a slice site is additive by the global instance
-- `AlgebraicGeometry.RingedSite.overFunctor_additive`
-- (StacksFrontier/CategoryTheory/Sites/Cohomology/Slice/RestrictionOfComplexes.lean:47); left and
-- right exactness are the named theorems of Stacks 04IX, made local instances here.
attribute [local instance] Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Restriction to a slice site carries the identity section to the identity section.** The
identity section of `SheafHom(P, P)` is characterised by its values
(`AlgebraicGeometry.RingedSite.applyHomSectionOver_idSection`), and a map of internal Hom
complexes with the property `AlgebraicGeometry.RingedSite.IsInternalHomRestrictionMap` does not
change the value of a section; so the two sides have the same values. -/
theorem idSection_sheafHomRestrictionComplexIso
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (V : Over U) :
    ((sheafHomRestrictionComplexIso X U P P).hom.f 0).val.app (op V)
        (idSection X P V.left) =
      idSection (X.over U) (restrictComplex X P U) V := by
  refine homSection_ext (X.over U)
    (sheafHomComplex (X.over U) (restrictComplex X P U) (restrictComplex X P U))
    V 0 fun r t hrt W i x ↦ ?_
  obtain rfl : t = r := by omega
  refine (applyHomSectionOver_isInternalHomRestrictionMap X U
    (sheafHomRestrictionComplexIso_isRestriction X U P P) V W i 0 t t hrt
    (idSection X P V.left) x).trans ?_
  exact (applyHomSectionOver_idSection X P V.left W.left i.left t x).trans
    (applyHomSectionOver_idSection (X.over U) (restrictComplex X P U) V W i t x).symm

variable (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- Restriction of sheaves of modules to a slice site preserves epimorphisms: it is right
exact, and a right exact functor carries a pushout square to a pushout square. -/
local instance overFunctorPreservesEpimorphisms''' :
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).PreservesEpimorphisms :=
  preservesEpimorphisms_of_preservesColimitsOfShape _

/-- The restriction of the projection from cycles onto a cohomology sheaf is an epimorphism. -/
local instance epi_overFunctor_map_homologyπ''' (n : ℤ) :
    Epi ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map
      ((endComplex X P).homologyπ n)) :=
  Functor.map_epi _ _

/-- **The restricted projection from cycles onto a cohomology sheaf is locally surjective on
the slice site.** It is an epimorphism, restriction preserving them, and an epimorphism of
sheaves of modules is locally surjective. -/
theorem isLocallySurjective_overFunctor_map_homologyπ (n : ℤ) :
    PresheafOfModules.IsLocallySurjective (X.J.over U)
      ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map
        ((endComplex X P).homologyπ n)).val :=
  _root_.Stacks.SheafOfModules.ImageSubsheaf.isLocallySurjective_of_epi _

/-- **The comparison is multiplicative on classes of cocycles.** This is the whole mathematical
content: both sides are the class of a cocycle computed by
`AlgebraicGeometry.RingedSite.homologyMul_app_homologyπ`, the two cocycles are compared inside
the complex by `Stacks.SheafOfModules.injective_app_of_mono` applied to the inclusion of cycles,
and there each is a `AlgebraicGeometry.RingedSite.compositionSection`, where the identity is
`AlgebraicGeometry.RingedSite.compositionSection_sheafHomRestrictionComplexIso`. -/
theorem homologyMul_sheafHomHomologyOverIso_of_cycles (i j : ℤ) (V : Over U)
    (a : ((endComplex X P).cycles i).val.obj (op V.left))
    (b : ((endComplex X P).cycles j).val.obj (op V.left)) :
    ((sheafHomHomologyOverIso X U P P (i + j)).hom.val.app (op V))
        ((homologyMul X P P P i j).app (op V.left)
          (((endComplex X P).homologyπ i).val.app (op V.left) a)
          (((endComplex X P).homologyπ j).val.app (op V.left) b)) =
      (homologyMul (X.over U) (restrictComplex X P U) (restrictComplex X P U)
            (restrictComplex X P U) i j).app (op V)
        ((sheafHomHomologyOverIso X U P P i).hom.val.app (op V)
          (((endComplex X P).homologyπ i).val.app (op V.left) a))
        ((sheafHomHomologyOverIso X U P P j).hom.val.app (op V)
          (((endComplex X P).homologyπ j).val.app (op V.left) b)) := by
  rw [homologyMul_app_homologyπ, sheafHomHomologyOverIso_hom_app_homologyπ,
    sheafHomHomologyOverIso_hom_app_homologyπ, sheafHomHomologyOverIso_hom_app_homologyπ]
  refine Eq.trans ?_ (homologyMul_app_homologyπ (X.over U) (restrictComplex X P U)
    (restrictComplex X P U) (restrictComplex X P U) i j V _ _).symm
  refine homologyπ_app_eq_of_iCycles_app_eq X U P _ _ _ _ ?_
  rw [sheafHomCyclesOverMap_iCycles_app, iCycles_cycleComposition_pureSection]
  refine (compositionSection_sheafHomRestrictionComplexIso X U P P P V i j (i + j) rfl _ _).trans ?_
  refine Eq.trans ?_ (iCycles_cycleComposition_pureSection (X.over U) (restrictComplex X P U)
    (restrictComplex X P U) (restrictComplex X P U) i j V _ _).symm
  rw [sheafHomCyclesOverMap_iCycles_app, sheafHomCyclesOverMap_iCycles_app]

/-- **The comparison carries the unit to the unit**: the class of the identity goes to the class
of the identity. -/
theorem homologyOne_sheafHomHomologyOverIso (V : Over U) :
    ((sheafHomHomologyOverIso X U P P 0).hom.val.app (op V))
        ((homologyOne X P).val (op V.left)) =
      (homologyOne (X.over U) (restrictComplex X P U)).val (op V) := by
  rw [homologyOne_eval, sheafHomHomologyOverIso_hom_app_homologyπ]
  refine Eq.trans ?_ (homologyOne_eval (X.over U) (restrictComplex X P U) (op V)).symm
  refine homologyπ_app_eq_of_iCycles_app_eq X U P _ _ _ _ ?_
  refine Eq.trans ?_ (iCycles_oneCycle (X.over U) (restrictComplex X P U) (op V)).symm
  rw [sheafHomCyclesOverMap_iCycles_app, iCycles_oneCycle]
  exact idSection_sheafHomRestrictionComplexIso X U P V

/-- **The comparison is multiplicative.** The two cohomology sections are lifted to cocycles
simultaneously on a common refinement of the slice site -- the restriction of `homologyπ` is an
epimorphism, hence locally surjective, and `AlgebraicGeometry.RingedSite.eq_of_forall_lift₃`
intersects the resulting covering sieves -- and on those lifts the identity is
`homologyMul_sheafHomHomologyOverIso_of_cycles`. -/
theorem homologyMul_sheafHomHomologyOverIso (i j : ℤ) (V : (Over U)ᵒᵖ)
    (x : ((endComplex X P).homology i).val.obj (op V.unop.left))
    (y : ((endComplex X P).homology j).val.obj (op V.unop.left)) :
    ((sheafHomHomologyOverIso X U P P (i + j)).hom.val.app V)
        ((homologyMul X P P P i j).app (op V.unop.left) x y) =
      (homologyMul (X.over U) (restrictComplex X P U) (restrictComplex X P U)
            (restrictComplex X P U) i j).app V
        ((sheafHomHomologyOverIso X U P P i).hom.val.app V x)
        ((sheafHomHomologyOverIso X U P P j).hom.val.app V y) := by
  refine @eq_of_forall_lift₃ (X.over U) _ _ _ _ _ _ _
    (((endComplex (X.over U) (restrictComplex X P U)).homology (i + j)).isSheaf.isSeparated)
    ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map
      ((endComplex X P).homologyπ i)).val
    ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map
      ((endComplex X P).homologyπ j)).val
    ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map
      ((endComplex X P).homologyπ j)).val
    (isLocallySurjective_overFunctor_map_homologyπ X U P i)
    (isLocallySurjective_overFunctor_map_homologyπ X U P j)
    (isLocallySurjective_overFunctor_map_homologyπ X U P j) _ x y y _ _ ?_
  intro W f m₁ m₂ _ hm₁ hm₂ _
  refine (PresheafOfModules.naturality_apply
    (sheafHomHomologyOverIso X U P P (i + j)).hom.val f _).symm.trans ?_
  refine Eq.trans ?_ (_root_.Stacks.BilinearMap.naturality
    (homologyMul (X.over U) (restrictComplex X P U) (restrictComplex X P U)
      (restrictComplex X P U) i j) f _ _).symm
  refine Eq.trans ?_ (congrArg₂ (fun u v =>
    (homologyMul (X.over U) (restrictComplex X P U) (restrictComplex X P U)
      (restrictComplex X P U) i j).app W u v)
    ((congrArg (fun z => (sheafHomHomologyOverIso X U P P i).hom.val.app W z) hm₁).trans
      (PresheafOfModules.naturality_apply (sheafHomHomologyOverIso X U P P i).hom.val f x))
    ((congrArg (fun z => (sheafHomHomologyOverIso X U P P j).hom.val.app W z) hm₂).trans
      (PresheafOfModules.naturality_apply (sheafHomHomologyOverIso X U P P j).hom.val f y)))
  refine Eq.trans (congrArg
    (fun z => (sheafHomHomologyOverIso X U P P (i + j)).hom.val.app W z) ?_)
    (homologyMul_sheafHomHomologyOverIso_of_cycles X U P i j W.unop m₁ m₂)
  refine (_root_.Stacks.BilinearMap.naturality (homologyMul X P P P i j)
    f.unop.left.op x y).trans ?_
  exact congrArg₂ (fun u v => (homologyMul X P P P i j).app (op W.unop.left) u v)
    hm₁.symm hm₂.symm

/-- **The comparison, as a unital homomorphism of sheaves of graded algebras.** The restriction
of the graded algebra of the cohomology sheaves of `SheafHom^•(P, P)` to the site over `U` maps
to the graded algebra of the cohomology sheaves of `SheafHom^•(P|_U, P|_U)`, degreewise by
`AlgebraicGeometry.RingedSite.sheafHomHomologyOverIso`. -/
def homologyGradedAlgebraOverHom :
    SheafOfModules.GradedAlgebra.UnitalHom
      ((homologyGradedAlgebra X P).over U)
      (homologyGradedAlgebra (X.over U) (restrictComplex X P U)) where
  app n := (sheafHomHomologyOverIso X U P P n).hom
  map_mul i j V x y := homologyMul_sheafHomHomologyOverIso X U P i j V x y
  map_one V := homologyOne_sheafHomHomologyOverIso X U P V.unop

/-- The degree-`n` component of the comparison is `sheafHomHomologyOverIso`. -/
theorem homologyGradedAlgebraOverHom_app (n : ℤ) :
    (homologyGradedAlgebraOverHom X U P).app n = (sheafHomHomologyOverIso X U P P n).hom := rfl

/-- **Every degree of the comparison is an isomorphism.** -/
instance isIso_homologyGradedAlgebraOverHom_app (n : ℤ) :
    IsIso ((homologyGradedAlgebraOverHom X U P).app n) :=
  (sheafHomHomologyOverIso X U P P n).isIso_hom

end AlgebraicGeometry.RingedSite

end
