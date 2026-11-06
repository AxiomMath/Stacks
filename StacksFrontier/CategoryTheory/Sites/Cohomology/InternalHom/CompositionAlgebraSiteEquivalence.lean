module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedSitePushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionCohomologyProduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionSiteEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexHomologySiteEquivalence

/-!
# The graded algebra of a complex is invariant under an equivalence of ringed sites

Let `(C, O_C)` and `(D, O_D)` be ringed sites, let `e : C ≌ D`, `φ`, `ψ` be an equivalence of
ringed sites, and let `P` be a complex of `O_D`-modules. The cohomology sheaves of
`SheafHom^•(P, P)` carry the composition product, and so form a sheaf of graded `O_D`-algebras
(`AlgebraicGeometry.RingedSite.homologyGradedAlgebra`). This file proves that the comparison

`φ_* Hⁿ(SheafHom(P, P)) ≅ Hⁿ(SheafHom(φ_* P, φ_* P))`

of `AlgebraicGeometry.RingedSite.sheafHomHomologySiteEquivIso` is a **homomorphism of sheaves of
graded algebras** from the transport of the graded algebra of `P` to the graded algebra of the
transport of `P`, and that it is an isomorphism in every degree.

This is the statement of
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/CompositionAlgebraSliceRestriction.lean`
with an arbitrary equivalence of ringed sites in place of restriction to a slice site. The
transport of the graded algebra is `SheafOfModules.GradedAlgebra.pushforward`, which has
`SheafOfModules.GradedAlgebra.over` for its case `Over.forget U` with the identity structure
map.

## Main definitions

* `AlgebraicGeometry.RingedSite.homologyGradedAlgebraSiteEquivHom`: **the comparison as a unital
  homomorphism of sheaves of graded algebras**
  `φ_*(homologyGradedAlgebra X P) ⟶ homologyGradedAlgebra Y (φ_* P)`.

## Main results

* `AlgebraicGeometry.RingedSite.homologyMul_sheafHomHomologySiteEquivIso_of_cycles`: **the
  comparison is multiplicative on classes of cocycles**, which is where the mathematics is.
* `AlgebraicGeometry.RingedSite.homologyMul_sheafHomHomologySiteEquivIso`: the same for
  arbitrary local sections, by lifting them to cocycles on a common refinement.
* `AlgebraicGeometry.RingedSite.homologyOne_sheafHomHomologySiteEquivIso`: the comparison
  carries the unit to the unit.
* `AlgebraicGeometry.RingedSite.isIso_homologyGradedAlgebraSiteEquivHom_app`: every degree of
  the comparison is an isomorphism — it is `sheafHomHomologySiteEquivIso` by construction.

## Implementation notes

The proof runs on local sections and not on morphisms, for the reason recorded in the
implementation notes of `CompositionAlgebraSliceRestriction`: the multiplication of
`AlgebraicGeometry.RingedSite.homologyGradedAlgebra` is `homologyMul`, a bilinear map on local
sections rather than a morphism out of a tensor product, and that is the shape the
`SheafOfModules.GradedAlgebra.UnitalHom` structure asks for. Read that way the statement needs
no comparison of the *tensor* products involved: each side is computed by
`AlgebraicGeometry.RingedSite.homologyMul_app_homologyπ` followed by
`AlgebraicGeometry.RingedSite.iCycles_cycleComposition_pureSection`, which reduce it to
`AlgebraicGeometry.RingedSite.compositionSection` on the two sites separately, and there the
identity is `AlgebraicGeometry.RingedSite.compositionSection_siteEquivSheafHomComplexIso`.

An arbitrary pair of local sections of the two cohomology sheaves is lifted to a pair of
cocycles on a common refinement by `AlgebraicGeometry.RingedSite.eq_of_forall_lift₃` applied
over `C`: the transport is exact, so the transport of the projection from cycles is still an
epimorphism and hence locally surjective there.

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

variable {X Y : RingedSite.{u, u, u}} (eqv : Y.C ≌ X.C)
  [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{u} Y.J X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
    (eqv.inverse.sheafPushforwardContinuous RingCat.{u} X.J Y.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
    ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op eqv.unit) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)

variable [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [hlim : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ)]
  [hcolim : PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ)]
  (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- The transport of sheaves of modules along an equivalence of ringed sites preserves
epimorphisms: it is right exact, and a right exact functor carries a pushout square to a
pushout square. -/
local instance pushforwardPreservesEpimorphisms'' :
    (SheafOfModules.pushforward.{u} φ).PreservesEpimorphisms :=
  preservesEpimorphisms_of_preservesColimitsOfShape _

/-- The transport of the projection from cycles onto a cohomology sheaf is an epimorphism. -/
local instance epi_pushforward_map_homologyπ'' (n : ℤ) :
    Epi ((SheafOfModules.pushforward.{u} φ).map ((endComplex X P).homologyπ n)) :=
  Functor.map_epi _ _

omit [eqv.inverse.IsContinuous X.J Y.J] hlim in
/-- **The transported projection from cycles onto a cohomology sheaf is locally surjective.** It
is an epimorphism, the transport preserving them, and an epimorphism of sheaves of modules is
locally surjective. -/
theorem isLocallySurjective_pushforward_map_homologyπ (n : ℤ) :
    PresheafOfModules.IsLocallySurjective Y.J
      ((SheafOfModules.pushforward.{u} φ).map ((endComplex X P).homologyπ n)).val :=
  _root_.Stacks.SheafOfModules.ImageSubsheaf.isLocallySurjective_of_epi _

/-- Two cycles of `SheafHom^•(Q, Q)` with the same image in the complex have the same class. -/
private theorem homologyπ_app_eq_of_iCycles_app_eq
    (Q : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (n : ℤ) (V : Y.C) {a b : ((endComplex Y Q).cycles n).val.obj (op V)}
    (h : ((endComplex Y Q).iCycles n).val.app (op V) a =
      ((endComplex Y Q).iCycles n).val.app (op V) b) :
    ((endComplex Y Q).homologyπ n).val.app (op V) a =
      ((endComplex Y Q).homologyπ n).val.app (op V) b :=
  congrArg _ (_root_.Stacks.SheafOfModules.injective_app_of_mono
    ((endComplex Y Q).iCycles n) (op V) h)

/-- **The comparison is multiplicative on classes of cocycles.** This is the whole mathematical
content: both sides are the class of a cocycle computed by
`AlgebraicGeometry.RingedSite.homologyMul_app_homologyπ`, the two cocycles are compared inside
the complex by `Stacks.SheafOfModules.injective_app_of_mono` applied to the inclusion of cycles,
and there each is a `AlgebraicGeometry.RingedSite.compositionSection`, where the identity is
`AlgebraicGeometry.RingedSite.compositionSection_siteEquivSheafHomComplexIso`. -/
theorem homologyMul_sheafHomHomologySiteEquivIso_of_cycles (i j : ℤ) (V : Y.C)
    (a : ((endComplex X P).cycles i).val.obj (op (eqv.functor.obj V)))
    (b : ((endComplex X P).cycles j).val.obj (op (eqv.functor.obj V))) :
    ((sheafHomHomologySiteEquivIso eqv φ ψ H₁ H₂ P P (i + j)).hom.val.app (op V))
        ((homologyMul X P P P i j).app (op (eqv.functor.obj V))
          (((endComplex X P).homologyπ i).val.app (op (eqv.functor.obj V)) a)
          (((endComplex X P).homologyπ j).val.app (op (eqv.functor.obj V)) b)) =
      (homologyMul Y ((pushComplex eqv φ).obj P) ((pushComplex eqv φ).obj P)
            ((pushComplex eqv φ).obj P) i j).app (op V)
        ((sheafHomHomologySiteEquivIso eqv φ ψ H₁ H₂ P P i).hom.val.app (op V)
          (((endComplex X P).homologyπ i).val.app (op (eqv.functor.obj V)) a))
        ((sheafHomHomologySiteEquivIso eqv φ ψ H₁ H₂ P P j).hom.val.app (op V)
          (((endComplex X P).homologyπ j).val.app (op (eqv.functor.obj V)) b)) := by
  rw [homologyMul_app_homologyπ, sheafHomHomologySiteEquivIso_hom_app_homologyπ,
    sheafHomHomologySiteEquivIso_hom_app_homologyπ,
    sheafHomHomologySiteEquivIso_hom_app_homologyπ, homologyMul_app_homologyπ]
  refine homologyπ_app_eq_of_iCycles_app_eq _ _ V ?_
  rw [sheafHomCyclesSiteEquivMap_iCycles_app, iCycles_cycleComposition_pureSection,
    iCycles_cycleComposition_pureSection, sheafHomCyclesSiteEquivMap_iCycles_app,
    sheafHomCyclesSiteEquivMap_iCycles_app]
  exact compositionSection_siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ P P P V i j (i + j) rfl _ _

/-- **The comparison carries the unit to the unit**: the class of the identity goes to the class
of the identity. -/
theorem homologyOne_sheafHomHomologySiteEquivIso (V : Y.C) :
    ((sheafHomHomologySiteEquivIso eqv φ ψ H₁ H₂ P P 0).hom.val.app (op V))
        ((homologyOne X P).val (op (eqv.functor.obj V))) =
      (homologyOne Y ((pushComplex eqv φ).obj P)).val (op V) := by
  rw [homologyOne_eval, sheafHomHomologySiteEquivIso_hom_app_homologyπ, homologyOne_eval]
  refine homologyπ_app_eq_of_iCycles_app_eq _ _ V ?_
  rw [sheafHomCyclesSiteEquivMap_iCycles_app, iCycles_oneCycle, iCycles_oneCycle,
    idSection_siteEquivSheafHomComplexIso]

/-- **The comparison is multiplicative.** The two cohomology sections are lifted to cocycles
simultaneously on a common refinement of `C` — the transport of `homologyπ` is an epimorphism,
hence locally surjective, and `AlgebraicGeometry.RingedSite.eq_of_forall_lift₃` intersects the
resulting covering sieves — and on those lifts the identity is
`homologyMul_sheafHomHomologySiteEquivIso_of_cycles`. -/
theorem homologyMul_sheafHomHomologySiteEquivIso (i j : ℤ) (V : Y.Cᵒᵖ)
    (x : ((endComplex X P).homology i).val.obj (op (eqv.functor.obj V.unop)))
    (y : ((endComplex X P).homology j).val.obj (op (eqv.functor.obj V.unop))) :
    ((sheafHomHomologySiteEquivIso eqv φ ψ H₁ H₂ P P (i + j)).hom.val.app V)
        ((homologyMul X P P P i j).app (op (eqv.functor.obj V.unop)) x y) =
      (homologyMul Y ((pushComplex eqv φ).obj P) ((pushComplex eqv φ).obj P)
            ((pushComplex eqv φ).obj P) i j).app V
        ((sheafHomHomologySiteEquivIso eqv φ ψ H₁ H₂ P P i).hom.val.app V x)
        ((sheafHomHomologySiteEquivIso eqv φ ψ H₁ H₂ P P j).hom.val.app V y) := by
  refine @eq_of_forall_lift₃ Y _ _ _ _ _ _ _
    (((endComplex Y ((pushComplex eqv φ).obj P)).homology (i + j)).isSheaf.isSeparated)
    ((SheafOfModules.pushforward.{u} φ).map ((endComplex X P).homologyπ i)).val
    ((SheafOfModules.pushforward.{u} φ).map ((endComplex X P).homologyπ j)).val
    ((SheafOfModules.pushforward.{u} φ).map ((endComplex X P).homologyπ j)).val
    (isLocallySurjective_pushforward_map_homologyπ eqv φ P i)
    (isLocallySurjective_pushforward_map_homologyπ eqv φ P j)
    (isLocallySurjective_pushforward_map_homologyπ eqv φ P j) _ x y y _ _ ?_
  intro W f m₁ m₂ _ hm₁ hm₂ _
  rw [← PresheafOfModules.naturality_apply
      (sheafHomHomologySiteEquivIso eqv φ ψ H₁ H₂ P P (i + j)).hom.val f,
    _root_.Stacks.BilinearMap.naturality
      (homologyMul Y ((pushComplex eqv φ).obj P) ((pushComplex eqv φ).obj P)
        ((pushComplex eqv φ).obj P) i j) f,
    ← PresheafOfModules.naturality_apply
      (sheafHomHomologySiteEquivIso eqv φ ψ H₁ H₂ P P i).hom.val f,
    ← PresheafOfModules.naturality_apply
      (sheafHomHomologySiteEquivIso eqv φ ψ H₁ H₂ P P j).hom.val f,
    ← hm₁, ← hm₂]
  refine Eq.trans (congrArg
    (fun z => (sheafHomHomologySiteEquivIso eqv φ ψ H₁ H₂ P P (i + j)).hom.val.app W z) ?_)
    (homologyMul_sheafHomHomologySiteEquivIso_of_cycles eqv φ ψ H₁ H₂ P i j W.unop m₁ m₂)
  refine (_root_.Stacks.BilinearMap.naturality (homologyMul X P P P i j)
    (eqv.functor.map f.unop).op x y).trans ?_
  exact congrArg₂ (fun u v =>
    (homologyMul X P P P i j).app (op (eqv.functor.obj W.unop)) u v) hm₁.symm hm₂.symm

/-- **The comparison, as a unital homomorphism of sheaves of graded algebras.** The transport
along the equivalence of ringed sites of the graded algebra of the cohomology sheaves of
`SheafHom^•(P, P)` maps to the graded algebra of the cohomology sheaves of
`SheafHom^•(φ_* P, φ_* P)`, degreewise by
`AlgebraicGeometry.RingedSite.sheafHomHomologySiteEquivIso`. -/
def homologyGradedAlgebraSiteEquivHom :
    SheafOfModules.GradedAlgebra.UnitalHom
      (SheafOfModules.GradedAlgebra.pushforward φ (homologyGradedAlgebra X P))
      (homologyGradedAlgebra Y ((pushComplex eqv φ).obj P)) where
  app n := (sheafHomHomologySiteEquivIso eqv φ ψ H₁ H₂ P P n).hom
  map_mul i j V x y := homologyMul_sheafHomHomologySiteEquivIso eqv φ ψ H₁ H₂ P i j V x y
  map_one V := homologyOne_sheafHomHomologySiteEquivIso eqv φ ψ H₁ H₂ P V.unop

/-- The degree-`n` component of the comparison is `sheafHomHomologySiteEquivIso`. -/
theorem homologyGradedAlgebraSiteEquivHom_app (n : ℤ) :
    (homologyGradedAlgebraSiteEquivHom eqv φ ψ H₁ H₂ P).app n =
      (sheafHomHomologySiteEquivIso eqv φ ψ H₁ H₂ P P n).hom := rfl

/-- **Every degree of the comparison is an isomorphism.** -/
instance isIso_homologyGradedAlgebraSiteEquivHom_app (n : ℤ) :
    IsIso ((homologyGradedAlgebraSiteEquivHom eqv φ ψ H₁ H₂ P).app n) :=
  inferInstanceAs (IsIso (sheafHomHomologySiteEquivIso eqv φ ψ H₁ H₂ P P n).hom)

section OfIso

variable [hφ : IsIso φ]

/-- **The comparison, for an invertible structure map.** This is
`AlgebraicGeometry.RingedSite.homologyGradedAlgebraSiteEquivHom` with the inverse structure map
and the two compatibilities supplied by `Stacks.SheafOfModules.InternalHom.psiOfIso`, so that
only `φ` and its invertibility are needed.

The invertibility hypothesis is the *named* instance argument `hφ`, so that it can be passed by
hand: the two interchangeable `Category` instances of `CategoryTheory.Sheaf` keep synthesis from
finding it at a use site. -/
def homologyGradedAlgebraSiteEquivHomOfIso :
    SheafOfModules.GradedAlgebra.UnitalHom
      (SheafOfModules.GradedAlgebra.pushforward φ (homologyGradedAlgebra X P))
      (homologyGradedAlgebra Y ((pushComplex eqv φ).obj P)) :=
  homologyGradedAlgebraSiteEquivHom eqv φ
    (Stacks.SheafOfModules.InternalHom.psiOfIso eqv φ)
    (Stacks.SheafOfModules.InternalHom.psiOfIso_counit eqv φ)
    (Stacks.SheafOfModules.InternalHom.psiOfIso_unit eqv φ) P

/-- **Every degree of the comparison is an isomorphism**, for an invertible structure map. -/
instance isIso_homologyGradedAlgebraSiteEquivHomOfIso_app (n : ℤ) :
    IsIso ((homologyGradedAlgebraSiteEquivHomOfIso eqv φ P).app n) :=
  isIso_homologyGradedAlgebraSiteEquivHom_app eqv φ
    (Stacks.SheafOfModules.InternalHom.psiOfIso eqv φ)
    (Stacks.SheafOfModules.InternalHom.psiOfIso_counit eqv φ)
    (Stacks.SheafOfModules.InternalHom.psiOfIso_unit eqv φ) P n

end OfIso

end AlgebraicGeometry.RingedSite

end
