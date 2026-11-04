module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafComplexLocalHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantRingModulesCompatibility
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategoryJunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The slicing compatibility of the two readings of a sheaf of `Λ`-modules, on derived categories

Let `(C, J)` be a site, `Λ` a ring and `R` a sheaf of rings with a locally bijective morphism
`α` out of the constant presheaf of rings on `Λ`. The equivalence
`Stacks.ConstantRingModules.toModuleSheaf Λ J α : SheafOfModules R ≌ Sheaf J (ModuleCat Λ)`
commutes with restriction to a slice site, and
`StacksFrontier.CategoryTheory.Sites.Modules.ConstantRingModulesCompatibility` proves that square
on the abelian categories themselves, every component being the identity. This file carries that
square, and its version along a morphism of the site, to the **derived** categories.

Both squares are needed in this form, not in the underived one:

* Stacks 094H's bounded case consumes the slice compatibility of the derived tensor product,
  `Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictNatIso`, which is an isomorphism of
  functors `D(O) × D(O) ⥤ D(O|_U)` for sheaves of modules over a ringed site. Transporting it to
  `D(Sheaf J (ModuleCat Λ))` needs exactly the derived square below, for both the structure sheaf
  and its restriction.
* Stacks 09BE needs Stacks 09BD transported across the same equivalence, and 09BD's conclusion is
  a comparison of morphisms of `D(O|_V)` for the arrows `V ⟶ U` of a covering sieve, so it is the
  version along a morphism of the site that applies there.

## Main definitions

* `Stacks.ConstantRingModules.toModuleSheafOverDerivedIso`: the derived slicing square, along
  `Over.forget U`.
* `Stacks.ConstantRingModules.toModuleSheafOverMapDerivedIso`: the derived slicing square along a
  morphism of the site.
* `Stacks.ConstantRingModules.toModuleSheafOverComplexIso` and
  `toModuleSheafOverMapComplexIso`: the two squares read degreewise on cochain complexes.

## Main results

* `Stacks.ConstantRingModules.toModuleSheafOverDerivedIso_hom_app_Q` and
  `toModuleSheafOverMapDerivedIso_hom_app_Q`: **the junction squares** — the component of each
  derived square at the class of a complex, written through the
  `CategoryTheory.Functor.mapDerivedCategoryFactors` of the four functors it compares and the
  degreewise square. Without these the derived squares are opaque: each is a lift through the
  localisation functor, and nothing in `Dualizing.mapDerivedCategoryCompNatIso` says what the lift
  does to the class of a complex, so no equation written through a `mapDerivedCategoryFactors` can
  be carried across. This is the junction of the kind
  `StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RestrictionToASliceJunction` supplies
  for the derived tensor product.

## Implementation notes

Both squares are the underived square pushed through
`CategoryTheory.Functor.mapDerivedCategory` by the functoriality package of
`StacksFrontier.RingTheory.Dualizing.MapDerivedCategory`:
`Dualizing.mapDerivedCategoryCompNatIso` turns an isomorphism `F ⋙ G ≅ H` of exact functors into
an isomorphism `F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory`, and
`Dualizing.mapDerivedCategoryComp` splits the right-hand side back into a composite. Neither is a
new comparison; what they add is that the comparison exists on derived categories, which is what
the two consumers above are stated about.

The two junction squares are each that definition read at `Q(A)`, by
`Dualizing.mapDerivedCategoryCompNatIso_hom_app_Q` and
`Dualizing.mapDerivedCategoryComp_hom_app_Q` of
`StacksFrontier.RingTheory.Dualizing.MapDerivedCategoryJunction`. The degreewise square has to be
named separately rather than left as
`CategoryTheory.Functor.mapHomologicalComplexCompIso` of the underived square: the latter lands at
the complex `((G ⋙ E).mapHomologicalComplex c).obj A` while the consumers work with
`(E.mapHomologicalComplex c).obj ((G.mapHomologicalComplex c).obj A)`, and although the two are
definitionally equal, a trailing identity indexed by one of them cannot be cancelled against a
morphism into the other.

**What the two junction squares do not do.** Conjugating a comparison of bifunctors by one of these
squares needs it in three slots, and only the outer one is the square as stated: the two inner
slots are about the *inverse* equivalences, where the needed comparison is
`Stacks.ConstantRingModules.toModuleSheaf`'s inverse against restriction, i.e. the **mate** of
`toModuleSheafOverIso` along the two adjunctions of
`Stacks.ConstantRingModules.moduleSheafEquivalence`. That mate is not constructed here, and it
should not be hand-rolled: it is `CategoryTheory.mateEquiv` of
`Mathlib/CategoryTheory/Adjunction/Mates.lean`, which is available at this project's Mathlib pin. It
is constructed from that `CategoryTheory.mateEquiv`, as
`Stacks.ConstantRingModules.toModuleSheafInvOverIso` with its derived form
`toModuleSheafInvOverDerivedIso`, in
`StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConstantRingDerivedTensorRestriction`, which is
also where the three-slot conjugation those and the squares above carry out is done. That module
imports this one, so the dependency runs only that way and the mention here is a pointer.

The exactness of the four functors involved is not assumed. For the two instances of
`toModuleSheaf` it is automatic, each being an equivalence; for restriction of
`ModuleCat Λ`-valued sheaves to a slice it is in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass`; and for restriction of
sheaves of modules it is
`Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits`,
`overFunctor_preservesFiniteColimits` and their counterparts along an arrow of the site, put into
instance scope below as `local instance`s. The instance-scope forms already in
`StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact` are not used for the slice functor
because they ask for binary products in the site, which neither consumer has.

Right exactness of restriction of `ModuleCat Λ`-valued sheaves *along an arrow* of the site is
the one thing the library did not have in this generality: it has
`Stacks.Cohomology.LocalizedSite.preservesFiniteColimits_overMapPullback` for `AddCommGrpCat` and
`Stacks.ConstantSheaf.preservesFiniteColimits_overPullback` for `ModuleCat Λ` along
`Over.forget`, but not the two combined. It is `preservesFiniteColimitsOverMapPullback` below,
by the same left-adjoint argument as the `Over.forget` case, and so is discharged rather than
assumed.

No `@[stacks]` attribute is attached. No statement of the source is a compatibility of an
equivalence of categories with restriction to a slice; these are the identifications that let a
theorem about one of the two readings of `Mod(C, Λ)` discharge an obligation stated about the
other.

## References

* [Stacks Project, Tag 094H](https://stacks.math.columbia.edu/tag/094H)
* [Stacks Project, Tag 09BD](https://stacks.math.columbia.edu/tag/09BD)
* [Stacks Project, Tag 09BE](https://stacks.math.columbia.edu/tag/09BE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

universe d u

namespace Stacks.ConstantRingModules

open Stacks.PresheafOfModules Stacks.ConstantSheaf

variable {C : Type u} [Category.{u} C] (Λ : Type u) [Ring Λ]
  (J : GrothendieckTopology C) {R : Sheaf J RingCat.{u}}
  (α : constRing (C := C) Λ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J (ModuleCat.{u} Λ)] [J.WEqualsLocallyBijective (ModuleCat.{u} Λ)]
  [J.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasDerivedCategory.{d} (_root_.SheafOfModules.{u} R)]
  [HasDerivedCategory.{d} (Sheaf J (ModuleCat.{u} Λ))]
  [∀ W : C, HasSheafify (J.over W) AddCommGrpCat.{u}]
  [∀ W : C, (J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restriction of sheaves of modules to a slice preserves finite limits. Seated as an instance
here from `Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits`, whose
instance-scope form in `StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact` asks for
binary products in the site and so does not fire on an arbitrary one. -/
local instance preservesFiniteLimitsModuleSheafOverFunctor (W : C) :
    PreservesFiniteLimits (_root_.SheafOfModules.overFunctor.{u} R W) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits W

/-- Restriction of sheaves of modules to a slice preserves finite colimits, seated from
`Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits` for the same reason. -/
local instance preservesFiniteColimitsModuleSheafOverFunctor (W : C) :
    PreservesFiniteColimits (_root_.SheafOfModules.overFunctor.{u} R W) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits W

/-- Restriction of sheaves of modules along an arrow of the site preserves finite limits, seated
from `Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits`. -/
local instance preservesFiniteLimitsModuleSheafOverMap {W W' : C} (g : W' ⟶ W) :
    PreservesFiniteLimits (_root_.SheafOfModules.overMap.{u} R g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits g

/-- Restriction of sheaves of modules along an arrow of the site preserves finite colimits,
seated from `Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits`. -/
local instance preservesFiniteColimitsModuleSheafOverMap {W W' : C} (g : W' ⟶ W) :
    PreservesFiniteColimits (_root_.SheafOfModules.overMap.{u} R g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits g

/-- **Restriction of `ModuleCat Λ`-valued sheaves along an arrow of the site is right exact.**
`Over.map g` is cocontinuous for the localized topologies, so restriction along it is the left
adjoint of `CategoryTheory.Functor.sheafAdjunctionCocontinuous` and preserves every colimit that
exists. This is the `ModuleCat Λ`-valued counterpart of
`Stacks.Cohomology.LocalizedSite.preservesFiniteColimits_overMapPullback`, which the library has
only for `AddCommGrpCat`, and of the `Over.forget` case
`Stacks.ConstantSheaf.preservesFiniteColimits_overPullback`, which it has for `ModuleCat Λ`. -/
@[ega "0 4.3.2" "partial", sga "4 IV 11.2.2" "special case"]
local instance preservesFiniteColimitsOverMapPullback {W W' : C} (g : W' ⟶ W)
    [HasWeakSheafify (J.over W') (ModuleCat.{u} Λ)]
    [HasWeakSheafify (J.over W) (ModuleCat.{u} Λ)] :
    PreservesFiniteColimits (J.overMapPullback (ModuleCat.{u} Λ) g) := by
  have := ((Over.map g).sheafAdjunctionCocontinuous (ModuleCat.{u} Λ)
    (J.over W') (J.over W)).leftAdjoint_preservesColimits
  infer_instance

/-- The component at the class of a complex of the derived square built from `e : F ⋙ G ≅ P ⋙ K`,
written through the `mapDerivedCategoryFactors` of the four functors and the degreewise square. -/
private theorem mapDerivedCategoryCompNatIso_trans_comp_hom_app_Q
    {C D E E' : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    [Category E] [Abelian E] [HasDerivedCategory E]
    [Category E'] [Abelian E'] [HasDerivedCategory E']
    (F : C ⥤ D) (G : D ⥤ E') (P : C ⥤ E) (K : E ⥤ E') (e : F ⋙ G ≅ P ⋙ K)
    [F.Additive] [G.Additive] [P.Additive] [K.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K] (A : CochainComplex C ℤ) :
    (Dualizing.mapDerivedCategoryCompNatIso F G (P ⋙ K) e ≪≫
        Dualizing.mapDerivedCategoryComp P K).hom.app (DerivedCategory.Q.obj A) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app A) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj A) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ) ≪≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (P ⋙ K))
            (ComplexShape.up ℤ)).symm).hom.app A) ≫
        K.mapDerivedCategoryFactors.inv.app ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj A) ≫
        K.mapDerivedCategory.map (P.mapDerivedCategoryFactors.inv.app A) := by
  have hθ : (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (P ⋙ K))
          (ComplexShape.up ℤ)).symm).hom.app A =
      (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app A := by
    ext n
    simp
  rw [Iso.trans_hom, NatTrans.comp_app, Dualizing.mapDerivedCategoryCompNatIso_hom_app_Q,
    Dualizing.mapDerivedCategoryComp_hom_app_Q, hθ]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

/-! ### Along `Over.forget U` -/

section Slice

variable (U : C)
  [HasWeakSheafify (J.over U) (ModuleCat.{u} Λ)]
  [(J.over U).WEqualsLocallyBijective (ModuleCat.{u} Λ)]
  [(J.over U).HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasDerivedCategory.{d} (_root_.SheafOfModules.{u} (R.over U))]
  [HasDerivedCategory.{d} (Sheaf (J.over U) (ModuleCat.{u} Λ))]

/-- **The slicing compatibility of the two readings of a sheaf of `Λ`-modules, on derived
categories.** `Stacks.ConstantRingModules.toModuleSheafOverIso` pushed through
`CategoryTheory.Functor.mapDerivedCategory`: reading a sheaf of modules over `R` as a sheaf of
`Λ`-modules commutes with restriction to the slice site `C/U` on `D(-)` as it does on the
abelian categories. -/
def toModuleSheafOverDerivedIso :
    (toModuleSheaf.{u} Λ J α).mapDerivedCategory ⋙
        (J.overPullback (ModuleCat.{u} Λ) U).mapDerivedCategory ≅
      (_root_.SheafOfModules.overFunctor.{u} R U).mapDerivedCategory ⋙
        (toModuleSheaf.{u} Λ (J.over U) (overRingMap Λ J α U)).mapDerivedCategory :=
  Dualizing.mapDerivedCategoryCompNatIso (toModuleSheaf.{u} Λ J α)
      (J.overPullback (ModuleCat.{u} Λ) U)
      (_root_.SheafOfModules.overFunctor.{u} R U ⋙
        toModuleSheaf.{u} Λ (J.over U) (overRingMap Λ J α U))
      (toModuleSheafOverIso.{u} Λ J α U) ≪≫
    Dualizing.mapDerivedCategoryComp (_root_.SheafOfModules.overFunctor.{u} R U)
      (toModuleSheaf.{u} Λ (J.over U) (overRingMap Λ J α U))

/-- The slicing compatibility of the two readings of a sheaf of `Λ`-modules, read degreewise on
cochain complexes. -/
def toModuleSheafOverComplexIso :
    (toModuleSheaf.{u} Λ J α).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (J.overPullback (ModuleCat.{u} Λ) U).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (_root_.SheafOfModules.overFunctor.{u} R U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (toModuleSheaf.{u} Λ (J.over U) (overRingMap Λ J α U)).mapHomologicalComplex
          (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (toModuleSheafOverIso.{u} Λ J α U)
      (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (_root_.SheafOfModules.overFunctor.{u} R U ⋙
        toModuleSheaf.{u} Λ (J.over U) (overRingMap Λ J α U))) (ComplexShape.up ℤ)).symm

omit [HasWeakSheafify J (ModuleCat.{u} Λ)] [J.WEqualsLocallyBijective (ModuleCat.{u} Λ)]
  [HasWeakSheafify (J.over U) (ModuleCat.{u} Λ)]
  [(J.over U).WEqualsLocallyBijective (ModuleCat.{u} Λ)] in
/-- **The junction square for the derived slicing square along `Over.forget U`.** The component of
`Stacks.ConstantRingModules.toModuleSheafOverDerivedIso` at the class of a complex, written
through the `CategoryTheory.Functor.mapDerivedCategoryFactors` of the four functors it compares
and the degreewise square `Stacks.ConstantRingModules.toModuleSheafOverComplexIso`.

Without this the derived slicing square is opaque: it is a lift through the localisation functor,
and nothing in its construction says what it does to the class of a complex. It is what lets the
conjugation of a comparison of functors `D(R) × D(R) ⥤ D(R|_U)` by this square be computed on the
models of the two sides, which is how
`Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictNatIso` is built in the first
place. -/
theorem toModuleSheafOverDerivedIso_hom_app_Q
    (A : CochainComplex (_root_.SheafOfModules.{u} R) ℤ) :
    (toModuleSheafOverDerivedIso.{d, u} Λ J α U).hom.app (DerivedCategory.Q.obj A) =
      (J.overPullback (ModuleCat.{u} Λ) U).mapDerivedCategory.map
          ((toModuleSheaf.{u} Λ J α).mapDerivedCategoryFactors.hom.app A) ≫
        (J.overPullback (ModuleCat.{u} Λ) U).mapDerivedCategoryFactors.hom.app
          (((toModuleSheaf.{u} Λ J α).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) ≫
        DerivedCategory.Q.map ((toModuleSheafOverComplexIso.{u} Λ J α U).hom.app A) ≫
        (toModuleSheaf.{u} Λ (J.over U) (overRingMap Λ J α U)).mapDerivedCategoryFactors.inv.app
          (((_root_.SheafOfModules.overFunctor.{u} R U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj A) ≫
        (toModuleSheaf.{u} Λ (J.over U) (overRingMap Λ J α U)).mapDerivedCategory.map
          ((_root_.SheafOfModules.overFunctor.{u} R U).mapDerivedCategoryFactors.inv.app A) :=
  mapDerivedCategoryCompNatIso_trans_comp_hom_app_Q _ _ _ _ _ A

end Slice

/-! ### Along a morphism of the site -/

section SliceMap

variable {X Y : C} (f : X ⟶ Y)
  [HasWeakSheafify (J.over X) (ModuleCat.{u} Λ)]
  [(J.over X).WEqualsLocallyBijective (ModuleCat.{u} Λ)]
  [(J.over X).HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasWeakSheafify (J.over Y) (ModuleCat.{u} Λ)]
  [(J.over Y).WEqualsLocallyBijective (ModuleCat.{u} Λ)]
  [(J.over Y).HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasDerivedCategory.{d} (_root_.SheafOfModules.{u} (R.over X))]
  [HasDerivedCategory.{d} (_root_.SheafOfModules.{u} (R.over Y))]
  [HasDerivedCategory.{d} (Sheaf (J.over X) (ModuleCat.{u} Λ))]
  [HasDerivedCategory.{d} (Sheaf (J.over Y) (ModuleCat.{u} Λ))]

/-- **The slicing compatibility along a morphism of the site, on derived categories.**
`Stacks.ConstantRingModules.toModuleSheafOverMapIso` pushed through
`CategoryTheory.Functor.mapDerivedCategory`. This is the shape the conclusion of Stacks 09BD is
in, where the chain map produced lives over the slices of the arrows of a covering sieve, so it
is the form the transport of 09BD across the equivalence consumes. -/
def toModuleSheafOverMapDerivedIso :
    (toModuleSheaf.{u} Λ (J.over Y) (overRingMap Λ J α Y)).mapDerivedCategory ⋙
        (J.overMapPullback (ModuleCat.{u} Λ) f).mapDerivedCategory ≅
      (_root_.SheafOfModules.overMap.{u} R f).mapDerivedCategory ⋙
        (toModuleSheaf.{u} Λ (J.over X) (overRingMap Λ J α X)).mapDerivedCategory :=
  Dualizing.mapDerivedCategoryCompNatIso
      (toModuleSheaf.{u} Λ (J.over Y) (overRingMap Λ J α Y))
      (J.overMapPullback (ModuleCat.{u} Λ) f)
      (_root_.SheafOfModules.overMap.{u} R f ⋙
        toModuleSheaf.{u} Λ (J.over X) (overRingMap Λ J α X))
      (toModuleSheafOverMapIso.{u} Λ J α f) ≪≫
    Dualizing.mapDerivedCategoryComp (_root_.SheafOfModules.overMap.{u} R f)
      (toModuleSheaf.{u} Λ (J.over X) (overRingMap Λ J α X))

/-- The slicing compatibility along a morphism of the site, read degreewise on cochain
complexes. -/
def toModuleSheafOverMapComplexIso :
    (toModuleSheaf.{u} Λ (J.over Y) (overRingMap Λ J α Y)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (J.overMapPullback (ModuleCat.{u} Λ) f).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (_root_.SheafOfModules.overMap.{u} R f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (toModuleSheaf.{u} Λ (J.over X) (overRingMap Λ J α X)).mapHomologicalComplex
          (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (toModuleSheafOverMapIso.{u} Λ J α f)
      (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (_root_.SheafOfModules.overMap.{u} R f ⋙
        toModuleSheaf.{u} Λ (J.over X) (overRingMap Λ J α X))) (ComplexShape.up ℤ)).symm

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J (ModuleCat.{u} Λ)] [J.WEqualsLocallyBijective (ModuleCat.{u} Λ)]
  [J.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasDerivedCategory.{d} (_root_.SheafOfModules.{u} R)]
  [HasDerivedCategory.{d} (Sheaf J (ModuleCat.{u} Λ))]
  [(J.over X).WEqualsLocallyBijective (ModuleCat.{u} Λ)]
  [(J.over Y).WEqualsLocallyBijective (ModuleCat.{u} Λ)] in
/-- **The junction square for the derived slicing square along a morphism of the site.** The
component of `Stacks.ConstantRingModules.toModuleSheafOverMapDerivedIso` at the class of a
complex, written through the `CategoryTheory.Functor.mapDerivedCategoryFactors` of the four
functors it compares and the degreewise square
`Stacks.ConstantRingModules.toModuleSheafOverMapComplexIso`.

This is what carries an equation stated through the `mapDerivedCategoryFactors` of restriction of
sheaves of modules along an arrow of the site -- which is the shape of the conclusion of Stacks
09BD -- to one stated through the `mapDerivedCategoryFactors` of restriction of
`ModuleCat Λ`-valued sheaves along the same arrow, which is the shape Stacks 09BE is about. -/
theorem toModuleSheafOverMapDerivedIso_hom_app_Q
    (A : CochainComplex (_root_.SheafOfModules.{u} (R.over Y)) ℤ) :
    (toModuleSheafOverMapDerivedIso.{d, u} Λ J α f).hom.app (DerivedCategory.Q.obj A) =
      (J.overMapPullback (ModuleCat.{u} Λ) f).mapDerivedCategory.map
          ((toModuleSheaf.{u} Λ (J.over Y)
            (overRingMap Λ J α Y)).mapDerivedCategoryFactors.hom.app A) ≫
        (J.overMapPullback (ModuleCat.{u} Λ) f).mapDerivedCategoryFactors.hom.app
          (((toModuleSheaf.{u} Λ (J.over Y) (overRingMap Λ J α Y)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj A) ≫
        DerivedCategory.Q.map ((toModuleSheafOverMapComplexIso.{u} Λ J α f).hom.app A) ≫
        (toModuleSheaf.{u} Λ (J.over X) (overRingMap Λ J α X)).mapDerivedCategoryFactors.inv.app
          (((_root_.SheafOfModules.overMap.{u} R f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj A) ≫
        (toModuleSheaf.{u} Λ (J.over X) (overRingMap Λ J α X)).mapDerivedCategory.map
          ((_root_.SheafOfModules.overMap.{u} R f).mapDerivedCategoryFactors.inv.app A) :=
  mapDerivedCategoryCompNatIso_trans_comp_hom_app_Q _ _ _ _ _ A

end SliceMap

end Stacks.ConstantRingModules

end
