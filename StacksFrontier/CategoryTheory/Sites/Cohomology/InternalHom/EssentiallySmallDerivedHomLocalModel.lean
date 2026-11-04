module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallHomComplexLocal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectTensorLocalModels
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.QuasiIsomorphismLocality
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact

/-!
# The derived internal Hom out of a perfect object, locally

Let `X` be a ringed site whose objects form a type in a universe `c` while its morphisms, its
structure sheaf and its modules live in `u`, with `X.C` essentially `u`-small.  Let `E` be an
object of `D(O)` represented by a complex `E'`, and `V` an object of `X.C` over which `E'` has a
strictly perfect model `q : P ⟶ E'|_V`.  Then for every complex `𝒢` of `O`-modules

`RSheafHom(E, 𝒢)|_V ≅ SheafHom^•(P, 𝒢|_V)`

in `D(O|_V)`: the derived internal Hom restricted to `V` is computed by the internal Hom complex
out of the model into the restriction of `𝒢` itself, with no resolution of `𝒢`.

## Main definitions

* `AlgebraicGeometry.RingedSite.restrictDerivedSheafHomSmallIsoOfModel`: the isomorphism.

## The proof

`RSheafHom(QE', Q𝒢)` is the class of `SheafHom^•(E', I)` for the chosen K-injective resolution
`𝒢 ⟶ I`.  Its restriction to `V` is `SheafHom^•(E'|_V, I|_V)` (the chain-level Stacks 08JB,
`AlgebraicGeometry.RingedSite.sheafHomComplexSmallRestrictIso`); `I|_V` is K-injective
(Stacks 08FI), so precomposing with the quasi-isomorphism `q` gives a quasi-isomorphism onto
`SheafHom^•(P, I|_V)` (Stacks 0A95); and `P` is strictly perfect, so postcomposing with the
quasi-isomorphism `𝒢|_V ⟶ I|_V` gives a quasi-isomorphism from `SheafHom^•(P, 𝒢|_V)`
(Stacks 08JH).

## References

* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0A95](https://stacks.math.columbia.edu/tag/0A95)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c u d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{max c u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max c u}]
  [X.J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

attribute [local instance] essentiallySmall_over_C
  Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall.sliceHasSheafify
  Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall.sliceWEqualsLocallyBijective

/-- The topology of `(X.over U).C` over `W` admits weak sheafification of presheaves of abelian
groups in universe `u`. -/
local instance sliceSliceHasSheafify (U : X.C) (W : (X.over U).C) :
    HasWeakSheafify ((X.over U).J.over W) AddCommGrpCat.{u} :=
  have := Stacks.essentiallySmall_over.{u} (C := (X.over U).C) W
  have := GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u}
    ((X.over U).J.over W)
  inferInstance

/-- For the topology of `(X.over U).C` over `W`, the weak equivalences of sheaves of abelian groups
in universe `u` are the locally bijective morphisms. -/
local instance sliceSliceWEq (U : X.C) (W : (X.over U).C) :
    ((X.over U).J.over W).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  have := Stacks.essentiallySmall_over.{u} (C := (X.over U).C) W
  .ofEssentiallySmall _

/-- The topology of `X.over U` admits sheafification of presheaves of abelian groups in universe
`max c u`. -/
local instance sliceHasSheafifyMax (U : X.C) :
    HasSheafify (X.over U).J AddCommGrpCat.{max c u} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{max c u} _

/-- For the topology of `X.over U`, the weak equivalences of sheaves of abelian groups in universe
`max c u` are the locally bijective morphisms. -/
local instance sliceWEqMax (U : X.C) :
    (X.over U).J.WEqualsLocallyBijective AddCommGrpCat.{max c u} :=
  GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat.{max c u} _

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [hSliceDerived : ∀ U : X.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{max c u, u, u} (X.over U))]

attribute [local instance]
  Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall.sliceHasDerivedCategory''

/-- **The derived internal Hom out of `E` restricted to an object carrying a strictly perfect
model of `E`.**  If `E'` is a complex with class `E` and `q : P ⟶ E'|_V` is a quasi-isomorphism
from a strictly perfect complex of `O|_V`-modules, then
`RSheafHom(E, Q𝒢)|_V ≅ Q(SheafHom^•(P, 𝒢|_V))`. -/
def restrictDerivedSheafHomSmallIsoOfModel
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (E' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (eE : DerivedCategory.Q.obj E' ≅ E) (V : X.C)
    (P : CochainComplex (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ)
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P)
    (q : P ⟶ X.restrictComplex E' V) (hq : QuasiIso q)
    (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (RingedSite.derivedRestriction.{c, u, u, d} X V).obj
        (((derivedSheafHomSmallBifunctor X).obj (op E)).obj (DerivedCategory.Q.obj G)) ≅
      DerivedCategory.Q.obj (sheafHomComplexSmall (X.over V) P (X.restrictComplex G V)) := by
  let I := (kInjectiveResolutionSmall X).obj G
  let ι : G ⟶ I := (kInjectiveAugmentationSmall X).app G
  have : (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      V).Additive := SheafOfModules.overFunctor_additive _ V
  have : PreservesFiniteLimits (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits V
  have : PreservesFiniteColimits (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits V
  let IV : CochainComplex (RingedSite.Modules.{max c u, u, u} (X.over V)) ℤ :=
    X.restrictComplex I V
  let GV : CochainComplex (RingedSite.Modules.{max c u, u, u} (X.over V)) ℤ :=
    X.restrictComplex G V
  let E'V : CochainComplex (RingedSite.Modules.{max c u, u, u} (X.over V)) ℤ :=
    X.restrictComplex E' V
  let P' : CochainComplex (RingedSite.Modules.{max c u, u, u} (X.over V)) ℤ := P
  let ιV : GV ⟶ IV := ((SheafOfModules.overFunctor.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapHomologicalComplex
      (ComplexShape.up ℤ)).map ι
  let q' : P' ⟶ E'V := q
  have hιV : QuasiIso ιV := HomologicalComplex.quasiIso_map_of_preservesHomology ι
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V)
  have hIV : IV.IsKInjective :=
    Stacks.Cohomology.Localization.isKInjective_over_of_essentiallySmall X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V I
  have hq' : QuasiIso q' := hq
  have h1 : QuasiIso (homMapSmall (X.over V) q' (𝟙 IV)) :=
    homMapSmall_quasiIso (X.over V) (𝟙 IV) q'
  have h2 : QuasiIso (homMapSmall (X.over V) (𝟙 P') ιV) :=
    homMapSmall_quasiIso_of_isStrictlyPerfect (X.over V) P' hP ιV
  exact (RingedSite.derivedRestriction.{c, u, u, d} X V).mapIso
      (((derivedSheafHomSmallBifunctor X).mapIso eE.op).app (DerivedCategory.Q.obj G) ≪≫
        derivedSheafHomSmallResolutionComparison X E' G) ≪≫
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      V).mapDerivedCategoryFactors.app (sheafHomComplexSmall X E' I) ≪≫
    DerivedCategory.Q.mapIso (sheafHomComplexSmallRestrictIso X E' I V) ≪≫
    @asIso _ _ _ _ (DerivedCategory.Q.map (homMapSmall (X.over V) q' (𝟙 IV)))
      ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 h1) ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map (homMapSmall (X.over V) (𝟙 P') ιV))
      ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 h2)).symm

end AlgebraicGeometry.RingedSite

end
