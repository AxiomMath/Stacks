module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkTensorComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficientStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.CategoryTheory.Sites.Point.UniverseChange
public import StacksFrontier.CategoryTheory.Sites.SheafSectionEssentiallySmall

/-!
# A constructible flat sheaf of modules is flat over the constant coefficient ring sheaf

The flatness hypothesis of [Stacks, Tag 03TR], in the form
`AlgebraicGeometry.stalk_projective` and `AlgebraicGeometry.stalk_isPerfect` ask for it, is
flatness of the sheaf of modules `AlgebraicGeometry.moduleSheafOverConstantCoefficients`
obtained from a sheaf of `Λ`-modules by sheafifying the action of the constant sections.
Condition (2) of [Stacks, Tag 03TT], on the other hand, is constructible flatness of the terms
of a representing complex: local constancy with finite projective values on the strata of a
constructible stratification.  This file derives the first from the second.

The route is Stacks 05VC.  Flatness of a sheaf of modules is read off the stalks at a
conservative family of points of the site, and the geometric points of `X` form such a family;
at a geometric point the stalk of the sheaf of modules over the constant coefficient ring sheaf
is the étale stalk of the sheaf of `Λ`-modules, which is a projective — hence flat — `Λ`-module
by `AlgebraicGeometry.etaleModuleStalk_projective_of_isConstructibleFlatModuleSheaf`.

## Main results

* `AlgebraicGeometry.isConservativeFamilyOfPoints_uliftGeometricSitePoint` — the universe lifts
  of the geometric points of `X` are a conservative family of points of the small étale site, at
  the universe in which the sheaf of modules over the constant coefficient ring sheaf lives.
* `AlgebraicGeometry.isFlatModuleStalk_of_flat_etaleModuleStalk` — flatness of the étale stalk
  over `Λ` is flatness of the stalk of the associated sheaf of modules over the stalk of the
  constant coefficient ring sheaf.
* `AlgebraicGeometry.isFlat_moduleSheafOverConstantCoefficients_of_flat_etaleModuleStalk` — **a
  sheaf of `Λ`-modules whose étale stalks are flat is flat over the constant coefficient ring
  sheaf.** Neither finiteness of the stalks nor any hypothesis on `X` enters.
* `AlgebraicGeometry.isFlat_moduleSheafOverConstantCoefficients_of_isConstructibleFlatModuleSheaf`
  — **a constructible flat sheaf of `Λ`-modules is flat over the constant coefficient ring
  sheaf**, the special case of the previous statement in which the stalks are projective.

## Implementation notes

The universes are the ones the comparison of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ConstantCoefficientStalk.lean` is stated at: the
sheaf of modules over the constant coefficient ring sheaf has its sections in
`max (u + 1) w r`, which contains the universe of the site, of the coefficient ring and of the
module sections, so the points whose stalks measure its flatness are points relative to that
universe.  The geometric points give points relative to `u`, and
`CategoryTheory.GrothendieckTopology.Point.ulift` raises them; conservativity survives the lift
because the family is indexed by the points of the underlying space of `X`, hence is `u`-small.
This is the same manoeuvre as in
`AlgebraicGeometry.SmallEtale.isConservativeFamilyOfPoints_uliftGeometricPointSitePoint`, there
performed at `u + 1`.

Flatness over the stalk of the constant coefficient ring sheaf and flatness over `Λ` are
identified through `AlgebraicGeometry.constantCoefficientRingFiberEquiv`, the two module
structures differing by that ring isomorphism; `AlgebraicGeometry.flat_of_semilinear_equiv`
transports flatness across it.  The intervening universe lift of the sections of the étale stalk
is harmless: a universe lift of a flat module is flat.

Only projectivity of the stalk is used, not its finiteness, so no Noetherian hypothesis is
needed here; it is needed by
`AlgebraicGeometry.stalk_isPerfect_of_isConstructibleFlatModuleSheaf` because finiteness of the
stalk of a constructible sheaf, Tag 03RW part (3), asks for it.

## References

* [Stacks Project, Tag 03TR](https://stacks.math.columbia.edu/tag/03TR)
* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
* [Stacks Project, Tag 05VC](https://stacks.math.columbia.edu/tag/05VC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]
  [HasColimitsOfSize.{u, u} (ModuleCat.{w} Λ)]

attribute [local instance] SheafOfModules.hasSheafify_commRingCat
  SheafOfModules.wEqualsLocallyBijective_commRingCat
  GrothendieckTopology.hasSheafify_addCommGrpCat
  SheafOfModules.wEqualsLocallyBijective_addCommGrpCat

/-! ### The conservative family of lifted geometric points -/

set_option linter.checkUnivs false in
/-- **The universe lifts of the geometric points of `X` are a conservative family of points of
its small étale site**, at the universe `max (u + 1) w r` containing the site, the coefficient
ring and the module sections.

`AlgebraicGeometry.isConservativeFamilyOfPoints_geometricSitePoints` is the family relative to
the universe `u`; it is indexed by the points of the underlying space of `X`, hence `u`-small,
so `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.ulift` raises it. -/
public theorem isConservativeFamilyOfPoints_uliftGeometricSitePoint :
    ObjectProperty.IsConservativeFamilyOfPoints
      (ObjectProperty.ofObj (fun x : ↥X.obj =>
        (geometricSitePoint B X (.ofPoint X.obj x)).ulift.{max (u + 1) w r})) := by
  have h₁ : (SmallEtale.topology B X.obj X.property).WEqualsLocallyBijective (Type u) :=
    GrothendieckTopology.wEqualsLocallyBijective_type _
  have h₂ : HasSheafify (SmallEtale.topology B X.obj X.property)
      (Type (max (u + 1) w r)) :=
    Stacks.Sites.SheafSection.hasSheafify_type_of_essentiallySmall _
  exact (GrothendieckTopology.isConservativeFamily_iff_ofObj _).1
    (GrothendieckTopology.IsConservativeFamily.ulift.{max (u + 1) w r}
      ((GrothendieckTopology.isConservativeFamily_iff_ofObj _).2
        (isConservativeFamilyOfPoints_geometricSitePoints B X.obj X.property)))

/-! ### Flatness of the stalk -/

omit [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)] in
/-- **Flatness of the étale stalk over `Λ` is flatness of the stalk of the associated sheaf of
modules.** The stalk of `AlgebraicGeometry.moduleSheafOverConstantCoefficients` at the universe
lift of the point of a geometric point is the étale stalk, by
`AlgebraicGeometry.etaleModuleStalkFiberIso`, and the two module structures differ by the
identification `AlgebraicGeometry.constantCoefficientRingFiberEquiv` of the stalk of the
constant coefficient ring sheaf with `Λ`. -/
public theorem isFlatModuleStalk_of_flat_etaleModuleStalk
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))
    (s : GeometricPoint X.obj)
    (hflat : Module.Flat Λ ((etaleModuleStalkFunctor B X Λ s).obj F)) :
    Stacks.IsFlatModuleStalk ((geometricSitePoint B X s).ulift.{max (u + 1) w r})
      (constantCoefficientSheaf.{u, w, r} B X Λ)
      (moduleSheafOverConstantCoefficients.{u, w, r} B X Λ F) := by
  have hL : Module.Flat Λ ↑((ModuleCat.uliftFunctor.{max (u + 1) r} Λ).obj
      ((etaleModuleStalkFunctor B X Λ s).obj F)) :=
    have := hflat
    Module.Flat.ulift (R := Λ) (M := ((etaleModuleStalkFunctor B X Λ s).obj F))
  set e := constantCoefficientRingFiberEquiv.{u, w, r} B X Λ
    ((geometricSitePoint B X s).ulift.{max (u + 1) w r}) with he
  set g := (etaleModuleStalkFiberIso.{u, w, r} B X Λ s F).symm.toLinearEquiv with hg
  refine flat_of_semilinear_equiv e.symm g.toAddEquiv (fun c m => ?_)
  exact (congrArg g (congrArg (· • m) (e.apply_symm_apply c).symm)).trans
    (g.map_smul (e.symm c) m)

/-! ### Flatness over the constant coefficient ring sheaf -/

omit [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)] in
/-- **A sheaf of `Λ`-modules whose étale stalks are flat is flat over the constant coefficient
ring sheaf.** This is Stacks 05VC applied to the conservative family of lifted geometric points:
at each of them the stalk of the associated sheaf of modules is the étale stalk, by
`AlgebraicGeometry.isFlatModuleStalk_of_flat_etaleModuleStalk`.

No hypothesis on `X` and no finiteness of the stalks enters, so this applies to the arbitrary
coproducts of the generators `j_{U!}\underline{Λ}` of Stacks 093B (2), which are not
constructible. -/
public theorem isFlat_moduleSheafOverConstantCoefficients_of_flat_etaleModuleStalk
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))
    (hF : ∀ s : GeometricPoint X.obj,
      Module.Flat Λ ((etaleModuleStalkFunctor B X Λ s).obj F)) :
    Stacks.SheafOfModules.IsFlat.{u, u + 1, max (u + 1) w r, max (u + 1) w r}
      (moduleSheafOverConstantCoefficients.{u, w, r} B X Λ F) :=
  Stacks.isFlat_of_forall_isFlatModuleStalk (constantCoefficientSheaf.{u, w, r} B X Λ) _
    (fun x : ↥X.obj => (geometricSitePoint B X (.ofPoint X.obj x)).ulift.{max (u + 1) w r})
    (isConservativeFamilyOfPoints_uliftGeometricSitePoint.{u, w, r} B X)
    (fun x => isFlatModuleStalk_of_flat_etaleModuleStalk.{u, w, r} B X Λ F _
      (hF (.ofPoint X.obj x)))

/-- **A constructible flat sheaf of `Λ`-modules is flat over the constant coefficient ring
sheaf.** Its étale stalks are projective by
`AlgebraicGeometry.etaleModuleStalk_projective_of_isConstructibleFlatModuleSheaf`, hence flat, so
this is the special case of
`AlgebraicGeometry.isFlat_moduleSheafOverConstantCoefficients_of_flat_etaleModuleStalk`.

It is the flatness hypothesis of `AlgebraicGeometry.stalk_projective` and
`AlgebraicGeometry.stalk_isPerfect`, so it closes the gap between condition (2) of
[Stacks, Tag 03TT] and [Stacks, Tag 03TR]. -/
public theorem isFlat_moduleSheafOverConstantCoefficients_of_isConstructibleFlatModuleSheaf
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) :
    Stacks.SheafOfModules.IsFlat.{u, u + 1, max (u + 1) w r, max (u + 1) w r}
      (moduleSheafOverConstantCoefficients.{u, w, r} B X Λ F) :=
  isFlat_moduleSheafOverConstantCoefficients_of_flat_etaleModuleStalk.{u, w, r} B X Λ F
    (fun s => have := etaleModuleStalk_projective_of_isConstructibleFlatModuleSheaf B X Λ F hF s
      inferInstance)

end AlgebraicGeometry

end
