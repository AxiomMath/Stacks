module

public import Mathlib.CategoryTheory.Sites.Point.Over
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficientStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatIsFlat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flatness over the constant coefficient ring sheaf is inherited by every slice

`AlgebraicGeometry.isFlat_moduleSheafOverConstantCoefficients_of_isConstructibleFlatModuleSheaf`
reads flatness of a sheaf of `Λ`-modules over the constant coefficient ring sheaf of Tag 03TR off
its étale stalks, by Stacks 05VC applied to the conservative family of lifted geometric points.
This file does the same over a slice of the small étale site: the stalk at a lift of a point to
the slice is again the étale stalk, so the very same flat stalks give flatness of the restricted
sheaf of modules on the localized ringed site.

This is Stacks 0E8J — restriction to an object of a ringed site preserves flatness — for the
sheaves of modules coming from sheaves of `Λ`-modules, at universes where `0E8J` itself is not
available: `Stacks.SheafOfModules.FlatRestriction.isFlat_over` runs through the reflection of
exactness by extension by zero (Stacks 0E8G) and so is pinned to a ringed site whose objects,
morphisms and ring sections lie in one universe, whereas
`AlgebraicGeometry.constantCoefficientRingedSite` is an
`AlgebraicGeometry.RingedSite.{u + 1, u, max (u + 1) w r}`. The route through the stalks has no
such pin, the stalk comparisons of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ConstantCoefficientStalk.lean` being stated at the
universes of that very site.

## Main results

* `AlgebraicGeometry.isConservativeFamilyOfPoints_uliftGeometricSitePointOver`: the lifts to a
  slice of the universe lifts of the geometric points of `X` form a conservative family of points
  of that slice.
* `AlgebraicGeometry.etaleModuleStalkOverFiberIso`: the étale stalk at a geometric point is the
  stalk, at a lift of that point to a slice, of the restriction to that slice of the associated
  sheaf of modules over the constant coefficient ring sheaf.
* `AlgebraicGeometry.isFlatModuleStalk_over_of_flat_etaleModuleStalk`: a flat étale stalk is a
  flat stalk of that restriction.
* `AlgebraicGeometry.isFlat_over_moduleSheafOverConstantCoefficients_of_forall_flat`: **a sheaf
  of `Λ`-modules with flat étale stalks becomes, on every slice of the small étale site, a flat
  sheaf of modules over the restricted constant coefficient ring sheaf.**

## Implementation notes

Conservativity on the slice is Mathlib's
`CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.over`, whose smallness hypothesis the
family here satisfies: it is indexed by the points of the underlying space of `X`, a `Type u`.
Its three sheafification hypotheses are stated for presheaves of *sets* at the universe
`max (u + 1) w r` of the comparison, and are discharged from essential smallness of the small
étale site and of its slices, by `CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_type`
and `Stacks.Sites.SheafSection.hasSheafify_type_of_essentiallySmall`; the same manoeuvre as in
`AlgebraicGeometry.isConservativeFamilyOfPoints_uliftGeometricSitePoint`, which supplies the
family downstairs.

Flatness of the stalk over the stalk of the restricted structure sheaf, rather than over `Λ`, is
read through `AlgebraicGeometry.constantCoefficientRingOverFiberEquiv` by
`AlgebraicGeometry.flat_of_semilinear_equiv`, exactly as
`AlgebraicGeometry.isFlatModuleStalk_of_flat_etaleModuleStalk` does on the total site; the
intervening universe lift of the sections of the étale stalk is harmless, a universe lift of a
flat module being flat.

No hypothesis on `X`, no Noetherian hypothesis on `Λ` and no constructibility enters: only
flatness of the étale stalks. Constructible flat sheaves have *projective* étale stalks, by
`AlgebraicGeometry.etaleModuleStalk_projective_of_isConstructibleFlatModuleSheaf`, which is how
Tag 03TT reaches the hypothesis here.

## References

* [Stacks Project, Tag 03TR](https://stacks.math.columbia.edu/tag/03TR)
* [Stacks Project, Tag 05VC](https://stacks.math.columbia.edu/tag/05VC)
* [Stacks Project, Tag 0E8J](https://stacks.math.columbia.edu/tag/0E8J)
* [Stacks Project, Tag 04H2](https://stacks.math.columbia.edu/tag/04H2)
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
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective

/-! ### The conservative family of points of a slice -/

set_option linter.checkUnivs false in
/-- **The lifts to a slice of the universe lifts of the geometric points of `X` are a
conservative family of points of that slice.**

`AlgebraicGeometry.isConservativeFamilyOfPoints_uliftGeometricSitePoint` is the family on the
small étale site itself, at the universe `max (u + 1) w r` containing the site, the coefficient
ring and the module sections; it is indexed by the points of the underlying space of `X`, hence
small, so Mathlib's `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.over` lifts it to
the slice over any object. -/
@[sga "4 IV 6.7.4" "special case"]
public theorem isConservativeFamilyOfPoints_uliftGeometricSitePointOver
    (V : SmallEtale B X.obj X.property) :
    ObjectProperty.IsConservativeFamilyOfPoints
      (ObjectProperty.ofObj (fun (ψ : Σ (Φ :
          (ObjectProperty.ofObj (fun x : ↥X.obj =>
            (geometricSitePoint B X (.ofPoint X.obj x)).ulift.{max (u + 1) w r})).FullSubcategory),
          Φ.obj.fiber.obj V) => ψ.1.obj.over ψ.2)) := by
  have h₁ : (SmallEtale.topology B X.obj X.property).WEqualsLocallyBijective
      (Type (max (u + 1) w r)) :=
    GrothendieckTopology.wEqualsLocallyBijective_type _
  have h₂ : HasSheafify (SmallEtale.topology B X.obj X.property) (Type (max (u + 1) w r)) :=
    Stacks.Sites.SheafSection.hasSheafify_type_of_essentiallySmall _
  have h₃ : HasSheafify ((SmallEtale.topology B X.obj X.property).over V)
      (Type (max (u + 1) w r)) :=
    Stacks.Sites.SheafSection.hasSheafify_type_of_essentiallySmall _
  exact ObjectProperty.IsConservativeFamilyOfPoints.over
    (isConservativeFamilyOfPoints_uliftGeometricSitePoint.{u, w, r} B X) V

/-! ### The stalk on a slice is the étale stalk -/

/-- **The étale stalk at a geometric point is the stalk, at a lift of that point to the slice
over `V`, of the restriction to that slice of the sheaf of modules over the constant coefficient
ring sheaf**, as `Λ`-modules through
`AlgebraicGeometry.constantCoefficientRingOverFiberEquiv`, after lifting the sections of the
étale stalk into the universe of the comparison.

This is the slice form of `AlgebraicGeometry.etaleModuleStalkFiberIso`, and it is assembled from
the same two pieces: the collapse of the universe lift at a geometric point and the comparison
of the stalk with the fibre, here on the slice. -/
public def etaleModuleStalkOverFiberIso (s : GeometricPoint X.obj)
    {V : SmallEtale B X.obj X.property}
    (x : ((geometricSitePoint B X s).ulift.{max (u + 1) w r}).fiber.obj V)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) :
    (ModuleCat.uliftFunctor.{max (u + 1) r} Λ).obj
        ((etaleModuleStalkFunctor B X Λ s).obj F) ≅
      (ModuleCat.restrictScalars
          (constantCoefficientRingOverFiberEquiv.{u, w, r} B X Λ
            ((geometricSitePoint B X s).ulift.{max (u + 1) w r}) x).toRingHom).obj
        (Stacks.moduleStalk (((geometricSitePoint B X s).ulift.{max (u + 1) w r}).over x)
          ((constantCoefficientRingedSite.{u, w, r} B X Λ).over V).O
          ((SheafOfModules.overFunctor
              (Stacks.commRingSheafToRingSheaf.{u, u + 1, max (u + 1) w r}
                (constantCoefficientSheaf.{u, w, r} B X Λ)) V).obj
            ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).obj F))) :=
  (upliftedEtaleFiberIso.{u, w, r} B X Λ s F).symm ≪≫
    moduleSheafOverConstantCoefficientsOverFiberIso.{u, w, r} B X Λ
      ((geometricSitePoint B X s).ulift.{max (u + 1) w r}) x F

omit [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)] in
/-- **A flat étale stalk is a flat stalk of the restriction to a slice.** The stalk at a lift of
a geometric point to the slice over `V` of the restriction of the sheaf of modules over the
constant coefficient ring sheaf is the étale stalk, and the two module structures differ by the
identification `AlgebraicGeometry.constantCoefficientRingOverFiberEquiv` of the stalk of the
restricted constant coefficient ring sheaf with `Λ`. -/
public theorem isFlatModuleStalk_over_of_flat_etaleModuleStalk
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))
    (s : GeometricPoint X.obj) {V : SmallEtale B X.obj X.property}
    (x : ((geometricSitePoint B X s).ulift.{max (u + 1) w r}).fiber.obj V)
    (hflat : Module.Flat Λ ((etaleModuleStalkFunctor B X Λ s).obj F)) :
    Stacks.IsFlatModuleStalk (((geometricSitePoint B X s).ulift.{max (u + 1) w r}).over x)
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over V).O
      ((SheafOfModules.overFunctor
          (Stacks.commRingSheafToRingSheaf.{u, u + 1, max (u + 1) w r}
            (constantCoefficientSheaf.{u, w, r} B X Λ)) V).obj
        ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).obj F)) := by
  have hL : Module.Flat Λ ↑((ModuleCat.uliftFunctor.{max (u + 1) r} Λ).obj
      ((etaleModuleStalkFunctor B X Λ s).obj F)) :=
    have := hflat
    Module.Flat.ulift (R := Λ) (M := ((etaleModuleStalkFunctor B X Λ s).obj F))
  set e := constantCoefficientRingOverFiberEquiv.{u, w, r} B X Λ
    ((geometricSitePoint B X s).ulift.{max (u + 1) w r}) x with he
  set g := (etaleModuleStalkOverFiberIso.{u, w, r} B X Λ s x F).symm.toLinearEquiv with hg
  refine flat_of_semilinear_equiv e.symm g.toAddEquiv (fun c m => ?_)
  exact (congrArg g (congrArg (· • m) (e.apply_symm_apply c).symm)).trans
    (g.map_smul (e.symm c) m)

/-! ### Flatness on every slice -/

omit [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)] in
/-- **A sheaf of `Λ`-modules with flat étale stalks becomes a flat sheaf of modules on every
slice of the small étale site.**

This is Stacks 05VC on the slice over `V`, applied to the conservative family of lifts of the
universe lifts of the geometric points: at each of them the stalk of the restriction is the étale
stalk, which is flat by hypothesis.

Together with
`AlgebraicGeometry.isFlat_moduleSheafOverConstantCoefficients_of_isConstructibleFlatModuleSheaf`,
which is the statement on the total site, this is what lets a Tor-amplitude statement about a
complex of constructible flat sheaves be read on each slice of the constant coefficient ringed
site, and so lets locally finite Tor dimension in the sense of Tag 08FZ (3) be established for
it. -/
public theorem isFlat_over_moduleSheafOverConstantCoefficients_of_forall_flat
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))
    (hflat : ∀ s : GeometricPoint X.obj,
      Module.Flat Λ ((etaleModuleStalkFunctor B X Λ s).obj F))
    (V : SmallEtale B X.obj X.property) :
    Stacks.SheafOfModules.IsFlat.{u, u + 1, max (u + 1) w r, max (u + 1) w r}
      (O := ((constantCoefficientRingedSite.{u, w, r} B X Λ).over V).O)
      ((SheafOfModules.overFunctor
          (Stacks.commRingSheafToRingSheaf.{u, u + 1, max (u + 1) w r}
            (constantCoefficientSheaf.{u, w, r} B X Λ)) V).obj
        ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).obj F)) := by
  refine Stacks.isFlat_of_forall_isFlatModuleStalk
    ((constantCoefficientRingedSite.{u, w, r} B X Λ).over V).O _
    (fun (ψ : Σ (Φ : (ObjectProperty.ofObj (fun y : ↥X.obj =>
        (geometricSitePoint B X (.ofPoint X.obj y)).ulift.{max (u + 1) w r})).FullSubcategory),
        Φ.obj.fiber.obj V) => ψ.1.obj.over ψ.2)
    (isConservativeFamilyOfPoints_uliftGeometricSitePointOver.{u, w, r} B X V) (fun ψ => ?_)
  obtain ⟨⟨Φ, hΦ⟩, y⟩ := ψ
  obtain ⟨z, hz⟩ := (ObjectProperty.ofObj_iff _ Φ).1 hΦ
  subst hz
  exact isFlatModuleStalk_over_of_flat_etaleModuleStalk.{u, w, r} B X Λ F _ y
    (hflat (.ofPoint X.obj z))

end AlgebraicGeometry

end
