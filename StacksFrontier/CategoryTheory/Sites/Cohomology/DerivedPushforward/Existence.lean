module

public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardComp
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelianSmall
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion
public import StacksCore.Tactic.StacksAttribute

/-!
# The unbounded total direct image of a morphism of ringed topoi

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi. Stacks 07A5 observes that
the category `Mod(O_C)` is Grothendieck abelian, so that every complex of `O_C`-modules admits a
K-injective resolution (Stacks 079P), and deduces from Stacks 070K that *every* functor out of
the unbounded homotopy category `K(Mod(O_C))` has a right derived functor on the unbounded
derived category `D(O_C)`. Applied to degreewise direct image this produces the total direct
image
`Rf_* : D(O_C) ⟶ D(O_D)`,
which is the functor the adjunction of Stacks 07A6 is about.

This file supplies the Grothendieck-abelian form of that existence statement, and its
instantiation at degreewise direct image.

## Main results

* `Stacks.Cohomology.UnboundedComplexes.hasPointwiseRightDerivedFunctor`: for `A` Grothendieck
  abelian, every functor out of `K(A)` has a pointwise right derived functor with respect to the
  quasi-isomorphisms, and in particular a right derived functor `D(A) ⥤ H`.
* `Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective`: that derived functor is
  computed by K-injective complexes.
* `Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_comp`: consequently such a right
  derived functor is *absolute* — it stays a right derived functor after composing with any
  functor.
* `Stacks.Cohomology.UnboundedComplexes.derivedAdjunction`: Stacks 09T5 on the unbounded
  derived category, in the form `CategoryTheory.Adjunction.derived` takes, with the
  absoluteness of the right derived functor discharged and only that of the left derived one
  left as a hypothesis.
* `Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy_hasRightDerivedFunctor`: the
  existence of `Rf_*` on the unbounded derived category.

## Main definitions

* `Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy`: degreewise direct image,
  followed by the localization `K(Mod(O_D)) ⥤ D(O_D)`.
* `Stacks.Cohomology.DerivedPushforward.derivedPushforward`: the total right derived functor
  `Rf_*` of that functor.

## Implementation notes

Grothendieck abelianness of `Mod(O_C)` in the universe `w` of the sections is *not* a
consequence of the hypotheses under which `Mod(O_C)` is abelian: the separator
`⨁_{U ∈ Ob(C)} j_{U!}O_U` of Stacks 03EV is indexed by the objects of the site and the hom types
involve its morphisms, so it exists in `Mod(O_C)` only when the objects and the morphisms of the
site are `w`-small. It is therefore assumed, as
`CategoryTheory.IsGrothendieckAbelian.{w} X.Modules`, and only of the *source* ringed topos,
which is where the K-injective resolutions are taken.

The hypothesis is *not* spelled as the two `UnivLE.{u, w}`, `UnivLE.{v, w}` that
`Stacks.SheafOfModules.Small.isGrothendieckAbelian_sheafOfModules` asks for, although that
instance is the usual way to meet it and does so with no extra work wherever the two hold. The
reason is that `UnivLE` is a strictly narrower route: the small étale ringed topos of an
algebraic space is `AlgebraicGeometry.RingedTopos.{u, u + 1, u}` — site objects in `Type (u + 1)`
while sections live in `Type u` — so it asks the unsynthesizable `UnivLE.{u + 1, u}`, and yet its
modules *are* Grothendieck abelian at `u`, by essential smallness of the small étale site
(`AlgebraicGeometry.Space.isGrothendieckAbelian_modules`). Taking the conclusion of the instance
as the hypothesis is what lets `Rf_*` and the adjunction of Stacks 07A6 reach those ringed topoi
at all; nothing is lost, since a consumer holding the two `UnivLE` instances has the
`IsGrothendieckAbelian` instance synthesized for it.

The module universes of the two ringed topoi are independent here, as they are for the direct
image itself.

## References

* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Stacks.Cohomology.UnboundedComplexes

universe w v u v₂ u₂ v₃ u₃ v₄ u₄

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]

/-- **Stacks 07A5**, first assertion: over a Grothendieck abelian category every functor on the
unbounded homotopy category has a pointwise right derived functor relative to the
quasi-isomorphisms. In particular `F.HasRightDerivedFunctor` holds, so that the right derived
functor `RF : D(A) ⥤ H` exists; this is Stacks 070K applied to the K-injective resolutions of
Stacks 079P, `Stacks.Injectives.exists_kInjective_resolution_of_grothendieck`. -/
@[sga "4 XVII 4.1.2" "partial"]
theorem hasPointwiseRightDerivedFunctor {H : Type u₂} [Category.{v₂} H]
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H) :
    F.HasPointwiseRightDerivedFunctor (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{v, v₂,
    v₂, u, u₂, u₂} F Stacks.Injectives.exists_kInjective_resolution_of_grothendieck).1

/-- **Stacks 07A5**, second assertion: the right derived functor of a functor on the unbounded
homotopy category of a Grothendieck abelian category is computed by K-injective complexes, in
the sense that its unit is invertible there. -/
theorem isIso_app_of_isKInjective {H : Type u₂} [Category.{v₂} H]
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H) {D : Type u₃} [Category.{v₃} D]
    (L : HomotopyCategory A (ComplexShape.up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] (RF : D ⥤ H)
    (α : F ⟶ L ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (I : CochainComplex A ℤ) (hI : I.IsKInjective) :
    IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{v, v₂,
    v₃, u, u₂, u₃} F Stacks.Injectives.exists_kInjective_resolution_of_grothendieck).2 L RF α I hI

/-- Every object of the unbounded derived category of a Grothendieck abelian category is
isomorphic to the image of a K-injective complex. -/
theorem exists_isKInjective_iso {D : Type u₃} [Category.{v₃} D]
    (L : HomotopyCategory A (ComplexShape.up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] (Z : D) :
    ∃ I : CochainComplex A ℤ, I.IsKInjective ∧
      Nonempty (L.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) ≅ Z) := by
  have := Localization.essSurj L (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  obtain ⟨K, hK⟩ := HomotopyCategory.quotient_obj_surjective (L.objPreimage Z)
  obtain ⟨I, i, hI, hi⟩ := Stacks.Injectives.exists_kInjective_resolution_of_grothendieck K
  have hmem : HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map i) := by
    rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff]
  exact ⟨I, hI, ⟨(Localization.isoOfHom L _ _ hmem).symm ≪≫
    eqToIso (congrArg L.obj hK) ≪≫ L.objObjPreimageIso Z⟩⟩

/-- **Right derived functors over a Grothendieck abelian category are absolute.** If `RΦ`,
with `β : Φ ⟶ L ⋙ RΦ`, is the right derived functor of a functor `Φ` on the unbounded homotopy
category of a Grothendieck abelian category, then for *every* functor `G` out of its target the
composite `RΦ ⋙ G` is the right derived functor of `Φ ⋙ G`.

This is what makes the derived adjunction of Stacks 09T5 available on the unbounded derived
category: `CategoryTheory.Adjunction.derived` asks for exactly this of the right derived
functor in play. The reason it holds is that `RΦ` is computed by K-injective complexes
(`isIso_app_of_isKInjective`), and so is any right derived functor of `Φ ⋙ G`, which exists by
`hasPointwiseRightDerivedFunctor`; the comparison between the two is therefore invertible at
the image of every K-injective complex, and every object of the derived category is isomorphic
to such an image. -/
theorem isRightDerivedFunctor_comp {H : Type u₂} [Category.{v₂} H] {H' : Type u₄}
    [Category.{v₄} H'] (Φ : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H) {D : Type u₃}
    [Category.{v₃} D] (L : HomotopyCategory A (ComplexShape.up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] (RΦ : D ⥤ H)
    (β : Φ ⟶ L ⋙ RΦ)
    [RΦ.IsRightDerivedFunctor β (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (G : H ⥤ H') :
    (RΦ ⋙ G).IsRightDerivedFunctor
      (Functor.whiskerRight β G ≫ (Functor.associator L RΦ G).hom)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  have hpt : (Φ ⋙ G).HasPointwiseRightDerivedFunctor
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := hasPointwiseRightDerivedFunctor _
  rw [Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
    ((Φ ⋙ G).totalRightDerived L (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    ((Φ ⋙ G).totalRightDerivedUnit L (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)), NatTrans.isIso_iff_isIso_app]
  intro Z
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_iso L Z
  rw [NatTrans.isIso_app_iff_of_iso _ e.symm]
  have h₁ := isIso_app_of_isKInjective (Φ ⋙ G) L _
    ((Φ ⋙ G).totalRightDerivedUnit L (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) I hI
  have h₂ := isIso_app_of_isKInjective Φ L RΦ β I hI
  have : IsIso ((Functor.whiskerRight β G ≫ (Functor.associator L RΦ G).hom).app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) := by
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Category.comp_id]
    infer_instance
  exact IsIso.of_isIso_fac_left (Functor.rightDerived_fac_app _ _ _ _ _ _)

section Adjunction

variable {C : Type u₂} [Category.{v₂} C] {G : C ⥤ HomotopyCategory A (ComplexShape.up ℤ)}
  {F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ C} (adj : G ⊣ F) (W : MorphismProperty C)
  {D : Type u₃} [Category.{v₃} D] {L : C ⥤ D} [L.IsLocalization W]
  {E : Type u₄} [Category.{v₄} E] {M : HomotopyCategory A (ComplexShape.up ℤ) ⥤ E}
  [M.IsLocalization (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  {LG : D ⥤ E} {RF : E ⥤ D} (α : L ⋙ LG ⟶ G ⋙ M) (β : F ⋙ L ⟶ M ⋙ RF)
  [LG.IsLeftDerivedFunctor α W]
  [RF.IsRightDerivedFunctor β (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [(LG ⋙ RF).IsLeftDerivedFunctor
    ((Functor.associator L LG RF).inv ≫ Functor.whiskerRight α RF) W]

/-- **Stacks 09T5** on the unbounded derived category of a Grothendieck abelian category. Let
`G ⊣ F` be an adjunction whose right adjoint `F` is defined on the unbounded homotopy category
of a Grothendieck abelian category `A`, let `LG` be a left derived functor of `G` relative to a
class `W` on the source and `RF` a right derived functor of `F` relative to the
quasi-isomorphisms of `K(A)`. Then `LG` is left adjoint to `RF`.

`CategoryTheory.Adjunction.derived` needs the two derived functors to be *absolute*. For `RF`
that is automatic, by `isRightDerivedFunctor_comp`, because `A` is Grothendieck abelian; only
the absoluteness of `LG` is left as a hypothesis, and that is what a construction of `LG` by
resolutions supplies (`CategoryTheory.LeftDerivedByResolutions`). -/
@[sga "4 XVIII 3.1.5" "more general"]
noncomputable def derivedAdjunction : LG ⊣ RF :=
  letI := isRightDerivedFunctor_comp (F ⋙ L) M RF β LG
  adj.derived W (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) α β

/-- The unit of `derivedAdjunction` is the one induced by the unit of `adj`. -/
theorem derivedAdjunction_unit_app (Z : C) :
    (derivedAdjunction adj W α β).unit.app (L.obj Z) ≫ RF.map (α.app Z) =
      L.map (adj.unit.app Z) ≫ β.app (G.obj Z) :=
  adj.derivedη_fac_app W α β Z

/-- The counit of `derivedAdjunction` is the one induced by the counit of `adj`. -/
theorem derivedAdjunction_counit_app (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    LG.map (β.app K) ≫ (derivedAdjunction adj W α β).counit.app (M.obj K) =
      α.app (F.obj K) ≫ M.map (adj.counit.app K) :=
  have := isRightDerivedFunctor_comp (F ⋙ L) M RF β LG
  adj.derivedε_fac_app (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) α β K

end Adjunction

end Stacks.Cohomology.UnboundedComplexes

namespace Stacks.Cohomology.DerivedPushforward

universe w w' v u v' u'

open AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w'}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]

attribute [local instance] HasDerivedCategory.standard

/-- Degreewise direct image of complexes of sheaves of modules along a morphism of ringed
topoi, read as a functor from the unbounded homotopy category of the source to the unbounded
derived category of the target. Its right derived functor is `Rf_*`. -/
abbrev pushforwardOnHomotopy (f : RingedToposHom X Y) :
    HomotopyCategory (SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)) :=
  (pushforwardModules f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

variable [IsGrothendieckAbelian.{w} (SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O))]

/-- **Stacks 07A5** for the direct image: degreewise direct image has a right derived functor
on the *unbounded* derived category, i.e. the total direct image
`Rf_* : D(O_C) ⥤ D(O_D)` of Stacks 07A5(3) exists.

Sheaves of `O_C`-modules form a Grothendieck abelian category, so every complex has a
K-injective resolution and Stacks 070K applies. -/
instance pushforwardOnHomotopy_hasRightDerivedFunctor (f : RingedToposHom X Y) :
    (pushforwardOnHomotopy f).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)) :=
  UnboundedComplexes.hasPointwiseRightDerivedFunctor _

/-- The unbounded total direct image `Rf_*`, the right derived functor of degreewise direct
image. -/
abbrev derivedPushforward (f : RingedToposHom X Y) :
    DerivedCategory (SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)) :=
  (pushforwardOnHomotopy f).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))

end Stacks.Cohomology.DerivedPushforward

end
