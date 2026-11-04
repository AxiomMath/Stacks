module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreSets.FiniteLocallyConstantClosure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.Modules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.Sets
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.DenseSubsiteGlobalCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DenseSubsiteCoverTransport
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.FiniteLimits
public import StacksFrontier.CategoryTheory.Sites.SlicePost.Pushforward

/-!
# Finite local constancy transports between the two small étale sites

The small étale site of a scheme `X` has two presentations in this library: the site of
Stacks 021B cut out of a chosen big étale site, `AlgebraicGeometry.SmallEtale B X.obj X.property`
with its topology `AlgebraicGeometry.SmallEtale.topology`, and Mathlib's choice-free
`AlgebraicGeometry.Scheme.Etale` with `AlgebraicGeometry.Scheme.smallEtaleTopology`. The first
embeds in the second as a dense subsite, so the two have the same sheaves
(`AlgebraicGeometry.SmallEtale.sheafEquiv`).

An equivalence of sheaf categories is *not* by itself a transport of local constancy: being
finite locally constant, or locally constant of finite type, is a condition on the restrictions
of a sheaf to the *slices* of the site, and the slices of the two presentations are different
categories. This file matches those slice conditions up, and so lets the dictionaries of
Tag 0DV5 be read on Mathlib's site, which is the site the étale-cohomology files of this library
work with.

## Main results

* `Stacks.ConstantSheaf.nonempty_constantSheaf_iso_overPullback_sheafPushforward_iff`:
  **the slice trivialization correspondence**, for an arbitrary dense subsite inclusion and
  arbitrary coefficients. The restriction of a sheaf to a slice of the subsite is the constant
  sheaf on `E` exactly when the restriction of the sheaf to the corresponding slice of the
  ambient site is.
* `AlgebraicGeometry.SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_inverse_iff` and
  `AlgebraicGeometry.SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_functor_iff`: Tag 03RW's
  condition on a sheaf of `Λ`-modules holds on one site exactly when it holds on the other.
* `AlgebraicGeometry.SmallEtale.finiteTypeLocallyConstantSheafEquiv`: the two categories of
  finite type locally constant sheaves of `Λ`-modules are equivalent.
* `AlgebraicGeometry.finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite`: **Tag 0DV5 (3)
  on Mathlib's small étale site.**
* `AlgebraicGeometry.SmallEtale.isFiniteLocallyConstant_sheafEquiv_inverse_iff`,
  `AlgebraicGeometry.SmallEtale.isFiniteLocallyConstant_sheafEquiv_functor_iff`,
  `AlgebraicGeometry.SmallEtale.finiteLocallyConstantSheafEquiv` and
  `AlgebraicGeometry.finiteLocallyConstantSetsEquivalenceEtaleSite`: the same for sheaves of
  sets, so **Tag 0DV5 (1) on Mathlib's small étale site.**

## Implementation notes

*The slice comparison.* For an object `V` of the subsite, `CategoryTheory.Over.post` of the
embedding carries the slice at `V` to the slice at the image of `V`, and it is again a dense
subsite inclusion by `Stacks.Sites.overPost_isDenseSubsite`. Two facts about it are then
combined: restriction along it takes the constant sheaf on `E` to the constant sheaf on `E`,
which is `Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso` — the application of
`CategoryTheory.Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility` to a constant
presheaf, in the form that asks only for continuity and cocontinuity; and restriction to a slice
commutes with restriction along the embedding, which is Stacks 03CF's last clause
`CategoryTheory.sheafPushforwardContinuous_overPost_eq`, a *strict equality* of functors because
both sides are precomposition with the opposite of one and the same functor. Since restriction
along the slice embedding is an equivalence, it reflects isomorphisms, and that turns the
comparison into an equivalence of the two trivialization conditions.

*From slices to covers.* With the slice conditions matched, the quantified shape of the
predicates is handled once and for all by
`Stacks.Sites.forall_exists_cover_iff_of_isDenseSubsite`, which needs only that each
trivialization condition is inherited along arrows —
`Stacks.ConstantSheaf.IsConstantFGOver.restrict` for modules and
`Stacks.ConstantSheaf.IsConstantFiniteOver.restrict` for sets.

*Universes.* Both presentations have objects in `Type (u + 1)` and morphisms in `Type u`, so the
index type `Type (u + 1)` of the covering families of the predicates is the same for both, and
the coefficient universes of Tag 0DV5 — `ModuleCat.{u + 1} Λ` and `Type (u + 1)` — are the
universe `max (u + 1) u w` at `w = u + 1` on either site. Sheafification on the slices of
Mathlib's site is therefore `Stacks.ConstantSheaf.hasSheafify_over_moduleCat` for modules and a
Mathlib instance for sets; no essential smallness of `AlgebraicGeometry.Scheme.Etale` is needed
or available. The `HasLimitsOfSize.{u, u}` hypothesis of
`AlgebraicGeometry.SmallEtale.sheafEquiv` is met by `ModuleCat.hasLimitsOfSize`, made a local
instance here because its `UnivLE` form is a lemma rather than an instance.

## References

* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 021E](https://stacks.math.columbia.edu/tag/021E)
* [Stacks Project, Tag 03CF](https://stacks.math.columbia.edu/tag/03CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped FintypeCatDiscrete

namespace Stacks.ConstantSheaf

universe v u v' u' w a r

section OverPost

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  [G.IsDenseSubsite J K] (A : Type a) [Category.{w} A] (V : C)
  [HasWeakSheafify (J.over V) A] [HasWeakSheafify (K.over (G.obj V)) A]
  [∀ Y : (Over (G.obj V))ᵒᵖ,
    HasLimitsOfShape (StructuredArrow Y (Over.post (X := V) G).op) A]

attribute [local instance] Stacks.Sites.overPost_isDenseSubsite

/-- **A trivialization on a slice of a dense subsite is a trivialization on the corresponding
slice of the ambient site.** Let `G` exhibit `(C, J)` as a dense subsite of `(D, K)` and let `F`
be a sheaf on `(D, K)`. Then the restriction of `F` to `C/V`, read through `G`, is the constant
sheaf on `E` exactly when the restriction of `F` to `D/G(V)` is.

Both sides are compared inside `D/G(V)`: restriction along `Over.post G` takes the constant sheaf
on `E` to the constant sheaf on `E`, by
`Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso`, and takes the restriction of
`F` to `D/G(V)` to the restriction to `C/V` of the restriction of `F` along `G`, by
`CategoryTheory.sheafPushforwardContinuous_overPost_eq`, which is an equality of functors rather
than an isomorphism. Restriction along `Over.post G` is an equivalence, since `Over.post G` is
again a dense subsite inclusion, so it both preserves and reflects the isomorphism. -/
public theorem nonempty_constantSheaf_iso_overPullback_sheafPushforward_iff
    (E : A) (F : Sheaf K A) :
    Nonempty ((constantSheaf (J.over V) A).obj E ≅
        (J.overPullback A V).obj ((G.sheafPushforwardContinuous A J K).obj F)) ↔
      Nonempty ((constantSheaf (K.over (G.obj V)) A).obj E ≅
        (K.overPullback A (G.obj V)).obj F) := by
  set P := (Over.post (X := V) G).sheafPushforwardContinuous A (J.over V) (K.over (G.obj V))
  have hsq : (J.overPullback A V).obj ((G.sheafPushforwardContinuous A J K).obj F) =
      P.obj ((K.overPullback A (G.obj V)).obj F) := rfl
  have hconst : (constantSheaf (J.over V) A).obj E ≅
      P.obj ((constantSheaf (K.over (G.obj V)) A).obj E) :=
    ((Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso (J.over V)
      (K.over (G.obj V)) (Over.post (X := V) G) A).app E).symm
  exact ⟨fun ⟨e⟩ ↦ ⟨P.preimageIso (hconst.symm ≪≫ e ≪≫ eqToIso hsq)⟩,
    fun ⟨e⟩ ↦ ⟨hconst ≪≫ P.mapIso e ≪≫ eqToIso hsq.symm⟩⟩

end OverPost

end Stacks.ConstantSheaf

namespace AlgebraicGeometry

open Stacks.ConstantSheaf

universe u r

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

attribute [local instance] ModuleCat.hasLimitsOfSize
attribute [local instance] Stacks.Sites.overPost_isDenseSubsite

/-! ### The instances the two presentations need at the coefficients of Tag 0DV5 -/

section Instances

variable (Λ : Type r) [Ring Λ]

/-- **Sheafification of presheaves of `Λ`-modules on a slice of Mathlib's small étale site.** The
module universe `u + 1` contains the universes of the site, so
`Stacks.ConstantSheaf.hasSheafify_over_moduleCat` applies with its section universe taken to be
`u + 1`. This is the companion of
`AlgebraicGeometry.hasWeakSheafify_smallEtaleOver_moduleCat` for the other presentation. -/
public instance hasWeakSheafify_etaleSiteOver_moduleCat (W : X.obj.Etale) :
    HasWeakSheafify (X.obj.smallEtaleTopology.over W) (ModuleCat.{u + 1} Λ) :=
  letI := hasSheafify_over_moduleCat.{u + 1, u, r, u + 1} X.obj.smallEtaleTopology Λ W
  inferInstance

/-- The limits of the comma categories of the slice embedding exist in `ModuleCat.{u + 1} Λ`:
the slice of the small étale site of Stacks 021B is essentially small, since that site is, so
the comma category is too and `max (u + 1) u`-sized limits are enough. -/
public instance hasLimitsOfShape_overPost_toEtaleSite_moduleCat
    (V : SmallEtale B X.obj X.property)
    (Y : (Over ((SmallEtale.toEtaleSite B X.obj X.property).obj V))ᵒᵖ) :
    HasLimitsOfShape
      (StructuredArrow Y (Over.post (X := V) (SmallEtale.toEtaleSite B X.obj X.property)).op)
      (ModuleCat.{u + 1} Λ) :=
  haveI := Stacks.essentiallySmall_over.{_, _, u} V
  hasLimitsOfShape_of_essentiallySmall.{u} _ _

end Instances

/-- A property closed under isomorphisms holds at `e.inverse (e.functor F)` iff it holds at `F`. -/
private theorem prop_inverse_functor_obj_iff {C D : Type*} [Category C] [Category D] (e : C ≌ D)
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] (F : C) :
    P (e.inverse.obj (e.functor.obj F)) ↔ P F :=
  P.prop_iff_of_iso (e.unitIso.app F).symm

/-! ### Sheaves of modules: Tag 03RW's condition transports -/

namespace SmallEtale

section Modules

variable (Λ : Type r) [Ring Λ]

/-- **The slice trivialization correspondence for the two small étale sites, with `Λ`-module
coefficients.** A sheaf of `Λ`-modules on Mathlib's small étale site becomes, on the slice at
the image of `V`, the constant sheaf on a finitely generated module exactly when its restriction
to the site of Stacks 021B does so on the slice at `V`. -/
public theorem isConstantFGOver_sheafEquiv_inverse_iff
    (F : Sheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V : SmallEtale B X.obj X.property) :
    IsConstantFGOver.{u, u + 1, u + 1, r} (topology B X.obj X.property) Λ V
        ((sheafEquiv B X.obj X.property (ModuleCat.{u + 1} Λ)).inverse.obj F) ↔
      IsConstantFGOver.{u, u + 1, u + 1, r} X.obj.smallEtaleTopology Λ
        ((toEtaleSite B X.obj X.property).obj V) F :=
  exists_congr fun E ↦ and_congr_right fun _ ↦
    nonempty_constantSheaf_iso_overPullback_sheafPushforward_iff
      (topology B X.obj X.property) X.obj.smallEtaleTopology
      (toEtaleSite B X.obj X.property) (ModuleCat.{u + 1} Λ) V E F

/-- **Tag 03RW's condition on a sheaf of `Λ`-modules transports to the site of Stacks 021B.**
The restriction along the embedding of a sheaf of `Λ`-modules on Mathlib's small étale site is
locally constant of finite type exactly when the sheaf is.

The slice conditions correspond by
`AlgebraicGeometry.SmallEtale.isConstantFGOver_sheafEquiv_inverse_iff`, each is inherited along
arrows by `Stacks.ConstantSheaf.IsConstantFGOver.restrict`, and
`Stacks.Sites.forall_exists_cover_iff_of_isDenseSubsite` turns that into the comparison of the
two covering conditions. -/
public theorem isFiniteTypeLocallyConstant_sheafEquiv_inverse_iff
    (F : Sheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsFiniteTypeLocallyConstant Λ (topology B X.obj X.property)
        ((sheafEquiv B X.obj X.property (ModuleCat.{u + 1} Λ)).inverse.obj F) ↔
      IsFiniteTypeLocallyConstant Λ X.obj.smallEtaleTopology F :=
  Stacks.Sites.forall_exists_cover_iff_of_isDenseSubsite
    (topology B X.obj X.property) X.obj.smallEtaleTopology (toEtaleSite B X.obj X.property)
    (fun g h ↦ IsConstantFGOver.restrict g h) (fun g h ↦ IsConstantFGOver.restrict g h)
    (isConstantFGOver_sheafEquiv_inverse_iff B X Λ F)

/-- **Tag 03RW's condition on a sheaf of `Λ`-modules transports to Mathlib's small étale site.**
A sheaf of `Λ`-modules on the site of Stacks 021B is locally constant of finite type exactly
when the sheaf on Mathlib's small étale site that corresponds to it is. -/
public theorem isFiniteTypeLocallyConstant_sheafEquiv_functor_iff
    (F : Sheaf (topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) :
    IsFiniteTypeLocallyConstant Λ X.obj.smallEtaleTopology
        ((sheafEquiv B X.obj X.property (ModuleCat.{u + 1} Λ)).functor.obj F) ↔
      IsFiniteTypeLocallyConstant Λ (topology B X.obj X.property) F := by
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (fun F : Sheaf (topology B X.obj X.property) (ModuleCat.{u + 1} Λ) ↦
        IsFiniteTypeLocallyConstant Λ (topology B X.obj X.property) F) :=
    isClosedUnderIsomorphisms_isFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, u + 1, r}
      (topology B X.obj X.property) Λ
  rw [← isFiniteTypeLocallyConstant_sheafEquiv_inverse_iff B X Λ
    ((sheafEquiv B X.obj X.property (ModuleCat.{u + 1} Λ)).functor.obj F)]
  exact prop_inverse_functor_obj_iff _ _ F

/-- **The finite type locally constant sheaves of `Λ`-modules of the two small étale sites are
the same category.** The equivalence of sheaf categories restricts to the two full subcategories
because `AlgebraicGeometry.SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_functor_iff` says
that the condition on Mathlib's site pulls back along it to the condition on the site of
Stacks 021B. -/
public noncomputable def finiteTypeLocallyConstantSheafEquiv :
    ObjectProperty.FullSubcategory
        (fun F : Sheaf (topology B X.obj X.property) (ModuleCat.{u + 1} Λ) ↦
          IsFiniteTypeLocallyConstant Λ (topology B X.obj X.property) F) ≌
      ObjectProperty.FullSubcategory
        (fun F : Sheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
          IsFiniteTypeLocallyConstant Λ X.obj.smallEtaleTopology F) :=
  haveI : ObjectProperty.IsClosedUnderIsomorphisms
      (fun F : Sheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
        IsFiniteTypeLocallyConstant Λ X.obj.smallEtaleTopology F) :=
    isClosedUnderIsomorphisms_isFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, u + 1, r}
      X.obj.smallEtaleTopology Λ
  Equivalence.congrFullSubcategory (sheafEquiv B X.obj X.property (ModuleCat.{u + 1} Λ))
    (funext fun F ↦ propext (isFiniteTypeLocallyConstant_sheafEquiv_functor_iff B X Λ F))

end Modules

/-! ### Sheaves of sets: finite local constancy transports -/

section Sets

/-- **The slice trivialization correspondence for the two small étale sites, with coefficients in
sets.** A sheaf of sets on Mathlib's small étale site becomes, on the slice at the image of `V`,
the constant sheaf on a finite set exactly when its restriction to the site of Stacks 021B does
so on the slice at `V`. -/
public theorem isConstantFiniteOver_sheafEquiv_inverse_iff
    (F : Sheaf X.obj.smallEtaleTopology (Type (u + 1)))
    (V : SmallEtale B X.obj X.property) :
    IsConstantFiniteOver.{u, u + 1, u + 1} (topology B X.obj X.property) V
        ((sheafEquiv B X.obj X.property (Type (u + 1))).inverse.obj F) ↔
      IsConstantFiniteOver.{u, u + 1, u + 1} X.obj.smallEtaleTopology
        ((toEtaleSite B X.obj X.property).obj V) F :=
  exists_congr fun E ↦ and_congr_right fun _ ↦
    nonempty_constantSheaf_iso_overPullback_sheafPushforward_iff
      (topology B X.obj X.property) X.obj.smallEtaleTopology
      (toEtaleSite B X.obj X.property) (Type (u + 1)) V E F

/-- **Finite local constancy of a sheaf of sets transports to the site of Stacks 021B.** -/
public theorem isFiniteLocallyConstant_sheafEquiv_inverse_iff
    (F : Sheaf X.obj.smallEtaleTopology (Type (u + 1))) :
    IsFiniteLocallyConstant (topology B X.obj X.property)
        ((sheafEquiv B X.obj X.property (Type (u + 1))).inverse.obj F) ↔
      IsFiniteLocallyConstant X.obj.smallEtaleTopology F := by
  have h := Stacks.Sites.forall_exists_cover_iff_of_isDenseSubsite
    (topology B X.obj X.property) X.obj.smallEtaleTopology (toEtaleSite B X.obj X.property)
    (T := fun V ↦ IsConstantFiniteOver.{u, u + 1, u + 1} (topology B X.obj X.property) V
      ((sheafEquiv B X.obj X.property (Type (u + 1))).inverse.obj F))
    (T' := fun W ↦ IsConstantFiniteOver.{u, u + 1, u + 1} X.obj.smallEtaleTopology W F)
    (fun g hh ↦ IsConstantFiniteOver.restrict _ g hh)
    (fun g hh ↦ IsConstantFiniteOver.restrict _ g hh)
    (isConstantFiniteOver_sheafEquiv_inverse_iff B X F)
  exact ⟨fun hF ↦ ⟨h.1 hF.exists_finite_cover⟩, fun hF ↦ ⟨h.2 hF.exists_finite_cover⟩⟩

/-- **Finite local constancy of a sheaf of sets transports to Mathlib's small étale site.** -/
public theorem isFiniteLocallyConstant_sheafEquiv_functor_iff
    (F : Sheaf (topology B X.obj X.property) (Type (u + 1))) :
    IsFiniteLocallyConstant X.obj.smallEtaleTopology
        ((sheafEquiv B X.obj X.property (Type (u + 1))).functor.obj F) ↔
      IsFiniteLocallyConstant (topology B X.obj X.property) F := by
  rw [← isFiniteLocallyConstant_sheafEquiv_inverse_iff B X
    ((sheafEquiv B X.obj X.property (Type (u + 1))).functor.obj F)]
  exact prop_inverse_functor_obj_iff _ _ F

/-- **The finite locally constant sheaves of sets of the two small étale sites are the same
category.** -/
public noncomputable def finiteLocallyConstantSheafEquiv :
    FiniteLocallyConstantSheaf B X ≌
      ObjectProperty.FullSubcategory
        (fun F : Sheaf X.obj.smallEtaleTopology (Type (u + 1)) ↦
          IsFiniteLocallyConstant X.obj.smallEtaleTopology F) :=
  Equivalence.congrFullSubcategory (sheafEquiv B X.obj X.property (Type (u + 1)))
    (funext fun F ↦ propext (isFiniteLocallyConstant_sheafEquiv_functor_iff B X F))

end Sets

end SmallEtale

/-! ### Tag 0DV5 on Mathlib's small étale site -/

section FundamentalGroup

variable [ConnectedSpace X.obj] (x : GeometricPoint X.obj)

/-- **Stacks Project, Tag 0DV5, part (3), on Mathlib's small étale site.** For a connected
scheme `X` with a geometric point `x` and a finite ring `Λ`, the finite type locally constant
sheaves of `Λ`-modules on `AlgebraicGeometry.Scheme.smallEtaleTopology` are equivalent to the
finite `Λ`-modules endowed with a commuting continuous action of `π₁(X, x)`.

This is `AlgebraicGeometry.finiteTypeLocallyConstantModuleSheafEquivalence`, which is stated on
the small étale site of Stacks 021B, read through
`AlgebraicGeometry.SmallEtale.finiteTypeLocallyConstantSheafEquiv`. -/
public noncomputable def finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite
    (Λ : Type r) [Ring Λ] [Finite Λ] :
    ObjectProperty.FullSubcategory
        (fun F : Sheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
          IsFiniteTypeLocallyConstant Λ X.obj.smallEtaleTopology F) ≌
      Stacks.GroupCohomology.FiniteTypeContinuousModule.{r, u + 1, u + 1} Λ
        (EtaleFundamentalGroup X.obj x) :=
  (SmallEtale.finiteTypeLocallyConstantSheafEquiv B X Λ).symm.trans
    (finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ)

/-- **Stacks Project, Tag 0DV5, part (1), on Mathlib's small étale site.** For a connected
scheme `X` with a geometric point `x`, the finite locally constant sheaves of sets on
`AlgebraicGeometry.Scheme.smallEtaleTopology` are equivalent to the finite sets with a
continuous action of `π₁(X, x)`.

This is `AlgebraicGeometry.finiteLocallyConstantSetsEquivalence` read through
`AlgebraicGeometry.SmallEtale.finiteLocallyConstantSheafEquiv`. -/
public noncomputable def finiteLocallyConstantSetsEquivalenceEtaleSite :
    ObjectProperty.FullSubcategory
        (fun F : Sheaf X.obj.smallEtaleTopology (Type (u + 1)) ↦
          IsFiniteLocallyConstant X.obj.smallEtaleTopology F) ≌
      ContAction FintypeCat.{u + 1} (EtaleFundamentalGroup X.obj x) :=
  (SmallEtale.finiteLocallyConstantSheafEquiv B X).symm.trans
    (finiteLocallyConstantSetsEquivalence B X x)

end FundamentalGroup

end AlgebraicGeometry

end
