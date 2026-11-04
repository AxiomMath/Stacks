module

public import Mathlib.Algebra.Module.Shrink
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The internal Hom of sheaves of modules on an essentially small ringed site

For a ringed site `X : RingedSite.{u, v, w}` and sheaves of modules `A B : SheafOfModules.{m}
X.ringSheaf`, `AlgebraicGeometry.RingedSite.internalHomSheaf X A B` is a sheaf of modules in the
module universe `max u v m`: its sections over `U` are the morphisms `A|_U ⟶ B|_U` on the slice
site `X.C/U`, and a morphism of presheaves of modules on `X.C/U` is a family of linear maps
indexed by the objects of `X.C/U`, which live in `max u v`.

That raise is an artefact of the construction, not of the mathematics, as soon as the site is
essentially `m`-small: a morphism out of a presheaf on an essentially `m`-small site is
determined by its components on an `m`-small model of the site, so the sections take `m`-small
values and the whole sheaf descends to the module universe `m`. This file proves that, and
constructs the descended internal Hom.

The point is not economy of universes. `DerivedInternalHom.lean` states
`derivedSheafHomBifunctor` only at `RingedSite.{u, u, u}` with modules in `SheafOfModules.{u}`,
and explains that the collapse of the three site universes onto the module universe is forced:
the functorial K-injective resolution needs sheaves of modules to be Grothendieck abelian *in
the module universe*, and the iterated internal Hom raises that universe. On the small étale
site of a scheme the universes are `{u + 1, u, u}`, so `max (u + 1) u m = u + 1` and the
internal Hom of two `SheafOfModules.{u}` is a `SheafOfModules.{u + 1}`: the internal Hom is not
an endofunctor there and the derived bifunctor cannot be instantiated. The forcing argument is
sound but says nothing about smallness, and the small étale site *is* essentially small
(`AlgebraicGeometry.SmallEtale.essentiallySmall`), so `internalHomSheafSmall` below is an
endofunctor on exactly the sites where the problem arises.

## Main definitions

* `Stacks.shrinkPresheaf`: the sectionwise `m`-small model of a presheaf of abelian groups whose
  values are `m`-small.
* `Stacks.SheafOfModules.presheafShrink` and `Stacks.SheafOfModules.sheafShrink`: the same for a
  presheaf, resp. a sheaf, of modules, together with
  `Stacks.SheafOfModules.presheafShrinkIso` and `Stacks.SheafOfModules.sheafShrinkIso`, which
  identify the universe lift of the shrunken object with the original one. These are inverse to
  `Stacks.SheafOfModules.presheafULift` and `Stacks.SheafOfModules.moduleULift` on the
  small-valued objects.
* `AlgebraicGeometry.RingedSite.internalHomSheafSmall`: the internal Hom of two
  `SheafOfModules.{m}` on an essentially `m`-small ringed site, **as a `SheafOfModules.{m}`**.
* `AlgebraicGeometry.RingedSite.internalHomSheafSmallFunctor`: it as a functor in the second
  variable, hence an endofunctor of `SheafOfModules.{m} X.ringSheaf`.

## Main results

* `Stacks.locallySmall_presheafOfModules_of_essentiallySmall`: presheaves of modules with
  `m`-small sections on an essentially `m`-small site are locally `m`-small.
* `AlgebraicGeometry.RingedSite.small_internalHomSheaf_obj`: hence the sections of
  `internalHomSheaf X A B` are `m`-small. This is the whole content; everything after it is the
  descent of a small-valued sheaf of modules to its module universe.
* `AlgebraicGeometry.RingedSite.internalHomSheafSmallIso`:
  `moduleULift (internalHomSheafSmall X A B) ≅ internalHomSheaf X A B`, so nothing is lost: the
  descended object is the old one, read in the smaller universe.

## Implementation notes

The smallness of the sections is proved by transporting local smallness of a functor category
along the equivalence with the functor category on a small model of the source
(`CategoryTheory.Equivalence.congrLeft`), and then along the faithful functor
`PresheafOfModules.toPresheaf`. The slice site `X.C/U` is essentially small because `Over U` is
equivalent to `CostructuredArrow (𝟭 X.C) U`, for which Mathlib has the instance; the two are
definitionally the same type but carry different `Category` instances, so the equivalence
`CategoryTheory.CostructuredArrow.toOver` is needed to move between them.

The descent itself is `Shrink` applied sectionwise. Its restriction maps and module structures
are transported along `Shrink.addEquiv`, and `shrinkPresheaf` is deliberately *not* reducible:
every lemma below is stated at the folded spelling, which is the spelling that appears in goals,
and making the definition reducible unfolds the goals past the point where those lemmas match.
The sheaf condition descends because `AddCommGrpCat.uliftFunctor` reflects limits
(`CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp`).

Functoriality of `internalHomSheafSmall` in the second variable is obtained from functoriality
of `internalHomSheaf`, by conjugating with `internalHomSheafSmallIso` and taking the preimage
under the fully faithful `Stacks.SheafOfModules.moduleULift`; the functor laws then follow from
faithfulness alone.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe m t u₁ v₁ w u v

namespace Stacks

/-! ### Local smallness from essential smallness -/

/-- A functor category out of an essentially `m`-small category into a locally `m`-small
category is locally `m`-small: restriction along an equivalence with a small model of the source
is an equivalence of functor categories, and a functor category out of a small category is
locally small. -/
@[sga "4 I 1.1.1" "more general"]
theorem locallySmall_functor_of_essentiallySmall (C : Type u₁) [Category.{v₁} C]
    [EssentiallySmall.{m} C] (A : Type u) [Category.{v} A] [LocallySmall.{m} A] :
    LocallySmall.{m} (C ⥤ A) :=
  (locallySmall_congr (Equivalence.congrLeft (E := A) (equivSmallModel.{m} C))).mpr inferInstance

/-- A slice of an essentially `m`-small category is essentially `m`-small. `Over U` is the same
type as `CostructuredArrow (𝟭 C) U`, for which this is a Mathlib instance, but carries its own
`Category` instance, so the transport along `CategoryTheory.CostructuredArrow.toOver` is
needed. -/
theorem essentiallySmall_over {C : Type u₁} [Category.{v₁} C] [EssentiallySmall.{m} C] (U : C) :
    EssentiallySmall.{m} (Over U) :=
  (essentiallySmall_congr (CostructuredArrow.toOver (𝟭 C) U).asEquivalence).mp inferInstance

/-- Presheaves of modules with sections in `m` over an essentially `m`-small site are locally
`m`-small: a morphism is a natural transformation of the underlying presheaves of abelian
groups, and those form a locally `m`-small category. No hypothesis is placed on the universe of
the presheaf of rings, whose values do not enter a linear map between the sections. -/
theorem locallySmall_presheafOfModules_of_essentiallySmall {C : Type u₁} [Category.{v₁} C]
    [EssentiallySmall.{m} C] (Rp : Cᵒᵖ ⥤ RingCat.{w}) :
    LocallySmall.{m} (PresheafOfModules.{m} Rp) :=
  have := locallySmall_functor_of_essentiallySmall.{m} Cᵒᵖ AddCommGrpCat.{m}
  locallySmall_of_faithful.{m} (PresheafOfModules.toPresheaf Rp)

/-! ### Shrinking a presheaf of abelian groups with small values -/

variable {C : Type u₁} [Category.{v₁} C]

/-- The sectionwise `m`-small model of a presheaf of abelian groups whose values are `m`-small:
the sections over `X` become `Shrink (P(X))`, with the restriction maps conjugated by
`Shrink.addEquiv`. -/
def shrinkPresheaf (P : Cᵒᵖ ⥤ AddCommGrpCat.{max m t}) [∀ X, Small.{m} (P.obj X)] :
    Cᵒᵖ ⥤ AddCommGrpCat.{m} where
  obj X := AddCommGrpCat.of (Shrink.{m} (P.obj X))
  map {X Y} f := AddCommGrpCat.ofHom (AddMonoidHom.mk'
    (fun x => (Shrink.addEquiv (α := (P.obj Y : Type _))).symm
      ((P.map f).hom (Shrink.addEquiv (α := (P.obj X : Type _)) x))) (by intro a b; simp))
  map_id X := by ext x; simp
  map_comp f g := by ext x; simp

/-- Under `Shrink.addEquiv`, the restriction maps of `shrinkPresheaf P` are those of `P`. -/
@[simp]
theorem shrinkPresheaf_map_apply (P : Cᵒᵖ ⥤ AddCommGrpCat.{max m t})
    [∀ X, Small.{m} (P.obj X)] {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : (shrinkPresheaf.{m, t} P).obj X) :
    Shrink.addEquiv ((shrinkPresheaf.{m, t} P).map f x) = (P.map f).hom (Shrink.addEquiv x) :=
  (Shrink.addEquiv (α := (P.obj Y : Type _))).apply_symm_apply _

namespace SheafOfModules

/-! ### Shrinking a presheaf of modules with small values -/

variable (Rp : Cᵒᵖ ⥤ RingCat.{w}) (M : PresheafOfModules.{max m t} Rp)
  [∀ X, Small.{m} (M.obj X)]

/-- The sections of the underlying presheaf of abelian groups of `M` are `m`-small. -/
instance small_presheaf_obj (X : Cᵒᵖ) : Small.{m} (M.presheaf.obj X) :=
  inferInstanceAs (Small.{m} (M.obj X))

/-- The `Rp.obj X`-module structure on the sections of `shrinkPresheaf M.presheaf` over `X`,
transported from `M.obj X` along `Shrink.addEquiv`. -/
instance module_shrinkPresheaf (X : Cᵒᵖ) :
    Module (Rp.obj X) ((shrinkPresheaf.{m, t} M.presheaf).obj X) :=
  inferInstanceAs (Module (Rp.obj X) (Shrink.{m} (M.presheaf.obj X)))

/-- `Shrink.addEquiv` commutes with scalar multiplication on the sections of
`shrinkPresheaf M.presheaf`. -/
@[simp]
theorem shrinkPresheaf_addEquiv_smul (X : Cᵒᵖ) (r : Rp.obj X)
    (x : (shrinkPresheaf.{m, t} M.presheaf).obj X) :
    Shrink.addEquiv (r • x) = r • Shrink.addEquiv x :=
  map_smul (Shrink.linearEquiv (Rp.obj X) (M.presheaf.obj X)) r x

/-- The sectionwise `m`-small model of a presheaf of modules whose sections are `m`-small. The
restriction maps are those of `Stacks.shrinkPresheaf`, and they are semilinear because the
transported module structures are transported along the same additive equivalences. -/
def presheafShrink : PresheafOfModules.{m} Rp :=
  PresheafOfModules.ofPresheaf (shrinkPresheaf.{m, t} M.presheaf) (by
    intro X Y f r x
    apply (Shrink.addEquiv (α := (M.presheaf.obj Y : Type _))).injective
    rw [shrinkPresheaf_map_apply, shrinkPresheaf_addEquiv_smul, shrinkPresheaf_addEquiv_smul,
      shrinkPresheaf_map_apply]
    exact M.map_smul f r _)

/-- Lifting the universe of the sections of `presheafShrink M` recovers `M`: so a presheaf of
modules with `m`-small sections is the universe lift of a presheaf of modules with sections in
`m`. -/
def presheafShrinkIso :
    (presheafULift.{t} Rp).obj (presheafShrink.{m, t} Rp M) ≅ M :=
  PresheafOfModules.isoMk
    (fun X => (ULift.moduleEquiv.trans
      (Shrink.linearEquiv (Rp.obj X) (M.presheaf.obj X))).toModuleIso)
    (fun {X Y} f => by ext x; exact shrinkPresheaf_map_apply M.presheaf f x.down)

/-! ### Shrinking a sheaf of modules with small values -/

variable {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  (N : _root_.SheafOfModules.{max m t} R) [∀ X, Small.{m} (N.val.obj X)]

/-- The sectionwise `m`-small model of a sheaf of modules whose sections are `m`-small. The
sheaf condition descends from `N` because `AddCommGrpCat.uliftFunctor` reflects limits. -/
def sheafShrink : _root_.SheafOfModules.{m} R where
  val := presheafShrink.{m, t} R.obj N.val
  isSheaf := Presheaf.isSheaf_of_isSheaf_comp J _ AddCommGrpCat.uliftFunctor.{t}
    ((Presheaf.isSheaf_of_iso_iff
      ((PresheafOfModules.toPresheaf R.obj).mapIso
        (presheafShrinkIso.{m, t} R.obj N.val))).mpr N.isSheaf)

/-- Lifting the universe of the sections of `sheafShrink N` recovers `N`. -/
def sheafShrinkIso : (moduleULift.{t} R).obj (sheafShrink.{m, t} R N) ≅ N where
  hom := ⟨(presheafShrinkIso.{m, t} R.obj N.val).hom⟩
  inv := ⟨(presheafShrinkIso.{m, t} R.obj N.val).inv⟩
  hom_inv_id := by
    apply _root_.SheafOfModules.hom_ext
    exact (presheafShrinkIso.{m, t} R.obj N.val).hom_inv_id
  inv_hom_id := by
    apply _root_.SheafOfModules.hom_ext
    exact (presheafShrinkIso.{m, t} R.obj N.val).inv_hom_id

end SheafOfModules

end Stacks

namespace AlgebraicGeometry.RingedSite

/-! ### The internal Hom on an essentially small ringed site -/

variable (X : RingedSite.{u, v, w}) [EssentiallySmall.{m} X.C]

/-- **The sections of the internal Hom sheaf are `m`-small** when the site is essentially
`m`-small. The sections over `U` are the morphisms `A|_U ⟶ B|_U` of presheaves of modules on the
slice site `X.C/U`, which is again essentially `m`-small, and such a category of presheaves of
modules is locally `m`-small. This is the fact that makes the module universe `max u v m` of
`internalHomSheaf` an artefact of the construction. -/
instance small_internalHomSheaf_obj
    (A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (Y : X.Cᵒᵖ) :
    Small.{m} ((internalHomSheaf X A B).val.obj Y) :=
  haveI := Stacks.essentiallySmall_over.{m} Y.unop
  haveI := Stacks.locallySmall_presheafOfModules_of_essentiallySmall.{m} (ORestr X.O.obj Y.unop)
  inferInstanceAs (Small.{m} ((restrFun X.O.obj Y.unop).obj (valOf X A) ⟶
    (restrFun X.O.obj Y.unop).obj (valOf X B)))

/-- **The internal Hom of two sheaves of `O`-modules with sections in `m` on an essentially
`m`-small ringed site, as a sheaf of `O`-modules with sections in `m`.** Its universe lift is
`internalHomSheaf X A B` (`internalHomSheafSmallIso`), so this is that internal Hom and not
another construction; what is new is that it does not leave the module universe. -/
def internalHomSheafSmall (A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  Stacks.SheafOfModules.sheafShrink.{m, max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (internalHomSheaf X A B)

/-- The internal Hom of `internalHomSheafSmall` is the internal Hom of `internalHomSheaf`: the
universe lift of the former is isomorphic to the latter. -/
def internalHomSheafSmallIso
    (A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Stacks.SheafOfModules.moduleULift.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
        (internalHomSheafSmall X A B) ≅
      internalHomSheaf X A B :=
  Stacks.SheafOfModules.sheafShrinkIso.{m, max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (internalHomSheaf X A B)

omit [EssentiallySmall.{m} X.C] in
private theorem internalHomPost_id
    (A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    internalHomPost X (A := A) (𝟙 B) = 𝟙 _ := by
  ext U a
  rfl


/-- **The internal Hom on an essentially `m`-small ringed site is an endofunctor of
`SheafOfModules.{m}`**: `internalHomSheafSmall X A` is functorial in its second variable. The
morphisms are those of `internalHomPost`, read through `internalHomSheafSmallIso` and brought
down the universe by full faithfulness of the lift, so this functor agrees with
`internalHomPost` on the nose after lifting. -/
def internalHomSheafSmallFunctor
    (A : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) where
  obj B := internalHomSheafSmall X A B
  map {B C} f :=
    (Stacks.SheafOfModules.moduleULiftFullyFaithful.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).preimage
      ((internalHomSheafSmallIso X A B).hom ≫ internalHomPost X f ≫
        (internalHomSheafSmallIso X A C).inv)
  map_id B := by
    apply (Stacks.SheafOfModules.moduleULiftFullyFaithful.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map_injective
    simp [internalHomPost_id]
  map_comp {B C D} f g := by
    apply (Stacks.SheafOfModules.moduleULiftFullyFaithful.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map_injective
    simp only [Functor.map_comp, Functor.FullyFaithful.map_preimage, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [← internalHomPost_comp X A f g, Category.assoc]

/-- The universe lift of `internalHomSheafSmallFunctor` is `internalHomPost`: the functor really
is the internal Hom. -/
theorem moduleULift_map_internalHomSheafSmallFunctor_map
    (A : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {B C : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : B ⟶ C) :
    (Stacks.SheafOfModules.moduleULift.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
        ((internalHomSheafSmallFunctor X A).map f) =
      (internalHomSheafSmallIso X A B).hom ≫ internalHomPost X f ≫
        (internalHomSheafSmallIso X A C).inv :=
  (Stacks.SheafOfModules.moduleULiftFullyFaithful.{max u v}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map_preimage _

end AlgebraicGeometry.RingedSite

end
