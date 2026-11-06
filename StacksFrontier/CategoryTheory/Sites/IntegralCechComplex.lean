module

public import Mathlib.CategoryTheory.Limits.FormalCoproducts.ExtraDegeneracy
public import Mathlib.CategoryTheory.Sites.Hypercover.Zero
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.IntegralComplex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The integral Čech complex of a family of morphisms with fixed target

Let `E` be a family of morphisms `E.f j : E.X j ⟶ X` in a category `C`, presented as a
`CategoryTheory.PreZeroHypercover`, and assume that the finite nonempty fibre products of the
family exist, i.e. that the selected objects `Over.mk (E.f j)` of `Over X` have the products
occurring in the Čech construction.  The *integral Čech complex* of `E` is the chain complex
of abelian presheaves whose degree `n` term is
`⨁_{i : Fin (n + 1) → E.I₀} **Z**[U_i]`, where `U_i` is the fibre product of the
`E.X (i p)` over `X` and `**Z**[U_i]` is the free abelian presheaf on the (universe-lifted)
presheaf represented by `U_i`, with the alternating sum of the face maps as differential.

The main content of this file is the identification of the underlying simplicial presheaf of
*sets* of that construction with the Čech nerve of the morphism of presheaves of sets induced
by the family (`Stacks.IntegralCech.cechSimplicialIso`).  This is the comparison needed to
deduce the vanishing of the positive-degree homology of the integral Čech complex from the
corresponding statement for Čech nerves, which is `Stacks.IntegralCech`
`.isZero_homology_freeAbelian_cechNerve` below and which is in turn obtained from the
Čech-nerve machinery of `StacksFrontier.CategoryTheory.Sites.CechNerveHomology`.

## Main definitions

* `Stacks.IntegralCech.sigmaPresheaf` is the presheaf of sets whose sections are the disjoint
  union of the sections of a family of presheaves, together with its inclusions
  `sigmaPresheafInj`, the induced maps out of it `sigmaPresheafDesc`, and the witness
  `isColimitSigmaPresheafCofan` that it is a coproduct.
* `Stacks.IntegralCech.famFormalCoproduct` is the formal coproduct of the family `E` itself
  and `cechπ` is the projection of an `α`-fold fibre product onto one of its factors.  The
  formal coproducts of the fibre products of `E`, their reindexing maps and the resulting
  simplicial object of `FormalCoproduct (Over X)` are taken from
  `StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily`:
  `Stacks.CechSite.cechFormalCoproduct`, `cechFormalCoproductMap` and `cechSimplicialObject`.
* `Stacks.IntegralCech.typeRealization` realizes a formal coproduct of objects over `X` as a
  presheaf of sets: its sections over `V` are the pairs of an index `i` and a morphism from
  `V` to the `i`-th object.
* `Stacks.IntegralCech.cechArrow` is the morphism of presheaves of sets induced by `E`, from
  the realization of `famFormalCoproduct E` to the presheaf represented by `X`, and
  `cechBase` is the structure morphism of the `α`-fold fibre products.
* `Stacks.IntegralCech.overLift` is the morphism into an `α`-fold fibre product determined by
  a compatible family of morphisms, and `ofFamily` is the section of the realization of the
  `α`-fold fibre products determined by a family of sections of `cechSource` with a common
  image.
* The integral Čech complex itself is `Stacks.CechSite.integralCechComplex`, built from
  `Stacks.CechSite.freeAbelianYoneda`, `Stacks.CechSite.integralCechRealization` and
  `Stacks.CechSite.integralCechSimplicialObject` in
  `StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/IntegralComplex.lean`; this file supplies the
  simplicial comparison that identifies it with the Čech nerve.

## Main results

* `Stacks.IntegralCech.cechNerveIso` and `Stacks.IntegralCech.cechSimplicialIso`: the
  realization of the simplicial formal coproduct of the fibre products of `E` is the Čech
  nerve of `cechArrow E`, degreewise and as simplicial presheaves of sets.  Pointwise these
  are the two bijections of the Stacks proof: a morphism into a fibre product over `X` is a
  compatible family of morphisms into the factors, and a disjoint union of index sets
  indexes a coproduct.
* `Stacks.IntegralCech.isZero_homology_freeAbelian_cechNerve`: for an *arbitrary* morphism of
  presheaves of sets, the positive-degree homology of the free abelian presheaf complex of
  its Čech nerve vanishes.  No surjectivity hypothesis is needed, because the Čech nerve only
  depends on the image subpresheaf, onto which the morphism is surjective on sections.

## Implementation notes

The index universe `w` of the family is independent of the coefficient universe of the
abelian presheaves.  That forces the presheaves of *sets* in the comparison to live in
`Type (max w v a)` rather than in the coefficient universe `Type (max v a)`: the sections of
the realization of a formal coproduct over an index type in `Type w` form a sigma type, which
`Type (max v a)` need not contain.

Two spellings are fixed throughout.  First, the morphisms of `Type u` are a wrapped structure
(`TypeCat.Hom`), so morphisms are built with the `↾` notation and `simp` cannot normalize
applications of them; every elementwise identity below is therefore discharged by a `congrArg`
term through `exact`, which is tolerant of the definitional unfolding that `rw` and `simp`
reject at `implicit` transparency.  Second, `typeRealization.obj U` and the unfolded
`sigmaPresheaf …` are definitionally equal and not syntactically so, and likewise
`(Arrow.mk (cechArrow E)).hom` and `cechArrow E`; every statement uses exactly one of each pair,
and the crossings happen only where a term is applied.

The products assumed are only the specific ones occurring in the Čech construction, as the
source assumes: `Over X` has no finite products in general.  This is why
`CategoryTheory.Limits.FormalCoproduct.power` and `isLimitPowerFan`, which require
`HasProductsOfShape`, are not used and `Stacks.CechSite.cechFormalCoproduct` is defined
directly.  For the same reason the comparison with the Čech nerve is proved by exhibiting an
explicit inverse rather than through `CategoryTheory.Arrow.cechNerveComp`, which needs the
source category to have all finite wide pullbacks.

## References

* [The Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [The Stacks Project, Tag 03AS](https://stacks.math.columbia.edu/tag/03AS)
* [The Stacks Project, Tag 03AT](https://stacks.math.columbia.edu/tag/03AT)
-/

@[expose] public section

universe b t w v u a

namespace Stacks.IntegralCech

open CategoryTheory CategoryTheory.Limits Opposite Stacks.CechSite

section SigmaPresheaf

variable {D : Type u} [Category.{v} D] {J : Type w}

/-- The presheaf of sets whose sections are the disjoint union of the sections of a family
of presheaves. -/
def sigmaPresheaf (R : J → (Dᵒᵖ ⥤ Type (max w t))) : Dᵒᵖ ⥤ Type (max w t) where
  obj V := (j : J) × (R j).obj V
  map {_ _} f := ↾fun x ↦ ⟨x.1, (R x.1).map f x.2⟩

/-- The restriction maps of `sigmaPresheaf R` act on a section of the `j`-th summand by the
restriction maps of `R j`. -/
@[simp]
lemma sigmaPresheaf_map_apply (R : J → (Dᵒᵖ ⥤ Type (max w t))) {V V' : Dᵒᵖ} (f : V ⟶ V')
    (x : (sigmaPresheaf R).obj V) :
    (sigmaPresheaf R).map f x = ⟨x.1, (R x.1).map f x.2⟩ := rfl

/-- The inclusion of the `j`-th summand into `sigmaPresheaf R`. -/
def sigmaPresheafInj (R : J → (Dᵒᵖ ⥤ Type (max w t))) (j : J) : R j ⟶ sigmaPresheaf R where
  app _ := ↾fun x ↦ ⟨j, x⟩

/-- The inclusion `sigmaPresheafInj R j` sends a section `x` of `R j` to the pair `⟨j, x⟩`. -/
@[simp]
lemma sigmaPresheafInj_app_apply (R : J → (Dᵒᵖ ⥤ Type (max w t))) (j : J) (V : Dᵒᵖ)
    (x : (R j).obj V) : (sigmaPresheafInj R j).app V x = ⟨j, x⟩ := rfl

/-- The cofan on `sigmaPresheaf R` given by the inclusions of the summands. -/
def sigmaPresheafCofan (R : J → (Dᵒᵖ ⥤ Type (max w t))) : Cofan R :=
  Cofan.mk (sigmaPresheaf R) (sigmaPresheafInj R)

/-- The map out of `sigmaPresheaf R` determined by a family of maps out of the summands. -/
def sigmaPresheafDesc {R : J → (Dᵒᵖ ⥤ Type (max w t))} {A : Dᵒᵖ ⥤ Type (max w t)}
    (k : ∀ j, R j ⟶ A) : sigmaPresheaf R ⟶ A where
  app _ := ↾fun x ↦ (k x.1).app _ x.2
  naturality _ _ f := by ext x; exact (k x.1).naturality_apply f x.2

/-- The map `sigmaPresheafDesc k` sends a section `⟨j, y⟩` to the image of `y` under `k j`. -/
@[simp]
lemma sigmaPresheafDesc_app_apply {R : J → (Dᵒᵖ ⥤ Type (max w t))} {A : Dᵒᵖ ⥤ Type (max w t)}
    (k : ∀ j, R j ⟶ A) (V : Dᵒᵖ) (x : (sigmaPresheaf R).obj V) :
    (sigmaPresheafDesc k).app V x = (k x.1).app V x.2 := rfl

/-- Equal morphisms of presheaves of sets agree on every section. -/
private theorem app_apply_congr {D : Type u} [Category.{v} D] {F G : Dᵒᵖ ⥤ Type b} {k l : F ⟶ G}
    (h : k = l) (V : Dᵒᵖ) (x : F.obj V) : k.app V x = l.app V x :=
  ConcreteCategory.congr_hom (NatTrans.congr_app h V) x

/-- Two maps out of `sigmaPresheaf R` agreeing on each summand are equal. -/
lemma sigmaPresheaf_hom_ext {R : J → (Dᵒᵖ ⥤ Type (max w t))} {A : Dᵒᵖ ⥤ Type (max w t)}
    {k l : sigmaPresheaf R ⟶ A} (h : ∀ j, sigmaPresheafInj R j ≫ k = sigmaPresheafInj R j ≫ l) :
    k = l := by
  ext V x
  obtain ⟨j, y⟩ := x
  exact app_apply_congr (h j) V y

/-- `sigmaPresheaf R` is a coproduct of the family `R`. -/
def isColimitSigmaPresheafCofan (R : J → (Dᵒᵖ ⥤ Type (max w t))) :
    IsColimit (sigmaPresheafCofan R) :=
  Cofan.IsColimit.mk _ (fun s ↦ sigmaPresheafDesc s.inj) (fun _ _ ↦ rfl)
    (fun _ _ hm ↦ sigmaPresheaf_hom_ext (fun j ↦ (hm j).trans rfl))

end SigmaPresheaf

section Engine

open AlgebraicTopology CategoryTheory.SimplicialObject
  CategoryTheory.SimplicialObject.Augmented

variable {D : Type u} [Category.{v} D] {F G : Dᵒᵖ ⥤ Type b}

/-- For a morphism of presheaves of sets which is surjective on sections, the positive-degree
homology of the free abelian presheaf complex of its Čech nerve vanishes. -/
lemma isZero_homology_freeAbelian_cechNerve_of_surjective (e : F ⟶ G)
    (he : ∀ U, Function.Surjective (e.app U)) (n : ℕ) (hn : 0 < n) :
    IsZero (((alternatingFaceMapComplex (Dᵒᵖ ⥤ AddCommGrpCat.{b})).obj
      ((Arrow.mk e).cechNerve ⋙ Presheaf.freeAbelian)).homology n) := by
  have h := Presheaf.quasiIso_ε_freeAbelian_augmentedCechNerve e he
  have hn' : IsIso (HomologicalComplex.homologyMap (AlternatingFaceMapComplex.ε.app
      (((Augmented.whiskering (Dᵒᵖ ⥤ Type b) (Dᵒᵖ ⥤ AddCommGrpCat.{b})).obj
        Presheaf.freeAbelian).obj (Arrow.mk e).augmentedCechNerve)) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).1 (h.quasiIsoAt n)
  exact (HomologicalComplex.isZero_single_obj_homology _ 0 _ n (by omega)).of_iso
    (@asIso _ _ _ _ _ hn')

/-- **The positive homology of an integral Čech complex vanishes.** For an arbitrary morphism
of presheaves of sets, the positive-degree homology of the free abelian presheaf complex of
its Čech nerve vanishes.  No surjectivity is needed: the Čech nerve only depends on the image
subpresheaf, onto which the morphism is surjective. -/
lemma isZero_homology_freeAbelian_cechNerve (e : F ⟶ G) (n : ℕ) (hn : 0 < n) :
    IsZero (((alternatingFaceMapComplex (Dᵒᵖ ⥤ AddCommGrpCat.{b})).obj
      ((Arrow.mk e).cechNerve ⋙ Presheaf.freeAbelian)).homology n) := by
  have hsurj : ∀ U, Function.Surjective ((Subfunctor.toRange e).app U) := by
    rintro U ⟨y, x, rfl⟩
    exact ⟨x, Subtype.ext (Subfunctor.toRange_app_val e x)⟩
  refine (isZero_homology_freeAbelian_cechNerve_of_surjective
    (Subfunctor.toRange e) hsurj n hn).of_iso ?_
  exact ((HomologicalComplex.homologyFunctor _ _ n).mapIso
    ((alternatingFaceMapComplex (Dᵒᵖ ⥤ AddCommGrpCat.{b})).mapIso
      (((SimplicialObject.whiskering (Dᵒᵖ ⥤ Type b)
          (Dᵒᵖ ⥤ AddCommGrpCat.{b})).obj Presheaf.freeAbelian).mapIso
        (Arrow.cechNerveCompMonoIso (Subfunctor.toRange e) (Subfunctor.range e).ι)))).symm

end Engine

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)

variable {α β : Type t}
  [instα : ∀ i : α → E.I₀, HasProduct (fun p ↦ Over.mk (E.f (i p)))]
  [instβ : ∀ i : β → E.I₀, HasProduct (fun q ↦ Over.mk (E.f (i q)))]

/-- The component of the reindexing map `cechFormalCoproductMap E g` at `i`, followed by the
`p`-th projection, is the `g p`-th projection. -/
@[reassoc]
lemma cechFormalCoproductMap_φ_comp_π (g : α → β) (i : β → E.I₀) (p : α) :
    (cechFormalCoproductMap E g).φ i ≫
        Pi.π (fun q : α ↦ Over.mk (E.f (i (g q)))) p =
      Pi.π (fun q : β ↦ Over.mk (E.f (i q))) (g p) :=
  Pi.lift_comp_π _ _

/-- The formal coproduct of the family `E` itself. -/
def famFormalCoproduct : FormalCoproduct.{w} (Over X) where
  I := E.I₀
  obj j := Over.mk (E.f j)

/-- The projection of the `α`-fold fibre product onto its `p`-th factor. -/
noncomputable def cechπ (α : Type)
    [∀ i : α → E.I₀, HasProduct (fun p ↦ Over.mk (E.f (i p)))] (p : α) :
    cechFormalCoproduct E α ⟶ famFormalCoproduct E where
  f i := i p
  φ := fun (i : α → E.I₀) ↦ Pi.π (fun q : α ↦ Over.mk (E.f (i q))) p

/-- The presheaf of sets realizing a formal coproduct of objects over `X`: its sections over
`V` are pairs of an index `i` and a morphism from `V` to the `i`-th object. -/
noncomputable abbrev typeReal (U : FormalCoproduct.{w} (Over X)) : Cᵒᵖ ⥤ Type (max w v a) :=
  sigmaPresheaf (fun i : U.I ↦ uliftYoneda.{max w a}.obj (U.obj i).left)

/-- The component at `V` of the map of realizations induced by a morphism of formal
coproducts. -/
noncomputable def typeRealMapApp {U U' : FormalCoproduct.{w} (Over X)} (k : U ⟶ U') (V : Cᵒᵖ) :
    (typeReal.{w, v, u, a} U).obj V ⟶ (typeReal.{w, v, u, a} U').obj V :=
  ↾fun x ↦ ⟨k.f x.1, ULift.up (x.2.down ≫ (k.φ x.1).left)⟩

/-- The map `typeRealMapApp k V` sends a pair `⟨i, h⟩` to `⟨k.f i, h ≫ (k.φ i).left⟩`. -/
@[simp]
lemma typeRealMapApp_apply {U U' : FormalCoproduct.{w} (Over X)} (k : U ⟶ U') (V : Cᵒᵖ)
    (x : (typeReal.{w, v, u, a} U).obj V) :
    typeRealMapApp.{w, v, u, a} k V x =
      ⟨k.f x.1, ULift.up (x.2.down ≫ (k.φ x.1).left)⟩ := rfl

/-- The map of realizations induced by a morphism of formal coproducts. -/
noncomputable def typeRealMap {U U' : FormalCoproduct.{w} (Over X)} (k : U ⟶ U') :
    typeReal.{w, v, u, a} U ⟶ typeReal.{w, v, u, a} U' where
  app := typeRealMapApp.{w, v, u, a} k
  naturality _ _ _ := by
    ext x
    obtain ⟨i, h⟩ := x
    exact congrArg (fun y ↦ (⟨k.f i, y⟩ : (typeReal.{w, v, u, a} U').obj _))
      (congrArg ULift.up (Category.assoc _ _ _))

/-- The realization of a formal coproduct of objects over `X` as a presheaf of sets. -/
noncomputable def typeRealization :
    FormalCoproduct.{w} (Over X) ⥤ (Cᵒᵖ ⥤ Type (max w v a)) where
  obj U := typeReal.{w, v, u, a} U
  map k := typeRealMap.{w, v, u, a} k
  map_id U := NatTrans.ext (funext (fun V ↦ by
    ext x
    obtain ⟨i, h⟩ := x
    exact congrArg (fun y ↦ (⟨i, y⟩ : (typeReal.{w, v, u, a} U).obj V))
      (congrArg ULift.up (Category.comp_id _))))
  map_comp {_ U' U''} k l := NatTrans.ext (funext (fun V ↦ by
    ext x
    obtain ⟨i, h⟩ := x
    exact congrArg (fun y ↦ (⟨l.f (k.f i), y⟩ : (typeReal.{w, v, u, a} U'').obj V))
      (congrArg ULift.up (Category.assoc _ _ _).symm)))

/-- The map `typeRealization.map k` sends a section `⟨i, h⟩` over `V` to
`⟨k.f i, h ≫ (k.φ i).left⟩`. -/
@[simp]
lemma typeRealization_map_app_apply {U U' : FormalCoproduct.{w} (Over X)} (k : U ⟶ U')
    (V : Cᵒᵖ) (x : (typeReal.{w, v, u, a} U).obj V) :
    (typeRealization.{w, v, u, a}.map k).app V x =
      ⟨k.f x.1, ULift.up (x.2.down ≫ (k.φ x.1).left)⟩ := rfl

/-- A map of realizations which preserves the structure morphisms to `X` is compatible with
any two maps to the representable presheaf on `X` given by composing with them. -/
private theorem typeRealization_map_comp_eq {U U' : FormalCoproduct.{w} (Over X)} (k : U ⟶ U')
    (b : typeRealization.{w, v, u, a}.obj U ⟶ uliftYoneda.{max w a}.obj X)
    (b' : typeRealization.{w, v, u, a}.obj U' ⟶ uliftYoneda.{max w a}.obj X)
    (hb : ∀ V x, b.app V x = ULift.up (x.2.down ≫ (U.obj x.1).hom))
    (hb' : ∀ V x, b'.app V x = ULift.up (x.2.down ≫ (U'.obj x.1).hom)) :
    typeRealization.{w, v, u, a}.map k ≫ b' = b := by
  refine NatTrans.ext (funext (fun V ↦ ?_))
  ext ⟨i, h⟩
  exact (hb' V _).trans (congrArg ULift.up ((Category.assoc _ _ _).trans
    (congrArg (fun m ↦ h.down ≫ m) (Over.w (k.φ i))))) |>.trans (hb V _).symm

/-- The presheaf of sets whose sections over `V` are pairs of an index `j` of the family `E`
and a morphism `V ⟶ E.X j`. -/
noncomputable abbrev cechSource : Cᵒᵖ ⥤ Type (max w v a) :=
  typeRealization.{w, v, u, a}.obj (famFormalCoproduct E)

/-- The morphism of presheaves of sets induced by the family `E`: it sends a morphism into a
member of the family to its composite with the structure morphism. -/
noncomputable def cechArrow : cechSource.{w, v, u, a} E ⟶ uliftYoneda.{max w a}.obj X where
  app _ := ↾fun x ↦ ULift.up (x.2.down ≫ E.f x.1)
  naturality _ _ _ := by
    ext x
    obtain ⟨j, h⟩ := x
    exact congrArg ULift.up (Category.assoc _ _ _)

/-- The morphism `cechArrow E` sends a section `⟨j, h⟩` to `h ≫ E.f j`. -/
@[simp]
lemma cechArrow_app_apply (V : Cᵒᵖ) (x : (cechSource.{w, v, u, a} E).obj V) :
    (cechArrow.{w, v, u, a} E).app V x = ULift.up (x.2.down ≫ E.f x.1) := rfl

section Alpha

variable (α : Type) [instα : ∀ i : α → E.I₀, HasProduct (fun p ↦ Over.mk (E.f (i p)))]

/-- The structure morphism of the `α`-fold fibre products, as a map of presheaves of sets. -/
noncomputable def cechBase :
    typeRealization.{w, v, u, a}.obj (cechFormalCoproduct E α) ⟶ uliftYoneda.{max w a}.obj X where
  app _ := ↾fun x ↦ ULift.up (x.2.down ≫ ((cechFormalCoproduct E α).obj x.1).hom)
  naturality _ _ _ := by
    ext x
    obtain ⟨i, h⟩ := x
    exact congrArg ULift.up (Category.assoc _ _ _)

/-- The morphism `cechBase E α` sends a section `⟨i, h⟩` to the composite of `h` with the
structure morphism of the `i`-th fibre product. -/
@[simp]
lemma cechBase_app_apply (V : Cᵒᵖ)
    (x : (typeRealization.{w, v, u, a}.obj (cechFormalCoproduct E α)).obj V) :
    (cechBase.{w, v, u, a} E α).app V x =
      ULift.up (x.2.down ≫ ((cechFormalCoproduct E α).obj x.1).hom) := rfl

/-- Each projection `cechπ E α p`, followed by `cechArrow E`, is the structure morphism
`cechBase E α`. -/
lemma cechπ_comp_cechArrow (p : α) :
    typeRealization.{w, v, u, a}.map (cechπ E α p) ≫ cechArrow.{w, v, u, a} E =
      cechBase.{w, v, u, a} E α := by
  exact typeRealization_map_comp_eq _ _ _ (cechBase_app_apply E α) (cechArrow_app_apply E)

variable {α}

/-- The morphism into the `α`-fold fibre product determined by a compatible family of
morphisms. -/
noncomputable def overLift {V : C} (i : α → E.I₀) (φ : V ⟶ X)
    (k : ∀ p, V ⟶ E.X (i p)) (hk : ∀ p, k p ≫ E.f (i p) = φ) :
    V ⟶ ((cechFormalCoproduct E α).obj i).left :=
  (Pi.lift (fun p ↦ (Over.homMk (k p) (hk p) : Over.mk φ ⟶ Over.mk (E.f (i p))))).left

/-- The `p`-th projection of `overLift E i φ k hk` is `k p`. -/
lemma overLift_comp_π {V : C} (i : α → E.I₀) (φ : V ⟶ X)
    (k : ∀ p, V ⟶ E.X (i p)) (hk : ∀ p, k p ≫ E.f (i p) = φ) (p : α) :
    overLift E i φ k hk ≫ (Pi.π (fun q : α ↦ Over.mk (E.f (i q))) p).left = k p :=
  (Over.comp_left ..).symm.trans (congrArg Over.Hom.left (Pi.lift_comp_π _ p))

/-- The composite of `overLift E i φ k hk` with the structure morphism to `X` is `φ`. -/
lemma overLift_comp_hom {V : C} (i : α → E.I₀) (φ : V ⟶ X)
    (k : ∀ p, V ⟶ E.X (i p)) (hk : ∀ p, k p ≫ E.f (i p) = φ) :
    overLift E i φ k hk ≫ ((cechFormalCoproduct E α).obj i).hom = φ :=
  Over.w (Pi.lift (fun p ↦ (Over.homMk (k p) (hk p) : Over.mk φ ⟶ Over.mk (E.f (i p)))))

/-- Two morphisms into the `α`-fold fibre product which have the same composite with the
structure morphism and with every projection are equal. -/
lemma overLift_ext {V : C} (i : α → E.I₀) (φ : V ⟶ X)
    {m m' : V ⟶ ((cechFormalCoproduct E α).obj i).left}
    (hm : m ≫ ((cechFormalCoproduct E α).obj i).hom = φ)
    (hm' : m' ≫ ((cechFormalCoproduct E α).obj i).hom = φ)
    (h : ∀ p, m ≫ (Pi.π (fun q : α ↦ Over.mk (E.f (i q))) p).left =
      m' ≫ (Pi.π (fun q : α ↦ Over.mk (E.f (i q))) p).left) : m = m' :=
  congrArg Over.Hom.left (Pi.hom_ext (f := fun q : α ↦ Over.mk (E.f (i q)))
    (Over.homMk m hm : Over.mk φ ⟶ _) (Over.homMk m' hm')
    (fun p ↦ Over.OverMorphism.ext (h p)))

/-- Precomposing `overLift E i φ k hk` with `g : V' ⟶ V` gives the morphism determined by the
family `g ≫ k p`. -/
lemma overLift_comp_left {V V' : C} (g : V' ⟶ V) (i : α → E.I₀) (φ : V ⟶ X)
    (k : ∀ p, V ⟶ E.X (i p)) (hk : ∀ p, k p ≫ E.f (i p) = φ)
    (hgk : ∀ p, (g ≫ k p) ≫ E.f (i p) = g ≫ φ) :
    overLift E i (g ≫ φ) (fun p ↦ g ≫ k p) hgk = g ≫ overLift E i φ k hk :=
  overLift_ext E i (g ≫ φ) (overLift_comp_hom ..)
    ((Category.assoc _ _ _).trans (congrArg (fun m ↦ g ≫ m) (overLift_comp_hom E i φ k hk)))
    (fun p ↦ (overLift_comp_π ..).trans
      (((congrArg (fun m ↦ g ≫ m) (overLift_comp_π E i φ k hk p)).symm).trans
        (Category.assoc _ _ _).symm))

/-- The section of the realization of the `α`-fold fibre products determined by a family of
sections of `cechSource` with a common image in the representable presheaf on `X`. -/
noncomputable def ofFamily {V : Cᵒᵖ} (sp : α → (cechSource.{w, v, u, a} E).obj V)
    (φ : (uliftYoneda.{max w a}.obj X).obj V)
    (hsp : ∀ p, (cechArrow.{w, v, u, a} E).app V (sp p) = φ) :
    (typeRealization.{w, v, u, a}.obj (cechFormalCoproduct E α)).obj V :=
  ⟨fun p ↦ (sp p).1, ULift.up (overLift E (fun p ↦ (sp p).1) φ.down
    (fun p ↦ (sp p).2.down) (fun p ↦ congrArg ULift.down (hsp p)))⟩

/-- `ofFamily E sp φ hsp` depends only on `sp` and `φ`. -/
lemma ofFamily_congr {V : Cᵒᵖ} (sp sp' : α → (cechSource.{w, v, u, a} E).obj V)
    (hs : sp = sp') (φ φ' : (uliftYoneda.{max w a}.obj X).obj V) (hφ : φ = φ')
    (hsp : ∀ p, (cechArrow.{w, v, u, a} E).app V (sp p) = φ)
    (hsp' : ∀ p, (cechArrow.{w, v, u, a} E).app V (sp' p) = φ') :
    ofFamily E sp φ hsp = ofFamily E sp' φ' hsp' := by
  subst hs
  subst hφ
  rfl

/-- The section determined by the restrictions along `g` of the family `sp` is the restriction
along `g` of `ofFamily E sp φ hsp`. -/
lemma ofFamily_map {V V' : Cᵒᵖ} (g : V ⟶ V') (sp : α → (cechSource.{w, v, u, a} E).obj V)
    (φ : (uliftYoneda.{max w a}.obj X).obj V)
    (hsp : ∀ p, (cechArrow.{w, v, u, a} E).app V (sp p) = φ)
    (hsp' : ∀ p, (cechArrow.{w, v, u, a} E).app V'
      ((cechSource.{w, v, u, a} E).map g (sp p)) = (uliftYoneda.{max w a}.obj X).map g φ) :
    ofFamily E (fun p ↦ (cechSource.{w, v, u, a} E).map g (sp p))
        ((uliftYoneda.{max w a}.obj X).map g φ) hsp' =
      (typeRealization.{w, v, u, a}.obj (cechFormalCoproduct E α)).map g (ofFamily E sp φ hsp) :=
  congrArg (fun y ↦ (⟨fun p ↦ (sp p).1, ULift.up y⟩ :
      (typeRealization.{w, v, u, a}.obj (cechFormalCoproduct E α)).obj V'))
    (overLift_comp_left E g.unop (fun p ↦ (sp p).1) φ.down (fun p ↦ (sp p).2.down)
      (fun p ↦ congrArg ULift.down (hsp p)) _)

/-- If `sp'` and `φ'` are the restrictions along `g` of `sp` and `φ`, then `ofFamily E sp' φ'`
is the restriction along `g` of `ofFamily E sp φ`. -/
lemma ofFamily_map' {V V' : Cᵒᵖ} (g : V ⟶ V')
    (sp : α → (cechSource.{w, v, u, a} E).obj V) (sp' : α → (cechSource.{w, v, u, a} E).obj V')
    (hss : ∀ p, sp' p = (cechSource.{w, v, u, a} E).map g (sp p))
    (φ : (uliftYoneda.{max w a}.obj X).obj V) (φ' : (uliftYoneda.{max w a}.obj X).obj V')
    (hφφ : φ' = (uliftYoneda.{max w a}.obj X).map g φ)
    (hsp : ∀ p, (cechArrow.{w, v, u, a} E).app V (sp p) = φ)
    (hsp' : ∀ p, (cechArrow.{w, v, u, a} E).app V' (sp' p) = φ') :
    ofFamily E sp' φ' hsp' =
      (typeRealization.{w, v, u, a}.obj (cechFormalCoproduct E α)).map g (ofFamily E sp φ hsp) := by
  subst hφφ
  obtain rfl : sp' = fun p ↦ (cechSource.{w, v, u, a} E).map g (sp p) := funext hss
  exact ofFamily_map E g sp φ hsp hsp'

/-- The `p`-th projection of `ofFamily E sp φ hsp` is `sp p`. -/
lemma ofFamily_comp_cechπ {V : Cᵒᵖ} (sp : α → (cechSource.{w, v, u, a} E).obj V)
    (φ : (uliftYoneda.{max w a}.obj X).obj V)
    (hsp : ∀ p, (cechArrow.{w, v, u, a} E).app V (sp p) = φ) (p : α) :
    (typeRealization.{w, v, u, a}.map (cechπ E α p)).app V (ofFamily E sp φ hsp) = sp p :=
  congrArg (fun y ↦ (⟨(sp p).1, ULift.up y⟩ : (cechSource.{w, v, u, a} E).obj V))
    (overLift_comp_π E (fun q ↦ (sp q).1) φ.down (fun q ↦ (sp q).2.down)
      (fun q ↦ congrArg ULift.down (hsp q)) p)

/-- The image of `ofFamily E sp φ hsp` under `cechBase E α` is `φ`. -/
lemma ofFamily_comp_cechBase {V : Cᵒᵖ} (sp : α → (cechSource.{w, v, u, a} E).obj V)
    (φ : (uliftYoneda.{max w a}.obj X).obj V)
    (hsp : ∀ p, (cechArrow.{w, v, u, a} E).app V (sp p) = φ) :
    (cechBase.{w, v, u, a} E α).app V (ofFamily E sp φ hsp) = φ :=
  congrArg ULift.up (overLift_comp_hom E (fun q ↦ (sp q).1) φ.down
    (fun q ↦ (sp q).2.down) (fun q ↦ congrArg ULift.down (hsp q)))

/-- A section `x` of the realization of the `α`-fold fibre products is the section determined
by its projections and its image under `cechBase E α`. -/
lemma ofFamily_eq_self {V : Cᵒᵖ}
    (x : (typeRealization.{w, v, u, a}.obj (cechFormalCoproduct E α)).obj V)
    (sp : α → (cechSource.{w, v, u, a} E).obj V)
    (hs : sp = fun p ↦ (typeRealization.{w, v, u, a}.map (cechπ E α p)).app V x)
    (φ : (uliftYoneda.{max w a}.obj X).obj V) (hφ : φ = (cechBase.{w, v, u, a} E α).app V x)
    (hsp : ∀ p, (cechArrow.{w, v, u, a} E).app V (sp p) = φ) :
    ofFamily E sp φ hsp = x := by
  subst hs
  subst hφ
  obtain ⟨i, h⟩ := x
  exact congrArg (fun y ↦ (⟨i, ULift.up y⟩ :
      (typeRealization.{w, v, u, a}.obj (cechFormalCoproduct E α)).obj V))
    (overLift_ext E i _ (overLift_comp_hom ..) rfl (fun _ ↦ overLift_comp_π ..))

end Alpha

section Nerve

variable [hE : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun p ↦ Over.mk (E.f (i p)))]

/-- The arrow of presheaves of sets attached to the family `E`. -/
noncomputable abbrev cechArr : Arrow (Cᵒᵖ ⥤ Type (max w v a)) :=
  Arrow.mk (cechArrow.{w, v, u, a} E)

variable (n : SimplexCategoryᵒᵖ)

/-- The comparison map from the realization of the `n`-fold fibre products of the family `E`
to the degree-`n` term of the Čech nerve. -/
noncomputable def cechNerveHom :
    typeRealization.{w, v, u, a}.obj (cechFormalCoproduct E (ToType n.unop)) ⟶
      (cechArr.{w, v, u, a} E).cechNerve.obj n :=
  WidePullback.lift (cechBase.{w, v, u, a} E (ToType n.unop))
    (fun p ↦ typeRealization.{w, v, u, a}.map (cechπ E (ToType n.unop) p))
    (fun p ↦ cechπ_comp_cechArrow E (ToType n.unop) p)

omit hE in
/-- Every section of the degree-`n` term of the Čech nerve has all its components mapping to
the same section of the representable presheaf on `X`. -/
lemma nerveCond (V : Cᵒᵖ) (z : ((cechArr.{w, v, u, a} E).cechNerve.obj n).obj V)
    (p : ToType n.unop) :
    (cechArrow.{w, v, u, a} E).app V
        ((WidePullback.π (fun _ : ToType n.unop ↦ (cechArr.{w, v, u, a} E).hom) p).app V z) =
      (WidePullback.base (fun _ : ToType n.unop ↦ (cechArr.{w, v, u, a} E).hom)).app V z :=
  app_apply_congr
    (WidePullback.π_arrow (fun _ : ToType n.unop ↦ (cechArr.{w, v, u, a} E).hom) p) V z

/-- The inverse comparison map. -/
noncomputable def cechNerveInv :
    (cechArr.{w, v, u, a} E).cechNerve.obj n ⟶
      typeRealization.{w, v, u, a}.obj (cechFormalCoproduct E (ToType n.unop)) where
  app V := ↾fun z ↦ ofFamily E
    (fun p ↦ (WidePullback.π (fun _ : ToType n.unop ↦ (cechArr.{w, v, u, a} E).hom) p).app V z)
    ((WidePullback.base (fun _ : ToType n.unop ↦ (cechArr.{w, v, u, a} E).hom)).app V z)
    (nerveCond E n V z)
  naturality V V' g := by
    ext z
    exact ofFamily_map' E g _ _ (fun p ↦
      (WidePullback.π (fun _ : ToType n.unop ↦
        (cechArr.{w, v, u, a} E).hom) p).naturality_apply g z) _ _
      ((WidePullback.base
        (fun _ : ToType n.unop ↦ (cechArr.{w, v, u, a} E).hom)).naturality_apply g z)
      (nerveCond E n V z) (nerveCond E n V' (((cechArr.{w, v, u, a} E).cechNerve.obj n).map g z))

/-- The `p`-th projection of `cechNerveHom E n` is the map induced by `cechπ E _ p`. -/
@[reassoc]
lemma cechNerveHom_comp_π (p : ToType n.unop) :
    cechNerveHom.{w, v, u, a} E n ≫
        WidePullback.π (fun _ : ToType n.unop ↦ (cechArr.{w, v, u, a} E).hom) p =
      typeRealization.{w, v, u, a}.map (cechπ E (ToType n.unop) p) := by
  apply WidePullback.lift_π

/-- The composite of `cechNerveHom E n` with the base of the wide pullback is `cechBase E _`. -/
@[reassoc]
lemma cechNerveHom_comp_base :
    cechNerveHom.{w, v, u, a} E n ≫
        WidePullback.base (fun _ : ToType n.unop ↦ (cechArr.{w, v, u, a} E).hom) =
      cechBase.{w, v, u, a} E (ToType n.unop) := by
  apply WidePullback.lift_base

/-- The composite of `cechNerveInv E n` with the map induced by `cechπ E _ p` is the `p`-th
projection of the wide pullback. -/
lemma cechNerveInv_comp_cechπ (p : ToType n.unop) :
    cechNerveInv.{w, v, u, a} E n ≫ typeRealization.{w, v, u, a}.map (cechπ E (ToType n.unop) p) =
      WidePullback.π (fun _ : ToType n.unop ↦ (cechArr.{w, v, u, a} E).hom) p :=
  NatTrans.ext (funext (fun V ↦ by ext z; exact ofFamily_comp_cechπ E _ _ (nerveCond E n V z) p))

/-- The composite of `cechNerveInv E n` with `cechBase E _` is the base of the wide pullback. -/
lemma cechNerveInv_comp_cechBase :
    cechNerveInv.{w, v, u, a} E n ≫ cechBase.{w, v, u, a} E (ToType n.unop) =
      WidePullback.base (fun _ : ToType n.unop ↦ (cechArr.{w, v, u, a} E).hom) :=
  NatTrans.ext (funext (fun V ↦ by
    ext z; exact ofFamily_comp_cechBase E _ _ (nerveCond E n V z)))

/-- **The comparison isomorphism.** The realization of the formal coproduct of the `n`-fold
fibre products of the family `E` is the degree-`n` term of the Čech nerve of the morphism of
presheaves of sets induced by `E`. -/
@[sga "4 V 1.10" "special case"]
noncomputable def cechNerveIso :
    typeRealization.{w, v, u, a}.obj (cechFormalCoproduct E (ToType n.unop)) ≅
      (cechArr.{w, v, u, a} E).cechNerve.obj n where
  hom := cechNerveHom.{w, v, u, a} E n
  inv := cechNerveInv.{w, v, u, a} E n
  hom_inv_id := NatTrans.ext (funext (fun V ↦ by
    ext x
    refine ofFamily_eq_self E x _ (funext (fun p ↦ ?_)) _ ?_
      (nerveCond E n V ((cechNerveHom.{w, v, u, a} E n).app V x))
    · exact ConcreteCategory.congr_hom (congrArg
        (fun (η : typeRealization.{w, v, u, a}.obj (cechFormalCoproduct E (ToType n.unop)) ⟶ _) ↦
          η.app V) (cechNerveHom_comp_π E n p)) x
    · exact ConcreteCategory.congr_hom (congrArg
        (fun (η : typeRealization.{w, v, u, a}.obj (cechFormalCoproduct E (ToType n.unop)) ⟶ _) ↦
          η.app V) (cechNerveHom_comp_base E n)) x))
  inv_hom_id := WidePullback.hom_ext _ _ _
    (fun p ↦ ((Category.assoc _ _ _).trans ((congrArg
      (fun m ↦ cechNerveInv.{w, v, u, a} E n ≫ m) (cechNerveHom_comp_π E n p)).trans
        (cechNerveInv_comp_cechπ E n p))).trans (Category.id_comp _).symm)
    (((Category.assoc _ _ _).trans ((congrArg
      (fun m ↦ cechNerveInv.{w, v, u, a} E n ≫ m) (cechNerveHom_comp_base E n)).trans
        (cechNerveInv_comp_cechBase E n))).trans (Category.id_comp _).symm)

end Nerve

section Reindex

variable {α β : Type}
  [instα : ∀ i : α → E.I₀, HasProduct (fun p ↦ Over.mk (E.f (i p)))]
  [instβ : ∀ i : β → E.I₀, HasProduct (fun q ↦ Over.mk (E.f (i q)))]

/-- The reindexing map `cechFormalCoproductMap E g` followed by the `p`-th projection is the
`g p`-th projection. -/
lemma cechFormalCoproductMap_comp_cechπ (g : α → β) (p : α) :
    cechFormalCoproductMap E g ≫ cechπ E α p = cechπ E β (g p) :=
  FormalCoproduct.hom_ext rfl (fun (i : β → E.I₀) ↦
    (Category.comp_id _).trans (cechFormalCoproductMap_φ_comp_π E g i p))

/-- The reindexing maps of the fibre products commute with the structure morphisms
`cechBase`. -/
lemma cechFormalCoproductMap_comp_cechBase (g : α → β) :
    typeRealization.{w, v, u, a}.map (cechFormalCoproductMap E g) ≫
        cechBase.{w, v, u, a} E α = cechBase.{w, v, u, a} E β := by
  exact typeRealization_map_comp_eq _ _ _ (cechBase_app_apply E β) (cechBase_app_apply E α)

end Reindex

section Simplicial

variable [hE : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun p ↦ Over.mk (E.f (i p)))]

omit hE in
/-- A simplicial structure map of the Čech nerve, followed by the `p`-th projection, is the
projection indexed by the image of `p`. -/
@[reassoc]
lemma cechNerve_map_comp_π {n m : SimplexCategoryᵒᵖ} (g : n ⟶ m) (p : ToType m.unop) :
    (cechArr.{w, v, u, a} E).cechNerve.map g ≫
        WidePullback.π (fun _ : ToType m.unop ↦ (cechArr.{w, v, u, a} E).hom) p =
      WidePullback.π (fun _ : ToType n.unop ↦ (cechArr.{w, v, u, a} E).hom)
        (g.unop.toOrderHom p) := by
  apply WidePullback.lift_π

omit hE in
/-- The simplicial structure maps of the Čech nerve commute with the base maps. -/
@[reassoc]
lemma cechNerve_map_comp_base {n m : SimplexCategoryᵒᵖ} (g : n ⟶ m) :
    (cechArr.{w, v, u, a} E).cechNerve.map g ≫
        WidePullback.base (fun _ : ToType m.unop ↦ (cechArr.{w, v, u, a} E).hom) =
      WidePullback.base (fun _ : ToType n.unop ↦ (cechArr.{w, v, u, a} E).hom) := by
  apply WidePullback.lift_base

/-- The comparison maps `cechNerveHom E n` are natural in `n`. -/
lemma cechNerveHom_naturality {n m : SimplexCategoryᵒᵖ} (g : n ⟶ m) :
    typeRealization.{w, v, u, a}.map (cechFormalCoproductMap E g.unop.toOrderHom.toFun) ≫
        cechNerveHom.{w, v, u, a} E m =
      cechNerveHom.{w, v, u, a} E n ≫ (cechArr.{w, v, u, a} E).cechNerve.map g := by
  refine WidePullback.hom_ext _ _ _ (fun p ↦ ?_) ?_
  · rw [Category.assoc, cechNerveHom_comp_π, ← typeRealization.map_comp,
      cechFormalCoproductMap_comp_cechπ, Category.assoc, cechNerve_map_comp_π,
      cechNerveHom_comp_π]
    rfl
  · rw [Category.assoc, cechNerveHom_comp_base, Category.assoc, cechNerve_map_comp_base,
      cechNerveHom_comp_base, cechFormalCoproductMap_comp_cechBase]

/-- **The simplicial comparison isomorphism.** The simplicial presheaf of sets realizing the
simplicial formal coproduct of the fibre products of `E` is the Čech nerve of the morphism of
presheaves of sets induced by `E`. -/
noncomputable def cechSimplicialIso :
    cechSimplicialObject E ⋙ typeRealization.{w, v, u, a} ≅ (cechArr.{w, v, u, a} E).cechNerve :=
  NatIso.ofComponents (cechNerveIso.{w, v, u, a} E)
    (fun {_ _} g ↦ cechNerveHom_naturality E g)

end Simplicial

section Integral

variable [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{max v a})]

/-- Realize a formal coproduct of objects over `X` as the corresponding coproduct of free
abelian representable presheaves. -/
noncomputable def integralCechRealization :
    FormalCoproduct.{w} (Over X) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) :=
  (FormalCoproduct.eval (Over X) (Cᵒᵖ ⥤ AddCommGrpCat.{max v a})).obj
    (Over.forget X ⋙ Stacks.CechSite.freeAbelianYoneda.{v, u, a})

variable [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun p ↦ Over.mk (E.f (i p)))]

/-- The simplicial abelian presheaf whose degree `n` term is the direct sum of the free
abelian presheaves represented by the `(n + 1)`-fold fibre products in the family. -/
noncomputable def integralCechSimplicialObject :
    SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) :=
  ((SimplicialObject.whiskering _ _).obj
    (integralCechRealization.{w, v, u, a} (X := X))).obj (cechSimplicialObject E)

/-- The canonical integral Čech chain complex of the family `E`.  Its degree `n` term is the
direct sum, over tuples `i : Fin (n + 1) → E.I₀`, of the free abelian presheaves represented
by the corresponding fibre products over `X`. -/
noncomputable def integralCechComplex : ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj
    (integralCechSimplicialObject.{w, v, u, a} E)

end Integral

end Stacks.IntegralCech
