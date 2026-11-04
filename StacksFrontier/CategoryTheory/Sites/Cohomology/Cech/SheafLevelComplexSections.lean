module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.WeaklyContractibleProducts
public import StacksFrontier.AlgebraicGeometry.SheafComplexLocality.Basic
public import StacksFrontier.CategoryTheory.Sites.CechComplexCoefficientChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.BaseChangedFamilyComplexExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.SheafLevelComplexAugmentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.SheafLevelSplitFamilyExactness

/-!
# The sections of the sheaf-level Čech complex, and its exactness above degree zero

Let `C` be a site with finite products, let `R` be a sheaf of rings on `C`, let `F` be a sheaf of
`R`-modules and let `{U_i → X}` be a family of morphisms with fixed target.
`Stacks.CechSite.SheafLevel.complexFunctor` is the Čech complex of that family with `F` as
coefficients: a cochain complex of *sheaves of modules*, whose degree-`p` term is the product,
over the `(p+1)`-tuples of indices, of `j_{U_{i_0} ×_X ⋯ ×_X U_{i_p}, *} j^{-1} F`.

This file computes its **sections over an object `W`** and uses that computation to prove that
the complex is **exact in every positive degree** when the family covers the terminal object.

The computation is `Stacks.CechSite.SheafLevel.complexFunctorSectionsIso`: for `X` *terminal*,

`Γ(W, Č(E, F)) ≅ Č(E.X, V ↦ F(W ⨯ V))`,

the Čech complex of the family of *objects* `E.X` with coefficients in the presheaf of abelian
groups `V ↦ F(W ⨯ V)`.  That right-hand side is exactly the complex
`Stacks.CechObjectFamily.exactAt_cechComplexFunctor_prodRestriction_of_hom` proves exact in
positive degrees as soon as `W` admits a morphism to one member of the family, so the sections
over such a `W` are exact; and exactness of a complex of sheaves of modules is local, by
`Stacks.SheafOfModules.ComplexLocality.exactAt_of_coversTop`.

A last section settles one of the two halves of the *degree-zero* statement: the augmentation
`F ⟶ Č⁰(E, F)` is a **monomorphism**, because over an object `W` mapping to a member of the family
it is a split monomorphism on sections, the retraction being restriction along the diagonal
`W ⟶ U_{i₀} ×_X W`.

## Main definitions

* `Stacks.CechSite.SheafLevel.diagramObjSectionsIso`: the Čech diagram `V ↦ j_{V,*} j_V^{-1} F`,
  read on sections over `W`, is the presheaf `V ↦ F(W ⨯ V)`.
* `Stacks.CechSite.SheafLevel.complexFunctorSectionsIso`: **the sections over `W` of the
  sheaf-level Čech complex**, for a family whose target is terminal.
* `Stacks.CechSite.SheafLevel.degreeZeroDiagonal`: the diagonal `W ⟶ U_{i₀} ×_X W` attached to a
  morphism `W ⟶ U_{i₀}`, as a morphism into the degree-zero Čech object.

## Main results

* `Stacks.CechSite.SheafLevel.sectionsOver_map_restriction`: on sections over `W`, the transition
  map of `Stacks.CechSite.SheafLevel.restriction` is `F` applied to `prod.map f (𝟙 W)`.
* `Stacks.CechSite.SheafLevel.exactAt_mapHomologicalComplex_complexFunctor`: the sections over
  `W` of the sheaf-level Čech complex are exact in every positive degree, when `W` maps to a
  member of the family.
* `Stacks.CechSite.SheafLevel.exactAt_complexFunctor_of_coversTop`: **the sheaf-level Čech
  complex of a family covering a terminal object is exact in every positive degree.**
* `Stacks.CechSite.SheafLevel.isSheaf_prodRestriction`: the coefficients `V ↦ F(W ⨯ V)` of the
  sections complex are a sheaf, being the underlying presheaf of `j_{W,*} j_W^{-1} F`.
* `Stacks.CechSite.SheafLevel.mono_augmentation_of_coversTop`: **the augmentation of the
  sheaf-level Čech complex of a family covering a terminal object is a monomorphism.**

## Implementation notes

Three mechanisms compose into `complexFunctorSectionsIso`, and none of them is a comparison that
has to be built here.

*Change of coefficient category.*  Sections over `W` is the functor
`Stacks.SheafOfModules.WeaklyContractible.sectionsOver R W`, the composite of
`CategoryTheory.SheafOfModules.forget`, `CategoryTheory.PresheafOfModules.toPresheaf` and
evaluation at `op W`.  Each factor is additive and preserves products indexed by the universe of
the modules, so `Stacks.CategoryTheory.CechComplex.mapCoeffIso` carries it through the Čech
construction.  This is why the modules, the index type of the family and the abelian groups are
all taken in one universe `w`: Mathlib's products of sheaves of modules exist for shapes in the
universe of the modules, so `HasProducts.{w} (SheafOfModules.{w} R)` — already a hypothesis of
`Stacks.CechSite.SheafLevel.complexFunctor` — is only available in that case anyway.

*Change of coefficient presheaf.*  `diagramObjSectionsIso` identifies the resulting coefficients
with `V ↦ F(W ⨯ V)`.  Its two sides have the *same* underlying groups: the sections of
`j_{V,*} j_V^{-1} F` over `W` are the sections of `F` over `V ⨯ W`, on the nose, because
`CategoryTheory.SheafOfModules.pushforwardOver` is pushforward along `CategoryTheory.Over.star`.
What is not on the nose is the *order* of the factors, so the comparison is the braiding
`V ⨯ W ≅ W ⨯ V`, and its naturality is `CategoryTheory.Limits.braid_natural`.  The one point
needing care is that the two descriptions of a transition map — `F` applied to
`(Limits.prod.functor.map f).app W`, which is what `restriction` is defined by, and `F` applied
to `Limits.prod.map f (𝟙 W)`, which is what the braiding square is stated with — are equal but
not syntactically so; `sectionsOver_map_restriction` records the identification once, on sections,
and the naturality square is then proved by an explicit term rather than by `rw`, because once a
goal mentions both the `sectionsOver`-spelling and the `F.val.presheaf`-spelling of the same group
it is reported as not type-correct at `implicit` transparency.  This is the obstruction documented
at `Stacks.CechSite.SheafLevel.starMap_comp_snd`.

*Change of ambient category.*  The sheaf-level complex is built from the fibre products
`U_{i_0} ×_X ⋯ ×_X U_{i_p}`, i.e. from products in the slice `Over X`, whereas the complex of
`Stacks.CechObjectFamily.exactAt_cechComplexFunctor_prodRestriction_of_hom` is built from products
in the site.  `Stacks.CechSiteChange.cechComplexFunctorSiteIso` identifies the two along
`CategoryTheory.Over.forget X`, which it asks to preserve finite products — and that is exactly
where **terminality of `X`** enters: `CategoryTheory.Over.forget X` is the functor of
`CategoryTheory.Over.equivalenceOfIsTerminal`, on the nose, hence an equivalence.

**Terminality is not a convenience hypothesis.**  For a non-terminal `X` the sheaf-level complex
is not a resolution of `F` at all: for the one-member family given by `𝟙 X` every term of it is
`j_{X,*} j_X^{-1} F`, the first differential vanishes, and the augmentation is `F` applied to the
projection `X ⨯ Y ⟶ Y` on sections over `Y` — by
`Stacks.CechSite.SheafLevel.augmentationAt_apply` — which is not an isomorphism.  Terminality is
also exactly what the intended application supplies: [Stacks, Tag 071N] resolves a module on the
small étale site *of* `X`, where `X` is terminal
(`AlgebraicGeometry.SmallEtale.finalIsTerminal`).

**What is not here: the quasi-isomorphism.**  Nothing below says that the augmentation
`Stacks.CechSite.SheafLevel.augmentationHom` is a quasi-isomorphism, and it does not follow from
what is proved here.  By `CochainComplex.quasiIsoAt₀_iff` and
`CategoryTheory.ShortComplex.quasiIso_iff_of_zeros` that statement is positive-degree exactness
together with the assertion that `F ⟶ Č⁰(E, F)` is a *kernel* of `d⁰`, equivalently — by
`CategoryTheory.ShortComplex.exact_and_mono_f_iff_f_is_kernel` — that it is a monomorphism and
that the short complex `F ⟶ Č⁰ ⟶ Č¹` is exact.  Positive-degree exactness is
`exactAt_complexFunctor_of_coversTop` and the monomorphism is `mono_augmentation_of_coversTop`.

The third piece, exactness of `F ⟶ Č⁰ ⟶ Č¹`, is
`Stacks.CechSite.SheafLevel.exact_shortComplex_augmentation_of_coversTop` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/SheafLevelComplexDegreeZero.lean`, and the
quasi-isomorphism itself is
`Stacks.CechSite.SheafLevel.quasiIso_augmentationHom_of_coversTop` there.  That file takes the
second of the two routes described below: over an object `W` mapping to a member of the family it
writes down a contracting homotopy of the complex of sections, so it uses neither
`isSheaf_prodRestriction` nor `complexFunctorSectionsIso`.  The compatibility the first route
needs — that `complexFunctorSectionsIso` carries the sections of
`Stacks.CechSite.SheafLevel.augmentation` to the augmentation of the Čech complex of `E.X` —
is **still unproved**, and nothing depends on it.

Two routes to it were open, and both need that compatibility.  Either apply
`Stacks.CategoryTheory.CechComplex.isLimitAugmentationFork`, whose sheaf hypothesis is discharged
by `isSheaf_prodRestriction` above and whose covering hypothesis is `hE`; or transport
`CategoryTheory.SimplicialSiteSituation.extraDegeneracy_exact_zero` along
`Stacks.CechSite.cechOpIso`, for the family base-changed to `Over W`, which is split.  The second
is what `SheafLevelComplexDegreeZero.lean` carries out by hand, with the homotopy written down
instead of transported.

## References

* [Stacks Project, Tag 03AT](https://stacks.math.columbia.edu/tag/03AT)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.WeaklyContractible (sectionsOver)
open scoped Simplicial

universe w v u

namespace Stacks.CechSite.SheafLevel

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The sections of a transition map.**  Over `W`, the morphism
`j_{V,*} j_V^{-1} F ⟶ j_{V',*} j_{V'}^{-1} F` of `Stacks.CechSite.SheafLevel.restriction` is `F`
applied to `Limits.prod.map f (𝟙 W) : V' ⨯ W ⟶ V ⨯ W`.

`Stacks.CechSite.SheafLevel.restriction_apply` gives the same formula with the morphism of
products spelled `(Limits.prod.functor.map f).app W`; the two spellings are identified here, once
and for all, by `CategoryTheory.Limits.prod.functor_map_app`. -/
theorem sectionsOver_map_restriction (F : SheafOfModules.{w} R) {V V' : C} (f : V' ⟶ V) (W : C) :
    (sectionsOver.{w} R W).map (restriction R F f) =
      F.val.presheaf.map (prod.map f (𝟙 W)).op := by
  ext x
  exact (restriction_apply R F f (op W) x).trans
    (congrArg (fun h : V' ⨯ W ⟶ V ⨯ W ↦
      (ConcreteCategory.hom (F.val.presheaf.map h.op)) x) (prod.functor_map_app f W))

/-- **The Čech diagram of `F`, read on sections over `W`, is the presheaf `V ↦ F(W ⨯ V)`.**  Both
sides send `V` to the sections of `F` over a product of `V` and `W` — the same group, by the
definition of `CategoryTheory.SheafOfModules.pushforwardOver` — so the comparison is the braiding
`V ⨯ W ≅ W ⨯ V`, and its naturality is `CategoryTheory.Limits.braid_natural`. -/
noncomputable def diagramObjSectionsIso (F : SheafOfModules.{w} R) (W : C) :
    (Over.star W ⋙ Over.forget W).op ⋙ F.val.presheaf ≅
      diagramObj R F ⋙ sectionsOver.{w} R W :=
  NatIso.ofComponents (fun Y ↦ F.val.presheaf.mapIso (prod.braiding Y.unop W).op)
    (fun {Y Z} g ↦ by
      have key : ((prod.map (𝟙 W) g.unop).op ≫ (prod.braiding Z.unop W).hom.op) =
          ((prod.braiding Y.unop W).hom.op ≫ (prod.map g.unop (𝟙 W)).op) := by
        rw [← op_comp, ← op_comp, braid_natural g.unop (𝟙 W)]
      change F.val.presheaf.map (prod.map (𝟙 W) g.unop).op ≫
          F.val.presheaf.map (prod.braiding Z.unop W).hom.op =
        F.val.presheaf.map (prod.braiding Y.unop W).hom.op ≫
          F.val.presheaf.map (prod.map g.unop (𝟙 W)).op
      exact (F.val.presheaf.map_comp _ _).symm.trans
        ((congrArg F.val.presheaf.map key).trans (F.val.presheaf.map_comp _ _)))

section Complex

variable [HasFiniteProducts C] {X : C} (E : PreZeroHypercover.{w} X)
  [HasFiniteProducts (Over X)] [HasProducts.{w} (SheafOfModules.{w} R)]

/-- **The sections over `W` of the sheaf-level Čech complex, for a family whose target is
terminal**: they are the Čech complex of the family of *objects* `E.X` with coefficients in the
presheaf of abelian groups `V ↦ F(W ⨯ V)`.

Three steps, in order: the sections functor is carried through the Čech construction by
`Stacks.CategoryTheory.CechComplex.mapCoeffIso`; the resulting coefficients are rewritten by
`Stacks.CechSite.SheafLevel.diagramObjSectionsIso`; and the ambient category is changed from the
slice `Over X` to the site by `Stacks.CechSiteChange.cechComplexFunctorSiteIso`, which applies
because `CategoryTheory.Over.forget X` is the functor of
`CategoryTheory.Over.equivalenceOfIsTerminal hX` and so preserves finite products.

The hypothesis `hX : IsTerminal X` cannot be dropped: see the implementation notes of this
file. -/
noncomputable def complexFunctorSectionsIso (hX : IsTerminal X) (F : SheafOfModules.{w} R)
    (W : C) :
    ((sectionsOver.{w} R W).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((complexFunctor R E).obj F) ≅
      (_root_.CategoryTheory.cechComplexFunctor E.X).obj
        ((Over.star W ⋙ Over.forget W).op ⋙ F.val.presheaf) :=
  haveI : (Over.forget X).IsEquivalence :=
    (Over.equivalenceOfIsTerminal hX).isEquivalence_functor
  Stacks.CategoryTheory.CechComplex.mapCoeffIso (fun i ↦ Over.mk (E.f i))
      ((Over.forget X).op ⋙ diagramObj R F) (sectionsOver.{w} R W) ≪≫
    ((_root_.CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (E.f i))).mapIso
      (Functor.isoWhiskerLeft (Over.forget X).op (diagramObjSectionsIso R F W))).symm ≪≫
    ((Stacks.CechSiteChange.cechComplexFunctorSiteIso (A := AddCommGrpCat.{w})
      (Over.forget X) (fun i ↦ Over.mk (E.f i))).app _).symm

/-- **The sections over `W` of the sheaf-level Čech complex are exact in every positive degree**,
as soon as `W` admits a morphism `q` to a member of the family and the target of the family is
terminal.

This is `Stacks.CechObjectFamily.exactAt_cechComplexFunctor_prodRestriction_of_hom` read through
`Stacks.CechSite.SheafLevel.complexFunctorSectionsIso`.  No hypothesis is placed on the family
itself: it need not be covering. -/
theorem exactAt_mapHomologicalComplex_complexFunctor (hX : IsTerminal X)
    (F : SheafOfModules.{w} R) (W : C) [HasFiniteProducts (Over W)] {i₀ : E.I₀} (q : W ⟶ E.X i₀)
    (n : ℕ) (hn : 0 < n) :
    (((sectionsOver.{w} R W).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      ((complexFunctor R E).obj F)).ExactAt n :=
  (Stacks.CechObjectFamily.exactAt_cechComplexFunctor_prodRestriction_of_hom
    E.X W F.val.presheaf q n hn).of_iso (complexFunctorSectionsIso R E hX F W).symm

end Complex

section Locality

variable [HasFiniteProducts C] {X : C} (E : PreZeroHypercover.{w} X)
  [HasFiniteProducts (Over X)] [HasProducts.{w} (SheafOfModules.{w} R)]
  [∀ W : C, HasFiniteProducts (Over W)]
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [HasFiniteProducts (Over X)] in
/-- **The sheaf-level Čech complex of a family covering a terminal object is exact in every
positive degree.**

`E.X` is required to cover the terminal object `X` of the site, and no section of any member is
assumed — this is the statement for a general covering family, which
`Stacks.CechSite.SheafLevel.exactAt_complexFunctor_of_section` is not.  The proof is the locality
criterion `Stacks.SheafOfModules.ComplexLocality.exactAt_of_coversTop`: over an object `W` mapping
to a member of the family the sections are exact by
`Stacks.CechSite.SheafLevel.exactAt_mapHomologicalComplex_complexFunctor`, and
`CategoryTheory.ShortComplex.ab_exact_iff` turns that exactness into the sectionwise statement the
criterion consumes.

This is positive-degree exactness only.  It is **not** the statement that the augmentation
`Stacks.CechSite.SheafLevel.augmentationHom` is a quasi-isomorphism; the degree-zero half of that
is still owed, as recorded in the implementation notes of this file. -/
theorem exactAt_complexFunctor_of_coversTop (hX : IsTerminal X) (hE : J.CoversTop E.X)
    (F : SheafOfModules.{w} R) (n : ℕ) (hn : 0 < n) :
    ((complexFunctor R E).obj F).ExactAt n := by
  refine Stacks.SheafOfModules.ComplexLocality.exactAt_of_coversTop _ n hE
    (fun i₀ W q z hz ↦ ?_)
  have hex := exactAt_mapHomologicalComplex_complexFunctor R E hX F W q n hn
  rw [HomologicalComplex.exactAt_iff, ShortComplex.ab_exact_iff] at hex
  exact hex z hz

end Locality

section DegreeZero

omit [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The coefficients of the sections complex are the underlying presheaf of
`j_{W,*} j_W^{-1} F`, on the nose.**  Both are the presheaf `V ↦ F(W ⨯ V)` with the restriction
maps of `F`; the left-hand side is the spelling
`Stacks.CechObjectFamily.exactAt_cechComplexFunctor_prodRestriction_of_hom` and
`Stacks.CechSite.SheafLevel.complexFunctorSectionsIso` use, the right-hand side carries a sheaf
structure. -/
theorem prodRestriction_eq_directImage_presheaf (F : SheafOfModules.{w} R) (W : C) :
    (Over.star W ⋙ Over.forget W).op ⋙ F.val.presheaf =
      ((directImage R W).obj F).val.presheaf := rfl

omit [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The coefficients of the sections complex are a sheaf.**  The presheaf `V ↦ F(W ⨯ V)` is the
underlying presheaf of abelian groups of the sheaf of modules `j_{W,*} j_W^{-1} F`, by
`Stacks.CechSite.SheafLevel.prodRestriction_eq_directImage_presheaf`, so it satisfies the sheaf
condition for nothing.

This is the hypothesis that `Stacks.CategoryTheory.CechComplex.isLimitAugmentationFork` — the
degree-zero kernel property of a Čech complex — asks of its coefficients, and it is recorded here
because it is the one input to the degree-zero half of the resolution that needs no new
mathematics; see the implementation notes of this file for what that half still needs. -/
theorem isSheaf_prodRestriction (F : SheafOfModules.{w} R) (W : C) :
    Presheaf.IsSheaf J ((Over.star W ⋙ Over.forget W).op ⋙ F.val.presheaf) :=
  ((directImage R W).obj F).isSheaf

/-- **The sections of the augmentation at one object.**  Over `W`, the unit
`F ⟶ j_{V,*} j_V^{-1} F` is `F` applied to the second projection `V ⨯ W ⟶ W`.  This is
`Stacks.CechSite.SheafLevel.augmentationAt_apply` as an equality of morphisms of abelian
groups. -/
theorem sectionsOver_map_augmentationAt (F : SheafOfModules.{w} R) (V W : C) :
    (sectionsOver.{w} R W).map (augmentationAt R F V) =
      F.val.presheaf.map (prod.snd : V ⨯ W ⟶ W).op := by
  ext x
  exact augmentationAt_apply R F V (op W) x

/-- **The sections of the augmentation at `V` are a split monomorphism once `W` maps to `V`.**
A morphism `s : W ⟶ V` retracts `F(W) ⟶ F(V ⨯ W)`, the retraction being `F` applied to
`Limits.prod.lift s (𝟙 W)`, because `prod.lift s (𝟙 W) ≫ prod.snd = 𝟙 W`. -/
theorem sectionsOver_map_augmentationAt_comp_prodLift (F : SheafOfModules.{w} R) {V W : C}
    (s : W ⟶ V) :
    (sectionsOver.{w} R W).map (augmentationAt R F V) ≫
      F.val.presheaf.map (prod.lift s (𝟙 W)).op = 𝟙 _ := by
  have key : (prod.snd : V ⨯ W ⟶ W).op ≫ (prod.lift s (𝟙 W)).op = 𝟙 (op W) := by
    rw [← op_comp, prod.lift_snd, op_id]
  have h2 : F.val.presheaf.map (prod.snd : V ⨯ W ⟶ W).op ≫
      F.val.presheaf.map (prod.lift s (𝟙 W)).op = 𝟙 _ :=
    ((F.val.presheaf.map_comp _ _).symm.trans
      (congrArg F.val.presheaf.map key)).trans (F.val.presheaf.map_id _)
  ext x
  exact (congrArg (ConcreteCategory.hom (F.val.presheaf.map (prod.lift s (𝟙 W)).op))
    (augmentationAt_apply R F V (op W) x)).trans (ConcreteCategory.congr_hom h2 x)

variable [HasFiniteProducts C] {X : C} (E : PreZeroHypercover.{w} X)
  [HasFiniteProducts (Over X)] [HasProducts.{w} (SheafOfModules.{w} R)]

/-- **The diagonal section of the degree-zero Čech object.**  When `X` is terminal, a morphism
`q : W ⟶ U_{i₀}` is the same as a morphism of `Over X`, so it lifts to the one-fold fibre product
of `U_{i₀}` with itself that indexes the constant tuple `i₀` in degree zero. -/
noncomputable def degreeZeroDiagonal (hX : IsTerminal X) {W : C} {i₀ : E.I₀} (q : W ⟶ E.X i₀) :
    W ⟶ (((Stacks.CechSite.cechSimplicialObject E).obj
      (op (⦋0⦌ : SimplexCategory))).obj (fun _ ↦ i₀)).left :=
  (Pi.lift (fun _ : Fin 1 ↦
    (Over.homMk q (hX.hom_ext _ _) : Over.mk (hX.from W) ⟶ Over.mk (E.f i₀)))).left

omit [HasFiniteProducts C] in
/-- **The augmentation of the sheaf-level Čech complex is injective on sections over an object
mapping to a member of the family.**  Composing the sections over `W` of the augmentation with
the `i₀`-th projection and then restricting along the diagonal
`Stacks.CechSite.SheafLevel.degreeZeroDiagonal` gives the identity of `F(W)`: the first two
composites give the unit `F ⟶ j_{V,*} j_V^{-1} F` by
`Stacks.CechSite.SheafLevel.augmentation_comp_pi`, whose sections over `W` are `F` applied to
`Limits.prod.snd`, and `prod.lift s (𝟙 W) ≫ prod.snd = 𝟙 W`.

The projection is obtained as an anonymous factorization rather than written out, because the
index type of the degree-zero product carries the whole Čech cosimplicial object in its
elaborated form. -/
theorem mono_sectionsOver_map_augmentation (hX : IsTerminal X) (F : SheafOfModules.{w} R)
    {W : C} {i₀ : E.I₀} (q : W ⟶ E.X i₀) :
    Mono ((sectionsOver.{w} R W).map (augmentation R E F)) := by
  obtain ⟨g, hg⟩ : ∃ g, augmentation R E F ≫ g = augmentationAt R F
      (((Stacks.CechSite.cechSimplicialObject E).obj
        (op (⦋0⦌ : SimplexCategory))).obj (fun _ ↦ i₀)).left :=
    ⟨_, augmentation_comp_pi R E F (fun _ : Fin 1 ↦ i₀)⟩
  have hfac : (sectionsOver.{w} R W).map (augmentation R E F) ≫
      ((sectionsOver.{w} R W).map g ≫
        F.val.presheaf.map (prod.lift (degreeZeroDiagonal E hX q) (𝟙 W)).op) = 𝟙 _ :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun φ ↦ φ ≫ F.val.presheaf.map
            (prod.lift (degreeZeroDiagonal E hX q) (𝟙 W)).op)
          (((sectionsOver.{w} R W).map_comp _ _).symm.trans
            (congrArg (sectionsOver.{w} R W).map hg))).trans
        (sectionsOver_map_augmentationAt_comp_prodLift R F (degreeZeroDiagonal E hX q)))
  rw [AddCommGrpCat.mono_iff_injective]
  intro a b hab
  have key : ∀ x, (ConcreteCategory.hom
      ((sectionsOver.{w} R W).map g ≫
        F.val.presheaf.map (prod.lift (degreeZeroDiagonal E hX q) (𝟙 W)).op))
      ((ConcreteCategory.hom ((sectionsOver.{w} R W).map (augmentation R E F))) x) = x :=
    fun x ↦ ConcreteCategory.congr_hom hfac x
  exact (key a).symm.trans ((congrArg (ConcreteCategory.hom
    ((sectionsOver.{w} R W).map g ≫
      F.val.presheaf.map (prod.lift (degreeZeroDiagonal E hX q) (𝟙 W)).op)) hab).trans (key b))

section Mono

variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [HasFiniteProducts C] in
/-- **The augmentation of the sheaf-level Čech complex of a family covering a terminal object is
a monomorphism.**

This is one of the two halves of the degree-zero statement that
`Stacks.CechSite.SheafLevel.augmentationHom` is a quasi-isomorphism; the other, exactness of
`F ⟶ Č⁰ ⟶ Č¹`, is not proved here.  Being a monomorphism is read off the locality criterion
`Stacks.SheafOfModules.ComplexLocality.exact_of_coversTop` through
`CategoryTheory.ShortComplex.exact_iff_mono`, applied to the short complex whose first map is
zero: over an object mapping to a member of the family the augmentation is a split monomorphism
on sections, by `Stacks.CechSite.SheafLevel.mono_sectionsOver_map_augmentation`. -/
theorem mono_augmentation_of_coversTop (hX : IsTerminal X) (hE : J.CoversTop E.X)
    (F : SheafOfModules.{w} R) : Mono (augmentation R E F) := by
  rw [← ShortComplex.exact_iff_mono
    (S := ShortComplex.mk (0 : F ⟶ F) (augmentation R E F) zero_comp) rfl]
  refine Stacks.SheafOfModules.ComplexLocality.exact_of_coversTop hE _
    (fun i₀ W q z hz ↦ ⟨z, ?_⟩)
  have hm := mono_sectionsOver_map_augmentation R E hX F q
  rw [AddCommGrpCat.mono_iff_injective] at hm
  exact (hm (hz.trans (map_zero _).symm)).symm

end Mono

end DegreeZero

end Stacks.CechSite.SheafLevel

end
