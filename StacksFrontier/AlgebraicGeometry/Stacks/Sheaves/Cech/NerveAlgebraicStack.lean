module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointSubstackExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.NerveFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack

/-!
# The terms of the Čech nerve of a 1-morphism of algebraic stacks are algebraic stacks

Let `f : 𝒰 ⟶ 𝒳` be a 1-morphism of algebraic stacks over `S`. The degree `n` term of its
relative Čech nerve, `Stacks.RelativeCech.Tuple`, is the category of `n + 1` objects of `𝒰` over a
common object of `𝒳`, lying over the site through that common object. It is the
`(n + 1)`-fold 2-fibre product `𝒰 ×_𝒳 ⋯ ×_𝒳 𝒰` (**Stacks 06X3**), hence an algebraic stack by
**Stacks 04TF**. This file proves that, and packages the term with its projection to `𝒳` as an
object and a 1-morphism of the 2-category of algebraic stacks, so that the relative Čech
spectral sequences of **Stacks 072D** and **Stacks 072E**, whose terms are the categories
`Stacks.RelativeCech.Tuple` over the site through the projection, are read as statements about
1-morphisms of algebraic stacks.

## Main definitions

* `Stacks.RelativeCech.nerveToFibreProduct`: the functor `U_{n + 1} ⥤ U ×_X U_n` splitting off
  the first coordinate of a tuple. Unlike its quasi-inverse
  `Stacks.RelativeCech.fibreProductToNerve` it is strictly compatible with the functors to the
  base, which is what transporting a property of categories over the base along it needs.
* `Stacks.RelativeCech.toTupleZero`: the functor `U ⥤ U_0` sending an object to the one-term tuple
  over its image, likewise strictly over the base.
* `AlgebraicGeometry.Stack.AlgebraicStacks.cechNerveTerm` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.cechNerveProjection`: the degree `n` term of the Čech
  nerve of `f`, as an algebraic stack, and its projection to `𝒳`.

## Main results

* `Stacks.RelativeCech.isEquivalence_nerveToFibreProduct` and
  `Stacks.RelativeCech.isEquivalence_toTupleZero`: both functors are equivalences.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAlgebraicStack_tuple`: the degree `n` term of the
  Čech nerve of a 1-morphism of algebraic stacks is an algebraic stack.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_cechNerveSquare_precompose`: the
  degree `n + 1` term is the 2-fibre product `𝒰 ×_𝒳 U_n` in the 2-category of algebraic stacks,
  its projection being the base change of `f` followed by the projection of the degree `n` term
  (`AlgebraicGeometry.Stack.AlgebraicStacks.cechNerveProjection_succ`).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiCompactMorphism_cechNerveProjection`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_cechNerveProjection` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_cechNerveProjection`: the projections of the
  Čech nerve of a quasi-compact, quasi-separated, resp. smooth 1-morphism are quasi-compact,
  quasi-separated, resp. smooth, by base change and composition (Stacks 050V and 050W; Stacks
  050K and the base change of quasi-separated 1-morphisms; Stacks 075W and 075V).

## Implementation notes

The structure functor of the degree `n` term is `Tuple.projection ⋙ p` for the structure functor
`p` of `𝒳`, which is the presentation `Stacks.RelativeCech.ModulePushforwardSpectralSequenceData`
and `Stacks.RelativeCech.PushforwardSpectralSequenceData` use; so the source of
`AlgebraicGeometry.Stack.AlgebraicStacks.cechNerveProjection` has, definitionally, the structure
functor those spectral sequences are stated over, and the underlying functor of the projection is
`Tuple.projection` itself.

The induction runs along the strict functors: in degree `0` the based functor `𝒰 ⥤ U_0`, in
degree `n + 1` the based functor `U_{n + 1} ⥤ U ×_X U_n`; an equivalence of categories fibred in
groupoids which is strictly over the base transports algebraicity
(`AlgebraicGeometry.Stack.isAlgebraicStack_iff_of_isEquivalence`, **Stacks 03YQ**).

## References

* [Stacks Project, Tag 06X3](https://stacks.math.columbia.edu/tag/06X3)
* [Stacks Project, Tag 04TF](https://stacks.math.columbia.edu/tag/04TF)
* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
* [Stacks Project, Tag 072D](https://stacks.math.columbia.edu/tag/072D)
* [Stacks Project, Tag 072E](https://stacks.math.columbia.edu/tag/072E)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.RelativeCech

universe vC vU vX uC uU uX

variable {C : Type uC} [Category.{vC} C] {U : Type uU} [Category.{vU} U]
  {X : Type uX} [Category.{vX} X] (p : X ⥤ C) (f : U ⥤ X)

/-- The functor `U_{n + 1} ⥤ U ×_X U_n` splitting off the first coordinate of a tuple: the first
coordinate, the tuple of the remaining ones, and the first comparison isomorphism, over the image
in `C` of the common target. It is strictly compatible with the functors to `C`.

The functor `pU : U ⥤ C` along which the first factor lies over `C` is any functor equal to
`f ⋙ p`; for a 1-morphism of categories fibred in groupoids it is the structure functor of the
source, which agrees with `f ⋙ p` only propositionally. -/
def nerveToFibreProduct (pU : U ⥤ C) (hpU : f ⋙ p = pU) (n : ℕ) :
    Tuple p f (n + 1) ⥤ TwoFibreProductOver pU (Tuple.projection p f n ⋙ p) p f
      (Tuple.projection p f n) where
  obj A :=
    haveI := A.comparison_lift 0
    { base := p.obj A.target
      x := A.source 0
      y := (Tuple.reindex p f (Fin.succ : Fin (n + 1) → Fin (n + 2))).obj A
      hx := by
        rw [← hpU]
        exact IsHomLift.domain_eq p (𝟙 (p.obj A.target)) (A.comparison 0).hom
      hy := rfl
      iso := A.comparison 0
      vertical := A.comparison_lift 0 }
  map {A A'} g :=
    { hbase := p.map g.target
      a := Tuple.Hom.source g 0
      b := (Tuple.reindex p f (Fin.succ : Fin (n + 1) → Fin (n + 2))).map g
      ha := by
        subst hpU
        exact tuple_source_isHomLift p f g 0 (p.map g.target)
      hb := IsHomLift.map (Tuple.projection p f n ⋙ p)
        ((Tuple.reindex p f (Fin.succ : Fin (n + 1) → Fin (n + 2))).map g)
      w := Tuple.Hom.comparison_naturality g 0 }
  map_id _ := TwoFibreProductOver.Hom.ext' rfl rfl
  map_comp _ _ := TwoFibreProductOver.Hom.ext' rfl rfl

/-- Splitting off the first coordinate is strictly over the base: the base object of the image
of a tuple is the image of its common target. -/
theorem nerveToFibreProduct_comp_structureFunctor (pU : U ⥤ C) (hpU : f ⋙ p = pU) (n : ℕ) :
    nerveToFibreProduct p f pU hpU n ⋙ TwoFibreProductOver.structureFunctor pU
        (Tuple.projection p f n ⋙ p) p f (Tuple.projection p f n) =
      Tuple.projection p f (n + 1) ⋙ p :=
  rfl

/-- Splitting off the first coordinate and prepending it again is the identity, up to the
canonical isomorphism of tuples. -/
def nerveToFibreProductCompIso (n : ℕ) :
    nerveToFibreProduct p f (f ⋙ p) rfl n ⋙ fibreProductToNerve p f n ≅ 𝟭 (Tuple p f (n + 1)) :=
  NatIso.ofComponents
    (fun A => Stacks.Cech.tupleIso (Iso.refl A.target)
      (Fin.cons (Iso.refl _) fun _ => Iso.refl _) (by
        refine Fin.cases ?_ (fun j => ?_)
        · change f.map (𝟙 (A.source 0)) ≫ (A.comparison 0).hom
            = (A.comparison 0).hom ≫ 𝟙 A.target
          simp
        · change f.map (𝟙 (A.source j.succ)) ≫ (A.comparison j.succ).hom
            = (A.comparison j.succ).hom ≫ 𝟙 A.target
          simp))
    (fun {A A'} g => by
      refine Stacks.Cech.tupleHom_ext ?_ (funext fun i => ?_)
      · change g.target ≫ 𝟙 _ = 𝟙 _ ≫ g.target
        simp
      · refine Fin.cases ?_ (fun j => ?_) i
        · change Tuple.Hom.source g 0 ≫ 𝟙 _ = 𝟙 _ ≫ Tuple.Hom.source g 0
          simp
        · change Tuple.Hom.source g j.succ ≫ 𝟙 _ = 𝟙 _ ≫ Tuple.Hom.source g j.succ
          simp)

/-- **Stacks 06X3, read strictly over the base.** Splitting off the first coordinate is an
equivalence `U_{n + 1} ⥤ U ×_X U_n`: for `pU = f ⋙ p` it is a section of the equivalence
`Stacks.RelativeCech.fibreProductToNerve`. -/
theorem isEquivalence_nerveToFibreProduct (pU : U ⥤ C) (hpU : f ⋙ p = pU) (n : ℕ) :
    (nerveToFibreProduct p f pU hpU n).IsEquivalence := by
  subst hpU
  have := isEquivalence_fibreProductToNerve p f n
  have : (nerveToFibreProduct p f (f ⋙ p) rfl n ⋙ fibreProductToNerve p f n).IsEquivalence :=
    Functor.isEquivalence_of_iso (nerveToFibreProductCompIso p f n).symm
  exact Functor.isEquivalence_of_comp_right _ (fibreProductToNerve p f n)

/-- The functor `U ⥤ U_0` sending an object of `U` to the one-term tuple over its image, with the
identity as comparison isomorphism. It is strictly compatible with the functors to `C`. -/
def toTupleZero : U ⥤ Tuple p f 0 where
  obj u :=
    { target := f.obj u
      source := fun _ => u
      comparison := fun _ => Iso.refl _
      comparison_lift := fun _ => IsHomLift.id rfl }
  map g :=
    { target := f.map g
      source := fun _ => g
      comparison_naturality := fun _ => by simp }
  map_id _ := Stacks.Cech.tupleHom_ext (f.map_id _) rfl
  map_comp _ _ := Stacks.Cech.tupleHom_ext (f.map_comp _ _) rfl

/-- **Stacks 06X3 in degree zero, read strictly over the base.** The functor `U ⥤ U_0` is an
equivalence: it is a section of the equivalence reading off the single coordinate. -/
theorem isEquivalence_toTupleZero : (toTupleZero p f).IsEquivalence := by
  have := isEquivalence_coordinate_zero p f
  have : (toTupleZero p f ⋙ Tuple.coordinate p f (0 : Fin 1)).IsEquivalence :=
    Functor.isEquivalence_of_iso (Iso.refl (𝟭 U))
  exact Functor.isEquivalence_of_comp_right _ (Tuple.coordinate p f (0 : Fin 1))

end Stacks.RelativeCech

namespace AlgebraicGeometry.Stack.AlgebraicStacks

open Stacks.RelativeCech

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The source of a 1-morphism of algebraic stacks, presented by the morphism's functor followed
by the structure functor of the target, is an algebraic stack: the presentation is the structure
functor of the source. -/
theorem isAlgebraicStack_homFunctor_comp {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳) :
    IsAlgebraicStack.{u, w} B S hS
      (BasedCategory.ofFunctor (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒳.val.val.p)) := by
  have h : BasedCategory.ofFunctor (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒳.val.val.p) =
      𝒰.val.val :=
    congrArg BasedCategory.ofFunctor (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
  rw [h]
  exact 𝒰.property

/-- **The terms of the Čech nerve of a 1-morphism of algebraic stacks are algebraic stacks.** For
`f : 𝒰 ⟶ 𝒳` and every `n`, the category `Stacks.RelativeCech.Tuple` of `n + 1` objects of `𝒰`
over a common object of `𝒳`, over the site through that common object, is an algebraic stack.

By induction on `n`: the degree `0` term is `𝒰` (**Stacks 06X3**), and the degree `n + 1` term is
the 2-fibre product `𝒰 ×_𝒳 U_n` (**Stacks 06X3**), an algebraic stack by **Stacks 04TF**;
algebraicity transports along both equivalences, which are strictly over the base
(**Stacks 03YQ**). -/
theorem isAlgebraicStack_tuple {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳) (n : ℕ) :
    IsAlgebraicStack.{u, w} B S hS (BasedCategory.ofFunctor
      (Tuple.projection 𝒳.val.val.p (CatFiberedInGroupoids.homFunctor f.hom) n ⋙
        𝒳.val.val.p)) := by
  have h𝒰 := isAlgebraicStack_homFunctor_comp B S hS f
  have hfib : (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒳.val.val.p).IsFiberedInGroupoids :=
    h𝒰.1
  have htup : ∀ m, (Tuple.projection 𝒳.val.val.p (CatFiberedInGroupoids.homFunctor f.hom) m ⋙
      𝒳.val.val.p).IsFiberedInGroupoids := fun m =>
    tuple_isFiberedInGroupoids 𝒳.val.val.p _ hfib 𝒳.val.isFiberedInGroupoids m
  induction n with
  | zero =>
    let a : BasedCategory.ofFunctor (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒳.val.val.p) ⥤ᵇ
        BasedCategory.ofFunctor (Tuple.projection 𝒳.val.val.p
          (CatFiberedInGroupoids.homFunctor f.hom) 0 ⋙ 𝒳.val.val.p) :=
      { toFunctor := toTupleZero 𝒳.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
        w := rfl }
    exact (isAlgebraicStack_iff_of_isEquivalence.{u, u, u + 1, w} B S hS a hfib (htup 0)
      (isEquivalence_toTupleZero _ _)).1 h𝒰
  | succ n ih =>
    obtain ⟨_, h𝒳stack, h𝒳diag, -⟩ := 𝒳.property
    have hP := isAlgebraicStack_twoFibreProduct B S hS
      (BasedCategory.ofFunctor (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒳.val.val.p))
      (BasedCategory.ofFunctor (Tuple.projection 𝒳.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) n ⋙ 𝒳.val.val.p)) 𝒳.val.val
      { toFunctor := CatFiberedInGroupoids.homFunctor f.hom, w := rfl }
      { toFunctor := Tuple.projection 𝒳.val.val.p (CatFiberedInGroupoids.homFunctor f.hom) n,
        w := rfl }
      h𝒳stack h𝒳diag h𝒰 ih
    let a : BasedCategory.ofFunctor (Tuple.projection 𝒳.val.val.p
          (CatFiberedInGroupoids.homFunctor f.hom) (n + 1) ⋙ 𝒳.val.val.p) ⥤ᵇ
        BasedCategory.ofFunctor (TwoFibreProductOver.structureFunctor
          (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒳.val.val.p)
          (Tuple.projection 𝒳.val.val.p (CatFiberedInGroupoids.homFunctor f.hom) n ⋙
            𝒳.val.val.p) 𝒳.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
          (Tuple.projection 𝒳.val.val.p (CatFiberedInGroupoids.homFunctor f.hom) n)) :=
      { toFunctor := nerveToFibreProduct 𝒳.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
          _ rfl n
        w := rfl }
    exact (isAlgebraicStack_iff_of_isEquivalence.{u, u, u + 1, w} B S hS a (htup (n + 1)) hP.1
      (isEquivalence_nerveToFibreProduct _ _ _ rfl n)).2 hP

/-- **The degree `n` term of the Čech nerve of `f : 𝒰 ⟶ 𝒳`, as an algebraic stack.** Its
underlying category is `Stacks.RelativeCech.Tuple` and its structure functor is the projection to
`𝒳` followed by the structure functor of `𝒳`. -/
def cechNerveTerm {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳) (n : ℕ) :
    AlgebraicStacks.{u, w} B S hS :=
  ⟨CatFiberedInGroupoids.mk (BasedCategory.ofFunctor
      (Tuple.projection 𝒳.val.val.p (CatFiberedInGroupoids.homFunctor f.hom) n ⋙ 𝒳.val.val.p))
    (isAlgebraicStack_tuple B S hS f n).1,
    isAlgebraicStack_tuple B S hS f n⟩

/-- **The projection of the degree `n` term of the Čech nerve of `f : 𝒰 ⟶ 𝒳` to `𝒳`**, as a
1-morphism of algebraic stacks; its underlying functor is
`Stacks.RelativeCech.Tuple.projection`. -/
def cechNerveProjection {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳) (n : ℕ) :
    cechNerveTerm B S hS f n ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := Tuple.projection 𝒳.val.val.p (CatFiberedInGroupoids.homFunctor f.hom) n
      w := rfl })

/-- The functor `𝒰 ⥤ U_0` sending an object to its one-term tuple, as a 1-morphism of algebraic
stacks `𝒰 ⟶ U_0` over `𝒳`. Its underlying functor is an equivalence, and followed by the
projection of `U_0` it is `f` on the nose. -/
def toCechNerveTermZero {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳) :
    𝒰 ⟶ cechNerveTerm B S hS f 0 :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := toTupleZero 𝒳.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
      w := CatFiberedInGroupoids.homFunctor_comp_p f.hom })

/-- The one-term tuple of an object of `𝒰`, followed by the projection, is `f`. -/
theorem toCechNerveTermZero_comp_cechNerveProjection {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒰 ⟶ 𝒳) : toCechNerveTermZero B S hS f ≫ cechNerveProjection B S hS f 0 = f :=
  rfl

/-- The canonical 2-fibre product `𝒰 ×_𝒳 U_n` of `f` with the projection of the degree `n` term of
its Čech nerve. -/
abbrev cechNerveSquare {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳)
    (n : ℕ) : Bicategory.TwoCommSq f (cechNerveProjection B S hS f n) :=
  twoFibreProductSquareAlgebraicStacks B S hS f (cechNerveProjection B S hS f n)

/-- Splitting off the first coordinate, as a 1-morphism of algebraic stacks from the degree
`n + 1` term of the Čech nerve to the canonical 2-fibre product `𝒰 ×_𝒳 U_n`. -/
noncomputable def cechNerveSplit {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳) (n : ℕ) :
    cechNerveTerm B S hS f (n + 1) ⟶ (cechNerveSquare B S hS f n).pt :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := nerveToFibreProduct 𝒳.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
        𝒰.val.val.p (CatFiberedInGroupoids.homFunctor_comp_p f.hom) n
      w := rfl })

/-- **The degree `n + 1` term of the Čech nerve is a 2-fibre product `𝒰 ×_𝒳 U_n`** (Stacks 06X3,
in the 2-category of algebraic stacks): the canonical square `𝒰 ×_𝒳 U_n` reindexed along
`AlgebraicGeometry.Stack.AlgebraicStacks.cechNerveSplit`, whose underlying functor is an
equivalence. -/
noncomputable def isTwoFibreProduct_cechNerveSquare_precompose
    {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳) (n : ℕ) :
    Bicategory.IsTwoFibreProduct
      ((cechNerveSquare B S hS f n).precompose (cechNerveSplit B S hS f n)) :=
  Bicategory.isTwoFibreProduct_of_underlying
    (Bicategory.isTwoFibreProduct_of_isEquivalence_to
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        f.hom (cechNerveProjection B S hS f n).hom)
      (Bicategory.TwoCommSq.PreHom.ofPrecompose _ (cechNerveSplit B S hS f n)).underlying
      (isEquivalence_nerveToFibreProduct _ _ _ (CatFiberedInGroupoids.homFunctor_comp_p f.hom) n))

/-- The projection of the degree `n + 1` term of the Čech nerve is the second leg of the 2-fibre
product `𝒰 ×_𝒳 U_n` followed by the projection of the degree `n` term. -/
theorem cechNerveProjection_succ {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳) (n : ℕ) :
    cechNerveProjection B S hS f (n + 1) =
      ((cechNerveSquare B S hS f n).precompose (cechNerveSplit B S hS f n)).snd ≫
        cechNerveProjection B S hS f n :=
  rfl

/-- **A property of 1-morphisms of algebraic stacks which is stable under base change and
composition, and which holds for `f`, holds for every projection of the Čech nerve of `f`**,
provided it holds for the projection of the degree `0` term. The base change clause is asked of
the second leg of a 2-fibre product, along the first. -/
theorem cechNerveProjection_induction (P : ∀ {𝒜 ℬ : AlgebraicStacks.{u, w} B S hS}, (𝒜 ⟶ ℬ) → Prop)
    (hbc : ∀ {𝒜 ℬ 𝒞 : AlgebraicStacks.{u, w} B S hS} (a : 𝒜 ⟶ 𝒞) (b : ℬ ⟶ 𝒞)
      (Q : Bicategory.TwoCommSq a b), Bicategory.IsTwoFibreProduct Q → P a → P Q.snd)
    (hcomp : ∀ {𝒜 ℬ 𝒞 : AlgebraicStacks.{u, w} B S hS} (a : 𝒜 ⟶ ℬ) (b : ℬ ⟶ 𝒞),
      P a → P b → P (a ≫ b))
    {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳) (hf : P f)
    (h0 : P (cechNerveProjection B S hS f 0)) (n : ℕ) :
    P (cechNerveProjection B S hS f n) := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [cechNerveProjection_succ]
    exact hcomp _ _ (hbc _ _ _ (isTwoFibreProduct_cechNerveSquare_precompose B S hS f n) hf) ih

/-- The functor of the one-term tuple has a quasi-inverse which is a 1-morphism of algebraic
stacks `U_0 ⟶ 𝒰`, and the projection of `U_0` is 2-isomorphic to it followed by `f`. -/
theorem exists_cechNerveProjection_zero_iso {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒰 ⟶ 𝒳) :
    ∃ j : cechNerveTerm B S hS f 0 ⟶ 𝒰,
      Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor j.hom) ∧
        Nonempty (j ≫ f ≅ cechNerveProjection B S hS f 0) := by
  obtain ⟨F, hF, η, ε, hη, hε⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over 𝒰.val.val.p
      (cechNerveTerm B S hS f 0).val.val.p 𝒰.val.isFiberedInGroupoids
      (cechNerveTerm B S hS f 0).val.isFiberedInGroupoids
      (toTupleZero 𝒳.val.val.p (CatFiberedInGroupoids.homFunctor f.hom))
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom) (isEquivalence_toTupleZero _ _)
  let j : cechNerveTerm B S hS f 0 ⟶ 𝒰 :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom ⟨F, hF⟩)
  refine ⟨j, (CategoryTheory.Equivalence.mk
    (toTupleZero 𝒳.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)) F η.symm
      ε).isEquivalence_inverse, ⟨?_⟩⟩
  let e : F ⋙ CatFiberedInGroupoids.homFunctor f.hom ≅
      Tuple.projection 𝒳.val.val.p (CatFiberedInGroupoids.homFunctor f.hom) 0 :=
    Functor.isoWhiskerRight ε
      (Tuple.projection 𝒳.val.val.p (CatFiberedInGroupoids.homFunctor f.hom) 0)
  exact Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
    (BasedNatIso.mkNatIso e fun x =>
      (Functor.isHomLift_comp_iff _ 𝒳.val.val.p _ _).1 (hε x)))

/-- **The projections of the Čech nerve of a quasi-compact 1-morphism are quasi-compact.** -/
theorem isQuasiCompactMorphism_cechNerveProjection {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒰 ⟶ 𝒳) (hf : IsQuasiCompactMorphism B S hS f) (n : ℕ) :
    IsQuasiCompactMorphism B S hS (cechNerveProjection B S hS f n) := by
  refine cechNerveProjection_induction B S hS (fun g => IsQuasiCompactMorphism B S hS g)
    (fun a b Q hQ ha => isQuasiCompactMorphism_baseChange B S hS a b Q.swap
      (Bicategory.isTwoFibreProduct_swap hQ) ha)
    (fun a b ha hb => isQuasiCompactMorphism_comp B S hS a b ha hb) f hf ?_ n
  exact isQuasiCompactMorphism_of_comp_of_isSurjective B S hS (toCechNerveTermZero B S hS f) f
    (cechNerveProjection B S hS f 0) (Iso.refl _)
    (isSurjective_of_isEquivalenceFunctor B S hS _ (isEquivalence_toTupleZero _ _)) hf

/-- **The projections of the Čech nerve of a quasi-separated 1-morphism are quasi-separated.** -/
theorem isQuasiSeparated_cechNerveProjection {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒰 ⟶ 𝒳) (hf : AlgebraicStacks.IsQuasiSeparated B S hS f) (n : ℕ) :
    AlgebraicStacks.IsQuasiSeparated B S hS (cechNerveProjection B S hS f n) := by
  refine cechNerveProjection_induction B S hS
    (fun g => AlgebraicStacks.IsQuasiSeparated B S hS g)
    (fun a b Q hQ ha => isQuasiSeparated_baseChange_of_isTwoFibreProduct B S hS a b Q hQ ha)
    (fun a b ha hb => isQuasiSeparated_comp B S hS a b ha hb) f hf ?_ n
  obtain ⟨j, hj, ⟨e⟩⟩ := exists_cechNerveProjection_zero_iso B S hS f
  exact isQuasiSeparated_of_equivalence B S hS f (cechNerveProjection B S hS f 0) j.hom.hom
    (Bicategory.InducedBicategory.isoHom (Bicategory.InducedBicategory.isoHom e)) hj hf

/-- **The projections of the Čech nerve of a smooth 1-morphism are smooth.** -/
theorem isSmooth_cechNerveProjection {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒰 ⟶ 𝒳) (hf : AlgebraicStacks.IsSmooth B S hS f) (n : ℕ) :
    AlgebraicStacks.IsSmooth B S hS (cechNerveProjection B S hS f n) := by
  refine cechNerveProjection_induction B S hS (fun g => AlgebraicStacks.IsSmooth B S hS g)
    (fun a b Q hQ ha => AlgebraicStacks.isSmooth_baseChange B S hS a b Q.swap
      (Bicategory.isTwoFibreProduct_swap hQ) ha)
    (fun a b ha hb => AlgebraicStacks.isSmooth_comp B S hS a b ha hb) f hf ?_ n
  obtain ⟨j, hj, ⟨e⟩⟩ := exists_cechNerveProjection_zero_iso B S hS f
  exact AlgebraicStacks.isSmooth_of_twoIso B S hS e (AlgebraicStacks.isSmooth_comp B S hS j f
    (AlgebraicStacks.isSmooth_of_isEquivalence B S hS j hj) hf)


end AlgebraicGeometry.Stack.AlgebraicStacks

end
