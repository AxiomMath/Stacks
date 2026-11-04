module

public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.NerveAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.UnderlyingTwoFibreProduct
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverCompare
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackRestrictionImmersion
public import StacksFrontier.CategoryTheory.FiberedCategory.CoGrothendieckMapEquivalence
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFieldValuedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedSchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardAffineGeometry

/-!
# Representability of the terms of the Čech nerve of a presentation (the levels of Stacks 076Z)

Let `g : 𝒱 ⟶ 𝒳` be a 1-morphism of algebraic stacks over `S` and let `𝒱ₙ` be the degree `n` term
of its relative Čech nerve, the `(n + 1)`-fold 2-fibre product `𝒱 ×_𝒳 ⋯ ×_𝒳 𝒱`
(`AlgebraicGeometry.Stack.AlgebraicStacks.cechNerveTerm`). The proof of **Stacks 076Z**, and of
**Stacks 0770** which is identical to it, improves the representability of the source of a
quasi-compact quasi-separated 1-morphism into an affine scheme four times, from an algebraic stack
to an algebraic space, a scheme, a separated scheme and finally an affine scheme, each time by
passing to the terms of the Čech nerve of a smooth surjective presentation by an affine scheme.
This file proves those four steps and packages the induction they drive.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.CechLevel`: the five levels — represented by an affine
  scheme, by a separated scheme, by a scheme, by an algebraic space, and arbitrary.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.cechLevel_cechNerveTerm`: the Čech nerve of a
  1-morphism from an affine scheme to a stack at level `k + 1` has all its terms at level `k`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.cechLevel_induction_of_isQuasiCompact`: **the induction
  of the proof of Stacks 076Z.** A property of 1-morphisms into the stack of an affine scheme
  which holds for 1-morphisms out of stacks represented by affine schemes and descends along the
  Čech nerve of a smooth surjective presentation holds for every quasi-compact quasi-separated
  1-morphism.

## Implementation notes

Representability by a scheme `T` of the site is equivalence over the site with the category of
elements of the Yoneda presheaf `h_T`, which is the shape
`AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpace` uses for algebraic spaces. In that shape
the representing presheaf of a 2-fibre product of represented stacks is the fibre product of the
representing presheaves
(`AlgebraicGeometry.Stack.isPullback_representingMap_of_isTwoFibreProduct`), so each step of the
induction is a statement about a fibre product of presheaves: over an algebraic space it is
representable because the diagonal of an algebraic space is; over a scheme it is the Yoneda image
of a fibre product of schemes, which is separated, resp. affine, by Mathlib's
`AlgebraicGeometry.IsSeparated.of_comp` and `AlgebraicGeometry.IsAffineHom.of_comp`.

## References

* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
* [Stacks Project, Tag 0770](https://stacks.math.columbia.edu/tag/0770)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 04YC](https://stacks.math.columbia.edu/tag/04YC)
* [Stacks Project, Tag 050Y](https://stacks.math.columbia.edu/tag/050Y)
* [Stacks Project, Tag 050M](https://stacks.math.columbia.edu/tag/050M)
* [Stacks Project, Tag 06X3](https://stacks.math.columbia.edu/tag/06X3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A 1-morphism of algebraic stacks whose underlying functor is an equivalence of categories is
an equivalence over the big fppf site of `S`: **Stacks 003Z** part (2) supplies a quasi-inverse
over the site with both 2-cells vertical. -/
theorem nonempty_equivalenceOver_of_isEquivalence {𝒜 𝒞 : AlgebraicStacks.{u, w} B S hS}
    (k : 𝒜 ⟶ 𝒞) (hk : (CatFiberedInGroupoids.homFunctor k.hom).IsEquivalence) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver 𝒜.val.val.p 𝒞.val.val.p) := by
  obtain ⟨F, hF, η, ε, hη, hε⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over 𝒜.val.val.p 𝒞.val.val.p
      𝒜.val.isFiberedInGroupoids 𝒞.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor k.hom) (CatFiberedInGroupoids.homFunctor_comp_p k.hom) hk
  refine ⟨StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
    (CatFiberedInGroupoids.homFunctor_comp_p k.hom)
    { inv := F
      inv_over := hF
      unitIso := η
      counitIso := ε
      unit_vertical := fun x => ?_
      counit_vertical := fun x => ?_ }⟩
  · have h : 𝒜.val.val.p.obj ((CatFiberedInGroupoids.homFunctor k.hom ⋙ F).obj x) =
        𝒜.val.val.p.obj x := by
      change ((CatFiberedInGroupoids.homFunctor k.hom ⋙ F) ⋙ 𝒜.val.val.p).obj x = _
      rw [Functor.assoc, hF, CatFiberedInGroupoids.homFunctor_comp_p]
    exact (congrArg (fun U => 𝒜.val.val.p.IsHomLift (𝟙 U) (η.hom.app x)) h).mpr (hη x)
  · have h : 𝒞.val.val.p.obj ((F ⋙ CatFiberedInGroupoids.homFunctor k.hom).obj x) =
        𝒞.val.val.p.obj x := by
      change ((F ⋙ CatFiberedInGroupoids.homFunctor k.hom) ⋙ 𝒞.val.val.p).obj x = _
      rw [Functor.assoc, CatFiberedInGroupoids.homFunctor_comp_p, hF]
    exact (congrArg (fun U => 𝒞.val.val.p.IsHomLift (𝟙 U) (ε.hom.app x)) h).mpr (hε x)

/-- **The terms of the Čech nerve of a 1-morphism out of an algebraic space are algebraic
spaces.** Let `g : 𝒱 ⟶ 𝒳` be a 1-morphism of algebraic stacks with `𝒱` representable by an
algebraic space. Then every term `𝒱ₙ` of its Čech nerve is representable by an algebraic space.

By induction on `n`: `𝒱₀` is equivalent to `𝒱` over the site, and `𝒱ₙ₊₁` is the 2-fibre product
`𝒱 ×_𝒳 𝒱ₙ` (**Stacks 06X3**), whose projection to `𝒱` is a base change of the projection of
`𝒱ₙ`, which is representable by algebraic spaces because its source is an algebraic space and the
diagonal of `𝒳` is representable by algebraic spaces; so **Stacks 0300** applies. -/
theorem isRepresentableByAlgebraicSpace_cechNerveTerm {𝒱 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (g : 𝒱 ⟶ 𝒳) (h𝒱 : IsRepresentableByAlgebraicSpace B S hS 𝒱.val) (n : ℕ) :
    IsRepresentableByAlgebraicSpace B S hS (cechNerveTerm B S hS g n).val := by
  induction n with
  | zero =>
    obtain ⟨j, hj, -⟩ := exists_cechNerveProjection_zero_iso B S hS g
    obtain ⟨e⟩ := nonempty_equivalenceOver_of_isEquivalence B S hS j hj
    exact isRepresentableByAlgebraicSpace_of_equivalenceOver e h𝒱
  | succ n ih =>
    exact isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      (cechNerveTerm B S hS g n).val 𝒳.val 𝒱.val (cechNerveProjection B S hS g n).hom g.hom
      ((cechNerveSquare B S hS g n).precompose (cechNerveSplit B S hS g n)).underlying
      (isTwoFibreProduct_underlying_algebraicStacks B S hS _
        (isTwoFibreProduct_cechNerveSquare_precompose B S hS g n))
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property ih
        (cechNerveProjection B S hS g n).hom)
      h𝒱

/-- Isomorphic presheaves of sets on the big fppf site of `S` have equivalent categories of
elements, over the site: the 1-morphism induced by the isomorphism is an equivalence over the
site, **Stacks 003Z** for the CoGrothendieck construction. -/
noncomputable def equivalenceOverOfIso {T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (ι : T ≅ T') :
    StacksRepresentableCFG.EquivalenceOver (presheafOfCategories (T ⋙ typeToCat)).p
      (presheafOfCategories (T' ⋙ typeToCat)).p :=
  StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
    (presheafOfCategoriesMap_comp (Functor.whiskerRight ι.hom typeToCat))
    (Pseudofunctor.CoGrothendieck.isEquivalenceOver_map _ fun a =>
      (typeToCat.mapIso (ι.app a.as)).isIso_hom)

/-- A stack equivalent over the site to the Yoneda image of an object of the site is representable
by an algebraic space. -/
private theorem isRepresentableByAlgebraicSpace_of_equivalenceOver_yoneda
    {𝒱 : AlgebraicStacks.{u, w} B S hS} {U : BigFppfOver B S hS}
    (eV : StacksRepresentableCFG.EquivalenceOver 𝒱.val.val.p
      (presheafOfCategories (yoneda.obj U ⋙ typeToCat)).p) :
    IsRepresentableByAlgebraicSpace B S hS 𝒱.val :=
  isRepresentableByAlgebraicSpace_of_equivalenceOver eV
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))

/-- **The terms of the Čech nerve of a presentation by a scheme are represented by schemes of a
class closed under the fibre products of the presentation.** Let `g : 𝒱 ⟶ 𝒳` be a 1-morphism of
algebraic stacks, with `𝒳` represented by a presheaf `F` and `𝒱` by the scheme `U`, and let `α`
be the morphism of presheaves `h_U ⟶ F` representing `g`. Let `𝓟` be a class of objects of the
site containing `U` such that for every `W` in `𝓟` and every `β : h_W ⟶ F` the fibre product
`h_U ×_{α, F, β} h_W` is represented by an object of `𝓟`, with second projection represented
by a morphism of the site. Then every term `𝒱ₙ` of the Čech nerve of `g` is represented by an
object of `𝓟`.

By induction on `n`: `𝒱₀` is equivalent to `𝒱`, and `𝒱ₙ₊₁` is the 2-fibre product
`𝒱 ×_𝒳 𝒱ₙ` (**Stacks 06X3**), whose representing presheaf is the fibre product of the
representing presheaves (the dictionary between 2-fibre products of represented categories and
pullbacks of presheaves); the hypothesis on `𝓟` identifies it with a representable presheaf. -/
theorem exists_equivalenceOver_cechNerveTerm_of_isPullback {𝒱 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (g : 𝒱 ⟶ 𝒳) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒳.val.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (U : BigFppfOver B S hS)
    (eV : StacksRepresentableCFG.EquivalenceOver 𝒱.val.val.p
      (presheafOfCategories (yoneda.obj U ⋙ typeToCat)).p)
    (𝓟 : BigFppfOver B S hS → Prop) (hU : 𝓟 U)
    (hpb : ∀ (W : BigFppfOver B S hS), 𝓟 W → ∀ β : yoneda.obj W ⟶ F,
      ∃ (W' : BigFppfOver B S hS) (_ : 𝓟 W') (π₁ : yoneda.obj W' ⟶ yoneda.obj U) (π₂ : W' ⟶ W),
        IsPullback π₁ (yoneda.map π₂)
          (representingMap B S hS 𝒱.val 𝒳.val (yoneda.obj U) F eV eF g.hom) β)
    (n : ℕ) :
    ∃ W : BigFppfOver B S hS, 𝓟 W ∧ Nonempty (StacksRepresentableCFG.EquivalenceOver
      (cechNerveTerm B S hS g n).val.val.p
      (presheafOfCategories (yoneda.obj W ⋙ typeToCat)).p) := by
  have h𝒱 := isRepresentableByAlgebraicSpace_of_equivalenceOver_yoneda B S hS eV
  induction n with
  | zero =>
    obtain ⟨j, hj, -⟩ := exists_cechNerveProjection_zero_iso B S hS g
    obtain ⟨e⟩ := nonempty_equivalenceOver_of_isEquivalence B S hS j hj
    exact ⟨U, hU, ⟨e.trans eV⟩⟩
  | succ n ih =>
    obtain ⟨W, hW, ⟨eW⟩⟩ := ih
    have hproj := isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_cechNerveTerm B S hS g h𝒱 n)
      (cechNerveProjection B S hS g n).hom
    obtain ⟨T, -, ⟨eT⟩⟩ := isRepresentableByAlgebraicSpace_cechNerveTerm B S hS g h𝒱 (n + 1)
    obtain ⟨C, -, ⟨eC⟩⟩ := isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1}
      B S hS (cechNerveTerm B S hS g n).val 𝒳.val 𝒱.val (cechNerveProjection B S hS g n).hom
      g.hom (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom
        (cechNerveProjection B S hS g n).hom)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
      hproj h𝒱
    have hpbT := isPullback_representingMap_of_isTwoFibreProduct B S hS
      (isTwoFibreProduct_underlying_algebraicStacks B S hS _
        (isTwoFibreProduct_cechNerveSquare_precompose B S hS g n))
      (yoneda.obj U) (yoneda.obj W) F T C eV eW eF eT eC
    obtain ⟨W', hW', π₁, π₂, hpb'⟩ := hpb W hW
      (representingMap B S hS (cechNerveTerm B S hS g n).val 𝒳.val (yoneda.obj W) F eW eF
        (cechNerveProjection B S hS g n).hom)
    exact ⟨W', hW', ⟨eT.trans (equivalenceOverOfIso B S hS (hpbT.isoIsPullback _ _ hpb'))⟩⟩

/-! ### Fibre products over an algebraic space, a scheme, a separated scheme -/

/-- **A fibre product of two schemes over an algebraic space is a scheme**: the diagonal of an
algebraic space is representable. -/
theorem exists_isPullback_of_isAlgebraicSpace {H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hH : IsAlgebraicSpace B S hS H) {U : BigFppfOver B S hS} (α : yoneda.obj U ⟶ H)
    (W : BigFppfOver B S hS) (β : yoneda.obj W ⟶ H) :
    ∃ (W' : BigFppfOver B S hS) (π₁ : yoneda.obj W' ⟶ yoneda.obj U) (π₂ : W' ⟶ W),
      IsPullback π₁ (yoneda.map π₂) α β := by
  let _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  obtain ⟨W', π₂, π₁, h⟩ :=
    Functor.relativelyRepresentable.of_diag hH.diagonal_representable α β
  exact ⟨W', π₁, π₂, h⟩

/-- **A fibre product of two objects of the site over a third is represented by the fibre product
in the site**, with the Yoneda images of its projections as the projections. -/
theorem exists_isPullback_yoneda {U X W : BigFppfOver B S hS} (a : U ⟶ X) (b : W ⟶ X) :
    IsPullback (yoneda.map (pullback.fst a b)) (yoneda.map (pullback.snd a b)) (yoneda.map a)
      (yoneda.map b) :=
  (IsPullback.of_hasPullback a b).map yoneda

/-- The underlying scheme of the fibre product in the site is the fibre product of underlying
schemes. -/
noncomputable def toSchemePullbackIso {U X W : BigFppfOver B S hS} (a : U ⟶ X) (b : W ⟶ X) :
    (BigFppfOver.toScheme B S hS).obj (pullback a b) ≅
      pullback ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b) :=
  PreservesPullback.iso (BigFppfOver.toScheme B S hS) a b

/-- **Over a scheme, the fibre product of an affine scheme with a separated scheme is
separated**: a morphism out of a separated scheme is separated, separatedness is stable under
base change and composition. -/
theorem isSeparated_toScheme_pullback {U X W : BigFppfOver B S hS} (a : U ⟶ X) (b : W ⟶ X)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [((BigFppfOver.toScheme B S hS).obj W).IsSeparated] :
    ((BigFppfOver.toScheme B S hS).obj (pullback a b)).IsSeparated := by
  let T := BigFppfOver.toScheme B S hS
  have : AlgebraicGeometry.IsSeparated (T.map a) :=
    AlgebraicGeometry.IsSeparated.of_comp (T.map a) (terminal.from (T.obj X))
  have : AlgebraicGeometry.IsSeparated (pullback.snd (T.map a) (T.map b)) := inferInstance
  have : (pullback (T.map a) (T.map b)).IsSeparated :=
    ⟨by
      rw [show terminal.from (pullback (T.map a) (T.map b)) =
        pullback.snd (T.map a) (T.map b) ≫ terminal.from (T.obj W) from
          (terminal.hom_ext _ _)]
      infer_instance⟩
  exact ⟨by
    rw [show terminal.from (T.obj (pullback a b)) =
      (toSchemePullbackIso B S hS a b).hom ≫ terminal.from (pullback (T.map a) (T.map b)) from
        (terminal.hom_ext _ _)]
    infer_instance⟩

/-- **Over a separated scheme, the fibre product of two affine schemes is affine**: a morphism
from an affine scheme to a separated scheme is affine, and affineness is stable under base
change. -/
theorem isAffine_toScheme_pullback {U X W : BigFppfOver B S hS} (a : U ⟶ X) (b : W ⟶ X)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    [((BigFppfOver.toScheme B S hS).obj X).IsSeparated] :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (pullback a b)) := by
  let T := BigFppfOver.toScheme B S hS
  have : IsAffineHom (T.map a) :=
    IsAffineHom.of_comp (T.map a) (terminal.from (T.obj X))
  exact IsAffine.of_isIso (toSchemePullbackIso B S hS a b).hom

/-! ### The four levels of the proof of Stacks 076Z -/

/-- **The representability levels of the proof of Stacks 076Z.** An algebraic stack `𝒵` over `S`
is at level

* `0` if it is represented by an affine scheme,
* `1` if it is represented by a separated scheme,
* `2` if it is represented by a scheme,
* `3` if it is represented by an algebraic space, and
* `n + 4` always.

Representability by a scheme `T` of the site is equivalence over the site with the category of
elements of `h_T`, the shape `AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpace` uses for
algebraic spaces. -/
def CechLevel : ℕ → AlgebraicStacks.{u, w} B S hS → Prop
  | 0, 𝒵 => ∃ T : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver 𝒵.val.val.p
        (presheafOfCategories (yoneda.obj T ⋙ typeToCat)).p)
  | 1, 𝒵 => ∃ T : BigFppfOver B S hS, ((BigFppfOver.toScheme B S hS).obj T).IsSeparated ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver 𝒵.val.val.p
        (presheafOfCategories (yoneda.obj T ⋙ typeToCat)).p)
  | 2, 𝒵 => ∃ T : BigFppfOver B S hS,
      Nonempty (StacksRepresentableCFG.EquivalenceOver 𝒵.val.val.p
        (presheafOfCategories (yoneda.obj T ⋙ typeToCat)).p)
  | 3, 𝒵 => IsRepresentableByAlgebraicSpace B S hS 𝒵.val
  | _ + 4, _ => True

/-- The stack of an affine scheme is at level `0`. -/
theorem cechLevel_zero_schemeStack (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)) :
    CechLevel B S hS 0 (schemeStack.{u, w} B S hS U) :=
  ⟨U, hU, ⟨representedChart B S hS U⟩⟩

/-- A stack at level `0` is equivalent over the site to the big fppf site of an affine scheme:
the category of elements of `h_T` is the slice over `T`
(`AlgebraicGeometry.Stack.representedChart`). This is representability by an affine scheme in
the form of **Stacks 0770** clause (4). -/
theorem exists_equivalenceOver_schemeFibredCategory_of_cechLevel_zero
    {𝒵 : AlgebraicStacks.{u, w} B S hS} (h𝒵 : CechLevel B S hS 0 𝒵) :
    ∃ T : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver 𝒵.val.val.p
        (schemeFibredCategory B S hS T).val.p) := by
  obtain ⟨T, hT, ⟨e⟩⟩ := h𝒵
  exact ⟨T, hT, ⟨e.trans (representedChart B S hS T).symm⟩⟩

/-- The pullback hypothesis of `exists_equivalenceOver_cechNerveTerm_of_isPullback` for a
presheaf represented by `X`, given that the class `𝓟` is stable under fibre products in the
site. -/
private theorem exists_isPullback_representingMap_yoneda
    {𝒱 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒱 ⟶ 𝒳) {U X : BigFppfOver B S hS}
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒳.val.val.p
      (presheafOfCategories (yoneda.obj X ⋙ typeToCat)).p)
    (eV : StacksRepresentableCFG.EquivalenceOver 𝒱.val.val.p
      (presheafOfCategories (yoneda.obj U ⋙ typeToCat)).p)
    (𝓟 : BigFppfOver B S hS → Prop)
    (h𝓟 : ∀ {W : BigFppfOver B S hS} (a : U ⟶ X) (b : W ⟶ X), 𝓟 W → 𝓟 (pullback a b))
    (W : BigFppfOver B S hS) (hW : 𝓟 W) (β : yoneda.obj W ⟶ yoneda.obj X) :
    ∃ (W' : BigFppfOver B S hS) (_ : 𝓟 W') (π₁ : yoneda.obj W' ⟶ yoneda.obj U) (π₂ : W' ⟶ W),
      IsPullback π₁ (yoneda.map π₂)
        (representingMap B S hS 𝒱.val 𝒳.val (yoneda.obj U) (yoneda.obj X) eV eF g.hom) β := by
  obtain ⟨a, ha⟩ := yoneda.map_surjective
    (representingMap B S hS 𝒱.val 𝒳.val (yoneda.obj U) (yoneda.obj X) eV eF g.hom)
  obtain ⟨b, rfl⟩ := yoneda.map_surjective β
  rw [← ha]
  exact ⟨pullback a b, h𝓟 a b hW, _, _, exists_isPullback_yoneda B S hS a b⟩

/-- **The terms of the Čech nerve of an affine presentation go down one level.** Let
`g : 𝒱 ⟶ 𝒳` be a 1-morphism of algebraic stacks with `𝒱` represented by an affine scheme. If `𝒳`
is at level `k + 1`, every term of the Čech nerve of `g` is at level `k`:

* over an algebraic stack the terms are algebraic spaces, the diagonal of an algebraic stack
  being representable by algebraic spaces;
* over an algebraic space they are schemes, its diagonal being representable;
* over a scheme they are separated schemes, a morphism out of an affine scheme being separated;
* over a separated scheme they are affine schemes, a morphism from an affine scheme to a
  separated scheme being affine.

These are the four steps of the proof of **Stacks 076Z**. -/
theorem cechLevel_cechNerveTerm (k : ℕ) {𝒱 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒱 ⟶ 𝒳)
    (h𝒱 : CechLevel B S hS 0 𝒱) (h𝒳 : CechLevel B S hS (k + 1) 𝒳) (n : ℕ) :
    CechLevel B S hS k (cechNerveTerm B S hS g n) := by
  obtain ⟨U, hU, ⟨eV⟩⟩ := h𝒱
  match k, h𝒳 with
  | 0, ⟨X, hX, ⟨eF⟩⟩ =>
    exact exists_equivalenceOver_cechNerveTerm_of_isPullback B S hS g (yoneda.obj X) eF U eV
      (fun T => IsAffine ((BigFppfOver.toScheme B S hS).obj T)) hU
      (exists_isPullback_representingMap_yoneda B S hS g eF eV _ fun a b hW =>
        isAffine_toScheme_pullback B S hS a b) n
  | 1, ⟨X, ⟨eF⟩⟩ =>
    exact exists_equivalenceOver_cechNerveTerm_of_isPullback B S hS g (yoneda.obj X) eF U eV
      (fun T => ((BigFppfOver.toScheme B S hS).obj T).IsSeparated) inferInstance
      (exists_isPullback_representingMap_yoneda B S hS g eF eV _ fun a b hW =>
        isSeparated_toScheme_pullback B S hS a b) n
  | 2, ⟨H, hH, ⟨eF⟩⟩ =>
    obtain ⟨W, -, he⟩ := exists_equivalenceOver_cechNerveTerm_of_isPullback B S hS g H eF U eV
      (fun _ => True) trivial (fun W _ β => by
        obtain ⟨W', π₁, π₂, h⟩ := exists_isPullback_of_isAlgebraicSpace B S hS hH
          (representingMap B S hS 𝒱.val 𝒳.val (yoneda.obj U) H eV eF g.hom) W β
        exact ⟨W', trivial, π₁, π₂, h⟩) n
    exact ⟨W, he⟩
  | 3, _ =>
    exact isRepresentableByAlgebraicSpace_cechNerveTerm B S hS g
      (isRepresentableByAlgebraicSpace_of_equivalenceOver_yoneda B S hS eV) n
  | _ + 4, _ => trivial

/-! ### The induction over the four levels -/

/-- **A 1-morphism between the stacks of two affine schemes is quasi-compact and
quasi-separated.** It is 2-isomorphic to the 1-morphism induced by a morphism of affine schemes,
which is quasi-compact; and its source is quasi-separated over `S` while the diagonal of the
target over `S` is quasi-separated (**Stacks 050N** part (8)). -/
theorem isQuasiCompactMorphism_and_isQuasiSeparated_of_isAffine {U Y : BigFppfOver B S hS}
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hY : IsAffine ((BigFppfOver.toScheme B S hS).obj Y))
    (c : schemeStack.{u, w} B S hS U ⟶ schemeStack.{u, w} B S hS Y) :
    IsQuasiCompactMorphism B S hS c ∧ AlgebraicStacks.IsQuasiSeparated B S hS c := by
  refine ⟨isQuasiCompactMorphism_of_comp_of_isSurjective B S hS (𝟙 _)
    (schemeStackMap.{u, w} B S hS (siteMap B S hS c)) c
    (Bicategory.leftUnitor c ≪≫ schemeStackMapIso B S hS c) (isSurjective_id B S hS _)
    (isQuasiCompactMorphism_schemeAlgebraicStackMap B S hS (siteMap B S hS c)
      (Space.isQuasiCompact_yoneda_of_isAffine B S hS _ hU hY)), ?_⟩
  exact isQuasiSeparated_of_isQuasiSeparatedOver B S hS c
    (isQuasiSeparatedOver_schemeStack_of_isAffine.{u, w} B S hS U hU)
    (isQuasiSeparatedOver_schemeStack_of_isAffine.{u, w} B S hS Y hY).2

/-- **The induction of the proof of Stacks 076Z.** Let `𝒯` be the stack of an affine scheme `Y`
and let `P` be a property of 1-morphisms into `𝒯` such that

* `P` holds for every 1-morphism out of an algebraic stack represented by an affine scheme, and
* `P` descends along a smooth surjective presentation: if `g : 𝒱 ⟶ 𝒵` is surjective, smooth and
  representable by algebraic spaces and `P` holds for the composite of `h` with every projection
  of the Čech nerve of `g`, then `P h`.

Then `P` holds for every quasi-compact and quasi-separated `h : 𝒵 ⟶ 𝒯` with `𝒵` at level `k`, by
induction on `k`: an affine presentation of `𝒵` (**Stacks 04YC**) has Čech nerve one level down
(`AlgebraicGeometry.Stack.AlgebraicStacks.cechLevel_cechNerveTerm`), and quasi-compactness and
quasi-separatedness pass to its projections. -/
theorem cechLevel_induction (Y : BigFppfOver B S hS)
    (hY : IsAffine ((BigFppfOver.toScheme B S hS).obj Y))
    (P : ∀ {𝒵 : AlgebraicStacks.{u, w} B S hS}, (𝒵 ⟶ schemeStack.{u, w} B S hS Y) → Prop)
    (hbase : ∀ {𝒵 : AlgebraicStacks.{u, w} B S hS}, CechLevel B S hS 0 𝒵 →
      ∀ h : 𝒵 ⟶ schemeStack.{u, w} B S hS Y, P h)
    (hcech : ∀ {𝒵 𝒱 : AlgebraicStacks.{u, w} B S hS} (g : 𝒱 ⟶ 𝒵),
      IsRepresentableByAlgebraicSpaces B S hS g.hom.hom → IsSurjective B S hS g →
      AlgebraicStacks.IsSmooth B S hS g → ∀ h : 𝒵 ⟶ schemeStack.{u, w} B S hS Y,
      (∀ n, P (cechNerveProjection B S hS g n ≫ h)) → P h)
    (k : ℕ) {𝒵 : AlgebraicStacks.{u, w} B S hS} (h𝒵 : CechLevel B S hS k 𝒵)
    (h : 𝒵 ⟶ schemeStack.{u, w} B S hS Y) (hqc : IsQuasiCompactMorphism B S hS h)
    (hqs : AlgebraicStacks.IsQuasiSeparated B S hS h) : P h := by
  induction k generalizing 𝒵 with
  | zero => exact hbase h𝒵 h
  | succ k ih =>
    have h𝒵qc := isQuasiCompactStack_of_isQuasiCompactMorphism B S hS h hqc
      (isQuasiCompactStack_schemeStack_of_isAffine.{u, w} B S hS Y hY)
    obtain ⟨U, hU, g, hgsurj, hgsm⟩ :=
      (isQuasiCompactStack_iff_hasAffineSmoothPresentation.{u, w} B S hS 𝒵).1 h𝒵qc
    have hrep : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom :=
      isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒵.property
        (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U) g.hom
    obtain ⟨hghqc, hghqs⟩ :=
      isQuasiCompactMorphism_and_isQuasiSeparated_of_isAffine B S hS hU hY (g ≫ h)
    have hgqc : IsQuasiCompactMorphism B S hS g :=
      isQuasiCompactMorphism_of_comp_of_isQuasiSeparated B S hS g h hghqc hqs
    have hgqs : AlgebraicStacks.IsQuasiSeparated B S hS g :=
      isQuasiSeparated_of_isQuasiSeparated_comp B S hS g h hghqs hqs.2
    refine hcech g hrep hgsurj (isSmooth_of_isRelativelySmooth B S hS g hgsm) h fun n => ?_
    exact ih (cechLevel_cechNerveTerm B S hS k g (cechLevel_zero_schemeStack B S hS U hU) h𝒵 n)
      _ (isQuasiCompactMorphism_comp B S hS _ h
        (isQuasiCompactMorphism_cechNerveProjection B S hS g hgqc n) hqc)
      (isQuasiSeparated_comp B S hS _ h (isQuasiSeparated_cechNerveProjection B S hS g hgqs n) hqs)

/-- **The conclusion of the induction for every quasi-compact quasi-separated 1-morphism into
the stack of an affine scheme.** Every algebraic stack is at level `4`. -/
theorem cechLevel_induction_of_isQuasiCompact (Y : BigFppfOver B S hS)
    (hY : IsAffine ((BigFppfOver.toScheme B S hS).obj Y))
    (P : ∀ {𝒵 : AlgebraicStacks.{u, w} B S hS}, (𝒵 ⟶ schemeStack.{u, w} B S hS Y) → Prop)
    (hbase : ∀ {𝒵 : AlgebraicStacks.{u, w} B S hS}, CechLevel B S hS 0 𝒵 →
      ∀ h : 𝒵 ⟶ schemeStack.{u, w} B S hS Y, P h)
    (hcech : ∀ {𝒵 𝒱 : AlgebraicStacks.{u, w} B S hS} (g : 𝒱 ⟶ 𝒵),
      IsRepresentableByAlgebraicSpaces B S hS g.hom.hom → IsSurjective B S hS g →
      AlgebraicStacks.IsSmooth B S hS g → ∀ h : 𝒵 ⟶ schemeStack.{u, w} B S hS Y,
      (∀ n, P (cechNerveProjection B S hS g n ≫ h)) → P h)
    {𝒵 : AlgebraicStacks.{u, w} B S hS} (h : 𝒵 ⟶ schemeStack.{u, w} B S hS Y)
    (hqc : IsQuasiCompactMorphism B S hS h) (hqs : AlgebraicStacks.IsQuasiSeparated B S hS h) :
    P h :=
  cechLevel_induction B S hS Y hY P hbase hcech 4 trivial h hqc hqs

end AlgebraicGeometry.Stack.AlgebraicStacks

end
