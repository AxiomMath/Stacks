module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Transporting a limiting fork: the formal steps of the exactness half of Stacks 03M8

Stacks 03M8 asserts that for a morphism `f : X ⟶ Y` of algebraic spaces, a surjective étale
chart `τ : U ⟶ X` and `R = U ×_X U` with its projections `t, s`, the sequence of `𝒪_Y`-modules

`0 → f_*F → a_*(F|_U) → b_*(F|_R)`

with second arrow `t^* - s^*` is exact.  Exactness of a three-term sequence whose composite
vanishes is the statement that the first arrow is a *kernel* of the second, and a kernel of a
difference is a limiting fork of the two parallel arrows.  This file collects the three formal
steps that turn one limiting fork into another, and which are what the geometric input of that
tag — the fork in `Mod(𝒪_X)` for the chart itself — is transported along.

None of them is specific to algebraic spaces: the first is abelian-category homological algebra,
the second is the sheaf condition read elementwise on a category of sheaves of modules, and the
third is preservation of limits by a functor together with two isomorphisms of the objects the
fork is taken over.

## Main results

* `CategoryTheory.ShortComplex.exact_and_mono_of_isLimit_fork`: **a limiting fork gives exactness
  and monomorphy**.  In an abelian category, if `e ≫ t = e ≫ s` exhibits `e : A ⟶ M` as a
  limiting fork of `t, s : M ⟶ N`, then the short complex `A → M → N` with middle-to-right
  arrow `t - s` is exact and `e` is a monomorphism.  This is the step by which the source's
  assertion of exactness of `0 → f_*F → a_*(F|_U) → b_*(F|_R)` follows from a fork.
* `SheafOfModules.nonempty_isLimit_fork_of_sections`: **the sectionwise criterion**.  A fork of
  sheaves of modules over a Grothendieck topology is a limit as soon as, over every object of
  the site, every section of the middle term equalized by the two parallel arrows is the image
  of a unique section of the left term.  This is what reduces the fork of Stacks 03M8 to the
  descent statement on sections that the source's proof establishes.
* `CategoryTheory.Limits.isLimitForkOfMap`: **transport of a limiting fork along a
  limit-preserving functor and two isomorphisms**.  This is the step by which the sequence of
  Stacks 03M8 for a general `f : X ⟶ Y` follows from the one for the identity of `X`: the
  functor is the direct image `f_*`, which preserves limits by
  `AlgebraicGeometry.Space.isRightAdjoint_modulePushforward`, and the two isomorphisms are the
  composition comparisons `τ_* ∘ f_* ≅ (τ ≫ f)_*` and `ρ_* ∘ f_* ≅ (ρ ≫ f)_*` of Stacks 03LU.

## Implementation notes

`CategoryTheory.ShortComplex.exact_and_mono_of_isLimit_fork` takes the vanishing of the
composite with the *difference* as its hypothesis and the fork as a `Nonempty`, rather than the
other way round, because that is the shape in which a consumer has them: the vanishing is the
"complex" half, proved separately, and the fork is produced by a transport which is
`noncomputable`, so it arrives wrapped.  The commutation the fork is stated at is then forced to
be the one derived from the vanishing, which is why it is written out in the binder rather than
taken as an argument.

`SheafOfModules.nonempty_isLimit_fork_of_sections` detects the limit through the composite
functor "underlying sheaf of abelian groups, then underlying presheaf, then underlying
presheaf of types": that composite reflects isomorphisms, hence reflects the limit of a parallel
pair, and limits in a category of presheaves of types are detected objectwise, where a fork is a
limit exactly when it has the unique-lifting property.  No sheaf condition is used beyond the
one already carried by the objects.

Its two typeclass hypotheses, `CategoryTheory.HasWeakSheafify` and
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective` for abelian groups, are what
Mathlib's `SheafOfModules.toSheaf` needs in order to reflect isomorphisms; they are not
restrictions in the intended application, being available for the small étale site of an
algebraic space by `AlgebraicGeometry.Space.SmallEtale.instHasSheafify` and
`AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective`.  The forgetful functor to
presheaves of modules reflects isomorphisms with no hypothesis, but Mathlib registers no such
instance for the further step to presheaves of abelian groups, so that route is not open.

`CategoryTheory.Limits.isLimitForkOfMap` states the compatibility of the two isomorphisms with
the arrows as `γ.hom ≫ t = P.map t₀ ≫ δ.hom` rather than by transporting `t` along them, so
that a consumer whose `t` is a given composite may discharge it by a calculation in the ambient
category rather than by rewriting inside the fork.  The first arrow, by contrast, is pinned down
by an equation `e = P.map e₀ ≫ γ.hom`, which is substituted away at once.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

/-! ### A limiting fork gives exactness and monomorphy -/

namespace CategoryTheory.ShortComplex

universe v u

/-- **A limiting fork gives exactness and monomorphy.**  Let `e : A ⟶ M` and `t, s : M ⟶ N` be
morphisms of an abelian category with `e ≫ (t - s) = 0`.  If `e` is a limiting fork of `t` and
`s`, then the short complex `A → M → N` whose second arrow is `t - s` is exact and `e` is a
monomorphism.

In Stacks 03M8 this is the step from the fork `f_*F → a_*(F|_U) ⇉ b_*(F|_R)` to the asserted
exactness of `0 → f_*F → a_*(F|_U) → b_*(F|_R)`: a fork of two parallel arrows is a kernel of
their difference, and a kernel is exactly what exactness at the first two terms together with
injectivity of the first arrow says. -/
theorem exact_and_mono_of_isLimit_fork {C : Type u} [Category.{v} C] [Abelian C] {A M N : C}
    (e : A ⟶ M) (t s : M ⟶ N) (hzero : e ≫ (t - s) = 0)
    (h : Nonempty (IsLimit (Fork.ofι e
      (show e ≫ t = e ≫ s by
        simpa only [Preadditive.comp_sub, sub_eq_zero] using hzero)))) :
    (ShortComplex.mk e (t - s) hzero).Exact ∧ Mono e :=
  (ShortComplex.exact_and_mono_f_iff_f_is_kernel _).2
    ⟨Preadditive.isLimitKernelForkOfFork h.some⟩

end CategoryTheory.ShortComplex

/-! ### The sectionwise criterion for a fork of sheaves of modules -/

namespace SheafOfModules

universe u v' u'

/-- **A fork of sheaves of modules is a limit as soon as it is one on sections.**  Let
`e : A ⟶ M` and `t, s : M ⟶ N` be morphisms of sheaves of modules over a sheaf of rings `R` on a
site, with `e ≫ t = e ≫ s`.  If over every object `V` of the site every section `x` of `M` with
`t(x) = s(x)` is `e(y)` for a unique section `y` of `A`, then `e` is a limiting fork of `t` and
`s`.

This is the criterion by which the fork of Stacks 03M8 is reduced to the descent statement on
sections which the source's proof establishes from the sheaf condition for the one-element
covering given by the chart. -/
theorem nonempty_isLimit_fork_of_sections {C : Type u'} [Category.{v'} C]
    {J : GrothendieckTopology C} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {R : Sheaf J RingCat.{u}} {A M N : SheafOfModules.{u} R}
    (e : A ⟶ M) (t s : M ⟶ N) (h : e ≫ t = e ≫ s)
    (hsections : ∀ (V : Cᵒᵖ) (x : M.val.obj V),
      t.val.app V x = s.val.app V x → ∃! y, e.val.app V y = x) :
    Nonempty (IsLimit (Fork.ofι e h)) := by
  let G := SheafOfModules.toSheaf R ⋙ sheafToPresheaf J AddCommGrpCat.{u} ⋙
    (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{u} (Type u)).obj
      (CategoryTheory.forget AddCommGrpCat.{u})
  have : ReflectsLimit (parallelPair t s) G :=
    reflectsLimit_of_reflectsIsomorphisms _ _
  refine ⟨isLimitOfReflects G (evaluationJointlyReflectsLimits _ fun V => ?_)⟩
  let E := G ⋙ (CategoryTheory.evaluation Cᵒᵖ (Type u)).obj V
  show IsLimit (E.mapCone (Fork.ofι e h))
  exact (isLimitMapConeForkEquiv E h).symm <|
    Classical.choice ((Types.type_equalizer_iff_unique _ _).2 (hsections V))

end SheafOfModules

/-! ### Transport of a limiting fork along a functor and two isomorphisms -/

namespace CategoryTheory.Limits

universe v v₂ u u₂

/-- **Transport of a limiting fork along a limit-preserving functor and two isomorphisms.**  Let
`P : C ⥤ D` preserve the limit of the parallel pair `t₀, s₀ : M ⟶ N`, let `e₀` be a limiting
fork of that pair, and let `γ : P.obj M ≅ M'`, `δ : P.obj N ≅ N'` be isomorphisms.  Then a fork
`e : P.obj A ⟶ M'` of `t, s : M' ⟶ N'` which is `P.map e₀` followed by `γ`, and whose two
parallel arrows correspond to `P.map t₀` and `P.map s₀` under `γ` and `δ`, is again a limit.

In Stacks 03M8 this is the reduction of the asserted sequence for a general `f : X ⟶ Y` to the
case of the identity of `X`: the functor is the direct image `f_*` of `𝒪`-modules, which
preserves limits because it is a right adjoint, and the two isomorphisms are the composition
comparisons of Stacks 03LU that read `τ_* ⋙ f_*` as `(τ ≫ f)_*` and `ρ_* ⋙ f_*` as
`(ρ ≫ f)_*`. -/
noncomputable def isLimitForkOfMap {C : Type u} {D : Type u₂} [Category.{v} C]
    [Category.{v₂} D] (P : C ⥤ D) {A M N : C} {e₀ : A ⟶ M} {t₀ s₀ : M ⟶ N}
    (h₀ : e₀ ≫ t₀ = e₀ ≫ s₀) [PreservesLimit (parallelPair t₀ s₀) P]
    (hl : IsLimit (Fork.ofι e₀ h₀)) {M' N' : D} (γ : P.obj M ≅ M') (δ : P.obj N ≅ N')
    {e : P.obj A ⟶ M'} {t s : M' ⟶ N'} (he : e = P.map e₀ ≫ γ.hom)
    (ht : γ.hom ≫ t = P.map t₀ ≫ δ.hom) (hs : γ.hom ≫ s = P.map s₀ ≫ δ.hom)
    (h : e ≫ t = e ≫ s) :
    IsLimit (Fork.ofι e h) := by
  subst he
  have hmap := (isLimitMapConeForkEquiv P h₀) (isLimitOfPreserves P hl)
  have ht' : γ.inv ≫ P.map t₀ ≫ δ.hom = t := by rw [← ht, Iso.inv_hom_id_assoc]
  have hs' : γ.inv ≫ P.map s₀ ≫ δ.hom = s := by rw [← hs, Iso.inv_hom_id_assoc]
  have key : ∀ c : Fork t s, (c.ι ≫ γ.inv) ≫ P.map t₀ = (c.ι ≫ γ.inv) ≫ P.map s₀ := fun c =>
    (cancel_mono δ.hom).mp (by simpa only [Category.assoc, ht', hs'] using c.condition)
  refine Fork.IsLimit.mk _ (fun c => (Fork.IsLimit.lift' hmap (c.ι ≫ γ.inv) (key c)).1) ?_ ?_
  · intro c
    have h1 := (Fork.IsLimit.lift' hmap (c.ι ≫ γ.inv) (key c)).2
    simp only [Fork.ι_ofι] at h1 ⊢
    rw [← Category.assoc, h1]
    simp
  · intro c m hm
    refine Fork.IsLimit.hom_ext hmap ?_
    rw [(Fork.IsLimit.lift' hmap (c.ι ≫ γ.inv) (key c)).2]
    simp only [Fork.ι_ofι] at hm ⊢
    rw [← hm]
    simp

end CategoryTheory.Limits

end
