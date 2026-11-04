module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LqcohSheafFbcFppfHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticHigherDirectImage

/-!
# The quasi-coherent direct image and its higher direct images (Stacks 077A, 0GQQ)

Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated 1-morphism of algebraic stacks.
**Stacks 077A** says:

1. `f^* : QCoh(𝒪_𝒴) ⥤ QCoh(𝒪_𝒳)` has a right adjoint `f_{QCoh,*}`, which can be defined as the
   composite `QCoh(𝒪_𝒳) → LQCoh^fbc(𝒪_𝒳) → LQCoh^fbc(𝒪_𝒴) → QCoh(𝒪_𝒴)` of the inclusion, the
   direct image of **Stacks 0771** and the coherator `Q` of **Stacks 0778**;
2. defining `Rⁱf_{QCoh,*}` as the same composite with `Rⁱf_*` in the middle, the family
   `{Rⁱf_{QCoh,*}}_{i ≥ 0}` is a cohomological δ-functor (**Stacks 010Q**).

The functors are `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentDirectImage` and
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHigherDirectImage`, the composites
`Q ∘ f_* ∘ i` and `Q ∘ Rⁱf_* ∘ i` through `Mod(𝒪_𝒳)` and `Mod(𝒪_𝒴)`, and the adjunction is
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentPullbackDirectImageAdjunction`.  This file
proves that these composites factor through `LQCoh^fbc` as the source writes them, and that
`{Rⁱf_{QCoh,*}}` is a cohomological δ-functor.  It also proves **Stacks 0GQQ**: at a flat object
`y` of `𝒴`, the sections of `f_*𝓕` and `f_{QCoh,*}𝓕`, and those of `Rⁱf_*𝓕` and
`Rⁱf_{QCoh,*}𝓕`, agree.

## The δ-functor

The δ-functor is `CategoryTheory.DeltaFunctor.ofCoreflections` applied to the δ-functor of the
higher direct images of modules, with inputs:

* `LQCoh^fbc` is a weak Serre subcategory of `Mod` containing `QCoh` (**Stacks 0771** part (2));
* the coherator is right exact on it (**Stacks 0779** part (3));
* the higher direct images preserve it (**Stacks 0771** part (4)(b));
* and they carry an object of `LQCoh^fbc(𝒪_𝒳)` killed by the coherator, that is a parasitic one
  (**Stacks 0779** part (1)), to a parasitic one (**Stacks 0775** part (2)), which the coherator
  kills.

The connecting morphism is the source's: for `0 → 𝓕₁ → 𝓕₂ → 𝓕₃ → 0` short exact in
`QCoh(𝒪_𝒳)`, it is `Q` of the connecting morphism of `Rf_*` at
`0 → Ker(𝓕₂ → 𝓕₃) → 𝓕₂ → 𝓕₃ → 0` (exact in `Mod(𝒪_𝒳)`), followed by the inverse of
`Q Rⁱ⁺¹f_*(𝓕₁ → Ker(𝓕₂ → 𝓕₃))`, a map whose kernel and cokernel are parasitic.

## Indexing

The source indexes the higher direct images of 0GQQ by `i ∈ ℤ`; for `i < 0` both sides vanish
by convention, and the statement here is for `i ∈ ℕ`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.lqcohSheafFbcDirectImage` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.lqcohSheafFbcHigherDirectImage`: `f_*` and `Rⁱf_*` on
  `LQCoh^fbc`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentDirectImageIsoComposite` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHigherDirectImageIsoComposite`:
  **Stacks 077A**, `f_{QCoh,*}` and `Rⁱf_{QCoh,*}` are the composites through `LQCoh^fbc`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHigherDirectImageDeltaFunctor`:
  **Stacks 077A**, the cohomological δ-functor `{Rⁱf_{QCoh,*}}`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.bijective_coheratorAdjunction_counit_directImage`:
  **Stacks 0GQQ**.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0775](https://stacks.math.columbia.edu/tag/0775)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 077A](https://stacks.math.columbia.edu/tag/077A)
* [Stacks Project, Tag 0GQQ](https://stacks.math.columbia.edu/tag/0GQQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff) (S : Scheme.{u})
  (hS : B.Contains S) {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (hqc : IsQuasiCompactMorphism B S hS f) (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)

include hqc hqs in
/-- **Stacks 0771, part (4)(b), in degree `0`**: for a quasi-compact and quasi-separated `f`, the
direct image of modules carries `LQCoh^fbc(𝒪_𝒳)` into `LQCoh^fbc(𝒪_𝒴)`, since it is its own
zeroth right derived functor. -/
theorem lqcohSheafFbcFppfModules_fppfModulesPushforward (F : Stack.fppfModules B S hS 𝒳)
    (hF : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F) :
    lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴 ((fppfModulesPushforward B S hS f).obj F) := by
  let := enoughInjectives_fppfModules B S hS 𝒳
  have := (fppfModulesPullbackPushforwardAdjunction B S hS f).rightAdjoint_preservesLimits
  exact (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).prop_of_iso
    (((fppfModulesPushforward B S hS f).rightDerivedZeroIsoSelf).app F)
    (lqcohSheafFbcFppfModules_fppfModulesHigherDirectImage B E h S hS f hqc hqs F hF 0)

/-- The direct image `f_* : LQCoh^fbc(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒴)` of **Stacks 0771** for a
quasi-compact and quasi-separated `f`. -/
abbrev lqcohSheafFbcDirectImage :
    (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).FullSubcategory ⥤
      (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).FullSubcategory :=
  ObjectProperty.lift _ ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙
    fppfModulesPushforward B S hS f)
    fun F => lqcohSheafFbcFppfModules_fppfModulesPushforward B E h S hS f hqc hqs F.obj F.property

/-- The higher direct images `Rⁱf_* : LQCoh^fbc(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒴)` of **Stacks 0771**
part (4)(b) for a quasi-compact and quasi-separated `f`. -/
abbrev lqcohSheafFbcHigherDirectImage (i : ℕ) :
    (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).FullSubcategory ⥤
      (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).FullSubcategory :=
  ObjectProperty.lift _ ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙
    fppfModulesHigherDirectImage B S hS f i)
    fun F => lqcohSheafFbcFppfModules_fppfModulesHigherDirectImage B E h S hS f hqc hqs F.obj
      F.property i

/-- A functor `R : Mod(𝒪_𝒳) ⥤ Mod(𝒪_𝒴)` carrying `LQCoh^fbc(𝒪_𝒳)` into `LQCoh^fbc(𝒪_𝒴)`: the
composite `Q ∘ R ∘ i` is the composite through `LQCoh^fbc`, on the nose. -/
def compositeIsoOfFactorization (R : Stack.fppfModules B S hS 𝒳 ⥤ Stack.fppfModules B S hS 𝒴)
    (hR : ∀ F : (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).FullSubcategory,
      lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴 (R.obj F.obj)) :
    quasicoherentInclusion B S hS 𝒳 ⋙ R ⋙ coherator B S hS 𝒴 ≅
      (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).lift (quasicoherentInclusion B S hS 𝒳)
          (lqcohSheafFbcFppfModules_quasicoherentInclusion B E h S hS 𝒳) ⋙
        (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).lift
          ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙ R) hR ⋙
          ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).ι ⋙ coherator B S hS 𝒴) :=
  Iso.refl _

/-- **Stacks 077A**: `f_{QCoh,*}` is the composite
`QCoh(𝒪_𝒳) → LQCoh^fbc(𝒪_𝒳) → LQCoh^fbc(𝒪_𝒴) → QCoh(𝒪_𝒴)` of the inclusion, the direct image
of **Stacks 0771** and the coherator `Q` of **Stacks 0778**, the restriction of the coherator to
`LQCoh^fbc(𝒪_𝒴)`. -/
@[stacks 077A "f_{QCoh,*} is the composite QCoh(O_X) → LQCoh^fbc(O_X) → LQCoh^fbc(O_Y) → \
  QCoh(O_Y) of the inclusion, f_* of Stacks 0771 and Q of Stacks 0778"]
def quasicoherentDirectImageIsoComposite :
    quasicoherentDirectImage B S hS f ≅
      (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).lift (quasicoherentInclusion B S hS 𝒳)
          (lqcohSheafFbcFppfModules_quasicoherentInclusion B E h S hS 𝒳) ⋙
        lqcohSheafFbcDirectImage B E h S hS f hqc hqs ⋙
          ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).ι ⋙ coherator B S hS 𝒴) :=
  Iso.refl _

/-- **Stacks 077A**: `Rⁱf_{QCoh,*}` is the composite
`QCoh(𝒪_𝒳) → LQCoh^fbc(𝒪_𝒳) → LQCoh^fbc(𝒪_𝒴) → QCoh(𝒪_𝒴)` of the inclusion, the higher direct
image `Rⁱf_*` of **Stacks 0771** and the coherator `Q` of **Stacks 0778**. -/
@[stacks 077A "R^i f_{QCoh,*} is the composite QCoh(O_X) → LQCoh^fbc(O_X) → LQCoh^fbc(O_Y) → \
  QCoh(O_Y) of the inclusion, R^i f_* of Stacks 0771 and Q of Stacks 0778"]
def quasicoherentHigherDirectImageIsoComposite (i : ℕ) :
    quasicoherentHigherDirectImage B S hS f i ≅
      (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).lift (quasicoherentInclusion B S hS 𝒳)
          (lqcohSheafFbcFppfModules_quasicoherentInclusion B E h S hS 𝒳) ⋙
        lqcohSheafFbcHigherDirectImage B E h S hS f hqc hqs i ⋙
          ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).ι ⋙ coherator B S hS 𝒴) :=
  compositeIsoOfFactorization B E h S hS (fppfModulesHigherDirectImage B S hS f i) _

include hqc hqs in
/-- **Stacks 077A, the second assertion: `{Rⁱf_{QCoh,*}}_{i ≥ 0}` is a cohomological δ-functor**
(**Stacks 010Q**) `QCoh(𝒪_𝒳) ⥤ QCoh(𝒪_𝒴)`, for a quasi-compact and quasi-separated 1-morphism
`f` of algebraic stacks.  Its degree-`i` functor is
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentHigherDirectImage` (by `rfl`), the
composite `Q ∘ Rⁱf_* ∘ i`. -/
@[stacks 077A "second assertion: {R^i f_{QCoh,*}}_{i ≥ 0} forms a cohomological δ-functor \
  QCoh(O_X) ⥤ QCoh(O_Y), for f quasi-compact and quasi-separated"]
def quasicoherentHigherDirectImageDeltaFunctor :
    DeltaFunctor (quasicoherentModules B S hS 𝒳) (quasicoherentModules B S hS 𝒴) :=
  let E := associatedBigEtaleSite B
  have h : E.cutoff = B.cutoff := rfl
  haveI := preservesFiniteColimits_lqcohSheafFbc_ι_comp B E h S hS 𝒳 (coheratorAdjunction B S hS 𝒳)
  haveI := preservesFiniteColimits_lqcohSheafFbc_ι_comp B E h S hS 𝒴 (coheratorAdjunction B S hS 𝒴)
  quasicoherentHigherDirectImageDeltaFunctorOfInputs B S hS f E h _ _
    (lqcohSheafFbcFppfModules_quasicoherentInclusion B E h S hS 𝒳)
    (lqcohSheafFbcFppfModules_quasicoherentInclusion B E h S hS 𝒴)
    (lqcohSheafFbcFppfModules_fppfModulesHigherDirectImage B E h S hS f hqc hqs)
    (fun F hF hz n => (isZero_coherator_obj_iff_isParasitic B S hS 𝒴 E h _
      (lqcohSheafFbcFppfModules_fppfModulesHigherDirectImage B E h S hS f hqc hqs F hF n)).2
      (isParasitic_fppfModulesHigherDirectImage f F
        ((isZero_coherator_obj_iff_isParasitic B S hS 𝒳 E h F hF).1 hz) n))

/-- The degree-`i` functor of the δ-functor of **Stacks 077A** is `Rⁱf_{QCoh,*}`. -/
@[simp]
theorem quasicoherentHigherDirectImageDeltaFunctor_functor (i : ℕ) :
    (quasicoherentHigherDirectImageDeltaFunctor B S hS f hqc hqs).functor i =
      quasicoherentHigherDirectImage B S hS f i :=
  rfl

include hqc hqs in
/-- **Stacks 0GQQ.** Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated 1-morphism of
algebraic stacks, `y` an object of `𝒴` such that `y : V → 𝒴` is flat, and `𝓕` a quasi-coherent
`𝒪_𝒳`-module.  Then `(f_*𝓕)(y) = (f_{QCoh,*}𝓕)(y)` and `(Rⁱf_*𝓕)(y) = (Rⁱf_{QCoh,*}𝓕)(y)` for
all `i`: the adjunction maps `f_{QCoh,*}𝓕 = Q(f_*𝓕) ⟶ f_*𝓕` and
`Rⁱf_{QCoh,*}𝓕 = Q(Rⁱf_*𝓕) ⟶ Rⁱf_*𝓕` of the coherator are bijective on sections at `y`.  Both
`f_*𝓕` and `Rⁱf_*𝓕` lie in `LQCoh^fbc(𝒪_𝒴)`, so the kernels and cokernels of those maps are
parasitic by **Stacks 0779** part (2), and vanish at `y`.  For `i < 0` both sides are zero. -/
@[stacks 0GQQ "(f_*F)(y) = (f_{QCoh,*}F)(y) and (R^i f_*F)(y) = (R^i f_{QCoh,*}F)(y) for f qcqs, \
  y flat and F quasi-coherent: the adjunction maps of the coherator are bijective at y; i ≥ 0, \
  both sides vanishing for i < 0"]
theorem bijective_coheratorAdjunction_counit_directImage (F : quasicoherentModules B S hS 𝒳)
    (y : 𝒴.val.val.obj) (hy : flatObject B S hS 𝒴.val y) :
    Function.Bijective (((coheratorAdjunction B S hS 𝒴).counit.app
        ((fppfModulesPushforward B S hS f).obj ((quasicoherentInclusion B S hS 𝒳).obj F))).val.app
          (op y)) ∧
      ∀ i, Function.Bijective (((coheratorAdjunction B S hS 𝒴).counit.app
        ((fppfModulesHigherDirectImage B S hS f i).obj
          ((quasicoherentInclusion B S hS 𝒳).obj F))).val.app (op y)) := by
  let E := associatedBigEtaleSite B
  have h : E.cutoff = B.cutoff := rfl
  have hi := lqcohSheafFbcFppfModules_quasicoherentInclusion B E h S hS 𝒳 F
  refine ⟨?_, fun i => ?_⟩ <;>
    refine (isParasitic_kernel_and_cokernel_coheratorAdjunction_counit B S hS 𝒴 E h _ ?_).elim
      fun h₁ h₂ => isIso_app_of_isParasitic_kernel_cokernel B S hS _ h₁ h₂ y hy
  · exact lqcohSheafFbcFppfModules_fppfModulesPushforward B E h S hS f hqc hqs _ hi
  · exact lqcohSheafFbcFppfModules_fppfModulesHigherDirectImage B E h S hS f hqc hqs _ hi i

end AlgebraicGeometry.Stack.AlgebraicStacks
