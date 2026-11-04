module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualRingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# `F ⊗ SheafHom(E, 𝒪) ≅ SheafHom(E, F)` for `E` locally a finite free summand

Let `𝒪` be a presheaf of commutative rings on a site `(C, J)` whose underlying presheaf of rings
is a sheaf, and let `E` and `F` be sheaves of `𝒪`-modules. The *rank-one operator* attached to a
section `f` of `F` over `U` and a section `lam` of the dual `E^∨ = SheafHom(E, 𝒪)` over `U` is the
morphism `g ↦ lam(g) • f` from `E|_U` to `F|_U`. Assembling these over all objects gives a
canonical morphism of sheaves of `𝒪`-modules

  `F ⊗_𝒪 SheafHom(E, 𝒪) ⟶ SheafHom(E, F)`,

and this file proves that it is an **isomorphism** as soon as `E` is locally a direct summand of a
finite free sheaf of modules, `F` being arbitrary.

That statement is **step (5) of the proof of
[Stacks, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)**: having reduced the third and
fourth assertions of that tag to a degreewise claim about a strictly perfect complex `E` and a
K-flat complex `F`, the source finishes with "everything reduces to the claim that
`F ⊗_𝒪 Hom_𝒪(E, 𝒪) ⟶ Hom_𝒪(E, F)` is an isomorphism for `E` a direct summand of a finite free
module and arbitrary `F`". The two files
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.Duals` and
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualityPairing` each name exactly this as
the input they lack.

It is a proof step and not an assertion of Tag 08JJ, so the attribute it carries is the
**suffixed** `@[stacks 08JJ "step (5) of the proof only: …"]`, whose text records that none of the
tag's four assertions is proved here; see the implementation notes.

## Main definitions

* `Stacks.SheafOfModules.rankOneHomSection` is the rank-one operator `g ↦ lam(g) • f`, as a
  section of `SheafHom(E, F)` over `U`.
* `Stacks.SheafOfModules.sheafHomEval` is the value of a section of `SheafHom(E, F)` over `U` on a
  section of `E` over `U`.
* `Stacks.SheafOfModules.tensorDualHomPresheaf` assembles the rank-one operators into a morphism
  `F ⊗ E^∨ ⟶ SheafHom(E, F)` out of the *pointwise* tensor product of presheaves of modules.
* `Stacks.SheafOfModules.tensorDualToSheafHom` is the induced morphism of *sheaves* of modules
  `F ⊗_𝒪 E^∨ ⟶ SheafHom(E, F)`, the tensor product of sheaves of modules being the sheafification
  of the pointwise one (Tag 05NA).

## Main results

* `Stacks.SheafOfModules.tensorDualToSheafHom_toTensorSheafSection`: **the canonical morphism
  sends the local pure tensor `f ⊗ lam` to the rank-one operator `g ↦ lam(g) • f`.** This pins the
  morphism down, which is what makes the isomorphism below a statement about a *named* map rather
  than an existence claim.
* `Stacks.SheafOfModules.bijective_tensorDualHomPresheaf_app_of_finiteDualBasis`: a finite dual
  basis **for `E`** over `U` makes the rank-one map bijective on sections over `U`, for every `F`.
* `Stacks.SheafOfModules.isLocallyInjective_tensorDualHomPresheaf` and
  `isLocallySurjective_tensorDualHomPresheaf`: finite dual bases for `E` on a family covering the
  final object make the rank-one map locally bijective, hence inverted by sheafification
  (`isIso_sheafify_map_tensorDualHomPresheaf`).
* `Stacks.SheafOfModules.isIso_tensorDualToSheafHom`: **`F ⊗ E^∨ ⟶ SheafHom(E, F)` is an
  isomorphism** when `E` has finite dual bases on a covering family.
* `Stacks.SheafOfModules.isIso_tensorDualToSheafHom_of_localSummand`: **the step (5) statement**,
  with the local hypothesis in the per-object form of Tag 0FNY, which is the form
  `Stacks.SheafOfModules.IsLocallyDirectSummandOfFiniteFree` records.

## Implementation notes

**This is the generalisation of the endomorphism case, and the statements of that case are its
`E = F` specialisations.** `Stacks.SheafOfModules.tensorDualToEndomorphism` of
`...Sheaf.TensorDualEndomorphism` is the case `E = F`, and
`Stacks.SheafOfModules.isIso_tensorDualToEndomorphism` is the corresponding case of
`isIso_tensorDualToSheafHom`; `rankOneHomSection_self`, `sheafHomEval_self`,
`tensorDualHomPresheaf_self` and `tensorDualToSheafHom_self` record those identifications, all of
them by `rfl`. Nothing in the imported files is restated or changed: the construction there is
written with one module playing both roles, so the general construction cannot be obtained by
instantiating it, but every *lemma* of that file which mentions only one of the two roles —
`Stacks.SheafOfModules.mulRestrSection`, `internalHom_ext`, `internalHom_sum_app_apply`,
`dualApp_add`, `dualApp_smul_left`, `resSection_add`, `resSection_smul`, `fRestr_eq_resRing`,
`smul_comm_section`, and the whole of `Stacks.SheafOfModules.FiniteDualBasis` — is reused here
verbatim at the appropriate one of `E`, `F`. In particular the dual-basis data is unchanged:
`Stacks.SheafOfModules.FiniteDualBasis` is a condition on a single module, and it is imposed on
`E` alone.

**A suffixed `@[stacks 08JJ]` attribute, and why it is the suffixed form.** The statement proved
here is a step of the proof of Tag 08JJ, not one of that tag's four assertions, and a covering set
is a set of declarations whose union *states* a tag — so a bare attribute would be false. Three
of the four assertions are in the library: the first is
`AlgebraicGeometry.RingedSite.isPerfect_derivedDual`, carrying
`@[stacks 08JJ "the dual of a perfect object is perfect"]`, and the third and fourth are
`AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomIso` and
`AlgebraicGeometry.RingedSite.derivedDualTensorGlobalSectionsEquiv` in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualTensorSheafHom`. Those two are proved
by a route that does not pass through this step at all, the diagonal of Stacks 0BYS at target
object the structure sheaf; what this step feeds is the source's own route, through the
*canonical* map `AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom` of Stacks 08JD, and
that still needs the comparison of that map with the morphism below on the terms of a strictly
perfect and a K-flat representative, which the library does not have. The suffix text says so
explicitly, so the attribute claims the step and nothing more.

The precedent is `@[stacks 063H "the Nakayama and shrinking step of the proof only: … The
characterization of quasi-regular ideal sheaves itself is not proved here."]` at
`StacksFrontier/AlgebraicGeometry/QuasiRegular/StalkGenerators.lean:312`. That is 063H's *only*
attribute in the library and it likewise sits on a step of a tag whose own content is unproved, so
the situation here is the same one. Tagging also makes the step findable by tag search, which is
how a consumer of Tag 08JJ's clause 3 will reach it.

The companion isomorphism `F ⊗ F^∨ ≅ SheafHom(F, F)` is an assertion of Tags 0FNV and 0FNY and is
tagged in the imported files; the present statement is not an assertion of either, since both are
about the endomorphism sheaf of a single module.

**The local hypothesis is weaker than the source's.** Tag 08JJ's step (5) asks that `E` be a
direct summand of a finite free module outright. What is assumed here is that it is one *locally*,
which is the hypothesis of Tag 0FNY and is implied by the global one; so the statement below is
stronger than the step, and the global case is the special case in which the covering sieve of
every object is the maximal one. Instantiating it at a global retract is a restriction-of-a-retract
step which needs `Stacks.SheafOfModules.freeOverIso` and so the slice-site `HasSheafify` instances
that `...Sheaf.SliceRestrictionFinite` assumes; none of those are hypotheses of anything below.

**Universes.** The site is `C : Type u` with `Category.{v} C` and the module universe is
`max u v`, as in the imported files, and for the reason recorded there: a section of
`SheafHom(E, F)` over `U` is a morphism of presheaves of modules on the slice site `C/U`, whose
objects live in `Type (max u v)`, so Tag 03EM's internal hom lands in
`PresheafOfModules.{max u v t}` for arguments in `PresheafOfModules.{t}` and is an object of the
same category as its arguments only when `max u v ≤ t`. Nothing is narrowed here relative to
`...Sheaf.TensorDualEndomorphism`, whose `endPresheaf` the construction below runs alongside.

**Hypotheses.** The rank-one operator and `tensorDualHomPresheaf` need no sheafification
hypothesis. The sheaf-level half assumes `J.WEqualsLocallyBijective AddCommGrpCat` and
`HasWeakSheafify J AddCommGrpCat`, which Tag 05NA's sheafification functor and the
locally-bijective criterion need, and `isIso_tensorDualToSheafHom_of_localSummand` additionally
assumes the slice-site instances without which its hypothesis
`Stacks.SheafOfModules.IsLocallyDirectSummandOfFiniteFree` cannot be used, exactly as
`Stacks.SheafOfModules.isIso_tensorDualToEndomorphism_of_localSummand` does.

## References

* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ) — the duality statement
  whose proof calls for this step.
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV) and
  [Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY) — the endomorphism case `E = F`.
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM) — the internal hom.
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA) — the tensor product
  sheaf as a sheafification.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite SheafOfModules

universe v u

namespace Stacks.SheafOfModules

attribute [local implicit_reducible] TensorSheafification.structureSheaf

section RankOne

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
  (h𝒪 : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf 𝒪))
  {E F : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)}

attribute [local instance] commRingStructureSheafObj

/-- **The rank-one morphism `g ↦ lam(g) • f`** from `E|_U` to `F|_U`, as a section of
`SheafHom(E, F)` over `U`.

A section of `SheafHom(E, F)` over `U` *is* a morphism `E|_U ⟶ F|_U` of presheaves of modules on
the slice site `C/U`, and a section of the dual `E^∨` over `U` *is* a morphism `E|_U ⟶ 𝒪|_U`; so
the rank-one operator is literally the composite of `lam` with multiplication by `f`. -/
noncomputable def rankOneHomSection {U : C} (f : F.val.obj (op U))
    (lam : (dualSheaf 𝒪 h𝒪 E).val.obj (op U)) :
    (sheafHom 𝒪 h𝒪 E F).val.obj (op U) :=
  lam ≫ mulRestrSection 𝒪 h𝒪 f

/-- At `E = F` the rank-one morphism is the rank-one endomorphism of
`Stacks.SheafOfModules.rankOneSection`. -/
lemma rankOneHomSection_self {U : C} (f : F.val.obj (op U))
    (lam : (dualSheaf 𝒪 h𝒪 F).val.obj (op U)) :
    rankOneHomSection 𝒪 h𝒪 f lam = rankOneSection 𝒪 h𝒪 f lam := rfl

/-- **The defining formula for the rank-one morphism**, read off at an object `V` of the slice
site `C/U`: it sends a section `g` of `E` over `V.left` to `lam(g) • f|_V`. -/
lemma rankOneHomSection_app {U : C} (f : F.val.obj (op U))
    (lam : (dualSheaf 𝒪 h𝒪 E).val.obj (op U)) (V : (Over U)ᵒᵖ)
    (g : E.val.obj (op V.unop.left)) :
    ((rankOneHomSection 𝒪 h𝒪 f lam).app V).hom g = dualApp lam V g • resSection V f := rfl

/-- A rank-one morphism is a sum of two others once this holds pointwise on the slice site. -/
private theorem rankOneHomSection_eq_add {U : C} {f f₁ f₂ : F.val.obj (op U)}
    {lam lam₁ lam₂ : (dualSheaf 𝒪 h𝒪 E).val.obj (op U)}
    (h : ∀ (V : (Over U)ᵒᵖ) (g : E.val.obj (op V.unop.left)),
      dualApp lam V g • resSection V f =
        dualApp lam₁ V g • resSection V f₁ + dualApp lam₂ V g • resSection V f₂) :
    rankOneHomSection 𝒪 h𝒪 f lam =
      rankOneHomSection 𝒪 h𝒪 f₁ lam₁ + rankOneHomSection 𝒪 h𝒪 f₂ lam₂ :=
  internalHom_ext 𝒪 h𝒪 _ _ fun V g =>
    (h V g).trans (internalHom_add_app_apply 𝒪 h𝒪 (rankOneHomSection 𝒪 h𝒪 f₁ lam₁)
      (rankOneHomSection 𝒪 h𝒪 f₂ lam₂) V g).symm

/-- A rank-one morphism is a multiple of another once this holds pointwise on the slice site. -/
private theorem rankOneHomSection_eq_smul {U : C} {f₁ f : F.val.obj (op U)}
    {lam₁ lam : (dualSheaf 𝒪 h𝒪 E).val.obj (op U)}
    (a : (TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U))
    (h : ∀ (V : (Over U)ᵒᵖ) (g : E.val.obj (op V.unop.left)),
      dualApp lam₁ V g • resSection V f₁ = resRing V a • (dualApp lam V g • resSection V f)) :
    rankOneHomSection 𝒪 h𝒪 f₁ lam₁ = a • rankOneHomSection 𝒪 h𝒪 f lam := by
  refine internalHom_ext 𝒪 h𝒪 _ _ fun V g => ?_
  refine (h V g).trans (Eq.trans ?_ (internalHom_smul_app_apply 𝒪 E.val F.val U a
    (rankOneHomSection 𝒪 h𝒪 f lam) V g).symm)
  rw [fRestr_eq_resRing]
  rfl

/-- The rank-one morphism is additive in the section of the target. -/
lemma rankOneHomSection_add_left {U : C} (f f' : F.val.obj (op U))
    (lam : (dualSheaf 𝒪 h𝒪 E).val.obj (op U)) :
    rankOneHomSection 𝒪 h𝒪 (f + f') lam =
      rankOneHomSection 𝒪 h𝒪 f lam + rankOneHomSection 𝒪 h𝒪 f' lam :=
  rankOneHomSection_eq_add 𝒪 h𝒪 fun V g => by
    rw [resSection_add, smul_add]

/-- The rank-one morphism is homogeneous in the section of the target. -/
lemma rankOneHomSection_smul_left {U : C}
    (a : (TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)) (f : F.val.obj (op U))
    (lam : (dualSheaf 𝒪 h𝒪 E).val.obj (op U)) :
    rankOneHomSection 𝒪 h𝒪 (a • f) lam = a • rankOneHomSection 𝒪 h𝒪 f lam :=
  rankOneHomSection_eq_smul 𝒪 h𝒪 a fun V g => by
    rw [resSection_smul]
    exact smul_comm_section 𝒪 h𝒪 V _ _ _

/-- The rank-one morphism is additive in the functional. -/
lemma rankOneHomSection_add_right {U : C} (f : F.val.obj (op U))
    (lam mu : (dualSheaf 𝒪 h𝒪 E).val.obj (op U)) :
    rankOneHomSection 𝒪 h𝒪 f (lam + mu) =
      rankOneHomSection 𝒪 h𝒪 f lam + rankOneHomSection 𝒪 h𝒪 f mu :=
  rankOneHomSection_eq_add 𝒪 h𝒪 fun V g => by
    rw [dualApp_add, add_smul]

/-- The rank-one morphism is homogeneous in the functional. -/
lemma rankOneHomSection_smul_right {U : C}
    (a : (TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)) (f : F.val.obj (op U))
    (lam : (dualSheaf 𝒪 h𝒪 E).val.obj (op U)) :
    rankOneHomSection 𝒪 h𝒪 f (a • lam) = a • rankOneHomSection 𝒪 h𝒪 f lam :=
  rankOneHomSection_eq_smul 𝒪 h𝒪 a fun V g => by
    rw [dualApp_smul_left, mul_smul]

/-- **The rank-one morphism is natural**: restricting the section and the functional from `X` to
`Y` and then forming the rank-one morphism is restricting the rank-one morphism. -/
lemma rankOneHomSection_naturality {X Y : Cᵒᵖ} (i : X ⟶ Y) (f : F.val.obj X)
    (lam : (dualSheaf 𝒪 h𝒪 E).val.obj X) :
    rankOneHomSection 𝒪 h𝒪 (U := Y.unop) ((F.val.map i).hom f)
        (ConcreteCategory.hom ((dualSheaf 𝒪 h𝒪 E).val.map i) lam) =
      ConcreteCategory.hom ((sheafHom 𝒪 h𝒪 E F).val.map i)
        (rankOneHomSection 𝒪 h𝒪 (U := X.unop) f lam) := by
  refine internalHom_ext 𝒪 h𝒪 _ _ fun V g => ?_
  refine (rankOneHomSection_app 𝒪 h𝒪 _ _ V g).trans ?_
  refine Eq.trans ?_ (internalHom_map_app_apply 𝒪 E.val F.val i
    (rankOneHomSection 𝒪 h𝒪 (U := X.unop) f lam) V g).symm
  refine Eq.trans ?_ (rankOneHomSection_app 𝒪 h𝒪 (U := X.unop) f lam
    (op ((Over.map i.unop).obj V.unop)) g).symm
  exact congrArg (dualApp lam (op ((Over.map i.unop).obj V.unop)) g • ·)
    (resSection_map 𝒪 h𝒪 (L := F) i.unop V f)

attribute [local instance] monoidalCategoryPresheafOfModules

/-- **The rank-one map `F ⊗ E^∨ ⟶ SheafHom(E, F)`**, as a morphism out of the pointwise tensor
product of presheaves of modules. On sections it is `f ⊗ lam ↦ (g ↦ lam(g) • f)`. -/
noncomputable def tensorDualHomPresheaf
    (E F : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    F.val ⊗ (dualSheaf 𝒪 h𝒪 E).val ⟶ (sheafHom 𝒪 h𝒪 E F).val := by
  refine PresheafOfModules.Hom.mk (fun X ↦ ?_) ?_
  · exact ModuleCat.MonoidalCategory.tensorLift
      (fun (f : F.val.obj X) (lam : (dualSheaf 𝒪 h𝒪 E).val.obj X) ↦
        rankOneHomSection 𝒪 h𝒪 (U := X.unop) f lam)
      (fun f f' lam => rankOneHomSection_add_left 𝒪 h𝒪 f f' lam)
      (fun a f lam => rankOneHomSection_smul_left 𝒪 h𝒪 a f lam)
      (fun f lam mu => rankOneHomSection_add_right 𝒪 h𝒪 f lam mu)
      (fun a f lam => rankOneHomSection_smul_right 𝒪 h𝒪 a f lam)
  · intro X Y i
    exact ModuleCat.MonoidalCategory.tensor_ext fun f lam =>
      rankOneHomSection_naturality 𝒪 h𝒪 i f lam

/-- At `E = F` the rank-one map is `Stacks.SheafOfModules.endPresheaf`. -/
lemma tensorDualHomPresheaf_self
    (F : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    tensorDualHomPresheaf 𝒪 h𝒪 F F = endPresheaf 𝒪 h𝒪 F := rfl

/-- On sections over `U`, the rank-one map sends a pure tensor `f ⊗ lam` to the rank-one
morphism `rankOneHomSection f lam`. -/
@[simp]
lemma tensorDualHomPresheaf_tmul
    (E F : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪))
    (U : Cᵒᵖ) (f : F.val.obj U) (lam : (dualSheaf 𝒪 h𝒪 E).val.obj U) :
    ((tensorDualHomPresheaf 𝒪 h𝒪 E F).app U).hom
        (f ⊗ₜ[(TensorSheafification.structureRingPresheaf 𝒪).obj U] lam) =
      rankOneHomSection 𝒪 h𝒪 (U := U.unop) f lam := rfl

/-- The value of a section of `SheafHom(E, F)` over `U` on a section of `E` over `U`. -/
noncomputable def sheafHomEval {U : C} (a : (sheafHom 𝒪 h𝒪 E F).val.obj (op U))
    (x : E.val.obj (op U)) : F.val.obj (op U) :=
  evalSection 𝒪 E.val F.val (op U) a x

/-- At `E = F` the evaluation is `Stacks.SheafOfModules.endEval`. -/
lemma sheafHomEval_self {U : C} (a : (sheafHom 𝒪 h𝒪 F F).val.obj (op U))
    (x : F.val.obj (op U)) : sheafHomEval 𝒪 h𝒪 a x = endEval 𝒪 h𝒪 a x := rfl

/-- Evaluating the zero section of `SheafHom(E, F)` at any section of `E` gives zero. -/
lemma sheafHomEval_zero {U : C} (x : E.val.obj (op U)) :
    sheafHomEval 𝒪 h𝒪 (0 : (sheafHom 𝒪 h𝒪 E F).val.obj (op U)) x = 0 := rfl

/-- Evaluation of sections of `SheafHom(E, F)` is additive in the section of `SheafHom(E, F)`. -/
lemma sheafHomEval_add {U : C} (a a' : (sheafHom 𝒪 h𝒪 E F).val.obj (op U))
    (x : E.val.obj (op U)) :
    sheafHomEval 𝒪 h𝒪 (a + a') x = sheafHomEval 𝒪 h𝒪 a x + sheafHomEval 𝒪 h𝒪 a' x := rfl

/-- **A finite dual basis for `E` makes the rank-one map bijective on sections over `U`**, for
every sheaf of modules `F`.

Surjectivity: a morphism `a : E|_U ⟶ F|_U` is the image of `∑ i, a(e i) ⊗ lam i`, because the
dual-basis identity of `E` turns `∑ i, lam i (g) • a(e i)` into `a(g)`. Injectivity: the same
formula is a two-sided inverse, computed on a pure tensor `f ⊗ l` by
`Stacks.SheafOfModules.FiniteDualBasis.eq_sum_smul_lam`. -/
theorem bijective_tensorDualHomPresheaf_app_of_finiteDualBasis {U : C} {I : Type*} [Fintype I]
    (b : FiniteDualBasis 𝒪 h𝒪 E U I)
    (F : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    Function.Bijective ((tensorDualHomPresheaf 𝒪 h𝒪 E F).app (op U)).hom := by
  classical
  have hright : ∀ a : (sheafHom 𝒪 h𝒪 E F).val.obj (op U),
      ((tensorDualHomPresheaf 𝒪 h𝒪 E F).app (op U)).hom
          (∑ i, sheafHomEval 𝒪 h𝒪 a (b.e i)
            ⊗ₜ[(TensorSheafification.structureRingPresheaf 𝒪).obj (op U)] b.lam i) = a := by
    intro a
    refine (map_sum ((tensorDualHomPresheaf 𝒪 h𝒪 E F).app (op U)).hom _ Finset.univ).trans ?_
    refine internalHom_ext 𝒪 h𝒪 _ _ fun V g => ?_
    refine (internalHom_sum_app_apply 𝒪 h𝒪 Finset.univ
      (fun i => ((tensorDualHomPresheaf 𝒪 h𝒪 E F).app (op U)).hom
        (sheafHomEval 𝒪 h𝒪 a (b.e i) ⊗ₜ b.lam i)) V g).trans ?_
    refine Eq.trans ?_ (congrArg (a.app V).hom (b.span V g))
    refine Eq.trans ?_ (map_sum (a.app V).hom _ Finset.univ).symm
    refine Finset.sum_congr rfl fun i _ => ?_
    refine (rankOneHomSection_app 𝒪 h𝒪 (sheafHomEval 𝒪 h𝒪 a (b.e i)) (b.lam i) V g).trans ?_
    refine Eq.trans ?_ ((a.app V).hom.map_smul _ _).symm
    exact congrArg (dualApp (b.lam i) V g • ·)
      (internalHom_app_restrict 𝒪 E.val F.val U a V (b.e i)).symm
  have hleft : ∀ t : (F.val ⊗ (dualSheaf 𝒪 h𝒪 E).val).obj (op U),
      (∑ i, sheafHomEval 𝒪 h𝒪 (((tensorDualHomPresheaf 𝒪 h𝒪 E F).app (op U)).hom t) (b.e i)
        ⊗ₜ[(TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)] b.lam i) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero =>
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) Finset.sum_const_zero
      refine Eq.trans (congrArg
        (· ⊗ₜ[(TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)] b.lam i)
        ((congrArg (fun z => sheafHomEval 𝒪 h𝒪 z (b.e i))
            (map_zero ((tensorDualHomPresheaf 𝒪 h𝒪 E F).app (op U)).hom)).trans
          (sheafHomEval_zero 𝒪 h𝒪 (b.e i)))) ?_
      exact TensorProduct.zero_tmul _ _
    | tmul f l =>
      have hev : ∀ i, sheafHomEval 𝒪 h𝒪 (((tensorDualHomPresheaf 𝒪 h𝒪 E F).app (op U)).hom
          (f ⊗ₜ[(TensorSheafification.structureRingPresheaf 𝒪).obj (op U)] l)) (b.e i) =
            dualEval l (b.e i) • f := by
        intro i
        refine (rankOneHomSection_app 𝒪 h𝒪 f l (op (Over.mk (𝟙 U))) (b.e i)).trans ?_
        rw [dualApp_self, resSection_self]
      have hstep : ∀ i : I,
          sheafHomEval 𝒪 h𝒪 (((tensorDualHomPresheaf 𝒪 h𝒪 E F).app (op U)).hom
                (f ⊗ₜ[(TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)] l)) (b.e i)
              ⊗ₜ[(TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)] b.lam i =
            f ⊗ₜ[(TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)]
              (dualEval l (b.e i) • b.lam i) := fun i =>
        (congrArg (· ⊗ₜ[(TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)] b.lam i)
          (hev i)).trans (TensorProduct.smul_tmul _ _ _)
      refine Eq.trans (Finset.sum_congr rfl fun i _ => hstep i) ?_
      refine Eq.trans (TensorProduct.tmul_sum f Finset.univ
        (fun i => dualEval l (b.e i) • b.lam i)).symm ?_
      exact congrArg (f ⊗ₜ[(TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)] ·)
        (b.eq_sum_smul_lam 𝒪 h𝒪 l)
    | add t s ht hs =>
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_)
        (Finset.sum_add_distrib.trans (congrArg₂ (· + ·) ht hs))
      refine Eq.trans (congrArg
        (· ⊗ₜ[(TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)] b.lam i)
        ((congrArg (fun z => sheafHomEval 𝒪 h𝒪 z (b.e i))
            (map_add ((tensorDualHomPresheaf 𝒪 h𝒪 E F).app (op U)).hom t s)).trans
          (sheafHomEval_add 𝒪 h𝒪 _ _ (b.e i)))) ?_
      exact TensorProduct.add_tmul _ _ _
  refine ⟨fun t t' h => ?_, fun a => ⟨_, hright a⟩⟩
  rw [← hleft t, ← hleft t', h]

/-! ### Local bijectivity of the rank-one map -/

/-- The rank-one map is locally injective when `E` has finite dual bases on a family covering the
final object. -/
theorem isLocallyInjective_tensorDualHomPresheaf {K : Type*} {X : K → C} (hX : J.CoversTop X)
    {I : K → Type*} [∀ k, Fintype (I k)] (b : ∀ k, FiniteDualBasis 𝒪 h𝒪 E (X k) (I k))
    (F : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    PresheafOfModules.IsLocallyInjective J (tensorDualHomPresheaf 𝒪 h𝒪 E F) := by
  constructor
  intro Z x y h
  refine J.superset_covering ?_ (hX Z.unop)
  rintro W p ⟨k, ⟨q⟩⟩
  have hn : ∀ t : (F.val ⊗ (dualSheaf 𝒪 h𝒪 E).val).obj Z,
      ((tensorDualHomPresheaf 𝒪 h𝒪 E F).app (op W)).hom
          (((F.val ⊗ (dualSheaf 𝒪 h𝒪 E).val).map p.op).hom t) =
        ConcreteCategory.hom ((sheafHom 𝒪 h𝒪 E F).val.map p.op)
          (((tensorDualHomPresheaf 𝒪 h𝒪 E F).app Z).hom t) :=
    PresheafOfModules.naturality_apply (tensorDualHomPresheaf 𝒪 h𝒪 E F) p.op
  apply (bijective_tensorDualHomPresheaf_app_of_finiteDualBasis 𝒪 h𝒪
    ((b k).restrict 𝒪 h𝒪 q) F).injective
  show ((tensorDualHomPresheaf 𝒪 h𝒪 E F).app (op W)).hom
      (((F.val ⊗ (dualSheaf 𝒪 h𝒪 E).val).map p.op).hom x)
    = ((tensorDualHomPresheaf 𝒪 h𝒪 E F).app (op W)).hom
      (((F.val ⊗ (dualSheaf 𝒪 h𝒪 E).val).map p.op).hom y)
  rw [hn x, hn y]
  exact congrArg (ConcreteCategory.hom ((sheafHom 𝒪 h𝒪 E F).val.map p.op)) h

/-- The rank-one map is locally surjective when `E` has finite dual bases on a family covering the
final object. -/
theorem isLocallySurjective_tensorDualHomPresheaf {K : Type*} {X : K → C} (hX : J.CoversTop X)
    {I : K → Type*} [∀ k, Fintype (I k)] (b : ∀ k, FiniteDualBasis 𝒪 h𝒪 E (X k) (I k))
    (F : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    PresheafOfModules.IsLocallySurjective J (tensorDualHomPresheaf 𝒪 h𝒪 E F) := by
  constructor
  intro Z s
  refine J.superset_covering ?_ (hX Z)
  rintro W p ⟨k, ⟨q⟩⟩
  exact (bijective_tensorDualHomPresheaf_app_of_finiteDualBasis 𝒪 h𝒪
    ((b k).restrict 𝒪 h𝒪 q) F).surjective _

section Sheafification

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]

/-- **The canonical rank-one morphism `F ⊗ E^∨ ⟶ SheafHom(E, F)`** of sheaves of modules. The
tensor product of sheaves of modules is the sheafification of the pointwise one (Tag 05NA), so
this is the morphism which `Stacks.SheafOfModules.tensorDualHomPresheaf` induces through the
sheafification adjunction. -/
noncomputable def tensorDualToSheafHom
    (E F : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    ((Tensor.sheafTensor
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj F).obj
        (dualSheaf 𝒪 h𝒪 E) ⟶ sheafHom 𝒪 h𝒪 E F :=
  ((TensorSheafification.sheafifyAdjunction 𝒪 h𝒪).homEquiv
    ((PresheafOfModules.tensorObj (O := 𝒪) (F.val) ((dualSheaf 𝒪 h𝒪 E).val)))
    (sheafHom 𝒪 h𝒪 E F)).symm (tensorDualHomPresheaf 𝒪 h𝒪 E F)

/-- At `E = F` the canonical morphism is
`Stacks.SheafOfModules.tensorDualToEndomorphism`, the map of Tags 0FNV and 0FNY. -/
lemma tensorDualToSheafHom_self
    (F : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    tensorDualToSheafHom 𝒪 h𝒪 F F = tensorDualToEndomorphism 𝒪 h𝒪 F := rfl

/-- **The canonical morphism on a local pure tensor is the rank-one morphism.** This pins the
morphism down: its value on the image of `f ⊗ lam` is the morphism `g ↦ lam(g) • f`. -/
theorem tensorDualToSheafHom_toTensorSheafSection
    (E F : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)) (U : Cᵒᵖ)
    (f : F.val.obj U) (lam : (dualSheaf 𝒪 h𝒪 E).val.obj U) :
    ((tensorDualToSheafHom 𝒪 h𝒪 E F).val.app U).hom
        (toTensorSheafSection 𝒪 h𝒪 F (dualSheaf 𝒪 h𝒪 E) U
          (f ⊗ₜ[(TensorSheafification.structureRingPresheaf 𝒪).obj U] lam)) =
      rankOneHomSection 𝒪 h𝒪 (U := U.unop) f lam :=
  congrArg (fun φ => ((φ.app U).hom (f
    ⊗ₜ[(TensorSheafification.structureRingPresheaf 𝒪).obj U] lam)))
    (((TensorSheafification.sheafifyAdjunction 𝒪 h𝒪).homEquiv
      ((PresheafOfModules.tensorObj (O := 𝒪) (F.val) ((dualSheaf 𝒪 h𝒪 E).val)))
      (sheafHom 𝒪 h𝒪 E F)).apply_symm_apply (tensorDualHomPresheaf 𝒪 h𝒪 E F))

/-- **Sheafification inverts the rank-one map**, when `E` has finite dual bases on a family
covering the final object. -/
theorem isIso_sheafify_map_tensorDualHomPresheaf {K : Type*} {X : K → C} (hX : J.CoversTop X)
    {I : K → Type*} [∀ k, Fintype (I k)] (b : ∀ k, FiniteDualBasis 𝒪 h𝒪 E (X k) (I k))
    (F : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    IsIso ((TensorSheafification.sheafify 𝒪 h𝒪).map (tensorDualHomPresheaf 𝒪 h𝒪 E F)) := by
  have := isLocallyInjective_tensorDualHomPresheaf 𝒪 h𝒪 hX b F
  have := isLocallySurjective_tensorDualHomPresheaf 𝒪 h𝒪 hX b F
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf
    (TensorSheafification.structureSheaf 𝒪 h𝒪))]
  exact (J.W_iff _).mp (J.W_of_isLocallyBijective
    ((PresheafOfModules.toPresheaf (TensorSheafification.structureSheaf 𝒪 h𝒪).obj).map
      (tensorDualHomPresheaf 𝒪 h𝒪 E F)))

/-- **`F ⊗ E^∨ ⟶ SheafHom(E, F)` is an isomorphism** when `E` has finite dual bases on a family
covering the final object — that is, when `E` is locally a direct summand of a finite free sheaf
of modules — and `F` is arbitrary.

This is step (5) of the proof of Stacks 08JJ, in the sectionwise form of the local hypothesis;
`Stacks.SheafOfModules.isIso_tensorDualToSheafHom_of_localSummand` is the same statement with
the hypothesis in the per-object form of Tag 0FNY. -/
@[ega "0 5.4.2" "more general"]
theorem isIso_tensorDualToSheafHom {K : Type*} {X : K → C} (hX : J.CoversTop X)
    {I : K → Type*} [∀ k, Fintype (I k)] (b : ∀ k, FiniteDualBasis 𝒪 h𝒪 E (X k) (I k))
    (F : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    IsIso (tensorDualToSheafHom 𝒪 h𝒪 E F) := by
  have hm : IsIso ((TensorSheafification.sheafify 𝒪 h𝒪).map
      (tensorDualHomPresheaf 𝒪 h𝒪 E F)) :=
    isIso_sheafify_map_tensorDualHomPresheaf 𝒪 h𝒪 hX b F
  have hc : IsIso ((TensorSheafification.sheafifyAdjunction 𝒪 h𝒪).counit.app
      (sheafHom 𝒪 h𝒪 E F)) :=
    inferInstanceAs (IsIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (TensorSheafification.structureSheaf 𝒪 h𝒪).obj)).counit.app (sheafHom 𝒪 h𝒪 E F)))
  have h := Adjunction.homEquiv_counit
    (TensorSheafification.sheafifyAdjunction 𝒪 h𝒪)
    ((PresheafOfModules.tensorObj (O := 𝒪) (F.val) ((dualSheaf 𝒪 h𝒪 E).val)))
    (sheafHom 𝒪 h𝒪 E F) (tensorDualHomPresheaf 𝒪 h𝒪 E F)
  rw [tensorDualToSheafHom, h]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hm hc

end Sheafification

end RankOne

section LocalSummand

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
  (h𝒪 : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf 𝒪))
  (E F : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- **Step (5) of the proof of Stacks 08JJ.** Let `(C, 𝒪)` be a ringed site, let `E` be a sheaf of
`𝒪`-modules which is locally a direct summand of a finite free sheaf of modules, and let `F` be an
arbitrary sheaf of `𝒪`-modules. Then the canonical map

`F ⊗_𝒪 SheafHom(E, 𝒪) ⟶ SheafHom(E, F)`

is an isomorphism.

The map is `Stacks.SheafOfModules.tensorDualToSheafHom`, pinned down on local sections by
`Stacks.SheafOfModules.tensorDualToSheafHom_toTensorSheafSection`. At `E = F` this is the first
assertion of Tag 0FNY, `Stacks.SheafOfModules.isIso_tensorDualToEndomorphism_of_localSummand`.

The hypothesis is the one of Tag 0FNY, that `E` is a summand of a finite free module *locally*;
Stacks 08JJ's step (5) asks for a global summand, which is a special case. -/
@[stacks 08JJ "step (5) of the proof only: the canonical map
`F ⊗_𝒪 SheafHom(E, 𝒪) ⟶ SheafHom(E, F)` is an isomorphism for `E` locally a summand of a finite
free module and `F` arbitrary. None of the tag's four assertions is proved here; in particular
the derived statement `M ⊗^L_𝒪 K^∨ ≅ RSheafHom(K, M)` for perfect `K` is not, and still needs a
complex-level comparison with its Koszul signs, the tensor-side analogue of Tag 08JH, locality
of the derived tensor product on a slice, and a K-flat representative on a ringed site.",
  ega "0 5.4.2" "more general", sga "5 IIIB 5.0" "more general"]
theorem isIso_tensorDualToSheafHom_of_localSummand
    (hE : IsLocallyDirectSummandOfFiniteFree 𝒪 h𝒪 E) :
    IsIso (tensorDualToSheafHom 𝒪 h𝒪 E F) := by
  set c := localFiniteFreeSummandCover 𝒪 h𝒪 E hE
  let := c.fintypeI
  let := c.decEqI
  exact isIso_tensorDualToSheafHom 𝒪 h𝒪 c.coversTop
    (fun k => FiniteDualBasis.ofRetract 𝒪 h𝒪 (c.retract k)) F

end LocalSummand

end Stacks.SheafOfModules

end
