module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.FiniteFreeLift
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.ModuleFunctorAtBase
public import StacksCore.Tactic.StacksAttribute

/-!
# Positive-degree Ext vanishing out of a finitely presented module functor

Let `A` be a ring, let `M` and `P` be `A`-modules and let `P` be of finite presentation.  In
the category `𝒫` of module-valued functors on the commutative `A`-algebras,
`Ext^i_𝒫(P̲, M̲) = 0` for `i > 0`, where `X̲` denotes `B ↦ B ⊗[A] X`.  The degrees `1` and `2`
are proved here.

Choose a finite presentation `Aᵐ --d--> Aⁿ ⟶ P ⟶ 0`.  Base change is right exact, so `P̲` is
the cokernel of `d̲`, and the two canonical short exact sequences of `d̲` are

* `0 ⟶ ker d̲ ⟶ Aᵐ̲ ⟶ im d̲ ⟶ 0`,
* `0 ⟶ im d̲ ⟶ Aⁿ̲ ⟶ P̲ ⟶ 0`.

The functor of a finite free module is a projective object of `𝒫`
(`AdequateFunctor.projective_moduleExtension`), so the contravariant long exact sequence of the
second one turns each of the two degrees into a lifting problem on `Ext⁰`, which is what
`CategoryTheory.Abelian.Ext.one_subsingleton_iff_of_projective` asks for:

* degree `1` needs every morphism `im d̲ ⟶ M̲` to extend across `im d̲ ⟶ Aⁿ̲`;
* degree `2` needs it for `ker d̲ ⟶ M̲` across `ker d̲ ⟶ Aᵐ̲`, which is [Stacks, Tag 06V0]
  (`AdequateFunctor.exists_lift_from_finite_free_kernel`).

The degree-one lifting problem is solved here by the device that also proves Tag 06V0: a
morphism out of a finite free module functor is determined by its value on one universal
section.  The universal algebra is the square-zero extension `A[N]` of `A` by
`AdequateFunctor.universalSolutionModule`, the cokernel of the transpose of `d`, and the
universal section is the tuple of classes of the standard basis vectors.  It lies in `ker d̲`
because the `j`-th relation it has to satisfy is the `j`-th column of the transpose, hence
zero in the cokernel.  Reading off its `N`-component then says that the tuple defining the
given morphism is a transpose image, and that is a factorisation through `d`.

## Main results

* `AdequateFunctor.exists_factor_of_vanishing_on_kernel` — the image-side companion of Tag
  06V0: a morphism out of `Aᵐ̲` which kills every section killed by `d̲` factors through `d`.
  With `AdequateFunctor.image_ι_comp_map_eq` this extends every `φ : im d̲ ⟶ M̲` to `Aⁿ̲`.
* `AdequateFunctor.subsingleton_ext_one_moduleExtension`,
  `AdequateFunctor.subsingleton_ext_two_moduleExtension_large` — the vanishing in degrees `1` and
  `2` for Mathlib's natural-number-graded `Ext`, at an arbitrary `HasExt` universe.
* `AdequateFunctor.subsingleton_zExt_moduleExtension_one`,
  `AdequateFunctor.subsingleton_zExt_moduleExtension_two_large` — the same two for the
  integer-graded `CategoryTheory.Abelian.zExt` of this library, which is how [Stacks, Tag
  06ZG] is phrased here.  Each carries the tag with a note naming the degree it covers.

## Relation to Tag 06ZG

Tag 06ZG asserts the vanishing for every `i > 0`.  The degrees `1` and `2` are registered,
each with a note naming the degree it covers.  The degrees `≥ 3` are not proved here, and the
source's argument for them is not available in this library: it needs property `(*)` of
[Stacks, Tag 06ZF] for the terms of an injective resolution of `M̲`, which is the content of
[Stacks, Tag 06ZA], and the middle-exactness half of that tag is false.  The refutation is
`AdequateFunctor.not_forall_hasRightExactTangentFunctor_of_injective` in
`StacksFrontier.Examples.Algebra.InjectiveTangentNotRightExact`; the corrected form of Tag 06ZA,
surjectivity only, is `AdequateFunctor.epi_tangentFunctorAt_map_of_injective`, and the module
documentation of
`StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.ModuleFunctorAtBase` records why
the surviving half does not help.

Dimension shifting along the two sequences above locates what is missing.  Both `Aⁿ̲` and
`Aᵐ̲` are projective, so the two contravariant long exact sequences give, for `i ≥ 3`,
surjections `Ext^{i-1}_𝒫(im d̲, M̲) ↠ Ext^i_𝒫(P̲, M̲)` and
`Ext^{i-2}_𝒫(ker d̲, M̲) ↠ Ext^{i-1}_𝒫(im d̲, M̲)`.  So the positive-degree vanishing
`Ext^j_𝒫(ker d̲, M̲) = 0` for `j ≥ 1` — that is, [Stacks, Tag 06ZH] for a linearly adequate
functor — implies the degrees `≥ 3` of this tag.  Its degree `j = 1` IS available: by
Remark 06V7 of the source every extension of a linearly adequate functor by an adequate one
splits, and that is proved at a free module universe as
`AdequateFunctor.exists_retraction_of_shortExact_large` in
`StacksFrontier.Algebra.Module.Adequate.Splitting06V7Large`, so degree `3` of this tag is
assembly work rather than a gap.  The degrees `j ≥ 2` of that statement are what nothing in
this library proves, and they are the whole of what is missing.

### The circle

Four tags of Stacks 46.4 and 46.9 rest on that one statement, and in this library they are
mutually equivalent rather than successively weaker, so none of them can be used to reach
another:

* degrees `≥ 3` of Tag 06ZG are **isomorphic** to Tag 06ZH for a linearly adequate functor.
  Both middle terms of the two sequences above are projective, so the dimension shift is an
  isomorphism and not merely a surjection in the direction that would help.
* Tag 06ZH's own proof consumes this tag, Tag 06ZG, and not Tag 06ZI: the source's proof of
  Tag 06ZH derives it from Tag 06ZG alone, by two dimension shifts.  The theorem
  `AdequateFunctor.subsingleton_zExt_of_isLinearlyAdequate` carries that consumption as the
  hypothesis `hM`, which quantifies over **every** positive degree; its proof appeals to `hM`
  only in degrees `≥ 3`, the two lower degrees being discharged in that module.
* Tag 06ZI is `AdequateFunctor.isZero_rightDerivedPlus_adequateCoreflection`, whose hypothesis
  `hFP` is this tag at every positive degree.
* Tag 06ZU, `Stacks.Adequate.isZero_rightDerived_adequator`, carries the inputs it is stated
  with — `hacyclic`, `P` with `hP` and `hExt`, besides the adequator's own data
  `Q`, `E`, `adj`, `hj` and `comm`.  Two of them are dischargeable from declarations in the
  tree: `hacyclic`, for an adequate module, by
  `Stacks.Adequate.affineSectionsAcyclic_of_isAdequate`, and `P` with `hP` by
  `Stacks.Adequate.adequateSeparatingFamily` and
  `Stacks.Adequate.isSeparating_adequateSeparatingFamily`; `hj` is
  `Stacks.Adequate.fullyFaithfulAffineSectionsFunctor`.  They are nevertheless still *carried*,
  because discharging them in place would change that theorem's statement.  `hExt` is Tag 06ZI
  at the separating family
  and so rests on this tag.  Tag 06ZW and Tag 0709 reduce to Tag 06ZU in
  turn.

The source escapes the circle only through property `(*)` for injective objects, and that is
the half of Tag 06ZA which is **false here** — refuted by
`AdequateFunctor.not_forall_hasRightExactTangentFunctor_of_injective`, with Tag 06ZA surviving
as an erratum carrying surjectivity alone.

**No erratum is recorded for Tag 06ZG, and none should be inferred from this note.**  What is
recorded here is only the mathematics: the single missing statement, in
Lean, immediately below; that the four tags are equivalent modulo it; and that the source's
route to it is unavailable in this library, with the refutation cited.  Two routes that look
like they avoid Tag 06ZA have been tried and both fail at one identifiable step — computing
`R^pQ(M̲)` from a pure injective resolution fails because
`injective_moduleExtension_of_pureInjective` concludes injectivity in the full subcategory of
adequate functors, not in `𝒫`, and `R^pQ` is computed from resolutions in `𝒫`; and a route
through corepresentability of `ker d̲` by `AdequateFunctor.universalSolutionAlgebra`, which was
*argued* to give projectivity of `ker d̲` among the adequate functors via a weight-one lift from
the grading.  **That projectivity is not available**: no declaration in this library concludes
`Projective` of any object of any `ObjectProperty.FullSubcategory`, and the only `Projective`
conclusion in the adequate development is `AdequateFunctor.projective_moduleExtension`, which is
in the *ambient* category and about `moduleExtension A Q` for a projective module `Q` — not about
any kernel.  So that step is a described argument, not an available fact, and nothing below may
cite it.

That second route is **refuted outright**, and the refutation is proved rather than asserted:
`AdequateFunctor.not_projective_twoTorsionKernel` of
`StacksFrontier.Examples.Algebra.LinearlyAdequateNotProjective` shows `ker d̲` is *not* projective
in `𝒫`, for `d` multiplication by two on `finiteFreeModule ℤ 1` — an actual presentation of
`ℤ/2`.  **It does not refute the missing statement.**  The nonvanishing it exhibits is at a
*non-adequate* target (the free functor's kernel), whereas the statement needed below has a
module extension — an adequate functor — as its target, and may well be true.  What that
counterexample establishes is where a proof must get its leverage: the obstruction is adequacy
of the functor one lifts into, so any proof must use adequacy of the target by some means other
than property `(*)` of [Stacks, Tag 06ZF].  That is the open direction; the routes closed so far
are *routes*, and none of them is a statement about the goal.

A **fourth** route is closed, and it fails for a different kind of reason than the other three —
not at a mathematical step but logically, its hypothesis being its conclusion.  One may ask
whether `Ext^j_𝒫(L, M̲) ≅ Ext^j_𝒜(L, M̲)` for adequate arguments, since then projectivity of `L`
in `𝒜` would suffice.  The comparison at a *single pair* genuinely needs less than
[Stacks, Tag 06ZU]: `Stacks.ExtAdjunction.mapExtAddHom_bijective_of_isZero_rightDerived` asks
only for vanishing of the right derived functors at the one target.  But acyclicity at `M̲` is
itself this tag at `M̲`: `AdequateFunctor.rightAcyclic_moduleExtension` is the library's only
route to it and discharges it from the same `hFP`, whose residual degrees `≥ 3` are isomorphic to
[Stacks, Tag 06ZH] at `M̲`, which is
`AdequateFunctor.subsingleton_zExt_of_isLinearlyAdequate` — the sought statement itself.
Narrowing the target removes the quantifier over the *second* argument, but this tag was already
stated per-target; the quantifier that survives runs over the *first*, whose range is the
linearly adequate functors.  So the route would re-derive that theorem from its own hypothesis,
and no re-engineering of the comparison step changes that.

The vanishing is not a projectivity statement about `P̲`: for `P` merely of finite
presentation `P̲` is not a projective object, as recorded in `ModuleFunctorAtBase`.

## Implementation notes

The module universe is a free parameter containing the universe of the algebra carriers, as in
`AdequateFunctor.moduleExtensionFunctor_preservesFiniteColimits`, which is what identifies
`P̲` with the cokernel of `d̲`, and in Tag 06V0.

`AdequateFunctor.imageLift` and `AdequateFunctor.imageFactorHom` exist only to pay a
respelling.  The value of the extension functor at a module and that module's extension are
the same object by definition, but the elaborator does not cross them cheaply here: each use
site that crosses costs more than the default heartbeat budget, while crossing once, as these
definitions' own types, costs nothing measurable.  `imageFactorHom` is the load-bearing one,
because reading the composite with the projection onto the image as the base change of a
module map needs the source spelled `moduleExtension A (finiteFreeModule A m)`.

## References

* [Stacks Project, Tag 06V0](https://stacks.math.columbia.edu/tag/06V0)
* [Stacks Project, Tag 06ZA](https://stacks.math.columbia.edu/tag/06ZA)
* [Stacks Project, Tag 06ZG](https://stacks.math.columbia.edu/tag/06ZG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t v u w z

namespace AdequateFunctor

section AbelianFactorisation

variable {C : Type u} [Category.{v} C] [Abelian C] {X Y : C} (δ : X ⟶ Y)

/-- The kernel inclusion of `δ` is annihilated by the projection onto the image of `δ`. -/
lemma kernel_ι_comp_factorThruImage : kernel.ι δ ≫ Abelian.factorThruImage δ = 0 :=
  zero_of_comp_mono (Abelian.image.ι δ)
    (by rw [Category.assoc, Abelian.image.fac, kernel.condition])

/-- The short complex `ker δ ⟶ X ⟶ im δ`. -/
noncomputable abbrev coimageShortComplex : ShortComplex C :=
  ShortComplex.mk (kernel.ι δ) (Abelian.factorThruImage δ) (kernel_ι_comp_factorThruImage δ)

/-- `0 ⟶ ker δ ⟶ X ⟶ im δ ⟶ 0` is short exact: the kernel inclusion of `δ` is a kernel of the
projection onto the image, because the image inclusion is a monomorphism. -/
lemma coimageShortComplex_shortExact : (coimageShortComplex δ).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _
    (KernelFork.IsLimit.ofι' _ _ fun k hk =>
      ⟨kernel.lift δ k (by
        rw [← Abelian.image.fac δ, ← Category.assoc, hk, zero_comp]), by simp⟩)
  mono_f := inferInstance
  epi_g := inferInstance

/-- The short complex `im δ ⟶ Y ⟶ coker δ`. -/
noncomputable abbrev abelianImageShortComplex : ShortComplex C :=
  ShortComplex.mk (Abelian.image.ι δ) (cokernel.π δ)
    (Abelian.image_ι_comp_eq_zero (cokernel.condition δ))

/-- `0 ⟶ im δ ⟶ Y ⟶ coker δ ⟶ 0` is short exact: the image of `δ` is by definition the kernel
of the cokernel projection. -/
lemma abelianImageShortComplex_shortExact : (abelianImageShortComplex δ).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel (cokernel.π δ))
  mono_f := inferInstance
  epi_g := inferInstance

end AbelianFactorisation

section ExtSteps

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{t} C] {X Y : C}

/-- Vanishing of an extension group is invariant under an isomorphism of the source. -/
lemma subsingleton_ext_of_iso_left {X X' Y : C} (e : X ≅ X') (n : ℕ)
    (h : Subsingleton (Abelian.Ext.{t} X Y n)) : Subsingleton (Abelian.Ext.{t} X' Y n) := by
  have key : ∀ z : Abelian.Ext.{t} X' Y n, (Abelian.Ext.mk₀ e.inv).comp
      ((Abelian.Ext.mk₀ e.hom).comp z (zero_add n)) (zero_add n) = z := fun z => by
    rw [Abelian.Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Abelian.Ext.mk₀_id_comp]
  refine ⟨fun a b => ?_⟩
  rw [← key a, ← key b, h.elim ((Abelian.Ext.mk₀ e.hom).comp a (zero_add n))
    ((Abelian.Ext.mk₀ e.hom).comp b (zero_add n))]

/-- `Ext¹(S.X₃, Z) = 0` for a short exact sequence whose middle term is projective, when every
morphism out of `S.X₁` extends across `S.f`. -/
private lemma subsingleton_ext_one_of_shortExact {S : ShortComplex C} (hS : S.ShortExact)
    (hX : Projective S.X₂) (Z : C) (hlift : ∀ φ : S.X₁ ⟶ Z, ∃ ψ : S.X₂ ⟶ Z, S.f ≫ ψ = φ) :
    Subsingleton (Abelian.Ext.{t} S.X₃ Z 1) := by
  rw [Abelian.Ext.one_subsingleton_iff_of_projective Z S hS hX]
  intro x₁
  obtain ⟨ψ, hψ⟩ := hlift (Abelian.Ext.addEquiv₀ x₁)
  refine ⟨Abelian.Ext.mk₀ ψ, ?_⟩
  change (Abelian.Ext.mk₀ S.f).comp (Abelian.Ext.mk₀ ψ) (add_zero 0) = x₁
  rw [Abelian.Ext.mk₀_comp_mk₀, hψ, Abelian.Ext.mk₀_addEquiv₀_apply]

/-- `Ext¹(im δ, Z) = 0` when the source of `δ` is projective and every morphism out of the
kernel of `δ` extends across the kernel inclusion. -/
lemma subsingleton_ext_one_image (δ : X ⟶ Y) (hX : Projective X) (Z : C)
    (hlift : ∀ φ : kernel δ ⟶ Z, ∃ ψ : X ⟶ Z, kernel.ι δ ≫ ψ = φ) :
    Subsingleton (Abelian.Ext.{t} (Abelian.image δ) Z 1) := by
  exact subsingleton_ext_one_of_shortExact (coimageShortComplex_shortExact δ) hX Z hlift

/-- `Ext¹(coker δ, Z) = 0` when the target of `δ` is projective and every morphism out of the
image of `δ` extends across the image inclusion: the contravariant long exact sequence of
`0 ⟶ im δ ⟶ Y ⟶ coker δ ⟶ 0` presents `Ext¹(coker δ, Z)` as the cokernel of
`Hom(Y, Z) ⟶ Hom(im δ, Z)`. -/
lemma subsingleton_ext_one_cokernel (δ : X ⟶ Y) (hY : Projective Y) (Z : C)
    (hext : ∀ φ : Abelian.image δ ⟶ Z, ∃ ψ : Y ⟶ Z, Abelian.image.ι δ ≫ ψ = φ) :
    Subsingleton (Abelian.Ext.{t} (cokernel δ) Z 1) := by
  exact subsingleton_ext_one_of_shortExact (abelianImageShortComplex_shortExact δ) hY Z hext

/-- `Ext²(coker δ, Z) = 0` when the target of `δ` is projective and `Ext¹(im δ, Z) = 0`: the
contravariant long exact sequence of `0 ⟶ im δ ⟶ Y ⟶ coker δ ⟶ 0` puts `Ext²(coker δ, Z)`
between `Ext¹(im δ, Z)` and `Ext²(Y, Z)`. -/
lemma subsingleton_ext_two_cokernel (δ : X ⟶ Y) (hY : Projective Y) (Z : C)
    (h1 : Subsingleton (Abelian.Ext.{t} (Abelian.image δ) Z 1)) :
    Subsingleton (Abelian.Ext.{t} (cokernel δ) Z 2) := by
  have := hY
  have h2 : Subsingleton (Abelian.Ext.{t} Y Z 2) :=
    Abelian.Ext.subsingleton_of_projective Y Z 1
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨x₁, hx₁⟩ := Abelian.Ext.contravariant_sequence_exact₃
    (abelianImageShortComplex_shortExact δ) (Y := Z) x (h2.elim _ _) (n₀ := 1) rfl
  rw [← hx₁, h1.elim x₁ 0, Abelian.Ext.comp_zero]

/-- `Ext^n(X, Y)` of Mathlib vanishing gives vanishing of the integer-graded `zExt`. -/
private lemma subsingleton_zExt_of_subsingleton_ext [HasDerivedCategory C] {n : ℕ}
    (h : Subsingleton (Abelian.Ext.{t} X Y n)) : Subsingleton (Abelian.zExt X Y n) :=
  ⟨fun _ _ => (Abelian.Ext.homAddEquiv (X := X) (Y := Y) (n := n)).symm.injective
    (Subsingleton.elim _ _)⟩

end ExtSteps

section Presentation

variable {A : Type u} [CommRing A]

/-- A finitely presented module is presented by a right exact sequence of finite free modules
in the universe of the module. -/
lemma exists_finiteFree_presentation_large (P : ModuleCat.{max u v w} A)
    [Module.FinitePresentation A P] :
    ∃ (n m : ℕ) (d : finiteFreeModule.{max v w} A m ⟶ finiteFreeModule.{max v w} A n)
      (p : finiteFreeModule.{max v w} A n ⟶ P),
      Function.Surjective p.hom ∧ Function.Exact d.hom p.hom := by
  obtain ⟨n, m, f, g, hf, hfg⟩ :=
    Module.FinitePresentation.exists_fin' A (P : Type (max u v w))
  refine ⟨n, m, ModuleCat.ofHom
      (ULift.moduleEquiv.symm.toLinearMap ∘ₗ g ∘ₗ ULift.moduleEquiv.toLinearMap),
    ModuleCat.ofHom (f ∘ₗ ULift.moduleEquiv.toLinearMap), hf.comp ULift.moduleEquiv.surjective,
    fun y => ?_⟩
  show f y.down = 0 ↔ _
  refine (hfg y.down).trans ⟨fun ⟨x, hx⟩ => ⟨ULift.up x, ?_⟩, fun ⟨x, hx⟩ => ⟨x.down, ?_⟩⟩
  · show ULift.up (g x) = y
    rw [hx]
    rfl
  · exact congrArg ULift.down hx

/-- The module-valued functor of a finitely presented module is the cokernel of the base
change of any finite presentation of it, because base change is right exact. -/
noncomputable def presentationCokernelIso_large {P : ModuleCat.{max u v w} A} {m n : ℕ}
    {d : finiteFreeModule.{max v w} A m ⟶ finiteFreeModule.{max v w} A n}
    {p : finiteFreeModule.{max v w} A n ⟶ P} (hp : Function.Surjective p.hom)
    (hdp : Function.Exact d.hom p.hom) :
    cokernel ((moduleExtensionFunctor.{max u v w, v} A).map d) ≅
      moduleExtension.{max u v w, v} A P := by
  have hdp0 : d ≫ p = 0 :=
    ModuleCat.hom_ext (LinearMap.ext fun x => (hdp (d.hom x)).mpr ⟨x, rfl⟩)
  have hex : (ShortComplex.mk d p hdp0).Exact := by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact (LinearMap.exact_iff.mp hdp).symm
  haveI : Epi p := (ModuleCat.epi_iff_surjective p).mpr hp
  exact (moduleExtensionCokernelIso d).symm ≪≫ (moduleExtensionFunctor.{max u v w, v} A).mapIso
    ((cokernelIsCokernel d).coconePointUniqueUpToIso hex.gIsCokernel)

/-- **Stacks Project, Tag 06V0**, in the form used here: a morphism from the kernel of the base
change of a map of finite free modules to a module functor extends to the middle term. -/
lemma exists_lift_from_kernel_moduleExtension_large (M : ModuleCat.{max u v w} A) {m n : ℕ}
    (d : finiteFreeModule.{max v w} A m ⟶ finiteFreeModule.{max v w} A n)
    (φ : kernel ((moduleExtensionFunctor.{max u v w, v} A).map d) ⟶
      moduleExtension.{max u v w, v} A M) :
    ∃ ψ : (moduleExtensionFunctor.{max u v w, v} A).obj (finiteFreeModule.{max v w} A m) ⟶
      moduleExtension.{max u v w, v} A M,
      kernel.ι ((moduleExtensionFunctor.{max u v w, v} A).map d) ≫ ψ = φ :=
  exists_lift_from_finite_free_kernel.{max v w} A (M : Type (max u v w)) m n
    (kernel ((moduleExtensionFunctor.{max u v w, v} A).map d))
    (kernel.ι _) ((moduleExtensionFunctor.{max u v w, v} A).map d) φ
    (kernel.condition _) (ShortComplex.kernelSequence_exact _)

/-! ### The forms the base carries

The three declarations of this section and the two theorems of the section after it are these
results at module universe `max u v`. The `_large` forms
above are the same statements with the module universe a free parameter, which is what the
degree-one argument and the consumers of Tag 06ZG need. Both are kept: taking `w := v` in a
`_large` form recovers one of them. -/

/-- A finitely presented module is presented by a right exact sequence of finite free modules
in the universe of the module. -/
lemma exists_finiteFree_presentation (P : ModuleCat.{max u v} A)
    [Module.FinitePresentation A P] :
    ∃ (n m : ℕ) (d : finiteFreeModule.{v} A m ⟶ finiteFreeModule.{v} A n)
      (p : finiteFreeModule.{v} A n ⟶ P),
      Function.Surjective p.hom ∧ Function.Exact d.hom p.hom :=
  exists_finiteFree_presentation_large.{v, u, v} P

/-- The module-valued functor of a finitely presented module is the cokernel of the base
change of any finite presentation of it, because base change is right exact. -/
noncomputable def presentationCokernelIso {P : ModuleCat.{max u v} A} {m n : ℕ}
    {d : finiteFreeModule.{v} A m ⟶ finiteFreeModule.{v} A n}
    {p : finiteFreeModule.{v} A n ⟶ P} (hp : Function.Surjective p.hom)
    (hdp : Function.Exact d.hom p.hom) :
    cokernel ((moduleExtensionFunctor.{max u v, v} A).map d) ≅
      moduleExtension.{max u v, v} A P := by
  have hdp0 : d ≫ p = 0 :=
    ModuleCat.hom_ext (LinearMap.ext fun x => (hdp (d.hom x)).mpr ⟨x, rfl⟩)
  have hex : (ShortComplex.mk d p hdp0).Exact := by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact (LinearMap.exact_iff.mp hdp).symm
  haveI : Epi p := (ModuleCat.epi_iff_surjective p).mpr hp
  exact (moduleExtensionCokernelIso d).symm ≪≫ (moduleExtensionFunctor.{max u v, v} A).mapIso
    ((cokernelIsCokernel d).coconePointUniqueUpToIso hex.gIsCokernel)

/-- **Stacks Project, Tag 06V0**, in the form used here: a morphism from the kernel of the base
change of a map of finite free modules to a module functor extends to the middle term. -/
lemma exists_lift_from_kernel_moduleExtension (M : ModuleCat.{max u v} A) {m n : ℕ}
    (d : finiteFreeModule.{v} A m ⟶ finiteFreeModule.{v} A n)
    (φ : kernel ((moduleExtensionFunctor.{max u v, v} A).map d) ⟶
      moduleExtension.{max u v, v} A M) :
    ∃ ψ : (moduleExtensionFunctor.{max u v, v} A).obj (finiteFreeModule.{v} A m) ⟶
      moduleExtension.{max u v, v} A M,
      kernel.ι ((moduleExtensionFunctor.{max u v, v} A).map d) ≫ ψ = φ :=
  exists_lift_from_kernel_moduleExtension_large.{v, u, v} M d φ

end Presentation

section ImageLift

/-! ### The image-side companion of Tag 06V0

Tag 06V0 extends a morphism out of the *kernel* of a map of finite free module-valued functors
across the kernel inclusion.  Degree one of Tag 06ZG needs the same for the *image*.  Both are
proved by evaluating on one universal section; the universal algebra used here is a
square-zero extension rather than a symmetric algebra, which makes the graded piece that has
to be read off a direct summand. -/

variable {A : Type u} [CommRing A]

/-- A vector is the combination of the standard basis vectors by its own coordinates. -/
lemma pi_eq_sum_single {k : ℕ} (x : Fin k → A) :
    x = ∑ j, x j • (Pi.single j 1 : Fin k → A) := by
  funext i
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

/-- The linear map determined by a tuple, evaluated on an arbitrary vector. -/
lemma linearMapOfTuple_apply {C : Type z} [AddCommGroup C] [Module A C] {n : ℕ}
    (zs : Fin n → C) (x : Fin n → A) :
    linearMapOfTuple A C zs x = ∑ j, x j • zs j := by
  simp [linearMapOfTuple, LinearMap.sum_apply]

/-- The tuple-to-section map of the module-valued functor of a finite free module.  This is
the one place where the universe lift inside `AdequateFunctor.finiteFreeModule` is crossed. -/
noncomputable def finiteFreeOf {m : ℕ} :
    (Fin m → A) →ₗ[A] (finiteFreeModule.{max v w} A m : Type (max u v w)) :=
  (ULift.moduleEquiv (R := A) (M := (Fin m → A))).symm.toLinearMap

/-- The section given by a tuple `x` is the combination of the sections given by the standard
basis vectors with coefficients `x i`. -/
lemma finiteFreeOf_eq_sum_basis {m : ℕ} (x : Fin m → A) :
    finiteFreeOf.{v, u, w} x = ∑ i, x i • finiteFreeOf.{v, u, w} (Pi.single i 1) := by
  conv_lhs => rw [pi_eq_sum_single x]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => map_smul _ _ _

/-- The coordinates of a morphism between the module-valued functors of finite free modules. -/
noncomputable def coords {m n : ℕ}
    (d : finiteFreeModule.{max v w} A m ⟶ finiteFreeModule.{max v w} A n) :
    (Fin m → A) →ₗ[A] (Fin n → A) :=
  ULift.moduleEquiv.toLinearMap ∘ₗ d.hom ∘ₗ ULift.moduleEquiv.symm.toLinearMap

/-- Two morphisms out of the module-valued functor of a finite free module agree as soon as
they agree on the sections given by tuples. -/
lemma finiteFree_hom_ext {M : ModuleCat.{max u v w} A} {m : ℕ}
    (a b : finiteFreeModule.{max v w} A m ⟶ M)
    (hab : ∀ t : Fin m → A,
      a.hom (finiteFreeOf.{v, u, w} t) = b.hom (finiteFreeOf.{v, u, w} t)) :
    a = b := by
  refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
  exact hab ((ULift.moduleEquiv (R := A) (M := (Fin m → A))) s)

/-- A morphism between the functors of finite free modules acts on the section given by a tuple
through its coordinates. -/
lemma hom_finiteFreeOf {m n : ℕ}
    (d : finiteFreeModule.{max v w} A m ⟶ finiteFreeModule.{max v w} A n) (x : Fin m → A) :
    d.hom (finiteFreeOf.{v, u, w} x) = finiteFreeOf.{v, u, w} (coords.{v, u, w} d x) := rfl

/-- The transpose of `d` sends the `j`-th standard basis vector to the `j`-th column of `d`. -/
lemma transposeLinearMap_single {m n : ℕ} (d : (Fin m → A) →ₗ[A] (Fin n → A)) (j : Fin n) :
    transposeLinearMap A d (Pi.single j 1) =
      ∑ i, d (Pi.single i 1) j • (Pi.single i 1 : Fin m → A) := by
  funext i
  have hl : transposeLinearMap A d (Pi.single j 1) i = d (Pi.single i 1) j := by
    simp [transposeLinearMap, LinearMap.pi_apply, LinearMap.sum_apply, Pi.single_apply]
  rw [hl, Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · simp

section Tensor

variable {Mod : Type z} [AddCommGroup Mod] [Module A Mod]

/-- Every element of `(Fin n → A) ⊗[A] Mod` is a combination of the standard basis vectors of
`Fin n → A` with coefficients in `Mod`. -/
lemma exists_basisTuple_tensor_eq {n : ℕ} (σ : TensorProduct A (Fin n → A) Mod) :
    ∃ z : Fin n → Mod, σ = ∑ j, (Pi.single j 1 : Fin n → A) ⊗ₜ[A] z j := by
  induction σ with
  | zero => exact ⟨0, by simp⟩
  | tmul a s =>
      refine ⟨fun j => a j • s, ?_⟩
      conv_lhs => rw [pi_eq_sum_single a]
      rw [TensorProduct.sum_tmul]
      exact Finset.sum_congr rfl fun j _ => TensorProduct.smul_tmul _ _ _
  | add x y hx hy =>
      obtain ⟨zx, hzx⟩ := hx
      obtain ⟨zy, hzy⟩ := hy
      refine ⟨zx + zy, ?_⟩
      rw [hzx, hzy, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => (TensorProduct.tmul_add _ _ _).symm

/-- The `i`-th coordinate of an element of `(Fin m → A) ⊗[A] Mod`. -/
noncomputable def tensorCoord {m : ℕ} (i : Fin m) :
    TensorProduct A (Fin m → A) Mod →ₗ[A] Mod :=
  (TensorProduct.lid A Mod).toLinearMap ∘ₗ (LinearMap.proj i).rTensor Mod

/-- The `i`-th coordinate of `a ⊗ₜ s` is `a i • s`. -/
@[simp] lemma tensorCoord_tmul {m : ℕ} (i : Fin m) (a : Fin m → A) (s : Mod) :
    tensorCoord i (a ⊗ₜ[A] s) = a i • s := rfl

/-- The `i`-th coordinate of `∑ j, Pi.single j 1 ⊗ₜ y j` is `y i`. -/
lemma tensorCoord_basisTuple {m : ℕ} (i : Fin m) (y : Fin m → Mod) :
    tensorCoord i (∑ j, (Pi.single j 1 : Fin m → A) ⊗ₜ[A] y j) = y i := by
  rw [map_sum, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [tensorCoord_tmul, Ne.symm hj]
  · simp

/-- **The algebraic content of the degree-one lifting problem.**  A tuple of module elements
whose combination with the classes of the standard basis vectors vanishes in the tensor
product with the cokernel of the transpose of `d` is a transpose image. -/
lemma exists_tuple_of_tensor_mkQ_eq_zero {m n : ℕ} (d : (Fin m → A) →ₗ[A] (Fin n → A))
    (y : Fin m → Mod)
    (h : ∑ i, (Submodule.mkQ (LinearMap.range (transposeLinearMap A d))
        (Pi.single i 1)) ⊗ₜ[A] y i = 0) :
    ∃ z : Fin n → Mod, ∀ i, y i = ∑ j, d (Pi.single i 1) j • z j := by
  classical
  set K := LinearMap.range (transposeLinearMap A d) with hK
  have hex : Function.Exact (transposeLinearMap A d) (Submodule.mkQ K) := by
    intro x
    simp [hK, Submodule.Quotient.mk_eq_zero]
  have hex' := rTensor_exact Mod hex (Submodule.mkQ_surjective K)
  set τ : TensorProduct A (Fin m → A) Mod :=
    ∑ i, (Pi.single i 1 : Fin m → A) ⊗ₜ[A] y i with hτ
  have hτ0 : (Submodule.mkQ K).rTensor Mod τ = 0 := by
    rw [hτ, map_sum]
    simpa using h
  obtain ⟨σ, hσ⟩ := (hex' τ).mp hτ0
  obtain ⟨z, hz⟩ := exists_basisTuple_tensor_eq σ
  refine ⟨z, fun i => ?_⟩
  have key : τ = ∑ i, (Pi.single i 1 : Fin m → A) ⊗ₜ[A] (∑ j, d (Pi.single i 1) j • z j) := by
    rw [← hσ, hz, map_sum]
    have step : ∀ j : Fin n,
        (transposeLinearMap A d).rTensor Mod ((Pi.single j 1 : Fin n → A) ⊗ₜ[A] z j) =
          ∑ i, (Pi.single i 1 : Fin m → A) ⊗ₜ[A] (d (Pi.single i 1) j • z j) := by
      intro j
      rw [LinearMap.rTensor_tmul, transposeLinearMap_single, TensorProduct.sum_tmul]
      exact Finset.sum_congr rfl fun i _ => TensorProduct.smul_tmul _ _ _
    rw [Finset.sum_congr rfl fun j _ => step j, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => (TensorProduct.tmul_sum _ _ _).symm
  calc y i = tensorCoord i τ := (tensorCoord_basisTuple i y).symm
    _ = _ := by rw [key, tensorCoord_basisTuple]

end Tensor

section SquareZero

variable {N : Type (max u v)} [AddCommGroup N] [Module A N]

/-- A module over a commutative ring carries the action of the opposite ring; this is what
lets the square-zero extension `A[N]` be formed as a commutative `A`-algebra. -/
local instance moduleOppositeOfComm : Module Aᵐᵒᵖ N :=
  Module.compHom _ ((RingHom.id A).fromOpposite mul_comm)

/-- The actions of `A` and `Aᵐᵒᵖ` on a module over the commutative ring `A` agree. -/
local instance isCentralScalarOfComm : IsCentralScalar A N := ⟨fun _ _ => rfl⟩

/-- A morphism out of the module-valued functor of a finite free module which kills every
section killed by `d̲` factors through `d`.

Both sides are tested on the universal section over the square-zero extension of `A` by the
cokernel of the transpose of `d`: that section lies in `ker d̲`, so the hypothesis says that
the tuple defining the morphism dies in the tensor product with that cokernel, which by
`AdequateFunctor.exists_tuple_of_tensor_mkQ_eq_zero` means it is a transpose image. -/
lemma exists_factor_of_vanishing_on_kernel {M : ModuleCat.{max u v w} A} {m n : ℕ}
    (d : finiteFreeModule.{max v w} A m ⟶ finiteFreeModule.{max v w} A n)
    (f : finiteFreeModule.{max v w} A m ⟶ M)
    (h : ∀ (X : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ)
        (x : ((moduleExtensionFunctor.{max u v w, v} A).obj
          (finiteFreeModule.{max v w} A m)).obj X),
        ((((moduleExtensionFunctor.{max u v w, v} A).map d).app X)) x = 0 →
        ((((moduleExtensionFunctor.{max u v w, v} A).map f).app X)) x = 0) :
    ∃ g : finiteFreeModule.{max v w} A n ⟶ M, d ≫ g = f := by
  classical
  set dd : (Fin m → A) →ₗ[A] (Fin n → A) := coords.{v, u, w} d with hdd
  set Nu := ULift.{v} (universalSolutionModule A dd) with hNu
  set B : CommAlgCat.{max u v} A := CommAlgCat.of A (TrivSqZeroExt A Nu) with hB
  set X₀ : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ := Opposite.op (Opposite.op B) with hX₀
  set upN : universalSolutionModule A dd →ₗ[A] Nu :=
    (ULift.moduleEquiv (R := A) (M := universalSolutionModule A dd)).symm.toLinearMap with hupN
  set e : Fin m → Nu := fun i =>
    upN (Submodule.mkQ (LinearMap.range (transposeLinearMap A dd)) (Pi.single i 1)) with he
  set ι : Nu →ₗ[A] (B : Type (max u v)) := TrivSqZeroExt.inrHom A Nu with hι
  set ξ : (((moduleExtensionFunctor.{max u v w, v} A).obj
      (finiteFreeModule.{max v w} A m)).obj X₀) :=
    ∑ i, ι (e i) ⊗ₜ[A] finiteFreeOf.{v, u, w} (Pi.single i 1) with hξ
  -- the universal section satisfies the relations imposed by `d`
  have hrel : ∀ j : Fin n, ∑ i, dd (Pi.single i 1) j • ι (e i) = 0 := by
    intro j
    have hsm : ∀ i : Fin m,
        dd (Pi.single i 1) j • ι (e i) = ι (dd (Pi.single i 1) j • e i) :=
      fun i => (map_smul _ _ _).symm
    have hz : ∑ i, dd (Pi.single i 1) j • e i = 0 := by
      have hup : ∑ i, dd (Pi.single i 1) j • e i =
          upN (Submodule.mkQ (LinearMap.range (transposeLinearMap A dd))
              (∑ i, dd (Pi.single i 1) j • (Pi.single i 1 : Fin m → A))) := by
        rw [map_sum, map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [he, map_smul, map_smul]
      rw [hup, ← transposeLinearMap_single, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ _), map_zero]
    rw [Finset.sum_congr rfl fun i _ => hsm i, ← map_sum, hz, map_zero]
  -- hence it is killed by `d̲`
  have hd0 : (((moduleExtensionFunctor.{max u v w, v} A).map d).app X₀).hom ξ = 0 := by
    have step : ∀ i : Fin m,
        (((moduleExtensionFunctor.{max u v w, v} A).map d).app X₀).hom
            (ι (e i) ⊗ₜ[A] finiteFreeOf.{v, u, w} (Pi.single i 1)) =
          ∑ j, (dd (Pi.single i 1) j • ι (e i)) ⊗ₜ[A]
            finiteFreeOf.{v, u, w} (Pi.single j 1) := by
      intro i
      rw [moduleExtensionFunctor_map_app_tmul, hom_finiteFreeOf, ← hdd,
        finiteFreeOf_eq_sum_basis (dd (Pi.single i 1)), TensorProduct.tmul_sum]
      exact Finset.sum_congr rfl fun j _ => by
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    rw [hξ, map_sum, Finset.sum_congr rfl fun i _ => step i, Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← TensorProduct.sum_tmul, hrel j, TensorProduct.zero_tmul]
  -- and therefore by `f̲`, which is the algebraic hypothesis of the core lemma
  set y : Fin m → (M : Type (max u v w)) :=
    fun i => f.hom (finiteFreeOf.{v, u, w} (Pi.single i 1)) with hy
  set ρ : (B : Type (max u v)) →ₗ[A] Nu := TrivSqZeroExt.sndHom A Nu with hρ
  set downN : Nu →ₗ[A] universalSolutionModule A dd :=
    (ULift.moduleEquiv (R := A) (M := universalSolutionModule A dd)).toLinearMap with hdownN
  have hcore : ∑ i, (Submodule.mkQ (LinearMap.range (transposeLinearMap A dd))
      (Pi.single i 1)) ⊗ₜ[A] y i = 0 := by
    have hval : (((moduleExtensionFunctor.{max u v w, v} A).map f).app X₀).hom ξ =
        ∑ i, ι (e i) ⊗ₜ[A] y i := by
      rw [hξ, map_sum]
      exact Finset.sum_congr rfl fun i _ => moduleExtensionFunctor_map_app_tmul _ _ _ _ _
    have h2 : ∑ i, ι (e i) ⊗ₜ[A] y i = 0 := by
      rw [← hval]
      exact h X₀ ξ hd0
    have hstep : ∀ i : Fin m,
        (downN.rTensor (M : Type (max u v w)))
            ((ρ.rTensor (M : Type (max u v w))) (ι (e i) ⊗ₜ[A] y i)) =
          (Submodule.mkQ (LinearMap.range (transposeLinearMap A dd))
            (Pi.single i 1)) ⊗ₜ[A] y i := by
      intro i
      rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
      congr 1
    calc ∑ i, (Submodule.mkQ (LinearMap.range (transposeLinearMap A dd))
            (Pi.single i 1)) ⊗ₜ[A] y i
        = ∑ i, (downN.rTensor (M : Type (max u v w)))
            ((ρ.rTensor (M : Type (max u v w))) (ι (e i) ⊗ₜ[A] y i)) :=
          Finset.sum_congr rfl fun i _ => (hstep i).symm
      _ = (downN.rTensor (M : Type (max u v w)))
            ((ρ.rTensor (M : Type (max u v w))) (∑ i, ι (e i) ⊗ₜ[A] y i)) := by
          rw [map_sum, map_sum]
      _ = 0 := by rw [h2, map_zero, map_zero]
  obtain ⟨z, hz⟩ := exists_tuple_of_tensor_mkQ_eq_zero dd y hcore
  have hyi : ∀ i, y i = f.hom (finiteFreeOf.{v, u, w} (Pi.single i 1)) := fun i => by rw [hy]
  have hleft : ∀ t : Fin m → A,
      (linearMapOfTuple A (M : Type (max u v w)) z) (dd t) = ∑ i, t i • y i := by
    intro t
    conv_lhs => rw [pi_eq_sum_single t]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, linearMapOfTuple_apply, ← hz i]
  have hright : ∀ t : Fin m → A,
      f.hom (finiteFreeOf.{v, u, w} t) = ∑ i, t i • y i := by
    intro t
    conv_lhs => rw [finiteFreeOf_eq_sum_basis t]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hyi i]
  refine ⟨ModuleCat.ofHom ((linearMapOfTuple A (M : Type (max u v w)) z) ∘ₗ
    (ULift.moduleEquiv (R := A) (M := (Fin n → A))).toLinearMap),
    finiteFree_hom_ext.{v, u, w} _ _ fun t => ?_⟩
  show (linearMapOfTuple A (M : Type (max u v w)) z)
      ((ULift.moduleEquiv (R := A) (M := (Fin n → A)))
        (d.hom (finiteFreeOf.{v, u, w} t))) = f.hom (finiteFreeOf.{v, u, w} t)
  rw [hright t, hom_finiteFreeOf, ← hdd]
  exact hleft t

end SquareZero

/-- The module map underlying the composite of the projection onto the image of `d̲` with a
morphism to the functor of a module. -/
noncomputable def imageFactorHom (M : ModuleCat.{max u v w} A) {m n : ℕ}
    (d : finiteFreeModule.{max v w} A m ⟶ finiteFreeModule.{max v w} A n)
    (φ : Abelian.image ((moduleExtensionFunctor.{max u v w, v} A).map d) ⟶
      moduleExtension.{max u v w, v} A M) :
    finiteFreeModule.{max v w} A m ⟶ M :=
  moduleHomOfExtensionNatTrans
    (Abelian.factorThruImage ((moduleExtensionFunctor.{max u v w, v} A).map d) ≫ φ)

/-- `imageFactorHom M d φ` is the module map underlying the composite of the projection onto the
image of the base change of `d` with `φ`. -/
lemma imageFactorHom_eq (M : ModuleCat.{max u v w} A) {m n : ℕ}
    (d : finiteFreeModule.{max v w} A m ⟶ finiteFreeModule.{max v w} A n)
    (φ : Abelian.image ((moduleExtensionFunctor.{max u v w, v} A).map d) ⟶
      moduleExtension.{max u v w, v} A M) :
    imageFactorHom.{v, u, w} M d φ = moduleHomOfExtensionNatTrans
      (Abelian.factorThruImage ((moduleExtensionFunctor.{max u v w, v} A).map d) ≫ φ) := rfl

/-- The base change of a map out of the target finite free module, *stated* as a morphism out
of the extension functor's value there. -/
noncomputable def imageLift (M : ModuleCat.{max u v w} A) {n : ℕ}
    (g : finiteFreeModule.{max v w} A n ⟶ M) :
    (moduleExtensionFunctor.{max u v w, v} A).obj (finiteFreeModule.{max v w} A n) ⟶
      moduleExtension.{max u v w, v} A M :=
  (moduleExtensionFunctor.{max u v w, v} A).map g

/-- `imageLift M g` is the base change of `g`. -/
lemma imageLift_eq (M : ModuleCat.{max u v w} A) {n : ℕ}
    (g : finiteFreeModule.{max v w} A n ⟶ M) :
    imageLift.{v, u, w} M g = (moduleExtensionFunctor.{max u v w, v} A).map g := rfl

/-- A section killed by `d̲` is killed by the projection onto the image of `d̲`: the image
inclusion is a monomorphism, hence injective on sections, and it undoes the projection. -/
lemma factorThruImage_app_eq_zero_of_app_eq_zero {m n : ℕ}
    (d : finiteFreeModule.{max v w} A m ⟶ finiteFreeModule.{max v w} A n)
    (X : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ)
    (x : ((moduleExtensionFunctor.{max u v w, v} A).obj
      (finiteFreeModule.{max v w} A m)).obj X)
    (hx : ((((moduleExtensionFunctor.{max u v w, v} A).map d).app X)) x = 0) :
    ((Abelian.factorThruImage ((moduleExtensionFunctor.{max u v w, v} A).map d)).app X) x
      = 0 := by
  have hinj : Function.Injective
      ((Abelian.image.ι ((moduleExtensionFunctor.{max u v w, v} A).map d)).app X) :=
    (ModuleCat.mono_iff_injective _).mp
      (inferInstanceAs (Mono ((PresheafOfModules.evaluation
        (algebraRingDiagram.{v} A) X).map
          (Abelian.image.ι ((moduleExtensionFunctor.{max u v w, v} A).map d)))))
  refine hinj ?_
  rw [map_zero]
  have hfac : ((Abelian.image.ι ((moduleExtensionFunctor.{max u v w, v} A).map d)).app X)
      (((Abelian.factorThruImage ((moduleExtensionFunctor.{max u v w, v} A).map d)).app X) x)
      = (((moduleExtensionFunctor.{max u v w, v} A).map d).app X) x := by
    conv_rhs => rw [← Abelian.image.fac ((moduleExtensionFunctor.{max u v w, v} A).map d)]
    rfl
  rw [hfac, hx]

/-- The morphism of `A`-modules underlying the composite of the projection onto the image of
`d̲` with a morphism to the functor of a module kills every section killed by `d̲`. -/
lemma map_moduleHom_app_eq_zero_of_app_eq_zero (M : ModuleCat.{max u v w} A) {m n : ℕ}
    (d : finiteFreeModule.{max v w} A m ⟶ finiteFreeModule.{max v w} A n)
    (φ : Abelian.image ((moduleExtensionFunctor.{max u v w, v} A).map d) ⟶
      moduleExtension.{max u v w, v} A M)
    (X : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ)
    (x : ((moduleExtensionFunctor.{max u v w, v} A).obj
      (finiteFreeModule.{max v w} A m)).obj X)
    (hx : ((((moduleExtensionFunctor.{max u v w, v} A).map d).app X)) x = 0) :
    ((((moduleExtensionFunctor.{max u v w, v} A).map
      (imageFactorHom.{v, u, w} M d φ)).app X)) x = 0 := by
  rw [imageFactorHom_eq, ← moduleExtension_natTrans_eq_map, PresheafOfModules.comp_app,
    ModuleCat.comp_apply, factorThruImage_app_eq_zero_of_app_eq_zero d X x hx, map_zero]

/-- A factorisation through `d` of the morphism underlying the composite with the projection
onto the image produces the required extension, because that projection is an
epimorphism. -/
lemma image_ι_comp_map_eq (M : ModuleCat.{max u v w} A) {m n : ℕ}
    (d : finiteFreeModule.{max v w} A m ⟶ finiteFreeModule.{max v w} A n)
    (φ : Abelian.image ((moduleExtensionFunctor.{max u v w, v} A).map d) ⟶
      moduleExtension.{max u v w, v} A M)
    (g : finiteFreeModule.{max v w} A n ⟶ M)
    (hg : d ≫ g = imageFactorHom.{v, u, w} M d φ) :
    Abelian.image.ι ((moduleExtensionFunctor.{max u v w, v} A).map d) ≫
      imageLift.{v, u, w} M g = φ := by
  refine (cancel_epi (Abelian.factorThruImage
    ((moduleExtensionFunctor.{max u v w, v} A).map d))).mp ?_
  rw [← Category.assoc, Abelian.image.fac, imageLift_eq, ← Functor.map_comp, hg,
    imageFactorHom_eq, ← moduleExtension_natTrans_eq_map]

/-- The morphism of `A`-modules underlying the composite of the projection onto the image of
`d̲` with a morphism to the functor of a module factors through `d`. -/
lemma exists_factor_moduleHom_comp_factorThruImage (M : ModuleCat.{max u v w} A) {m n : ℕ}
    (d : finiteFreeModule.{max v w} A m ⟶ finiteFreeModule.{max v w} A n)
    (φ : Abelian.image ((moduleExtensionFunctor.{max u v w, v} A).map d) ⟶
      moduleExtension.{max u v w, v} A M) :
    ∃ g : finiteFreeModule.{max v w} A n ⟶ M, d ≫ g = imageFactorHom.{v, u, w} M d φ :=
  exists_factor_of_vanishing_on_kernel d (imageFactorHom.{v, u, w} M d φ)
    (map_moduleHom_app_eq_zero_of_app_eq_zero M d φ)

end ImageLift

section Vanishing

variable (A : Type u) [CommRing A] (M P : ModuleCat.{max u v w} A)

/-- Degree one Ext out of the module-valued functor of a finitely presented module vanishes,
for Mathlib's natural-number-graded extension groups. -/
theorem subsingleton_ext_one_moduleExtension [Module.FinitePresentation A P]
    [HasExt.{t} (ModuleValuedFunctor.{max u v w, v} A)] :
    Subsingleton (Abelian.Ext.{t} (moduleExtension.{max u v w, v} A P)
      (moduleExtension.{max u v w, v} A M) 1) := by
  obtain ⟨n, m, d, p, hp, hdp⟩ := exists_finiteFree_presentation_large.{v} P
  refine subsingleton_ext_of_iso_left (presentationCokernelIso_large hp hdp) 1
    (subsingleton_ext_one_cokernel ((moduleExtensionFunctor.{max u v w, v} A).map d)
      (projective_moduleExtension (finiteFreeModule.{max v w} A n)) _ ?_)
  intro φ
  obtain ⟨g, hg⟩ := exists_factor_moduleHom_comp_factorThruImage M d φ
  exact ⟨imageLift.{v, u, w} M g, image_ι_comp_map_eq M d φ g hg⟩

/-- Degree two Ext out of the module-valued functor of a finitely presented module vanishes,
for Mathlib's natural-number-graded extension groups. -/
theorem subsingleton_ext_two_moduleExtension_large [Module.FinitePresentation A P]
    [HasExt.{t} (ModuleValuedFunctor.{max u v w, v} A)] :
    Subsingleton (Abelian.Ext.{t} (moduleExtension.{max u v w, v} A P)
      (moduleExtension.{max u v w, v} A M) 2) := by
  obtain ⟨n, m, d, p, hp, hdp⟩ := exists_finiteFree_presentation_large.{v} P
  refine subsingleton_ext_of_iso_left (presentationCokernelIso_large hp hdp) 2
    (subsingleton_ext_two_cokernel ((moduleExtensionFunctor.{max u v w, v} A).map d)
      (projective_moduleExtension (finiteFreeModule.{max v w} A n)) _
      (subsingleton_ext_one_image ((moduleExtensionFunctor.{max u v w, v} A).map d)
        (projective_moduleExtension (finiteFreeModule.{max v w} A m)) _
        (exists_lift_from_kernel_moduleExtension_large M d)))

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks Project, Tag 06ZG in degree one.**  For an `A`-module `P` of finite
presentation, `Ext¹` from the module-valued functor `B ↦ B ⊗[A] P` to `B ↦ B ⊗[A] M` vanishes
in the category of module-valued functors on the commutative `A`-algebras. -/
@[stacks 06ZG "degree 1, via the universal section over the square-zero extension by the \
cokernel of the transpose of a presentation"]
theorem subsingleton_zExt_moduleExtension_one [Module.FinitePresentation A P] :
    Subsingleton (Abelian.zExt (moduleExtension.{max u v w, v} A P)
      (moduleExtension.{max u v w, v} A M) 1) := by
  let _ : HasExt.{max (u + 1) (v + 1) (w + 1)} (ModuleValuedFunctor.{max u v w, v} A) :=
    HasExt.standard (ModuleValuedFunctor.{max u v w, v} A)
  exact subsingleton_zExt_of_subsingleton_ext (n := 1) (subsingleton_ext_one_moduleExtension A M P)

/-- **Stacks Project, Tag 06ZG in degree two.**  For an `A`-module `P` of finite presentation,
`Ext²` from the module-valued functor `B ↦ B ⊗[A] P` to `B ↦ B ⊗[A] M` vanishes in the
category of module-valued functors on the commutative `A`-algebras. -/
@[stacks 06ZG "degree 2, via Tag 06V0 and projectivity of the free module functors"]
theorem subsingleton_zExt_moduleExtension_two_large [Module.FinitePresentation A P] :
    Subsingleton (Abelian.zExt (moduleExtension.{max u v w, v} A P)
      (moduleExtension.{max u v w, v} A M) 2) := by
  let _ : HasExt.{max (u + 1) (v + 1) (w + 1)} (ModuleValuedFunctor.{max u v w, v} A) :=
    HasExt.standard (ModuleValuedFunctor.{max u v w, v} A)
  exact subsingleton_zExt_of_subsingleton_ext (n := 2)
    (subsingleton_ext_two_moduleExtension_large A M P)

end Vanishing

section VanishingBase

variable (A : Type u) [CommRing A] (M P : ModuleCat.{max u v} A)

attribute [local instance] HasDerivedCategory.standard

/-- Degree two Ext out of the module-valued functor of a finitely presented module vanishes,
for Mathlib's natural-number-graded extension groups. -/
theorem subsingleton_ext_two_moduleExtension [Module.FinitePresentation A P]
    [HasExt.{t} (ModuleValuedFunctor.{max u v, v} A)] :
    Subsingleton (Abelian.Ext.{t} (moduleExtension.{max u v, v} A P)
      (moduleExtension.{max u v, v} A M) 2) :=
  subsingleton_ext_two_moduleExtension_large.{t, v, u, v} A M P

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks Project, Tag 06ZG in degree two.**  For an `A`-module `P` of finite presentation,
`Ext²` from the module-valued functor `B ↦ B ⊗[A] P` to `B ↦ B ⊗[A] M` vanishes in the
category of module-valued functors on the commutative `A`-algebras. -/
@[stacks 06ZG "degree 2, via Tag 06V0 and projectivity of the free module functors"]
theorem subsingleton_zExt_moduleExtension_two [Module.FinitePresentation A P] :
    Subsingleton (Abelian.zExt (moduleExtension.{max u v, v} A P)
      (moduleExtension.{max u v, v} A M) 2) := by
  let _ : HasExt.{max (u + 1) (v + 1)} (ModuleValuedFunctor.{max u v, v} A) :=
    HasExt.standard (ModuleValuedFunctor.{max u v, v} A)
  exact subsingleton_zExt_of_subsingleton_ext (n := 2) (subsingleton_ext_two_moduleExtension A M P)

end VanishingBase

end AdequateFunctor

end
