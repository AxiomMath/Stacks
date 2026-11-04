module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Module.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Module.Adequate.Defs
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.ModuleFunctorAtBase

/-!
# Higher exts of linearly adequate functors

Let `A` be a commutative ring, let `M` be an `A`-module and let `L` be a linearly adequate
module-valued functor on the commutative `A`-algebras. Then the extension groups
`Ext^i(L, M̲)` vanish in positive degrees, where `M̲` is the module-valued functor
`B ↦ B ⊗[A] M` and the extension groups are taken in the category of module-valued functors.

The proof analyses the presentation of a linearly adequate functor: `L` is the kernel of a map
`f̲ : A^{⊕n}̲ → A^{⊕m}̲` of module-valued functors coming from a map `f` of finite free
`A`-modules, and the two long exact sequences attached to `0 → L → A^{⊕n}̲ → K → 0` and
`0 → K → A^{⊕m}̲ → coker(f)̲ → 0` reduce the vanishing to the same vanishing for the
module-valued functors of `A^{⊕n}`, `A^{⊕m}` and `coker f`. The functor of a finite free
module is a projective object, so the first two reductions are unconditional and only
`coker f`, which is of finite presentation, is left.

## Main results

* `AdequateFunctor.subsingleton_zExt_of_isLinearlyAdequate`: positive-degree extension groups
  from a linearly adequate functor to the functor of a module vanish.

## Implementation notes

Vanishing of an extension group is expressed by its underlying type being a subsingleton.

## The one fact this tag is still missing

The hypothesis `hM` of the theorem below is the positive-degree vanishing for the functor of a
finitely presented module, Tag 06ZG. Stated at the universes the consumers use, with the
module universe a free parameter independent of the algebra carriers, it reads:

    theorem subsingleton_zExt_moduleExtension_of_finitePresentation
        {A : Type u} [CommRing A] (M P : ModuleCat.{max u v w} A)
        [Module.FinitePresentation A P] (j : ℤ) (hj : 0 < j) :
        Subsingleton (Abelian.zExt (moduleExtension.{max u v w, v} A P)
          (moduleExtension.{max u v w, v} A M) j)

That statement is not available in this library, in two respects at once.

* Degree. Only `j = 2` is proved, by
  `AdequateFunctor.subsingleton_zExt_moduleExtension_two`. This proof needs `j ≥ 3`; it does
  not need `j = 1`, which is the degree that proof records as out of reach.
* Universe. The degree-two statement pins the module universe to the algebra universe,
  so it has no free `w`, and the consumers apply this tag at a strictly larger module
  universe: `AdequateFunctor.rightAcyclic_moduleExtension` instantiates it at
  `max (u + 1) (v + 1) w`. The two shapes agree only when `w ≤ max u v`. No bridge closes the
  gap, because the target `M` is an arbitrary module of the larger universe rather than a
  small one.

The degrees that are missing are not a weaker fact than this tag. For `f` a map of finite free
`A`-modules, `L = ker f̲` and `P = coker f`, the two short exact sequences used in the proof
below are flanked by projective objects, so the degree shift along them is an isomorphism
`Ext^i(L, M̲) ≅ Ext^{i + 2}(P̲, M̲)` for `i ≥ 1`. Hence Tag 06ZG in degrees `≥ 3` and this tag
in degrees `≥ 1` have the same content, and neither can be obtained from the other half of the
section. The same identification is recorded from the other side in the module documentation
of `StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.ModuleFunctorAtBase`.

The source's route to Tag 06ZG is closed in this library. It derives Tag 06ZG from property
`(*)` for the injective objects of an injective resolution of `M̲`, which is the
middle-exactness conjunct of Tag 06ZA, and that conjunct is false:
`AdequateFunctor.not_forall_hasRightExactTangentFunctor_of_injective` refutes it, with the
module-valued functor coinduced from `ℚ[ε]` as the witness. Tag 06ZA survives as an
erratum with its surjectivity conjunct only,
`AdequateFunctor.epi_tangentFunctorAt_map_of_injective`, and that half does not suffice.

## References

* [Stacks Project, Tag 06ZH](https://stacks.math.columbia.edu/tag/06ZH)
* [Stacks Project, Tag 06ZG](https://stacks.math.columbia.edu/tag/06ZG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w c d

namespace AdequateFunctor

attribute [local instance] HasDerivedCategory.standard

/-- Vanishing of `Ext^n` in the `ℕ`-indexed sense is equivalent to that of `zExt` in degree `n`. -/
private lemma subsingleton_zExt_iff_ext
    {C : Type c} [Category.{d} C] [Abelian C] [HasDerivedCategory.{max c d} C]
    [HasExt.{max c d} C] (X Y : C) (n : ℕ) (i : ℤ) (hn : (n : ℤ) = i) :
    Subsingleton (Abelian.zExt X Y i) ↔ Subsingleton (Abelian.Ext.{max c d} X Y n) := by
  subst hn
  exact (Abelian.Ext.homEquiv.{max c d, max c d} (X := X) (Y := Y) (n := n)).subsingleton_congr.symm

/-- Vanishing of `Ext^i(X₂, Y)` and of `Ext^{i+1}(X₃, Y)` forces `Ext^i(X₁, Y)` to vanish,
for a short exact sequence `0 → X₁ → X₂ → X₃ → 0` and `i ≥ 0`. -/
private lemma subsingleton_zExt_of_shortExact
    {C : Type c} [Category.{d} C] [Abelian C] [HasDerivedCategory.{max c d} C]
    {S : ShortComplex C} (hS : S.ShortExact) (Y : C) (i : ℤ) (hi : 0 ≤ i)
    (hX₂ : Subsingleton (Abelian.zExt S.X₂ Y i))
    (hX₃ : Subsingleton (Abelian.zExt S.X₃ Y (i + 1))) :
    Subsingleton (Abelian.zExt S.X₁ Y i) := by
  let n := i.toNat
  have hn : (n : ℤ) = i := Int.toNat_of_nonneg hi
  let _ : HasExt.{max c d} C := HasExt.standard C
  have hX₂' := (subsingleton_zExt_iff_ext S.X₂ Y n i hn).mp hX₂
  have hX₃' := (subsingleton_zExt_iff_ext S.X₃ Y (n + 1) (i + 1) (by omega)).mp hX₃
  refine (subsingleton_zExt_iff_ext S.X₁ Y n i hn).mpr ?_
  refine subsingleton_of_forall_eq 0 fun a => ?_
  obtain ⟨x, hx⟩ := Abelian.Ext.contravariant_sequence_exact₁
    (hS := hS) (Y := Y) (x₁ := a) (n₀ := n) (n₁ := n + 1) (hn₁ := by omega)
    (hx₁ := Subsingleton.elim _ _)
  rw [Subsingleton.elim x 0] at hx
  simpa using hx.symm

/-- Extension groups out of isomorphic objects vanish together. -/
private lemma subsingleton_zExt_of_iso
    {C : Type c} [Category.{d} C] [Abelian C] [HasDerivedCategory.{max c d} C]
    {X Y Z : C} (e : X ≅ Y) (i : ℤ)
    (hY : Subsingleton (Abelian.zExt Y Z i)) :
    Subsingleton (Abelian.zExt X Z i) :=
  (Iso.homCongr ((DerivedCategory.singleFunctor C 0).mapIso e)
    (Iso.refl _)).subsingleton_congr.mpr hY

/-- Positive-degree extension groups out of a projective object vanish. -/
private lemma subsingleton_zExt_of_projective
    {C : Type c} [Category.{d} C] [Abelian C] [HasDerivedCategory.{max c d} C]
    (X Y : C) [Projective X] (i : ℤ) (hi : 0 < i) :
    Subsingleton (Abelian.zExt X Y i) := by
  let n := (i - 1).toNat
  let _ : HasExt.{max c d} C := HasExt.standard C
  exact (subsingleton_zExt_iff_ext X Y (n + 1) i (by omega)).mpr
    (Abelian.Ext.subsingleton_of_projective X Y n)

/-- Vanishing of `Ext^i(X, Z)`, `Ext^{i+1}(Y, Z)` and `Ext^{i+2}(coker f, Z)` forces
`Ext^i(ker f, Z)` to vanish, for a morphism `f : X ⟶ Y` and `i ≥ 0`. -/
private lemma subsingleton_zExt_kernel
    {C : Type c} [Category.{d} C] [Abelian C] [HasDerivedCategory.{max c d} C]
    {X Y Z : C} (f : X ⟶ Y) (i : ℤ) (hi : 0 ≤ i)
    (hX : Subsingleton (Abelian.zExt X Z i))
    (hY : Subsingleton (Abelian.zExt Y Z (i + 1)))
    (hcoker : Subsingleton (Abelian.zExt (cokernel f) Z (i + 2))) :
    Subsingleton (Abelian.zExt (kernel f) Z i) := by
  have hS₁ : (ShortComplex.mk (Abelian.image.ι f) (cokernel.π f) (by simp)).ShortExact :=
    ⟨(ShortComplex.exact_iff_exact_image_ι _).mp (ShortComplex.exact_cokernel f)⟩
  have himage : Subsingleton (Abelian.zExt (Abelian.image f) Z (i + 1)) :=
    subsingleton_zExt_of_shortExact hS₁ Z (i + 1) (by omega) hY
      (by simpa only [show i + 1 + 1 = i + 2 from by ring] using hcoker)
  have hcoimage : Subsingleton (Abelian.zExt (Abelian.coimage f) Z (i + 1)) :=
    subsingleton_zExt_of_iso (Abelian.coimageIsoImage f) (i + 1) himage
  have hS₂ : (ShortComplex.mk (kernel.ι f) (cokernel.π (kernel.ι f)) (by simp)).ShortExact :=
    ⟨ShortComplex.exact_cokernel (kernel.ι f)⟩
  exact subsingleton_zExt_of_shortExact hS₂ Z i hi hX hcoimage

/-- The module-valued functor of a finite free module is a projective object, so the extension
groups out of it vanish in positive degrees. -/
private lemma subsingleton_zExt_moduleExtension_finiteFreeModule {A : Type u} [CommRing A]
    (k : ℕ) (Z : ModuleValuedFunctor.{max u v w, v} A) (i : ℤ) (hi : 0 < i) :
    Subsingleton (Abelian.zExt
      (moduleExtension.{max u v w, v} A (finiteFreeModule.{max u v w} A k)) Z i) := by
  have : Module.Projective A (finiteFreeModule.{max u v w} A k) := by
    dsimp [finiteFreeModule]
    exact Module.Projective.of_equiv
      (ULift.moduleEquiv.symm : (Fin k → A) ≃ₗ[A] ULift.{max u v w, u} (Fin k → A))
  exact subsingleton_zExt_of_projective _ _ i hi

/-- Let `A` be a commutative ring, `M` an `A`-module and `L` a linearly adequate module-valued
functor on the commutative `A`-algebras. Then `Ext^i(L, M̲)` vanishes for `i > 0`, where `M̲`
is the module-valued functor `B ↦ B ⊗[A] M`. -/
@[stacks 06ZH "The positive-degree vanishing for the functor of a finitely presented module, \
Tag 06ZG, is a hypothesis. Only its degree-two case is proved in this library, in \
`AdequateFunctor.subsingleton_zExt_moduleExtension_two`, while this proof needs degrees at \
least three: both short exact sequences used here are flanked by projective objects, so the \
degree shift along them is an isomorphism and those degrees of Tag 06ZG carry the content of \
this tag itself. The source derives Tag 06ZG from Tag 06ZA, which is false as \
stated and is refuted by \
`AdequateFunctor.not_forall_hasRightExactTangentFunctor_of_injective`."]
public theorem subsingleton_zExt_of_isLinearlyAdequate {A : Type u} [CommRing A]
    (L : ModuleValuedFunctor.{max u v w, v} A) (hL : IsLinearlyAdequate (𝟭 _) L)
    (M : ModuleCat.{max u v w} A)
    (hM : ∀ P : ModuleCat.{max u v w} A, Module.FinitePresentation A P → ∀ j : ℤ, 0 < j →
      Subsingleton (Abelian.zExt (moduleExtension.{max u v w, v} A P)
        (moduleExtension.{max u v w, v} A M) j))
    (i : ℤ) (hi : 0 < i) :
    Subsingleton (Abelian.zExt L (moduleExtension.{max u v w, v} A M) i) := by
  obtain ⟨n, m, f, hf⟩ := (isLinearlyAdequate_iff_exists_module_map L).mp hL
  obtain ⟨e⟩ := (isKernelPresentation_iff L f).mp hf
  have freeFP : ∀ k : ℕ, Module.FinitePresentation A (finiteFreeModule.{max u v w} A k) := by
    intro k
    dsimp [finiteFreeModule]
    exact Module.FinitePresentation.of_equiv
      (ULift.moduleEquiv.symm : (Fin k → A) ≃ₗ[A] ULift.{max u v w, u} (Fin k → A))
  have hcoker : Module.FinitePresentation A (cokernel f : ModuleCat.{max u v w} A) := by
    refine Module.finitePresentation_of_surjective (h := freeFP m) (cokernel.π f).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance) ?_
    rw [← (ShortComplex.exact_cokernel f).moduleCat_range_eq_ker]
    exact Submodule.fg_range f.hom
  exact subsingleton_zExt_of_iso e i (subsingleton_zExt_kernel
    ((moduleExtensionFunctor.{max u v w, v} A).map f) i hi.le
    (subsingleton_zExt_moduleExtension_finiteFreeModule n _ i hi)
    (subsingleton_zExt_moduleExtension_finiteFreeModule m _ (i + 1) (by omega))
    (subsingleton_zExt_of_iso (moduleExtensionCokernelIso.{max u v w, v, u} f).symm (i + 2)
      (hM _ hcoker (i + 2) (by omega))))

end AdequateFunctor

end
