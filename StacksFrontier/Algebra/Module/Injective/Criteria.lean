module

public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.Algebra.Category.ModuleCat.Ext.Baer
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Module.Injective
public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Linear.Yoneda
public import StacksCore.Tactic.StacksAttribute

/-!
# Criteria for injectivity

Injectivity of a module `J` over a commutative ring `R` admits three successively cheaper
tests, all recorded here:

* exactness of the contravariant Hom functor `Hom_R(-, J)` — this is the definition;
* vanishing of `Ext¹(M, J)` for every module `M`;
* vanishing of `Ext¹(R/I, J)` for every ideal `I`, equivalently the extension to `R` of every
  linear map out of an ideal, which is Baer's criterion.

Mathlib has the second test only for an object of an arbitrary abelian category carrying an `Ext`
theory, so the module-level form, quantified over `R`-modules, is proved here from it; the
abelian-category form is registered under the same tag. The third test is Mathlib's and this file
only records its tags.

Over `R = ℤ`, that is for abelian groups, the third test reads as divisibility: extending a map
out of the ideal `nℤ` to all of `ℤ` is dividing an element by `n`. That specialisation is proved
here too.

## Main results

* `Module.injective_iff_exact_linearYoneda`: injectivity is equivalent to exactness of
  `Hom_R(-, J)`.
* `Module.injective_iff_subsingleton_ext_one`: injectivity is equivalent to the vanishing of
  `Ext¹_R(M, J)` for every `R`-module `M`.
* `AddCommGrpCat.injective_iff_divisible`: an abelian group is an injective object of the
  category of abelian groups if and only if it is divisible.

## Implementation notes

`Hom_R(-, J)` is presented as a functor out of the opposite category of modules, namely the
linear Yoneda functor at `J`; since rings are commutative here it takes values in modules over
the same ring. Exactness is `CategoryTheory.exactFunctor`, i.e. preservation of finite limits
and finite colimits. Vanishing of an `Ext` group is expressed by its being a subsingleton.

Divisibility of an abelian group is Mathlib's `DivisibleBy _ ℕ`, a structure rather than a
proposition, so the criterion asserts that it is inhabited.

## References

* [Stacks Project, Tag 01D7](https://stacks.math.columbia.edu/tag/01D7)
* [Stacks Project, Tag 0AVD](https://stacks.math.columbia.edu/tag/0AVD)
* [Stacks Project, Tag 0AVE](https://stacks.math.columbia.edu/tag/0AVE)
* [Stacks Project, Tag 0AVF](https://stacks.math.columbia.edu/tag/0AVF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

/-- **Stacks 0AVD.** An `R`-module `J` is injective if and only if its contravariant Hom
functor `Hom_R(-, J)` is exact.

Exactness of a functor out of `(ModuleCat R)ᵒᵖ` is tested after composing with the forgetful
functor to abelian groups, where the composite is the preadditive Yoneda functor at `J`, for
which Mathlib already characterises injectivity. -/
@[stacks 0AVD]
theorem Module.injective_iff_exact_linearYoneda (R : Type u) [CommRing R]
    (J : Type v) [AddCommGroup J] [Module R J] :
    Module.Injective R J ↔
      exactFunctor _ _ ((linearYoneda R (ModuleCat.{v} R)).obj (ModuleCat.of R J)) := by
  let F := (linearYoneda R (ModuleCat.{v} R)).obj (ModuleCat.of R J)
  let U := forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}
  have hF : F ⋙ U = preadditiveYoneda.obj (ModuleCat.of R J) :=
    congrArg (fun G => G.obj (ModuleCat.of R J))
      (whiskering_linearYoneda₂ R (ModuleCat.{v} R))
  rw [Module.injective_iff_injective_object]
  constructor
  · intro h
    have hcompEpi : (F ⋙ U).PreservesEpimorphisms := by
      rw [hF]
      exact (Injective.injective_iff_preservesEpimorphisms_preadditiveYoneda_obj _).mp h
    have hEpi : F.PreservesEpimorphisms :=
      Functor.preservesEpimorphisms_of_preserves_of_reflects F U
    have hcompLim : PreservesFiniteLimits (F ⋙ U) := by
      rw [hF]
      infer_instance
    have hLim : PreservesFiniteLimits F :=
      preservesFiniteLimits_of_reflects_of_preserves F U
    have hHomology : F.PreservesHomology :=
      Functor.preservesHomology_of_preservesEpis_and_kernels F
    exact ⟨hLim, Functor.preservesFiniteColimits_of_preservesHomology F⟩
  · intro h
    have hcol : PreservesFiniteColimits F := h.2
    have hEpi : F.PreservesEpimorphisms := inferInstance
    have hcompEpi : (F ⋙ U).PreservesEpimorphisms := inferInstance
    refine (Injective.injective_iff_preservesEpimorphisms_preadditiveYoneda_obj _).mpr ?_
    rw [← hF]
    exact hcompEpi

/-- **Stacks 01D7.** An abelian group is an injective object in the category of abelian groups
if and only if it is divisible.

Divisibility is Baer's criterion over `ℤ`: an injective group is Baer, and dividing `x` by `n`
is extending to `ℤ` the map `nℤ → J` determined by `n ↦ x`. Conversely a divisible group is
injective, which is Mathlib's `AddCommGrpCat.injective_of_divisible`. -/
@[stacks 01D7]
theorem AddCommGrpCat.injective_iff_divisible (J : Type u) [AddCommGroup J] :
    Injective (C := AddCommGrpCat) (AddCommGrpCat.of J) ↔ Nonempty (DivisibleBy J ℕ) := by
  constructor
  · intro h
    have _ : Injective (ModuleCat.of ℤ J) :=
      (AddCommGrpCat.injective_as_module_iff J).mpr h
    have _ : Module.Injective ℤ J :=
      Module.injective_module_of_injective_object ℤ J
    have hbaer : Module.Baer ℤ J := Module.Baer.of_injective inferInstance
    let _ : DivisibleBy J ℤ := divisibleByOfSMulRightSurj J ℤ fun {n} hn x ↦ by
      let I : Ideal ℤ := Ideal.span {n}
      let e : ℤ ≃ₗ[ℤ] I := LinearEquiv.toSpanNonzeroSingleton ℤ ℤ n hn
      let f : I →ₗ[ℤ] J := (LinearMap.toSpanSingleton ℤ J x) ∘ₗ e.symm
      obtain ⟨g, hg⟩ := hbaer I f
      refine ⟨g 1, ?_⟩
      have hnI : n ∈ I := Ideal.mem_span_singleton_self n
      have he : e.symm ⟨n, hnI⟩ = 1 := by
        apply mul_right_cancel₀ hn
        simpa [e] using
          (LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul ℤ ℤ n hn ⟨n, hnI⟩)
      calc
        n • g 1 = g (n • 1) := (map_zsmul g n 1).symm
        _ = g n := by simp
        _ = f ⟨n, hnI⟩ := hg n hnI
        _ = x := by simp [f, he, LinearMap.toSpanSingleton_apply]
    exact ⟨AddGroup.divisibleByNatOfDivisibleByInt J⟩
  · rintro ⟨h⟩
    let _ : DivisibleBy J ℤ := AddGroup.divisibleByIntOfDivisibleByNat J
    exact AddCommGrpCat.injective_of_divisible J

/-- **Stacks 0AVE.** An `R`-module `J` is injective if and only if `Ext¹_R(M, J)` vanishes for
every `R`-module `M`.

Mathlib's `CategoryTheory.injective_iff_subsingleton_ext_one` is this criterion for an object of
an abelian category with an `Ext` theory; here it is read off for modules, the quantifier running
over `R`-modules rather than over objects of `ModuleCat R`. The two agree because every object of
`ModuleCat.{v} R` is `ModuleCat.of R` of its own carrier. -/
@[stacks 0AVE]
theorem Module.injective_iff_subsingleton_ext_one (R : Type u) [Ring R] [Small.{v} R]
    (J : Type v) [AddCommGroup J] [Module R J] :
    Module.Injective R J ↔
      ∀ (M : Type v) [AddCommGroup M] [Module R M],
        Subsingleton (Abelian.Ext (ModuleCat.of R M) (ModuleCat.of R J) 1) := by
  rw [Module.injective_iff_injective_object, CategoryTheory.injective_iff_subsingleton_ext_one]
  constructor
  · intro h M _ _
    exact h (Y := ModuleCat.of R M)
  · intro h Y
    have := h Y
    rwa [ModuleCat.of_coe] at this

/-! ### Registrations of Mathlib's remaining criteria -/

add_to_stacks 0AVE CategoryTheory.injective_iff_subsingleton_ext_one
add_to_sga "6 I 5.7" "(ii) ⇒ (i)" CategoryTheory.injective_iff_subsingleton_ext_one

add_to_stacks 0AVF "injectivity is equivalent to vanishing Ext^1 from quotients by ideals"
  ModuleCat.injective_iff_subsingleton_ext_quotient_one

add_to_stacks 0AVF "vanishing Ext^1 is equivalent to extending maps from ideals"
  ModuleCat.ext_quotient_one_subsingleton_iff

end
