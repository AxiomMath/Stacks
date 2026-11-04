module

public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.Stalks
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.AssociatedPointsCompat
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Reduced
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionAssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleStalk
public import StacksFrontier.RingTheory.Dualizing.ResidueFieldShift

/-!
# A surjection of the structure sheaf onto a dualizing module is an isomorphism

Let `X` be an integral locally Noetherian scheme and let `ω` be a dualizing module on `X`
([Stacks, Tag 0B4R]). This file proves that **every epimorphism `𝒪_X ⟶ ω` is an isomorphism**.

## Main results

* `Stacks.Duality.injective_of_surjective_of_nontrivial`: a surjective linear map out of a field
  onto a nontrivial module over it is injective.
* `Stacks.Duality.eq_genericPoint_of_isAssociatedPoint_structureModule`: an associated point of
  the structure sheaf of an integral locally Noetherian scheme is the generic point.
* `Stacks.Duality.nontrivial_stalk_of_isDualizingModule_of_isField`: the stalk of a dualizing
  module is nontrivial at a point whose local ring is a field.
* `Stacks.Duality.isIso_of_epi_structureModule_to_dualizingModule`: **the result**.

## The argument

By [Stacks, Tag 0AVL] (`Stacks.Divisors.mono_of_stalk_injective_on_associatedPoints`) a morphism
of quasi-coherent modules on a locally Noetherian scheme is a monomorphism as soon as it is
injective on the stalk at every associated point of its source, and the only associated point of
the structure sheaf of an integral scheme is the generic point: the weakly associated points of a
reduced scheme are the generic points of the irreducible components by [Stacks, Tag 0EME], an
associated point is a weakly associated point by [Stacks, Tag 05AM], and an irreducible sober
`T₀` space has exactly one generic point.

At the generic point the local ring is the function field, so the stalk of the morphism is a
surjective — the morphism being an epimorphism — linear map out of a field. The stalk of `ω`
there is nontrivial: the stalk of a dualizing module, placed in degree zero, is a dualizing
complex over the local ring (`Stacks.Duality.isDualizingComplex_single_stalk`), a dualizing
complex over a field is a simple object (`Dualizing.simple_of_isDualizingComplex_field`), and a
simple object is not a zero object. A surjective linear map out of a field onto a nontrivial
module is injective, because it is multiplication by its nonzero value at `1`.

So the morphism is a monomorphism as well as an epimorphism, hence an isomorphism.

## References

* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 0AVL](https://stacks.math.columbia.edu/tag/0AVL)
* [Stacks Project, Tag 0EME](https://stacks.math.columbia.edu/tag/0EME)
* [Stacks Project, Tag 05AM](https://stacks.math.columbia.edu/tag/05AM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Duality

/-- **A surjective linear map out of a field onto a nontrivial module is injective.** The map is
multiplication by its value at `1`, which is nonzero because the module is nontrivial and the
map is onto, and a field acts on a module without zero divisors. -/
theorem injective_of_surjective_of_nontrivial {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Nontrivial V] (φ : K →ₗ[K] V) (hsurj : Function.Surjective φ) :
    Function.Injective φ := by
  have h1 : φ 1 ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨a, ha⟩ := hsurj v
    refine hv ?_
    rw [← ha, show a = a • (1 : K) from (mul_one a).symm, map_smul, h, smul_zero]
  refine (injective_iff_map_eq_zero φ).2 fun a ha => ?_
  have hz : a • φ 1 = 0 := by
    rw [← map_smul, show a • (1 : K) = a from mul_one a, ha]
  exact (smul_eq_zero.1 hz).resolve_right h1

/-- **An associated point of the structure sheaf of an integral locally Noetherian scheme is the
generic point.** An associated point is a weakly associated point ([Stacks, Tag 05AM]), the
weakly associated points of a reduced scheme are the generic points of its irreducible
components ([Stacks, Tag 0EME]), and an irreducible scheme has exactly one generic point. -/
theorem eq_genericPoint_of_isAssociatedPoint_structureModule {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsIntegral X] {x : X}
    (hx : Stacks.Divisors.IsAssociatedPoint (Stacks.Divisors.structureModule X) x) :
    x = genericPoint (X : Type u) := by
  have hmem : x ∈ Stacks.Divisors.schemeWeaklyAssociatedPoints X :=
    (Stacks.Divisors.mem_schemeWeaklyAssociatedPoints_iff X x).2
      (associatedPoints_subset_weaklyAssociatedPoints _ hx)
  rw [weaklyAssociatedPointsOfScheme_eq_genericPoints X, genericPoints_eq_singleton] at hmem
  exact hmem

/-- **The stalk of a dualizing module at a point whose local ring is a field is nontrivial.**
The stalk of a dualizing module, placed in degree zero, is a dualizing complex over the local
ring; over a field a dualizing complex is a simple object, hence not a zero object, and the
degree-zero single complex of a subsingleton module is a zero object. -/
theorem nontrivial_stalk_of_isDualizingModule_of_isField {X : Scheme.{u}}
    [IsLocallyNoetherian X] (ω : X.Modules) [ω.IsQuasicoherent] (n : ℤ)
    (hω : letI := HasDerivedCategory.standard X.Modules
      IsDualizingComplex ((DerivedCategory.singleFunctor X.Modules n).obj ω))
    {x : X} (hx : IsField (X.presheaf.stalk x)) :
    letI := Stacks.ModuleStalkSpecialization.stalkModule ω x
    Nontrivial (ω.presheaf.stalk x) := by
  let := HasDerivedCategory.standard X.Modules
  let := Stacks.ModuleStalkSpecialization.stalkModule ω x
  let := HasDerivedCategory.standard (ModuleCat.{u} (X.presheaf.stalk x))
  let : Field (X.presheaf.stalk x) := hx.toField
  have hdual := isDualizingComplex_single_stalk ω n hω x
  let K := (DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj
    (ModuleCat.of (X.presheaf.stalk x) (ω.presheaf.stalk x))
  have : CategoryTheory.Simple K := Dualizing.simple_of_isDualizingComplex_field _ hdual
  by_contra hcon
  refine CategoryTheory.Simple.not_isZero K (Functor.map_isZero _ ?_)
  rw [ModuleCat.isZero_iff_subsingleton]
  exact not_nontrivial_iff_subsingleton.1 hcon

/-- **An epimorphism from the structure sheaf onto a dualizing module is an isomorphism.** On an
integral locally Noetherian scheme, if `ω` is a dualizing module ([Stacks, Tag 0B4R]) then every
epimorphism `𝒪_X ⟶ ω` is an isomorphism.

See the module documentation for the argument. -/
theorem isIso_of_epi_structureModule_to_dualizingModule {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsIntegral X] (ω : X.Modules)
    (hω : letI := HasDerivedCategory.standard X.Modules
      IsDualizingModule ω)
    (φ : Stacks.Divisors.structureModule X ⟶ ω) (hepi : Epi φ) :
    IsIso φ := by
  let := HasDerivedCategory.standard X.Modules
  let : ω.IsQuasicoherent :=
    (((Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae X ω).out 1 2 rfl rfl).mp hω.1).1
  obtain ⟨n, hn⟩ := hω.2
  have := hepi
  have hmono : Mono φ := by
    refine Stacks.Divisors.mono_of_stalk_injective_on_associatedPoints φ fun x => ?_
    by_cases hx : Stacks.Divisors.IsAssociatedPoint (Stacks.Divisors.structureModule X) x
    · refine Or.inl ?_
      obtain rfl := eq_genericPoint_of_isAssociatedPoint_structureModule hx
      have : Nontrivial (ω.presheaf.stalk (genericPoint (X : Type u))) :=
        nontrivial_stalk_of_isDualizingModule_of_isField ω n hn
          (Field.toIsField (X.presheaf.stalk (genericPoint (X : Type u))))
      have hsurj : Function.Surjective
          (stalkLinearMap (Stacks.Divisors.structureModule X) ω φ
            (genericPoint (X : Type u))) :=
        Stacks.Chow.surjective_stalkLinearMap_of_epi φ hepi _
      have hinj : Function.Injective
          ((stalkLinearMap (Stacks.Divisors.structureModule X) ω φ
              (genericPoint (X : Type u))).comp
            (Stacks.Divisors.unitStalkLinearEquiv
              (genericPoint (X : Type u))).toLinearMap) :=
        injective_of_surjective_of_nontrivial _
          (hsurj.comp (Stacks.Divisors.unitStalkLinearEquiv
            (genericPoint (X : Type u))).surjective)
      exact (Function.Injective.of_comp_iff' _
        (Stacks.Divisors.unitStalkLinearEquiv (genericPoint (X : Type u))).bijective).1 hinj
    · exact Or.inr hx
  exact isIso_of_mono_of_epi φ

end Stacks.Duality

end
