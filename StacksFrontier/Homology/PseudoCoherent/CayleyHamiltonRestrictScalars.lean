module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Homology.PseudoCoherent.CayleyHamilton

/-!
# Complexes of modules over a finite type algebra, pseudo-coherent over the base

Let `f : A →+* R` be a ring map of finite type and `M` an object of `D(R)` whose restriction of
scalars to `D(A)` is pseudo-coherent. Every element `r ∈ R` acts on a complex representing `M` by
the chain endomorphism `r • 𝟙`, whose restriction of scalars is a chain endomorphism of a complex
of `A`-modules pseudo-coherent in `D(A)`. Cayley–Hamilton for pseudo-coherent complexes
(`StacksDraft.PseudoCoherence.exists_ideal_finite_quotient_homologyMap_eq_zero`) then gives, for
each `i`, an ideal `J ⊆ R` with `R ⧸ J` finite over `A` killing the `R`-module `Hⁱ(M)`.

## Main results

* `StacksDraft.PseudoCoherence.exists_ideal_finite_quotient_smul_homology_eq_zero`: the statement
  for a complex of `R`-modules.
* `StacksDraft.PseudoCoherence.exists_ideal_finite_quotient_smul_homologyFunctor_eq_zero`: the
  statement for an object of `D(R)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.PseudoCoherence

universe u v

variable {A R : Type u} [CommRing A] [CommRing R]

/-- **The cohomology of a complex of modules over a finite type algebra which is pseudo-coherent
over the base is killed by an ideal of finite colength over the base.** Let `f : A →+* R` be of
finite type and `C` a complex of `R`-modules whose restriction of scalars to `A` is
pseudo-coherent in `D(A)`. For every `i` there is an ideal `J ⊆ R`, with `R ⧸ J` finite over `A`,
killing the `R`-module `Hⁱ(C)`. -/
theorem exists_ideal_finite_quotient_smul_homology_eq_zero
    [HasDerivedCategory (ModuleCat.{v} A)] (f : A →+* R) (hf : f.FiniteType)
    (C : CochainComplex (ModuleCat.{v} R) ℤ)
    (hC : IsPseudoCoherent (DerivedCategory.Q.obj
      (((ModuleCat.restrictScalars.{v} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)))
    (i : ℤ) :
    ∃ J : Ideal R, ((Ideal.Quotient.mk J).comp f).Finite ∧
      ∀ r ∈ J, ∀ x : C.homology i, r • x = 0 := by
  let := f.toAlgebra
  have : Algebra.FiniteType A R := hf
  let F := ModuleCat.restrictScalars.{v} f
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let ρ : R →+* End (G.obj C) :=
    { toFun r := End.of (G.map (r • 𝟙 C))
      map_one' := by rw [one_smul, G.map_id]; rfl
      map_mul' r s := by
        ext1
        change G.map ((r * s) • 𝟙 C) = G.map (s • 𝟙 C) ≫ G.map (r • 𝟙 C)
        rw [← G.map_comp, Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul,
          mul_comm]
      map_zero' := by rw [zero_smul, G.map_zero]; rfl
      map_add' r s := by rw [add_smul, G.map_add]; rfl }
  have hρ (a : A) : (ρ (algebraMap A R a)).asHom = a • (𝟙 (G.obj C) : G.obj C ⟶ G.obj C) := by
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    ext x
    rfl
  obtain ⟨J, hJ, hJ0⟩ := exists_ideal_finite_quotient_homologyMap_eq_zero hC ρ hρ i
  refine ⟨J, ?_, fun r hr x => ?_⟩
  · rw [← Ideal.Quotient.algebraMap_eq, ← RingHom.algebraMap_toAlgebra f,
      ← IsScalarTower.algebraMap_eq]
    exact RingHom.finite_algebraMap.2 hJ
  · have h0 := hJ0 r hr
    -- `Hⁱ(G (r • 𝟙)) = 0` gives `F (Hⁱ(r • 𝟙)) = 0` through `F(Hⁱ C) ≅ Hⁱ(G C)`.
    have hnat := ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) i).map
        (r • 𝟙 C)) F
    have h1 : ShortComplex.homologyMap (F.mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) i).map
          (r • 𝟙 C))) = 0 := h0
    rw [h1, zero_comp, eq_comm, Preadditive.IsIso.comp_left_eq_zero] at hnat
    have h2 : HomologicalComplex.homologyMap (r • 𝟙 C) i = r • 𝟙 _ := by
      let Fs := HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) i
      have hsc : Fs.map (r • 𝟙 C) = r • 𝟙 (Fs.obj C) := by
        ext <;> rfl
      change ShortComplex.homologyMap (Fs.map (r • 𝟙 C)) = _
      rw [hsc, ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
      rfl
    have h3 := congrArg (fun g => g.hom x) hnat
    change (HomologicalComplex.homologyMap (r • 𝟙 C) i).hom x = 0 at h3
    rw [h2] at h3
    exact h3

/-- **The cohomology of an object of `D(R)`, `R` of finite type over `A`, pseudo-coherent over
`A`, is killed by an ideal of finite colength over `A`.** Let `f : A →+* R` be of finite type and
`M ∈ D(R)` with restriction of scalars pseudo-coherent in `D(A)`. For every `i` there is an ideal
`J ⊆ R`, with `R ⧸ J` finite over `A`, killing the `R`-module `Hⁱ(M)`. -/
theorem exists_ideal_finite_quotient_smul_homologyFunctor_eq_zero
    [HasDerivedCategory (ModuleCat.{v} A)] [HasDerivedCategory (ModuleCat.{v} R)]
    (f : A →+* R) (hf : f.FiniteType) (M : DerivedCategory (ModuleCat.{v} R))
    (hM : IsPseudoCoherent ((ModuleCat.restrictScalars.{v} f).mapDerivedCategory.obj M))
    (i : ℤ) :
    ∃ J : Ideal R, ((Ideal.Quotient.mk J).comp f).Finite ∧
      ∀ r ∈ J, ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj M, r • x = 0 := by
  let F := ModuleCat.restrictScalars.{v} f
  let C := DerivedCategory.Q.objPreimage M
  let e : DerivedCategory.Q.obj C ≅ M := DerivedCategory.Q.objObjPreimageIso M
  have hC : IsPseudoCoherent (DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj C)) :=
    hM.ofIso (F.mapDerivedCategory.mapIso e.symm ≪≫ F.mapDerivedCategoryFactors.app C)
  obtain ⟨J, hJ, hJ0⟩ := exists_ideal_finite_quotient_smul_homology_eq_zero f hf C hC i
  refine ⟨J, hJ, fun r hr x => ?_⟩
  let u : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj M ≅ C.homology i :=
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) i).app C
  apply (ModuleCat.mono_iff_injective u.hom).1 inferInstance
  rw [map_smul, hJ0 r hr, map_zero]

end StacksDraft.PseudoCoherence

end
