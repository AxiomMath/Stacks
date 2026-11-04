module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeFiniteFree
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Complexes on the spectrum of a field concentrated in one degree

Let `k` be a field. A quasi-coherent `𝒪_{Spec k}`-module `M` of finite type is `Γ(M)^~`, and
`Γ(M)` is a finite-dimensional `k`-vector space, so a choice of basis identifies `M` with a finite
direct sum of copies of `𝒪_{Spec k}`. Consequently an object `K` of `D(𝒪_{Spec k})` concentrated
in one degree `d`, whose cohomology sheaf `H^d(K)` is quasi-coherent of finite type, is a finite
direct sum of copies of `𝒪_{Spec k}[-d]`.

## Main results

* `AlgebraicGeometry.exists_iso_biproduct_tilde_of_isFiniteType`: the module statement, with the
  summands spelled `k^~`.
* `AlgebraicGeometry.exists_iso_biproduct_singleFunctor_unit_of_isGE_of_isLE`: the derived
  statement, with the summands `𝒪_{Spec k}` placed in degree `d`.

## Implementation notes

In the module statement the summand is spelled `(tilde.functor R).obj (ModuleCat.of R R)` rather
than `SheafOfModules.unit (Spec R).ringCatSheaf`; the two are equal on the nose
(`AlgebraicGeometry.tildeSelf` is `Iso.refl`), but only the first has type
`AlgebraicGeometry.Scheme.Modules`, where the `HasFiniteBiproducts` instance
`Stacks.AffineTilde.hasFiniteBiproducts_modules` is found (see the implementation notes of
`StacksFrontier.Homology.PseudoCoherentRelative.TildeFiniteFree`). In the derived category no such
issue arises and the summand is `SheafOfModules.unit` in degree `d`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- **A quasi-coherent module of finite type on the spectrum of a field is a finite direct sum of
copies of the structure sheaf.** It is `Γ(M)^~`, and a basis of the finite-dimensional vector
space `Γ(M)` identifies it with `(k^n)^~ = ⨁ k^~`. -/
theorem exists_iso_biproduct_tilde_of_isFiniteType (M : (Spec (.of k)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ n : ℕ, Nonempty (M ≅ ⨁ fun _ : Fin n =>
      (tilde.functor (.of k)).obj (ModuleCat.of (CommRingCat.of k) (CommRingCat.of k))) := by
  let R : CommRingCat.{u} := CommRingCat.of k
  let V : ModuleCat.{u} R := moduleSpecΓFunctor.obj M
  have : Module.Finite R V := moduleFinite_of_isFiniteType_qc R M
  let _ : Field (R : Type u) := inferInstanceAs (Field k)
  let b := Module.finBasis R V
  exact ⟨_, ⟨(asIso M.fromTildeΓ).symm ≪≫ (tilde.functor R).mapIso b.equivFun.toModuleIso ≪≫
    Stacks.AffineTilde.tildeFinPi R _⟩⟩

attribute [local instance 100000] HasDerivedCategory.standard

/-- **An object of `D(𝒪_{Spec k})` concentrated in degree `d` whose cohomology sheaf `H^d` is
quasi-coherent of finite type is a finite direct sum of copies of `𝒪_{Spec k}[-d]`.** It is
`H^d[-d]`, and `H^d` is a finite direct sum of copies of `𝒪_{Spec k}`
(`exists_iso_biproduct_tilde_of_isFiniteType`). -/
theorem exists_iso_biproduct_singleFunctor_unit_of_isGE_of_isLE
    (K : DerivedCategory (Spec (.of k)).Modules) (d : ℤ) [K.IsGE d] [K.IsLE d]
    [((DerivedCategory.homologyFunctor (Spec (.of k)).Modules d).obj K).IsQuasicoherent]
    [((DerivedCategory.homologyFunctor (Spec (.of k)).Modules d).obj K).IsFiniteType] :
    ∃ n : ℕ, Nonempty (K ≅ ⨁ fun _ : Fin n =>
      (DerivedCategory.singleFunctor (Spec (.of k)).Modules d).obj
        (SheafOfModules.unit (Spec (.of k)).ringCatSheaf)) := by
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K d
  let eH : (DerivedCategory.homologyFunctor (Spec (.of k)).Modules d).obj K ≅ Y :=
    (DerivedCategory.homologyFunctor _ d).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ d).app Y
  have : Y.IsQuasicoherent :=
    ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent (Spec (.of k)).ringCatSheaf) eH
      (inferInstanceAs ((DerivedCategory.homologyFunctor _ d).obj K).IsQuasicoherent)
  have : Y.IsFiniteType := isFiniteType_of_scheme_iso eH
  obtain ⟨n, ⟨f⟩⟩ := exists_iso_biproduct_tilde_of_isFiniteType Y
  exact ⟨n, ⟨e ≪≫ (DerivedCategory.singleFunctor _ d).mapIso f ≪≫
    (DerivedCategory.singleFunctor _ d).mapBiproduct _⟩⟩

end AlgebraicGeometry

end
