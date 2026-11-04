module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalQuasiRegularClosedImmersion
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk

/-!
# The conormal criterion for quasi-regular immersions of algebraic spaces

This file proves Stacks 09RY in full: an immersion `i : Z ⟶ X` of algebraic spaces over a scheme
`S` is a quasi-regular immersion (Stacks 06BN, part (3)) if and only if

1. `i` is locally of finite presentation,
2. the conormal sheaf `𝒞_{Z/X}` is finite locally free, and
3. the canonical map `Sym^*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` of Stacks 09RQ is an isomorphism.

Condition (3) is stated for every symmetric algebra `Sym^*(𝒞_{Z/X})` together with its degree-one
generator; all of them are isomorphic, and in the direction into quasi-regularity one is
supplied by `SheafOfModules.algebras`.

## Proof

The immersion factors as a closed immersion `k : Z ⟶ X ∖ ∂Z` followed by the inclusion of an
open subspace (Stacks 04CE), and the conormal algebra, conormal sheaf and map of Stacks 09RQ of
`i` are by definition those of `k`.  Quasi-regularity of `i` is quasi-regularity of the base
changes `j_V` of `k` along the étale charts `V` of `X ∖ ∂Z`
(`AlgebraicGeometry.Space.isQuasiRegularImmersion_iff_forall_closedFactor`), and local finite
presentation of `i` gives that of every `j_V`
(`AlgebraicGeometry.Space.locallyOfFinitePresentation_closedFactor_baseChange`).

* Out of quasi-regularity, condition (1) is
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_isQuasiRegularImmersion`, and
  conditions (2) and (3) are
  `Space.isFiniteLocallyFreeOnSite_conormalAlgebra_piece_one_of_forall_quasiRegular` and
  `AlgebraicGeometry.Space.isIso_symmetricAlgebraToConormalAlgebra_of_forall_quasiRegular`.
* Into quasi-regularity, every `j_V` is quasi-regular by
  `Space.quasiRegularImmersionProperty_of_isIso_symmetricAlgebraToConormalAlgebra`.

Both chart-level arguments are those of the case of schemes, Stacks 063M, read on the sections of
the conormal algebra over affine étale charts.

## Main results

* `AlgebraicGeometry.Space.isQuasiRegularImmersion_iff_conormal`: an immersion is a quasi-regular
  immersion if and only if it satisfies conditions (1), (2) and (3).

## References

* [Stacks Project, Tag 09RY](https://stacks.math.columbia.edu/tag/09RY)
* [Stacks Project, Tag 063M](https://stacks.math.columbia.edu/tag/063M)
* [Stacks Project, Tag 09RQ](https://stacks.math.columbia.edu/tag/09RQ)
* [Stacks Project, Tag 06BN](https://stacks.math.columbia.edu/tag/06BN)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Z₀ X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks Project, Tag 09RY.**  An immersion `i : Z ⟶ X` of algebraic spaces is a
quasi-regular immersion if and only if (1) it is locally of finite presentation, (2) its conormal
sheaf `𝒞_{Z/X}` is finite locally free, and (3) the canonical map
`Sym^*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` of Stacks 09RQ is an isomorphism in every degree, for every
symmetric algebra `Sym^*(𝒞_{Z/X})` on the conormal sheaf.

The proof reduces to the closed factorisation `Z ⟶ X ∖ ∂Z` of Stacks 04CE and its base changes to
the étale charts of `X ∖ ∂Z`, where the case of schemes, Stacks 063M, is run on the sections of
the conormal algebra over affine charts; see the module documentation. -/
@[stacks 09RY "the whole statement: an immersion of algebraic spaces is quasi-regular iff it is \
locally of finite presentation, its conormal sheaf is finite locally free, and the map of 09RQ \
from the symmetric algebra on the conormal sheaf is an isomorphism in every degree, for every \
symmetric algebra"]
theorem isQuasiRegularImmersion_iff_conormal (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    IsQuasiRegularImmersion B S hS i ↔
      IsLocallyOfFinitePresentation B S hS i ∧
        SheafOfModules.IsFiniteLocallyFreeOnSite (conormalModuleOfImmersion B S hS hX hZ i hi) ∧
        ∀ (A : SheafOfModules.GradedAlgebra.{u, u}
            (structureRingSheaf B S hS (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS)))
          (ι : (conormalAlgebraOfImmersion B S hS hX hZ i hi).piece 1 ⟶ A.piece 1)
          (hA : SheafOfModules.GradedAlgebra.IsSymmetricAlgebra A ι) (n : ℤ),
          IsIso ((symmetricAlgebraToConormalAlgebraOfImmersion B S hS hX hZ i hi A ι hA).app
            n) := by
  have hk := isClosedImmersion_immersionClosedFactorization B S hS hX hZ i hi
  rw [conormalModuleOfImmersion_eq_conormalAlgebraOfImmersion_piece_one,
    isQuasiRegularImmersion_iff_forall_closedFactor B S hS hX hZ i hi]
  constructor
  · intro h
    exact ⟨isLocallyOfFinitePresentation_of_isQuasiRegularImmersion B S hS hZ hX i hi
        ((isQuasiRegularImmersion_iff_forall_closedFactor B S hS hX hZ i hi).2 h),
      isFiniteLocallyFreeOnSite_conormalAlgebra_piece_one_of_forall_quasiRegular B S hS _ hk h,
      fun A ι hA n =>
        isIso_symmetricAlgebraToConormalAlgebra_of_forall_quasiRegular B S hS _ hk h A ι hA n⟩
  · rintro ⟨hfp, hflf, hiso⟩
    have h1 : (smallEtaleRingedSite B S hS Z₀ hZ).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
      SmallEtale.instWEqualsLocallyBijective B S hS Z₀ AddCommGrpCat.{u}
    have h2 : HasWeakSheafify (smallEtaleRingedSite B S hS Z₀ hZ).J AddCommGrpCat.{u} :=
      smallEtaleRingedSite_hasWeakSheafify_addCommGrpCat B S hS Z₀ hZ
    have h3 : (smallEtaleRingedSite B S hS Z₀ hZ).J.HasSheafCompose
        (forget₂ CommRingCat.{u} RingCat.{u}) :=
      (smallEtaleRingedSite B S hS Z₀ hZ).hasSheafCompose_forget₂_ringCat
    let P := @SheafOfModules.algebras.{u, u + 1, u} _ _ (smallEtaleRingedSite B S hS Z₀ hZ).J h3
      (smallEtaleRingedSite B S hS Z₀ hZ).O h1 h2
      ((conormalAlgebraOfImmersion B S hS hX hZ i hi).piece 1)
    exact quasiRegularImmersionProperty_of_isIso_symmetricAlgebraToConormalAlgebra B S hS _ hk
      (locallyOfFinitePresentation_closedFactor_baseChange B S hS hX hZ i hi hfp) hflf
      P.symmetric P.symmetricGenerator P.symmetric_isSymmetricAlgebra
      (hiso P.symmetric P.symmetricGenerator P.symmetric_isSymmetricAlgebra)

end AlgebraicGeometry.Space

end
