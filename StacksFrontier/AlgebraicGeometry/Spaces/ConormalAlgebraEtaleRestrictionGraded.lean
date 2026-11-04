module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraOfImmersionSquareMap
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleGradedAlgebraPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleUnitCompJoin
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleGradedAlgebraPullbackCompApp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleGradedAlgebraPullbackCompAssoc

/-!
# The conormal algebra commutes with étale localization, as sheaves of graded algebras

Let `i : Z ⟶ X` be an immersion of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `φ : U ⟶ X` be étale and let

```
Z_U --p--> Z
|i_U       |i
U  --φ-->  X
```

be cartesian.  [Stacks Project, Tag 09RR] asserts that

`𝒞_{Z/X,*}|_{Z_U} = 𝒞_{Z_U/U,*}`

canonically and functorially in `U`, as sheaves of graded `𝒪_{Z_U}`-algebras.  This file
constructs the identification as an isomorphism of **sheaves of graded algebras**, proves that it
is **functorial in `U`**, and does both also for the conormal algebra of an immersion as
Stacks 09RN defines it.  No hypothesis is imposed on `i` in the general form, and `U` is an
arbitrary algebraic space étale over `X` rather than a scheme.

## Main definitions

* `AlgebraicGeometry.Space.reesGradedAlgebraEtalePullbackIso`: for an étale `φ : U ⟶ X`, a sheaf
  of ideals `𝓘 ⊆ 𝒪_X` and a sheaf of ideals `𝓙 ⊆ 𝒪_U` with the same sections over every étale
  chart, the isomorphism of sheaves of graded algebras `φ^*(⨁ 𝓘ⁿ) ≅ ⨁ 𝓙ⁿ`.
* `AlgebraicGeometry.Space.kernelIdealGradedAlgebraEtalePullbackIso`: the case of the kernel
  ideal sheaves of the two vertical arrows of a cartesian square.
* `AlgebraicGeometry.Space.conormalAlgebraEtaleRestrictionIso`: **Stacks 09RR**, the
  isomorphism of sheaves of graded `𝒪_{Z_U}`-algebras `p^*𝒞_{Z/X,*} ≅ 𝒞_{Z_U/U,*}` for the
  conormal algebra `AlgebraicGeometry.Space.conormalAlgebra` of an arbitrary morphism `i`.
* `AlgebraicGeometry.Space.conormalAlgebraIsoConormalAlgebraOfImmersion`: for an immersion,
  `AlgebraicGeometry.Space.conormalAlgebra` is the conormal algebra of Stacks 09RN,
  `AlgebraicGeometry.Space.conormalAlgebraOfImmersion`.
* `AlgebraicGeometry.Space.conormalAlgebraOfImmersionEtaleRestrictionIso`: **Stacks 09RR** for
  the conormal algebra of an immersion of Stacks 09RN.

## Main results

* `AlgebraicGeometry.Space.isEtaleRestrictionMultiplicative_rees`: the identification
  `𝓘ⁿ|_U = 𝓙ⁿ` of `AlgebraicGeometry.Space.etaleModulePullback_idealSheafZPow_eq` is
  multiplicative.
* `AlgebraicGeometry.Space.reesGradedAlgebraEtalePullbackIso_comp`: the identification
  `φ^*(⨁ 𝓘ⁿ) ≅ ⨁ 𝓙ⁿ` along a composite of étale morphisms is the composite of the
  identifications.
* `AlgebraicGeometry.Space.conormalAlgebraEtaleRestrictionIso_comp` and
  `AlgebraicGeometry.Space.conormalAlgebraOfImmersionEtaleRestrictionIso_comp`: **the
  functoriality in `U` of Stacks 09RR.**  For `ψ : U' ⟶ U` over `X`, the identification along
  `U'` is the identification along `U`, restricted to `Z_{U'}`, followed by the identification
  along `ψ`.

## References

* [Stacks Project, Tag 09RR](https://stacks.math.columbia.edu/tag/09RR)
* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03FV](https://stacks.math.columbia.edu/tag/03FV)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The graded algebra of the powers of a sheaf of ideals, along an étale morphism -/

section Rees

variable {U X : AlgebraicSpaces B S hS} (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (𝓘 : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (𝓙 : (SheafOfModules.unit (structureRingSheaf B S hS U)).Submodule)
    (h : ∀ W : SmallEtale B S hS U.1,
      SheafOfModules.idealAt 𝓙 (op W) =
        SheafOfModules.idealAt 𝓘 (op ((smallEtalePostcomp B S hS φ hφ).obj W)))

/-- Transport along an equality of sheaf submodules does not change the underlying section of
the structure sheaf. -/
theorem eqToHom_submodule_val {K K' : (SheafOfModules.unit (structureRingSheaf B S hS U)).Submodule}
    (hK : K = K') (W : (SmallEtale B S hS U.1)ᵒᵖ) (s : K.toSheafOfModules.val.obj W) :
    ((eqToHom (congrArg SheafOfModules.Submodule.toSheafOfModules hK)).val.app W s).1 = s.1 := by
  subst hK
  rfl

/-- The identification `𝓘ⁿ|_U = 𝓙ⁿ` of
`AlgebraicGeometry.Space.etaleModulePullback_idealSheafZPow_eq` does not change the underlying
section of the structure sheaf. -/
theorem eqToHom_etaleModulePullback_idealSheafZPow_val (n : ℤ) (W : (SmallEtale B S hS U.1)ᵒᵖ)
    (s : ((etaleModulePullback.{u, u} B S hS φ hφ).obj
      (SheafOfModules.idealSheafZPow 𝓘 n).toSheafOfModules).val.obj W) :
    ((eqToHom (etaleModulePullback_idealSheafZPow_eq B S hS φ hφ 𝓘 𝓙 h n)).val.app W s).1 =
      s.1 :=
  eqToHom_submodule_val B S hS (etaleRestrictionIdealSheafZPowSheaf_eq B S hS φ hφ 𝓘 𝓙 h n) W s

/-- **The identification `𝓘ⁿ|_U = 𝓙ⁿ` is multiplicative**: both multiplications are
multiplication of sections of the structure sheaf, over the same ring. -/
theorem isEtaleRestrictionMultiplicative_rees :
    IsEtaleRestrictionMultiplicative B S hS φ hφ
      (SheafOfModules.reesGradedAlgebra 𝓘 (structureRingSheaf_mul_comm B S hS X))
      (SheafOfModules.reesGradedAlgebra 𝓙 (structureRingSheaf_mul_comm B S hS U))
      (fun n => eqToIso (etaleModulePullback_idealSheafZPow_eq B S hS φ hφ 𝓘 𝓙 h n)) := by
  intro i j W x y
  refine Subtype.ext ?_
  refine (eqToHom_etaleModulePullback_idealSheafZPow_val B S hS φ hφ 𝓘 𝓙 h (i + j) W _).trans ?_
  exact (congrArg₂ (fun a b : ToType ((structureRingSheaf B S hS X).obj.obj
      (op ((smallEtalePostcomp B S hS φ hφ).obj W.unop))) => a * b)
    (eqToHom_etaleModulePullback_idealSheafZPow_val B S hS φ hφ 𝓘 𝓙 h i W x)
    (eqToHom_etaleModulePullback_idealSheafZPow_val B S hS φ hφ 𝓘 𝓙 h j W y)).symm

/-- **The graded algebra of the powers of a sheaf of ideals, along an étale morphism.**  For an
étale `φ : U ⟶ X` and sheaves of ideals `𝓘 ⊆ 𝒪_X`, `𝓙 ⊆ 𝒪_U` with the same sections over every
étale chart of `U`, the pullback `φ^*(⨁_n 𝓘ⁿ)` is `⨁_n 𝓙ⁿ` as a sheaf of graded `𝒪_U`-algebras.
Its degree-`n` component is the identification of Stacks 03LW followed by the equality
`𝓘ⁿ|_U = 𝓙ⁿ`. -/
noncomputable def reesGradedAlgebraEtalePullbackIso :
    (gradedPull (X := smallEtaleRingedTopos B S hS U) (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS φ)).obj
        (SheafOfModules.reesGradedAlgebra 𝓘 (structureRingSheaf_mul_comm B S hS X)) ≅
      SheafOfModules.reesGradedAlgebra 𝓙 (structureRingSheaf_mul_comm B S hS U) :=
  etaleGradedPullbackIso (isEtaleRestrictionMultiplicative_rees B S hS φ hφ 𝓘 𝓙 h)

/-- The degree-`n` component of `AlgebraicGeometry.Space.reesGradedAlgebraEtalePullbackIso`. -/
theorem reesGradedAlgebraEtalePullbackIso_hom_app (n : ℤ) :
    (reesGradedAlgebraEtalePullbackIso B S hS φ hφ 𝓘 𝓙 h).hom.app n =
      (modulePullbackIsoEtaleModulePullback B S hS φ hφ).hom.app
          (SheafOfModules.idealSheafZPow 𝓘 n).toSheafOfModules ≫
        eqToHom (etaleModulePullback_idealSheafZPow_eq B S hS φ hφ 𝓘 𝓙 h n) :=
  rfl

include h in
/-- The identification `𝓘ⁿ|_U = 𝓙ⁿ` of
`AlgebraicGeometry.Space.etaleModulePullback_idealSheafZPow_eq`, stated for the homogeneous pieces
of the two graded algebras of powers, read over the structure
sheaves of the small étale ringed topoi. -/
theorem etaleModulePullback_reesGradedAlgebra_piece_eq (n : ℤ) :
    (etaleModulePullback.{u, u} B S hS φ hφ).obj (SheafOfModules.GradedAlgebra.piece
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)
        (SheafOfModules.reesGradedAlgebra 𝓘 (structureRingSheaf_mul_comm B S hS X)) n) =
      SheafOfModules.GradedAlgebra.piece
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS U).O)
        (SheafOfModules.reesGradedAlgebra 𝓙 (structureRingSheaf_mul_comm B S hS U)) n :=
  etaleModulePullback_idealSheafZPow_eq B S hS φ hφ 𝓘 𝓙 h n

/-- The degree-`n` component of `AlgebraicGeometry.Space.reesGradedAlgebraEtalePullbackIso`, with
its objects read as the homogeneous pieces of the two graded algebras of powers. -/
theorem reesGradedAlgebraEtalePullbackIso_hom_app_piece (n : ℤ) :
    (reesGradedAlgebraEtalePullbackIso B S hS φ hφ 𝓘 𝓙 h).hom.app n =
      (modulePullbackIsoEtaleModulePullback B S hS φ hφ).hom.app
          (SheafOfModules.GradedAlgebra.piece (R := Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos B S hS X).O)
            (SheafOfModules.reesGradedAlgebra 𝓘 (structureRingSheaf_mul_comm B S hS X)) n) ≫
        eqToHom (etaleModulePullback_reesGradedAlgebra_piece_eq B S hS φ hφ 𝓘 𝓙 h n) :=
  etaleGradedPullbackIso_hom_app _ n

end Rees

/-! ### The identification along a composite of étale morphisms -/

section ReesComp

variable {U' U X : AlgebraicSpaces B S hS} (ψ : U' ⟶ U) (φ : U ⟶ X)
    (hψ : IsEtale B S hS ψ.hom) (hφ : IsEtale B S hS φ.hom)
    (hψφ : IsEtale B S hS (ψ ≫ φ).hom)

/-- **Stacks 03LW along a composite of étale morphisms, transported along equalities.**  The
comparison `(ψ ≫ φ)^* ≅ ψ^*φ^*` of Stacks 03LU, followed by the identification of Stacks 03LW
along `φ` and then along `ψ`, each followed by a transport along an equality of modules, is the
identification of Stacks 03LW along `ψ ≫ φ` followed by the transport. -/
theorem modulePullbackCompIso_inv_etaleRestriction_eqToHom (M : Modules.{u, u} B S hS X.1 X.2)
    (N : Modules.{u, u} B S hS U.1 U.2) (K : Modules.{u, u} B S hS U'.1 U'.2)
    (eφ : (etaleModulePullback.{u, u} B S hS φ hφ).obj M = N)
    (eψ : (etaleModulePullback.{u, u} B S hS ψ hψ).obj N = K)
    (eψφ : (etaleModulePullback.{u, u} B S hS (ψ ≫ φ) hψφ).obj M = K) :
    (modulePullbackCompIso B S hS ψ φ).inv.app M ≫
      (modulePullback B S hS ψ).map
        ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).hom.app M ≫ eqToHom eφ) ≫
      (modulePullbackIsoEtaleModulePullback B S hS ψ hψ).hom.app N ≫ eqToHom eψ =
    (modulePullbackIsoEtaleModulePullback B S hS (ψ ≫ φ) hψφ).hom.app M ≫ eqToHom eψφ := by
  have key : (modulePullbackCompIso B S hS ψ φ).hom.app M ≫
      (modulePullbackIsoEtaleModulePullback B S hS (ψ ≫ φ) hψφ).hom.app M =
      (modulePullbackIsoEtaleModulePullback B S hS ψ hψ).hom.app
          ((modulePullback B S hS φ).obj M) ≫
        (etaleModulePullback.{u, u} B S hS ψ hψ).map
          ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).hom.app M) ≫
        (etaleModulePullbackComp B S hS ψ φ hψ hφ hψφ).hom.app M :=
    NatTrans.congr_app
      (modulePullbackCompIso_hom_comp_etaleRestriction B S hS ψ φ hψ hφ hψφ
        (etaleModulePullbackCompAdjunction_unit B S hS ψ φ hψ hφ hψφ)) M
  refine CategoryTheory.CompIsoCube.inv_comp_map_comp_app_comp
    (modulePullbackIsoEtaleModulePullback B S hS ψ hψ).hom _ _
    ((modulePullbackCompIso B S hS ψ φ).app M) _ _ _ _ key ?_
  exact CategoryTheory.CompIsoCube.map_eqToHom_comp_eqToHom
    (etaleModulePullback.{u, u} B S hS ψ hψ) _ _ _

variable (𝓘 : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (𝓙 : (SheafOfModules.unit (structureRingSheaf B S hS U)).Submodule)
    (𝓚 : (SheafOfModules.unit (structureRingSheaf B S hS U')).Submodule)
    (hJ : ∀ W : SmallEtale B S hS U.1,
      SheafOfModules.idealAt 𝓙 (op W) =
        SheafOfModules.idealAt 𝓘 (op ((smallEtalePostcomp B S hS φ hφ).obj W)))
    (hK : ∀ W : SmallEtale B S hS U'.1,
      SheafOfModules.idealAt 𝓚 (op W) =
        SheafOfModules.idealAt 𝓙 (op ((smallEtalePostcomp B S hS ψ hψ).obj W)))
    (hK' : ∀ W : SmallEtale B S hS U'.1,
      SheafOfModules.idealAt 𝓚 (op W) =
        SheafOfModules.idealAt 𝓘 (op ((smallEtalePostcomp B S hS (ψ ≫ φ) hψφ).obj W)))

/-- `AlgebraicGeometry.Space.modulePullbackCompIso_inv_etaleRestriction_eqToHom` at the
homogeneous pieces of the graded algebras of powers of three compatible sheaves of ideals. -/
theorem modulePullbackCompIso_inv_etaleRestriction_reesPiece (n : ℤ) :
    (modulePullbackCompIso B S hS ψ φ).inv.app (SheafOfModules.GradedAlgebra.piece
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)
        (SheafOfModules.reesGradedAlgebra 𝓘 (structureRingSheaf_mul_comm B S hS X)) n) ≫
      (modulePullback B S hS ψ).map
        ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).hom.app
          (SheafOfModules.GradedAlgebra.piece (R := Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos B S hS X).O)
            (SheafOfModules.reesGradedAlgebra 𝓘 (structureRingSheaf_mul_comm B S hS X)) n) ≫
        eqToHom (etaleModulePullback_reesGradedAlgebra_piece_eq B S hS φ hφ 𝓘 𝓙 hJ n)) ≫
      (modulePullbackIsoEtaleModulePullback B S hS ψ hψ).hom.app
          (SheafOfModules.GradedAlgebra.piece (R := Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos B S hS U).O)
            (SheafOfModules.reesGradedAlgebra 𝓙 (structureRingSheaf_mul_comm B S hS U)) n) ≫
        eqToHom (etaleModulePullback_reesGradedAlgebra_piece_eq B S hS ψ hψ 𝓙 𝓚 hK n) =
    (modulePullbackIsoEtaleModulePullback B S hS (ψ ≫ φ) hψφ).hom.app
        (SheafOfModules.GradedAlgebra.piece (R := Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos B S hS X).O)
            (SheafOfModules.reesGradedAlgebra 𝓘 (structureRingSheaf_mul_comm B S hS X)) n) ≫
      eqToHom (etaleModulePullback_reesGradedAlgebra_piece_eq B S hS (ψ ≫ φ) hψφ 𝓘 𝓚 hK' n) :=
  modulePullbackCompIso_inv_etaleRestriction_eqToHom B S hS ψ φ hψ hφ hψφ _ _ _ _ _ _

/-- The degree-`n` component of the composition comparison along a morphism equal to `ψ ≫ φ`, at
the graded algebra of powers of `𝓘`, is the inverse of the comparison of Stacks 03LU. -/
theorem gradedAlgebraPullbackCompIsoOfEq_hom_app_app_rees (hc : ψ ≫ φ = ψ ≫ φ) (n : ℤ) :
    ((gradedAlgebraPullbackCompIsoOfEq B S hS ψ φ (ψ ≫ φ) hc).hom.app
        (SheafOfModules.reesGradedAlgebra 𝓘 (structureRingSheaf_mul_comm B S hS X))).app n =
      (modulePullbackCompIso B S hS ψ φ).inv.app (SheafOfModules.GradedAlgebra.piece
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)
        (SheafOfModules.reesGradedAlgebra 𝓘 (structureRingSheaf_mul_comm B S hS X)) n) :=
  (congrArg (fun e => (e.hom.app
      (SheafOfModules.reesGradedAlgebra 𝓘 (structureRingSheaf_mul_comm B S hS X))).app n)
    (gradedAlgebraPullbackCompIsoOfEq_self B S hS ψ φ hc)).trans
    (gradedAlgebraPullbackCompIso_hom_app_app B S hS ψ φ _ n)

/-- The degree-`n` component of the inverse image along `ψ` of the identification of the graded
algebras of powers along `φ`. -/
theorem gradedPull_map_reesGradedAlgebraEtalePullbackIso_app (n : ℤ) :
    ((gradedPull (X := smallEtaleRingedTopos B S hS U') (Y := smallEtaleRingedTopos B S hS U)
      (smallEtaleRingedToposHom B S hS ψ)).map
        (reesGradedAlgebraEtalePullbackIso B S hS φ hφ 𝓘 𝓙 hJ).hom).app n =
      (modulePullback B S hS ψ).map
        ((reesGradedAlgebraEtalePullbackIso B S hS φ hφ 𝓘 𝓙 hJ).hom.app n) := rfl

/-- **The identification of the graded algebras of powers along a composite of étale
morphisms.**  For étale `ψ : U' ⟶ U`, `φ : U ⟶ X` and compatible sheaves of ideals
`𝓘 ⊆ 𝒪_X`, `𝓙 ⊆ 𝒪_U`, `𝓚 ⊆ 𝒪_{U'}`, the identification `(ψ ≫ φ)^*(⨁ 𝓘ⁿ) ≅ ⨁ 𝓚ⁿ` is the
composition comparison `(ψ ≫ φ)^* ≅ ψ^*φ^*` followed by the inverse image along `ψ` of the
identification along `φ` and by the identification along `ψ`. -/
theorem reesGradedAlgebraEtalePullbackIso_comp (hc : ψ ≫ φ = ψ ≫ φ) :
    (gradedAlgebraPullbackCompIsoOfEq B S hS ψ φ (ψ ≫ φ) hc).hom.app
        (SheafOfModules.reesGradedAlgebra 𝓘 (structureRingSheaf_mul_comm B S hS X)) ≫
      (gradedPull (X := smallEtaleRingedTopos B S hS U') (Y := smallEtaleRingedTopos B S hS U)
          (smallEtaleRingedToposHom B S hS ψ)).map
        (reesGradedAlgebraEtalePullbackIso B S hS φ hφ 𝓘 𝓙 hJ).hom ≫
      (reesGradedAlgebraEtalePullbackIso B S hS ψ hψ 𝓙 𝓚 hK).hom =
    (reesGradedAlgebraEtalePullbackIso B S hS (ψ ≫ φ) hψφ 𝓘 𝓚 hK').hom := by
  refine SheafOfModules.GradedAlgebra.Hom.ext fun n => ?_
  rw [SheafOfModules.GradedAlgebra.categoryStruct_comp_app,
    SheafOfModules.GradedAlgebra.categoryStruct_comp_app,
    gradedAlgebraPullbackCompIsoOfEq_hom_app_app_rees,
    gradedPull_map_reesGradedAlgebraEtalePullbackIso_app,
    reesGradedAlgebraEtalePullbackIso_hom_app_piece,
    reesGradedAlgebraEtalePullbackIso_hom_app_piece,
    reesGradedAlgebraEtalePullbackIso_hom_app_piece]
  exact modulePullbackCompIso_inv_etaleRestriction_reesPiece B S hS ψ φ hψ hφ hψφ 𝓘 𝓙 𝓚 hJ hK
    hK' n

end ReesComp

/-! ### The conormal algebra of a base change along an étale morphism -/

variable {U X Z ZU : AlgebraicSpaces B S hS}

/-- **The graded algebra of the powers of the kernel ideal sheaf, along an étale morphism.**  For
a cartesian square `p ≫ i = i_U ≫ φ` with `φ` étale, the pullback along `φ` of `⨁_n Ker(i^♯)ⁿ` is
`⨁_n Ker(i_U^♯)ⁿ` as a sheaf of graded `𝒪_U`-algebras. -/
noncomputable def kernelIdealGradedAlgebraEtalePullbackIso (p : ZU ⟶ Z) (iU : ZU ⟶ U)
    (i : Z ⟶ X) (φ : U ⟶ X) (sq : IsPullback p iU i φ) (hφ : IsEtale B S hS φ.hom) :
    (gradedPull (X := smallEtaleRingedTopos B S hS U) (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS φ)).obj (kernelIdealGradedAlgebra B S hS i) ≅
      kernelIdealGradedAlgebra B S hS iU :=
  reesGradedAlgebraEtalePullbackIso B S hS φ hφ (kernelIdealSheaf B S hS i)
    (kernelIdealSheaf B S hS iU)
    (fun W ↦ kernelIdealSheaf_baseChange_obj B S hS p iU i φ sq hφ W)

/-- **Stacks 09RR.**  Let `i : Z ⟶ X` be a morphism of algebraic spaces, let `φ : U ⟶ X` be
étale and let `Z_U = U ×_X Z`, with projections `p : Z_U ⟶ Z` and `i_U : Z_U ⟶ U`.  Then the
restriction `p^*𝒞_{Z/X,*}` of the conormal algebra of `i` is the conormal algebra of `i_U`, as
sheaves of graded `𝒪_{Z_U}`-algebras:

`𝒞_{Z/X,*}|_{Z_U} = p^*𝒞_{Z/X,*} ≅ 𝒞_{Z_U/U,*}`.

The isomorphism is canonical: it is the multiplicative composition comparison
`p^*i^* ≅ (i_U ≫ φ)^* ≅ i_U^*φ^*` of Stacks 03LU followed by the inverse image along `i_U` of the
identification `φ^*(⨁ 𝓘ⁿ) = ⨁ 𝓘_Uⁿ` of the graded algebras of the powers of the kernel ideal
sheaves, which is Stacks 03LW in each degree.

No hypothesis is imposed on `i` and `U` is an arbitrary algebraic space étale over `X`; for an
immersion `i` and a scheme `U` this is the statement of Stacks 09RR. -/
@[stacks 09RR "the conormal algebra of an etale localisation, as graded algebras"]
noncomputable def conormalAlgebraEtaleRestrictionIso (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X)
    (φ : U ⟶ X) (sq : IsPullback p iU i φ) (hφ : IsEtale B S hS φ.hom) :
    (gradedPull (X := smallEtaleRingedTopos B S hS ZU) (Y := smallEtaleRingedTopos B S hS Z)
        (smallEtaleRingedToposHom B S hS p)).obj (conormalAlgebra B S hS i) ≅
      conormalAlgebra B S hS iU :=
  CategoryTheory.CompIsoCube.squareIso
    (GA := fun A : AlgebraicSpaces B S hS => SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS A).O))
    (fun {A B'} (f : A ⟶ B') => gradedPull (X := smallEtaleRingedTopos B S hS A)
      (Y := smallEtaleRingedTopos B S hS B') (smallEtaleRingedToposHom B S hS f))
    (fun a b t h => gradedAlgebraPullbackCompIsoOfEq B S hS a b t h)
    p iU i φ (iU ≫ φ) sq.w.symm rfl
    (kernelIdealGradedAlgebraEtalePullbackIso B S hS p iU i φ sq hφ)

/-- The isomorphism of Stacks 09RR, unfolded: the composition comparison `p^*i^* ≅ (i_U ≫ φ)^*`
read through the square, the composition comparison `(i_U ≫ φ)^* ≅ i_U^*φ^*`, and the inverse
image along `i_U` of the identification of the graded algebras of powers. -/
theorem conormalAlgebraEtaleRestrictionIso_eq (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X)
    (φ : U ⟶ X) (sq : IsPullback p iU i φ) (hφ : IsEtale B S hS φ.hom) :
    conormalAlgebraEtaleRestrictionIso B S hS p iU i φ sq hφ =
      ((gradedAlgebraPullbackCompIsoOfEq B S hS p i (iU ≫ φ) sq.w.symm).app
          (kernelIdealGradedAlgebra B S hS i)).symm ≪≫
        (gradedAlgebraPullbackCompIsoOfEq B S hS iU φ (iU ≫ φ) rfl).app
          (kernelIdealGradedAlgebra B S hS i) ≪≫
        (gradedPull (X := smallEtaleRingedTopos B S hS ZU) (Y := smallEtaleRingedTopos B S hS U)
            (smallEtaleRingedToposHom B S hS iU)).mapIso
          (kernelIdealGradedAlgebraEtalePullbackIso B S hS p iU i φ sq hφ) :=
  rfl

/-! ### Functoriality in the étale source -/

variable {U' ZU' : AlgebraicSpaces B S hS}

/-- A morphism between two algebraic spaces étale over `X`, compatible with the structure
morphisms, is étale (Stacks 03FV). -/
theorem isEtale_of_comp_eq {φ : U ⟶ X} {φ' : U' ⟶ X} (ψ : U' ⟶ U) (hφ : IsEtale B S hS φ.hom)
    (hφ' : IsEtale B S hS φ'.hom) (hψφ : ψ ≫ φ = φ') : IsEtale B S hS ψ.hom :=
  isEtale_of_isEtale_over B S hS U'.2 U.2 X.2 ψ.hom φ'.hom φ.hom hφ' hφ
    (congrArg (fun k : U' ⟶ X => k.hom) hψφ)

/-- The square of `U'` over `U` is cartesian when the squares of `U'` and of `U` over `X` are. -/
theorem isPullback_of_comp_eq {p : ZU ⟶ Z} {iU : ZU ⟶ U} {i : Z ⟶ X} {φ : U ⟶ X}
    (sq : IsPullback p iU i φ) {p' : ZU' ⟶ Z} {iU' : ZU' ⟶ U'} {φ' : U' ⟶ X}
    (sq' : IsPullback p' iU' i φ') (ψ : U' ⟶ U) (hψφ : ψ ≫ φ = φ') (q : ZU' ⟶ ZU)
    (hqp : q ≫ p = p') (hqi : q ≫ iU = iU' ≫ ψ) : IsPullback q iU' iU ψ := by
  subst hψφ hqp
  exact IsPullback.of_right sq' hqi sq

/-- **Stacks 09RR, functoriality in `U`.**  Let `i : Z ⟶ X` be a morphism of algebraic spaces and
let `φ : U ⟶ X`, `φ' : U' ⟶ X` be étale, with cartesian squares `Z_U = U ×_X Z` and
`Z_{U'} = U' ×_X Z`.  Let `ψ : U' ⟶ U` be a morphism over `X` and `q : Z_{U'} ⟶ Z_U` the
induced morphism, so that `q ≫ p = p'` and `q ≫ i_U = i_{U'} ≫ ψ`.  Then the identification
`𝒞_{Z/X,*}|_{Z_{U'}} ≅ 𝒞_{Z_{U'}/U',*}` of Stacks 09RR along `φ'` is the identification
along `φ`, restricted along `q`, followed by the identification along `ψ`:

`p'^*𝒞_{Z/X,*} ≅ q^*p^*𝒞_{Z/X,*} ≅ q^*𝒞_{Z_U/U,*} ≅ 𝒞_{Z_{U'}/U',*}`. -/
@[stacks 09RR "functoriality in U of the identification of conormal algebras"]
theorem conormalAlgebraEtaleRestrictionIso_comp (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X)
    (φ : U ⟶ X) (sq : IsPullback p iU i φ) (hφ : IsEtale B S hS φ.hom) (p' : ZU' ⟶ Z)
    (iU' : ZU' ⟶ U') (φ' : U' ⟶ X) (sq' : IsPullback p' iU' i φ')
    (hφ' : IsEtale B S hS φ'.hom) (ψ : U' ⟶ U) (hψφ : ψ ≫ φ = φ') (q : ZU' ⟶ ZU)
    (hqp : q ≫ p = p') (hqi : q ≫ iU = iU' ≫ ψ) :
    conormalAlgebraEtaleRestrictionIso B S hS p' iU' i φ' sq' hφ' =
      (gradedAlgebraPullbackCompIsoOfEq B S hS q p p' hqp.symm).app (conormalAlgebra B S hS i) ≪≫
        (gradedPull (X := smallEtaleRingedTopos B S hS ZU') (Y := smallEtaleRingedTopos B S hS ZU)
            (smallEtaleRingedToposHom B S hS q)).mapIso
          (conormalAlgebraEtaleRestrictionIso B S hS p iU i φ sq hφ) ≪≫
        conormalAlgebraEtaleRestrictionIso B S hS q iU' iU ψ
          (isPullback_of_comp_eq B S hS sq sq' ψ hψφ q hqp hqi)
          (isEtale_of_comp_eq B S hS ψ hφ hφ' hψφ) := by
  subst hψφ hqp
  exact CategoryTheory.CompIsoCube.squareIso_comp
    (isAssoc_gradedAlgebraPullbackCompIsoOfEq B S hS) p iU i φ (iU ≫ φ) sq.w.symm rfl q iU' ψ
    (iU' ≫ ψ) hqi.symm rfl (q ≫ p) rfl (ψ ≫ φ) rfl (iU' ≫ ψ ≫ φ) sq'.w.symm rfl
    (kernelIdealGradedAlgebraEtalePullbackIso B S hS p iU i φ sq hφ)
    (kernelIdealGradedAlgebraEtalePullbackIso B S hS q iU' iU ψ
      (isPullback_of_comp_eq B S hS sq sq' ψ rfl q rfl hqi)
      (isEtale_of_comp_eq B S hS ψ hφ hφ' rfl))
    (kernelIdealGradedAlgebraEtalePullbackIso B S hS (q ≫ p) iU' i (ψ ≫ φ) sq' hφ')
    (reesGradedAlgebraEtalePullbackIso_comp B S hS ψ φ
      (isEtale_of_comp_eq B S hS ψ hφ hφ' rfl) hφ hφ' (kernelIdealSheaf B S hS i)
      (kernelIdealSheaf B S hS iU) (kernelIdealSheaf B S hS iU') _ _ _ rfl)

/-! ### The conormal algebra of an immersion -/

section Immersion

/-- The identity of an algebraic space is étale. -/
theorem isEtale_hom_id (Z : AlgebraicSpaces B S hS) : IsEtale B S hS (𝟙 Z : Z ⟶ Z).hom :=
  fun _ _ hφ => by simpa using hφ

/-- **The inverse image of a sheaf of graded algebras along the identity is the sheaf itself.**
This is `AlgebraicGeometry.Space.etaleGradedPullbackIso` along the identity, with the identity in
every degree. -/
noncomputable def gradedAlgebraPullbackIdIso (Z : AlgebraicSpaces B S hS)
    (𝒜 : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Z).O)) :
    (gradedPull (X := smallEtaleRingedTopos B S hS Z) (Y := smallEtaleRingedTopos B S hS Z)
      (smallEtaleRingedToposHom B S hS (𝟙 Z))).obj 𝒜 ≅ 𝒜 :=
  etaleGradedPullbackIso (f := 𝟙 Z) (hf := isEtale_hom_id B S hS Z) (𝒜 := 𝒜) (𝒜' := 𝒜)
    (c := fun _ => Iso.refl _) (fun _ _ _ _ _ => rfl)

variable {Z₀ X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The conormal algebra of an immersion, as a morphism, is the conormal algebra of Stacks
09RN.**  For an immersion `i : Z ⟶ X` the conormal algebra
`AlgebraicGeometry.Space.conormalAlgebra` of `i`, the inverse image of the graded algebra of the
powers of the kernel ideal sheaf of `i` itself, is the conormal algebra
`AlgebraicGeometry.Space.conormalAlgebraOfImmersion` of Stacks 09RN, which is taken through the
closed factorisation of `i` through the complement of its boundary: it is
`AlgebraicGeometry.Space.conormalAlgebraOfImmersionIso`, read through the inverse image along the
identity of `Z`. -/
noncomputable def conormalAlgebraIsoConormalAlgebraOfImmersion (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    conormalAlgebra B S hS
        (ObjectProperty.homMk i : (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X₀, hX⟩) ≅
      conormalAlgebraOfImmersion B S hS hX hZ i hi :=
  (gradedAlgebraPullbackIdIso B S hS ⟨Z₀, hZ⟩
      (conormalAlgebra B S hS
        (ObjectProperty.homMk i : (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X₀, hX⟩))).symm ≪≫
    conormalAlgebraOfImmersionIso B S hS hZ hX
      (ObjectProperty.homMk i : (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X₀, hX⟩) hi

/-- **Stacks 09RR, for the conormal algebra of an immersion as defined in Stacks 09RN.**  Let
`i : Z ⟶ X` be an immersion of algebraic spaces, let `φ : U ⟶ X` be étale and let
`Z_U = U ×_X Z`, with projections `p : Z_U ⟶ Z` and `i_U : Z_U ⟶ U`; then `i_U` is an
immersion and

`𝒞_{Z/X,*}|_{Z_U} = p^*𝒞_{Z/X,*} ≅ 𝒞_{Z_U/U,*}`

as sheaves of graded `𝒪_{Z_U}`-algebras, where both conormal algebras are those of Stacks 09RN,
`AlgebraicGeometry.Space.conormalAlgebraOfImmersion`.

It is `AlgebraicGeometry.Space.conormalAlgebraEtaleRestrictionIso` read through the
identification `AlgebraicGeometry.Space.conormalAlgebraIsoConormalAlgebraOfImmersion` on both
sides. -/
@[stacks 09RR "the conormal algebra of an immersion, restricted to an etale U, as graded algebras"]
noncomputable def conormalAlgebraOfImmersionEtaleRestrictionIso (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i)
    {U ZU : AlgebraicSpaces B S hS} (p : ZU ⟶ ⟨Z₀, hZ⟩) (iU : ZU ⟶ U) (φ : U ⟶ ⟨X₀, hX⟩)
    (sq : IsPullback p iU
      (ObjectProperty.homMk i : (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X₀, hX⟩) φ)
    (hφ : IsEtale B S hS φ.hom) :
    (gradedPull (X := smallEtaleRingedTopos B S hS ZU)
        (Y := smallEtaleRingedTopos B S hS ⟨Z₀, hZ⟩) (smallEtaleRingedToposHom B S hS p)).obj
        (conormalAlgebraOfImmersion B S hS hX hZ i hi) ≅
      conormalAlgebraOfImmersion B S hS U.2 ZU.2 iU.hom (isImmersion_of_isPullback B S hS sq hi) :=
  (gradedPull (X := smallEtaleRingedTopos B S hS ZU)
      (Y := smallEtaleRingedTopos B S hS ⟨Z₀, hZ⟩) (smallEtaleRingedToposHom B S hS p)).mapIso
      (conormalAlgebraIsoConormalAlgebraOfImmersion B S hS hX hZ i hi).symm ≪≫
    conormalAlgebraEtaleRestrictionIso B S hS p iU
      (ObjectProperty.homMk i : (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X₀, hX⟩) φ sq hφ ≪≫
    conormalAlgebraIsoConormalAlgebraOfImmersion B S hS U.2 ZU.2 iU.hom
      (isImmersion_of_isPullback B S hS sq hi)

/-- **Stacks 09RR, functoriality in `U`, for the conormal algebra of an immersion as defined in
Stacks 09RN.**  Let `i : Z ⟶ X` be an immersion and let `φ : U ⟶ X`, `φ' : U' ⟶ X` be étale, with
cartesian squares `Z_U = U ×_X Z` and `Z_{U'} = U' ×_X Z`.  Let `ψ : U' ⟶ U` be a morphism over
`X` and `q : Z_{U'} ⟶ Z_U` the induced morphism, so that `q ≫ p = p'` and `q ≫ i_U = i_{U'} ≫ ψ`.
Then the identification `𝒞_{Z/X,*}|_{Z_{U'}} ≅ 𝒞_{Z_{U'}/U',*}` along `φ'` is the identification
along `φ`, restricted along `q`, followed by the identification along `ψ` for the immersion
`i_U`. -/
@[stacks 09RR "functoriality in U, for the conormal algebra of an immersion"]
theorem conormalAlgebraOfImmersionEtaleRestrictionIso_comp (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i)
    {U ZU U' ZU' : AlgebraicSpaces B S hS} (p : ZU ⟶ ⟨Z₀, hZ⟩) (iU : ZU ⟶ U)
    (φ : U ⟶ ⟨X₀, hX⟩)
    (sq : IsPullback p iU
      (ObjectProperty.homMk i : (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X₀, hX⟩) φ)
    (hφ : IsEtale B S hS φ.hom) (p' : ZU' ⟶ ⟨Z₀, hZ⟩) (iU' : ZU' ⟶ U') (φ' : U' ⟶ ⟨X₀, hX⟩)
    (sq' : IsPullback p' iU'
      (ObjectProperty.homMk i : (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X₀, hX⟩) φ')
    (hφ' : IsEtale B S hS φ'.hom) (ψ : U' ⟶ U) (hψφ : ψ ≫ φ = φ') (q : ZU' ⟶ ZU)
    (hqp : q ≫ p = p') (hqi : q ≫ iU = iU' ≫ ψ) :
    conormalAlgebraOfImmersionEtaleRestrictionIso B S hS hX hZ i hi p' iU' φ' sq' hφ' =
      (gradedAlgebraPullbackCompIsoOfEq B S hS q p p' hqp.symm).app
          (conormalAlgebraOfImmersion B S hS hX hZ i hi) ≪≫
        (gradedPull (X := smallEtaleRingedTopos B S hS ZU') (Y := smallEtaleRingedTopos B S hS ZU)
            (smallEtaleRingedToposHom B S hS q)).mapIso
          (conormalAlgebraOfImmersionEtaleRestrictionIso B S hS hX hZ i hi p iU φ sq hφ) ≪≫
        conormalAlgebraOfImmersionEtaleRestrictionIso B S hS U.2 ZU.2 iU.hom
          (isImmersion_of_isPullback B S hS sq hi) q iU' ψ
          (isPullback_of_comp_eq B S hS sq sq' ψ hψφ q hqp hqi)
          (isEtale_of_comp_eq B S hS ψ hφ hφ' hψφ) :=
  CategoryTheory.CompIsoCube.conj_comp
    (GA := fun A : AlgebraicSpaces B S hS => SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS A).O))
    (P := fun {A B'} (f : A ⟶ B') => gradedPull (X := smallEtaleRingedTopos B S hS A)
      (Y := smallEtaleRingedTopos B S hS B') (smallEtaleRingedToposHom B S hS f))
    (D := fun a b t h => gradedAlgebraPullbackCompIsoOfEq B S hS a b t h)
    p q p' hqp.symm _ _ _
    (conormalAlgebraEtaleRestrictionIso_comp B S hS p iU _ φ sq hφ p' iU' φ' sq' hφ' ψ hψφ q hqp
      hqi)
    (conormalAlgebraIsoConormalAlgebraOfImmersion B S hS hX hZ i hi).symm
    (conormalAlgebraIsoConormalAlgebraOfImmersion B S hS U.2 ZU.2 iU.hom
      (isImmersion_of_isPullback B S hS sq hi))
    (conormalAlgebraIsoConormalAlgebraOfImmersion B S hS U'.2 ZU'.2 iU'.hom
      (isImmersion_of_isPullback B S hS sq' hi))

end Immersion

end AlgebraicGeometry.Space

end
