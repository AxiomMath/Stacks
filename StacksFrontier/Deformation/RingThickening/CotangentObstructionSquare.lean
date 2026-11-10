module

public import StacksFrontier.Cotangent.BaseChangeComplexCounit
public import StacksFrontier.Deformation.RingThickening.CotangentObstructionCokernel

/-!
# The compatibility of the obstruction classes with the tower map

For ring maps `A' → A → B` this file proves that the cocycle descriptions of
`Ext¹_B(L_{B/A'}, N)` and `Ext¹_B(L_{A/A'} ⊗_A B, N)` turn the map
`Ext¹_B(NL_{B/A'}, N) → Ext¹_A(NL_{A/A'}, N)` of Lemma 0GPX (restriction along `A → B` followed by
precomposition with `NL_{A/A'} → NL_{B/A'}`) into precomposition with the functoriality map
`L_{A/A'} ⊗_A B → L_{B/A'}` of Tag 08PN, the first morphism of the fundamental triangle. This is
the step "for the equalities see Deformation Theory, Remark 0GPY and use that
`NL = τ_{≥ -1} L`" of the proof of Tag 08SP, part (1).

## Main results

* `Stacks.Cotangent.cotangentComplexToNaive_negOne_apply`: the map `L_{B/A} → NL_{B/A}` in degree
  `-1`, on a pure differential: `d f ↦ [d₀ f - d₁ f]`.
* `Stacks.Deformation.SquareZeroExtensionProblem.towerConormal_cotangentComplexToNaive`: the
  maps of Tags 08RB and 08PN are compatible in degree `-1`.
* `Stacks.Deformation.SquareZeroExtensionProblem.baseCocycleMap_comp_coneDesc`: the
  compatibility on cocycles.
* `Stacks.Deformation.SquareZeroExtensionProblem.baseClass_towerMap`: the compatibility.

## References

* [Stacks Project, Tag 08SP](https://stacks.math.columbia.edu/tag/08SP)
* [Stacks Project, Tag 0GPY](https://stacks.math.columbia.edu/tag/0GPY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped ChangeOfRings

universe u

namespace Stacks.Cotangent

open CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- **The map `L_{B/A} → NL_{B/A}` in degree `-1`, on a pure differential**: `d f ⊗ 1` goes to
the class of `d₀ f - d₁ f` in the conormal module of the canonical presentation `A[B] → B`. -/
theorem cotangentComplexToNaive_negOne_apply
    (q : (standardResolution.{u, u} A B).left.obj (op ⦋1⦌)) :
    (Algebra.Extension.naiveComplexXNegOneIso (naiveExtension.{u, u} A B)).hom
        ((cotangentComplexToNaive.{u, u} A B).f (-1)
          ((cotangentComplex_degreeIso.{u, u} A B 1).inv
            (cotangentTermDifferential.{u, u} A B (op ⦋1⦌) q))) =
      Algebra.Extension.Cotangent.map (standardResolutionExtensionZeroToNaive A B)
        (naiveCotangentComparison A B
          ((1 : B) ⊗ₜ KaehlerDifferential.D A
            (standardResolutionExtension.{u, u} A B 1).Ring q)) := by
  have h : (cotangentComplexToNaive.{u, u} A B).f (-1) =
      comparisonDegreeNegOne A B ≫
        Algebra.Extension.naiveComplexMapNegOne (standardResolutionExtensionZeroToNaive A B) := by
    rw [cotangentComplexToNaive, HomologicalComplex.comp_f, explicitNaiveComparison_f,
      comparisonComponent_negOne]
    rfl
  rw [h]
  simp only [comparisonDegreeNegOne, Algebra.Extension.naiveComplexMapNegOne,
    ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  rfl

/-- The pure differentials `1 ⊗ d p` span the term `B ⊗_{Pₙ} Ω_{Pₙ/A}` of the cotangent complex. -/
theorem span_cotangentTermDifferential (n : SimplexCategoryᵒᵖ) :
    Submodule.span (R := B) (M := (cotangentTerm.{u, u} A B n : Type u))
      (Set.range (cotangentTermDifferential.{u, u} A B n)) = ⊤ := by
  let : Module B (cotangentTerm.{u, u} A B n : Type u) := (cotangentTerm.{u, u} A B n).isModule
  let p := Submodule.span (R := B) (M := (cotangentTerm.{u, u} A B n : Type u))
    (Set.range (cotangentTermDifferential.{u, u} A B n))
  have h := cotangentTerm_hom_ext.{u, u} A B n
    (ModuleCat.ofHom (X := (cotangentTerm.{u, u} A B n : Type u)) p.mkQ) 0 fun q => by
    change p.mkQ _ = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨q, rfl⟩
  refine eq_top_iff.2 fun x _ => ?_
  have hx : (ModuleCat.ofHom (X := (cotangentTerm.{u, u} A B n : Type u)) p.mkQ).hom x = 0 :=
    congrArg (fun φ => φ.hom x) h
  rwa [ModuleCat.hom_ofHom, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx

end Stacks.Cotangent

namespace Stacks.Deformation.SquareZeroExtensionProblem

open CommAlgCat

variable (S : SquareZeroExtensionProblem.{u, u, u, u})

/-- The map `A → B` as a map of `A'`-algebras. -/
noncomputable abbrev towerAlgHom : CommAlgCat.of S.A' S.A →ₐ[S.A'] CommAlgCat.of S.A' S.B :=
  IsScalarTower.toAlgHom S.A' S.A S.B

/-- The commutative square `(1_{A'}, A → B)` of the tower, whose functoriality map is the first
morphism of the fundamental triangle. -/
noncomputable abbrev towerSquare :
    AlgebraSquare.{u, u, u} S.A' S.A' (CommAlgCat.of S.A' S.A) (CommAlgCat.of S.A' S.B) :=
  algebraSquareOfAlgHom (A := S.A') (A' := S.A') (B := CommAlgCat.of S.A' S.A)
    (B' := CommAlgCat.of S.A' S.B) S.towerAlgHom

/-- **In degree zero, the map of standard resolutions is the comparison of canonical
presentations**: on `P₀ = A'[A] → P₀ = A'[B]` it is `[a] ↦ [a]`, read through
`A'[A] → A'[B]`. -/
theorem standardResolutionZeroAlgEquiv_squareMap
    (p : (standardResolution.{u, u} S.A' (CommAlgCat.of S.A' S.A)).left.obj (op ⦋0⦌)) :
    standardResolutionZeroAlgEquiv.{u, u} S.A' (CommAlgCat.of S.A' S.B)
        (standardResolutionSquareMap.{u, u, u} S.towerSquare (op ⦋0⦌) p) =
      towerPolyHom S.A' S.A S.B (standardResolutionZeroAlgEquiv.{u, u} S.A'
        (CommAlgCat.of S.A' S.A) p) := by
  obtain ⟨q, rfl⟩ := (standardResolutionZeroAlgEquiv.{u, u} S.A'
    (CommAlgCat.of S.A' S.A)).symm.surjective p
  rw [AlgEquiv.apply_symm_apply]
  have h : ((standardResolutionZeroAlgEquiv.{u, u} S.A' (CommAlgCat.of S.A' S.B)).toRingHom.comp
      ((standardResolutionSquareMap.{u, u, u} S.towerSquare (op ⦋0⦌)).comp
        (standardResolutionZeroAlgEquiv.{u, u} S.A' (CommAlgCat.of S.A' S.A)).symm.toRingHom)) =
      (towerPolyHom S.A' S.A S.B).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun a => ?_) <;>
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        AlgEquiv.coe_toRingEquiv, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    · rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, standardResolutionSquareMap_algebraMap,
        AlgEquiv.commutes, AlgHom.commutes]
      rfl
    · rw [standardResolutionSquareMap_zero_X, AlgEquiv.apply_symm_apply, towerPolyHom_X]
      rfl
  exact RingHom.congr_fun h q

/-- **The compatibility in degree `-1`, on a pure differential.** For `f` in the degree-one term
of the standard resolution of `A` over `A'`, the class `[d₀ f - d₁ f]` in the conormal module of
`A'[A] → A`, pushed to that of `A'[B] → B`, is the class of `[d₀ u(f) - d₁ u(f)]`, `u` being the
map of standard resolutions. -/
theorem towerConormal_cotangentComplexToNaive_differential
    (p : (standardResolution.{u, u} S.A' (CommAlgCat.of S.A' S.A)).left.obj (op ⦋1⦌)) :
    towerConormal S.A' S.A S.B
        ((Algebra.Extension.naiveComplexXNegOneIso S.baseNaive).hom
          ((Cotangent.cotangentComplexToNaive.{u, u} S.A' (CommAlgCat.of S.A' S.A)).f (-1)
            ((cotangentComplex_degreeIso.{u, u} S.A' (CommAlgCat.of S.A' S.A) 1).inv
              (cotangentTermDifferential.{u, u} S.A' (CommAlgCat.of S.A' S.A) (op ⦋1⦌) p)))) =
      (Algebra.Extension.naiveComplexXNegOneIso S.towerNaive).hom
        ((Cotangent.cotangentComplexToNaive.{u, u} S.A' (CommAlgCat.of S.A' S.B)).f (-1)
          ((cotangentComplex_degreeIso.{u, u} S.A' (CommAlgCat.of S.A' S.B) 1).inv
            (cotangentTermDifferential.{u, u} S.A' (CommAlgCat.of S.A' S.B) (op ⦋1⦌)
              (standardResolutionSquareMap.{u, u, u} S.towerSquare (op ⦋1⦌) p)))) := by
  have h₁ := naiveCotangentComparison_tmul.{u, u} S.A' (CommAlgCat.of S.A' S.A) 1 p
  have h₂ := naiveCotangentComparison_tmul.{u, u} S.A' (CommAlgCat.of S.A' S.B) 1
    (standardResolutionSquareMap.{u, u, u} S.towerSquare (op ⦋1⦌) p)
  rw [Cotangent.cotangentComplexToNaive_negOne_apply,
    Cotangent.cotangentComplexToNaive_negOne_apply, h₁, h₂, one_smul, one_smul,
    Algebra.Extension.Cotangent.map_mk, Algebra.Extension.Cotangent.map_mk, towerConormal,
    Algebra.Extension.Cotangent.map_mk]
  congr 1
  apply Subtype.ext
  change towerPolyHom S.A' S.A S.B (standardResolutionZeroAlgEquiv.{u, u} S.A'
      (CommAlgCat.of S.A' S.A) (((standardResolutionExtensionFace _ _ 0 0).subToKer
        (standardResolutionExtensionFace _ _ 0 1) p).val)) =
    standardResolutionZeroAlgEquiv.{u, u} S.A' (CommAlgCat.of S.A' S.B)
      (((standardResolutionExtensionFace _ _ 0 0).subToKer
        (standardResolutionExtensionFace _ _ 0 1)
          (standardResolutionSquareMap.{u, u, u} S.towerSquare (op ⦋1⦌) p)).val)
  have h₃ := naiveCotangentComparison_subToKer_coe.{u, u} S.A' (CommAlgCat.of S.A' S.A) p
  have h₄ := naiveCotangentComparison_subToKer_coe.{u, u} S.A' (CommAlgCat.of S.A' S.B)
    (standardResolutionSquareMap.{u, u, u} S.towerSquare (op ⦋1⦌) p)
  rw [h₃, h₄, map_sub,
    map_sub, map_sub, ← standardResolutionSquareMap_δ, ← standardResolutionSquareMap_δ,
    S.standardResolutionZeroAlgEquiv_squareMap, S.standardResolutionZeroAlgEquiv_squareMap]

/-- **The compatibility in degree `-1`.** The class in `J_A/J_A²` of an element of `L_{A/A'}` in
degree `-1`, pushed to `J_B/J_B²`, is the class of its image in `L_{B/A'}` under the map of
Tag 08PN. -/
theorem towerConormal_cotangentComplexToNaive
    (x : (CommAlgCat.cotangentComplex.{u, u} S.A' (CommAlgCat.of S.A' S.A)).X (-1)) :
    towerConormal S.A' S.A S.B
        ((Algebra.Extension.naiveComplexXNegOneIso S.baseNaive).hom
          ((Cotangent.cotangentComplexToNaive.{u, u} S.A' (CommAlgCat.of S.A' S.A)).f (-1) x)) =
      (Algebra.Extension.naiveComplexXNegOneIso S.towerNaive).hom
        ((Cotangent.cotangentComplexToNaive.{u, u} S.A' (CommAlgCat.of S.A' S.B)).f (-1)
          ((squareCotangentComplexMap.{u, u, u} S.towerSquare).f (-1) x)) := by
  obtain ⟨y, rfl⟩ : ∃ y, (cotangentComplex_degreeIso.{u, u} S.A' (CommAlgCat.of S.A' S.A) 1).inv
      y = x := ⟨(cotangentComplex_degreeIso.{u, u} S.A' (CommAlgCat.of S.A' S.A) 1).hom x,
        Iso.hom_inv_id_apply _ _⟩
  let φ₁ : (cotangentTerm.{u, u} S.A' (CommAlgCat.of S.A' S.A) (op ⦋1⦌) : Type u) →+
      S.towerNaive.Cotangent :=
    (towerConormal S.A' S.A S.B).toAddMonoidHom.comp
      ((Algebra.Extension.naiveComplexXNegOneIso S.baseNaive).hom.hom.toAddMonoidHom.comp
        (((Cotangent.cotangentComplexToNaive.{u, u} S.A'
          (CommAlgCat.of S.A' S.A)).f (-1)).hom.toAddMonoidHom.comp
          (cotangentComplex_degreeIso.{u, u} S.A' (CommAlgCat.of S.A' S.A)
            1).inv.hom.toAddMonoidHom))
  let φ₂ : (cotangentTerm.{u, u} S.A' (CommAlgCat.of S.A' S.A) (op ⦋1⦌) : Type u) →+
      S.towerNaive.Cotangent :=
    (Algebra.Extension.naiveComplexXNegOneIso S.towerNaive).hom.hom.toAddMonoidHom.comp
      (((Cotangent.cotangentComplexToNaive.{u, u} S.A' (CommAlgCat.of S.A' S.B)).f
        (-1)).hom.toAddMonoidHom.comp
        (((squareCotangentComplexMap.{u, u, u} S.towerSquare).f (-1)).hom.toAddMonoidHom.comp
          (cotangentComplex_degreeIso.{u, u} S.A' (CommAlgCat.of S.A' S.A)
            1).inv.hom.toAddMonoidHom))
  suffices h : φ₁ = φ₂ from DFunLike.congr_fun h y
  have hsmul₁ : ∀ (a : CommAlgCat.of S.A' S.A) z, φ₁ (a • z) = algebraMap S.A S.B a • φ₁ z := by
    intro a z
    change towerConormal S.A' S.A S.B ((Algebra.Extension.naiveComplexXNegOneIso
        S.baseNaive).hom.hom (((Cotangent.cotangentComplexToNaive.{u, u} S.A'
          (CommAlgCat.of S.A' S.A)).f (-1)).hom
        ((cotangentComplex_degreeIso.{u, u} S.A' (CommAlgCat.of S.A' S.A) 1).inv.hom
          (a • z)))) = _
    rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul,
      algebraMap_smul]
    rfl
  have hsmul₂ : ∀ (a : CommAlgCat.of S.A' S.A) z, φ₂ (a • z) = algebraMap S.A S.B a • φ₂ z := by
    intro a z
    change (Algebra.Extension.naiveComplexXNegOneIso S.towerNaive).hom.hom
        (((Cotangent.cotangentComplexToNaive.{u, u} S.A' (CommAlgCat.of S.A' S.B)).f (-1)).hom
          (((squareCotangentComplexMap.{u, u, u} S.towerSquare).f (-1)).hom
            ((cotangentComplex_degreeIso.{u, u} S.A' (CommAlgCat.of S.A' S.A) 1).inv.hom
              (a • z)))) = _
    rw [LinearMap.map_smul, LinearMap.map_smul]
    change (Algebra.Extension.naiveComplexXNegOneIso S.towerNaive).hom.hom
        (((Cotangent.cotangentComplexToNaive.{u, u} S.A' (CommAlgCat.of S.A' S.B)).f (-1)).hom
          (S.towerSquare.map a • (show ((CommAlgCat.cotangentComplex.{u, u} S.A'
            (CommAlgCat.of S.A' S.B)).X (-1) : Type u) from
              ((squareCotangentComplexMap.{u, u, u} S.towerSquare).f (-1)).hom
                ((cotangentComplex_degreeIso.{u, u} S.A' (CommAlgCat.of S.A' S.A) 1).inv.hom
                  z)))) = _
    rw [LinearMap.map_smul, LinearMap.map_smul]
    rfl
  have hgen : ∀ p, φ₁ (cotangentTermDifferential.{u, u} S.A' (CommAlgCat.of S.A' S.A)
      (op ⦋1⦌) p) = φ₂ (cotangentTermDifferential.{u, u} S.A' (CommAlgCat.of S.A' S.A)
        (op ⦋1⦌) p) := by
    intro p
    have hd := squareCotangentComplexMap_differential.{u, u, u} S.towerSquare 1 p
    have hd' : (squareCotangentComplexMap.{u, u, u} S.towerSquare).f (-1)
        ((cotangentComplex_degreeIso.{u, u} S.A' (CommAlgCat.of S.A' S.A) 1).inv
          (cotangentTermDifferential.{u, u} S.A' (CommAlgCat.of S.A' S.A) (op ⦋1⦌) p)) =
        (cotangentComplex_degreeIso.{u, u} S.A' (CommAlgCat.of S.A' S.B) 1).inv
          (cotangentTermDifferential.{u, u} S.A' (CommAlgCat.of S.A' S.B) (op ⦋1⦌)
            (standardResolutionSquareMap.{u, u, u} S.towerSquare (op ⦋1⦌) p)) := by
      rw [← hd]
      exact (Iso.hom_inv_id_apply
        (cotangentComplex_degreeIso.{u, u} S.A' (CommAlgCat.of S.A' S.B) 1) _).symm
    change towerConormal S.A' S.A S.B _ = (Algebra.Extension.naiveComplexXNegOneIso
      S.towerNaive).hom ((Cotangent.cotangentComplexToNaive.{u, u} S.A'
        (CommAlgCat.of S.A' S.B)).f (-1) ((squareCotangentComplexMap.{u, u, u}
          S.towerSquare).f (-1) ((cotangentComplex_degreeIso.{u, u} S.A'
            (CommAlgCat.of S.A' S.A) 1).inv (cotangentTermDifferential.{u, u} S.A'
              (CommAlgCat.of S.A' S.A) (op ⦋1⦌) p))))
    rw [hd']
    exact S.towerConormal_cotangentComplexToNaive_differential p
  refine AddMonoidHom.ext fun z => ?_
  have hz : z ∈ Submodule.span (R := CommAlgCat.of S.A' S.A)
      (M := (cotangentTerm.{u, u} S.A' (CommAlgCat.of S.A' S.A) (op ⦋1⦌) : Type u))
      (Set.range (cotangentTermDifferential.{u, u} S.A' (CommAlgCat.of S.A' S.A) (op ⦋1⦌))) := by
    rw [Cotangent.span_cotangentTermDifferential]
    trivial
  induction hz using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨p, rfl⟩ := hw
      exact hgen p
  | zero => rw [map_zero, map_zero]
  | add w w' _ _ hw hw' => rw [map_add, map_add, hw, hw']
  | smul a w _ hw => rw [hsmul₁, hsmul₂, hw]

/-- **The two liftings agree on a base change**: if a `B`-linear functional `k` on `B ⊗_A M`
restricts on `1 ⊗ M` to the `A`-linear functional `h`, then `h` and `k` give the same morphism
out of the lifted `B ⊗_A M`. -/
theorem baseHomEquiv_eq_towerHomEquiv (M : ModuleCat.{u} S.A) (h : M →ₗ[S.A] S.N)
    (k : S.baseChangeFunctor.obj M →ₗ[S.B] S.N)
    (hk : ∀ x : M, k ((1 : S.B) ⊗ₜ[S.A, algebraMap S.A S.B] x) = h x) :
    S.baseHomEquiv M h = S.towerHomEquiv (S.baseChangeFunctor.obj M) k := by
  change (S.liftBIso _).hom ≫ ((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap S.A S.B)).homEquiv M _).symm (S.toRestrictedKernelEquiv M h) =
    (S.liftBIso _).hom ≫ S.toLiftedKernelEquiv _ k
  congr 1
  refine ModuleCat.ExtendScalars.hom_ext fun x => ?_
  change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (algebraMap S.A S.B)
    ((S.toRestrictedKernelEquiv M) h) ((1 : S.B) ⊗ₜ[S.A, algebraMap S.A S.B] x) =
      ULift.up (k ((1 : S.B) ⊗ₜ[S.A, algebraMap S.A S.B] x))
  rw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_tmul, one_smul, hk]
  rfl

/-- `baseHomEquiv_eq_towerHomEquiv`, for composites. -/
theorem liftBaseChange_map_comp_baseHomEquiv {M₁ M₀ : ModuleCat.{u} S.A} (d : M₁ ⟶ M₀)
    (g : M₀ →ₗ[S.A] S.N) {M : ModuleCat.{u} S.B} (e : S.baseChangeFunctor.obj M₁ ⟶ M)
    (k : M →ₗ[S.B] S.N)
    (hk : ∀ x : M₁, k (e ((1 : S.B) ⊗ₜ[S.A, algebraMap S.A S.B] x)) = g (d x)) :
    S.liftBaseChange.map d ≫ S.baseHomEquiv M₀ g = S.liftB.map e ≫ S.towerHomEquiv M k := by
  rw [← S.baseHomEquiv_comp, ← S.towerHomEquiv_comp]
  exact S.baseHomEquiv_eq_towerHomEquiv M₁ _ _ hk

/-- The map of Tag 08PN for the tower, in degree `-1`, on `1 ⊗ x`: it is the functoriality map
of the standard resolutions. -/
theorem cotangentExtendScalarsComplexMap_tower_one_tmul
    (x : (CommAlgCat.cotangentComplex.{u, u} S.A' (CommAlgCat.of S.A' S.A)).X (-1)) :
    (cotangentExtendScalarsComplexMap (A := S.A') (A' := S.A') (B := CommAlgCat.of S.A' S.A)
      (B' := CommAlgCat.of S.A' S.B) S.towerAlgHom).f (-1)
        ((1 : S.B) ⊗ₜ[S.A, algebraMap S.A S.B] x) =
      (squareCotangentComplexMap.{u, u, u} S.towerSquare).f (-1) x := by
  rw [cotangentExtendScalarsComplexMap_eq_counit]
  exact one_smul (CommAlgCat.of S.A' S.B) (show ((CommAlgCat.cotangentComplex.{u, u} S.A'
    (CommAlgCat.of S.A' S.B)).X (-1) : Type u) from
      (squareCotangentComplexMap.{u, u, u} S.towerSquare).f (-1) x)

/-- The functoriality map `L_{A/A'} ⊗_A B → L_{B/A'}` of Tag 08PN for the tower, lifted to the
module universe of `cotangentExt`: the first morphism of the fundamental triangle, on
complexes. -/
noncomputable abbrev towerComplexMap :
    (S.liftBaseChange.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CommAlgCat.cotangentComplex.{u, u} S.A' (CommAlgCat.of S.A' S.A)) ⟶
      (S.liftB.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CommAlgCat.cotangentComplex.{u, u} S.A' (CommAlgCat.of S.A' S.B)) :=
  (S.liftB.mapHomologicalComplex (ComplexShape.up ℤ)).map
    (cotangentExtendScalarsComplexMap (A := S.A') (A' := S.A') (B := CommAlgCat.of S.A' S.A)
      (B' := CommAlgCat.of S.A' S.B) S.towerAlgHom)

/-- **The cocycles are compatible with the tower map, on complexes.** The cocycle on
`L_{A/A'} ⊗_A B` of the pullback `J_A/J_A² → J_B/J_B² → N` of a conormal functional `f` is the
composite of the map of Tag 08PN with the cocycle of `f` on `L_{B/A'}`. -/
theorem baseCocycleMap_comp_coneDesc (f : S.towerNaive.Cotangent →ₗ[S.B] S.N) :
    S.baseCocycleMap ≫ NaiveCotangent.ExtCokernelLinear.coneDesc S.baseDifferential
        (S.baseHomEquiv (ModuleCat.of S.A S.baseNaive.Cotangent)
          (towerConormalPullback S.A' S.A S.B f)) =
      S.towerComplexMap ≫ S.towerCocycleMap ≫
        NaiveCotangent.ExtCokernelLinear.coneDesc S.towerDifferential
          (S.towerHomEquiv (ModuleCat.of S.B S.towerNaive.Cotangent) f) := by
  ext i : 1
  by_cases hi : i = -1
  swap
  · exact (NaiveCotangent.ExtCokernelLinear.isZero_shiftSingle _ hi).eq_of_tgt _ _
  subst hi
  have h₁ := naiveComplexCofiberIso_hom_coneDesc_f_negOne S.liftBaseChange S.baseNaive
    (S.baseHomEquiv (ModuleCat.of S.A S.baseNaive.Cotangent)
      (towerConormalPullback S.A' S.A S.B f))
  have h₂ := naiveComplexCofiberIso_hom_coneDesc_f_negOne S.liftB S.towerNaive
    (S.towerHomEquiv (ModuleCat.of S.B S.towerNaive.Cotangent) f)
  rw [baseCocycleMap, towerCocycleMap, Category.assoc, Category.assoc, HomologicalComplex.comp_f,
    h₁, HomologicalComplex.comp_f, HomologicalComplex.comp_f, h₂]
  have key : ((S.liftBaseChange.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (Cotangent.cotangentComplexToNaive.{u, u} S.A' (CommAlgCat.of S.A' S.A))).f (-1) ≫
        (naiveComplexConeIsoNegOne S.liftBaseChange S.baseNaive).inv ≫
          S.baseHomEquiv (ModuleCat.of S.A S.baseNaive.Cotangent)
            (towerConormalPullback S.A' S.A S.B f) =
      S.towerComplexMap.f (-1) ≫ ((S.liftB.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (Cotangent.cotangentComplexToNaive.{u, u} S.A' (CommAlgCat.of S.A' S.B))).f (-1) ≫
        (naiveComplexConeIsoNegOne S.liftB S.towerNaive).inv ≫
          S.towerHomEquiv (ModuleCat.of S.B S.towerNaive.Cotangent) f := by
    change S.liftBaseChange.map ((Cotangent.cotangentComplexToNaive.{u, u} S.A'
          (CommAlgCat.of S.A' S.A)).f (-1)) ≫
        S.liftBaseChange.map (Algebra.Extension.naiveComplexXNegOneIso S.baseNaive).hom ≫
          S.baseHomEquiv (ModuleCat.of S.A S.baseNaive.Cotangent)
            (towerConormalPullback S.A' S.A S.B f) =
      S.liftB.map ((cotangentExtendScalarsComplexMap (A := S.A') (A' := S.A')
          (B := CommAlgCat.of S.A' S.A) (B' := CommAlgCat.of S.A' S.B) S.towerAlgHom).f (-1)) ≫
        S.liftB.map ((Cotangent.cotangentComplexToNaive.{u, u} S.A'
          (CommAlgCat.of S.A' S.B)).f (-1)) ≫
          S.liftB.map (Algebra.Extension.naiveComplexXNegOneIso S.towerNaive).hom ≫
            S.towerHomEquiv (ModuleCat.of S.B S.towerNaive.Cotangent) f
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
    refine S.liftBaseChange_map_comp_baseHomEquiv _ _ _ _ fun x => ?_
    change f ((Algebra.Extension.naiveComplexXNegOneIso S.towerNaive).hom
        ((Cotangent.cotangentComplexToNaive.{u, u} S.A' (CommAlgCat.of S.A' S.B)).f (-1)
          ((cotangentExtendScalarsComplexMap (A := S.A') (A' := S.A')
            (B := CommAlgCat.of S.A' S.A) (B' := CommAlgCat.of S.A' S.B) S.towerAlgHom).f (-1)
              ((1 : S.B) ⊗ₜ[S.A, algebraMap S.A S.B] x)))) =
      f (towerConormal S.A' S.A S.B ((Algebra.Extension.naiveComplexXNegOneIso S.baseNaive).hom
        ((Cotangent.cotangentComplexToNaive.{u, u} S.A' (CommAlgCat.of S.A' S.A)).f (-1) x)))
    rw [S.cotangentExtendScalarsComplexMap_tower_one_tmul, S.towerConormal_cotangentComplexToNaive]
  rw [reassoc_of% key]

attribute [local instance high] HasDerivedCategory.standard

/-- **The cocycle class of a conormal functional on `J_B/J_B²`.** -/
theorem towerClass_eq (y : naiveCotangentExtOne S.A' S.B S.N)
    (f : S.towerNaive.Cotangent →ₗ[S.B] S.N)
    (hf : extCokernelIso S.A' S.B S.N y = Submodule.Quotient.mk f) :
    S.towerClass y = DerivedCategory.Q.map (S.towerCocycleMap ≫
        NaiveCotangent.ExtCokernelLinear.coneDesc S.towerDifferential
          (S.towerHomEquiv (ModuleCat.of S.B S.towerNaive.Cotangent) f)) ≫
      (NaiveCotangent.ExtCokernelLinear.shiftSingleQIso
        (liftedKernelModule.{u, u, u, u} S)).hom := by
  rw [Functor.map_comp, Category.assoc]
  change DerivedCategory.Q.map S.towerCocycleMap ≫
    NaiveCotangent.ExtCokernelLinear.cokernelExtOneEquiv S.towerDifferential
      (S.towerCokernelEquiv (extCokernelIso S.A' S.B S.N y)) = _
  rw [hf]
  rfl

/-- **The cocycle class of a conormal functional on `J_A/J_A²`.** -/
theorem baseClass_eq (y : naiveCotangentExtOne S.A' S.A S.N)
    (f : S.baseNaive.Cotangent →ₗ[S.A] S.N)
    (hf : extCokernelIso S.A' S.A S.N y = Submodule.Quotient.mk f) :
    S.baseClass y = DerivedCategory.Q.map (S.baseCocycleMap ≫
        NaiveCotangent.ExtCokernelLinear.coneDesc S.baseDifferential
          (S.baseHomEquiv (ModuleCat.of S.A S.baseNaive.Cotangent) f)) ≫
      (NaiveCotangent.ExtCokernelLinear.shiftSingleQIso
        (liftedKernelModule.{u, u, u, u} S)).hom := by
  rw [Functor.map_comp, Category.assoc]
  change DerivedCategory.Q.map S.baseCocycleMap ≫
    NaiveCotangent.ExtCokernelLinear.cokernelExtOneEquiv S.baseDifferential
      (S.baseCokernelEquiv (extCokernelIso S.A' S.A S.N y)) = _
  rw [hf]
  rfl

/-- **The tower map of Lemma 0GPX is precomposition with the map of Tag 08PN.** Under the
cocycle descriptions, the map `Ext¹_B(NL_{B/A'}, N) → Ext¹_A(NL_{A/A'}, N)` becomes
precomposition with `L_{A/A'} ⊗_A B → L_{B/A'}`. -/
theorem baseClass_towerMap (y : naiveCotangentExtOne S.A' S.B S.N) :
    S.baseClass (naiveCotangentExtOneTowerMap S.A' S.A S.B y) =
      DerivedCategory.Q.map S.towerComplexMap ≫ S.towerClass y := by
  obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective _ (extCokernelIso S.A' S.B S.N y)
  have hb : extCokernelIso S.A' S.A S.N (naiveCotangentExtOneTowerMap S.A' S.A S.B y) =
      Submodule.Quotient.mk (towerConormalPullback S.A' S.A S.B f) := by
    change extCokernelIso S.A' S.A S.N ((extCokernelIso S.A' S.A S.N).symm
      (conormalCokernelPullback S.A' S.A S.B (extCokernelIso S.A' S.B S.N y))) = _
    rw [AddEquiv.apply_symm_apply, ← hf]
    rfl
  rw [S.baseClass_eq _ _ hb, S.towerClass_eq y f hf.symm, ← Category.assoc, ← Functor.map_comp,
    S.baseCocycleMap_comp_coneDesc]

end Stacks.Deformation.SquareZeroExtensionProblem

end
