module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsShortExactFree
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentImmersionDegreeZero
public import StacksFrontier.Cotangent.SheavesOfRings.BaseChangedCotangentDerived
public import StacksFrontier.Cotangent.SheavesOfRings.NaiveComparisonCanonical
public import StacksFrontier.Cotangent.SheavesOfRings.PullbackCotangentComplex
public import StacksFrontier.Deformation.ToposThickening.CotangentObstructionConormal

/-!
# Homology of a short complex under a left adjoint, and of a base-changed cotangent complex

Let `F ⊣ R` be an adjunction between abelian categories and let `S` be a short complex on the
source side whose left homology `F` preserves. A morphism `m : F(S) ⟶ T` of short complexes has
a transpose `S ⟶ R(T)`, and this file proves that the two induced maps on homology are
transposes of one another, through the comparisons `H(F S) ≅ F(H S)` and `H(R T) ≅ R(H T)`.

It also records when a right exact functor preserves the left homology of a short complex
`X₁ ⟶ X₂ ⟶ X₃` with epimorphic second map: exactly when it keeps
`0 ⟶ ker ⟶ X₂ ⟶ X₃ ⟶ 0` short exact.

The case of interest is extension of scalars along `h : B ⟶ D` applied to the cotangent complex
`L_{B/A}` of a locally surjective homomorphism `A ⟶ B` of sheaves of commutative rings. There
`H⁰(L_{B/A}) = Ω_{B/A} = 0`, the last term `L⁰` is flat, so extension of scalars keeps the kernel
sequence of the differential `L^{-1} ⟶ L⁰` short exact (Stacks 03EX), and
`H^{-1}(L_{B/A} ⊗_B D) = H^{-1}(L_{B/A}) ⊗_B D` with `H^{-1}(L_{B/A}) = I/I²`.

## Main results

* `CategoryTheory.ShortComplex.homologyπ_comp_homologyMapIsoOfLeftHomologyData_hom`: the
  comparison `H(F S) ≅ F(H S)` is compatible with the projections from the cycles.
* `CategoryTheory.ShortComplex.homEquiv_homologyMapIso_inv_comp_homologyMap`: the transpose of
  the map on homology induced by `m` is the map on homology induced by the transpose of `m`.
* `CategoryTheory.ShortComplex.LeftHomologyData.isPreservedBy_of_shortExact`: a right exact
  functor keeping the kernel sequence of the second map short exact preserves the left homology.
* `CategoryTheory.Sheaf.cotangentComplexHomologyNegOneIsoConormal`: `H^{-1}(L_{B/A}) = I/I²`.
* `CategoryTheory.Sheaf.extendScalarsCotangentHomologyNegOneIso`:
  `H^{-1}(L_{B/A} ⊗_B D) = H^{-1}(L_{B/A}) ⊗_B D`.
* `CategoryTheory.Sheaf.isLE_Q_obj_baseChangedCotangentComplex`: `L_{B/A} ⊗_B D` lies in degrees
  `≤ -1`.

## References

* [Stacks Project, Tag 03EX](https://stacks.math.columbia.edu/tag/03EX)
* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

variable {𝒜 ℬ : Type*} [Category* 𝒜] [Category* ℬ] [Abelian 𝒜] [Abelian ℬ]

variable (F : 𝒜 ⥤ ℬ) [F.PreservesZeroMorphisms] {S : ShortComplex 𝒜} (hl : S.LeftHomologyData)
  [hl.IsPreservedBy F]

/-- The comparison `Z(F S) ≅ F(Z S)` of cycles, read through a left homology data of `S`
preserved by `F`. -/
noncomputable def cyclesMapIsoOfLeftHomologyData : (S.map F).cycles ≅ F.obj S.cycles :=
  (hl.map F).cyclesIso ≪≫ F.mapIso hl.cyclesIso.symm

/-- The comparison `H(F S) ≅ F(H S)` of homology, read through a left homology data of `S`
preserved by `F`. -/
noncomputable def homologyMapIsoOfLeftHomologyData : (S.map F).homology ≅ F.obj S.homology :=
  (hl.map F).homologyIso ≪≫ F.mapIso hl.homologyIso.symm

/-- The comparison of cycles is compatible with the inclusions of the cycles. -/
@[reassoc]
theorem cyclesMapIsoOfLeftHomologyData_hom_comp_map_iCycles :
    (cyclesMapIsoOfLeftHomologyData F hl).hom ≫ F.map S.iCycles = (S.map F).iCycles := by
  change ((hl.map F).cyclesIso.hom ≫ F.map hl.cyclesIso.inv) ≫ F.map S.iCycles = _
  exact (Category.assoc _ _ _).trans ((congrArg ((hl.map F).cyclesIso.hom ≫ ·)
    ((F.map_comp _ _).symm.trans (congrArg F.map hl.cyclesIso_inv_comp_iCycles))).trans
      (hl.map F).cyclesIso_hom_comp_i)

/-- The comparison of homology is compatible with the projections from the cycles. -/
@[reassoc]
theorem homologyπ_comp_homologyMapIsoOfLeftHomologyData_hom :
    (S.map F).homologyπ ≫ (homologyMapIsoOfLeftHomologyData F hl).hom =
      (cyclesMapIsoOfLeftHomologyData F hl).hom ≫ F.map S.homologyπ := by
  change (S.map F).homologyπ ≫ (hl.map F).homologyIso.hom ≫ F.map hl.homologyIso.inv =
    ((hl.map F).cyclesIso.hom ≫ F.map hl.cyclesIso.inv) ≫ F.map S.homologyπ
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ F.map hl.homologyIso.inv)
    (hl.map F).homologyπ_comp_homologyIso_hom).trans ((Category.assoc _ _ _).trans
      ((congrArg ((hl.map F).cyclesIso.hom ≫ ·) ((F.map_comp _ _).symm.trans
        ((congrArg F.map hl.π_comp_homologyIso_inv).trans (F.map_comp _ _)))).trans
          (Category.assoc _ _ _).symm)))

/-- **The transpose of a map on homology is the map on homology of the transpose.** For an
adjunction `F ⊣ R`, a morphism `m : F(S) ⟶ T` and a morphism `m' : S ⟶ R(T)` whose middle
component is the transpose of that of `m`, the transpose of `H(m) : F(H S) ⟶ H(T)` is
`H(m') : H(S) ⟶ R(H T)`, through the comparisons of homology with `F` and with `R`. -/
theorem homEquiv_homologyMapIso_inv_comp_homologyMap {R : ℬ ⥤ 𝒜} [R.PreservesZeroMorphisms]
    (adj : F ⊣ R) {T : ShortComplex ℬ} (hr : T.LeftHomologyData) [hr.IsPreservedBy R]
    (m : S.map F ⟶ T) (m' : S ⟶ T.map R) (hm : m'.τ₂ = adj.homEquiv _ _ m.τ₂) :
    adj.homEquiv _ _ ((homologyMapIsoOfLeftHomologyData F hl).inv ≫ homologyMap m) =
      homologyMap m' ≫ (homologyMapIsoOfLeftHomologyData R hr).hom := by
  have : Mono (R.map T.iCycles) := by
    have := adj.rightAdjoint_preservesLimits
    infer_instance
  have hπ : F.map S.homologyπ ≫ (homologyMapIsoOfLeftHomologyData F hl).inv =
      (cyclesMapIsoOfLeftHomologyData F hl).inv ≫ (S.map F).homologyπ := by
    rw [Iso.comp_inv_eq, Category.assoc, homologyπ_comp_homologyMapIsoOfLeftHomologyData_hom,
      Iso.inv_hom_id_assoc]
  have hi : (cyclesMapIsoOfLeftHomologyData F hl).inv ≫ (S.map F).iCycles = F.map S.iCycles := by
    rw [Iso.inv_comp_eq, cyclesMapIsoOfLeftHomologyData_hom_comp_map_iCycles]
  have key : adj.homEquiv _ _ ((cyclesMapIsoOfLeftHomologyData F hl).inv ≫ cyclesMap m) =
      cyclesMap m' ≫ (cyclesMapIsoOfLeftHomologyData R hr).hom := by
    rw [← cancel_mono (R.map T.iCycles), ← Adjunction.homEquiv_naturality_right, Category.assoc,
      Category.assoc, cyclesMapIsoOfLeftHomologyData_hom_comp_map_iCycles, cyclesMap_i,
      cyclesMap_i, ← Category.assoc, hi, Adjunction.homEquiv_naturality_left, hm]
  rw [← cancel_epi S.homologyπ, ← Adjunction.homEquiv_naturality_left, ← Category.assoc, hπ,
    Category.assoc, homologyπ_naturality, ← Category.assoc,
    Adjunction.homEquiv_naturality_right, key, homologyπ_naturality_assoc,
    homologyπ_comp_homologyMapIsoOfLeftHomologyData_hom, Category.assoc]

/-- The comparison of homology with `F` is natural. -/
theorem homologyMap_map_comp_homologyMapIsoOfLeftHomologyData_hom {S₂ : ShortComplex 𝒜}
    (hl₂ : S₂.LeftHomologyData) [hl₂.IsPreservedBy F] (φ : S ⟶ S₂) :
    homologyMap (F.mapShortComplex.map φ) ≫ (homologyMapIsoOfLeftHomologyData F hl₂).hom =
      (homologyMapIsoOfLeftHomologyData F hl).hom ≫ F.map (homologyMap φ) := by
  have : Mono (F.map S₂.iCycles) := by
    rw [(Iso.eq_inv_comp _).2 (cyclesMapIsoOfLeftHomologyData_hom_comp_map_iCycles F hl₂)]
    infer_instance
  rw [← cancel_epi (S.map F).homologyπ, homologyπ_naturality_assoc]
  change cyclesMap (F.mapShortComplex.map φ) ≫ (S₂.map F).homologyπ ≫ _ = _
  rw [homologyπ_comp_homologyMapIsoOfLeftHomologyData_hom,
    homologyπ_comp_homologyMapIsoOfLeftHomologyData_hom_assoc, ← F.map_comp,
    homologyπ_naturality, F.map_comp, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono (F.map S₂.iCycles), Category.assoc,
    cyclesMapIsoOfLeftHomologyData_hom_comp_map_iCycles]
  refine (cyclesMap_i (F.mapShortComplex.map φ)).trans ?_
  rw [Category.assoc, ← F.map_comp, cyclesMap_i, F.map_comp, ← Category.assoc,
    cyclesMapIsoOfLeftHomologyData_hom_comp_map_iCycles]
  rfl

/-- **A right exact functor preserves the left homology of `X₁ ⟶ X₂ ⟶ X₃` when it keeps the
kernel sequence of `X₂ ⟶ X₃` short exact.** -/
theorem LeftHomologyData.isPreservedBy_of_shortExact {S : ShortComplex 𝒜} (h : S.LeftHomologyData)
    (F : 𝒜 ⥤ ℬ) [F.PreservesZeroMorphisms] [PreservesColimitsOfShape WalkingParallelPair F]
    (hS : ((ShortComplex.mk (kernel.ι S.g) S.g (kernel.condition _)).map F).ShortExact) :
    h.IsPreservedBy F where
  g := preservesLimit_of_preserves_limit_cone (kernelIsKernel S.g)
    ((isLimitMapConeForkEquiv' F (kernel.condition S.g)).symm hS.fIsKernel)
  f' := inferInstance

end CategoryTheory.ShortComplex

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B D : Sheaf J CommRingCat.{max u v w}} (g : A ⟶ B) (h : B ⟶ D)
  [Presheaf.IsLocallySurjective J g.hom]

/-- A cochain complex with vanishing degree `1` is exact at `0` iff its differential into degree
`0` is an epimorphism. -/
private theorem exactAt_zero_iff_epi_d_negOne {M : Type*} [Category* M] [Abelian M]
    (K : CochainComplex M ℤ) (h : IsZero (K.X 1)) : K.ExactAt 0 ↔ Epi (K.d (-1) 0) := by
  rw [HomologicalComplex.exactAt_iff' _ (-1) 0 1 (by simp) (by simp)]
  exact ShortComplex.exact_iff_epi _ (h.eq_of_tgt _ _)

/-- **`H⁰(L_{B/A}) = 0` for a locally surjective `A ⟶ B`**: it is `H⁰(NL_{B/A}) = Ω_{B/A}`. -/
theorem isZero_cotangentComplex_homology_zero :
    IsZero ((cotangentComplex.{u, v, w} J g).homology 0) := by
  have := canonicalNaiveComparison_isIso_homologyMap J g 0 (by decide)
  exact (Stacks.NaiveCotangentDegreeZero.isZero_homology_zero_naiveCotangentComplex.{v, u,
    max u v w, u} J A B g).of_iso
      (asIso (HomologicalComplex.homologyMap (canonicalNaiveComparison J g) 0))

/-- **`H^{-1}(L_{B/A}) = I/I²`** for a locally surjective `A ⟶ B` with kernel `I`. -/
noncomputable def cotangentComplexHomologyNegOneIsoConormal
    [J.WEqualsLocallyBijective CommRingCat.{max u v w}] :
    (cotangentComplex.{u, v, w} J g).homology (-1) ≅
      Stacks.Sites.Conormal.conormalSheaf.{v, u, max u v w, u} J A B g :=
  haveI := canonicalNaiveComparison_isIso_homologyMap J g (-1) le_rfl
  asIso (HomologicalComplex.homologyMap (canonicalNaiveComparison J g) (-1)) ≪≫
    Stacks.SheafOfModules.naiveCotangentHomologyNegOneIsoConormal.{v, u, max u v w, u} J A B g

/-- The differential of `L_{B/A}` out of degree `-1` is an epimorphism for a locally surjective
`A ⟶ B`, since `H⁰(L_{B/A}) = 0`. -/
theorem epi_cotangentComplex_d_negOne_zero : Epi ((cotangentComplex.{u, v, w} J g).d (-1) 0) := by
  exact (exactAt_zero_iff_epi_d_negOne _ (cotangentComplex_isZero_pos.{u, v, w} J g 1
    (by decide))).1 ((HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      (isZero_cotangentComplex_homology_zero J g))

/-- The kernel sequence `0 ⟶ Z^{-1} ⟶ L^{-1} ⟶ L⁰ ⟶ 0` of `L_{B/A}`, for a locally surjective
`A ⟶ B`. -/
theorem shortExact_cotangentComplex_kernelSequence :
    (ShortComplex.mk (kernel.ι ((cotangentComplex.{u, v, w} J g).sc (-1)).g)
      ((cotangentComplex.{u, v, w} J g).sc (-1)).g (kernel.condition _)).ShortExact := by
  have : Epi ((cotangentComplex.{u, v, w} J g).sc (-1)).g := by
    change Epi ((cotangentComplex.{u, v, w} J g).d (-1) ((ComplexShape.up ℤ).next (-1)))
    rw [CochainComplex.next]
    exact epi_cotangentComplex_d_negOne_zero J g
  exact { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _) }

/-- The left homology data of `L_{B/A}` in degree `-1`. -/
noncomputable abbrev cotangentNegOneData :
    ((cotangentComplex.{u, v, w} J g).sc (-1)).LeftHomologyData :=
  ((cotangentComplex.{u, v, w} J g).sc (-1)).leftHomologyData

/-- Extension of scalars along `h` preserves the left homology of `L_{B/A}` in degree `-1`: it
is right exact, and the kernel sequence of the differential stays short exact because its last
term `L⁰` is flat (Stacks 03EX). -/
instance isPreservedBy_cotangentNegOneData :
    (cotangentNegOneData.{u, v, w} J g).IsPreservedBy (towerExtendScalars.{u, v, w} J h) := by
  have := (towerExtendRestrictAdjunction.{u, v, w} J h).leftAdjoint_preservesColimits
  refine ShortComplex.LeftHomologyData.isPreservedBy_of_shortExact _ _ ?_
  exact Stacks.FlatChangeOfRings.shortExact_map_extendScalars h _
    (shortExact_cotangentComplex_kernelSequence J g)
    (isFlat_cotangentComplex_X' J g _)

/-- **`H^{-1}(L_{B/A} ⊗_B D) = H^{-1}(L_{B/A}) ⊗_B D`** for a locally surjective `A ⟶ B` and any
`h : B ⟶ D`, the degreewise base change being taken along `h`. -/
noncomputable def extendScalarsCotangentHomologyNegOneIso :
    (((cotangentComplex.{u, v, w} J g).sc (-1)).map (towerExtendScalars.{u, v, w} J h)).homology ≅
      (towerExtendScalars.{u, v, w} J h).obj ((cotangentComplex.{u, v, w} J g).sc (-1)).homology :=
  ShortComplex.homologyMapIsoOfLeftHomologyData (towerExtendScalars.{u, v, w} J h)
    (cotangentNegOneData.{u, v, w} J g)

/-- **`H⁰(L_{B/A} ⊗_B D) = 0`** for a locally surjective `A ⟶ B`: extension of scalars keeps the
differential into degree `0` an epimorphism. -/
theorem isZero_extendScalars_cotangentComplex_homology_zero :
    IsZero ((((towerExtendScalars.{u, v, w} J h).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (cotangentComplex.{u, v, w} J g)).homology 0) := by
  have := (towerExtendRestrictAdjunction.{u, v, w} J h).leftAdjoint_preservesColimits
  have := epi_cotangentComplex_d_negOne_zero J g
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  refine (exactAt_zero_iff_epi_d_negOne _ ?_).2 ?_
  · exact (towerExtendScalars.{u, v, w} J h).map_isZero
      (cotangentComplex_isZero_pos.{u, v, w} J g 1 (by decide))
  · change Epi ((towerExtendScalars.{u, v, w} J h).map ((cotangentComplex.{u, v, w} J g).d (-1) 0))
    infer_instance

/-- **The first vertex of the fundamental triangle of `A ⟶ B ⟶ D` lies in degrees `≤ -1`** when
`A ⟶ B` is locally surjective: `L_{B/A} ⊗_B D` has no cohomology in degree `0` and no terms in
positive degrees. -/
theorem isLE_Q_obj_baseChangedCotangentComplex [HasDerivedCategory (targetModules.{u, v, w} J D)] :
    (DerivedCategory.Q.obj (baseChangedCotangentComplex.{u, v, w} J g h)).IsLE (-1) := by
  rw [DerivedCategory.isLE_Q_obj_iff, CochainComplex.isLE_iff]
  intro i hi
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  refine IsZero.of_iso ?_ (HomologicalComplex.homologyMapIso
    (towerExtendScalarsCotangentComplexIso.{u, v, w} J g h) i).symm
  obtain rfl | hi' : i = 0 ∨ 0 < i := by omega
  · exact isZero_extendScalars_cotangentComplex_homology_zero J g h
  · exact ShortComplex.isZero_homology_of_isZero_X₂ _
      ((towerExtendScalars.{u, v, w} J h).map_isZero
        (cotangentComplex_isZero_pos.{u, v, w} J g i hi'))

end CategoryTheory.Sheaf

end
