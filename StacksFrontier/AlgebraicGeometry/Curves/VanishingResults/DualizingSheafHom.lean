module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafClauseFive
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDuality
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyLinear
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms into the dualizing sheaf of a proper curve

Let `k` be a field and `f : X ⟶ Spec k` proper with `X` of dimension at most one. For the
dualizing sheaf `ω_X = H^{-1}(ω_X^•)` of [Stacks, Tag 0BS2] and every quasi-coherent `ℱ` there is
a functorial isomorphism

  `Hom_{𝒪_X}(ℱ, ω_X) = Hom_k(H^1(X, ℱ), k)`,

which is clause (5) of [Stacks, Tag 0BS2].

## Main definitions

* `Stacks.Duality.homTruncLEAddEquiv`: maps into `τ^{≤ n}K` out of an object of `D^{≤ n}` are maps
  into `K`.
* `Stacks.Duality.homDualizingSheafShiftAddEquiv`: `Hom(ℱ, ω_X) = Hom_{D(𝒪_X)}(ℱ[0]⟦1⟧, ω_X^•)`.
* `Stacks.Duality.homDualizingSheafAddEquiv`: **[Stacks, Tag 0BS2], clause (5).**

## Main results

* `Stacks.Duality.homDualizingSheafAddEquiv_naturality`: the isomorphism of clause (5) is natural
  in `ℱ`.

## The argument

`ω_X^•` lies in `D^{≥ -1}` (`Stacks.Duality.isGE_dualizingComplexOverField`), so
`τ^{≤ -1}(ω_X^•) ≅ ω_X[1]` (`Stacks.Duality.truncLEIsoSingleDualizingSheaf`). Since `ℱ[0]⟦1⟧`
lies in `D^{≤ -1}`, a morphism `ℱ[0]⟦1⟧ ⟶ ω_X^•` is the same as a morphism into
`τ^{≤ -1}(ω_X^•) ≅ ω_X[0]⟦1⟧`, i.e. a morphism `ℱ ⟶ ω_X`, the single-degree and shift functors
being fully faithful. Clause (4) of [Stacks, Tag 0BS2] in degree zero
(`Stacks.Duality.dualityAddEquivZero`) identifies `Hom(ℱ[0]⟦1⟧, ω_X^•)` with the dual of
`H^0(X, ℱ[0]⟦1⟧) = H^1(X, ℱ)`.

## References

* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.Triangulated

universe u

namespace Stacks.Duality

/-- **Maps into `τ^{≤ n}K` out of an object of `D^{≤ n}` are maps into `K`**: postcomposition with
the canonical map `τ^{≤ n}K ⟶ K` is an isomorphism of abelian groups. -/
def homTruncLEAddEquiv {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (t : TStructure C) (A K : C)
    (n : ℤ) [t.IsLE A n] : (A ⟶ (t.truncLE n).obj K) ≃+ (A ⟶ K) where
  toFun g := g ≫ (t.truncLEι n).app K
  invFun h := t.liftTruncLE h n
  left_inv g := t.to_truncLE_obj_ext (by simp)
  right_inv h := by simp
  map_add' _ _ := Preadditive.add_comp _ _ _ _ _ _

/-- `homTruncLEAddEquiv` sends `g` to its composite with the canonical map `τ^{≤ n}K ⟶ K`. -/
theorem homTruncLEAddEquiv_apply {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (t : TStructure C)
    (A K : C) (n : ℤ) [t.IsLE A n] (g : A ⟶ (t.truncLE n).obj K) :
    homTruncLEAddEquiv t A K n g = g ≫ (t.truncLEι n).app K := rfl

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- **`Hom_{𝒪_X}(ℱ, ω_X) = Hom_{D(𝒪_X)}(ℱ[0]⟦1⟧, ω_X^•)`**: the dualizing sheaf placed in degree
`-1` is the truncation `τ^{≤ -1}(ω_X^•)`, and `ℱ[0]⟦1⟧` lies in `D^{≤ -1}`. -/
def homDualizingSheafShiftAddEquiv (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    (F : X.Modules) :
    (F ⟶ dualizingSheafOverField f) ≃+
      (((DerivedCategory.singleFunctor X.Modules 0).obj F)⟦(1 : ℤ)⟧ ⟶
        (dualizingComplexOverField f).obj) :=
  haveI := isLE_singleShiftOne F
  (fullyFaithfulHomAddEquiv
      (Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.singleFunctor X.Modules 0))
      _ _).trans <|
    (fullyFaithfulHomAddEquiv
      (Functor.FullyFaithful.ofFullyFaithful
        (shiftFunctor (DerivedCategory X.Modules) (1 : ℤ))) _ _).trans <|
    (homCongrAddEquiv (Iso.refl _) (singleShiftOneIsoTruncLE f hdim)).trans <|
    homTruncLEAddEquiv DerivedCategory.TStructure.t _ _ (-1)

/-- `homDualizingSheafShiftAddEquiv` sends `α : ℱ ⟶ ω_X` to `α[0]⟦1⟧` followed by the
identification `ω_X[0]⟦1⟧ ≅ τ^{≤ -1}(ω_X^•)` and the canonical map `τ^{≤ -1}(ω_X^•) ⟶ ω_X^•`. -/
theorem homDualizingSheafShiftAddEquiv_apply (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    (F : X.Modules) (α : F ⟶ dualizingSheafOverField f) :
    homDualizingSheafShiftAddEquiv f hdim F α =
      ((DerivedCategory.singleFunctor X.Modules 0).map α)⟦(1 : ℤ)⟧' ≫
        (singleShiftOneIsoTruncLE f hdim).hom ≫
          (DerivedCategory.TStructure.t.truncLEι (-1)).app (dualizingComplexOverField f).obj := by
  simp [homDualizingSheafShiftAddEquiv, homTruncLEAddEquiv_apply, homCongrAddEquiv_apply]
  rfl

/-- The shift step of clause (5) is natural in the module. -/
theorem homDualizingSheafShiftAddEquiv_naturality
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) {G F : X.Modules} (g : G ⟶ F)
    (α : F ⟶ dualizingSheafOverField f) :
    homDualizingSheafShiftAddEquiv f hdim G (g ≫ α) =
      ((DerivedCategory.singleFunctor X.Modules 0).map g)⟦(1 : ℤ)⟧' ≫
        homDualizingSheafShiftAddEquiv f hdim F α := by
  simp [homDualizingSheafShiftAddEquiv_apply]

/-- **`H^0(X, ℱ[0]⟦1⟧) = H^1(X, ℱ)`**: the shift comparison of hypercohomology followed by the
comparison of hypercohomology of a module placed in degree zero with its sheaf cohomology. -/
def derivedCohomologyShiftOneIsoCohomology (F : X.Modules) :
    derivedCohomologyOverField f (((DerivedCategory.singleFunctor X.Modules 0).obj F)⟦(1 : ℤ)⟧) 0 ≅
      cohomologyOverField k f F 1 :=
  derivedCohomologyShiftIso f _ 1 ≪≫ (cohomologyOverFieldIsoDerivedCohomologyOverField k f F 1).symm

/-- **[Stacks, Tag 0BS2], clause (5).** For a proper `f : X ⟶ Spec k` with `X` of dimension at
most one and a quasi-coherent `𝒪_X`-module `ℱ` there is an isomorphism

  `Hom_{𝒪_X}(ℱ, ω_X) = Hom_k(H^1(X, ℱ), k)`,

where `ω_X = H^{-1}(ω_X^•)` is the dualizing sheaf. It is natural in `ℱ` by
`Stacks.Duality.homDualizingSheafAddEquiv_naturality`. -/
@[stacks 0BS2 "clause (5)"]
def homDualizingSheafAddEquiv (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) (F : X.Modules)
    (hF : F.IsQuasicoherent) :
    (F ⟶ dualizingSheafOverField f) ≃+ (cohomologyOverField k f F 1 ⟶ ModuleCat.of k k) :=
  (homDualizingSheafShiftAddEquiv f hdim F).trans <|
    (dualityAddEquivZero f (shiftQuasiCoherent (singleQuasiCoherent F hF 0) 1)).trans <|
    precompAddEquiv (derivedCohomologyShiftOneIsoCohomology f F)

/-- `homDualizingSheafAddEquiv` sends `α` to the linear form on `H^1(X, ℱ)` obtained from the
degree-zero duality `Stacks.Duality.dualityAddEquivZero` applied to
`Stacks.Duality.homDualizingSheafShiftAddEquiv` of `α`, precomposed with the comparison
`H^1(X, ℱ) ≅ H^0(X, ℱ[0]⟦1⟧)`. -/
theorem homDualizingSheafAddEquiv_apply (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    (F : X.Modules) (hF : F.IsQuasicoherent) (α : F ⟶ dualizingSheafOverField f) :
    homDualizingSheafAddEquiv f hdim F hF α =
      (derivedCohomologyShiftOneIsoCohomology f F).inv ≫
        dualityAddEquivZero f (shiftQuasiCoherent (singleQuasiCoherent F hF 0) 1)
          (homDualizingSheafShiftAddEquiv f hdim F α) := rfl

omit [IsProper f] in
/-- The comparison `H^0(X, ℱ[0]⟦1⟧) = H^1(X, ℱ)` is natural in the module. -/
theorem derivedCohomologyShiftOneIsoCohomology_inv_naturality {G F : X.Modules} (g : G ⟶ F) :
    (derivedCohomologyShiftOneIsoCohomology f G).inv ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
          ((derivedGlobalSectionsOver f).map
            (((DerivedCategory.singleFunctor X.Modules 0).map g)⟦(1 : ℤ)⟧')) =
      cohomologyOverFieldMap k f g 1 ≫ (derivedCohomologyShiftOneIsoCohomology f F).inv := by
  have h1 := cohomologyOverFieldIsoDerivedCohomologyOverField_cohomologyOverFieldMap k f 1 g
  have h2 := (derivedCohomologyShiftNatIso f (1 : ℤ)).inv.naturality
    ((DerivedCategory.singleFunctor X.Modules 0).map g)
  simp only [Functor.comp_obj, Functor.comp_map] at h1 h2
  simp only [derivedCohomologyShiftOneIsoCohomology, derivedCohomologyShiftIso, Iso.trans_inv,
    Iso.symm_inv, Category.assoc, Iso.app_inv]
  rw [← h2, reassoc_of% h1]
  rfl

/-- **[Stacks, Tag 0BS2], clause (5), is natural in `ℱ`**: the isomorphism
`Hom_{𝒪_X}(ℱ, ω_X) = Hom_k(H^1(X, ℱ), k)` turns precomposition with `g : 𝒢 ⟶ ℱ` into
precomposition with `H^1(X, g)`. -/
@[stacks 0BS2 "clause (5): naturality"]
theorem homDualizingSheafAddEquiv_naturality (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    {G F : X.Modules} (hG : G.IsQuasicoherent) (hF : F.IsQuasicoherent) (g : G ⟶ F)
    (α : F ⟶ dualizingSheafOverField f) :
    homDualizingSheafAddEquiv f hdim G hG (g ≫ α) =
      cohomologyOverFieldMap k f g 1 ≫ homDualizingSheafAddEquiv f hdim F hF α := by
  rw [homDualizingSheafAddEquiv_apply, homDualizingSheafAddEquiv_apply,
    homDualizingSheafShiftAddEquiv_naturality]
  have h := dualityAddEquivZero_naturality f (shiftQuasiCoherent (singleQuasiCoherent G hG 0) 1)
    (shiftQuasiCoherent (singleQuasiCoherent F hF 0) 1)
    (((DerivedCategory.singleFunctor X.Modules 0).map g)⟦(1 : ℤ)⟧')
    (homDualizingSheafShiftAddEquiv f hdim F α)
  refine (congrArg (fun z => (derivedCohomologyShiftOneIsoCohomology f G).inv ≫ z) h).trans ?_
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (fun z => z ≫ dualityAddEquivZero f
        (shiftQuasiCoherent (singleQuasiCoherent F hF 0) 1)
        (homDualizingSheafShiftAddEquiv f hdim F α))
      (derivedCohomologyShiftOneIsoCohomology_inv_naturality f g)).trans (Category.assoc _ _ _)

/-! ### The `k`-linear form, and its first consequences -/

/-- **[Stacks, Tag 0BS2], clause (5), `k`-linearly**: `Hom_{𝒪_X}(ℱ, ω_X) ≃ₗ[k] H^1(X, ℱ)^∨` for the
`k`-linear structure `AlgebraicGeometry.modulesLinearOverField` on `𝒪_X`-modules. Linearity is a
consequence of naturality: `c • α = (c • 𝟙) ≫ α`, and `H^1(X, c • 𝟙) = c • 𝟙`. -/
def homDualizingSheafLinearEquiv (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    (F : X.Modules) (hF : F.IsQuasicoherent) :
    letI := modulesLinearOverField k f
    (F ⟶ dualizingSheafOverField f) ≃ₗ[k] (cohomologyOverField k f F 1 →ₗ[k] k) :=
  letI := modulesLinearOverField k f
  { (homDualizingSheafAddEquiv f hdim F hF).trans ModuleCat.homAddEquiv with
    map_smul' := fun c α => by
      have h := homDualizingSheafAddEquiv_naturality f hdim hF hF (c • 𝟙 F) α
      rw [Linear.smul_comp, Category.id_comp, cohomologyOverFieldMap_smul,
        cohomologyOverFieldMap_id, Linear.smul_comp, Category.id_comp] at h
      change (homDualizingSheafAddEquiv f hdim F hF (c • α)).hom =
        c • (homDualizingSheafAddEquiv f hdim F hF α).hom
      rw [h]
      rfl }

/-- `homDualizingSheafLinearEquiv` sends `α` to the linear map underlying
`Stacks.Duality.homDualizingSheafAddEquiv` of `α`. -/
theorem homDualizingSheafLinearEquiv_apply (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    (F : X.Modules) (hF : F.IsQuasicoherent) (α : F ⟶ dualizingSheafOverField f) :
    homDualizingSheafLinearEquiv f hdim F hF α = (homDualizingSheafAddEquiv f hdim F hF α).hom :=
  rfl

/-- **A nonvanishing `H^1(X, ℱ)` gives a nonzero map `ℱ ⟶ ω_X`**: a nonzero vector of `H^1(X, ℱ)`
is detected by a linear form, which clause (5) of [Stacks, Tag 0BS2] turns into a map into the
dualizing sheaf. -/
theorem exists_ne_zero_hom_dualizingSheaf (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    (F : X.Modules) (hF : F.IsQuasicoherent) (h : ¬ IsZero (cohomologyOverField k f F 1)) :
    ∃ φ : F ⟶ dualizingSheafOverField f, φ ≠ 0 := by
  let := modulesLinearOverField k f
  rw [ModuleCat.isZero_iff_subsingleton, not_subsingleton_iff_nontrivial] at h
  obtain ⟨v, hv⟩ := exists_ne (0 : cohomologyOverField k f F 1)
  obtain ⟨l, hl⟩ : ∃ l : Module.Dual k (cohomologyOverField k f F 1), l v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv ((Module.forall_dual_apply_eq_zero_iff k v).mp hcon)
  refine ⟨(homDualizingSheafLinearEquiv f hdim F hF).symm l, fun h0 => hl ?_⟩
  have := congrArg (homDualizingSheafLinearEquiv f hdim F hF) h0
  rw [LinearEquiv.apply_symm_apply, map_zero] at this
  rw [this, LinearMap.zero_apply]

/-- **`dim_k H^0(X, ω_X) = g`**, equation [Stacks, Tag 0BY8]: by clause (5) of
[Stacks, Tag 0BS2] at `ℱ = 𝒪_X`, the global sections `Hom(𝒪_X, ω_X)` of the dualizing sheaf are
the dual of `H^1(X, 𝒪_X)`, whose dimension is the genus. -/
theorem finrank_cohomologyOverField_zero_dualizingSheafOverField
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) :
    Module.finrank k (cohomologyOverField k f (dualizingSheafOverField f) 0) = genus f := by
  let := modulesLinearOverField k f
  have := _root_.Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
  have := finiteDimensional_cohomologyOverField_of_isProper k f
    (SheafOfModules.unit X.ringCatSheaf) 1
  rw [← (unitHomLinearEquivCohomologyZero k f (dualizingSheafOverField f)).finrank_eq,
    (homDualizingSheafLinearEquiv f hdim (structureSheafModule X)
      (isQuasicoherent_of_isCoherent _)).finrank_eq,
    Subspace.dual_finrank_eq, finrank_cohomologyOverField_one_unit_eq_genus]

/-- **`H^0(X, ω_X)` is finite dimensional**: it is the dual of `H^1(X, 𝒪_X)` by clause (5) of
[Stacks, Tag 0BS2]. -/
theorem finiteDimensional_cohomologyOverField_zero_dualizingSheafOverField
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) :
    FiniteDimensional k (cohomologyOverField k f (dualizingSheafOverField f) 0) := by
  let := modulesLinearOverField k f
  have := _root_.Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
  have := finiteDimensional_cohomologyOverField_of_isProper k f
    (SheafOfModules.unit X.ringCatSheaf) 1
  exact LinearEquiv.finiteDimensional
    ((homDualizingSheafLinearEquiv f hdim (structureSheafModule X)
      (isQuasicoherent_of_isCoherent _)).symm.trans
      (unitHomLinearEquivCohomologyZero k f (dualizingSheafOverField f)))

end Stacks.Duality

end
