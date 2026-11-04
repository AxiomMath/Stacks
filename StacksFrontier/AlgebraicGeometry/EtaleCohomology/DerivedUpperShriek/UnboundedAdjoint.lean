module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionCoefficientsDirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction
public import StacksFrontier.Homology.Injectives.BrownRepresentabilityRightAdjoint
public import StacksFrontier.Homology.Perfect.Characterizing

/-!
# The right adjoint of the unbounded derived lower shriek

Let `f : X ⟶ Y` be a separated morphism of finite type between quasi-compact and
quasi-separated schemes, let `j : X ⟶ Xbar` be a compactification of `f` with proper structure
morphism `fbar : Xbar ⟶ Y`, and let `Λ` be a torsion ring. The derived lower shriek
`Rf_! = R(fbar)_* ∘ j_! : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` of
`Stacks.EtaleCohomology.derivedLowerShriekUnbounded` has a right adjoint `Rf^!`,
[Stacks, Tag 0G2C].

The proof is the source's: `Rf_!` is exact and commutes with direct sums ([Stacks, Tag 0G29]),
so Brown representability ([Stacks, Tag 0F5Y]) produces the adjoint. The commutation with
direct sums is the open immersion case (`j_!` is a left adjoint) together with the proper case,
[Stacks, Tag 0F0D], which is [Stacks, Tag 0F11] once `fbar_*` has finite cohomological
dimension.

## Main results

* `exists_isZero_rightDerived_etaleModuleDirectImage_of_natCast_eq_zero`: for a torsion ring
  `Λ`, a bound for the cohomological dimension `cd(f)` of [Stacks, Tag 0F0Z]
  bounds the higher direct images of every sheaf of `Λ`-modules.
* `Stacks.Injectives.isLeftAdjoint_of_preservesCoproducts`: [Stacks, Tag 0F5Y] for an exact
  functor between the derived categories of two Grothendieck abelian categories.
* `isLeftAdjoint_derivedLowerShriekUnbounded_of_isZero_rightDerived`: `Rf_!` is a left adjoint
  as soon as the higher direct images along `fbar` vanish in high
  degrees.

## Implementation notes

*Universes.* Sheaves of `Λ`-modules on a small étale site satisfy the Grothendieck axioms
relative to the universe of their morphisms, not of their objects, so Brown representability is
applied through `Stacks.Injectives.exists_exact_rightAdjoint_of_isGrothendieckAbelian`, after
replacing the standard model of `D(Y_étale, Λ)`, whose morphisms are one universe too large, by
the equivalent model of [Stacks, Tag 079Q].

*Coefficients.* `Λ` is a commutative ring in `Type`, the setting of the comparison
`Stacks.EtaleCohomology.rightDerivedEtaleModuleDirectImageForgetIso` between higher direct
images of sheaves of modules and of their underlying abelian sheaves. A ring is torsion exactly
when `n = 0` in it for some `n ≥ 1`, since `1` is then torsion.

## References

* [Stacks Project, Tag 0G2C](https://stacks.math.columbia.edu/tag/0G2C)
* [Stacks Project, Tag 0G29](https://stacks.math.columbia.edu/tag/0G29)
* [Stacks Project, Tag 0F5Y](https://stacks.math.columbia.edu/tag/0F5Y)
* [Stacks Project, Tag 0F11](https://stacks.math.columbia.edu/tag/0F11)
* [Stacks Project, Tag 0F0Z](https://stacks.math.columbia.edu/tag/0F0Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.EtaleCohomology.DerivedUpperShriek

section Torsion

open _root_.AlgebraicGeometry Opposite

variable (Λ : Type) [CommRing Λ] (n : ℕ) (hn : 0 < n) (hΛ : (n : Λ) = 0)

include hn hΛ in
/-- **The underlying abelian sheaf of a sheaf of `Λ`-modules is torsion** when `n Λ = 0` for
some `n ≥ 1`: every section is annihilated by `n`. -/
theorem torsionSheafProperty_etaleModuleForget_obj_of_natCast_eq_zero (X : Scheme.{u})
    (F : EtaleModules.{u, 0} Λ X) :
    Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology
      ((etaleModuleForget Λ X).obj F) :=
  fun U x => ⟨⊤, X.smallEtaleTopology.top_mem U, fun V g _ => ⟨n, hn, by
    show n • ((F.obj.map g.op).hom x : F.obj.obj (op V)) = 0
    rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]⟩⟩

include hn hΛ in
/-- **A bound for the higher direct images of torsion abelian sheaves bounds those of every
sheaf of `Λ`-modules**, when `n Λ = 0` for some `n ≥ 1`: a sheaf of `Λ`-modules is torsion, and
its higher direct images are those of its underlying abelian sheaf. -/
theorem isZero_rightDerived_etaleModuleDirectImage_of_natCast_eq_zero
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (hab : ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G → ∀ q : ℕ, d < q →
        IsZero (((etaleAbelianDirectImage.{u, u + 1} f).rightDerived q).obj G))
    (q : ℕ) (hq : d < q) (F : EtaleModules.{u, 0} Λ X) :
    IsZero (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj F) :=
  isZero_of_isZero_etaleModuleForget_obj _ _
    (IsZero.of_iso (hab _ (torsionSheafProperty_etaleModuleForget_obj_of_natCast_eq_zero Λ n hn hΛ
      X F) q hq) ((rightDerivedEtaleModuleDirectImageForgetIso Λ f q).app F))

include hn hΛ in
/-- **Finite cohomological dimension of `f` bounds the higher direct images of every sheaf of
`Λ`-modules**, when `n Λ = 0` for some `n ≥ 1`. -/
theorem exists_isZero_rightDerived_etaleModuleDirectImage_of_natCast_eq_zero
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hcd : f.etaleCohomologicalDimension < ⊤) :
    ∃ d : ℕ, ∀ q : ℕ, d ≤ q → ∀ F : EtaleModules.{u, 0} Λ X,
      IsZero (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj F) := by
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1 hcd.ne
  refine ⟨d + 1, fun q hq F ↦ isZero_rightDerived_etaleModuleDirectImage_of_natCast_eq_zero Λ n hn
    hΛ f d (fun G hG q hq ↦ f.isZero_rightDerived_etaleAbelianDirectImage G hG q ?_) q
    (by omega) F⟩
  rw [← hd]
  exact_mod_cast hq

end Torsion

end Stacks.EtaleCohomology.DerivedUpperShriek

namespace Stacks.Injectives

universe v z₁ z₂ u₁ u₂

/-- **[Stacks, Tag 0F5Y] between derived categories of Grothendieck abelian categories.** Let `A`
and `B` be Grothendieck abelian categories relative to the universe `v` of their morphisms. An
exact functor `F : D(A) ⥤ D(B)` which commutes with direct sums indexed by types in `v` is a left
adjoint, for any models of the two derived categories. -/
theorem isLeftAdjoint_of_preservesCoproducts {A : Type u₁} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] [HasDerivedCategory.{z₁} A]
    {B : Type u₂} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
    [hB : HasDerivedCategory.{z₂} B]
    (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) F] : F.IsLeftAdjoint := by
  have hadd : ∀ n : ℤ, (shiftFunctor (DerivedCategory B) n).Additive := inferInstance
  obtain ⟨hsmall⟩ : Nonempty (HasDerivedCategory.{v} B) :=
    ⟨Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian B⟩
  let e := StacksDraft.Perfect.derivedEquivalence hB hsmall
  let := StacksDraft.Perfect.derivedEquivalenceCommShift hB hsmall
  have := StacksDraft.Perfect.derivedEquivalence_isTriangulated hB hsmall
  have : ∀ n : ℤ, (shiftFunctor (@DerivedCategory B _ _ hsmall) n).Additive := by
    let := hsmall
    infer_instance
  have : (F ⋙ e.functor).IsTriangulated := inferInstance
  have : ∀ J : Type v, PreservesColimitsOfShape (Discrete J) (F ⋙ e.functor) :=
    fun J ↦ inferInstance
  obtain ⟨G, adj, -⟩ := Stacks.Injectives.exists_exact_rightAdjoint_of_isGrothendieckAbelian
    A (F ⋙ e.functor) fun _ _ ↦ inferInstance
  have : (F ⋙ e.functor).IsLeftAdjoint := adj.isLeftAdjoint
  have : ((F ⋙ e.functor) ⋙ e.inverse).IsLeftAdjoint := Functor.isLeftAdjoint_comp _ _
  exact Functor.isLeftAdjoint_of_iso
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F e.unitIso.symm ≪≫ F.rightUnitor)

end Stacks.Injectives

namespace Stacks.EtaleCohomology.DerivedUpperShriek

open _root_.AlgebraicGeometry Stacks.Injectives.KInjectiveResolution

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [CommRing Λ] (n : ℕ) (hn : 0 < n) (hΛ : (n : Λ) = 0)

/-- **[Stacks, Tag 0G2C], given the vanishing of the higher direct images along `fbar`.** Let
`j : X ⟶ Xbar` be a compactification of `f : X ⟶ Y`, with proper structure morphism
`fbar = j.toBase`, and suppose that `R^q fbar_* F = 0` for all `q ≥ d` and every sheaf of
`Λ`-modules `F`. Then `Rf_! = R(fbar)_* ∘ j_! : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` has a right
adjoint.

The vanishing makes `R(fbar)_*` commute with direct sums ([Stacks, Tag 0F11]); `j_!` commutes
with them as the left adjoint of `j^{-1}`; and Brown representability does the rest. -/
theorem isLeftAdjoint_derivedLowerShriekUnbounded_of_isZero_rightDerived
    {X Y : Scheme.{u}} (f : X ⟶ Y) (j : CompactificationOf (Over.mk f))
    (d : ℕ) (hd : ∀ q : ℕ, d ≤ q → ∀ F : EtaleModules.{u, 0} Λ j.space,
      IsZero (((etaleModuleDirectImage.{u, 0} Λ j.toBase).rightDerived q).obj F)) :
    (derivedLowerShriekUnbounded.{u, 0} f j Λ).IsLeftAdjoint := by
  let := etaleModuleDerivedDirectImageUnboundedCommShift.{u, 0} Λ j.toBase
  have := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, 0} Λ j.toBase
  have hpush : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ j.toBase) := fun I ↦
    preservesColimitsOfShape_of_finiteCohomologicalDimension_directImage Λ j.toBase ⟨d, hd⟩
      (fun q I ↦ preservesColimitsOfShape_discrete_rightDerived_etaleModuleDirectImage Λ
        j.toBase q I) _
      (homotopyCategoryUnit _ _ (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ j.toBase)) I
  let F₀ := (etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapDerivedCategory ⋙
    etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ j.toBase
  let eF : F₀ ≅ derivedLowerShriekUnbounded.{u, 0} f j Λ :=
    Functor.isoWhiskerRight (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ
      j.immersion).symm _
  have hsum : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) F₀ := fun I ↦ by
    have := (etaleModuleExtensionByZeroAdj.{u, 0} Λ
      j.immersion).mapDerivedCategory.leftAdjoint_preservesColimits.preservesColimitsOfShape
      (J := Discrete I)
    exact Limits.comp_preservesColimitsOfShape _ _
  let : F₀.CommShift ℤ := inferInstance
  have : F₀.IsTriangulated := inferInstance
  have : F₀.IsLeftAdjoint := Stacks.Injectives.isLeftAdjoint_of_preservesCoproducts F₀
  exact Functor.isLeftAdjoint_of_iso eF

include hn hΛ in
/-- **[Stacks, Tag 0G2C], given that `fbar` has finite cohomological dimension.** For a torsion
ring `Λ` (that is, `n = 0` in `Λ` for some `n ≥ 1`) and a compactification `j` of `f` whose
proper structure morphism `fbar` satisfies `cd(fbar) < ∞` ([Stacks, Tag 0F0Z]), the derived lower
shriek `Rf_! : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` has a right adjoint. -/
theorem isLeftAdjoint_derivedLowerShriekUnbounded_of_etaleCohomologicalDimension
    {X Y : Scheme.{u}} (f : X ⟶ Y) (j : CompactificationOf (Over.mk f))
    (hcd : j.toBase.etaleCohomologicalDimension < ⊤) :
    (derivedLowerShriekUnbounded.{u, 0} f j Λ).IsLeftAdjoint := by
  obtain ⟨d, hd⟩ :=
    exists_isZero_rightDerived_etaleModuleDirectImage_of_natCast_eq_zero Λ n hn hΛ j.toBase hcd
  exact isLeftAdjoint_derivedLowerShriekUnbounded_of_isZero_rightDerived Λ f j d hd

end Stacks.EtaleCohomology.DerivedUpperShriek
