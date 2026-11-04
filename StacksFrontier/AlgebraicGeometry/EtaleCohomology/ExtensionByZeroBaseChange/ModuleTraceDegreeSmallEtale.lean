module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.ModuleTraceDegree
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.TraceDegreeSmallEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trace of a finite étale morphism of constant degree, for sheaves of modules on Mathlib's
small étale site

Let `f : T ⟶ S` be a finite étale morphism of schemes which is finite locally free of rank `d`,
let `Λ` be a ring and let `G` be a sheaf of `Λ`-modules on `S_étale`. The unit
`G ⟶ f_* f^{-1} G` of the adjunction `f^{-1} ⊣ f_*` has a left inverse up to `d`: there is
`r : f_* f^{-1} G ⟶ G` whose composite with the unit is multiplication by `d`. The map `r` is the
trace of Definition 03SE, transported from the size-bounded small étale site of Tag 021B, on
which the identity is `AlgebraicGeometry.unit_comp_moduleTrace_eq_nsmul`.

When multiplication by `d` is an isomorphism of `G` — for instance when `G` is killed by an
integer prime to `d` — the unit is therefore a split monomorphism: `G` is a direct summand of
`f_* f^{-1} G`. This is the form in which Section 03SH is used.

## Main results

* `Stacks.EtaleCohomology.exists_etaleModule_unit_comp_eq_nsmul_of_finiteEtale`.
* `Stacks.EtaleCohomology.exists_etaleModule_unit_comp_eq_id_of_isIso_nsmul`.
* `Stacks.EtaleCohomology.exists_etaleModule_unit_comp_eq_id_of_coprime`.

## Implementation notes

The transport is the one of `Stacks.EtaleCohomology.exists_unit_comp_eq_nsmul_of_finiteEtale`,
for abelian sheaves: the comparisons of inverse and of direct images between the two models of
the small étale site are mates, and the mate relation carries the unit of one adjunction to the
unit of the other.

## References

* [Stacks Project, Tag 03SE](https://stacks.math.columbia.edu/tag/03SE)
* [Stacks Project, Tag 03SH](https://stacks.math.columbia.edu/tag/03SH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (Λ : Type r) [Ring Λ]

/-- **Stacks 03SH, on Mathlib's small étale site.** For a finite étale `f` of degree `d` the unit
`G ⟶ f_* f^{-1} G` of sheaves of `Λ`-modules has a left inverse up to `d`, the trace: there is
`r : f_* f^{-1} G ⟶ G` with `unit ≫ r = d`. -/
theorem exists_etaleModule_unit_comp_eq_nsmul_of_finiteEtale {S T : Scheme.{u}} (f : T ⟶ S)
    [IsFinite f] [Etale f] (d : ℕ) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d]
    (G : EtaleModules.{u, r} Λ S) :
    ∃ r : (etaleModuleDirectImage.{u, r} Λ f).obj ((etaleModuleInverseImage.{u, r} Λ f).obj G) ⟶
        G, (etaleModuleInverseImageAdj.{u, r} Λ f).unit.app G ≫ r = d • 𝟙 G := by
  let S₀ : Set Scheme.{u} := {S, T}
  let B := BigEtaleSite.ofSet S₀
  have hS : B.Contains S := BigEtaleSite.contains_ofSet S₀ (by simp [S₀])
  have hT : B.Contains T := BigEtaleSite.contains_ofSet S₀ (by simp [S₀])
  let f₀ : B.obj T hT ⟶ B.obj S hS := ObjectProperty.homMk f
  have : IsFinite (B.inclusion.map f₀) := ‹IsFinite f›
  have : Etale (B.inclusion.map f₀) := ‹Etale f›
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (B.inclusion.map f₀) d :=
    ‹Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d›
  let A := ModuleCat.{max (u + 1) r} Λ
  let adjU := etaleModuleInverseImageAdj.{u, r} Λ f
  let adjB := smallEtalePostcomposePushforwardAdjunction B f₀ A
  let ρS := (SmallEtale.toEtaleSite B S hS).sheafPushforwardContinuous A
    (SmallEtale.topology B S hS) S.smallEtaleTopology
  have hff : ρS.FullyFaithful :=
    (SmallEtale.sheafEquiv B S hS A).fullyFaithfulInverse
  let α := SmallEtale.restrictionPullbackBaseChangeIso B A f₀ adjU adjB
  let β := SmallEtale.toEtaleSitePushforwardBaseChangeIso B f₀ A
  have hmate := SmallEtale.mateEquiv_restrictionPullbackBaseChange B A f₀ adjU adjB
  have hunit := unit_mateEquiv adjU adjB
    (SmallEtale.restrictionPullbackBaseChange B A f₀ adjU adjB) G
  have hβ : (mateEquiv adjU adjB (SmallEtale.restrictionPullbackBaseChange B A f₀ adjU adjB)).app
      ((etaleModuleInverseImage.{u, r} Λ f).obj G) =
      β.hom.app ((etaleModuleInverseImage.{u, r} Λ f).obj G) :=
    congrArg (fun t ↦ t.app ((etaleModuleInverseImage.{u, r} Λ f).obj G)) hmate
  rw [hβ] at hunit
  let rB := (moduleTrace B S hS (SmallEtale.ofEtaleHom B f₀) Λ).app (ρS.obj G)
  have htr := unit_comp_moduleTrace_eq_nsmul B f₀ Λ d (ρS.obj G)
  have hαα : (SmallEtale.restrictionPullbackBaseChange B A f₀ adjU adjB).app G ≫ α.inv.app G =
      𝟙 _ := α.hom_inv_id_app G
  have h1 : ρS.map (adjU.unit.app G) ≫ β.hom.app ((etaleModuleInverseImage.{u, r} Λ f).obj G) ≫
      (B.smallPushforward f₀ A).map (α.inv.app G) ≫ rB = d • 𝟙 _ := by
    rw [reassoc_of% hunit, ← Functor.map_comp_assoc, hαα]
    simpa using htr
  refine ⟨hff.preimage (β.hom.app ((etaleModuleInverseImage.{u, r} Λ f).obj G) ≫
    (B.smallPushforward f₀ A).map (α.inv.app G) ≫ rB), hff.map_injective ?_⟩
  rw [Functor.map_comp, hff.map_preimage, h1, Functor.map_nsmul]
  simp

/-- **Stacks 03SH: `G` is a direct summand of `f_* f^{-1} G`.** For a finite étale `f` of degree
`d` and a sheaf of `Λ`-modules `G` on which multiplication by `d` is an isomorphism, the unit
`G ⟶ f_* f^{-1} G` has a left inverse. -/
@[sga "5 IIIB 3.2" "partial"]
theorem exists_etaleModule_unit_comp_eq_id_of_isIso_nsmul {S T : Scheme.{u}} (f : T ⟶ S)
    [IsFinite f] [Etale f] (d : ℕ) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d]
    (G : EtaleModules.{u, r} Λ S) [IsIso (d • 𝟙 G)] :
    ∃ r : (etaleModuleDirectImage.{u, r} Λ f).obj ((etaleModuleInverseImage.{u, r} Λ f).obj G) ⟶
        G, (etaleModuleInverseImageAdj.{u, r} Λ f).unit.app G ≫ r = 𝟙 G := by
  obtain ⟨r, hr⟩ := exists_etaleModule_unit_comp_eq_nsmul_of_finiteEtale Λ f d G
  exact ⟨r ≫ inv (d • 𝟙 G), by rw [reassoc_of% hr, IsIso.hom_inv_id]⟩

/-- Multiplication by `d` is an isomorphism of an object of a preadditive category killed by an
integer `n` prime to `d`: a Bézout combination `a d + b n = 1` gives its inverse. -/
theorem isIso_nsmul_id_of_coprime {C : Type*} [Category* C] [Preadditive C] (G : C)
    {d n : ℕ} (hdn : Nat.Coprime d n) (hn : n • 𝟙 G = 0) : IsIso (d • 𝟙 G) := by
  have hb : ((Nat.gcdA d n : ℤ) * d + Nat.gcdB d n * n) = 1 := by
    have := Nat.gcd_eq_gcd_ab d n
    rw [hdn] at this
    push_cast at this
    linarith
  have hn' : (n : ℤ) • 𝟙 G = 0 := by rw [natCast_zsmul, hn]
  have key : (Nat.gcdA d n : ℤ) • (d • 𝟙 G) = 𝟙 G := by
    have h1 : (1 : ℤ) • 𝟙 G = ((Nat.gcdA d n : ℤ) * d + Nat.gcdB d n * n) • 𝟙 G := by rw [hb]
    rw [one_smul, add_smul, mul_smul, mul_smul, hn', smul_zero, add_zero, natCast_zsmul] at h1
    exact h1.symm
  refine ⟨⟨(Nat.gcdA d n : ℤ) • 𝟙 G, ?_, ?_⟩⟩
  · rw [Preadditive.comp_zsmul, Category.comp_id, key]
  · rw [Preadditive.zsmul_comp, Category.id_comp, key]

/-- **Stacks 03SH, in the form used for torsion coefficients.** For a finite étale `f` of degree
`d` and a sheaf of `Λ`-modules `G` killed by an integer `n` prime to `d`, the unit
`G ⟶ f_* f^{-1} G` has a left inverse. -/
theorem exists_etaleModule_unit_comp_eq_id_of_coprime {S T : Scheme.{u}} (f : T ⟶ S)
    [IsFinite f] [Etale f] (d : ℕ) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d]
    (G : EtaleModules.{u, r} Λ S) {n : ℕ} (hdn : Nat.Coprime d n) (hn : n • 𝟙 G = 0) :
    ∃ r : (etaleModuleDirectImage.{u, r} Λ f).obj ((etaleModuleInverseImage.{u, r} Λ f).obj G) ⟶
        G, (etaleModuleInverseImageAdj.{u, r} Λ f).unit.app G ≫ r = 𝟙 G :=
  have := isIso_nsmul_id_of_coprime G hdn hn
  exists_etaleModule_unit_comp_eq_id_of_isIso_nsmul Λ f d G

end Stacks.EtaleCohomology

end
