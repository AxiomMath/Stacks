module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleTerminalBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TerminalBaseChangeOfLocallyBijectivePullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangePropertySheafified
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleRestrictionFinalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentEtaleCartesianLargeSections
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianTransportAlongComparison
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.OverFunctorIso

/-!
# Flat base change gives cartesianness between objects over affine schemes, at large universes

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be fibred in groupoids and `𝓖` a locally quasi-coherent module on `𝒳`
(Stacks 06WJ) with sections in `Type (max (u + 1) v w m)`. If, for an arrow `φ : x ⟶ y` of `𝒳`
over a morphism of affine schemes, the comparison `c_φ` of Stacks 06WC is locally bijective (the
flat base change property of Stacks 0762, read with the pullback of sheaves, at `φ`), then `𝓖` is
cartesian along `φ`: `𝒪(x) ⊗_{𝒪(y)} 𝓖(y) ⟶ 𝓖(x)` is bijective. No Zariski module category is used,
so the statement holds at the module universe `u + 1` of the stacks chapters.

The proof restricts to the small étale sites of the two affine schemes, where the restrictions are
locally their base changes from the final objects (they are quasi-coherent, hence cartesian
between affine objects), and applies
`bijective_restrictionBaseChange_of_isLocallyBijective_pullbackComparison`.

## Main results

* `bijective_restrictionBaseChange_of_isLocallyBijectiveRestrictModulePullbackComparison`:
  if the comparison of Stacks 06WC at an arrow `φ : x ⟶ y` over affine schemes is locally
  bijective, then `𝒪(x) ⊗_{𝒪(y)} 𝓖(y) ⟶ 𝓖(x)` is bijective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.TerminalBaseChange
open Stacks.PresheafOfModules

universe u v w m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- Under the hypotheses of
`bijective_restrictionBaseChange_of_isLocallyBijectiveRestrictModulePullbackComparison`,
the module is cartesian along the arrow `φ'` computing the comparison of Stacks 06W2 over the final
object of the small étale site below `y`. -/
theorem exists_lift_bijective_restrictionBaseChange_of_isLocallyBijectivePullbackComparison
    (G₀ : PresheafOfModules.{max (u + 1) v w m}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hG : IsLocallyQuasicoherent B E h S hS p hp G₀) {x y : 𝒳} (φ : x ⟶ y)
    (hφ : IsLocallyBijectiveRestrictModulePullbackComparisonUnivLE.{u, v, w, max (u + 1) v w m}
      B E h S hS p hp (etaleTopology B) (etaleTopology_le_topology B) φ G₀)
    (hx : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj x))
    (hy : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj y)) :
    letI := isEquivalence_overPost B S hS p hp x
    letI := isEquivalence_overPost B S hS p hp y
    ∃ φ' : ((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv.obj
        ((smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x)).obj
          ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj
            (smallEtaleFinal B E h S hS p y)))).left ⟶
        ((Over.post (X := y) (p ⋙ Over.forget (B.obj hS))).inv.obj
          ((smallEtaleInclusion B E h (p.obj y).left.1 (contains_base B E h S hS p y)).obj
            (smallEtaleFinal B E h S hS p y))).left,
      φ' ≫ ((Over.post (X := y) (p ⋙ Over.forget (B.obj hS))).inv.obj
          ((smallEtaleInclusion B E h (p.obj y).left.1 (contains_base B E h S hS p y)).obj
            (smallEtaleFinal B E h S hS p y))).hom =
        ((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv.obj
          ((smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x)).obj
            ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj
              (smallEtaleFinal B E h S hS p y)))).hom ≫ φ ∧
      Function.Bijective (restrictionBaseChange.{v, w, u, max (u + 1) v w m}
        (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
        G₀ φ'.op) := by
  obtain ⟨hMy, hqy⟩ := hG.2 y
  obtain ⟨hMx, hqx⟩ := hG.2 x
  let X := smallEtaleFinal B E h S hS p y
  have hX : IsTerminal X := SmallEtale.finalIsTerminal E _ _
  have hXa : IsAffine ((SmallEtale.toScheme E _ _).obj X) := hy
  let b := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)
  have hbX : IsTerminal (b.obj X) := hX.isTerminalObj b
  have hbXa : IsAffine ((SmallEtale.toScheme E _ _).obj (b.obj X)) := by
    have e := hbX.uniqueUpToIso (SmallEtale.finalIsTerminal E _ (contains_base B E h S hS p x))
    have : IsAffine ((SmallEtale.toScheme E _ _).obj
      (SmallEtale.final E _ (contains_base B E h S hS p x))) := hx
    exact IsAffine.of_isIso ((SmallEtale.toScheme E _ _).map e.hom)
  have : HasSheafify (SmallEtale.topology E _ (contains_base B E h S hS p y))
      AddCommGrpCat.{max (u + 1) v w m} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max (u + 1) v w m, u, u + 1} _
  have : ∀ z : 𝒳, (SmallEtale.topology E _ (contains_base B E h S hS p z)).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) v w m} := fun _ =>
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max (u + 1) v w m,
      u + 1, u} _
  let ρ := smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
    (etaleTopology_le_topology B)
  let := isEquivalence_overPost B S hS p hp x
  let := isEquivalence_overPost B S hS p hp y
  let G := restrictModuleToSmallEtale B E h S hS p hp y (etaleTopology B)
    (etaleTopology_le_topology B) G₀
  let H := restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
    (etaleTopology_le_topology B) G₀
  let d : G ⟶ (PresheafOfModules.pushforward ρ).obj H :=
    restrictModulePushforwardComparison B E h S hS p hp φ (etaleTopology B)
      (etaleTopology_le_topology B) G₀
  have hGi := SmallEtale.isLocallyInjective_baseChangeAdj_counit.{u, max v w m} hX hXa ⟨G, hMy⟩ hqy
  have hGs := SmallEtale.isLocallySurjective_baseChangeAdj_counit.{u, max v w m} hX hXa ⟨G, hMy⟩ hqy
  have hHi := SmallEtale.isLocallyInjective_baseChangeAdj_counit.{u, max v w m} hbX hbXa ⟨H, hMx⟩
    hqx
  have hHs := SmallEtale.isLocallySurjective_baseChangeAdj_counit.{u, max v w m} hbX hbXa ⟨H, hMx⟩
    hqx
  obtain ⟨φ', hfac, hbase⟩ := exists_restrictionComparisonLift B E h S hS p hp φ X
  have hring := restrictionPushforwardComparison_app B E h S hS p hp φ
    (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj
    X φ' hfac hbase
  refine ⟨φ', hfac, ?_⟩
  refine bijective_restrictionBaseChange_of_isLocallyBijective_pullbackComparison.{
    max (u + 1) v w m, u}
    (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj G₀
    (smallEtaleInclusion B E h (p.obj y).left.1 (contains_base B E h S hS p y) ⋙
      (Over.post (X := y) (p ⋙ Over.forget (B.obj hS))).inv ⋙ Over.forget y)
    (smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x) ⋙
      (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv ⋙ Over.forget x)
    (localStructurePresheafIso B E h S hS p hp y (etaleTopology B) (etaleTopology_le_topology B))
    (localStructurePresheafIso B E h S hS p hp x (etaleTopology B) (etaleTopology_le_topology B))
    b ρ (J := SmallEtale.topology E _ (contains_base B E h S hS p y))
    (K := SmallEtale.topology E _ (contains_base B E h S hS p x)) hX hbX φ' (fun t => ?_) d
    (fun g => ConcreteCategory.congr_hom
      (restrictionPushforwardComparison_app B E h S hS p hp φ G₀.presheaf X φ' hfac hbase) g)
    (fun Q hQ => b.op_comp_isSheaf _ _ ⟨Q.presheaf, hQ⟩)
    (fun Y => SmallEtale.exists_isSheaf_obj_iso_of_isTerminal.{u, max v w m} hbX hbXa Y)
    (hcs := hφ.2) (hci := hφ.1) (hGs := hGs) (hGi := hGi) (hHs := hHs) (hHi := hHi)
  have e : (ρ.app (op X)).hom t =
      ((localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B)).inv.app (op (b.obj X))).hom
        (((restrictionPushforwardComparison B E h S hS p hp φ
          (ringStructureSheafCore B S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B)).obj).app (op X)).hom
          (((localStructurePresheafIso B E h S hS p hp y (etaleTopology B)
            (etaleTopology_le_topology B)).hom.app (op X)).hom t)) :=
    rfl
  rw [e, hring]
  exact ((localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
    (etaleTopology_le_topology B)).app (op (b.obj X))).inv_hom_id_apply _

/-- **Flat base change makes a locally quasi-coherent module cartesian along an arrow between
objects over affine schemes**, at module universe `max (u + 1) v w m`: if the comparison `c_φ` of
Stacks 06WC is locally bijective (the flat base change property of Stacks 0762 at `φ`), then
`𝒪(x) ⊗_{𝒪(y)} 𝓖(y) ⟶ 𝓖(x)` is bijective. -/
theorem bijective_restrictionBaseChange_of_isLocallyBijectiveRestrictModulePullbackComparison
    (G₀ : PresheafOfModules.{max (u + 1) v w m}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hG : IsLocallyQuasicoherent B E h S hS p hp G₀) {x y : 𝒳} (φ : x ⟶ y)
    (hφ : IsLocallyBijectiveRestrictModulePullbackComparisonUnivLE.{u, v, w, max (u + 1) v w m}
      B E h S hS p hp (etaleTopology B) (etaleTopology_le_topology B) φ G₀)
    (hx : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj x))
    (hy : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj y)) :
    Function.Bijective (restrictionBaseChange.{v, w, u, max (u + 1) v w m}
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      G₀ φ.op) := by
  obtain ⟨φ', hfac, hβ⟩ :=
    exists_lift_bijective_restrictionBaseChange_of_isLocallyBijectivePullbackComparison.{u, v, w, m}
      B E h S hS p hp G₀ hG φ hφ hx hy
  let := isEquivalence_overPost B S hS p hp x
  let := isEquivalence_overPost B S hS p hp y
  let X := smallEtaleFinal B E h S hS p y
  have hX : IsTerminal X := SmallEtale.finalIsTerminal E _ _
  let b := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)
  have hbX : IsTerminal (b.obj X) := hX.isTerminalObj b
  have hyo := Over.isIso_hom_of_isTerminal (IsTerminal.isTerminalObj
    (Over.post (X := y) (p ⋙ Over.forget (B.obj hS))).inv _
    (isTerminal_smallEtaleInclusion_obj_final B E h S hS p y))
  have hxo := Over.isIso_hom_of_isTerminal (IsTerminal.isTerminalObj
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv _
    (IsTerminal.ofIso (isTerminal_smallEtaleInclusion_obj_final B E h S hS p x)
      ((smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x)).mapIso
        ((hbX.uniqueUpToIso (SmallEtale.finalIsTerminal E _ _))).symm)))
  exact (bijective_restrictionBaseChange_iff_of_arrowIso_freeModuleUniverse.{v, w, u,
    max (u + 1) v w m}
    (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj) G₀
    φ.op φ'.op _ _ (by rw [← op_comp, ← op_comp, hfac])).2 hβ

end AlgebraicGeometry.Stack

end
