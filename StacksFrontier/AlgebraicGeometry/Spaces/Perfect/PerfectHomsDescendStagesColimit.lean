module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictedPerfectIsoDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.StagesColimitFiveLemma

/-!
# Descent of morphisms of perfect objects as a filtered colimit of homomorphism groups

For a situation `D` of Stacks 09RH, a stage `i ≥ 0` and objects `E`, `K` of the derived category
of the model of `Xᵢ`, the groups `Hom(Lf_{ki}^*E, Lf_{ki}^*K)`, `k ≥ i`, form a directed system
under `AlgebraicGeometry.Space.DescentSituation.raiseStageHom`, with maps
`AlgebraicGeometry.Space.DescentSituation.limitStageHom` to `Hom(Lfᵢ^*E, Lfᵢ^*K)`. The full
faithfulness half of Stacks 09RI–09RJ,
`AlgebraicGeometry.Space.DescentSituation.PerfectHomsDescend`, says exactly that the limit group
is the filtered colimit of this system for perfect `E`, `K`
(`AlgebraicGeometry.Space.DescentSituation.PerfectHomsDescend.isStagesColimit` and
`AlgebraicGeometry.Space.DescentSituation.perfectHomsDescend_of_isStagesColimit`). This is the
form in which the five lemma on directed colimits, `Stacks.IsStagesColimit.of_distTriang`, is
applied in the Mayer–Vietoris step of the proof of Stacks 09RI.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.PerfectHomsDescend.isStagesColimit`
* `AlgebraicGeometry.Space.DescentSituation.perfectHomsDescend_of_isStagesColimit`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.Space.DescentSituation

attribute [local instance high] HasDerivedCategory.standard
attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- **Full faithfulness at the stages as a filtered colimit**: if morphisms of perfect objects
descend in `D`, then for perfect `E`, `K` at a stage `i ≥ 0` the group `Hom(Lfᵢ^*E, Lfᵢ^*K)` is
the filtered colimit of the groups `Hom(Lf_{ki}^*E, Lf_{ki}^*K)`, `k ≥ i`. -/
theorem PerfectHomsDescend.isStagesColimit (hFF : D.PerfectHomsDescend) {i : I}
    (hi : D.base ≤ i)
    {E K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
          AlgebraicSpaces B S hS)).O))}
    (hE : (spacesEtaleModelRingedSite B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
        AlgebraicSpaces B S hS)).IsPerfect E)
    (hK : (spacesEtaleModelRingedSite B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
        AlgebraicSpaces B S hS)).IsPerfect K) :
    Stacks.IsStagesColimit (I := {k : I // i ≤ k})
      (fun k m (h : k ≤ m) x => D.raiseStageHom (E := E) (K := K) k.2 h x)
      (fun k x => D.limitStageHom (E := E) (K := K) k.2 x) where
  ι_trans k m h x := D.limitStageHom_raiseStageHom k.2 h x
  exists_stage φ := by
    obtain ⟨j, hij, ψ, hψ⟩ := (hFF i hi E K hE hK).1 φ
    exact ⟨⟨j, hij⟩, ψ, hψ.symm⟩
  exists_trans_eq k x y hxy := by
    obtain ⟨m, hkm, h⟩ := PerfectHomsDescend.exists_raiseStageHom_eq D hFF hi k.2 hE hK hxy
    exact ⟨⟨m, k.2.trans hkm⟩, hkm, h⟩

/-- The limit reading of the pullback of a morphism `φ` of stage `i` to a stage `k ≥ i` is the
pullback of `φ` to the limit. -/
theorem limitStageHom_map {i k : I} (hik : i ≤ k)
    {E K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
          AlgebraicSpaces B S hS)).O))} (φ : E ⟶ K) :
    D.limitStageHom hik
        ((derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
            (⟨D.system.obj (op k), D.algebraicSpace k⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op i), D.algebraicSpace i⟩))).map φ) =
      (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
          (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨D.system.obj (op i), D.algebraicSpace i⟩))).map φ := by
  rw [limitStageHom, Iso.inv_comp_eq]
  exact D.stageProjectionDerivedPullbackIso_hom_naturality hik φ

/-- Raising the pullback of a morphism `φ` of stage `i` from a stage `k ≥ i` to a stage `m ≥ k`
gives the pullback of `φ` to `m`. -/
theorem raiseStageHom_map {i k m : I} (hik : i ≤ k) (hkm : k ≤ m)
    {E K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
          AlgebraicSpaces B S hS)).O))} (φ : E ⟶ K) :
    D.raiseStageHom hik hkm
        ((derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.system.map (homOfLE hik).op) :
            (⟨D.system.obj (op k), D.algebraicSpace k⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op i), D.algebraicSpace i⟩))).map φ) =
      (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE (hik.trans hkm)).op) :
          (⟨D.system.obj (op m), D.algebraicSpace m⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨D.system.obj (op i), D.algebraicSpace i⟩))).map φ := by
  rw [raiseStageHom, Iso.inv_comp_eq]
  exact spacesEtaleModelDerivedPullbackCompIsoOfEq_hom_naturality B S hS _ _ _ φ

/-- **Full faithfulness at the stages from the filtered colimits**: if for every stage `i ≥ 0`
and perfect `E`, `K` there the group `Hom(Lfᵢ^*E, Lfᵢ^*K)` is the filtered colimit of the groups
`Hom(Lf_{ki}^*E, Lf_{ki}^*K)`, `k ≥ i`, then morphisms of perfect objects descend in `D`. -/
theorem perfectHomsDescend_of_isStagesColimit
    (h : ∀ (i : I) (_ : D.base ≤ i)
      (E K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (spacesEtaleModelRingedTopos B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
          AlgebraicSpaces B S hS)).O))),
      (spacesEtaleModelRingedSite B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
        AlgebraicSpaces B S hS)).IsPerfect E →
      (spacesEtaleModelRingedSite B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
        AlgebraicSpaces B S hS)).IsPerfect K →
      Stacks.IsStagesColimit (I := {k : I // i ≤ k})
        (fun k m (h : k ≤ m) x => D.raiseStageHom (E := E) (K := K) k.2 h x)
        (fun k x => D.limitStageHom (E := E) (K := K) k.2 x)) :
    D.PerfectHomsDescend := by
  intro i hi E K hE hK
  refine ⟨fun φ => ?_, fun φ ψ hφψ => ?_⟩
  · obtain ⟨⟨j, hij⟩, x, hx⟩ := (h i hi E K hE hK).exists_stage φ
    exact ⟨j, hij, x, hx.symm⟩
  · have hι : D.limitStageHom (le_refl i)
        ((derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.system.map (homOfLE (le_refl i)).op) :
            (⟨D.system.obj (op i), D.algebraicSpace i⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op i), D.algebraicSpace i⟩))).map φ) =
        D.limitStageHom (le_refl i)
        ((derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.system.map (homOfLE (le_refl i)).op) :
            (⟨D.system.obj (op i), D.algebraicSpace i⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op i), D.algebraicSpace i⟩))).map ψ) := by
      rw [D.limitStageHom_map, D.limitStageHom_map, hφψ]
    obtain ⟨⟨m, him⟩, hm, hx⟩ := (h i hi E K hE hK).exists_trans_eq ⟨i, le_refl i⟩ _ _ hι
    refine ⟨m, him, ?_⟩
    have h₁ := D.raiseStageHom_map (le_refl i) hm φ
    have h₂ := D.raiseStageHom_map (le_refl i) hm ψ
    exact h₁.symm.trans (hx.trans h₂)

end AlgebraicGeometry.Space.DescentSituation

end
