module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.StageHomSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectHomsDescendStagesColimit

/-!
# The system of homomorphism groups of the stages of Situation 09RH

For a stage `i` of a situation `D` of Stacks 09RH, the derived pullbacks `Lf_{ki}^*` to the
stages `k ≥ i` and `Lfᵢ^*` to the limit, with the transition maps
`AlgebraicGeometry.Space.DescentSituation.raiseStageHom` and the maps to the limit
`AlgebraicGeometry.Space.DescentSituation.limitStageHom`, form a `Stacks.StageHomSystem`. Its
colimit property at `E`, `K` is the filtered colimit statement
`colim_{k ≥ i} Hom(Lf_{ki}^*E, Lf_{ki}^*K) = Hom(Lfᵢ^*E, Lfᵢ^*K)` of Stacks 09RI, so the formal
closure properties of `Stacks.StageHomSystem.IsColimitAt` (isomorphisms, biproducts,
distinguished triangles) apply to it.

## References

* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi

universe u

namespace AlgebraicGeometry.Space

attribute [local instance high] HasDerivedCategory.standard
attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Derived pullback along a morphism of models of spaces-étale sites is additive (it is exact,
Stacks 06YY). -/
theorem additive_derivedPullback_spacesEtaleModelHom (B S hS) {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) :
    (derivedPullback.{u} (spacesEtaleModelHom B S hS f)).Additive := by
  have := isTriangulated_derivedPullback _ (isMorphismOfSites_spacesEtaleModelHom B S hS f)
  infer_instance

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- **Raising a morphism twice is raising it once**: from the stage `k` to `m` and then to `n` is
from `k` to `n`. -/
theorem raiseStageHom_raiseStageHom {i k m n : I} (hik : i ≤ k) (hkm : k ≤ m) (hmn : m ≤ n)
    {E K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
          AlgebraicSpaces B S hS)).O))}
    (x : (derivedPullback (spacesEtaleModelHom B S hS (ObjectProperty.homMk (D.system.map
        (homOfLE hik).op) : (⟨D.system.obj (op k), D.algebraicSpace k⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨D.system.obj (op i), D.algebraicSpace i⟩))).obj E ⟶
      (derivedPullback (spacesEtaleModelHom B S hS (ObjectProperty.homMk (D.system.map
        (homOfLE hik).op) : (⟨D.system.obj (op k), D.algebraicSpace k⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨D.system.obj (op i), D.algebraicSpace i⟩))).obj K) :
    D.raiseStageHom (hik.trans hkm) hmn (D.raiseStageHom hik hkm x) =
      D.raiseStageHom hik (hkm.trans hmn) x := by
  have hc : ∀ Z, (derivedPullback (spacesEtaleModelHom B S hS (ObjectProperty.homMk (D.system.map
        (homOfLE hmn).op) : (⟨D.system.obj (op n), D.algebraicSpace n⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨D.system.obj (op m), D.algebraicSpace m⟩))).map
        (D.stageTransitionDerivedPullbackIso hik hkm Z).hom ≫
        (D.stageTransitionDerivedPullbackIso (hik.trans hkm) hmn Z).hom =
      (D.stageTransitionDerivedPullbackIso hkm hmn _).hom ≫
        (D.stageTransitionDerivedPullbackIso hik (hkm.trans hmn) Z).hom := fun Z =>
    spacesEtaleModelDerivedPullbackCompIsoOfEq_cocycle B S hS _ _ _ _ _ _ _ Z
  have hn := spacesEtaleModelDerivedPullbackCompIsoOfEq_hom_naturality B S hS _ _
    (ObjectProperty.hom_ext _ (by
      show D.system.map (homOfLE hmn).op ≫ D.system.map (homOfLE hkm).op = _
      rw [← D.system.map_comp]
      rfl) :
      (ObjectProperty.homMk (D.system.map (homOfLE hmn).op) :
          (⟨D.system.obj (op n), D.algebraicSpace n⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨D.system.obj (op m), D.algebraicSpace m⟩) ≫
        (ObjectProperty.homMk (D.system.map (homOfLE hkm).op) :
          (⟨D.system.obj (op m), D.algebraicSpace m⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨D.system.obj (op k), D.algebraicSpace k⟩) =
        ObjectProperty.homMk (D.system.map (homOfLE (hkm.trans hmn)).op)) x
  exact conj_raise _ _ _ _ _ _ _ _ _ _ _ (hc E) (hc K) x hn

/-- Raising to a later stage is additive. -/
theorem raiseStageHom_add {i k m : I} (hik : i ≤ k) (hkm : k ≤ m)
    {E K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
          AlgebraicSpaces B S hS)).O))}
    (a b : (derivedPullback (spacesEtaleModelHom B S hS (ObjectProperty.homMk (D.system.map
        (homOfLE hik).op) : (⟨D.system.obj (op k), D.algebraicSpace k⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨D.system.obj (op i), D.algebraicSpace i⟩))).obj E ⟶
      (derivedPullback (spacesEtaleModelHom B S hS (ObjectProperty.homMk (D.system.map
        (homOfLE hik).op) : (⟨D.system.obj (op k), D.algebraicSpace k⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨D.system.obj (op i), D.algebraicSpace i⟩))).obj K) :
    D.raiseStageHom hik hkm (a + b) = D.raiseStageHom hik hkm a + D.raiseStageHom hik hkm b := by
  have := additive_derivedPullback_spacesEtaleModelHom B S hS
    (ObjectProperty.homMk (D.system.map (homOfLE hkm).op) :
      (⟨D.system.obj (op m), D.algebraicSpace m⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨D.system.obj (op k), D.algebraicSpace k⟩)
  simp only [raiseStageHom, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

/-- Derived pullback `Lf_{ki}^*` from a stage `i` to a later stage `k`. -/
abbrev stagePullbackFunctor (i : I) (k : {k : I // i ≤ k}) :=
  derivedPullback.{u} (spacesEtaleModelHom B S hS
    (ObjectProperty.homMk (D.system.map (homOfLE k.2).op) :
      (⟨D.system.obj (op k.1), D.algebraicSpace k.1⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨D.system.obj (op i), D.algebraicSpace i⟩))

/-- Derived pullback `Lfᵢ^*` from a stage `i` to the limit. -/
abbrev limitPullbackFunctor (i : I) :=
  derivedPullback.{u} (spacesEtaleModelHom B S hS
    (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
      (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨D.system.obj (op i), D.algebraicSpace i⟩))

/-- **The system of homomorphism groups of the stages `k ≥ i`** of a situation of Stacks 09RH:
derived pullback `Lf_{ki}^*` to the later stages and `Lfᵢ^*` to the limit, with the transition
maps `AlgebraicGeometry.Space.DescentSituation.raiseStageHom` and the maps to the limit
`AlgebraicGeometry.Space.DescentSituation.limitStageHom`. -/
abbrev stageHomSystem (i : I) : Stacks.StageHomSystem.{u, u + 1, u + 1} {k : I // i ≤ k}
    (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
        AlgebraicSpaces B S hS)).O)))
    (fun k => DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS (⟨D.system.obj (op k.1), D.algebraicSpace k.1⟩ :
        AlgebraicSpaces B S hS)).O)))
    (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ :
        AlgebraicSpaces B S hS)).O))) where
  F k := D.stagePullbackFunctor i k
  F' := D.limitPullbackFunctor i
  raise _ _ k _ h x := D.raiseStageHom k.2 h x
  lim _ _ k x := D.limitStageHom k.2 x
  raise_add _ _ k m h a b := D.raiseStageHom_add k.2 h a b
  raise_map_comp _ _ _ k m h φ a := by
    rw [raiseStageHom_comp, raiseStageHom_map]
  raise_raise _ _ k m n hkm hmn a := D.raiseStageHom_raiseStageHom k.2 hkm hmn a
  lim_add _ _ k a b := by
    have := additive_derivedPullback_spacesEtaleModelHom B S hS
      (ObjectProperty.homMk (D.limitCone.π.app (op k.1)) :
        (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨D.system.obj (op k.1), D.algebraicSpace k.1⟩)
    simp only [limitStageHom, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]
  lim_map_comp _ _ _ k φ a := by
    rw [limitStageHom_comp, limitStageHom_map]
  lim_raise _ _ k m h a := D.limitStageHom_raiseStageHom k.2 h a

/-- The colimit property of `AlgebraicGeometry.Space.DescentSituation.stageHomSystem` is the
filtered colimit statement of
`AlgebraicGeometry.Space.DescentSituation.perfectHomsDescend_of_isStagesColimit`. -/
theorem stageHomSystem_isColimitAt_iff {i : I}
    (E K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS (⟨D.system.obj (op i), D.algebraicSpace i⟩ :
        AlgebraicSpaces B S hS)).O))) :
    (D.stageHomSystem i).IsColimitAt E K ↔
      Stacks.IsStagesColimit (I := {k : I // i ≤ k})
        (fun k m (h : k ≤ m) x => D.raiseStageHom (E := E) (K := K) k.2 h x)
        (fun k x => D.limitStageHom (E := E) (K := K) k.2 x) := Iff.rfl

end DescentSituation

end AlgebraicGeometry.Space
