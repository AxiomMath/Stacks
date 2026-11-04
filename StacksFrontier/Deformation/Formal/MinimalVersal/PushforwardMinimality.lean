module

public import StacksFrontier.Deformation.Formal.MinimalVersal.LevelProjection

/-!
# Minimality of the Artinian pushforwards of the descended object

After every Artinian base change, the descent of the formal object over the image of the descended
subalgebra is minimal. The proof compares that descent with the pushforward of the minimal stage
at a suitable filtration index, which is minimal because pushforward preserves minimality under
(S1).

## Main results

* `Deformation.isMinimalObject_of_stageBaseTowerFormalObject`: after an Artinian base change,
  every cocartesian pushforward of the descended formal object over the image of the descended
  subalgebra is a minimal descent object.

## References

* [Stacks Project, Tag 06T2](https://stacks.math.columbia.edu/tag/06T2)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v w uF vF

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- After an Artinian base change, every cocartesian pushforward of the descended formal object
over the image of the descended subalgebra is a minimal descent object. -/
theorem isMinimalObject_of_stageBaseTowerFormalObject
    [IsNoetherianRing Λ] [Module.Finite Λ k]
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (n : ℕ) {x y : F}
    (a : AdicTruncation.obj ξ.base n ⟶ p.obj x)
    (b : AdicTruncation.obj (stageBaseTowerFormalObject hp hS1 ξ hbound).base n ⟶ p.obj y)
    (toX : ξ.level n ⟶ x)
    (toY : (stageBaseTowerFormalObject hp hS1 ξ hbound).level n ⟶ y)
    (g : y ⟶ x)
    (ha : p.IsHomLift a toX) (_hb : p.IsHomLift b toY)
    (_hcartA : p.IsStronglyCocartesian a toX) (_hcartB : p.IsStronglyCocartesian b toY)
    (hcomm : toY ≫ g = (stageBaseTowerFormalObjectHom hp hS1 ξ hbound).app n ≫ toX)
    (hrange : AlgHom.range (p.map g).hom =
      AlgHom.range ((AdicTruncation.map
        (stageBaseTowerFormalObjectHom hp hS1 ξ hbound).base n ≫ a).hom))
    (hg : Function.Injective (p.map g).hom) :
    IsMinimalObject (⟨Over.mk g, hg⟩ : DescentObject p x) := by
  classical
  let incl := stageBaseTowerFormalObjectHom hp hS1 ξ hbound
  let I := stageBaseTowerIdealFiltration hp hS1 ξ hbound
  let X := minimalStagesFilteredFormalObject hp hS1 ξ hbound
  let c := toAdicIndex I n
  let M := minimalStages hp hS1 ξ c
  let q := stageFormalQuotientToAdic hp hS1 ξ hbound n
  let qStage := cofiberedPushforwardMap hp q (X.level c) (X.level_eq c)
  let e := stageBaseTowerQuotientIso hp hS1 ξ hbound c
  have hMbase : p.obj M.obj.left = stageBaseTower hp hS1 ξ c := rfl
  have hobj : cofiberedPushforwardObj hp e.inv M.obj.left hMbase = X.level c := by
    dsimp [X, minimalStagesFilteredFormalObject]
  let s₀ := cofiberedPushforwardMap hp e.inv M.obj.left hMbase
  let s := s₀ ≫ eqToHom hobj
  let k := s ≫ qStage ≫ toY
  let path := formalObjectPath ξ n c (toAdicIndex_ge I n)
  let g₀ := path ≫ toX
  let D := descentPushforward p hp g₀
  let W := D.functor.obj M
  let i := D.inclusion M
  let v := W.obj.hom
  have hfactor : k ≫ g = (s ≫ qStage) ≫ (incl.app n ≫ toX) := by
    change (s ≫ qStage ≫ toY) ≫ g = _
    rw [Category.assoc s (qStage ≫ toY) g, Category.assoc qStage toY g,
      Category.assoc s qStage]
    exact congrArg (s ≫ qStage ≫ ·) hcomm
  have happ : qStage ≫ incl.app n = stageFilteredLevelToOriginal
      hp hS1 ξ hbound n := by
    simpa [incl, stageBaseTowerFormalObjectHom, qStage, q, X, I] using
      stageBaseTowerFormalObjectApp_fac hp hS1 ξ hbound n
  have hsFac : s ≫ stageFilteredLevelMapAtStage hp hS1 ξ hbound c = M.obj.hom := by
    simpa [s, s₀, hobj, M, X] using
      stageFilteredLevelMapAtStage_fac hp hS1 ξ hbound c
  have hcomm' : k ≫ g = i ≫ v := by
    calc
      k ≫ g = (s ≫ qStage) ≫ (incl.app n ≫ toX) := hfactor
      _ = (s ≫ (qStage ≫ incl.app n)) ≫ toX := by
        rw [Category.assoc s qStage (incl.app n ≫ toX), ← Category.assoc qStage (incl.app n) toX,
          ← Category.assoc s (qStage ≫ incl.app n) toX]
      _ = (M.obj.hom ≫ path) ≫ toX := congrArg (· ≫ toX) <| by
        rw [happ, ← hsFac, Category.assoc s]
        rfl
      _ = M.obj.hom ≫ g₀ := by simp [g₀, path, Category.assoc]
      _ = i ≫ v := (D.inclusion_fac M).symm
  let := incl.app_lift n
  have hcanLift : p.IsHomLift
      (AdicTruncation.map incl.base n ≫ a) (incl.app n ≫ toX) :=
    @IsHomLift.comp _ _ _ _ p _ _ _ _ _ _
      (AdicTruncation.map incl.base n) a (incl.app n) toX
      (incl.app_lift n) ha
  have hcanRange := algHom_range_eq_of_isHomLift
    (AdicTruncation.map incl.base n ≫ a) (incl.app n ≫ toX) hcanLift
  have hq : Function.Surjective q.hom := by
    dsimp [q, stageFormalQuotientToAdic]
    exact Ideal.Quotient.factor_surjective (toAdicIndex_le I n)
  have hs₀iso : IsIso (p.map s₀) := map_isIso_of_isHomLift_isIso e.inv s₀ inferInstance
    (cofiberedPushforwardMap_lift hp e.inv M.obj.left hMbase)
  have hsiso : IsIso (p.map s) := by
    dsimp [s]
    rw [Functor.map_comp]
    infer_instance
  have hs : Function.Surjective (p.map s).hom :=
    artinianHom_surjective_of_isIso (p.map s)
  have hqStage : Function.Surjective (p.map qStage).hom :=
    map_surjective_of_isHomLift_surjective q qStage hq
      (cofiberedPushforwardMap_lift hp q (X.level c) (X.level_eq c))
  have hsourceSurj : Function.Surjective (p.map (s ≫ qStage)).hom := by
    rw [Functor.map_comp, ArtinianLocalAlgCat.comp_hom]
    exact hqStage.comp hs
  have hfactorMap : p.map (k ≫ g) =
      p.map (s ≫ qStage) ≫ p.map (incl.app n ≫ toX) := by
    rw [hfactor, Functor.map_comp]
  have hRangeComp : AlgHom.range (p.map (k ≫ g)).hom =
      AlgHom.range (p.map (incl.app n ≫ toX)).hom := by
    rw [hfactorMap, ArtinianLocalAlgCat.comp_hom]
    exact algHom_range_comp_eq_of_surjective
      (p.map (s ≫ qStage)).hom (p.map (incl.app n ≫ toX)).hom hsourceSurj
  have hRangeG : AlgHom.range (p.map g).hom =
      AlgHom.range ((p.map k ≫ p.map g).hom) := by
    calc
      AlgHom.range (p.map g).hom =
          AlgHom.range ((AdicTruncation.map incl.base n ≫ a).hom) := hrange
      _ = AlgHom.range (p.map (incl.app n ≫ toX)).hom := hcanRange
      _ = AlgHom.range (p.map (k ≫ g)).hom := hRangeComp.symm
      _ = AlgHom.range ((p.map k ≫ p.map g).hom) := by
            rw [← p.map_comp]
  have hRangeV : AlgHom.range (p.map v).hom =
      AlgHom.range ((p.map i ≫ p.map v).hom) := by
    calc
      AlgHom.range (p.map v).hom =
          AlgHom.range (p.map (M.obj.hom ≫ g₀)).hom := D.base_range M
      _ = AlgHom.range (p.map (i ≫ v)).hom := by
            rw [← D.inclusion_fac M]
      _ = AlgHom.range ((p.map i ≫ p.map v).hom) := by rw [← p.map_comp]
  have hmin : IsMinimalObject (W : DescentObject p x) := by
    change IsMinimalObject (D.functor.obj M)
    exact isMinimal_descentPushforward
      p hp hS1 g₀ M (minimalStages_spec hp hS1 ξ |>.1 c)
  exact minimalDescent_iso_of_same_image hp k i g v hcomm' hg W.property
    hRangeG hRangeV hmin

end Deformation

end
