module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfEtaleCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesDirectImage

/-!
# fppf and étale higher direct images of an `ε_*`-acyclic module (Stacks 075R (3))

Let `f : 𝒳 ⟶ 𝒴` be a `1`-morphism of algebraic stacks and `ε : 𝒳_fppf ⟶ 𝒳_étale` the comparison
morphisms.  **Stacks 075R (3)** says that for `ℱ` in `LQCoh^fbc(𝒪_𝒳)` the higher direct image
`R^if_*ℱ` (fppf) is the fppf sheafification of the higher direct image computed in the étale
topology.  The source deduces this from **Stacks 075G** and part (2).  The argument here is
functorial instead, and needs only that `ℱ` be `ε_*`-acyclic (which is part (1)):

* `ε^*ε_* = 𝟭` (`ε_*` is fully faithful) and `ε^*` is exact, so
  `R^if_{fppf,*}ℱ = R^i(ε^* ∘ ε_* ∘ f_{fppf,*})ℱ = ε^*R^i(ε_* ∘ f_{fppf,*})ℱ`;
* `ε_* ∘ f_{fppf,*} = f_{ét,*} ∘ ε_*`, the direct images being right Kan extensions of the
  underlying presheaves, which do not see the topology
  (`AlgebraicGeometry.Stack.stackModuleDirectImageEtaleComparisonIso`);
* `ε_*` preserves injectives, so `R^i(f_{ét,*} ∘ ε_*)ℱ = R^if_{ét,*}(ε_*ℱ)` for `ε_*`-acyclic `ℱ`.

## Main results

* `Stacks.RightDerivedComp.nonempty_rightDerived_obj_iso_of_comm`: the abstract form.
* `Stacks.SheafOfModules.directImageOfEqComparisonPushforwardIso`: the direct image along a
  continuous and cocontinuous functor commutes with coarsening the topologies.
* `AlgebraicGeometry.Stack.stackModuleDirectImageEtaleComparisonIso`:
  `ε_* ∘ f_{fppf,*} ≅ f_{ét,*} ∘ ε_*` at module universe `u`.
* `AlgebraicGeometry.Stack.nonempty_rightDerived_stackModuleDirectImage_iso_of_isZero`:
  `R^if_{fppf,*}ℱ ≅ ε^*R^if_{ét,*}(ε_*ℱ)` for `ε_*`-acyclic `ℱ`.

## References

* [Stacks Project, Tag 075R](https://stacks.math.columbia.edu/tag/075R)
* [Stacks Project, Tag 075G](https://stacks.math.columbia.edu/tag/075G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Stacks.RightDerivedComp

variable {A₀ B₀ C₀ D₀ : Type*} [Category* A₀] [Category* B₀] [Category* C₀] [Category* D₀]
  [Abelian A₀] [Abelian B₀] [Abelian C₀] [Abelian D₀]
  [EnoughInjectives A₀] [EnoughInjectives B₀]
  (P : A₀ ⥤ C₀) (Q : B₀ ⥤ D₀) (G : A₀ ⥤ B₀) (H : C₀ ⥤ D₀) (L : D₀ ⥤ C₀)
  [hP : P.Additive] [hQ : Q.Additive] [hG : G.Additive] [hH : H.Additive] [hL : L.Additive]
  [hLh : L.PreservesHomology] [hGl : PreservesFiniteLimits G] [hGi : G.PreservesInjectiveObjects]

/-- **Derived functors of a composite through an exact localisation.**  Let `P : 𝒜 ⥤ 𝒞`,
`Q : ℬ ⥤ 𝒟`, `G : 𝒜 ⥤ ℬ` and `H : 𝒞 ⥤ 𝒟` with `P ⋙ H ≅ G ⋙ Q`, and let `L : 𝒟 ⥤ 𝒞` be exact with
`H ⋙ L ≅ 𝟭`.  If `G` is left exact, preserves injectives and `X` is `G`-acyclic, then
`R^nP(X) ≅ L(R^nQ(G X))`. -/
theorem nonempty_rightDerived_obj_iso_of_comm (e : H ⋙ L ≅ 𝟭 C₀) (c : P ⋙ H ≅ G ⋙ Q) {X : A₀}
    (hX : ∀ n, 0 < n → IsZero ((G.rightDerived n).obj X)) (n : ℕ) :
    Nonempty ((P.rightDerived n).obj X ≅ L.obj ((Q.rightDerived n).obj (G.obj X))) := by
  obtain ⟨e₁⟩ := rightDerived_comp_iso_of_preservesHomology (P ⋙ H) L n X
  exact ⟨(Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
      ((Functor.rightUnitor P).symm ≪≫ Functor.isoWhiskerLeft P e.symm ≪≫
        (Functor.associator _ _ _).symm) n).app X ≪≫ e₁.symm ≪≫
    L.mapIso ((Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso c n).app X ≪≫
      objIso G (injectiveResolution X) hX Q n)⟩

end Stacks.RightDerivedComp

namespace Stacks.SheafOfModules

universe r w' uC vC uD vD

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D] (f : C ⥤ D)
  {J J' : GrothendieckTopology C} {K K' : GrothendieckTopology D} (hJ : J' ≤ J) (hK : K' ≤ K)
  [f.IsContinuous J K] [f.IsCocontinuous J K] [f.IsContinuous J' K'] [f.IsCocontinuous J' K']
  (O : Sheaf K RingCat.{r})

/-- **The direct image commutes with coarsening the topologies**: for a functor continuous and
cocontinuous for both pairs of topologies `J, K` and `J' ≤ J, K' ≤ K`, reading the direct image
of a `J`-sheaf of modules as a `K'`-sheaf is the direct image of the module read as a `J'`-sheaf.
Both have the same underlying presheaf of modules, the right Kan extension. -/
def directImageOfEqComparisonPushforwardIso {T : Sheaf J RingCat.{r}}
    (hT : T = (f.sheafPushforwardContinuous RingCat.{r} J K).obj O)
    (hT' : ringOfLe hJ T = (f.sheafPushforwardContinuous RingCat.{r} J' K').obj (ringOfLe hK O)) :
    SheafOfModules.directImageOfEq.{r, w'} f J K O hT ⋙
        comparisonPushforward.{uD, vD, r, max uC vD w'} hK O ≅
      comparisonPushforward.{uC, vC, r, max uC vD w'} hJ T ⋙
        SheafOfModules.directImageOfEq.{r, w'} f J' K' (ringOfLe hK O) hT' := by
  subst hT
  have : hT' = rfl := rfl
  subst this
  exact NatIso.ofComponents (fun _ ↦ (_root_.SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (fun _ _ _ ↦ rfl))) (fun _ ↦ rfl)

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `ε_*` on modules of an algebraic stack at module universe `u + 1`. -/
abbrev etaleComparisonPushforwardSucc (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    SheafOfModules.{u + 1} (FibredSite.ringStructureSheafCore B S hS 𝒵.val.val.p
      𝒵.val.isFiberedInGroupoids .fppf) ⥤
    SheafOfModules.{u + 1} (FibredSite.ringStructureSheafCore B S hS 𝒵.val.val.p
      𝒵.val.isFiberedInGroupoids .etale) :=
  Stacks.SheafOfModules.comparisonPushforward.{u + 1, u, u, u + 1}
    (BigFppfOver.associatedTopology_le_fppf B S hS 𝒵.val.val.p .etale)
    (fppfSiteRingSheaf B S hS 𝒵.val.val.p 𝒵.val.isFiberedInGroupoids)

/-- `ε_*` commutes with the universe lift of modules. -/
def etaleComparisonPushforwardULiftIso (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    etaleComparisonPushforward B S hS 𝒵.val.val.p 𝒵.val.isFiberedInGroupoids ⋙
        stackModuleULift B S hS .etale 𝒵 ≅
      stackModuleULift B S hS .fppf 𝒵 ⋙ etaleComparisonPushforwardSucc B S hS 𝒵 :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (fun _ _ _ ↦ rfl))) (fun _ ↦ rfl)

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- `ε_* ∘ f_{fppf,*} ≅ f_{ét,*} ∘ ε_*` at module universe `u + 1`. -/
def stackModuleDirectImageSuccEtaleComparisonIso :
    stackModuleDirectImageSucc B S hS f .fppf ⋙ etaleComparisonPushforwardSucc B S hS 𝒴 ≅
      etaleComparisonPushforwardSucc B S hS 𝒳 ⋙ stackModuleDirectImageSucc B S hS f .etale := by
  letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  letI : 𝒴.val.val.p.IsFibered := 𝒴.val.isFiberedInGroupoids.isFibered
  have hF := 𝒴.val.isFiberedInGroupoids.isFibredOneMorphism
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
  letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
    (BigFppfOver.baseOverTopology B S hS .fppf)).1
  letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
    (BigFppfOver.baseOverTopology B S hS .fppf)).2
  letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
    (BigFppfOver.baseOverTopology B S hS .etale)).1
  letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
    (BigFppfOver.baseOverTopology B S hS .etale)).2
  exact Stacks.SheafOfModules.directImageOfEqComparisonPushforwardIso
    (CatFiberedInGroupoids.homFunctor f.hom)
    (BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p .etale)
    (BigFppfOver.associatedTopology_le_fppf B S hS 𝒴.val.val.p .etale) _
    (Stacks.RelativeCech.ringStructureSheafCore_eq_pushforward B S hS 𝒳.val.val.p 𝒴.val.val.p
      𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom) .fppf)
    (Stacks.RelativeCech.ringStructureSheafCore_eq_pushforward B S hS 𝒳.val.val.p 𝒴.val.val.p
      𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom) .etale)

/-- **`ε_* ∘ f_{fppf,*} ≅ f_{ét,*} ∘ ε_*`** for a `1`-morphism of algebraic stacks at module
universe `u`: through the fully faithful universe lift, this is the `u + 1` statement. -/
def stackModuleDirectImageEtaleComparisonIso :
    stackModuleDirectImage B S hS f .fppf ⋙
        etaleComparisonPushforward B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids ≅
      etaleComparisonPushforward B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids ⋙
        stackModuleDirectImage B S hS f .etale :=
  ((stackModuleULiftFullyFaithful B S hS .etale 𝒴).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (etaleComparisonPushforwardULiftIso B S hS 𝒴) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (stackModuleDirectImageULiftIso B S hS f .fppf) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (stackModuleDirectImageSuccEtaleComparisonIso B S hS f) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (etaleComparisonPushforwardULiftIso B S hS 𝒳).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (stackModuleDirectImageULiftIso B S hS f .etale).symm ≪≫
      (Functor.associator _ _ _).symm)

attribute [local instance] enoughInjectives_moduleRingSheaf

/-- `ε_*` on the modules of an algebraic stack, read between the categories `StackModules` in
which the direct images `AlgebraicGeometry.Stack.stackModuleDirectImage` are stated. -/
def stackModulesEtaleComparison (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    StackModules B S hS .fppf 𝒵 ⥤ StackModules B S hS .etale 𝒵 :=
  etaleComparisonPushforward B S hS 𝒵.val.val.p 𝒵.val.isFiberedInGroupoids

/-- `ε^*`, fppf sheafification, on the modules of an algebraic stack, read between the
categories `StackModules`. -/
def stackModulesEtaleComparisonPullback (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    StackModules B S hS .etale 𝒵 ⥤ StackModules B S hS .fppf 𝒵 :=
  Stacks.Cohomology.CompareTopologies.pullback.{u + 1, u, u, u}
    (BigFppfOver.associatedTopology_le_fppf B S hS 𝒵.val.val.p .etale)
    (fppfSiteRingSheaf B S hS 𝒵.val.val.p 𝒵.val.isFiberedInGroupoids)

/-- The comparison functor `ε_*` on modules of an algebraic stack is additive. -/
instance (𝒵 : AlgebraicStacks.{u, w} B S hS) : (stackModulesEtaleComparison B S hS 𝒵).Additive :=
  SheafOfModules.pushforward_additive _

/-- The comparison functor `ε_*` on modules of an algebraic stack preserves finite limits. -/
instance (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    PreservesFiniteLimits (stackModulesEtaleComparison B S hS 𝒵) :=
  preservesFiniteLimits_etaleComparisonPushforward B S hS 𝒵.val.val.p 𝒵.val.isFiberedInGroupoids

/-- The comparison functor `ε_*` on modules of an algebraic stack preserves injective objects. -/
instance (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    (stackModulesEtaleComparison B S hS 𝒵).PreservesInjectiveObjects :=
  preservesInjectiveObjects_etaleComparisonPushforward B S hS 𝒵.val.val.p
    𝒵.val.isFiberedInGroupoids

/-- The functor `ε^*` on modules of an algebraic stack is additive. -/
instance (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    (stackModulesEtaleComparisonPullback B S hS 𝒵).Additive :=
  Stacks.Cohomology.CompareTopologies.additive_pullback _ _

/-- The functor `ε^*` on modules of an algebraic stack preserves finite limits. -/
instance (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    PreservesFiniteLimits (stackModulesEtaleComparisonPullback B S hS 𝒵) :=
  Stacks.Cohomology.CompareTopologies.preservesFiniteLimits_pullback _ _

/-- The functor `ε^*` on modules of an algebraic stack preserves finite colimits. -/
instance (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    PreservesFiniteColimits (stackModulesEtaleComparisonPullback B S hS 𝒵) :=
  Stacks.Cohomology.CompareTopologies.preservesFiniteColimits_pullback _ _

/-- `ε^*ε_* ≅ 𝟭`: `ε_*` is fully faithful. -/
def stackModulesEtaleComparisonCounitIso (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    stackModulesEtaleComparison B S hS 𝒵 ⋙ stackModulesEtaleComparisonPullback B S hS 𝒵 ≅
      𝟭 _ :=
  have hFull : (etaleComparisonPushforward B S hS 𝒵.val.val.p 𝒵.val.isFiberedInGroupoids).Full :=
    ⟨fun g => ⟨⟨g.val⟩, rfl⟩⟩
  have hFaith : (etaleComparisonPushforward B S hS 𝒵.val.val.p
      𝒵.val.isFiberedInGroupoids).Faithful :=
    ⟨fun h => SheafOfModules.hom_ext (congrArg (fun k => k.val) h)⟩
  @asIso _ _ _ _ (etaleComparisonAdjunction B S hS 𝒵.val.val.p 𝒵.val.isFiberedInGroupoids).counit
    (@Adjunction.counit_isIso_of_R_fully_faithful _ _ _ _ _ _
      (etaleComparisonAdjunction B S hS 𝒵.val.val.p 𝒵.val.isFiberedInGroupoids) hFull hFaith)

/-- `f_{ét,*} ∘ ε_* ≅ ε_* ∘ f_{fppf,*}`, in the `StackModules` reading. -/
def stackModulesDirectImageEtaleComparisonIso :
    stackModuleDirectImage B S hS f .fppf ⋙ stackModulesEtaleComparison B S hS 𝒴 ≅
      stackModulesEtaleComparison B S hS 𝒳 ⋙ stackModuleDirectImage B S hS f .etale :=
  stackModuleDirectImageEtaleComparisonIso B S hS f

/-- **Stacks 075R (3) for an `ε_*`-acyclic module**: for a `1`-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks and `ℱ` with `R^nε_*ℱ = 0` for `n > 0`, `R^if_*ℱ` on the fppf sites is the fppf
sheafification `ε^*` of `R^if_*(ε_*ℱ)` on the étale sites. -/
theorem nonempty_rightDerived_stackModuleDirectImage_iso_of_isZero
    (F : StackModules B S hS .fppf 𝒳)
    (hF : ∀ n, 0 < n → IsZero (((stackModulesEtaleComparison B S hS 𝒳).rightDerived n).obj F))
    (i : ℕ) :
    Nonempty (((stackModuleDirectImage B S hS f .fppf).rightDerived i).obj F ≅
      (stackModulesEtaleComparisonPullback B S hS 𝒴).obj
        (((stackModuleDirectImage B S hS f .etale).rightDerived i).obj
          ((stackModulesEtaleComparison B S hS 𝒳).obj F))) := by
  have : (stackModulesEtaleComparisonPullback B S hS 𝒴).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  have key := Stacks.RightDerivedComp.nonempty_rightDerived_obj_iso_of_comm
    (stackModuleDirectImage B S hS f .fppf) (stackModuleDirectImage B S hS f .etale)
    (stackModulesEtaleComparison B S hS 𝒳) (stackModulesEtaleComparison B S hS 𝒴)
    (stackModulesEtaleComparisonPullback B S hS 𝒴)
    (stackModulesEtaleComparisonCounitIso B S hS 𝒴)
    (stackModulesDirectImageEtaleComparisonIso B S hS f) hF i
  exact key

end AlgebraicGeometry.Stack
