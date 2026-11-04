module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineKummerGenerator
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineKummerValuation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleZariskiCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.DerivedFunctorBoundary

/-!
# The Kummer class of the coordinate has order `N` at every point over the origin

Let `j : U₀ ⟶ U` be a morphism of schemes and `N` invertible on `U₀`. The Kummer coboundary
`∂ : j_* 𝐆_m ⟶ R¹ j_* μ_N` (`Stacks.EtaleCohomology.Purity.kummerDirectImageδ`) kills exactly the
`N`-th powers, stalkwise: the long exact sequence of the higher direct images of the Kummer
sequence gives an exact sequence `j_* 𝐆_m ⟶ j_* 𝐆_m ⟶ R¹ j_* μ_N` (the first map the `N`-th power),
and stalks are exact.

For `j : 𝐆_m ⟶ 𝐀¹_k`, a geometric point `x` over the origin and the coordinate `t`, it follows that
`n • (∂ t)_x = 0` only if `N ∣ n`: otherwise `t^n` would be an `N`-th power on `W ×_{𝐀¹} 𝐆_m` for
an étale neighbourhood `W` of `x`, which the valuation at the image of `x` in `W` forbids
(`Stacks.EtaleCohomology.Purity.dvd_of_pow_eq_coordinate_pow_pullback`).

## Main results

* `Stacks.EtaleCohomology.Purity.exists_stalk_powMap_eq_of_kummerDirectImageδ`.
* `Stacks.EtaleCohomology.Purity.dvd_of_nsmul_germ_localKummerClass_eq_zero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  TopologicalSpace Opposite

universe w u

namespace Stacks.EtaleCohomology.Purity

attribute [-instance] CategoryTheory.catToReflQuiver

open Stacks.Kummer

section Exactness

variable {U₀ U : Scheme.{u}} (j : U₀ ⟶ U)
  [HasDerivedCategory.{w} (Sheaf (smallEtaleTopology U₀) Ab.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallEtaleTopology U) Ab.{u + 1})] {N : ℕ}

/-- **`∂` kills exactly the `N`-th powers, stalkwise**: an element of the stalk of `j_* 𝐆_m` at a
geometric point which `∂` kills is an `N`-th power there. -/
theorem exists_stalk_powMap_eq_of_kummerDirectImageδ (hN0 : N ≠ 0)
    (hN : IsUnit ((N : ℕ) : Γ(U₀, ⊤))) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ U)
    (s : ToType ((smallEtaleStalkAb x).obj
      ((smallEtalePushforwardAb j).obj (multiplicativeSheaf.{u, 0} U₀))))
    (hs : (smallEtaleStalkAb x).map (kummerDirectImageδ j hN0 hN) s = 0) :
    ∃ z, (smallEtaleStalkAb x).map
      ((smallEtalePushforwardAb j).map (powMap.{u, 0} U₀ N)) z = s := by
  have : PreservesLimitsOfSize.{0, 0} (smallEtalePushforwardAb j) :=
    (smallEtaleAdjunctionAb j).rightAdjoint_preservesLimits
  have := Stacks.RightDerivedPlus.isIso_rightDerivedZeroUnit (smallEtalePushforwardAb j)
    (multiplicativeSheaf.{u, 0} U₀)
  have hn : (smallEtalePushforwardAb j).map (powMap.{u, 0} U₀ N) ≫
      (Stacks.RightDerivedPlus.rightDerivedZeroUnit (smallEtalePushforwardAb j)
          (multiplicativeSheaf.{u, 0} U₀) ≫
        (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb j) 0).inv.app
          (multiplicativeSheaf.{u, 0} U₀)) =
      (Stacks.RightDerivedPlus.rightDerivedZeroUnit (smallEtalePushforwardAb j)
          (multiplicativeSheaf.{u, 0} U₀) ≫
        (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb j) 0).inv.app
          (multiplicativeSheaf.{u, 0} U₀)) ≫
        ((smallEtalePushforwardAb j).rightDerived 0).map (powMap.{u, 0} U₀ N) := by
    rw [reassoc_of% (Stacks.DerivedFunctor.rightDerivedZeroUnit_naturality
      (smallEtalePushforwardAb j) (powMap.{u, 0} U₀ N)), Category.assoc]
    exact congrArg (_ ≫ ·)
      ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb j) 0).inv.naturality
        (powMap.{u, 0} U₀ N))
  obtain ⟨α, hαdef⟩ : ∃ α, α = Stacks.RightDerivedPlus.rightDerivedZeroUnit
      (smallEtalePushforwardAb j) (multiplicativeSheaf.{u, 0} U₀) ≫
        (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb j) 0).inv.app
          (multiplicativeSheaf.{u, 0} U₀) := ⟨_, rfl⟩
  have hα : IsIso α := by rw [hαdef]; infer_instance
  rw [← hαdef] at hn
  have hδ : (smallEtaleStalkAb x).map (kummerDirectImageδ j hN0 hN) =
      (smallEtaleStalkAb x).map α ≫ (smallEtaleStalkAb x).map
        ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
          (smallEtalePushforwardAb j)).δ (kummerSequence_shortExact.{u, 0} U₀ hN0 hN) 0) := by
    rw [kummerDirectImageδ_eq, ← hαdef]
    exact (smallEtaleStalkAb x).map_comp _ _
  have hex := ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (smallEtalePushforwardAb j)).exact_δ₁ (kummerSequence_shortExact.{u, 0} U₀ hN0 hN) 0).map
      (smallEtaleStalkAb x)
  rw [ShortComplex.ab_exact_iff] at hex
  have hs' : (smallEtaleStalkAb x).map
      ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
        (smallEtalePushforwardAb j)).δ (kummerSequence_shortExact.{u, 0} U₀ hN0 hN) 0)
        ((smallEtaleStalkAb x).map α s) = 0 :=
    (ConcreteCategory.congr_hom hδ s).symm.trans hs
  obtain ⟨z₁, hz₁⟩ := hex ((smallEtaleStalkAb x).map α s) hs'
  refine ⟨(smallEtaleStalkAb x).map (inv α) z₁, ?_⟩
  have hinj : Function.Injective ((smallEtaleStalkAb x).map α) :=
    ((ConcreteCategory.isIso_iff_bijective ((smallEtaleStalkAb x).map α)).1 inferInstance).1
  have e1 : ∀ v, (smallEtaleStalkAb x).map α
      ((smallEtaleStalkAb x).map ((smallEtalePushforwardAb j).map (powMap.{u, 0} U₀ N)) v) =
      (smallEtaleStalkAb x).map (((smallEtalePushforwardAb j).rightDerived 0).map
        (powMap.{u, 0} U₀ N)) ((smallEtaleStalkAb x).map α v) := fun v =>
    ConcreteCategory.congr_hom
      (show (smallEtaleStalkAb x).map ((smallEtalePushforwardAb j).map (powMap.{u, 0} U₀ N)) ≫
          (smallEtaleStalkAb x).map α = (smallEtaleStalkAb x).map α ≫
          (smallEtaleStalkAb x).map (((smallEtalePushforwardAb j).rightDerived 0).map
            (powMap.{u, 0} U₀ N)) by
        rw [← (smallEtaleStalkAb x).map_comp, hn, (smallEtaleStalkAb x).map_comp]) v
  have e2 : (smallEtaleStalkAb x).map α ((smallEtaleStalkAb x).map (inv α) z₁) = z₁ :=
    ConcreteCategory.congr_hom
      (show (smallEtaleStalkAb x).map (inv α) ≫ (smallEtaleStalkAb x).map α = 𝟙 _ by
        rw [← (smallEtaleStalkAb x).map_comp, IsIso.inv_hom_id,
          CategoryTheory.Functor.map_id]) z₁
  apply hinj
  calc (smallEtaleStalkAb x).map α
        ((smallEtaleStalkAb x).map ((smallEtalePushforwardAb j).map (powMap.{u, 0} U₀ N))
          ((smallEtaleStalkAb x).map (inv α) z₁))
      = (smallEtaleStalkAb x).map (((smallEtalePushforwardAb j).rightDerived 0).map
          (powMap.{u, 0} U₀ N)) ((smallEtaleStalkAb x).map α
            ((smallEtaleStalkAb x).map (inv α) z₁)) := e1 _
    _ = (smallEtaleStalkAb x).map (((smallEtalePushforwardAb j).rightDerived 0).map
          (powMap.{u, 0} U₀ N)) z₁ := by rw [e2]
    _ = (smallEtaleStalkAb x).map α s := hz₁

end Exactness

section AffineLine

variable {k : Type u} [Field k]

/-- The coordinate on `𝐆_m`, restricted to the base change `W ×_{𝐀¹} 𝐆_m` of an étale `W`, is the
pullback of the coordinate along `W ×_{𝐀¹} 𝐆_m ⟶ 𝐀¹`. -/
theorem appTop_baseChange_puncturedFunction_top {W : (affineLine k).Etale}
    (g : W ⟶ (opensToEtale (affineLine k)).obj ⊤) :
    ((smallEtaleBaseChange (punctured k).ι).map g).left.appTop
        (puncturedFunction (punctured k).ι ⊤ (coordinate k)) =
      (pullback.fst W.hom (punctured k).ι ≫ W.hom).appTop (coordinate k) := by
  have h1 : ((smallEtaleBaseChange (punctured k).ι).map g).left ≫
      pullback.fst ((opensToEtale (affineLine k)).obj ⊤).hom (punctured k).ι =
        pullback.fst W.hom (punctured k).ι ≫ g.left := pullback.lift_fst _ _ _
  have hw : g.left ≫ ((opensToEtale (affineLine k)).obj ⊤).hom = W.hom :=
    Over.w ((Scheme.Etale.forget (affineLine k)).map g)
  have hc : ((smallEtaleBaseChange (punctured k).ι).map g).left ≫
      puncturedOpenHom (punctured k).ι ⊤ = pullback.fst W.hom (punctured k).ι ≫ W.hom :=
    (Category.assoc _ _ _).symm.trans ((h1 =≫ ((opensToEtale (affineLine k)).obj ⊤).hom).trans
      ((Category.assoc _ _ _).trans (congrArg (pullback.fst W.hom (punctured k).ι ≫ ·) hw)))
  have key : (puncturedOpenHom (punctured k).ι ⊤).appLE ⊤ ⊤
      (top_le_preimage_puncturedOpenHom (punctured k).ι ⊤) ≫
      ((smallEtaleBaseChange (punctured k).ι).map g).left.appLE ⊤ ⊤ le_top =
      (pullback.fst W.hom (punctured k).ι ≫ W.hom).appLE ⊤ ⊤ le_top :=
    (Scheme.Hom.appLE_comp_appLE _ _ ⊤ ⊤ ⊤ _ _).trans (appLE_eq_of_eq hc ⊤ ⊤ _ _)
  rw [← Stacks.AlgebraicGeometry.GlobalSectionsBaseChange.appLE_top_top _ le_top,
    ← Stacks.AlgebraicGeometry.GlobalSectionsBaseChange.appLE_top_top
      (pullback.fst W.hom (punctured k).ι ≫ W.hom) le_top]
  exact congrArg (fun φ => φ.hom (coordinate k)) key

/-- A geometric point has at most one lift to the whole scheme, read as an étale object. -/
instance subsingleton_fiber_opensToEtale_top {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    Subsingleton ((Scheme.pointSmallEtale x).fiber.obj ((opensToEtale X).obj ⊤)) := by
  have : Mono ((opensToEtale X).obj ⊤).hom := inferInstanceAs (Mono (⊤ : X.Opens).ι)
  refine ⟨fun p q => ?_⟩
  have hp : (show Over.mk x ⟶ (Scheme.Etale.forget X).obj ((opensToEtale X).obj ⊤) from p).left ≫
      ((opensToEtale X).obj ⊤).hom = x := Over.w p
  have hq : (show Over.mk x ⟶ (Scheme.Etale.forget X).obj ((opensToEtale X).obj ⊤) from q).left ≫
      ((opensToEtale X).obj ⊤).hom = x := Over.w q
  exact Over.OverMorphism.ext ((cancel_mono ((opensToEtale X).obj ⊤).hom).1 (hp.trans hq.symm))

variable [HasDerivedCategory.{w} (Sheaf (smallEtaleTopology (punctured k).toScheme) Ab.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallEtaleTopology (affineLine k)) Ab.{u + 1})]

/-- **The Kummer class of the coordinate has order `N` at every geometric point over the
origin**: `n • (∂ t)_x = 0` only if `N ∣ n`. -/
theorem dvd_of_nsmul_germ_localKummerClass_eq_zero {N : ℕ} (hN0 : N ≠ 0)
    (hN : IsUnit ((N : ℕ) : Γ((punctured k).toScheme, ⊤)))
    (ht : IsUnit (puncturedFunction (punctured k).ι ⊤ (coordinate k)))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ affineLine k)
    (hx : Set.range x.base ⊆ ((punctured k : Set (affineLine k)))ᶜ)
    (y : (Scheme.pointSmallEtale x).fiber.obj ((opensToEtale (affineLine k)).obj ⊤)) (n : ℕ)
    (h : n • (Scheme.pointSmallEtale x).toPresheafFiber ((opensToEtale (affineLine k)).obj ⊤) y
        (kummerTarget (punctured k).ι N).obj
        (localKummerClass (punctured k).ι hN0 hN ⊤ (coordinate k) ht) = 0) : N ∣ n := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget Ab.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} (forget Ab.{u + 1})
  let j := (punctured k).ι
  let Φ := Scheme.pointSmallEtale x
  let T := (opensToEtale (affineLine k)).obj ⊤
  let P := smallEtalePushforwardAb j
  let G := multiplicativeSheaf.{u, 0} (punctured k).toScheme
  have ht' : IsUnit (M := Γ(((smallEtaleBaseChange j).obj T).left, ⊤))
      (puncturedFunction (punctured k).ι ⊤ (coordinate k)) := ht
  have hpow : (ofUnit.{u, 0} (X := (punctured k).toScheme) (U := puncturedOpen j ⊤)
      (ht'.unit ^ n)) = n • ofUnit.{u, 0} (X := (punctured k).toScheme)
        (U := puncturedOpen j ⊤) ht'.unit :=
    congrArg ULift.up (ofMul_pow n ht'.unit)
  have h1 : Φ.toPresheafFiber T y (kummerTarget j N).obj
      ((kummerDirectImageδ j hN0 hN).hom.app (op T)
        (ofUnit.{u, 0} (X := (punctured k).toScheme) (U := puncturedOpen j ⊤)
          (ht'.unit ^ n))) = 0 := by
    have e1 := ((kummerDirectImageδ j hN0 hN).hom.app (op T)).hom.map_nsmul n
        (ofUnit.{u, 0} (X := (punctured k).toScheme) (U := puncturedOpen j ⊤) ht'.unit)
    have e2 := (Φ.toPresheafFiber T y (kummerTarget j N).obj).hom.map_nsmul n
        (((kummerDirectImageδ j hN0 hN).hom.app (op T)
        (ofUnit.{u, 0} (X := (punctured k).toScheme) (U := puncturedOpen j ⊤) ht'.unit)))
    rw [hpow]
    exact (congrArg (ConcreteCategory.hom (Φ.toPresheafFiber T y (kummerTarget j N).obj)) e1).trans
      (e2.trans h)
  have h2 : (smallEtaleStalkAb x).map (kummerDirectImageδ j hN0 hN)
      (Φ.toPresheafFiber T y (P.obj G).obj
        (ofUnit.{u, 0} (X := (punctured k).toScheme) (U := puncturedOpen j ⊤)
          (ht'.unit ^ n))) = 0 :=
    (Φ.toPresheafFiber_naturality_apply (kummerDirectImageδ j hN0 hN).hom T y _).trans h1
  obtain ⟨z, hz⟩ := exists_stalk_powMap_eq_of_kummerDirectImageδ j hN0 hN x _ h2
  obtain ⟨V, v, σ, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := (P.obj G).obj) z
  obtain ⟨a, rfl⟩ := ofUnit_surjective.{u, 0} (X := (punctured k).toScheme)
    (U := (smallEtaleBaseChange j).obj V) σ
  let g : V ⟶ T := (isTerminal_opensToEtale_top (affineLine k)).from V
  have hy : Φ.fiber.map g v = y := Subsingleton.elim _ _
  have hz2 : Φ.toPresheafFiber V v (P.obj G).obj (ofUnit.{u, 0} (a ^ N)) =
      Φ.toPresheafFiber V v (P.obj G).obj ((P.obj G).obj.map g.op
        (ofUnit.{u, 0} (X := (punctured k).toScheme) (U := puncturedOpen j ⊤) (ht'.unit ^ n))) := by
    refine Eq.trans ?_ (hz.trans ?_)
    · rw [← powMap_app_ofUnit.{u, 0}]
      exact (Φ.toPresheafFiber_naturality_apply
        ((smallEtalePushforwardAb j).map (powMap.{u, 0} _ N)).hom V v _).symm
    · rw [← hy]
      exact (Φ.toPresheafFiber_w_apply g v _ _).symm
  obtain ⟨W, e, w, -, hW⟩ := (Φ.toPresheafFiber_eq_iff' V v _ _).1 hz2
  have hW' : ((smallEtaleBaseChange j).map e).left.appTop
      ((a : Γ(((smallEtaleBaseChange j).obj V).left, ⊤)) ^ N) =
      ((smallEtaleBaseChange j).map e).left.appTop (((smallEtaleBaseChange j).map g).left.appTop
        ((ht'.unit : Γ(((smallEtaleBaseChange j).obj T).left, ⊤)) ^ n)) :=
    congrArg (fun z => (Additive.toMul z.down).val) hW
  have hcomp : ((smallEtaleBaseChange j).map e).left.appTop
      (((smallEtaleBaseChange j).map g).left.appTop
        (puncturedFunction (punctured k).ι ⊤ (coordinate k))) =
      (pullback.fst W.hom (punctured k).ι ≫ W.hom).appTop (coordinate k) := by
    rw [← appTop_baseChange_puncturedFunction_top (e ≫ g), CategoryTheory.Functor.map_comp]
    rfl
  rw [map_pow, map_pow, map_pow] at hW'
  change (((smallEtaleBaseChange j).map e).left.appTop
      (a : Γ(((smallEtaleBaseChange j).obj V).left, ⊤))) ^ N =
    (((smallEtaleBaseChange j).map e).left.appTop
      (((smallEtaleBaseChange j).map g).left.appTop
        (puncturedFunction (punctured k).ι ⊤ (coordinate k)))) ^ n at hW'
  rw [hcomp] at hW'
  have : Etale W.hom := W.prop
  let wl := (show Over.mk x ⟶ (Scheme.Etale.forget (affineLine k)).obj W from w).left
  have hwl : wl ≫ W.hom = x :=
    Over.w (show Over.mk x ⟶ (Scheme.Etale.forget (affineLine k)).obj W from w)
  obtain ⟨pt⟩ : Nonempty (Spec (.of Ω)) := inferInstance
  have hpt : W.hom.base (wl.base pt) ∉ (punctured k : Set (affineLine k)) := by
    have : W.hom.base (wl.base pt) = x.base pt := by rw [← hwl]; rfl
    rw [this]
    exact hx ⟨pt, rfl⟩
  exact dvd_of_pow_eq_coordinate_pow_pullback W.hom (wl.base pt) hpt _ hN0 hW'

end AffineLine

end Stacks.EtaleCohomology.Purity

end
