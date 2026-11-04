module

public import StacksCore.CategoryTheory.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# The diagonal of a representable transformation

A representable transformation between presheaves on the big fppf site of a scheme has a
representable relative diagonal.

## Main results

* `AlgebraicGeometry.Space.relativelyRepresentable_diagonal`: the relative diagonal of a
  representable transformation of presheaves on the big fppf site over `S` is representable.

## References

* [Stacks Project, Tag 05L9](https://stacks.math.columbia.edu/tag/05L9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- The diagonal of a representable transformation of presheaves on the big fppf site over `S` is
representable. -/
@[stacks 05L9]
public theorem relativelyRepresentable_diagonal
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (ha : yoneda.relativelyRepresentable a) :
    yoneda.relativelyRepresentable (pullback.diagonal a) := by
  rw [yoneda_relativelyRepresentable_iff_pullback_representable]
  intro U ξ
  let η : yoneda.obj U ⟶ pullback a a := yonedaEquiv.symm ξ
  let α : yoneda.obj U ⟶ F := η ≫ pullback.fst a a
  let β : yoneda.obj U ⟶ F := η ≫ pullback.snd a a
  have hαβ : α ≫ a = β ≫ a := by simp [α, β, pullback.condition]
  obtain ⟨V, s, q, hp⟩ := ha (α ≫ a)
  let j₁ : yoneda.obj U ⟶ yoneda.obj V := hp.lift α (𝟙 _) (by simp)
  let j₂ : yoneda.obj U ⟶ yoneda.obj V := hp.lift β (𝟙 _) (by simp [hαβ])
  let e₁ : U ⟶ V := yonedaEquiv j₁
  let e₂ : U ⟶ V := yonedaEquiv j₂
  let d := Limits.diag V
  let p := prod.lift e₁ e₂
  let W := pullback d p
  let t : W ⟶ U := pullback.snd d p
  let v : W ⟶ V := pullback.fst d p
  let qW : yoneda.obj W ⟶ F := yoneda.map v ≫ q
  let tW : yoneda.obj W ⟶ yoneda.obj U := yoneda.map t
  have hw : ∀ π : V ⨯ V ⟶ V, d ≫ π = 𝟙 V → v = t ≫ p ≫ π := fun π hπ => by
    simpa [v, t, hπ] using congrArg (· ≫ π) (pullback.condition (f := d) (g := p))
  have hw1 : v = t ≫ e₁ := by simpa [p, e₁] using hw prod.fst (by simp [d])
  have hw2 : v = t ≫ e₂ := by simpa [p, e₂] using hw prod.snd (by simp [d])
  have hj₁ : yoneda.map e₁ = j₁ := yonedaEquiv.injective (yonedaEquiv_yoneda_map e₁)
  have hj₂ : yoneda.map e₂ = j₂ := yonedaEquiv.injective (yonedaEquiv_yoneda_map e₂)
  have hj₁fst : j₁ ≫ q = α := hp.lift_fst α (𝟙 _) (by simp)
  have hj₁snd : j₁ ≫ yoneda.map s = 𝟙 _ := hp.lift_snd α (𝟙 _) (by simp)
  have hj₂fst : j₂ ≫ q = β := hp.lift_fst β (𝟙 _) (by simp [hαβ])
  have hj₂snd : j₂ ≫ yoneda.map s = 𝟙 _ := hp.lift_snd β (𝟙 _) (by simp [hαβ])
  have hq : ∀ (e : U ⟶ V) (γ : yoneda.obj U ⟶ F), yoneda.map e ≫ q = γ → v = t ≫ e →
      qW = tW ≫ γ := fun e γ he hv => by
    dsimp only [qW, tW]
    rw [hv, Functor.map_comp, Category.assoc, he]
  have hq₁ : qW = tW ≫ α := hq e₁ α (hj₁ ▸ hj₁fst) hw1
  have hq₂ : qW = tW ≫ β := hq e₂ β (hj₂ ▸ hj₂fst) hw2
  have hcomm : qW ≫ pullback.diagonal a = tW ≫ η :=
    pullback.hom_ext (by simpa [α] using hq₁) (by simpa [β] using hq₂)
  have hsq : IsPullback qW tW (pullback.diagonal a) η := by
    refine IsPullback.of_forall_isPullback_app fun X => ?_
    let c : PullbackCone ((pullback.diagonal a).app X) (η.app X) :=
      PullbackCone.mk (qW.app X) (tW.app X) (by
        simpa using congrArg (fun f => f.app X) hcomm)
    have point (π : pullback a a ⟶ F) (hπ : pullback.diagonal a ≫ π = 𝟙 _)
        (s₀ : PullbackCone ((pullback.diagonal a).app X) (η.app X)) (z : s₀.pt) :
        s₀.fst z = (η ≫ π).app X (s₀.snd z) := by
      have hpair : (pullback.diagonal a).app X (s₀.fst z) = η.app X (s₀.snd z) := by
        simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom s₀.condition z
      have hdfx : π.app X ((pullback.diagonal a).app X (s₀.fst z)) = s₀.fst z := by
        simpa only [NatTrans.comp_app, NatTrans.id_app, ConcreteCategory.comp_apply,
          ConcreteCategory.id_apply] using ConcreteCategory.congr_hom (congr_app hπ X) (s₀.fst z)
      exact hdfx.symm.trans (by rw [hpair]; simp)
    let liftHom (s₀ : PullbackCone ((pullback.diagonal a).app X) (η.app X))
        (z : s₀.pt) : X.unop ⟶ W := by
      let g₀ : yoneda.obj X.unop ⟶ yoneda.obj U :=
        yonedaEquiv.symm (s₀.snd z)
      let k : X.unop ⟶ U := yonedaEquiv g₀
      have hg : ∀ γ : yoneda.obj U ⟶ F, s₀.fst z = γ.app X (s₀.snd z) →
          yonedaEquiv.symm (s₀.fst z) = g₀ ≫ γ := fun γ h => by
        apply yonedaEquiv.injective
        simp only [Equiv.apply_symm_apply, yonedaEquiv_comp]
        simpa [g₀] using h
      let ell := hp.lift (yonedaEquiv.symm (s₀.fst z)) g₀
        (by rw [hg α (point _ (pullback.diagonal_fst a) s₀ z), Category.assoc])
      have hg₀ : g₀ = yoneda.map k := yonedaEquiv.injective (yonedaEquiv_yoneda_map k).symm
      have hr : ∀ (j : yoneda.obj U ⟶ yoneda.obj V) (γ : yoneda.obj U ⟶ F), j ≫ q = γ →
          j ≫ yoneda.map s = 𝟙 _ → s₀.fst z = γ.app X (s₀.snd z) →
          yonedaEquiv ell = k ≫ yonedaEquiv j := fun j γ hjq hjs h => by
        have : ell = g₀ ≫ j :=
          hp.hom_ext (by simpa [ell, hjq] using hg γ h) (by simp [ell, hjs])
        rw [this, hg₀]
        simpa using (yonedaEquiv_naturality j k).symm
      have hr₁ : yonedaEquiv ell = k ≫ e₁ := hr j₁ α hj₁fst hj₁snd
        (point _ (pullback.diagonal_fst a) s₀ z)
      have hr₂ : yonedaEquiv ell = k ≫ e₂ := hr j₂ β hj₂fst hj₂snd
        (point _ (pullback.diagonal_snd a) s₀ z)
      have hdiag : (k ≫ e₁) ≫ d = k ≫ p := by
        apply prod.hom_ext <;> simp [d, p, hr₁.symm.trans hr₂]
      exact pullback.lift (k ≫ e₁) k hdiag
    let lift (s₀ : PullbackCone ((pullback.diagonal a).app X) (η.app X))
        : s₀.pt ⟶ c.pt :=
      TypeCat.ofHom fun z => liftHom s₀ z
    apply IsPullback.of_isLimit (c := c)
    refine PullbackCone.IsLimit.mk c.condition lift ?_ ?_ ?_
    · intro s
      refine ConcreteCategory.hom_ext (lift s ≫ c.fst) s.fst fun z => ?_
      have ht : liftHom s z ≫ t = s.snd z := by
        dsimp [liftHom, t]
        rw [pullback.lift_snd]
        simp
      show qW.app X (liftHom s z) = s.fst z
      rw [hq₁]
      show α.app X (liftHom s z ≫ t) = s.fst z
      rw [ht]
      exact (point _ (pullback.diagonal_fst a) s z).symm
    · intro s
      refine ConcreteCategory.hom_ext (lift s ≫ c.snd) s.snd fun z => ?_
      show liftHom s z ≫ t = s.snd z
      dsimp [liftHom, t]
      rw [pullback.lift_snd]
      simp
    · intro s m hm₁ hm₂
      refine ConcreteCategory.hom_ext m (lift s) fun z => ?_
      let mX : X.unop ⟶ W := (ConcreteCategory.hom m) z
      have hz : mX ≫ t = s.snd z := ConcreteCategory.congr_hom hm₂ z
      apply pullback.hom_ext
      · have hv := congrArg (fun f => mX ≫ f) hw1
        calc
          mX ≫ pullback.fst d p = (mX ≫ t) ≫ e₁ := by simpa [v] using hv
          _ = s.snd z ≫ e₁ := by rw [hz]
          _ = liftHom s z ≫ pullback.fst d p := by
            simp [liftHom, pullback.lift_fst]
      · show mX ≫ pullback.snd d p = liftHom s z ≫ pullback.snd d p
        calc
          mX ≫ pullback.snd d p = s.snd z := by simpa [t] using hz
          _ = liftHom s z ≫ pullback.snd d p := by
            symm
            simp [liftHom, pullback.lift_snd]
  exact Functor.IsRepresentable.mk'
    (hsq.isoIsPullback F (yoneda.obj U) (IsPullback.of_hasPullback (pullback.diagonal a) η) ≪≫
      pullbackSymmetry (pullback.diagonal a) η)

end AlgebraicGeometry.Space

end
