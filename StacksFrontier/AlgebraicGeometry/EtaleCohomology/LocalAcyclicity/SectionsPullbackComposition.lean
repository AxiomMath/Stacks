module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkOfDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SpecializationMap

/-!
# Restriction of sections along a composite of morphisms of schemes

Let `b : X' ⟶ X` and `a : T ⟶ X'` be morphisms of schemes, let `W` be an object of the small
étale site of `X`, and let `ρ : T ⟶ W ×_X X'` be a morphism into the base change of `W` lying
over `a`. Restricting a section of an abelian étale sheaf `F` on `X` over `W` to a global section
of `(a ≫ b)⁻¹F` on `T` can be done in two steps: first restrict to a section of `b⁻¹F` over
`W ×_X X'`, which is the unit of the inverse-image/direct-image adjunction for `b`, and then
restrict that along `ρ` to a global section of `a⁻¹b⁻¹F`. The two agree, modulo the composition
isomorphism `a⁻¹b⁻¹F ≅ (a ≫ b)⁻¹F`. This is the compatibility of
`Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb` with composition in the morphism variable.

## Main results

* `Stacks.EtaleCohomology.smallEtalePushforwardAbCompIso_inv_app_hom_app`: the composition
  isomorphism for direct image is, on sections over an étale object, restriction along the
  comparison of base changes.
* `Stacks.EtaleCohomology.smallEtaleBaseChangeComp_hom_app_left_fst_fst`: the comparison of base
  changes is compatible with the projections to the étale object.
* `Stacks.EtaleCohomology.smallEtaleBaseChangeLift_comp_smallEtaleBaseChangeComp_hom`: a lift of
  `T` into the iterated base change is, through the comparison, the lift into the base change
  along the composite.
* `Stacks.EtaleCohomology.unit_comp_unit_comp_smallEtalePullbackAbCompIso`: the composite of the
  two adjunction units, followed by the composition isomorphism for inverse image, is the unit
  for the composite morphism followed by the comparison of base changes.
* `Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb_comp_app`: restriction of sections along
  a composite is the two restrictions in turn.

## References

* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

section Bookkeeping

variable {C : Type*} [Category C]

/-- A composite of five morphisms is rewritten by moving a comparison morphism leftwards past
three of them, given the commuting squares `hg`, `hm`, `hu` and `hn`. -/
private theorem comp_shuffle {A₀ A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ : C}
    (u₁ : A₀ ⟶ A₁) (u₂ : A₁ ⟶ A₂) (m : A₂ ⟶ A₃) (g : A₃ ⟶ A₄) (w : A₄ ⟶ A₅)
    (θ₁ : A₃ ⟶ B₃) (g' : B₃ ⟶ A₅) (θ₂ : A₂ ⟶ B₂) (m' : B₂ ⟶ B₃)
    (u₃ : A₀ ⟶ B₁) (n : B₁ ⟶ B₂) (m'' : B₁ ⟶ B₃)
    (hg : g ≫ w = θ₁ ≫ g') (hm : m ≫ θ₁ = θ₂ ≫ m')
    (hu : u₁ ≫ u₂ ≫ θ₂ = u₃ ≫ n) (hn : n ≫ m' = m'') :
    u₁ ≫ ((u₂ ≫ m) ≫ g) ≫ w = (u₃ ≫ m'') ≫ g' := by
  simp only [Category.assoc]
  rw [hg, reassoc_of% hm, reassoc_of% hu, reassoc_of% hn]

end Bookkeeping

section LiftPullback

variable {X X' T : Scheme.{u}} (a : T ⟶ X') (b : X' ⟶ X) {V : Scheme.{u}} (h : V ⟶ X)

/-- The two lifts of `T` into the two presentations of the iterated fibre product agree, given
that the comparison between them is compatible with the projection to `V` and lies over `T`. -/
private theorem lift_comp_eq_lift (c : pullback h (a ≫ b) ⟶ pullback (pullback.snd h b) a)
    (hfst : c ≫ pullback.fst (pullback.snd h b) a ≫ pullback.fst h b =
      pullback.fst h (a ≫ b))
    (hsnd : c ≫ pullback.snd (pullback.snd h b) a = pullback.snd h (a ≫ b))
    (ρ : T ⟶ pullback h b) (e : ρ ≫ pullback.snd h b = 𝟙 T ≫ a)
    (e' : (ρ ≫ pullback.fst h b) ≫ h = 𝟙 T ≫ a ≫ b) :
    pullback.lift ρ (𝟙 T) e = pullback.lift (ρ ≫ pullback.fst h b) (𝟙 T) e' ≫ c := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc, hfst, pullback.lift_fst]
    · simp only [Category.assoc, pullback.condition, reassoc_of% hsnd,
        pullback.lift_snd_assoc, Category.id_comp]
  · simp only [Category.assoc, hsnd, pullback.lift_snd]

end LiftPullback

section Composition

variable {X X' T : Scheme.{u}} (a : T ⟶ X') (b : X' ⟶ X)

/-! ### The composition isomorphism for direct image, on sections -/

/-- The inverse of the composition isomorphism for direct image of abelian étale sheaves is, on
sections over an object `W` of the small étale site of the target, restriction along the
comparison of the iterated base change of `W` with the base change of `W` along the composite. -/
public theorem smallEtalePushforwardAbCompIso_inv_app_hom_app
    (M : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (W : X.Etale) :
    ((smallEtalePushforwardAbCompIso a b).inv.app M).hom.app (op W) =
      M.obj.map ((smallEtaleBaseChangeComp a b).inv.app W).op :=
  Functor.sheafPushforwardContinuousComp'_inv_app_hom_app _ _ _ _ _ M (op W)

/-! ### The comparison of base changes -/

/-- The comparison of the base change of an étale object along a composite with its iterated base
change is compatible with the projections to that object. -/
public theorem smallEtaleBaseChangeComp_hom_app_left_fst_fst (W : X.Etale) :
    ((smallEtaleBaseChangeComp a b).hom.app W).left ≫
        pullback.fst ((smallEtaleBaseChange b).obj W).hom a ≫ pullback.fst W.hom b =
      pullback.fst W.hom (a ≫ b) := by
  let _ : MorphismProperty.HasPullbacksAlong
      (@Etale : MorphismProperty Scheme.{u}) a := ⟨fun _ _ ↦ inferInstance⟩
  let _ : MorphismProperty.HasPullbacksAlong
      (@Etale : MorphismProperty Scheme.{u}) b := ⟨fun _ _ ↦ inferInstance⟩
  let _ : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) a :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  let _ : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) b :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  exact MorphismProperty.Over.pullbackComp_left_fst_fst a b W

/-! ### Matching the two lifts -/

variable (W : X.Etale) (ρ : T ⟶ ((smallEtaleBaseChange b).obj W).left)

/-- The lift of `T` into the iterated base change of an étale object, followed by the comparison
with the base change along the composite, is the lift of `T` into the latter. -/
public theorem smallEtaleBaseChangeLift_comp_smallEtaleBaseChangeComp_hom
    (hρ : ρ ≫ ((smallEtaleBaseChange b).obj W).hom = a)
    (hr : (ρ ≫ pullback.fst W.hom b) ≫ W.hom = a ≫ b) :
    smallEtaleBaseChangeLift a ((smallEtaleBaseChange b).obj W) ρ hρ =
      smallEtaleBaseChangeLift (a ≫ b) W (ρ ≫ pullback.fst W.hom b) hr ≫
        (smallEtaleBaseChangeComp a b).hom.app W := by
  apply MorphismProperty.Over.Hom.ext
  show (smallEtaleBaseChangeLift a ((smallEtaleBaseChange b).obj W) ρ hρ).left =
    (smallEtaleBaseChangeLift (a ≫ b) W (ρ ≫ pullback.fst W.hom b) hr).left ≫
      ((smallEtaleBaseChangeComp a b).hom.app W).left
  rw [smallEtaleBaseChangeLift_left, smallEtaleBaseChangeLift_left]
  exact lift_comp_eq_lift a b W.hom ((smallEtaleBaseChangeComp a b).hom.app W).left
    (smallEtaleBaseChangeComp_hom_app_left_fst_fst a b W)
    (MorphismProperty.Over.w ((smallEtaleBaseChangeComp a b).hom.app W)) ρ _ _

/-! ### The units and the composition isomorphism for inverse image -/

/-- The unit of the inverse-image/direct-image adjunction for `b`, followed by the unit for `a`
and by the composition isomorphism for inverse image, is the unit for `a ≫ b` followed by
restriction along the comparison of base changes. -/
public theorem unit_comp_unit_comp_smallEtalePullbackAbCompIso
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    ((smallEtaleAdjunctionAb b).unit.app F).hom.app (op W) ≫
        ((smallEtaleAdjunctionAb a).unit.app ((smallEtalePullbackAb b).obj F)).hom.app
            (op ((smallEtaleBaseChange b).obj W)) ≫
          ((smallEtalePullbackAbCompIso a b).hom.app F).hom.app
            (op ((smallEtaleBaseChange a).obj ((smallEtaleBaseChange b).obj W))) =
      ((smallEtaleAdjunctionAb (a ≫ b)).unit.app F).hom.app (op W) ≫
        ((smallEtalePullbackAb (a ≫ b)).obj F).obj.map
          ((smallEtaleBaseChangeComp a b).inv.app W).op := by
  have key := congrArg (fun φ ↦ φ.hom.app (op W)) (Adjunction.unit_leftAdjointUniq_hom_app
    ((smallEtaleAdjunctionAb b).comp (smallEtaleAdjunctionAb a))
    (Adjunction.ofNatIsoRight (smallEtaleAdjunctionAb (a ≫ b))
      (smallEtalePushforwardAbCompIso a b).symm) F)
  simp only [Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit] at key
  exact key.trans (congrArg (_ ≫ ·)
    (smallEtalePushforwardAbCompIso_inv_app_hom_app a b ((smallEtalePullbackAb (a ≫ b)).obj F) W))

/-! ### Restriction of sections along a composite -/

/-- Restricting a section of an abelian étale sheaf `F` on `X` over an étale object `W` to a
global section of `(a ≫ b)⁻¹F` on `T`, along a lift `ρ` of `T` into the base change of `W` along
`b`, is the unit of the adjunction for `b` followed by the restriction of the resulting section of
`b⁻¹F` along `ρ`, read through the composition isomorphism `a⁻¹b⁻¹F ≅ (a ≫ b)⁻¹F`. -/
public theorem smallEtaleSectionsPullbackAb_comp_app
    (hρ : ρ ≫ ((smallEtaleBaseChange b).obj W).hom = a)
    (hr : (ρ ≫ pullback.fst W.hom b) ≫ W.hom = a ≫ b)
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    ((smallEtaleAdjunctionAb b).unit.app F).hom.app (op W) ≫
        (smallEtaleSectionsPullbackAb a ((smallEtaleBaseChange b).obj W) ρ hρ).app
            ((smallEtalePullbackAb b).obj F) ≫
          (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}).map
            ((smallEtalePullbackAbCompIso a b).hom.app F) =
      (smallEtaleSectionsPullbackAb (a ≫ b) W (ρ ≫ pullback.fst W.hom b) hr).app F := by
  have hcomp : ((smallEtaleBaseChangeComp a b).inv.app W).op ≫
        (smallEtaleBaseChangeLift a ((smallEtaleBaseChange b).obj W) ρ hρ).op =
      (smallEtaleBaseChangeLift (a ≫ b) W (ρ ≫ pullback.fst W.hom b) hr).op := by
    rw [← op_comp, smallEtaleBaseChangeLift_comp_smallEtaleBaseChangeComp_hom a b W ρ hρ hr,
      Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  refine comp_shuffle
    (((smallEtaleAdjunctionAb b).unit.app F).hom.app (op W))
    (((smallEtaleAdjunctionAb a).unit.app ((smallEtalePullbackAb b).obj F)).hom.app
      (op ((smallEtaleBaseChange b).obj W)))
    (((smallEtalePullbackAb a).obj ((smallEtalePullbackAb b).obj F)).obj.map
      (smallEtaleBaseChangeLift a ((smallEtaleBaseChange b).obj W) ρ hρ).op)
    ((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1}
        (isTerminalEtaleMkId T)).inv.app
      ((smallEtalePullbackAb a).obj ((smallEtalePullbackAb b).obj F)))
    ((Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}).map
      ((smallEtalePullbackAbCompIso a b).hom.app F))
    (((smallEtalePullbackAbCompIso a b).hom.app F).hom.app (op (Scheme.Etale.mk (𝟙 T))))
    ((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1}
      (isTerminalEtaleMkId T)).inv.app ((smallEtalePullbackAb (a ≫ b)).obj F))
    (((smallEtalePullbackAbCompIso a b).hom.app F).hom.app
      (op ((smallEtaleBaseChange a).obj ((smallEtaleBaseChange b).obj W))))
    (((smallEtalePullbackAb (a ≫ b)).obj F).obj.map
      (smallEtaleBaseChangeLift a ((smallEtaleBaseChange b).obj W) ρ hρ).op)
    (((smallEtaleAdjunctionAb (a ≫ b)).unit.app F).hom.app (op W))
    (((smallEtalePullbackAb (a ≫ b)).obj F).obj.map
      ((smallEtaleBaseChangeComp a b).inv.app W).op)
    (((smallEtalePullbackAb (a ≫ b)).obj F).obj.map
      (smallEtaleBaseChangeLift (a ≫ b) W (ρ ≫ pullback.fst W.hom b) hr).op)
    ?_ ?_ (unit_comp_unit_comp_smallEtalePullbackAbCompIso a b W F) ?_
  · exact ((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1}
      (isTerminalEtaleMkId T)).inv.naturality
        ((smallEtalePullbackAbCompIso a b).hom.app F)).symm
  · exact ((smallEtalePullbackAbCompIso a b).hom.app F).hom.naturality
      (smallEtaleBaseChangeLift a ((smallEtaleBaseChange b).obj W) ρ hρ).op
  · exact (((smallEtalePullbackAb (a ≫ b)).obj F).obj.map_comp _ _).symm.trans
      (congrArg ((smallEtalePullbackAb (a ≫ b)).obj F).obj.map hcomp)

end Composition

end Stacks.EtaleCohomology

end
