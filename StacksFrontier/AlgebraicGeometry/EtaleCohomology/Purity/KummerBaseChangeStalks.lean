module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerChartGenerator
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClopenDecomposition

/-!
# The degree-one base change map on `μ_N` from the two Kummer generators

Let `h ≫ f' = e ≫ g` be a commutative square with `g : T ⟶ S` and `h : Y ⟶ X'` quasi-compact open
immersions, `f'` carrying the complement of `Y` into the complement of `T`, and `N` invertible.
For a global `t` on `S`, if `σ_{∂ t} : ℤ/N ⟶ R¹ g_* μ_N` is invertible on the stalks outside `T`
and `σ_{∂ (f'^* t)} : ℤ/N ⟶ R¹ h_* μ_N` on those outside `Y`, the degree-one base change map
`f'⁻¹ R¹ g_* μ_N ⟶ R¹ h_* μ_N` (`Stacks.EtaleCohomology.Purity.kummerBaseChangeMap`) is an
isomorphism (`Stacks.EtaleCohomology.Purity.isIso_kummerBaseChangeMap_of_isIsoStalksOver`).

Outside `Y` this is two out of three
(`Stacks.EtaleCohomology.Purity.IsIsoStalksOver.of_pullback_comp`) applied to
`f'⁻¹ σ_{∂ t} ≫ β = e ≫ σ_{∂ (f'^* t)}`
(`Stacks.EtaleCohomology.Purity.pullback_map_torsionSectionSheafHom_localKummerClass_comp`); on
`Y` both stalks vanish, `R¹ g_* μ_N` vanishing on `T` and `R¹ h_* μ_N` on `Y`
(`Stacks.EtaleCohomology.Purity.isZero_restriction_kummerTarget`).

## Main results

* `Stacks.EtaleCohomology.Purity.IsIsoStalksOver.of_pullback_comp`.
* `Stacks.EtaleCohomology.Purity.isZero_smallEtaleStalkAb_of_isZero_restriction`.
* `Stacks.EtaleCohomology.Purity.isIso_kummerBaseChangeMap_of_isIsoStalksOver`.
* `Stacks.EtaleCohomology.Purity.isIsoStalksOver_torsionSectionSheafHom_of_isPullback`: the
  generator property is carried along smooth base change, over any base (for the charts
  `V' ⟶ 𝔸¹_{W'} ⟶ 𝔸¹_{k'}` of a base-changed relative curve).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

universe u

namespace Stacks.EtaleCohomology.Purity

open Stacks.Kummer

/-- **Two out of three for the stalk-isomorphism property along an inverse image.** If
`f⁻¹ σ ≫ β = e ≫ σ'` with `σ` invertible on the stalks over `T ⊇ f(T')` and `e`, `σ'` invertible
on the stalks over `T'`, then so is `β`. -/
theorem IsIsoStalksOver.of_pullback_comp {X S : Scheme.{u}} (f : X ⟶ S) {T : Set S}
    {T' : Set X} (hT : f.base '' T' ⊆ T) {A B : Sheaf (smallEtaleTopology S) Ab.{u + 1}}
    {A' B' : Sheaf (smallEtaleTopology X) Ab.{u + 1}} {σ : A ⟶ B} {σ' : A' ⟶ B'}
    (e : (smallEtalePullbackAb f).obj A ⟶ A') (β : (smallEtalePullbackAb f).obj B ⟶ B')
    (h : (smallEtalePullbackAb f).map σ ≫ β = e ≫ σ') (hσ : IsIsoStalksOver T σ)
    (he : IsIsoStalksOver T' e) (hσ' : IsIsoStalksOver T' σ') : IsIsoStalksOver T' β := by
  intro Ω _ _ x hx
  have hfx : Set.range (x ≫ f).base ⊆ T := by
    rintro _ ⟨p, rfl⟩
    exact hT ⟨x.base p, hx ⟨p, rfl⟩, rfl⟩
  have := hσ (x ≫ f) hfx
  have := he x hx
  have := hσ' x hx
  have hnat := (smallEtalePullbackStalkAbIso f x).hom.naturality σ
  have key : IsIso ((smallEtalePullbackAb f ⋙ smallEtaleStalkAb x).map σ) := by
    have : IsIso ((smallEtalePullbackAb f ⋙ smallEtaleStalkAb x).map σ ≫
        (smallEtalePullbackStalkAbIso f x).hom.app B) := by
      rw [hnat]; infer_instance
    exact IsIso.of_isIso_comp_right _ ((smallEtalePullbackStalkAbIso f x).hom.app B)
  have : IsIso ((smallEtaleStalkAb x).map ((smallEtalePullbackAb f).map σ)) := key
  have hc := congrArg (smallEtaleStalkAb x).map h
  rw [Functor.map_comp, Functor.map_comp] at hc
  have : IsIso ((smallEtaleStalkAb x).map ((smallEtalePullbackAb f).map σ) ≫
      (smallEtaleStalkAb x).map β) := by
    rw [hc]; infer_instance
  exact IsIso.of_isIso_comp_left ((smallEtaleStalkAb x).map ((smallEtalePullbackAb f).map σ)) _

/-- **A sheaf whose restriction to an open vanishes has zero stalks at the geometric points of
that open.** -/
theorem isZero_smallEtaleStalkAb_of_isZero_restriction {V X : Scheme.{u}} (j : V ⟶ X)
    [IsOpenImmersion j] {F : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (hF : IsZero ((etaleRestriction.{u, 0} j).obj F)) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (y : Spec (.of Ω) ⟶ V) : IsZero ((smallEtaleStalkAb (y ≫ j)).obj F) := by
  have h1 : IsZero ((smallEtalePullbackAb j).obj F) :=
    hF.of_iso ((smallEtalePullbackAbRestrictionIso j).app F)
  exact (Functor.map_isZero (smallEtaleStalkAb y) h1).of_iso
    ((smallEtalePullbackStalkAbIso j y).app F).symm

section Kummer

attribute [local instance] HasDerivedCategory.standard

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g) [IsOpenImmersion g] [IsOpenImmersion h] [QuasiCompact g] [QuasiCompact h]
  {N : ℕ} [NeZero N] (hNT : IsUnit ((N : ℕ) : Γ(T, ⊤))) (hNY : IsUnit ((N : ℕ) : Γ(Y, ⊤)))

/-- Every stalk element of `μ_N` on `T` is killed by `N`, which is invertible on `S`. -/
private theorem exists_nsmul_eq_zero_isUnit_kummerSequence_X₁ {T S : Scheme.{u}} (N : ℕ) [NeZero N]
    (hNS : IsUnit ((N : ℤ) : Γ(S, ⊤))) (t : GeometricPoint T)
    (a : (smallEtaleStalkAb t.hom).obj (kummerSequence.{u, 0} T N).X₁) :
    ∃ n : ℕ, 0 < n ∧ IsUnit ((n : ℤ) : Γ(S, ⊤)) ∧ n • a = 0 :=
  ⟨N, Nat.pos_of_ne_zero (NeZero.ne N), hNS,
    nsmul_eq_zero_stalk_of_nsmul_id (nsmul_id_rootsOfUnitySheaf_univ _ N) t a⟩

/-- The pullback along `f'` of the constant-sheaf comparison is invertible on all stalks. -/
private theorem isIsoStalksOver_pullbackAbConstantIso {X' S : Scheme.{u}} (f' : X' ⟶ S) (N : ℕ)
    (T : Set X') : IsIsoStalksOver T
      ((smallEtalePullbackAbConstantIso f').hom.app
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod N)))) := by
  intro Ω _ _ x _
  infer_instance

/-- `R¹ g_* μ_N` vanishes on the open `T`, for `g : T ⟶ S` a quasi-compact open immersion and `N`
invertible on `S`. -/
theorem isZero_restriction_kummerTarget {T S : Scheme.{u}} (g : T ⟶ S) [IsOpenImmersion g]
    [QuasiCompact g] (N : ℕ) [NeZero N] (hNS : IsUnit ((N : ℤ) : Γ(S, ⊤))) :
    IsZero ((etaleRestriction.{u, 0} g).obj
      (((smallEtalePushforwardAb g).rightDerived (0 + 1)).obj (kummerSequence.{u, 0} T N).X₁)) :=
  isZero_restriction_rightDerived_of_isOpenImmersion g _
    (exists_nsmul_eq_zero_isUnit_kummerSequence_X₁ N hNS) (0 + 1) Nat.one_pos

/-- **The degree-one base change map on `μ_N` is invertible when both Kummer classes generate.**
For a commutative square `h ≫ f' = e ≫ g` of quasi-compact open immersions `g`, `h` with `f'`
carrying the complement of `Y` into the complement of `T`, and a global `t` on `S`, if
`σ_{∂ t}` is invertible on the stalks outside `T` and `σ_{∂ (f'^* t)}` on those outside `Y`, then
`f'⁻¹ R¹ g_* μ_N ⟶ R¹ h_* μ_N` is an isomorphism: outside `Y` by two out of three
(`Stacks.EtaleCohomology.Purity.pullback_map_torsionSectionSheafHom_localKummerClass_comp`), on
`Y` both stalks vanish. -/
theorem isIso_kummerBaseChangeMap_of_isIsoStalksOver (hNS : IsUnit ((N : ℤ) : Γ(S, ⊤)))
    (hNX : IsUnit ((N : ℤ) : Γ(X', ⊤))) (t : Γ(S, ⊤))
    (ht : IsUnit (puncturedFunction g ⊤ t)) (ht' : IsUnit (puncturedFunction h ⊤ (f'.appTop t)))
    (hσ : IsIsoStalksOver (Set.range g.base)ᶜ
      (torsionSectionSheafHom (localKummerClass g (NeZero.ne N) hNT ⊤ t ht)
        (nsmul_localKummerClass g (NeZero.ne N) hNT ⊤ t ht)))
    (hσ' : IsIsoStalksOver (Set.range h.base)ᶜ
      (torsionSectionSheafHom (localKummerClass h (NeZero.ne N) hNY ⊤ (f'.appTop t) ht')
        (nsmul_localKummerClass h (NeZero.ne N) hNY ⊤ (f'.appTop t) ht')))
    (hrange : f'.base '' (Set.range h.base)ᶜ ⊆ (Set.range g.base)ᶜ) :
    IsIso (kummerBaseChangeMap f' g h e w N) := by
  rw [isIso_iff_forall_isIso_smallEtaleStalkAb]
  intro x
  by_cases hx : Set.range x.hom.base ⊆ Set.range h.base
  · obtain ⟨y, hy⟩ : ∃ y, y ≫ h = x.hom := ⟨_, IsOpenImmersion.lift_fac h x.hom hx⟩
    have hs : IsZero ((smallEtaleStalkAb x.hom).obj ((smallEtalePullbackAb f').obj
        (((smallEtalePushforwardAb g).rightDerived (0 + 1)).obj
          (kummerSequence.{u, 0} T N).X₁))) := by
      refine IsZero.of_iso ?_ ((smallEtalePullbackStalkAbIso f' x.hom).app _)
      have heq : x.hom ≫ f' = (y ≫ e) ≫ g := by
        rw [← hy, Category.assoc, w, Category.assoc]
      rw [heq]
      exact isZero_smallEtaleStalkAb_of_isZero_restriction g
        (isZero_restriction_kummerTarget g N hNS) _
    have ht : IsZero ((smallEtaleStalkAb x.hom).obj
        (((smallEtalePushforwardAb h).rightDerived (0 + 1)).obj
          (kummerSequence.{u, 0} Y N).X₁)) := by
      rw [← hy]
      exact isZero_smallEtaleStalkAb_of_isZero_restriction h
        (isZero_restriction_kummerTarget h N hNX) _
    exact ⟨⟨0, hs.eq_of_src _ _, ht.eq_of_src _ _⟩⟩
  · have hx' : Set.range x.hom.base ⊆ (Set.range h.base)ᶜ := by
      rintro _ ⟨a, rfl⟩ hp
      refine hx ?_
      rintro _ ⟨b, rfl⟩
      rwa [Subsingleton.elim b a]
    exact IsIsoStalksOver.of_pullback_comp f' hrange _ _
      (pullback_map_torsionSectionSheafHom_localKummerClass_comp f' g h e w (NeZero.ne N) hNT hNY
        t ht ht') hσ (isIsoStalksOver_pullbackAbConstantIso f' N _) hσ' x.hom hx'

omit [IsOpenImmersion h] [QuasiCompact h] [IsOpenImmersion g] [QuasiCompact g] in
/-- The points of `X'` over the open `T ⊆ S` are the points of `Y`, for `Y` the pullback of `T`
along `f'`. -/
theorem mem_range_iff_of_isPullback_of_isOpenImmersion (sq : IsPullback h e f' g) (x : X') :
    x ∈ Set.range h.base ↔ f'.base x ∈ Set.range g.base := by
  have hj : Set.range h.base = f'.base ⁻¹' Set.range g.base := by
    rw [← sq.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
      ← Scheme.Pullback.range_fst]
    exact Function.Surjective.range_comp (Scheme.homeoOfIso sq.isoPullback).surjective _
  rw [hj]
  rfl

omit [IsOpenImmersion h] [QuasiCompact h] in
/-- **The Kummer generator property is carried along smooth base change.** For a cartesian square
`h ≫ f' = e ≫ g` with `f'` smooth and `g` a quasi-compact open immersion, and `N` invertible on
`S`, if `σ_{∂ t}` is invertible on the stalks outside `T` then `σ_{∂ (f'^* t)}` is invertible on
the stalks outside `Y`: smooth base change (Stacks 0EYU) makes the degree-one base change map an
isomorphism, and it carries `σ_{∂ t}` to `σ_{∂ (f'^* t)}`. This is
`Stacks.EtaleCohomology.Purity.isIsoStalksOver_torsionSectionSheafHom_of_isPullback_affineLine`
with the base `𝔸¹_k` replaced by any `S`. -/
theorem isIsoStalksOver_torsionSectionSheafHom_of_isPullback [Smooth f']
    (sq : IsPullback h e f' g) (hNS : IsUnit ((N : ℤ) : Γ(S, ⊤))) (t : Γ(S, ⊤))
    (ht : IsUnit (puncturedFunction g ⊤ t)) (ht' : IsUnit (puncturedFunction h ⊤ (f'.appTop t)))
    (hσ : IsIsoStalksOver (Set.range g.base)ᶜ
      (torsionSectionSheafHom (localKummerClass g (NeZero.ne N) hNT ⊤ t ht)
        (nsmul_localKummerClass g (NeZero.ne N) hNT ⊤ t ht))) :
    IsIsoStalksOver (Set.range h.base)ᶜ
      (torsionSectionSheafHom (localKummerClass h (NeZero.ne N) hNY ⊤ (f'.appTop t) ht')
        (nsmul_localKummerClass h (NeZero.ne N) hNY ⊤ (f'.appTop t) ht')) := by
  have : IsSeparated g := IsSeparated.isSeparated_of_mono _
  have : QuasiSeparated g := AlgebraicGeometry.IsSeparated.instQuasiSeparated _
  have h3b := pullback_map_torsionSectionSheafHom_localKummerClass_comp f' g h e sq.w
    (NeZero.ne N) hNT hNY t ht ht'
  have := SmoothBaseChange.isIso_higherBaseChangeMapAb_app_of_smooth f' h e g sq
    (kummerSequence.{u, 0} T N).X₁ (exists_nsmul_eq_zero_isUnit_kummerSequence_X₁ N hNS) (0 + 1)
  have : IsIso (rootsOfUnityInverseImageComparison.{u, 0} e N) :=
    isIso_rootsOfUnityInverseImageComparison e N hNT
  have : IsIso (kummerSequencePullbackMap e N).τ₁ := by
    change IsIso (((smallEtalePullbackAbIsoEtaleAbelianInverseImage e).hom.app _) ≫
      rootsOfUnityInverseImageComparison.{u, 0} e N)
    infer_instance
  have : IsIso (kummerBaseChangeMap f' g h e sq.w N) := by
    unfold kummerBaseChangeMap
    infer_instance
  have hβ : IsIsoStalksOver (Set.range h.base)ᶜ (kummerBaseChangeMap f' g h e sq.w N) := by
    intro Ω _ _ x _
    infer_instance
  have hT : f'.base '' (Set.range h.base)ᶜ ⊆ (Set.range g.base)ᶜ := by
    rintro _ ⟨v, hv, rfl⟩
    exact fun hg => hv ((mem_range_iff_of_isPullback_of_isOpenImmersion f' g h e sq v).2 hg)
  intro Ω _ _ x hx
  exact IsIsoStalksOver.of_pullback f' hT _ _ h3b hσ
    (isIsoStalksOver_pullbackAbConstantIso f' N _) hβ x hx

end Kummer

end Stacks.EtaleCohomology.Purity

end
