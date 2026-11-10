module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.AssemblyStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverField
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01
public import StacksFrontier.AlgebraicGeometry.Quot.PrestableCurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleChartGlobalFunctions

/-!
# `f_*𝒪_X = 𝒪_S` universally for a proper scheme over a field with `H⁰ = k`

Let `X` be a proper scheme over a field `k` with `H⁰(X, 𝒪_X) = k`. Then for every algebraic space
`Y` over `Spec k`, pullback of global regular functions along the projection `X ×_k Y ⟶ Y` is
bijective: the family of curves of `X` (`AlgebraicGeometry.curveFamilyOfScheme`) satisfies the
direct image condition of Stacks 0E6T. Conversely that condition gives `H⁰(X, 𝒪_X) = k`, by base
change along the identity of `Spec k`.

The proof is in two steps. For schemes it is flat base change in degree zero
([Stacks, Tag 02KH]): every scheme `T` over `Spec k` is flat over it, so `𝒪_T ⟶ p_*𝒪_{X_T}` is
an isomorphism for the projection `p : X_T ⟶ T`, and in particular `Γ(T, 𝒪) ≅ Γ(X_T, 𝒪)`. For an
algebraic space `Y` it is formal: a global regular function on an algebraic space is a compatible
family of regular functions on all its scheme charts
(`AlgebraicGeometry.Space.globalFunctionsChartEquiv`), the base change of a chart `T ⟶ Y` is the
chart `X_T ⟶ X ×_k Y`, and a compatible family on the charts of `X ×_k Y` restricts on each `X_T`
to a function coming from a unique function on `T`.

## Main results

* `AlgebraicGeometry.C1590Private.chartFunctionsMap_bijective_of_isPullback`: pullback of chart
  functions along a morphism of presheaves is bijective when it is bijective on global functions
  after every base change to a scheme.
* `AlgebraicGeometry.C1590Private.bijective_globalFunctionsMap_iff`: pullback of global functions
  along a morphism of algebraic spaces is bijective exactly when pullback of chart functions is.
* `AlgebraicGeometry.C1590Private.bijective_appTop_of_bijective_globalFunctionsMap`: on a morphism
  of schemes of the site, bijectivity on global functions of the algebraic spaces gives it on the
  schemes.
* `AlgebraicGeometry.C1590Private.bijective_globalFunctionsMap_fiberProduct_snd`: the same for
  the base change of a morphism of schemes of the site along any algebraic space.
* `AlgebraicGeometry.C1590Private.bijective_appTop_of_isPullback`: flat base change of
  `H⁰(X, 𝒪_X) = k` to a scheme over `Spec k`.
* `AlgebraicGeometry.C1590Private.hasUniversallyBijectiveGlobalFunctions_curveFamilyOfScheme_iff`:
  the family of curves of a proper scheme `X` of dimension at most one over `k` has
  `f_*𝒪_X = 𝒪_S` universally exactly when `k = H⁰(X, 𝒪_X)`.

## References

* [Stacks Project, Tag 0E6T](https://stacks.math.columbia.edu/tag/0E6T)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.C1590Private

section Chart

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullback of global functions is contravariantly functorial, for sections typed as values of
`Scheme.Γ`. -/
theorem gamma_map_comp_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (s : Scheme.Γ.obj (op Z)) :
    (Scheme.Γ.map f.op).hom ((Scheme.Γ.map g.op).hom s) = (Scheme.Γ.map (f ≫ g).op).hom s := by
  rw [op_comp, Functor.map_comp]
  rfl

/-- A compatible family of regular functions on the charts of `F` restricts along a morphism of
schemes over a chart to its value on the composite chart. -/
theorem chartFunctions_restrict {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (s : Space.chartFunctions B S hS F) {T T' : BigFppfOver B S hS} (j : yoneda.obj T ⟶ F)
    (h : T' ⟶ T) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map h).op).hom
        (s.val (op (CostructuredArrow.mk j))) =
      s.val (op (CostructuredArrow.mk (yoneda.map h ≫ j))) :=
  s.property (CostructuredArrow.homMk h rfl :
    CostructuredArrow.mk (yoneda.map h ≫ j) ⟶ CostructuredArrow.mk j).op

/-- **Global functions under a morphism of presheaves that is bijective on charts.** Let
`π : G ⟶ F` be a morphism of presheaves on the big fppf site whose base change along every
scheme chart `T ⟶ F` is represented by a scheme `P` with `Γ(T, 𝒪) ⟶ Γ(P, 𝒪)` bijective. Then
pullback along `π` of compatible families of regular functions on all scheme charts is
bijective. -/
theorem chartFunctionsMap_bijective_of_isPullback {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (π : G ⟶ F)
    (hpb : ∀ (T : BigFppfOver B S hS) (j : yoneda.obj T ⟶ F), ∃ (P : BigFppfOver B S hS)
      (pr : P ⟶ T) (c : yoneda.obj P ⟶ G), IsPullback c (yoneda.map pr) π j)
    (hΓ : ∀ {T P : BigFppfOver B S hS} (j : yoneda.obj T ⟶ F) (pr : P ⟶ T)
      (c : yoneda.obj P ⟶ G), IsPullback c (yoneda.map pr) π j →
        Function.Bijective (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map pr).op).hom) :
    Function.Bijective (Space.chartFunctionsMap B S hS π) := by
  set Fs := BigFppfOver.toScheme B S hS
  choose P pr c sq using hpb
  refine ⟨fun s s' hss' => ?_, fun t => ?_⟩
  · apply Subtype.ext
    funext J
    obtain ⟨⟨T, ⟨⟨⟩⟩, j⟩⟩ := J
    have key : ∀ s : Space.chartFunctions B S hS F,
        (Scheme.Γ.map (Fs.map (pr T j)).op).hom (s.val (op (CostructuredArrow.mk j))) =
          (Space.chartFunctionsMap B S hS π s).val (op (CostructuredArrow.mk (c T j))) := by
      intro s
      rw [chartFunctions_restrict]
      change _ = s.val (op (CostructuredArrow.mk (c T j ≫ π)))
      rw [(sq T j).w]
    exact (hΓ j _ _ (sq T j)).1 ((key s).trans
      ((congrArg (fun z => z.val (op (CostructuredArrow.mk (c T j)))) hss').trans (key s').symm))
  · let s1 : ∀ (T : BigFppfOver B S hS) (j : yoneda.obj T ⟶ F), Scheme.Γ.obj (op (Fs.obj T)) :=
      fun T j => Function.surjInv (hΓ j _ _ (sq T j)).2 (t.val (op (CostructuredArrow.mk (c T j))))
    have hs1 : ∀ (T : BigFppfOver B S hS) (j : yoneda.obj T ⟶ F),
        (Scheme.Γ.map (Fs.map (pr T j)).op).hom (s1 T j) =
          t.val (op (CostructuredArrow.mk (c T j))) := fun T j =>
      Function.surjInv_eq _ _
    have hrest : ∀ (T : BigFppfOver B S hS) (j : yoneda.obj T ⟶ F) {W : BigFppfOver B S hS}
        (c0 : yoneda.obj W ⟶ G) (p : W ⟶ T), c0 ≫ π = yoneda.map p ≫ j →
          (Scheme.Γ.map (Fs.map p).op).hom (s1 T j) = t.val (op (CostructuredArrow.mk c0)) := by
      intro T j W c0 p hw
      let l0 := Yoneda.fullyFaithful.preimage ((sq T j).lift c0 (yoneda.map p) hw)
      have hl0 : yoneda.map l0 = (sq T j).lift c0 (yoneda.map p) hw :=
        Yoneda.fullyFaithful.map_preimage _
      have hfac : l0 ≫ pr T j = p :=
        yoneda.map_injective (by rw [Functor.map_comp, hl0, (sq T j).lift_snd])
      have hc : yoneda.map l0 ≫ c T j = c0 := by rw [hl0, (sq T j).lift_fst]
      rw [← hfac, Functor.map_comp, ← gamma_map_comp_apply, hs1 T j]
      change (Scheme.Γ.map (Fs.map l0).op).hom (t.val (op (CostructuredArrow.mk (c T j)))) = _
      rw [chartFunctions_restrict, hc]
    refine ⟨⟨fun J => s1 J.unop.left J.unop.hom, fun {J J'} g => ?_⟩, ?_⟩
    · obtain ⟨⟨T, ⟨⟨⟩⟩, j⟩⟩ := J
      obtain ⟨⟨T', ⟨⟨⟩⟩, j'⟩⟩ := J'
      obtain ⟨⟨h, ⟨⟨⟨⟩⟩⟩, w⟩⟩ := g
      simp only [Functor.const_obj_obj, Discrete.functor_map_id, Category.comp_id] at w
      have hw : c T' j' ≫ π = yoneda.map (pr T' j' ≫ h) ≫ j := by
        rw [(sq T' j').w, Functor.map_comp, Category.assoc, w]
      change (Scheme.Γ.map (Fs.map h).op).hom (s1 T j) = s1 T' j'
      refine (hΓ j' _ _ (sq T' j')).1 ?_
      rw [hs1 T' j', gamma_map_comp_apply, ← Functor.map_comp]
      exact hrest T j _ _ hw
    · apply Subtype.ext
      funext K
      obtain ⟨⟨W, ⟨⟨⟩⟩, c0⟩⟩ := K
      change s1 W (c0 ≫ π) = t.val (op (CostructuredArrow.mk c0))
      exact hrest W (c0 ≫ π) c0 (𝟙 W) (by simp)

/-- Pullback of global regular functions along a morphism of algebraic spaces is bijective
exactly when pullback of compatible families on all scheme charts is. -/
theorem bijective_globalFunctionsMap_iff {U V : AlgebraicSpaces B S hS} (f : V ⟶ U) :
    Function.Bijective (Space.globalFunctionsMap B S hS f) ↔
      Function.Bijective (Space.chartFunctionsMap B S hS f.hom) := by
  let eU := (Space.globalFunctionsChartEquiv B S hS U).val
  let eV := (Space.globalFunctionsChartEquiv B S hS V).val
  have h : (Space.globalFunctionsMap B S hS f : _ → _) =
      eV.symm ∘ Space.chartFunctionsMap B S hS f.hom ∘ eU := rfl
  rw [h, Function.Bijective.of_comp_iff' eV.symm.bijective,
    Function.Bijective.of_comp_iff _ eU.bijective]

/-- **Base change of a morphism of schemes along an algebraic space is bijective on global
functions** as soon as every base change along a morphism of schemes of the site is: for a
morphism `g : T ⟶ U` of the site and an algebraic space `Y ⟶ U`, pullback of global regular
functions along the projection `T ×_U Y ⟶ Y` is bijective. -/
theorem bijective_globalFunctionsMap_fiberProduct_snd {T U : BigFppfOver B S hS} (g : T ⟶ U)
    (hg : ∀ {P T' : BigFppfOver B S hS} (a : P ⟶ T) (pr : P ⟶ T') (m : T' ⟶ U),
      IsPullback a pr g m →
        Function.Bijective (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map pr).op).hom)
    (Y : AlgebraicSpaces B S hS) (g' : Y ⟶ schemeSpace U) :
    Function.Bijective (Space.globalFunctionsMap B S hS
      (ObjectProperty.homMk (pullback.snd (schemeSpaceMap g).hom g'.hom) :
        AlgebraicSpaces.fiberProduct B S hS (schemeSpaceMap g) g' ⟶ Y)) := by
  rw [bijective_globalFunctionsMap_iff]
  have hR : IsPullback (P := (AlgebraicSpaces.fiberProduct B S hS (schemeSpaceMap g) g').obj)
      (X := (schemeSpace T).obj) (pullback.fst (schemeSpaceMap g).hom g'.hom)
      (pullback.snd (schemeSpaceMap g).hom g'.hom) (schemeSpaceMap g).hom g'.hom :=
    IsPullback.of_hasPullback _ _
  refine chartFunctionsMap_bijective_of_isPullback _ (fun T' j => ?_) (fun {T' P} j pr c hsq => ?_)
  · obtain ⟨m, hm⟩ : ∃ m : T' ⟶ U, yoneda.map m = j ≫ g'.hom := yoneda.map_surjective _
    let a0 : yoneda.obj (pullback g m) ⟶ (schemeSpace T).obj := yoneda.map (pullback.fst g m)
    have hbig : IsPullback a0 (yoneda.map (pullback.snd g m)) (schemeSpaceMap g).hom
        (j ≫ g'.hom) := by
      rw [← hm]
      exact (IsPullback.of_hasPullback g m).map yoneda
    refine ⟨pullback g m, pullback.snd g m,
      hR.lift a0 (yoneda.map (pullback.snd g m) ≫ j)
        (by rw [Category.assoc]; exact hbig.w), ?_⟩
    exact IsPullback.of_right (by rw [hR.lift_fst]; exact hbig) (hR.lift_snd _ _ _) hR
  · have hbig := hsq.paste_horiz hR
    obtain ⟨m, hm⟩ : ∃ m : T' ⟶ U, yoneda.map m = j ≫ g'.hom := yoneda.map_surjective _
    obtain ⟨a, ha⟩ : ∃ a : P ⟶ T, yoneda.map a = c ≫ pullback.fst _ _ := yoneda.map_surjective _
    rw [← hm, ← ha] at hbig
    exact hg a pr m (IsPullback.of_map_of_faithful yoneda hbig)

/-- **Global functions on a morphism of schemes of the site.** If pullback of global regular
functions along the morphism of algebraic spaces of a morphism `g` of schemes of the site is
bijective, then so is `Γ(g)`: the two agree under evaluation at the identity charts. -/
theorem bijective_appTop_of_bijective_globalFunctionsMap {T U : BigFppfOver B S hS} (g : T ⟶ U)
    (hb : Function.Bijective (Space.globalFunctionsMap B S hS (schemeSpaceMap g))) :
    Function.Bijective ((BigFppfOver.toScheme B S hS).map g).appTop.hom := by
  let eT := Space.globalFunctionsYonedaRingEquiv B S hS T
  let eU := Space.globalFunctionsYonedaRingEquiv B S hS U
  have hfun : (((BigFppfOver.toScheme B S hS).map g).appTop.hom : _ → _) ∘ eU =
      eT ∘ Space.globalFunctionsMap B S hS (schemeSpaceMap g) := funext fun s =>
    (Space.globalFunctionsMap_val_chart B S hS (schemeSpaceMap g)
      (Space.idEtaleChart B S hS U) (Space.idEtaleChart B S hS T) g
      ((Category.comp_id _).trans (Category.id_comp _).symm) s).symm
  exact (Function.Bijective.of_comp_iff _ eU.bijective).1 (hfun ▸ eT.bijective.comp hb)

end Chart

/-! ### Flat base change of `H⁰ = k` -/

/-- **`H⁰(X, 𝒪_X) = k` is preserved by base change to any scheme over `Spec k`.** For a
quasi-compact quasi-separated morphism `f : X ⟶ Spec k` with `Γ(X, 𝒪_X) = k` and a cartesian
square with `m : T ⟶ Spec k`, pullback of global functions along the projection `pr : P ⟶ T` is
bijective. Every scheme over a field is flat over it, so this is flat base change in degree zero
([Stacks, Tag 02KH]). -/
theorem bijective_appTop_of_isPullback {k : Type u} [Field k] {X P T : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] {a : P ⟶ X} {pr : P ⟶ T}
    {m : T ⟶ Spec (.of k)} (h : IsPullback a pr f m) :
    Function.Bijective (Scheme.Γ.map pr.op).hom := by
  have : IsIso f.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv f.appTop
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have hs := Stacks.Groupoids.isIso_structureSheafHom_pullback_snd_of_isIso_appTop f m
  have h1 : IsIso ((sheafToPresheaf _ _).map (RingedSpaceModuleAdjunction.structureSheafHom
      (pullback.snd f m).toLRSHom.toShHom)) := Functor.map_isIso _ _
  have h2 := NatIso.isIso_app_of_isIso ((sheafToPresheaf _ _).map
    (RingedSpaceModuleAdjunction.structureSheafHom (pullback.snd f m).toLRSHom.toShHom)) (op ⊤)
  have h3 : IsIso ((forget₂ CommRingCat RingCat).map ((pullback.snd f m).app ⊤)) := h2
  have : IsIso ((pullback.snd f m).app ⊤) := isIso_of_reflects_iso _ (forget₂ CommRingCat RingCat)
  have hpr : pr = h.isoPullback.hom ≫ pullback.snd f m := h.isoPullback_hom_snd.symm
  have : IsIso (Scheme.Γ.map pr.op) := by
    rw [hpr, op_comp, Functor.map_comp]
    have : IsIso (Scheme.Γ.map (pullback.snd f m).op) :=
      inferInstanceAs (IsIso ((pullback.snd f m).app ⊤))
    infer_instance
  exact ConcreteCategory.bijective_of_isIso _

/-! ### The family of curves of a proper scheme over a field -/

/-- **`f_*𝒪_X = 𝒪_S` universally for the family of curves of a proper scheme over a field.** For
a proper scheme `X` of dimension at most one over a field `k`, its family of curves `X ⟶ Spec k`
has `f_*𝒪_X = 𝒪_{Spec k}` universally exactly when `k = H⁰(X, 𝒪_X)`. One direction is base change
along the identity of `Spec k`; for the other, every base change to a scheme of the site is
bijective on global functions by flat base change
(`AlgebraicGeometry.C1590Private.bijective_appTop_of_isPullback`), and then so is every base change
to an algebraic space
(`AlgebraicGeometry.C1590Private.bijective_globalFunctionsMap_fiberProduct_snd`). -/
theorem hasUniversallyBijectiveGlobalFunctions_curveFamilyOfScheme_iff {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [IsProper X.hom] (B : BigFppfSite.{u})
    (hZ : B.Contains integerBase) (hk : B.Contains (Spec (.of k)))
    (hdim : topologicalKrullDim X.left ≤ 1) :
    HasUniversallyBijectiveGlobalFunctions B hZ (curveFamilyOfScheme X B hZ hk hdim) ↔
      IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) := by
  let g := integerSiteMap B hZ (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hk) hk
    X.hom
  have hPB : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B integerBase hZ) := by
    dsimp [BigFppfOver.toScheme]
    infer_instance
  constructor
  · intro h
    have h1 := HasUniversallyBijectiveGlobalFunctions.bijective_globalFunctionsMap B hZ h
    have hb := bijective_appTop_of_bijective_globalFunctionsMap g h1
    have : IsIso X.hom.appTop := (ConcreteCategory.isIso_iff_bijective _).2 hb
    infer_instance
  · intro hX Y g'
    refine bijective_globalFunctionsMap_fiberProduct_snd g (fun a pr m hsq => ?_) Y g'
    have hS : IsPullback ((BigFppfOver.toScheme B integerBase hZ).map a)
        ((BigFppfOver.toScheme B integerBase hZ).map pr) X.hom
        ((BigFppfOver.toScheme B integerBase hZ).map m) :=
      hsq.map (BigFppfOver.toScheme B integerBase hZ)
    exact bijective_appTop_of_isPullback X.hom hS

end AlgebraicGeometry.C1590Private

end
