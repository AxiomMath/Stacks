module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleComparison
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSubmoduleFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSections
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCechDirectImagePushforward

/-!
# The associated module of a map out of an ideal sheaf, away from its support

Let `V` be a scheme of the big fppf site over `S`, let `E` be a sheaf of ideals on `V` and let
`t̃ : E ⟶ 𝒪_V` be a map of `𝒪_V`-modules which, on the open `U₀ = V ∖ V(E)`, is multiplication
by a function `f` on `U₀` against the inclusion `ι : E ⟶ 𝒪_V`. Then the associated module
`Φ = AlgebraicGeometry.Space.representedAssociatedModule` of Stacks 03DU (4) carries `t̃` to the
multiple of `Φ ι` by the pullback of `f`, on every étale chart of `h_V` which lands in `U₀`.

## Main definitions

* `AlgebraicGeometry.C1590Private.AssociatedModuleMapAwayFromSupport`: the proposition that `Φ`
  carries `t̃` to the multiple of `Φ ι` by the pullback of `f` on every such chart.
* `AlgebraicGeometry.C1590Private.unitSectionOfGlobal`: a global function on a scheme `X`, read
  as a global section of the structure sheaf of the small étale site of `X`.
* `AlgebraicGeometry.C1590Private.associatedModuleUnitToUnit`: the comparison
  `(𝒪_T)^a ⟶ 𝒪` of the associated module of the structure sheaf with the structure sheaf of the
  small étale site, with its source written through
  `AlgebraicGeometry.SmallEtale.associatedModule`.

## Main results

* `AlgebraicGeometry.C1590Private.associatedModule_map_app_eq_smul_of_eq_mul`: the statement on
  the small étale site of a scheme `T`: if `α, β : M ⟶ 𝒪_T` satisfy `α = f · β` over every open
  inside `U₀`, then `α^a = f · β^a` over every étale `W₀ / T` landing in `U₀`.
* `AlgebraicGeometry.C1590Private.associatedModuleMapAwayFromSupport`: the same statement for
  `Φ = AlgebraicGeometry.Space.representedAssociatedModule`.

## References

* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.C1590Private

universe u

/-! ### Pulling back functions along a morphism landing in an open -/

section Opens

variable {T Z : Scheme.{u}} (W : T.Opens)

/-- The inverse of `W.topIso` is the restriction map `Γ(T, W) ⟶ Γ(W, ⊤)`. -/
private theorem topIso_inv_eq_appLE : W.topIso.inv = W.ι.appLE W ⊤ (by simp) := by
  rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  exact congrArg (fun i => T.presheaf.map i) (Subsingleton.elim _ _)

/-- `Scheme.Hom.appLE` into the top open, composed with the global sections of a map. -/
private theorem appLE_comp_appTop {X : Scheme.{u}} (g : X ⟶ T) (U : T.Opens) (hg : ⊤ ≤ g ⁻¹ᵁ U)
    (p : Z ⟶ X) (hp : ⊤ ≤ (p ≫ g) ⁻¹ᵁ U) : g.appLE U ⊤ hg ≫ p.appTop = (p ≫ g).appLE U ⊤ hp := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _

/-- `Scheme.Hom.appLE` along equal morphisms. -/
private theorem appLE_congr_hom {h₁ h₂ : Z ⟶ T} (e : h₁ = h₂) (U : T.Opens) (V : Z.Opens)
    (e₁ : V ≤ h₁ ⁻¹ᵁ U) (e₂ : V ≤ h₂ ⁻¹ᵁ U) : h₁.appLE U V e₁ = h₂.appLE U V e₂ := by
  subst e
  rfl

/-- A relation between sections over `W ∩ U₀` survives pullback to a scheme over `W` landing in
`U₀`: if `p₁ : Z ⟶ W` and `p₂ : Z ⟶ X` form a commutative square with `g : X ⟶ T`, and `g`
lands in `U₀`, then `s|_{W ∩ U₀} = f|_{W ∩ U₀} · t|_{W ∩ U₀}` gives
`p₁^♯ s = p₁^♯ t · p₂^♯ (g^♯ f)`. -/
theorem appTop_topIso_inv_eq_mul {X : Scheme.{u}} (p₁ : Z ⟶ W.toScheme) (p₂ : Z ⟶ X)
    (g : X ⟶ T) (hc : p₁ ≫ W.ι = p₂ ≫ g) (U₀ : T.Opens) (f : Γ(T, U₀))
    (hg : ⊤ ≤ g ⁻¹ᵁ U₀) (s t : Γ(T, W))
    (hst : T.presheaf.map (homOfLE (inf_le_left : W ⊓ U₀ ≤ W)).op s =
      T.presheaf.map (homOfLE (inf_le_right : W ⊓ U₀ ≤ U₀)).op f *
        T.presheaf.map (homOfLE (inf_le_left : W ⊓ U₀ ≤ W)).op t) :
    p₁.appTop (W.topIso.inv s) = p₁.appTop (W.topIso.inv t) * p₂.appTop (g.appLE U₀ ⊤ hg f) := by
  have hle : ⊤ ≤ (p₁ ≫ W.ι) ⁻¹ᵁ (W ⊓ U₀) := by
    intro x _
    refine ⟨(p₁ x).2, ?_⟩
    show (p₁ ≫ W.ι) x ∈ U₀
    rw [hc]
    exact hg (Set.mem_univ (p₂ x))
  have e {Y : Scheme.{u}} (g' : Y ⟶ T) (q : Z ⟶ Y) (U : T.Opens) (hg' : ⊤ ≤ g' ⁻¹ᵁ U)
      (hq : q ≫ g' = p₁ ≫ W.ι) (hU : W ⊓ U₀ ≤ U) (r : Γ(T, U)) :
      q.appTop (g'.appLE U ⊤ hg' r) =
        (p₁ ≫ W.ι).appLE (W ⊓ U₀) ⊤ hle (T.presheaf.map (homOfLE hU).op r) := by
    have e1 := appLE_comp_appTop g' U hg' q (fun x _ => hg' (Set.mem_univ (q x)))
    refine (congrArg (fun φ => φ.hom r) (e1.trans (appLE_congr_hom hq _ _ _
      (fun x _ => hU (hle (Set.mem_univ x)))))).trans ?_
    exact (congrArg (fun φ => φ.hom r) (Scheme.Hom.map_appLE (p₁ ≫ W.ι) hle (homOfLE hU).op)).symm
  have eA (r : Γ(T, W)) : p₁.appTop (W.topIso.inv r) =
      (p₁ ≫ W.ι).appLE (W ⊓ U₀) ⊤ hle (T.presheaf.map (homOfLE inf_le_left).op r) := by
    rw [topIso_inv_eq_appLE]
    exact e W.ι p₁ W _ rfl inf_le_left r
  have eB := e g p₂ U₀ hg hc.symm inf_le_right f
  rw [eA, eA, eB, hst, map_mul, mul_comm]

end Opens

/-! ### The comparison on the small étale site of a scheme -/

section SmallEtale

variable (B : BigEtaleSite.{u})

/-- A global function `a` on the scheme of an object `X` of a big étale site, read as a global
section of the structure sheaf of the small étale site of `X`: over an étale `W / X` it is the
pullback of `a` to `W`. -/
def unitSectionOfGlobal (X : B.Scheme) (a : Γ(X.obj, ⊤)) :
    (SheafOfModules.unit (SmallEtale.structureSheaf B X.obj X.property)).sections :=
  PresheafOfModules.sectionsMk
    (fun W => (show Γ(W.unop.obj.left.obj, ⊤) from (B.inclusion.map W.unop.obj.hom).appTop a))
    (fun W W' h => by
      change (B.inclusion.map h.unop.hom.left).appTop
          ((B.inclusion.map W.unop.obj.hom).appTop a) =
        (B.inclusion.map W'.unop.obj.hom).appTop a
      rw [← Over.w h.unop.hom, Functor.map_comp, Scheme.Hom.comp_appTop]
      rfl)

variable (T : Scheme.{u}) (hT : B.Contains T)

/-- The comparison `(𝒪_T)^a ⟶ 𝒪` of the associated module of the structure sheaf of `T` with the
structure sheaf of the small étale site of `T`, with its source written through
`AlgebraicGeometry.SmallEtale.associatedModule`. -/
def associatedModuleUnitToUnit :
    (SmallEtale.associatedModule B T hT).obj (SheafOfModules.unit T.ringCatSheaf) ⟶
      SheafOfModules.unit (SmallEtale.structureSheaf B T hT) :=
  SheafOfModules.pullbackObjUnitToUnit (SmallEtale.structureMap B T hT)

/-- The adjunct of a map out of `(𝒪_T)^a` through `associatedModuleUnitToUnit`. -/
theorem homEquiv_associatedModuleUnitToUnit_comp
    {Q : SheafOfModules (SmallEtale.structureSheaf B T hT)}
    (k : SheafOfModules.unit (SmallEtale.structureSheaf B T hT) ⟶ Q) :
    (SmallEtale.associatedModuleAdjunction B T hT).homEquiv _ _
        (associatedModuleUnitToUnit B T hT ≫ k) =
      SheafOfModules.unitToPushforwardObjUnit (SmallEtale.structureMap B T hT) ≫
        (SmallEtale.restrictModule B T hT).map k :=
  ((SmallEtale.associatedModuleAdjunction B T hT).homEquiv_naturality_right _ k).trans
    (congrArg (· ≫ (SmallEtale.restrictModule B T hT).map k)
      (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _))

/-- The comparison against the test object `ε_{p*} 𝒪_{W₀}`: if `α = f · β` over the opens
inside `U₀` and `p : W₀ ⟶ T` lands in `U₀`, then `α^a` and `β^a` followed by multiplication by
`p^♯ f` agree after the map `𝒪 ⟶ ε_{p*} 𝒪_{W₀}`. -/
theorem associatedModule_map_comp_eq_of_eq_mul (M : T.Modules)
    (tt ι : M ⟶ SheafOfModules.unit T.ringCatSheaf) (U₀ : T.Opens)
    (f : Γ(T, U₀))
    (h : ∀ (W : T.Opens) (hW : W ≤ U₀) (x : M.val.obj (op W)),
      (show Γ(T, W) from tt.val.app (op W) x) =
        T.presheaf.map (homOfLE hW).op f * (show Γ(T, W) from ι.val.app (op W) x))
    (W₀ : SmallEtale B T hT) (hW₀ : ⊤ ≤ (B.inclusion.map W₀.obj.hom) ⁻¹ᵁ U₀) :
    (SmallEtale.associatedModule B T hT).map tt ≫
        associatedModuleUnitToUnit B T hT ≫
        SheafOfModules.unitToPushforwardObjUnit
          (SmallEtale.smallEtaleStructureMapRing B W₀.obj.hom) =
      (SmallEtale.associatedModule B T hT).map ι ≫
        associatedModuleUnitToUnit B T hT ≫
        SheafOfModules.unitToPushforwardObjUnit
          (SmallEtale.smallEtaleStructureMapRing B W₀.obj.hom) ≫
        (SheafOfModules.pushforward (SmallEtale.smallEtaleStructureMapRing B W₀.obj.hom)).map
          ((SheafOfModules.unitHomEquiv _).symm (unitSectionOfGlobal B W₀.obj.left
            ((B.inclusion.map W₀.obj.hom).appLE U₀ ⊤ hW₀ f))) := by
  set adj := SmallEtale.associatedModuleAdjunction B T hT
  apply (adj.homEquiv _ _).injective
  refine (adj.homEquiv_naturality_left tt _).trans
    ((congrArg (tt ≫ ·) (homEquiv_associatedModuleUnitToUnit_comp B T hT _)).trans (Eq.trans ?_
      ((adj.homEquiv_naturality_left ι _).trans
        (congrArg (ι ≫ ·) (homEquiv_associatedModuleUnitToUnit_comp B T hT _))).symm))
  ext W x
  show (B.inclusion.map (pullback.fst ((SmallEtale.opensToSmallEtale B T hT).obj W).obj.hom
      W₀.obj.hom)).appTop.hom (W.topIso.inv.hom (tt.val.app (op W) x)) =
    (B.inclusion.map (pullback.fst ((SmallEtale.opensToSmallEtale B T hT).obj W).obj.hom
      W₀.obj.hom)).appTop.hom (W.topIso.inv.hom (ι.val.app (op W) x)) *
    (B.inclusion.map (pullback.snd ((SmallEtale.opensToSmallEtale B T hT).obj W).obj.hom
      W₀.obj.hom)).appTop.hom ((B.inclusion.map W₀.obj.hom).appLE U₀ ⊤ hW₀ f)
  have hnat : ∀ (κ : M ⟶ SheafOfModules.unit T.ringCatSheaf),
      T.presheaf.map (homOfLE (inf_le_left : W ⊓ U₀ ≤ W)).op (κ.val.app (op W) x) =
        κ.val.app (op (W ⊓ U₀)) (M.val.map (homOfLE (inf_le_left : W ⊓ U₀ ≤ W)).op x) :=
    fun κ => (PresheafOfModules.naturality_apply κ.val _ x).symm
  refine appTop_topIso_inv_eq_mul W _ _ (B.inclusion.map W₀.obj.hom) ?_ U₀ f hW₀ _ _ ?_
  · exact (B.inclusion.map_comp _ _).symm.trans
      ((congrArg B.inclusion.map pullback.condition).trans (B.inclusion.map_comp _ _))
  · rw [hnat, hnat]
    exact h (W ⊓ U₀) inf_le_right _

/-- `α^a = f · β^a` over an étale `W₀ / T` landing in `U₀`, for maps `α, β : M ⟶ 𝒪_T` with
`α = f · β` over every open inside `U₀`. -/
theorem associatedModule_map_app_eq_smul_of_eq_mul (M : T.Modules)
    (tt ι : M ⟶ SheafOfModules.unit T.ringCatSheaf) (U₀ : T.Opens)
    (f : Γ(T, U₀))
    (h : ∀ (W : T.Opens) (hW : W ≤ U₀) (x : M.val.obj (op W)),
      (show Γ(T, W) from tt.val.app (op W) x) =
        T.presheaf.map (homOfLE hW).op f * (show Γ(T, W) from ι.val.app (op W) x))
    (W₀ : SmallEtale B T hT) (hW₀ : ⊤ ≤ (B.inclusion.map W₀.obj.hom) ⁻¹ᵁ U₀)
    (z : ((SmallEtale.associatedModule B T hT).obj M).val.obj (op W₀)) :
    ((SmallEtale.associatedModule B T hT).map tt).val.app (op W₀) z =
      (show (SmallEtale.structureSheaf B T hT).obj.obj (op W₀) from
        (B.inclusion.map W₀.obj.hom).appLE U₀ ⊤ hW₀ f) •
        ((SmallEtale.associatedModule B T hT).map ι).val.app (op W₀) z := by
  have : IsIso (associatedModuleUnitToUnit B T hT) := SmallEtale.isIso_pullbackObjUnitToUnit B T hT
  have hinj : Function.Injective ((associatedModuleUnitToUnit B T hT).val.app (op W₀)) := by
    have h1 : ∀ w, ((inv (associatedModuleUnitToUnit B T hT)).val.app (op W₀)).hom
        (((associatedModuleUnitToUnit B T hT).val.app (op W₀)).hom w) = w := fun w =>
      congrArg (fun φ : (SmallEtale.associatedModule B T hT).obj
          (SheafOfModules.unit T.ringCatSheaf) ⟶
          (SmallEtale.associatedModule B T hT).obj (SheafOfModules.unit T.ringCatSheaf) =>
        (φ.val.app (op W₀)).hom w) (IsIso.hom_inv_id (associatedModuleUnitToUnit B T hT))
    exact fun p q hpq => (h1 p).symm.trans ((congrArg _ hpq).trans (h1 q))
  apply hinj
  have hk := congrArg (fun φ => (φ.val.app (op W₀)).hom z)
    (associatedModule_map_comp_eq_of_eq_mul B T hT M tt ι U₀ f h W₀ hW₀)
  set a : Γ(W₀.obj.left.obj, ⊤) := (B.inclusion.map W₀.obj.hom).appLE U₀ ⊤ hW₀ f
  set y := (associatedModuleUnitToUnit B T hT).val.app (op W₀)
    (((SmallEtale.associatedModule B T hT).map tt).val.app (op W₀) z)
  set y' := (associatedModuleUnitToUnit B T hT).val.app (op W₀)
    (((SmallEtale.associatedModule B T hT).map ι).val.app (op W₀) z)
  change (B.inclusion.map (pullback.fst W₀.obj.hom W₀.obj.hom)).appTop.hom y =
    (B.inclusion.map (pullback.fst W₀.obj.hom W₀.obj.hom)).appTop.hom y' *
      (B.inclusion.map (pullback.snd W₀.obj.hom W₀.obj.hom)).appTop.hom a at hk
  rw [LinearMap.map_smul]
  show (show Γ(W₀.obj.left.obj, ⊤) from y) = a * (show Γ(W₀.obj.left.obj, ⊤) from y')
  let d := pullback.lift (f := W₀.obj.hom) (g := W₀.obj.hom) (𝟙 W₀.obj.left) (𝟙 W₀.obj.left) rfl
  have hd (π : pullback W₀.obj.hom W₀.obj.hom ⟶ W₀.obj.left) (hπ : d ≫ π = 𝟙 _)
      (r : Γ(W₀.obj.left.obj, ⊤)) : (B.inclusion.map d).appTop.hom
      ((B.inclusion.map π).appTop.hom r) = r := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Functor.map_comp, hπ]
    simp
  have hfst := hd _ (pullback.lift_fst _ _ _)
  have hsnd := hd _ (pullback.lift_snd _ _ _)
  exact (hfst y).symm.trans ((congrArg (B.inclusion.map d).appTop.hom hk).trans
    ((map_mul _ _ _).trans ((congrArg₂ (· * ·) (hfst y') (hsnd a)).trans (mul_comm _ _))))

end SmallEtale

/-! ### The statement for a represented algebraic space -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `Φ` of a morphism out of a sheaf of ideals, away from the ideal: if a morphism `t̃ : I ⟶ 𝒪_V`
is multiplication by `f` on `U₀ = V ∖ V(I)`, then `Φ t̃` is multiplication by the pullback of `f`
against `Φ` of the inclusion, on every étale chart of `h_V` landing in `U₀`. -/
def AssociatedModuleMapAwayFromSupport : Prop :=
  ∀ (V : BigFppfOver B S hS) (E : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData)
    (tt : E.unitSubmodule.toSheafOfModules ⟶
      SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf)
    (f : Γ((BigFppfOver.toScheme B S hS).obj V, E.support.compl)),
    (∀ (W : ((BigFppfOver.toScheme B S hS).obj V).Opens) (hW : W ≤ E.support.compl)
      (x : E.unitSubmodule.toSheafOfModules.val.obj (op W)),
      (show Γ((BigFppfOver.toScheme B S hS).obj V, W) from tt.val.app (op W) x) =
        ((BigFppfOver.toScheme B S hS).obj V).presheaf.map (homOfLE hW).op f *
        (show Γ((BigFppfOver.toScheme B S hS).obj V, W) from
          (Stacks.ClosedSubscheme.idealIota E).val.app (op W) x)) →
    ∀ (U : Space.SmallEtale B S hS (yoneda.obj V))
      (hU : ⊤ ≤ (BigFppfOver.toScheme B S hS).map (yoneda.preimage U.1.hom) ⁻¹ᵁ E.support.compl)
      (z : ((Space.representedAssociatedModule B S hS V (isAlgebraicSpace_yoneda B S hS V)).obj
        E.unitSubmodule.toSheafOfModules).val.obj (op U)),
      ((Space.representedAssociatedModule B S hS V (isAlgebraicSpace_yoneda B S hS V)).map
          tt).val.app (op U) z =
        (show Space.chartRing B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V) U from
          ((BigFppfOver.toScheme B S hS).map (yoneda.preimage U.1.hom)).appLE
            E.support.compl ⊤ hU f) •
          ((Space.representedAssociatedModule B S hS V (isAlgebraicSpace_yoneda B S hS V)).map
            (Stacks.ClosedSubscheme.idealIota E)).val.app (op U) z

/-- `Φ` of a morphism out of a sheaf of ideals which is multiplication by `f` away from the ideal
is multiplication by the pullback of `f` against `Φ` of the inclusion, on every étale chart of
`h_V` landing in `U₀`: `AlgebraicGeometry.C1590Private.AssociatedModuleMapAwayFromSupport`
holds. -/
theorem associatedModuleMapAwayFromSupport : AssociatedModuleMapAwayFromSupport B S hS := by
  intro V E tt f h U hU z
  have hy : yonedaEquiv U.obj.hom = yoneda.preimage U.obj.hom :=
    yoneda.map_injective (by
      rw [Functor.map_preimage]
      apply yonedaEquiv.injective
      rw [yonedaEquiv_yoneda_map])
  have hg : (associatedBigEtaleSite B).inclusion.map
      ((Space.representedSmallEtaleEquivalence B S hS V).functor.obj U).obj.hom =
      (BigFppfOver.toScheme B S hS).map (yoneda.preimage U.obj.hom) := by
    rw [← hy]
    rfl
  have hU' : ⊤ ≤ (associatedBigEtaleSite B).inclusion.map
      ((Space.representedSmallEtaleEquivalence B S hS V).functor.obj U).obj.hom ⁻¹ᵁ
        E.support.compl := hg ▸ hU
  refine (associatedModule_map_app_eq_smul_of_eq_mul (associatedBigEtaleSite B) _
    V.left.property E.unitSubmodule.toSheafOfModules tt
    (Stacks.ClosedSubscheme.idealIota E) E.support.compl f h
    ((Space.representedSmallEtaleEquivalence B S hS V).functor.obj U) hU' z).trans ?_
  rw [appLE_congr_hom hg _ _ hU' hU]
  rfl

end AlgebraicGeometry.C1590Private

end
