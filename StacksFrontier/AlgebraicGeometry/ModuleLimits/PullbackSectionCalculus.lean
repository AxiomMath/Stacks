module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalAffine

/-!
# Morphisms out of a pullback, and the calculus of the canonical identification

A morphism of sheaves of modules out of a pullback `f^*M` is determined by what it does to the
pulled-back sections `AlgebraicGeometry.Scheme.Modules.pullbackSection f M U (f⁻¹U) a`: that is
the adjunction `f^* ⊣ f_*` read on sections, and it is the content of
`hom_ext_of_pullbackSection` below.  Iterating it through the canonical identification
`Stacks.AlgebraicGeometry.ModuleLimits.canHom` gives the same criterion for an iterated
pullback, where the sections to test on are the doubly and triply pulled-back ones.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.doublePullbackSection` and
  `triplePullbackSection`: a section of `F` over `U`, pulled back along two resp. three
  composable morphisms, over the iterated preimage of `U`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_pullbackSection`: two morphisms
  `f^*M ⟶ N` agreeing on every pulled-back section are equal.
* `Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_doublePullbackSection` and
  `hom_ext_of_triplePullbackSection`: the same for an iterated pullback.
* `Stacks.AlgebraicGeometry.ModuleLimits.canHom_val_app_pullbackSection` and
  `canHom_inv_val_app_pullbackSection`: the canonical identification carries an iterated
  pulled-back section to the section pulled back along the composite, at arbitrary opens.
* `Stacks.AlgebraicGeometry.ModuleLimits.canHom_cocycle`: **the cocycle condition for the
  canonical identification.**  For a composable triple the two routes from `r^*(q^*(g^*F))` to
  the pullback of `F` along the total composite agree.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctorIsoPullback_hom_val_app`: along an open
  immersion the comparison of the restriction with the pullback sends a section to its pullback.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-! ### Two utilities on sections -/

/-- Pulling a section back and then restricting to a smaller open is pulling it back to that
open.  Only the open of the *source* shrinks. -/
theorem pullbackSection_shrink {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (V V' : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (hV : V' ≤ V) (h' : V' ≤ f ⁻¹ᵁ U)
    (a : M.val.obj (op U)) :
    ((Scheme.Modules.pullback f).obj M).val.map (homOfLE hV).op
        (pullbackSection f M U V h a)
      = pullbackSection f M U V' h' a := by
  unfold pullbackSection
  refine (PresheafOfModules.map_comp_apply _ (homOfLE h).op (homOfLE hV).op _).symm.trans ?_
  congr 2

/-- The inverse of an isomorphism of sheaves of modules undoes it on sections. -/
theorem inv_val_app_apply {Y : Scheme.{u}} {A B : Y.Modules} (θ : A ⟶ B) [IsIso θ]
    (V : Y.Opens) (x : A.val.obj (op V)) :
    (inv θ).val.app (op V) (θ.val.app (op V) x) = x :=
  congrArg (fun k : A ⟶ A => k.val.app (op V) x) (IsIso.hom_inv_id θ)

/-- If `θ` sends `x` to `y`, then `inv θ` sends `y` back to `x`. -/
private theorem inv_val_app_eq_of_val_app_eq {Y : Scheme.{u}} {A B : Y.Modules} (θ : A ⟶ B)
    [IsIso θ] (V : Y.Opens) (x : A.val.obj (op V)) (y : B.val.obj (op V))
    (h : θ.val.app (op V) x = y) : (inv θ).val.app (op V) y = x :=
  h ▸ inv_val_app_apply θ V x

/-- Precomposing with `inv θ` and evaluating at `y` is evaluating at the preimage `x` of `y`. -/
private theorem inv_comp_val_app_eq {Y : Scheme.{u}} {A B N : Y.Modules} (θ : A ⟶ B) [IsIso θ]
    (α : A ⟶ N) (V : Y.Opens) (x : A.val.obj (op V)) (y : B.val.obj (op V))
    (h : (inv θ).val.app (op V) y = x) : (inv θ ≫ α).val.app (op V) y = α.val.app (op V) x :=
  h ▸ rfl

/-! ### Morphisms out of a pullback are determined on pulled-back sections -/

/-- The adjunction `f^* ⊣ f_*` read on sections: the transpose of `α` acts on a section `a` of
`M` over `U` by applying `α` to the pullback of `a`. -/
theorem homEquiv_val_app {X Y : Scheme.{u}} (f : Y ⟶ X) {M : X.Modules} {N : Y.Modules}
    (α : (Scheme.Modules.pullback f).obj M ⟶ N) (U : X.Opens) (a : M.val.obj (op U)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M N) α).val.app (op U) a =
      α.val.app (op (f ⁻¹ᵁ U)) (pullbackSection f M U (f ⁻¹ᵁ U) le_rfl a) := by
  rw [Adjunction.homEquiv_apply]
  unfold pullbackSection
  rw [show (homOfLE (le_refl (f ⁻¹ᵁ U))).op = 𝟙 _ from Subsingleton.elim _ _]
  simp
  rfl

/-- **Morphisms out of a pullback are determined on pulled-back sections.**  Two morphisms
`f^*M ⟶ N` that agree on `pullbackSection f M U (f⁻¹U) a` for every open `U` of the target and
every section `a` of `M` over `U` are equal. -/
theorem hom_ext_of_pullbackSection {X Y : Scheme.{u}} (f : Y ⟶ X) {M : X.Modules} {N : Y.Modules}
    {α β : (Scheme.Modules.pullback f).obj M ⟶ N}
    (h : ∀ (U : X.Opens) (a : M.val.obj (op U)),
      α.val.app (op (f ⁻¹ᵁ U)) (pullbackSection f M U (f ⁻¹ᵁ U) le_rfl a) =
        β.val.app (op (f ⁻¹ᵁ U)) (pullbackSection f M U (f ⁻¹ᵁ U) le_rfl a)) :
    α = β := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M N).injective
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext a
  exact (homEquiv_val_app f α U a).trans ((h U a).trans (homEquiv_val_app f β U a).symm)

/-! ### The canonical identification on sections -/

/-- **The canonical identification on sections, at arbitrary opens.**  It carries the section
obtained by pulling `a` back along `g` and then along `q` to the section obtained by pulling `a`
back along the composite. -/
theorem canHom_val_app_pullbackSection {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X)
    (pi : W ⟶ X) (hpi : q ≫ g = pi) (F : X.Modules) (U : X.Opens) (W₀ : Z.Opens) (V : W.Opens)
    (hg : W₀ ≤ g ⁻¹ᵁ U) (hf : V ≤ q ⁻¹ᵁ W₀) (h : V ≤ pi ⁻¹ᵁ U) (a : F.val.obj (op U)) :
    (canHom q g pi hpi F).val.app (op V)
        (pullbackSection q ((Scheme.Modules.pullback g).obj F) W₀ V hf
          (pullbackSection g F U W₀ hg a))
      = pullbackSection pi F U V h a := by
  rw [canHom]
  change ((Scheme.Modules.pullbackCongr hpi).hom.app F).val.app (op V)
    (((Scheme.Modules.pullbackComp q g).hom.app F).val.app (op V) _) = _
  rw [pullbackSection_comp q g F U W₀ V hg hf (hpi ▸ h), pullbackSection_congr hpi F U V _ h]

/-- The inverse of the canonical identification carries a pulled-back section to the twice
pulled-back section. -/
theorem canHom_inv_val_app_pullbackSection {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X)
    (pi : W ⟶ X) (hpi : q ≫ g = pi) (F : X.Modules) (U : X.Opens) (W₀ : Z.Opens) (V : W.Opens)
    (hg : W₀ ≤ g ⁻¹ᵁ U) (hf : V ≤ q ⁻¹ᵁ W₀) (h : V ≤ pi ⁻¹ᵁ U) (a : F.val.obj (op U)) :
    (inv (canHom q g pi hpi F)).val.app (op V) (pullbackSection pi F U V h a)
      = pullbackSection q ((Scheme.Modules.pullback g).obj F) W₀ V hf
          (pullbackSection g F U W₀ hg a) := by
  exact inv_val_app_eq_of_val_app_eq _ V _ _
    (canHom_val_app_pullbackSection q g pi hpi F U W₀ V hg hf h a)

/-! ### Iterated pulled-back sections, and the criteria they support -/

/-- The section of `q^*(g^*F)` over `q⁻¹(g⁻¹U)` obtained by pulling a section of `F` over `U`
back along `g` and then along `q`. -/
noncomputable def doublePullbackSection {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X)
    (F : X.Modules) (U : X.Opens) (a : F.val.obj (op U)) :
    ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj F)).val.obj
      (op (q ⁻¹ᵁ (g ⁻¹ᵁ U))) :=
  pullbackSection q ((Scheme.Modules.pullback g).obj F) (g ⁻¹ᵁ U) (q ⁻¹ᵁ (g ⁻¹ᵁ U)) le_rfl
    (pullbackSection g F U (g ⁻¹ᵁ U) le_rfl a)

/-- **Morphisms out of a twice-iterated pullback are determined on twice pulled-back
sections.** -/
theorem hom_ext_of_doublePullbackSection {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X)
    {F : X.Modules} {N : W.Modules}
    {α β : (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj F) ⟶ N}
    (h : ∀ (U : X.Opens) (a : F.val.obj (op U)),
      α.val.app (op (q ⁻¹ᵁ (g ⁻¹ᵁ U))) (doublePullbackSection q g F U a)
        = β.val.app (op (q ⁻¹ᵁ (g ⁻¹ᵁ U))) (doublePullbackSection q g F U a)) :
    α = β := by
  refine (cancel_epi (inv (canHom q g (q ≫ g) rfl F))).mp
    (hom_ext_of_pullbackSection (q ≫ g) (M := F) (N := N) ?_)
  intro U a
  have e := canHom_inv_val_app_pullbackSection q g (q ≫ g) rfl F U (g ⁻¹ᵁ U) ((q ≫ g) ⁻¹ᵁ U)
    le_rfl le_rfl le_rfl a
  exact (inv_comp_val_app_eq _ α _ _ _ e).trans
    ((h U a).trans (inv_comp_val_app_eq _ β _ _ _ e).symm)

/-- The section of `r^*(q^*(g^*F))` obtained by pulling a section of `F` over `U` back along
`g`, then `q`, then `r`. -/
noncomputable def triplePullbackSection {V₁ W Z X : Scheme.{u}} (r : V₁ ⟶ W) (q : W ⟶ Z)
    (g : Z ⟶ X) (F : X.Modules) (U : X.Opens) (a : F.val.obj (op U)) :
    ((Scheme.Modules.pullback r).obj
      ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj F))).val.obj
        (op (r ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U)))) :=
  pullbackSection r ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj F))
    (q ⁻¹ᵁ (g ⁻¹ᵁ U)) (r ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U))) le_rfl (doublePullbackSection q g F U a)

/-- Applying `f^*` of the canonical identification to a thrice pulled-back section gives the
section pulled back along the composite `qg`. -/
private theorem map_pullback_canHom_triplePullbackSection {V₁ W Z X : Scheme.{u}} (r : V₁ ⟶ W)
    (q : W ⟶ Z) (g : Z ⟶ X) (qg : W ⟶ X) (hqg : q ≫ g = qg) (F : X.Modules) (U : X.Opens)
    (a : F.val.obj (op U)) (hqgle : q ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ qg ⁻¹ᵁ U) :
    ((Scheme.Modules.pullback r).map (canHom q g qg hqg F)).val.app
        (op (r ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U)))) (triplePullbackSection r q g F U a)
      = pullbackSection r ((Scheme.Modules.pullback qg).obj F) (q ⁻¹ᵁ (g ⁻¹ᵁ U))
          (r ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U))) le_rfl (pullbackSection qg F U (q ⁻¹ᵁ (g ⁻¹ᵁ U)) hqgle a) := by
  rw [triplePullbackSection,
    pullbackSection_naturality r (canHom q g qg hqg F) (q ⁻¹ᵁ (g ⁻¹ᵁ U))
      (r ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U))) le_rfl (doublePullbackSection q g F U a),
    doublePullbackSection,
    canHom_val_app_pullbackSection q g qg hqg F U (g ⁻¹ᵁ U) (q ⁻¹ᵁ (g ⁻¹ᵁ U))
      le_rfl le_rfl hqgle a]

/-- **Morphisms out of a thrice-iterated pullback are determined on thrice pulled-back
sections.** -/
theorem hom_ext_of_triplePullbackSection {V₁ W Z X : Scheme.{u}} (r : V₁ ⟶ W) (q : W ⟶ Z)
    (g : Z ⟶ X) {F : X.Modules} {N : V₁.Modules}
    {α β : (Scheme.Modules.pullback r).obj
      ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj F)) ⟶ N}
    (h : ∀ (U : X.Opens) (a : F.val.obj (op U)),
      α.val.app (op (r ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U)))) (triplePullbackSection r q g F U a)
        = β.val.app (op (r ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U)))) (triplePullbackSection r q g F U a)) :
    α = β := by
  refine (cancel_epi (inv ((Scheme.Modules.pullback r).map (canHom q g (q ≫ g) rfl F)))).mp
    (hom_ext_of_doublePullbackSection r (q ≫ g) (F := F) (N := N) ?_)
  intro U a
  have e := inv_val_app_eq_of_val_app_eq _ _ _ _
    (map_pullback_canHom_triplePullbackSection r q g (q ≫ g) rfl F U a le_rfl)
  exact (inv_comp_val_app_eq _ α _ _ _ e).trans
    ((h U a).trans (inv_comp_val_app_eq _ β _ _ _ e).symm)

/-! ### The cocycle condition for the canonical identification -/

/-- **The canonical identifications satisfy the cocycle condition.**  For a composable triple
`r`, `q`, `g` the two ways of identifying `r^*(q^*(g^*F))` with the pullback of `F` along the
total composite — first contract `q` and `g`, or first contract `r` and `q` — agree. -/
theorem canHom_cocycle {V₁ W Z X : Scheme.{u}} (r : V₁ ⟶ W) (q : W ⟶ Z) (g : Z ⟶ X)
    (rq : V₁ ⟶ Z) (qg : W ⟶ X) (pi : V₁ ⟶ X) (hrq : r ≫ q = rq) (hqg : q ≫ g = qg)
    (h1 : rq ≫ g = pi) (h2 : r ≫ qg = pi) (F : X.Modules) :
    (Scheme.Modules.pullback r).map (canHom q g qg hqg F) ≫ canHom r qg pi h2 F
      = canHom r q rq hrq ((Scheme.Modules.pullback g).obj F) ≫ canHom rq g pi h1 F := by
  refine hom_ext_of_triplePullbackSection r q g (F := F) fun U a => ?_
  have hqgle : q ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ qg ⁻¹ᵁ U := hqg ▸ le_rfl
  have hrqle : r ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U)) ≤ rq ⁻¹ᵁ (g ⁻¹ᵁ U) := hrq ▸ le_rfl
  have hpile : r ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U)) ≤ pi ⁻¹ᵁ U := by rw [← h2, ← hqg]; exact le_rfl
  have hL : ((Scheme.Modules.pullback r).map (canHom q g qg hqg F) ≫
        canHom r qg pi h2 F).val.app (op (r ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U))))
        (triplePullbackSection r q g F U a)
      = pullbackSection pi F U (r ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U))) hpile a := by
    change (canHom r qg pi h2 F).val.app (op (r ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U))))
      (((Scheme.Modules.pullback r).map (canHom q g qg hqg F)).val.app
        (op (r ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U)))) (triplePullbackSection r q g F U a)) = _
    rw [map_pullback_canHom_triplePullbackSection r q g qg hqg F U a hqgle,
      canHom_val_app_pullbackSection r qg pi h2 F U (q ⁻¹ᵁ (g ⁻¹ᵁ U))
        (r ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U))) hqgle le_rfl hpile a]
  have hR : (canHom r q rq hrq ((Scheme.Modules.pullback g).obj F) ≫
        canHom rq g pi h1 F).val.app (op (r ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U))))
        (triplePullbackSection r q g F U a)
      = pullbackSection pi F U (r ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U))) hpile a := by
    change (canHom rq g pi h1 F).val.app (op (r ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U))))
      ((canHom r q rq hrq ((Scheme.Modules.pullback g).obj F)).val.app
        (op (r ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U)))) (triplePullbackSection r q g F U a)) = _
    rw [triplePullbackSection, doublePullbackSection,
      canHom_val_app_pullbackSection r q rq hrq ((Scheme.Modules.pullback g).obj F)
        (g ⁻¹ᵁ U) (q ⁻¹ᵁ (g ⁻¹ᵁ U)) (r ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U))) le_rfl le_rfl hrqle
        (pullbackSection g F U (g ⁻¹ᵁ U) le_rfl a),
      canHom_val_app_pullbackSection rq g pi h1 F U (g ⁻¹ᵁ U)
        (r ⁻¹ᵁ (q ⁻¹ᵁ (g ⁻¹ᵁ U))) le_rfl hrqle hpile a]
  exact hL.trans hR.symm

/-! ### The comparison of a restriction with a pullback, on sections -/

/-- Along an open immersion the comparison of the restriction with the pullback carries a
section to its pullback. -/
theorem restrictFunctorIsoPullback_hom_val_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ (f ''ᵁ V)) (t : (Scheme.Modules.restrict M f).val.obj (op V)) :
    ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M).val.app (op V) t =
      pullbackSection f M (f ''ᵁ V) V h t := by
  have hid : M.val.map (homOfLE (le_refl (f ''ᵁ V))).op t = t := by
    rw [show (homOfLE (le_refl (f ''ᵁ V))).op = 𝟙 _ from Subsingleton.elim _ _]
    simp
    rfl
  have h2 := Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection f M (f ''ᵁ V) V h
    le_rfl t
  rw [hid] at h2
  refine Eq.trans (congrArg (fun y : (Scheme.Modules.restrict M f).val.obj (op V) =>
    ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M).val.app (op V) y) h2.symm) ?_
  exact congrArg (fun k : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj M =>
    k.val.app (op V) (pullbackSection f M (f ''ᵁ V) V h t))
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M).inv_hom_id

end Stacks.AlgebraicGeometry.ModuleLimits

end
