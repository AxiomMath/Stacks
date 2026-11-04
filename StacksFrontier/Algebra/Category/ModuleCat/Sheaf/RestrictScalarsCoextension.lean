module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.RestrictScalarsCoextension
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.Subsheaf

@[expose] public section

/-
# Problem Description (continued, sheaf level)

Stacks Tag 0932 (Lemma 18.27.8), "Modules on Sites", Section 18.27 "Internal Hom", at the
*sheaf* level. The presheaf-level internal-hom (coextension of scalars) functor and its
adjunction with restriction of scalars are constructed in
`Stacks.PresheafOfModules.CoextendScalars` (file `Presheaf/RestrictScalarsCoextension.lean`).

Here `C` is a site `(C, J)` and `O O' : Sheaf J RingCat` are *sheaves* of rings, with
`φ : O ⟶ O'` a morphism of sheaves of rings. We build:

* the sheaf-level coextension-of-scalars functor
  `coextendScalars φ : SheafOfModules O ⥤ SheafOfModules O'`, agreeing with the presheaf-level
  `coextendScalars` on underlying presheaves of modules;
* the adjunction `SheafOfModules.restrictScalars φ ⊣ coextendScalars φ`.

## Strategy

By definition, `SheafOfModules R` is a `PresheafOfModules R.obj` together with a proof that
its underlying presheaf of abelian groups is a sheaf (`Presheaf.IsSheaf`). The underlying
presheaf of modules of the sheaf-level `coextendScalars` is literally the presheaf-level
`Stacks.PresheafOfModules.CoextendScalars.coextObj`; the sole new content at the sheaf level
is therefore the **sheaf condition**: for `F : SheafOfModules O`, the internal-hom presheaf
`(coextObj φ.hom F.val).presheaf` is a sheaf.

We prove this by comparing `coextObj` to Mathlib's `presheafHom` (the sheaf of *all* (not
necessarily `O`-linear) morphisms between the restrictions of the underlying `Ab`-presheaves
to slices), which is already known to be a sheaf of types whenever its target is
(`Presheaf.IsSheaf.hom`). The `O`-linear ones among these form a `Subfunctor` (a sub-presheaf
of types, `CategoryTheory.Subfunctor`), and `Subfunctor.isSheaf_iff` reduces the sheaf
condition for that subfunctor to a local-to-global statement about the linearity condition
itself, which is a consequence of the separatedness of the target sheaf.
-/

open CategoryTheory

namespace Stacks.SheafOfModules.CoextendScalars

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {O O' : Sheaf J RingCat.{u}}

open Stacks.PresheafOfModules.CoextendScalars

/-! ## The ambient sheaf of all (not necessarily linear) morphisms. -/

/-- The presheaf of types `X ↦ Hom_{Ab}(O'|_X, F|_X)`, i.e. `presheafHom` applied to the
underlying `Ab`-presheaves of `O'asOModule φ` and `F`. This is the ambient presheaf inside
which the `O`-linear morphisms (the sections of `coextObj`) sit as a subfunctor. -/
noncomputable def allHoms (φ : O ⟶ O') (F : PresheafOfModules.{u} O.obj) : Cᵒᵖ ⥤ Type u :=
  presheafHom (O'asOModule φ.hom).presheaf F.presheaf

/-- `allHoms` is a sheaf of types whenever its target `F` underlies a sheaf of modules. -/
theorem allHoms_isSheaf (φ : O ⟶ O') {F : PresheafOfModules.{u} O.obj}
    (hF : Presheaf.IsSheaf J F.presheaf) :
    Presieve.IsSheaf J (allHoms φ F) := by
  rw [← isSheaf_iff_isSheaf_of_type]
  exact Presheaf.IsSheaf.hom _ _ hF

/-! ## The `O`-linear subfunctor of `allHoms`. -/

/-- The components of a section of `allHoms φ F` as honest functions between the module
carriers, obtained from the presheaf-level `Hom` of underlying `Ab`-presheaves by unfolding the
definitional equality between the underlying type of `M.presheaf.obj X` and of `M.obj X`. -/
noncomputable def allHomsEval {φ : O ⟶ O'} {F : PresheafOfModules.{u} O.obj} {X : Cᵒᵖ}
    (η : (allHoms φ F).obj X) (W : (Over X.unop)ᵒᵖ) :
    (O'asOModule φ.hom).obj (Opposite.op W.unop.left) → F.obj (Opposite.op W.unop.left) :=
  η.app W

/-- A section `η` of `allHoms φ F` over `X` is `O`-linear if each of its components, indexed by
the slice category `(Over X.unop)ᵒᵖ`, is linear for the `O`-module structures on `O'asOModule φ`
and `F`. These are exactly the sections corresponding to morphisms `coextSec φ.hom F X`. -/
def IsLin (φ : O ⟶ O') (F : PresheafOfModules.{u} O.obj) (X : Cᵒᵖ)
    (η : (allHoms φ F).obj X) : Prop :=
  ∀ (W : (Over X.unop)ᵒᵖ) (r : O.obj.obj (Opposite.op W.unop.left))
    (m : (O'asOModule φ.hom).obj (Opposite.op W.unop.left)),
    allHomsEval η W (r • m) = r • allHomsEval η W m

/-- The subfunctor of `allHoms φ F` cut out by `IsLin`. Its restriction-stability (the `map`
field) needs no more than `O`-linearity being preserved under reindexing along `Over.map`, since
that functor does not change the underlying object of the slice category. -/
noncomputable def linSub (φ : O ⟶ O') (F : PresheafOfModules.{u} O.obj) :
    Subfunctor (allHoms φ F) where
  obj X := {η | IsLin φ F X η}
  map {_X _Y} i _η hη W r m := hη ((Over.map i.unop).op.obj W) r m

/-! ## The object-level bijection `coextSec φ.hom F X ≃ (linSub φ F).toFunctor.obj X`. -/

/-- A morphism `coextSec φ.hom F X` (i.e. `restrictToOver X.unop (O'asOModule φ.hom) ⟶
restrictToOver X.unop F`) gives, via its underlying `Ab`-presheaf morphism, a section of
`allHoms φ F` over `X`; this section is `O`-linear since each component of the original
morphism is a morphism of modules. -/
noncomputable def coextSecEquiv (φ : O ⟶ O') (F : PresheafOfModules.{u} O.obj) (X : Cᵒᵖ) :
    coextSec φ.hom F X ≃ (linSub φ F).toFunctor.obj X where
  toFun ψ := ⟨(PresheafOfModules.toPresheaf _).map ψ, fun W r m => (ψ.app W).hom.map_smul r m⟩
  invFun η := PresheafOfModules.homMk η.1 η.2
  left_inv ψ := by
    apply PresheafOfModules.hom_ext
    intro W
    rfl
  right_inv η := by
    apply Subtype.ext
    apply NatTrans.ext
    funext W
    rfl

/-! ## Naturality of `coextSecEquiv` with respect to restriction. -/

private alias mcHomHEq := Stacks.PresheafOfModules.CoextendScalars.mc_hom_heq

private alias hfunCongrHEq := Stacks.PresheafOfModules.CoextendScalars.hfun_congr_heq

private theorem eqToHomAppCast {Y : Cᵒᵖ}
    {M N : PresheafOfModules.{u} ((Over.forget Y.unop).op ⋙ O.obj)}
    (h : M = N) (V : (Over Y.unop)ᵒᵖ) :
    (eqToHom h).app V = eqToHom (congrArg (fun P => P.obj V) h) := by
  subst h; rfl

/-- The pointwise formula for the restriction map `coextRestrFun`: its `V`-component is,
up to the coherence identification `overRestrict_objEq`, simply `ψ` evaluated at the
reindexed object `(Over.map f.unop).op.obj V`. -/
theorem coextRestrFun_app (φ : O ⟶ O') (F : PresheafOfModules.{u} O.obj) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) (ψ : coextSec φ.hom F X) (V : (Over Y.unop)ᵒᵖ) :
    HEq ((coextRestrFun φ.hom F f ψ).app V) (ψ.app ((Over.map f.unop).op.obj V)) := by
  simp only [coextRestrFun, overRestrictIso, eqToIso.inv, eqToIso.hom,
    PresheafOfModules.comp_app, eqToHomAppCast, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  refine mcHomHEq (congrArg (fun M => M.obj V)
    (overRestrict_objEq Y.unop X.unop f.unop (O'asOModule φ.hom)))
    (congrArg (fun M => M.obj V) (overRestrict_objEq Y.unop X.unop f.unop F))
      _ _ (fun z => ?_)
  refine hfunCongrHEq (congrArg (fun (M : ModuleCat (O.obj.obj _)) => (M : Type u))
    (congrArg (fun M => M.obj V) (overRestrict_objEq Y.unop X.unop f.unop F))) ?_
    (eqRec_heq _ z).symm
  unfold overRestrictFunctor
  simp only [PresheafOfModules.pushforward]
  rw [show (baseRingIso Y.unop X.unop f.unop).inv = 𝟙 ((Over.forget Y.unop).op ⋙ O.obj) from by
    ext W; simp [baseRingIso, Over.mapForget]]
  simp only [Functor.comp_obj, Functor.comp_map, PresheafOfModules.restrictScalars_map_app]
  rfl

/-! ## Naturality of `coextSecEquiv`: assembling into an isomorphism of presheaves of types. -/

private theorem coextMap_apply_eq (φ : O ⟶ O') (F : PresheafOfModules.{u} O.obj) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) (ψ : coextSec φ.hom F X) :
    (coextObj φ.hom F).map f ψ = coextRestrFun φ.hom F f ψ := by
  show (ModuleCat.semilinearMapAddEquiv (RingCat.Hom.hom (O'.obj.map f)) _ _
    (coextRestrSemilinear φ.hom F f)) ψ = _
  rw [ModuleCat.semilinearMapAddEquiv_apply]
  rfl

/-- `coextSecEquiv`, bundled across all `X`, is a natural isomorphism between the underlying
type-valued presheaf of `coextObj φ.hom F` and the `O`-linear subfunctor `linSub φ F`. -/
noncomputable def coextIsoLinSub (φ : O ⟶ O') (F : PresheafOfModules.{u} O.obj) :
    (coextObj φ.hom F).presheaf ⋙ CategoryTheory.forget AddCommGrpCat ≅ (linSub φ F).toFunctor :=
  NatIso.ofComponents (fun X => Equiv.toIso (coextSecEquiv φ F X)) (by
    intro X Y f
    ext ψ
    change (((coextObj φ.hom F).presheaf ⋙ CategoryTheory.forget AddCommGrpCat).map f ≫
        (coextSecEquiv φ F Y).toIso.hom) ψ =
      ((coextSecEquiv φ F X).toIso.hom ≫ (linSub φ F).toFunctor.map f) ψ
    have e1 : (((coextObj φ.hom F).presheaf ⋙ CategoryTheory.forget AddCommGrpCat).map f ≫
        (coextSecEquiv φ F Y).toIso.hom) ψ =
        coextSecEquiv φ F Y
          (((coextObj φ.hom F).presheaf ⋙ CategoryTheory.forget AddCommGrpCat).map f ψ) :=
      (types_comp_apply _ _ ψ).trans (Equiv.toIso_hom_hom_apply _ _)
    have e2 : (((coextObj φ.hom F).presheaf ⋙ CategoryTheory.forget AddCommGrpCat).map f ψ) =
        coextRestrFun φ.hom F f ψ :=
      (PresheafOfModules.presheaf_map_apply_coe _ f ψ).trans (coextMap_apply_eq φ F f ψ)
    have e4 : ((coextSecEquiv φ F X).toIso.hom ≫ (linSub φ F).toFunctor.map f) ψ =
        (linSub φ F).toFunctor.map f (coextSecEquiv φ F X ψ) :=
      (types_comp_apply _ _ ψ).trans (congrArg ((linSub φ F).toFunctor.map f)
        (Equiv.toIso_hom_hom_apply _ _))
    rw [e1, e2, e4]
    apply Subtype.ext
    apply NatTrans.ext
    funext W
    apply ConcreteCategory.hom_ext
    intro w
    change (ConcreteCategory.hom ((coextRestrFun φ.hom F f ψ).app W)) w =
      (ConcreteCategory.hom (ψ.app ((Over.map f.unop).op.obj W))) w
    exact DFunLike.congr_fun (congrArg ConcreteCategory.hom
      (eq_of_heq (coextRestrFun_app φ F f ψ W))) w)

/-! ## `IsLin` is local: the sheaf condition for `linSub`. -/

/-- `IsLin` is a local condition: a section of `allHoms` that is `O`-linear after restriction
along every arrow of a covering sieve is already `O`-linear. The argument restricts further
along an arbitrary arrow `p` of (the pullback to `W.unop.left` of) that covering sieve, uses
the hypothesis there together with naturality of `s` and `PresheafOfModules.map_smul` (for both
the ambient and the target module presheaves) to show the two sides of the goal agree after
restriction along `p`, and concludes by separatedness of the target sheaf. -/
theorem linSub_isSheaf (φ : O ⟶ O') (F : SheafOfModules.{u} O) :
    Presieve.IsSheaf J (linSub φ F.val).toFunctor := by
  rw [(linSub φ F.val).isSheaf_iff (allHoms_isSheaf φ F.isSheaf)]
  intro U s hs W r m
  have hcov : Sieve.pullback W.unop.hom ((linSub φ F.val).sieveOfSection s) ∈ J W.unop.left :=
    J.pullback_stable W.unop.hom hs
  have hsep : Presheaf.IsSeparated J F.val.presheaf := Presheaf.IsSheaf.isSeparated F.isSheaf
  refine hsep W.unop.left _ hcov (allHomsEval s W (r • m)) (r • allHomsEval s W m) ?_
  intro Y p hp
  have hlin : IsLin φ F.val (Opposite.op Y)
      ((allHoms φ F.val).map (p ≫ W.unop.hom).op s) := hp
  have etop : ∀ x : (O'asOModule φ.hom).obj (Opposite.op Y),
      allHomsEval ((allHoms φ F.val).map (p ≫ W.unop.hom).op s)
        (Opposite.op (Over.mk (𝟙 Y))) x =
        allHomsEval s (Opposite.op (Over.mk (p ≫ W.unop.hom))) x := fun x =>
    DFunLike.congr_fun
      (congrArg ConcreteCategory.hom (presheafHom_map_app_op_mk_id (p ≫ W.unop.hom) s)) x
  have enat : ∀ x : (O'asOModule φ.hom).obj (Opposite.op W.unop.left),
      allHomsEval s (Opposite.op (Over.mk (p ≫ W.unop.hom)))
          ((O'asOModule φ.hom).restrictₛₗ p.op x) =
        F.val.restrictₛₗ p.op (allHomsEval s W x) := fun x =>
    DFunLike.congr_fun
      (congrArg ConcreteCategory.hom
        (s.naturality
          (Over.homMk p (by rfl) : Over.mk (p ≫ W.unop.hom) ⟶ Over.mk W.unop.hom).op))
      x
  have key : allHomsEval s (Opposite.op (Over.mk (p ≫ W.unop.hom)))
        (O.obj.map p.op r • (O'asOModule φ.hom).restrictₛₗ p.op m) =
      O.obj.map p.op r • allHomsEval s (Opposite.op (Over.mk (p ≫ W.unop.hom)))
        ((O'asOModule φ.hom).restrictₛₗ p.op m) := by
    rw [← etop, hlin (Opposite.op (Over.mk (𝟙 Y))) (O.obj.map p.op r), etop]
  have hsmul : ∀ (M : PresheafOfModules.{u} O.obj) (x : M.obj (Opposite.op W.unop.left)),
      M.restrictₛₗ p.op (r • x) = O.obj.map p.op r • M.restrictₛₗ p.op x := fun M x => by
    simp only [PresheafOfModules.restrictₛₗ_apply]
    exact PresheafOfModules.map_smul (M := M) p.op r x
  show F.val.restrictₛₗ p.op (allHomsEval s W (r • m)) =
    F.val.restrictₛₗ p.op (r • allHomsEval s W m)
  rw [← enat, hsmul (O'asOModule φ.hom), key, enat, ← hsmul F.val]

/-! ## The sheaf condition for the internal-hom presheaf of modules. -/

/-- The underlying presheaf of modules `coextObj φ.hom F.val` of the (to-be-constructed)
sheaf-level `coextendScalars φ F` is itself a sheaf, for `F : SheafOfModules O`. This transports
`linSub_isSheaf` across the isomorphism `coextIsoLinSub` (between the underlying type-valued
presheaf of `coextObj φ.hom F.val` and `(linSub φ F.val).toFunctor`) and across the generic
comparison, for a concrete category such as `AddCommGrpCat`, between being a sheaf and having a
sheaf of underlying types. -/
theorem coextendScalars_isSheaf (φ : O ⟶ O') (F : SheafOfModules.{u} O) :
    Presheaf.IsSheaf J (coextObj φ.hom F.val).presheaf := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (s := CategoryTheory.forget AddCommGrpCat.{u}),
    Presheaf.isSheaf_of_iso_iff (coextIsoLinSub φ F.val), isSheaf_iff_isSheaf_of_type]
  exact linSub_isSheaf φ F

/-! ## Main Definition 2, sheaf level: the coextension-of-scalars functor. -/

/-- **Main Definition 2, sheaf level.** The sheaf-level coextension-of-scalars functor
`φ_*^coext : Mod(O) ⥤ Mod(O')`, agreeing with the presheaf-level
`Stacks.PresheafOfModules.CoextendScalars.coextendScalars` on underlying presheaves of
modules, the sole new content being the sheaf condition `coextendScalars_isSheaf`. -/
noncomputable def coextendScalars (φ : O ⟶ O') :
    SheafOfModules.{u} O ⥤ SheafOfModules.{u} O' where
  obj F := { val := coextObj φ.hom F.val, isSheaf := coextendScalars_isSheaf φ F }
  map {_ _} η := { val := coextFunMap φ.hom η.val }
  map_id F := by
    apply SheafOfModules.hom_ext
    exact coextFunMap_id φ.hom F.val
  map_comp η θ := by
    apply SheafOfModules.hom_ext
    exact coextFunMap_comp φ.hom η.val θ.val

/-! ## The sheaf-level Hom-bijection and the adjunction. -/

/-- The sheaf-level Hom-bijection, obtained from the presheaf-level `homEquiv` by transporting
across the fully faithful forgetful functors `SheafOfModules.forget O` and
`SheafOfModules.forget O'` (the underlying-presheaf-of-modules components of
`(SheafOfModules.restrictScalars φ).obj G` and `(coextendScalars φ).obj F` agree, by
construction, with the presheaf-level `(PresheafOfModules.restrictScalars φ.hom).obj G.val`
and `coextObj φ.hom F.val`). -/
noncomputable def coextendScalarsSheafHomEquiv (φ : O ⟶ O') (G : SheafOfModules.{u} O')
    (F : SheafOfModules.{u} O) :
    ((SheafOfModules.restrictScalars φ).obj G ⟶ F) ≃ (G ⟶ (coextendScalars φ).obj F) where
  toFun β := ⟨homEquiv φ.hom G.val F.val β.val⟩
  invFun α := ⟨(homEquiv φ.hom G.val F.val).symm α.val⟩
  left_inv β := SheafOfModules.hom_ext ((homEquiv φ.hom G.val F.val).left_inv β.val)
  right_inv α := SheafOfModules.hom_ext ((homEquiv φ.hom G.val F.val).right_inv α.val)

/-- Naturality of `coextendScalarsSheafHomEquiv.symm` with respect to precomposition, transported
from the presheaf-level `homEquiv_naturality_left_symm` via `.val`. -/
theorem sheafHomEquiv_naturality_left_symm (φ : O ⟶ O') {G' G : SheafOfModules.{u} O'}
    {F : SheafOfModules.{u} O} (γ : G' ⟶ G) (β : G ⟶ (coextendScalars φ).obj F) :
    (coextendScalarsSheafHomEquiv φ G' F).symm (γ ≫ β) =
      (SheafOfModules.restrictScalars φ).map γ ≫ (coextendScalarsSheafHomEquiv φ G F).symm β := by
  apply SheafOfModules.hom_ext
  exact homEquiv_naturality_left_symm φ.hom γ.val β.val

/-- Naturality of `coextendScalarsSheafHomEquiv` with respect to postcomposition, transported
from the presheaf-level `homEquiv_naturality_right` via `.val`. -/
theorem sheafHomEquiv_naturality_right (φ : O ⟶ O') {G : SheafOfModules.{u} O'}
    {F F' : SheafOfModules.{u} O} (α : (SheafOfModules.restrictScalars φ).obj G ⟶ F)
    (η : F ⟶ F') :
    coextendScalarsSheafHomEquiv φ G F' (α ≫ η) =
      coextendScalarsSheafHomEquiv φ G F α ≫ (coextendScalars φ).map η := by
  apply SheafOfModules.hom_ext
  exact homEquiv_naturality_right φ.hom α.val η.val

/-- **Stacks Tag 0932 / Lemma 18.27.8, sheaf level.** The adjunction
`SheafOfModules.restrictScalars φ ⊣ coextendScalars φ`: restriction of scalars along a
morphism of sheaves of rings `φ` is left adjoint to the sheaf-level coextension-of-scalars
functor `coextendScalars φ`, transported from the presheaf-level adjunction
`Stacks.PresheafOfModules.CoextendScalars.restrictScalars_coextendScalars_adjunction` via the
sheaf-level Hom-bijection `coextendScalarsSheafHomEquiv` and its naturality lemmas, using
`Adjunction.mkOfHomEquiv`. -/
noncomputable def restrictScalars_coextendScalars_adjunction (φ : O ⟶ O') :
    SheafOfModules.restrictScalars.{u} φ ⊣ coextendScalars φ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G F => coextendScalarsSheafHomEquiv φ G F
      homEquiv_naturality_left_symm := fun γ β => sheafHomEquiv_naturality_left_symm φ γ β
      homEquiv_naturality_right := fun α η => sheafHomEquiv_naturality_right φ α η }

end Stacks.SheafOfModules.CoextendScalars
