module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.Hom
public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.CategoryTheory.Limits.Types.Coequalizers
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ExtensionByInitial
public import StacksFrontier.Topology.Sheaves.Sheaf.Constant
public import StacksFrontier.Topology.Spectral.AsDirectedInverseLimit
public import StacksFrontier.Topology.Spectral.InverseLimits
public import StacksFrontier.Topology.Sheaves.Limits.PullbackSections
public import StacksFrontier.Topology.Sheaves.Stalk.Constant
public import StacksFrontier.Topology.Sheaves.Skyscraper.Adjunction
public import StacksFrontier.Topology.Sheaves.Functors.Pullback.SheafStalk
public import StacksFrontier.Topology.Sheaves.Limits.GermPullbackComparison
public import StacksFrontier.Topology.Sheaves.Functors.Pullback.Comp

/-!
# Descending a finitely presented sheaf of sets to a finite sober space

Let `X` be a spectral topological space and let `F` be a sheaf of sets on `X` which is the
coequalizer of two maps between finite coproducts of finite constant sheaves extended from
quasi-compact opens of `X`. This file proves that `F` is the pullback of a sheaf with finite
stalks along a spectral map from `X` to a finite sober space.

The argument writes `X` as a directed inverse limit of finite sober spaces (Stacks 09XX,
`spectralSpace_iff_isDirectedInverseLimitOfFiniteSober`), descends the finitely many
quasi-compact opens carrying the presentation to a single stage `E.obj j` of that limit, and
transports the presentation along the projection: pullback preserves finite coproducts and
coequalizers, and it takes a constant sheaf extended from an open to the constant sheaf
extended from the preimage of that open, so the presentation itself descends.

## Main definitions

* `Stacks.extendedConstantSheaf U S`: the sheaf of sets on `X` obtained by extending by the
  initial object the constant sheaf with value `S` on the open subspace `U`.
* `Stacks.HasFiniteBasisCoequalizerPresentation B F`: `F` is isomorphic to the coequalizer of
  two maps between finite coproducts of sheaves `extendedConstantSheaf (U a) (S a)` with each
  `U a` in `B` and each `S a` finite.

## Main results

* `Stacks.exists_pullback_from_finite_sober_of_hasFiniteBasisCoequalizerPresentation`
  (Stacks 0CAK): a sheaf of sets on a spectral space with a finite coequalizer presentation
  over the quasi-compact opens is pulled back, along a spectral map, from a sheaf with finite
  stalks on a finite sober space.

## Implementation notes

The whole statement is single-universe: the space, the sheaf values and the index type of the
inverse limit all live in `Type u`. This is forced rather than chosen — the finite sober space
produced by `spectralSpace_iff_isDirectedInverseLimitOfFiniteSober` is a value of a diagram
indexed in the universe of `X`, so it is a `Type u`, and the sheaf of sets on it must then take
values in `Type u` for the pullback comparison to typecheck.

Soberness of the target is recorded by the `QuasiSober` and `T0Space` instances rather than by
a `SoberSpace` predicate, matching `IsDirectedInverseLimitOfFiniteSober`. The spectral map is
produced as a morphism of `TopCat` together with `IsSpectralMap`, so that it can be fed
directly to `TopCat.Sheaf.pullback`.

Two models of the set-valued sheaf pullback are compared in the first section: the left adjoint
`TopCat.Sheaf.pullback` and the explicit germ model `GermPullback`. The comparison is done at
the level of the adjunction unit, which is what makes the descent of sections computable; the
long run of private lemmas there is bookkeeping for that single comparison.

## References

* [Stacks Project, Tag 0CAK](https://stacks.math.columbia.edu/tag/0CAK)
* [Stacks Project, Tag 0CAI](https://stacks.math.columbia.edu/tag/0CAI)
* [Stacks Project, Tag 09XX](https://stacks.math.columbia.edu/tag/09XX)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite

namespace Stacks

open Stacks.GermPullbackComparison

section Presentation

variable {X : Type u} [TopologicalSpace X]

/-- The sheaf of sets on `X` obtained by extending by the initial object the constant sheaf
with value `S` on the open subspace `U` of `X`. -/
noncomputable abbrev extendedConstantSheaf (U : Opens X) (S : Type u) :
    TopCat.Sheaf (Type u) (TopCat.of X) :=
  (TopCat.Presheaf.extendByInitialSheaf (X := TopCat.of X) (C := Type u) U).obj
    (constantSheafOnSpace
      (TopCat.Presheaf.ExtensionByInitial.sp (X := TopCat.of X) U) (Type u) S)

/-- A sheaf has a finite basis coequalizer presentation if it is isomorphic to the coequalizer
of two maps between finite coproducts of extensions of finite constant sheaves from opens in
the specified basis. -/
def HasFiniteBasisCoequalizerPresentation (B : Set (Opens X))
    (G : TopCat.Sheaf (Type u) (TopCat.of X)) : Prop :=
  letI : HasFiniteColimits (TopCat.Sheaf (Type u) (TopCat.of X)) :=
    CategoryTheory.Sheaf.instHasFiniteColimits
  ∃ (n m : ℕ) (U : Fin n → Opens X) (V : Fin m → Opens X)
      (S : Fin n → Type u) (T : Fin m → Type u),
      (∀ a, U a ∈ B) ∧ (∀ b, V b ∈ B) ∧
        (∀ a, Finite (S a)) ∧ (∀ b, Finite (T b)) ∧
        ∃ (f g : (∐ fun b ↦ extendedConstantSheaf (V b) (T b)) ⟶
            (∐ fun a ↦ extendedConstantSheaf (U a) (S a))),
          Nonempty (coequalizer f g ≅ G)

end Presentation

/-! ### Comparison of the two pullback sheaf models -/

private lemma germPullback_eval_cast {Y Z : TopCat.{u}} (g : Z → Y)
    (F : Y.Presheaf (Type u)) {W W' : Opens Z} (h : W = W')
    (σ : (GermPullback.sheaf g F).presheaf.obj (op W)) (z : W') :
    germPullback_eval g F
      (cast (congrArg (fun U : Opens Z =>
        (GermPullback.sheaf g F).presheaf.obj (op U)) h) σ) z =
      germPullback_eval g F σ ⟨z.1, h.symm ▸ z.2⟩ := by
  cases h
  rfl

private lemma subst_trans_cast {α : Type u} {P : α → Type u}
    {a b c : α} (h : a = b) (h' : b = c) (x : P a) :
    (h.trans h') ▸ x = cast (congrArg P h') (h ▸ x) := by
  cases h
  cases h'
  rfl

private lemma germPullback_eval_comap {Y Z Z' : TopCat.{u}}
    (g : Z → Y) (g' : Z' → Y) (h : Z' → Z) (hh : Continuous h)
    (hc : ∀ z, g' z = g (h z)) (F : Y.Presheaf (Type u))
    {W : Opens Z} {W' : Opens Z'} (hW : ∀ z : W', h z.1 ∈ W)
    (σ : (GermPullback.sheaf g F).presheaf.obj (op W)) (z : W') :
    germPullback_eval g' F (GermPullback.comap hh hc hW σ) z =
      cast (congrArg F.stalk (hc z.1).symm)
        (germPullback_eval g F σ ⟨h z.1, hW z⟩) := by
  let v := σ.1 ⟨h z.1, hW z⟩
  let p : v.1 = g (h z.1) := germPullback_first g F σ ⟨h z.1, hW z⟩
  let q : v.1 = g' z.1 :=
    germPullback_first g' F (GermPullback.comap hh hc hW σ) z
  have hpq : q = p.trans (hc z.1).symm := Subsingleton.elim _ _
  unfold germPullback_eval
  simp only [GermPullback.comap_val]
  show (q ▸ v.2) = cast (congrArg F.stalk (hc z.1).symm) (p ▸ v.2)
  rw [hpq]
  exact subst_trans_cast p (hc z.1).symm v.2

private lemma presheaf_germ_cast {Z : TopCat.{u}} (F : Z.Presheaf (Type u))
    {W W' : Opens Z} (h : W = W') (s : F.obj (op W))
    (z : Z) (hz : z ∈ W') :
    F.germ W' z hz
      (cast (congrArg (fun U : Opens Z => F.obj (op U)) h) s) =
    F.germ W z (h.symm ▸ hz) s := by
  cases h
  rfl

private lemma pullbackToGerm_eval {Y Z : TopCat.{u}} (g : Z ⟶ Y)
    (F : Y.Sheaf (Type u)) {W : Opens Z}
    (σ : ((TopCat.Sheaf.pullback (Type u) g).obj F).presheaf.obj (op W)) (z : W) :
    germPullback_eval (ConcreteCategory.hom g) F.presheaf
      ((pullbackToGerm g F).hom.app (op W) σ) z =
    (stalkPullbackSheafIso g F z.1).hom
      (((TopCat.Sheaf.pullback (Type u) g).obj F).presheaf.germ W z.1 z.2 σ) := by
  calc
    _ = germPullback_stalkEval (ConcreteCategory.hom g) F.presheaf z.1
          ((GermPullback.sheaf (ConcreteCategory.hom g) F.presheaf).presheaf.germ
            W z.1 z.2 ((pullbackToGerm g F).hom.app (op W) σ)) :=
      (germPullback_stalkEval_germ (ConcreteCategory.hom g) F.presheaf
        z.1 z.2 _).symm
    _ = germPullback_stalkEval (ConcreteCategory.hom g) F.presheaf z.1
          ((TopCat.Presheaf.stalkFunctor (Type u) z.1).map (pullbackToGerm g F).hom
            (((TopCat.Sheaf.pullback (Type u) g).obj F).presheaf.germ W z.1 z.2 σ)) := by
      rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    _ = _ := pullbackToGerm_stalkEval g F z.1 _

private lemma stalkPullbackSheafIso_unit {Y Z : TopCat.{u}} (g : Z ⟶ Y)
    (F : Y.Sheaf (Type u)) (z : Z) (V : Opens Y) (hz : g z ∈ V)
    (s : F.presheaf.obj (op V)) :
    (stalkPullbackSheafIso g F z).hom
      (((TopCat.Sheaf.pullback (Type u) g).obj F).presheaf.germ
        ((Opens.map g).obj V) z hz
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app F).hom.app
          (op V) s)) = F.presheaf.germ V (g z) hz s := by
  rw [← stalkPullbackSheafIso_inv_germ g F z V hz s]
  exact (stalkPullbackSheafIso g F z).inv_hom_id_apply _

private lemma sheafPullbackCompIso_unit {A B C : TopCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (F : C.Sheaf (Type u)) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f ≫ g)).unit.app F ≫
      (TopCat.Sheaf.pushforward (Type u) (f ≫ g)).map
        ((sheafPullbackCompIso f g (Type u)).hom.app F) =
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app F ≫
      (TopCat.Sheaf.pushforward (Type u) g).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
          ((TopCat.Sheaf.pullback (Type u) g).obj F)) := by
  let a := TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f ≫ g)
  let b := (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f)
  have h := a.unit_leftAdjointUniq_hom_app
    (b.ofNatIsoRight (sheafPushforwardCompIso f g (Type u)).symm) F
  have hiso : (sheafPushforwardCompIso f g (Type u)).symm.hom = 𝟙 _ := rfl
  rw [Adjunction.ofNatIsoRight_unit] at h
  simp only [NatTrans.comp_app, hiso] at h
  exact h

private lemma sheafPullbackCompIso_unit_apply {A B C : TopCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (F : C.Sheaf (Type u))
    (V : Opens C) (s : F.presheaf.obj (op V)) :
    (((sheafPullbackCompIso f g (Type u)).app F).hom).hom.app
      (op ((Opens.map (f ≫ g)).obj V))
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f ≫ g)).unit.app F).hom.app
          (op V) s) =
    (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
      ((TopCat.Sheaf.pullback (Type u) g).obj F)).hom.app
        (op ((Opens.map g).obj V)))
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app F).hom.app
            (op V) s) :=
  congrArg (fun m : F ⟶
      (TopCat.Sheaf.pushforward (Type u) (f ≫ g)).obj
        ((TopCat.Sheaf.pullback (Type u) g ⋙ TopCat.Sheaf.pullback (Type u) f).obj F) =>
      m.hom.app (op V) s) (sheafPullbackCompIso_unit f g F)

/-- Applying an isomorphism of sheaves and then its inverse is the identity on sections. -/
private lemma sheaf_iso_hom_inv_apply {A : TopCat.{u}} {P Q : A.Sheaf (Type u)} (i : P ≅ Q)
    (W : Opens A) (x : P.presheaf.obj (op W)) :
    i.inv.hom.app (op W) (i.hom.hom.app (op W) x) = x :=
  congrArg (fun m : P ⟶ P => m.hom.app (op W) x) i.hom_inv_id

/-- A morphism of sheaves that is an isomorphism is injective on sections. -/
private lemma injective_app_of_isIso {A : TopCat.{u}} {P Q : A.Sheaf (Type u)} (m : P ⟶ Q)
    [IsIso m] (W : Opens A) : Function.Injective (m.hom.app (op W)) := by
  have : IsIso m.hom := by
    change IsIso ((TopCat.Sheaf.forget (Type u) A).map m)
    infer_instance
  exact ((isIso_iff_bijective _).mp inferInstance).1

private lemma sheafPullbackCompIso_inv_unit_apply {A B C : TopCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (F : C.Sheaf (Type u))
    (V : Opens C) (s : F.presheaf.obj (op V)) :
    (((sheafPullbackCompIso f g (Type u)).app F).inv).hom.app
      (op ((Opens.map f).obj ((Opens.map g).obj V)))
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
          ((TopCat.Sheaf.pullback (Type u) g).obj F)).hom.app
            (op ((Opens.map g).obj V))
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app F).hom.app
            (op V) s)) =
    (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f ≫ g)).unit.app F).hom.app
      (op V) s) := by
  let i := (sheafPullbackCompIso f g (Type u)).app F
  have hi := sheaf_iso_hom_inv_apply i ((Opens.map (f ≫ g)).obj V)
    (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f ≫ g)).unit.app F).hom.app
      (op V) s)
  rwa [sheafPullbackCompIso_unit_apply f g F V s] at hi

private lemma pullback_unit_naturality_apply {A B : TopCat.{u}} (f : A ⟶ B)
    {F G : B.Sheaf (Type u)} (m : F ⟶ G)
    (V : Opens B) (s : F.presheaf.obj (op V)) :
    ((TopCat.Sheaf.pullback (Type u) f).map m).hom.app
      (op ((Opens.map f).obj V))
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app F).hom.app
          (op V) s) =
    (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app G).hom.app
      (op V)) (m.hom.app (op V) s) :=
  (congrArg (fun k : F ⟶
      (TopCat.Sheaf.pushforward (Type u) f).obj
        ((TopCat.Sheaf.pullback (Type u) f).obj G) =>
      k.hom.app (op V) s)
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.naturality m)).symm

private lemma stalkPullbackSheafIso_eq_germ {A B : TopCat.{u}}
    {f g : A ⟶ B} (h : f = g) (F : B.Sheaf (Type u))
    (W : Opens A) (x : A) (hx : x ∈ W)
    (s : ((TopCat.Sheaf.pullback (Type u) f).obj F).presheaf.obj (op W)) :
    (stalkPullbackSheafIso g F x).hom
      (((TopCat.Sheaf.pullback (Type u) g).obj F).presheaf.germ W x hx
        ((eqToIso (congrArg
          (fun k : A ⟶ B => (TopCat.Sheaf.pullback (Type u) k).obj F) h)).hom.hom.app
          (op W) s)) =
    cast (congrArg (fun k : A ⟶ B => F.presheaf.stalk (k x)) h)
      ((stalkPullbackSheafIso f F x).hom
        (((TopCat.Sheaf.pullback (Type u) f).obj F).presheaf.germ W x hx s)) := by
  cases h
  rfl

private lemma stalkPullbackSheafIso_comp {A B C : TopCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (F : C.Sheaf (Type u)) (x : A)
    (a : ((TopCat.Sheaf.pullback (Type u) f).obj
      ((TopCat.Sheaf.pullback (Type u) g).obj F)).presheaf.stalk x) :
    (stalkPullbackSheafIso (f ≫ g) F x).hom
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map
        (((sheafPullbackCompIso f g (Type u)).app F).inv).hom a) =
    (stalkPullbackSheafIso g F (f x)).hom
      ((stalkPullbackSheafIso f ((TopCat.Sheaf.pullback (Type u) g).obj F) x).hom a) := by
  let ef := stalkPullbackSheafIso f ((TopCat.Sheaf.pullback (Type u) g).obj F) x
  let eg := stalkPullbackSheafIso g F (f x)
  let eh := stalkPullbackSheafIso (f ≫ g) F x
  let c := (TopCat.Presheaf.stalkFunctor (Type u) x).map
    (((sheafPullbackCompIso f g (Type u)).app F).inv).hom
  suffices hh : ∀ ζ : F.presheaf.stalk (g (f x)),
      eh.hom (c (ef.inv (eg.inv ζ))) = ζ by
    simpa only [eg.hom_inv_id_apply, ef.hom_inv_id_apply] using hh (eg.hom (ef.hom a))
  intro ζ
  obtain ⟨V, hz, s, hs⟩ := F.presheaf.exists_germ_eq ζ
  rw [← hs]
  let Q := (TopCat.Sheaf.pullback (Type u) g).obj F
  let W := (Opens.map g).obj V
  let s₁ := (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app F).hom.app
    (op V)) s
  have h₁ : eg.inv (F.presheaf.germ V (g (f x)) hz s) =
      Q.presheaf.germ W (f x) hz s₁ :=
    stalkPullbackSheafIso_inv_germ g F (f x) V hz s
  rw [h₁]
  have h₂ : ef.inv (Q.presheaf.germ W (f x) hz s₁) =
      ((TopCat.Sheaf.pullback (Type u) f).obj Q).presheaf.germ
        ((Opens.map f).obj W) x hz
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app Q).hom.app
          (op W) s₁) :=
    stalkPullbackSheafIso_inv_germ f Q x W hz s₁
  rw [h₂]
  have hm := TopCat.Presheaf.stalkFunctor_map_germ_apply
    ((Opens.map f).obj W) x hz
    (((sheafPullbackCompIso f g (Type u)).app F).inv).hom
    ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app Q).hom.app
      (op W)) s₁)
  calc
    _ = eh.hom
      (((TopCat.Sheaf.pullback (Type u) (f ≫ g)).obj F).presheaf.germ
        ((Opens.map f).obj W) x hz
        ((((sheafPullbackCompIso f g (Type u)).app F).inv).hom.app
          (op ((Opens.map f).obj W))
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app Q).hom.app
            (op W)) s₁))) := congrArg eh.hom hm
    _ = _ := by
      rw [sheafPullbackCompIso_inv_unit_apply f g F V s]
      exact stalkPullbackSheafIso_unit (f ≫ g) F x V hz s


variable {X : Type u} [TopologicalSpace X] [SpectralSpace X]

/-- Pulling an open back along a transition map does not change its preimage under projections. -/
private theorem preimage_proj_comp_map {Z : Type u} {J : Type u} [SmallCategory J]
    [IsCofiltered J] (D : SpectralDiagram.{u, u} J) (r : Z → D.invLimit) {j i : J} (a : j ⟶ i)
    (W : Opens (D.F.obj i)) :
    (fun x => D.projFun j (r x)) ⁻¹' ((Opens.map (D.F.map a)).obj W : Set (D.F.obj j)) =
      (fun x => D.projFun i (r x)) ⁻¹' (W : Set (D.F.obj i)) := by
  ext x
  change D.mapFun a (D.projFun j (r x)) ∈ W ↔ D.projFun i (r x) ∈ W
  rw [← D.projFun_eq_mapFun a]

/-- A compact open of a spectral inverse limit is pulled back from one stage. -/
private theorem exists_stage_compact_open {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : SpectralDiagram.{u, u} J) (U : Opens D.invLimit)
    (hU : IsCompact (U : Set D.invLimit)) :
    ∃ (j : J) (V : Opens (D.F.obj j)),
      IsCompact (V : Set (D.F.obj j)) ∧
        (D.projFun j) ⁻¹' (V : Set (D.F.obj j)) = (U : Set D.invLimit) := by
  let : ∀ j, SpectralSpace (D.F.obj j) := D.isSpectralSpace
  obtain ⟨j, V, hVopen, hVcompact, hpre⟩ :=
    SpectralLimits.descent_of_quasiCompact_opens D.F
      (fun {_ _} a => D.isSpectralMap a) (U : Set D.invLimit) U.isOpen hU
  exact ⟨j, ⟨V, hVopen⟩, hVcompact, hpre⟩

/-- Finitely many compact opens can be descended to one common stage. -/
private theorem exists_stage_fin_compact_opens {J : Type u} [SmallCategory J]
    [IsCofiltered J] (D : SpectralDiagram.{u, u} J) (n : ℕ)
    (U : Fin n → Opens D.invLimit)
    (hU : ∀ a, IsCompact (U a : Set D.invLimit)) :
    ∃ (k : J) (V : Fin n → Opens (D.F.obj k)),
      (∀ a, IsCompact (V a : Set (D.F.obj k))) ∧
        ∀ a, (D.projFun k) ⁻¹' (V a : Set (D.F.obj k)) =
          (U a : Set D.invLimit) := by
  classical
  choose idx W hWcompact hWpre using
    (fun a => exists_stage_compact_open D (U a) (hU a))
  let objs : Finset J := Finset.univ.image idx
  let k : J := IsCofiltered.inf objs ∅
  let arrow (a : Fin n) : k ⟶ idx a :=
    IsCofiltered.infTo objs ∅ (Finset.mem_image_of_mem idx (Finset.mem_univ a))
  let V (a : Fin n) : Opens (D.F.obj k) := (Opens.map (D.F.map (arrow a))).obj (W a)
  refine ⟨k, V, fun a => (D.isSpectralMap (arrow a)).isCompact_preimage_of_isOpen
    (W a).isOpen (hWcompact a), fun a => ?_⟩
  exact (preimage_proj_comp_map D id (arrow a) (W a)).trans (hWpre a)

omit [SpectralSpace X] in
/-- The same finite descent statement after identifying the limit with `X`. -/
private theorem exists_stage_fin_compact_opens_of_homeomorph
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : SpectralDiagram.{u, u} J) (q : X ≃ₜ D.invLimit) (n : ℕ)
    (U : Fin n → Opens X) (hU : ∀ a, IsCompact (U a : Set X)) :
    ∃ (k : J) (V : Fin n → Opens (D.F.obj k)),
      (∀ a, IsCompact (V a : Set (D.F.obj k))) ∧
        ∀ a, (fun x : X => D.projFun k (q x)) ⁻¹' (V a : Set (D.F.obj k)) =
          (U a : Set X) := by
  let U' (a : Fin n) : Opens D.invLimit :=
    ⟨q '' (U a : Set X), q.isOpenMap _ (U a).isOpen⟩
  have hU' (a : Fin n) : IsCompact (U' a : Set D.invLimit) :=
    q.isCompact_image.mpr (hU a)
  obtain ⟨k, V, hV, hpre⟩ := exists_stage_fin_compact_opens D n U' hU'
  refine ⟨k, V, hV, fun a => ?_⟩
  ext x
  show D.projFun k (q x) ∈ V a ↔ x ∈ U a
  have hx : D.projFun k (q x) ∈ V a ↔ q x ∈ U' a :=
    Set.ext_iff.mp (hpre a) (q x)
  rw [hx]
  show q x ∈ q '' (U a : Set X) ↔ x ∈ U a
  exact q.injective.mem_set_image

/-- Pullback carries a coequalizer presentation to the corresponding coequalizer. -/
private noncomputable instance finiteColimitsSheaves (A : TopCat.{u}) :
    HasFiniteColimits (TopCat.Sheaf (Type u) A) :=
  CategoryTheory.Sheaf.instHasFiniteColimits

private noncomputable def pullback_coequalizer_iso {A B : TopCat.{u}} (f : A ⟶ B)
    {S T : TopCat.Sheaf (Type u) B} (β γ : S ⟶ T) :
    coequalizer ((TopCat.Sheaf.pullback (Type u) f).map β)
        ((TopCat.Sheaf.pullback (Type u) f).map γ) ≅
      (TopCat.Sheaf.pullback (Type u) f).obj (coequalizer β γ) :=
  PreservesCoequalizer.iso (TopCat.Sheaf.pullback (Type u) f) β γ

/-- Conjugate parallel pairs have isomorphic coequalizers. -/
private noncomputable def coequalizerIsoOfConjugate
    {C : Type v} [Category C] [HasCoequalizers C]
    {A B A' B' : C} (β γ : A ⟶ B) (β' γ' : A' ⟶ B')
    (eA : A ≅ A') (eB : B ≅ B')
    (hβ : eA.hom ≫ β' = β ≫ eB.hom)
    (hγ : eA.hom ≫ γ' = γ ≫ eB.hom) :
    coequalizer β γ ≅ coequalizer β' γ' := by
  let p : B ⟶ coequalizer β' γ' := eB.hom ≫ coequalizer.π β' γ'
  let q : B' ⟶ coequalizer β γ := eB.inv ≫ coequalizer.π β γ
  have hp : β ≫ p = γ ≫ p := by
    change β ≫ (eB.hom ≫ coequalizer.π β' γ') =
      γ ≫ (eB.hom ≫ coequalizer.π β' γ')
    rw [← Category.assoc, ← Category.assoc, ← hβ, ← hγ]
    simp only [Category.assoc, coequalizer.condition β' γ']
  have hq : β' ≫ q = γ' ≫ q := by
    apply (cancel_epi eA.hom).mp
    calc
      eA.hom ≫ (β' ≫ q) = β ≫ coequalizer.π β γ := by
        rw [← Category.assoc, hβ]
        simp [q, Category.assoc]
      _ = γ ≫ coequalizer.π β γ := coequalizer.condition β γ
      _ = eA.hom ≫ (γ' ≫ q) := by
        rw [← Category.assoc, hγ]
        simp [q, Category.assoc]
  refine ⟨coequalizer.desc p hp, coequalizer.desc q hq, ?_, ?_⟩ <;>
    apply coequalizer.hom_ext <;> simp [p, q]

/-- Pullback commutes with the finite coproducts in the presentation. -/
private noncomputable def pullback_coproduct_iso {A B : TopCat.{u}} (f : A ⟶ B)
    (n : ℕ) (K : Fin n → TopCat.Sheaf (Type u) B) :
    (TopCat.Sheaf.pullback (Type u) f).obj (∐ fun a => K a) ≅
      ∐ fun a => (TopCat.Sheaf.pullback (Type u) f).obj (K a) :=
  PreservesCoproduct.iso (TopCat.Sheaf.pullback (Type u) f) K

/-- Each finite constant summand extended from an open has finite stalks. -/
private theorem finite_stalk_extendedConstantSheaf (A : TopCat.{u})
    (U : Opens A) (S : Type u) [Finite S] (x : A) :
    Finite ((extendedConstantSheaf U S).presheaf.stalk x) := by
  by_cases hx : x ∈ U
  · let y : TopCat.Presheaf.ExtensionByInitial.sp (X := A) U := ⟨x, hx⟩
    let C : TopCat.Sheaf (Type u) (TopCat.Presheaf.ExtensionByInitial.sp (X := A) U) :=
      constantSheafOnSpace
      (TopCat.Presheaf.ExtensionByInitial.sp (X := A) U) (Type u) S
    have hC : Finite (C.presheaf.stalk y) := by
      let P := constantPresheafOnSpace
        (TopCat.Presheaf.ExtensionByInitial.sp (X := A) U) (Type u) S
      have hP : Finite (P.stalk y) :=
        Finite.of_surjective (alphaX _ S y) (alphaX_bijective _ S y).2
      have : Finite ((TopCat.Presheaf.stalkFunctor (Type u) y).obj P) := by
        simpa only [TopCat.Presheaf.stalkFunctor_obj] using hP
      let c := (TopCat.Presheaf.stalkFunctor (Type u) y).map
        (CategoryTheory.toSheafify
          (Opens.grothendieckTopology (TopCat.Presheaf.ExtensionByInitial.sp (X := A) U)) P)
      have : IsIso c :=
        TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso y (Type u) P
      exact Finite.of_equiv _ (asIso c).toEquiv
    let e := TopCat.Presheaf.stalkExtendByInitialSheafifyIso U C.presheaf y
    exact Finite.of_equiv _ e.toEquiv.symm
  · have he : IsEmpty ((extendedConstantSheaf U S).presheaf.stalk x) :=
      TopCat.Presheaf.isEmpty_stalk_extendByInitialSheafify U _ hx
    exact Finite.of_surjective (fun z : Empty => z.elim) (fun t => isEmptyElim t)

/-- The stalk functor on sheaves preserves colimits. -/
private theorem preservesColimits_stalk_forget (A : TopCat.{u}) (x : A) :
    PreservesColimits
      (TopCat.Sheaf.forget (Type u) A ⋙ TopCat.Presheaf.stalkFunctor (Type u) x) := by
  classical
  exact (stalkSkyscraperSheafAdjunction x).leftAdjoint_preservesColimits

/-- A finite coproduct of sheaves with finite stalks has finite stalks. -/
private theorem finite_stalk_coproduct (A : TopCat.{u}) (n : ℕ)
    (K : Fin n → TopCat.Sheaf (Type u) A)
    (hK : ∀ a (x : A), Finite ((K a).presheaf.stalk x)) (x : A) :
    Finite ((∐ fun a => K a).presheaf.stalk x) := by
  let L := TopCat.Sheaf.forget (Type u) A ⋙ TopCat.Presheaf.stalkFunctor (Type u) x
  have := preservesColimits_stalk_forget A x
  have : ∀ a, Finite (L.obj (K a)) := fun a => hK a x
  exact Finite.of_equiv (Σ a : Fin n, L.obj (K a))
    ((Types.coproductIso (fun a => L.obj (K a))).toEquiv.symm.trans
      (PreservesCoproduct.iso L K).toEquiv.symm)

/-- A coequalizer of sheaves has finite stalks if its target does. -/
private theorem finite_stalk_coequalizer (A : TopCat.{u})
    {S T : TopCat.Sheaf (Type u) A} (β γ : S ⟶ T)
    (hT : ∀ x : A, Finite (T.presheaf.stalk x)) (x : A) :
    Finite ((coequalizer β γ).presheaf.stalk x) := by
  let L := TopCat.Sheaf.forget (Type u) A ⋙ TopCat.Presheaf.stalkFunctor (Type u) x
  have := preservesColimits_stalk_forget A x
  have : Finite (L.obj T) := hT x
  have : Finite (Function.Coequalizer (L.map β) (L.map γ)) :=
    Finite.of_surjective (Function.Coequalizer.mk (L.map β) (L.map γ))
      (Function.Coequalizer.mk_surjective _ _)
  exact Finite.of_equiv (Function.Coequalizer (L.map β) (L.map γ))
    ((Types.coequalizerIso (L.map β) (L.map γ)).toEquiv.symm.trans
      (PreservesCoequalizer.iso L β γ).toEquiv)

/-- Finitely many elements of a filtered colimit admit representatives at one stage. -/
private theorem finite_family_factors_through_filtered_colimit
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ Type u) (S : Type u) [Finite S] (φ : S → colimit D) :
    ∃ (j : J) (ψ : S → D.obj j),
      ∀ s, colimit.ι D j (ψ s) = φ s := by
  classical
  let : Fintype S := Fintype.ofFinite S
  choose idx val hval using (fun s => CategoryTheory.Limits.Types.jointly_surjective' (φ s))
  let objs : Finset J := Finset.univ.image idx
  let j : J := IsFiltered.sup objs ∅
  let a (s : S) : idx s ⟶ j :=
    IsFiltered.toSup objs ∅ (Finset.mem_image_of_mem idx (Finset.mem_univ s))
  refine ⟨j, fun s => D.map (a s) (val s), fun s => ?_⟩
  rw [← hval s, ← ConcreteCategory.comp_apply, colimit.w D (a s)]

/-- Finitely many equalities in a filtered colimit hold at one later stage. -/
@[sga "4 I 2.8.1" "4: forward implication"]
private theorem finite_family_eq_eventually_in_filtered_colimit
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ Type u) (i : J) (S : Type u) [Finite S]
    (ψ χ : S → D.obj i)
    (h : ∀ s, colimit.ι D i (ψ s) = colimit.ι D i (χ s)) :
    ∃ (j : J) (a : i ⟶ j), ∀ s, D.map a (ψ s) = D.map a (χ s) := by
  classical
  let : Fintype S := Fintype.ofFinite S
  choose idx arrow heq using (fun s =>
    (CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'
      (colimit.isColimit D) (ψ s) (χ s)).mp (h s))
  obtain ⟨B, hB⟩ := IsFiltered.sup_objs_exists
    (Finset.image (fun s => Under.mk (arrow s)) (Finset.univ : Finset S))
  let b (s : S) : Under.mk (arrow s) ⟶ B :=
    (hB (Finset.mem_image_of_mem _ (Finset.mem_univ s))).some
  refine ⟨B.right, B.hom, fun s => ?_⟩
  have hw : arrow s ≫ (b s).right = B.hom := Under.w (b s)
  rw [← hw, D.map_comp]
  exact congrArg (D.map (b s).right) (heq s)

/-- Finitely many sections of a pullback sheaf over a compact open descend together. -/
private theorem finite_pullback_sections_descend
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : SpectralDiagram.{u, u} J) (i : J) (U : Opens (D.F.obj i))
    (hU : IsCompact (U : Set (D.F.obj i)))
    (𝒢 : (D.F.obj i).Sheaf (Type u)) (S : Type u) [Finite S]
    (φ : S → D.limSections U 𝒢) :
    ∃ (A : Over i) (ψ : S → (D.sliceFunctor U 𝒢).obj (Opposite.op A)),
      ∀ s, D.toLim U 𝒢 A (ψ s) = φ s := by
  let θ : S → colimit (D.sliceFunctor U 𝒢) :=
    fun s => Classical.choose ((D.bijective_canonicalMap U 𝒢 hU).2 (φ s))
  have hθ (s : S) : D.canonicalMap U 𝒢 (θ s) = φ s :=
    Classical.choose_spec ((D.bijective_canonicalMap U 𝒢 hU).2 (φ s))
  obtain ⟨A, ψ, hψ⟩ :=
    finite_family_factors_through_filtered_colimit (D.sliceFunctor U 𝒢) S θ
  refine ⟨A.unop, ψ, fun s => ?_⟩
  rw [← D.canonicalMap_ι_apply U 𝒢 A.unop (ψ s)]
  simpa only [Opposite.op_unop, hψ s, SpectralDiagram.sliceCocone] using hθ s

/-- Finitely many equal pullback sections become equal at a common stage. -/
private theorem finite_pullback_sections_eq_eventually
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : SpectralDiagram.{u, u} J) (i : J) (U : Opens (D.F.obj i))
    (hU : IsCompact (U : Set (D.F.obj i)))
    (H : (D.F.obj i).Sheaf (Type u)) (A : Over i)
    (S : Type u) [Finite S]
    (ψ χ : S → (D.sliceFunctor U H).obj (op A))
    (h : ∀ s, D.toLim U H A (ψ s) = D.toLim U H A (χ s)) :
    ∃ (B : Over i) (a : B ⟶ A),
      ∀ s, (D.sliceFunctor U H).map a.op (ψ s) =
        (D.sliceFunctor U H).map a.op (χ s) := by
  have hc (s : S) :
      colimit.ι (D.sliceFunctor U H) (op A) (ψ s) =
        colimit.ι (D.sliceFunctor U H) (op A) (χ s) := by
    apply D.injective_canonicalMap U H hU
    rw [D.canonicalMap_ι_apply U H A, D.canonicalMap_ι_apply U H A]
    exact h s
  obtain ⟨B, a, ha⟩ := finite_family_eq_eventually_in_filtered_colimit
    (D.sliceFunctor U H) (op A) S ψ χ hc
  exact ⟨B.unop, a.unop, ha⟩

/-- Every sheaf with the specified finite coequalizer presentation has finite stalks. -/
private theorem finite_stalk_finite_presentation (A : TopCat.{u})
    (n m : ℕ) (U : Fin n → Opens A) (V : Fin m → Opens A)
    (S : Fin n → Type u) (T : Fin m → Type u)
    (hS : ∀ a, Finite (S a)) (_hT : ∀ b, Finite (T b))
    (β γ : (∐ fun b => extendedConstantSheaf (V b) (T b)) ⟶
      (∐ fun a => extendedConstantSheaf (U a) (S a)))
    (x : A) : Finite ((coequalizer β γ).presheaf.stalk x) :=
  finite_stalk_coequalizer A β γ (finite_stalk_coproduct A n
    (fun a => extendedConstantSheaf (U a) (S a))
    fun a => finite_stalk_extendedConstantSheaf A (U a) (S a)) x

/-- The adjunction between sets and sheaves on `A` extended by the initial object from `U`. -/
private noncomputable abbrev extendedConstantAdj (A : TopCat.{u}) (U : Opens A) :=
  (constantSheafAdj (Opens.grothendieckTopology
    (TopCat.Presheaf.ExtensionByInitial.sp (X := A) U)) (Type u) isTerminalTop).comp
    (TopCat.Presheaf.extendByInitialSheafAdjunction (C := Type u) U)

/-- The image of the whole space under the inclusion of an open is that open. -/
private lemma isOpenMap_functor_top {A : TopCat.{u}} (U : Opens A) :
    U.isOpenEmbedding.isOpenMap.functor.obj ⊤ = U := by
  ext x
  simp

/-- Sections over an inverse image open can be computed after pushforward. -/
private noncomputable def sections_restrict_pushforward_iso
    {A B : TopCat.{u}} (f : A ⟶ B) (V : Opens B) :
    TopCat.Sheaf.pushforward (Type u) f ⋙ Opens.sheafRestrict V ⋙
      (sheafSections (Opens.grothendieckTopology
        (TopCat.Presheaf.ExtensionByInitial.sp (X := B) V)) (Type u)).obj (Opposite.op ⊤) ≅
    Opens.sheafRestrict ((Opens.map f).obj V) ⋙
      (sheafSections (Opens.grothendieckTopology
        (TopCat.Presheaf.ExtensionByInitial.sp (X := A) ((Opens.map f).obj V)))
        (Type u)).obj (Opposite.op ⊤) := by
  let W₁ : Opens A := (Opens.map f).obj (V.isOpenEmbedding.isOpenMap.functor.obj ⊤)
  let W₂ : Opens A := ((Opens.map f).obj V).isOpenEmbedding.isOpenMap.functor.obj ⊤
  have hW : W₁ = W₂ := by
    ext x
    simp [W₁, W₂]
  refine NatIso.ofComponents (fun H => ?_) ?_
  · change H.obj.obj (op W₁) ≅ H.obj.obj (op W₂)
    exact eqToIso (congrArg (fun W : Opens A => H.obj.obj (op W)) hW)
  · intro H K α
    change α.hom.app (op W₁) ≫
        eqToHom (congrArg (fun W : Opens A => K.obj.obj (op W)) hW) =
      eqToHom (congrArg (fun W : Opens A => H.obj.obj (op W)) hW) ≫
        α.hom.app (op W₂)
    simpa only [eqToHom_map] using
      (α.hom.naturality (eqToHom (congrArg op hW))).symm

/-- Pullback commutes with a finite constant sheaf extended from an open. -/
private noncomputable def pullback_extendedConstant_iso
    {A B : TopCat.{u}} (f : A ⟶ B) (V : Opens B) (S : Type u) :
    (TopCat.Sheaf.pullback (Type u) f).obj (extendedConstantSheaf V S) ≅
      extendedConstantSheaf ((Opens.map f).obj V) S := by
  let U := (Opens.map f).obj V
  let adjB := extendedConstantAdj B V
  let adjA := extendedConstantAdj A U
  let adjF := adjB.comp (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f)
  exact ((adjF.ofNatIsoRight (sections_restrict_pushforward_iso f V)).leftAdjointUniq
    adjA).app S

/-- Pullback of a finite coproduct of extended constants, term by term. -/
private noncomputable def pullback_extendedConstant_coproduct_iso
    {A B : TopCat.{u}} (f : A ⟶ B) (n : ℕ)
    (U : Fin n → Opens B) (S : Fin n → Type u) :
    (TopCat.Sheaf.pullback (Type u) f).obj
      (∐ fun a => extendedConstantSheaf (U a) (S a)) ≅
    (∐ fun a => extendedConstantSheaf ((Opens.map f).obj (U a)) (S a)) :=
  pullback_coproduct_iso f n (fun a => extendedConstantSheaf (U a) (S a)) ≪≫
    Sigma.mapIso (fun a => pullback_extendedConstant_iso f (U a) (S a))

private lemma pullback_extendedConstant_coproduct_iso_ι
    {A B : TopCat.{u}} (f : A ⟶ B) (n : ℕ)
    (U : Fin n → Opens B) (S : Fin n → Type u) (a : Fin n) :
    (TopCat.Sheaf.pullback (Type u) f).map
        (Sigma.ι (fun b => extendedConstantSheaf (U b) (S b)) a) ≫
      (pullback_extendedConstant_coproduct_iso f n U S).hom =
    (pullback_extendedConstant_iso f (U a) (S a)).hom ≫
      Sigma.ι (fun b => extendedConstantSheaf
        ((Opens.map f).obj (U b)) (S b)) a := by
  let F := TopCat.Sheaf.pullback (Type u) f
  let K (b : Fin n) := extendedConstantSheaf (U b) (S b)
  have hι : F.map (Sigma.ι K a) ≫ (PreservesCoproduct.iso F K).hom =
      Sigma.ι (fun b => F.obj (K b)) a :=
    (isColimitOfHasCoproductOfPreservesColimit F K).comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit _) ⟨a⟩
  show F.map (Sigma.ι K a) ≫ (PreservesCoproduct.iso F K).hom ≫
    (Sigma.mapIso (fun b => pullback_extendedConstant_iso f (U b) (S b))).hom = _
  rw [← Category.assoc, hι, Sigma.ι_mapIso_hom]

private lemma pullback_extendedConstant_coproduct_iso_inv_ι
    {A B : TopCat.{u}} (f : A ⟶ B) (n : ℕ)
    (U : Fin n → Opens B) (S : Fin n → Type u) (a : Fin n) :
    Sigma.ι (fun b => extendedConstantSheaf
        ((Opens.map f).obj (U b)) (S b)) a ≫
      (pullback_extendedConstant_coproduct_iso f n U S).inv =
    (pullback_extendedConstant_iso f (U a) (S a)).inv ≫
      (TopCat.Sheaf.pullback (Type u) f).map
        (Sigma.ι (fun b => extendedConstantSheaf (U b) (S b)) a) := by
  apply (cancel_mono (pullback_extendedConstant_coproduct_iso f n U S).hom).mp
  simp [pullback_extendedConstant_coproduct_iso_ι]

/-- A map out of an extended constant sheaf is a family of sections on its open. -/
private noncomputable def extendedConstantHomSections
    (A : TopCat.{u}) (U : Opens A) (S : Type u)
    (H : A.Sheaf (Type u)) :
    (extendedConstantSheaf U S ⟶ H) ≃
      (S → H.presheaf.obj (op U)) := by
  let adj := extendedConstantAdj A U
  have htop := isOpenMap_functor_top U
  let e : (extendedConstantSheaf U S ⟶ H) ≃
      (S → H.presheaf.obj (op
        (U.isOpenEmbedding.isOpenMap.functor.obj ⊤))) :=
    (adj.homEquiv S H).trans TypeCat.homEquiv
  exact e.trans (Equiv.cast (congrArg
    (fun W : Opens A => S → H.presheaf.obj (op W)) htop))

private lemma castSectionFunction_apply
    (A : TopCat.{u}) (S : Type u) (H : A.Sheaf (Type u))
    {W W' : Opens A} (h : W = W')
    (φ : S → H.presheaf.obj (op W)) (s : S) :
    (cast (congrArg (fun V : Opens A => S → H.presheaf.obj (op V)) h) φ) s =
      cast (congrArg (fun V : Opens A => H.presheaf.obj (op V)) h) (φ s) := by
  cases h
  rfl

private lemma castSection_map
    (A : TopCat.{u}) {H K : A.Sheaf (Type u)} (m : H ⟶ K)
    {W W' : Opens A} (h : W = W') (s : H.presheaf.obj (op W)) :
    cast (congrArg (fun V : Opens A => K.presheaf.obj (op V)) h)
      (m.hom.app (op W) s) =
    m.hom.app (op W')
      (cast (congrArg (fun V : Opens A => H.presheaf.obj (op V)) h) s) := by
  cases h
  rfl

private lemma extendedConstantHomSections_naturality
    (A : TopCat.{u}) (U : Opens A) (S : Type u)
    {H K : A.Sheaf (Type u)} (α : extendedConstantSheaf U S ⟶ H)
    (m : H ⟶ K) (s : S) :
    (extendedConstantHomSections A U S K) (α ≫ m) s =
      m.hom.app (op U) ((extendedConstantHomSections A U S H) α s) := by
  let adj := extendedConstantAdj A U
  have htop := isOpenMap_functor_top U
  show (cast (congrArg (fun W : Opens A => S → K.presheaf.obj (op W)) htop)
      (TypeCat.homEquiv ((adj.homEquiv S K) (α ≫ m)))) s =
    m.hom.app (op U)
      ((cast (congrArg (fun W : Opens A => S → H.presheaf.obj (op W)) htop)
        (TypeCat.homEquiv ((adj.homEquiv S H) α))) s)
  rw [castSectionFunction_apply, castSectionFunction_apply,
    ← castSection_map A m htop]
  all_goals try assumption
  have h := adj.homEquiv_naturality_right α m
  have hs := congrArg (fun z => z s) h
  change (TypeCat.homEquiv ((adj.homEquiv S K) (α ≫ m))) s =
    m.hom.app (op (U.isOpenEmbedding.isOpenMap.functor.obj ⊤))
      ((TypeCat.homEquiv ((adj.homEquiv S H) α)) s) at hs
  exact congrArg (fun z => cast
    (congrArg (fun W : Opens A => K.presheaf.obj (op W)) htop) z) hs

private lemma extendedConstantHomSections_eq
    (A : TopCat.{u}) {U V : Opens A} (h : U = V) (S : Type u)
    (H : A.Sheaf (Type u))
    (α : extendedConstantSheaf U S ⟶ H) (s : S) :
    (extendedConstantHomSections A V S H)
      ((eqToIso (congrArg (fun W => extendedConstantSheaf W S) h)).inv ≫ α) s =
      cast (congrArg (fun W : Opens A => H.presheaf.obj (op W)) h)
        ((extendedConstantHomSections A U S H) α s) := by
  cases h
  simp

private lemma leftAdjointUniq_homEquiv_inv_comp
    {C : Type v} {D : Type w} [Category C] [Category D]
    {L L' : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R) (X : C) (Y : D) (m : L.obj X ⟶ Y) :
    (b.homEquiv X Y) (((a.leftAdjointUniq b).inv.app X) ≫ m) =
      (a.homEquiv X Y) m := by
  show b.unit.app X ≫ R.map ((a.leftAdjointUniq b).inv.app X ≫ m) =
    a.unit.app X ≫ R.map m
  rw [← a.unit_leftAdjointUniq_hom_app b X, Functor.map_comp]
  calc
    (a.unit.app X ≫ R.map ((a.leftAdjointUniq b).hom.app X)) ≫
        R.map ((a.leftAdjointUniq b).inv.app X) ≫ R.map m =
      a.unit.app X ≫ R.map
        ((a.leftAdjointUniq b).hom.app X ≫ (a.leftAdjointUniq b).inv.app X) ≫
        R.map m := by simp only [Functor.map_comp, Category.assoc]
    _ = a.unit.app X ≫ R.map m := by
      rw [(a.leftAdjointUniq b).hom_inv_id_app X]
      simp

private lemma eqToHom_type_apply_cast {I : Type v} (P : I → Type u)
    {a b : I} (h : a = b) (x : P a) :
    (eqToHom (congrArg P h) : P a ⟶ P b) x =
      cast (congrArg P h) x := by
  cases h
  rfl

private lemma typeHomEquiv_comp_apply {P Q R : Type u}
    (f : P ⟶ Q) (g : Q ⟶ R) (s : P) :
    TypeCat.homEquiv (f ≫ g) s =
      (ConcreteCategory.hom g) (TypeCat.homEquiv f s) := by
  simp only [TypeCat.homEquiv_apply, types_comp_apply]

private lemma extendedConstantHomSections_pullback
    {A B : TopCat.{u}} (f : A ⟶ B) (V : Opens B) (S : Type u)
    (H : B.Sheaf (Type u))
    (α : extendedConstantSheaf V S ⟶ H) (s : S) :
    (extendedConstantHomSections A ((Opens.map f).obj V) S
      ((TopCat.Sheaf.pullback (Type u) f).obj H))
      ((pullback_extendedConstant_iso f V S).inv ≫
        (TopCat.Sheaf.pullback (Type u) f).map α) s =
    (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app H).hom.app
      (op V)) ((extendedConstantHomSections B V S H) α s) := by
  let U := (Opens.map f).obj V
  let adjB := extendedConstantAdj B V
  let adjA := extendedConstantAdj A U
  let adjF := adjB.comp (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f)
  let adjF' := adjF.ofNatIsoRight (sections_restrict_pushforward_iso f V)
  have h := leftAdjointUniq_homEquiv_inv_comp adjF' adjA S
    ((TopCat.Sheaf.pullback (Type u) f).obj H)
    ((TopCat.Sheaf.pullback (Type u) f).map α)
  have htop := isOpenMap_functor_top U
  show (cast (congrArg (fun W : Opens A => S →
      ((TopCat.Sheaf.pullback (Type u) f).obj H).presheaf.obj (op W)) htop)
      (TypeCat.homEquiv ((adjA.homEquiv S
        ((TopCat.Sheaf.pullback (Type u) f).obj H))
        ((pullback_extendedConstant_iso f V S).inv ≫
          (TopCat.Sheaf.pullback (Type u) f).map α)))) s = _
  have h' := congrArg (fun m : S ⟶
      (Opens.sheafRestrict U ⋙
        (sheafSections (Opens.grothendieckTopology
          (TopCat.Presheaf.ExtensionByInitial.sp (X := A) U)) (Type u)).obj (op ⊤)).obj
          ((TopCat.Sheaf.pullback (Type u) f).obj H) =>
      (cast (congrArg (fun W : Opens A => S →
        ((TopCat.Sheaf.pullback (Type u) f).obj H).presheaf.obj (op W)) htop)
          (TypeCat.homEquiv m)) s) h
  refine h'.trans ?_
  simp only [adjF', Adjunction.homEquiv_ofNatIsoRight_apply,
    adjF, Adjunction.comp_homEquiv]
  have hF : ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv _ _)
      ((TopCat.Sheaf.pullback (Type u) f).map α) =
      α ≫ (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app H := by
    rw [Adjunction.homEquiv_unit]
    exact ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.naturality α).symm
  change ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv
      ((constantSheaf (Opens.grothendieckTopology
        (TopCat.Presheaf.ExtensionByInitial.sp (X := B) V)) (Type u) ⋙
        TopCat.Presheaf.extendByInitialSheaf (C := Type u) V).obj S)
      ((TopCat.Sheaf.pullback (Type u) f).obj H))
      ((TopCat.Sheaf.pullback (Type u) f).map α) =
      α ≫ (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app H at hF
  simp only [Equiv.trans_apply]
  rw [hF]
  have hB := adjB.homEquiv_naturality_right α
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app H)
  simp only [Functor.comp_obj] at hB
  have hB' := congrArg (fun m : S ⟶
      (Opens.sheafRestrict V ⋙
        (sheafSections (Opens.grothendieckTopology
          (TopCat.Presheaf.ExtensionByInitial.sp (X := B) V)) (Type u)).obj (op ⊤)).obj
      ((TopCat.Sheaf.pushforward (Type u) f).obj
        ((TopCat.Sheaf.pullback (Type u) f).obj H)) =>
      (cast (congrArg (fun W : Opens A => S →
        ((TopCat.Sheaf.pullback (Type u) f).obj H).presheaf.obj (op W)) htop)
        (TypeCat.homEquiv
          (m ≫ (sections_restrict_pushforward_iso f V).hom.app
            ((TopCat.Sheaf.pullback (Type u) f).obj H)))) s) hB
  refine hB'.trans ?_
  have vtop := isOpenMap_functor_top V
  let W₁ : Opens A := (Opens.map f).obj
    (V.isOpenEmbedding.isOpenMap.functor.obj ⊤)
  let W₂ : Opens A := U.isOpenEmbedding.isOpenMap.functor.obj ⊤
  have hW : W₁ = W₂ := by
    ext x
    simp [W₁, W₂, U]
  let s₀ : H.presheaf.obj (op (V.isOpenEmbedding.isOpenMap.functor.obj ⊤)) :=
    TypeCat.homEquiv ((adjB.homEquiv S H) α) s
  have hmap : (TypeCat.homEquiv
      ((adjB.homEquiv S H) α ≫
        (Opens.sheafRestrict V ⋙
          (sheafSections (Opens.grothendieckTopology
            (TopCat.Presheaf.ExtensionByInitial.sp (X := B) V)) (Type u)).obj
            (op ⊤)).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app H))) s =
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app H).hom.app
        (op (V.isOpenEmbedding.isOpenMap.functor.obj ⊤))) s₀ :=
    rfl
  have hiso (ξ : ((TopCat.Sheaf.pullback (Type u) f).obj H).presheaf.obj (op W₁)) :
      (sections_restrict_pushforward_iso f V).hom.app
        ((TopCat.Sheaf.pullback (Type u) f).obj H) ξ =
      cast (congrArg (fun W : Opens A =>
        ((TopCat.Sheaf.pullback (Type u) f).obj H).presheaf.obj (op W)) hW) ξ := by
    show (eqToHom (congrArg (fun W : Opens A =>
      ((TopCat.Sheaf.pullback (Type u) f).obj H).presheaf.obj (op W)) hW)) ξ = _
    exact eqToHom_type_apply_cast (fun W : Opens A =>
      ((TopCat.Sheaf.pullback (Type u) f).obj H).presheaf.obj (op W)) hW ξ
  let Q := (TopCat.Sheaf.pullback (Type u) f).obj H
  let m₀ := (adjB.homEquiv S H) α ≫
    (Opens.sheafRestrict V ⋙
      (sheafSections (Opens.grothendieckTopology
        (TopCat.Presheaf.ExtensionByInitial.sp (X := B) V)) (Type u)).obj (op ⊤)).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app H)
  have hs₀ : (extendedConstantHomSections B V S H) α s =
      cast (congrArg (fun W : Opens B => H.presheaf.obj (op W)) vtop) s₀ := by
    show (cast (congrArg (fun W : Opens B => S → H.presheaf.obj (op W)) vtop)
      (TypeCat.homEquiv ((adjB.homEquiv S H) α))) s = _
    exact castSectionFunction_apply B S H vtop
      (TypeCat.homEquiv ((adjB.homEquiv S H) α)) s
  have htransport (ξ : Q.presheaf.obj (op W₁)) :
      cast (congrArg (fun W : Opens A => Q.presheaf.obj (op W)) htop)
        (cast (congrArg (fun W : Opens A => Q.presheaf.obj (op W)) hW) ξ) =
      cast (congrArg (fun W : Opens B =>
        ((TopCat.Sheaf.pushforward (Type u) f).obj Q).presheaf.obj (op W)) vtop) ξ := by
    simp only [cast_cast]
    rfl
  have hlast :
      cast (congrArg (fun W : Opens A => Q.presheaf.obj (op W)) htop)
        (cast (congrArg (fun W : Opens A => Q.presheaf.obj (op W)) hW)
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app H).hom.app
            (op (V.isOpenEmbedding.isOpenMap.functor.obj ⊤)) s₀)) =
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app H).hom.app
        (op V))
        (cast (congrArg (fun W : Opens B => H.presheaf.obj (op W)) vtop) s₀) := by
    calc
      _ = cast (congrArg (fun W : Opens B =>
            ((TopCat.Sheaf.pushforward (Type u) f).obj Q).presheaf.obj (op W)) vtop)
            (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app H).hom.app
              (op (V.isOpenEmbedding.isOpenMap.functor.obj ⊤)) s₀) := htransport _
      _ = _ := castSection_map B
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app H) vtop s₀
  rw [hs₀]
  refine (show _ = cast (congrArg (fun W : Opens A => Q.presheaf.obj (op W)) htop)
      ((sections_restrict_pushforward_iso f V).hom.app Q
        (TypeCat.homEquiv m₀ s)) from ?_).trans ?_
  · rw [castSectionFunction_apply A S Q htop]
    exact congrArg (fun ξ : Q.presheaf.obj (op W₂) =>
      cast (congrArg (fun W : Opens A => Q.presheaf.obj (op W)) htop) ξ)
      (typeHomEquiv_comp_apply m₀
        ((sections_restrict_pushforward_iso f V).hom.app Q) s)
  refine (congrArg _ (hiso (TypeCat.homEquiv m₀ s))).trans ?_
  refine (congrArg _ (congrArg _ hmap)).trans ?_
  exact hlast

/-- A homeomorphism transports the germwise model of pullback sections. -/
private noncomputable def germPullbackSectionsHomeomorph
    {Y Z A : TopCat.{u}} (q : A ≃ₜ Z) (g : Z → Y)
    (H : Y.Presheaf (Type u)) (W : Opens Z) :
    (GermPullback.sheaf g H).presheaf.obj (op W) ≃
      (GermPullback.sheaf (g ∘ q) H).presheaf.obj
        (op (⟨q ⁻¹' (W : Set Z), W.isOpen.preimage q.continuous⟩ : Opens A)) := by
  let W' : Opens A := ⟨q ⁻¹' (W : Set Z), W.isOpen.preimage q.continuous⟩
  refine ⟨GermPullback.comap q.continuous (fun _ => rfl) (fun z => z.2),
    GermPullback.comap q.symm.continuous (fun z => by simp)
      (fun z => by change q (q.symm z.1) ∈ W; simp), ?_, ?_⟩
  · intro σ
    apply GermPullback.ext
    intro z
    simp only [GermPullback.comap_val]
    exact congrArg σ.1 (Subtype.ext (q.apply_symm_apply z.1))
  · intro σ
    apply GermPullback.ext
    intro z
    simp only [GermPullback.comap_val]
    exact congrArg σ.1 (Subtype.ext (q.symm_apply_apply z.1))

omit [SpectralSpace X] in
/-- Finitely many pullback sections on a space homeomorphic to the limit descend together. -/
private theorem finite_pullback_sections_descend_homeomorph
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : SpectralDiagram.{u, u} J) (q : X ≃ₜ D.invLimit)
    (i : J) (U : Opens (D.F.obj i))
    (hU : IsCompact (U : Set (D.F.obj i)))
    (H : (D.F.obj i).Sheaf (Type u))
    (S : Type u) [Finite S]
    (φ : S → (GermPullback.sheaf (Y := D.F.obj i) (Z := TopCat.of X)
      (fun x : X => D.projFun i (q x)) H.presheaf).presheaf.obj
      (op (⟨(fun x : X => q x) ⁻¹' (D.limPre U : Set D.invLimit),
        (D.limPre U).isOpen.preimage q.continuous⟩ : Opens X))) :
    ∃ (A : Over i) (ψ : S → (D.sliceFunctor U H).obj (op A)),
      ∀ s, germPullbackSectionsHomeomorph
        (A := TopCat.of X) (Z := TopCat.of D.invLimit) (Y := D.F.obj i)
        q (D.projFun i) H.presheaf
        (D.limPre U) (D.toLim U H A (ψ s)) = φ s := by
  let e := germPullbackSectionsHomeomorph
    (A := TopCat.of X) (Z := TopCat.of D.invLimit) (Y := D.F.obj i)
    q (D.projFun i) H.presheaf
    (D.limPre U)
  obtain ⟨A, ψ, hψ⟩ := finite_pullback_sections_descend D i U hU H S
    (fun s => e.symm (φ s))
  exact ⟨A, ψ, fun s => by rw [hψ s, Equiv.apply_symm_apply]⟩

omit [SpectralSpace X] in
/-- Transporting a stage section through the limit homeomorphism is precomposition. -/
private theorem germPullbackSectionsHomeomorph_toLim
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : SpectralDiagram.{u, u} J) (q : X ≃ₜ D.invLimit)
    (i : J) (U : Opens (D.F.obj i))
    (H : (D.F.obj i).Sheaf (Type u)) (A : Over i)
    (σ : (D.sliceFunctor U H).obj (op A)) :
    germPullbackSectionsHomeomorph
      (A := TopCat.of X) (Z := TopCat.of D.invLimit) (Y := D.F.obj i)
      q (D.projFun i) H.presheaf (D.limPre U) (D.toLim U H A σ) =
    GermPullback.comap
      ((D.projFun_continuous A.left).comp q.continuous)
      (fun x : X => D.projFun_eq_mapFun A.hom (q x))
      (fun x : (⟨(fun x : X => q x) ⁻¹' (D.limPre U : Set D.invLimit),
        (D.limPre U).isOpen.preimage q.continuous⟩ : Opens X) =>
        D.proj_mem U (⟨q x.1, x.2⟩ : D.limPre U)) σ :=
  GermPullback.ext fun _ => rfl

/-- A sheaf with a finite coequalizer presentation over the quasi-compact
opens of a spectral space descends to a sheaf with finite stalks on a finite
sober space. -/
@[stacks 0CAK]
theorem exists_pullback_from_finite_sober_of_hasFiniteBasisCoequalizerPresentation
    (F : TopCat.Sheaf (Type u) (TopCat.of X))
    (hF : HasFiniteBasisCoequalizerPresentation
      {U : Opens X | IsCompact (U : Set X)} F) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : Finite Y)
      (_ : QuasiSober Y) (_ : T0Space Y) (f : TopCat.of X ⟶ TopCat.of Y)
      (G : TopCat.Sheaf (Type u) (TopCat.of Y)),
      IsSpectralMap f ∧
        (∀ y, Finite (G.presheaf.stalk y)) ∧
        Nonempty ((TopCat.Sheaf.pullback (Type u) f).obj G ≅ F) := by
  obtain ⟨n, m, U, V, S, T, hU, hV, hS, hT, β, γ, ⟨hcoeq⟩⟩ := hF
  obtain ⟨J, _, _, E, hfinite, hsober, ht0, ⟨e⟩⟩ :=
    (spectralSpace_iff_isDirectedInverseLimitOfFiniteSober X).mp inferInstance
  let D : SpectralDiagram.{u, u} J :=
    { F := E
      isSpectralSpace := fun _ => ⟨⟩
      isSpectralMap := fun a =>
        ⟨(E.map a).hom.continuous, fun _ _ _ => (Set.toFinite _).isCompact⟩ }
  let q : X ≃ₜ D.invLimit :=
    e.trans (TopCat.homeoOfIso
      ((TopCat.limitConeIsLimit E).conePointUniqueUpToIso
        (CategoryTheory.Limits.limit.isLimit E)))
  obtain ⟨iU, Ui, hUi, hUi_pre⟩ :=
    exists_stage_fin_compact_opens_of_homeomorph D q n U (fun a => hU a)
  obtain ⟨iV, Vi, hVi, hVi_pre⟩ :=
    exists_stage_fin_compact_opens_of_homeomorph D q m V (fun b => hV b)
  let i : J := IsCofiltered.min iU iV
  let aU : i ⟶ iU := IsCofiltered.minToLeft iU iV
  let aV : i ⟶ iV := IsCofiltered.minToRight iU iV
  let Ui' (a : Fin n) : Opens (E.obj i) := (Opens.map (E.map aU)).obj (Ui a)
  let Vi' (b : Fin m) : Opens (E.obj i) := (Opens.map (E.map aV)).obj (Vi b)
  have hUi'_compact (a : Fin n) : IsCompact (Ui' a : Set (E.obj i)) :=
    (D.isSpectralMap aU).isCompact_preimage_of_isOpen (Ui a).isOpen (hUi a)
  have hVi'_compact (b : Fin m) : IsCompact (Vi' b : Set (E.obj i)) :=
    (D.isSpectralMap aV).isCompact_preimage_of_isOpen (Vi b).isOpen (hVi b)
  have hUi' (a : Fin n) :
      (fun x : X => D.projFun i (q x)) ⁻¹' (Ui' a : Set (E.obj i)) =
        (U a : Set X) :=
    (preimage_proj_comp_map D q aU (Ui a)).trans (hUi_pre a)
  have hVi' (b : Fin m) :
      (fun x : X => D.projFun i (q x)) ⁻¹' (Vi' b : Set (E.obj i)) =
        (V b : Set X) :=
    (preimage_proj_comp_map D q aV (Vi b)).trans (hVi_pre b)
  let f : TopCat.of X ⟶ E.obj i :=
    TopCat.ofHom ⟨fun x => D.projFun i (q x),
      (D.projFun_continuous i).comp q.continuous⟩
  have hf : IsSpectralMap f := ⟨f.hom.continuous, fun _ hWopen hWcompact =>
    q.isCompact_preimage.mpr <|
      (spectralDiagram_proj_isSpectralMap D i).isCompact_preimage_of_isOpen hWopen hWcompact⟩
  have hUi'_open (a : Fin n) : (Opens.map f).obj (Ui' a) = U a :=
    Opens.ext (hUi' a)
  have hVi'_open (b : Fin m) : (Opens.map f).obj (Vi' b) = V b :=
    Opens.ext (hVi' b)
  let B₀ : (E.obj i).Sheaf (Type u) :=
    ∐ fun a => extendedConstantSheaf (Ui' a) (S a)
  let A₀ : (E.obj i).Sheaf (Type u) :=
    ∐ fun b => extendedConstantSheaf (Vi' b) (T b)
  let eB : (TopCat.Sheaf.pullback (Type u) f).obj B₀ ≅
      (∐ fun a => extendedConstantSheaf (U a) (S a)) :=
    pullback_extendedConstant_coproduct_iso f n Ui' S ≪≫
      Sigma.mapIso (fun a => eqToIso (congrArg
        (fun W => extendedConstantSheaf W (S a)) (hUi'_open a)))
  let eA : (TopCat.Sheaf.pullback (Type u) f).obj A₀ ≅
      (∐ fun b => extendedConstantSheaf (V b) (T b)) :=
    pullback_extendedConstant_coproduct_iso f m Vi' T ≪≫
      Sigma.mapIso (fun b => eqToIso (congrArg
        (fun W => extendedConstantSheaf W (T b)) (hVi'_open b)))
  let β' : (TopCat.Sheaf.pullback (Type u) f).obj A₀ ⟶
      (TopCat.Sheaf.pullback (Type u) f).obj B₀ := eA.hom ≫ β ≫ eB.inv
  let γ' : (TopCat.Sheaf.pullback (Type u) f).obj A₀ ⟶
      (TopCat.Sheaf.pullback (Type u) f).obj B₀ := eA.hom ≫ γ ≫ eB.inv
  let Bₓ : (TopCat.of X).Sheaf (Type u) :=
    ∐ fun a => extendedConstantSheaf (U a) (S a)
  let Aₓ : (TopCat.of X).Sheaf (Type u) :=
    ∐ fun b => extendedConstantSheaf (V b) (T b)
  let sectionOf (b : Fin m) (t : T b) (which : Bool) :
      (GermPullback.sheaf (Y := D.F.obj i) (Z := TopCat.of X)
        (fun x : X => D.projFun i (q x)) B₀.presheaf).presheaf.obj
        (op (V b)) := by
    let h : extendedConstantSheaf (V b) (T b) ⟶ Bₓ :=
      Sigma.ι (fun c => extendedConstantSheaf (V c) (T c)) b ≫
        (if which then β else γ)
    let s := (extendedConstantHomSections (TopCat.of X) (V b) (T b) Bₓ) h t
    exact (pullbackToGerm f B₀).hom.app (op (V b))
      (eB.inv.hom.app (op (V b)) s)
  have hWb (b : Fin m) :
      (⟨(fun x : X => q x) ⁻¹' (D.limPre (Vi' b) : Set D.invLimit),
        (D.limPre (Vi' b)).isOpen.preimage q.continuous⟩ : Opens X) = V b :=
    Opens.ext (hVi' b)
  let φ (b : Fin m) : T b × Bool →
      (GermPullback.sheaf (Y := D.F.obj i) (Z := TopCat.of X)
        (fun x : X => D.projFun i (q x)) B₀.presheaf).presheaf.obj
        (op (⟨(fun x : X => q x) ⁻¹' (D.limPre (Vi' b) : Set D.invLimit),
          (D.limPre (Vi' b)).isOpen.preimage q.continuous⟩ : Opens X)) :=
    fun z => (hWb b).symm ▸ sectionOf b z.1 z.2
  have stage_b (b : Fin m) :
      ∃ (A : Over i) (ψ : T b × Bool → (D.sliceFunctor (Vi' b) B₀).obj (op A)),
        ∀ z, germPullbackSectionsHomeomorph
          (A := TopCat.of X) (Z := TopCat.of D.invLimit) (Y := D.F.obj i)
          q (D.projFun i) B₀.presheaf (D.limPre (Vi' b))
          (D.toLim (Vi' b) B₀ A (ψ z)) = φ b z :=
    finite_pullback_sections_descend_homeomorph D q i (Vi' b)
      (hVi'_compact b) B₀ (T b × Bool) (φ b)
  choose A_b ψ_b hψ_b using stage_b
  classical
  let objs : Finset (Over i) := Finset.univ.image A_b
  let K : Over i := IsCofiltered.inf objs ∅
  let toA (b : Fin m) : K ⟶ A_b b :=
    IsCofiltered.infTo objs ∅ (Finset.mem_image_of_mem A_b (Finset.mem_univ b))
  let ψK (b : Fin m) (z : T b × Bool) :
      (D.sliceFunctor (Vi' b) B₀).obj (op K) :=
    (D.sliceFunctor (Vi' b) B₀).map (toA b).op (ψ_b b z)
  have hψK (b : Fin m) (z : T b × Bool) :
      germPullbackSectionsHomeomorph
        (A := TopCat.of X) (Z := TopCat.of D.invLimit) (Y := D.F.obj i)
        q (D.projFun i) B₀.presheaf (D.limPre (Vi' b))
        (D.toLim (Vi' b) B₀ K (ψK b z)) = φ b z := by
    have hlim : D.toLim (Vi' b) B₀ K (ψK b z) =
        D.toLim (Vi' b) B₀ (A_b b) (ψ_b b z) := by
      apply GermPullback.ext
      intro x
      simp only [SpectralDiagram.toLim_val, ψK,
        SpectralDiagram.sliceFunctor_map_val]
      exact congrArg (ψ_b b z).1 (Subtype.ext
        (D.projFun_eq_mapFun (toA b).left x.1).symm)
    rw [hlim]
    exact hψ_b b z
  let g : E.obj K.left ⟶ E.obj i := E.map K.hom
  let Uj (a : Fin n) : Opens (E.obj K.left) := D.slicePre (Ui' a) K
  let Vj (b : Fin m) : Opens (E.obj K.left) := D.slicePre (Vi' b) K
  let Bj : (E.obj K.left).Sheaf (Type u) :=
    ∐ fun a => extendedConstantSheaf (Uj a) (S a)
  let Aj : (E.obj K.left).Sheaf (Type u) :=
    ∐ fun b => extendedConstantSheaf (Vj b) (T b)
  let ejB : (TopCat.Sheaf.pullback (Type u) g).obj B₀ ≅ Bj :=
    pullback_extendedConstant_coproduct_iso g n Ui' S
  let ejA : (TopCat.Sheaf.pullback (Type u) g).obj A₀ ≅ Aj :=
    pullback_extendedConstant_coproduct_iso g m Vi' T
  let : IsIso (pullbackToGerm g B₀) := Stacks.GermPullbackComparison.pullbackToGerm_isIso g B₀
  let stageMap (b : Fin m) (which : Bool) :
      extendedConstantSheaf (Vj b) (T b) ⟶ Bj :=
    (extendedConstantHomSections (E.obj K.left) (Vj b) (T b) Bj).symm
      (fun t => ejB.hom.hom.app (op (Vj b))
        ((asIso (pullbackToGerm g B₀)).inv.hom.app (op (Vj b))
          (ψK b (t, which))))
  let βj : Aj ⟶ Bj := Sigma.desc (fun b => stageMap b true)
  let γj : Aj ⟶ Bj := Sigma.desc (fun b => stageMap b false)
  let G : (E.obj K.left).Sheaf (Type u) := coequalizer βj γj
  have hG (y : E.obj K.left) : Finite (G.presheaf.stalk y) :=
    finite_stalk_finite_presentation (E.obj K.left) n m Uj Vj S T hS hT βj γj y
  let fK : TopCat.of X ⟶ E.obj K.left :=
    TopCat.ofHom ⟨fun x => D.projFun K.left (q x),
      (D.projFun_continuous K.left).comp q.continuous⟩
  have hfK : IsSpectralMap fK := ⟨fK.hom.continuous, fun _ hWopen hWcompact =>
    q.isCompact_preimage.mpr <|
      (spectralDiagram_proj_isSpectralMap D K.left).isCompact_preimage_of_isOpen hWopen hWcompact⟩
  have hfg : fK ≫ g = f := by
    ext x
    exact (D.projFun_eq_mapFun K.hom (q x)).symm
  have hUj (a : Fin n) : (Opens.map fK).obj (Uj a) = U a :=
    Opens.ext ((preimage_proj_comp_map D q K.hom (Ui' a)).trans (hUi' a))
  have hVj (b : Fin m) : (Opens.map fK).obj (Vj b) = V b :=
    Opens.ext ((preimage_proj_comp_map D q K.hom (Vi' b)).trans (hVi' b))
  let eBjX : (TopCat.Sheaf.pullback (Type u) fK).obj Bj ≅ Bₓ :=
    (TopCat.Sheaf.pullback (Type u) fK).mapIso ejB.symm ≪≫
      ((sheafPullbackCompIso fK g (Type u)).app B₀).symm ≪≫
      eqToIso (congrArg
        (fun h : TopCat.of X ⟶ E.obj i =>
          (TopCat.Sheaf.pullback (Type u) h).obj B₀) hfg) ≪≫ eB
  let eAjX : (TopCat.Sheaf.pullback (Type u) fK).obj Aj ≅ Aₓ :=
    pullback_extendedConstant_coproduct_iso fK m Vj T ≪≫
      Sigma.mapIso (fun b => eqToIso (congrArg
        (fun W => extendedConstantSheaf W (T b)) (hVj b)))
  let βK : Aₓ ⟶ Bₓ :=
    eAjX.inv ≫ (TopCat.Sheaf.pullback (Type u) fK).map βj ≫ eBjX.hom
  let γK : Aₓ ⟶ Bₓ :=
    eAjX.inv ≫ (TopCat.Sheaf.pullback (Type u) fK).map γj ≫ eBjX.hom
  have hιAj (b : Fin m) :
      Sigma.ι (fun c => extendedConstantSheaf (V c) (T c)) b ≫
        eAjX.inv =
      (eqToIso (congrArg (fun W => extendedConstantSheaf W (T b))
        (hVj b))).inv ≫
        (pullback_extendedConstant_iso fK (Vj b) (T b)).inv ≫
        (TopCat.Sheaf.pullback (Type u) fK).map
          (Sigma.ι (fun c => extendedConstantSheaf (Vj c) (T c)) b) := by
    let p (c : Fin m) := eqToIso (congrArg
      (fun W => extendedConstantSheaf W (T c)) (hVj c))
    simp only [eAjX, Iso.trans_inv]
    rw [← Category.assoc, Sigma.ι_mapIso_inv p b, Category.assoc,
      pullback_extendedConstant_coproduct_iso_inv_ι]
  have hgen (b : Fin m) (which : Bool) :
      Sigma.ι (fun c => extendedConstantSheaf (V c) (T c)) b ≫
        (if which then βK else γK) =
      (eqToIso (congrArg (fun W => extendedConstantSheaf W (T b))
        (hVj b))).inv ≫
        (pullback_extendedConstant_iso fK (Vj b) (T b)).inv ≫
        (TopCat.Sheaf.pullback (Type u) fK).map (stageMap b which) ≫ eBjX.hom := by
    cases which <;>
    · simp only [Bool.false_eq_true, ↓reduceIte, βK, γK, βj, γj]
      rw [← Category.assoc, hιAj b]
      simp only [Category.assoc, ← Functor.map_comp_assoc, Sigma.ι_desc]
  have hsection (b : Fin m) (t : T b) (which : Bool) :
      cast (congrArg (fun W : Opens X =>
        (GermPullback.sheaf (Y := D.F.obj i) (Z := TopCat.of X)
          (fun x : X => D.projFun i (q x)) B₀.presheaf).presheaf.obj
          (op W)) (hWb b))
        (germPullbackSectionsHomeomorph
          (A := TopCat.of X) (Z := TopCat.of D.invLimit) (Y := D.F.obj i)
          q (D.projFun i) B₀.presheaf (D.limPre (Vi' b))
          (D.toLim (Vi' b) B₀ K (ψK b (t, which)))) =
      (sectionOf b t which :
        (GermPullback.sheaf (Y := D.F.obj i) (Z := TopCat.of X)
          (fun x : X => D.projFun i (q x)) B₀.presheaf).presheaf.obj
          (op (V b))) := by
    have h := hψK b (t, which)
    change _ = (hWb b).symm ▸ sectionOf b t which at h
    have h' := congrArg (fun ξ => cast (congrArg (fun W : Opens X =>
      (GermPullback.sheaf (Y := D.F.obj i) (Z := TopCat.of X)
        (fun x : X => D.projFun i (q x)) B₀.presheaf).presheaf.obj
        (op W)) (hWb b)) ξ) h
    have hcancel {W W' : Opens X} (hw : W = W')
        (s : (GermPullback.sheaf (Y := D.F.obj i) (Z := TopCat.of X)
          (fun x : X => D.projFun i (q x)) B₀.presheaf).presheaf.obj (op W')) :
        cast (congrArg (fun W : Opens X =>
          (GermPullback.sheaf (Y := D.F.obj i) (Z := TopCat.of X)
            (fun x : X => D.projFun i (q x)) B₀.presheaf).presheaf.obj (op W)) hw)
          (hw.symm ▸ s) = s := by
      cases hw
      rfl
    exact h'.trans (hcancel (hWb b) (sectionOf b t which))
  -- Coherence of the two pullback models at the chosen stage sections.
  have hmodel (b : Fin m) (t : T b) (which : Bool) :
      (pullbackToGerm f B₀).hom.app (op (V b))
        (eB.inv.hom.app (op (V b))
          (cast (congrArg (fun W : Opens X => Bₓ.presheaf.obj (op W)) (hVj b))
            (eBjX.hom.hom.app (op ((Opens.map fK).obj (Vj b)))
              (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) fK).unit.app Bj).hom.app
                (op (Vj b))
                (ejB.hom.hom.app (op (Vj b))
                  ((asIso (pullbackToGerm g B₀)).inv.hom.app (op (Vj b))
                    (ψK b (t, which)))))))) =
      cast (congrArg (fun W : Opens X =>
        (GermPullback.sheaf (Y := D.F.obj i) (Z := TopCat.of X)
          (fun x : X => D.projFun i (q x)) B₀.presheaf).presheaf.obj
          (op W)) (hWb b))
        (germPullbackSectionsHomeomorph
          (A := TopCat.of X) (Z := TopCat.of D.invLimit) (Y := D.F.obj i)
          q (D.projFun i) B₀.presheaf (D.limPre (Vi' b))
          (D.toLim (Vi' b) B₀ K (ψK b (t, which)))) := by
    rw [germPullbackSectionsHomeomorph_toLim]
    apply GermPullback.ext
    intro x
    apply germPullback_value_eq_of_eval_eq
    rw [germPullback_eval_cast (ConcreteCategory.hom f) B₀.presheaf (hWb b), pullbackToGerm_eval,
      ← castSection_map (TopCat.of X) eB.inv (hVj b)]
    let W := (Opens.map fK).obj (Vj b)
    let r : (TopCat.Sheaf.pullback (Type u) fK).obj Bj ⟶
        (TopCat.Sheaf.pullback (Type u) f).obj B₀ :=
      (TopCat.Sheaf.pullback (Type u) fK).map ejB.inv ≫
        ((sheafPullbackCompIso fK g (Type u)).app B₀).inv ≫
          (eqToIso (congrArg
            (fun h : TopCat.of X ⟶ E.obj i =>
              (TopCat.Sheaf.pullback (Type u) h).obj B₀) hfg)).hom
    have he : eBjX.hom ≫ eB.inv = r := by
      simp [eBjX, r, Category.assoc]
    have he' (z : ((TopCat.Sheaf.pullback (Type u) fK).obj Bj).presheaf.obj (op W)) :
        eB.inv.hom.app (op W) (eBjX.hom.hom.app (op W) z) =
        r.hom.app (op W) z :=
      congrArg (fun m : (TopCat.Sheaf.pullback (Type u) fK).obj Bj ⟶
          (TopCat.Sheaf.pullback (Type u) f).obj B₀ => m.hom.app (op W) z) he
    let P := (TopCat.Sheaf.pullback (Type u) f).obj B₀
    let sG : ((TopCat.Sheaf.pullback (Type u) g).obj B₀).presheaf.obj (op (Vj b)) :=
      (asIso (pullbackToGerm g B₀)).inv.hom.app (op (Vj b)) (ψK b (t, which))
    let z : ((TopCat.Sheaf.pullback (Type u) fK).obj Bj).presheaf.obj (op W) :=
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) fK).unit.app Bj).hom.app
        (op (Vj b)))
        (ejB.hom.hom.app (op (Vj b)) sG)
    have hfirst := congrArg (fun ξ : P.presheaf.obj (op W) =>
      (stalkPullbackSheafIso f B₀ x.1).hom
        (P.presheaf.germ (V b) x.1 x.2
          (cast (congrArg (fun U : Opens X => P.presheaf.obj (op U)) (hVj b)) ξ)))
      (he' z)
    refine hfirst.trans ?_
    rw [presheaf_germ_cast _ (hVj b)]
    have hcancel : ejB.inv.hom.app (op (Vj b))
        (ejB.hom.hom.app (op (Vj b)) sG) = sG :=
      sheaf_iso_hom_inv_apply ejB (Vj b) sG
    have hnat : ((TopCat.Sheaf.pullback (Type u) fK).map ejB.inv).hom.app
        (op W) z =
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) fK).unit.app
        ((TopCat.Sheaf.pullback (Type u) g).obj B₀)).hom.app
          (op (Vj b))) sG := by
      calc
        _ = (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) fK).unit.app
            ((TopCat.Sheaf.pullback (Type u) g).obj B₀)).hom.app
              (op (Vj b)))
              (ejB.inv.hom.app (op (Vj b))
                (ejB.hom.hom.app (op (Vj b)) sG)) :=
          pullback_unit_naturality_apply fK ejB.inv (Vj b)
            (ejB.hom.hom.app (op (Vj b)) sG)
        _ = _ := congrArg _ hcancel
    let eEq : (TopCat.Sheaf.pullback (Type u) (fK ≫ g)).obj B₀ ≅ P :=
      eqToIso (congrArg
        (fun h : TopCat.of X ⟶ E.obj i =>
          (TopCat.Sheaf.pullback (Type u) h).obj B₀) hfg)
    have hr : r.hom.app (op W) z =
        eEq.hom.hom.app (op W)
          ((((sheafPullbackCompIso fK g (Type u)).app B₀).inv).hom.app (op W)
            (((TopCat.Sheaf.pullback (Type u) fK).map ejB.inv).hom.app (op W) z)) :=
      rfl
    rw [hr, hnat]
    let τ : ((TopCat.Sheaf.pullback (Type u) (fK ≫ g)).obj B₀).presheaf.obj
        (op W) :=
      (((sheafPullbackCompIso fK g (Type u)).app B₀).inv).hom.app (op W)
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) fK).unit.app
          ((TopCat.Sheaf.pullback (Type u) g).obj B₀)).hom.app
            (op (Vj b))) sG)
    have hxW : x.1 ∈ W := by
      show x.1 ∈ (Opens.map fK).obj (Vj b)
      rw [hVj b]
      exact x.2
    rw [stalkPullbackSheafIso_eq_germ hfg B₀ W x.1 hxW τ]
    let Q := (TopCat.Sheaf.pullback (Type u) g).obj B₀
    let aSt : ((TopCat.Sheaf.pullback (Type u) fK).obj Q).presheaf.stalk x.1 :=
      ((TopCat.Sheaf.pullback (Type u) fK).obj Q).presheaf.germ W x.1 hxW
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) fK).unit.app Q).hom.app
          (op (Vj b)) sG)
    have hxj : fK x.1 ∈ Vj b := hxW
    have hψ : (pullbackToGerm g B₀).hom.app (op (Vj b)) sG =
        ψK b (t, which) :=
      sheaf_iso_hom_inv_apply (asIso (pullbackToGerm g B₀)).symm (Vj b) _
    have hcomp0 :
        (stalkPullbackSheafIso (fK ≫ g) B₀ x.1).hom
          (((TopCat.Sheaf.pullback (Type u) (fK ≫ g)).obj B₀).presheaf.germ
            W x.1 hxW τ) =
        germPullback_eval (ConcreteCategory.hom g) B₀.presheaf
          (ψK b (t, which)) ⟨fK x.1, hxj⟩ := by
      let u := (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) fK).unit.app
        Q).hom.app (op (Vj b))) sG
      have hm := TopCat.Presheaf.stalkFunctor_map_germ_apply W x.1 hxW
        (((sheafPullbackCompIso fK g (Type u)).app B₀).inv).hom u
      calc
        _ = (stalkPullbackSheafIso (fK ≫ g) B₀ x.1).hom
            ((TopCat.Presheaf.stalkFunctor (Type u) x.1).map
              (((sheafPullbackCompIso fK g (Type u)).app B₀).inv).hom aSt) :=
          congrArg _ hm.symm
        _ = (stalkPullbackSheafIso g B₀ (fK x.1)).hom
            ((stalkPullbackSheafIso fK Q x.1).hom aSt) :=
          stalkPullbackSheafIso_comp fK g B₀ x.1 aSt
        _ = (stalkPullbackSheafIso g B₀ (fK x.1)).hom
            (Q.presheaf.germ (Vj b) (fK x.1) hxj sG) :=
          congrArg _ (stalkPullbackSheafIso_unit fK Q x.1 (Vj b) hxj sG)
        _ = _ := by
          rw [← hψ]
          exact (pullbackToGerm_eval g B₀ sG ⟨fK x.1, hxj⟩).symm
    have hcast := congrArg
      (fun ξ : B₀.presheaf.stalk ((fK ≫ g) x.1) =>
        cast (congrArg (fun k : TopCat.of X ⟶ E.obj i =>
          B₀.presheaf.stalk (k x.1)) hfg) ξ) hcomp0
    refine hcast.trans ?_
    let W' : Opens X :=
      ⟨(fun a : X => q a) ⁻¹' (D.limPre (Vi' b) : Set D.invLimit),
        (D.limPre (Vi' b)).isOpen.preimage q.continuous⟩
    have hxW' : x.1 ∈ W' := by
      show x.1 ∈ (⟨(fun a : X => q a) ⁻¹' (D.limPre (Vi' b) : Set D.invLimit),
        (D.limPre (Vi' b)).isOpen.preimage q.continuous⟩ : Opens X)
      rw [hWb b]
      exact x.2
    let z' : W' := ⟨x.1, hxW'⟩
    have hcv := germPullback_eval_comap
      (g := ConcreteCategory.hom g) (g' := ConcreteCategory.hom f)
      (h := ConcreteCategory.hom fK) fK.hom.continuous
      (fun a : X => D.projFun_eq_mapFun K.hom (q a)) B₀.presheaf
      (W := Vj b) (W' := W')
      (fun a : W' => D.proj_mem (Vi' b)
        (⟨q a.1, a.2⟩ : D.limPre (Vi' b)))
      (ψK b (t, which)) z'
    exact hcv.symm
  let : IsIso (pullbackToGerm f B₀) := Stacks.GermPullbackComparison.pullbackToGerm_isIso f B₀
  have hbridge (b : Fin m) (t : T b) (which : Bool) :
      cast (congrArg (fun W : Opens X => Bₓ.presheaf.obj (op W)) (hVj b))
        (eBjX.hom.hom.app (op ((Opens.map fK).obj (Vj b)))
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) fK).unit.app Bj).hom.app
            (op (Vj b))
            (ejB.hom.hom.app (op (Vj b))
              ((asIso (pullbackToGerm g B₀)).inv.hom.app (op (Vj b))
                (ψK b (t, which)))))) =
      (extendedConstantHomSections (TopCat.of X) (V b) (T b) Bₓ)
        (Sigma.ι (fun c => extendedConstantSheaf (V c) (T c)) b ≫
          (if which then β else γ)) t :=
    injective_app_of_isIso eB.inv (V b)
      (injective_app_of_isIso (pullbackToGerm f B₀) (V b)
        ((hmodel b t which).trans (hsection b t which)))
  have hmapgen (b : Fin m) (t : T b) (which : Bool) :
      (extendedConstantHomSections (TopCat.of X) (V b) (T b) Bₓ)
        (Sigma.ι (fun c => extendedConstantSheaf (V c) (T c)) b ≫
          (if which then βK else γK)) t =
      (extendedConstantHomSections (TopCat.of X) (V b) (T b) Bₓ)
        (Sigma.ι (fun c => extendedConstantSheaf (V c) (T c)) b ≫
          (if which then β else γ)) t := by
    rw [hgen b which, extendedConstantHomSections_eq (TopCat.of X) (hVj b) (T b) Bₓ
      ((pullback_extendedConstant_iso fK (Vj b) (T b)).inv ≫
        (TopCat.Sheaf.pullback (Type u) fK).map (stageMap b which) ≫ eBjX.hom) t,
      ← Category.assoc, extendedConstantHomSections_naturality (TopCat.of X)
        ((Opens.map fK).obj (Vj b)) (T b)
        ((pullback_extendedConstant_iso fK (Vj b) (T b)).inv ≫
          (TopCat.Sheaf.pullback (Type u) fK).map (stageMap b which)) eBjX.hom t,
      extendedConstantHomSections_pullback fK (Vj b) (T b) Bj (stageMap b which) t]
    simpa only [stageMap, Equiv.apply_symm_apply] using hbridge b t which
  obtain ⟨hβK, hγK⟩ : βK = β ∧ γK = γ := by
    constructor <;> refine Sigma.hom_ext _ _ fun b => ?_ <;>
      refine (extendedConstantHomSections (TopCat.of X) (V b) (T b) Bₓ).injective
        (funext fun t => ?_)
    exacts [hmapgen b t true, hmapgen b t false]
  have hβconj : eAjX.hom ≫ β =
      (TopCat.Sheaf.pullback (Type u) fK).map βj ≫ eBjX.hom := by
    simpa only [βK, Category.assoc, eAjX.hom_inv_id_assoc] using
      (congrArg (fun m : Aₓ ⟶ Bₓ => eAjX.hom ≫ m) hβK).symm
  have hγconj : eAjX.hom ≫ γ =
      (TopCat.Sheaf.pullback (Type u) fK).map γj ≫ eBjX.hom := by
    simpa only [γK, Category.assoc, eAjX.hom_inv_id_assoc] using
      (congrArg (fun m : Aₓ ⟶ Bₓ => eAjX.hom ≫ m) hγK).symm
  let eQ : (TopCat.Sheaf.pullback (Type u) fK).obj G ≅ F :=
    (pullback_coequalizer_iso fK βj γj).symm ≪≫
      coequalizerIsoOfConjugate
        ((TopCat.Sheaf.pullback (Type u) fK).map βj)
        ((TopCat.Sheaf.pullback (Type u) fK).map γj)
        β γ eAjX eBjX hβconj hγconj ≪≫ hcoeq
  exact ⟨E.obj K.left, inferInstance, inferInstance, inferInstance, inferInstance,
    fK, G, hfK, hG, ⟨eQ⟩⟩

end Stacks

end
