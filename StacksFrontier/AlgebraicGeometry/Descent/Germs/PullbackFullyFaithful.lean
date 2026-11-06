module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackFullyFaithful.BaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.PullbackSquare

/-!
# Full faithfulness of pullback for descent data

Pullback of descent data along a single fpqc covering of the source, over a fixed base scheme,
is fully faithful.

## Main results

* `AlgebraicGeometry.pullbackFunctor_fullyFaithful_of_fpqc` gives full faithfulness of pullback
  of descent data along an fpqc covering.

## Implementation notes

The pullback functor is specified by `AlgebraicGeometry.DescentData.PullbackFunctor`, so the
result applies to any functor with that structure, in particular to
`AlgebraicGeometry.DescentData.pullbackFunctor`. The equality of the two base schemes is
expressed by taking the lower horizontal arrow of the square to be the identity of `S`.

An fpqc covering is an effective epimorphism, because the fpqc topology is subcanonical, and it
stays one after base change. Faithfulness is therefore descent of equality of morphisms along
the covering, and fullness produces the descended morphism as the unique map through which the
pulled-back morphism factors. That the descended map is compatible with the gluing
isomorphisms uses the diagonal identity `gluingPullback_diagonal_snd`: on the diagonal of
`V ×_S X` the gluing isomorphism of a descent datum acts as the identity, which is what the
cocycle condition gives for a single-member family.

## References

* [Stacks Project, Tag 0241](https://stacks.math.columbia.edu/tag/0241)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

private lemma fpqcEffectiveEpi
    {X X' : Scheme.{u}} (f : X' ⟶ X)
    (hcover : Presieve.singleton f ∈ Scheme.fpqcPrecoverage X) :
    EffectiveEpi f := by
  rw [← Sieve.effectiveEpimorphic_singleton,
    Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
  intro Z
  exact (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := Scheme.fpqcTopology) (yoneda.obj Z)).isSheafFor _
      (Precoverage.generate_mem_toGrothendieck hcover)

private lemma fpqcPullbackCover
    {X X' V : Scheme.{u}} (f : X' ⟶ X) (p : V ⟶ X)
    (hcover : Presieve.singleton f ∈ Scheme.fpqcPrecoverage X) :
    Presieve.singleton (pullback.fst p f) ∈ Scheme.fpqcPrecoverage V := by
  rw [← Presieve.ofArrows_pUnit.{0}]
  exact Precoverage.mem_coverings_of_isPullback
    (fun _ : PUnit.{1} ↦ f) (by rw [Presieve.ofArrows_pUnit.{0}]; exact hcover) p
    (fun _ ↦ pullback.fst p f) (fun _ ↦ pullback.snd p f) fun _ ↦ IsPullback.of_hasPullback p f

/-- The composite of two single-arrow fpqc coverings is an fpqc covering. -/
private lemma fpqcSingleton_comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Presieve.singleton f ∈ Scheme.fpqcPrecoverage Y)
    (hg : Presieve.singleton g ∈ Scheme.fpqcPrecoverage Z) :
    Presieve.singleton (f ≫ g) ∈ Scheme.fpqcPrecoverage Z := by
  let : Unique (Σ _ : PUnit.{1}, PUnit.{1}) := {
    default := ⟨PUnit.unit, PUnit.unit⟩
    uniq := by intro x; cases x with | mk i j => cases i; cases j; rfl }
  have hc := Scheme.fpqcPrecoverage.comp_mem_coverings
    (fun _ : PUnit.{1} ↦ g) (by simpa only [← Presieve.ofArrows_pUnit.{0}] using hg)
    (fun _ : PUnit.{1} ↦ fun _ : PUnit.{1} ↦ f)
    (fun _ ↦ by simpa only [← Presieve.ofArrows_pUnit.{0}] using hf)
  rw [Presieve.ofArrows_of_unique] at hc
  simpa using hc

/-- Precomposing a single-arrow fpqc covering with an isomorphism gives an fpqc covering. -/
private lemma fpqcSingleton_isIso_comp {X Y Z : Scheme.{u}} (e : X ⟶ Y) [IsIso e] {g : Y ⟶ Z}
    (hg : Presieve.singleton g ∈ Scheme.fpqcPrecoverage Z) :
    Presieve.singleton (e ≫ g) ∈ Scheme.fpqcPrecoverage Z :=
  fpqcSingleton_comp (Precoverage.mem_coverings_of_isIso _) hg

private lemma fpqcPullbackEffectiveEpi
    {X X' V : Scheme.{u}} (f : X' ⟶ X) (p : V ⟶ X)
    (hcover : Presieve.singleton f ∈ Scheme.fpqcPrecoverage X) :
    EffectiveEpi (pullback.fst p f) :=
  fpqcEffectiveEpi _ (fpqcPullbackCover f p hcover)

private lemma gluingIso_hom_left
    {S X : Scheme.{u}} {a : X ⟶ S}
    (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)) :
    Over.Hom.left (D.gluingIso () ()).hom =
      Over.Hom.left ((D.gluing () ()).hom.left) := by
  rfl

private lemma gluing_diagonal
    {S X : Scheme.{u}} (a : X ⟶ S)
    (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)) :
  prod.lift (𝟙 ((Over.map a).obj (D.obj ())))
      (structureMap a (D.obj ())) ≫
        (D.gluing () ()).hom.left =
      prod.lift (structureMap a (D.obj ()))
        (𝟙 ((Over.map a).obj (D.obj ()))) := by
  apply prod.hom_ext
  · simp [DescentData.gluing_hom_fst]
  · let δ := prod.lift (𝟙 ((Over.map a).obj (D.obj ())))
        (structureMap a (D.obj ()))
    let φ := (D.gluing () ()).hom.left
    let β := δ ≫ φ ≫ prod.snd
    let d : ((Over.map a).obj (D.obj ())) ⟶
        (((Over.map a).obj (D.obj ()) ⨯ Over.mk a) ⨯ Over.mk a) :=
      prod.lift (prod.lift (𝟙 _) (structureMap a (D.obj ())))
        (structureMap a (D.obj ()))
    have hc := congrArg (fun q => d ≫ q) (D.cocycle () () ())
    have hp := congrArg (fun q => q ≫ prod.snd) hc
    simp only [Over.mk_left, prodMapLastTwo, prod.associator_hom, prod.associator_inv,
      prod.comp_lift, prod.map_fst, Category.comp_id, prod.map_snd_assoc,
      DescentData.gluing_hom_fst, limit.lift_π, BinaryFan.mk_pt, BinaryFan.mk_fst,
      limit.lift_π_assoc, pair_obj_right, BinaryFan.mk_snd, pair_obj_left, Category.assoc,
      prod.map_fst_assoc, DescentData.gluing_hom_snd_structureMap, Category.id_comp,
      prod.lift_map_assoc, prodMapFirstThird, prod.braiding_hom, prod.map_snd, d] at hp
    have hβbase : β ≫ structureMap a (D.obj ()) =
        structureMap a (D.obj ()) := by
      have hh : φ ≫ prod.snd ≫ structureMap a (D.obj ()) = prod.snd := by
        simp [φ]
      show δ ≫ φ ≫ prod.snd ≫ structureMap a (D.obj ()) = _
      rw [hh]
      simp [δ]
    have hleft :
        prod.lift (δ ≫ φ) (structureMap a (D.obj ())) ≫
            prod.lift (prod.fst ≫ prod.snd) prod.snd = β ≫ δ := by
      apply prod.hom_ext
      · simp [Category.assoc, β, δ]
      · simp [Category.assoc, β, δ, hβbase]
    have hright :
        d ≫ prod.lift (prod.fst ≫ prod.fst) prod.snd = δ := by
      apply prod.hom_ext <;> simp [d, δ]
    have hleft' := congrArg (fun m => m ≫ φ ≫ prod.snd) hleft
    have hright' := congrArg (fun m => m ≫ φ ≫ prod.snd) hright
    dsimp [δ, φ, β] at hleft' hright'
    simp only [Category.assoc] at hleft' hright'
    rw [hleft', hright'] at hp
    have hβidem : β ≫ β = β := by
      simpa [β, δ] using hp
    let δ' := prod.lift (structureMap a (D.obj ()))
      (𝟙 ((Over.map a).obj (D.obj ())))
    let φinv := (D.gluing () ()).inv.left
    have hdiag : δ ≫ φ = β ≫ δ' := by
      apply prod.hom_ext
      · calc
          δ ≫ φ ≫ prod.fst = δ ≫ prod.fst ≫ structureMap a (D.obj ()) := by
            rw [DescentData.gluing_hom_fst]
          _ = structureMap a (D.obj ()) := by simp [δ]
          _ = β ≫ structureMap a (D.obj ()) := hβbase.symm
          _ = β ≫ δ' ≫ prod.fst := by simp [δ']
      · simp [β, δ, δ']
    have hmove : δ ≫ φ ≫ prod.snd ≫ δ' = δ ≫ φ := by
      calc
        _ = β ≫ δ' := rfl
        _ = δ ≫ φ := hdiag.symm
    have hmove' := congrArg (fun m => m ≫ φinv ≫ prod.fst) hmove
    let γ := δ' ≫ φinv ≫ prod.fst
    have hβγ : β ≫ γ = 𝟙 ((Over.map a).obj (D.obj ())) := by
      dsimp [β, γ]
      calc
        _ = δ ≫ φ ≫ prod.snd ≫ δ' ≫ φinv ≫ prod.fst := rfl
        _ = δ ≫ φ ≫ φinv ≫ prod.fst := by
          simpa only [Category.assoc] using hmove'
        _ = δ ≫ prod.fst := by simp [φ, φinv]
        _ = 𝟙 _ := by simp [δ]
    have hβid : β = 𝟙 ((Over.map a).obj (D.obj ())) := by
      calc
        β = β ≫ 𝟙 _ := by simp
        _ = β ≫ (β ≫ γ) := by rw [hβγ]
        _ = (β ≫ β) ≫ γ := by simp only [Category.assoc]
        _ = β ≫ γ := by rw [hβidem]
        _ = 𝟙 _ := hβγ
    simpa [β, δ, δ'] using hβid

private lemma gluingPullback_diagonal_snd
    {S X : Scheme.{u}} (a : X ⟶ S)
    (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a))
    {Z : Scheme.{u}} (d : Z ⟶ (D.obj ()).left) :
    pullback.lift d (d ≫ (D.obj ()).hom) (by simp [Category.assoc]) ≫
      (D.gluingPullbackIso () ()).hom ≫ pullback.snd _ _ = d := by
  let δ := prod.lift (𝟙 ((Over.map a).obj (D.obj ())))
    (structureMap a (D.obj ()))
  let δ' := prod.lift (structureMap a (D.obj ()))
    (𝟙 ((Over.map a).obj (D.obj ())))
  let s := Over.prodLeftIsoPullback ((Over.map a).obj (D.obj ())) (Over.mk a)
  let t := Over.prodLeftIsoPullback (Over.mk a) ((Over.map a).obj (D.obj ()))
  have hδfst : δ.left ≫ (prod.fst (X := (Over.map a).obj (D.obj ()))).left =
      𝟙 ((D.obj ()).left) :=
    congrArg Over.Hom.left
      (prod.lift_fst (𝟙 ((Over.map a).obj (D.obj ())))
        (structureMap a (D.obj ())))
  have hδsnd : δ.left ≫ (prod.snd (X := (Over.map a).obj (D.obj ()))).left =
      (D.obj ()).hom :=
    congrArg Over.Hom.left
      (prod.lift_snd (𝟙 ((Over.map a).obj (D.obj ())))
        (structureMap a (D.obj ())))
  have hsrc : pullback.lift d (d ≫ (D.obj ()).hom) (by simp [Category.assoc]) =
      d ≫ δ.left ≫ s.hom := by
    apply pullback.hom_ext
    · dsimp only [s]
      show pullback.lift d (d ≫ (D.obj ()).hom) _ ≫ pullback.fst _ _ =
        d ≫ δ.left ≫ (((Over.map a).obj (D.obj ())).prodLeftIsoPullback
          (Over.mk a)).hom ≫ pullback.fst _ _
      rw [Over.prodLeftIsoPullback_hom_fst, pullback.lift_fst]
      simp [hδfst]
    · dsimp only [s]
      show pullback.lift d (d ≫ (D.obj ()).hom) _ ≫ pullback.snd _ _ =
        d ≫ δ.left ≫ (((Over.map a).obj (D.obj ())).prodLeftIsoPullback
          (Over.mk a)).hom ≫ pullback.snd _ _
      rw [Over.prodLeftIsoPullback_hom_snd, pullback.lift_snd]
      simp [hδsnd]
  have hfirst : pullback.lift d (d ≫ (D.obj ()).hom) (by simp [Category.assoc]) ≫
      (D.gluingPullbackIso () ()).hom ≫ pullback.snd _ _ =
      d ≫ δ.left ≫ (D.gluingIso () ()).hom.left ≫ t.hom ≫ pullback.snd _ _ := by
    have hcomp := congrArg
      (fun k => k ≫ s.inv ≫ ((Over.forget S).mapIso (D.gluingIso () ())).hom ≫
        t.hom ≫ pullback.snd _ _) hsrc
    simpa [DescentData.gluingPullbackIso, s, t, Category.assoc] using hcomp
  have hdiag : δ.left ≫ (D.gluingIso () ()).hom.left = δ'.left := by
    simpa [DescentData.gluingIso] using
      congrArg Over.Hom.left (gluing_diagonal a D)
  calc
    _ = d ≫ δ.left ≫ (D.gluingIso () ()).hom.left ≫ t.hom ≫ pullback.snd _ _ := hfirst
    _ = d ≫ δ'.left ≫ t.hom ≫ pullback.snd _ _ :=
      congrArg (fun k => d ≫ k ≫ t.hom ≫ pullback.snd _ _) hdiag
    _ = d := by
      have hδ'snd : δ'.left ≫ (prod.snd (X := Over.mk a)).left =
          𝟙 ((D.obj ()).left) :=
        congrArg Over.Hom.left
          (prod.lift_snd (structureMap a (D.obj ()))
            (𝟙 ((Over.map a).obj (D.obj ()))))
      dsimp only [t]
      rw [Over.prodLeftIsoPullback_hom_snd]
      simpa [Category.assoc] using congrArg (fun k => d ≫ k) hδ'snd

/-- Under the identifications `Over.prodLeftIsoPullback` of binary products in `Over S` with
fibre products over `S`, the underlying morphism of `prod.map a b` is `pullback.map` of `a.left`
and `b.left`. -/
alias prodMap_left := DescentData.prodMap_left

/-- The morphism `V ×_S X ⟶ W ×_S X` induced by a morphism `u : V ⟶ W` over `X`, where `V` and
`W` lie over `S` through `a`. -/
abbrev sourcePullbackMap {S X : Scheme.{u}} (a : X ⟶ S)
    {V W : Over X} (u : V ⟶ W) :
    pullback (V.hom ≫ a) a ⟶ pullback (W.hom ≫ a) a :=
  pullback.map _ _ _ _ u.left (𝟙 X)
    (𝟙 S)
    (by simp) (by simp)

/-- The morphism `X ×_S V ⟶ X ×_S W` induced by a morphism `u : V ⟶ W` over `X`, where `V` and
`W` lie over `S` through `a`. -/
abbrev targetPullbackMap {S X : Scheme.{u}} (a : X ⟶ S)
    {V W : Over X} (u : V ⟶ W) :
  pullback a (V.hom ≫ a) ⟶ pullback a (W.hom ≫ a) :=
  pullback.map _ _ _ _ (𝟙 X) u.left (𝟙 S) (by simp)
    (by simp)

/-- `sourcePullbackMap a u` followed by the first projection is the first projection followed
by `u.left`. -/
lemma sourcePullbackMap_fst {S X : Scheme.{u}} (a : X ⟶ S)
    {V W : Over X} (u : V ⟶ W) :
    sourcePullbackMap a u ≫ pullback.fst (W.hom ≫ a) a =
      pullback.fst (V.hom ≫ a) a ≫ u.left := by
  dsimp [sourcePullbackMap, pullback.map]
  exact pullback.lift_fst _ _ _

/-- `sourcePullbackMap a u` commutes with the second projections to `X`. -/
lemma sourcePullbackMap_snd {S X : Scheme.{u}} (a : X ⟶ S)
    {V W : Over X} (u : V ⟶ W) :
    sourcePullbackMap a u ≫ pullback.snd (W.hom ≫ a) a =
      pullback.snd (V.hom ≫ a) a := by
  dsimp [sourcePullbackMap, pullback.map]
  exact pullback.lift_snd _ _ _

/-- `targetPullbackMap a u` commutes with the first projections to `X`. -/
lemma targetPullbackMap_fst {S X : Scheme.{u}} (a : X ⟶ S)
    {V W : Over X} (u : V ⟶ W) :
    targetPullbackMap a u ≫ pullback.fst a (W.hom ≫ a) =
      pullback.fst a (V.hom ≫ a) := by
  dsimp [targetPullbackMap, pullback.map]
  exact pullback.lift_fst _ _ _

/-- `targetPullbackMap a u` followed by the second projection is the second projection followed
by `u.left`. -/
lemma targetPullbackMap_snd {S X : Scheme.{u}} (a : X ⟶ S)
    {V W : Over X} (u : V ⟶ W) :
    targetPullbackMap a u ≫ pullback.snd a (W.hom ≫ a) =
      pullback.snd a (V.hom ≫ a) ≫ u.left := by
  dsimp [targetPullbackMap, pullback.map]
  exact pullback.lift_snd _ _ _

/-- `sourcePullbackMap` in terms of `prod.map` in `Over S`. -/
private lemma sourcePullbackMap_eq_prodMap {S X : Scheme.{u}} (a : X ⟶ S)
    {V W : Over X} (u : V ⟶ W) :
    sourcePullbackMap a u =
      (Over.prodLeftIsoPullback ((Over.map a).obj V) (Over.mk a)).inv ≫
        (prod.map ((Over.map a).map u) (𝟙 (Over.mk a))).left ≫
        (Over.prodLeftIsoPullback ((Over.map a).obj W) (Over.mk a)).hom := by
  simpa [sourcePullbackMap] using (prodMap_left ((Over.map a).map u) (𝟙 (Over.mk a))).symm

/-- `targetPullbackMap` in terms of `prod.map` in `Over S`. -/
private lemma targetPullbackMap_eq_prodMap {S X : Scheme.{u}} (a : X ⟶ S)
    {V W : Over X} (u : V ⟶ W) :
    targetPullbackMap a u =
      (Over.prodLeftIsoPullback (Over.mk a) ((Over.map a).obj V)).inv ≫
        (prod.map (𝟙 (Over.mk a)) ((Over.map a).map u)).left ≫
        (Over.prodLeftIsoPullback (Over.mk a) ((Over.map a).obj W)).hom := by
  simpa [targetPullbackMap] using (prodMap_left (𝟙 (Over.mk a)) ((Over.map a).map u)).symm

/-- The gluing isomorphisms `gluingPullbackIso` are natural in a morphism `g : D ⟶ E` of descent
data: they intertwine `sourcePullbackMap` and `targetPullbackMap` of `g.hom ()`. -/
lemma gluingPullback_comm
    {S X : Scheme.{u}} {a : X ⟶ S}
    {D E : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)}
    (g : D ⟶ E) :
    sourcePullbackMap a (g.hom ()) ≫ (E.gluingPullbackIso () ()).hom =
      (D.gluingPullbackIso () ()).hom ≫ targetPullbackMap a (g.hom ()) := by
  let sD := Over.prodLeftIsoPullback ((Over.map a).obj (D.obj ())) (Over.mk a)
  let sE := Over.prodLeftIsoPullback ((Over.map a).obj (E.obj ())) (Over.mk a)
  let tD := Over.prodLeftIsoPullback (Over.mk a) ((Over.map a).obj (D.obj ()))
  let tE := Over.prodLeftIsoPullback (Over.mk a) ((Over.map a).obj (E.obj ()))
  have hs := sourcePullbackMap_eq_prodMap a (g.hom ())
  have ht := targetPullbackMap_eq_prodMap a (g.hom ())
  have hcomm := g.comm () ()
  have h' := congrArg (fun k => sD.inv ≫ k ≫ tE.hom)
    (congrArg Over.Hom.left hcomm)
  simpa [hs, ht, sD, sE, tD, tE,
    DescentData.gluingPullbackIso,
    DescentData.gluingIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Over.forget_map, Over.comp_left,
    Category.assoc] using h'

private lemma sourceMap_epi
    {S X X' : Scheme.{u}} {a : X ⟶ S} {a' : X' ⟶ S} {f : X' ⟶ X}
    {comm : f ≫ a = a' ≫ (𝟙 S)}
    (P : DescentData.PullbackFunctor a a' (𝟙 S) f comm)
    (hcover : Presieve.singleton f ∈ Scheme.fpqcPrecoverage X)
    (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)) :
    Epi (P.sourceMap D) := by
  let D' (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)) :=
    P.functor.obj D
  let eD (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)) :=
    P.objIso D
  let coverMap := pullback.fst (D.obj ()).hom f
  let u := (eD D).hom.left ≫ pullback.fst (D.obj ()).hom f
  let b := (D.obj ()).hom ≫ a
  let b' := ((D' D).obj ()).hom ≫ a'
  let T := pullback b a
  let U := pullback b a'
  let Q := pullback b' a'
  have hucov : Presieve.singleton u ∈ Scheme.fpqcPrecoverage (D.obj ()).left := by
    let : IsIso (eD D).hom.left := (Over.forget X').mapIso (eD D) |>.isIso_hom
    exact fpqcSingleton_isIso_comp _ (fpqcPullbackCover f (D.obj ()).hom hcover)
  have hucompat : u ≫ b = b' := by
    dsimp [u, b, b']
    have hw : (eD D).hom.left ≫ pullback.snd (D.obj ()).hom f =
        ((D' D).obj ()).hom := by
      simpa only [Over.pullback_obj_hom] using Over.w (eD D).hom
    calc
      _ = (eD D).hom.left ≫ (pullback.fst (D.obj ()).hom f ≫
            (D.obj ()).hom) ≫ a := by simp only [Category.assoc]
      _ = (eD D).hom.left ≫ (pullback.snd (D.obj ()).hom f ≫ f) ≫ a := by
        rw [pullback.condition]
      _ = (eD D).hom.left ≫ pullback.snd (D.obj ()).hom f ≫ f ≫ a := by
        simp only [Category.assoc]
      _ = ((D' D).obj ()).hom ≫ a' := by
        calc
          _ = ((eD D).hom.left ≫ pullback.snd (D.obj ()).hom f) ≫ (f ≫ a) := by
            simp only [Category.assoc]
          _ = ((D' D).obj ()).hom ≫ (f ≫ a) := by rw [hw]
          _ = ((D' D).obj ()).hom ≫ a' := by
            have hfa : f ≫ a = a' := by simpa using comm
            exact congrArg (fun k => ((D' D).obj ()).hom ≫ k) hfa
  let r₁ := pullbackRightPullbackFstIso b a' u
  let c₁ : pullback (u ≫ b) a' ≅ pullback b' a' :=
    pullback.congrHom hucompat rfl
  let i₁ := c₁.symm ≪≫ r₁.symm
  let q₁ := i₁.hom ≫ pullback.snd u (pullback.fst b a')
  have hq₁fst : q₁ ≫ pullback.fst b a' = pullback.fst b' a' ≫ u := by
    show (c₁.inv ≫ (pullbackRightPullbackFstIso b a' u).inv) ≫
      pullback.snd u (pullback.fst b a') ≫ pullback.fst b a' = _
    calc
      _ = c₁.inv ≫ ((pullbackRightPullbackFstIso b a' u).inv ≫
          pullback.snd u (pullback.fst b a') ≫ pullback.fst b a') := by
        simp only [Category.assoc]
      _ = c₁.inv ≫ (pullback.fst (u ≫ b) a' ≫ u) := by
        rw [pullbackRightPullbackFstIso_inv_snd_fst]
      _ = pullback.fst b' a' ≫ u := by
        have hfst : c₁.inv ≫ pullback.fst (u ≫ b) a' =
            pullback.fst b' a' := by
          dsimp only [c₁]
          rw [pullback.congrHom_inv hucompat rfl]
          dsimp [pullback.map]
          rw [pullback.lift_fst]
          simp
        exact congrArg (fun k => k ≫ u) hfst
  have hq₁snd : q₁ ≫ pullback.snd b a' = pullback.snd b' a' := by
    show (c₁.inv ≫ (pullbackRightPullbackFstIso b a' u).inv) ≫
      pullback.snd u (pullback.fst b a') ≫ pullback.snd b a' = _
    calc
      _ = c₁.inv ≫ ((pullbackRightPullbackFstIso b a' u).inv ≫
          pullback.snd u (pullback.fst b a') ≫ pullback.snd b a') := by
        simp only [Category.assoc]
      _ = c₁.inv ≫ pullback.snd (u ≫ b) a' := by
        rw [pullbackRightPullbackFstIso_inv_snd_snd]
      _ = pullback.snd b' a' := by
        dsimp only [c₁]
        rw [pullback.congrHom_inv hucompat rfl]
        dsimp [pullback.map]
        rw [pullback.lift_snd]
        simp
  have hq₁ : Presieve.singleton q₁ ∈ Scheme.fpqcPrecoverage U := by
    let : IsIso (pullbackSymmetry u (pullback.fst b a')).hom := Iso.isIso_hom _
    have hq₁base : Presieve.singleton (pullback.snd u (pullback.fst b a')) ∈
        Scheme.fpqcPrecoverage U := by
      simpa [pullbackSymmetry_hom_comp_fst] using fpqcSingleton_isIso_comp
        (pullbackSymmetry u (pullback.fst b a')).hom (fpqcPullbackCover u (pullback.fst b a') hucov)
    let : IsIso i₁.hom := Iso.isIso_hom i₁
    exact fpqcSingleton_isIso_comp i₁.hom hq₁base
  have hfa : f ≫ a = a' := by simpa using comm
  let r₂ := pullbackLeftPullbackSndIso b a f
  let c₂ : pullback b (f ≫ a) ≅ pullback b a' :=
    pullback.congrHom rfl hfa
  let i₂ := r₂ ≪≫ c₂
  let q₂ := i₂.inv ≫ pullback.fst (pullback.snd b a) f
  have hq₂fst : q₂ ≫ pullback.fst b a = pullback.fst b a' := by
    show (c₂.inv ≫ (pullbackLeftPullbackSndIso b a f).inv) ≫
      pullback.fst (pullback.snd b a) f ≫ pullback.fst b a = _
    calc
      _ = c₂.inv ≫ ((pullbackLeftPullbackSndIso b a f).inv ≫
          pullback.fst (pullback.snd b a) f ≫ pullback.fst b a) := by
        simp only [Category.assoc]
      _ = c₂.inv ≫ pullback.fst b (f ≫ a) := by
        rw [pullbackLeftPullbackSndIso_inv_fst]
      _ = pullback.fst b a' := by
        dsimp only [c₂]
        rw [pullback.congrHom_inv rfl hfa]
        dsimp [pullback.map]
        rw [pullback.lift_fst]
        simp
  have hq₂snd : q₂ ≫ pullback.snd b a = pullback.snd b a' ≫ f := by
    show (c₂.inv ≫ (pullbackLeftPullbackSndIso b a f).inv) ≫
      pullback.fst (pullback.snd b a) f ≫ pullback.snd b a = _
    calc
      _ = c₂.inv ≫ ((pullbackLeftPullbackSndIso b a f).inv ≫
          pullback.fst (pullback.snd b a) f ≫ pullback.snd b a) := by
        simp only [Category.assoc]
      _ = c₂.inv ≫ (pullback.snd b (f ≫ a) ≫ f) := by
        rw [pullbackLeftPullbackSndIso_inv_fst_snd]
      _ = pullback.snd b a' ≫ f := by
        have hproj : c₂.inv ≫ pullback.snd b (f ≫ a) =
            pullback.snd b a' := by
          dsimp only [c₂]
          rw [pullback.congrHom_inv rfl hfa]
          exact pullback.lift_snd _ _ _
        simpa only [Category.assoc] using congrArg (fun k => k ≫ f) hproj
  have hq₂ : Presieve.singleton q₂ ∈ Scheme.fpqcPrecoverage T := by
    let : IsIso i₂.inv := Iso.isIso_inv i₂
    exact fpqcSingleton_isIso_comp i₂.inv (fpqcPullbackCover f (pullback.snd b a) hcover)
  have hfactor : P.sourceMap D = q₁ ≫ q₂ := by
    apply pullback.hom_ext
    · calc
        _ = pullback.fst b' a' ≫ u := by
          simpa [u, b, b', coverMap, Category.assoc] using P.sourceMap_fst D
        _ = q₁ ≫ pullback.fst b a' := hq₁fst.symm
        _ = q₁ ≫ q₂ ≫ pullback.fst b a := by
          calc
            _ = q₁ ≫ (q₂ ≫ pullback.fst b a) :=
              congrArg (fun k => q₁ ≫ k) hq₂fst.symm
            _ = _ := (Category.assoc _ _ _).symm
    · calc
        _ = pullback.snd b' a' ≫ f := P.sourceMap_snd D
        _ = q₁ ≫ pullback.snd b a' ≫ f := by
          simpa only [Category.assoc] using congrArg (fun k => k ≫ f) hq₁snd.symm
        _ = q₁ ≫ q₂ ≫ pullback.snd b a := by
          calc
            _ = q₁ ≫ (q₂ ≫ pullback.snd b a) :=
              congrArg (fun k => q₁ ≫ k) hq₂snd.symm
            _ = _ := (Category.assoc _ _ _).symm
  have hsourceCover : Presieve.singleton (P.sourceMap D) ∈
      Scheme.fpqcPrecoverage T := by
    simpa [hfactor] using fpqcSingleton_comp hq₁ hq₂
  let : EffectiveEpi (P.sourceMap D) := fpqcEffectiveEpi _ hsourceCover
  infer_instance

private alias pullbackMap_snd := DescentData.pullbackMap_left_snd

/-- **Stacks Project, Tag 0241.** Pullback along an fpqc covering over a fixed
base scheme is fully faithful on descent data. -/
@[stacks 0241]
public theorem pullbackFunctor_fullyFaithful_of_fpqc
    {S X X' : Scheme.{u}} {a : X ⟶ S} {a' : X' ⟶ S} {f : X' ⟶ X}
    {comm : f ≫ a = a' ≫ (𝟙 S)}
    (P : DescentData.PullbackFunctor a a' (𝟙 S) f comm)
    (hcover : Presieve.singleton f ∈ Scheme.fpqcPrecoverage X) :
    Nonempty P.functor.FullyFaithful := by
  let D' (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)) :=
    P.functor.obj D
  let eD (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)) :=
    P.objIso D
  have eD_snd (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)) :
      (eD D).hom.left ≫ pullback.snd (D.obj ()).hom f = ((D' D).obj ()).hom := by
    simpa only [Over.pullback_obj_hom] using Over.w (eD D).hom
  have eD_inv_hom (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)) :
      (eD D).inv.left ≫ (eD D).hom.left = 𝟙 (pullback (D.obj ()).hom f) := by
    simpa only [Over.comp_left, Over.id_left, Over.pullback_obj_left] using
      congrArg Over.Hom.left (Iso.inv_hom_id (eD D))
  let localMap {D E : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)}
      (g : D' D ⟶ D' E) :=
    (eD D).inv.left ≫ (g.hom ()).left ≫ (eD E).hom.left ≫
      pullback.fst (E.obj ()).hom f
  let coverMap {D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)} :=
    pullback.fst (D.obj ()).hom f
  let descendMap {D E : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)}
      (g : D' D ⟶ D' E) : (D.obj ()).left ⟶ (E.obj ()).left := by
    let := fpqcPullbackEffectiveEpi f (D.obj ()).hom hcover
    exact EffectiveEpi.desc coverMap (localMap g) (by
      intro Z g₁ g₂ h
      change g₁ ≫ pullback.fst (D.obj ()).hom f =
        g₂ ≫ pullback.fst (D.obj ()).hom f at h
      have hcomp : g₁ ≫ pullback.fst (D.obj ()).hom f ≫ (D.obj ()).hom =
          g₂ ≫ pullback.fst (D.obj ()).hom f ≫ (D.obj ()).hom := by
        simpa only [Category.assoc] using
          congrArg (fun k => k ≫ (D.obj ()).hom) h
      have hbase : g₁ ≫ pullback.snd (D.obj ()).hom f ≫ f =
          g₂ ≫ pullback.snd (D.obj ()).hom f ≫ f := by
        calc
          _ = g₁ ≫ pullback.fst (D.obj ()).hom f ≫ (D.obj ()).hom := by
            rw [← pullback.condition]
          _ = g₂ ≫ pullback.fst (D.obj ()).hom f ≫ (D.obj ()).hom := hcomp
          _ = g₂ ≫ pullback.snd (D.obj ()).hom f ≫ f := by
            rw [pullback.condition]
      have hw := Over.w (eD D).inv
      let u₁ := g₁ ≫ (eD D).inv.left
      let u₂ := g₂ ≫ (eD D).inv.left
      let x₁ := g₁ ≫ pullback.snd (D.obj ()).hom f
      let x₂ := g₂ ≫ pullback.snd (D.obj ()).hom f
      have hu₁ : u₁ ≫ ((D' D).obj ()).hom = x₁ := by
        dsimp [u₁, x₁, D']
        simp [Over.pullback, Category.assoc]
      have hxa : x₁ ≫ a' = x₂ ≫ a' := by
        simpa [x₁, x₂, comm] using congrArg (fun q => q ≫ a) hbase
      have hq : u₁ ≫ ((D' D).obj ()).hom ≫ a' = x₂ ≫ a' := by
        rw [← Category.assoc, hu₁, hxa]
      let q := pullback.lift u₁ x₂ hq
      let d := g₁ ≫ pullback.fst (D.obj ()).hom f
      have hqfst : q ≫ pullback.fst (((D' D).obj ()).hom ≫ a') a' = u₁ := by
        dsimp [q]
        exact pullback.lift_fst u₁ x₂ hq
      have hqsnd : q ≫ pullback.snd (((D' D).obj ()).hom ≫ a') a' = x₂ := by
        dsimp [q]
        exact pullback.lift_snd u₁ x₂ hq
      have hpair : d ≫ (D.obj ()).hom = x₂ ≫ f := by
        dsimp [d, x₂]
        calc
          _ = g₁ ≫ pullback.snd (D.obj ()).hom f ≫ f := by
            rw [Category.assoc, pullback.condition]
          _ = g₂ ≫ pullback.snd (D.obj ()).hom f ≫ f := hbase
          _ = _ := rfl
      have hg₂ : g₂ = pullback.lift d x₂ hpair := by
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
          simpa [d] using h.symm
        · rw [pullback.lift_snd]
      have heiso := eD_inv_hom D
      have he₁fst : u₁ ≫ (eD D).hom.left ≫ pullback.fst (D.obj ()).hom f = d := by
        dsimp [u₁, d]
        calc
          _ = g₁ ≫ ((eD D).inv.left ≫ (eD D).hom.left) ≫
              pullback.fst (D.obj ()).hom f := by simp only [Category.assoc]
          _ = _ := by rw [heiso]; simp
      have he₁snd : u₁ ≫ (eD D).hom.left ≫ pullback.snd (D.obj ()).hom f = x₁ := by
        dsimp [u₁, x₁]
        calc
          _ = g₁ ≫ ((eD D).inv.left ≫ (eD D).hom.left) ≫
              pullback.snd (D.obj ()).hom f := by simp only [Category.assoc]
          _ = _ := by rw [heiso]; simp
      have hu₂ : u₂ ≫ ((D' D).obj ()).hom = x₂ := by
        dsimp [u₂, x₂, D']
        simp [Over.pullback, Category.assoc]
      have hsource : q ≫ P.sourceMap D =
          pullback.lift d (d ≫ (D.obj ()).hom) (by simp [Category.assoc]) := by
        apply pullback.hom_ext
        · calc
            q ≫ P.sourceMap D ≫ pullback.fst _ _ =
                q ≫ pullback.fst _ _ ≫ (eD D).hom.left ≫ pullback.fst _ _ := by
              simpa only [Category.assoc] using
                congrArg (fun k => q ≫ k) (P.sourceMap_fst D)
            _ = d := by
              simpa [Category.assoc] using
                congrArg (fun k => k ≫ (eD D).hom.left ≫ pullback.fst (D.obj ()).hom f)
                  hqfst |>.trans he₁fst
            _ = pullback.lift d (d ≫ (D.obj ()).hom) (by simp [Category.assoc]) ≫
                  pullback.fst _ _ := by rw [pullback.lift_fst]
        · calc
            q ≫ P.sourceMap D ≫ pullback.snd _ _ =
                q ≫ pullback.snd _ _ ≫ f := by
              simpa only [Category.assoc] using
                congrArg (fun k => q ≫ k) (P.sourceMap_snd D)
            _ = d ≫ (D.obj ()).hom := by
              simpa [Category.assoc] using
                (congrArg (fun k => k ≫ f) hqsnd).trans hpair.symm
            _ = pullback.lift d (d ≫ (D.obj ()).hom) (by simp [Category.assoc]) ≫
                  pullback.snd _ _ := by rw [pullback.lift_snd]
      have htransition_fst :
          q ≫ ((D' D).gluingPullbackIso () ()).hom ≫ pullback.snd _ _ ≫
            (eD D).hom.left ≫ pullback.fst (D.obj ()).hom f = d := by
        calc
          _ = q ≫ ((D' D).gluingPullbackIso () ()).hom ≫
              P.targetMap D ≫ pullback.snd _ _ := by
            simpa only [Category.assoc] using
              (congrArg (fun k => q ≫ ((D' D).gluingPullbackIso () ()).hom ≫ k)
                (P.targetMap_snd D)).symm
          _ = q ≫ P.sourceMap D ≫ (D.gluingPullbackIso () ()).hom ≫
              pullback.snd _ _ := by
            simpa only [Category.assoc] using
              congrArg (fun k => q ≫ k ≫ pullback.snd _ _) (P.gluing D)
          _ = d := by
            calc
              _ = (q ≫ P.sourceMap D) ≫ (D.gluingPullbackIso () ()).hom ≫
                    pullback.snd _ _ := by simp only [Category.assoc]
              _ = pullback.lift d (d ≫ (D.obj ()).hom) (by simp [Category.assoc]) ≫
                    (D.gluingPullbackIso () ()).hom ≫ pullback.snd _ _ := by rw [hsource]
              _ = d := gluingPullback_diagonal_snd a D d
      have htransition_snd :
          q ≫ ((D' D).gluingPullbackIso () ()).hom ≫ pullback.snd _ _ ≫
            (eD D).hom.left ≫ pullback.snd (D.obj ()).hom f = x₂ := by
        have hbaseG : ((D' D).gluingPullbackIso () ()).hom ≫ pullback.snd _ _ ≫
            ((D' D).obj ()).hom = pullback.snd _ _ := by
          let U := (D' D).obj ()
          let src := Over.prodLeftIsoPullback ((Over.map a').obj U) (Over.mk a')
          let tgt := Over.prodLeftIsoPullback (Over.mk a') ((Over.map a').obj U)
          have hglue : ((D' D).gluingIso () ()).hom.left ≫
              (prod.snd (X := Over.mk a')).left ≫ U.hom =
                (prod.snd (X := (Over.map a').obj U)).left :=
            congrArg Over.Hom.left
              ((D' D).gluing_hom_snd_structureMap () ())
          have hforget : ((Over.forget S).mapIso ((D' D).gluingIso () ())).hom =
              ((D' D).gluingIso () ()).hom.left := rfl
          show src.inv ≫ ((Over.forget S).mapIso ((D' D).gluingIso () ())).hom ≫
              tgt.hom ≫ pullback.snd _ _ ≫ U.hom = pullback.snd _ _
          calc
            _ = src.inv ≫ ((D' D).gluingIso () ()).hom.left ≫
                  (prod.snd (X := Over.mk a')).left ≫ U.hom := by
              have ht : tgt.hom ≫ pullback.snd _ _ =
                  (prod.snd (X := Over.mk a')).left := by
                dsimp only [tgt]
                simpa using Over.prodLeftIsoPullback_hom_snd (Over.mk a')
                  ((Over.map a').obj U)
              simpa only [Category.assoc, hforget] using
                congrArg (fun k => src.inv ≫ ((D' D).gluingIso () ()).hom.left ≫
                  k ≫ U.hom) ht
            _ = src.inv ≫ (prod.snd (X := (Over.map a').obj U)).left := by
              simpa only [Category.assoc] using congrArg (fun k => src.inv ≫ k) hglue
            _ = pullback.snd _ _ := by
              simpa only [src] using
                Over.prodLeftIsoPullback_inv_snd ((Over.map a').obj U) (Over.mk a')
        calc
          _ = q ≫ ((D' D).gluingPullbackIso () ()).hom ≫ pullback.snd _ _ ≫
                ((D' D).obj ()).hom := by rw [eD_snd D]
          _ = q ≫ pullback.snd _ _ := by
            simpa only [Category.assoc] using congrArg (fun k => q ≫ k) hbaseG
          _ = x₂ := hqsnd
      have he₂map : u₂ ≫ (eD D).hom.left = pullback.lift d x₂ hpair := by
        apply pullback.hom_ext
        · dsimp [u₂]
          calc
            _ = g₂ ≫ ((eD D).inv.left ≫ (eD D).hom.left) ≫
                pullback.fst (D.obj ()).hom f := by
              simp only [Category.assoc]
            _ = g₂ ≫ 𝟙 _ ≫ pullback.fst (D.obj ()).hom f := by
              rw [heiso]
            _ = g₂ ≫ pullback.fst (D.obj ()).hom f := by simp
            _ = d := by rw [hg₂, pullback.lift_fst]
            _ = pullback.lift d x₂ hpair ≫ pullback.fst (D.obj ()).hom f := by
              rw [pullback.lift_fst]
        · dsimp [u₂]
          calc
            _ = g₂ ≫ ((eD D).inv.left ≫ (eD D).hom.left) ≫
                pullback.snd (D.obj ()).hom f := by
              simp only [Category.assoc]
            _ = g₂ ≫ 𝟙 _ ≫ pullback.snd (D.obj ()).hom f := by
              rw [heiso]
            _ = g₂ ≫ pullback.snd (D.obj ()).hom f := by simp
            _ = x₂ := by rw [hg₂, pullback.lift_snd]
            _ = pullback.lift d x₂ hpair ≫ pullback.snd (D.obj ()).hom f := by
              rw [pullback.lift_snd]
      have htransition : q ≫ ((D' D).gluingPullbackIso () ()).hom ≫
          pullback.snd _ _ = u₂ := by
        apply (cancel_mono (eD D).hom.left).1
        apply pullback.hom_ext
        · calc
            _ = d := htransition_fst
            _ = (u₂ ≫ (eD D).hom.left) ≫ pullback.fst (D.obj ()).hom f := by
              rw [he₂map]
              simp [pullback.lift_fst]
        · calc
            _ = x₂ := htransition_snd
            _ = (u₂ ≫ (eD D).hom.left) ≫ pullback.snd (D.obj ()).hom f := by
              rw [he₂map]
              simp [pullback.lift_snd]
      let sD := Over.prodLeftIsoPullback ((Over.map a').obj ((D' D).obj ())) (Over.mk a')
      let sE := Over.prodLeftIsoPullback ((Over.map a').obj ((D' E).obj ())) (Over.mk a')
      let tE := Over.prodLeftIsoPullback (Over.mk a') ((Over.map a').obj ((D' E).obj ()))
      let v := u₁ ≫ (g.hom ()).left
      let dE := v ≫ (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f
      have hvbase : v ≫ ((D' E).obj ()).hom = x₁ := by
        calc
          _ = u₁ ≫ ((g.hom ()).left ≫ ((D' E).obj ()).hom) := by
            simp only [v, Category.assoc]
          _ = u₁ ≫ ((D' D).obj ()).hom := by rw [Over.w (g.hom ())]
          _ = x₁ := hu₁
      have hqE : v ≫ ((D' E).obj ()).hom ≫ a' = x₂ ≫ a' := by
        calc
          _ = x₁ ≫ a' := by
            simpa only [Category.assoc] using congrArg (fun k => k ≫ a') hvbase
          _ = x₂ ≫ a' := hxa
      have hqE' : v ≫ ((Over.map a').obj ((D' E).obj ())).hom =
          x₂ ≫ (Over.mk a').hom := by
        calc
          _ = x₂ ≫ a' := by simpa only [Over.map_obj_hom] using hqE
          _ = x₂ ≫ (Over.mk a').hom := rfl
      let qE := pullback.lift v x₂ hqE'
      have hqEfst : qE ≫ pullback.fst ((Over.map a').obj ((D' E).obj ())).hom
          (Over.mk a').hom = v := pullback.lift_fst v x₂ hqE'
      have hqEsnd : qE ≫ pullback.snd ((Over.map a').obj ((D' E).obj ())).hom
          (Over.mk a').hom = x₂ := pullback.lift_snd v x₂ hqE'
      have hdEbase : dE ≫ (E.obj ()).hom = x₂ ≫ f := by
        dsimp only [dE]
        calc
          _ = v ≫ (eD E).hom.left ≫
              pullback.snd (E.obj ()).hom f ≫ f := by
            rw [← pullback.condition]
            simp only [Category.assoc]
          _ = v ≫ ((D' E).obj ()).hom ≫ f := by
            simpa only [Category.assoc] using
              congrArg (fun k => v ≫ k ≫ f) (eD_snd E)
          _ = x₁ ≫ f :=
            congrArg (fun k => k ≫ f) hvbase
          _ = x₂ ≫ f := hbase
      have hsourceE : qE ≫ P.sourceMap E =
          pullback.lift dE (dE ≫ (E.obj ()).hom) (by simp [Category.assoc]) := by
        apply pullback.hom_ext
        · calc
            _ = qE ≫ pullback.fst _ _ ≫ (eD E).hom.left ≫
                pullback.fst (E.obj ()).hom f := by
              simpa [D', Over.map_obj_hom, Category.assoc] using
                congrArg (fun k => qE ≫ k) (P.sourceMap_fst E)
            _ = dE := by
              simpa only [Category.assoc, dE] using
                congrArg (fun k => k ≫ (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f) hqEfst
            _ = pullback.lift dE (dE ≫ (E.obj ()).hom) _ ≫ pullback.fst _ _ := by
              rw [pullback.lift_fst]
        · calc
            _ = qE ≫ pullback.snd _ _ ≫ f := by
              simpa [D', Over.map_obj_hom, Category.assoc] using
                congrArg (fun k => qE ≫ k) (P.sourceMap_snd E)
            _ = dE ≫ (E.obj ()).hom :=
              (congrArg (fun k => k ≫ f) hqEsnd).trans hdEbase.symm
            _ = pullback.lift dE (dE ≫ (E.obj ()).hom) _ ≫ pullback.snd _ _ := by
              rw [pullback.lift_snd]
      have hEglue : qE ≫ ((D' E).gluingPullbackIso () ()).hom ≫
          pullback.snd _ _ ≫ (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f = dE := by
        calc
          _ = qE ≫ ((D' E).gluingPullbackIso () ()).hom ≫ P.targetMap E ≫
              pullback.snd _ _ := by
            rw [P.targetMap_snd E]
          _ = qE ≫ P.sourceMap E ≫ (E.gluingPullbackIso () ()).hom ≫
              pullback.snd _ _ := by
            simpa only [Category.assoc] using
              congrArg (fun k => qE ≫ k ≫ pullback.snd _ _) (P.gluing E)
          _ = pullback.lift dE (dE ≫ (E.obj ()).hom) (by simp [Category.assoc]) ≫
              (E.gluingPullbackIso () ()).hom ≫ pullback.snd _ _ :=
            congrArg
              (fun k => k ≫ (E.gluingPullbackIso () ()).hom ≫ pullback.snd _ _) hsourceE
          _ = dE := gluingPullback_diagonal_snd a E dE
      have hpairE : qE ≫ sE.inv =
          q ≫ sD.inv ≫ (prod.map ((Over.map a').map (g.hom ()))
            (𝟙 (Over.mk a'))).left := by
        have hmfst :
            (prod.map ((Over.map a').map (g.hom ())) (𝟙 (Over.mk a'))).left ≫
                (prod.fst (X := (Over.map a').obj ((D' E).obj ())) (Y := Over.mk a')).left =
              (prod.fst (X := (Over.map a').obj ((D' D).obj ())) (Y := Over.mk a')).left ≫
                ((Over.map a').map (g.hom ())).left := by
          simpa only [Over.comp_left] using
            congrArg Over.Hom.left
              (prod.map_fst ((Over.map a').map (g.hom ())) (𝟙 (Over.mk a')))
        have hmsnd :
            (prod.map ((Over.map a').map (g.hom ())) (𝟙 (Over.mk a'))).left ≫
                (prod.snd (X := (Over.map a').obj ((D' E).obj ())) (Y := Over.mk a')).left =
              (prod.snd (X := (Over.map a').obj ((D' D).obj ())) (Y := Over.mk a')).left := by
          simpa only [Over.comp_left, Over.id_left, Category.comp_id] using
            congrArg Over.Hom.left
              (prod.map_snd ((Over.map a').map (g.hom ())) (𝟙 (Over.mk a')))
        have hmk : (Over.mk a').hom = a' := rfl
        have hmfst' :
            (prod.map ((Over.map a').map (g.hom ())) (𝟙 (Over.mk a'))).left ≫
                (prod.fst (X := (Over.map a').obj ((D' E).obj ())) (Y := Over.mk a')).left =
              (prod.fst (X := (Over.map a').obj ((D' D).obj ())) (Y := Over.mk a')).left ≫
                (g.hom ()).left := by
          simpa only [Over.map_map_left] using hmfst
        have hmsnd' :
            (prod.map ((Over.map a').map (g.hom ())) (𝟙 (Over.mk a'))).left ≫
                (prod.snd (X := (Over.map a').obj ((D' E).obj ())) (Y := Over.mk a')).left =
              (prod.snd (X := (Over.map a').obj ((D' D).obj ())) (Y := Over.mk a')).left := by
          simpa only [Over.map_map_left] using hmsnd
        have hsDfst : sD.inv ≫
            (prod.fst (X := (Over.map a').obj ((D' D).obj ())) (Y := Over.mk a')).left =
              pullback.fst (((D' D).obj ()).hom ≫ a') a' := by
          convert (Over.prodLeftIsoPullback_inv_fst ((Over.map a').obj ((D' D).obj ()))
            (Over.mk a')) using 1
          rfl
        have hsDsnd : sD.inv ≫
            (prod.snd (X := (Over.map a').obj ((D' D).obj ())) (Y := Over.mk a')).left =
              pullback.snd (((D' D).obj ()).hom ≫ a') a' := by
          convert (Over.prodLeftIsoPullback_inv_snd ((Over.map a').obj ((D' D).obj ()))
            (Over.mk a')) using 1
          rfl
        have hsEfst : sE.hom ≫
            pullback.fst (((D' E).obj ()).hom ≫ a') (Over.mk a').hom =
              (prod.fst (X := (Over.map a').obj ((D' E).obj ())) (Y := Over.mk a')).left := by
          convert (Over.prodLeftIsoPullback_hom_fst ((Over.map a').obj ((D' E).obj ()))
            (Over.mk a')) using 1 <;> rfl
        have hsEsnd : sE.hom ≫
            pullback.snd (((D' E).obj ()).hom ≫ a') (Over.mk a').hom =
              (prod.snd (X := (Over.map a').obj ((D' E).obj ())) (Y := Over.mk a')).left := by
          convert (Over.prodLeftIsoPullback_hom_snd ((Over.map a').obj ((D' E).obj ()))
            (Over.mk a')) using 1
          rfl
        apply (cancel_mono sE.hom).1
        apply pullback.hom_ext
        · calc
            _ = qE ≫ pullback.fst (((Over.map a').obj ((D' E).obj ())).hom) (Over.mk a').hom := by
              simp only [Category.assoc, Iso.inv_hom_id_assoc]
            _ = v := hqEfst
            _ = q ≫ sD.inv ≫ (prod.map ((Over.map a').map (g.hom ()))
                (𝟙 (Over.mk a'))).left ≫ sE.hom ≫
                  pullback.fst (((D' E).obj ()).hom ≫ a') (Over.mk a').hom := by
              calc
                _ = u₁ ≫ (g.hom ()).left := by simp [v]
                _ = q ≫ pullback.fst (((D' D).obj ()).hom ≫ a') a' ≫
                    (g.hom ()).left := by
                  rw [← hqfst]
                  simp only [Category.assoc]
                _ = q ≫ sD.inv ≫ (prod.fst (X := (Over.map a').obj ((D' D).obj ()))
                    (Y := Over.mk a')).left ≫ (g.hom ()).left := by
                  simp only [← hsDfst, Category.assoc]
                _ = q ≫ sD.inv ≫ (prod.map ((Over.map a').map (g.hom ()))
                    (𝟙 (Over.mk a'))).left ≫ sE.hom ≫
                    pullback.fst (((D' E).obj ()).hom ≫ a') (Over.mk a').hom := by
                  rw [← hmfst', ← hsEfst]
        · calc
            _ = qE ≫ pullback.snd (((Over.map a').obj ((D' E).obj ())).hom) (Over.mk a').hom := by
              simp only [Category.assoc, Iso.inv_hom_id_assoc]
            _ = x₂ := hqEsnd
            _ = q ≫ sD.inv ≫ (prod.map ((Over.map a').map (g.hom ()))
                (𝟙 (Over.mk a'))).left ≫ sE.hom ≫
                  pullback.snd (((D' E).obj ()).hom ≫ a') (Over.mk a').hom := by
              calc
                _ = q ≫ pullback.snd (((D' D).obj ()).hom ≫ a') a' := by
                  rw [← hqsnd]
                _ = q ≫ sD.inv ≫ (prod.snd (X := (Over.map a').obj ((D' D).obj ()))
                    (Y := Over.mk a')).left := by
                  simp only [← hsDsnd]
                _ = q ≫ sD.inv ≫ (prod.map ((Over.map a').map (g.hom ()))
                    (𝟙 (Over.mk a'))).left ≫
                    (prod.snd (X := (Over.map a').obj ((D' E).obj ())) (Y := Over.mk a')).left := by
                  rw [← hmsnd]
                _ = q ≫ sD.inv ≫ (prod.map ((Over.map a').map (g.hom ()))
                    (𝟙 (Over.mk a'))).left ≫ sE.hom ≫
                    pullback.snd (((D' E).obj ()).hom ≫ a') (Over.mk a').hom := by
                  rw [← hsEsnd]
      have hcomm :
          q ≫ sD.inv ≫
              (prod.map ((Over.map a').map (g.hom ())) (𝟙 (Over.mk a'))).left ≫
              Over.Hom.left ((D' E).gluing () ()).hom.left ≫
              (prod.snd (X := Over.mk a')
                (Y := (Over.map a').obj ((D' E).obj ()))).left ≫
              (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f =
            q ≫ sD.inv ≫ Over.Hom.left ((D' D).gluing () ()).hom.left ≫
              (prod.map (𝟙 (Over.mk a')) ((Over.map a').map (g.hom ()))).left ≫
              (prod.snd (X := Over.mk a')
                (Y := (Over.map a').obj ((D' E).obj ()))).left ≫
              (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f := by
        have hcompat0 := congrArg Over.Hom.left (g.comm () ())
        have hcompat :
            (prod.map ((Over.map a').map (g.hom ())) (𝟙 (Over.mk a'))).left ≫
                Over.Hom.left ((D' E).gluing () ()).hom.left =
              Over.Hom.left ((D' D).gluing () ()).hom.left ≫
                (prod.map (𝟙 (Over.mk a')) ((Over.map a').map (g.hom ()))).left := by
          simpa only [Over.comp_left] using hcompat0
        simpa only [Category.assoc] using congrArg
          (fun m => q ≫ sD.inv ≫ m ≫
            (prod.snd (X := Over.mk a')
              (Y := (Over.map a').obj ((D' E).obj ()))).left ≫
            (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f)
          hcompat
      let tD := Over.prodLeftIsoPullback (Over.mk a') ((Over.map a').obj ((D' D).obj ()))
      have hmapSnd :
          (prod.map (𝟙 (Over.mk a')) ((Over.map a').map (g.hom ()))).left ≫
              (prod.snd (X := Over.mk a')
                (Y := (Over.map a').obj ((D' E).obj ()))).left =
            (prod.snd (X := Over.mk a')
              (Y := (Over.map a').obj ((D' D).obj ()))).left ≫
              Over.Hom.left ((Over.map a').map (g.hom ())) := by
        simpa only [Over.comp_left] using
          congrArg Over.Hom.left
            (prod.map_snd (𝟙 (Over.mk a')) ((Over.map a').map (g.hom ())))
      have hglueD : sD.inv ≫ Over.Hom.left ((D' D).gluing () ()).hom.left ≫
          (prod.snd (X := Over.mk a')
            (Y := (Over.map a').obj ((D' D).obj ()))).left =
          ((D' D).gluingPullbackIso () ()).hom ≫ pullback.snd _ _ := by
        show sD.inv ≫ Over.Hom.left ((D' D).gluing () ()).hom.left ≫
            (prod.snd (X := Over.mk a')
              (Y := (Over.map a').obj ((D' D).obj ()))).left =
          sD.inv ≫ Over.Hom.left ((D' D).gluing () ()).hom.left ≫
            (Over.prodLeftIsoPullback (Over.mk a')
              ((Over.map a').obj ((D' D).obj ()))).hom ≫ pullback.snd _ _
        rw [Over.prodLeftIsoPullback_hom_snd]
      have hglueE : sE.inv ≫ Over.Hom.left ((D' E).gluing () ()).hom.left ≫
          (prod.snd (X := Over.mk a')
            (Y := (Over.map a').obj ((D' E).obj ()))).left =
          ((D' E).gluingPullbackIso () ()).hom ≫ pullback.snd _ _ := by
        show sE.inv ≫ Over.Hom.left ((D' E).gluing () ()).hom.left ≫
            (prod.snd (X := Over.mk a')
              (Y := (Over.map a').obj ((D' E).obj ()))).left =
          sE.inv ≫ Over.Hom.left ((D' E).gluing () ()).hom.left ≫
            (Over.prodLeftIsoPullback (Over.mk a')
              ((Over.map a').obj ((D' E).obj ()))).hom ≫ pullback.snd _ _
        rw [Over.prodLeftIsoPullback_hom_snd]
      have hcomm' : qE ≫ ((D' E).gluingPullbackIso () ()).hom ≫
          pullback.snd _ _ ≫ (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f =
        q ≫ ((D' D).gluingPullbackIso () ()).hom ≫ pullback.snd _ _ ≫
          (g.hom ()).left ≫ (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f := by
        calc
          _ = qE ≫ sE.inv ≫ Over.Hom.left ((D' E).gluing () ()).hom.left ≫
              (prod.snd (X := Over.mk a') (Y := (Over.map a').obj ((D' E).obj ()))).left ≫
              (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f := by
            simpa only [Category.assoc] using congrArg
              (fun k => qE ≫ k ≫ (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f)
              hglueE.symm
          _ = q ≫ sD.inv ≫ (prod.map ((Over.map a').map (g.hom ()))
              (𝟙 (Over.mk a'))).left ≫ Over.Hom.left ((D' E).gluing () ()).hom.left ≫
              (prod.snd (X := Over.mk a') (Y := (Over.map a').obj ((D' E).obj ()))).left ≫
              (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f :=
            congrArg (fun k => k ≫ Over.Hom.left ((D' E).gluing () ()).hom.left ≫
              (prod.snd (X := Over.mk a') (Y := (Over.map a').obj ((D' E).obj ()))).left ≫
              (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f) hpairE
          _ = q ≫ sD.inv ≫ Over.Hom.left ((D' D).gluing () ()).hom.left ≫
              (prod.map (𝟙 (Over.mk a')) ((Over.map a').map (g.hom ()))).left ≫
              (prod.snd (X := Over.mk a') (Y := (Over.map a').obj ((D' E).obj ()))).left ≫
              (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f := hcomm
          _ = q ≫ ((D' D).gluingPullbackIso () ()).hom ≫ pullback.snd _ _ ≫
              (g.hom ()).left ≫ (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f := by
            calc
              _ = q ≫ sD.inv ≫ Over.Hom.left ((D' D).gluing () ()).hom.left ≫
                    (prod.map (𝟙 (Over.mk a')) ((Over.map a').map (g.hom ()))).left ≫
                    (prod.snd (X := Over.mk a')
                      (Y := (Over.map a').obj ((D' E).obj ()))).left ≫
                    (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f := rfl
              _ = q ≫ sD.inv ≫ Over.Hom.left ((D' D).gluing () ()).hom.left ≫
                    (prod.snd (X := Over.mk a')
                      (Y := (Over.map a').obj ((D' D).obj ()))).left ≫
                    (g.hom ()).left ≫ (eD E).hom.left ≫
                    pullback.fst (E.obj ()).hom f := by
                simpa only [Category.assoc, Over.map_map_left] using congrArg
                  (fun k => q ≫ sD.inv ≫
                    Over.Hom.left ((D' D).gluing () ()).hom.left ≫ k ≫
                    (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f) hmapSnd
              _ = q ≫ ((D' D).gluingPullbackIso () ()).hom ≫ pullback.snd _ _ ≫
                    (g.hom ()).left ≫ (eD E).hom.left ≫
                    pullback.fst (E.obj ()).hom f := by
                simpa only [Category.assoc] using congrArg
                  (fun k => q ≫ k ≫ (g.hom ()).left ≫
                    (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f) hglueD
      calc
        _ = dE := by simp [localMap, u₁, dE, v, Category.assoc]
        _ = qE ≫ ((D' E).gluingPullbackIso () ()).hom ≫ pullback.snd _ _ ≫
            (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f := hEglue.symm
        _ = q ≫ ((D' D).gluingPullbackIso () ()).hom ≫ pullback.snd _ _ ≫
            (g.hom ()).left ≫ (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f := hcomm'
        _ = u₂ ≫ (g.hom ()).left ≫ (eD E).hom.left ≫
            pullback.fst (E.obj ()).hom f := by
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ (g.hom ()).left ≫ (eD E).hom.left ≫
              pullback.fst (E.obj ()).hom f) htransition
        _ = _ := by simp [localMap, u₂, Category.assoc]
      )
  have hfac {D E : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)}
      (g : D' D ⟶ D' E) : coverMap ≫ descendMap g = localMap g := by
    simp [descendMap]
  have descendMap_over
      {D E : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)}
      (g : D' D ⟶ D' E) : descendMap g ≫ (E.obj ()).hom = (D.obj ()).hom := by
    let := fpqcPullbackEffectiveEpi f (D.obj ()).hom hcover
    apply (cancel_epi coverMap).1
    rw [← Category.assoc, hfac g]
    dsimp [localMap]
    have heDbase : (eD D).inv.left ≫ ((D' D).obj ()).hom =
        pullback.snd (D.obj ()).hom f := by
      simpa only [Over.pullback_obj_hom] using Over.w (eD D).inv
    calc
      _ = (eD D).inv.left ≫ (g.hom ()).left ≫ (eD E).hom.left ≫
          pullback.snd (E.obj ()).hom f ≫ f := by
        simp only [Category.assoc, ← pullback.condition]
      _ = (eD D).inv.left ≫ (g.hom ()).left ≫ ((D' E).obj ()).hom ≫ f := by
        simpa only [Category.assoc] using congrArg
          (fun k => (eD D).inv.left ≫ (g.hom ()).left ≫ k ≫ f) (eD_snd E)
      _ = (eD D).inv.left ≫ ((D' D).obj ()).hom ≫ f := by
        simpa only [Category.assoc] using congrArg
          (fun k => (eD D).inv.left ≫ k ≫ f) (Over.w (g.hom ()))
      _ = pullback.snd (D.obj ()).hom f ≫ f :=
        congrArg (fun k => k ≫ f) heDbase
      _ = coverMap ≫ (D.obj ()).hom := by
        rw [← pullback.condition]
  let preimage {D E : DescentData (S := S)
      (X := fun _ : Unit ↦ X) (fun _ ↦ a)}
      (g : D' D ⟶ D' E) : D ⟶ E := {
      hom := fun _ => Over.homMk (descendMap g) (descendMap_over g)
      comm := by
        intro i j
        cases i
        cases j
        let φ₀ : D.obj () ⟶ E.obj () :=
          Over.homMk (descendMap g) (descendMap_over g)
        let : EffectiveEpi (pullback.fst (D.obj ()).hom f) :=
          fpqcPullbackEffectiveEpi f (D.obj ()).hom hcover
        have : Epi f := by
          have : EffectiveEpi f := fpqcEffectiveEpi f hcover
          infer_instance
        let : IsIso (eD D).hom := Iso.isIso_hom (eD D)
        let : IsIso (eD D).hom.left :=
          (Over.forget X').mapIso (eD D) |>.isIso_hom
        have hcoverD : Epi ((eD D).hom.left ≫ pullback.fst (D.obj ()).hom f) :=
          inferInstance
        have hlocal : (eD D).hom.left ≫ pullback.fst (D.obj ()).hom f ≫ φ₀.left =
            (g.hom ()).left ≫ (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f := by
          calc
            _ = (eD D).hom.left ≫ coverMap ≫ descendMap g := rfl
            _ = (eD D).hom.left ≫ localMap g :=
              congrArg (fun k => (eD D).hom.left ≫ k) (hfac g)
            _ = _ := by simp [localMap]
        have hsourceNat : P.sourceMap D ≫ sourcePullbackMap a φ₀ =
            sourcePullbackMap a' (g.hom ()) ≫ P.sourceMap E := by
          apply pullback.hom_ext
          · calc
              _ = P.sourceMap D ≫ pullback.fst ((D.obj ()).hom ≫ a) a ≫ φ₀.left := by
                rw [Category.assoc, sourcePullbackMap_fst]
              _ = pullback.fst (((D' D).obj ()).hom ≫ a') a' ≫
                    (eD D).hom.left ≫ pullback.fst (D.obj ()).hom f ≫ φ₀.left := by
                simpa only [Category.assoc] using
                  congrArg (fun k => k ≫ φ₀.left) (P.sourceMap_fst D)
              _ = pullback.fst (((D' D).obj ()).hom ≫ a') a' ≫
                    (g.hom ()).left ≫ (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f :=
                congrArg
                  (fun k => pullback.fst (((D' D).obj ()).hom ≫ a') a' ≫ k) hlocal
              _ = sourcePullbackMap a' (g.hom ()) ≫ P.sourceMap E ≫
                    pullback.fst ((E.obj ()).hom ≫ a) a := by
                have h₁ := congrArg
                  (fun k => k ≫ (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f)
                  (sourcePullbackMap_fst a' (g.hom ())).symm
                have h₂ := congrArg (fun k => sourcePullbackMap a' (g.hom ()) ≫ k)
                  (P.sourceMap_fst E).symm
                calc
                  _ = sourcePullbackMap a' (g.hom ()) ≫
                      pullback.fst (((D' E).obj ()).hom ≫ a') a' ≫
                      (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f := by
                    simpa only [Category.assoc] using h₁
                  _ = sourcePullbackMap a' (g.hom ()) ≫ P.sourceMap E ≫
                      pullback.fst ((E.obj ()).hom ≫ a) a := by
                    simpa only [Category.assoc] using h₂
          · calc
              _ = P.sourceMap D ≫ pullback.snd ((D.obj ()).hom ≫ a) a := by
                rw [Category.assoc, sourcePullbackMap_snd]
              _ = pullback.snd (((D' D).obj ()).hom ≫ a') a' ≫ f :=
                P.sourceMap_snd D
              _ = sourcePullbackMap a' (g.hom ()) ≫ P.sourceMap E ≫
                    pullback.snd ((E.obj ()).hom ≫ a) a := by
                have h₁ := congrArg (fun k => k ≫ f)
                  (sourcePullbackMap_snd a' (g.hom ())).symm
                have h₂ := congrArg (fun k => sourcePullbackMap a' (g.hom ()) ≫ k)
                  (P.sourceMap_snd E).symm
                calc
                  _ = sourcePullbackMap a' (g.hom ()) ≫
                      pullback.snd (((D' E).obj ()).hom ≫ a') a' ≫ f := by
                    simpa only [Category.assoc] using h₁
                  _ = sourcePullbackMap a' (g.hom ()) ≫ P.sourceMap E ≫
                      pullback.snd ((E.obj ()).hom ≫ a) a := by
                    simpa only [Category.assoc] using h₂
        have htargetNat : P.targetMap D ≫ targetPullbackMap a φ₀ =
            targetPullbackMap a' (g.hom ()) ≫ P.targetMap E := by
          apply pullback.hom_ext
          · calc
              _ = P.targetMap D ≫ pullback.fst a ((D.obj ()).hom ≫ a) := by
                rw [Category.assoc, targetPullbackMap_fst]
              _ = pullback.fst a' (((D' D).obj ()).hom ≫ a') ≫ f :=
                P.targetMap_fst D
              _ = targetPullbackMap a' (g.hom ()) ≫ P.targetMap E ≫
                    pullback.fst a ((E.obj ()).hom ≫ a) := by
                have h₁ := congrArg (fun k => k ≫ f)
                  (targetPullbackMap_fst a' (g.hom ())).symm
                have h₂ := congrArg (fun k => targetPullbackMap a' (g.hom ()) ≫ k)
                  (P.targetMap_fst E).symm
                calc
                  _ = targetPullbackMap a' (g.hom ()) ≫
                      pullback.fst a' (((D' E).obj ()).hom ≫ a') ≫ f := by
                    simpa only [Category.assoc] using h₁
                  _ = targetPullbackMap a' (g.hom ()) ≫ P.targetMap E ≫
                      pullback.fst a ((E.obj ()).hom ≫ a) := by
                    simpa only [Category.assoc] using h₂
          · calc
              _ = P.targetMap D ≫ pullback.snd a ((D.obj ()).hom ≫ a) ≫ φ₀.left := by
                rw [Category.assoc, targetPullbackMap_snd]
              _ = pullback.snd a' (((D' D).obj ()).hom ≫ a') ≫
                    (eD D).hom.left ≫ pullback.fst (D.obj ()).hom f ≫ φ₀.left := by
                simpa only [Category.assoc] using
                  congrArg (fun k => k ≫ φ₀.left) (P.targetMap_snd D)
              _ = pullback.snd a' (((D' D).obj ()).hom ≫ a') ≫
                    (g.hom ()).left ≫ (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f :=
                congrArg
                  (fun k => pullback.snd a' (((D' D).obj ()).hom ≫ a') ≫ k) hlocal
              _ = targetPullbackMap a' (g.hom ()) ≫ P.targetMap E ≫
                    pullback.snd a ((E.obj ()).hom ≫ a) := by
                have h₁ := congrArg
                  (fun k => k ≫ (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f)
                  (targetPullbackMap_snd a' (g.hom ())).symm
                have h₂ := congrArg (fun k => targetPullbackMap a' (g.hom ()) ≫ k)
                  (P.targetMap_snd E).symm
                calc
                  _ = targetPullbackMap a' (g.hom ()) ≫
                      pullback.snd a' (((D' E).obj ()).hom ≫ a') ≫
                      (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f := by
                    simpa only [Category.assoc] using h₁
                  _ = targetPullbackMap a' (g.hom ()) ≫ P.targetMap E ≫
                      pullback.snd a ((E.obj ()).hom ≫ a) := by
                    simpa only [Category.assoc] using h₂
        have hsourceEpi : Epi (P.sourceMap D) := sourceMap_epi P hcover D
        have hpb : sourcePullbackMap a φ₀ ≫
            (E.gluingPullbackIso () ()).hom =
            (D.gluingPullbackIso () ()).hom ≫ targetPullbackMap a φ₀ := by
          apply (cancel_epi (P.sourceMap D)).1
          calc
            _ = sourcePullbackMap a' (g.hom ()) ≫ P.sourceMap E ≫
                (E.gluingPullbackIso () ()).hom := by
              simpa only [Category.assoc] using congrArg
                (fun k => k ≫ (E.gluingPullbackIso () ()).hom) hsourceNat
            _ = sourcePullbackMap a' (g.hom ()) ≫
                ((P.functor.obj E).gluingPullbackIso () ()).hom ≫ P.targetMap E := by
              simpa only [Category.assoc] using congrArg
                (fun k => sourcePullbackMap a' (g.hom ()) ≫ k)
                (P.gluing E).symm
            _ = ((P.functor.obj D).gluingPullbackIso () ()).hom ≫
                targetPullbackMap a' (g.hom ()) ≫ P.targetMap E :=
              congrArg (fun k => k ≫ P.targetMap E)
                (gluingPullback_comm (a := a') g)
            _ = ((P.functor.obj D).gluingPullbackIso () ()).hom ≫
                P.targetMap D ≫ targetPullbackMap a φ₀ := by
              simpa only [Category.assoc] using congrArg
                (fun k => ((P.functor.obj D).gluingPullbackIso () ()).hom ≫ k)
                htargetNat.symm
            _ = P.sourceMap D ≫ (D.gluingPullbackIso () ()).hom ≫
                targetPullbackMap a φ₀ := by
              simpa only [Category.assoc] using congrArg
                (fun k => k ≫ targetPullbackMap a φ₀) (P.gluing D)
        let sD := Over.prodLeftIsoPullback ((Over.map a).obj (D.obj ())) (Over.mk a)
        let sE := Over.prodLeftIsoPullback ((Over.map a).obj (E.obj ())) (Over.mk a)
        let tD := Over.prodLeftIsoPullback (Over.mk a) ((Over.map a).obj (D.obj ()))
        let tE := Over.prodLeftIsoPullback (Over.mk a) ((Over.map a).obj (E.obj ()))
        have hs := sourcePullbackMap_eq_prodMap a φ₀
        have ht := targetPullbackMap_eq_prodMap a φ₀
        have hcomm : (prod.map ((Over.map a).map φ₀)
            (𝟙 (Over.mk a))).left ≫ (E.gluingIso () ()).hom.left =
            (D.gluingIso () ()).hom.left ≫
              (prod.map (𝟙 (Over.mk a)) ((Over.map a).map φ₀)).left := by
          have h' : sD.inv ≫ (prod.map ((Over.map a).map φ₀)
              (𝟙 (Over.mk a))).left ≫ (E.gluingIso () ()).hom.left ≫ tE.hom =
              sD.inv ≫ (D.gluingIso () ()).hom.left ≫
                (prod.map (𝟙 (Over.mk a)) ((Over.map a).map φ₀)).left ≫ tE.hom := by
            simpa [DescentData.gluingPullbackIso,
              DescentData.gluingIso, hs, ht, sD, sE, tD, tE,
              Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
              Over.forget_map, Over.comp_left, Category.assoc] using hpb
          have h'' := (cancel_epi sD.inv).1 (by
            simpa only [Category.assoc] using h')
          exact (cancel_mono tE.hom).1 (by
            simpa only [Category.assoc] using h'')
        apply Over.OverMorphism.ext
        simpa only [φ₀, Over.comp_left, Over.map_map_left,
          gluingIso_hom_left] using hcomm
    }
  exact ⟨{
    preimage := preimage
    map_preimage := by
      intro D E g
      apply DescentData.hom_ext
      intro i
      cases i
      apply Over.OverMorphism.ext
      have hnat := congrArg Over.Hom.left (P.map (preimage g))
      have htransport :
          (eD D).hom.left ≫ ((Over.pullback f).map ((preimage g).hom ())).left =
            (g.hom ()).left ≫ (eD E).hom.left := by
        apply pullback.hom_ext
        · have hcancel : (eD D).hom.left ≫ (eD D).inv.left =
              𝟙 (((P.functor.obj D).obj ()).left) := by
            simpa only [Over.comp_left, Over.id_left, Over.pullback_obj_left] using
              congrArg Over.Hom.left (Iso.hom_inv_id (eD D))
          have hmapfst :
              ((Over.pullback f).map ((preimage g).hom ())).left ≫
                  pullback.fst (E.obj ()).hom f =
                pullback.fst (D.obj ()).hom f ≫ Over.Hom.left ((preimage g).hom ()) := by
            dsimp [Over.pullback]
            exact pullback.lift_fst _ _ _
          calc
            _ = (eD D).hom.left ≫ pullback.fst (D.obj ()).hom f ≫
                Over.Hom.left ((preimage g).hom ()) := by rw [Category.assoc, hmapfst]
            _ = (eD D).hom.left ≫ coverMap ≫ descendMap g := by
              simp [coverMap, preimage]
            _ = (eD D).hom.left ≫ localMap g :=
              congrArg (fun k => (eD D).hom.left ≫ k) (hfac g)
            _ = (g.hom ()).left ≫ (eD E).hom.left ≫
                pullback.fst (E.obj ()).hom f := by
              dsimp [localMap]
              calc
                _ = ((eD D).hom.left ≫ (eD D).inv.left) ≫ (g.hom ()).left ≫
                    (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f := by
                  simp only [Category.assoc]
                _ = (g.hom ()).left ≫ (eD E).hom.left ≫
                    pullback.fst (E.obj ()).hom f := by rw [hcancel, Category.id_comp]
        · have hmapSnd : ((Over.pullback f).map ((preimage g).hom ())).left ≫
              pullback.snd (E.obj ()).hom f = pullback.snd (D.obj ()).hom f :=
            pullbackMap_snd f ((preimage g).hom ())
          rw [Category.assoc, hmapSnd, eD_snd D, ← Over.w (g.hom ()),
            ← eD_snd E]
          simp only [Category.assoc]
      apply (cancel_mono (eD E).hom.left).1
      calc
        Over.Hom.left ((P.functor.map (preimage g)).hom ()) ≫ (eD E).hom.left =
            (eD D).hom.left ≫ ((Over.pullback f).map ((preimage g).hom ())).left := hnat.symm
        _ = (g.hom ()).left ≫ (eD E).hom.left := htransport
    preimage_map := by
      intro D E g
      apply DescentData.hom_ext
      intro i
      cases i
      apply Over.OverMorphism.ext
      let := fpqcPullbackEffectiveEpi f (D.obj ()).hom hcover
      apply (cancel_epi (pullback.fst (D.obj ()).hom f)).1
      have hnat := congrArg Over.Hom.left (P.map g)
      have hbase :
          (eD D).inv.left ≫ Over.Hom.left ((P.functor.map g).hom ()) ≫
              (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f =
            pullback.fst (D.obj ()).hom f ≫ (g.hom ()).left := by
        have hnat' := congrArg (fun k => k ≫ pullback.fst (E.obj ()).hom f) hnat
        have hnat'' := congrArg (fun k => (eD D).inv.left ≫ k) hnat'
        simpa [Category.assoc, eD_inv_hom D, eD, Over.pullback,
          pullback.map, pullback.lift_fst] using hnat''.symm
      calc
        (pullback.fst (D.obj ()).hom f) ≫ (((preimage (P.functor.map g)).hom ()).left) =
            coverMap ≫ descendMap (P.functor.map g) := rfl
        _ = localMap (P.functor.map g) := hfac _
        _ = (eD D).inv.left ≫ Over.Hom.left ((P.functor.map g).hom ()) ≫
            (eD E).hom.left ≫ pullback.fst (E.obj ()).hom f := rfl
        _ = pullback.fst (D.obj ()).hom f ≫ (g.hom ()).left := hbase
  }⟩

end AlgebraicGeometry
