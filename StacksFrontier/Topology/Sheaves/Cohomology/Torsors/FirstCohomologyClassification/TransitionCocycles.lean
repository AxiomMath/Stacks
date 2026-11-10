module

public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.PresheavesOfGroupsAndActions
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingCochainGroups
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.DegreeOneComparison
public import StacksFrontier.Homology.Injectives.Sheaf.AbelianSheavesOnSpace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CohomologyPresheafLocallyZero
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.FirstCohomologyClassification.TorsorClasses
import all StacksFrontier.Topology.Sheaves.Cohomology.Torsors.FirstCohomologyClassification.TorsorClasses

/-!
# Differences of sections and transition cocycles of torsors

For a torsor `F` under an abelian sheaf `H` on a topological space, two sections of `F` over the
same open differ by a unique section of `H`. The differences of a family of local sections form a
Čech `1`-cocycle. This file also proves the local facts about affine maps of torsors into abelian
sheaves used in the classification of torsors by first cohomology.

## Main definitions

* `Stacks.Cohomology.SheafTorsor.torsorDifference` is the unique section of `H` carrying one
  section of a torsor to another.
* `Stacks.Cohomology.SheafTorsor.torsorTransitionCocycle` is the Čech `1`-cocycle of transition
  differences of a family of local sections of a torsor.

## Main results

* `Stacks.Cohomology.SheafTorsor.torsorTransitionCocycle_spec` says that the transition cocycle
  of a family of local sections carries each section to the next on every overlap.

## References

* [Stacks Project, Tag 02FQ](https://stacks.math.columbia.edu/tag/02FQ)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u v w
universe z

namespace Stacks.Cohomology.SheafTorsor

/-- If the `Ui` cover the whole space, they cover every open set. -/
private lemma eq_iSup_inf_of_top_eq {X : Type u} [TopologicalSpace X] {ι : Type*}
    {Ui : ι → Opens X} (hUi : (⊤ : Opens X) = ⨆ i, Ui i) (V : Opens X) :
    V = ⨆ i, V ⊓ Ui i := by
  rw [← inf_iSup_eq, ← hUi, inf_top_eq]

private lemma exists_presheafHom_of_cover {X : Type u} [TopologicalSpace X]
    (F : Stacks.SpaceTorsor.PresheafOfSets.{u, v} X)
    (A : Stacks.SpaceTorsor.SheafOfSets.{u, v} X)
    (Ui : X → Opens X) (hUi : (⊤ : Opens X) = ⨆ i, Ui i)
    (f : ∀ (i : X) (V : Opens X), V ≤ Ui i → F.obj V → A.obj V)
    (hn : ∀ i (V W : Opens X) (hV : V ≤ Ui i) (hWV : W ≤ V) (s : F.obj V),
      A.res hWV (f i V hV s) = f i W (hWV.trans hV) (F.res hWV s))
    (hc : ∀ i j (V : Opens X) (hi : V ≤ Ui i) (hj : V ≤ Ui j) (s : F.obj V),
      f i V hi s = f j V hj s) :
    ∃ g : F.Hom A.toPresheafOfSets,
      ∀ i (V : Opens X) (hV : V ≤ Ui i) (s : F.obj V), g.app V s = f i V hV s := by
  classical
  have hcover (V : Opens X) : V = ⨆ i, V ⊓ Ui i := eq_iSup_inf_of_top_eq hUi V
  have hex (V : Opens X) (s : F.obj V) :
      ∃! a : A.obj V, ∀ i, A.res (inf_le_left : V ⊓ Ui i ≤ V) a =
        f i (V ⊓ Ui i) inf_le_right (F.res inf_le_left s) := by
    let sf : A.CompatibleFamily (fun i => V ⊓ Ui i) :=
      ⟨fun i => f i (V ⊓ Ui i) inf_le_right (F.res inf_le_left s), by
        intro i j W hi hj
        rw [hn, hn, F.res_comp, F.res_comp]
        exact hc i j W (hi.trans inf_le_right) (hj.trans inf_le_right) _⟩
    have hb := A.isSheaf V X (fun i => V ⊓ Ui i) (fun _ => inf_le_left) (hcover V)
    obtain ⟨a, ha⟩ := hb.2 sf
    refine ⟨a, ?_, ?_⟩
    · exact fun i => congrFun (congrArg Subtype.val ha) i
    · intro b hb'
      apply hb.1
      apply Subtype.ext
      funext i
      exact (hb' i).trans (congrFun (congrArg Subtype.val ha) i).symm
  choose g hg huniq using hex
  have hext (V : Opens X) (a b : A.obj V)
      (h : ∀ i, A.res (inf_le_left : V ⊓ Ui i ≤ V) a = A.res inf_le_left b) : a = b := by
    apply (A.isSheaf V X (fun i => V ⊓ Ui i) (fun _ => inf_le_left) (hcover V)).1
    exact Subtype.ext (funext h)
  have hg_local (i : X) (V : Opens X) (hV : V ≤ Ui i) (s : F.obj V) :
      g V s = f i V hV s := by
    apply hext V
    intro j
    rw [hg, hn]
    exact hc j i (V ⊓ Ui j) inf_le_right (inf_le_left.trans hV) _
  refine ⟨⟨g, ?_⟩, hg_local⟩
  intro V W hWV s
  apply hext W
  intro i
  rw [hg, A.res_comp]
  have hi := congrArg (A.res (show W ⊓ Ui i ≤ V ⊓ Ui i from
    inf_le_inf_right _ hWV)) (hg V s i)
  rw [A.res_comp, hn, F.res_comp] at hi
  rw [F.res_comp]
  exact hi.symm

/-- The unique section of `H` carrying one section of a torsor to another on the same open.
Over an open where the torsor has a section the action is simply transitive, so `s` and `t`
differ by exactly one element of `H(U)`. -/
noncomputable def torsorDifference {X : TopCat.{u}}
    {H : TopCat.Sheaf AddCommGrpCat.{v} X} (F : Torsor X H)
    {U : Opens X} (s t : F.F.obj U) : H.presheaf.obj (op U) :=
  (Classical.choose ((F.isTorsor.1 U ⟨t⟩).2 t s).exists).toAdd

/-- The difference of two sections of a torsor acts on the second to give the first. -/
lemma torsorDifference_act {X : TopCat.{u}}
    {H : TopCat.Sheaf AddCommGrpCat.{v} X} (F : Torsor X H)
    {U : Opens X} (s t : F.F.obj U) :
    F.action.act (Multiplicative.ofAdd (torsorDifference F s t)) t = s :=
  Classical.choose_spec ((F.isTorsor.1 U ⟨t⟩).2 t s).exists

/-- Any section of `H` carrying `t` to `s` is their difference: the action is simply
transitive. -/
lemma torsorDifference_eq {X : TopCat.{u}}
    {H : TopCat.Sheaf AddCommGrpCat.{v} X} (F : Torsor X H)
    {U : Opens X} (s t : F.F.obj U) (h : H.presheaf.obj (op U))
    (hh : F.action.act (Multiplicative.ofAdd h) t = s) :
    torsorDifference F s t = h := by
  apply Multiplicative.ofAdd.injective
  exact ((F.isTorsor.1 U ⟨t⟩).2 t s).unique (torsorDifference_act F s t) hh

/-- Restriction of sections restricts their difference. -/
lemma torsorDifference_res {X : TopCat.{u}}
    {H : TopCat.Sheaf AddCommGrpCat.{v} X} (F : Torsor X H)
    {U V : Opens X} (h : V ≤ U) (s t : F.F.obj U) :
    torsorDifference F (F.F.res h s) (F.F.res h t) =
      H.presheaf.map (homOfLE h).op (torsorDifference F s t) := by
  apply torsorDifference_eq
  exact (F.action.res_act h _ t).symm.trans
    (congrArg (F.F.res h) (torsorDifference_act F s t))

/-- Differences of three sections of a torsor add up along the chain. -/
lemma torsorDifference_add {X : TopCat.{u}}
    {H : TopCat.Sheaf AddCommGrpCat.{v} X} (F : Torsor X H)
    {U : Opens X} (s t r : F.F.obj U) :
    torsorDifference F s t + torsorDifference F t r = torsorDifference F s r := by
  symm
  refine torsorDifference_eq F s r _ ((act_ofAdd_add F _ _ r).trans ?_)
  exact (congrArg (F.action.act (Multiplicative.ofAdd (torsorDifference F s t)))
    (torsorDifference_act F t r)).trans (torsorDifference_act F s t)

/-- A section of a torsor does not differ from itself. -/
lemma torsorDifference_self {X : TopCat.{u}}
    {H : TopCat.Sheaf AddCommGrpCat.{v} X} (F : Torsor X H)
    {U : Opens X} (s : F.F.obj U) : torsorDifference F s s = 0 :=
  torsorDifference_eq F s s 0 (F.action.one_act s)

/-- Restricting both sections restricts their difference, written with the Čech restriction
homomorphism so that it rewrites inside the Čech differential. -/
theorem torsorDifference_restr {X : TopCat.{u}}
    {H : TopCat.Sheaf AddCommGrpCat.{v} X} (F : Torsor X H)
    {U V : Opens X} (h : V ≤ U) (s t : F.F.obj U) :
    CechCochains.restr H.presheaf h (torsorDifference F s t) =
      torsorDifference F (F.F.res h s) (F.F.res h t) :=
  (torsorDifference_res F h s t).symm

/-- Two successive restrictions in a sheaf of sets compose.  Stated on the sheaf itself, so
that the rewrite pattern is headed by a variable rather than by a projection. -/
private theorem res_res {X : Type u} [TopologicalSpace X]
    (A : Stacks.SpaceTorsor.SheafOfSets.{u, v} X)
    {U V W : Opens X} (hWV : W ≤ V) (hVU : V ≤ U) (x : A.obj U) :
    A.res hWV (A.res hVU x) = A.res (hWV.trans hVU) x :=
  A.res_comp hWV hVU x

/-- The three differences of three sections cancel in the Čech alternating sum. -/
@[ega "IV 16.5.15" "partial"]
private theorem torsorDifference_alternating {X : TopCat.{u}}
    {H : TopCat.Sheaf AddCommGrpCat.{v} X} (F : Torsor X H)
    {U : Opens X} (x y z : F.F.obj U) :
    torsorDifference F x y + -torsorDifference F x z + torsorDifference F y z = 0 := by
  rw [← torsorDifference_add F x y z]
  abel

/-- The Čech `1`-cochain of differences of a family of local sections of a torsor. -/
@[sga "4½ Cycle 1.1.2"]
def transitionCochain {X : TopCat.{u}}
    {H : TopCat.Sheaf AddCommGrpCat.{v} X} (F : Torsor X H)
    {I : Type w} (Ui : I → Opens X) (s : ∀ i, F.F.obj (Ui i)) :
    CechCochains.Cochain Ui H.presheaf 1 := fun i =>
  torsorDifference F
    (F.F.res (iInf_le (fun k => Ui (i k)) 1) (s (i 1)))
    (F.F.res (iInf_le (fun k => Ui (i k)) 0) (s (i 0)))

/-- The restriction of the transition cochain to a smaller open, recomputed as the difference
of the sections restricted all the way down. -/
theorem restr_transitionCochain {X : TopCat.{u}}
    {H : TopCat.Sheaf AddCommGrpCat.{v} X} (F : Torsor X H)
    {I : Type w} (Ui : I → Opens X) (s : ∀ i, F.F.obj (Ui i))
    {V : Opens X} (j : Fin 2 → I) (h : V ≤ CechCochains.inter Ui j) :
    CechCochains.restr H.presheaf h (transitionCochain F Ui s j) =
      torsorDifference F
        (F.F.res (h.trans (iInf_le (fun m => Ui (j m)) 1)) (s (j 1)))
        (F.F.res (h.trans (iInf_le (fun m => Ui (j m)) 0)) (s (j 0))) :=
  (torsorDifference_restr F h _ _).trans
    (congrArg₂ (torsorDifference F) (F.F.res_comp _ _ _) (F.F.res_comp _ _ _))

/-- The cochain of differences is a Čech cocycle: on a triple overlap the three differences
of the restricted sections cancel. -/
theorem cechD_transitionCochain {X : TopCat.{u}}
    {H : TopCat.Sheaf AddCommGrpCat.{v} X} (F : Torsor X H)
    {I : Type w} (Ui : I → Opens X) (s : ∀ i, F.F.obj (Ui i)) :
    CechCochains.cechD Ui H.presheaf 1 (transitionCochain F Ui s) = 0 := by
  funext i
  rw [CechCochains.cechD_apply, CechCochains.Cochain.zero_apply]
  simp only [Nat.reduceAdd, Fin.sum_univ_three, Fin.val_zero, pow_zero, one_zsmul,
    Fin.val_one, pow_one, neg_one_zsmul, Fin.val_two, even_two, Even.neg_pow, one_pow]
  rw [restr_transitionCochain, restr_transitionCochain, restr_transitionCochain]
  exact torsorDifference_alternating F _ _ _

/-- The Čech cocycle of transition differences of a family of local sections. -/
@[ega "IV 16.5.15" "special case", sga "4½ Cycle 1.1.2"]
def torsorTransitionCocycle {X : TopCat.{u}}
    {H : TopCat.Sheaf AddCommGrpCat.{v} X} (F : Torsor X H)
    {I : Type w} (Ui : I → Opens X) (s : ∀ i, F.F.obj (Ui i)) :
    CechCochains.cocycles1 Ui H.presheaf :=
  ⟨transitionCochain F Ui s, by
    change CechCochains.cechD Ui H.presheaf 1 (transitionCochain F Ui s) = 0
    exact cechD_transitionCochain F Ui s⟩

/-- The value of the transition cocycle on an overlap. -/
theorem torsorTransitionCocycle_val {X : TopCat.{u}}
    {H : TopCat.Sheaf AddCommGrpCat.{v} X} (F : Torsor X H)
    {I : Type w} (Ui : I → Opens X) (s : ∀ i, F.F.obj (Ui i)) (i : Fin 2 → I) :
    (torsorTransitionCocycle F Ui s).val i =
      torsorDifference F
        (F.F.res (iInf_le (fun k => Ui (i k)) 1) (s (i 1)))
        (F.F.res (iInf_le (fun k => Ui (i k)) 0) (s (i 0))) := rfl

/-- The transition cocycle of a family of local sections carries each section to the next on
every overlap. -/
@[ega "IV 16.5.15" "Existence"]
theorem torsorTransitionCocycle_spec {X : TopCat.{u}}
    {H : TopCat.Sheaf AddCommGrpCat.{v} X} (F : Torsor X H)
    {I : Type w} (Ui : I → Opens X) (s : ∀ i, F.F.obj (Ui i)) :
    IsTransitionCocycle F Ui s (torsorTransitionCocycle F Ui s) := fun i =>
  (congrArg (fun d => F.action.act (Multiplicative.ofAdd d)
      (F.F.res (iInf_le (fun k => Ui (i k)) 0) (s (i 0))))
    (torsorTransitionCocycle_val F Ui s i)).trans (torsorDifference_act F _ _)

private lemma torsor_common_cover {X : TopCat.{u}}
    {H : TopCat.Sheaf AddCommGrpCat.{v} X} (F G : Torsor X H) :
    ∃ (Ui : X → Opens X), (⊤ : Opens X) = ⨆ x, Ui x ∧
      Nonempty (∀ x, F.F.obj (Ui x)) ∧ Nonempty (∀ x, G.F.obj (Ui x)) := by
  classical
  choose U hU s using fun x => F.isTorsor.2 x
  choose V hV t using fun x => G.isTorsor.2 x
  refine ⟨fun x => U x ⊓ V x, ?_, ?_, ?_⟩
  · apply le_antisymm
    · intro x _
      exact Opens.mem_iSup.mpr ⟨x, hU x, hV x⟩
    · exact le_top
  · exact ⟨fun x => F.F.res inf_le_left (Classical.choice (s x))⟩
  · exact ⟨fun x => G.F.res inf_le_right (Classical.choice (t x))⟩

private lemma torsorAffineMap_injective {X : TopCat.{u}}
    {H A : TopCat.Sheaf AddCommGrpCat.{v} X} (F : Torsor X H)
    (φ : H ⟶ A) {U : Opens X} (hφ : Function.Injective (φ.hom.app (op U)))
    (f : F.F.obj U → A.presheaf.obj (op U))
    (hf : ∀ (h : H.presheaf.obj (op U)) (s : F.F.obj U),
      f (F.action.act (Multiplicative.ofAdd h) s) = φ.hom.app (op U) h + f s) :
    Function.Injective f := by
  intro s t hst
  have h := hf (torsorDifference F s t) t
  rw [torsorDifference_act F s t, hst] at h
  have hz : φ.hom.app (op U) (torsorDifference F s t) = 0 := by
    exact add_right_cancel (h.symm.trans (zero_add (f t)).symm)
  have hd : torsorDifference F s t = 0 := hφ (hz.trans (map_zero _).symm)
  have ha := torsorDifference_act F s t
  rw [hd] at ha
  exact ha.symm.trans (F.action.one_act t)

private theorem torsorPairing_transitionCocycle {X : TopCat.{u}}
    {H : TopCat.Sheaf AddCommGrpCat.{v} X} {I : Type w}
    (F G K : Torsor X H) (p : TorsorPairing F G K) (Ui : I → Opens X)
    (s : ∀ i, F.F.obj (Ui i)) (t : ∀ i, G.F.obj (Ui i))
    (zF : CechCochains.cocycles1 Ui H.presheaf)
    (zG : CechCochains.cocycles1 Ui H.presheaf)
    (hzF : IsTransitionCocycle F Ui s zF)
    (hzG : IsTransitionCocycle G Ui t zG) :
    IsTransitionCocycle K Ui (fun i => p.app (Ui i) (s i) (t i))
      ⟨fun i => zF.val i + zG.val i, by
        change CechCochains.cechD Ui H.presheaf 1 (zF.val + zG.val) = 0
        rw [map_add, zF.property, zG.property, add_zero]⟩ := by
  intro i
  let W : Opens X := CechCochains.inter Ui i
  let h₀ : W ≤ Ui (i 0) := iInf_le (fun k => Ui (i k)) 0
  let h₁ : W ≤ Ui (i 1) := iInf_le (fun k => Ui (i k)) 1
  dsimp only [Subtype.coe_mk, Function.comp_apply]
  rw [← p.naturality h₀ (s (i 0)) (t (i 0))]
  calc
    K.action.act (Multiplicative.ofAdd (zF.val i + zG.val i))
        (p.app W (F.F.res h₀ (s (i 0))) (G.F.res h₀ (t (i 0)))) =
      p.app W
        (F.action.act (Multiplicative.ofAdd (zF.val i)) (F.F.res h₀ (s (i 0))))
        (G.action.act (Multiplicative.ofAdd (zG.val i)) (G.F.res h₀ (t (i 0)))) := by
          let a : (underlyingPresheafOfGroups X H).obj W :=
            Multiplicative.ofAdd (zF.val i)
          let b : (underlyingPresheafOfGroups X H).obj W :=
            Multiplicative.ofAdd (zG.val i)
          change K.action.act (a * b) _ = _
          calc
            K.action.act (a * b)
                (p.app W (F.F.res h₀ (s (i 0))) (G.F.res h₀ (t (i 0)))) =
              K.action.act a (K.action.act b
                (p.app W (F.F.res h₀ (s (i 0))) (G.F.res h₀ (t (i 0))))) :=
                  K.action.mul_act a b _
            _ = K.action.act a
                (p.app W (F.F.res h₀ (s (i 0)))
                  (G.action.act b (G.F.res h₀ (t (i 0))))) := by
                    rw [← p.map_act_right]
            _ = p.app W (F.action.act a (F.F.res h₀ (s (i 0))))
                (G.action.act b (G.F.res h₀ (t (i 0)))) := by
                  rw [← p.map_act_left]
    _ = p.app W (F.F.res h₁ (s (i 1))) (G.F.res h₁ (t (i 1))) := by
      rw [hzF i, hzG i]
      rfl
    _ = K.F.res h₁ (p.app (Ui (i 1)) (s (i 1)) (t (i 1))) :=
      p.naturality h₁ (s (i 1)) (t (i 1))

private abbrev abelianSheafOfSets {X : TopCat.{u}}
    (A : TopCat.Sheaf AddCommGrpCat.{max u v} X) :
    Stacks.SpaceTorsor.SheafOfSets.{u, max u v} X where
  obj U := A.presheaf.obj (op U)
  res h := A.presheaf.map (homOfLE h).op
  res_self U s := by simp
  res_comp hWV hVU s := by
    rw [← ConcreteCategory.comp_apply, ← A.presheaf.map_comp]
    rfl
  isSheaf := fromSitePresheaf_isSheaf.{u, v} X _
    (Presheaf.isSheaf_comp_of_isSheaf (Opens.grothendieckTopology X) A.presheaf
      (forget AddCommGrpCat.{max u v}) A.property)

private lemma abelianSheaf_res_comp {X : TopCat.{u}}
    (A : TopCat.Sheaf AddCommGrpCat.{v} X) {U V W : Opens X}
    (hWV : W ≤ V) (hVU : V ≤ U) (a : A.presheaf.obj (op U)) :
    A.presheaf.map (homOfLE hWV).op (A.presheaf.map (homOfLE hVU).op a) =
      A.presheaf.map (homOfLE (hWV.trans hVU)).op a := by
  rw [← ConcreteCategory.comp_apply, ← A.presheaf.map_comp]
  rfl

private lemma abelianSheafHom_naturality {X : TopCat.{u}}
    {H A : TopCat.Sheaf AddCommGrpCat.{v} X} (φ : H ⟶ A)
    {U V : Opens X} (h : V ≤ U) (a : H.presheaf.obj (op U)) :
    A.presheaf.map (homOfLE h).op (φ.hom.app (op U) a) =
      φ.hom.app (op V) (H.presheaf.map (homOfLE h).op a) := by
  exact (ConcreteCategory.congr_hom (φ.hom.naturality (homOfLE h).op) a).symm

private lemma torsorDifference_act_add {X : TopCat.{u}}
    {H : TopCat.Sheaf AddCommGrpCat.{v} X} (F : Torsor X H)
    {U : Opens X} (h : H.presheaf.obj (op U)) (s t : F.F.obj U) :
    torsorDifference F (F.action.act (Multiplicative.ofAdd h) s) t =
      h + torsorDifference F s t := by
  refine torsorDifference_eq F _ t _ ((act_ofAdd_add F h (torsorDifference F s t) t).trans ?_)
  exact congrArg (F.action.act (Multiplicative.ofAdd h)) (torsorDifference_act F s t)

private lemma abelianSheaf_eq_of_cover {X : TopCat.{u}}
    (A : TopCat.Sheaf AddCommGrpCat.{max u v} X)
    (Ui : X → Opens X) (hUi : (⊤ : Opens X) = ⨆ i, Ui i)
    (V : Opens X) (a b : A.presheaf.obj (op V))
    (h : ∀ i, A.presheaf.map (homOfLE (inf_le_left : V ⊓ Ui i ≤ V)).op a =
      A.presheaf.map (homOfLE (inf_le_left : V ⊓ Ui i ≤ V)).op b) : a = b := by
  exact ((abelianSheafOfSets A).isSheaf V X (fun i => V ⊓ Ui i)
    (fun _ => inf_le_left) (eq_iSup_inf_of_top_eq hUi V)).1 (Subtype.ext (funext h))

private lemma exists_affine_map {X : TopCat.{u}}
    {H A : TopCat.Sheaf AddCommGrpCat.{max u v} X} (φ : H ⟶ A)
    (F : Torsor X H) (Ui : X → Opens X) (hUi : (⊤ : Opens X) = ⨆ i, Ui i)
    (s : ∀ i, F.F.obj (Ui i))
    (b : ∀ i, A.presheaf.obj (op (Ui i)))
    (hb : ∀ i j (V : Opens X) (hi : V ≤ Ui i) (hj : V ≤ Ui j),
      φ.hom.app (op V) (torsorDifference F (F.F.res hj (s j)) (F.F.res hi (s i))) =
        A.presheaf.map (homOfLE hj).op (b j) -
          A.presheaf.map (homOfLE hi).op (b i)) :
    ∃ g : F.F.toPresheafOfSets.Hom (abelianSheafOfSets A).toPresheafOfSets,
      (∀ i (V : Opens X) (hV : V ≤ Ui i) (t : F.F.obj V),
        g.app V t = φ.hom.app (op V) (torsorDifference F t (F.F.res hV (s i))) +
          A.presheaf.map (homOfLE hV).op (b i)) ∧
      (∀ (V : Opens X) (h : H.presheaf.obj (op V)) (t : F.F.obj V),
        g.app V (F.action.act (Multiplicative.ofAdd h) t) =
          φ.hom.app (op V) h + (g.app V t : A.presheaf.obj (op V))) := by
  let f (i : X) (V : Opens X) (hV : V ≤ Ui i) (t : F.F.obj V) :=
    φ.hom.app (op V) (torsorDifference F t (F.F.res hV (s i))) +
      A.presheaf.map (homOfLE hV).op (b i)
  obtain ⟨g, hg⟩ := exists_presheafHom_of_cover F.F.toPresheafOfSets
    (abelianSheafOfSets A) Ui hUi f (by
      intro i V W hV hWV t
      change A.presheaf.map (homOfLE hWV).op (f i V hV t) = _
      dsimp only [f]
      rw [map_add, abelianSheafHom_naturality, abelianSheaf_res_comp,
        ← torsorDifference_res, F.F.res_comp]) (by
      intro i j V hi hj t
      dsimp only [f]
      rw [← torsorDifference_add F t (F.F.res hj (s j)) (F.F.res hi (s i)),
        map_add, hb]
      abel)
  refine ⟨g, hg, ?_⟩
  -- Equivariance of the glued map, checked on each covering member.
  have key : ∀ (i : X) (W : Opens X) (hWi : W ≤ Ui i) (k : H.presheaf.obj (op W))
      (x : F.F.obj W),
      g.app W (F.action.act (Multiplicative.ofAdd k) x) =
        φ.hom.app (op W) k + (g.app W x : A.presheaf.obj (op W)) := by
    intro i W hWi k x
    have h1 : torsorDifference F (F.action.act (Multiplicative.ofAdd k) x)
        (F.F.res hWi (s i)) = k + torsorDifference F x (F.F.res hWi (s i)) :=
      torsorDifference_act_add F k x (F.F.res hWi (s i))
    rw [hg i W hWi, hg i W hWi]
    dsimp only [f]
    rw [h1, map_add, add_assoc]
  intro V h t
  refine abelianSheaf_eq_of_cover A Ui hUi V _ _ fun i => ?_
  change (abelianSheafOfSets A).res (inf_le_left : V ⊓ Ui i ≤ V) _ = (abelianSheafOfSets A).res _ _
  calc (abelianSheafOfSets A).res (inf_le_left : V ⊓ Ui i ≤ V)
        (g.app V (F.action.act (Multiplicative.ofAdd h) t))
      = g.app (V ⊓ Ui i) (F.F.res inf_le_left
          (F.action.act (Multiplicative.ofAdd h) t)) :=
        (g.naturality _ _).symm
    _ = g.app (V ⊓ Ui i) (F.action.act (Multiplicative.ofAdd
          (H.presheaf.map (homOfLE (inf_le_left : V ⊓ Ui i ≤ V)).op h))
          (F.F.res inf_le_left t)) :=
        congrArg (g.app (V ⊓ Ui i)) (res_act_ofAdd F inf_le_left h t)
    _ = φ.hom.app (op (V ⊓ Ui i))
            (H.presheaf.map (homOfLE (inf_le_left : V ⊓ Ui i ≤ V)).op h) +
          (g.app (V ⊓ Ui i) (F.F.res inf_le_left t) :
            A.presheaf.obj (op (V ⊓ Ui i))) :=
        key i (V ⊓ Ui i) inf_le_right _ _
    _ = A.presheaf.map (homOfLE (inf_le_left : V ⊓ Ui i ≤ V)).op
            (φ.hom.app (op V) h) +
          (g.app (V ⊓ Ui i) (F.F.res inf_le_left t) :
            A.presheaf.obj (op (V ⊓ Ui i))) :=
        congrArg (fun y => y + (g.app (V ⊓ Ui i) (F.F.res inf_le_left t) :
            A.presheaf.obj (op (V ⊓ Ui i))))
          (abelianSheafHom_naturality φ inf_le_left h).symm
    _ = A.presheaf.map (homOfLE (inf_le_left : V ⊓ Ui i ≤ V)).op
            (φ.hom.app (op V) h) +
          A.presheaf.map (homOfLE (inf_le_left : V ⊓ Ui i ≤ V)).op
            (g.app V t : A.presheaf.obj (op V)) :=
        congrArg (fun y => A.presheaf.map
            (homOfLE (inf_le_left : V ⊓ Ui i ≤ V)).op (φ.hom.app (op V) h) + y)
          (g.naturality (inf_le_left : V ⊓ Ui i ≤ V) t)
    _ = (abelianSheafOfSets A).res (inf_le_left : V ⊓ Ui i ≤ V)
          (φ.hom.app (op V) h + (g.app V t : A.presheaf.obj (op V))) :=
        (map_add _ _ _).symm

private def cechZeroSection {X : TopCat.{u}}
    (A : TopCat.Sheaf AddCommGrpCat.{v} X) {I : Type w} (Ui : I → Opens X)
    (b : CechCochains.Cochain Ui A.presheaf 0) (i : I) : A.presheaf.obj (op (Ui i)) :=
  A.presheaf.map (homOfLE (le_iInf fun _ => le_rfl)).op (b (fun _ => i))

private lemma transition_coboundary {X : TopCat.{u}}
    {H A : TopCat.Sheaf AddCommGrpCat.{v} X} (φ : H ⟶ A)
    (F : Torsor X H) {I : Type w} (Ui : I → Opens X) (s : ∀ i, F.F.obj (Ui i))
    (z : CechCochains.cocycles1 Ui H.presheaf) (hz : IsTransitionCocycle F Ui s z)
    (b : CechCochains.Cochain Ui A.presheaf 0)
    (hb : ∀ i, CechCochains.cechD Ui A.presheaf 0 b i =
      φ.hom.app (op (CechCochains.inter Ui i)) (z.val i))
    (i j : I) (V : Opens X) (hi : V ≤ Ui i) (hj : V ≤ Ui j) :
    φ.hom.app (op V) (torsorDifference F (F.F.res hj (s j)) (F.F.res hi (s i))) =
      A.presheaf.map (homOfLE hj).op (cechZeroSection A Ui b j) -
        A.presheaf.map (homOfLE hi).op (cechZeroSection A Ui b i) := by
  let ij : Fin 2 → I := ![i, j]
  have hV : V ≤ CechCochains.inter Ui ij := by
    apply le_iInf
    intro k
    fin_cases k
    · exact hi
    · exact hj
  have hd : torsorDifference F
      (F.F.res (iInf_le (fun k => Ui (ij k)) 1) (s (ij 1)))
      (F.F.res (iInf_le (fun k => Ui (ij k)) 0) (s (ij 0))) = z.val ij :=
    torsorDifference_eq F _ _ _ (hz ij)
  have hres : H.presheaf.map (homOfLE hV).op
      (torsorDifference F
        (F.F.res (iInf_le (fun k => Ui (ij k)) 1) (s (ij 1)))
        (F.F.res (iInf_le (fun k => Ui (ij k)) 0) (s (ij 0)))) =
      torsorDifference F (F.F.res hj (s j)) (F.F.res hi (s i)) :=
    (torsorDifference_res F hV _ _).symm.trans
      (congrArg₂ (torsorDifference F) (F.F.res_comp _ _ _) (F.F.res_comp _ _ _))
  have hdV : torsorDifference F (F.F.res hj (s j)) (F.F.res hi (s i)) =
      H.presheaf.map (homOfLE hV).op (z.val ij) :=
    hres.symm.trans (congrArg (H.presheaf.map (homOfLE hV).op) hd)
  rw [hdV, ← abelianSheafHom_naturality, ← hb ij]
  have hstep : CechCochains.cechD Ui A.presheaf 0 b ij =
      CechCochains.restr A.presheaf (CechCochains.inter_le_omit Ui ij 0)
          (b (ij ∘ Fin.succAbove 0)) -
        CechCochains.restr A.presheaf (CechCochains.inter_le_omit Ui ij 1)
          (b (ij ∘ Fin.succAbove 1)) := by
    rw [CechCochains.cechD_apply]
    simp only [Nat.reduceAdd, Fin.sum_univ_two, Fin.val_zero, pow_zero, one_zsmul,
      Fin.val_one, pow_one, neg_one_zsmul, sub_eq_add_neg]
  have hres2 (a : Fin 1 → I) (hVa : V ≤ CechCochains.inter Ui a)
      (hWa : CechCochains.inter Ui ij ≤ CechCochains.inter Ui a) :
      A.presheaf.map (homOfLE hV).op (CechCochains.restr A.presheaf hWa (b a)) =
        A.presheaf.map (homOfLE hVa).op (b a) :=
    abelianSheaf_res_comp A hV hWa (b a)
  have hzero (c : I) (hc : V ≤ Ui c) (hVc : V ≤ CechCochains.inter Ui (fun _ => c)) :
      A.presheaf.map (homOfLE hc).op (cechZeroSection A Ui b c) =
        A.presheaf.map (homOfLE hVc).op (b (fun _ => c)) :=
    abelianSheaf_res_comp A hc (le_iInf fun _ => le_rfl) (b (fun _ => c))
  have h0 : ij ∘ Fin.succAbove 0 = fun _ => j := by funext k; fin_cases k; rfl
  have h1 : ij ∘ Fin.succAbove 1 = fun _ => i := by funext k; fin_cases k; rfl
  have heq (a a' : Fin 1 → I) (ha : a = a')
      (hVa : V ≤ CechCochains.inter Ui a) (hVa' : V ≤ CechCochains.inter Ui a') :
      A.presheaf.map (homOfLE hVa).op (b a) =
        A.presheaf.map (homOfLE hVa').op (b a') := by
    subst a'
    rfl
  rw [hstep, map_sub,
    hres2 (ij ∘ Fin.succAbove 0) (hV.trans (CechCochains.inter_le_omit Ui ij 0))
      (CechCochains.inter_le_omit Ui ij 0),
    hres2 (ij ∘ Fin.succAbove 1) (hV.trans (CechCochains.inter_le_omit Ui ij 1))
      (CechCochains.inter_le_omit Ui ij 1),
    hzero j hj (le_iInf fun _ => hj), hzero i hi (le_iInf fun _ => hi)]
  exact congrArg₂ (fun x y => x - y)
    (heq _ _ h0 (hV.trans (CechCochains.inter_le_omit Ui ij 0)) (le_iInf fun _ => hj))
    (heq _ _ h1 (hV.trans (CechCochains.inter_le_omit Ui ij 1)) (le_iInf fun _ => hi))

private lemma affine_map_fiber {X : TopCat.{u}}
    {H A B : TopCat.Sheaf AddCommGrpCat.{max u v} X} (φ : H ⟶ A) (d : A ⟶ B)
    (F : Torsor X H) (g : F.F.toPresheafOfSets.Hom (abelianSheafOfSets A).toPresheafOfSets)
    (hg : ∀ (V : Opens X) (h : H.presheaf.obj (op V)) (t : F.F.obj V),
      g.app V (F.action.act (Multiplicative.ofAdd h) t) =
        φ.hom.app (op V) h + (g.app V t : A.presheaf.obj (op V)))
    (hφ : ∀ V, Function.Injective (φ.hom.app (op V)))
    (hk : ∀ V (a : A.presheaf.obj (op V)), d.hom.app (op V) a = 0 →
      ∃ h, φ.hom.app (op V) h = a)
    (q : B.presheaf.obj (op ⊤))
    (hq : ∀ V (t : F.F.obj V), d.hom.app (op V) (g.app V t) =
      B.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op q) :
    (∀ V, Function.Injective (g.app V)) ∧
      ∀ V (a : A.presheaf.obj (op V)),
        d.hom.app (op V) a = B.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op q ↔
          ∃ t, g.app V t = a := by
  have hinj V := torsorAffineMap_injective F φ (hφ V) (g.app V) (hg V)
  refine ⟨hinj, ?_⟩
  intro V a
  constructor
  · intro ha
    obtain ⟨Ui, hUi, ⟨s⟩, _⟩ := torsor_common_cover F F
    have hex (i : X) : ∃ t : F.F.obj (V ⊓ Ui i),
        g.app (V ⊓ Ui i) t = A.presheaf.map (homOfLE inf_le_left).op a := by
      let t : F.F.obj (V ⊓ Ui i) := F.F.res inf_le_right (s i)
      let a' := A.presheaf.map (homOfLE (inf_le_left : V ⊓ Ui i ≤ V)).op a
      obtain ⟨h, hh⟩ := hk (V ⊓ Ui i) (a' - g.app _ t) (by
        rw [map_sub, hq]
        dsimp only [a']
        rw [← abelianSheafHom_naturality, ha, abelianSheaf_res_comp, sub_self])
      refine ⟨F.action.act (Multiplicative.ofAdd h) t, ?_⟩
      rw [hg, hh, sub_add_cancel]
    choose t ht using hex
    let sf : F.F.CompatibleFamily (fun i => V ⊓ Ui i) := ⟨t, by
      intro i j W hi hj
      apply hinj W
      rw [g.naturality, g.naturality]
      change A.presheaf.map (homOfLE hi).op (g.app _ (t i)) =
        A.presheaf.map (homOfLE hj).op (g.app _ (t j))
      rw [ht, ht, abelianSheaf_res_comp, abelianSheaf_res_comp]⟩
    obtain ⟨t', ht'⟩ := (F.F.isSheaf V X (fun i => V ⊓ Ui i)
      (fun _ => inf_le_left) (eq_iSup_inf_of_top_eq hUi V)).2 sf
    refine ⟨t', abelianSheaf_eq_of_cover A Ui hUi V _ _ ?_⟩
    intro i
    change (abelianSheafOfSets A).res inf_le_left (g.app V t') = _
    rw [← g.naturality]
    have hi := congrFun (congrArg Subtype.val ht') i
    change F.F.res inf_le_left t' = t i at hi
    rw [hi, ht]
  · rintro ⟨t, rfl⟩
    exact hq V t

end Stacks.Cohomology.SheafTorsor
