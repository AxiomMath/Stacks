module

public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.FirstCohomologyClassification
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import StacksCore.Tactic.EgaSgaAttribute

/-!
# First Čech cohomology and locally trivial torsors

Let `H` be an abelian sheaf on a topological space `X` and let `Ui : I → Opens X` be an open
covering of `X`.  The canonical comparison from first Čech cohomology of the covering to first
sheaf cohomology is injective, and under the classification of torsors by first cohomology its
image consists exactly of the classes of torsors having a section over every member of the
covering.

The surjectivity onto those classes is the transition-cocycle description of the classification:
a torsor with sections over every `Ui i` has a Čech `1`-cocycle of differences computing its
class.  For the injectivity one needs the construction in the other direction: a Čech `1`-cocycle
`z`, together with an injective resolution `J` of `H` and a representative of the comparison in
it, produces the sheaf of solutions of `d x + c = 0` in `J⁰`, where `c` is the global cocycle of
the representative.  This is a torsor under `H`, it is trivial on every member of the covering,
and the differences of the local solutions supplied by the representative are exactly `z`.

## Main definitions

* `Stacks.Cohomology.SheafTorsor.IsLocallyTrivialOn` is local triviality of a torsor class on a
  family of opens.
* `Stacks.Cohomology.SheafTorsor.resolutionFiberTorsor` is the torsor of solutions of
  `d x + c = 0` attached to an injective-resolution representative of a Čech cocycle.
* `Stacks.Cohomology.SheafTorsor.sectionDifferenceCochain` is the Čech `0`-cochain of differences
  of two families of local sections of a torsor.
* `Stacks.Cohomology.SheafTorsor.cechH1EquivLocallyTrivialTorsorClass` identifies first Čech
  cohomology with the locally trivial torsor classes.

## Main results

* `Stacks.Cohomology.SheafTorsor.torsorClassEquivSheafCohomologyOne_cechH1Equiv` says that the
  identification is the one induced by the classification of torsors by first cohomology.
* `Stacks.Cohomology.SheafTorsor.cechH1ToRightDerivedSections_injective` is the injectivity of
  the canonical comparison.
* `Stacks.Cohomology.SheafTorsor.cls_torsorTransitionCocycle_congr` and
  `Stacks.Cohomology.SheafTorsor.torsorTransitionCocycle_comp` say that the Čech class of the
  transition cocycle depends neither on the chosen local sections nor on the torsor within its
  isomorphism class.

## References

* [Stacks Project, Tag 0B8R](https://stacks.math.columbia.edu/tag/0B8R)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u v w

namespace Stacks.Cohomology.SheafTorsor

/-! ## The Čech class of a family of local sections -/

section Transition

variable {X : TopCat.{u}} {I : Type w} {H : TopCat.Sheaf AddCommGrpCat.{v} X}

/-- An equivariant morphism of torsors preserves differences of sections: the section of `H`
carrying one section to another is determined by that property. -/
theorem torsorDifference_app {F G : Torsor X H}
    (φ : Stacks.SpaceTorsor.TorsorHom F.action G.action) {U : Opens X} (s t : F.F.obj U) :
    torsorDifference G (φ.app U s) (φ.app U t) = torsorDifference F s t :=
  torsorDifference_eq G _ _ _
    ((φ.map_act _ t).symm.trans (congrArg (φ.app U) (torsorDifference_act F s t)))

/-- The transition cocycle of a family of local sections is carried along an equivariant
morphism of torsors. -/
theorem torsorTransitionCocycle_comp {F G : Torsor X H}
    (φ : Stacks.SpaceTorsor.TorsorHom F.action G.action) (Ui : I → Opens X)
    (s : ∀ i, F.F.obj (Ui i)) :
    torsorTransitionCocycle G Ui (fun i => φ.app (Ui i) (s i)) =
      torsorTransitionCocycle F Ui s := by
  apply Subtype.ext
  funext i
  rw [torsorTransitionCocycle_val, torsorTransitionCocycle_val, ← φ.naturality, ← φ.naturality,
    torsorDifference_app]

/-- The Čech `0`-cochain of differences of two families of local sections of a torsor. -/
def sectionDifferenceCochain (F : Torsor X H) (Ui : I → Opens X)
    (s t : ∀ i, F.F.obj (Ui i)) : CechCochains.Cochain Ui H.presheaf 0 := fun j =>
  torsorDifference F
    (F.F.res (iInf_le (fun k => Ui (j k)) 0) (t (j 0)))
    (F.F.res (iInf_le (fun k => Ui (j k)) 0) (s (j 0)))

/-- The restriction of the cochain of section differences to a smaller open, recomputed as the
difference of the sections restricted all the way down. -/
theorem restr_sectionDifferenceCochain (F : Torsor X H) (Ui : I → Opens X)
    (s t : ∀ i, F.F.obj (Ui i)) {V : Opens X} (j : Fin 1 → I)
    (h : V ≤ CechCochains.inter Ui j) :
    CechCochains.restr H.presheaf h (sectionDifferenceCochain F Ui s t j) =
      torsorDifference F
        (F.F.res (h.trans (iInf_le (fun m => Ui (j m)) 0)) (t (j 0)))
        (F.F.res (h.trans (iInf_le (fun m => Ui (j m)) 0)) (s (j 0))) :=
  (torsorDifference_restr F h _ _).trans
    (congrArg₂ (torsorDifference F) (F.F.res_comp _ _ _) (F.F.res_comp _ _ _))

/-- The Čech coboundary of the cochain of section differences, on an overlap: the difference of
the two transition values there. -/
theorem cechD_sectionDifferenceCochain_apply (F : Torsor X H) (Ui : I → Opens X)
    (s t : ∀ i, F.F.obj (Ui i)) (i : Fin 2 → I) :
    CechCochains.cechD Ui H.presheaf 0 (sectionDifferenceCochain F Ui s t) i =
      torsorDifference F (F.F.res (iInf_le (fun k => Ui (i k)) 1) (t (i 1)))
          (F.F.res (iInf_le (fun k => Ui (i k)) 0) (t (i 0))) -
        torsorDifference F (F.F.res (iInf_le (fun k => Ui (i k)) 1) (s (i 1)))
          (F.F.res (iInf_le (fun k => Ui (i k)) 0) (s (i 0))) := by
  rw [CechCochains.cechD_apply]
  simp only [Nat.reduceAdd, Fin.sum_univ_two, Fin.val_zero, pow_zero, one_zsmul,
    Fin.val_one, pow_one, neg_one_zsmul]
  rw [restr_sectionDifferenceCochain, restr_sectionDifferenceCochain, ← sub_eq_add_neg]
  exact sub_eq_sub_iff_add_eq_add.mpr
    ((torsorDifference_add F _ _ _).trans (torsorDifference_add F _ _ _).symm)

/-- Two families of local sections of a torsor have transition cocycles differing by the Čech
coboundary of their cochain of differences. -/
@[ega "IV 16.5.15" "special case"]
theorem cechD_sectionDifferenceCochain (F : Torsor X H) (Ui : I → Opens X)
    (s t : ∀ i, F.F.obj (Ui i)) :
    CechCochains.cechD Ui H.presheaf 0 (sectionDifferenceCochain F Ui s t) =
      transitionCochain F Ui t - transitionCochain F Ui s :=
  funext fun i => cechD_sectionDifferenceCochain_apply F Ui s t i

/-- The Čech class of the transition cocycle of a torsor does not depend on the chosen family of
local sections. -/
@[ega "IV 16.5.15" "special case"]
theorem cls_torsorTransitionCocycle_congr (F : Torsor X H) (Ui : I → Opens X)
    (s t : ∀ i, F.F.obj (Ui i)) :
    CechCochains.cls Ui H.presheaf (torsorTransitionCocycle F Ui t) =
      CechCochains.cls Ui H.presheaf (torsorTransitionCocycle F Ui s) :=
  QuotientAddGroup.eq_iff_sub_mem.mpr (AddSubgroup.mem_comap.mpr
    (AddMonoidHom.mem_range.mpr
      ⟨sectionDifferenceCochain F Ui s t, cechD_sectionDifferenceCochain F Ui s t⟩))

/-- A transition cocycle for a family of local sections is their cocycle of differences. -/
@[ega "IV 16.5.15" "partial"]
theorem torsorTransitionCocycle_eq_of_isTransitionCocycle (F : Torsor X H) (Ui : I → Opens X)
    (s : ∀ i, F.F.obj (Ui i)) (z : CechCochains.cocycles1 Ui H.presheaf)
    (hz : IsTransitionCocycle F Ui s z) : torsorTransitionCocycle F Ui s = z := by
  apply Subtype.ext
  funext i
  rw [torsorTransitionCocycle_val]
  exact torsorDifference_eq F _ _ _ (hz i)

/-- Isomorphic torsors have sections over the same opens. -/
theorem nonempty_sections_congr (Ui : I → Opens X) {F G : Torsor X H}
    (h : Relation.EqvGen (fun F G : Torsor X H => F.action.Iso G.action) F G) :
    (∀ i, Nonempty (F.F.obj (Ui i))) ↔ ∀ i, Nonempty (G.F.obj (Ui i)) := by
  induction h with
  | rel F G hFG =>
      obtain ⟨φ, hφ⟩ := hFG
      exact ⟨fun hs i => ⟨φ.app (Ui i) (Classical.choice (hs i))⟩,
        fun hs i => ⟨Classical.choose ((hφ (Ui i)).2 (Classical.choice (hs i)))⟩⟩
  | refl F => exact Iff.rfl
  | symm F G hFG ih => exact ih.symm
  | trans F G K hFG hGK ihFG ihGK => exact ihFG.trans ihGK

/-- The Čech class of the transition cocycle depends only on the isomorphism class of the
torsor. -/
@[ega "IV 16.5.15" "partial"]
theorem cls_torsorTransitionCocycle_eq_of_eqvGen (Ui : I → Opens X) {F G : Torsor X H}
    (h : Relation.EqvGen (fun F G : Torsor X H => F.action.Iso G.action) F G)
    (hsF : ∀ i, Nonempty (F.F.obj (Ui i))) (hsG : ∀ i, Nonempty (G.F.obj (Ui i)))
    (sF : ∀ i, F.F.obj (Ui i)) (sG : ∀ i, G.F.obj (Ui i)) :
    CechCochains.cls Ui H.presheaf (torsorTransitionCocycle F Ui sF) =
      CechCochains.cls Ui H.presheaf (torsorTransitionCocycle G Ui sG) := by
  induction h with
  | rel F G hFG =>
      obtain ⟨φ, -⟩ := hFG
      exact (congrArg (CechCochains.cls Ui H.presheaf)
            (torsorTransitionCocycle_comp φ Ui sF).symm).trans
        (cls_torsorTransitionCocycle_congr G Ui sG (fun i => φ.app (Ui i) (sF i)))
  | refl F => exact cls_torsorTransitionCocycle_congr F Ui sG sF
  | symm F G hFG ih => exact (ih hsG hsF sG sF).symm
  | trans F G K hFG hGK ihFG ihGK =>
      have hsM := (nonempty_sections_congr Ui hFG).mp hsF
      exact (ihFG hsF hsM sF (fun i => Classical.choice (hsM i))).trans
        (ihGK hsM hsG (fun i => Classical.choice (hsM i)) sG)

/-- Restricting a section of a presheaf in two steps is restricting it in one. -/
private theorem map_homOfLE_map_homOfLE_apply (P : TopCat.Presheaf AddCommGrpCat.{v} X)
    {U V W : Opens X} (h : V ≤ U) (h' : W ≤ V) (h'' : W ≤ U) (x : P.obj (op U)) :
    P.map (homOfLE h').op (P.map (homOfLE h).op x) = P.map (homOfLE h'').op x := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp]
  congr 1

/-- A torsor class is *locally trivial on* a family of opens if it has a representative with a
section over every member of the family. -/
def IsLocallyTrivialOn (H : TopCat.Sheaf AddCommGrpCat.{v} X) (Ui : I → Opens X)
    (c : TorsorClass X H) : Prop :=
  ∃ F : Torsor X H, Quotient.mk _ F = c ∧ ∀ i, Nonempty (F.F.obj (Ui i))

end Transition

/-! ## The torsor of solutions in an injective resolution -/

section Fiber

variable {X : TopCat.{u}} [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
  {I : Type w}

/-- Exactness at degree zero of an injective resolution is visible on sections of every open
set. -/
lemma resolution_kernel_preimage (H : TopCat.Sheaf AddCommGrpCat.{max u v} X)
    (J : InjectiveResolution H) (V : Opens X)
    (x : (J.cocomplex.X 0).presheaf.obj (op V))
    (hx : (J.cocomplex.d 0 1).hom.app (op V) x = 0) :
    ∃ h : H.presheaf.obj (op V), (J.ι.f 0).hom.app (op V) h = x := by
  let D := parallelPair (J.cocomplex.d 0 1) 0
  let E := TopCat.Sheaf.forget AddCommGrpCat.{max u v} X
  have hc : IsLimit (E.mapCone J.kernelFork) := isLimitOfPreserves E J.isLimitKernelFork
  let P := (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{max u v}).obj (op V)
  let : PreservesLimit (D ⋙ E) P := evaluation_preservesLimit (D ⋙ E) (op V)
  have hk : IsLimit (P.mapCone (E.mapCone J.kernelFork)) := isLimitOfPreserves P hc
  let q : AddCommGrpCat.of (ULift ℤ) ⟶ P.obj (E.obj (J.cocomplex.X 0)) :=
    AddCommGrpCat.ofHom
      { toFun := fun n => n.down • x
        map_zero' := zero_smul ℤ x
        map_add' := fun a b => add_zsmul x a.down b.down }
  have hq : q ≫ P.map (E.map (J.cocomplex.d 0 1)) = 0 := by
    ext n
    dsimp [q]
    change ((J.cocomplex.d 0 1).hom.app (op V)) (n.down • x) = 0
    rw [map_zsmul, hx, smul_zero]
  let C : Cone (D ⋙ E ⋙ P) :=
    { pt := AddCommGrpCat.of (ULift ℤ)
      π :=
        { app := fun j => match j with
            | WalkingParallelPair.zero => q
            | WalkingParallelPair.one => 0
          naturality := by
            intro i j f
            cases i <;> cases j <;> cases f
            all_goals first
              | (simp [D, E, P]; done)
              | simpa [D, E, P] using hq.symm
              | (ext n; simp) } }
  let l := hk.lift C
  have hqfac : l ≫ P.map (E.map (J.ι.f 0)) = q := hk.fac C WalkingParallelPair.zero
  refine ⟨l (ULift.up 1), ?_⟩
  have hval := congrArg (fun f : AddCommGrpCat.of (ULift ℤ) ⟶
    P.obj (E.obj (J.cocomplex.X 0)) => f (ULift.up 1)) hqfac
  rw [ConcreteCategory.comp_apply] at hval
  change (ConcreteCategory.hom ((E.map (J.ι.f 0)).app (op V)))
      (ConcreteCategory.hom l (ULift.up 1)) = (1 : ℤ) • x at hval
  change (ConcreteCategory.hom ((E.map (J.ι.f 0)).app (op V)))
      (ConcreteCategory.hom l (ULift.up 1)) = x
  simpa only [one_smul] using hval

/-- The sections over `V` of the fibre of the resolution differential over a global section `c`
of `J¹`: the solutions of `d x + c = 0` in `J⁰(V)`. -/
abbrev resolutionFiberSections (H : TopCat.Sheaf AddCommGrpCat.{max u v} X)
    (J : InjectiveResolution H) (c : (J.cocomplex.X 1).presheaf.obj (op (⊤ : Opens X)))
    (V : Opens X) :=
  {x : (J.cocomplex.X 0).presheaf.obj (op V) //
    (J.cocomplex.d 0 1).hom.app (op V) x +
      (J.cocomplex.X 1).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op c = 0}

/-- The fibre of the resolution differential over a global section `c` of `J¹`, as a presheaf of
sets. -/
def resolutionFiberPresheaf (H : TopCat.Sheaf AddCommGrpCat.{max u v} X)
    (J : InjectiveResolution H) (c : (J.cocomplex.X 1).presheaf.obj (op (⊤ : Opens X))) :
    Stacks.SpaceTorsor.PresheafOfSets.{u, max u v} X where
  obj V := resolutionFiberSections H J c V
  res {V W} h s := ⟨(J.cocomplex.X 0).presheaf.map (homOfLE h).op s.1, by
    have hnat := NatTrans.naturality_apply (J.cocomplex.d 0 1).hom (homOfLE h).op s.1
    have hc : (J.cocomplex.X 1).presheaf.map (homOfLE h).op
        ((J.cocomplex.X 1).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op c) =
        (J.cocomplex.X 1).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op c := by
      rw [← ConcreteCategory.comp_apply, ← (J.cocomplex.X 1).presheaf.map_comp]
      congr 1
    change (J.cocomplex.d 0 1).hom.app (op W)
        ((J.cocomplex.X 0).presheaf.map (homOfLE h).op s.1) + _ = 0
    rw [hnat, ← hc, ← map_add, s.2]
    simp⟩
  res_self := by
    intro V s
    apply Subtype.ext
    simp
  res_comp := by
    intro U V W hWV hVU s
    apply Subtype.ext
    change ((J.cocomplex.X 0).presheaf.map (homOfLE hWV).op)
        ((J.cocomplex.X 0).presheaf.map (homOfLE hVU).op s.1) = _
    calc
      _ = ((J.cocomplex.X 0).presheaf.map (homOfLE hVU).op ≫
          (J.cocomplex.X 0).presheaf.map (homOfLE hWV).op) s.1 := by
            rw [← ConcreteCategory.comp_apply]
      _ = (J.cocomplex.X 0).presheaf.map ((homOfLE hVU).op ≫ (homOfLE hWV).op) s.1 := by
            rw [← (J.cocomplex.X 0).presheaf.map_comp]
      _ = (J.cocomplex.X 0).presheaf.map (homOfLE (hWV.trans hVU)).op s.1 := by
            congr 1

/-- If a section `x` of `J⁰` glues a family of local solutions of `d x + c = 0`, then its defect
`d x + c` restricts to zero on every member of the family. -/
lemma isGluing_zero_resolutionFiber_defect (H : TopCat.Sheaf AddCommGrpCat.{max u v} X)
    (J : InjectiveResolution H) (c : (J.cocomplex.X 1).presheaf.obj (op (⊤ : Opens X)))
    {ι : Type*} (V : ι → Opens X) (loc : ∀ i, resolutionFiberSections H J c (V i))
    (x : (J.cocomplex.X 0).presheaf.obj (op (⨆ i, V i)))
    (hxglue : (J.cocomplex.X 0).presheaf.IsGluing V (fun i => (loc i).1) x) :
    (J.cocomplex.X 1).presheaf.IsGluing V (fun _ => 0)
      ((J.cocomplex.d 0 1).hom.app (op (⨆ i, V i)) x +
        (J.cocomplex.X 1).presheaf.map (homOfLE (le_top : (⨆ i, V i) ≤ ⊤)).op c) := by
  intro i
  change (J.cocomplex.X 1).presheaf.map (homOfLE (le_iSup V i)).op
    ((J.cocomplex.d 0 1).hom.app (op (⨆ i, V i)) x +
      (J.cocomplex.X 1).presheaf.map (homOfLE (le_top : (⨆ i, V i) ≤ ⊤)).op c) = 0
  rw [map_add]
  have hnat' : (J.cocomplex.X 1).presheaf.map (homOfLE (le_iSup V i)).op
      ((J.cocomplex.d 0 1).hom.app (op (⨆ i, V i)) x) =
        (J.cocomplex.d 0 1).hom.app (op (V i))
          ((J.cocomplex.X 0).presheaf.map (homOfLE (le_iSup V i)).op x) :=
    (NatTrans.naturality_apply (J.cocomplex.d 0 1).hom (homOfLE (le_iSup V i)).op x).symm
  have hxi : (J.cocomplex.X 0).presheaf.map (homOfLE (le_iSup V i)).op x = (loc i).1 := by
    convert hxglue i using 1
    congr 1
  have hc := map_homOfLE_map_homOfLE_apply (J.cocomplex.X 1).presheaf
    (le_top : (⨆ i, V i) ≤ ⊤) (le_iSup V i) (le_top : V i ≤ ⊤) c
  rw [hnat', hxi, hc]
  exact (loc i).2

/-- The fibre of the resolution differential is a sheaf: `J⁰` and `J¹` are sheaves, so a
compatible family of local solutions glues to a section of `J⁰` whose defect glues to zero. -/
lemma resolutionFiberPresheaf_isSheaf (H : TopCat.Sheaf AddCommGrpCat.{max u v} X)
    (J : InjectiveResolution H) (c : (J.cocomplex.X 1).presheaf.obj (op (⊤ : Opens X))) :
    (resolutionFiberPresheaf H J c).IsSheaf := by
  classical
  intro U ι V hV hU
  subst U
  let P₀ := J.cocomplex.X 0
  let P₁ := J.cocomplex.X 1
  let F := resolutionFiberPresheaf H J c
  have h₀ : P₀.presheaf.IsSheaf := P₀.property
  have h₁ : P₁.presheaf.IsSheaf := P₁.property
  constructor
  · intro a b hab
    obtain ⟨x, _, huniq⟩ := h₀.isSheafUniqueGluing V
      (fun i => (F.res (le_iSup V i) a).1) (by
        intro i j
        dsimp [F, resolutionFiberPresheaf]
        change P₀.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op
            (P₀.presheaf.map (homOfLE (le_iSup V i)).op a.1) =
          P₀.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op
            (P₀.presheaf.map (homOfLE (le_iSup V j)).op a.1)
        rw [map_homOfLE_map_homOfLE_apply P₀.presheaf _ _ ((inf_le_left : V i ⊓ V j ≤ V i).trans
            (le_iSup V i)), map_homOfLE_map_homOfLE_apply P₀.presheaf _ _
            ((inf_le_right : V i ⊓ V j ≤ V j).trans (le_iSup V j))])
    have hb : P₀.presheaf.IsGluing V (fun i => (F.res (le_iSup V i) a).1) b.1 := by
      intro i
      have hi := congrArg (fun f : F.CompatibleFamily V => f.1 i) hab
      change (F.res (le_iSup V i) b).1 = (F.res (le_iSup V i) a).1
      exact (congrArg Subtype.val hi).symm
    exact Subtype.ext ((huniq a.1 fun _ => rfl).trans (huniq b.1 hb).symm)
  · intro a
    let loc : ∀ i, resolutionFiberSections H J c (V i) := a.1
    obtain ⟨x, hxglue, -⟩ := h₀.isSheafUniqueGluing V (fun i => (loc i).1) (by
      intro i j
      exact congrArg Subtype.val (a.2 i j (V i ⊓ V j) inf_le_left inf_le_right))
    let y : P₁.presheaf.obj (op (⨆ i, V i)) :=
      (J.cocomplex.d 0 1).hom.app (op (⨆ i, V i)) x +
        P₁.presheaf.map (homOfLE (le_top : (⨆ i, V i) ≤ ⊤)).op c
    obtain ⟨_, -, huniq⟩ := h₁.isSheafUniqueGluing V
      (fun i => (0 : P₁.presheaf.obj (op (V i)))) (by
        intro i j
        change P₁.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op 0 =
          P₁.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op 0
        simp)
    have hzglue : P₁.presheaf.IsGluing V (fun i => (0 : P₁.presheaf.obj (op (V i))))
        (0 : P₁.presheaf.obj (op (⨆ i, V i))) := by
      intro i
      simp
    have hy : y = 0 := (huniq y (isGluing_zero_resolutionFiber_defect H J c V loc x hxglue)).trans
      (huniq 0 hzglue).symm
    exact ⟨⟨x, hy⟩, Subtype.ext (funext fun i => Subtype.ext (hxglue i))⟩

/-- The fibre of the resolution differential over a global section `c` of `J¹`, as a sheaf of
sets. -/
def resolutionFiberSheaf (H : TopCat.Sheaf AddCommGrpCat.{max u v} X)
    (J : InjectiveResolution H) (c : (J.cocomplex.X 1).presheaf.obj (op (⊤ : Opens X))) :
    Stacks.SpaceTorsor.SheafOfSets.{u, max u v} X where
  toPresheafOfSets := resolutionFiberPresheaf H J c
  isSheaf := resolutionFiberPresheaf_isSheaf H J c

/-- The action of `H` on the fibre of the resolution differential, by adding the image of a
section of `H` under the resolution inclusion. -/
def resolutionFiberAction (H : TopCat.Sheaf AddCommGrpCat.{max u v} X)
    (J : InjectiveResolution H) (c : (J.cocomplex.X 1).presheaf.obj (op (⊤ : Opens X))) :
    Stacks.SpaceTorsor.Action (underlyingPresheafOfGroups X H)
      (resolutionFiberPresheaf H J c) where
  act {U} g s := ⟨s.1 + (J.ι.f 0).hom.app (op U) g.toAdd, by
    change (J.cocomplex.d 0 1).hom.app (op U)
        (s.1 + (J.ι.f 0).hom.app (op U) g.toAdd) + _ = 0
    rw [map_add, CechOne.ι_d_app X H J U g.toAdd]
    simpa only [add_zero] using s.2⟩
  one_act {U} s := by
    apply Subtype.ext
    change s.1 + (J.ι.f 0).hom.app (op U) 0 = s.1
    rw [map_zero, add_zero]
  mul_act {U} g h s := by
    let : AddCommGroup (H.presheaf.obj (op U) : Type _) := (H.presheaf.obj (op U)).str
    change Multiplicative (H.presheaf.obj (op U) : Type _) at g h
    apply Subtype.ext
    change s.1 + (J.ι.f 0).hom.app (op U) (g * h).toAdd =
      (s.1 + (J.ι.f 0).hom.app (op U) h.toAdd) + (J.ι.f 0).hom.app (op U) g.toAdd
    rw [toAdd_mul g h]
    change s.1 + (AddCommGrpCat.Hom.hom ((J.ι.f 0).hom.app (op U)))
        (g.toAdd + h.toAdd) =
      (s.1 + (AddCommGrpCat.Hom.hom ((J.ι.f 0).hom.app (op U))) h.toAdd) +
        (AddCommGrpCat.Hom.hom ((J.ι.f 0).hom.app (op U))) g.toAdd
    calc
      _ = s.1 + ((AddCommGrpCat.Hom.hom ((J.ι.f 0).hom.app (op U))) g.toAdd +
          (AddCommGrpCat.Hom.hom ((J.ι.f 0).hom.app (op U))) h.toAdd) :=
            congrArg (fun x => s.1 + x)
              ((J.ι.f 0).hom.app (op U) |>.hom.map_add g.toAdd h.toAdd)
      _ = _ := by abel
  res_act {U V} hVU g s := by
    apply Subtype.ext
    change (J.cocomplex.X 0).presheaf.map (homOfLE hVU).op
        (s.1 + (J.ι.f 0).hom.app (op U) g.toAdd) = _
    rw [map_add, (NatTrans.naturality_apply (J.ι.f 0).hom (homOfLE hVU).op g.toAdd).symm]
    rfl

variable (H : TopCat.Sheaf AddCommGrpCat.{max u v} X) (Ui : I → Opens X)
  (hUi : (⊤ : Opens X) = ⨆ i, Ui i)

/-- The global section of `J¹` carried by an injective-resolution representative of a Čech
cocycle. -/
abbrev resolutionRepresentativeCycle (J : InjectiveResolution H)
    (z : CechCochains.cocycles1 Ui H.presheaf)
    (r : CechOne.CechOneResolutionRepresentative X ⊤ Ui hUi H J z) :=
  (CechOne.abelianResolutionSections X ⊤ J).iCycles 1 r.cycle

/-- The zero-cochain of a representative gives a solution of `d x + c = 0` over every member of
the covering. -/
def resolutionFiberLocalSection (J : InjectiveResolution H)
    (z : CechCochains.cocycles1 Ui H.presheaf)
    (r : CechOne.CechOneResolutionRepresentative X ⊤ Ui hUi H J z) (i : I) :
    resolutionFiberSections H J (resolutionRepresentativeCycle H Ui hUi J z r) (Ui i) := by
  let V := CechCochains.inter Ui (fun _ : Fin 1 => i)
  let b := r.b (fun _ : Fin 1 => i)
  let f : (op V) ⟶ op (Ui i) := (homOfLE (CechCochains.le_inter_const Ui i)).op
  let P₀ := J.cocomplex.X 0
  let P₁ := J.cocomplex.X 1
  let c := resolutionRepresentativeCycle H Ui hUi J z r
  have hd : (J.cocomplex.d 0 1).hom.app (op (Ui i)) (P₀.presheaf.map f b) =
      P₁.presheaf.map f ((J.cocomplex.d 0 1).hom.app (op V) b) :=
    NatTrans.naturality_apply (J.cocomplex.d 0 1).hom f b
  have hcv : P₁.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op c =
      -((J.cocomplex.d 0 1).hom.app (op V) b) := by
    have hr := r.restriction (fun _ : Fin 1 => i)
    dsimp [resolutionRepresentativeCycle] at hr
    exact hr
  have hc : P₁.presheaf.map f (P₁.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op c) =
      P₁.presheaf.map (homOfLE (le_top : Ui i ≤ ⊤)).op c := by
    rw [← ConcreteCategory.comp_apply, ← P₁.presheaf.map_comp]
    congr 1
  have hz : (J.cocomplex.d 0 1).hom.app (op V) b +
      P₁.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op c = 0 := by
    rw [hcv]
    abel
  have hzero : P₁.presheaf.map f ((J.cocomplex.d 0 1).hom.app (op V) b) +
      P₁.presheaf.map f (P₁.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op c) = 0 := by
    have hh := congrArg (fun x => (P₁.presheaf.map f).hom x) hz
    rwa [map_add, map_zero] at hh
  refine ⟨P₀.presheaf.map f b, ?_⟩
  change (J.cocomplex.d 0 1).hom.app (op (Ui i)) (P₀.presheaf.map f b) +
      P₁.presheaf.map (homOfLE (le_top : Ui i ≤ ⊤)).op c = 0
  rwa [hd, ← hc]

/-- The local solutions of a representative, restricted to a smaller open, are the restrictions
of its zero-cochain. -/
lemma resolutionFiberLocalSection_restrict (J : InjectiveResolution H)
    (z : CechCochains.cocycles1 Ui H.presheaf)
    (r : CechOne.CechOneResolutionRepresentative X ⊤ Ui hUi H J z) (i : I) {V : Opens X}
    (hV : V ≤ Ui i) :
    (J.cocomplex.X 0).presheaf.map (homOfLE hV).op
        (resolutionFiberLocalSection H Ui hUi J z r i).1 =
      (J.cocomplex.X 0).presheaf.map
        (homOfLE (hV.trans (CechCochains.le_inter_const Ui i))).op (r.b (fun _ : Fin 1 => i)) := by
  let f : (op (CechCochains.inter Ui (fun _ : Fin 1 => i))) ⟶ op (Ui i) :=
    (homOfLE (CechCochains.le_inter_const Ui i)).op
  let P := (J.cocomplex.X 0).presheaf
  change P.map (homOfLE hV).op (P.map f (r.b (fun _ : Fin 1 => i))) = _
  exact map_homOfLE_map_homOfLE_apply _ _ _ _ _

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}] in
/-- The value of a Čech zero-cochain on an open contained in two equal intersections does not
depend on which index tuple is used. -/
lemma cechZeroRestriction_congr (Ui : I → Opens X)
    (P : TopCat.Presheaf AddCommGrpCat.{max u v} X) (b : CechCochains.Cochain Ui P 0)
    {i j : Fin 1 → I} (hij : i = j) {W : Opens X} (hi : W ≤ CechCochains.inter Ui i)
    (hj : W ≤ CechCochains.inter Ui j) :
    CechCochains.restr P hi (b i) = CechCochains.restr P hj (b j) := by
  cases hij
  rfl

/-- The degree-zero map of an injective resolution is injective on sections over every open. -/
lemma injectiveResolution_ι_app_injective (H : TopCat.Sheaf AddCommGrpCat.{max u v} X)
    (J : InjectiveResolution H) (U : Opens X) :
    Function.Injective ((J.ι.f 0).hom.app (op U)) :=
  (AddCommGrpCat.mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app _).mp
    (Functor.map_mono (TopCat.Sheaf.forget AddCommGrpCat.{max u v} X) (J.ι.f 0)) (op U))

/-- The fibre of the resolution differential is a torsor under `H`: the action is simply
transitive because `H` is the kernel of the differential on `J⁰`, and the zero-cochain of the
representative provides sections near every point. -/
lemma resolutionFiberAction_isTorsor (J : InjectiveResolution H)
    (z : CechCochains.cocycles1 Ui H.presheaf)
    (r : CechOne.CechOneResolutionRepresentative X ⊤ Ui hUi H J z) :
    (resolutionFiberAction H J (resolutionRepresentativeCycle H Ui hUi J z r)).IsTorsor := by
  classical
  constructor
  · rintro U ⟨s⟩
    refine ⟨⟨s⟩, fun s t => ?_⟩
    let d := (J.cocomplex.d 0 1).hom.app (op U)
    have hdt : d t.1 = d s.1 :=
      (eq_neg_of_add_eq_zero_left t.2).trans (eq_neg_of_add_eq_zero_left s.2).symm
    have hd : d (t.1 - s.1) = 0 := by rw [map_sub, hdt, sub_self]
    obtain ⟨g, hg⟩ := resolution_kernel_preimage H J U (t.1 - s.1) hd
    have hg' : s.1 + (J.ι.f 0).hom.app (op U) g = t.1 := by
      rw [hg]
      abel
    refine ⟨Multiplicative.ofAdd g, Subtype.ext hg', fun h hh => ?_⟩
    have hh' := congrArg Subtype.val hh
    change s.1 + (J.ι.f 0).hom.app (op U) h.toAdd = t.1 at hh'
    exact congrArg Multiplicative.ofAdd
      (injectiveResolution_ι_app_injective H J U (add_left_cancel (hh'.trans hg'.symm)))
  · intro x
    obtain ⟨i, hxi⟩ : ∃ i, x ∈ Ui i := by
      apply Opens.mem_iSup.mp
      rw [← hUi]
      trivial
    exact ⟨Ui i, hxi, ⟨resolutionFiberLocalSection H Ui hUi J z r i⟩⟩

/-- The torsor under `H` attached to an injective-resolution representative of a Čech cocycle:
the sheaf of solutions of `d x + c = 0` in `J⁰`, where `c` is the representative's global
cocycle. -/
def resolutionFiberTorsor (J : InjectiveResolution H)
    (z : CechCochains.cocycles1 Ui H.presheaf)
    (r : CechOne.CechOneResolutionRepresentative X ⊤ Ui hUi H J z) : Torsor X H where
  F := resolutionFiberSheaf H J (resolutionRepresentativeCycle H Ui hUi J z r)
  action := resolutionFiberAction H J (resolutionRepresentativeCycle H Ui hUi J z r)
  isTorsor := resolutionFiberAction_isTorsor H Ui hUi J z r

/-- The local sections of the fibre torsor supplied by the representative's zero-cochain. -/
def resolutionFiberLocalSections (J : InjectiveResolution H)
    (z : CechCochains.cocycles1 Ui H.presheaf)
    (r : CechOne.CechOneResolutionRepresentative X ⊤ Ui hUi H J z) :
    ∀ i, (resolutionFiberTorsor H Ui hUi J z r).F.obj (Ui i) :=
  fun i => resolutionFiberLocalSection H Ui hUi J z r i

/-- The local solution of a representative over `Ui (i m)`, restricted to the overlap of `i`, is
the restriction of its zero-cochain at the face of `i` omitting `k`, when that face is `i m`. -/
lemma map_resolutionFiberLocalSections_eq_restr (J : InjectiveResolution H)
    (z : CechCochains.cocycles1 Ui H.presheaf)
    (r : CechOne.CechOneResolutionRepresentative X ⊤ Ui hUi H J z) (i : Fin 2 → I)
    (m k : Fin 2) (hidx : i ∘ Fin.succAbove k = fun _ : Fin 1 => i m) :
    (J.cocomplex.X 0).presheaf.map (homOfLE (CechCochains.inter_le Ui i m)).op
        (resolutionFiberLocalSections H Ui hUi J z r (i m)).1 =
      CechCochains.restr (J.cocomplex.X 0).presheaf (CechCochains.inter_le_omit Ui i k)
        (r.b (i ∘ Fin.succAbove k)) := by
  have hlocal := resolutionFiberLocalSection_restrict H Ui hUi J z r (i m)
    (CechCochains.inter_le Ui i m)
  calc
    _ = (J.cocomplex.X 0).presheaf.map
        (homOfLE ((CechCochains.inter_le Ui i m).trans
          (CechCochains.le_inter_const Ui (i m)))).op (r.b (fun _ : Fin 1 => i m)) := by
          simpa [resolutionFiberLocalSections] using hlocal
    _ = _ :=
      cechZeroRestriction_congr Ui (J.cocomplex.X 0).presheaf r.b hidx.symm
        ((CechCochains.inter_le Ui i m).trans (CechCochains.le_inter_const Ui (i m)))
        (CechCochains.inter_le_omit Ui i k)

/-- The cocycle a representative came from is the transition cocycle of the local sections of
its fibre torsor: that is exactly the representative's coboundary equation. -/
@[ega "IV 16.5.15" "partial"]
lemma resolutionFiberTorsor_isTransitionCocycle (J : InjectiveResolution H)
    (z : CechCochains.cocycles1 Ui H.presheaf)
    (r : CechOne.CechOneResolutionRepresentative X ⊤ Ui hUi H J z) :
    IsTransitionCocycle (resolutionFiberTorsor H Ui hUi J z r) Ui
      (resolutionFiberLocalSections H Ui hUi J z r) z := by
  classical
  intro i
  apply Subtype.ext
  change (J.cocomplex.X 0).presheaf.map (homOfLE (CechCochains.inter_le Ui i 0)).op
      (resolutionFiberLocalSections H Ui hUi J z r (i 0)).1 +
        (J.ι.f 0).hom.app (op (CechCochains.inter Ui i)) (z.val i) =
    (J.cocomplex.X 0).presheaf.map (homOfLE (CechCochains.inter_le Ui i 1)).op
      (resolutionFiberLocalSections H Ui hUi J z r (i 1)).1
  have hcb := r.coboundary i
  rw [CechCochains.cechD_apply, Fin.sum_univ_two] at hcb
  norm_num at hcb
  have hcb' :
      CechCochains.restr (J.cocomplex.X 0).presheaf (CechCochains.inter_le_omit Ui i 0)
          (r.b (i ∘ Fin.succAbove 0)) -
        CechCochains.restr (J.cocomplex.X 0).presheaf (CechCochains.inter_le_omit Ui i 1)
          (r.b (i ∘ Fin.succAbove 1)) =
        (J.ι.f 0).hom.app (op (CechCochains.inter Ui i)) (z.val i) := by
    simpa only [sub_eq_add_neg] using hcb
  rw [map_resolutionFiberLocalSections_eq_restr H Ui hUi J z r i 0 1
      (by funext j; fin_cases j; rfl),
    map_resolutionFiberLocalSections_eq_restr H Ui hUi J z r i 1 0
      (by funext j; fin_cases j; rfl), ← hcb']
  abel

/-- The fibre torsor of a representative has a section over every member of the covering. -/
lemma resolutionFiberTorsor_locallyTrivial (J : InjectiveResolution H)
    (z : CechCochains.cocycles1 Ui H.presheaf)
    (r : CechOne.CechOneResolutionRepresentative X ⊤ Ui hUi H J z) :
    IsLocallyTrivialOn H Ui (Quotient.mk _ (resolutionFiberTorsor H Ui hUi J z r)) :=
  ⟨resolutionFiberTorsor H Ui hUi J z r, rfl,
    fun i => ⟨resolutionFiberLocalSections H Ui hUi J z r i⟩⟩

/-- The class of the fibre torsor of a representative is the comparison image of the Čech class
it came from. -/
lemma torsorClassEquivSheafCohomologyOne_resolutionFiberTorsor (J : InjectiveResolution H)
    (z : CechCochains.cocycles1 Ui H.presheaf)
    (r : CechOne.CechOneResolutionRepresentative X ⊤ Ui hUi H J z) :
    torsorClassEquivSheafCohomologyOne X H
        (Quotient.mk _ (resolutionFiberTorsor H Ui hUi J z r)) =
      CechOne.cechH1ToRightDerivedSections X ⊤ Ui hUi H (CechCochains.cls Ui H.presheaf z) :=
  torsorClassEquivSheafCohomologyOne_of_cocycle X H (resolutionFiberTorsor H Ui hUi J z r) Ui
    hUi (resolutionFiberLocalSections H Ui hUi J z r) z
    (resolutionFiberTorsor_isTransitionCocycle H Ui hUi J z r)

end Fiber

/-! ## The identification of first Čech cohomology -/

section Identification

variable {X : TopCat.{u}} [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
  {I : Type w} (H : TopCat.Sheaf AddCommGrpCat.{max u v} X) (Ui : I → Opens X)
  (hUi : (⊤ : Opens X) = ⨆ i, Ui i)

/-- A chosen injective-resolution representative of a Čech cocycle, in the canonical injective
resolution. -/
def chosenResolutionRepresentative (z : CechCochains.cocycles1 Ui H.presheaf) :
    CechOne.CechOneResolutionRepresentative X ⊤ Ui hUi H (injectiveResolution H) z :=
  Classical.choose (CechOne.exists_cechOneResolutionRepresentative X ⊤ Ui hUi H
    (injectiveResolution H) z)

/-- The locally trivial torsor class attached to a Čech cocycle. -/
@[ega "IV 16.5.15" "partial"]
def cocycleToLocallyTrivialClass (z : CechCochains.cocycles1 Ui H.presheaf) :
    {c : TorsorClass X H // IsLocallyTrivialOn H Ui c} :=
  ⟨Quotient.mk _
      (resolutionFiberTorsor H Ui hUi (injectiveResolution H) z (chosenResolutionRepresentative H Ui
        hUi z)),
    resolutionFiberTorsor_locallyTrivial H Ui hUi (injectiveResolution H) z
      (chosenResolutionRepresentative H Ui hUi z)⟩

/-- The class of the torsor attached to a Čech cocycle is the comparison image of the
cocycle's Čech class. -/
lemma cocycleToLocallyTrivialClass_cohomology (z : CechCochains.cocycles1 Ui H.presheaf) :
    torsorClassEquivSheafCohomologyOne X H (cocycleToLocallyTrivialClass H Ui hUi z).1 =
      CechOne.cechH1ToRightDerivedSections X ⊤ Ui hUi H (CechCochains.cls Ui H.presheaf z) :=
  torsorClassEquivSheafCohomologyOne_resolutionFiberTorsor H Ui hUi (injectiveResolution H) z
    (chosenResolutionRepresentative H Ui hUi z)

/-- The locally trivial torsor class attached to a Čech cohomology class. -/
def cechH1ToLocallyTrivialClass :
    CechCochains.CechH1 Ui H.presheaf → {c : TorsorClass X H // IsLocallyTrivialOn H Ui c} :=
  Quotient.lift (cocycleToLocallyTrivialClass H Ui hUi) (by
    intro z z' hzz'
    apply Subtype.ext
    apply (torsorClassEquivSheafCohomologyOne X H).injective
    rw [cocycleToLocallyTrivialClass_cohomology, cocycleToLocallyTrivialClass_cohomology]
    exact congrArg (CechOne.cechH1ToRightDerivedSections X ⊤ Ui hUi H) (Quotient.sound hzz'))

/-- The locally trivial class attached to a Čech cohomology class has that class's comparison
image as its cohomology class. -/
lemma cechH1ToLocallyTrivialClass_cohomology (z : CechCochains.CechH1 Ui H.presheaf) :
    torsorClassEquivSheafCohomologyOne X H (cechH1ToLocallyTrivialClass H Ui hUi z).1 =
      CechOne.cechH1ToRightDerivedSections X ⊤ Ui hUi H z :=
  Quotient.inductionOn z (cocycleToLocallyTrivialClass_cohomology H Ui hUi)

/-- The Čech cohomology class of a locally trivial torsor class: the class of the transition
cocycle of any family of local sections of any representative. -/
@[sga "4½ Cycle 1.1.2" "partial"]
def locallyTrivialClassToCechH1
    (c : {c : TorsorClass X H // IsLocallyTrivialOn H Ui c}) : CechCochains.CechH1 Ui H.presheaf :=
  CechCochains.cls Ui H.presheaf
    (torsorTransitionCocycle (Classical.choose c.2) Ui
      (fun i => Classical.choice ((Classical.choose_spec c.2).2 i)))

/-- Passing from a locally trivial torsor class to its Čech class and back is the identity. -/
@[ega "IV 16.5.15" "partial"]
lemma cechH1ToLocallyTrivialClass_locallyTrivialClassToCechH1
    (c : {c : TorsorClass X H // IsLocallyTrivialOn H Ui c}) :
    cechH1ToLocallyTrivialClass H Ui hUi (locallyTrivialClassToCechH1 H Ui c) = c := by
  classical
  set F := Classical.choose c.2
  set s : ∀ i, F.F.obj (Ui i) := fun i => Classical.choice ((Classical.choose_spec c.2).2 i)
  apply Subtype.ext
  rw [← (Classical.choose_spec c.2).1]
  apply (torsorClassEquivSheafCohomologyOne X H).injective
  rw [cechH1ToLocallyTrivialClass_cohomology]
  exact (torsorClassEquivSheafCohomologyOne_of_cocycle X H F Ui hUi s
    (torsorTransitionCocycle F Ui s) (torsorTransitionCocycle_spec F Ui s)).symm

/-- Passing from a Čech cohomology class to a locally trivial torsor class and back is the
identity. -/
@[ega "IV 16.5.15" "partial"]
lemma locallyTrivialClassToCechH1_cechH1ToLocallyTrivialClass
    (z : CechCochains.CechH1 Ui H.presheaf) :
    locallyTrivialClassToCechH1 H Ui (cechH1ToLocallyTrivialClass H Ui hUi z) = z := by
  classical
  refine Quotient.inductionOn z fun z => ?_
  set c := cocycleToLocallyTrivialClass H Ui hUi z
  set F := Classical.choose c.2
  set s : ∀ i, F.F.obj (Ui i) := fun i => Classical.choice ((Classical.choose_spec c.2).2 i)
  set r := chosenResolutionRepresentative H Ui hUi z
  set Fz := resolutionFiberTorsor H Ui hUi (injectiveResolution H) z r
  set sz := resolutionFiberLocalSections H Ui hUi (injectiveResolution H) z r
  have hrel : Relation.EqvGen (fun F G : Torsor X H => F.action.Iso G.action) F Fz :=
    Quotient.exact (Classical.choose_spec c.2).1
  have hclass := cls_torsorTransitionCocycle_eq_of_eqvGen Ui hrel
    ((Classical.choose_spec c.2).2) (fun i => ⟨sz i⟩) s sz
  have hcanonical : torsorTransitionCocycle Fz Ui sz = z :=
    torsorTransitionCocycle_eq_of_isTransitionCocycle Fz Ui sz z
      (resolutionFiberTorsor_isTransitionCocycle H Ui hUi (injectiveResolution H) z r)
  change CechCochains.cls Ui H.presheaf (torsorTransitionCocycle F Ui s) =
    CechCochains.cls Ui H.presheaf z
  rw [hclass, hcanonical]

/-- **Stacks Project, Tag 0B8R.** First Čech cohomology of an open covering is in canonical
bijection with the set of isomorphism classes of torsors which are trivial on every member of
the covering. -/
@[stacks 0B8R "identification with locally trivial torsors",
  sga "4½ Cycle 1.1.2" "cocycle ↔ torsor class", ega "IV 16.5.15" "partial"]
def cechH1EquivLocallyTrivialTorsorClass :
    CechCochains.CechH1 Ui H.presheaf ≃ {c : TorsorClass X H // IsLocallyTrivialOn H Ui c} where
  toFun := cechH1ToLocallyTrivialClass H Ui hUi
  invFun := locallyTrivialClassToCechH1 H Ui
  left_inv := locallyTrivialClassToCechH1_cechH1ToLocallyTrivialClass H Ui hUi
  right_inv := cechH1ToLocallyTrivialClass_locallyTrivialClassToCechH1 H Ui hUi

/-- **Stacks Project, Tag 0B8R.** The bijection of
`cechH1EquivLocallyTrivialTorsorClass` is the one induced by the canonical comparison to first
sheaf cohomology and the classification of torsors of Tag 02FQ. -/
@[stacks 0B8R "identification with locally trivial torsors"]
theorem torsorClassEquivSheafCohomologyOne_cechH1Equiv (z : CechCochains.CechH1 Ui H.presheaf) :
    torsorClassEquivSheafCohomologyOne X H
        (cechH1EquivLocallyTrivialTorsorClass H Ui hUi z).1 =
      CechOne.cechH1ToRightDerivedSections X ⊤ Ui hUi H z :=
  cechH1ToLocallyTrivialClass_cohomology H Ui hUi z

/-- **Stacks Project, Tag 0B8R.** The canonical additive comparison from first Čech cohomology
of an open covering to first sheaf cohomology is injective. -/
@[stacks 0B8R "injectivity"]
theorem cechH1ToRightDerivedSections_injective :
    Function.Injective (CechOne.cechH1ToRightDerivedSections X ⊤ Ui hUi H) := by
  intro a b hab
  apply (cechH1EquivLocallyTrivialTorsorClass H Ui hUi).injective
  apply Subtype.ext
  apply (torsorClassEquivSheafCohomologyOne X H).injective
  rwa [torsorClassEquivSheafCohomologyOne_cechH1Equiv,
    torsorClassEquivSheafCohomologyOne_cechH1Equiv]

end Identification

add_to_stacks 0B8R "the canonical comparison map"
  Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections

end Stacks.Cohomology.SheafTorsor
