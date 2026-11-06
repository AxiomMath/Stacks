module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Sites.Preserves
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardPhRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.V.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.V.PhComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.V.StandardCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Vtopology.Permanence

/-!
# Recognizing sheaves for the V topology

A presheaf on schemes is a sheaf for the V topology exactly when it is a Zariski sheaf and
satisfies the sheaf condition for standard V coverings of affine schemes. For a single morphism
of affine schemes the standard V sheaf condition is the equalizer condition for that one arrow.

## Main results

* `AlgebraicGeometry.isVSheaf_iff_zariski_and_standard` reduces the V sheaf condition to the
  Zariski sheaf condition together with the standard V coverings of affine schemes.
* `AlgebraicGeometry.isStandardVSheaf_iff_singleton` reduces the standard V sheaf condition on
  an affine scheme to the single-arrow case.

## Implementation notes

The reduction glues a section from local data on an affine open cover of the target, so the bulk
of the work is the compatibility of those local sections: the descent data is assembled on each
affine open, matched on overlaps, and then recombined. Zariski coverings are V coverings via the
ph topology, by composing `AlgebraicGeometry.IsPHCovering.of_openCover` with
`AlgebraicGeometry.isVCovering_of_isPHCovering`. The index type of a standard V covering is
shrunk to the universe of the schemes before the covering is pulled back, which is why the
transport along `eqToHom` of the index equivalence appears.

## References

* [Stacks Project, Tag 0ETM](https://stacks.math.columbia.edu/tag/0ETM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v w

namespace AlgebraicGeometry

/-- A choice of affine open neighbourhood of a point of a scheme. -/
noncomputable def affineOpenNbhd (T : Scheme.{u}) (x : T) : T.Opens :=
  Classical.choose (exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp))

/-- The chosen affine open neighbourhood of a point is affine and contains the point. -/
lemma affineOpenNbhd_spec (T : Scheme.{u}) (x : T) :
    IsAffineOpen (affineOpenNbhd T x) ∧ x ∈ affineOpenNbhd T x :=
  (Classical.choose_spec
    (exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp))).imp_right
      (fun h => h.1)

/-- The covering of a scheme by the chosen affine open neighbourhoods of its points, with index
type raised to any larger universe. -/
noncomputable def affineOpenCover (T : Scheme.{u}) : T.OpenCover.{max u v} where
  I₀ := ULift.{max u v} T
  X x := affineOpenNbhd T x.down
  f x := (affineOpenNbhd T x.down).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, ?_⟩
    · exact ⟨ULift.up x, ⟨x, (affineOpenNbhd_spec T x).2⟩, by simp⟩
    · intro x
      infer_instance

/-- A standard V covering stays one after raising the universe of its index type. -/
private theorem isStandardVCovering_uliftIndex {T : Scheme.{u}} [IsAffine T] {I : Type v}
    [Finite I] {X : I → Scheme.{u}} [∀ i, IsAffine (X i)] {f : ∀ i, X i ⟶ T}
    (hf : AlgebraicGeometry.IsStandardVCovering X f) :
    AlgebraicGeometry.IsStandardVCovering (fun j : ULift.{w} I ↦ X j.down)
      (fun j ↦ f j.down) := by
  intro V _ _ _ a
  obtain ⟨W, hW₁, hW₂, hW₃, r, hr, i, k, hk⟩ := hf V a
  exact ⟨W, hW₁, hW₂, hW₃, r, hr, ULift.up i, k, hk⟩

private structure LocalDescentData {T : Scheme.{u}} {I : Type v}
    {F : Scheme.{u}ᵒᵖ ⥤ Type w} (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (x : ∀ i, F.obj (op (X i))) (U : T.Opens) (hU : IsAffineOpen U) where
  E : PreZeroHypercover.{max u v} U.toScheme
  finite : Finite E.I₀
  affine : ∀ j, IsAffine (E.X j)
  standard : @AlgebraicGeometry.IsStandardVCovering U.toScheme hU
    E.I₀ finite E.X affine E.f
  index : E.I₀ → I
  toOriginal : ∀ j, E.X j ⟶ X (index j)
  toOriginal_over : ∀ j, toOriginal j ≫ f (index j) = E.f j ≫ U.ι
  localSection : F.obj (op U.toScheme)
  glue : ∀ j, F.map (E.f j).op localSection =
    F.map (toOriginal j).op (x (index j))

private lemma exists_localDescentData {T : Scheme.{u}} {I : Type v}
    {F : Scheme.{u}ᵒᵖ ⥤ Type w} (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (x : ∀ i, F.obj (op (X i)))
    (hx : Presieve.Arrows.Compatible F f x)
    (hstd : ∀ (U : Scheme.{u}) [IsAffine U] (J : Type (max u v)) [Finite J]
      (Y : J → Scheme.{u}) [∀ j, IsAffine (Y j)] (g : ∀ j, Y j ⟶ U),
      AlgebraicGeometry.IsStandardVCovering Y g →
        (Presieve.ofArrows Y g).IsSheafFor F)
    (hf : AlgebraicGeometry.IsVCovering X f) (U : T.Opens) (hU : IsAffineOpen U) :
    Nonempty (LocalDescentData X f x U hU) := by
  let : IsAffine U.toScheme := hU
  obtain ⟨Es, hfinite, haffine, hstandard, hm⟩ := hf U hU
  let ms := Classical.choice hm
  let E₀' : PreZeroHypercover.{v} U.toScheme :=
    { I₀ := I
      X i := pullback (f i) U.ι
      f i := pullback.snd (f i) U.ι }
  let E : PreZeroHypercover.{max u v} U.toScheme :=
    { I₀ := ULift.{max u v} Es.I₀
      X j := Es.X j.down
      f j := Es.f j.down }
  let m : E.Hom E₀' :=
    { s₀ j := ms.s₀ j.down
      h₀ j := ms.h₀ j.down
      w₀ j := ms.w₀ j.down }
  have hstandard' : AlgebraicGeometry.IsStandardVCovering E.X E.f :=
    isStandardVCovering_uliftIndex hstandard
  let idx : E.I₀ → I := fun j ↦ m.s₀ j
  let orig : ∀ j, E.X j ⟶ X (idx j) := fun j => m.h₀ j ≫ pullback.fst (f (idx j)) U.ι
  have horig (j : E.I₀) : orig j ≫ f (idx j) = E.f j ≫ U.ι := by
    have hw : m.h₀ j ≫ pullback.snd (f (idx j)) U.ι = E.f j := m.w₀ j
    calc
      m.h₀ j ≫ pullback.fst (f (idx j)) U.ι ≫ f (idx j) =
          m.h₀ j ≫ pullback.snd (f (idx j)) U.ι ≫ U.ι := by
            simpa only [Category.assoc] using
              congrArg (fun k => m.h₀ j ≫ k)
                (pullback.condition (f := f (idx j)) (g := U.ι))
      _ = E.f j ≫ U.ι := by
        simpa only [Category.assoc] using congrArg (fun k => k ≫ U.ι) hw
  let y : (j : E.I₀) → F.obj (op (E.X j)) := fun j ↦ F.map (orig j).op (x (idx j))
  have hy : Presieve.Arrows.Compatible F E.f y := by
    intro i j Z gi gj h
    have hab : (gi ≫ orig i) ≫ f (idx i) = (gj ≫ orig j) ≫ f (idx j) := by
      simp only [Category.assoc, horig, reassoc_of% h]
    simpa only [y, ← types_comp_apply, ← F.map_comp, ← op_comp] using
      hx (idx i) (idx j) Z (gi ≫ orig i) (gj ≫ orig j) hab
  obtain ⟨s, hs, _⟩ := (Presieve.isSheafFor_arrows_iff F E.f).mp
    (hstd U E.I₀ E.X E.f hstandard') y hy
  exact ⟨⟨E, inferInstance, fun j => haffine j.down, hstandard', idx, orig, horig, s, hs⟩⟩

/-- Two sections of a presheaf which agree on the members of a family for which the presheaf
satisfies the sheaf condition are equal. -/
lemma eq_of_sheafFor_arrows {C : Type*} [Category C] {T : C} {I : Type*} {X : I → C}
    {F : Cᵒᵖ ⥤ Type w} (f : ∀ i, X i ⟶ T)
    (hs : (Presieve.ofArrows X f).IsSheafFor F)
    {a b : F.obj (op T)} (hab : ∀ i, F.map (f i).op a = F.map (f i).op b) : a = b := by
  let y : ∀ i, F.obj (op (X i)) := fun i => F.map (f i).op a
  have hy : Presieve.Arrows.Compatible F f y := by
    intro i j Z g h e
    simpa only [y, ← types_comp_apply, ← F.map_comp, ← op_comp] using
      congrArg (fun k => F.map k.op a) e
  obtain ⟨t, ht, hu⟩ := (Presieve.isSheafFor_arrows_iff F f).mp hs y hy
  exact (hu a fun _ => rfl).trans (hu b fun i => (hab i).symm).symm

/-- Two sections of a Zariski sheaf are equal if they agree after pulling back along every
morphism from an affine scheme. -/
private lemma eq_of_forall_affine {F : Scheme.{u}ᵒᵖ ⥤ Type w}
    (hZ : ∀ (T : Scheme.{u}) (𝒰 : T.OpenCover.{max u v}),
      (Presieve.ofArrows 𝒰.X 𝒰.f).IsSheafFor F)
    {Z : Scheme.{u}} {a b : F.obj (op Z)}
    (h : ∀ (V : Scheme.{u}) [IsAffine V] (v : V ⟶ Z), F.map v.op a = F.map v.op b) : a = b :=
  eq_of_sheafFor_arrows (affineOpenCover.{u, v} Z).f (hZ Z (affineOpenCover Z)) fun j =>
    have : IsAffine ((affineOpenCover.{u, v} Z).X j) := (affineOpenNbhd_spec Z j.down).1
    h _ _

private lemma map_ι_eq_localSection {T : Scheme.{u}} {I : Type v}
    {F : Scheme.{u}ᵒᵖ ⥤ Type w} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T}
    {x : ∀ i, F.obj (op (X i))}
    (hstd : ∀ (U : Scheme.{u}) [IsAffine U] (J : Type (max u v)) [Finite J]
      (Y : J → Scheme.{u}) [∀ j, IsAffine (Y j)] (g : ∀ j, Y j ⟶ U),
      AlgebraicGeometry.IsStandardVCovering Y g →
        (Presieve.ofArrows Y g).IsSheafFor F)
    {U : T.Opens} {hU : IsAffineOpen U} (D : LocalDescentData X f x U hU)
    {t : F.obj (op T)} (ht : ∀ i, F.map (f i).op t = x i) :
    F.map U.ι.op t = D.localSection := by
  let : IsAffine U.toScheme := hU
  let : Finite D.E.I₀ := D.finite
  let : ∀ j, IsAffine (D.E.X j) := D.affine
  refine eq_of_sheafFor_arrows D.E.f (hstd U.toScheme D.E.I₀ D.E.X D.E.f D.standard)
    fun j => ?_
  rw [D.glue j, ← ht (D.index j)]
  simpa only [← types_comp_apply, ← F.map_comp, ← op_comp] using
    congrArg (fun m => F.map m.op t) (D.toOriginal_over j).symm

private lemma localSection_matchesOnAffine
    {T : Scheme.{u}} {I : Type v} {F : Scheme.{u}ᵒᵖ ⥤ Type w}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ T) (x : ∀ i, F.obj (op (X i)))
    (hx : Presieve.Arrows.Compatible F f x)
    (hstd : ∀ (U : Scheme.{u}) [IsAffine U] (J : Type (max u v)) [Finite J]
      (Y : J → Scheme.{u}) [∀ j, IsAffine (Y j)] (g : ∀ j, Y j ⟶ U),
      AlgebraicGeometry.IsStandardVCovering Y g →
        (Presieve.ofArrows Y g).IsSheafFor F)
    {U : T.Opens} (hU : IsAffineOpen U) (D : LocalDescentData X f x U hU)
    {V : Scheme.{u}} [IsAffine V] (g : V ⟶ U.toScheme)
    (i : I) (q : V ⟶ X i) (hq : g ≫ U.ι = q ≫ f i) :
    F.map g.op D.localSection = F.map q.op (x i) := by
  let : IsAffine U.toScheme := hU
  let : Finite D.E.I₀ := D.finite
  let : ∀ j, IsAffine (D.E.X j) := D.affine
  let Z : D.E.I₀ → Scheme.{u} := fun j => pullback (D.E.f j) g
  let k : ∀ j, Z j ⟶ V := fun j => pullback.snd (D.E.f j) g
  let : ∀ j, IsAffine (Z j) := fun j => by
    dsimp [Z]
    infer_instance
  have hs := hstd V D.E.I₀ Z k
    (AlgebraicGeometry.isStandardVCovering_pullback D.E.X D.E.f g D.standard)
  have local_j (j : D.E.I₀) :
      F.map (k j ≫ g).op D.localSection =
        F.map (k j ≫ q).op (x i) := by
    let a : Z j ⟶ X (D.index j) :=
      pullback.fst (D.E.f j) g ≫ D.toOriginal j
    let b : Z j ⟶ X i := k j ≫ q
    have hab : a ≫ f (D.index j) = b ≫ f i := by
      dsimp [a, b, k, Z]
      calc
        (pullback.fst (D.E.f j) g ≫ D.toOriginal j) ≫ f (D.index j) =
            pullback.fst (D.E.f j) g ≫ (D.E.f j ≫ U.ι) := by
              rw [Category.assoc]
              exact congrArg (fun m => pullback.fst (D.E.f j) g ≫ m)
                (D.toOriginal_over j)
        _ = pullback.snd (D.E.f j) g ≫ (g ≫ U.ι) := by
          rw [← Category.assoc, pullback.condition, Category.assoc]
        _ = pullback.snd (D.E.f j) g ≫ (q ≫ f i) :=
          congrArg (fun m => pullback.snd (D.E.f j) g ≫ m) hq
    calc
      F.map (k j ≫ g).op D.localSection =
          F.map (pullback.fst (D.E.f j) g ≫ D.E.f j).op D.localSection :=
            congrArg (fun m => F.map m.op D.localSection)
              (pullback.condition (f := D.E.f j) (g := g)).symm
      _ = F.map (pullback.fst (D.E.f j) g).op
            (F.map (D.E.f j).op D.localSection) := by
              rw [← types_comp_apply, ← F.map_comp, ← op_comp]
      _ = F.map (pullback.fst (D.E.f j) g).op
            (F.map (D.toOriginal j).op (x (D.index j))) := by
              rw [D.glue j]
      _ = F.map a.op (x (D.index j)) := by
            dsimp [a]
            rw [← types_comp_apply, ← F.map_comp, ← op_comp]
      _ = F.map b.op (x i) := hx (D.index j) i (Z j) a b hab
      _ = F.map (k j ≫ q).op (x i) := rfl
  refine eq_of_sheafFor_arrows k hs fun j => ?_
  simpa only [← types_comp_apply, ← F.map_comp, ← op_comp] using local_j j

private lemma preservesDiscreteOfOpenCover
    {F : Scheme.{u}ᵒᵖ ⥤ Type w} (hZ : ∀ (T : Scheme.{u})
      (𝒰 : T.OpenCover.{max u v}), (Presieve.ofArrows 𝒰.X 𝒰.f).IsSheafFor F)
    {I : Type (max u v)} [Finite I] (X : I → Scheme.{u}) :
    PreservesLimit (Discrete.functor (fun i ↦ op (X i))) F := by
  have hEmpty : (Presieve.ofArrows (X := (⊥_ Scheme)) Empty.elim
      Empty.instIsEmpty.elim).IsSheafFor F := by
    let 𝒰 : Scheme.OpenCover.{max u v, u} (⊥_ Scheme) :=
      { I₀ := ULift.{max u v} Empty
        X := fun i => i.down.elim
        f := fun i => i.down.elim
        mem₀ := by
          rw [Scheme.presieve₀_mem_precoverage_iff]
          exact ⟨fun x => isEmptyElim x, fun i => i.down.elim⟩ }
    have h := hZ _ 𝒰
    have h₁ : Presieve.ofArrows 𝒰.X 𝒰.f = (⊥ : Presieve (⊥_ Scheme)) := by
      apply le_antisymm
      · rw [Presieve.ofArrows_le_iff]
        intro i
        exact isEmptyElim i
      · exact bot_le
    have h₂ : Presieve.ofArrows (X := (⊥_ Scheme)) Empty.elim
        Empty.instIsEmpty.elim = (⊥ : Presieve (⊥_ Scheme)) := by
      apply le_antisymm
      · rw [Presieve.ofArrows_le_iff]
        intro i
        exact i.elim
      · exact bot_le
    rw [h₁] at h
    rwa [h₂]
  let c : Cofan X := Cofan.mk (∐ X) (Sigma.ι X)
  have hc : IsColimit c := coproductIsCoproduct X
  have hd : Pairwise fun i j =>
      IsPullback (initial.to _) (initial.to _) (c.inj i) (c.inj j) := fun _ _ hij =>
    CoproductDisjoint.isPullback_of_isInitial hc initialIsInitial hij
  let : ∀ i, Mono (c.inj i) := fun i => by
    show Mono (Sigma.ι X i)
    infer_instance
  have hcover : (Presieve.ofArrows X c.inj).IsSheafFor F := by
    have h := hZ (∐ X) (AlgebraicGeometry.sigmaOpenCover X)
    have heq : Presieve.ofArrows (AlgebraicGeometry.sigmaOpenCover X).X
        (AlgebraicGeometry.sigmaOpenCover X).f = Presieve.ofArrows X (Sigma.ι X) := by
      apply le_antisymm <;> rw [Presieve.ofArrows_le_iff] <;> intro i
      all_goals
        have hXi : (AlgebraicGeometry.sigmaOpenCover X).X i = X i :=
          AlgebraicGeometry.sigmaOpenCover_X X i
        have hfi : (AlgebraicGeometry.sigmaOpenCover X).f i = Sigma.ι X i :=
          AlgebraicGeometry.sigmaOpenCover_f X i
        cases hXi
        cases hfi
        exact ⟨i⟩
    rwa [heq] at h
  exact Presieve.preservesProduct_of_isSheafFor F hEmpty initialIsInitial c hc hd hcover

/-- A constant family of arrows over a nonempty index type generates the presieve of the single
arrow it repeats, so replacing the index type by another nonempty one changes nothing. -/
lemma constOfArrows_eq {C : Type*} [Category C] {T X : C} (f : X ⟶ T)
    {I J : Type*} [Nonempty I] [Nonempty J] :
    Presieve.ofArrows (fun _ : I ↦ X) (fun _ ↦ f) =
      Presieve.ofArrows (fun _ : J ↦ X) (fun _ ↦ f) := by
  apply le_antisymm <;> rw [Presieve.ofArrows_le_iff] <;> intro i
  all_goals exact Presieve.ofArrows.mk (Classical.choice inferInstance)

/-- A standard V covering of an affine scheme is a V covering: over an affine open of the target
it is refined by its own base change, after the index type is shrunk to the universe of the
schemes. -/
lemma standardCovering_isVCovering {T : Scheme.{u}} [IsAffine T]
    {I : Type v} [Finite I] (X : I → Scheme.{u}) [∀ i, IsAffine (X i)]
    (f : ∀ i, X i ⟶ T) (hf : AlgebraicGeometry.IsStandardVCovering X f) :
    AlgebraicGeometry.IsVCovering X f := by
  intro U hU
  obtain ⟨J, ⟨e⟩⟩ := Small.equiv_small.{u} (α := I)
  let : Finite J := Finite.of_equiv I e
  let : IsAffine U.toScheme := hU
  let Xsmall : J → Scheme.{u} := fun j ↦ X (e.symm j)
  let fsmall : ∀ j, Xsmall j ⟶ T := fun j ↦ f (e.symm j)
  let Y : J → Scheme.{u} := fun j ↦ pullback (fsmall j) U.ι
  let g : ∀ j, Y j ⟶ U.toScheme := fun j ↦ pullback.snd (fsmall j) U.ι
  have hY : ∀ j, IsAffine (Y j) := fun j ↦ by
    dsimp [Y, fsmall, Xsmall]
    infer_instance
  let : ∀ j, IsAffine (Y j) := hY
  have hstd : AlgebraicGeometry.IsStandardVCovering Y g := by
    have hf' : AlgebraicGeometry.IsStandardVCovering
        Xsmall fsmall := by
      intro V _ _ _ a
      obtain ⟨W, hW₁, hW₂, hW₃, r, hr, i, k, hk⟩ := hf V a
      have hei : e.symm (e i) = i := e.symm_apply_apply i
      have hidx : X i = Xsmall (e i) := by simp [Xsmall, hei]
      have hcast : eqToHom hidx ≫ fsmall (e i) = f i := by
        have hn := eqToHom_naturality (fun j : I ↦ f j) hei.symm
        simpa [fsmall, Xsmall, hei] using hn.symm
      exact ⟨W, hW₁, hW₂, hW₃, r, hr, e i, k ≫ eqToHom hidx,
        hk.trans (by rw [Category.assoc, hcast])⟩
    exact AlgebraicGeometry.isStandardVCovering_pullback
      Xsmall fsmall U.ι hf'
  let E : PreZeroHypercover.{u} U.toScheme :=
    { I₀ := J, X := Y, f := g }
  exact ⟨E, inferInstance, hY, hstd, ⟨{ s₀ := fun j ↦ e.symm j, h₀ := fun j ↦ 𝟙 (Y j) }⟩⟩

private lemma isSheafFor_vCovering_affine
    {T : Scheme.{u}} [IsAffine T] {I : Type (max u v)}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hf : AlgebraicGeometry.IsVCovering X f)
    (F : Scheme.{u}ᵒᵖ ⥤ Type w)
    (hZ : ∀ (T : Scheme.{u}) (𝒰 : T.OpenCover.{max u v}),
      (Presieve.ofArrows 𝒰.X 𝒰.f).IsSheafFor F)
    (hstd : ∀ (T : Scheme.{u}) [IsAffine T] (J : Type (max u v)) [Finite J]
      (Y : J → Scheme.{u}) [∀ j, IsAffine (Y j)] (g : ∀ j, Y j ⟶ T),
      AlgebraicGeometry.IsStandardVCovering Y g →
        (Presieve.ofArrows Y g).IsSheafFor F) :
    (Presieve.ofArrows X f).IsSheafFor F := by
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  let U : T.Opens := ⊤
  have hU : IsAffineOpen U := by simpa [U] using isAffineOpen_top T
  let : IsAffine U.toScheme := hU
  obtain ⟨D⟩ := exists_localDescentData X f x hx hstd hf U hU
  let s : F.obj (op T) := F.map T.topIso.inv.op D.localSection
  have hmatch : ∀ i, F.map (f i).op s = x i := by
    intro i
    refine eq_of_forall_affine hZ fun V _ q => ?_
    let g := q ≫ f i ≫ T.topIso.inv
    have hg : g ≫ U.ι = q ≫ f i := by
      dsimp [g, U]
      simp [Category.assoc]
    have hloc := localSection_matchesOnAffine f x hx hstd hU D g i q hg
    dsimp [s, g]
    simpa only [← types_comp_apply, ← F.map_comp, ← op_comp,
      Category.assoc, Scheme.topIso_hom, Iso.inv_hom_id] using hloc
  refine ⟨s, hmatch, fun t ht => ?_⟩
  have heq' := congrArg (fun z => F.map T.topIso.inv.op z) (map_ι_eq_localSection hstd D ht)
  have hcomp : T.topIso.inv ≫ U.ι = 𝟙 T := by
    dsimp [U]
    rw [← Scheme.topIso_hom]
    exact T.topIso.inv_hom_id
  simpa [s, ← types_comp_apply, ← F.map_comp, ← op_comp, hcomp] using heq'

private lemma localSection_matches
    {T : Scheme.{u}} {I : Type v} {F : Scheme.{u}ᵒᵖ ⥤ Type w}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ T) (x : ∀ i, F.obj (op (X i)))
    (hx : Presieve.Arrows.Compatible F f x)
    (hZ : ∀ (T : Scheme.{u}) (𝒰 : T.OpenCover.{max u v}),
      (Presieve.ofArrows 𝒰.X 𝒰.f).IsSheafFor F)
    (hstd : ∀ (U : Scheme.{u}) [IsAffine U] (J : Type (max u v)) [Finite J]
      (Y : J → Scheme.{u}) [∀ j, IsAffine (Y j)] (g : ∀ j, Y j ⟶ U),
      AlgebraicGeometry.IsStandardVCovering Y g →
        (Presieve.ofArrows Y g).IsSheafFor F)
    {U : T.Opens} (hU : IsAffineOpen U) (D : LocalDescentData X f x U hU)
    {V : Scheme.{u}} (g : V ⟶ U.toScheme)
    (i : I) (q : V ⟶ X i) (hq : g ≫ U.ι = q ≫ f i) :
    F.map g.op D.localSection = F.map q.op (x i) := by
  refine eq_of_forall_affine hZ fun W _ v => ?_
  have hloc := localSection_matchesOnAffine f x hx hstd hU D (v ≫ g) i (v ≫ q)
    (by rw [Category.assoc, hq, Category.assoc])
  simpa only [← types_comp_apply, ← F.map_comp, ← op_comp] using hloc

private lemma localSections_compatible_affine
    {T : Scheme.{u}} {I : Type (max u v)}
    {F : Scheme.{u}ᵒᵖ ⥤ Type w}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ T)
    (x : ∀ i, F.obj (op (X i)))
    (hx : Presieve.Arrows.Compatible F f x)
    (hf : AlgebraicGeometry.IsVCovering X f)
    (hZ : ∀ (T : Scheme.{u}) (𝒰 : T.OpenCover.{max u v}),
      (Presieve.ofArrows 𝒰.X 𝒰.f).IsSheafFor F)
    (hstd : ∀ (U : Scheme.{u}) [IsAffine U] (J : Type (max u v)) [Finite J]
      (Y : J → Scheme.{u}) [∀ j, IsAffine (Y j)] (g : ∀ j, Y j ⟶ U),
      AlgebraicGeometry.IsStandardVCovering Y g →
        (Presieve.ofArrows Y g).IsSheafFor F)
    {U₁ U₂ : T.Opens} (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂)
    (D₁ : LocalDescentData X f x U₁ hU₁) (D₂ : LocalDescentData X f x U₂ hU₂)
    {V : Scheme.{u}} [IsAffine V] (g₁ : V ⟶ U₁.toScheme) (g₂ : V ⟶ U₂.toScheme)
    (hbase : g₁ ≫ U₁.ι = g₂ ≫ U₂.ι) :
    F.map g₁.op D₁.localSection = F.map g₂.op D₂.localSection := by
  let r : V ⟶ T := g₁ ≫ U₁.ι
  let Y : I → Scheme.{u} := fun i => pullback (f i) r
  let p : ∀ i, Y i ⟶ V := fun i => pullback.snd (f i) r
  let q : ∀ i, Y i ⟶ X i := fun i => pullback.fst (f i) r
  have hsheaf := isSheafFor_vCovering_affine Y p
    (AlgebraicGeometry.isVCovering_pullback X f r hf) F hZ hstd
  have hside : ∀ {U : T.Opens} (hU : IsAffineOpen U) (D : LocalDescentData X f x U hU)
      (g : V ⟶ U.toScheme), g ≫ U.ι = r → ∀ i,
      F.map (p i).op (F.map g.op D.localSection) = F.map (q i).op (x i) := by
    intro U hU D g hg i
    have heq : (p i ≫ g) ≫ U.ι = (q i) ≫ f i := by
      rw [Category.assoc, hg]
      exact pullback.condition (f := f i) (g := r) |>.symm
    have hloc := localSection_matches f x hx hZ hstd hU D (p i ≫ g) i (q i) heq
    simpa only [← types_comp_apply, ← F.map_comp, ← op_comp] using hloc
  exact eq_of_sheafFor_arrows p hsheaf fun i =>
    (hside hU₁ D₁ g₁ rfl i).trans (hside hU₂ D₂ g₂ hbase.symm i).symm

private lemma localSections_compatible
    {T : Scheme.{u}} {I : Type (max u v)}
    {F : Scheme.{u}ᵒᵖ ⥤ Type w}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ T)
    (x : ∀ i, F.obj (op (X i)))
    (hx : Presieve.Arrows.Compatible F f x)
    (hf : AlgebraicGeometry.IsVCovering X f)
    (hZ : ∀ (T : Scheme.{u}) (𝒰 : T.OpenCover.{max u v}),
      (Presieve.ofArrows 𝒰.X 𝒰.f).IsSheafFor F)
    (hstd : ∀ (U : Scheme.{u}) [IsAffine U] (J : Type (max u v)) [Finite J]
      (Y : J → Scheme.{u}) [∀ j, IsAffine (Y j)] (g : ∀ j, Y j ⟶ U),
      AlgebraicGeometry.IsStandardVCovering Y g →
        (Presieve.ofArrows Y g).IsSheafFor F)
    {U₁ U₂ : T.Opens} (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂)
    (D₁ : LocalDescentData X f x U₁ hU₁) (D₂ : LocalDescentData X f x U₂ hU₂)
    {Z : Scheme.{u}} (g₁ : Z ⟶ U₁.toScheme) (g₂ : Z ⟶ U₂.toScheme)
    (hbase : g₁ ≫ U₁.ι = g₂ ≫ U₂.ι) :
    F.map g₁.op D₁.localSection = F.map g₂.op D₂.localSection := by
  refine eq_of_forall_affine hZ fun W _ v => ?_
  have hlocal := localSections_compatible_affine f x hx hf hZ hstd hU₁ hU₂ D₁ D₂
    (v ≫ g₁) (v ≫ g₂) (by rw [Category.assoc, hbase, Category.assoc])
  simpa only [← types_comp_apply, ← F.map_comp, ← op_comp] using hlocal

/-- **Stacks Project, Tag 0ETM.** The V sheaf condition is equivalent to the
Zariski sheaf condition together with the sheaf condition for all standard V
coverings. -/
@[stacks 0ETM "Zariski and standard V criterion"]
theorem isVSheaf_iff_zariski_and_standard
    (F : Scheme.{u}ᵒᵖ ⥤ Type w) :
    AlgebraicGeometry.IsVSheaf.{u, max u v, w} F ↔
      (∀ (T : Scheme.{u}) (𝒰 : T.OpenCover.{max u v}),
        (Presieve.ofArrows 𝒰.X 𝒰.f).IsSheafFor F) ∧
      (∀ (T : Scheme.{u}) [IsAffine T] (I : Type (max u v)) [Finite I]
        (X : I → Scheme.{u}) [∀ i, IsAffine (X i)] (f : ∀ i, X i ⟶ T),
        AlgebraicGeometry.IsStandardVCovering X f →
          (Presieve.ofArrows X f).IsSheafFor F) := by
  refine ⟨fun hV => ⟨fun T 𝒰 => hV T 𝒰.I₀ 𝒰.X 𝒰.f
      (isVCovering_of_isPHCovering 𝒰.X 𝒰.f (IsPHCovering.of_openCover 𝒰)),
    fun T _ I _ X _ f hf => hV T I X f (standardCovering_isVCovering (X := X) (f := f) hf)⟩, ?_⟩
  · rintro ⟨hZ, hstd⟩ T I X f hf
    rw [Presieve.isSheafFor_arrows_iff]
    intro x hx
    let 𝒰 := affineOpenCover T
    let U : 𝒰.I₀ → T.Opens := fun a => affineOpenNbhd T a.down
    have hU : ∀ a, IsAffineOpen (U a) := fun a =>
      (affineOpenNbhd_spec T a.down).1
    let D : ∀ a, LocalDescentData X f x (U a) (hU a) := fun a =>
      Classical.choice (exists_localDescentData X f x hx hstd hf (U a) (hU a))
    let y : ∀ a, F.obj (op ((U a).toScheme)) := fun a => (D a).localSection
    have hy : Presieve.Arrows.Compatible F 𝒰.f y := fun a b _ g₁ g₂ hab =>
      localSections_compatible f x hx hf hZ hstd (hU a) (hU b) (D a) (D b) g₁ g₂ hab
    obtain ⟨s, hs, _⟩ :=
      (Presieve.isSheafFor_arrows_iff F 𝒰.f).mp (hZ T 𝒰) y hy
    have hmatch : ∀ i, F.map (f i).op s = x i := by
      intro i
      let 𝒱 := 𝒰.pullback₁ (f i)
      have hI : 𝒱.I₀ = 𝒰.I₀ := by
        dsimp [𝒱]
        simp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
          PreZeroHypercover.pullback₁_I₀]
      cases hI
      refine eq_of_sheafFor_arrows 𝒱.f (hZ (X i) 𝒱) fun a => ?_
      let g := pullback.snd (f i) (𝒰.f a)
      let q := pullback.fst (f i) (𝒰.f a)
      have hloc := localSection_matches f x hx hZ hstd (hU a) (D a) g i q
        (pullback.condition (f := f i) (g := 𝒰.f a)).symm
      have hfac : 𝒱.f a ≫ f i = g ≫ (U a).ι := by
        show pullback.fst (f i) (𝒰.f a) ≫ f i = pullback.snd (f i) (𝒰.f a) ≫ 𝒰.f a
        exact pullback.condition
      have hstep : F.map (𝒱.f a).op (F.map (f i).op s) = F.map g.op (F.map (U a).ι.op s) := by
        simp only [← types_comp_apply, ← F.map_comp, ← op_comp, hfac]
        exact congrArg (fun k => k s) (F.map_comp (U a).ι.op g.op)
      exact hstep.trans ((congrArg (F.map g.op) (hs a)).trans hloc)
    refine ⟨s, hmatch, fun t ht => ?_⟩
    have hchart : ∀ a, F.map (𝒰.f a).op t = F.map (𝒰.f a).op s := fun a =>
      (map_ι_eq_localSection hstd (D a) ht).trans (hs a).symm
    exact eq_of_sheafFor_arrows 𝒰.f (hZ T 𝒰) hchart

/-- **Stacks Project, Tag 0ETM, moreover.** Under the Zariski sheaf condition,
the sheaf condition for standard V coverings can be tested on one-arrow
standard V coverings. -/
@[stacks 0ETM "single-arrow standard V criterion"]
theorem isStandardVSheaf_iff_singleton
    (F : Scheme.{u}ᵒᵖ ⥤ Type w)
    (hZ : ∀ (T : Scheme.{u}) (𝒰 : T.OpenCover.{max u v}),
      (Presieve.ofArrows 𝒰.X 𝒰.f).IsSheafFor F) :
    (∀ (T : Scheme.{u}) [IsAffine T] (I : Type (max u v)) [Finite I]
      (X : I → Scheme.{u}) [∀ i, IsAffine (X i)] (f : ∀ i, X i ⟶ T),
      AlgebraicGeometry.IsStandardVCovering X f →
        (Presieve.ofArrows X f).IsSheafFor F) ↔
    (∀ (T X : Scheme.{u}) [IsAffine T] [IsAffine X] (f : X ⟶ T),
      AlgebraicGeometry.IsStandardVCovering (fun _ : Unit ↦ X) (fun _ ↦ f) →
        (Presieve.ofArrows (fun _ : Unit ↦ X) (fun _ ↦ f)).IsSheafFor F) := by
  constructor
  · intro h T X hT hX f hf
    let J := ULift.{max u v} Unit
    let Y : J → Scheme.{u} := fun _ ↦ X
    have hs := h T J Y (fun _ ↦ f) (isStandardVCovering_uliftIndex hf)
    rwa [constOfArrows_eq f (I := J) (J := Unit)] at hs
  · intro h T hT I hI X hX f hf
    have : PreservesLimit (Discrete.functor (fun i ↦ op (X i))) F :=
      preservesDiscreteOfOpenCover hZ X
    have : PreservesLimit
        (Discrete.functor (fun ij : I × I ↦
          op (Limits.pullback (f ij.1) (f ij.2)))) F :=
      preservesDiscreteOfOpenCover hZ
        (fun ij : I × I ↦ Limits.pullback (f ij.1) (f ij.2))
    have hsingle : (Presieve.ofArrows (fun _ : Unit ↦ ∐ X)
        (fun _ ↦ Limits.Sigma.desc f)).IsSheafFor F :=
      h T (∐ X) (Limits.Sigma.desc f) (((isStandardVCovering_tfae X f).out 1 3).mp hf)
    have heq : Presieve.ofArrows (fun _ : Unit ↦ ∐ X)
        (fun _ ↦ Limits.Sigma.desc f) =
        Presieve.singleton (Limits.Sigma.desc f) := by
      apply le_antisymm
      · rw [Presieve.ofArrows_le_iff]
        intro i
        exact Presieve.singleton_self _
      · rw [Presieve.singleton_le_iff]
        exact ⟨()⟩
    rw [heq] at hsingle
    exact (Presieve.isSheafFor_sigmaDesc_iff f (coproductIsCoproduct X)
      (FinitaryExtensive.isVanKampen_finiteCoproducts (coproductIsCoproduct X)).isUniversal F).mp
      hsingle

end AlgebraicGeometry
