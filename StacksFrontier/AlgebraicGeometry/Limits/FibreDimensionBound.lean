module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Order.SuccPred.ENat
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Openness

/-!
# Fibre dimension in an inverse limit

Consider a morphism between cofiltered inverse systems of schemes.  Suppose that the base
schemes are quasi-compact and quasi-separated, their transition morphisms are affine, the
component morphisms are of finite type, and every source transition is a closed immersion into
the corresponding base change.  If the fibres of the induced morphism between the limits have
dimension at most `d`, then the same bound holds at some finite stage.

## Main definitions

No new definitions are introduced.

## Main results

* `exists_forall_topologicalKrullDim_fiber_le_of_isLimit_of_essentiallySmall` gives, for an
  index category that is essentially small relative to the universe of the schemes, a stage at
  which all fibres have the dimension bound satisfied by the limit.
* `not_exists_forall_topologicalKrullDim_fiber_le_of_isLimit` shows that the smallness
  assumption on the index category cannot be dropped.

## Implementation notes

A directed inverse system is represented by a functor from a cofiltered category.  The
morphism of systems is a natural transformation.  Tag 05M5 indexes the system by a directed
*set*, so the index category is required to be essentially small relative to the universe of
the schemes; `not_exists_forall_topologicalKrullDim_fiber_le_of_isLimit` shows that this bound
cannot be dropped.  The proof is first given for an index category that is literally small and
then transported along the equivalence with the small model.
For a transition `g : i ⟶ j`, the map
from `X.obj i` to the base change of `X.obj j` along `S.map g` is the canonical pullback lift.
The morphism between the chosen limit objects is the lift of the source limit cone, postcomposed
with the natural transformation, to the target limit cone.

## References

* [The Stacks Project, Tag 05M5](https://stacks.math.columbia.edu/tag/05M5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

open Set Topology
open Scheme.IdealSheafData

private lemma exists_pointwise_dimension_gt_of_topologicalKrullDim_gt
    {Y : Type*} [TopologicalSpace Y] {d : ℕ}
    (h : (d : WithBot ℕ∞) < topologicalKrullDim Y) :
    ∃ y : Y, (d : WithBot ℕ∞) < topologicalKrullDimAt Y y := by
  classical
  have hlen : (d + 1 : WithBot ℕ∞) ≤ topologicalKrullDim Y := by
    rw [ENat.WithBot.add_one_le_iff]
    exact h
  obtain ⟨p, hp⟩ := (Order.le_krullDim_iff (α := TopologicalSpace.IrreducibleCloseds Y)
    (n := d + 1)).mp (by simpa [topologicalKrullDim] using hlen)
  have hx0 : (p.head : Set Y).Nonempty := p.head.isIrreducible.nonempty
  obtain ⟨y, hy⟩ := hx0
  refine ⟨y, ?_⟩
  apply (ENat.WithBot.add_one_le_iff).mp
  unfold topologicalKrullDimAt
  apply le_iInf
  intro U
  let eU : U.1 → Y := Subtype.val
  have heU : IsOpenEmbedding eU := U.2.2.isOpenEmbedding_subtypeVal
  let q : LTSeries (TopologicalSpace.IrreducibleCloseds U.1) :=
    LTSeries.mk p.length
      (fun k => ⟨eU ⁻¹' (p k : Set Y),
        (p k).isIrreducible.preimage heU
          ⟨y, (p.strictMono.monotone (Fin.zero_le k)) hy, ⟨⟨y, U.2.1⟩, rfl⟩⟩,
        (p k).isClosed.preimage heU.continuous⟩)
      (by
        intro a b hab
        apply lt_of_le_of_ne (Set.preimage_mono (p.strictMono hab).le)
        intro heq
        have hba : eU ⁻¹' (p b : Set Y) ⊆ eU ⁻¹' (p a : Set Y) := by
          rw [← heq]
        have hnot : ¬ (p b : Set Y) ⊆ (p a : Set Y) := by
          intro hsub
          exact (not_le_of_gt (p.strictMono hab)) hsub
        obtain ⟨y', hyb, hya⟩ := Set.not_subset.mp hnot
        have hUb : ((p b : Set Y) ∩ U.1).Nonempty :=
          ⟨y, (p.strictMono.monotone (Fin.zero_le b)) hy, U.2.1⟩
        have hDiff : ((p b : Set Y) ∩ (p a : Set Y)ᶜ).Nonempty :=
          ⟨y', hyb, hya⟩
        obtain ⟨z, hzb, hzUV⟩ := (p b).isIrreducible.isPreirreducible
          U.1 (p a : Set Y)ᶜ U.2.2 (isOpen_compl_iff.mpr (p a).isClosed) hUb hDiff
        have hza : z ∈ (p a : Set Y) := by
          have hzmem : (⟨z, hzUV.1⟩ : U.1) ∈ eU ⁻¹' (p a : Set Y) :=
            @hba (⟨z, hzUV.1⟩ : U.1) (by simpa using hzb)
          simpa using hzmem
        exact hzUV.2 hza)
  have hq : (p.length : WithBot ℕ∞) ≤ topologicalKrullDim U.1 := by
    apply le_iSup_of_le q
    rfl
  simpa [hp] using hq

private lemma topologicalKrullDimAt_le_of_isClosedEmbedding
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {e : A → B} (he : IsClosedEmbedding e) (a : A) :
    topologicalKrullDimAt A a ≤ topologicalKrullDimAt B (e a) := by
  unfold topologicalKrullDimAt
  apply le_iInf
  intro V
  let W : {U : Set A // a ∈ U ∧ IsOpen U} :=
    ⟨e ⁻¹' V.1, by simpa using V.2.1, V.2.2.preimage he.continuous⟩
  refine (iInf_le _ W).trans ?_
  exact (Set.restrictPreimage_isClosedEmbedding V.1 he).isInducing.topologicalKrullDim_le

private lemma fiberDimensionAt_le_of_closedImmersion_over
    {A B T : Scheme} (e : A ⟶ B) (u : A ⟶ T) (v : B ⟶ T)
    [IsClosedImmersion e] (he : e ≫ v = u) (a : A) :
    topologicalKrullDimAt (u.fiber (u a)) (u.asFiber a) ≤
      topologicalKrullDimAt (v.fiber (v (e a))) (v.asFiber (e a)) := by
  classical
  let Z : Set B := v ⁻¹' {v (e a)}
  have hcomm (b : A) : u b = v (e b) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun q : A ⟶ T => q b) he.symm
  have hset : u ⁻¹' {u a} = e ⁻¹' Z := by
    ext b
    show (u b = u a) ↔ (v (e b) = v (e a))
    rw [hcomm b, hcomm a]
  let E : (u ⁻¹' {u a}) → Z :=
    fun x => (Z.restrictPreimage e) ((Homeomorph.setCongr hset) x)
  have hE : IsClosedEmbedding E :=
    (Set.restrictPreimage_isClosedEmbedding Z e.isClosedEmbedding).comp
      (Homeomorph.setCongr hset).isClosedEmbedding
  have hEpt : E ⟨a, rfl⟩ = v.fiberHomeo (v (e a)) (v.asFiber (e a)) := by
    have hx : (Homeomorph.setCongr hset) ⟨a, rfl⟩ = ⟨a, rfl⟩ := by
      apply Subtype.ext
      rfl
    apply Subtype.ext
    show e (((Homeomorph.setCongr hset) ⟨a, rfl⟩).val) = _
    rw [hx]
    simp [Z, Scheme.Hom.fiberHomeo_apply, Scheme.Hom.fiberι_asFiber]
  have hsourcept : (u.fiberHomeo (u a)) (u.asFiber a) = ⟨a, rfl⟩ := by
    apply Subtype.ext
    simp [Scheme.Hom.asFiber]
  have htargetpt : (v.fiberHomeo (v (e a))) (v.asFiber (e a)) = ⟨e a, rfl⟩ := by
    apply Subtype.ext
    simp [Scheme.Hom.asFiber]
  have hs : topologicalKrullDimAt (u.fiber (u a)) (u.asFiber a) =
      topologicalKrullDimAt (u ⁻¹' {u a}) ⟨a, rfl⟩ := by
    rw [← hsourcept]
    exact topologicalKrullDimAt_eq_of_homeomorph (u.fiberHomeo (u a)) (u.asFiber a)
  have ht : topologicalKrullDimAt (v.fiber (v (e a))) (v.asFiber (e a)) =
      topologicalKrullDimAt (v ⁻¹' {v (e a)})
        (v.fiberHomeo (v (e a)) (v.asFiber (e a))) :=
    topologicalKrullDimAt_eq_of_homeomorph
      (v.fiberHomeo (v (e a))) (v.asFiber (e a))
  rw [hs, ht]
  rw [← hEpt]
  exact topologicalKrullDimAt_le_of_isClosedEmbedding hE ⟨a, rfl⟩

private lemma exists_max_idealSheafData_of_isNoetherian
    {Y : Scheme.{u}} [IsNoetherian Y] (A : Set Y.IdealSheafData) (hA : A.Nonempty)
    (hdir : ∀ I ∈ A, ∀ J ∈ A, ∃ K ∈ A, I ≤ K ∧ J ≤ K) :
    ∃ I ∈ A, ∀ J ∈ A, J ≤ I := by
  classical
  let 𝒰 := Y.affineCover.finiteSubcover
  let V : 𝒰.I₀ → Y.affineOpens := fun i =>
    ⟨(𝒰.f i).opensRange, isAffineOpen_opensRange _⟩
  have hV : ⨆ i, (V i).1 = ⊤ := by
    simpa [V] using Scheme.OpenCover.iSup_opensRange 𝒰
  let R : 𝒰.I₀ → Type u := fun i =>
    ↑((PresheafedSpace.presheaf (SheafedSpace.toPresheafedSpace
      (LocallyRingedSpace.toSheafedSpace (Scheme.toLocallyRingedSpace Y)))).obj
        (Opposite.op (V i).1))
  let e : Y.IdealSheafData ↪o (∀ i, Ideal (R i)) := {
    toFun := fun I i => I.ideal (V i)
    inj' := by
      intro I J h
      exact Scheme.IdealSheafData.ext_of_iSup_eq_top V hV (fun i => congrFun h i)
    map_rel_iff' := by
      intro I J
      constructor
      · intro h
        exact Scheme.IdealSheafData.le_of_iSup_eq_top V hV h
      · intro h i
        exact h (V i)
  }
  have hR (i : 𝒰.I₀) : IsNoetherianRing (R i) := by
    let : IsLocallyNoetherian Y := inferInstance
    exact IsLocallyNoetherian.component_noetherian (V i)
  let : ∀ i, IsNoetherianRing (R i) := hR
  have : Finite 𝒰.I₀ := inferInstance
  let : Fintype 𝒰.I₀ := Fintype.ofFinite 𝒰.I₀
  let : IsNoetherianRing (∀ i, R i) := inferInstance
  let : WellFoundedGT (Ideal (∀ i, R i)) := inferInstance
  have hPi : WellFoundedGT (∀ i, Ideal (R i)) :=
    (Ideal.piOrderIso (R := R)).symm.toOrderEmbedding.wellFoundedGT
  let : WellFoundedGT (∀ i, Ideal (R i)) := hPi
  let : WellFoundedGT Y.IdealSheafData := OrderEmbedding.wellFoundedGT e
  let toRange : A → Y.IdealSheafData := fun I => I.1
  have hrange : (Set.range toRange).Nonempty := by
    rcases hA with ⟨I, hI⟩
    exact ⟨I, ⟨⟨I, hI⟩, rfl⟩⟩
  obtain ⟨I, hIr, hmax⟩ := wellFounded_gt.has_min (Set.range toRange) hrange
  obtain ⟨I', hI'A⟩ := hIr
  subst I
  refine ⟨I'.1, I'.2, ?_⟩
  intro J hJA
  obtain ⟨K, hKA, hIK, hJK⟩ := hdir I'.1 I'.2 J hJA
  by_contra hnot
  have hnotKI : ¬ K ≤ I'.1 := fun h => hnot (hJK.trans h)
  have hne : I'.1 ≠ K := fun heq => hnotKI (heq ▸ le_rfl)
  have hlt : I'.1 < K := lt_of_le_of_ne hIK hne
  have hKr : toRange ⟨K, hKA⟩ ∈ Set.range toRange := ⟨⟨K, hKA⟩, rfl⟩
  exact hmax _ hKr hlt

private lemma isIso_projection_of_noetherian_closed_diagram
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsClosedImmersion (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i : I) [IsNoetherian (D.obj i)] :
    ∃ j : I, IsIso (c.π.app j) := by
  classical
  let A : Set (D.obj i).IdealSheafData :=
    {K | ∃ (j : I) (f : j ⟶ i), K = (D.map f).ker}
  have hA : A.Nonempty := by
    refine ⟨(D.map (𝟙 i)).ker, ?_⟩
    exact ⟨i, 𝟙 i, rfl⟩
  have hdir : ∀ K ∈ A, ∀ L ∈ A, ∃ M ∈ A, K ≤ M ∧ L ≤ M := by
    intro K hK L hL
    obtain ⟨j, f, rfl⟩ := hK
    obtain ⟨k, g, rfl⟩ := hL
    obtain ⟨l, p, q, hpq⟩ := IsCofiltered.cospan f g
    refine ⟨(D.map (p ≫ f)).ker, ⟨l, p ≫ f, rfl⟩, ?_, ?_⟩
    · rw [D.map_comp]
      exact (D.map p).le_ker_comp (D.map f)
    · rw [hpq, D.map_comp]
      exact (D.map q).le_ker_comp (D.map g)
  obtain ⟨K, hK, hmax⟩ := exists_max_idealSheafData_of_isNoetherian A hA hdir
  obtain ⟨j, f, hKf⟩ := hK
  have hconst : D.IsEventuallyConstantTo j := by
    intro k g
    have hle : (D.map f).ker ≤ (D.map (g ≫ f)).ker := by
      rw [D.map_comp]
      exact (D.map g).le_ker_comp (D.map f)
    have hge : (D.map (g ≫ f)).ker ≤ (D.map f).ker := by
      rw [← hKf]
      exact hmax _ ⟨k, g ≫ f, rfl⟩
    exact IsClosedImmersion.isIso_of_ker_eq
      (D.map (g ≫ f)) (D.map f) (D.map g)
      (D.map_comp g f).symm (le_antisymm hge hle)
  exact ⟨j, hconst.isIso_π_of_isLimit hc⟩

/-- If the target of a morphism is a single point, each fibre is homeomorphic to the source. -/
private lemma exists_homeomorph_fiber_of_subsingleton {A B : Scheme.{u}} (h : A ⟶ B)
    [Subsingleton B] (b : B) : ∃ e : h.fiber b ≃ₜ A, ∀ x, e x = h.fiberι b x := by
  have heq : h ⁻¹' {b} = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  exact ⟨(h.fiberHomeo b).trans ((Homeomorph.setCongr heq).trans (Homeomorph.Set.univ A)),
    fun x => rfl⟩

private lemma topologicalKrullDimAt_eq_fiber_of_subsingleton
    {A B : Scheme.{u}} (h : A ⟶ B) [Subsingleton B] (a : A) :
    topologicalKrullDimAt A a =
      topologicalKrullDimAt (h.fiber (h a)) (h.asFiber a) := by
  obtain ⟨e, he⟩ := exists_homeomorph_fiber_of_subsingleton h (h a)
  have hea : e (h.asFiber a) = a := (he _).trans (h.fiberι_asFiber a)
  exact (congrArg (topologicalKrullDimAt A) hea).symm.trans
    (topologicalKrullDimAt_eq_of_homeomorph e (h.asFiber a)).symm

private noncomputable def pullbackDiagramAlongLimitMap
    {I : Type u} [Category.{u} I] {F S : I ⥤ Scheme.{u}} (g : F ⟶ S)
    (cS : Cone S) (T : Scheme.{u}) (t : T ⟶ cS.pt)
    [∀ i, HasPullback (g.app i) (t ≫ cS.π.app i)]
    {i j : I} (h : i ⟶ j) :
    pullback (g.app i) (t ≫ cS.π.app i) ⟶ pullback (g.app j) (t ≫ cS.π.app j) :=
  pullback.lift
    (pullback.fst (g.app i) (t ≫ cS.π.app i) ≫ F.map h)
    (pullback.snd (g.app i) (t ≫ cS.π.app i)) (by
      calc
        _ = pullback.fst (g.app i) (t ≫ cS.π.app i) ≫
            (F.map h ≫ g.app j) := by simp [Category.assoc]
        _ = pullback.fst (g.app i) (t ≫ cS.π.app i) ≫
            (g.app i ≫ S.map h) := by rw [g.naturality h]
        _ = (pullback.fst (g.app i) (t ≫ cS.π.app i) ≫ g.app i) ≫ S.map h := by
          simp [Category.assoc]
        _ = (pullback.snd (g.app i) (t ≫ cS.π.app i) ≫
            (t ≫ cS.π.app i)) ≫ S.map h := by rw [pullback.condition]
        _ = pullback.snd (g.app i) (t ≫ cS.π.app i) ≫
            ((t ≫ cS.π.app i) ≫ S.map h) := by simp [Category.assoc]
        _ = pullback.snd (g.app i) (t ≫ cS.π.app i) ≫
            (t ≫ cS.π.app j) := by simp [Category.assoc, cS.w h])

private lemma pullbackDiagramAlongLimitMap_fst
    {I : Type u} [Category.{u} I] {F S : I ⥤ Scheme.{u}} (g : F ⟶ S)
    (cS : Cone S) (T : Scheme.{u}) (t : T ⟶ cS.pt)
    [∀ i, HasPullback (g.app i) (t ≫ cS.π.app i)]
    {i j : I} (h : i ⟶ j) :
    pullbackDiagramAlongLimitMap g cS T t h ≫
        pullback.fst (g.app j) (t ≫ cS.π.app j) =
      pullback.fst (g.app i) (t ≫ cS.π.app i) ≫ F.map h :=
  pullback.lift_fst _ _ _

private lemma pullbackDiagramAlongLimitMap_snd
    {I : Type u} [Category.{u} I] {F S : I ⥤ Scheme.{u}} (g : F ⟶ S)
    (cS : Cone S) (T : Scheme.{u}) (t : T ⟶ cS.pt)
    [∀ i, HasPullback (g.app i) (t ≫ cS.π.app i)]
    {i j : I} (h : i ⟶ j) :
    pullbackDiagramAlongLimitMap g cS T t h ≫
        pullback.snd (g.app j) (t ≫ cS.π.app j) =
      pullback.snd (g.app i) (t ≫ cS.π.app i) :=
  pullback.lift_snd _ _ _

private noncomputable def pullbackDiagramAlongLimit
    {I : Type u} [Category.{u} I] {F S : I ⥤ Scheme.{u}} (g : F ⟶ S)
    (cS : Cone S) (T : Scheme.{u}) (t : T ⟶ cS.pt)
    [∀ i, HasPullback (g.app i) (t ≫ cS.π.app i)] : I ⥤ Scheme.{u} where
  obj i := pullback (g.app i) (t ≫ cS.π.app i)
  map h := pullbackDiagramAlongLimitMap g cS T t h
  map_id i := by
    apply pullback.hom_ext
    · simp [pullbackDiagramAlongLimitMap]
    · simp [pullbackDiagramAlongLimitMap]
  map_comp h k := by
    apply pullback.hom_ext
    · calc
        pullbackDiagramAlongLimitMap g cS T t (h ≫ k) ≫
            pullback.fst (g.app _) (t ≫ cS.π.app _) =
          pullback.fst (g.app _) (t ≫ cS.π.app _) ≫ F.map (h ≫ k) :=
            pullbackDiagramAlongLimitMap_fst g cS T t (h ≫ k)
        _ = pullback.fst (g.app _) (t ≫ cS.π.app _) ≫ F.map h ≫ F.map k := by
              rw [F.map_comp]
        _ = (pullbackDiagramAlongLimitMap g cS T t h ≫
              pullback.fst (g.app _) (t ≫ cS.π.app _)) ≫ F.map k := by
              simpa [Category.assoc] using congrArg (fun q => q ≫ F.map k)
                (pullbackDiagramAlongLimitMap_fst g cS T t h).symm
        _ = pullbackDiagramAlongLimitMap g cS T t h ≫
              (pullback.fst (g.app _) (t ≫ cS.π.app _) ≫ F.map k) := by
              simp [Category.assoc]
        _ = pullbackDiagramAlongLimitMap g cS T t h ≫
              (pullbackDiagramAlongLimitMap g cS T t k ≫
                pullback.fst (g.app _) (t ≫ cS.π.app _)) := by
              simpa [Category.assoc] using congrArg
                (fun q => pullbackDiagramAlongLimitMap g cS T t h ≫ q)
                (pullbackDiagramAlongLimitMap_fst g cS T t k).symm
        _ = _ := by simp [Category.assoc]
    · calc
        pullbackDiagramAlongLimitMap g cS T t (h ≫ k) ≫
            pullback.snd (g.app _) (t ≫ cS.π.app _) =
          pullback.snd (g.app _) (t ≫ cS.π.app _) :=
            pullbackDiagramAlongLimitMap_snd g cS T t (h ≫ k)
        _ = pullbackDiagramAlongLimitMap g cS T t h ≫
              pullback.snd (g.app _) (t ≫ cS.π.app _) :=
              (pullbackDiagramAlongLimitMap_snd g cS T t h).symm
        _ = pullbackDiagramAlongLimitMap g cS T t h ≫
              (pullbackDiagramAlongLimitMap g cS T t k ≫
                pullback.snd (g.app _) (t ≫ cS.π.app _)) :=
              congrArg
                (fun q => pullbackDiagramAlongLimitMap g cS T t h ≫ q)
                (pullbackDiagramAlongLimitMap_snd g cS T t k).symm
        _ = _ := by simp [Category.assoc]

private lemma pullbackDiagramAlongLimit_fst
    {I : Type u} [Category.{u} I] {F S : I ⥤ Scheme.{u}} (g : F ⟶ S)
    (cS : Cone S) (T : Scheme.{u}) (t : T ⟶ cS.pt)
    [∀ i, HasPullback (g.app i) (t ≫ cS.π.app i)]
    {i j : I} (h : i ⟶ j) :
    (pullbackDiagramAlongLimit g cS T t).map h ≫
        pullback.fst (g.app j) (t ≫ cS.π.app j) =
      pullback.fst (g.app i) (t ≫ cS.π.app i) ≫ F.map h :=
  pullbackDiagramAlongLimitMap_fst g cS T t h

private lemma pullbackDiagramAlongLimit_snd
    {I : Type u} [Category.{u} I] {F S : I ⥤ Scheme.{u}} (g : F ⟶ S)
    (cS : Cone S) (T : Scheme.{u}) (t : T ⟶ cS.pt)
    [∀ i, HasPullback (g.app i) (t ≫ cS.π.app i)]
    {i j : I} (h : i ⟶ j) :
    (pullbackDiagramAlongLimit g cS T t).map h ≫
        pullback.snd (g.app j) (t ≫ cS.π.app j) =
      pullback.snd (g.app i) (t ≫ cS.π.app i) :=
  pullbackDiagramAlongLimitMap_snd g cS T t h

private noncomputable def pullbackConeAlongLimit
    {I : Type u} [Category.{u} I] {F S : I ⥤ Scheme.{u}} (g : F ⟶ S)
    (cF : Cone F) (_hcF : IsLimit cF) (cS : Cone S) (hcS : IsLimit cS)
    (T : Scheme.{u}) (t : T ⟶ cS.pt)
    [∀ i, HasPullback (g.app i) (t ≫ cS.π.app i)] :
    Cone (pullbackDiagramAlongLimit g cS T t) := by
  let f₀ := hcS.lift ((Cone.postcompose g).obj cF)
  let l : ∀ i, pullback f₀ t ⟶ pullback (g.app i) (t ≫ cS.π.app i) := fun i =>
    pullback.lift (pullback.fst f₀ t ≫ cF.π.app i) (pullback.snd f₀ t) (by
      have hlim : f₀ ≫ cS.π.app i = cF.π.app i ≫ g.app i := by
        simpa only [f₀, Cone.postcompose_obj_π, NatTrans.comp_app] using
          hcS.fac ((Cone.postcompose g).obj cF) i
      rw [Category.assoc, ← hlim, pullback.condition_assoc])
  refine { pt := pullback f₀ t, π := { app := l, naturality := ?_ } }
  intro i j h
  change l j = l i ≫ (pullbackDiagramAlongLimit g cS T t).map h
  have hli_fst : l i ≫ pullback.fst (g.app i) (t ≫ cS.π.app i) =
      pullback.fst f₀ t ≫ cF.π.app i := by
    dsimp [l]
    exact pullback.lift_fst _ _ _
  have hli_snd : l i ≫ pullback.snd (g.app i) (t ≫ cS.π.app i) =
      pullback.snd f₀ t := by
    dsimp [l]
    exact pullback.lift_snd _ _ _
  apply pullback.hom_ext
  · calc
      l j ≫ pullback.fst (g.app j) (t ≫ cS.π.app j) =
          pullback.fst f₀ t ≫ cF.π.app j := pullback.lift_fst _ _ _
      _ = pullback.fst f₀ t ≫ cF.π.app i ≫ F.map h := by rw [cF.w h]
      _ = l i ≫ pullback.fst (g.app i) (t ≫ cS.π.app i) ≫ F.map h :=
            (congrArg (fun q => q ≫ F.map h) hli_fst).symm
      _ = l i ≫ ((pullbackDiagramAlongLimit g cS T t).map h ≫
          pullback.fst (g.app j) (t ≫ cS.π.app j)) :=
            congrArg (fun q => l i ≫ q)
              (pullbackDiagramAlongLimit_fst g cS T t h).symm
      _ = _ := (Category.assoc _ _ _).symm
  · calc
      l j ≫ pullback.snd (g.app j) (t ≫ cS.π.app j) = pullback.snd f₀ t :=
          pullback.lift_snd _ _ _
      _ = l i ≫ pullback.snd (g.app i) (t ≫ cS.π.app i) := hli_snd.symm
      _ = l i ≫ ((pullbackDiagramAlongLimit g cS T t).map h ≫
          pullback.snd (g.app j) (t ≫ cS.π.app j)) :=
            congrArg (fun q => l i ≫ q)
              (pullbackDiagramAlongLimit_snd g cS T t h).symm
      _ = _ := (Category.assoc _ _ _).symm

private noncomputable def isLimit_pullbackConeAlongLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {F S : I ⥤ Scheme.{u}} (g : F ⟶ S)
    (cF : Cone F) (hcF : IsLimit cF) (cS : Cone S) (hcS : IsLimit cS)
    (T : Scheme.{u}) (t : T ⟶ cS.pt)
    [∀ i, HasPullback (g.app i) (t ≫ cS.π.app i)] :
    IsLimit (pullbackConeAlongLimit g cF hcF cS hcS T t) := by
  classical
  letI : Nonempty I := IsCofiltered.nonempty
  let P := pullbackDiagramAlongLimit g cS T t
  let cP := pullbackConeAlongLimit g cF hcF cS hcS T t
  let f₀ := hcS.lift ((Cone.postcompose g).obj cF)
  have hcPfst (i : I) :
      cP.π.app i ≫ pullback.fst (g.app i) (t ≫ cS.π.app i) =
        pullback.fst f₀ t ≫ cF.π.app i := by
    change pullback.lift (pullback.fst f₀ t ≫ cF.π.app i)
        (pullback.snd f₀ t) _ ≫ pullback.fst (g.app i) (t ≫ cS.π.app i) = _
    exact pullback.lift_fst _ _ _
  have hcPsnd (i : I) :
      cP.π.app i ≫ pullback.snd (g.app i) (t ≫ cS.π.app i) =
        pullback.snd f₀ t := by
    change pullback.lift (pullback.fst f₀ t ≫ cF.π.app i)
        (pullback.snd f₀ t) _ ≫ pullback.snd (g.app i) (t ≫ cS.π.app i) = _
    exact pullback.lift_snd _ _ _
  let cF' (s : Cone (pullbackDiagramAlongLimit g cS T t)) : Cone F := {
    pt := s.pt
    π := {
      app i := s.π.app i ≫ pullback.fst (g.app i) (t ≫ cS.π.app i)
      naturality := by
        intro i j h
        calc
          s.π.app j ≫ pullback.fst (g.app j) (t ≫ cS.π.app j) =
              s.π.app i ≫ (pullbackDiagramAlongLimit g cS T t).map h ≫
                pullback.fst (g.app j) (t ≫ cS.π.app j) :=
                  congrArg (fun q => q ≫
                    pullback.fst (g.app j) (t ≫ cS.π.app j)) (s.w h).symm
          _ = (s.π.app i ≫ pullback.fst (g.app i) (t ≫ cS.π.app i)) ≫ F.map h := by
                calc
                  _ = s.π.app i ≫
                      ((pullbackDiagramAlongLimit g cS T t).map h ≫
                        pullback.fst (g.app j) (t ≫ cS.π.app j)) := Category.assoc _ _ _
                  _ = s.π.app i ≫
                      (pullback.fst (g.app i) (t ≫ cS.π.app i) ≫ F.map h) :=
                        congrArg (fun q => s.π.app i ≫ q)
                          (pullbackDiagramAlongLimit_fst g cS T t h)
                  _ = _ := (Category.assoc _ _ _).symm
    }
  }
  let i₀ : I := Classical.arbitrary I
  have hb (s : Cone (pullbackDiagramAlongLimit g cS T t)) (i : I) :
      s.π.app i ≫ pullback.snd (g.app i) (t ≫ cS.π.app i) =
        s.π.app i₀ ≫ pullback.snd (g.app i₀) (t ≫ cS.π.app i₀) := by
    obtain ⟨k, hki, hki₀, _⟩ := IsCofilteredOrEmpty.cone_objs i i₀
    calc
      s.π.app i ≫ pullback.snd (g.app i) (t ≫ cS.π.app i) =
          s.π.app k ≫ (pullbackDiagramAlongLimit g cS T t).map hki ≫
            pullback.snd (g.app i) (t ≫ cS.π.app i) :=
        congrArg (fun q => q ≫ pullback.snd (g.app i) (t ≫ cS.π.app i))
          (s.w hki).symm
      _ = s.π.app k ≫ pullback.snd (g.app k) (t ≫ cS.π.app k) := by
        calc
          _ = s.π.app k ≫
              ((pullbackDiagramAlongLimit g cS T t).map hki ≫
                pullback.snd (g.app i) (t ≫ cS.π.app i)) := Category.assoc _ _ _
          _ = s.π.app k ≫ pullback.snd (g.app k) (t ≫ cS.π.app k) :=
                congrArg (fun q => s.π.app k ≫ q)
                  (pullbackDiagramAlongLimit_snd g cS T t hki)
      _ = s.π.app k ≫ (pullbackDiagramAlongLimit g cS T t).map hki₀ ≫
          pullback.snd (g.app i₀) (t ≫ cS.π.app i₀) := by
        calc
          _ = s.π.app k ≫
              ((pullbackDiagramAlongLimit g cS T t).map hki₀ ≫
                pullback.snd (g.app i₀) (t ≫ cS.π.app i₀)) :=
                  congrArg (fun q => s.π.app k ≫ q)
                    (pullbackDiagramAlongLimit_snd g cS T t hki₀).symm
          _ = _ := (Category.assoc _ _ _).symm
      _ = s.π.app i₀ ≫ pullback.snd (g.app i₀) (t ≫ cS.π.app i₀) :=
        congrArg (fun q => q ≫ pullback.snd (g.app i₀) (t ≫ cS.π.app i₀)) (s.w hki₀)
  have hab (s : Cone (pullbackDiagramAlongLimit g cS T t)) :
      hcF.lift (cF' s) ≫ f₀ =
        (s.π.app i₀ ≫ pullback.snd (g.app i₀) (t ≫ cS.π.app i₀)) ≫ t := by
    apply hcS.hom_ext
    intro i
    have hlim : f₀ ≫ cS.π.app i = cF.π.app i ≫ g.app i := by
      simpa only [f₀, Cone.postcompose_obj_π, NatTrans.comp_app] using
        hcS.fac ((Cone.postcompose g).obj cF) i
    calc
      hcF.lift (cF' s) ≫ f₀ ≫ cS.π.app i =
          (hcF.lift (cF' s) ≫ cF.π.app i) ≫ g.app i := by
        rw [hlim, Category.assoc]
      _ = (s.π.app i ≫ pullback.fst (g.app i) (t ≫ cS.π.app i)) ≫ g.app i := by
        rw [hcF.fac]
      _ = (s.π.app i ≫ pullback.snd (g.app i) (t ≫ cS.π.app i)) ≫ t ≫ cS.π.app i := by
        calc
          _ = s.π.app i ≫
              (pullback.fst (g.app i) (t ≫ cS.π.app i) ≫ g.app i) := Category.assoc _ _ _
          _ = s.π.app i ≫
              (pullback.snd (g.app i) (t ≫ cS.π.app i) ≫
                (t ≫ cS.π.app i)) := congrArg (fun q => s.π.app i ≫ q) pullback.condition
          _ = _ := (Category.assoc _ _ _).symm
      _ = (s.π.app i₀ ≫ pullback.snd (g.app i₀) (t ≫ cS.π.app i₀)) ≫ t ≫ cS.π.app i := by
        rw [hb s i]
  refine {
    lift s := pullback.lift (hcF.lift (cF' s))
      (s.π.app i₀ ≫ pullback.snd (g.app i₀) (t ≫ cS.π.app i₀)) (hab s)
    fac := ?_
    uniq := ?_
  }
  · intro s i
    change pullback.lift (hcF.lift (cF' s)) _ (hab s) ≫
        pullback.lift (pullback.fst f₀ t ≫ cF.π.app i)
          (pullback.snd f₀ t) _ = s.π.app i
    apply pullback.hom_ext
    · calc
        (pullback.lift (hcF.lift (cF' s)) _ (hab s) ≫
            pullback.lift (pullback.fst f₀ t ≫ cF.π.app i)
              (pullback.snd f₀ t) _) ≫ pullback.fst (g.app i) (t ≫ cS.π.app i) =
            hcF.lift (cF' s) ≫ cF.π.app i := by
          simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
        _ = s.π.app i ≫ pullback.fst (g.app i) (t ≫ cS.π.app i) := hcF.fac (cF' s) i
    · calc
        (pullback.lift (hcF.lift (cF' s)) _ (hab s) ≫
            pullback.lift (pullback.fst f₀ t ≫ cF.π.app i)
              (pullback.snd f₀ t) _) ≫ pullback.snd (g.app i) (t ≫ cS.π.app i) =
            s.π.app i₀ ≫ pullback.snd (g.app i₀) (t ≫ cS.π.app i₀) := by
          simp only [Category.assoc, pullback.lift_snd]
        _ = s.π.app i ≫ pullback.snd (g.app i) (t ≫ cS.π.app i) := (hb s i).symm
  · intro s m hm
    apply pullback.hom_ext
    · apply hcF.hom_ext
      intro i
      calc
        m ≫ pullback.fst f₀ t ≫ cF.π.app i =
            (m ≫ cP.π.app i) ≫ pullback.fst (g.app i) (t ≫ cS.π.app i) :=
          (congrArg (fun q => m ≫ q) (hcPfst i).symm).trans (Category.assoc _ _ _).symm
        _ = s.π.app i ≫ pullback.fst (g.app i) (t ≫ cS.π.app i) := by rw [hm i]
        _ = hcF.lift (cF' s) ≫ cF.π.app i := (hcF.fac (cF' s) i).symm
        _ = _ := by rw [Category.assoc, pullback.lift_fst_assoc]
    · calc
        m ≫ pullback.snd f₀ t =
            (m ≫ cP.π.app i₀) ≫ pullback.snd (g.app i₀) (t ≫ cS.π.app i₀) :=
          (congrArg (fun q => m ≫ q) (hcPsnd i₀).symm).trans (Category.assoc _ _ _).symm
        _ = s.π.app i₀ ≫ pullback.snd (g.app i₀) (t ≫ cS.π.app i₀) := by rw [hm i₀]
        _ = _ := (pullback.lift_snd _ _ _).symm

private lemma isClosedImmersion_pullbackDiagramAlongLimit_map
    {I : Type u} [Category.{u} I] {X S : I ⥤ Scheme.{u}} (f : X ⟶ S)
    (cS : Cone S) (T : Scheme.{u}) (t : T ⟶ cS.pt)
    [∀ i, HasPullback (f.app i) (t ≫ cS.π.app i)]
    [∀ {i j : I} (g : i ⟶ j),
      IsClosedImmersion (pullback.lift (X.map g) (f.app i) (f.naturality g))]
    {i j : I} (g : i ⟶ j) :
    IsClosedImmersion ((pullbackDiagramAlongLimit f cS T t).map g) := by
  classical
  let ti := t ≫ cS.π.app i
  let tj := t ≫ cS.π.app j
  have ht : ti ≫ S.map g = tj := by
    dsimp [ti, tj]
    rw [Category.assoc, ← cS.w g]
  let e := pullback.lift (X.map g) (f.app i) (f.naturality g)
  let r : pullback (f.app j) tj ⟶ pullback (f.app j) (S.map g) :=
    pullback.lift (pullback.fst (f.app j) tj)
      (pullback.snd (f.app j) tj ≫ ti) (by
        rw [Category.assoc, ht]
        exact pullback.condition)
  have hright : IsPullback r (pullback.snd (f.app j) tj)
      (pullback.snd (f.app j) (S.map g)) ti := by
    have hs : IsPullback (r ≫ pullback.fst (f.app j) (S.map g))
        (pullback.snd (f.app j) tj) (f.app j) (ti ≫ S.map g) := by
      rw [pullback.lift_fst, ht]
      exact IsPullback.of_hasPullback (f.app j) tj
    exact hs.of_right (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback (f.app j) (S.map g))
  have hleft : IsPullback ((pullbackDiagramAlongLimit f cS T t).map g)
      (pullback.fst (f.app i) ti) r e := by
    have hs : IsPullback
        (((pullbackDiagramAlongLimit f cS T t).map g) ≫ pullback.snd (f.app j) tj)
        (pullback.fst (f.app i) ti) ti
        (e ≫ pullback.snd (f.app j) (S.map g)) := by
      rw [pullbackDiagramAlongLimit_snd, pullback.lift_snd]
      exact (IsPullback.of_hasPullback (f.app i) ti).flip
    have hp : ((pullbackDiagramAlongLimit f cS T t).map g) ≫ r =
        pullback.fst (f.app i) ti ≫ e := by
      show pullbackDiagramAlongLimitMap f cS T t g ≫ r =
        pullback.fst (f.app i) ti ≫ e
      apply pullback.hom_ext
      · have hrfst : r ≫ pullback.fst (f.app j) (S.map g) =
            pullback.fst (f.app j) tj := pullback.lift_fst _ _ _
        have hefst : e ≫ pullback.fst (f.app j) (S.map g) =
            X.map g := pullback.lift_fst _ _ _
        simp only [Category.assoc, hrfst, hefst]
        exact pullbackDiagramAlongLimitMap_fst f cS T t g
      · have hrsnd : r ≫ pullback.snd (f.app j) (S.map g) =
            pullback.snd (f.app j) tj ≫ ti := pullback.lift_snd _ _ _
        have hesnd : e ≫ pullback.snd (f.app j) (S.map g) =
            f.app i := pullback.lift_snd _ _ _
        simp only [Category.assoc, hrsnd, hesnd,
          pullback.condition]
        exact congrArg (fun q => q ≫ ti)
          (pullbackDiagramAlongLimitMap_snd f cS T t g)
    exact hs.of_right hp hright.flip
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsClosedImmersion) hleft.flip inferInstance

/-- The case of `exists_forall_topologicalKrullDim_fiber_le_of_isLimit_of_essentiallySmall`
where the index category is literally small: `I : Type u` with morphisms in `Type u`. -/
private lemma exists_forall_topologicalKrullDim_fiber_le_of_isLimit_small
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (X S : I ⥤ Scheme.{u}) (f : X ⟶ S)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (S.map g)]
    [∀ i : I, CompactSpace (S.obj i)] [∀ i : I, QuasiSeparatedSpace (S.obj i)]
    [∀ i : I, LocallyOfFiniteType (f.app i)] [∀ i : I, QuasiCompact (f.app i)]
    [∀ {i j : I} (g : i ⟶ j),
      IsClosedImmersion (pullback.lift (X.map g) (f.app i) (f.naturality g))]
    (cX : Cone X) (hcX : IsLimit cX) (cS : Cone S) (hcS : IsLimit cS) (d : ℕ)
    (hdim : ∀ s : cS.pt,
      topologicalKrullDim
        ((hcS.lift ((Cone.postcompose f).obj cX)).fiber s) ≤ (d : WithBot ℕ∞)) :
    ∃ i : I, ∀ s : S.obj i,
      topologicalKrullDim ((f.app i).fiber s) ≤ (d : WithBot ℕ∞) := by
  classical
  by_contra hresult
  push Not at hresult
  let fLimit := hcS.lift ((Cone.postcompose f).obj cX)
  have htrans {i j : I} (g : i ⟶ j) : IsAffineHom (X.map g) := by
    let : MorphismProperty.IsStableUnderBaseChange (P := @IsAffineHom) := inferInstance
    let : MorphismProperty.IsStableUnderBaseChangeAlong (P := @IsAffineHom) (f.app j) :=
      ⟨fun pb h =>
        (inferInstance : MorphismProperty.IsStableUnderBaseChange (P := @IsAffineHom))
          |>.of_isPullback pb h⟩
    let e := pullback.lift (X.map g) (f.app i) (f.naturality g)
    have : IsAffineHom e := inferInstance
    have hp : IsAffineHom (pullback.fst (f.app j) (S.map g)) :=
      MorphismProperty.pullback_fst (P := @IsAffineHom) (f.app j) (S.map g)
        (inferInstance : IsAffineHom (S.map g))
    have he : e ≫ pullback.fst (f.app j) (S.map g) = X.map g :=
      pullback.lift_fst _ _ _
    rw [← he]
    infer_instance
  have hcompact (i : I) : CompactSpace (X.obj i) :=
    QuasiCompact.compactSpace_of_compactSpace (f.app i)
  have hbad_closed (i : I) : IsClosed
      {x : X.obj i | ¬ topologicalKrullDimAt ((f.app i).fiber (f.app i x))
          ((f.app i).asFiber x) ≤ (d : WithBot ℕ∞)} := by
    simpa only [Set.compl_ofPred] using
      (AlgebraicGeometry.isOpen_setOf_fiberDimensionAt_le (f.app i) d).isClosed_compl
  have hbad_maps (i j : I) (g : i ⟶ j) :
      Set.MapsTo (X.map g)
        {x : X.obj i | ¬ topologicalKrullDimAt ((f.app i).fiber (f.app i x))
          ((f.app i).asFiber x) ≤ (d : WithBot ℕ∞)}
        {x : X.obj j | ¬ topologicalKrullDimAt ((f.app j).fiber (f.app j x))
          ((f.app j).asFiber x) ≤ (d : WithBot ℕ∞)} := by
    intro x hx
    let e := pullback.lift (X.map g) (f.app i) (f.naturality g)
    let p := pullback.snd (f.app j) (S.map g)
    have he : e ≫ p = f.app i := by
      dsimp [e, p]
      exact pullback.lift_snd _ _ _
    have hle := fiberDimensionAt_le_of_closedImmersion_over e (f.app i) p
      he x
    have hpull : IsPullback (pullback.fst (f.app j) (S.map g)) p
        (f.app j) (S.map g) := IsPullback.of_hasPullback _ _
    have heq := (topologicalKrullDimAt_fiber_eq_of_isPullback hpull (e x)).symm
    have hfst : (pullback.fst (f.app j) (S.map g)) (e x) = X.map g x := by
      have hcomp : e ≫ pullback.fst (f.app j) (S.map g) = X.map g := by
        dsimp [e]
        exact pullback.lift_fst _ _ _
      have h := congrArg (fun q : X.obj i ⟶ X.obj j => q x) hcomp
      simpa only [Scheme.Hom.comp_apply] using h
    have heq' : topologicalKrullDimAt ((f.app j).fiber ((f.app j) (X.map g x)))
        ((f.app j).asFiber (X.map g x)) =
        topologicalKrullDimAt (p.fiber (p (e x))) (p.asFiber (e x)) := by
      rw [← hfst]
      simpa [p] using heq
    change ¬ topologicalKrullDimAt ((f.app i).fiber ((f.app i) x))
      ((f.app i).asFiber x) ≤ (d : WithBot ℕ∞) at hx
    show ¬ topologicalKrullDimAt ((f.app j).fiber ((f.app j) (X.map g x)))
      ((f.app j).asFiber (X.map g x)) ≤ (d : WithBot ℕ∞)
    exact fun hj => hx (hle.trans (heq'.symm ▸ hj))
  have hbad_ne : ∀ i : I,
      {x : X.obj i | ¬ topologicalKrullDimAt ((f.app i).fiber (f.app i x))
        ((f.app i).asFiber x) ≤ (d : WithBot ℕ∞)}.Nonempty := by
    intro i
    obtain ⟨s, hs⟩ := hresult i
    have hgt : (d : WithBot ℕ∞) < topologicalKrullDim ((f.app i).fiber s) := hs
    obtain ⟨x, hx⟩ := exists_pointwise_dimension_gt_of_topologicalKrullDim_gt hgt
    generalize hydef : (f.app i).fiberι s x = y
    have hfy : (f.app i) y = s := by
      have hy : y ∈ (f.app i) ⁻¹' {s} := by
        rw [← (f.app i).range_fiberι s]
        exact ⟨x, hydef⟩
      exact Set.mem_singleton_iff.mp hy
    refine ⟨y, ?_⟩
    have hybad : ¬ topologicalKrullDimAt ((f.app i).fiber ((f.app i) y))
        ((f.app i).asFiber y) ≤ (d : WithBot ℕ∞) := by
      cases hfy
      have hpoint : (f.app i).asFiber y = x := by
        apply (f.app i).fiberι ((f.app i) y) |>.isEmbedding.injective
        rw [Scheme.Hom.fiberι_asFiber]
        exact hydef.symm
      rw [hpoint]
      exact not_le_of_gt hx
    exact hybad
  let : ∀ {i j : I} (g : i ⟶ j), IsAffineHom (X.map g) :=
    fun {_ _} g => htrans g
  obtain ⟨z, hz⟩ := exists_mem_of_isClosed_of_nonempty X cX hcX
    (fun i => {x : X.obj i | ¬ topologicalKrullDimAt
      ((f.app i).fiber (f.app i x)) ((f.app i).asFiber x) ≤ (d : WithBot ℕ∞)})
    hbad_closed hbad_ne (fun i => (hbad_closed i).isCompact) (fun g => hbad_maps _ _ g)
  let s : cS.pt := fLimit z
  let T : Scheme.{u} := Spec (cS.pt.residueField s)
  let t : T ⟶ cS.pt := cS.pt.fromSpecResidueField s
  let D := pullbackDiagramAlongLimit f cS T t
  let c := pullbackConeAlongLimit f cX hcX cS hcS T t
  have hc : IsLimit c := isLimit_pullbackConeAlongLimit f cX hcX cS hcS T t
  have hclosed : ∀ {i j : I} (g : i ⟶ j), IsClosedImmersion (D.map g) := by
    intro i j g
    exact isClosedImmersion_pullbackDiagramAlongLimit_map f cS T t g
  let : ∀ {i j : I} (g : i ⟶ j), IsClosedImmersion (D.map g) :=
    fun {_ _} g => hclosed g
  let i : I := Classical.choice (IsCofiltered.nonempty : Nonempty I)
  have hnoeth : IsNoetherian (D.obj i) := by
    let q : D.obj i ⟶ T := pullback.snd (f.app i) (t ≫ cS.π.app i)
    have : IsLocallyNoetherian (D.obj i) := by
      show IsLocallyNoetherian (pullback (f.app i) (t ≫ cS.π.app i))
      infer_instance
    have : QuasiCompact q := by
      dsimp [q]
      let : MorphismProperty.IsStableUnderBaseChangeAlong
          (P := @QuasiCompact) (t ≫ cS.π.app i) :=
        ⟨fun pb h =>
          (inferInstance : MorphismProperty.IsStableUnderBaseChange (P := @QuasiCompact))
            |>.of_isPullback pb h⟩
      exact MorphismProperty.pullback_snd (P := @QuasiCompact)
        (f.app i) (t ≫ cS.π.app i) inferInstance
    have : CompactSpace (D.obj i) := QuasiCompact.compactSpace_of_compactSpace q
    exact ⟨⟩
  let : IsNoetherian (D.obj i) := hnoeth
  obtain ⟨j, hj⟩ := isIso_projection_of_noetherian_closed_diagram D c hc i
  let p : c.pt := (fLimit.asFiber z)
  have hproj (k : I) :
      (pullback.fst (f.app k) (t ≫ cS.π.app k)) (c.π.app k p) = cX.π.app k z := by
    have hh : c.π.app k ≫ pullback.fst (f.app k) (t ≫ cS.π.app k) =
        (fLimit.fiberι s) ≫ cX.π.app k := by
      show pullback.lift (pullback.fst fLimit t ≫ cX.π.app k)
        (pullback.snd fLimit t) _ ≫ pullback.fst (f.app k) (t ≫ cS.π.app k) = _
      exact pullback.lift_fst _ _ _
    have hp := congrArg (fun q : c.pt ⟶ X.obj k => q p) hh
    change (pullback.fst (f.app k) (t ≫ cS.π.app k)) (c.π.app k p) =
      (cX.π.app k) ((fLimit.fiberι s) p) at hp
    simpa [p, s, Scheme.Hom.fiberι_asFiber] using hp
  have hgt : (d : WithBot ℕ∞) <
      topologicalKrullDimAt (D.obj j) (c.π.app j p) := by
    have heq := (topologicalKrullDimAt_fiber_eq_of_isPullback
      (IsPullback.of_hasPullback (f.app j) (t ≫ cS.π.app j)) (c.π.app j p)).symm
    rw [hproj j] at heq
    have hbad := hz j
    change ¬ topologicalKrullDimAt ((f.app j).fiber (f.app j (cX.π.app j z)))
      ((f.app j).asFiber (cX.π.app j z)) ≤ (d : WithBot ℕ∞) at hbad
    have hsub : Subsingleton T := inferInstance
    have hdim : topologicalKrullDimAt
        ((pullback.snd (f.app j) (t ≫ cS.π.app j)).fiber
          ((pullback.snd (f.app j) (t ≫ cS.π.app j)) (c.π.app j p)))
        ((pullback.snd (f.app j) (t ≫ cS.π.app j)).asFiber (c.π.app j p)) =
        topologicalKrullDimAt (D.obj j) (c.π.app j p) :=
      (topologicalKrullDimAt_eq_fiber_of_subsingleton
        (pullback.snd (f.app j) (t ≫ cS.π.app j)) (c.π.app j p)).symm
    rw [heq, hdim] at hbad
    exact lt_of_not_ge hbad
  have hlim : topologicalKrullDimAt (D.obj j) (c.π.app j p) =
      topologicalKrullDimAt c.pt p :=
    (topologicalKrullDimAt_eq_of_homeomorph
      (c.π.app j).homeomorph p).symm
  rw [hlim] at hgt
  exact (not_le_of_gt hgt)
    ((topologicalKrullDimAt_le_topologicalKrullDim p).trans (hdim s))

/-- **Stacks Project, Tag 05M5**, for an index category that is essentially small relative to
the universe of the schemes: a uniform bound on the dimensions of the fibres of a morphism
between inverse limits already holds at some stage. -/
@[stacks 05M5]
public lemma exists_forall_topologicalKrullDim_fiber_le_of_isLimit_of_essentiallySmall
    {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (X S : I ⥤ Scheme.{u}) (f : X ⟶ S)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (S.map g)]
    [∀ i : I, CompactSpace (S.obj i)] [∀ i : I, QuasiSeparatedSpace (S.obj i)]
    [∀ i : I, LocallyOfFiniteType (f.app i)] [∀ i : I, QuasiCompact (f.app i)]
    [∀ {i j : I} (g : i ⟶ j),
      IsClosedImmersion (pullback.lift (X.map g) (f.app i) (f.naturality g))]
    (cX : Cone X) (hcX : IsLimit cX) (cS : Cone S) (hcS : IsLimit cS) (d : ℕ)
    (hdim : ∀ s : cS.pt,
      topologicalKrullDim
        ((hcS.lift ((Cone.postcompose f).obj cX)).fiber s) ≤ (d : WithBot ℕ∞)) :
    ∃ i : I, ∀ s : S.obj i,
      topologicalKrullDim ((f.app i).fiber s) ≤ (d : WithBot ℕ∞) := by
  classical
  let : IsCofiltered (SmallModel.{u} I) := .of_equivalence (equivSmallModel.{u} I)
  let e : SmallModel.{u} I ≌ I := (equivSmallModel.{u} I).symm
  let X' : SmallModel.{u} I ⥤ Scheme.{u} := e.functor ⋙ X
  let S' : SmallModel.{u} I ⥤ Scheme.{u} := e.functor ⋙ S
  let f' : X' ⟶ S' := Functor.whiskerLeft e.functor f
  let cX' : Cone X' := cX.whisker e.functor
  let cS' : Cone S' := cS.whisker e.functor
  have hcX' : IsLimit cX' := hcX.whiskerEquivalence e
  have hcS' : IsLimit cS' := hcS.whiskerEquivalence e
  let : ∀ {i j : SmallModel.{u} I} (g : i ⟶ j), IsAffineHom (S'.map g) :=
    fun {_ _} g => inferInstanceAs (IsAffineHom (S.map (e.functor.map g)))
  let : ∀ i : SmallModel.{u} I, CompactSpace (S'.obj i) :=
    fun i => inferInstanceAs (CompactSpace (S.obj (e.functor.obj i)))
  let : ∀ i : SmallModel.{u} I, QuasiSeparatedSpace (S'.obj i) :=
    fun i => inferInstanceAs (QuasiSeparatedSpace (S.obj (e.functor.obj i)))
  let : ∀ i : SmallModel.{u} I, LocallyOfFiniteType (f'.app i) :=
    fun i => inferInstanceAs (LocallyOfFiniteType (f.app (e.functor.obj i)))
  let : ∀ i : SmallModel.{u} I, QuasiCompact (f'.app i) :=
    fun i => inferInstanceAs (QuasiCompact (f.app (e.functor.obj i)))
  let : ∀ {i j : SmallModel.{u} I} (g : i ⟶ j),
      IsClosedImmersion (pullback.lift (X'.map g) (f'.app i) (f'.naturality g)) :=
    fun {_ _} g => inferInstanceAs (IsClosedImmersion
      (pullback.lift (X.map (e.functor.map g)) (f.app _) (f.naturality (e.functor.map g))))
  have hlift : hcS'.lift ((Cone.postcompose f').obj cX') =
      hcS.lift ((Cone.postcompose f).obj cX) := by
    refine hcS'.hom_ext fun j => ?_
    rw [hcS'.fac]
    exact (hcS.fac ((Cone.postcompose f).obj cX) (e.functor.obj j)).symm
  have hdim' : ∀ s : cS'.pt, topologicalKrullDim
      ((hcS'.lift ((Cone.postcompose f').obj cX')).fiber s) ≤ (d : WithBot ℕ∞) := by
    intro s
    rw [hlift]
    exact hdim s
  obtain ⟨j, hj⟩ := exists_forall_topologicalKrullDim_fiber_le_of_isLimit_small
    X' S' f' cX' hcX' cS' hcS' d hdim'
  exact ⟨e.functor.obj j, hj⟩

/-!
### The index universes cannot be dropped

The remainder of the file shows that the statement above becomes false if the index category is
allowed to be large relative to the universe of the schemes.  The counterexample is the inverse
system indexed by the finite subsets `T` of `Cardinal.{u}` whose `T`-th stage is the spectrum of
the rational function field `ℚ(x_t : t ∈ T)`, together with the affine lines over these fields.
Both limits in `Scheme.{u}` are the empty scheme, because a cone with nonempty vertex `W` would
give a compatible family of ring maps out of the stage fields and hence, the stage fields being
fields, an injection of `Cardinal.{u}` into `Γ(W, ⊤)`.  So the dimension hypothesis on the limit
is vacuous, while every stage fibre is an affine line over a field and therefore
one-dimensional.
-/

/-- The index type of the counterexample.  It is essential that it is not `Small.{u}`:
no injection of it into a `Type u` exists. -/
private abbrev BigIndex : Type (u + 1) := Cardinal.{u}

private instance : IsDirected (Finset BigIndex.{u}) (· ≤ ·) := by
  classical
  exact ⟨fun a b => ⟨a ∪ b, Finset.subset_union_left, Finset.subset_union_right⟩⟩

private instance small_coe_finset (T : Finset BigIndex.{u}) : Small.{u} (↑T : Type (u + 1)) :=
  small_map T.equivFin

/-- The variables of the `T`-th stage: a `Type u` model of the finite set `T`. -/
private def StageVar (T : Finset BigIndex.{u}) : Type u := Shrink.{u} (↑T : Type (u + 1))

/-- The variable attached to a member of `T`. -/
private noncomputable def stageVar {T : Finset BigIndex.{u}} {a : BigIndex.{u}} (ha : a ∈ T) :
    StageVar T :=
  equivShrink _ ⟨a, ha⟩

/-- The transition on variables induced by an inclusion of finite sets. -/
private noncomputable def stageVarMap {T T' : Finset BigIndex.{u}} (h : T ≤ T') :
    StageVar T → StageVar T' :=
  fun x => equivShrink _ ⟨((equivShrink (↑T : Type (u+1))).symm x : BigIndex.{u}),
    h ((equivShrink (↑T : Type (u+1))).symm x).2⟩

private lemma stageVarMap_varOf {T T' : Finset BigIndex.{u}} (h : T ≤ T') {a : BigIndex.{u}}
    (ha : a ∈ T) :
    stageVarMap h (stageVar ha) = stageVar (h ha) := by
  simp only [stageVarMap, stageVar, Equiv.symm_apply_apply]
  rfl

private lemma stageVarMap_injective {T T' : Finset BigIndex.{u}} (h : T ≤ T') :
    Function.Injective (stageVarMap h) := by
  intro x y hxy
  have h1 := (equivShrink (↑T' : Type (u+1))).injective hxy
  have h2 : ((equivShrink (↑T : Type (u+1))).symm x : BigIndex.{u}) =
      ((equivShrink (↑T : Type (u+1))).symm y : BigIndex.{u}) :=
    congrArg (fun z : (↑T' : Type (u+1)) => (z : BigIndex.{u})) h1
  exact (equivShrink (↑T : Type (u+1))).symm.injective (Subtype.ext h2)

private lemma stageVarMap_id (T : Finset BigIndex.{u}) : stageVarMap (le_refl T) = id := by
  funext x
  show equivShrink _ ⟨_, _⟩ = x
  rw [Subtype.coe_eta]
  exact (equivShrink (↑T : Type (u+1))).apply_symm_apply x

private lemma stageVarMap_comp {T₁ T₂ T₃ : Finset BigIndex.{u}} (h : T₁ ≤ T₂) (h' : T₂ ≤ T₃) :
    stageVarMap h' ∘ stageVarMap h = stageVarMap (h.trans h') := by
  funext x
  simp only [Function.comp_apply, stageVarMap, Equiv.symm_apply_apply]
  rfl

/-- The polynomial ring `ℚ[x_t : t ∈ T]` of the `T`-th stage. -/
private abbrev StagePoly (T : Finset BigIndex.{u}) : Type u := MvPolynomial (StageVar T) ℚ

/-- The rational function field `ℚ(x_t : t ∈ T)` of the `T`-th stage. -/
private abbrev StageField (T : Finset BigIndex.{u}) : Type u := FractionRing (StagePoly T)

/-- The transition `ℚ[x_t : t ∈ T] → ℚ[x_t : t ∈ T']` of polynomial rings. -/
private noncomputable def stagePolyMap {T T' : Finset BigIndex.{u}} (h : T ≤ T') :
    StagePoly T →+* StagePoly T' :=
  (MvPolynomial.rename (stageVarMap h)).toRingHom

private lemma stagePolyMap_injective {T T' : Finset BigIndex.{u}} (h : T ≤ T') :
    Function.Injective (stagePolyMap h) :=
  MvPolynomial.rename_injective _ (stageVarMap_injective h)

/-- The transition `ℚ(x_t : t ∈ T) → ℚ(x_t : t ∈ T')` of rational function fields. -/
private noncomputable def stageFieldMap {T T' : Finset BigIndex.{u}} (h : T ≤ T') :
    StageField T →+* StageField T' :=
  IsFractionRing.lift (A := StagePoly T) (K := StageField T)
    (g := (algebraMap (StagePoly T') (StageField T')).comp (stagePolyMap h))
    ((IsFractionRing.injective (StagePoly T') (StageField T')).comp (stagePolyMap_injective h))

private lemma stageFieldMap_algebraMap {T T' : Finset BigIndex.{u}} (h : T ≤ T') (x : StagePoly T) :
    stageFieldMap h (algebraMap (StagePoly T) (StageField T) x) =
      algebraMap (StagePoly T') (StageField T') (stagePolyMap h x) :=
  IsFractionRing.lift_algebraMap _ x

private lemma stageFieldMap_id (T : Finset BigIndex.{u}) :
    stageFieldMap (le_refl T) = RingHom.id (StageField T) := by
  refine IsFractionRing.ringHom_ext (A := StagePoly T) fun x => ?_
  rw [stageFieldMap_algebraMap]
  simp [stagePolyMap, stageVarMap_id]

private lemma stageFieldMap_comp {T₁ T₂ T₃ : Finset BigIndex.{u}} (h : T₁ ≤ T₂) (h' : T₂ ≤ T₃) :
    (stageFieldMap h').comp (stageFieldMap h) = stageFieldMap (h.trans h') := by
  refine IsFractionRing.ringHom_ext (A := StagePoly T₁) fun x => ?_
  simp only [RingHom.comp_apply, stageFieldMap_algebraMap]
  congr 1
  simp [stagePolyMap, MvPolynomial.rename_rename, stageVarMap_comp]

/-- The system of rational function fields, as a functor to commutative rings. -/
private noncomputable def stageFieldFunctor : Finset BigIndex.{u} ⥤ CommRingCat.{u} where
  obj T := CommRingCat.of (StageField T)
  map h := CommRingCat.ofHom (stageFieldMap (leOfHom h))
  map_id T := by simp [stageFieldMap_id T]
  map_comp h h' := by
    simp only [← stageFieldMap_comp (leOfHom h) (leOfHom h')]
    rfl

/-- Adjoining one variable, as an endofunctor of commutative rings. -/
private noncomputable def polynomialFunctor : CommRingCat.{u} ⥤ CommRingCat.{u} where
  obj R := CommRingCat.of (Polynomial R)
  map f := CommRingCat.ofHom (Polynomial.mapRingHom f.hom)
  map_id R := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun p => ?_
    simp
  map_comp f g := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun p => ?_
    simp

/-- The structure maps of the affine lines over the stages, i.e. the inclusions of constants. -/
private noncomputable def stageStructure :
    (stageFieldFunctor.{u}) ⟶ stageFieldFunctor.{u} ⋙ polynomialFunctor.{u} where
  app T := CommRingCat.ofHom (Polynomial.C (R := StageField T))
  naturality := by
    intro T T' h
    apply CommRingCat.hom_ext
    refine RingHom.ext fun x => ?_
    change Polynomial.C (stageFieldMap (leOfHom h) x) =
      Polynomial.mapRingHom (stageFieldMap (leOfHom h)) (Polynomial.C x)
    exact (Polynomial.map_C _).symm

/-- The inverse system of the spectra of the stage fields. -/
private noncomputable def baseSystem : (Finset BigIndex.{u})ᵒᵖ ⥤ Scheme.{u} :=
  stageFieldFunctor.op ⋙ Scheme.Spec

/-- The inverse system of the affine lines over the stage fields. -/
private noncomputable def sourceSystem : (Finset BigIndex.{u})ᵒᵖ ⥤ Scheme.{u} :=
  (stageFieldFunctor ⋙ polynomialFunctor).op ⋙ Scheme.Spec

/-- The morphism of inverse systems: at each stage the affine line over the stage field. -/
private noncomputable def systemMap : sourceSystem.{u} ⟶ baseSystem.{u} :=
  Functor.whiskerRight (NatTrans.op stageStructure) Scheme.Spec

/-- The variable `x_a` of the `T`-th stage field attached to a member `a` of `T`. -/
private noncomputable def stageGen {T : Finset BigIndex.{u}} {a : BigIndex.{u}} (ha : a ∈ T) :
    StageField T :=
  algebraMap (StagePoly T) (StageField T) (MvPolynomial.X (stageVar ha))

private lemma stageFieldMap_gen {T T' : Finset BigIndex.{u}} (h : T ≤ T') {a : BigIndex.{u}}
    (ha : a ∈ T) :
    stageFieldMap h (stageGen ha) = stageGen (h ha) := by
  rw [stageGen, stageFieldMap_algebraMap]
  simp only [stageGen, stagePolyMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    MvPolynomial.rename_X, stageVarMap_varOf]

private lemma stageGen_injective {T : Finset BigIndex.{u}} {a b : BigIndex.{u}}
    (ha : a ∈ T) (hb : b ∈ T) (hab : stageGen ha = stageGen hb) : a = b := by
  have h1 : (MvPolynomial.X (stageVar ha) : StagePoly T) = MvPolynomial.X (stageVar hb) :=
    IsFractionRing.injective (StagePoly T) (StageField T) hab
  have h2 : stageVar ha = stageVar hb := MvPolynomial.X_injective h1
  have h3 : (⟨a, ha⟩ : (↑T : Type (u+1))) = ⟨b, hb⟩ :=
    (equivShrink (↑T : Type (u+1))).injective h2
  exact congrArg (fun z : (↑T : Type (u+1)) => (z : BigIndex.{u})) h3

/-- A compatible family of morphisms into the spectra of the stage fields forces the source to
be empty: the images of the variables would give an injection of `Cardinal.{u}` into a
`Type u`. -/
private lemma isEmpty_of_compatible_family (W : Scheme.{u})
    (π : ∀ T : Finset BigIndex.{u}, W ⟶ Spec (CommRingCat.of (StageField T)))
    (hπ : ∀ {T T' : Finset BigIndex.{u}} (h : T ≤ T'),
      π T = π T' ≫ Spec.map (CommRingCat.ofHom (stageFieldMap h))) : IsEmpty W := by
  by_contra hne
  rw [not_isEmpty_iff] at hne
  have : Nonempty (⊤ : W.Opens) := ⟨⟨hne.some, trivial⟩⟩
  have : Nontrivial Γ(W, ⊤) := Scheme.component_nontrivial W ⊤
  let ψ : ∀ T : Finset BigIndex.{u}, CommRingCat.of (StageField T) ⟶ Γ(W, ⊤) := fun T =>
    (Scheme.ΓSpecIso (CommRingCat.of (StageField T))).inv ≫ (π T).appTop
  have hψ : ∀ {T T' : Finset BigIndex.{u}} (h : T ≤ T'),
      ψ T = CommRingCat.ofHom (stageFieldMap h) ≫ ψ T' := by
    intro T T' h
    dsimp only [ψ]
    rw [hπ h, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
      Category.assoc]
  have hψinj : ∀ T : Finset BigIndex.{u}, Function.Injective (ψ T).hom :=
    fun T => RingHom.injective _
  let e : BigIndex.{u} → Γ(W, ⊤) := fun a => (ψ {a}).hom (stageGen (Finset.mem_singleton_self a))
  have he : ∀ (T : Finset BigIndex.{u}) (a : BigIndex.{u}) (ha : a ∈ T),
      e a = (ψ T).hom (stageGen ha) := by
    intro T a ha
    have hsub : ({a} : Finset BigIndex.{u}) ≤ T := Finset.singleton_subset_iff.mpr ha
    dsimp only [e]
    rw [hψ hsub]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom]
    rw [stageFieldMap_gen hsub (Finset.mem_singleton_self a)]
  have hinj : Function.Injective e := by
    classical
    intro a b hab
    have ha : a ∈ ({a, b} : Finset BigIndex.{u}) := by simp
    have hb : b ∈ ({a, b} : Finset BigIndex.{u}) := by simp
    rw [he _ a ha, he _ b hb] at hab
    exact stageGen_injective ha hb (hψinj _ hab)
  exact not_small_cardinal.{u, u} (small_of_injective hinj)

/-- Every cone over the system of stage fields has empty vertex, so the empty scheme is its
limit in `Scheme.{u}`. -/
private lemma isEmpty_of_cone_baseSystem (c : Cone baseSystem.{u}) : IsEmpty c.pt :=
  isEmpty_of_compatible_family c.pt (fun T => c.π.app (Opposite.op T))
    (fun {_ _} h => (c.w ((homOfLE h).op)).symm)

/-- The cone with empty vertex over the system of stage fields. -/
private noncomputable def baseCone : Cone baseSystem.{u} where
  pt := ∅
  π :=
    { app := fun _ => IsInitial.to emptyIsInitial _
      naturality := fun _ _ _ => IsInitial.hom_ext emptyIsInitial _ _ }

/-- The empty scheme is the limit of the system of stage fields. -/
private noncomputable def isLimitBaseCone : IsLimit baseCone.{u} where
  lift s := by
    letI := isEmpty_of_cone_baseSystem s
    exact IsInitial.to isInitialOfIsEmpty _
  fac s j := by
    let _ : IsEmpty s.pt := isEmpty_of_cone_baseSystem s
    exact IsInitial.hom_ext isInitialOfIsEmpty _ _
  uniq s m _ := by
    let _ : IsEmpty s.pt := isEmpty_of_cone_baseSystem s
    exact IsInitial.hom_ext isInitialOfIsEmpty _ _

/-- The cone with empty vertex over the system of affine lines. -/
private noncomputable def sourceCone : Cone sourceSystem.{u} where
  pt := ∅
  π :=
    { app := fun _ => IsInitial.to emptyIsInitial _
      naturality := fun _ _ _ => IsInitial.hom_ext emptyIsInitial _ _ }

/-- The empty scheme is the limit of the system of affine lines. -/
private noncomputable def isLimitSourceCone : IsLimit sourceCone.{u} where
  lift s := by
    letI : IsEmpty s.pt := isEmpty_of_cone_baseSystem ((Cone.postcompose systemMap).obj s)
    exact IsInitial.to isInitialOfIsEmpty _
  fac s j := by
    let _ : IsEmpty s.pt := isEmpty_of_cone_baseSystem ((Cone.postcompose systemMap).obj s)
    exact IsInitial.hom_ext isInitialOfIsEmpty _ _
  uniq s m _ := by
    let _ : IsEmpty s.pt := isEmpty_of_cone_baseSystem ((Cone.postcompose systemMap).obj s)
    exact IsInitial.hom_ext isInitialOfIsEmpty _ _

/-- Adjoining a variable is a pushout square of commutative rings:
`B[X] = A[X] ⊗[A] B` for any ring map `A → B`. -/
private lemma isPushout_polynomial {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B) :
    IsPushout (CommRingCat.ofHom (Polynomial.C (R := A))) (CommRingCat.ofHom ρ)
      (CommRingCat.ofHom (Polynomial.mapRingHom ρ))
      (CommRingCat.ofHom (Polynomial.C (R := B))) := by
  have hcomm : CommRingCat.ofHom (Polynomial.C (R := A)) ≫
      CommRingCat.ofHom (Polynomial.mapRingHom ρ) =
      CommRingCat.ofHom ρ ≫ CommRingCat.ofHom (Polynomial.C (R := B)) := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun a => ?_
    show Polynomial.map ρ (Polynomial.C a) = Polynomial.C (ρ a)
    rw [Polynomial.map_C]
  refine IsPushout.of_isColimit' ⟨hcomm⟩ (PushoutCocone.IsColimit.mk hcomm
    (fun s => CommRingCat.ofHom (Polynomial.eval₂RingHom s.inr.hom (s.inl.hom Polynomial.X)))
    ?_ ?_ ?_)
  · intro s
    set β : B →+* s.pt := s.inr.hom with hβ
    set α : Polynomial A →+* s.pt := s.inl.hom with hα
    have hc : ∀ a : A, α (Polynomial.C a) = β (ρ a) := fun a =>
      congrArg (fun q : CommRingCat.of A ⟶ s.pt => q.hom a) s.condition
    apply CommRingCat.hom_ext
    show (Polynomial.eval₂RingHom β (α Polynomial.X)).comp (Polynomial.mapRingHom ρ) = α
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · show Polynomial.eval₂ β (α Polynomial.X) (Polynomial.map ρ (Polynomial.C a)) =
        α (Polynomial.C a)
      rw [Polynomial.map_C, Polynomial.eval₂_C, hc a]
    · show Polynomial.eval₂ β (α Polynomial.X) (Polynomial.map ρ Polynomial.X) =
        α Polynomial.X
      rw [Polynomial.map_X, Polynomial.eval₂_X]
  · intro s
    set β : B →+* s.pt := s.inr.hom with hβ
    set α : Polynomial A →+* s.pt := s.inl.hom with hα
    apply CommRingCat.hom_ext
    show (Polynomial.eval₂RingHom β (α Polynomial.X)).comp (Polynomial.C (R := B)) = β
    refine RingHom.ext fun a => ?_
    show Polynomial.eval₂ β (α Polynomial.X) (Polynomial.C a) = β a
    rw [Polynomial.eval₂_C]
  · intro s m hl hr
    set β : B →+* s.pt := s.inr.hom with hβ
    set α : Polynomial A →+* s.pt := s.inl.hom with hα
    set μ : Polynomial B →+* s.pt := m.hom with hμ
    have hrr : ∀ b : B, μ (Polynomial.C b) = β b := fun b =>
      congrArg (fun q : CommRingCat.of B ⟶ s.pt => q.hom b) hr
    have hll : μ (Polynomial.map ρ Polynomial.X) = α Polynomial.X :=
      congrArg (fun q : CommRingCat.of (Polynomial A) ⟶ s.pt => q.hom Polynomial.X) hl
    apply CommRingCat.hom_ext
    show μ = Polynomial.eval₂RingHom β (α Polynomial.X)
    refine Polynomial.ringHom_ext (fun b => ?_) ?_
    · show μ (Polynomial.C b) = Polynomial.eval₂ β (α Polynomial.X) (Polynomial.C b)
      rw [Polynomial.eval₂_C, hrr b]
    · show μ Polynomial.X = Polynomial.eval₂ β (α Polynomial.X) Polynomial.X
      rw [Polynomial.eval₂_X, ← hll, Polynomial.map_X]

/-- Adjoining a variable commutes with the transitions of the system. -/
private lemma isPushout_stageStructure {T T' : Finset BigIndex.{u}} (h : T ≤ T') :
    IsPushout (stageStructure.app T) (stageFieldFunctor.map (homOfLE h))
      ((stageFieldFunctor ⋙ polynomialFunctor).map (homOfLE h)) (stageStructure.app T') :=
  isPushout_polynomial (stageFieldMap h)

private instance isAffine_baseSystem_obj (i : (Finset BigIndex.{u})ᵒᵖ) :
    IsAffine (baseSystem.obj i) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (StageField i.unop))))

private instance isAffine_sourceSystem_obj (i : (Finset BigIndex.{u})ᵒᵖ) :
    IsAffine (sourceSystem.obj i) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (Polynomial (StageField i.unop)))))

private instance compactSpace_baseSystem_obj (i : (Finset BigIndex.{u})ᵒᵖ) :
    CompactSpace (baseSystem.obj i) :=
  inferInstanceAs (CompactSpace ↥(Spec (CommRingCat.of (StageField i.unop))))

private instance quasiSeparatedSpace_baseSystem_obj (i : (Finset BigIndex.{u})ᵒᵖ) :
    QuasiSeparatedSpace (baseSystem.obj i) :=
  inferInstanceAs (QuasiSeparatedSpace ↥(Spec (CommRingCat.of (StageField i.unop))))

private instance subsingleton_baseSystem_obj (i : (Finset BigIndex.{u})ᵒᵖ) :
    Subsingleton (baseSystem.obj i) :=
  inferInstanceAs (Subsingleton ↥(Spec (CommRingCat.of (StageField i.unop))))

private instance nonempty_baseSystem_obj (i : (Finset BigIndex.{u})ᵒᵖ) :
    Nonempty (baseSystem.obj i) :=
  inferInstanceAs (Nonempty ↥(Spec (CommRingCat.of (StageField i.unop))))

private instance locallyOfFiniteType_systemMap_app (i : (Finset BigIndex.{u})ᵒᵖ) :
    LocallyOfFiniteType (systemMap.app i) := by
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Polynomial.C (R := StageField i.unop))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  change RingHom.FiniteType (Polynomial.C (R := StageField i.unop))
  rw [show (Polynomial.C (R := StageField i.unop)) =
      algebraMap (StageField i.unop) (Polynomial (StageField i.unop)) from rfl,
    RingHom.finiteType_algebraMap]
  infer_instance

private instance quasiCompact_systemMap_app (i : (Finset BigIndex.{u})ᵒᵖ) :
    QuasiCompact (systemMap.app i) := by
  change QuasiCompact (Spec.map (CommRingCat.ofHom (Polynomial.C (R := StageField i.unop))))
  infer_instance

/-- The transitions of the system of affine lines are cartesian over the base system. -/
private lemma isPullback_systemMap {i j : (Finset BigIndex.{u})ᵒᵖ} (g : i ⟶ j) :
    IsPullback (sourceSystem.map g) (systemMap.app i) (systemMap.app j) (baseSystem.map g) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_stageStructure (leOfHom g.unop))

private instance isClosedImmersion_lift_systemMap {i j : (Finset BigIndex.{u})ᵒᵖ} (g : i ⟶ j) :
    IsClosedImmersion
      (pullback.lift (sourceSystem.map g) (systemMap.app i) (systemMap.naturality g)) := by
  have hp := isPullback_systemMap g
  have hlift : pullback.lift (sourceSystem.map g) (systemMap.app i) (systemMap.naturality g) =
      hp.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, IsPullback.isoPullback_hom_fst]
    · rw [pullback.lift_snd, IsPullback.isoPullback_hom_snd]
  rw [hlift]
  infer_instance

/-- If the target of a morphism is a single point, each fibre is the whole source. -/
private lemma topologicalKrullDim_fiber_of_subsingleton {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Subsingleton Y] (y : Y) :
    topologicalKrullDim (f.fiber y) = topologicalKrullDim X := by
  obtain ⟨e, -⟩ := exists_homeomorph_fiber_of_subsingleton f y
  exact IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph

/-- Every stage fibre is an affine line over a field, hence one-dimensional. -/
private lemma topologicalKrullDim_fiber_fMor (i : (Finset BigIndex.{u})ᵒᵖ) (s : baseSystem.obj i) :
    topologicalKrullDim ((systemMap.app i).fiber s) = 1 := by
  rw [topologicalKrullDim_fiber_of_subsingleton]
  have h1 : topologicalKrullDim ↥(Spec (CommRingCat.of (Polynomial (StageField i.unop)))) =
      ringKrullDim (Polynomial (StageField i.unop)) :=
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
  show topologicalKrullDim ↥(Spec (CommRingCat.of (Polynomial (StageField i.unop)))) = 1
  rw [h1, Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  rfl

/-- **The universally quantified form of Tag 05M5 is false when the index universes are
unrestricted.** -/
public theorem not_exists_forall_topologicalKrullDim_fiber_le_of_isLimit :
    ¬ ∀ {I : Type (u + 1)} [Category.{u + 1} I] [IsCofiltered I]
      (X S : I ⥤ Scheme.{u}) (f : X ⟶ S)
      [∀ {i j : I} (g : i ⟶ j), IsAffineHom (S.map g)]
      [∀ i : I, CompactSpace (S.obj i)] [∀ i : I, QuasiSeparatedSpace (S.obj i)]
      [∀ i : I, LocallyOfFiniteType (f.app i)] [∀ i : I, QuasiCompact (f.app i)]
      [∀ {i j : I} (g : i ⟶ j),
        IsClosedImmersion (pullback.lift (X.map g) (f.app i) (f.naturality g))]
      (cX : Cone X) (_ : IsLimit cX) (cS : Cone S) (hcS : IsLimit cS) (d : ℕ),
      (∀ s : cS.pt, topologicalKrullDim
          ((hcS.lift ((Cone.postcompose f).obj cX)).fiber s) ≤ (d : WithBot ℕ∞)) →
      ∃ i : I, ∀ s : S.obj i,
        topologicalKrullDim ((f.app i).fiber s) ≤ (d : WithBot ℕ∞) := by
  intro H
  obtain ⟨i, hi⟩ := H sourceSystem baseSystem systemMap sourceCone isLimitSourceCone
    baseCone isLimitBaseCone 0
    (fun s => ((isEmpty_of_cone_baseSystem baseCone).elim s))
  obtain ⟨s⟩ := nonempty_baseSystem_obj i
  have h1 := hi s
  rw [topologicalKrullDim_fiber_fMor i s] at h1
  norm_num at h1

end AlgebraicGeometry
