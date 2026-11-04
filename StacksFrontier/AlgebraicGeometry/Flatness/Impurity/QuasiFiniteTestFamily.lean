module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismAssociatedPoints.BaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.Impurity.FinitePresentationBase
public import StacksFrontier.AlgebraicGeometry.Flatness.Impurity.QuasiFiniteNeighborhood
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteTypePullbackScheme
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ClosedPointsFibre.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeAssassin.GenericFibrePoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Surjective
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.IrreducibleComponentsBaseChange
public import StacksFrontier.Topology.Sober.LocallyClosed

/-!
# An impurity over a locally Noetherian base occurs over a quasi-finite test family

Over a locally Noetherian base every impurity of a finite type quasi-coherent module along a
fibre is witnessed by a test family which is quasi-finite over the base at the specialized
point.

## Main results

* `AlgebraicGeometry.exists_isImpurity_quasiFiniteAt`: over a locally Noetherian base, an impurity
  can be witnessed by an impurity whose test family is quasi-finite over the base at its
  specialized point.
* `AlgebraicGeometry.ImpurityDiagram.apply_ne_of_isImpurity`: the generalization of an impurity
  does not lie over the chosen point of the base.

## References

* [Stacks Project, Tag 05J1](https://stacks.math.columbia.edu/tag/05J1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- A morphism from a reduced scheme whose image lies in a closed subset factors through the
reduced induced closed subscheme on that subset. -/
@[ega "I 5.5.4" "partial", sga "3 VIB 7.1" "partial"]
private theorem exists_lift_vanishingIdeal {X Y : Scheme.{u}} [IsReduced Y] (Z : Closeds X)
    (f : Y ⟶ X) (hf : Set.range f.base ⊆ (Z : Set X)) :
    ∃ g : Y ⟶ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme,
      g ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = f := by
  have hker : Scheme.IdealSheafData.vanishingIdeal Z ≤ f.ker := by
    rw [f.ker_eq_vanishingIdeal_closure_range]
    exact Scheme.IdealSheafData.vanishingIdeal_antimono (Closeds.closure_le.mpr hf)
  exact ⟨IsClosedImmersion.lift _ f (by rwa [Scheme.IdealSheafData.ker_subschemeι]),
    IsClosedImmersion.lift_fac _ _ _⟩

/-- Equal morphisms of schemes have equal values at every point. -/
private theorem hom_congr_apply {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (x : X) :
    f x = g x := by rw [h]

/-- A point of the reduced induced closed subscheme on the closure of a point maps into that
closure. -/
private theorem subschemeι_mem_closure {X : Scheme.{u}} (x : X)
    (z : (Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({x} : Set X), isClosed_closure⟩ : Closeds X)).subscheme) :
    (Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({x} : Set X), isClosed_closure⟩ : Closeds X)).subschemeι z ∈
        closure ({x} : Set X) := by
  have h := Scheme.IdealSheafData.range_subschemeι_vanishingIdeal
    (⟨closure ({x} : Set X), isClosed_closure⟩ : Closeds X)
  exact h.subset ⟨z, rfl⟩

/-- The reduced induced closed subscheme on the closure of a point is irreducible. -/
private theorem irreducibleSpace_subscheme_closure {X : Scheme.{u}} (x : X) :
    IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({x} : Set X), isClosed_closure⟩ : Closeds X)).subscheme :=
  Scheme.IdealSheafData.irreducibleSpace_subscheme X _ (by
    rw [Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]
    exact isIrreducible_singleton.closure)

/-- A nonempty locally closed subset of a quasi-sober space has a generic point of an
irreducible component. -/
private theorem nonempty_genericPoints_of_isLocallyClosed {Y : Type*} [TopologicalSpace Y]
    [QuasiSober Y] {A : Set Y} (hA : IsLocallyClosed A) (hne : A.Nonempty) :
    Nonempty (genericPoints A) := by
  obtain ⟨a, ha⟩ := hne
  have : QuasiSober A := hA.quasiSober
  exact ⟨genericPoints.ofComponent ⟨irreducibleComponent (⟨a, ha⟩ : A),
    irreducibleComponent_mem_irreducibleComponents _⟩⟩

/-- A generic point of an irreducible component is a generalization of every point it is a
specialization of. -/
private theorem specializes_of_isGenericPoint_component {Y : Type*} [TopologicalSpace Y]
    {p q : Y} {C : Set Y} (hC : C ∈ irreducibleComponents Y) (hp : IsGenericPoint p C)
    (hqp : q ⤳ p) : p ⤳ q := by
  have hsub : C ⊆ closure ({q} : Set Y) := by
    rw [← hp.def]
    exact specializes_iff_closure_subset.mp hqp
  exact hp.specializes (hC.2 isIrreducible_singleton.closure hsub (subset_closure rfl))

/-- The canonical morphism from the spectrum of the tensor product of residue fields attached to
a point of a fibre product is a preimmersion. -/
private theorem isPreimmersion_specTensorTo {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (T : Scheme.Pullback.Triplet f g) : IsPreimmersion T.SpecTensorTo := by
  let a := X.fromSpecResidueField T.x
  let b := Y.fromSpecResidueField T.y
  let i := S.fromSpecResidueField T.s
  let u := Spec.map ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
  let v := Spec.map ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)
  have hu : u ≫ i = a ≫ f := by
    dsimp [u, i, a]
    rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField T.hx.symm]
    exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f T.x
  have hv : v ≫ i = b ≫ g := by
    dsimp [v, i, b]
    rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField T.hy.symm]
    exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g T.y
  have hD := T.isPullback_SpecMap_tensor
  have hS : IsPullback (Spec.map T.tensorInl) (Spec.map T.tensorInr) (a ≫ f) (b ≫ g) := by
    rw [← hu, ← hv]
    exact IsPullback.of_isLimit <|
      PullbackCone.isLimitOfCompMono u v i
        (PullbackCone.mk (Spec.map T.tensorInl) (Spec.map T.tensorInr) hD.w) hD.isLimit
  let e := hS.isoPullback
  let m := pullback.map (a ≫ f) (b ≫ g) f g a b (𝟙 _) (by simp) (by simp)
  have hm : IsPreimmersion m := by
    have : MorphismProperty.IsStableUnderBaseChange @IsPreimmersion := inferInstance
    have : MorphismProperty.IsStableUnderComposition @IsPreimmersion :=
      ⟨fun f g hf hg => IsPreimmersion.comp f g⟩
    exact MorphismProperty.pullbackMap (P := @IsPreimmersion)
      (inferInstance : IsPreimmersion a) (inferInstance : IsPreimmersion b) rfl rfl
  have hefst : e.hom ≫ pullback.fst (a ≫ f) (b ≫ g) = Spec.map T.tensorInl := by
    simp [e]
  have hesnd : e.hom ≫ pullback.snd (a ≫ f) (b ≫ g) = Spec.map T.tensorInr := by
    simp [e]
  have hcomp : e.hom ≫ m = T.SpecTensorTo := by
    apply pullback.hom_ext
    · simp only [m, pullback.map]
      rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hefst]
      simp [a, T.specTensorTo_fst]
    · simp only [m, pullback.map]
      rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hesnd]
      simp [b, T.specTensorTo_snd]
  rw [← hcomp]
  infer_instance

/-- Let `Z` be a scheme over a field `k` and let `K/k` be an extension of fields. A point of
`Z ×_k K` which is minimal among the points with its image in `Z` admits, for every
specialization of that image, a specialization lying over it. -/
private theorem exists_specializes_of_baseChange_field (k K : Type u) [Field k] [Field K]
    [Algebra k K] {Z : Scheme.{u}} (q : Z ⟶ Spec (.of k)) (α : Spec (.of K) ⟶ Spec (.of k))
    (hα : α = Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (p : ↑(pullback (C := Scheme.{u}) q α)) (y : Z)
    (hpy : pullback.fst q α p ⤳ y)
    (hmin : ∀ r : ↑(pullback (C := Scheme.{u}) q α), r ⤳ p →
      pullback.fst q α r = pullback.fst q α p → p ⤳ r) :
    ∃ r : ↑(pullback (C := Scheme.{u}) q α), p ⤳ r ∧ pullback.fst q α r = y := by
  classical
  subst hα
  let α := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let π := pullback.fst q α
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure ({π p} : Set Z), isClosed_closure⟩ : Closeds Z)
  let j := I.subschemeι
  have hj : Set.range j = closure ({π p} : Set Z) :=
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal _
  let qc := j ≫ q
  let πc := pullback.fst qc α
  let m : pullback qc α ⟶ pullback q α :=
    pullback.map qc α q α j (𝟙 _) (𝟙 _) (by simp [qc]) (by simp)
  have hm : m ≫ π = πc ≫ j := by
    simp only [m, π, πc, pullback.map, pullback.lift_fst]
  obtain ⟨pc, hpc⟩ : p ∈ Set.range m := by
    rw [Scheme.Pullback.range_map]
    refine ⟨?_, ⟨_, rfl⟩⟩
    rw [hj]
    exact subset_closure rfl
  let comp : irreducibleComponents ↑(pullback (C := Scheme.{u}) qc α) :=
    ⟨irreducibleComponent pc, irreducibleComponent_mem_irreducibleComponents pc⟩
  let r := genericPoints.ofComponent comp
  have hr : IsGenericPoint r.1 (comp : Set ↑(pullback (C := Scheme.{u}) qc α)) :=
    genericPoints.isGenericPoint_ofComponent comp
  have : IrreducibleSpace I.subscheme := irreducibleSpace_subscheme_closure (π p)
  have hcomp : πc '' (comp : Set ↑(pullback (C := Scheme.{u}) qc α)) = Set.univ := by
    simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using
      mapsTo_irreducibleComponents_baseChange k K I.subscheme qc comp.2
  have hmr : m r.1 ⤳ p := by
    rw [← hpc]
    exact (hr.specializes mem_irreducibleComponent).map m.continuous
  have hrbase : π (m r.1) = π p := by
    refine ((hmr.map π.continuous).antisymm (specializes_iff_mem_closure.mpr ?_)).eq
    rw [← hj]
    exact ⟨πc r.1, (hom_congr_apply hm r.1).symm⟩
  obtain ⟨yc, hyc⟩ : y ∈ Set.range j := by
    rw [hj]
    exact hpy.mem_closure
  obtain ⟨rc, hrc, hrcy⟩ : yc ∈ πc '' (comp : Set ↑(pullback (C := Scheme.{u}) qc α)) := by
    rw [hcomp]
    trivial
  refine ⟨m rc, (hmin (m r.1) hmr hrbase).trans ((hr.specializes hrc).map m.continuous), ?_⟩
  calc
    π (m rc) = j (πc rc) := hom_congr_apply hm rc
    _ = y := by rw [hrcy, hyc]

/-- A point of a fibre product whose point in the spectrum of the tensor product of residue
fields is generic in an irreducible component is minimal among the points with its two
images. -/
private theorem specializes_of_specializes_of_isGenericPoint_tensor {X Y S : Scheme.{u}}
    {f : X ⟶ S} {g : Y ⟶ S} (p q : ↑(pullback (C := Scheme.{u}) f g))
    (hp : ∃ C ∈ irreducibleComponents (Spec (Scheme.Pullback.Triplet.ofPoint p).tensor),
      IsGenericPoint (Scheme.Pullback.SpecOfPoint p) C)
    (hqp : q ⤳ p) (hx : pullback.fst f g q = pullback.fst f g p)
    (hy : pullback.snd f g q = pullback.snd f g p) : p ⤳ q := by
  let T := Scheme.Pullback.Triplet.ofPoint p
  have hT : Scheme.Pullback.Triplet.ofPoint q = T := Scheme.Pullback.Triplet.ext hx hy
  obtain ⟨w, hw⟩ : q ∈ Set.range T.SpecTensorTo := by
    rw [← hT]
    exact ⟨Scheme.Pullback.SpecOfPoint q, Scheme.Pullback.SpecTensorTo_SpecOfPoint q⟩
  obtain ⟨C, hC, hpC⟩ := hp
  have : IsPreimmersion T.SpecTensorTo := isPreimmersion_specTensorTo T
  have hspec : w ⤳ Scheme.Pullback.SpecOfPoint p := by
    apply T.SpecTensorTo.isEmbedding.isInducing.specializes_iff.mp
    simpa only [hw, T, Scheme.Pullback.SpecTensorTo_SpecOfPoint] using hqp
  simpa only [T, Scheme.Pullback.SpecTensorTo_SpecOfPoint, hw] using
    (specializes_of_isGenericPoint_component hC hpC hspec).map T.SpecTensorTo.continuous

/-- A point of a fibre product whose point in the spectrum of the tensor product of residue
fields is generic in an irreducible component specializes to a point lying over any
specialization of its second coordinate inside the fibre of its first coordinate. -/
private theorem exists_specializes_of_isGenericPoint_tensor {X Y S : Scheme.{u}}
    {f : X ⟶ S} {g : Y ⟶ S} (p : ↑(pullback (C := Scheme.{u}) f g))
    (hp : ∃ C ∈ irreducibleComponents (Spec (Scheme.Pullback.Triplet.ofPoint p).tensor),
      IsGenericPoint (Scheme.Pullback.SpecOfPoint p) C)
    (y : Y) (hpy : pullback.snd f g p ⤳ y) (hgy : g y = f (pullback.fst f g p)) :
    ∃ q : ↑(pullback (C := Scheme.{u}) f g), p ⤳ q ∧ pullback.snd f g q = y := by
  classical
  let x := pullback.fst f g p
  let s := f x
  let : Algebra ↥(S.residueField s) ↥(X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  let α := Spec.map (CommRingCat.ofHom (algebraMap ↥(S.residueField s) ↥(X.residueField x)))
  let b := g.fiberToSpecResidueField s
  let j := X.fromSpecResidueField x
  have ha : α ≫ S.fromSpecResidueField s = j ≫ f :=
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f x
  let π := pullback.fst b α
  let ρ := pullback.snd b α
  have hfib : IsPullback (g.fiberι s) b g (S.fromSpecResidueField s) :=
    IsPullback.of_hasPullback _ _
  have hsq : IsPullback (π ≫ g.fiberι s) ρ g (j ≫ f) :=
    ha ▸ (IsPullback.of_hasPullback b α).paste_horiz hfib
  let m : pullback b α ⟶ pullback f g :=
    pullback.lift (ρ ≫ j) (π ≫ g.fiberι s) ((Category.assoc _ _ _).trans hsq.w.symm)
  have hmfst : m ≫ pullback.fst f g = ρ ≫ j := pullback.lift_fst _ _ _
  have hmsnd : m ≫ pullback.snd f g = π ≫ g.fiberι s := pullback.lift_snd _ _ _
  have hfst (r) : pullback.fst f g (m r) = j (ρ r) :=
    hom_congr_apply hmfst r
  have hsnd (r) : pullback.snd f g (m r) = g.fiberι s (π r) :=
    hom_congr_apply hmsnd r
  have hL : IsPullback m ρ (pullback.fst f g) j := by
    refine IsPullback.of_right (h₁₂ := pullback.snd f g) ?_ hmfst
      (IsPullback.of_hasPullback f g).flip
    rwa [hmsnd]
  have : IsPreimmersion m := MorphismProperty.of_isPullback hL.flip inferInstance
  obtain ⟨o, ho⟩ : pullback.fst f g p ∈ Set.range j := by
    rw [Scheme.range_fromSpecResidueField]
    rfl
  obtain ⟨w, hmw, -⟩ := Scheme.exists_preimage_of_isPullback hL p o ho.symm
  have hmwsnd : pullback.snd f g p = g.fiberι s (π w) := by rw [← hmw, hsnd]
  let y' : g.fiber s := (g.fiberHomeo s).symm ⟨y, hgy⟩
  have hy' : g.fiberι s y' = y := g.fiberι_fiberHomeo_symm s _
  have hπ : π w ⤳ y' :=
    (g.fiberι s).isEmbedding.isInducing.specializes_iff.mp (by rwa [hy', ← hmwsnd])
  obtain ⟨w', hww', hw'y⟩ := exists_specializes_of_baseChange_field
      ↥(S.residueField s) ↥(X.residueField x) b α rfl w y' hπ (by
    intro r hr hπr
    apply m.isEmbedding.isInducing.specializes_iff.mp
    rw [hmw]
    refine specializes_of_specializes_of_isGenericPoint_tensor p (m r) hp
      (by simpa only [hmw] using hr.map m.continuous) ?_ ?_
    · rw [hfst]
      exact Scheme.fromSpecResidueField_apply x _
    · rw [hsnd, hπr, ← hmwsnd])
  refine ⟨m w', by simpa only [hmw] using hww'.map m.continuous, ?_⟩
  rw [hsnd, hw'y, hy']

/-- A specialization of the point of an impurity does not lie in the fibre over the chosen point
of the test family. -/
private theorem false_of_specializes_of_isImpurity {P : PrePureSituation.{u}}
    {D : ImpurityDiagram P} (hD : IsImpurity P D) {y : D.X_T} (hxy : D.xi ⤳ y)
    (hy : D.toT y = D.t) : False :=
  Set.eq_empty_iff_forall_notMem.mp hD.2 y
    ⟨hxy.mem_closure, by rw [D.toT.range_fiberι]; exact hy⟩

/-- The generalization of an impurity does not lie over the chosen point of the base. -/
theorem ImpurityDiagram.apply_ne_of_isImpurity (P : PrePureSituation.{u}) (D : ImpurityDiagram P)
    (hD : IsImpurity P D) : D.g.base D.t' ≠ P.s := by
  intro heq
  let e := D.isPullback.isoPullback
  let F' := (Scheme.Modules.pullback (pullback.fst P.f D.g)).obj P.F
  have : LocallyOfFiniteType D.toT := MorphismProperty.of_isPullback D.isPullback inferInstance
  have : LocallyOfFiniteType (pullback.snd P.f D.g) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback P.f D.g) inferInstance
  let ei : D.pulledBack P ≅ (Scheme.Modules.pullback e.hom).obj F' :=
    (Scheme.Modules.pullbackCongr D.isPullback.isoPullback_hom_fst.symm).app P.F ≪≫
      (Scheme.Modules.pullbackComp e.hom (pullback.fst P.f D.g)).symm.app P.F
  have h1 : D.xi ∈ Stacks.Divisors.relativeAssassin (e.hom ≫ pullback.snd P.f D.g)
      ((Scheme.Modules.pullback e.hom).obj F') := by
    rw [D.isPullback.isoPullback_hom_snd, ← relativeAssassin_eq_of_moduleIso D.toT ei]
    exact hD.1
  have hcan := mem_relativeAssassin_map_of_isIso e.hom (pullback.snd P.f D.g) F' h1
  have hgen := ((mem_relativeAssassin_pullback_iff P.f D.g P.F (e.hom D.xi)).mp hcan).2
  have hsnd : pullback.snd P.f D.g (e.hom D.xi) = D.t' := by
    rw [← Scheme.Hom.comp_apply, D.isPullback.isoPullback_hom_snd]
    exact D.xi_liesOver
  have hbase : D.g.base D.t = P.f (pullback.fst P.f D.g (e.hom D.xi)) := by
    rw [D.mapsToChosenPoint, ← heq, ← hsnd]
    exact (hom_congr_apply pullback.condition (e.hom D.xi)).symm
  obtain ⟨q, hq, hqt⟩ := exists_specializes_of_isGenericPoint_tensor (e.hom D.xi) hgen D.t
    (by simpa only [hsnd] using D.specializes) hbase
  have hq' : D.xi ⤳ e.inv q := by simpa using hq.map e.inv.continuous
  have htoT : D.toT (e.inv q) = D.t := by
    have hi : e.inv ≫ D.toT = pullback.snd P.f D.g := by
      rw [← D.isPullback.isoPullback_hom_snd]
      simp [e]
    change (e.inv ≫ D.toT) q = D.t
    rwa [hi]
  exact false_of_specializes_of_isImpurity hD hq' htoT

/-- **Stacks Project, Tag 05J1.** Over a locally Noetherian base, an impurity of the module of a
pre-pure situation above the chosen point of the base can be witnessed by an impurity whose test
family is quasi-finite over the base at its specialized point. -/
@[stacks 05J1]
theorem exists_isImpurity_quasiFiniteAt (P : PrePureSituation.{u}) [IsLocallyNoetherian P.S]
    (h : ∃ D : ImpurityDiagram P, IsImpurity P D) :
    ∃ D : ImpurityDiagram P, IsImpurity P D ∧ quasiFiniteAt D.g D.t := by
  classical
  obtain ⟨D, hD, hfp, t_fib, ht_fib, ht_closed⟩ :=
    exists_impurity_locallyOfFinitePresentation_closedPoint P h
  have : LocallyOfFinitePresentation D.g := hfp
  have : LocallyOfFiniteType D.g := inferInstance
  have : LocallyOfFiniteType D.toT := MorphismProperty.of_isPullback D.isPullback inferInstance
  have : QuasiCompact D.toT := MorphismProperty.of_isPullback D.isPullback inferInstance
  let F := D.pulledBack P
  obtain ⟨V, hVopen, hVnonempty, hVass⟩ :=
    Stacks.RelativeAssassin.exists_open_closure_genericPoints_fibre_mem_relativeAssassin
      D.toT F D.xi hD.1
  let CT : Closeds D.T := ⟨closure ({D.t'} : Set D.T), isClosed_closure⟩
  let I_T := Scheme.IdealSheafData.vanishingIdeal CT
  let j := I_T.subschemeι
  have hjRange : Set.range j.base = closure ({D.t'} : Set D.T) :=
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal CT
  obtain ⟨t₀', ht₀'⟩ : D.t' ∈ Set.range j := by
    rw [hjRange]
    exact subset_closure rfl
  obtain ⟨t₀, ht₀⟩ : D.t ∈ Set.range j := by
    rw [hjRange]
    exact specializes_iff_mem_closure.mp D.specializes
  have hspec₀ : t₀' ⤳ t₀ := by
    apply j.isClosedEmbedding.isInducing.specializes_iff.mp
    simpa [ht₀', ht₀] using D.specializes
  let g₀ := j ≫ D.g
  have hchosen₀ : g₀ t₀ = P.s := by
    change D.g (j t₀) = P.s
    rw [ht₀]
    exact D.mapsToChosenPoint
  have : IsLocallyNoetherian D.T := LocallyOfFiniteType.isLocallyNoetherian D.g
  have : IsLocallyNoetherian I_T.subscheme := LocallyOfFiniteType.isLocallyNoetherian j
  have : IrreducibleSpace I_T.subscheme := irreducibleSpace_subscheme_closure D.t'
  have hgenT₀ : IsGenericPoint t₀' (Set.univ : Set I_T.subscheme) := by
    refine isGenericPoint_iff_specializes.mpr fun y => ⟨fun _ => by simp, fun _ => ?_⟩
    apply j.isClosedEmbedding.isInducing.specializes_iff.mp
    simpa [ht₀'] using isGenericPoint_closure.specializes (subschemeι_mem_closure D.t' y)
  let CX : Closeds D.X_T := ⟨closure ({D.xi} : Set D.X_T), isClosed_closure⟩
  let I_X := Scheme.IdealSheafData.vanishingIdeal CX
  have hXrange : Set.range I_X.subschemeι.base = closure ({D.xi} : Set D.X_T) :=
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal CX
  let fX := I_X.subschemeι ≫ D.toT
  have hfXrange : Set.range fX.base ⊆ closure ({D.t'} : Set D.T) := by
    rintro y ⟨z, rfl⟩
    have hspec : D.xi ⤳ I_X.subschemeι z :=
      specializes_iff_mem_closure.mpr (subschemeι_mem_closure D.xi z)
    have hspecT : D.t' ⤳ D.toT (I_X.subschemeι z) := by
      simpa [D.xi_liesOver] using hspec.map D.toT.continuous
    exact hspecT.mem_closure
  obtain ⟨f₀, hf₀⟩ := exists_lift_vanishingIdeal CT fX hfXrange
  have : LocallyOfFiniteType (f₀ ≫ j) := by rw [hf₀]; infer_instance
  have : LocallyOfFiniteType f₀ := locallyOfFiniteType_of_comp f₀ j
  have : QuasiCompact (f₀ ≫ j) := by rw [hf₀]; infer_instance
  have : QuasiCompact f₀ := QuasiCompact.of_comp f₀ j
  have hxiGeneric :
      IsGenericPoint (⟨D.xi, subset_closure rfl⟩ : closure ({D.xi} : Set D.X_T)) Set.univ := by
    refine isGenericPoint_iff_specializes.mpr fun y => ⟨fun _ => by simp, fun _ => ?_⟩
    exact (subtype_specializes_iff _ _).2 (isGenericPoint_closure.specializes y.2)
  have hxiV : (⟨D.xi, subset_closure rfl⟩ : closure ({D.xi} : Set D.X_T)) ∈ V := by
    exact (hxiGeneric.mem_open_set_iff hVopen).2 (by simpa using hVnonempty)
  let φ : I_X.subscheme → closure ({D.xi} : Set D.X_T) := fun z ↦
    ⟨I_X.subschemeι z, subschemeι_mem_closure D.xi z⟩
  have hφ : Continuous φ := continuous_induced_rng.mpr I_X.subschemeι.continuous
  let V₀ : I_X.subscheme.Opens := ⟨φ ⁻¹' V, hVopen.preimage hφ⟩
  obtain ⟨z, hzi⟩ : D.xi ∈ Set.range I_X.subschemeι := by
    rw [hXrange]
    exact subset_closure rfl
  have hzV₀ : z ∈ V₀.1 := by
    have hφz : φ z = ⟨D.xi, subset_closure rfl⟩ := Subtype.ext hzi
    change φ z ∈ V
    rwa [hφz]
  let fV : V₀.toScheme ⟶ I_T.subscheme := V₀.ι ≫ f₀
  have hfVcomp : fV ≫ j = V₀.ι ≫ fX := by
    change V₀.ι ≫ f₀ ≫ j = V₀.ι ≫ fX
    rw [hf₀]
  let a₀ : V₀.toScheme := ⟨z, hzV₀⟩
  have hfa₀ : fV a₀ = t₀' := by
    apply j.isClosedEmbedding.injective
    calc
      j (fV a₀) = fX z := hom_congr_apply hfVcomp a₀
      _ = D.t' := by simp [fX, hzi, D.xi_liesOver]
      _ = j t₀' := ht₀'.symm
  have hfiberV : Nonempty (fV.fiber t₀') := by
    rw [← hfa₀]
    exact ⟨fV.asFiber a₀⟩
  have : IsLocallyNoetherian D.X_T := LocallyOfFiniteType.isLocallyNoetherian D.toT
  have : IsLocallyNoetherian I_X.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian I_X.subschemeι
  have : LocallyOfFiniteType fV := inferInstance
  have : QuasiCompact fV := inferInstance
  obtain ⟨W, hWnonempty, hWsurjective⟩ :=
    exists_nonempty_open_surjective_baseChange fV t₀' hgenT₀ hfiberV
  let tFib : D.g.fiber P.s := (D.g.fiberHomeo P.s).symm ⟨D.t, D.mapsToChosenPoint⟩
  have htFib : D.g.fiberι P.s tFib = D.t := D.g.fiberι_fiberHomeo_symm P.s _
  have htClosed : IsClosed ({tFib} : Set (D.g.fiber P.s)) := by
    have heq : t_fib = tFib := (D.g.fiberι P.s).isEmbedding.injective (by rw [ht_fib, htFib])
    rw [← heq]
    exact ht_closed
  let k : g₀.fiber (g₀ t₀) → D.g.fiber P.s := fun y =>
    (D.g.fiberHomeo P.s).symm ⟨j (g₀.fiberι (g₀ t₀) y), by
      change D.g (j (g₀.fiberι (g₀ t₀) y)) = P.s
      rw [show D.g (j (g₀.fiberι (g₀ t₀) y)) = g₀ (g₀.fiberι (g₀ t₀) y) from rfl,
        g₀.apply_fiberι (g₀ t₀) y]
      exact hchosen₀⟩
  have hk (y : g₀.fiber (g₀ t₀)) : D.g.fiberι P.s (k y) = j (g₀.fiberι (g₀ t₀) y) :=
    D.g.fiberι_fiberHomeo_symm P.s _
  have hkcont : Continuous k :=
    (D.g.fiberHomeo P.s).symm.continuous.comp
      ((j.continuous.comp (g₀.fiberι (g₀ t₀)).continuous).subtype_mk _)
  have hclosedGU : IsClosed ({g₀.asFiber t₀} : Set (g₀.fiber (g₀ t₀))) := by
    have hkpre : k ⁻¹' {tFib} = {g₀.asFiber t₀} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hy
        have h1 : j (g₀.fiberι (g₀ t₀) y) = D.t := by
          have h := congrArg (D.g.fiberι P.s) hy
          rwa [hk y, htFib] at h
        have h2 : g₀.fiberι (g₀ t₀) y = t₀ :=
          j.isClosedEmbedding.injective (by rw [h1, ht₀])
        exact (g₀.fiberι (g₀ t₀)).isEmbedding.injective (by
          rw [h2, Scheme.Hom.fiberι_asFiber])
      · intro hy
        subst hy
        apply (D.g.fiberι P.s).isEmbedding.injective
        rw [hk, htFib, Scheme.Hom.fiberι_asFiber, ht₀]
    rw [← hkpre]
    exact htClosed.preimage hkcont
  have ht₀'W : t₀' ∈ W.1 :=
    mem_of_isGenericPoint_univ hgenT₀ W.2 hWnonempty
  have hgenericNotS : g₀ t₀' ≠ P.s := by
    change D.g (j t₀') ≠ P.s
    rw [ht₀']
    exact D.apply_ne_of_isImpurity P hD
  have hws' : g₀ t₀' ≠ g₀ t₀ := by rwa [hchosen₀]
  obtain ⟨Z, i, hi, xZ, hix, hqf, zZ, hzW, hzspec, -⟩ :=
    Stacks.ClosedPointsFibre.exists_closedSubscheme_quasiFiniteAt_meeting_open
      g₀ t₀ W hclosedGU ⟨t₀', ht₀'W, hspec₀, hws'⟩
  let wZ : I_T.subscheme := i zZ
  obtain ⟨b, hb⟩ := hWsurjective.surj ⟨wZ, hzW⟩
  let vZ : V₀.toScheme := pullback.fst fV W.ι b
  have hfvZ : fV vZ = wZ := by
    have h : fV vZ = W.ι (pullback.snd fV W.ι b) :=
      hom_congr_apply (pullback.condition (f := fV) (g := W.ι)) b
    rw [hb] at h
    simpa using h
  let xD : D.X_T := I_X.subschemeι (V₀.ι vZ)
  have hxV : xD ∈ (Subtype.val '' V : Set D.X_T) := ⟨φ vZ.1, vZ.2, rfl⟩
  have hxbase : D.toT xD = j wZ := by
    have hcomp : j (fV vZ) = D.toT xD := hom_congr_apply hfVcomp vZ
    rw [hfvZ] at hcomp
    exact hcomp.symm
  let sZ : D.T := j wZ
  let E : Set (D.toT.fiber sZ) := D.toT.fiberι sZ ⁻¹' (Subtype.val '' V : Set D.X_T)
  have hEloc : IsLocallyClosed E := by
    have hrangeLC : IsLocallyClosed
        (Set.range (Subtype.val : closure ({D.xi} : Set D.X_T) → D.X_T)) := by
      simpa using isClosed_closure.isLocallyClosed
    exact ((hVopen.isLocallyClosed.image Topology.IsInducing.subtypeVal
      hrangeLC).preimage (D.toT.fiberι sZ).continuous)
  let xF : D.toT.fiber sZ := (D.toT.fiberHomeo sZ).symm ⟨xD, hxbase⟩
  have hxFE : xF ∈ E := by
    change D.toT.fiberι sZ xF ∈ (Subtype.val '' V : Set D.X_T)
    rw [D.toT.fiberι_fiberHomeo_symm]
    exact hxV
  obtain ⟨etaE⟩ := nonempty_genericPoints_of_isLocallyClosed hEloc ⟨xF, hxFE⟩
  let eta : D.toT.fiber sZ := etaE.1.1
  let etaX : D.X_T := D.toT.fiberι sZ eta
  have hetaBase : D.toT etaX = sZ := D.toT.apply_fiberι sZ eta
  have hetaXV : etaX ∈ (Subtype.val '' V : Set D.X_T) := etaE.1.2
  have hetaAss : etaX ∈ Stacks.Divisors.relativeAssassin D.toT F :=
    hVass sZ ⟨etaX, hetaXV, hetaBase⟩ etaE
  let kT := i ≫ j
  obtain ⟨b₀, hb₀, hc₀⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := D.toT) (g := kT) etaX zZ
      (by simpa [kT] using hetaBase)
  let Tr : Scheme.Pullback.Triplet D.toT kT := Scheme.Pullback.Triplet.ofPoint b₀
  let comp : irreducibleComponents (Spec Tr.tensor) :=
    ⟨irreducibleComponent (Scheme.Pullback.SpecOfPoint b₀),
      irreducibleComponent_mem_irreducibleComponents _⟩
  let p := genericPoints.ofComponent comp
  let r := pullback.fst D.toT kT
  let q := pullback.snd D.toT kT
  let xi₁ : ↑(pullback (C := Scheme.{u}) D.toT kT) := Tr.SpecTensorTo p.1
  have hrxi : r xi₁ = etaX :=
    (Tr.fst_SpecTensorTo_apply p.1).trans (by simpa [Tr] using hb₀)
  have hqxi : q xi₁ = zZ :=
    (Tr.snd_SpecTensorTo_apply p.1).trans (by simpa [Tr] using hc₀)
  let D₁ : ImpurityDiagram P := by
    refine
      { T := Z
        g := kT ≫ D.g
        t' := zZ
        t := xZ
        specializes := hzspec
        mapsToChosenPoint := ?_
        X_T := pullback D.toT kT
        toX := r ≫ D.toX
        toT := q
        isPullback := (IsPullback.of_hasPullback D.toT kT).paste_horiz D.isPullback
        xi := xi₁
        xi_liesOver := hqxi }
    change D.g (j (i xZ)) = P.s
    rw [hix, ht₀]
    exact D.mapsToChosenPoint
  have hxiNested : xi₁ ∈ Stacks.Divisors.relativeAssassin q
      ((Scheme.Modules.pullback r).obj F) := by
    rw [mem_relativeAssassin_pullback_iff]
    refine ⟨by rw [show r xi₁ = etaX from hrxi]; exact hetaAss, ?_⟩
    have he : (⟨Scheme.Pullback.Triplet.ofPoint xi₁, Scheme.Pullback.SpecOfPoint xi₁⟩ :
        Σ T : Scheme.Pullback.Triplet D.toT kT, Spec T.tensor) = ⟨Tr, p.1⟩ :=
      (Scheme.Pullback.carrierEquiv (f := D.toT) (g := kT)).apply_symm_apply ⟨Tr, p.1⟩
    let Good : (Σ T : Scheme.Pullback.Triplet D.toT kT, Spec T.tensor) → Prop := fun w =>
      ∃ C ∈ irreducibleComponents (Spec w.1.tensor), IsGenericPoint w.2 C
    change Good ⟨Scheme.Pullback.Triplet.ofPoint xi₁, Scheme.Pullback.SpecOfPoint xi₁⟩
    exact he.symm ▸ (show Good ⟨Tr, p.1⟩ from
      ⟨comp, comp.2, genericPoints.isGenericPoint_ofComponent comp⟩)
  let eQ : D₁.pulledBack P ≅ (Scheme.Modules.pullback r).obj F :=
    (Scheme.Modules.pullbackComp r D.toX).symm.app P.F
  have hxiAss₁ : xi₁ ∈ Stacks.Divisors.relativeAssassin q (D₁.pulledBack P) := by
    rw [relativeAssassin_eq_of_moduleIso q eQ]
    exact hxiNested
  have hxiEta : D.xi ⤳ etaX := by
    obtain ⟨v, hv, hvEta⟩ := hetaXV
    rw [← hvEta]
    exact specializes_iff_mem_closure.mpr v.2
  have hdisj : closure ({xi₁} : Set ↑(pullback (C := Scheme.{u}) D.toT kT)) ∩
      Set.range (q.fiberι xZ) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_
    have hspec : xi₁ ⤳ y := specializes_iff_mem_closure.mpr hy.1
    have hspec' : D.xi ⤳ r y := by
      have hmap := hspec.map r.continuous
      rw [show r xi₁ = etaX from hrxi] at hmap
      exact hxiEta.trans hmap
    have hqy : q y = xZ := by
      rw [q.range_fiberι] at hy
      exact hy.2
    have hcoord : D.toT (r y) = j t₀ := by
      have hcomp : D.toT (r y) = kT (q y) :=
        hom_congr_apply (pullback.condition (f := D.toT) (g := kT)) y
      rw [hcomp, hqy]
      change j (i xZ) = j t₀
      rw [hix]
    have hrt : D.toT (r y) = D.t := by rw [hcoord, ht₀]
    exact false_of_specializes_of_isImpurity hD hspec' hrt
  refine ⟨D₁, ⟨hxiAss₁, hdisj⟩, ?_⟩
  change quasiFiniteAt ((i ≫ j) ≫ D.g) xZ
  rw [Category.assoc]
  exact hqf

end AlgebraicGeometry

end
