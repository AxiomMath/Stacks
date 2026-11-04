module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.InfinitesimalNeighbourhood.NeighbourhoodSpace
import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianNilradical

/-!
# A locally Noetherian formal algebraic space is the colimit of its infinitesimal neighbourhoods

Let `W` be a locally Noetherian formal algebraic space with reduction `i : W_red ⟶ W`. The
infinitesimal neighbourhoods `W_0 ⊆ W_1 ⊆ W_2 ⊆ ⋯` of `W_red` in `W`
(`AlgebraicGeometry.FormalSpace.reductionNeighbourhood`) form a diagram `ℕ ⥤ FppfSheaf` with a
cocone over `W`, and this cocone is a colimit: every section of `W` lies, locally, in some
`W_k`, because over a Noetherian adic affine chart `Spf A` every morphism from an affine scheme
factors through some stage `Spec(A/J)`, and `J ⊇ 𝔞^(k+1)` for some `k`. This is the assertion
`X = colim X_n` of Stacks 0GHM.

## Main definitions

* `AlgebraicGeometry.FormalSpace.reductionNeighbourhoodDiagram`: the diagram `k ↦ W_k`.
* `AlgebraicGeometry.FormalSpace.reductionNeighbourhoodCocone`: its cocone over `W`.

## Main results

* `AlgebraicGeometry.FormalSpace.isColimit_of_mono_of_locally_mem`: a cocone of monomorphisms
  of sheaves of sets indexed by `ℕ` is a colimit when every section of its point lies locally
  in the image of some leg.
* `AlgebraicGeometry.FormalSpace.isColimit_reductionNeighbourhoodCocone`: `W = colim W_k`.

## References

* [Stacks Project, Tag 0GHM](https://stacks.math.columbia.edu/tag/0GHM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalRing

universe w v u

namespace AlgebraicGeometry.FormalSpace

section General

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **A directed union of subsheaves is their colimit.** Let `G : ℕ ⥤ Sheaf J (Type w)` with a
cocone `ι` of monomorphisms over `F`. If every section of `F` lies locally in the image of some
leg, the cocone is a colimit. -/
def isColimit_of_mono_of_locally_mem {F : Sheaf J (Type w)} {G : ℕ ⥤ Sheaf J (Type w)}
    (ι : G ⟶ (Functor.const ℕ).obj F) (hι : ∀ n, Mono (ι.app n))
    (hloc : ∀ (T : C) (t : F.obj.obj (op T)), ∃ R ∈ J T, ∀ ⦃V : C⦄ (g : V ⟶ T), R g →
      ∃ (n : ℕ) (x : (G.obj n).obj.obj (op V)), (ι.app n).hom.app (op V) x = F.obj.map g.op t) :
    IsColimit (Cocone.mk F ι) := by
  classical
  have hinj : ∀ (n : ℕ) (V : Cᵒᵖ), Function.Injective ((ι.app n).hom.app V) := fun n V =>
    haveI := hι n
    (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1
      ((sheafToPresheaf J (Type w)).map_mono (ι.app n)) V)
  have hιnat : ∀ {n m : ℕ} (h : n ⟶ m) (V : Cᵒᵖ) (x : (G.obj n).obj.obj V),
      (ι.app m).hom.app V ((G.map h).hom.app V x) = (ι.app n).hom.app V x := by
    intro n m h V x
    exact congrArg (fun φ => φ.hom.app V x) (ι.naturality h)
  let U : Subfunctor F.obj := ⨆ n, Subfunctor.range (ι.app n).hom
  have hU : ∀ (V : Cᵒᵖ) (t : F.obj.obj V), t ∈ U.obj V ↔
      ∃ (n : ℕ) (x : (G.obj n).obj.obj V), (ι.app n).hom.app V x = t := by
    intro V t
    simp only [U, Subfunctor.iSup_obj, Set.mem_iUnion, Subfunctor.range_obj, Set.mem_range]
  -- two legs meeting in `F` are identified in any cocone
  have hwd : ∀ (s : Cocone G) {n m : ℕ} (V : Cᵒᵖ) (x : (G.obj n).obj.obj V)
      (y : (G.obj m).obj.obj V), (ι.app n).hom.app V x = (ι.app m).hom.app V y →
      (s.ι.app n).hom.app V x = (s.ι.app m).hom.app V y := by
    intro s n m V x y hxy
    let N := max n m
    have hx := hιnat (homOfLE (le_max_left n m)) V x
    have hy := hιnat (homOfLE (le_max_right n m)) V y
    have heq : (G.map (homOfLE (le_max_left n m))).hom.app V x =
        (G.map (homOfLE (le_max_right n m))).hom.app V y :=
      hinj N V (hx.trans (hxy.trans hy.symm))
    have sx := congrArg (fun φ => φ.hom.app V x) (s.ι.naturality (homOfLE (le_max_left n m)))
    have sy := congrArg (fun φ => φ.hom.app V y) (s.ι.naturality (homOfLE (le_max_right n m)))
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at sx sy
    rw [← sx, ← sy]
    change (s.ι.app N).hom.app V ((G.map _).hom.app V x) =
      (s.ι.app N).hom.app V ((G.map _).hom.app V y)
    rw [heq]
  have hsheafify : ∀ (V : Cᵒᵖ) (t : F.obj.obj V), t ∈ (U.sheafify J).obj V := by
    intro V t
    obtain ⟨R, hR, h⟩ := hloc V.unop t
    refine J.superset_covering (fun W g hg => ?_) hR
    obtain ⟨n, x, hx⟩ := h g hg
    exact (hU _ _).2 ⟨n, x, hx⟩
  have hF : Presieve.IsSheaf J F.obj := (isSheaf_iff_isSheaf_of_type J _).1 F.property
  -- the map out of the union
  let φ (s : Cocone G) : U.toFunctor ⟶ s.pt.obj :=
    { app := fun V => TypeCat.ofHom fun t => (s.ι.app ((hU V t.1).1 t.2).choose).hom.app V
          ((hU V t.1).1 t.2).choose_spec.choose
      naturality := by
        intro V V' g
        ext t
        obtain ⟨n, x, hx⟩ := (hU V t.1).1 t.2
        change (s.ι.app _).hom.app V' _ = s.pt.obj.map g ((s.ι.app _).hom.app V _)
        rw [← NatTrans.naturality_apply]
        refine hwd s V' _ _ ?_
        rw [NatTrans.naturality_apply, ((hU V t.1).1 t.2).choose_spec.choose_spec,
          ((hU V' _).1 (U.toFunctor.map g t).2).choose_spec.choose_spec]
        rfl }
  have hφ : ∀ (s : Cocone G) (n : ℕ) (V : Cᵒᵖ) (x : (G.obj n).obj.obj V)
      (hx : (ι.app n).hom.app V x ∈ U.obj V),
      (φ s).app V ⟨_, hx⟩ = (s.ι.app n).hom.app V x := by
    intro s n V x hx
    exact hwd s V _ _ (((hU V _).1 hx).choose_spec.choose_spec)
  let incl : F.obj ⟶ (U.sheafify J).toFunctor :=
    Subfunctor.lift (𝟙 F.obj) (by rintro V _ ⟨t, rfl⟩; exact hsheafify V t)
  let desc (s : Cocone G) : F ⟶ s.pt :=
    ⟨incl ≫ U.sheafifyLift (φ s) ((isSheaf_iff_isSheaf_of_type J _).1 s.pt.property)⟩
  have hfac : ∀ (s : Cocone G) (n : ℕ), ι.app n ≫ desc s = s.ι.app n := by
    intro s n
    apply (sheafToPresheaf J (Type w)).map_injective
    ext V x
    have hx : (ι.app n).hom.app V x ∈ U.obj V := (hU V _).2 ⟨n, x, rfl⟩
    have h1 := congrArg (fun ψ => ψ.app V ⟨_, hx⟩)
      (U.to_sheafifyLift (φ s) ((isSheaf_iff_isSheaf_of_type J _).1 s.pt.property))
    refine Eq.trans ?_ (h1.trans (hφ s n V x hx))
    rfl
  refine ⟨desc, fun s n => hfac s n, fun s m hm => ?_⟩
  apply (sheafToPresheaf J (Type w)).map_injective
  ext V t
  obtain ⟨R, hR, h⟩ := hloc V.unop t
  apply ((isSheaf_iff_isSheaf_of_type J _).1 s.pt.property _ hR).isSeparatedFor.ext
  intro W g hg
  obtain ⟨n, x, hx⟩ := h g hg
  change s.pt.obj.map g.op (m.hom.app V t) = s.pt.obj.map g.op ((desc s).hom.app V t)
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, ← hx]
  have e1 := congrArg (fun ψ => ψ.hom.app (op W) x) (hm n)
  have e2 := congrArg (fun ψ => ψ.hom.app (op W) x) (hfac s n)
  exact e1.trans e2.symm

end General

attribute [local instance] sheaf_hasColimits

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {W Wred : FppfSheaf B S hS} (i : Wred ⟶ W)

/-- The infinitesimal neighbourhoods grow with their order. -/
theorem reductionNeighbourhood_mono {k m : ℕ} (h : k ≤ m) :
    reductionNeighbourhood i k ≤ reductionNeighbourhood i m := by
  intro T t ht V g hV K hK
  rw [eq_bot_iff]
  calc K ^ (m + 1) ≤ K ^ (k + 1) := Ideal.pow_le_pow_right (Nat.succ_le_succ h)
    _ = ⊥ := ht V g hV K hK

/-- The diagram `W_0 ⟶ W_1 ⟶ W_2 ⟶ ⋯` of infinitesimal neighbourhoods of the reduction. -/
def reductionNeighbourhoodDiagram : ℕ ⥤ FppfSheaf B S hS where
  obj k := reductionNeighbourhoodSheaf i k
  map h := ⟨Subfunctor.homOfLe (reductionNeighbourhood_mono i (leOfHom h))⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The cocone of inclusions `W_k ⟶ W`. -/
def reductionNeighbourhoodCocone : Cocone (reductionNeighbourhoodDiagram i) where
  pt := W
  ι := { app k := reductionNeighbourhoodι i k }

variable {i}

/-- Over a Noetherian adic chart every section over an affine object lies in some stage
`Spec(A/𝔞^(k+1))`. -/
theorem PresentedEtaleChart.exists_mem_range_powStage {c : PresentedEtaleChart B S hS W}
    {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (y : (formalSpectrum c.system).obj.obj (op T)) :
    ∃ k, y ∈ (Subfunctor.range (stageIncl c.system (c.powStage k)).hom).obj (op T) := by
  obtain ⟨J, g, hg₀⟩ := exists_stage_hom c.weaklyAdmissible c.system T
    ((Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm y)
  have hg : (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm y =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g ≫
        stageIncl c.system J := hg₀
  obtain ⟨⟨I, -, hI⟩, -⟩ := c.isAdic
  obtain ⟨n, hn⟩ := (isAdic_iff.mp (isAdic_topologicalNilradical hI)).2 _
    (J.2.1.mem_nhds J.1.zero_mem)
  refine ⟨n, (mem_range_stageIncl_iff c.weaklyAdmissible c.system J _ hg).2 ?_⟩
  have hJ := (mem_range_stageIncl_iff c.weaklyAdmissible c.system J J hg).1
    (mem_range_stageIncl_of_eq c.system J g hg)
  refine le_bot_iff.1 (le_trans (Ideal.map_mono (Ideal.comap_mono ?_)) hJ.le)
  exact (Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn

/-- **Every section of `W` lies locally in some `W_k`.** -/
theorem exists_mem_reductionNeighbourhood_locally (hW : IsLocallyNoetherian B S hS W)
    (hred : IsReduction B S hS W Wred i) {T : BigFppfOver B S hS} (t : W.obj.obj (op T)) :
    ∃ R ∈ BigFppfOver.topology B S hS T, ∀ ⦃V : BigFppfOver B S hS⦄ (g : V ⟶ T), R g →
      ∃ k, W.obj.map g.op t ∈ (reductionNeighbourhood i k).obj (op V) := by
  obtain ⟨I, c, hcover⟩ := exists_presentedEtaleCharts hW
  obtain ⟨R, hR, h⟩ := (Sheaf.isLocallySurjective_sigmaDesc_iff _).1 hcover t
  refine ⟨_, mem_topology_of_affine hR (P := Sieve.bind R.arrows fun V g _ =>
    { arrows := fun V' g' => ∃ k, W.obj.map (g' ≫ g).op t ∈ (reductionNeighbourhood i k).obj
        (op V')
      downward_closed := by
        rintro V' V'' g' ⟨k, hk⟩ g''
        refine ⟨k, ?_⟩
        rw [Category.assoc, op_comp, FunctorToTypes.map_comp_apply]
        exact (reductionNeighbourhood i k).map g''.op hk }) fun V g hV hg => ?_, ?_⟩
  · have := hV
    obtain ⟨j, y, hy⟩ := h g hg
    obtain ⟨k, hk⟩ := (c j).exists_mem_range_powStage y
    refine ⟨V, 𝟙 V, g, hg, ⟨k, ?_⟩, Category.id_comp g⟩
    rw [Category.id_comp, ← hy]
    exact ((c j).mem_range_powStage_iff_mem hred k y).1 hk
  · rintro V _ ⟨V', g', g, hg, ⟨k, hk⟩, rfl⟩
    exact ⟨k, hk⟩

/-- **`W` is the colimit of its infinitesimal neighbourhoods `W_k`** (Stacks 0GHM). -/
def isColimit_reductionNeighbourhoodCocone (hW : IsLocallyNoetherian B S hS W)
    (hred : IsReduction B S hS W Wred i) :
    IsColimit (reductionNeighbourhoodCocone i) := by
  refine isColimit_of_mono_of_locally_mem (F := W) (G := reductionNeighbourhoodDiagram i)
    (reductionNeighbourhoodCocone i).ι (fun k => (sheafToPresheaf _ _).mono_of_mono_map
      (inferInstanceAs (Mono (reductionNeighbourhood i k).ι))) fun T t => ?_
  obtain ⟨R, hR, h⟩ := exists_mem_reductionNeighbourhood_locally hW hred t
  exact ⟨R, hR, fun V g hg => by
    obtain ⟨k, hk⟩ := h g hg
    exact ⟨k, ⟨_, hk⟩, rfl⟩⟩

end AlgebraicGeometry.FormalSpace

end
