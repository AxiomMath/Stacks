module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChartFrameHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRank

/-!
# Frames and finite freeness

A sheaf of modules `N` on a site is finite free over an object `W` — its restriction to the slice
site at `W` is a finite coproduct of copies of the structure sheaf — exactly when `N` has a frame
over `W` in the sense of `Stacks.SheafOfModules.ChartFrames.IsFrame`.  This file proves the two
directions used to pass between the categorical notion of Stacks 03DL (2) and the sectionwise
notion of `Stacks.SheafOfModules.ChartFrames`.

## Main results

* `Stacks.SheafOfModules.ChartFrames.isColimit_cofan_of_isFrame`: a frame exhibits the restriction
  to the slice as a coproduct of copies of the structure sheaf.
* `Stacks.SheafOfModules.ChartFrames.exists_isFrame_of_isFiniteFree`: a finite free restriction
  has a frame.
* `Stacks.SheafOfModules.ChartFrames.isFiniteLocallyFreeOnSite_of_isFrame` and
  `.isFiniteLocallyFreeOfRank_of_isFrame`: frames on a family covering the final object make
  the module finite locally free, of rank `r` if all frames have `r` vectors.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits

universe u v w

namespace Stacks.SheafOfModules.ChartFrames

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {O : Sheaf J CommRingCat.{w}}

/-- The underlying presheaf of a sheaf of modules over `Tensor.ringSheaf O`, typed over the
presheaf of rings `O ⋙ forget₂ CommRingCat RingCat` in which frames are stated. -/
def valP (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    PresheafOfModules.{w} (O.obj ⋙ forget₂ CommRingCat RingCat) :=
  N.val

section Colimit

variable (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) {W : C} {n : ℕ}
  {e : Fin n → (valP N).obj (op W)} (he : IsFrame (valP N) e)

/-- The sections of the structure sheaf of the slice over an object of the slice. -/
abbrev SliceRing (Y : (Over W)ᵒᵖ) : Type w :=
  ((Stacks.SheafOfModules.Tensor.ringSheaf O).over W).obj.obj Y

/-- The coordinate of a section of the slice in the frame, read as a section of the structure
sheaf of the slice. -/
def sliceCoord (Y : (Over W)ᵒᵖ) (x : (N.over W).val.obj Y) (a : Fin n) : SliceRing (O := O) Y :=
  he.coord Y.unop.hom (show (valP N).obj (op Y.unop.left) from x) a

/-- The morphisms from the structure sheaf of the slice that a frame defines. -/
def frameInj (a : Fin n) :
    SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf O).over W) ⟶ N.over W :=
  (N.over W).unitHomEquiv.symm (SheafOfModules.sectionOver N (e a))

/-- The morphism `frameInj N a` sends the unit section over `Y` to the restriction of `e a`. -/
theorem frameInj_app (a : Fin n) (Y : (Over W)ᵒᵖ) :
    (show (valP N).obj (op Y.unop.left) from
      (frameInj N (e := e) a).val.app Y (1 : SliceRing (O := O)
          Y)) = res (valP N) Y.unop.hom (e a) := by
  have := (N.over W).unitHomEquiv_apply_coe (frameInj N (e := e) a) Y
  rw [frameInj, Equiv.apply_symm_apply] at this
  exact this.symm

/-- The frame coordinates of a section of the slice are additive. -/
theorem sliceCoord_add (Y : (Over W)ᵒᵖ) (x y : (N.over W).val.obj Y) (a : Fin n) :
    sliceCoord N he Y (x + y) a = sliceCoord N he Y x a + sliceCoord N he Y y a :=
  congrFun (he.coord_add Y.unop.hom (show (valP N).obj (op Y.unop.left) from x)
    (show (valP N).obj (op Y.unop.left) from y)) a

/-- The frame coordinates of a section of the slice are linear over the structure sheaf. -/
theorem sliceCoord_smul (Y : (Over W)ᵒᵖ) (r : SliceRing (O := O) Y) (x : (N.over W).val.obj Y)
    (a : Fin n) : sliceCoord N he Y (r • x) a = r * sliceCoord N he Y x a :=
  congrFun (he.coord_smul Y.unop.hom (show O.obj.obj (op Y.unop.left) from r)
    (show (valP N).obj (op Y.unop.left) from x)) a

/-- The frame coordinates of a section of the slice commute with restriction. -/
theorem sliceCoord_map {Y Y' : (Over W)ᵒᵖ} (g : Y ⟶ Y') (x : (N.over W).val.obj Y) (a : Fin n) :
    sliceCoord N he Y' ((N.over W).val.map g x) a =
      ((Stacks.SheafOfModules.Tensor.ringSheaf O).over W).obj.map g (sliceCoord N he Y x a) := by
  have hw : g.unop.left ≫ Y.unop.hom = Y'.unop.hom := Over.w g.unop
  have := he.coord_res_apply Y.unop.hom g.unop.left (show (valP N).obj (op Y.unop.left) from x) a
  unfold sliceCoord
  rw [← hw]
  exact this

/-- The image of the unit section under `frameInj N a` has coordinates `Pi.single a 1`. -/
theorem sliceCoord_frameInj (a : Fin n) (Y : (Over W)ᵒᵖ) :
    sliceCoord N he Y ((frameInj N (e := e) a).val.app Y (1 : SliceRing (O := O) Y)) =
      Pi.single a 1 := by
  funext b
  unfold sliceCoord
  rw [frameInj_app]
  exact congrFun (coord_frame he Y.unop.hom a) b

/-- A section of the slice is the sum of its frame coordinates times the images of the unit
section under the morphisms `frameInj N a`. -/
theorem sum_sliceCoord (Y : (Over W)ᵒᵖ) (x : (N.over W).val.obj Y) :
    ∑ a, sliceCoord N he Y x a • (frameInj N (e := e) a).val.app Y (1 : SliceRing (O := O) Y) =
      x := by
  have h := he.sum_coord Y.unop.hom (show (valP N).obj (op Y.unop.left) from x)
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl (fun a _ => ?_)
  exact congrArg (fun z : (valP N).obj (op Y.unop.left) =>
    he.coord Y.unop.hom (show (valP N).obj (op Y.unop.left) from x) a • z) (frameInj_app N a Y)

variable (t : Cofan (fun _ : Fin n =>
    SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf O).over W)))

/-- The value of the descending morphism of the coproduct cofan of a frame. -/
def frameDescApp (Y : (Over W)ᵒᵖ) (x : (N.over W).val.obj Y) : t.pt.val.obj Y :=
  ∑ a, sliceCoord N he Y x a • (t.inj a).val.app Y (1 : SliceRing (O := O) Y)

/-- The map `frameDescApp N he t Y` is additive. -/
theorem frameDescApp_add (Y : (Over W)ᵒᵖ) (x y : (N.over W).val.obj Y) :
    frameDescApp N he t Y (x + y) = frameDescApp N he t Y x + frameDescApp N he t Y y := by
  simp only [frameDescApp]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [sliceCoord_add, add_smul]

/-- The map `frameDescApp N he t Y` is linear over the structure sheaf of the slice. -/
theorem frameDescApp_smul (Y : (Over W)ᵒᵖ) (r : SliceRing (O := O) Y)
    (x : (N.over W).val.obj Y) :
    frameDescApp N he t Y (r • x) = r • frameDescApp N he t Y x := by
  simp only [frameDescApp]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [sliceCoord_smul, smul_smul]

/-- The maps `frameDescApp N he t Y` commute with restriction along morphisms of the slice. -/
theorem frameDescApp_naturality {Y Y' : (Over W)ᵒᵖ} (g : Y ⟶ Y') (x : (N.over W).val.obj Y) :
    frameDescApp N he t Y' ((N.over W).val.map g x) = t.pt.val.map g (frameDescApp N he t Y x) := by
  simp only [frameDescApp]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [t.pt.val.map_smul]
  have h2 : (t.inj a).val.app Y' (1 : SliceRing (O := O) Y') =
      t.pt.val.map g ((t.inj a).val.app Y (1 : SliceRing (O := O) Y)) := by
    have := PresheafOfModules.naturality_apply (t.inj a).val g (1 : SliceRing (O := O) Y)
    refine Eq.trans ?_ this
    exact congrArg _ (map_one (((Stacks.SheafOfModules.Tensor.ringSheaf O).over W).obj.map
        g).hom).symm
  rw [sliceCoord_map, h2]
  rfl

/-- The descending morphism of the coproduct cofan of a frame. -/
def frameDesc : N.over W ⟶ t.pt where
  val :=
    { app Y := ConcreteCategory.ofHom (C := ModuleCat _)
        { toFun := frameDescApp N he t Y
          map_add' := frameDescApp_add N he t Y
          map_smul' := fun r x => frameDescApp_smul N he t Y r x }
      naturality {Y Y'} g := by
        ext x
        exact frameDescApp_naturality N he t g x }

/-- The composite of `frameInj N a` with `frameDesc N he t` is the `a`-th injection of `t`. -/
theorem frameInj_frameDesc (a : Fin n) :
    frameInj N (e := e) a ≫ frameDesc N he t = t.inj a := by
  apply (SheafOfModules.unitHomEquiv _).injective
  ext Y
  rw [SheafOfModules.unitHomEquiv_apply_coe, SheafOfModules.unitHomEquiv_apply_coe]
  show frameDescApp N he t Y ((frameInj N (e := e) a).val.app Y _) = _
  rw [frameDescApp, sliceCoord_frameInj, Finset.sum_eq_single a]
  · rw [Pi.single_eq_same, one_smul]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, zero_smul]
  · simp

/-- **A frame exhibits the restriction to the slice as a finite coproduct of copies of the
structure sheaf.** -/
def isColimitCofanOfIsFrame : IsColimit (Cofan.mk (N.over W) (frameInj N (e := e))) :=
  Cofan.IsColimit.mk _ (fun t => frameDesc N he t) (fun t a => frameInj_frameDesc N he t a)
    (fun t m hm => by
      ext Y x
      change m.val.app Y x = frameDescApp N he t Y x
      conv_lhs => rw [← sum_sliceCoord N he Y x]
      rw [map_sum, frameDescApp]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [map_smul]
      congr 1
      rw [← hm a]
      rfl)

end Colimit

section OfFree

/-- **A trivialization of the restriction to a slice gives a frame** of the same size. -/
theorem exists_isFrame_of_finsuppEquiv
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) {V : C} {n : ℕ}
    (ψ : ∀ X : (Over V)ᵒᵖ, ((N.over V).val.obj X) ≃ₗ[((Stacks.SheafOfModules.Tensor.ringSheaf
        O).over
      V).obj.obj X] (Fin n →₀ ((Stacks.SheafOfModules.Tensor.ringSheaf O).over V).obj.obj X))
    (hψ : ∀ ⦃X Y : (Over V)ᵒᵖ⦄ (g : X ⟶ Y) (x : (N.over V).val.obj X) (i : Fin n),
      ψ Y ((N.over V).val.map g x) i =
        ((Stacks.SheafOfModules.Tensor.ringSheaf O).over V).obj.map g (ψ X x i)) :
    ∃ e : Fin n → (valP N).obj (op V), IsFrame (valP N) e := by
  let Y₀ : (Over V)ᵒᵖ := op (Over.mk (𝟙 V))
  let e : Fin n → (valP N).obj (op V) := fun a => (ψ Y₀).symm (Finsupp.single a 1)
  let bas : ∀ {T : C} (g : T ⟶ V), Module.Basis (Fin n)
      (((Stacks.SheafOfModules.Tensor.ringSheaf O).over V).obj.obj (op (Over.mk g)))
      ((N.over V).val.obj (op (Over.mk g))) := fun g =>
    (Finsupp.basisSingleOne).map (ψ (op (Over.mk g))).symm
  have key : ∀ {T : C} (g : T ⟶ V) (a : Fin n),
      bas g a = (show (N.over V).val.obj (op (Over.mk g)) from res (valP N) g (e a)) := by
    intro T g a
    show (ψ (op (Over.mk g))).symm (Finsupp.single a 1) = _
    rw [LinearEquiv.symm_apply_eq]
    ext i
    have := hψ (Over.homMk g : Over.mk g ⟶ Over.mk (𝟙 V)).op ((ψ Y₀).symm (Finsupp.single a 1)) i
    refine Eq.trans ?_ this.symm
    rw [LinearEquiv.apply_symm_apply]
    by_cases hai : a = i
    · subst hai
      simp only [Finsupp.single_eq_same]
      exact (map_one _).symm
    · simp only [Finsupp.single_apply, if_neg hai]
      exact (map_zero _).symm
  refine ⟨e, ⟨fun {T} g => ?_, fun {T} g => ?_⟩⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc a
    have hli := Fintype.linearIndependent_iff.1 (bas g).linearIndependent
    exact hli c (by simp only [key]; exact hc) a
  · intro x _
    have hx : x = ∑ a, (show O.obj.obj (op T) from (bas g).repr x a) • res (valP N) g (e a) := by
      have := (bas g).sum_repr x
      simp only [key] at this
      exact this.symm
    rw [hx]
    exact Submodule.sum_mem _ (fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self a)))

/-- **A finite free restriction to a slice has a frame.** -/
theorem exists_isFrame_of_isFiniteFree
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) {V : C}
    (h : SheafOfModules.IsFiniteFree ((Stacks.SheafOfModules.Tensor.ringSheaf O).over V) (N.over
        V)) :
    ∃ (n : ℕ) (e : Fin n → (valP N).obj (op V)), IsFrame (valP N) e := by
  obtain ⟨n, ψ, hψ⟩ := Stacks.SheafOfModules.exists_finsuppEquiv_of_isFiniteFree h
  exact ⟨n, exists_isFrame_of_finsuppEquiv N ψ hψ⟩

/-- **A restriction to a slice which is a coproduct of `n` copies of the unit has a frame of
size `n`.** -/
theorem exists_isFrame_of_isColimit_cofan
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) {V : C} {n : ℕ}
    (ι : ∀ _ : Fin n, SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf O).over V) ⟶
      N.over V)
    (hι : IsColimit (Cofan.mk (N.over V) ι)) :
    ∃ e : Fin n → (valP N).obj (op V), IsFrame (valP N) e := by
  obtain ⟨ψ, hψ⟩ := Stacks.SheafOfModules.exists_finsuppEquiv_of_isColimit_cofan ι hι
  exact exists_isFrame_of_finsuppEquiv N ψ hψ

end OfFree

section Locally

variable {K : Type*} {W : K → C} (hW : J.CoversTop W)
  (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) {n : K → ℕ}
  {e : ∀ k, Fin (n k) → (valP N).obj (op (W k))} (he : ∀ k, IsFrame (valP N) (e k))

/-- The objects mapping to `U` and to some member of the family. -/
def overMembers (U : C) : Type (max u v) :=
  {p : Σ T : C, T ⟶ U // ∃ k, Nonempty (p.1 ⟶ W k)}

include hW in
/-- The objects over `U` which map to some member of a family covering the final object form a
covering sieve of `U`. -/
theorem ofArrows_overMembers_mem (U : C) :
    Sieve.ofArrows (fun p : overMembers (W := W) U => p.1.1) (fun p => p.1.2) ∈ J U := by
  refine J.superset_covering ?_ (hW U)
  rintro T g ⟨k, ⟨h⟩⟩
  exact Sieve.ofArrows_mk _ _ (⟨⟨T, g⟩, ⟨k, ⟨h⟩⟩⟩ : overMembers (W := W) U)

include he in
/-- Over each object of `overMembers U`, the restriction of `N` is a coproduct of `n k` copies of
the structure sheaf for some `k`. -/
theorem exists_isColimit_of_overMembers {U : C} (p : overMembers (W := W) U) :
    ∃ k, ∃ ι : Fin (n k) → (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf O).over
        p.1.1) ⟶
      N.over p.1.1), Nonempty (IsColimit (Cofan.mk (N.over p.1.1) ι)) := by
  obtain ⟨k, ⟨h⟩⟩ := p.2
  exact ⟨k, _, ⟨isColimitCofanOfIsFrame N ((he k).restrict h)⟩⟩

include hW he in
/-- **Frames on a family covering the final object make a module finite locally free.** -/
theorem isFiniteLocallyFreeOnSite_of_isFrame : SheafOfModules.IsFiniteLocallyFreeOnSite N := by
  intro U
  refine ⟨overMembers (W := W) U, fun p => p.1.1, fun p => p.1.2, ofArrows_overMembers_mem hW U,
    fun p => ?_⟩
  obtain ⟨k, ι, ⟨hι⟩⟩ := exists_isColimit_of_overMembers N he p
  exact ⟨n k, N.over p.1.1, ι, ⟨hι⟩, fun _ => LinearEquiv.refl _ _, fun _ _ => rfl⟩

include hW he in
/-- **Frames of a common size `r` on a family covering the final object make a module finite
locally free of rank `r`**, in the form of the rank clause of Stacks 0409. -/
theorem isFiniteLocallyFreeOfRank_of_isFrame (r : ℕ) (hn : ∀ k, n k = r) :
    ∀ U : C, ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
      (Sieve.ofArrows V f ∈ J U) ∧ ∀ i : I,
        ∃ (ι : ∀ _ : Fin r, SheafOfModules.unit
            ((Stacks.SheafOfModules.Tensor.ringSheaf O).over (V i)) ⟶ N.over (V i)),
          Nonempty (IsColimit (Cofan.mk (N.over (V i)) ι)) := by
  intro U
  refine ⟨overMembers (W := W) U, fun p => p.1.1, fun p => p.1.2, ofArrows_overMembers_mem hW U,
    fun p => ?_⟩
  obtain ⟨k, ι, ⟨hι⟩⟩ := exists_isColimit_of_overMembers N he p
  have h := hn k
  revert ι
  rw [h]
  exact fun ι hι => ⟨ι, ⟨hι⟩⟩

end Locally

end Stacks.SheafOfModules.ChartFrames
