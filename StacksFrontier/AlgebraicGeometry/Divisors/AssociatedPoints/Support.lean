module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.Topology.Sheaves.Modules.SupportSection
public import StacksFrontier.Topology.Sheaves.Modules.Support
public import StacksCore.Tactic.StacksAttribute

/-!
# Closedness of the support of a sheaf of modules of finite type

The support of a sheaf of modules of finite type on a topological space is closed. This
applies in particular to a finite type quasi-coherent module on a scheme.

## Main results

* `SheafOfModules.supp_eq_moduleSheaf_supp` identifies this support with the support of a sheaf
  of modules on a ringed space.
* `SheafOfModules.isClosed_supp`: the support of a sheaf of modules of finite type is closed.

## Implementation notes

The support used here is `SheafOfModules.supp`, the set of points at which the stalk is
nonzero. The statement is for an arbitrary sheaf of rings on a topological space; neither
quasi-coherence nor a scheme structure is used.

Finite type gives, around any point `x` outside the support, an open `V` and finitely many
sections of the module over `V` which generate it locally. Their germs at `x` vanish, so they
all restrict to zero on some smaller neighbourhood `W` of `x`; since they still generate on
`W`, every germ at every point of `W` vanishes, and `W` misses the support.

The two auxiliary statements are phrased over
`CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat`, which is what `TopCat.Sheaf`
unfolds to, because the local-generators API they use is stated that way and the unfolding is
not performed at `instances` transparency.

## References

* [Stacks Project, Tag 01BA](https://stacks.math.columbia.edu/tag/01BA)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace SheafOfModules

/-- The support of a categorical sheaf of modules agrees with the support of the module sheaf
it determines: both are read off the same underlying `Ab`-valued presheaf. -/
lemma supp_eq_moduleSheaf_supp {X : AlgebraicGeometry.RingedSpace.{u, u}}
    (F : SheafOfModules.{u}
      ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)) :
    (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = supp F :=
  rfl

section Auxiliary

variable {X : TopCat.{u}}
  {R : CategoryTheory.Sheaf (Opens.grothendieckTopology (X : Type u)) RingCat.{u}}

/-- If a section restricts to zero on an open `W ≤ V`, it restricts to zero on every open
`W' ≤ W`. -/
private lemma res_eq_zero_of_res_eq_zero (F : SheafOfModules.{u} R) {V W W' : Opens X}
    {g : W ⟶ V} {m : ToType (F.val.obj (op V))} (hm : Stacks.SheafOfModules.res F g m = 0)
    (f : W' ⟶ W) (h : W' ⟶ V) : Stacks.SheafOfModules.res F h m = 0 := by
  rw [Subsingleton.elim h (f ≫ g), ← Stacks.SheafOfModules.res_res, hm,
    Stacks.SheafOfModules.res_zero]

/-- If finitely many sections generate a sheaf of modules on an open `V` and all of them
restrict to zero on an open `W ≤ V`, then the stalk of the sheaf vanishes at every point
of `W`. -/
private lemma eq_zero_of_res_generators_eq_zero (F : SheafOfModules.{u} R)
    {V W : Opens X} (hWV : W ⟶ V) {ι : Type u} [Finite ι]
    (u : ι → ToType (F.val.obj (op V)))
    [Epi (Stacks.SheafOfModules.freeToOver F u)]
    (hu : ∀ k : ι, Stacks.SheafOfModules.res F hWV (u k) = 0)
    {y : X} (hy : y ∈ W) (a : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :
    a = 0 := by
  have : Fintype ι := Fintype.ofFinite _
  obtain ⟨U, hyU, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf a
  have hyUW : y ∈ U ⊓ W := ⟨hyU, hy⟩
  obtain ⟨W', h', hyW', c, hc⟩ := Stacks.SheafOfModules.generates_of_epi F u
    (homOfLE (inf_le_right : U ⊓ W ≤ W) ≫ hWV)
    (Stacks.SheafOfModules.res F (homOfLE (inf_le_left : U ⊓ W ≤ U)) m) y hyUW
  have hcomb (k : ι) : Stacks.SheafOfModules.res F
      (h' ≫ homOfLE (inf_le_right : U ⊓ W ≤ W) ≫ hWV) (u k) = 0 :=
    res_eq_zero_of_res_eq_zero F (hu k) (h' ≫ homOfLE (inf_le_right : U ⊓ W ≤ W)) _
  rw [Finset.sum_congr rfl fun k _ => by rw [hcomb k, smul_zero], Finset.sum_const_zero] at hc
  calc TopCat.Presheaf.germ F.val.presheaf U y hyU m
      = Stacks.SheafOfModules.germ F y hyUW
          (Stacks.SheafOfModules.res F (homOfLE (inf_le_left : U ⊓ W ≤ U)) m) :=
        (Stacks.SheafOfModules.germ_res y _ hyUW m).symm
    _ = Stacks.SheafOfModules.germ F y hyW' (Stacks.SheafOfModules.res F h'
          (Stacks.SheafOfModules.res F (homOfLE (inf_le_left : U ⊓ W ≤ U)) m)) :=
        (Stacks.SheafOfModules.germ_res y h' hyW' _).symm
    _ = 0 := by rw [hc]; exact Stacks.SheafOfModules.germ_zero y hyW'

/-- The sections of a family of generating sections of a restriction `F.over V`, read as
sections of `F` over `V`. -/
private noncomputable def generatorsSection (F : SheafOfModules.{u} R) {V : Opens X}
    (gs : (F.over V).GeneratingSections) (j : gs.I) : ToType (F.val.obj (op V)) :=
  (gs.s j).eval (op (Over.mk (𝟙 V)))

/-- A family of generating sections of `F.over V`, read as sections of `F` over `V`, induces an
epimorphism from the free sheaf of modules. -/
private lemma epi_freeToOver_generatorsSection (F : SheafOfModules.{u} R) {V : Opens X}
    (gs : (F.over V).GeneratingSections) :
    Epi (Stacks.SheafOfModules.freeToOver F (generatorsSection F gs)) :=
  Stacks.SheafOfModules.freeHomEquiv_symm_eq_freeToOver F gs.s ▸ gs.epi

/-- Finitely many sections of `F` over `V` whose germs at `x` all vanish restrict to zero on a
single open neighbourhood of `x` inside `V`. -/
private lemma exists_nbhd_forall_res_eq_zero (F : SheafOfModules.{u} R) {V : Opens X}
    {x : X} (hxV : x ∈ V) {ι : Type u} [Finite ι] (u : ι → ToType (F.val.obj (op V)))
    (hx : ∀ j : ι, Stacks.SheafOfModules.germ F x hxV (u j) = 0) :
    ∃ (W : Opens X) (hWV : W ⟶ V), x ∈ W ∧
      ∀ j : ι, Stacks.SheafOfModules.res F hWV (u j) = 0 := by
  classical
  have hzero (j : ι) : ∃ (W : Opens X) (h : W ⟶ V), x ∈ W ∧
      Stacks.SheafOfModules.res F h (u j) = 0 := by
    obtain ⟨W, h, hxW, hres⟩ := Stacks.SheafOfModules.exists_res_eq x hxV (u j) 0
      ((hx j).trans (Stacks.SheafOfModules.germ_zero x hxV).symm)
    exact ⟨W, h, hxW, hres.trans (Stacks.SheafOfModules.res_zero F h)⟩
  choose W hWV hxW hres using hzero
  obtain ⟨W₀, hW₀V, hxW₀, hW₀⟩ := Stacks.SheafOfModules.exists_nbhd_le' x V hxV W hxW
  refine ⟨W₀, hW₀V, hxW₀, fun j => ?_⟩
  exact res_eq_zero_of_res_eq_zero F (hres j) (homOfLE (hW₀ j)) hW₀V

/-- Every point at which the stalk of a sheaf of modules of finite type vanishes has an open
neighbourhood at each of whose points the stalk vanishes. -/
private lemma eventually_stalk_eq_zero (F : SheafOfModules.{u} R) [F.IsFiniteType] {x : X}
    (hx : ∀ a : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x, a = 0) :
    ∀ᶠ y in nhds x, ∀ a : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y, a = 0 := by
  obtain ⟨σ, hσ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  obtain ⟨U₀, -, ⟨i, ⟨g₀⟩⟩, hxU₀⟩ := σ.coversTop ⊤ x (by trivial)
  have hxV : x ∈ σ.X i := (leOfHom g₀) hxU₀
  have hfin : Finite (σ.generators i).I := (hσ.isFiniteType i).finite
  have hepi := epi_freeToOver_generatorsSection F (σ.generators i)
  obtain ⟨W₀, hW₀V, hxW₀, hu⟩ := exists_nbhd_forall_res_eq_zero F hxV
    (generatorsSection F (σ.generators i)) fun j => hx _
  refine Filter.mem_of_superset (W₀.2.mem_nhds hxW₀) fun y hy => ?_
  exact eq_zero_of_res_generators_eq_zero F hW₀V _ hu hy

end Auxiliary

/-- The support of a sheaf of modules of finite type on a topological space is closed. -/
@[stacks 01BA, stacks 056J "closed_support"]
lemma isClosed_supp {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
    (F : SheafOfModules.{u} R) [F.IsFiniteType] :
    IsClosed (supp F) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx0 : ∀ a : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x, a = 0 := by
    simpa only [supp, Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_not] using hx
  refine (eventually_stalk_eq_zero F hx0).mono fun y hy => ?_
  simpa only [Set.mem_compl_iff, supp, Set.mem_ofPred_eq, not_exists, not_not] using hy

end SheafOfModules
