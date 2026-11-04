module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceScalarRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackLocalGeneration
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackPresentationData

/-!
# A finite presentation from section-level presentation data

Stacks 03DL states finite presentation of a sheaf of modules on a ringed site in terms of
sections: over an object `V` there are finitely many sections `s` of `M` which generate locally,
and finitely many tuples `t j` of sections of the structure sheaf, each a relation among the
`s`, such that every relation among the `s` is locally a combination of the `t j`. Mathlib's
`SheafOfModules.Presentation` is instead a pair of `SheafOfModules.GeneratingSections`, one for
the module and one for the kernel of the resulting morphism out of a free sheaf of modules.
This file shows that the section-level data over `V` yields a finite `(M.over V).Presentation`.

## Main definitions

* `Stacks.SheafOfModules.overTerminalSection`: a section over the terminal object
  `Over.mk (𝟙 V)` of a sheaf of modules on the slice site at `V`, read as a global section.
* `Stacks.SheafOfModules.generatorsOfGeneratesLocally`: the generating sections of `M.over V`
  given by a finite locally generating family of sections of `M` over `V`.

## Main results

* `Stacks.SheafOfModules.generatesLocally_of_locallySpans`: a family of sections which
  `Stacks.Sheaves.LocalGeneration.LocallySpans` generates locally in the sense of
  `Stacks.SheafOfModules.GeneratesLocally`.
* `Stacks.SheafOfModules.coordsOver_sum_smul`: the coordinates of a linear combination of
  sections of a free sheaf of modules on a slice site are the combination of their coordinates,
  with the scalars read in the base.
* `Stacks.SheafOfModules.generatorsOfGeneratesLocally_π`: the morphism out of the free sheaf
  given by those generators is `Stacks.SheafOfModules.freeToOver`.
* `Stacks.SheafOfModules.exists_isFinite_presentation_over_of_relations`: section-level finite
  presentation data for `M` over `V` yields a finite `(M.over V).Presentation`.
* `Stacks.SheafOfModules.exists_isFinite_presentation_over_of_locallySpans`: the same with local
  generation in the `Stacks.Sheaves.LocalGeneration.LocallySpans` form.
* `Stacks.SheafOfModules.exists_isFinite_presentation_over_of_isPresentationData`: the same for
  data satisfying `Stacks.Sheaves.LocalGeneration.IsPresentationData`.

## Implementation notes

The generators come from local generation of `s` through
`Stacks.SheafOfModules.epi_freeHomEquiv_symm_mkOver`. Each row of `t` lies in
`Stacks.SheafOfModules.relationsSubmodule` over the terminal object of the slice site, hence lifts
to a section of the kernel there by `Stacks.SheafOfModules.exists_kernel_section_coordsOver_eq`,
which `overTerminalSection` turns into a global section. These global sections span the kernel
locally, and the generating sections of the kernel are given by
`Stacks.Sheaves.LocalGeneration.exists_generatingSections_of_locally_spanning_sections` on the
slice site.

Both index types are `ULift (Fin _)`, since `GeneratingSections.I` lives in the module universe.
The relations are stated with scalars in `R(Z)` and `R(W)`; the slice spelling
`(R.over V).obj.obj (op W)` is reached through `coordsOver` and
`Stacks.SheafOfModules.overScalarsHom`.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 01BN](https://stacks.math.columbia.edu/tag/01BN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open Stacks.Sheaves.LocalGeneration

universe u v u'

namespace Stacks.SheafOfModules

/-! ### Local generation in the two spellings -/

section Bridge

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {N : SheafOfModules.{u} R} {V : C}

/-- A family of sections which `Stacks.Sheaves.LocalGeneration.LocallySpans` generates locally in
the sense of `Stacks.SheafOfModules.GeneratesLocally`. -/
theorem generatesLocally_of_locallySpans {n : ℕ} (s : Fin n → ToType (N.val.obj (op V)))
    (hs : LocallySpans N s) : GeneratesLocally J N.val s := by
  intro W f x
  refine ⟨spanSieve N (fun i => restr N f.op (s i)) x, hs W f x, fun Z g hg => ?_⟩
  obtain ⟨a, ha⟩ := hg
  refine ⟨a, Eq.trans (Finset.sum_congr rfl fun i _ => ?_) ha⟩
  exact congrArg (a i • ·)
    ((congrArg (fun h => restr N h (s i)) (op_comp (f := g) (g := f))).trans
      (restr_restr N f.op g.op (s i)).symm)

end Bridge

/-! ### Coordinates of a linear combination -/

section Coords

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {U : C} [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] {ι : Type u} [DecidableEq ι]

/-- Taking coordinates in the base commutes with linear combinations, the scalars in `R(W.left)`
acting through `Stacks.SheafOfModules.overScalarsHom`. -/
lemma coordsOver_sum_smul (W : Over U) {κ : Type*} (d : Finset κ)
    (c : κ → ToType (R.obj.obj (op W.left)))
    (e : κ → ToType ((free (R := R.over U) ι).val.obj (op W))) (i : ι) :
    coordsOver W (∑ k ∈ d, (overScalarsHom R U).app (op W) (c k) • e k) i
      = ∑ k ∈ d, c k * coordsOver W (e k) i :=
  (map_sum ((freeProj (S := R.over U) i).val.app (op W)).hom _ d).trans
    (Finset.sum_congr rfl fun k _ => coordsOver_smul W (c k) (e k) i)

end Coords

/-! ### Global sections from a section over the terminal object of a slice site -/

section Terminal

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- A section over the terminal object `Over.mk (𝟙 V)` of the slice site at `V`, read as a global
section of a sheaf of modules on that site. -/
noncomputable def overTerminalSection {V : C} {K : SheafOfModules.{u} (R.over V)}
    (x : ToType (K.val.obj (op (Over.mk (𝟙 V))))) : K.sections :=
  (FiniteTypeKernel.sectionsEquivOfTerminal K Over.mkIdTerminal).symm x

/-- The value of `overTerminalSection x` over `W` is the restriction of `x` along the morphism
`Over.homMk W.hom` from `W` to the terminal object. -/
@[simp]
lemma overTerminalSection_val {V : C} {K : SheafOfModules.{u} (R.over V)}
    (x : ToType (K.val.obj (op (Over.mk (𝟙 V))))) (W : Over V) :
    (overTerminalSection x).val (op W)
      = K.val.map (Over.homMk W.hom (Category.comp_id _) : W ⟶ Over.mk (𝟙 V)).op x :=
  congrArg (fun g : W ⟶ Over.mk (𝟙 V) => K.val.map g.op x)
    (Over.mkIdTerminal.hom_ext _ _)

end Terminal

/-! ### Decoding section-level presentation data -/

section Decode

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The generating sections of `N.over V` named by a finite family of sections of `N` over `V`
which generates locally, indexed by `ULift (Fin n)`. -/
noncomputable def generatorsOfGeneratesLocally (N : SheafOfModules.{u} R) {V : C} {n : ℕ}
    (s : Fin n → ToType (N.val.obj (op V))) (hs : GeneratesLocally J N.val s) :
    (N.over V).GeneratingSections where
  I := ULift.{u} (Fin n)
  s i := mkOver (s i.down)
  epi := epi_freeHomEquiv_symm_mkOver _ (generatesLocally_comp_equiv Equiv.ulift s hs)

/-- The morphism out of the free sheaf given by `generatorsOfGeneratesLocally N s hs` is
`Stacks.SheafOfModules.freeToOver` of the family `s`. -/
@[simp]
lemma generatorsOfGeneratesLocally_π (N : SheafOfModules.{u} R) {V : C} {n : ℕ}
    (s : Fin n → ToType (N.val.obj (op V))) (hs : GeneratesLocally J N.val s) :
    (generatorsOfGeneratesLocally N s hs).π
      = freeToOver N (fun i : ULift.{u} (Fin n) => s i.down) := rfl

/-- Section-level finite presentation data over `V` yields a finite presentation of `N.over V`.
The data is `n` sections `s` of `N` over `V` and `m` tuples `t j` of sections of
the structure sheaf over `V`, subject to: each `t j` is a relation among the `s`; the `s`
generate `N` locally over `V`; and every relation among the restrictions of the `s` is, on a
covering sieve, a combination of the restrictions of the `t j`. -/
theorem exists_isFinite_presentation_over_of_relations (N : SheafOfModules.{u} R) {V : C}
    {n m : ℕ} (s : Fin n → ToType (N.val.obj (op V)))
    (t : Fin m → Fin n → ToType (R.obj.obj (op V)))
    (hrel : ∀ j, ∑ i, t j i • s i = 0)
    (hgen : GeneratesLocally J N.val s)
    (hall : ∀ (W : C) (g : W ⟶ V) (a : Fin n → ToType (R.obj.obj (op W))),
      ∑ i, a i • res N g (s i) = 0 →
      ∃ S : Sieve W, S ∈ J W ∧ ∀ (Z : C) (h : Z ⟶ W), S h →
        ∃ c : Fin m → ToType (R.obj.obj (op Z)),
          ∀ i, resR R h (a i) = ∑ j, c j * resR R (h ≫ g) (t j i)) :
    ∃ P : (N.over V).Presentation, P.IsFinite := by
  set s' : ULift.{u} (Fin n) → ToType (N.val.obj (op V)) := fun i => s i.down with hs'
  set gen := generatorsOfGeneratesLocally N s hgen with hgen'
  have hπ : gen.π = freeToOver N s' := rfl
  set K := kernel (freeToOver N s') with hK
  set t' : Fin m → ULift.{u} (Fin n) → ToType (R.obj.obj (op (Over.mk (𝟙 V)).left)) :=
    fun j i => t j i.down with ht'
  have hmemRel : ∀ (W : Over V) (a : ULift.{u} (Fin n) → ToType (R.obj.obj (op W.left))),
      a ∈ relationsSubmodule N.val s' W ↔ ∑ i : Fin n, a (ULift.up i) • res N W.hom (s i) = 0 := by
    intro W a
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply]
    exact Iff.of_eq (congrArg (· = 0) (Fintype.sum_equiv Equiv.ulift _ _ fun _ => rfl))
  have hrow : ∀ j, t' j ∈ relationsSubmodule N.val s' (Over.mk (𝟙 V)) := fun j =>
    (hmemRel _ _).2 (by simpa [t', res_id] using hrel j)
  choose w hw using fun j => exists_kernel_section_coordsOver_eq N s' (Over.mk (𝟙 V)) _ (hrow j)
  set ρ : Fin m → K.sections := fun j => overTerminalSection (w j) with hρ
  have hspan : ∀ (W : Over V) (x : ToType (K.val.obj (op W))),
      spanSieve K (fun j => (ρ j).val (op W)) x ∈ (J.over V) W := by
    intro W x
    set z := (kernel.ι (freeToOver N s')).val.app (op W) x with hz
    have hsyz := (hmemRel W _).1 (coordsOver_kernel_mem_relationsSubmodule N s' W x)
    obtain ⟨S, hS, hc⟩ := hall W.left W.hom _ hsyz
    refine (J.over V).superset_covering ?_ (J.overEquiv_symm_mem_over W S hS)
    intro W' f hf
    obtain ⟨c, hcc⟩ := hc W'.left f.left hf
    refine ⟨fun j => c j, ?_⟩
    refine injective_app_kernel_ι (freeToOver N s') (op W') ?_
    refine Eq.trans ?_ (PresheafOfModules.naturality_apply
      (kernel.ι (freeToOver N s')).val f.op x).symm
    refine (coordsOver_bijective W').injective (funext fun i => ?_)
    have hcoord : ∀ (j : Fin m) (i : ULift.{u} (Fin n)),
        coordsOver W' ((kernel.ι (freeToOver N s')).val.app (op W')
            (restr K f.op ((ρ j).val (op W)))) i
          = resR R (f.left ≫ W.hom) (t j i.down) := by
      intro j i
      have e₁ : (kernel.ι (freeToOver N s')).val.app (op W') (restr K f.op ((ρ j).val (op W)))
          = (free (R := R.over V) (ULift.{u} (Fin n))).val.map f.op
              ((free (R := R.over V) (ULift.{u} (Fin n))).val.map
                (Over.homMk W.hom (Category.comp_id _) : W ⟶ Over.mk (𝟙 V)).op
                ((kernel.ι (freeToOver N s')).val.app (op (Over.mk (𝟙 V))) (w j))) :=
        (PresheafOfModules.naturality_apply (kernel.ι (freeToOver N s')).val f.op
            ((ρ j).val (op W))).trans
          (congrArg (fun y => (free (R := R.over V) (ULift.{u} (Fin n))).val.map f.op y)
            ((congrArg ((kernel.ι (freeToOver N s')).val.app (op W))
                (overTerminalSection_val (w j) W)).trans
              (PresheafOfModules.naturality_apply (kernel.ι (freeToOver N s')).val
                (Over.homMk W.hom (Category.comp_id _) : W ⟶ Over.mk (𝟙 V)).op (w j))))
      have e₂ := coordsOver_map (U := V) (ι := ULift.{u} (Fin n)) f
        ((free (R := R.over V) (ULift.{u} (Fin n))).val.map
          (Over.homMk W.hom (Category.comp_id _) : W ⟶ Over.mk (𝟙 V)).op
          ((kernel.ι (freeToOver N s')).val.app (op (Over.mk (𝟙 V))) (w j))) i
      have e₃ := coordsOver_map (U := V) (ι := ULift.{u} (Fin n))
        (Over.homMk W.hom (Category.comp_id _) : W ⟶ Over.mk (𝟙 V))
        ((kernel.ι (freeToOver N s')).val.app (op (Over.mk (𝟙 V))) (w j)) i
      refine (congrArg (fun y => coordsOver W' y i) e₁).trans (e₂.trans ?_)
      refine (congrArg (resR R f.left) (e₃.trans
        (congrArg (resR R W.hom) (congrFun (hw j) i)))).trans ?_
      exact resR_resR R W.hom f.left (t j i.down)
    refine Eq.trans ?_ (coordsOver_map (U := V) (ι := ULift.{u} (Fin n)) f z i).symm
    refine Eq.trans ?_ ((Finset.sum_congr rfl fun j _ =>
      congrArg (fun y => c j * y) (hcoord j i)).trans (hcc i.down).symm)
    refine Eq.trans (congrArg (fun e => coordsOver W' e i)
      (map_sum ((kernel.ι (freeToOver N s')).val.app (op W')).hom _ Finset.univ)) ?_
    refine Eq.trans (congrArg (fun e => coordsOver W' e i)
      (Finset.sum_congr rfl fun j _ =>
        ((kernel.ι (freeToOver N s')).val.app (op W')).hom.map_smul (c j) _)) ?_
    exact coordsOver_sum_smul W' Finset.univ c
      (fun j => (kernel.ι (freeToOver N s')).val.app (op W')
        (restr K f.op ((ρ j).val (op W)))) i
  obtain ⟨rel, hrelEquiv⟩ := exists_generatingSections_of_locally_spanning_sections K m ρ hspan
  exact ⟨⟨gen, rel⟩,
    { isFiniteType_generators := ⟨inferInstanceAs (Finite (ULift.{u} (Fin n)))⟩
      isFiniteType_relations := ⟨Finite.of_equiv (Fin m) hrelEquiv.some.symm⟩ }⟩

/-- Section-level finite presentation data over `V`, with local generation in the
`Stacks.Sheaves.LocalGeneration.LocallySpans` form, yields a finite presentation of
`N.over V`. -/
theorem exists_isFinite_presentation_over_of_locallySpans (N : SheafOfModules.{u} R) {V : C}
    {n m : ℕ} (s : Fin n → ToType (N.val.obj (op V)))
    (t : Fin m → Fin n → ToType (R.obj.obj (op V)))
    (hrel : ∀ j, combinationValue N (t j) s = 0)
    (hgen : LocallySpans N s)
    (hall : ∀ (W : C) (g : W ⟶ V) (a : Fin n → ToType (R.obj.obj (op W))),
      combinationValue N a (fun i => restr N g.op (s i)) = 0 →
      ∃ S : Sieve W, S ∈ J W ∧ ∀ (Z : C) (h : Z ⟶ W), S h →
        ∃ c : Fin m → ToType (R.obj.obj (op Z)),
          ∀ i, resR R h (a i) = ∑ j, c j * resR R (h ≫ g) (t j i)) :
    ∃ P : (N.over V).Presentation, P.IsFinite :=
  exists_isFinite_presentation_over_of_relations N s t hrel
    (generatesLocally_of_locallySpans s hgen) hall

/-- Section-level presentation data satisfying
`Stacks.Sheaves.LocalGeneration.IsPresentationData` over `V` yields a finite presentation of
`N.over V`. -/
theorem exists_isFinite_presentation_over_of_isPresentationData (N : SheafOfModules.{u} R)
    {V : C} {n m : ℕ} (s : Fin n → ToType (N.val.obj (op V)))
    (t : Fin m → Fin n → ToType (R.obj.obj (op V))) (h : IsPresentationData N s t) :
    ∃ P : (N.over V).Presentation, P.IsFinite := by
  refine exists_isFinite_presentation_over_of_locallySpans N s t h.1 h.2.1 fun W g a ha => ?_
  refine ⟨relationSpanSieve R (fun j i => R.obj.map g.op (t j i)) a, h.2.2 W g a ha,
    fun Z k hk => ?_⟩
  obtain ⟨c, hc⟩ := hk
  exact ⟨c, fun i => (hc i).symm.trans
    (Finset.sum_congr rfl fun j _ => congrArg (c j * ·) (resR_resR R g k (t j i)))⟩

end Decode

end Stacks.SheafOfModules

end
