module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeLocallySurjective
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.Modules.Generators.ClosedEmbeddingFiniteType

/-!
# Finite type in the section-and-local-span form, and pushforward along a closed embedding

`Stacks.RingedSpace.IsFiniteType` says that near every point there are finitely many sections of
the module whose restrictions span every section on a smaller open *locally*; this is the form of
finite type used in Stacks 01C4. Mathlib's `SheafOfModules.IsFiniteType` asks instead for a
covering on which the module is a quotient of a free module on a finite index type.

This file identifies the two, and states Stacks 01C4 in Mathlib's form: pushforward along a
closed embedding with surjective structure-sheaf map both preserves and reflects finite type
sheaves of modules.

## Main results

* `Stacks.RingedSpace.localSpan_of_isFiniteType` and
  `Stacks.RingedSpace.isFiniteType_of_localSpan`, combined as
  `Stacks.RingedSpace.isFiniteType_iff_localSpan`: the two forms of finite type agree.
* `Stacks.RingedSpace.exists_generatingSections_of_localLinComb`: finitely many sections of a
  module over an open which locally span every section are generating sections of the
  localization of the module at that open.
* `Stacks.RingedSpace.isFiniteType_modulePushforward_of_isFiniteType` and
  `Stacks.RingedSpace.isFiniteType_of_isFiniteType_modulePushforward`, combined as
  `Stacks.RingedSpace.isFiniteType_modulePushforward_iff'`: **Stacks 01C4** in Mathlib's form.

## Implementation notes

The finite index type of the section-and-local-span form is `Fin n`, which lives in `Type 0`,
while the index type of `SheafOfModules.GeneratingSections` lives in the universe of the sheaf of
rings, so it is lifted with `ULift`.

Sheaves of modules on a ringed space appear here in two interchangeable spellings: as
`AlgebraicGeometry.RingedSpace.ModuleSheaf`, which Stacks 01C4 is stated for, and as
`SheafOfModules (structureSheafRing X)`, whose sheaf of rings is the same
`TopCat.Presheaf RingCat` as the former's; passing between them is the structure literal
`⟨M.val, M.isSheaf⟩`, which changes nothing.

## References

* [Stacks Project, Tag 01C4](https://stacks.math.columbia.edu/tag/01C4)
* [Stacks Project, Tag 01B8](https://stacks.math.columbia.edu/tag/01B8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.LocallySurjective

universe u

namespace Stacks.RingedSpace

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}

/-! ### Generating sections from a family of locally spanning sections -/

/-- A section of `M` over an open `V`, read as a section of the localization `M|_V` of `M` at
`V`: over an object `U ⟶ V` of the slice site its value is the restriction of the given section
to `U`. -/
noncomputable def sectionOver (M : SheafOfModules.{u} (structureSheafRing X))
    (V : Opens X) (s : M.val.obj (op V)) : (M.over V).sections :=
  (M.over V).val.sectionsMk (fun U => M.val.map (unop U).hom.op s) (by
    intro U W f
    change M.val.map f.unop.left.op (M.val.map (unop U).hom.op s) =
      M.val.map (unop W).hom.op s
    calc _ = M.val.map ((unop U).hom.op ≫ f.unop.left.op) s :=
            (M.val.map_comp_apply (unop U).hom.op f.unop.left.op s).symm
      _ = _ := by congr 1)

/-- **Finitely many sections which locally span every section are generating sections.** If the
sections `s : I → M(V)` have the property that every section of `M` on an open contained in `V`
is, near each of its points, an `𝒪`-linear combination of their restrictions, then the induced
map from the free module on `I` over the slice site at `V` is an epimorphism onto `M|_V`. -/
theorem exists_generatingSections_of_localLinComb
    (M : SheafOfModules.{u} (structureSheafRing X)) (V : Opens X)
    {I : Type u} [Fintype I] (s : I → M.val.presheaf.obj (op V))
    (hs : LocalLinComb (F := M) V s) :
    ∃ σ : (M.over V).GeneratingSections, σ.IsFiniteType := by
  classical
  let R := structureSheafRing X
  let sec : I → (M.over V).sections := fun j => sectionOver M V (s j)
  let π : SheafOfModules.free (R := R.over V) I ⟶ M.over V :=
    (M.over V).freeHomEquiv.symm sec
  have hloc : Presheaf.IsLocallySurjective
      ((Opens.grothendieckTopology X.carrier).over V)
      (((SheafOfModules.toSheaf (R.over V)).map π).hom) := by
    constructor
    intro Uo t
    rw [GrothendieckTopology.mem_over_iff]
    intro y hyU
    have hUV : Uo.left ≤ V := leOfHom Uo.hom
    obtain ⟨W, hWU, hyW, a, ha⟩ := hs Uo.left hUV t y hyU
    let Wo : Over V := Over.mk (homOfLE (le_trans hWU hUV))
    let g : Wo ⟶ Uo := Over.homMk (homOfLE hWU) (by cat_disch)
    refine ⟨W, homOfLE hWU, ?_, hyW⟩
    rw [Sieve.overEquiv_iff]
    show Presheaf.imageSieve (((SheafOfModules.toSheaf (R.over V)).map π).hom) t g
    let ar : I → (R.over V).obj.obj (op Wo) := fun j => a j
    let fs : I → (SheafOfModules.free (R := R.over V) I).val.obj (op Wo) :=
      fun j => (SheafOfModules.freeSection (R := R.over V) j).eval (op Wo)
    refine ⟨∑ j, ar j • fs j, ?_⟩
    show π.val.app (op Wo) (∑ j, ar j • fs j) = (M.over V).val.map g.op t
    rw [map_sum]
    have hsmul (j : I) : π.val.app (op Wo) (ar j • fs j) =
        ar j • π.val.app (op Wo) (fs j) :=
      (π.val.app (op Wo)).hom.map_smul (ar j) _
    simp_rw [hsmul]
    have hfree (j : I) : π.val.app (op Wo) (fs j) = (sec j).eval (op Wo) :=
      congrArg (fun q : (M.over V).sections => q.val (op Wo))
        (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection sec j)
    simp_rw [hfree]
    convert ha.symm using 1
    rfl
  have hepiSheaf : Epi ((SheafOfModules.toSheaf (R.over V)).map π) := by
    have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf (R.over V)).map π) := hloc
    infer_instance
  have hepi : Epi π := (SheafOfModules.toSheaf (R.over V)).epi_of_epi_map hepiSheaf
  exact ⟨{ I := I, s := sec, epi := hepi }, ⟨inferInstance⟩⟩

/-! ### The two forms of finite type -/

/-- **A sheaf of modules of finite type in Mathlib's sense is of finite type in the
section-and-local-span sense of Stacks 01C4.** -/
theorem localSpan_of_isFiniteType
    (M : SheafOfModules.{u} (structureSheafRing X))
    (h : SheafOfModules.IsFiniteType (R := structureSheafRing X) M) :
    IsFiniteType (⟨M.val, M.isSheaf⟩ : AlgebraicGeometry.RingedSpace.ModuleSheaf X) := by
  classical
  intro x
  obtain ⟨V, hxV, J, hJ, s, hs⟩ := exists_local_generators h x
  let e := Fintype.equivFin J
  refine ⟨V, hxV, Fintype.card J, fun j => s (e.symm j), ?_⟩
  intro W hWV t y hyW
  obtain ⟨W', hW'W, hyW', a, ha⟩ := hs W hWV t y hyW
  refine ⟨W', hW'W, hyW', ?_⟩
  show (M.val.presheaf.map (homOfLE hW'W).op) t ∈
    Submodule.span ((structureSheafRing X).obj.obj (op W'))
      (Set.range fun j : Fin (Fintype.card J) =>
        (M.val.presheaf.map (homOfLE (hW'W.trans hWV)).op) (s (e.symm j)))
  rw [ha]
  refine Submodule.sum_smul_mem _ a fun j _ => Submodule.subset_span ⟨e j, ?_⟩
  exact congrArg (fun k => (M.val.presheaf.map (homOfLE (hW'W.trans hWV)).op) (s k))
    (e.symm_apply_apply j)

/-- **A sheaf of modules of finite type in the section-and-local-span sense of Stacks 01C4 is of
finite type in Mathlib's sense.** -/
theorem isFiniteType_of_localSpan
    (M : SheafOfModules.{u} (structureSheafRing X))
    (h : IsFiniteType (⟨M.val, M.isSheaf⟩ : AlgebraicGeometry.RingedSpace.ModuleSheaf X)) :
    SheafOfModules.IsFiniteType (R := structureSheafRing X) M := by
  classical
  choose U hxU n s hs using h
  have hlin : ∀ x : X, LocalLinComb (F := M) (U x)
      (fun j : ULift.{u} (Fin (n x)) => s x j.down) := by
    intro x W hWV t y hyW
    obtain ⟨W', hW'W, hyW', ht⟩ := hs x W hWV t y hyW
    have ht' : (M.val.presheaf.map (homOfLE hW'W).op) t ∈
        Submodule.span ((structureSheafRing X).obj.obj (op W'))
          (Set.range fun j : Fin (n x) =>
            (M.val.presheaf.map (homOfLE (hW'W.trans hWV)).op) (s x j)) := ht
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp ht'
    refine ⟨W', hW'W, hyW', fun j => c j.down, ?_⟩
    rw [← hc]
    exact (Fintype.sum_equiv Equiv.ulift _ _ fun j => rfl).symm
  have hgen : ∀ x : X, ∃ σ : (M.over (U x)).GeneratingSections, σ.IsFiniteType :=
    fun x => exists_generatingSections_of_localLinComb M (U x) _ (hlin x)
  let data : M.LocalGeneratorsData.{u, u, u, u} :=
    { I := X
      X := U
      coversTop := (Opens.coversTop_iff (X : Type u) U).2
        (top_unique fun x _ => Opens.mem_iSup.mpr ⟨x, hxU x⟩)
      generators := fun x => (hgen x).choose }
  have hdata : data.IsFiniteType := by
    constructor
    intro x
    exact (hgen x).choose_spec
  exact SheafOfModules.IsFiniteType.mk (M := M) ⟨data, hdata⟩

/-- **The section-and-local-span form of finite type used by Stacks 01C4 agrees with Mathlib's
`SheafOfModules.IsFiniteType`.** -/
theorem isFiniteType_iff_localSpan
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    IsFiniteType (⟨M.val, M.isSheaf⟩ : AlgebraicGeometry.RingedSpace.ModuleSheaf X) ↔
      SheafOfModules.IsFiniteType (R := structureSheafRing X) M :=
  ⟨isFiniteType_of_localSpan M, localSpan_of_isFiniteType M⟩

/-! ### Stacks 01C4 in Mathlib's form -/

variable {Z : AlgebraicGeometry.RingedSpace.{u, u}}

/-- **Stacks 01C4, the direction that pushforward preserves finite type**, in Mathlib's form:
the direct image of a sheaf of modules of finite type along a closed embedding of ringed spaces
with surjective map on structure sheaves is of finite type. -/
theorem isFiniteType_modulePushforward_of_isFiniteType (i : Z ⟶ X)
    (hi : Topology.IsClosedEmbedding i.hom.base)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) i.hom.c]
    (F : SheafOfModules.{u} (structureSheafRing Z))
    (h : SheafOfModules.IsFiniteType (R := structureSheafRing Z) F) :
    SheafOfModules.IsFiniteType (R := structureSheafRing X)
      ((RingedSpaceModuleAdjunction.modulePushforward i).obj F) :=
  isFiniteType_of_localSpan _
    ((isFiniteType_modulePushforward_iff i hi ⟨F.val, F.isSheaf⟩).2
      (localSpan_of_isFiniteType F h))

/-- **Stacks 01C4, the direction that pushforward reflects finite type**, in Mathlib's form. -/
theorem isFiniteType_of_isFiniteType_modulePushforward (i : Z ⟶ X)
    (hi : Topology.IsClosedEmbedding i.hom.base)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) i.hom.c]
    (F : SheafOfModules.{u} (structureSheafRing Z))
    (h : SheafOfModules.IsFiniteType (R := structureSheafRing X)
      ((RingedSpaceModuleAdjunction.modulePushforward i).obj F)) :
    SheafOfModules.IsFiniteType (R := structureSheafRing Z) F :=
  isFiniteType_of_localSpan _
    ((isFiniteType_modulePushforward_iff i hi ⟨F.val, F.isSheaf⟩).1
      (localSpan_of_isFiniteType _ h))

/-- **Stacks 01C4** in Mathlib's form: pushforward along a closed embedding of ringed spaces with
surjective map on structure sheaves preserves and reflects finite type sheaves of modules. -/
theorem isFiniteType_modulePushforward_iff' (i : Z ⟶ X)
    (hi : Topology.IsClosedEmbedding i.hom.base)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) i.hom.c]
    (F : SheafOfModules.{u} (structureSheafRing Z)) :
    SheafOfModules.IsFiniteType (R := structureSheafRing X)
        ((RingedSpaceModuleAdjunction.modulePushforward i).obj F) ↔
      SheafOfModules.IsFiniteType (R := structureSheafRing Z) F :=
  ⟨isFiniteType_of_isFiniteType_modulePushforward i hi F,
    isFiniteType_modulePushforward_of_isFiniteType i hi F⟩

end Stacks.RingedSpace

end
