module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.ConstantModuleSheafSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExt

/-!
# Global sections of the extension by zero of a constant sheaf

Let `j : V ⟶ Y` be an open immersion with closed complement `i : W ⟶ Y`, and let `M` be a module.
If every nonempty clopen subset of `Y` meets `W`, then the sheaf `j_! j⁻¹ M_Y` on `Y_étale` has no
nonzero global section.

A global section of `j_! j⁻¹ M_Y` is a global section `s` of `M_Y` (extension by zero is a
subsheaf, Tag 095L) whose image under the unit `M_Y ⟶ i_* i⁻¹ M_Y` vanishes. The section `s` is a
locally constant function `φ : Y → M` (Tag 03P5). If `φ` takes a value `m ≠ 0`, the clopen subset
`Z = φ⁻¹(m)` meets `W`; over the open subscheme `Z` the section `s` is the constant section `m`,
and its image in `i⁻¹ M_Y = M_W` over `Z ×_Y W` is the constant section `m`, which is nonzero
since `Z ×_Y W` is nonempty.

## Main results

* `Stacks.EtaleCohomology.injective_unit_app_constantSheaf_terminal`: global sections of `M_Y`
  inject into those of `i_* i⁻¹ M_Y`.
* `Stacks.EtaleCohomology.isZero_extensionByZero_constant_terminal`: `j_! j⁻¹ M_Y` has no
  nonzero global section.

## References

* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5)
* [Stacks Project, Tag 095L](https://stacks.math.columbia.edu/tag/095L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [Ring Λ] {Y : Scheme.{u}} (M : ModuleCat.{u + 1} Λ)

/-- The final object `𝟙 Y` of the small étale site of `Y`. -/
abbrev smallEtaleIdObject (Y : Scheme.{u}) : Y.Etale :=
  MorphismProperty.Over.mk ⊤ (𝟙 Y) (by infer_instance)

/-- `𝟙 Y` is terminal in the small étale site of `Y`. -/
def isTerminalSmallEtaleIdObject (Y : Scheme.{u}) : IsTerminal (smallEtaleIdObject Y) := by
  letI : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    (HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
      RingHom.Etale.containsIdentities :
        MorphismProperty.IsMultiplicative
          (@Etale : MorphismProperty Scheme.{u})).toContainsIdentities
  exact MorphismProperty.Over.mkIdTerminal _ _

/-- The constant section `m` of `M_Y` over an étale `Y`-scheme `T`. -/
abbrev constModuleSection (T : Y.Etale) (m : M) :
    ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M).obj.obj (op T) :=
  ((toSheafify Y.smallEtaleTopology ((Functor.const (Y.Etale)ᵒᵖ).obj M)).app (op T)).hom m

/-- Restricting a constant section gives the constant section. -/
lemma map_constModuleSection {T T' : Y.Etale} (g : T' ⟶ T) (m : M) :
    (((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M).obj.map g.op).hom
      (constModuleSection Λ M T m) = constModuleSection Λ M T' m :=
  (ConcreteCategory.congr_hom
    ((toSheafify Y.smallEtaleTopology ((Functor.const (Y.Etale)ᵒᵖ).obj M)).naturality g.op) m).symm

/-- The comparison with locally constant maps sends a constant section to a constant map. -/
lemma lc_constModuleSection (T : Y.Etale) (m : M) :
    ((constantSheafToSmallEtaleLocallyConstantMapsModule.{u, 0} Λ Y M).hom.app (op T)).hom
      (constModuleSection Λ M T m) = LocallyConstant.const T.left m :=
  constantSheafToSmallEtaleLocallyConstantMapsModule_unit.{u, 0} Λ Y M (op T) m

/-- A section whose locally constant map is constant is the constant section. -/
lemma eq_constModuleSection_of_lc_eq (T : Y.Etale) (m : M)
    (s : ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M).obj.obj (op T))
    (hs : ((constantSheafToSmallEtaleLocallyConstantMapsModule.{u, 0} Λ Y M).hom.app (op T)).hom s =
      LocallyConstant.const T.left m) :
    s = constModuleSection Λ M T m :=
  (ConcreteCategory.bijective_of_isIso
    ((constantSheafToSmallEtaleLocallyConstantMapsModule.{u, 0} Λ Y M).hom.app (op T))).1
      (hs.trans (lc_constModuleSection Λ M T m).symm)

/-- A nonzero constant section over a nonempty étale scheme is nonzero. -/
lemma constModuleSection_ne_zero (T : Y.Etale) [Nonempty T.left] {m : M} (hm : m ≠ 0) :
    constModuleSection Λ M T m ≠ 0 := by
  intro h
  have h' := lc_constModuleSection Λ M T m
  rw [h, map_zero] at h'
  obtain ⟨t⟩ := ‹Nonempty T.left›
  exact hm (congrArg (fun f : LocallyConstant T.left M => f t) h').symm

/-- The constant section over the final object is the unit of the constant sheaf adjunction. -/
lemma constantSheafAdj_unit_app_apply (T : Y.Etale) (hT : IsTerminal T) (m : M) :
    ((constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT).unit.app M).hom m =
      constModuleSection Λ M T m :=
  rfl

variable {W : Scheme.{u}} (i : W ⟶ Y)

/-- **The unit of `i⁻¹ ⊣ i_*` on a constant section over the final object**, read through
`i⁻¹ M_Y ≅ M_W`, is the constant section over the final object of `W_étale`. -/
lemma inverseImageConstantIso_unit_constModuleSection (m : M) :
    (((etaleModuleInverseImageConstantIso.{u, 0} Λ i).hom.app M).hom.app
        (op ((smallEtaleBaseChange i).obj (smallEtaleIdObject Y)))).hom
      ((((etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).hom.app
          (op (smallEtaleIdObject Y))).hom (constModuleSection Λ M (smallEtaleIdObject Y) m)) =
      constModuleSection Λ M ((smallEtaleBaseChange i).obj (smallEtaleIdObject Y)) m := by
  let hT := isTerminalSmallEtaleIdObject Y
  exact ConcreteCategory.congr_hom (Adjunction.unit_leftAdjointUniq_hom_app
    ((constantSheafAdj _ _ hT).comp (etaleModuleInverseImageAdj.{u, 0} Λ i))
    (constantSheafAdj _ _ (hT.isTerminalObj (smallEtaleBaseChange i))) M) m

/-- The unit of `i⁻¹ ⊣ i_*` on a constant section over any étale `Y`-scheme `T`, read through
`i⁻¹ M_Y ≅ M_W`, is the constant section over `T ×_Y W`. -/
private lemma inverseImageConstantIso_unit_constModuleSection_app (T : Y.Etale) (m : M) :
    (((etaleModuleInverseImageConstantIso.{u, 0} Λ i).hom.app M).hom.app
        (op ((smallEtaleBaseChange i).obj T))).hom
      ((((etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).hom.app (op T)).hom
          (constModuleSection Λ M T m)) =
      constModuleSection Λ M ((smallEtaleBaseChange i).obj T) m := by
  let g : T ⟶ smallEtaleIdObject Y := (isTerminalSmallEtaleIdObject Y).from T
  have h1 : (((etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).hom.app (op T)).hom
        (constModuleSection Λ M T m) =
      (((etaleModuleInverseImage.{u, 0} Λ i).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).obj.map
          ((smallEtaleBaseChange i).map g).op).hom
        ((((etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).hom.app
            (op (smallEtaleIdObject Y))).hom
              (constModuleSection Λ M (smallEtaleIdObject Y) m)) := by
    rw [← map_constModuleSection Λ M g m]
    exact ConcreteCategory.congr_hom (((etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).hom.naturality g.op)
        (constModuleSection Λ M (smallEtaleIdObject Y) m)
  rw [h1]
  have hι := ConcreteCategory.congr_hom
    (((etaleModuleInverseImageConstantIso.{u, 0} Λ i).hom.app M).hom.naturality
      ((smallEtaleBaseChange i).map g).op)
    ((((etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).hom.app
        (op (smallEtaleIdObject Y))).hom (constModuleSection Λ M (smallEtaleIdObject Y) m))
  refine hι.trans ?_
  exact (congrArg (fun x => (((constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
    M).obj.map ((smallEtaleBaseChange i).map g).op).hom x)
      (inverseImageConstantIso_unit_constModuleSection Λ M i m)).trans
        (map_constModuleSection Λ M _ m)

/-- The base change `T ×_Y W` is nonempty when the image of `T` meets the image of `i`. -/
private lemma nonempty_smallEtaleBaseChange_obj_left_of_mem_range (T : Y.Etale) {w : W}
    (hw : i w ∈ Set.range T.hom.base) : Nonempty ((smallEtaleBaseChange i).obj T).left := by
  rw [← not_isEmpty_iff]
  show ¬ IsEmpty ↥(Limits.pullback (T.hom : T.left ⟶ Y) i)
  rw [Scheme.isEmpty_pullback_iff, Set.not_disjoint_iff]
  exact ⟨i w, hw, ⟨w, rfl⟩⟩

/-- **Global sections of `M_Y` inject into those of `i_* i⁻¹ M_Y`** when every nonempty clopen
subset of `Y` meets the image of `i`. -/
theorem injective_unit_app_constantSheaf_smallEtaleIdObject
    (hY : ∀ Z : Set Y, IsClopen Z → Z.Nonempty → ∃ w : W, i w ∈ Z) :
    Function.Injective (((etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).hom.app
        (op (smallEtaleIdObject Y))).hom := by
  let e := constantSheafToSmallEtaleLocallyConstantMapsModule.{u, 0} Λ Y M
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine (ConcreteCategory.bijective_of_isIso (e.hom.app (op (smallEtaleIdObject Y)))).1 ?_
  rw [map_zero]
  show ((e.hom.app (op (smallEtaleIdObject Y))).hom s :
    LocallyConstant (smallEtaleIdObject Y).left M) = 0
  refine LocallyConstant.ext fun y => ?_
  by_contra hm
  set φ : LocallyConstant (smallEtaleIdObject Y).left M :=
    (e.hom.app (op (smallEtaleIdObject Y))).hom s with hφ
  set m := φ y with hmdef
  have hZ : IsClopen {x | φ x = m} := φ.isLocallyConstant.isClopen_fiber m
  obtain ⟨w, hw⟩ := hY {x | φ x = m} hZ ⟨y, rfl⟩
  let O : Y.Opens := ⟨{x | φ x = m}, hZ.isOpen⟩
  let TO : Y.Etale := MorphismProperty.Over.mk ⊤ O.ι (by infer_instance)
  let g : TO ⟶ smallEtaleIdObject Y := (isTerminalSmallEtaleIdObject Y).from TO
  have hsO : (((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M).obj.map g.op).hom
      s = constModuleSection Λ M TO m := by
    refine eq_constModuleSection_of_lc_eq Λ M TO m _ ?_
    refine (ConcreteCategory.congr_hom (e.hom.naturality g.op) s).trans ?_
    exact LocallyConstant.ext fun p => p.2
  have h0 : (((etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).hom.app (op TO)).hom
        (constModuleSection Λ M TO m) = 0 := by
    rw [← hsO]
    refine (ConcreteCategory.congr_hom (((etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).hom.naturality g.op)
        s).trans ?_
    exact (congrArg (fun x => ((((etaleModuleDirectImage.{u, 0} Λ i).obj
      ((etaleModuleInverseImage.{u, 0} Λ i).obj ((constantSheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj M))).obj.map g.op).hom x)) hs).trans (map_zero _)
  have := nonempty_smallEtaleBaseChange_obj_left_of_mem_range i TO
    (show i w ∈ Set.range TO.hom.base from ⟨⟨i w, hw⟩, rfl⟩)
  have hm0 : m ≠ 0 := hm
  refine constModuleSection_ne_zero Λ M ((smallEtaleBaseChange i).obj TO) hm0
    ((inverseImageConstantIso_unit_constModuleSection_app Λ M i TO m).symm.trans ?_)
  rw [h0]
  exact map_zero _

/-- **`j_! j⁻¹ M_Y` has no nonzero global section** when `j` is an open immersion with closed
complement `i` and every nonempty clopen subset of `Y` meets that complement. -/
theorem isZero_extensionByZero_constant_smallEtaleIdObject {V : Scheme.{u}} (j : V ⟶ Y)
    [IsOpenImmersion j] [IsClosedImmersion i] (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (hY : ∀ Z : Set Y, IsClopen Z → Z.Nonempty → ∃ w : W, i w ∈ Z) :
    IsZero (((etaleModuleExtensionByZero.{u, 0} Λ j).obj ((etaleModuleRestriction.{u, 0} Λ j).obj
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))).obj.obj
        (op (smallEtaleIdObject Y))) := by
  obtain ⟨h, hS⟩ := shortExact_etaleModuleExtensionByZero_directImage.{u, 0} Λ i j hij
    ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
  have := hS.mono_f
  let ev :=
    (sheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op (smallEtaleIdObject Y))
  have : ev.IsRightAdjoint := (constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (isTerminalSmallEtaleIdObject Y)).isRightAdjoint
  have hm : Mono (ev.map ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).counit.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) := inferInstance
  have hinj := (ModuleCat.mono_iff_injective _).1 hm
  have hcomp := congrArg ev.map h
  rw [Functor.map_comp, Functor.map_zero] at hcomp
  refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun a b => hinj ?_⟩
  apply injective_unit_app_constantSheaf_smallEtaleIdObject Λ M i hY
  have ha := ConcreteCategory.congr_hom hcomp a
  have hb := ConcreteCategory.congr_hom hcomp b
  simp only [ConcreteCategory.comp_apply] at ha hb
  exact ha.trans hb.symm

end Stacks.EtaleCohomology

end
