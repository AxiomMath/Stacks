module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.InverseImageSectionsColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageDimensionShift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SystemPullbackDiagram
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SystemColimitSections

/-!
# Sections of the colimit of a system of étale sheaves over a limit of schemes

Let `X = lim X_i` be the limit of a directed inverse system of schemes with affine transition
morphisms, let `(F_i, φ_{i'i})` be a system of abelian sheaves on the small étale sites of the
`X_i` ([Stacks, Tag 0EZL]) and let `𝓖 = colim f_i⁻¹F_i` on the small
étale site of `X`. For an object `V₀` of the small étale site of a stage `X_{i₀}` whose underlying
scheme is quasi-compact and quasi-separated, with base changes `V_k = V₀ ×_{X_{i₀}} X_k` and
`V = V₀ ×_{X_{i₀}} X`,

`𝓖(V) = colim_{k ≥ i₀} F_k(V_k)`.

This is the degree zero case of [Stacks, Tag 09YQ] over the object `V₀`, which in the source is
[Stacks, Tag 09YN] applied to the colimit of sites of [Stacks, Tag 0EYL]. It is stated here
elementwise, with the maps of the colimit given by sheaf maps on the small étale site of `X_{i₀}`:
the legs `F_k(V_k) ⟶ 𝓖(V)` are the components at `V₀` of the maps
`f_{k i₀,*}F_k ⟶ f_{i₀,*}𝓖` adjoint to the maps `f_k⁻¹F_k ⟶ 𝓖`, and the transition maps
`F_k(V_k) ⟶ F_l(V_l)` are the components of the direct images of the transition maps of the
system.

## Main definitions

* `Stacks.EtaleCohomology.EtaleSheafSystem.pushforwardLeg`: the map `f_{k i₀,*}F_k ⟶ f_{i₀,*}𝓖`.
* `Stacks.EtaleCohomology.EtaleSheafSystem.pushforwardTransition`: the map
  `f_{k i₀,*}F_k ⟶ f_{l i₀,*}F_l`.
* `Stacks.EtaleCohomology.EtaleSheafSystem.pushforwardUnit`: the map
  `f_{k i₀,*}F_k ⟶ f_{i₀,*}f_k⁻¹F_k` through which the leg factors.

## Main results

* `Stacks.EtaleCohomology.EtaleSheafSystem.exists_pushforwardLeg_apply_eq`: every section of `𝓖`
  over `V` comes from a stage.
* `Stacks.EtaleCohomology.EtaleSheafSystem.exists_pushforwardTransition_apply_eq_zero`: a section
  of a stage whose image in `𝓖(V)` vanishes dies at a later stage.

## Implementation notes

The proof is the source's two-step colimit argument. The sections over `V` of the colimit
`𝓖 = colim_k f_k⁻¹F_k` of sheaves on `X` are the colimit of the sections of the `f_k⁻¹F_k` over
`V` (Stacks 0739 in degree zero, `isSystemColimit_sections_of_isSystemColimit`), and the sections
over `V` of a single inverse image `f_k⁻¹F_k` are the colimit of the sections of the
`f_{lk}⁻¹F_k` over `V_l` (Stacks 09YN for one sheaf, `exists_pullbackSectionsMap_eq_of_isLimit`
and `exists_unitApp_eq_zero_of_isLimit`). The transition maps `f_{lk}⁻¹F_k ⟶ F_l` of the system
then carry the second colimit to the colimit of the `F_l(V_l)`.

## References

* [Stacks Project, Tag 09YN](https://stacks.math.columbia.edu/tag/09YN)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- Being quasi-compact and separated over the base is stable under base change. -/
lemma smallEtaleBaseChange_obj_mem_qcSeparatedOver {X Y : Scheme.{u}} (f : Y ⟶ X) {V : X.Etale}
    (hV : V ∈ qcSeparatedOver X) : (smallEtaleBaseChange f).obj V ∈ qcSeparatedOver Y := by
  obtain ⟨_, _⟩ := hV
  exact ⟨MorphismProperty.of_isPullback (IsPullback.of_hasPullback V.hom f) inferInstance,
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback V.hom f) inferInstance⟩

variable {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} (c : Cone D)

namespace EtaleSheafSystem

variable (F : EtaleSheafSystem D Ab.{u + 1}) {𝓖 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}}
  (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓖)

/-- The leg `f_{k i₀,*}F_k ⟶ f_{i₀,*}𝓖` on the small étale site of `X_{i₀}`: the direct image of
the map `F_k ⟶ f_{k,*}𝓖` adjoint to `ι_k`, followed by `f_{k i₀,*}f_{k,*} = f_{i₀,*}`. -/
def pushforwardLeg {k i₀ : Iᵒᵖ} (a : k ⟶ i₀) :
    (systemPushforward D Ab.{u + 1} a).obj (F.obj k) ⟶
      (smallEtalePushforwardAb (c.π.app i₀)).obj 𝓖 :=
  (systemPushforward D Ab.{u + 1} a).map
      ((smallEtaleAdjunctionAb (c.π.app k)).homEquiv _ _ (ι k)) ≫
    (coneDirectImageCompAb c a).hom.app 𝓖

/-- The transition `f_{k i₀,*}F_k ⟶ f_{l i₀,*}F_l` on the small étale site of `X_{i₀}`: the
direct image of the transition map of the system in adjoint form, followed by
`f_{k i₀,*}f_{l k,*} = f_{l i₀,*}`. -/
def pushforwardTransition {l k i₀ : Iᵒᵖ} (b : l ⟶ k) (a : k ⟶ i₀) :
    (systemPushforward D Ab.{u + 1} a).obj (F.obj k) ⟶
      (systemPushforward D Ab.{u + 1} (b ≫ a)).obj (F.obj l) :=
  (systemPushforward D Ab.{u + 1} a).map (F.transition b) ≫
    (systemPushforwardComp D Ab.{u + 1} b a).hom.app (F.obj l)

/-- The component of the leg at an object, on sections: the image of a section under the unit,
mapped by `ι_k`, and restricted along the comparison of the base changes. -/
lemma pushforwardLeg_app_apply {k i₀ : Iᵒᵖ} (a : k ⟶ i₀) (V₀ : (D.obj i₀).Etale)
    (x : ToType ((F.obj k).obj.obj (op ((smallEtaleBaseChange (D.map a)).obj V₀)))) :
    (F.pushforwardLeg c ι a).hom.app (op V₀) x =
      𝓖.obj.map ((smallEtaleBaseChangeComp' (c.π.app k) (D.map a) (c.π.app i₀)
          (c.w a).symm).hom.app V₀).op
        ((ι k).hom.app _ (smallEtalePullbackAbUnitApp (c.π.app k) (F.obj k) _ x)) := by
  rfl

/-- The component of the transition at an object, on sections. -/
lemma pushforwardTransition_app_apply {l k i₀ : Iᵒᵖ} (b : l ⟶ k) (a : k ⟶ i₀)
    (V₀ : (D.obj i₀).Etale)
    (x : ToType ((F.obj k).obj.obj (op ((smallEtaleBaseChange (D.map a)).obj V₀)))) :
    (F.pushforwardTransition b a).hom.app (op V₀) x =
      (F.obj l).obj.map ((smallEtaleBaseChangeComp' (D.map b) (D.map a) (D.map (b ≫ a))
          (D.map_comp b a)).hom.app V₀).op
        ((F.map b).hom.app _ (smallEtalePullbackAbUnitApp (D.map b) (F.obj k) _ x)) := by
  rfl


/-- The map `f_{k i₀,*}F_k ⟶ f_{i₀,*}f_k⁻¹F_k` on the small étale site of `X_{i₀}`: the direct
image of the unit of `f_k⁻¹ ⊣ f_{k,*}`, followed by `f_{k i₀,*}f_{k,*} = f_{i₀,*}`. -/
def pushforwardUnit {k i₀ : Iᵒᵖ} (a : k ⟶ i₀) :
    (systemPushforward D Ab.{u + 1} a).obj (F.obj k) ⟶
      (smallEtalePushforwardAb (c.π.app i₀)).obj
        ((smallEtalePullbackAb (c.π.app k)).obj (F.obj k)) :=
  (systemPushforward D Ab.{u + 1} a).map
      ((smallEtaleAdjunctionAb (c.π.app k)).unit.app (F.obj k)) ≫
    (coneDirectImageCompAb c a).hom.app _

/-- The component of `pushforwardUnit` at an object, on sections. -/
lemma pushforwardUnit_app_apply {k i₀ : Iᵒᵖ} (a : k ⟶ i₀) (V₀ : (D.obj i₀).Etale)
    (x : ToType ((F.obj k).obj.obj (op ((smallEtaleBaseChange (D.map a)).obj V₀)))) :
    (F.pushforwardUnit c a).hom.app (op V₀) x =
      ((smallEtalePullbackAb (c.π.app k)).obj (F.obj k)).obj.map
        ((smallEtaleBaseChangeComp' (c.π.app k) (D.map a) (c.π.app i₀)
          (c.w a).symm).hom.app V₀).op
        (smallEtalePullbackAbUnitApp (c.π.app k) (F.obj k) _ x) := by
  rfl

/-- The leg `f_{k i₀,*}F_k ⟶ f_{i₀,*}𝓖` factors through `f_{i₀,*}f_k⁻¹F_k`. -/
lemma pushforwardUnit_comp_map {k i₀ : Iᵒᵖ} (a : k ⟶ i₀) :
    F.pushforwardUnit c a ≫ (smallEtalePushforwardAb (c.π.app i₀)).map (ι k) =
      F.pushforwardLeg c ι a := by
  rw [pushforwardUnit, pushforwardLeg, Adjunction.homEquiv_unit, Functor.map_comp,
    Category.assoc, Category.assoc]
  congr 1
  exact ((coneDirectImageCompAb c a).hom.naturality (ι k)).symm

/-- **The units of the inverse images intertwine the transition maps of a system** with the maps
of the diagram of its inverse images to the limit. -/
lemma pushforwardUnit_comp_map_pullbackDiagramMap {l k i₀ : Iᵒᵖ} (b : l ⟶ k) (a : k ⟶ i₀) :
    F.pushforwardUnit c a ≫
        (smallEtalePushforwardAb (c.π.app i₀)).map (F.pullbackDiagramMap c (i := l) (j := k) b) =
      F.pushforwardTransition b a ≫ F.pushforwardUnit c (b ≫ a) := by
  have hcoc := congrArg
    (fun z => NatTrans.app (Iso.hom z) ((smallEtalePullbackAb (c.π.app l)).obj (F.obj l)))
    (smallEtalePushforwardComp'_assoc (c.π.app l) (D.map b) (D.map a) (c.π.app k) (c.w b).symm
      (D.map (b ≫ a)) (D.map_comp b a) (c.π.app i₀) (c.w a).symm (c.w (b ≫ a)).symm Ab.{u + 1})
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at hcoc
  have hu : (smallEtaleAdjunctionAb (c.π.app k)).unit.app (F.obj k) ≫
      (smallEtalePushforwardAb (c.π.app k)).map (F.pullbackDiagramMap c (i := l) (j := k) b) =
      F.transition b ≫ (systemPushforward D Ab.{u + 1} b).map
          ((smallEtaleAdjunctionAb (c.π.app l)).unit.app (F.obj l)) ≫
            (coneDirectImageCompAb c b).hom.app _ :=
    ((smallEtaleAdjunctionAb (c.π.app k)).homEquiv_unit _ _ _).symm.trans
      (by rw [F.pullbackDiagramMap_eq c b]; exact Equiv.apply_symm_apply _ _)
  calc _ = (systemPushforward D Ab.{u + 1} a).map
          ((smallEtaleAdjunctionAb (c.π.app k)).unit.app (F.obj k) ≫
            (smallEtalePushforwardAb (c.π.app k)).map
              (F.pullbackDiagramMap c (i := l) (j := k) b)) ≫
          (coneDirectImageCompAb c a).hom.app _ := by
        rw [pushforwardUnit, Category.assoc, Functor.map_comp, Category.assoc]
        congr 1
        exact ((coneDirectImageCompAb c a).hom.naturality _).symm
    _ = _ := by
        rw [hu, pushforwardTransition, pushforwardUnit, Functor.map_comp, Functor.map_comp,
          Category.assoc, Category.assoc, Category.assoc]
        congr 1
        rw [← reassoc_of% ((systemPushforwardComp D Ab.{u + 1} b a).hom.naturality
          ((smallEtaleAdjunctionAb (c.π.app l)).unit.app (F.obj l)))]
        congr 1

/-- **The transition maps pushed to a stage compose.** -/
lemma pushforwardTransition_comp {m l k i₀ : Iᵒᵖ} (e : m ⟶ l) (b : l ⟶ k) (a : k ⟶ i₀) :
    F.pushforwardTransition b a ≫ F.pushforwardTransition e (b ≫ a) =
      F.pushforwardTransition (e ≫ b) a := by
  have hcoc := congrArg (fun z => NatTrans.app (Iso.hom z) (F.obj m))
    (smallEtalePushforwardComp'_assoc (D.map e) (D.map b) (D.map a) (D.map (e ≫ b))
      (D.map_comp e b) (D.map (b ≫ a)) (D.map_comp b a) (D.map ((e ≫ b) ≫ a))
      (D.map_comp (e ≫ b) a) (D.map_comp e (b ≫ a)) Ab.{u + 1})
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at hcoc
  rw [pushforwardTransition, pushforwardTransition, pushforwardTransition, F.transition_comp e b,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, Category.assoc]
  congr 1
  rw [← reassoc_of% ((systemPushforwardComp D Ab.{u + 1} b a).hom.naturality (F.transition e)),
    Category.assoc]
  congr 1
  exact hcoc.symm

/-- The maps of the diagram of inverse images to the limit are compatible with the legs `ι`. -/
private lemma pullbackDiagramMap_comp_ι
    (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), (conePullbackComp c a).inv.app (F.obj j) ≫
      (smallEtalePullbackAb (c.π.app i)).map (F.map a) ≫ ι i = ι j) {i j : Iᵒᵖ} (a : i ⟶ j) :
    F.pullbackDiagramMap c (i := i) (j := j) a ≫ ι i = ι j :=
  (Category.assoc _ _ _).trans (hι a)

end EtaleSheafSystem


/-! ### The degree zero colimit -/

section DegreeZero

variable [IsDirected I (· ≤ ·)] [Nonempty I] [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]

/-- The unit of the inverse image along `f` is natural in the sheaf, on sections. -/
lemma smallEtalePullbackAbUnitApp_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : Sheaf (smallEtaleTopology Y) Ab.{u + 1}} (φ : A ⟶ B) (U : Y.Etale)
    (h : ToType (A.obj.obj (op U))) :
    smallEtalePullbackAbUnitApp f B U (φ.hom.app (op U) h) =
      ((smallEtalePullbackAb f).map φ).hom.app _ (smallEtalePullbackAbUnitApp f A U h) := by
  have := congrArg (fun ψ => ψ.hom.app (op U) h) ((smallEtaleAdjunctionAb f).unit.naturality φ)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply] at this
  exact this

/-- The base change to the limit of a quasi-compact and quasi-separated object of a stage has
quasi-compact and quasi-separated underlying scheme, the projections being affine. -/
lemma mem_qcqsEtaleObjects_smallEtaleBaseChange_obj (hc : IsLimit c) {i₀ : Iᵒᵖ}
    (V₀ : (D.obj i₀).Etale) [CompactSpace V₀.left] [QuasiSeparatedSpace V₀.left] :
    (smallEtaleBaseChange (c.π.app i₀)).obj V₀ ∈ qcqsEtaleObjects c.pt := by
  have := isAffineHom_π_app D c hc i₀
  exact ⟨compactSpace_smallEtaleBaseChange_obj (c.π.app i₀) V₀ inferInstance,
    quasiSeparatedSpace_smallEtaleBaseChange_obj (c.π.app i₀) V₀ inferInstance⟩

variable (hc : IsLimit c) (F : EtaleSheafSystem D Ab.{u + 1})
  {𝓖 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}}
  (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓖)
  (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), (conePullbackComp c a).inv.app (F.obj j) ≫
    (smallEtalePullbackAb (c.π.app i)).map (F.map a) ≫ ι i = ι j)
  (hpres : LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓖 F ι)

/-- The sections over the base change of a quasi-compact separated object form a system colimit. -/
private lemma EtaleSheafSystem.isSystemColimit_sections_pullbackDiagram (hc : IsLimit c)
    (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), (conePullbackComp c a).inv.app (F.obj j) ≫
      (smallEtalePullbackAb (c.π.app i)).map (F.map a) ≫ ι i = ι j)
    (hpres : LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓖 F ι) {i₀ : Iᵒᵖ}
    (V₀ : (D.obj i₀).Etale) [CompactSpace V₀.left] [QuasiSeparatedSpace V₀.left] :
    IsSystemColimit
      (fun i => ((sheafSections (smallEtaleTopology c.pt) Ab.{u + 1}).obj
        (op ((smallEtaleBaseChange (c.π.app i₀)).obj V₀))).obj
          ((smallEtalePullbackAb (c.π.app i)).obj (F.obj i)))
      (fun a => ((sheafSections (smallEtaleTopology c.pt) Ab.{u + 1}).obj
        (op ((smallEtaleBaseChange (c.π.app i₀)).obj V₀))).map
          (F.pullbackDiagramMap c a))
      (((sheafSections (smallEtaleTopology c.pt) Ab.{u + 1}).obj
        (op ((smallEtaleBaseChange (c.π.app i₀)).obj V₀))).obj 𝓖)
      (fun i => ((sheafSections (smallEtaleTopology c.pt) Ab.{u + 1}).obj
        (op ((smallEtaleBaseChange (c.π.app i₀)).obj V₀))).map (ι i)) :=
  isSystemColimit_sections_of_isSystemColimit (fun a b => F.pullbackDiagramMap_comp c a b)
    (fun a => F.pullbackDiagramMap_comp_ι c ι hι a) hpres _
    (mem_qcqsEtaleObjects_smallEtaleBaseChange_obj c hc V₀)

include hc hι hpres in
/-- **Every section of the colimit over the base change of a quasi-compact separated object comes
from a stage** (the surjectivity half of the degree zero case of Stacks 09YQ). -/
theorem EtaleSheafSystem.exists_pushforwardLeg_apply_eq {i₀ : Iᵒᵖ} (V₀ : (D.obj i₀).Etale)
    [CompactSpace V₀.left] [QuasiSeparatedSpace V₀.left]
    (s : ToType (𝓖.obj.obj (op ((smallEtaleBaseChange (c.π.app i₀)).obj V₀)))) :
    ∃ (k : Iᵒᵖ) (a : k ⟶ i₀)
      (x : ToType ((F.obj k).obj.obj (op ((smallEtaleBaseChange (D.map a)).obj V₀)))),
      (F.pushforwardLeg c ι a).hom.app (op V₀) x = s := by
  let V := (smallEtaleBaseChange (c.π.app i₀)).obj V₀
  have hsec := F.isSystemColimit_sections_pullbackDiagram c ι hc hι hpres V₀
  obtain ⟨j₁, y, hy⟩ := hsec.exists_eq
    (fun a b => by rw [F.pullbackDiagramMap_comp c, Functor.map_comp])
    (fun a => by rw [← Functor.map_comp, F.pullbackDiagramMap_comp_ι c ι hι]) s
  obtain ⟨j, h₁, h₂⟩ := directed_of (· ≤ ·) j₁.unop i₀.unop
  let b₁ : Opposite.op j ⟶ j₁ := (homOfLE h₁).op
  let a : Opposite.op j ⟶ i₀ := (homOfLE h₂).op
  let y₂ := (F.pullbackDiagramMap c (i := Opposite.op j) (j := j₁) b₁).hom.app (op V) y
  have hy₂ : (ι (Opposite.op j)).hom.app (op V) y₂ = s :=
    (congrArg (fun φ => φ.hom.app (op V) y) (F.pullbackDiagramMap_comp_ι c ι hι b₁)).trans hy
  let W := (smallEtaleBaseChange (D.map a)).obj V₀
  let ε := (smallEtaleBaseChangeComp' (c.π.app (Opposite.op j)) (D.map a) (c.π.app i₀)
    (c.w a).symm).app V₀
  let y₃ := ((smallEtalePullbackAb (c.π.app (Opposite.op j))).obj (F.obj (Opposite.op j))).obj.map
    ε.inv.op y₂
  have : CompactSpace W.left := compactSpace_smallEtaleBaseChange_obj (D.map a) V₀ inferInstance
  have : QuasiSeparatedSpace W.left :=
    quasiSeparatedSpace_smallEtaleBaseChange_obj (D.map a) V₀ inferInstance
  obtain ⟨k, b, t, ht⟩ := exists_pullbackSectionsMap_eq_of_isLimit hc (F.obj (Opposite.op j)) W y₃
  let C2 := smallEtaleBaseChangeComp' (D.map b) (D.map a) (D.map (b ≫ a)) (D.map_comp b a)
  let C3 := smallEtaleBaseChangeComp' (c.π.app k) (D.map b) (c.π.app (Opposite.op j)) (c.w b).symm
  let C := smallEtaleBaseChangeComp' (c.π.app k) (D.map (b ≫ a)) (c.π.app i₀) (c.w (b ≫ a)).symm
  let W' := (smallEtaleBaseChange (D.map b)).obj W
  let c2 : (smallEtaleBaseChange (D.map (b ≫ a))).obj V₀ ⟶ W' := C2.hom.app V₀
  refine ⟨k, b ≫ a, (F.obj k).obj.map c2.op ((F.map b).hom.app _ t), ?_⟩
  -- the comparison of the two ways of reaching `V`
  have hmor : C.hom.app V₀ ≫ (smallEtaleBaseChange (c.π.app k)).map c2 =
      ε.hom ≫ C3.hom.app W := by
    have h := NatTrans.congr_app (smallEtaleBaseChangeComp'_assoc (c.π.app k) (D.map b) (D.map a)
      (c.π.app (Opposite.op j)) (c.w b).symm (D.map (b ≫ a)) (D.map_comp b a) (c.π.app i₀)
      (c.w a).symm (c.w (b ≫ a)).symm) V₀
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_inv_app, Category.comp_id] at h
    exact h
  -- the sections
  let O2 := (smallEtaleBaseChange (c.π.app k)).obj W'
  let Gk := (smallEtalePullbackAb (c.π.app k)).obj (F.obj k)
  let Gj := (smallEtalePullbackAb (c.π.app (Opposite.op j))).obj (F.obj (Opposite.op j))
  let M := (smallEtaleBaseChange (c.π.app k)).map c2
  let ψt := pullbackSectionsMap (c.π.app k) (D.map b) (c.π.app (Opposite.op j)) (c.w b).symm
    (F.obj (Opposite.op j)) W' t
  have hιb : (smallEtalePullbackAbComp' (c.π.app k) (D.map b) (c.π.app (Opposite.op j))
        (c.w b).symm).hom.app (F.obj (Opposite.op j)) ≫ ι (Opposite.op j) =
      (smallEtalePullbackAb (c.π.app k)).map (F.map b) ≫ ι k := by
    rw [← conePullbackComp_eq, ← hι b, Iso.hom_inv_id_app_assoc]
  have e : (ι k).hom.app (op O2) (((smallEtalePullbackAb (c.π.app k)).map (F.map b)).hom.app
      (op O2) (smallEtalePullbackAbUnitApp (c.π.app k) _ W' t)) =
        (ι (Opposite.op j)).hom.app (op O2) ψt :=
    (congrArg (fun φ => φ.hom.app (op O2) (smallEtalePullbackAbUnitApp (c.π.app k) _ W' t))
      hιb).symm
  have hιn : ∀ (i : Iᵒᵖ) {O O' : c.pt.Etale} (g : O ⟶ O')
      (z : ToType (((smallEtalePullbackAb (c.π.app i)).obj (F.obj i)).obj.obj (op O'))),
      (ι i).hom.app (op O) (((smallEtalePullbackAb (c.π.app i)).obj (F.obj i)).obj.map g.op z) =
        𝓖.obj.map g.op ((ι i).hom.app (op O') z) :=
    fun i _ _ g z => congrArg (fun φ => φ z) ((ι i).hom.naturality g.op)
  let c3 : (smallEtaleBaseChange (c.π.app (Opposite.op j))).obj W ⟶ O2 := C3.hom.app W
  have hmor' : C.hom.app V₀ ≫ M = ε.hom ≫ c3 := hmor
  have ht' : Gj.obj.map c3.op ψt = y₃ := ht
  have hy₃ : Gj.obj.map ε.hom.op y₃ = y₂ := by
    show Gj.obj.map ε.hom.op (Gj.obj.map ε.inv.op y₂) = y₂
    rw [presheaf_map_map_apply, Iso.hom_inv_id, op_id, CategoryTheory.Functor.map_id,
      ConcreteCategory.id_apply]
  calc _ = 𝓖.obj.map (C.hom.app V₀).op ((ι k).hom.app _ (Gk.obj.map M.op
          (((smallEtalePullbackAb (c.π.app k)).map (F.map b)).hom.app (op O2)
            (smallEtalePullbackAbUnitApp (c.π.app k) _ W' t)))) := by
        rw [pushforwardLeg_app_apply, smallEtalePullbackAbUnitApp_naturality,
          smallEtalePullbackAbUnitApp_map]
    _ = 𝓖.obj.map (C.hom.app V₀).op (𝓖.obj.map M.op ((ι (Opposite.op j)).hom.app _ ψt)) := by
        rw [hιn k, e]
    _ = 𝓖.obj.map ε.hom.op (𝓖.obj.map c3.op ((ι (Opposite.op j)).hom.app (op O2) ψt)) := by
        rw [presheaf_map_map_apply, presheaf_map_map_apply, hmor']
    _ = 𝓖.obj.map ε.hom.op ((ι (Opposite.op j)).hom.app _ y₃) :=
        congrArg (𝓖.obj.map ε.hom.op) ((hιn _ c3 ψt).symm.trans
          (congrArg ((ι (Opposite.op j)).hom.app _) ht'))
    _ = s :=
        (hιn _ ε.hom y₃).symm.trans ((congrArg ((ι (Opposite.op j)).hom.app (op V)) hy₃).trans hy₂)

include hι in
/-- The legs `f_{k i₀,*}F_k ⟶ f_{i₀,*}𝓖` are compatible with the transition maps. -/
lemma EtaleSheafSystem.pushforwardTransition_comp_pushforwardLeg {l k i₀ : Iᵒᵖ} (b : l ⟶ k)
    (a : k ⟶ i₀) :
    F.pushforwardTransition b a ≫ F.pushforwardLeg c ι (b ≫ a) = F.pushforwardLeg c ι a := by
  rw [← F.pushforwardUnit_comp_map c ι (b ≫ a), ← Category.assoc,
    ← F.pushforwardUnit_comp_map_pullbackDiagramMap c b a, Category.assoc, ← Functor.map_comp,
    F.pullbackDiagramMap_comp_ι c ι hι, F.pushforwardUnit_comp_map c ι a]

include hc hι hpres in
/-- **A section of a stage whose image in the colimit vanishes dies at a later stage** (the
injectivity half of the degree zero case of Stacks 09YQ). -/
theorem EtaleSheafSystem.exists_pushforwardTransition_apply_eq_zero {i₀ : Iᵒᵖ}
    (V₀ : (D.obj i₀).Etale) [CompactSpace V₀.left] [QuasiSeparatedSpace V₀.left] {k : Iᵒᵖ}
    (a : k ⟶ i₀) (x : ToType ((F.obj k).obj.obj (op ((smallEtaleBaseChange (D.map a)).obj V₀))))
    (hx : (F.pushforwardLeg c ι a).hom.app (op V₀) x = 0) :
    ∃ (l : Iᵒᵖ) (b : l ⟶ k), (F.pushforwardTransition b a).hom.app (op V₀) x = 0 := by
  have hsec := F.isSystemColimit_sections_pullbackDiagram c ι hc hι hpres V₀
  let u := (F.pushforwardUnit c a).hom.app (op V₀) x
  have hu : (ι k).hom.app (op ((smallEtaleBaseChange (c.π.app i₀)).obj V₀)) u = 0 :=
    (congrArg (fun φ => φ.hom.app (op V₀) x) (F.pushforwardUnit_comp_map c ι a)).trans hx
  obtain ⟨l, b, hb⟩ := hsec.exists_eq_zero
    (fun a b => by rw [F.pullbackDiagramMap_comp c, Functor.map_comp])
    (fun a => by rw [← Functor.map_comp, F.pullbackDiagramMap_comp_ι c ι hι]) u hu
  let z := (F.pushforwardTransition b a).hom.app (op V₀) x
  have hz : (F.pushforwardUnit c (b ≫ a)).hom.app (op V₀) z = 0 :=
    (congrArg (fun φ => φ.hom.app (op V₀) x)
      (F.pushforwardUnit_comp_map_pullbackDiagramMap c b a)).symm.trans hb
  let Gl := (smallEtalePullbackAb (c.π.app l)).obj (F.obj l)
  let ε := (smallEtaleBaseChangeComp' (c.π.app l) (D.map (b ≫ a)) (c.π.app i₀)
    (c.w (b ≫ a)).symm).app V₀
  have hz' : smallEtalePullbackAbUnitApp (c.π.app l) (F.obj l) _ z = 0 := by
    refine Eq.trans ?_ ((congrArg (Gl.obj.map ε.inv.op)
      ((F.pushforwardUnit_app_apply c (b ≫ a) V₀ z).symm.trans hz)).trans (map_zero _))
    show _ = Gl.obj.map ε.inv.op (Gl.obj.map ε.hom.op _)
    rw [presheaf_map_map_apply, Iso.inv_hom_id, op_id, CategoryTheory.Functor.map_id,
      ConcreteCategory.id_apply]
  have : CompactSpace ((smallEtaleBaseChange (D.map (b ≫ a))).obj V₀).left :=
    compactSpace_smallEtaleBaseChange_obj (D.map (b ≫ a)) V₀ inferInstance
  obtain ⟨m, e, he⟩ := exists_unitApp_eq_zero_of_isLimit D c hc (F.obj l) _ z hz'
  refine ⟨m, e ≫ b, ?_⟩
  rw [← F.pushforwardTransition_comp e b a]
  exact (F.pushforwardTransition_app_apply e (b ≫ a) V₀ z).trans
    (by rw [he, map_zero, map_zero]; rfl)

end DegreeZero

end Stacks.EtaleCohomology

end
