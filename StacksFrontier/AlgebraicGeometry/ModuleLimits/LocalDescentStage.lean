module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.LocalDescentGlue
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq

/-!
# Local descent data across the stages of the diagram, and on an overlap

Let `D` be a diagram of schemes and `c` a cone over it. A local descent datum over an open `V` of a
stage `i` transports along a morphism of stages over `i`. For a cofiltered diagram with affine
transition morphisms and a limit cone, two local descent data over opens `Va` and `Vb` of the stage
whose intersection is quasi-compact agree on the intersection at a later stage.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.stageTransport`: the transport of a local descent datum
  to a later stage of the diagram.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.localDescent_stageTransport`: the transported datum is
  again a local descent datum.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_stage_valSections_eq`: two local descent data over
  opens `Va` and `Vb` of a stage, with `Va ⊓ Vb` quasi-compact, have transports to a later stage
  with the same sections over every open contained in the preimages of both `Va` and `Vb`.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

section Stage

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})

/-- The preimage of an open of a stage is the preimage along a transition of its preimage at a
later stage. -/
theorem preimage_map_left {i : I} {k k' : Over i} (p : k' ⟶ k) (V : (D.obj i).Opens) :
    D.map k'.hom ⁻¹ᵁ V = D.map p.left ⁻¹ᵁ (D.map k.hom ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, ← D.map_comp, Over.w p]

/-- For a morphism `p : k' ⟶ k` of objects over `i`, the transition `D.map p.left` followed by
`D.map k.hom` is `D.map k'.hom`. -/
theorem map_left_comp {i : I} {k k' : Over i} (p : k' ⟶ k) :
    D.map p.left ≫ D.map k.hom = D.map k'.hom := by
  rw [← D.map_comp, Over.w p]

/-- The transport of a local descent datum over an open `V` of the stage `i` from a stage over
`i` to a later one. -/
noncomputable def stageTransport {i : I} {k k' : Over i} (p : k' ⟶ k)
    {F G : (D.obj i).Modules} {V : (D.obj i).Opens}
    (Θ : Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k.hom)).obj F)
          (D.map k.hom ⁻¹ᵁ V).ι ⟶
        Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k.hom)).obj G)
          (D.map k.hom ⁻¹ᵁ V).ι) :
    Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k'.hom)).obj F)
        (D.map k'.hom ⁻¹ᵁ V).ι ⟶
      Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k'.hom)).obj G)
        (D.map k'.hom ⁻¹ᵁ V).ι :=
  transportRestrictHom (D.map p.left) (D.map k.hom) (D.map k'.hom) (map_left_comp D p)
    (le_of_eq (preimage_map_left D p V)) Θ

variable (c : Cone D)

/-- A local descent datum transports to a later stage of the diagram. -/
theorem localDescent_stageTransport {i : I} {k k' : Over i} (p : k' ⟶ k)
    {F G : (D.obj i).Modules}
    {φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G} {V : (D.obj i).Opens}
    (Θ : Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k.hom)).obj F)
          (D.map k.hom ⁻¹ᵁ V).ι ⟶
        Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k.hom)).obj G)
          (D.map k.hom ⁻¹ᵁ V).ι)
    (h : LocalDescent (c.π.app k.left) (D.map k.hom) (c.π.app i) (c.w k.hom) φ
      (D.map k.hom ⁻¹ᵁ V) Θ) :
    LocalDescent (c.π.app k'.left) (D.map k'.hom) (c.π.app i) (c.w k'.hom) φ
      (D.map k'.hom ⁻¹ᵁ V) (stageTransport D p Θ) :=
  localDescent_transport (D.map p.left) (D.map k.hom) (D.map k'.hom) (map_left_comp D p)
    (c.π.app k.left) (c.π.app k'.left) (c.w p.left) (c.π.app i) (c.w k.hom) (c.w k'.hom) φ
    (le_of_eq (preimage_map_left D p V)) Θ h

end Stage

section Overlap

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)

/-- **Two local descent data agree on the intersection of their opens, at a later stage.**  Let
`D` be a cofiltered diagram of schemes with affine transition morphisms and `c` a limit cone. Two
local descent data `Θa` and `Θb` at a stage `k` over `i`, over the preimages of opens `Va` and `Vb`
of `D i` with `Va ⊓ Vb` quasi-compact, have transports along some `p : k' ⟶ k` with the same
sections over every open `W` contained in the preimages of both `Va` and `Vb`. -/
theorem exists_stage_valSections_eq (hc : IsLimit c) (i : I)
    {Va Vb : (D.obj i).Opens}
    (hqc : IsCompact ((Va ⊓ Vb : (D.obj i).Opens) : Set (D.obj i)))
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) (k : Over i)
    (Θa : Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k.hom)).obj F)
          (D.map k.hom ⁻¹ᵁ Va).ι ⟶
        Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k.hom)).obj G)
          (D.map k.hom ⁻¹ᵁ Va).ι)
    (Θb : Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k.hom)).obj F)
          (D.map k.hom ⁻¹ᵁ Vb).ι ⟶
        Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k.hom)).obj G)
          (D.map k.hom ⁻¹ᵁ Vb).ι)
    (ha : LocalDescent (c.π.app k.left) (D.map k.hom) (c.π.app i) (c.w k.hom) φ
      (D.map k.hom ⁻¹ᵁ Va) Θa)
    (hb : LocalDescent (c.π.app k.left) (D.map k.hom) (c.π.app i) (c.w k.hom) φ
      (D.map k.hom ⁻¹ᵁ Vb) Θb) :
    ∃ (k' : Over i) (p : k' ⟶ k),
      ∀ (W : (D.obj k'.left).Opens) (hwa : W ≤ D.map k'.hom ⁻¹ᵁ Va)
        (hwb : W ≤ D.map k'.hom ⁻¹ᵁ Vb)
        (m : ((Scheme.Modules.pullback (D.map k'.hom)).obj F).val.obj (op W)),
        valSections (stageTransport D p Θa) W hwa m
          = valSections (stageTransport D p Θb) W hwb m := by
  classical
  have hRa : D.map k.hom ⁻¹ᵁ (Va ⊓ Vb) ≤ D.map k.hom ⁻¹ᵁ Va :=
    Scheme.Hom.preimage_mono _ inf_le_left
  have hRb : D.map k.hom ⁻¹ᵁ (Va ⊓ Vb) ≤ D.map k.hom ⁻¹ᵁ Vb :=
    Scheme.Hom.preimage_mono _ inf_le_right
  have hRT : D.map k.hom ⁻¹ᵁ (Va ⊓ Vb)
      ≤ D.map k.hom ⁻¹ᵁ (D.map (𝟙 i) ⁻¹ᵁ (Va ⊓ Vb)) :=
    Scheme.Hom.preimage_mono _ (by simp)
  have hW₀ : c.π.app i ⁻¹ᵁ (Va ⊓ Vb)
      ≤ c.π.app k.left ⁻¹ᵁ (D.map k.hom ⁻¹ᵁ (Va ⊓ Vb)) :=
    le_of_eq (by rw [← Scheme.Hom.comp_preimage, c.w k.hom])
  have ha' := localDescent_restrictTo (c.π.app k.left) (D.map k.hom) (c.π.app i)
    (c.w k.hom) φ hRa ha
  have hb' := localDescent_restrictTo (c.π.app k.left) (D.map k.hom) (c.π.app i)
    (c.w k.hom) φ hRb hb
  have hpull := map_resLE_eq_of_localDescent (c.π.app k.left) (D.map k.hom) (c.π.app i)
    (c.w k.hom) φ hRT hW₀ (restrictTo hRa Θa) (restrictTo hRb Θb) ha' hb'
  have hfpF : ((Scheme.Modules.pullback (D.map k.hom)).obj F).IsFinitePresentation :=
    isFinitePresentation_pullback _ F
  have hfpG : ((Scheme.Modules.pullback (D.map k.hom)).obj G).IsFinitePresentation :=
    isFinitePresentation_pullback _ G
  have hrF : (Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k.hom)).obj F)
      (D.map k.hom ⁻¹ᵁ (Va ⊓ Vb)).ι).IsFinitePresentation :=
    isFinitePresentation_restrict _ _
  have hrG : (Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k.hom)).obj G)
      (D.map k.hom ⁻¹ᵁ (Va ⊓ Vb)).ι).IsFinitePresentation :=
    isFinitePresentation_restrict _ _
  obtain ⟨k', p, hstep⟩ := @exists_pullback_map_eq_of_isLimit' _ _ _
    (EventualLimit.preimageDiagram D i (Va ⊓ Vb)) (fun _ ↦ inferInstance)
    (EventualLimit.preimageCone D c i (Va ⊓ Vb))
    (EventualLimit.isLimitPreimageCone D c hc i (Va ⊓ Vb)) k
    (isCompact_iff_compactSpace.mp ((D.map k.hom).isCompact_preimage hqc)) _ _ hrF hrG
    (restrictTo hRa Θa) (restrictTo hRb Θb) hpull
  refine ⟨k', p, fun W hwa hwb m ↦ ?_⟩
  have hWa : D.map k'.hom ⁻¹ᵁ Va ≤ D.map p.left ⁻¹ᵁ (D.map k.hom ⁻¹ᵁ Va) :=
    le_of_eq (preimage_map_left D p Va)
  have hWb : D.map k'.hom ⁻¹ᵁ Vb ≤ D.map p.left ⁻¹ᵁ (D.map k.hom ⁻¹ᵁ Vb) :=
    le_of_eq (preimage_map_left D p Vb)
  have hWR : D.map k'.hom ⁻¹ᵁ (Va ⊓ Vb)
      ≤ D.map p.left ⁻¹ᵁ (D.map k.hom ⁻¹ᵁ (Va ⊓ Vb)) :=
    le_of_eq (preimage_map_left D p (Va ⊓ Vb))
  have hR'a : D.map k'.hom ⁻¹ᵁ (Va ⊓ Vb) ≤ D.map k'.hom ⁻¹ᵁ Va :=
    Scheme.Hom.preimage_mono _ inf_le_left
  have hR'b : D.map k'.hom ⁻¹ᵁ (Va ⊓ Vb) ≤ D.map k'.hom ⁻¹ᵁ Vb :=
    Scheme.Hom.preimage_mono _ inf_le_right
  have hWR' : W ≤ D.map k'.hom ⁻¹ᵁ (Va ⊓ Vb) := le_inf hwa hwb
  have hbr : pullbackRestrictHom (D.map p.left) hWR (restrictTo hRa Θa)
      = pullbackRestrictHom (D.map p.left) hWR (restrictTo hRb Θb) :=
    congrArg (_ ≫ · ≫ _) hstep
  have hta := restrictTo_pullbackRestrictHom (D.map p.left) hRa hWa hWR hR'a Θa
  have htb := restrictTo_pullbackRestrictHom (D.map p.left) hRb hWb hWR hR'b Θb
  have hsec : valSections (pullbackRestrictHom (D.map p.left) hWa Θa) W hwa
        ((inv (canHom (D.map p.left) (D.map k.hom) (D.map k'.hom) (map_left_comp D p)
          F)).val.app (op W) m)
      = valSections (pullbackRestrictHom (D.map p.left) hWb Θb) W hwb
        ((inv (canHom (D.map p.left) (D.map k.hom) (D.map k'.hom) (map_left_comp D p)
          F)).val.app (op W) m) := by
    rw [← valSections_restrictTo hR'a (pullbackRestrictHom (D.map p.left) hWa Θa) W hWR',
      ← valSections_restrictTo hR'b (pullbackRestrictHom (D.map p.left) hWb Θb) W hWR',
      hta, htb, hbr]
  simp only [stageTransport, transportRestrictHom, valSections_comp,
    valSections_restrictFunctor_map, hsec]

end Overlap

end Stacks.AlgebraicGeometry.ModuleLimits

end
