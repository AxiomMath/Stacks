module

public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.ChartTwist
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.PullbackSectionCalculus
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.LocalDescentGlue
public import StacksFrontier.AlgebraicGeometry.ChartTransNonNested.TwistSectionOn

/-!
# `legTail` on pulled-back sections

`Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.legTail` is a composite of the
pseudofunctoriality isomorphisms of the inverse image, an identification `χ`, a morphism `tw` and
a contraction. On a section pulled back twice — first along `h`, then along `k` — each factor is
computed by one lemma about `AlgebraicGeometry.Scheme.Modules.pullbackSection`, and this file
records the outcome: if `χ` carries the pulled-back section to the restriction of a global section
`d`, and `tw` carries the pull-back of `d` to the pull-back of a global section `b`, then `legTail`
carries the twice pulled-back section to the restriction of `b`. Everything is stated with the
schemes, modules and morphisms free.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.legTail_pullbackSection`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules (pullbackSection)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {W Z Y D Vv : Scheme.{u}} (k : W ⟶ Z) (h : Z ⟶ Y) (ρ : W ⟶ D)
  (hU : D ⟶ Vv) (c : Vv ⟶ Y) (ι : D ⟶ W) (e : k ≫ h = ρ ≫ hU ≫ c) (hρι : ρ ≫ ι = 𝟙 W)
  {M : Y.Modules} {N : Vv.Modules} {B : W.Modules}
  (χ : (Scheme.Modules.pullback c).obj M ≅ N)
  (tw : (Scheme.Modules.pullback hU).obj N ⟶ (Scheme.Modules.pullback ι).obj B)

/-- `pullbackSection` along `f` of a section over `U`, to `V`, read back from the inverse image
along a composite: the inverse of the pseudofunctoriality isomorphism splits it. -/
theorem pullbackComp_inv_pullbackSection {X X' X'' : Scheme.{u}} (f : X ⟶ X') (f' : X' ⟶ X'')
    (P : X''.Modules) (U : X''.Opens) (V : X.Opens) (h : V ≤ (f ≫ f') ⁻¹ᵁ U)
    (a : P.val.obj (op U)) :
    ((Scheme.Modules.pullbackComp f f').inv.app P).val.app (op V)
        (pullbackSection (f ≫ f') P U V h a) =
      pullbackSection f ((Scheme.Modules.pullback f').obj P) (f' ⁻¹ᵁ U) V h
        (pullbackSection f' P U (f' ⁻¹ᵁ U) le_rfl a) := by
  refine Eq.trans (congrArg (((Scheme.Modules.pullbackComp f f').inv.app P).val.app (op V))
    (Scheme.Modules.pullbackSection_comp f f' P U (f' ⁻¹ᵁ U) V le_rfl h h a).symm) ?_
  exact TwistRigidity.iso_inv_app_hom_app ((Scheme.Modules.pullbackComp f f').app P) (op V) _

/-- Over the identity, the pulled-back section is the restriction. -/
theorem pullbackId_hom_pullbackSection {X : Scheme.{u}} (P : X.Modules) (U V : X.Opens)
    (h : V ≤ (𝟙 X) ⁻¹ᵁ U) (hVU : V ≤ U) (a : P.val.obj (op U)) :
    ((Scheme.Modules.pullbackId X).hom.app P).val.app (op V) (pullbackSection (𝟙 X) P U V h a) =
      P.val.map (homOfLE hVU).op a := by
  have hnat := PresheafOfModules.naturality_apply ((Scheme.Modules.pullbackId X).hom.app P).val
    (homOfLE h).op
    (((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app P).val.app (op U) a)
  unfold pullbackSection
  refine hnat.trans ?_
  exact congrArg (P.val.map (homOfLE h).op)
    (PullbackUnit.pullbackId_hom_pullbackSectionOn X P U a)

/-- **`legTail` on a twice pulled-back section.** -/
theorem legTail_pullbackSection (U1 : Y.Opens) (t : M.val.obj (op U1))
    (d : N.val.obj (op ⊤)) (b : B.val.obj (op ⊤))
    (hχ : χ.hom.val.app (op (c ⁻¹ᵁ U1)) (pullbackSection c M U1 (c ⁻¹ᵁ U1) le_rfl t) =
      N.val.map (homOfLE le_top).op d)
    (htw : tw.val.app (op ⊤) (pullbackSection hU N ⊤ ⊤ (fun _ _ => trivial) d) =
      pullbackSection ι B ⊤ ⊤ (fun _ _ => trivial) b)
    (Wo : W.Opens) (hk : Wo ≤ k ⁻¹ᵁ (h ⁻¹ᵁ U1)) :
    (legTail k h ρ hU c ι e hρι χ tw).val.app (op Wo)
        (pullbackSection k ((Scheme.Modules.pullback h).obj M) (h ⁻¹ᵁ U1) Wo hk
          (pullbackSection h M U1 (h ⁻¹ᵁ U1) le_rfl t)) =
      B.val.map (homOfLE le_top).op b := by
  have hW : Wo ≤ (k ≫ h) ⁻¹ᵁ U1 := hk
  have hW' : Wo ≤ (ρ ≫ hU ≫ c) ⁻¹ᵁ U1 := e ▸ hW
  have hZ2 : Wo ≤ ρ ⁻¹ᵁ ((hU ≫ c) ⁻¹ᵁ U1) := hW'
  -- the leg
  have s1 := Scheme.Modules.pullbackSection_comp k h M U1 (h ⁻¹ᵁ U1) Wo le_rfl hk hW t
  have s2 := Scheme.Modules.pullbackSection_congr e M U1 Wo hW hW' t
  have s3 := pullbackComp_inv_pullbackSection ρ (hU ≫ c) M U1 Wo hW' t
  have s4a := pullbackComp_inv_pullbackSection hU c M U1 ((hU ≫ c) ⁻¹ᵁ U1) le_rfl t
  have s4b := Scheme.Modules.pullbackSection_naturality hU χ.hom (c ⁻¹ᵁ U1)
    ((hU ≫ c) ⁻¹ᵁ U1) le_rfl (pullbackSection c M U1 (c ⁻¹ᵁ U1) le_rfl t)
  have s4c : pullbackSection hU N (c ⁻¹ᵁ U1) ((hU ≫ c) ⁻¹ᵁ U1) le_rfl
      (N.val.map (homOfLE le_top).op d) =
      pullbackSection hU N ⊤ ((hU ≫ c) ⁻¹ᵁ U1) (fun _ _ => trivial) d :=
    ModuleLimits.pullbackSection_target_le hU N le_top _ _ _ d
  -- the morphism `tw`
  have s5 : tw.val.app (op ((hU ≫ c) ⁻¹ᵁ U1))
      (pullbackSection hU N ⊤ ((hU ≫ c) ⁻¹ᵁ U1) (fun _ _ => trivial) d) =
      pullbackSection ι B ⊤ ((hU ≫ c) ⁻¹ᵁ U1) (fun _ _ => trivial) b := by
    refine Eq.trans (congrArg (tw.val.app (op ((hU ≫ c) ⁻¹ᵁ U1)))
      (ModuleLimits.pullbackSection_shrink hU N ⊤ ⊤ ((hU ≫ c) ⁻¹ᵁ U1) (fun _ _ => trivial)
        le_top (fun _ _ => trivial) d).symm) ?_
    refine Eq.trans (PresheafOfModules.naturality_apply tw.val (homOfLE le_top).op _) ?_
    refine Eq.trans (congrArg _ htw) ?_
    exact ModuleLimits.pullbackSection_shrink ι B ⊤ ⊤ ((hU ≫ c) ⁻¹ᵁ U1) (fun _ _ => trivial)
      le_top (fun _ _ => trivial) b
  -- the contraction
  have s6 := Scheme.Modules.pullbackSection_comp ρ ι B ⊤ ((hU ≫ c) ⁻¹ᵁ U1) Wo
    (fun _ _ => trivial) hZ2 (fun _ _ => trivial) b
  have s7 := Scheme.Modules.pullbackSection_congr hρι B ⊤ Wo (fun _ _ => trivial)
    (fun _ _ => trivial) b
  have s8 := pullbackId_hom_pullbackSection B ⊤ Wo (fun _ _ => trivial) le_top b
  unfold legTail TwistMulLeg.legIso
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv,
    Functor.map_comp, Tag07ZGTwist.comp_val_app_apply]
  have n1 := Scheme.Modules.pullbackSection_naturality ρ
    ((Scheme.Modules.pullbackComp hU c).inv.app M) ((hU ≫ c) ⁻¹ᵁ U1) Wo hZ2
    (pullbackSection (hU ≫ c) M U1 ((hU ≫ c) ⁻¹ᵁ U1) le_rfl t)
  have n2 := Scheme.Modules.pullbackSection_naturality ρ
    ((Scheme.Modules.pullback hU).map χ.hom) ((hU ≫ c) ⁻¹ᵁ U1) Wo hZ2
    (pullbackSection hU ((Scheme.Modules.pullback c).obj M) (c ⁻¹ᵁ U1) ((hU ≫ c) ⁻¹ᵁ U1) le_rfl
      (pullbackSection c M U1 (c ⁻¹ᵁ U1) le_rfl t))
  have n3 := Scheme.Modules.pullbackSection_naturality ρ tw ((hU ≫ c) ⁻¹ᵁ U1) Wo hZ2
    (pullbackSection hU N ⊤ ((hU ≫ c) ⁻¹ᵁ U1) (fun _ _ => trivial) d)
  rw [s1, s2, s3]
  rw [n1]
  rw [s4a]
  simp only [Functor.comp_obj]
  rw [n2]
  rw [s4b, hχ, s4c]
  rw [n3]
  rw [s5, s6, s7, s8]

end Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

end
