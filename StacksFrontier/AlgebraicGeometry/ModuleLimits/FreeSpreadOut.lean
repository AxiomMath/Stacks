module

public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport
public import StacksFrontier.AlgebraicGeometry.LimitDescent.BaseChangeLimit
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismDescentGlue
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.ReflectIso
public import StacksFrontier.AlgebraicGeometry.StalkAffineNhdsLimit.Basic

/-!
# Freeness of finite rank spreads out from a limit, and from a local scheme

Let `S = lim Sᵢ` be a cofiltered limit of quasi-compact and quasi-separated schemes with affine
transition morphisms, and let `ℱ` be a sheaf of modules of finite presentation on a stage `Sᵢ`.
If the pullback of `ℱ` to `S` is free of rank `r`, then so is its pullback to some later stage:
the isomorphism descends as a morphism by [Stacks, Tag 01ZR] (2), and its invertibility descends
by Tag 01ZR (3).

Applied to `Spec 𝒪_{Y,s} = lim W` over the affine open neighbourhoods `W` of a point `s`
(`AlgebraicGeometry.isLimitSpecStalkCone`), base changed along a quasi-compact quasi-separated
`f : X ⟶ Y`: a module of finite presentation on `X` whose pullback to `X ×_Y Spec 𝒪_{Y,s}` is free
of rank `r` is free of rank `r` over `f ⁻¹ W` for an open neighbourhood `W` of `s`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_iso_free_of_isLimit`.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_mem_pullback_iso_free_of_fromSpecStalk`.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-- Composing pullbacks along `a` and `b` is the pullback along any `c` equal to `a ≫ b`. -/
private def pullbackCompIsoOfEq {X Y Z : Scheme.{u}} {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ Z}
    (h : a ≫ b = c) (E : Z.Modules) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj E) ≅
      (Scheme.Modules.pullback c).obj E :=
  (Scheme.Modules.pullbackComp a b).app E ≪≫ (Scheme.Modules.pullbackCongr h).app E

/-- The pullback along `a` of a module isomorphic to `𝒪^{⊕r}` is isomorphic to `𝒪^{⊕r}`. -/
private def pullbackIsoFreeOfIso {X Y : Scheme.{u}} (a : X ⟶ Y) {M : Y.Modules} {r : ℕ}
    (e : M ≅ SheafOfModules.free (ULift.{u} (Fin r))) :
    (Scheme.Modules.pullback a).obj M ≅ SheafOfModules.free (ULift.{u} (Fin r)) :=
  (Scheme.Modules.pullback a).mapIso e ≪≫ Scheme.Modules.pullbackFreeIso a _

section Limit

variable {I : Type u} [Category.{v} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)

/-- **Freeness of finite rank descends to a stage of a cofiltered limit.** Let `c` be a limit cone
on a cofiltered diagram of quasi-compact quasi-separated schemes with affine transition morphisms
and let `ℱ` be of finite presentation on a stage `D.obj i`. If the pullback of `ℱ` to the limit is
isomorphic to `𝒪^{⊕r}`, then so is its pullback to some stage over `i`. -/
theorem exists_pullback_iso_free_of_isLimit (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (F : (D.obj i).Modules) [F.IsFinitePresentation] (r : ℕ)
    (e : (Scheme.Modules.pullback (c.π.app i)).obj F ≅ SheafOfModules.free (ULift.{u} (Fin r))) :
    ∃ (j : I) (g : j ⟶ i), Nonempty ((Scheme.Modules.pullback (D.map g)).obj F ≅
      SheafOfModules.free (ULift.{u} (Fin r))) := by
  let G : (D.obj i).Modules := SheafOfModules.free (ULift.{u} (Fin r))
  have : G.IsFinitePresentation := isFinitePresentation_free_of_finite _ _
  let φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G :=
    (e ≪≫ (Scheme.Modules.pullbackFreeIso (c.π.app i) _).symm).hom
  have hφ : IsIso φ := Iso.isIso_hom _
  obtain ⟨j, g, φj, hφj⟩ := exists_map_of_pullback_of_isLimit D c hc i F G φ
  have hiso : IsIso ((Scheme.Modules.pullback (c.π.app j)).map φj) := by
    have h2 : (Scheme.Modules.pullback (c.π.app j)).map φj =
        ((Scheme.Modules.pullbackComp (c.π.app j) (D.map g)).hom.app F ≫
          (Scheme.Modules.pullbackCongr (c.w g)).hom.app F ≫ φ) ≫
        inv ((Scheme.Modules.pullbackComp (c.π.app j) (D.map g)).hom.app G ≫
          (Scheme.Modules.pullbackCongr (c.w g)).hom.app G) := by
      rw [← hφj, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [h2]
    infer_instance
  have : ((Scheme.Modules.pullback (D.map g)).obj F).IsFinitePresentation :=
    isFinitePresentation_pullback (D.map g) F
  have : ((Scheme.Modules.pullback (D.map g)).obj G).IsFinitePresentation :=
    isFinitePresentation_pullback (D.map g) G
  obtain ⟨k, g', hk⟩ := exists_isIso_pullback_map_of_isLimit D c hc j _ _ φj hiso
  exact ⟨k, g' ≫ g, ⟨(pullbackCompIsoOfEq (D.map_comp g' g).symm F).symm ≪≫
    asIso ((Scheme.Modules.pullback (D.map g')).map φj) ≪≫
      pullbackIsoFreeOfIso _ (Scheme.Modules.pullbackFreeIso (D.map g) _)⟩⟩

end Limit

/-- **Freeness of finite rank over the local scheme at a point spreads out to a neighbourhood.**
Let `f : X ⟶ Y` be quasi-compact and quasi-separated and `ℰ` of finite presentation on `X`. If the
pullback of `ℰ` to `X ×_Y Spec 𝒪_{Y,s}` is isomorphic to `𝒪^{⊕r}`, then there is an open
neighbourhood `W` of `s` such that the pullback of `ℰ` to `X ×_Y W` is isomorphic to `𝒪^{⊕r}`. -/
theorem exists_mem_pullback_iso_free_of_fromSpecStalk {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (E : X.Modules) [E.IsFinitePresentation] (s : Y)
    (r : ℕ) (e : (Scheme.Modules.pullback (pullback.fst f (Y.fromSpecStalk s))).obj E ≅
      SheafOfModules.free (ULift.{u} (Fin r))) :
    ∃ W : Y.Opens, s ∈ W ∧ Nonempty ((Scheme.Modules.pullback (pullback.fst f W.ι)).obj E ≅
      SheafOfModules.free (ULift.{u} (Fin r))) := by
  let D := affineOpenNhdsDiagram Y s
  let c := specStalkCone Y s
  let hc : IsLimit c := isLimitSpecStalkCone Y s
  let W₀ : AffineOpenNhds Y s := Classical.arbitrary _
  let ιW : D.obj W₀ ⟶ Y := Scheme.Opens.ι (X := Y) W₀.obj.1
  let X₀ : Over (D.obj W₀) := Over.mk (pullback.snd f ιW)
  have : CompactSpace X₀.left := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f ιW)
  have : QuasiSeparatedSpace X₀.left := quasiSeparatedSpace_of_quasiSeparated (pullback.snd f ιW)
  let L := LimitDescent.bcDiagram D W₀ X₀
  let cL := LimitDescent.bcCone D c W₀ X₀
  let hcL : IsLimit cL := LimitDescent.isLimitBcCone D c W₀ X₀ hc
  let j₀ : Over W₀ := Over.mk (𝟙 W₀)
  -- the map from the stage `j` of the base-changed diagram to `X`
  let toX : ∀ j : Over W₀, L.obj j ⟶ X := fun j ↦
    pullback.fst X₀.hom (D.map j.hom) ≫ pullback.fst f ιW
  let F₀ : (L.obj j₀).Modules := (Scheme.Modules.pullback (toX j₀)).obj E
  have : F₀.IsFinitePresentation := isFinitePresentation_pullback _ E
  -- the limit point maps to `X ×_Y Spec 𝒪_{Y,s}` over `X`
  have h1 : pullback.fst X₀.hom (c.π.app W₀) ≫ X₀.hom =
      pullback.snd X₀.hom (c.π.app W₀) ≫ c.π.app W₀ := pullback.condition
  have h2 : c.π.app W₀ ≫ ιW = Y.fromSpecStalk s :=
    Scheme.Opens.fromSpecStalkOfMem_ι _ _ _
  have hcond : (pullback.fst X₀.hom (c.π.app W₀) ≫ pullback.fst f ιW) ≫ f =
      pullback.snd X₀.hom (c.π.app W₀) ≫ Y.fromSpecStalk s := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact (h1 =≫ ιW).trans (by rw [Category.assoc, h2])
  let κ : cL.pt ⟶ pullback f (Y.fromSpecStalk s) :=
    pullback.lift _ _ hcond
  have hκ : cL.π.app j₀ ≫ toX j₀ = κ ≫ pullback.fst f (Y.fromSpecStalk s) :=
    (LimitDescent.bcπ_fst_assoc D c W₀ X₀ j₀ _).trans (pullback.lift_fst _ _ _).symm
  let e₀ : (Scheme.Modules.pullback (cL.π.app j₀)).obj F₀ ≅
      SheafOfModules.free (ULift.{u} (Fin r)) :=
    pullbackCompIsoOfEq hκ E ≪≫ (pullbackCompIsoOfEq rfl E).symm ≪≫ pullbackIsoFreeOfIso κ e
  obtain ⟨j, g, ⟨ej⟩⟩ := exists_pullback_iso_free_of_isLimit L cL hcL j₀ F₀ r e₀
  -- the open neighbourhood `W` of the stage `j`
  let W : Y.Opens := j.left.obj.1
  refine ⟨W, j.left.obj.2, ⟨?_⟩⟩
  -- `X ×_Y W` maps to the stage `j` over `X`
  have hjW : D.map j.hom ≫ ιW = W.ι := by
    show (affineOpenNhdsDiagram Y s).map j.hom ≫ Scheme.Opens.ι (X := Y) W₀.obj.1 = W.ι
    rw [affineOpenNhdsDiagram_map]
    exact Scheme.homOfLE_ι _ _
  let σ₀ : pullback f W.ι ⟶ X₀.left :=
    pullback.lift (pullback.fst f W.ι) (pullback.snd f W.ι ≫ D.map j.hom)
      (pullback.condition.trans ((congrArg (pullback.snd f W.ι ≫ ·) hjW.symm).trans
        (Category.assoc _ _ _).symm))
  have hσ₀ : σ₀ ≫ X₀.hom = pullback.snd f W.ι ≫ D.map j.hom := pullback.lift_snd _ _ _
  let σ : pullback f W.ι ⟶ L.obj j := pullback.lift σ₀ (pullback.snd f W.ι) hσ₀
  have hσ : σ ≫ (L.map g ≫ toX j₀) = pullback.fst f W.ι := by
    have e1 : σ ≫ pullback.fst X₀.hom (D.map j.hom) = σ₀ := pullback.lift_fst _ _ _
    have e2 : σ₀ ≫ pullback.fst f ιW = pullback.fst f W.ι := pullback.lift_fst _ _ _
    have e3 : L.map g ≫ pullback.fst X₀.hom (D.map j₀.hom) =
        pullback.fst X₀.hom (D.map j.hom) := LimitDescent.bcMap_fst D W₀ X₀ g
    simp only [toX]
    rw [reassoc_of% e3, ← Category.assoc, e1, e2]
  exact (pullbackCompIsoOfEq hσ E).symm ≪≫
    pullbackIsoFreeOfIso σ ((pullbackCompIsoOfEq rfl E).symm ≪≫ ej)

end Stacks.AlgebraicGeometry.ModuleLimits

end
