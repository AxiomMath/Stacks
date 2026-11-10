module

public import StacksFrontier.AlgebraicGeometry.GenericFlatness.ImageStratification
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.ModuleStratification
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismDescentGlue
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The flattening stratification over a quasi-compact quasi-separated base

Let `f : X ⟶ S` be a morphism of finite presentation between quasi-compact, quasi-separated
schemes and let `ℱ` be an `𝒪_X`-module of finite presentation. Then the base carries a finite
descending chain of closed subschemes `S ⊇ S₀ ⊇ S₁ ⊇ ⋯ ⊇ S_t = ∅`, each cut out by an ideal
sheaf of finite type and with `S₀ ⊆ S` a thickening, such that the pullback of `ℱ` to
`X ×_S (S_i ∖ S_{i+1})` is flat over the locally closed stratum `S_i ∖ S_{i+1}`.

This is [Stacks, Tag 0ASY]. The Noetherian case is
`AlgebraicGeometry.exists_flat_stratification_of_isNoetherian`, and the content of this file is
the reduction of the general case to it: the base is written as a cofiltered limit of schemes of
finite type over `ℤ` with affine transition morphisms, the morphism `f` descends to a model over
one of those Noetherian stages, the module `ℱ` descends to a model over a further stage, the
Noetherian case is applied there, and the resulting chain of ideal sheaves is pulled back to `S`.

## Main results

* `AlgebraicGeometry.exists_flat_stratification`: **[Stacks, Tag 0ASY]**.

## Implementation notes

The conclusion is recorded exactly as in the Noetherian case and as in
`Stacks.GenericFlatness.HasStratification`: a descending chain of closed subschemes of `S` is the
*ascending* chain `I : Fin (t + 1) → S.IdealSheafData` of their quasi-coherent ideal sheaves,
`S_t = ∅` is `I (Fin.last t) = ⊤`, and the locally closed stratum `S_i ∖ S_{i+1}` is the open
subscheme of `S_i` obtained by removing the support of `I (i + 1)`. The transport of the chain
from the Noetherian stage down to `S` is therefore
`Stacks.GenericFlatness.HasStratification.comap`, whose hypothesis — stability of the condition
on a stratum under precomposition — is `AlgebraicGeometry.isFlatOver_pullback_snd_comp` here.

The module-descent step is
`Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_qcqs`, which
is [Stacks, Tag 01ZR] (1) for a cofiltered limit of quasi-compact quasi-separated schemes with
affine transition morphisms. It is applied not to the approximating diagram of the base but to
the diagram `AlgebraicGeometry.baseChangeDiagram` of base changes of the model of `f`, whose
limit is `X`.

## References

* [Stacks Project, Tag 0ASY](https://stacks.math.columbia.edu/tag/0ASY)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.GenericFlatness

universe u

namespace AlgebraicGeometry

/-! ### Flatness over a stratum and base change -/

/-- **Flatness over a stratum descends from a model.** Let `f : X ⟶ S` be the base change of
`f₀ : X₀ ⟶ S₀` along `s : S ⟶ S₀`, let `ℱ` on `X` be the pullback of a quasi-coherent `M` on
`X₀`, and let `g : T ⟶ S` factor through `g₀ : T₀ ⟶ S₀` after composing with `s`. If the pullback
of `M` to `X₀ ×_{S₀} T₀` is flat over `T₀`, then the pullback of `ℱ` to `X ×_S T` is flat
over `T`.

This is the transport step of [Stacks, Tag 0ASY]: the strata produced over the Noetherian base
`S₀` are pulled back to `S`, and this is what makes their flatness survive. -/
private lemma isFlatOver_pullback_snd_of_model {X S X₀ S₀ T T₀ : Scheme.{u}}
    {x : X ⟶ X₀} {f : X ⟶ S} {f₀ : X₀ ⟶ S₀} {s : S ⟶ S₀}
    (h : IsPullback x f f₀ s) (g : T ⟶ S) (g₀ : T₀ ⟶ S₀)
    (v : T ⟶ T₀) (hv : g ≫ s = v ≫ g₀)
    (M : X₀.Modules) [M.IsQuasicoherent] (F : X.Modules)
    (eF : F ≅ (Scheme.Modules.pullback x).obj M)
    (hM : IsFlatOver (pullback.snd f₀ g₀).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst f₀ g₀)).obj M)) :
    IsFlatOver (pullback.snd f g).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst f g)).obj F) := by
  let m : pullback f g ⟶ pullback f₀ g₀ :=
    pullback.lift (pullback.fst f g ≫ x) (pullback.snd f g ≫ v) (by
      calc
        (pullback.fst f g ≫ x) ≫ f₀ = (pullback.fst f g ≫ f) ≫ s := by
          rw [Category.assoc, h.w, ← Category.assoc]
        _ = (pullback.snd f g ≫ v) ≫ g₀ := by
          rw [pullback.condition, Category.assoc, hv, ← Category.assoc])
  have hout' : IsPullback (m ≫ pullback.fst f₀ g₀) (pullback.snd f g) f₀ (v ≫ g₀) := by
    simpa only [m, pullback.lift_fst, ← hv] using (IsPullback.of_hasPullback f g).paste_horiz h
  have hm : IsPullback m (pullback.snd f g) (pullback.snd f₀ g₀) v :=
    hout'.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f₀ g₀)
  have hQ : ((Scheme.Modules.pullback (pullback.fst f₀ g₀)).obj M).IsQuasicoherent :=
    inferInstance
  have hG : IsFlatOver (pullback.snd f g).toLRSHom.toShHom
      ((Scheme.Modules.pullback m).obj
        ((Scheme.Modules.pullback (pullback.fst f₀ g₀)).obj M)) :=
    @modulePullback_isFlatOver _ _ _ _ _ _ _ _ hm _ hQ hM
  exact isFlatOver_of_moduleIso _
    ((Scheme.Modules.pullbackComp m (pullback.fst f₀ g₀)).app M ≪≫
      (Scheme.Modules.pullbackCongr (pullback.lift_fst _ _ _)).app M ≪≫
      ((Scheme.Modules.pullbackComp (pullback.fst f g) x).app M).symm ≪≫
      (Scheme.Modules.pullback (pullback.fst f g)).mapIso eF.symm) hG

/-- **Flatness over a stratum is inherited by any further base change of the stratum.** This is
the degenerate case of `AlgebraicGeometry.isFlatOver_pullback_snd_of_model` in which the model is
the given situation itself, and it is the hypothesis
`Stacks.GenericFlatness.HasStratification.comap` asks for. -/
public lemma isFlatOver_pullback_snd_comp_of_isFlatOver {X S U V : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) [F.IsQuasicoherent] (a : U ⟶ S) (b : V ⟶ U)
    (h : IsFlatOver (pullback.snd f a).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst f a)).obj F)) :
    IsFlatOver (pullback.snd f (b ≫ a)).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst f (b ≫ a))).obj F) :=
  isFlatOver_pullback_snd_of_model (x := 𝟙 X) (f := f) (f₀ := f) (s := 𝟙 S)
    (IsPullback.of_horiz_isIso ⟨by simp⟩) (b ≫ a) a b (by simp) F F
    ((Scheme.Modules.pullbackId X).app F).symm h

/-- **Flatness over a stratum is inherited by any further base change of the stratum.** This is
the degenerate case of `AlgebraicGeometry.isFlatOver_pullback_snd_of_model` in which the model is
the given situation itself, and it is the hypothesis
`Stacks.GenericFlatness.HasStratification.comap` asks for. -/
private alias isFlatOver_pullback_snd_comp := isFlatOver_pullback_snd_comp_of_isFlatOver

/-- **The flat stratification descends from a Noetherian model.** If, up to an isomorphism
`e : P ≅ X`, the morphism `f : X ⟶ S` is the base change along `s : S ⟶ T` of a morphism of
finite presentation `fa : Y ⟶ T` to a Noetherian scheme, and `ℱ` corresponds to the pullback of
a finitely presented module on `Y`, then `ℱ` has a flat stratification over `S`. -/
private lemma hasStratification_isFlatOver_of_isPullback {X S P Y T : Scheme.{u}} [IsNoetherian T]
    {f : X ⟶ S} {fa : Y ⟶ T} {s : S ⟶ T} {q : P ⟶ Y} {p : P ⟶ S}
    (hsq : IsPullback q p fa s) (e : P ≅ X) (he : e.hom ≫ f = p) (hfa : FinitePresentation fa)
    (F : X.Modules) (M : Y.Modules) [M.IsFinitePresentation]
    (eM : (Scheme.Modules.pullback e.hom).obj F ≅ (Scheme.Modules.pullback q).obj M) :
    HasStratification S (fun _ b ↦ IsFlatOver (pullback.snd f b).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst f b)).obj F)) := by
  subst he
  have hsqX : IsPullback (e.inv ≫ q) f fa s := by
    have hi : IsPullback e.inv f (e.hom ≫ f) (𝟙 S) := IsPullback.of_horiz_isIso ⟨by simp⟩
    simpa only [Category.id_comp] using hi.paste_horiz hsq
  let eF : F ≅ (Scheme.Modules.pullback (e.inv ≫ q)).obj M :=
    ((Scheme.Modules.pullbackComp e.inv e.hom).app F ≪≫
      (Scheme.Modules.pullbackCongr e.inv_hom_id).app F ≪≫
      (Scheme.Modules.pullbackId X).app F).symm ≪≫
    (Scheme.Modules.pullback e.inv).mapIso eM ≪≫ (Scheme.Modules.pullbackComp e.inv q).app M
  have : M.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation M
  -- Stratify the Noetherian stage, then pull the chain back to `S`.
  have hN := HasStratification.comap
    (P := fun _ b ↦ IsFlatOver (pullback.snd fa b).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst fa b)).obj M))
    (fun b d hb ↦ isFlatOver_pullback_snd_comp_of_isFlatOver fa M b d hb)
    (exists_flat_stratification_of_isNoetherian fa hfa M) s
  exact hN.mono fun U b hb ↦
    isFlatOver_pullback_snd_of_model hsqX b (b ≫ s) (𝟙 U) (by simp) M F eF hb

/-! ### The stratification -/

/-- **Stacks Project, Tag 0ASY.**

For a morphism of finite presentation `f : X ⟶ S` between quasi-compact, quasi-separated schemes
and a finitely presented `𝒪_X`-module `ℱ`, the base carries a finite ascending chain of
quasi-coherent ideal sheaves of finite type whose first closed subscheme is a thickening of `S`
and whose last closed subscheme is empty, such that the pullback of `ℱ` to the fibre product of
`X` with each locally closed stratum is flat over that stratum.

The general case is reduced to the Noetherian case
`AlgebraicGeometry.exists_flat_stratification_of_isNoetherian`; see the module docstring. -/
@[stacks 0ASY, ega "IV 6.9.3" "more general", ega "IV 8.9.5"]
public theorem exists_flat_stratification {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace S] [QuasiSeparatedSpace S]
    (hf : FinitePresentation f) (F : X.Modules) [F.IsFinitePresentation] :
    ∃ (t : ℕ) (I : Fin (t + 1) → S.IdealSheafData),
      Stacks.Thickenings.IsThickening (I 0).subschemeι ∧
      (∀ i, Scheme.IdealSheafData.IsFiniteType (I i)) ∧
      (∀ i : Fin t, I (Fin.castSucc i) ≤ I (Fin.succ i)) ∧
      I (Fin.last t) = ⊤ ∧
      ∀ i : Fin t,
        let Z := I (Fin.castSucc i)
        let V : S.Opens := (I (Fin.succ i)).support.compl
        let U : Z.subscheme.Opens := Z.subschemeι ⁻¹ᵁ V
        let g : U.toScheme ⟶ S := U.ι ≫ Z.subschemeι
        IsFlatOver (pullback.snd f g).toLRSHom.toShHom
          ((Scheme.Modules.pullback (pullback.fst f g)).obj F) := by
  classical
  -- Write `S` as a cofiltered limit of schemes of finite type over `ℤ`.
  let app := finiteTypeApproximation (S := S)
  let _ := app.indexPreorder
  have := app.indexNonempty
  have := app.indexDirected
  let D := app.ambient
  let c : Cone D := Cone.mk S app.ambientCone
  have hc : IsLimit c := app.ambientCone_isLimit
  have : ∀ {i j : app.indexTypeᵒᵈ} (e : i ⟶ j), IsAffineHom (D.map e) := app.transition_affine
  have : ∀ i, LocallyOfFiniteType (terminal.from (D.obj i)) := app.locallyOfFiniteType
  have : ∀ i, QuasiCompact (terminal.from (D.obj i)) := app.quasiCompact
  have : ∀ i, IsNoetherian (D.obj i) := fun i ↦
    AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType_terminal_from (D.obj i)
  -- Descend `f` to a model over one of the Noetherian stages.
  obtain ⟨i₀, X₀, hX₀, ⟨eX₀⟩⟩ :=
    LimitDescent.exists_model_of_finitePresentation_of_essentiallySmall D c hc (Over.mk f) hf
  have : LocallyOfFinitePresentation X₀.hom := hX₀.1
  have : QuasiCompact X₀.hom := hX₀.2.1
  have : QuasiSeparated X₀.hom := hX₀.2.2
  have : CompactSpace X₀.left := QuasiCompact.compactSpace_of_compactSpace X₀.hom
  have : QuasiSeparatedSpace X₀.left := quasiSeparatedSpace_of_quasiSeparated X₀.hom
  -- The diagram of base changes of that model, whose limit is `X`.
  let Y : Over i₀ ⥤ Scheme.{u} := baseChangeDiagram D i₀ X₀
  let cY : Cone Y := baseChangeCone D c i₀ X₀
  have : ∀ {a b : Over i₀} (g : a ⟶ b), IsAffineHom (Y.map g) := fun g ↦
    isAffineHom_baseChangeDiagram_map D i₀ X₀ g
  have : ∀ a : Over i₀, CompactSpace (Y.obj a) := compactSpace_baseChangeDiagram_obj D i₀ X₀
  have : ∀ a : Over i₀, QuasiSeparatedSpace (Y.obj a) :=
    quasiSeparatedSpace_baseChangeDiagram_obj D i₀ X₀
  let eX : cY.pt ≅ X := pullbackSymmetry (c.π.app i₀) X₀.hom ≪≫ (Over.forget S).mapIso eX₀.symm
  have heX : eX.hom ≫ f = pullback.fst (c.π.app i₀) X₀.hom := by
    change ((pullbackSymmetry (c.π.app i₀) X₀.hom).hom ≫ eX₀.inv.left) ≫ f = _
    rw [Category.assoc,
      show eX₀.inv.left ≫ f = pullback.snd X₀.hom (c.π.app i₀) from Over.w eX₀.inv]
    exact pullbackSymmetry_hom_comp_snd _ _
  -- Descend `ℱ` to a model over a further stage.
  have : ((Scheme.Modules.pullback eX.hom).obj F).IsFinitePresentation :=
    Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback eX.hom F
  obtain ⟨a, Fa, hFa, ⟨eFbase⟩⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_qcqs
      Y cY (baseChangeConeIsLimit D hc i₀ X₀) ((Scheme.Modules.pullback eX.hom).obj F)
  have : Fa.IsFinitePresentation := hFa
  -- The model situation over the Noetherian stage `a`, and its comparison with `f` and `ℱ`.
  have hsq : IsPullback (cY.π.app a) (pullback.fst (c.π.app i₀) X₀.hom)
      (pullback.fst (D.map a.hom) X₀.hom) (c.π.app a.left) :=
    (overPullback_isPullback X₀.hom (Over.mk (c.π.app i₀)) ((Over.post D).obj a)
      (((Over.conePost D i₀).obj c).π.app a)).flip
  exact hasStratification_isFlatOver_of_isPullback hsq eX heX
    (FinitePresentation.of_isPullback (IsPullback.of_hasPullback (D.map a.hom) X₀.hom).flip hX₀)
    F Fa eFbase

end AlgebraicGeometry

end
