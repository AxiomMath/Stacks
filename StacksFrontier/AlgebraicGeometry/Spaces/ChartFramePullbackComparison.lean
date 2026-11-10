module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChartFrameFree
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# The inverse image of a module with frames along a representable morphism

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces, let `W k` be a finite family of
étale charts of `Y` covering the final object of its small étale site, and let `M` be an
`𝒪_Y`-module with frames `e k` over the `W k`.  Let `E` be an `𝒪_X`-module with frames `e' k` over
the base changes `W k ×_Y X`, which cover the final object of the small étale site of `X`.  If
the coordinates of the transition between the frames of `E`, over the base changes of the
products `W k ×_Y W l`, are the pullbacks of those of `M`, then `E ≅ f^*M`.

The proof is the Yoneda lemma: for every `𝒪_X`-module `F`, a morphism `f^*M ⟶ F` is a morphism
`M ⟶ f_*F`, the sections of `f_*F` over a chart of `Y` being the sections of `F` over its base
change; by `Stacks.SheafOfModules.ChartFrames.homEquiv` both these and the morphisms `E ⟶ F` are
the families of sections of `F` over the charts `W k ×_Y X` transforming like the frames, and the
two transformation rules agree.

## Main results

* `AlgebraicGeometry.Space.nonempty_iso_modulePullback_of_frames`: **the comparison.**
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits Stacks.SheafOfModules.ChartFrames

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {B S hS} in
/-- The underlying presheaf of modules of an `𝒪_X`-module, over the structure presheaf of the
small étale site of `X`. -/
abbrev sval {X : AlgebraicSpaces B S hS} (F : Modules.{u, u} B S hS X.1 X.2) :
    PresheafOfModules.{u} ((structureSheaf B S hS X.1 X.2).obj ⋙ forget₂ CommRingCat RingCat) :=
  valP (O := structureSheaf B S hS X.1 X.2) F

/-- The sheaf condition, on underlying sets, of an `𝒪`-module on an algebraic space. -/
theorem isSheaf_sval {X : AlgebraicSpaces B S hS} (F : Modules.{u, u} B S hS X.1 X.2) :
    Presieve.IsSheaf (SmallEtale.topology B S hS X.1)
      ((sval F).presheaf ⋙ CategoryTheory.forget AddCommGrpCat) :=
  (isSheaf_iff_isSheaf_of_type _ _).mp (Presheaf.isSheaf_comp_of_isSheaf _ _ _ F.isSheaf)

section Comparison

variable {B S hS} {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
  (hf : yoneda.relativelyRepresentable f.hom)
  {K : Type} {W : K → SmallEtale B S hS Y.1}
  (hW : (SmallEtale.topology B S hS Y.1).CoversTop W) {n : K → ℕ}
  (M : Modules.{u, u} B S hS Y.1 Y.2) {e : ∀ k, Fin (n k) → (sval M).obj (op (W k))}
  (he : ∀ k, IsFrame (sval M) (e k))
  (E : Modules.{u, u} B S hS X.1 X.2)
  {e' : ∀ k, Fin (n k) → (sval E).obj (op ((smallBaseChange B S hS f hf).obj (W k)))}
  (he' : ∀ k, IsFrame (sval E) (e' k))
  (hW' : (SmallEtale.topology B S hS X.1).CoversTop (fun k => (smallBaseChange B S hS f hf).obj (W
      k)))
  {P : K → K → SmallEtale B S hS Y.1} {p₁ : ∀ k l, P k l ⟶ W k} {p₂ : ∀ k l, P k l ⟶ W l}
  (hlift : ∀ (V : SmallEtale B S hS X.1) (k l : K)
    (h : V ⟶ (smallBaseChange B S hS f hf).obj (W k))
    (h' : V ⟶ (smallBaseChange B S hS f hf).obj (W l)),
    ∃ t : V ⟶ (smallBaseChange B S hS f hf).obj (P k l),
      t ≫ (smallBaseChange B S hS f hf).map (p₁ k l) = h ∧
        t ≫ (smallBaseChange B S hS f hf).map (p₂ k l) = h')
  (hcoord : ∀ (k l : K) (a : Fin (n k)) (b : Fin (n l)),
    ((smallBaseChangeSharp B S hS f hf).hom.app (op (P k l))).hom
      ((he k).coord (p₁ k l) (res (sval M) (p₂ k l) (e l b)) a) =
    (he' k).coord ((smallBaseChange B S hS f hf).map (p₁ k l))
      (res (sval E) ((smallBaseChange B S hS f hf).map (p₂ k l)) (e' l b)) a)

/-- The direct image of an `𝒪_X`-module, as a module on `Y` whose sections over a chart are the
sections over its base change. -/
abbrev smallBaseChangePush (F : Modules.{u, u} B S hS X.1 X.2) : Modules.{u, u} B S hS Y.1 Y.2 :=
  (smallBaseChangeModulePushforward.{u, u} B S hS f hf).obj F

include hcoord hlift in
/-- The two transformation rules agree. -/
theorem compat_smallBaseChangePush_iff (hlift' : ∀ (V : SmallEtale B S hS Y.1) (k l : K) (h : V ⟶
    W k)
      (h' : V ⟶ W l), ∃ t : V ⟶ P k l, t ≫ p₁ k l = h ∧ t ≫ p₂ k l = h')
    (F : Modules.{u, u} B S hS X.1 X.2)
    (s : ∀ k, Fin (n k) → (sval F).obj (op ((smallBaseChange B S hS f hf).obj (W k)))) :
    Compat he (sval (smallBaseChangePush f hf F)) s ↔ Compat he' (sval F) s := by
  refine (compat_iff_pairCompat he (sval (smallBaseChangePush f hf F)) P p₁ p₂ hlift'
      (show ∀ k, Fin (n k) → (sval (smallBaseChangePush f hf F)).obj (op (W k)) from s)).trans
      (Iff.trans ?_ (compat_iff_pairCompat he' (sval F)
      (fun k l => (smallBaseChange B S hS f hf).obj (P k l))
      (fun k l => (smallBaseChange B S hS f hf).map (p₁ k l))
      (fun k l => (smallBaseChange B S hS f hf).map (p₂ k l)) hlift s).symm)
  refine forall_congr' fun k => forall_congr' fun l => forall_congr' fun b => ?_
  refine Eq.congr_right ?_
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← hcoord k l a b]
  rfl

variable (hlift' : ∀ (V : SmallEtale B S hS Y.1) (k l : K) (h : V ⟶ W k)
      (h' : V ⟶ W l), ∃ t : V ⟶ P k l, t ≫ p₁ k l = h ∧ t ≫ p₂ k l = h')

/-- The morphism `M ⟶ f_*F` corresponding to a morphism `f^*M ⟶ F`, with `f_*F` read through the
base change of charts. -/
def toSmallBaseChangePush {F : Modules.{u, u} B S hS X.1 X.2} (φ : (modulePullback B S hS f).obj M
    ⟶ F) :
    M ⟶ smallBaseChangePush f hf F :=
  (modulePullbackAdjunction B S hS f).homEquiv M F φ ≫
    (modulePushforwardChartIso B S hS f hf).hom.app F

/-- `toSmallBaseChangePush` is natural in the target: the morphism corresponding to `φ ≫ ψ` is
the one corresponding to `φ`, followed by the direct image of `ψ`. -/
theorem toSmallBaseChangePush_comp {F F' : Modules.{u, u} B S hS X.1 X.2}
    (φ : (modulePullback B S hS f).obj M ⟶ F) (ψ : F ⟶ F') :
    toSmallBaseChangePush f hf M (φ ≫ ψ) =
      toSmallBaseChangePush f hf M φ ≫ (smallBaseChangeModulePushforward.{u, u} B S hS f
          hf).map ψ := by
  simp only [toSmallBaseChangePush, Adjunction.homEquiv_naturality_right, Category.assoc]
  rw [(modulePushforwardChartIso B S hS f hf).hom.naturality ψ]
  exact (Category.assoc _ _ _).symm

include hW hW' hlift hlift' hcoord in
/-- **Morphisms out of `f^*M` are morphisms out of `E`**, for every `𝒪_X`-module. -/
def homEquivOfFrames (F : Modules.{u, u} B S hS X.1 X.2) :
    ((modulePullback B S hS f).obj M ⟶ F) ≃ (E ⟶ F) :=
  ((modulePullbackAdjunction B S hS f).homEquiv M F).trans <|
  (Iso.homCongr (Iso.refl M) ((modulePushforwardChartIso B S hS f hf).app F)).trans <|
  (SheafOfModules.fullyFaithfulForget _).homEquiv.trans <|
  (homEquiv he hW (sval (smallBaseChangePush f hf F)) (isSheaf_sval B S hS _)).trans <|
  (Equiv.subtypeEquivRight (fun s => compat_smallBaseChangePush_iff f hf M he E he' hlift hcoord
      hlift' F s)).trans <|
  (homEquiv he' hW' (sval F) (isSheaf_sval B S hS F)).symm.trans <|
  (SheafOfModules.fullyFaithfulForget _).homEquiv.symm

include hW hW' hlift hlift' hcoord in
/-- The morphism `E ⟶ F` corresponding to `φ : f^*M ⟶ F` sends the frame element `e' k a` to the
image of `e k a` under the corresponding morphism `M ⟶ f_*F`. -/
theorem homEquivOfFrames_app_frame (F : Modules.{u, u} B S hS X.1 X.2)
    (φ : (modulePullback B S hS f).obj M ⟶ F) (k : K) (a : Fin (n k)) :
    (homEquivOfFrames f hf hW M he E he' hW' hlift hcoord hlift' F φ).val.app
        (op ((smallBaseChange B S hS f hf).obj (W k))) (e' k a) =
      (toSmallBaseChangePush f hf M φ).val.app (op (W k)) (e k a) := by
  unfold homEquivOfFrames
  simp only [Equiv.trans_apply]
  refine (glue_app_frame he' hW' (sval F) (isSheaf_sval B S hS F) _ k a).trans ?_
  simp only [Iso.homCongr_apply, Iso.refl_inv, Category.id_comp]
  rfl

include hW hW' hlift hlift' hcoord in
/-- `homEquivOfFrames` is natural in the target `𝒪_X`-module: it sends `φ ≫ ψ` to the image of `φ`
followed by `ψ`. -/
theorem homEquivOfFrames_comp {F F' : Modules.{u, u} B S hS X.1 X.2}
    (φ : (modulePullback B S hS f).obj M ⟶ F) (ψ : F ⟶ F') :
    homEquivOfFrames f hf hW M he E he' hW' hlift hcoord hlift' F' (φ ≫ ψ) =
      homEquivOfFrames f hf hW M he E he' hW' hlift hcoord hlift' F φ ≫ ψ := by
  apply (SheafOfModules.fullyFaithfulForget _).map_injective
  refine hom_ext_of_frames he' hW' (sval F') (isSheaf_sval B S hS F') (fun k a => ?_)
  change (homEquivOfFrames f hf hW M he E he' hW' hlift hcoord hlift' F' (φ ≫ ψ)).val.app _ _ =
    ψ.val.app _ ((homEquivOfFrames f hf hW M he E he' hW' hlift hcoord hlift' F φ).val.app _ _)
  refine (homEquivOfFrames_app_frame f hf hW M he E he' hW' hlift hcoord hlift' F' (φ ≫ ψ)
    k a).trans ?_
  refine Eq.trans ?_ (congrArg (fun z => ψ.val.app (op ((smallBaseChange B S hS f hf).obj (W k))) z)
    (homEquivOfFrames_app_frame f hf hW M he E he' hW' hlift hcoord hlift' F φ k a)).symm
  rw [toSmallBaseChangePush_comp]
  rfl

include hW hW' hlift hlift' hcoord in
/-- **The comparison**: `E ≅ f^*M`. -/
theorem nonempty_iso_modulePullback_of_frames :
    Nonempty (E ≅ (modulePullback B S hS f).obj M) := by
  let α : coyoneda.obj (op ((modulePullback B S hS f).obj M)) ≅ coyoneda.obj (op E) :=
    NatIso.ofComponents
      (fun F => (homEquivOfFrames f hf hW M he E he' hW' hlift hcoord hlift' F).toIso)
      (fun {F F'} ψ => by
        ext φ
        exact (homEquivOfFrames_comp f hf hW M he E he' hW' hlift hcoord hlift' φ ψ))
  exact ⟨(Coyoneda.fullyFaithful.preimageIso α).unop⟩

end Comparison

end AlgebraicGeometry.Space
