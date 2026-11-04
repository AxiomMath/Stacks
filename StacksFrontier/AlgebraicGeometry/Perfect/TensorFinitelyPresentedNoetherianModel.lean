module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.SchemePropertiesPermanence
public import StacksFrontier.AlgebraicGeometry.ChowFiniteType.ModuleSupport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.FlatDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.ModuleIsoFlatness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportPullback.BaseChange
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.AlgebraicGeometry.Perfect.LimitPerfectObjectsDescent
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismDescentGlue
public import StacksFrontier.AlgebraicGeometry.Perfect.TensorFinitelyPresentedPerfectPushforward
public import StacksFrontier.AlgebraicGeometry.Limits.AffineNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The base changes of a scheme of finite presentation along a directed system

Let `i ↦ S_i` be a directed inverse system of quasi-compact and quasi-separated schemes with
affine transition morphisms and limit `S`, and let `X₀` be of finite presentation over `S_{i₀}`.
The base changes `X_i = S_i ×_{S_{i₀}} X₀` for `i ≥ i₀` form again such a system, with limit
`S ×_{S_{i₀}} X₀`.

## Main definitions

* `AlgebraicGeometry.Scheme.overOpEquiv`: for a preorder `J` and `j₀ : J`, the category of
  stages `j ≥ j₀` is equivalent to the over category `Over (op j₀)` of `Jᵒᵖ`.
* `AlgebraicGeometry.Scheme.baseChangeDescentSituation`: the system `j ↦ S_j ×_{S_{j₀}} X₀`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable {J : Type u} [Preorder J]

/-- The functor from the stages `j ≥ j₀` of a preorder to the over category `Over (op j₀)` of
its opposite. -/
def overOpFunctor (j₀ : J) : {j : J // j₀ ≤ j}ᵒᵖ ⥤ Over (op j₀) where
  obj j := Over.mk (homOfLE j.unop.2).op
  map φ :=
    Over.homMk (homOfLE (leOfHom φ.unop)).op (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
  map_id _ := Over.OverMorphism.ext (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
  map_comp _ _ := Over.OverMorphism.ext (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

/-- The inverse of `AlgebraicGeometry.Scheme.overOpFunctor`. -/
def overOpInverse (j₀ : J) : Over (op j₀) ⥤ {j : J // j₀ ≤ j}ᵒᵖ where
  obj k := op ⟨k.left.unop, leOfHom k.hom.unop⟩
  map φ := (homOfLE (leOfHom φ.left.unop)).op
  map_id _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  map_comp _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

/-- The stages `j ≥ j₀` of a preorder form a category equivalent to `Over (op j₀)`. -/
def overOpEquiv (j₀ : J) : {j : J // j₀ ≤ j}ᵒᵖ ≌ Over (op j₀) where
  functor := overOpFunctor j₀
  inverse := overOpInverse j₀
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _))
  counitIso := NatIso.ofComponents (fun _ => Over.isoMk (Iso.refl _)
      (Quiver.Hom.unop_inj (Subsingleton.elim _ _)))
    (fun _ => Over.OverMorphism.ext (Quiver.Hom.unop_inj (Subsingleton.elim _ _)))
  functor_unitIso_comp _ := Over.OverMorphism.ext (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

/-- The stages beyond a fixed stage of a directed preorder are directed. -/
instance isDirected_subtype_le [IsDirected J (· ≤ ·)] (j₀ : J) :
    IsDirected {j : J // j₀ ≤ j} (· ≤ ·) :=
  ⟨fun a b => by
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩⟩

/-- **The base changes of a scheme of finite presentation along a descent situation.** For a
directed system `S_j` of quasi-compact and quasi-separated schemes with affine transition
morphisms and limit `S`, and `X₀` of finite presentation over the base stage `S_{j₀}`, the system
`j ↦ S_j ×_{S_{j₀}} X₀` over the stages `j ≥ j₀`, with limit `S ×_{S_{j₀}} X₀`. -/
@[ega "IV 8.1.1" "special case", sga "3 VIB 10.0"]
def baseChangeDescentSituation [IsDirected J (· ≤ ·)] (D : DescentSituation.{u, u} J)
    (X₀ : Over (D.system.obj (op D.base))) (hX₀ : FinitePresentation X₀.hom) :
    DescentSituation.{u, u} {j : J // D.base ≤ j} :=
  haveI : Nonempty J := ⟨D.base⟩
  haveI : IsFiltered J := isFiltered_of_directed_le_nonempty J
  haveI : ∀ {i j : Jᵒᵖ} (e : i ⟶ j), IsAffineHom (D.system.map e) := D.transition_affine
  haveI : QuasiCompact X₀.hom := hX₀.quasiCompact
  haveI : QuasiSeparated X₀.hom := hX₀.quasiSeparated
  { system := overOpFunctor D.base ⋙ baseChangeDiagram D.system (op D.base) X₀
    transition_affine := fun _ => isAffineHom_baseChangeDiagram_map D.system (op D.base) X₀ _
    quasiCompact := fun j =>
      haveI : CompactSpace ((Over.post D.system).obj ((overOpFunctor D.base).obj (op j))).left :=
        D.quasiCompact j.1
      haveI : QuasiSeparatedSpace
          ((Over.post D.system).obj ((overOpFunctor D.base).obj (op j))).left :=
        D.quasiSeparated j.1
      haveI := D.quasiCompact D.base
      haveI := D.quasiSeparated D.base
      haveI : CompactSpace X₀.left := QuasiCompact.compactSpace_of_compactSpace X₀.hom
      haveI : QuasiSeparatedSpace X₀.left := quasiSeparatedSpace_of_quasiSeparated X₀.hom
      (compactSpace_and_quasiSeparatedSpace_pullback _ _).1
    quasiSeparated := fun j =>
      haveI : CompactSpace ((Over.post D.system).obj ((overOpFunctor D.base).obj (op j))).left :=
        D.quasiCompact j.1
      haveI : QuasiSeparatedSpace
          ((Over.post D.system).obj ((overOpFunctor D.base).obj (op j))).left :=
        D.quasiSeparated j.1
      haveI := D.quasiCompact D.base
      haveI := D.quasiSeparated D.base
      haveI : CompactSpace X₀.left := QuasiCompact.compactSpace_of_compactSpace X₀.hom
      haveI : QuasiSeparatedSpace X₀.left := quasiSeparatedSpace_of_quasiSeparated X₀.hom
      (compactSpace_and_quasiSeparatedSpace_pullback _ _).2
    limitCone := (baseChangeCone D.system (op D.base) X₀ D.limitCone).whisker
      (overOpFunctor D.base)
    isLimit :=
      (isLimitBaseChangeCone D.system (op D.base) X₀ D.limitCone D.isLimit).whiskerEquivalence
        (overOpEquiv D.base)
    base := ⟨D.base, le_rfl⟩ }

/-! ### Base change steps along a limit -/

section Steps

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- **One base change step.** If `X` is the base change of `p : Y ⟶ T` along `π : S ⟶ T`, and
`π` factors as `S ⟶ T' ⟶ T`, then `X` is the base change of `Y ×_T T' ⟶ T'` along `S ⟶ T'`. -/
theorem isPullback_lift_snd {Y T T' : Scheme.{u}} {p : Y ⟶ T} {g : X ⟶ Y} {π : S ⟶ T}
    (hsq : IsPullback g f p π) (b : T' ⟶ T) (b' : S ⟶ T') (hb : b' ≫ b = π) :
    IsPullback (pullback.lift g (f ≫ b') (by rw [Category.assoc, hb, hsq.w]))
      f (pullback.snd p b) b' :=
  IsPullback.of_right (by rwa [pullback.lift_fst, hb]) (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback p b)

/-- The pullback of a module along a lift through a fibre product. -/
def pullbackLiftFstIso {Y T T' : Scheme.{u}} {p : Y ⟶ T} {g : X ⟶ Y} (b : T' ⟶ T) (k : X ⟶ T')
    (w : g ≫ p = k ≫ b) (N : Y.Modules) :
    (Scheme.Modules.pullback (pullback.lift g k w)).obj
        ((Scheme.Modules.pullback (pullback.fst p b)).obj N) ≅
      (Scheme.Modules.pullback g).obj N :=
  (Scheme.Modules.pullbackComp _ _).app N ≪≫
    (Scheme.Modules.pullbackCongr (pullback.lift_fst _ _ _)).app N

/-- **Properness of a scheme-theoretic support over the base, read along `Over.pullback`.** -/
theorem isProper_schemeTheoreticSupport_overPullback_iff {Y T T' : Scheme.{u}} (p : Y ⟶ T)
    [LocallyOfFiniteType p] (b : T' ⟶ T) (N : (pullback p b).Modules) [N.IsQuasicoherent]
    [N.IsFiniteType] :
    IsProper ((Scheme.Modules.schemeTheoreticSupport N).subschemeι ≫
        ((Over.pullback b).map (Over.homMk p : Over.mk p ⟶ Over.mk (𝟙 T))).left) ↔
      IsProperOver (pullback.snd p b) ⟨SheafOfModules.supp N, SheafOfModules.isClosed_supp N⟩ := by
  have hm : ((Over.pullback b).map (Over.homMk p : Over.mk p ⟶ Over.mk (𝟙 T))).left ≫
      (asIso (pullback.snd (𝟙 T) b)).hom = pullback.snd p b := by
    dsimp only [Over.pullback, asIso_hom, Comma.mapLeft_obj_hom, Functor.id_obj,
      Over.map_obj_left, Over.map_obj_hom, Over.homMk_left]
    exact pullback.lift_snd _ _ _
  rw [Scheme.Modules.isProperOver_supp_iff_isProper_schemeTheoreticSupport, ← hm,
    ← Category.assoc]
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsProper) _ _).symm

end Steps

section Limit

/-- A module of finite presentation on a scheme is of finite type. -/
local instance isFiniteType_of_isFinitePresentation_scheme {Z : Scheme.{u}} (M : Z.Modules)
    [M.IsFinitePresentation] : M.IsFiniteType :=
  (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isFinitePresentation M
    inferInstance).2

/-- A module of finite presentation on a scheme is quasi-coherent. -/
local instance isQuasicoherent_of_isFinitePresentation_scheme {Z : Scheme.{u}} (M : Z.Modules)
    [M.IsFinitePresentation] : M.IsQuasicoherent :=
  (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isFinitePresentation M
    inferInstance).1

variable {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J] (D : Jᵒᵖ ⥤ Scheme.{u})
  [∀ {i j : Jᵒᵖ} (e : i ⟶ j), IsAffineHom (D.map e)] [∀ i : Jᵒᵖ, CompactSpace (D.obj i)]
  [∀ i : Jᵒᵖ, QuasiSeparatedSpace (D.obj i)] (c : Cone D) (hc : IsLimit c)

include hc in
/-- **Properness of the support at a stage** ([Stacks, Tag 081G] with [Stacks, Tag 0CYS]). If
the support of the pullback of a finitely presented module on `Y` over `D.obj i` is proper over
the limit, then it is proper over some later stage. -/
theorem exists_isProperOver_supp_baseChange (i : Jᵒᵖ) {Y : Scheme.{u}} (p : Y ⟶ D.obj i)
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    (N : Y.Modules) [N.IsFinitePresentation]
    (hlim : IsProperOver (pullback.snd p (c.π.app i))
        ⟨SheafOfModules.supp ((Scheme.Modules.pullback (pullback.fst p (c.π.app i))).obj N),
          SheafOfModules.isClosed_supp _⟩) :
    ∃ (k : Jᵒᵖ) (e : k ⟶ i), IsProperOver (pullback.snd p (D.map e))
        ⟨SheafOfModules.supp ((Scheme.Modules.pullback (pullback.fst p (D.map e))).obj N),
          SheafOfModules.isClosed_supp _⟩ := by
  have : IsFiltered J := isFiltered_of_directed_le_nonempty J
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated p
  let f₀ : Over.mk p ⟶ Over.mk (𝟙 (D.obj i)) := Over.homMk p
  have : LocallyOfFiniteType f₀.left := inferInstanceAs (LocallyOfFiniteType p)
  have : CompactSpace (Over.mk p).left := ‹_›
  have : QuasiSeparatedSpace (Over.mk p).left := ‹_›
  have : CompactSpace (Over.mk (𝟙 (D.obj i))).left := inferInstanceAs (CompactSpace (D.obj i))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  obtain ⟨k, e, hk⟩ := exists_isProper_schemeTheoreticSupport_baseChange_of_isLimit D c i hc
    (Over.mk p) (Over.mk (𝟙 _)) f₀ N
    ((isProper_schemeTheoreticSupport_overPullback_iff p (c.π.app i) _).2 hlim)
  exact ⟨k, e, (isProper_schemeTheoreticSupport_overPullback_iff p (D.map e) _).1 hk⟩

include hc in
/-- **Flatness at a stage** ([Stacks, Tag 05LY]). If the pullback of a finitely presented module
on `Y` over `D.obj i` is flat over the limit, then it is flat over some later stage. -/
theorem exists_isFlatOver_baseChange (i : Jᵒᵖ) {Y : Scheme.{u}} (p : Y ⟶ D.obj i)
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    (N : Y.Modules) [N.IsFinitePresentation]
    (hlim : IsFlatOver (pullback.snd p (c.π.app i)).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst p (c.π.app i))).obj N)) :
    ∃ (k : Jᵒᵖ) (e : k ⟶ i), IsFlatOver (pullback.snd p (D.map e)).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst p (D.map e))).obj N) := by
  have : IsFiltered J := isFiltered_of_directed_le_nonempty J
  obtain ⟨k, e, hk⟩ := @eventually_isFlatOver_modulePullback Jᵒᵖ _ _ _ D c hc _ _ _ i
    (Over.mk p) (Over.mk (𝟙 _)) ⟨inferInstanceAs (LocallyOfFinitePresentation p),
      inferInstanceAs (QuasiCompact p), inferInstanceAs (QuasiSeparated p)⟩
    ⟨inferInstanceAs (LocallyOfFinitePresentation (𝟙 _)),
      inferInstanceAs (QuasiCompact (𝟙 _)), inferInstanceAs (QuasiSeparated (𝟙 _))⟩
    (Over.homMk p) N (inferInstanceAs N.IsQuasicoherent) ‹N.IsFinitePresentation›
    ((isFlatOver_overPullback_map_iff (Over.mk p) (c.π.app i) _).2 hlim)
  exact ⟨k, e, (isFlatOver_overPullback_map_iff (Over.mk p) (D.map e) _).1 hk⟩

omit [IsDirected J (· ≤ ·)] [Nonempty J] [∀ {i j : Jᵒᵖ} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i : Jᵒᵖ, CompactSpace (D.obj i)] [∀ i : Jᵒᵖ, QuasiSeparatedSpace (D.obj i)] in
/-- **The conditions at the limit.** If `X ⟶ S` is the base change of `p : Y ⟶ D.obj i` along the
projection from the limit and `M ≅ g^*N` is flat over `S` with support proper over `S`, then the
pullback of `N` to `Y ×_{D.obj i} S` is flat over `S` with support proper over `S`. -/
theorem limit_isFlatOver_and_isProperOver (i : Jᵒᵖ) {X Y : Scheme.{u}} {f : X ⟶ c.pt}
    {p : Y ⟶ D.obj i} [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    [LocallyOfFiniteType f] {g : X ⟶ Y} (hsq : IsPullback g f p (c.π.app i)) (N : Y.Modules)
    [N.IsFinitePresentation] {M : X.Modules} [M.IsFinitePresentation]
    (eM : (Scheme.Modules.pullback g).obj N ≅ M) (hflat : IsFlatOver f.toLRSHom.toShHom M)
    (hsupp : IsProperOver f ⟨SheafOfModules.supp M, SheafOfModules.isClosed_supp M⟩) :
    IsFlatOver (pullback.snd p (c.π.app i)).toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst p (c.π.app i))).obj N) ∧
      IsProperOver (pullback.snd p (c.π.app i))
        ⟨SheafOfModules.supp ((Scheme.Modules.pullback (pullback.fst p (c.π.app i))).obj N),
          SheafOfModules.isClosed_supp _⟩ := by
  have := (isPullback_lift_snd hsq (c.π.app i) (𝟙 _) (Category.id_comp _)).isIso_fst_of_isIso
  let γ := pullback.lift g (f ≫ 𝟙 c.pt) (by rw [Category.assoc, Category.id_comp, hsq.w])
  have : IsIso (𝟙 c.pt) := IsIso.id _
  have hsq' : IsPullback (inv γ) (pullback.snd p (c.π.app i)) f (𝟙 c.pt) :=
    IsPullback.of_horiz_isIso ⟨by simp [IsIso.inv_comp_eq, γ, pullback.lift_snd]⟩
  let N' := (Scheme.Modules.pullback (pullback.fst p (c.π.app i))).obj N
  have eN : N' ≅ (Scheme.Modules.pullback (inv γ)).obj M :=
    (Scheme.Modules.pullbackId _).symm.app N' ≪≫
      (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id γ)).symm.app N' ≪≫
      ((Scheme.Modules.pullbackComp (inv γ) γ).app N').symm ≪≫
      (Scheme.Modules.pullback (inv γ)).mapIso (pullbackLiftFstIso _ _ _ N ≪≫ eM)
  refine ⟨(isFlatOver_iff_of_moduleIso _ eN).2 (@modulePullback_isFlatOver _ _ _ _ _ _ _ _ hsq' M
    (isQuasicoherent_of_isFinitePresentation_scheme M) hflat), ?_⟩
  convert isProperOver_preimage_baseChange (inv γ) (pullback.snd p (c.π.app i)) f (𝟙 c.pt)
    hsq' _ hsupp using 2
  ext x
  show x ∈ SheafOfModules.supp N' ↔ x ∈ (inv γ) ⁻¹' SheafOfModules.supp M
  rw [SheafOfModules.supp_eq_of_iso eN, Stacks.Modules.supp_pullback]

include hc in
/-- **A stage at which the module is flat with proper support.** If `X ⟶ S` is the base change of
`p : Y ⟶ D.obj i` and `M ≅ g^*N` for a finitely presented `N`, with `M` flat over `S` and with
support proper over `S`, then at some later stage `k` there is a base change
`Y' = Y ×_{D.obj i} D.obj k` and a finitely presented module on it, flat over `D.obj k` with
support proper over `D.obj k`, pulling back to `M`. -/
theorem exists_stage_isFlatOver_isProperOver (i : Jᵒᵖ) {X Y : Scheme.{u}} {f : X ⟶ c.pt}
    {p : Y ⟶ D.obj i} [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    [LocallyOfFiniteType f] {g : X ⟶ Y} (hsq : IsPullback g f p (c.π.app i)) (N : Y.Modules)
    [N.IsFinitePresentation] {M : X.Modules} [M.IsFinitePresentation]
    (eM : (Scheme.Modules.pullback g).obj N ≅ M) (hflat : IsFlatOver f.toLRSHom.toShHom M)
    (hsupp : IsProperOver f ⟨SheafOfModules.supp M, SheafOfModules.isClosed_supp M⟩) :
    ∃ (k : Jᵒᵖ) (Y' : Scheme.{u}) (p' : Y' ⟶ D.obj k) (t : Y' ⟶ Y) (g' : X ⟶ Y')
      (_ : LocallyOfFinitePresentation p') (_ : QuasiCompact p') (_ : QuasiSeparated p'),
        IsPullback g' f p' (c.π.app k) ∧ g' ≫ t = g ∧
        ∃ (N' : Y'.Modules) (_ : N'.IsFinitePresentation),
          IsFlatOver p'.toLRSHom.toShHom N' ∧
            IsProperOver p' ⟨SheafOfModules.supp N', SheafOfModules.isClosed_supp N'⟩ ∧
            Nonempty ((Scheme.Modules.pullback g').obj N' ≅ M) := by
  -- the support becomes proper at a stage
  obtain ⟨k₄, e₄, h₄⟩ := exists_isProperOver_supp_baseChange D c hc i p N
    (limit_isFlatOver_and_isProperOver D c i hsq N eM hflat hsupp).2
  have hsq₄ := isPullback_lift_snd hsq (D.map e₄) (c.π.app k₄) (c.w e₄)
  let N₄ := (Scheme.Modules.pullback (pullback.fst p (D.map e₄))).obj N
  let eM₄ := pullbackLiftFstIso (D.map e₄) (f ≫ c.π.app k₄)
    (by rw [Category.assoc, c.w e₄, hsq.w]) N ≪≫ eM
  -- then the module becomes flat at a further stage
  obtain ⟨k₅, e₅, h₅⟩ := exists_isFlatOver_baseChange D c hc k₄ (pullback.snd p (D.map e₄)) N₄
    (limit_isFlatOver_and_isProperOver D c k₄ hsq₄ N₄ eM₄ hflat hsupp).1
  have hsq₅ := isPullback_lift_snd hsq₄ (D.map e₅) (c.π.app k₅) (c.w e₅)
  exact ⟨k₅, _, pullback.snd (pullback.snd p (D.map e₄)) (D.map e₅),
    pullback.fst (pullback.snd p (D.map e₄)) (D.map e₅) ≫ pullback.fst p (D.map e₄), _,
    inferInstance, inferInstance, inferInstance, hsq₅,
    by rw [← Category.assoc, pullback.lift_fst, pullback.lift_fst],
    (Scheme.Modules.pullback (pullback.fst (pullback.snd p (D.map e₄)) (D.map e₅))).obj N₄,
    inferInstance, h₅, isProperOver_supp_pullback _ _ _ _ (IsPullback.of_hasPullback _ _) N₄ h₄,
    ⟨pullbackLiftFstIso (D.map e₅) _ _ N₄ ≪≫ eM₄⟩⟩

end Limit

/-! ### Descending a perfect object and a finitely presented module -/

section Descent

attribute [local instance 10000] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

variable {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)]

/-- A cartesian square stays cartesian when two of its sides are replaced by equal morphisms. -/
theorem isPullback_of_eq {P A B Z : Scheme.{u}} {fst fst' : P ⟶ A} {snd : P ⟶ B} {f : A ⟶ Z}
    {g g' : B ⟶ Z} (h : IsPullback fst snd f g) (hf : fst = fst') (hg : g = g') :
    IsPullback fst' snd f g' := by
  subst hf hg
  exact h

/-- The leg of the cone of `AlgebraicGeometry.Scheme.baseChangeDescentSituation` at a stage is a
base change of the structure morphism of that stage. -/
theorem isPullback_baseChangeDescentSituation_π (D : DescentSituation.{u, u} J)
    (X₀ : Over (D.system.obj (op D.base))) (hX₀ : FinitePresentation X₀.hom)
    (j : {j : J // D.base ≤ j}) :
    IsPullback ((baseChangeDescentSituation D X₀ hX₀).limitCone.π.app (op j))
      (pullback.fst (D.limitCone.π.app (op D.base)) X₀.hom)
      (pullback.fst (D.system.map (homOfLE j.2).op) X₀.hom) (D.limitCone.π.app (op j.1)) := by
  refine IsPullback.of_right (h₁₂ := pullback.snd (D.system.map (homOfLE j.2).op) X₀.hom)
    (h₂₂ := D.system.map (homOfLE j.2).op) ?_ ?_
    (IsPullback.of_hasPullback (D.system.map (homOfLE j.2).op) X₀.hom).flip
  · exact isPullback_of_eq
      (IsPullback.of_hasPullback (D.limitCone.π.app (op D.base)) X₀.hom).flip
      (baseChangeCone_π_snd D.system (op D.base) X₀ D.limitCone
        ((overOpFunctor D.base).obj (op j))).symm
      (D.limitCone.w (homOfLE j.2).op).symm
  · exact baseChangeCone_π_fst D.system (op D.base) X₀ D.limitCone
      ((overOpFunctor D.base).obj (op j))

/-- **Descending a perfect object and a finitely presented module.** Let `X ⟶ S` be the base
change of a morphism of finite presentation `p : Y ⟶ S_{j₀}` along the projection from the limit
of a descent situation. A perfect object of `D(𝒪_X)` and a finitely presented `𝒪_X`-module are the
pullbacks of a perfect object and of a finitely presented module on a base change of `Y` to some
later stage ([Stacks, Tag 09RF] and [Stacks, Tag 01ZR]). -/
@[ega "IV 8.1.1" "partial"]
theorem exists_stage_perfect_finitePresentation (D : DescentSituation.{u, u} J) {X Y : Scheme.{u}}
    {f : X ⟶ D.limitCone.pt} {p : Y ⟶ D.system.obj (op D.base)} (hp : FinitePresentation p)
    {g : X ⟶ Y} (hsq : IsPullback g f p (D.limitCone.π.app (op D.base)))
    (E : DerivedCategory X.Modules) (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (M : X.Modules) [M.IsFinitePresentation] :
    ∃ (j : J) (_ : D.base ≤ j) (Y' : Scheme.{u}) (p' : Y' ⟶ D.system.obj (op j)) (g' : X ⟶ Y')
      (_ : LocallyOfFinitePresentation p') (_ : QuasiCompact p') (_ : QuasiSeparated p'),
      IsPullback g' f p' (D.limitCone.π.app (op j)) ∧
        (∃ E' : DerivedCategory Y'.Modules, RingedSpace.IsPerfect (X := Y'.toRingedSpace) E' ∧
          Nonempty ((derivedPullback g'.toLRSHom.toShHom).obj E' ≅ E)) ∧
        ∃ (N : Y'.Modules) (_ : N.IsFinitePresentation),
          Nonempty ((Scheme.Modules.pullback g').obj N ≅ M) := by
  let X₀ : Over (D.system.obj (op D.base)) := Over.mk p
  let D' := baseChangeDescentSituation D X₀ hp
  have : Nonempty J := ⟨D.base⟩
  have : IsFiltered {j : J // D.base ≤ j} :=
    isFiltered_of_directed_le_nonempty {j : J // D.base ≤ j}
  let φ : X ≅ D'.limitCone.pt := hsq.flip.isoPullback
  -- descend `E`
  let EP := (derivedPullback φ.inv.toLRSHom.toShHom).obj E
  obtain ⟨j₁, hj₁, E₁, hE₁, ⟨eE⟩⟩ := D'.exists_isPerfect_derivedPullback_iso EP
    (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ E hE)
  -- descend `M`
  let MP := (Scheme.Modules.pullback φ.inv).obj M
  have : ∀ {i j : {j : J // D.base ≤ j}ᵒᵖ} (e : i ⟶ j), IsAffineHom (D'.system.map e) :=
    D'.transition_affine
  have : ∀ j : {j : J // D.base ≤ j}ᵒᵖ, CompactSpace (D'.system.obj j) :=
    fun j => D'.quasiCompact j.unop
  have : ∀ j : {j : J // D.base ≤ j}ᵒᵖ, QuasiSeparatedSpace (D'.system.obj j) :=
    fun j => D'.quasiSeparated j.unop
  obtain ⟨k, M₂, hM₂, ⟨eM⟩⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_qcqs
      D'.system D'.limitCone D'.isLimit MP
  -- a common stage
  obtain ⟨j₃, h₁₃, h₂₃⟩ := (isDirected_subtype_le D.base).directed j₁ k.unop
  let π₃ := D'.limitCone.π.app (op j₃)
  let t₁ := D'.system.map (homOfLE h₁₃).op
  let t₂ := D'.system.map (homOfLE h₂₃).op
  let p' : D'.system.obj (op j₃) ⟶ D.system.obj (op j₃.1) :=
    pullback.fst (D.system.map (homOfLE j₃.2).op) X₀.hom
  have hφ : IsPullback φ.hom f (pullback.fst (D.limitCone.π.app (op D.base)) X₀.hom)
      (𝟙 D.limitCone.pt) :=
    IsPullback.of_horiz_isIso ⟨hsq.flip.isoPullback_hom_fst.trans (Category.comp_id f).symm⟩
  have hsqY : IsPullback (φ.hom ≫ π₃) f p' (D.limitCone.π.app (op j₃.1)) :=
    isPullback_of_eq (hφ.paste_horiz (isPullback_baseChangeDescentSituation_π D X₀ hp j₃)) rfl
      (Category.id_comp _)
  have hb := (IsPullback.of_hasPullback (D.system.map (homOfLE j₃.2).op) X₀.hom).flip
  have hw (j : {j : J // D.base ≤ j}) (h : j ≤ j₃) :
      (φ.hom ≫ π₃) ≫ D'.system.map (homOfLE h).op = φ.hom ≫ D'.limitCone.π.app (op j) := by
    rw [Category.assoc, D'.limitCone.w (homOfLE h).op]
  refine ⟨j₃.1, j₃.2, _, p', φ.hom ≫ π₃,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hb hp.1,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hb hp.2.1,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hb hp.2.2, hsqY,
    ⟨(derivedPullback t₁.toLRSHom.toShHom).obj E₁,
      RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ E₁ hE₁, ⟨?_⟩⟩,
    (Scheme.Modules.pullback t₂).obj M₂, inferInstance, ⟨?_⟩⟩
  · exact (Stacks.DerivedPullback.schemeFactorIso _ t₁ _ (hw j₁ h₁₃)).app E₁ ≪≫
      ((Stacks.DerivedPullback.schemeFactorIso φ.hom (D'.limitCone.π.app (op j₁)) _ rfl).app
        E₁).symm ≪≫
      (derivedPullback φ.hom.toLRSHom.toShHom).mapIso eE ≪≫
      (Stacks.DerivedPullback.schemeFactorIso φ.hom φ.inv (𝟙 _) φ.hom_inv_id).app E ≪≫
      (Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso _).app E
  · exact (Scheme.Modules.pullbackComp _ t₂).app M₂ ≪≫
      (Scheme.Modules.pullbackCongr (hw k.unop h₂₃)).app M₂ ≪≫
      ((Scheme.Modules.pullbackComp φ.hom (D'.limitCone.π.app k)).app M₂).symm ≪≫
      (Scheme.Modules.pullback φ.hom).mapIso eM.symm ≪≫
      (Scheme.Modules.pullbackComp φ.hom φ.inv).app M ≪≫
      (Scheme.Modules.pullbackCongr φ.hom_inv_id).app M ≪≫
      (Scheme.Modules.pullbackId _).app M

end Descent

/-! ### The affine case for a single module -/

section Affine

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local implicit_reducible] StacksDraft.KFlat.modulePullback

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedPullbackTensor (pullbackComplex)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

/-- A module of finite presentation on a scheme is quasi-coherent. -/
local instance isQuasicoherent_of_isFinitePresentation_scheme' {Z : Scheme.{u}} (M : Z.Modules)
    [M.IsFinitePresentation] : M.IsQuasicoherent :=
  (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isFinitePresentation M
    inferInstance).1

/-- A module of finite presentation on a scheme is of finite type. -/
local instance isFiniteType_of_isFinitePresentation_scheme' {Z : Scheme.{u}} (M : Z.Modules)
    [M.IsFinitePresentation] : M.IsFiniteType :=
  (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isFinitePresentation M
    inferInstance).2

/-- The pullback of a module placed in degree zero is the pullback of the module placed in degree
zero. -/
def pullbackComplexSingleDegreeIso {X Y : Scheme.{u}} (g : X ⟶ Y) (N : Y.Modules) :
    (pullbackComplex g.toLRSHom.toShHom).obj (ProperFlatBaseChange.singleDegreeComplex N) ≅
      ProperFlatBaseChange.singleDegreeComplex ((Scheme.Modules.pullback g).obj N) :=
  (HomologicalComplex.singleMapHomologicalComplex
    (StacksDraft.KFlat.modulePullback g.toLRSHom.toShHom) (ComplexShape.up ℤ) 0).app N

/-- **The perfectness half of [Stacks, Tag 0A1H] over an affine base, for a single module.** Let
`S` be affine, `f : X ⟶ S` of finite presentation, `E` perfect and `ℳ` a finitely presented
`𝒪_X`-module flat over `S` whose support is proper over `S`. Then `Rf_*(E ⊗^L ℳ)` is perfect. The
data descend to a Noetherian stage of an approximation of `S` ([Stacks, Tag 01ZM],
[Stacks, Tag 01ZR], [Stacks, Tag 09RF], [Stacks, Tag 05LY], [Stacks, Tag 081G]), where
[Stacks, Tag 0DJQ] applies, and the conclusion is transported back by [Stacks, Tag 0A1D]. -/
theorem isPerfect_derivedPushforward_tensor_singleDegree_of_isAffine {X S : Scheme.{u}}
    [IsAffine S] (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) (M : X.Modules)
    [M.IsFinitePresentation] (hflat : IsFlatOver f.toLRSHom.toShHom M)
    (hsupp : IsProperOver f ⟨SheafOfModules.supp M, SheafOfModules.isClosed_supp M⟩) :
    RingedSpace.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforward f.toLRSHom.toShHom).obj
        (((derivedTensorProductFunctor X.sheaf).obj E).obj
          (DerivedCategory.Q.obj (ProperFlatBaseChange.singleDegreeComplex M)))) := by
  have hf : FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨J, _, _, _, D₀, rfl, -, -⟩ := exists_limitNoetherianSituation_of_isAffine S
  have : ∀ {i j : Jᵒᵖ} (e : i ⟶ j), IsAffineHom (D₀.system.map e) := D₀.transition_affine
  have (j : Jᵒᵖ) : IsNoetherian (D₀.system.obj j) := D₀.noetherian j.unop
  have : IsFiltered J := isFiltered_of_directed_le_nonempty J
  obtain ⟨i, Y, p, g, hp, hsq⟩ :=
    LimitDescent.exists_isPullback_of_finitePresentation D₀.system D₀.limitCone D₀.isLimit f hf
  let D : DescentSituation.{u, u} J :=
    { system := D₀.system
      transition_affine := D₀.transition_affine
      quasiCompact := fun _ => inferInstance
      quasiSeparated := fun _ => inferInstance
      limitCone := D₀.limitCone
      isLimit := D₀.isLimit
      base := i.unop }
  obtain ⟨j, -, Y', p', g', _, _, _, hsq', ⟨E', hE', ⟨eE⟩⟩, N, _, ⟨eM⟩⟩ :=
    exists_stage_perfect_finitePresentation D hp hsq E hE M
  obtain ⟨k, Y'', p'', t, g'', _, _, _, hsq'', ht, N'', _, hflat'', hsupp'', ⟨eM''⟩⟩ :=
    exists_stage_isFlatOver_isProperOver D₀.system D₀.limitCone D₀.isLimit (op j) hsq' N eM
      hflat hsupp
  have hE'' : RingedSpace.IsPerfect (X := Y''.toRingedSpace)
      ((derivedPullback t.toLRSHom.toShHom).obj E') :=
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ E' hE'
  have hp'' : FinitePresentation p'' := ⟨inferInstance, inferInstance, inferInstance⟩
  exact isPerfect_derivedPushforward_tensor_of_noetherianModel f p'' (D₀.limitCone.π.app k) g''
    hsq'' hp'' _ hE'' (ProperFlatBaseChange.singleDegreeComplex N'')
    (flatProperSupportFinitelyPresented_singleDegreeComplex' p'' N'' inferInstance hflat''
      ⟨_, hsupp'', subset_rfl⟩) E
    ((Stacks.DerivedPullback.schemeFactorIso g'' t g' ht).app E' ≪≫ eE)
    (ProperFlatBaseChange.singleDegreeComplex M)
    (pullbackComplexSingleDegreeIso g'' N'' ≪≫
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso eM'')

end Affine

end AlgebraicGeometry.Scheme

end
