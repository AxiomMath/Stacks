module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Limits.IndexHomUniverse
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.FinitePresentationSections
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.PullbackSectionNaturality
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.SectionsColimitFinitePresentation
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.FinitePresentationColimit
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 01Z0 for a quasi-coherent module on the base stage

Stacks 01Z0 reads: in the situation of Stacks 086P — a directed inverse system of quasi-compact
and quasi-separated schemes `Sᵢ` with affine transition morphisms, with limit `S = lim Sᵢ` and a
chosen base index `0` — for `ℱ₀` a **quasi-coherent** module on `S₀`, writing `ℱᵢ = f_{i0}⁺ℱ₀`
for `i ≥ 0` and `ℱ = f_0⁺ℱ₀`, one has `Γ(S, ℱ) = colim_{i ≥ 0} Γ(Sᵢ, ℱᵢ)`.

`StacksFrontier/AlgebraicGeometry/ModuleLimits/SectionsColimitFinitePresentation.lean` proves this
for `ℱ₀` of **finite presentation**, which is as far as [Stacks Project, Tag 01ZR] reaches: both
halves of that case are read off Tag 01ZR, a statement about finitely presented modules.  **This
file removes that restriction**, by an interchange of two filtered colimits.

## Main results

* `AlgebraicGeometry.isStagesColimit_stagePullbackSection_of_isQuasicoherent`:
  **[Stacks Project, Tag 01Z0]**, in the elementwise form `Stacks.IsStagesColimit` of
  `StacksFrontier/AlgebraicGeometry/Spaces/Limits/SectionsColimitDescent.lean`.

## Implementation notes

The interchange has three inputs, all of them already in the library.

* [Stacks Project, Tag 01PJ], `AlgebraicGeometry.exists_filtered_diagram_of_isFinitePresentation`,
  writes `ℱ₀` as the colimit of a filtered diagram `λ ↦ 𝒢_λ` of modules of finite presentation on
  the quasi-compact quasi-separated scheme `S₀`.
* `AlgebraicGeometry.Scheme.Modules.pullback` is a left adjoint
  (`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`), so it preserves that
  colimit: `p⁺ℱ₀ = colim_λ p⁺𝒢_λ` for every `p : T ⟶ S₀`.
* [Stacks Project, Tag 009F] for sheaves of modules, read on elements by
  `Stacks.AlgebraicGeometry.ModuleLimits.exists_section_of_isColimit` and
  `...ModuleLimits.exists_map_eq_of_isColimit`, computes that colimit on sections over a
  quasi-compact open of a quasi-separated scheme.  Composing the two gives the two private
  lemmas below, `exists_sectionsMap_eq` and `exists_hom_sectionsMap_eq`: over a quasi-compact
  quasi-separated `T` every global section of `p⁺ℱ₀` comes from some `p⁺𝒢_λ`, and two global
  sections with the same image in `p⁺ℱ₀` have equal images in `p⁺𝒢_μ` for some `μ` beyond both.
  The passage between a global section as a compatible family (`SheafOfModules.sections`, the
  form the colimit assertion is stated in) and as an element of `Γ(·, ⊤)` (the form Tag 009F is
  read in) is `Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal` at the terminal
  open `⊤`, under which the action of a morphism on sections is its action on sections over `⊤`
  — `AlgebraicGeometry.Scheme.Modules.sectionsMap_val`, a `rfl`.

Both `T = Sᵢ` and `T = S` are used, the latter needing the limit to be quasi-compact and
quasi-separated: the projection `S ⟶ Sᵢ` is affine
(`AlgebraicGeometry.isAffineHom_π_app'`), hence quasi-compact and quasi-separated, and the stage
is both.

What then carries a section between the coefficient modules is the naturality in the module of
the stage maps, which is `...ModuleLimits.sectionsMap_canHom_modulePullbackSection_naturality`
of `StacksFrontier/AlgebraicGeometry/ModuleLimits/PullbackSectionNaturality.lean` read at the two
factorisations the stage maps are built from.  With it the three clauses are mechanical: the
cocone clause needs no coefficient hypothesis at all and is the one of the finitely presented
case verbatim; surjectivity lifts a section of `ℱ` to a `𝒢_λ`, applies the finitely presented
case there, and pushes the resulting stage section forward to `ℱ₀`; and injectivity lifts the two
sections to one `𝒢_λ`, uses that their images in `Γ(S, ℱ)` agree to make their images in
`Γ(S, p⁺𝒢_μ)` agree at some `μ`, applies the finitely presented case at `𝒢_μ`, and pushes the
resulting later stage forward to `ℱ₀`.

The index set lies in the universe of the schemes.  That is not a restriction that may be
dropped: `Stacks.LimitSectionsIdentification.not_card_01Z0` refutes the statement over an index
set one universe up, so a `u`-small directed index set is what the source's "directed set" means
and the tag asserts nothing more.

## References

* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
* [Stacks Project, Tag 01PJ](https://stacks.math.columbia.edu/tag/01PJ)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 009F](https://stacks.math.columbia.edu/tag/009F)
* [Stacks Project, Tag 086P](https://stacks.math.columbia.edu/tag/086P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules.FiniteTypeKernel (sectionsEquivOfTerminal)

universe u

namespace AlgebraicGeometry

/-! ### A filtered colimit of modules computed on global sections -/

section Sections

variable {T Z : Scheme.{u}} [CompactSpace ↥T] [QuasiSeparatedSpace ↥T] (p : T ⟶ Z)
  {Λ : Type u} [SmallCategory Λ] [IsFiltered Λ] {D : Λ ⥤ Z.Modules} {F : Z.Modules}
  {φ : D ⟶ (Functor.const Λ).obj F}

/-- A global section of the pullback of a filtered colimit of modules comes from a stage of the
colimit, over a quasi-compact quasi-separated scheme. -/
private theorem exists_sectionsMap_eq (hcol : IsColimit (Cocone.mk F φ))
    (s : ((Scheme.Modules.pullback p).obj F).sections) :
    ∃ (l : Λ) (y : ((Scheme.Modules.pullback p).obj (D.obj l)).sections),
      SheafOfModules.sectionsMap ((Scheme.Modules.pullback p).map (φ.app l)) y = s := by
  have hpb : IsColimit ((Scheme.Modules.pullback p).mapCocone (Cocone.mk F φ)) :=
    isColimitOfPreserves (Scheme.Modules.pullback p) hcol
  obtain ⟨l, t, ht⟩ := Stacks.AlgebraicGeometry.ModuleLimits.exists_section_of_isColimit
    hpb ⊤ (by simpa using isCompact_univ (X := ↥T)) (s.val (op ⊤))
  refine ⟨l, (sectionsEquivOfTerminal _ (isTerminalTop (α := T.Opens))).symm t, ?_⟩
  refine (sectionsEquivOfTerminal ((Scheme.Modules.pullback p).obj F)
    (isTerminalTop (α := T.Opens))).injective ?_
  show (SheafOfModules.sectionsMap ((Scheme.Modules.pullback p).map (φ.app l)) _).val (op ⊤)
    = s.val (op ⊤)
  rw [Scheme.Modules.sectionsMap_val,
    show ((sectionsEquivOfTerminal ((Scheme.Modules.pullback p).obj (D.obj l))
        (isTerminalTop (α := T.Opens))).symm t).val (op ⊤) = t from
      (sectionsEquivOfTerminal _ (isTerminalTop (α := T.Opens))).apply_symm_apply t]
  exact ht

/-- Two global sections of pullbacks of stages of a filtered colimit of modules with the same
image in the pullback of the colimit have equal images at some later stage, over a quasi-compact
quasi-separated scheme. -/
private theorem exists_hom_sectionsMap_eq (hcol : IsColimit (Cocone.mk F φ)) {l₁ l₂ : Λ}
    (y₁ : ((Scheme.Modules.pullback p).obj (D.obj l₁)).sections)
    (y₂ : ((Scheme.Modules.pullback p).obj (D.obj l₂)).sections)
    (h : SheafOfModules.sectionsMap ((Scheme.Modules.pullback p).map (φ.app l₁)) y₁
      = SheafOfModules.sectionsMap ((Scheme.Modules.pullback p).map (φ.app l₂)) y₂) :
    ∃ (m : Λ) (g₁ : l₁ ⟶ m) (g₂ : l₂ ⟶ m),
      SheafOfModules.sectionsMap ((Scheme.Modules.pullback p).map (D.map g₁)) y₁
        = SheafOfModules.sectionsMap ((Scheme.Modules.pullback p).map (D.map g₂)) y₂ := by
  have hpb : IsColimit ((Scheme.Modules.pullback p).mapCocone (Cocone.mk F φ)) :=
    isColimitOfPreserves (Scheme.Modules.pullback p) hcol
  obtain ⟨m, g₁, g₂, hg⟩ := Stacks.AlgebraicGeometry.ModuleLimits.exists_map_eq_of_isColimit
    hpb ⊤ (by simpa using isCompact_univ (X := ↥T)) (y₁.val (op ⊤)) (y₂.val (op ⊤))
    (congrArg (fun z : ((Scheme.Modules.pullback p).obj F).sections => z.val (op ⊤)) h)
  refine ⟨m, g₁, g₂, (sectionsEquivOfTerminal ((Scheme.Modules.pullback p).obj (D.obj m))
    (isTerminalTop (α := T.Opens))).injective ?_⟩
  show (SheafOfModules.sectionsMap ((Scheme.Modules.pullback p).map (D.map g₁)) y₁).val (op ⊤)
    = (SheafOfModules.sectionsMap ((Scheme.Modules.pullback p).map (D.map g₂)) y₂).val (op ⊤)
  rw [Scheme.Modules.sectionsMap_val, Scheme.Modules.sectionsMap_val]
  exact hg

end Sections

/-! ### Stacks 01Z0 for a quasi-coherent module on the base stage -/

open Stacks.AlgebraicGeometry.ModuleLimits

variable {α : Type u} [Preorder α] [IsDirected α (· ≤ ·)] [Nonempty α] (E : αᵒᵖ ⥤ Scheme.{u})

/-- **The transition map of Stacks 01Z0 is natural in the coefficient module.**  This is
`...ModuleLimits.sectionsMap_canHom_modulePullbackSection_naturality` at the factorisation
`Sⱼ ⟶ Sᵢ ⟶ S₀` that `AlgebraicGeometry.stagePullbackSectionTransition` is built from. -/
theorem sectionsMap_stagePullbackSectionTransition {a₀ a b : α} (ha : a₀ ≤ a) (hb : a₀ ≤ b)
    (hab : a ≤ b) {F F' : (E.obj (op a₀)).Modules} (ψ : F ⟶ F')
    (x : ((Scheme.Modules.pullback (E.map (homOfLE ha).op)).obj F).sections) :
    SheafOfModules.sectionsMap ((Scheme.Modules.pullback (E.map (homOfLE hb).op)).map ψ)
          (stagePullbackSectionTransition E ha hb hab F x)
      = stagePullbackSectionTransition E ha hb hab F'
          (SheafOfModules.sectionsMap
            ((Scheme.Modules.pullback (E.map (homOfLE ha).op)).map ψ) x) :=
  sectionsMap_canHom_modulePullbackSection_naturality (E.map (homOfLE hab).op)
    (E.map (homOfLE ha).op) (E.map (homOfLE hb).op) (map_homOfLE_op_comp E ha hb hab) ψ x

omit [IsDirected α (· ≤ ·)] [Nonempty α] in
/-- **The map to the limit of Stacks 01Z0 is natural in the coefficient module.**  This is
`...ModuleLimits.sectionsMap_canHom_modulePullbackSection_naturality` at the factorisation
`S ⟶ Sᵢ ⟶ S₀` that `AlgebraicGeometry.stagePullbackSectionProjection` is built from. -/
theorem sectionsMap_stagePullbackSectionProjection {a₀ a : α} (ha : a₀ ≤ a)
    {F F' : (E.obj (op a₀)).Modules} (ψ : F ⟶ F') (c : Cone E)
    (x : ((Scheme.Modules.pullback (E.map (homOfLE ha).op)).obj F).sections) :
    SheafOfModules.sectionsMap ((Scheme.Modules.pullback (c.π.app (op a₀))).map ψ)
          (stagePullbackSectionProjection E ha F c x)
      = stagePullbackSectionProjection E ha F' c
          (SheafOfModules.sectionsMap
            ((Scheme.Modules.pullback (E.map (homOfLE ha).op)).map ψ) x) :=
  sectionsMap_canHom_modulePullbackSection_naturality (c.π.app (op a))
    (E.map (homOfLE ha).op) (c.π.app (op a₀)) (c.w (homOfLE ha).op) ψ x

/-- **[Stacks Project, Tag 01Z0].** Let `E` be a directed inverse system of quasi-compact and
quasi-separated schemes with affine transition morphisms, let `c` be a limit cone on it, let `0`
be a chosen index and let `ℱ₀` be a **quasi-coherent** module on `S₀ = E.obj (op 0)`.  Setting
`ℱᵢ = f_{i0}⁺ℱ₀` for `i ≥ 0` and `ℱ = f_0⁺ℱ₀`, the group `Γ(S, ℱ)` is the filtered colimit of the
`Γ(Sᵢ, ℱᵢ)`, in the elementwise form `Stacks.IsStagesColimit`: the maps to `Γ(S, ℱ)` are
compatible with the transition maps, every global section at the limit comes from a stage, and
two global sections at one stage with the same image at the limit already agree at a later stage.

The finite-presentation case is
`AlgebraicGeometry.isStagesColimit_stagePullbackSection_of_isFinitePresentation`, and this is it
interchanged with the presentation of a quasi-coherent module as a filtered colimit of finitely
presented ones, [Stacks Project, Tag 01PJ]; see the file's implementation notes.

The index set lies in the universe of the schemes, which is not a restriction that may be
dropped — `Stacks.LimitSectionsIdentification.not_card_01Z0` refutes the statement over an index
set one universe up, so a `u`-small directed index set is exactly the source's "directed set". -/
@[stacks 01Z0, ega "IV 8.5.4"]
theorem isStagesColimit_stagePullbackSection_of_isQuasicoherent
    [∀ {i j : αᵒᵖ} (f : i ⟶ j), IsAffineHom (E.map f)]
    [∀ i : αᵒᵖ, CompactSpace (E.obj i)] [∀ i : αᵒᵖ, QuasiSeparatedSpace (E.obj i)]
    (c : Cone E) (hc : IsLimit c) (a₀ : α) (F₀ : (E.obj (op a₀)).Modules)
    (hF₀ : F₀.IsQuasicoherent) :
    Stacks.IsStagesColimit
      (fun (a b : {a : α // a₀ ≤ a}) (h : a ≤ b) =>
        stagePullbackSectionTransition E a.2 b.2 (Subtype.coe_le_coe.mpr h) F₀)
      (fun a : {a : α // a₀ ≤ a} => stagePullbackSectionProjection E a.2 F₀ c) := by
  have : F₀.IsQuasicoherent := hF₀
  have hcpt : CompactSpace ↥c.pt := Scheme.compactSpace_of_isLimit' E c hc
  have hqs : QuasiSeparatedSpace ↥c.pt := by
    obtain ⟨i⟩ : Nonempty αᵒᵖ := inferInstance
    have : IsAffineHom (c.π.app i) := isAffineHom_π_app' E c hc i
    exact quasiSeparatedSpace_of_quasiSeparated (c.π.app i)
  obtain ⟨Λ, _, _, D, φ, hfp, ⟨hcol⟩⟩ :=
    exists_filtered_diagram_of_isFinitePresentation (E.obj (op a₀)) F₀
  refine
    { ι_trans := fun a b h x =>
        sectionsMap_canHom_modulePullbackSection_comp (c.π.app (op b.1))
          (E.map (homOfLE (Subtype.coe_le_coe.mpr h)).op) (E.map (homOfLE a.2).op)
          (c.π.app (op a.1)) (c.w (homOfLE (Subtype.coe_le_coe.mpr h)).op)
          (E.map (homOfLE b.2).op) (map_homOfLE_op_comp E a.2 b.2 (Subtype.coe_le_coe.mpr h))
          (c.π.app (op a₀)) (c.w (homOfLE a.2).op) (c.w (homOfLE b.2).op) F₀ x
      exists_stage := ?_
      exists_trans_eq := ?_ }
  · intro t
    obtain ⟨l, y, hy⟩ := exists_sectionsMap_eq (T := c.pt) (c.π.app (op a₀)) hcol t
    obtain ⟨a, x, hx⟩ := (isStagesColimit_stagePullbackSection_of_isFinitePresentation E c hc a₀
      (D.obj l) (hfp l)).exists_stage y
    refine ⟨a, SheafOfModules.sectionsMap
      ((Scheme.Modules.pullback (E.map (homOfLE a.2).op)).map (φ.app l)) x, ?_⟩
    have hstep := congrArg (SheafOfModules.sectionsMap
      ((Scheme.Modules.pullback (c.π.app (op a₀))).map (φ.app l : D.obj l ⟶ F₀))) hx
    exact (sectionsMap_stagePullbackSectionProjection E a.2 (F := D.obj l) (F' := F₀)
      (φ.app l) c x).symm.trans (hstep.trans hy)
  · intro a x y hxy
    obtain ⟨l₁, x₁, hx₁⟩ := exists_sectionsMap_eq (E.map (homOfLE a.2).op) hcol x
    obtain ⟨l₂, y₁, hy₁⟩ := exists_sectionsMap_eq (E.map (homOfLE a.2).op) hcol y
    have key := ((sectionsMap_stagePullbackSectionProjection E a.2 (F := D.obj l₁) (F' := F₀)
          (φ.app l₁) c x₁).trans
        (congrArg (stagePullbackSectionProjection E a.2 F₀ c) hx₁)).trans
      (hxy.trans (((sectionsMap_stagePullbackSectionProjection E a.2 (F := D.obj l₂) (F' := F₀)
          (φ.app l₂) c y₁).trans
        (congrArg (stagePullbackSectionProjection E a.2 F₀ c) hy₁)).symm))
    obtain ⟨m, g₁, g₂, hg⟩ :=
      exists_hom_sectionsMap_eq (T := c.pt) (c.π.app (op a₀)) hcol _ _ key
    have hmid := ((sectionsMap_stagePullbackSectionProjection E a.2 (F := D.obj l₁)
          (F' := D.obj m) (D.map g₁) c x₁).symm.trans hg).trans
      (sectionsMap_stagePullbackSectionProjection E a.2 (F := D.obj l₂) (F' := D.obj m)
        (D.map g₂) c y₁)
    obtain ⟨b, hab, hb⟩ := (isStagesColimit_stagePullbackSection_of_isFinitePresentation E c hc a₀
      (D.obj m) (hfp m)).exists_trans_eq a _ _ hmid
    refine ⟨b, hab, ?_⟩
    have hcomp : ∀ {l' : Λ} (g : l' ⟶ m)
        (z : ((Scheme.Modules.pullback (E.map (homOfLE a.2).op)).obj (D.obj l')).sections),
        SheafOfModules.sectionsMap
            ((Scheme.Modules.pullback (E.map (homOfLE a.2).op)).map
              (φ.app m : D.obj m ⟶ F₀))
            (SheafOfModules.sectionsMap
              ((Scheme.Modules.pullback (E.map (homOfLE a.2).op)).map (D.map g)) z)
          = SheafOfModules.sectionsMap
            ((Scheme.Modules.pullback (E.map (homOfLE a.2).op)).map
              (φ.app l' : D.obj l' ⟶ F₀)) z := by
      intro l' g z
      refine (SheafOfModules.sectionsMap_comp _ _ z).symm.trans
        (congrArg (fun w => SheafOfModules.sectionsMap w z) ?_)
      exact ((Scheme.Modules.pullback (E.map (homOfLE a.2).op)).map_comp
        (D.map g) (φ.app m)).symm.trans
        (congrArg (Scheme.Modules.pullback (E.map (homOfLE a.2).op)).map
          ((Cocone.mk F₀ φ).w g))
    have hgoal := congrArg (SheafOfModules.sectionsMap
      ((Scheme.Modules.pullback (E.map (homOfLE b.2).op)).map
        (φ.app m : D.obj m ⟶ F₀))) hb
    refine Eq.trans (congrArg (stagePullbackSectionTransition E a.2 b.2
      (Subtype.coe_le_coe.mpr hab) F₀) ((hcomp g₁ x₁).trans hx₁).symm) ?_
    refine Eq.trans ?_ (congrArg (stagePullbackSectionTransition E a.2 b.2
      (Subtype.coe_le_coe.mpr hab) F₀) ((hcomp g₂ y₁).trans hy₁))
    exact ((sectionsMap_stagePullbackSectionTransition E a.2 b.2
          (Subtype.coe_le_coe.mpr hab) (F := D.obj m) (F' := F₀) (φ.app m) _).symm.trans
        hgoal).trans
      (sectionsMap_stagePullbackSectionTransition E a.2 b.2
        (Subtype.coe_le_coe.mpr hab) (F := D.obj m) (F' := F₀) (φ.app m) _)

end AlgebraicGeometry

end
