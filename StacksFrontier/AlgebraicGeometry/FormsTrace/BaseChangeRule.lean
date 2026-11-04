module

public import StacksFrontier.AlgebraicGeometry.FormsTrace.Construction
public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.Uniqueness

/-!
# The trace maps on forms are compatible with base change

Condition (2) of Stacks, Lemma 0FLB for the rule of trace maps on forms: for a cartesian square
`Y' = X' ×_X Y` with `f : Y ⟶ X` and `f' : Y' ⟶ X'` finite syntomic, the map `Θ_{Y'/X'}` on the
pull-back of a local form of `Y` is the pull-back of `Θ_{Y/X}` on that form.

The statement is local on `X'`, and the framed opens form a basis
(`Stacks.FormsTrace.isBasis_framedOpens`): every point of `X'` over an open `U ⊆ X` has a framed
neighbourhood `W'` with `W' ⊆ a⁻¹W` for a framed `W ⊆ U`. Over such a pair the two sides become,
through the identifications of sections with forms, `Θ_{B'/A'}(g^*x)` and `f^*Θ_{B/A}(x)` for
the pushout square `A = Γ(X, W)`, `B = Γ(Y, f⁻¹W)`, `A' = Γ(X', W')`, `B' = Γ(Y', f'⁻¹W')`, and
these agree by `Stacks.FormsTrace.frameTrace_formsMap_of_isPushout`.

The argument only uses that the rule is given on framed opens by the local trace maps, so it is
stated for any rule with that property (`AlgebraicGeometry.FormsTraceRule.IsLocalTrace`).

## Main definitions

* `AlgebraicGeometry.FormsTraceRule.IsLocalTrace`: on every framed open the sections of the rule
  are the local trace maps `Stacks.FormsTrace.localTrace`.

## Main results

* `AlgebraicGeometry.FormsTraceRule.IsLocalTrace.isBaseChange`: such a rule is compatible with
  base change.
* `AlgebraicGeometry.formsTraceRule_isBaseChange`: the rule `f ↦ Θ_{Y/X}` is compatible with base
  change.

## References

* [Stacks Project, Tag 0FLB](https://stacks.math.columbia.edu/tag/0FLB)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace FormsTraceRule

variable (Θ : FormsTraceRule.{u})

/-- **The rule is given by the local trace maps on framed opens**: over every framed open `U` of
the target, the sections of `Θ_{Y/X}` are, through the identifications of sections with forms,
the local trace maps `Θ_{Γ(Y, f⁻¹U)/Γ(X, U)}` of `Stacks.FormsTrace.localTrace`. -/
def IsLocalTrace : Prop :=
  ∀ ⦃X Y : Scheme.{u}⦄ (f : Y ⟶ X) [IsFinite f] (hf : Syntomic f) (p : ℕ) (U : X.Opens)
    (hU : Stacks.FormsTrace.IsFramedOpen f U)
    (η : Γ(Scheme.absoluteDifferentialForms Y p, f ⁻¹ᵁ U)),
    Scheme.absoluteFormsSectionsEquiv X hU.1 p ((Θ f hf p).app U η) =
      Stacks.FormsTrace.localTrace f U p
        (Scheme.absoluteFormsSectionsEquiv Y (hU.1.preimage f) p η)

/-- Restricting twice is restricting once. -/
theorem modules_presheaf_map_map {Z : Scheme.{u}} (M : Z.Modules) {V₁ V₂ V₃ : Z.Opens}
    (h₁ : V₂ ≤ V₁) (h₂ : V₃ ≤ V₂) (s : Γ(M, V₁)) :
    M.presheaf.map (homOfLE h₂).op (M.presheaf.map (homOfLE h₁).op s) =
      M.presheaf.map (homOfLE (h₂.trans h₁)).op s :=
  (PresheafOfModules.map_comp_apply M.val (homOfLE h₁).op (homOfLE h₂).op s).symm

variable {Θ}

section Square

variable ⦃X Y X' Y' : Scheme.{u}⦄ {f : Y ⟶ X} {f' : Y' ⟶ X'} {a : X' ⟶ X} {b : Y' ⟶ Y}
  (sq : IsPullback b f' f a) (p : ℕ)

/-- **The trace maps commute with the pushout square of rings over framed opens** `W ⊆ X`,
`W' ⊆ a⁻¹W ⊆ X'`: `Θ_{B'/A'}(g^*x) = f^*Θ_{B/A}(x)` for `A = Γ(X, W)`, `B = Γ(Y, f⁻¹W)`,
`A' = Γ(X', W')`, `B' = Γ(Y', f'⁻¹W')`. -/
theorem localTrace_formsMap_of_isPullback [IsAffineHom f] {W : X.Opens} {W' : X'.Opens}
    (hW : Stacks.FormsTrace.IsFramedOpen f W) (hW' : Stacks.FormsTrace.IsFramedOpen f' W')
    (hW'W : W' ≤ a ⁻¹ᵁ W)
    (x : ⋀[Γ(Y, f ⁻¹ᵁ W)]^p Ω[Γ(Y, f ⁻¹ᵁ W)⁄ℤ]) :
    letI := (a.appLE W W' hW'W).hom.toAlgebra
    letI := (b.appLE (f ⁻¹ᵁ W) (f' ⁻¹ᵁ W')
      (AlgebraicGeometry.preimage_le_preimage_of_comm sq.w.symm hW'W)).hom.toAlgebra
    Stacks.FormsTrace.localTrace f' W' p (Stacks.FormsTrace.formsMap Γ(Y, f ⁻¹ᵁ W)
        Γ(Y', f' ⁻¹ᵁ W') p x) =
      Stacks.FormsTrace.formsMap Γ(X, W) Γ(X', W') p (Stacks.FormsTrace.localTrace f W p x) := by
  have eW := AlgebraicGeometry.preimage_le_preimage_of_comm sq.w.symm hW'W
  let : Algebra Γ(X, W) Γ(Y, f ⁻¹ᵁ W) := (f.app W).hom.toAlgebra
  let : Algebra Γ(X', W') Γ(Y', f' ⁻¹ᵁ W') := (f'.app W').hom.toAlgebra
  let : Algebra Γ(X, W) Γ(X', W') := (a.appLE W W' hW'W).hom.toAlgebra
  let : Algebra Γ(Y, f ⁻¹ᵁ W) Γ(Y', f' ⁻¹ᵁ W') :=
    (b.appLE (f ⁻¹ᵁ W) (f' ⁻¹ᵁ W') eW).hom.toAlgebra
  let : Algebra Γ(X, W) Γ(Y', f' ⁻¹ᵁ W') := (a.appLE W W' hW'W ≫ f'.app W').hom.toAlgebra
  have hpo := Stacks.Morphisms.isPushout_appLE_of_isPullback sq ⟨W, hW.1⟩ ⟨W', hW'.1⟩ hW'W eW
  have : IsScalarTower Γ(X, W) Γ(X', W') Γ(Y', f' ⁻¹ᵁ W') :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Γ(X, W) Γ(Y, f ⁻¹ᵁ W) Γ(Y', f' ⁻¹ᵁ W') :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show (a.appLE W W' hW'W ≫ f'.app W').hom x =
        (f.app W ≫ b.appLE (f ⁻¹ᵁ W) (f' ⁻¹ᵁ W') eW).hom x
      rw [hpo.w]
  have : Algebra.IsPushout Γ(X, W) Γ(Y, f ⁻¹ᵁ W) Γ(X', W') Γ(Y', f' ⁻¹ᵁ W') :=
    (CommRingCat.isPushout_iff_isPushout.mp hpo.flip).symm
  exact Stacks.FormsTrace.frameTrace_formsMap_of_isPushout Γ(X', W') Γ(Y', f' ⁻¹ᵁ W')
    (Stacks.FormsTrace.framed_or_subsingleton_of_isFramedOpen f hW)
    (Stacks.FormsTrace.framed_or_subsingleton_of_isFramedOpen f' hW') p x

/-- The left-hand side of the base change condition, restricted to `W' ⊆ U'`. -/
theorem baseChange_lhs_restrict (Θf' : (Scheme.Modules.pushforward f').obj
      (Scheme.absoluteDifferentialForms Y' p) ⟶ Scheme.absoluteDifferentialForms X' p)
    {U W : X.Opens} {U' W' : X'.Opens} (hU : U' ≤ a ⁻¹ᵁ U) (hWU : W ≤ U) (hW'U' : W' ≤ U')
    (hW'W : W' ≤ a ⁻¹ᵁ W) (η : Γ(Scheme.absoluteDifferentialForms Y p, f ⁻¹ᵁ U)) :
    (Scheme.absoluteDifferentialForms X' p).presheaf.map (homOfLE hW'U').op
      (Θf'.app U' ((Scheme.absoluteDifferentialForms Y' p).presheaf.map
        (homOfLE (AlgebraicGeometry.preimage_le_preimage_of_comm sq.w.symm hU)).op
        (b.absoluteFormsPullback p (f ⁻¹ᵁ U) η))) =
      Θf'.app W' ((Scheme.absoluteDifferentialForms Y' p).presheaf.map
        (homOfLE (AlgebraicGeometry.preimage_le_preimage_of_comm sq.w.symm hW'W)).op
        (b.absoluteFormsPullback p (f ⁻¹ᵁ W)
          ((Scheme.absoluteDifferentialForms Y p).presheaf.map
            (homOfLE (f.preimage_mono hWU)).op η))) := by
  refine (Scheme.Hom.pushforward_hom_app_restrict _ Θf' hW'U' _).symm.trans ?_
  refine congrArg (Θf'.app W') ((modules_presheaf_map_map _ _ _ _).trans ?_)
  exact Scheme.Hom.map_absoluteFormsPullback_eq b (p : ℤ) _
    (AlgebraicGeometry.preimage_le_preimage_of_comm sq.w.symm hW'W) (f.preimage_mono hWU) η

/-- The right-hand side of the base change condition, restricted to `W' ⊆ U'`. -/
theorem baseChange_rhs_restrict (Θf : (Scheme.Modules.pushforward f).obj
      (Scheme.absoluteDifferentialForms Y p) ⟶ Scheme.absoluteDifferentialForms X p)
    {U W : X.Opens} {U' W' : X'.Opens} (hU : U' ≤ a ⁻¹ᵁ U) (hWU : W ≤ U) (hW'U' : W' ≤ U')
    (hW'W : W' ≤ a ⁻¹ᵁ W) (η : Γ(Scheme.absoluteDifferentialForms Y p, f ⁻¹ᵁ U)) :
    (Scheme.absoluteDifferentialForms X' p).presheaf.map (homOfLE hW'U').op
      ((Scheme.absoluteDifferentialForms X' p).presheaf.map (homOfLE hU).op
        (a.absoluteFormsPullback p U (Θf.app U η))) =
      (Scheme.absoluteDifferentialForms X' p).presheaf.map (homOfLE hW'W).op
        (a.absoluteFormsPullback p W (Θf.app W ((Scheme.absoluteDifferentialForms Y p).presheaf.map
            (homOfLE (f.preimage_mono hWU)).op η))) := by
  refine (modules_presheaf_map_map _ _ _ _).trans ?_
  refine (Scheme.Hom.map_absoluteFormsPullback_eq a (p : ℤ) _ hW'W hWU _).trans ?_
  exact congrArg (fun z => (Scheme.absoluteDifferentialForms X' p).presheaf.map (homOfLE hW'W).op
    (a.absoluteFormsPullback p W z)) (Scheme.Hom.pushforward_hom_app_restrict _ Θf hWU η).symm

end Square

/-- **Base change over a pair of framed opens.** For a cartesian square, framed opens `W ⊆ U` of
`X` and `W' ⊆ U' ⊓ a⁻¹W` of `X'`, the two sides of the base change condition agree on `W'`. -/
theorem IsLocalTrace.restrict_eq (hΘ : Θ.IsLocalTrace) ⦃X Y X' Y' : Scheme.{u}⦄ (f : Y ⟶ X)
    (f' : Y' ⟶ X') (a : X' ⟶ X) (b : Y' ⟶ Y) (sq : IsPullback b f' f a) [IsFinite f]
    [IsFinite f'] (hf : Syntomic f) (hf' : Syntomic f') (p : ℕ) (U : X.Opens) (U' : X'.Opens)
    (hU : U' ≤ a ⁻¹ᵁ U) (η : Γ(Scheme.absoluteDifferentialForms Y p, f ⁻¹ᵁ U)) {W : X.Opens}
    {W' : X'.Opens} (hW : Stacks.FormsTrace.IsFramedOpen f W)
    (hW' : Stacks.FormsTrace.IsFramedOpen f' W') (hWU : W ≤ U) (hW'U' : W' ≤ U')
    (hW'W : W' ≤ a ⁻¹ᵁ W) :
    (Scheme.absoluteDifferentialForms X' p).presheaf.map (homOfLE hW'U').op
      ((Θ f' hf' p).app U' ((Scheme.absoluteDifferentialForms Y' p).presheaf.map
        (homOfLE (AlgebraicGeometry.preimage_le_preimage_of_comm sq.w.symm hU)).op
        (b.absoluteFormsPullback p (f ⁻¹ᵁ U) η))) =
    (Scheme.absoluteDifferentialForms X' p).presheaf.map (homOfLE hW'U').op
      ((Scheme.absoluteDifferentialForms X' p).presheaf.map (homOfLE hU).op
        (a.absoluteFormsPullback p U ((Θ f hf p).app U η))) := by
  refine (baseChange_lhs_restrict sq p (Θ f' hf' p) hU hWU hW'U' hW'W η).trans
    (Eq.trans ?_ (baseChange_rhs_restrict p (Θ f hf p) hU hWU hW'U' hW'W η).symm)
  have eW := AlgebraicGeometry.preimage_le_preimage_of_comm sq.w.symm hW'W
  obtain ⟨ηW, hηW⟩ : ∃ x, x = (Scheme.absoluteDifferentialForms Y p).presheaf.map
      (homOfLE (f.preimage_mono hWU)).op η := ⟨_, rfl⟩
  rw [← hηW]
  have h1 := hΘ f' hf' p W' hW' ((Scheme.absoluteDifferentialForms Y' p).presheaf.map
    (homOfLE eW).op (b.absoluteFormsPullback p (f ⁻¹ᵁ W) ηW))
  have h2 := Scheme.absoluteFormsSectionsEquiv_absoluteFormsPullback b (hW.1.preimage f)
    (hW'.1.preimage f') eW p ηW
  have h3 := localTrace_formsMap_of_isPullback sq p hW hW' hW'W
    (Scheme.absoluteFormsSectionsEquiv Y (hW.1.preimage f) p ηW)
  have h4 := Scheme.absoluteFormsSectionsEquiv_absoluteFormsPullback a hW.1 hW'.1 hW'W p
    ((Θ f hf p).app W ηW)
  have h5 := hΘ f hf p W hW ηW
  refine (Scheme.absoluteFormsSectionsEquiv X' hW'.1 p).injective ?_
  rw [h1, h2, h3, h4, h5]

/-- **A rule given by the local trace maps is compatible with base change** (condition (2) of
Stacks, Lemma 0FLB). -/
theorem IsLocalTrace.isBaseChange (hΘ : Θ.IsLocalTrace) : Θ.IsBaseChange := by
  intro X Y X' Y' f f' a b sq _ _ hf hf' p U U' hU η
  have := AlgebraicGeometry.flat hf
  have := AlgebraicGeometry.locallyOfFinitePresentation hf
  have := AlgebraicGeometry.flat hf'
  have := AlgebraicGeometry.locallyOfFinitePresentation hf'
  let ι := {W' : X'.Opens // W' ≤ U' ∧ Stacks.FormsTrace.IsFramedOpen f' W' ∧
    ∃ W : X.Opens, Stacks.FormsTrace.IsFramedOpen f W ∧ W ≤ U ∧ W' ≤ a ⁻¹ᵁ W}
  refine Stacks.BasisRestriction.moduleSheafSection_ext_of_cover
    (Scheme.absoluteDifferentialForms X' p) (fun i : ι => i.1) (fun i => i.2.1) ?_ _ _ ?_
  · intro x hx
    obtain ⟨W, hW, hxW, hWU⟩ := (Opens.isBasis_iff_nbhd.mp
      (Stacks.FormsTrace.isBasis_framedOpens f hf)) (hU hx)
    obtain ⟨W', hW', hxW', hW'le⟩ := (Opens.isBasis_iff_nbhd.mp
      (Stacks.FormsTrace.isBasis_framedOpens f' hf'))
      (show x ∈ U' ⊓ a ⁻¹ᵁ W from ⟨hx, hxW⟩)
    exact ⟨⟨W', hW'le.trans inf_le_left, hW', W, hW, hWU, hW'le.trans inf_le_right⟩, hxW'⟩
  · rintro ⟨W', hW'U', hW', W, hW, hWU, hW'W⟩
    exact hΘ.restrict_eq f f' a b sq hf hf' p U U' hU η hW hW' hWU hW'U' hW'W

end FormsTraceRule

/-- The rule of trace maps on forms is given by the local trace maps on framed opens. -/
theorem formsTraceRule_isLocalTrace : formsTraceRule.{u}.IsLocalTrace := by
  intro X Y f _ hf p U hU η
  have h := f.absoluteFormsSectionsEquiv_formsTrace_app hf p ⟨U, hU⟩ η
  have hrule : formsTraceRule f hf p = f.formsTrace hf p := rfl
  rw [hrule]
  convert h using 2

/-- **The trace maps on forms are compatible with base change** (condition (2) of Stacks,
Lemma 0FLB, for the rule `f ↦ Θ_{Y/X}`). -/
theorem formsTraceRule_isBaseChange : formsTraceRule.{u}.IsBaseChange :=
  formsTraceRule_isLocalTrace.isBaseChange

end AlgebraicGeometry

end
