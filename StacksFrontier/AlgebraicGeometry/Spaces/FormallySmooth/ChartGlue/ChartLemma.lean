module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.AlgChart
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover

/-!
# Relative formal étaleness and smoothness of a chart over a thickening

Let `a : yoneda U ⟶ X` be a formally étale transformation and `f : X ⟶ Y` a transformation such
that `a ≫ f` is formally smooth. Let `T'` be an object with a section `y` of `Y`, and let `E` be an
object with morphisms `e_T : E ⟶ T'` and `e_U : E ⟶ U` such that `(a ≫ f)(e_U) = y|_E`. Suppose
that `E ⟶ U ×_Y T'` is formally étale in the sense that infinitesimal lifting problems against
the pair `(e_U, e_T)` have unique solutions. Then:

* the section `a(e_U)` of `X` over `E` is formally étale relative to `T'`
  (`AlgebraicGeometry.Space.ChartGlue.relFormallyEtale_of_pair`), and
* `E` is formally smooth relative to `T'`
  (`AlgebraicGeometry.Space.ChartGlue.exists_lift_of_pair`).
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space.ChartGlue

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T' : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (y : Y.obj (op T'))
  {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X)
  {E : BigFppfOver B S hS} (eT : E ⟶ T') (eU : E ⟶ U)

/-- **Formal étaleness of `E ⟶ U ×_Y T'`**, in the form of unique solutions of infinitesimal
lifting problems against the pair `(e_U, e_T)`. -/
def PairFormallyEtale : Prop :=
  ∀ (C₀ D₀ : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj C₀) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj D₀) → ∀ (j : D₀ ⟶ C₀),
      IsSquareZeroClosedImmersion B S hS j → ∀ (u : C₀ ⟶ U) (c : C₀ ⟶ T'),
        f.app _ (a.app (op C₀) u) = Y.map c.op y →
        ∀ (e₀ : D₀ ⟶ E), e₀ ≫ eU = j ≫ u → e₀ ≫ eT = j ≫ c →
          ∃! e : C₀ ⟶ E, j ≫ e = e₀ ∧ e ≫ eU = u ∧ e ≫ eT = c

variable {B S hS T' f y a eT eU}

/-- The section `a(u)` of `X` over `C₀`. -/
abbrev aPt {C₀ : BigFppfOver B S hS} (u : C₀ ⟶ U) : X.obj (op C₀) := a.app (op C₀) u

/-- Restricting the section `a(u)` along `j` gives `a(j ≫ u)`. -/
lemma aPt_comp {C₀ D₀ : BigFppfOver B S hS} (j : D₀ ⟶ C₀) (u : C₀ ⟶ U) :
    X.map j.op (aPt (a := a) u) = aPt (a := a) (j ≫ u) := by
  show X.map j.op (a.app _ u) = a.app _ ((yoneda.obj U).map j.op u)
  rw [a.naturality_apply]

variable (hfa : FormallyEtale a) (hfs : FormallySmooth (a ≫ f))
  (hyE : f.app _ (aPt (a := a) eU) = Y.map eT.op y)
  (hpair : PairFormallyEtale B S hS T' f y a eT eU)

include hfa hpair hyE in
omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- **The section `a(e_U)` is formally étale relative to `T'`.** -/
theorem relFormallyEtale_of_pair : RelFormallyEtale B S hS T' f y eT (aPt (a := a) eU) := by
  intro C₀ D₀ hC hD j hj c g hg e₀ he₀ hge
  obtain ⟨u, ⟨hu₁, hu₂⟩, huu⟩ := hfa D₀ C₀ hD hC j hj (e₀ ≫ eU) g (by
    rw [← hge, aPt_comp])
  obtain ⟨e, ⟨he₁, he₂, he₃⟩, heu⟩ :=
    hpair C₀ D₀ hC hD j hj u c (by rw [hu₂, hg]) e₀ hu₁.symm he₀
  refine ⟨e, ⟨he₁, he₃, ?_⟩, fun e' ⟨he'₁, he'₂, he'₃⟩ ↦ ?_⟩
  · show X.map e.op (a.app _ eU) = g
    rw [aPt_comp (a := a) e eU, he₂]
    exact hu₂
  · have hu' : e' ≫ eU = u := by
      refine huu (e' ≫ eU) ⟨?_, ?_⟩
      · show j ≫ e' ≫ eU = e₀ ≫ eU
        rw [← Category.assoc, he'₁]
      · rw [← he'₃]
        exact (aPt_comp (a := a) e' eU).symm
    exact heu e' ⟨he'₁, hu', he'₂⟩

include hfs hpair hyE in
omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- **`E` is formally smooth relative to `T'`.** -/
theorem exists_lift_of_pair (C₀ D₀ : BigFppfOver B S hS)
    (hC : IsAffine ((BigFppfOver.toScheme B S hS).obj C₀))
    (hD : IsAffine ((BigFppfOver.toScheme B S hS).obj D₀)) (j : D₀ ⟶ C₀)
    (hj : IsSquareZeroClosedImmersion B S hS j) (c : C₀ ⟶ T') (e₀ : D₀ ⟶ E)
    (he₀ : e₀ ≫ eT = j ≫ c) : ∃ e : C₀ ⟶ E, j ≫ e = e₀ ∧ e ≫ eT = c := by
  obtain ⟨u, hu₁, hu₂⟩ := hfs D₀ C₀ hD hC j hj (e₀ ≫ eU) (Y.map c.op y) (by
    show f.app _ (a.app _ (e₀ ≫ eU)) = _
    rw [show a.app _ (e₀ ≫ eU) = X.map e₀.op (aPt (a := a) eU) from (aPt_comp e₀ eU).symm,
      f.naturality_apply, hyE, ← Functor.map_comp_apply,
      ← op_comp, he₀, op_comp, Functor.map_comp_apply])
  obtain ⟨e, ⟨he₁, -, he₃⟩, -⟩ := hpair C₀ D₀ hC hD j hj u c hu₂ e₀ hu₁.symm he₀
  exact ⟨e, he₁, he₃⟩

section Pullback

variable (B S hS T' f y a)
variable (hrep : yoneda.relativelyRepresentable (a ≫ f))

/-- The fibre product `U ×_Y T'`, as an object of the site. -/
abbrev UZ : BigFppfOver B S hS := hrep.pullback (yonedaEquiv.symm y)

/-- The projection `U ×_Y T' ⟶ U`. -/
abbrev UZfst : UZ B S hS T' f y a hrep ⟶ U := hrep.fst' (yonedaEquiv.symm y)

/-- The projection `U ×_Y T' ⟶ T'`. -/
abbrev UZsnd : UZ B S hS T' f y a hrep ⟶ T' := hrep.snd (yonedaEquiv.symm y)

variable {B S hS T' f y a hrep}

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- If `f(a(u)) = Y(c)(y)`, then `yoneda u ≫ a ≫ f = yoneda c ≫ y` as transformations. -/
lemma yoneda_compat {C₀ : BigFppfOver B S hS} (u : C₀ ⟶ U) (c : C₀ ⟶ T')
    (h : f.app _ (a.app (op C₀) u) = Y.map c.op y) :
    yoneda.map u ≫ (a ≫ f) = yoneda.map c ≫ yonedaEquiv.symm y := by
  apply yonedaEquiv.injective
  simpa [yonedaEquiv_comp, yonedaEquiv_apply, yonedaEquiv_symm_app_apply] using h

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- If `yoneda u ≫ a ≫ f = yoneda c ≫ y` as transformations, then `f(a(u)) = Y(c)(y)`. -/
lemma compat_of_yoneda {C₀ : BigFppfOver B S hS} (u : C₀ ⟶ U) (c : C₀ ⟶ T')
    (h : yoneda.map u ≫ (a ≫ f) = yoneda.map c ≫ yonedaEquiv.symm y) :
    f.app _ (a.app (op C₀) u) = Y.map c.op y := by
  have := congrArg (fun φ ↦ yonedaEquiv φ) h
  simpa [yonedaEquiv_comp, yonedaEquiv_apply, yonedaEquiv_symm_app_apply] using this

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- The two projections of `U ×_Y T'` satisfy `f(a(UZfst)) = Y(UZsnd)(y)`. -/
lemma UZ_compat : f.app _ (aPt (a := a) (UZfst B S hS T' f y a hrep)) =
    Y.map (UZsnd B S hS T' f y a hrep).op y := by
  refine compat_of_yoneda _ _ ?_
  rw [Functor.relativelyRepresentable.map_fst']
  exact hrep.w (yonedaEquiv.symm y)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- **An object formally étale over `U ×_Y T'` has the pair lifting property.** -/
theorem pairFormallyEtale_of_formallyEtale {E : BigFppfOver B S hS}
    (eZ : E ⟶ UZ B S hS T' f y a hrep) (heZ : FormallyEtale (yoneda.map eZ)) :
    PairFormallyEtale B S hS T' f y a (eZ ≫ UZsnd B S hS T' f y a hrep)
      (eZ ≫ UZfst B S hS T' f y a hrep) := by
  intro C₀ D₀ hC hD j hj u c hcomp e₀ heU heT
  let m : C₀ ⟶ UZ B S hS T' f y a hrep := hrep.lift' u c (yoneda_compat u c hcomp)
  have hm₁ : m ≫ UZfst B S hS T' f y a hrep = u := hrep.lift'_fst _ _ _
  have hm₂ : m ≫ UZsnd B S hS T' f y a hrep = c := hrep.lift'_snd _ _ _
  have hext : ∀ {W : BigFppfOver B S hS} (p q : W ⟶ UZ B S hS T' f y a hrep),
      p ≫ UZfst B S hS T' f y a hrep = q ≫ UZfst B S hS T' f y a hrep →
      p ≫ UZsnd B S hS T' f y a hrep = q ≫ UZsnd B S hS T' f y a hrep → p = q :=
    fun p q h₁ h₂ ↦ hrep.hom_ext' h₁ h₂
  have hjm : e₀ ≫ eZ = j ≫ m := hext _ _ (by
    rw [Category.assoc, Category.assoc, hm₁]; exact heU) (by
    rw [Category.assoc, Category.assoc, hm₂]; exact heT)
  obtain ⟨z, ⟨hz₁, hz₂⟩, hzu⟩ := heZ D₀ C₀ hD hC j hj e₀ m hjm
  have hz₂' : z ≫ eZ = m := hz₂
  refine ⟨z, ⟨hz₁, ?_, ?_⟩, fun e' ⟨he'₁, he'₂, he'₃⟩ ↦ hzu e' ⟨he'₁, ?_⟩⟩
  · rw [← Category.assoc, hz₂', hm₁]
  · rw [← Category.assoc, hz₂', hm₂]
  · show e' ≫ eZ = m
    refine hext _ _ ?_ ?_
    · rw [Category.assoc, he'₂, hm₁]
    · rw [Category.assoc, he'₃, hm₂]

end Pullback

end AlgebraicGeometry.Space.ChartGlue

end
