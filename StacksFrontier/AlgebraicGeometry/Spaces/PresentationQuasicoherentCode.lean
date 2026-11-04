module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFinitePresentationCode
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSeparator
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackFinitePresentationStability

/-!
# Isomorphism classes of finitely presented modules on an algebraic space with an affine
presentation

Let `F = U/R` be an algebraic space presented by an étale equivalence relation whose presenting
scheme `U` and relation scheme `R` are affine. By Stacks 03M3 a quasi-coherent `𝒪_F`-module is the
same as a quasi-coherent module `(𝓕, α)` on the groupoid `(U, R, s, t, c)`. When the module is
of finite presentation, `𝓕` is a finitely presented quasi-coherent module on the affine `U`, which
is determined up to isomorphism by a finite matrix over `𝒪(U)`, and once `𝓕` is fixed the
transition `α : t^*𝓕 ⟶ s^*𝓕` is determined by finitely many sections of `s^*𝓕` over the affine
`R`, which form a finitely generated `𝒪(R)`-module. So the finitely presented quasi-coherent
`𝒪_F`-modules have at most `max ℵ₀ (max #𝒪(U) #𝒪(R))` isomorphism classes.

## Main results

* `AlgebraicGeometry.Space.exists_code_of_presentation`: an injection of the isomorphism classes
  of finitely presented quasi-coherent `𝒪_F`-modules into a type of that cardinality.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
  (P : Presentation B S hS F hF)

/-- The finitely presented quasi-coherent modules on an algebraic space. -/
abbrev FinitePresentationModules (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :=
  {M : Modules.{u, u} B S hS F hF //
    M.IsQuasicoherentOnSite ∧ SheafOfModules.IsFinitePresentationOnSite M}

/-- The codes of the finitely presented quasi-coherent modules on the presenting scheme of a
presentation. -/
abbrev presentationObjectCode :=
  Σ n k : ℕ, Fin k → Fin n →
    chartRing B S hS (yoneda.obj P.U) (isAlgebraicSpace_yoneda B S hS P.U) (idChart B S hS P.U)

/-- The pullback of a finitely presented module along a morphism of algebraic spaces is of finite
presentation. -/
theorem FinitePresentationModules.isFinitePresentationOnSite_modulePullback
    {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y) (M : FinitePresentationModules Y.1 Y.2) :
    SheafOfModules.IsFinitePresentationOnSite ((modulePullback B S hS g).obj M.1) :=
  (modulePullbackStabilityOfFinitePresentation B S hS).finitePresentation g M.1 M.2.2

/-- The finitely presented quasi-coherent module `t^*W` on the relation scheme. -/
def pullbackFinitePresentationModule {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y)
    (M : FinitePresentationModules Y.1 Y.2) : FinitePresentationModules X.1 X.2 :=
  ⟨(modulePullback B S hS g).obj M.1,
    have := FinitePresentationModules.isFinitePresentationOnSite_modulePullback g M
    inferInstance,
    FinitePresentationModules.isFinitePresentationOnSite_modulePullback g M⟩


/-- A sigma type over a type of cardinality at most an infinite cardinal `c`, with fibres of
cardinality at most `c`, has cardinality at most `c`. -/
theorem _root_.Cardinal.mk_sigma_le_of_le {K : Type u} {X : K → Type u} {c : Cardinal.{u}}
    (hc : ℵ₀ ≤ c) (hK : #K ≤ c) (hX : ∀ κ, #(X κ) ≤ c) : #(Σ κ, X κ) ≤ c := by
  rw [Cardinal.mk_sigma]
  calc sum (fun κ => #(X κ)) ≤ sum (fun _ : K => c) := sum_le_sum _ _ hX
    _ = lift.{u} #K * lift.{u} c := sum_const _ _
    _ = #K * c := by simp
    _ ≤ c * c := by gcongr
    _ = c := mul_eq_self hc

/-- Tuples of elements of a finitely generated module over a ring of cardinality at most an
infinite cardinal `c` form a type of cardinality at most `c`. -/
private theorem _root_.Cardinal.mk_fin_arrow_le_of_module_finite {A M : Type u} [Ring A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] {c : Cardinal.{u}} (hc : ℵ₀ ≤ c)
    (hA : #A ≤ c) (n : ℕ) : #(Fin n → M) ≤ c := by
  rw [show #(Fin n → M) = #M ^ (n : Cardinal) by simp]
  exact (power_le_power_right ((Cardinal.mk_le_of_module_finite A M).trans
    (max_le hc hA))).trans (power_nat_le hc)

omit P in
/-- Transported transition morphisms that agree up to the identification of the two fixed
modules give isomorphic quasi-coherent modules on the groupoid. -/
theorem nonempty_iso_of_heq_transportedTransition {A : AlgebraicSpaces B S hS}
    {G : GroupoidInAlgebraicSpaces B S hS A} {Y Y' : QuasicoherentModule B S hS G}
    {W W' : Modules.{u, u} B S hS G.objects.obj G.objects.property} (hW : W = W')
    (e : Y.F.obj ≅ W) (e' : Y'.F.obj ≅ W')
    (h : HEq (transportedTransition Y e) (transportedTransition Y' e')) : Nonempty (Y ≅ Y') := by
  subst hW
  exact ⟨isoOfTransportedTransitionEq e e' (eq_of_heq h)⟩

omit P in
/-- An injective family of maps on a dependent family reflects heterogeneous equality. -/
theorem heq_of_heq_of_injective {K : Type*} {A : K → Type*} {X : K → Type*}
    (w : ∀ κ, A κ → X κ) (hw : ∀ κ, Function.Injective (w κ)) {κ κ' : K} (hκ : κ = κ')
    {x : A κ} {x' : A κ'} (h : HEq (w κ x) (w κ' x')) : HEq x x' := by
  subst hκ
  exact heq_of_eq (hw κ (eq_of_heq h))

/-- **The isomorphism classes of finitely presented quasi-coherent modules on an algebraic space
with a presentation by affine schemes are at most `max ℵ₀ (max #𝒪(U) #𝒪(R))`.** -/
theorem exists_code_of_presentation
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj P.U))
    (hR : IsAffine ((BigFppfOver.toScheme B S hS).obj P.R)) :
    ∃ (ι : Type u) (_ : #ι ≤ max ℵ₀
        (max #(chartRing B S hS (yoneda.obj P.U) (isAlgebraicSpace_yoneda B S hS P.U)
            (idChart B S hS P.U))
          #(chartRing B S hS (yoneda.obj P.R) (isAlgebraicSpace_yoneda B S hS P.R)
            (idChart B S hS P.R))))
      (c : FinitePresentationModules F hF → ι), ∀ M M', c M = c M' → Nonempty (M.1 ≅ M'.1) := by
  classical
  let G := presentationGroupoid P
  obtain ⟨cU, hcU⟩ := exists_code_of_isTerminal (isAlgebraicSpace_yoneda B S hS P.U)
    (isTerminal_idChart B S hS P.U) hU
  let K := {κ : presentationObjectCode P // ∃ W, cU W = κ}
  choose rep hrep using fun κ : K => κ.2
  let Wt : K → FinitePresentationModules (yoneda.obj P.R) (isAlgebraicSpace_yoneda B S hS P.R) :=
    fun κ => pullbackFinitePresentationModule G.target (rep κ)
  let Ws : K → FinitePresentationModules (yoneda.obj P.R) (isAlgebraicSpace_yoneda B S hS P.R) :=
    fun κ => pullbackFinitePresentationModule G.source (rep κ)
  choose n w hw using fun κ : K => exists_injective_hom_of_isTerminal
    (isAlgebraicSpace_yoneda B S hS P.R) (isTerminal_idChart B S hS P.R) hR
    (Wt κ).1 (Ws κ).1 (Wt κ).2.1 (Wt κ).2.2
  have := isEquivalence_quasicoherentFromSpaceBase B S hS G (presentationAtlas P)
    (presentationAtlas_isEtale P) (presentationAtlas_comm P)
    (presentationAtlas_isEtaleCovering P) (presentationAtlas_relativelyRepresentable P)
    (presentationGroupoid_isPullback P)
  let Φ := quasicoherentFromSpaceBase B S hS G (presentationAtlas P) (presentationAtlas_comm P)
  let Y : FinitePresentationModules F hF → QuasicoherentModule B S hS G :=
    fun M => Φ.obj ⟨M.1, M.2.1⟩
  have hYfp : ∀ M, SheafOfModules.IsFinitePresentationOnSite (Y M).F.obj := fun M => by
    show SheafOfModules.IsFinitePresentationOnSite
      (spaceBaseObj B S hS G (presentationAtlas P) (presentationAtlas_comm P) ⟨M.1, M.2.1⟩).F.obj
    rw [spaceBaseObj_F_obj]
    exact FinitePresentationModules.isFinitePresentationOnSite_modulePullback
      (Y := ⟨F, hF⟩) (presentationAtlas P) M
  let WY : FinitePresentationModules F hF →
      FinitePresentationModules (yoneda.obj P.U) (isAlgebraicSpace_yoneda B S hS P.U) :=
    fun M => ⟨(Y M).F.obj, (Y M).F.property, hYfp M⟩
  let κ : FinitePresentationModules F hF → K := fun M => ⟨cU (WY M), WY M, rfl⟩
  let e : ∀ M, (Y M).F.obj ≅ (rep (κ M)).1 := fun M =>
    (hcU (WY M) (rep (κ M)) (hrep (κ M)).symm).some
  let ι := Σ κ : K, Fin (n κ) → (Ws κ).1.val.obj (op (idChart B S hS P.R))
  refine ⟨ι, ?_, fun M => ⟨κ M, w (κ M) (transportedTransition (Y M) (e M))⟩, ?_⟩
  · have hc := le_max_left ℵ₀ (max #(chartRing B S hS (yoneda.obj P.U)
      (isAlgebraicSpace_yoneda B S hS P.U) (idChart B S hS P.U))
        #(chartRing B S hS (yoneda.obj P.R) (isAlgebraicSpace_yoneda B S hS P.R)
          (idChart B S hS P.R)))
    refine Cardinal.mk_sigma_le_of_le hc ?_ fun κ => ?_
    · exact (mk_subtype_le _).trans <| mk_sigma_nat_le hc fun n => mk_sigma_nat_le hc fun k =>
        mk_fin_fin_le hc ((le_max_left _ _).trans (le_max_right _ _)) k n
    · have := module_finitePresentation_sections_of_isFinitePresentationOnSite (Ws κ).1
        (Ws κ).2.1 (Ws κ).2.2 (idChart B S hS P.R) hR
      exact mk_fin_arrow_le_of_module_finite hc ((le_max_right _ _).trans (le_max_right _ _)) _
  · intro M M' h
    have hκ : κ M = κ M' := congrArg Sigma.fst h
    obtain ⟨i⟩ := nonempty_iso_of_heq_transportedTransition
      (congrArg (fun κ => (rep κ).1) hκ) (e M) (e M')
      (heq_of_heq_of_injective w hw hκ (Sigma.mk.inj_iff.mp h).2)
    exact ⟨(ObjectProperty.ι _).mapIso ((Functor.FullyFaithful.ofFullyFaithful Φ).preimageIso i)⟩

end AlgebraicGeometry.Space

end
