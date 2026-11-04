module

public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Catenary
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.FibrePointsSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionFunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedAffineLineFibres
public import StacksFrontier.Topology.Dimension.NotCatenaryOfChains

/-!
# Branches glued along an étale equivalence relation

Let `s, t : E ⇉ V` be an étale equivalence relation on an affine scheme `V`, mapping by a
morphism locally of finite type to an algebraic space `T` all of whose decent algebraic spaces
locally of finite type are catenary. This file proves that an immediate specialization `x ⤳ y`
of `V` cannot sit on a branch through `y` which the relation glues to a branch through `y` of
codimension at least two. This is the step on which the proof of Stacks 0EDN rests, and where
the argument of the source is incomplete.

The obstruction is a decent algebraic space, locally of finite type over `T`, which is not
catenary. It is the affine line over `V` glued along `E`, but twisted by `a ↦ 1 - a` across the
branches. Write `C` for the closure of `x` and `λ` for the indicator of the complement of `C`. A
point `ε` of `E` with `λ(s ε) ≠ λ(t ε)` identifies `(s ε, a)` with `(t ε, 1 - a)`, and every other
point of `E` identifies `(s ε, a)` with `(t ε, a)`. In the quotient, the generic point of the line
over `x` specializes to the zero section over `y` along a maximal chain of length two through the
zero section over `x`. It also specializes along a chain of length three, through the zero section
of a branch of codimension at least two.

## Main definitions

* `AlgebraicGeometry.Space.ChartBranch.branchSet`: the set of points of `E` relating a point of `C`
  to a point outside `C`.

## Main results

* `AlgebraicGeometry.Space.ChartBranch.isClopen_branchSet`: that set is clopen.
* `AlgebraicGeometry.Space.ChartBranch.false_of_branches`: the configuration is impossible.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.ChartBranch

open TwistedAffineLine

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {V E : BigFppfOver B S hS} (s t : E ⟶ V)

/-- The set of points of the relation scheme which relate a point of `C` to a point outside
`C`. -/
def branchSet (C : Set ((BigFppfOver.toScheme B S hS).obj V)) :
    Set ((BigFppfOver.toScheme B S hS).obj E) :=
  {ε | ¬ (((BigFppfOver.toScheme B S hS).map s ε ∈ C) ↔
    ((BigFppfOver.toScheme B S hS).map t ε ∈ C))}

/-- **The branch set is clopen** when `C` is closed, the closure of its complement meets it only
inside a set `Y`, and near every point of the relation scheme over `Y` the two projections
agree. -/
theorem isClopen_branchSet (C : Set ((BigFppfOver.toScheme B S hS).obj V)) (hC : IsClosed C)
    (Y : Set ((BigFppfOver.toScheme B S hS).obj V)) (hsep : closure Cᶜ ∩ C ⊆ Y)
    (hloc : ∀ ε : (BigFppfOver.toScheme B S hS).obj E,
      (BigFppfOver.toScheme B S hS).map s ε ∈ Y ∨ (BigFppfOver.toScheme B S hS).map t ε ∈ Y →
        ∃ U : Set ((BigFppfOver.toScheme B S hS).obj E), IsOpen U ∧ ε ∈ U ∧
          ∀ ε' ∈ U, (BigFppfOver.toScheme B S hS).map s ε' =
            (BigFppfOver.toScheme B S hS).map t ε') :
    IsClopen (branchSet B S hS s t C) := by
  set σ := (BigFppfOver.toScheme B S hS).map s
  set τ := (BigFppfOver.toScheme B S hS).map t
  -- Away from `Y`, membership in `C` is locally constant.
  have hlc : ∀ v, v ∉ Y → ∃ U : Set ((BigFppfOver.toScheme B S hS).obj V), IsOpen U ∧ v ∈ U ∧
      ∀ w ∈ U, (w ∈ C ↔ v ∈ C) := by
    intro v hv
    by_cases hvC : v ∈ C
    · refine ⟨(closure Cᶜ)ᶜ, isClosed_closure.isOpen_compl, fun hcl ↦ hv (hsep ⟨hcl, hvC⟩),
        fun w hw ↦ ⟨fun _ ↦ hvC, fun _ ↦ ?_⟩⟩
      by_contra hwC
      exact hw (subset_closure hwC)
    · exact ⟨Cᶜ, hC.isOpen_compl, hvC, fun w hw ↦ ⟨fun h ↦ absurd h hw, fun h ↦ absurd h hvC⟩⟩
  -- Near every point, membership of the branch set is locally constant.
  have hnbhd : ∀ ε, ∃ U : Set ((BigFppfOver.toScheme B S hS).obj E), IsOpen U ∧ ε ∈ U ∧
      ∀ ε' ∈ U, (ε' ∈ branchSet B S hS s t C ↔ ε ∈ branchSet B S hS s t C) := by
    intro ε
    by_cases hy : σ ε ∈ Y ∨ τ ε ∈ Y
    · obtain ⟨U, hU, hεU, hst⟩ := hloc ε hy
      refine ⟨U, hU, hεU, fun ε' hε' ↦ ?_⟩
      simp only [branchSet, Set.mem_ofPred_eq]
      change ¬ (σ ε' ∈ C ↔ τ ε' ∈ C) ↔ ¬ (σ ε ∈ C ↔ τ ε ∈ C)
      rw [hst ε' hε', hst ε hεU]
      simp
    · rw [not_or] at hy
      obtain ⟨U₁, hU₁, hσU₁, h₁⟩ := hlc (σ ε) hy.1
      obtain ⟨U₂, hU₂, hτU₂, h₂⟩ := hlc (τ ε) hy.2
      refine ⟨σ ⁻¹' U₁ ∩ τ ⁻¹' U₂, (hU₁.preimage σ.continuous).inter (hU₂.preimage τ.continuous),
        ⟨hσU₁, hτU₂⟩, fun ε' hε' ↦ ?_⟩
      simp only [branchSet, Set.mem_ofPred_eq]
      change ¬ (σ ε' ∈ C ↔ τ ε' ∈ C) ↔ ¬ (σ ε ∈ C ↔ τ ε ∈ C)
      rw [h₁ _ hε'.1, h₂ _ hε'.2]
  refine ⟨isOpen_compl_iff.1 <| isOpen_iff_forall_mem_open.2 fun ε hε ↦ ?_,
    isOpen_iff_forall_mem_open.2 fun ε hε ↦ ?_⟩ <;> obtain ⟨U, hU, hεU, h⟩ := hnbhd ε
  · exact ⟨U, fun ε' hε' hmem ↦ hε ((h ε' hε').1 hmem), hU, hεU⟩
  · exact ⟨U, fun ε' hε' ↦ (h ε' hε').2 hε, hU, hεU⟩

/-! ### The twisting idempotent -/

section Idempotent

variable (C : Set ((BigFppfOver.toScheme B S hS).obj V)) (hBC : IsClopen (branchSet B S hS s t C))

/-- The idempotent of the branch set. -/
noncomputable def branchIdempotent : Γ((BigFppfOver.toScheme B S hS).obj E, ⊤) :=
  Scheme.clopenIdempotent (branchSet B S hS s t C) hBC

/-- The idempotent of the branch set is idempotent. -/
theorem isIdempotentElem_branchIdempotent :
    IsIdempotentElem (branchIdempotent B S hS s t C hBC) :=
  Scheme.isIdempotentElem_clopenIdempotent _ _

/-- The idempotent of a preimage of the branch set. -/
theorem appTop_branchIdempotent {T : Scheme.{u}} (f : T ⟶ (BigFppfOver.toScheme B S hS).obj E) :
    f.appTop (branchIdempotent B S hS s t C hBC) =
      Scheme.clopenIdempotent (f ⁻¹' branchSet B S hS s t C) (hBC.preimage f.continuous) :=
  Scheme.appTop_clopenIdempotent _ _ _

/-- The scheme morphism underlying `r ≫ f` is the composite of those underlying `r` and `f`. -/
theorem schemeHom_comp {T : Over (B.inclusion.obj (B.obj hS))} {X Y : BigFppfOver B S hS}
    (r : T ⟶ (Over.post B.inclusion).obj X) (f : X ⟶ Y) :
    schemeHom B S hS (r ≫ (Over.post B.inclusion).map f) =
      schemeHom B S hS r ≫ (BigFppfOver.toScheme B S hS).map f := rfl

/-- If `r ≫ f = r' ≫ f'`, then the underlying maps of schemes agree on every point `p`. -/
theorem apply_eq_of_comp_eq {T : Over (B.inclusion.obj (B.obj hS))} {X Y : BigFppfOver B S hS}
    {r r' : T ⟶ (Over.post B.inclusion).obj X} {f f' : X ⟶ Y}
    (h : r ≫ (Over.post B.inclusion).map f = r' ≫ (Over.post B.inclusion).map f') (p : T.left) :
    (BigFppfOver.toScheme B S hS).map f (schemeHom B S hS r p) =
      (BigFppfOver.toScheme B S hS).map f' (schemeHom B S hS r' p) := by
  have h' := congrArg (schemeHom B S hS) h
  rw [schemeHom_comp, schemeHom_comp] at h'
  rw [← Scheme.Hom.comp_apply, h', Scheme.Hom.comp_apply]

/-- The idempotent of the empty set is zero. -/
theorem clopenIdempotent_empty {X : Scheme.{u}} (h : IsClopen (∅ : Set X)) :
    Scheme.clopenIdempotent (∅ : Set X) h = 0 :=
  (Scheme.eq_of_isIdempotentElem_of_basicOpen_eq (Scheme.isIdempotentElem_clopenIdempotent _ h)
    (by change (0 : Γ(X, ⊤)) * 0 = 0; rw [mul_zero])
    (by rw [Scheme.coe_basicOpen_clopenIdempotent, Scheme.basicOpen_zero]; rfl))

/-- The idempotent of a clopen set depends only on the set. -/
theorem clopenIdempotent_congr {X : Scheme.{u}} {U U' : Set X} (h : U = U') (hU : IsClopen U)
    (hU' : IsClopen U') : Scheme.clopenIdempotent U hU = Scheme.clopenIdempotent U' hU' := by
  subst h; rfl

/-- The idempotent of the symmetric difference of clopen sets `U` and `U'` is `e + e' - 2 e e'`,
where `e` and `e'` are the idempotents of `U` and `U'`. -/
theorem clopenIdempotent_symmDiff {X : Scheme.{u}} {U U' : Set X} (hU : IsClopen U)
    (hU' : IsClopen U') (h : IsClopen (symmDiff U U')) :
    Scheme.clopenIdempotent (symmDiff U U') h =
      Scheme.clopenIdempotent U hU + Scheme.clopenIdempotent U' hU' -
        2 * Scheme.clopenIdempotent U hU * Scheme.clopenIdempotent U' hU' := by
  refine Scheme.eq_of_isIdempotentElem_of_basicOpen_eq
    (Scheme.isIdempotentElem_clopenIdempotent _ h)
    (Scheme.isIdempotentElem_xor (Scheme.isIdempotentElem_clopenIdempotent _ hU)
      (Scheme.isIdempotentElem_clopenIdempotent _ hU')) ?_
  rw [Scheme.coe_basicOpen_xor (Scheme.isIdempotentElem_clopenIdempotent _ hU)
      (Scheme.isIdempotentElem_clopenIdempotent _ hU'),
    Scheme.coe_basicOpen_clopenIdempotent, Scheme.coe_basicOpen_clopenIdempotent,
    Scheme.coe_basicOpen_clopenIdempotent]

/-- The branch idempotent pulls back to zero along a point `r` of `E` with `r ≫ s = r ≫ t`. -/
theorem branchIdempotent_cocycle₀ (T : Over (B.inclusion.obj (B.obj hS)))
    (r : T ⟶ (Over.post B.inclusion).obj E)
    (h : r ≫ (Over.post B.inclusion).map s = r ≫ (Over.post B.inclusion).map t) :
    (schemeHom B S hS r).appTop (branchIdempotent B S hS s t C hBC) = 0 := by
  rw [appTop_branchIdempotent]
  have hempty : schemeHom B S hS r ⁻¹' branchSet B S hS s t C = ∅ := by
    ext p
    simp only [Set.mem_preimage, branchSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false, not_not]
    rw [apply_eq_of_comp_eq B S hS h p]
  rw [clopenIdempotent_congr hempty _ (hempty ▸ (hBC.preimage (schemeHom B S hS r).continuous)),
    clopenIdempotent_empty]

/-- The branch idempotent has the same pullback along `r` and along a point `r'` of `E` with
the two projections exchanged. -/
theorem branchIdempotent_cocycle₁ (T : Over (B.inclusion.obj (B.obj hS)))
    (r r' : T ⟶ (Over.post B.inclusion).obj E)
    (h₁ : r' ≫ (Over.post B.inclusion).map s = r ≫ (Over.post B.inclusion).map t)
    (h₂ : r' ≫ (Over.post B.inclusion).map t = r ≫ (Over.post B.inclusion).map s) :
    (schemeHom B S hS r').appTop (branchIdempotent B S hS s t C hBC) =
      (schemeHom B S hS r).appTop (branchIdempotent B S hS s t C hBC) := by
  rw [appTop_branchIdempotent, appTop_branchIdempotent]
  refine clopenIdempotent_congr ?_ _ _
  ext p
  simp only [Set.mem_preimage, branchSet, Set.mem_ofPred_eq]
  rw [apply_eq_of_comp_eq B S hS h₁ p, apply_eq_of_comp_eq B S hS h₂ p]
  tauto

/-- For points `r₁, r₂, r₃` of `E` with `s ∘ r₁ = t ∘ r₂`, `t ∘ r₃ = t ∘ r₁` and
`s ∘ r₃ = s ∘ r₂`, the pullback of the branch idempotent along `r₃` is `e₁ + e₂ - 2 e₁ e₂`,
where `eᵢ` is its pullback along `rᵢ`. -/
theorem branchIdempotent_cocycle₂ (T : Over (B.inclusion.obj (B.obj hS)))
    (r₁ r₂ r₃ : T ⟶ (Over.post B.inclusion).obj E)
    (h₁ : r₁ ≫ (Over.post B.inclusion).map s = r₂ ≫ (Over.post B.inclusion).map t)
    (h₂ : r₃ ≫ (Over.post B.inclusion).map t = r₁ ≫ (Over.post B.inclusion).map t)
    (h₃ : r₃ ≫ (Over.post B.inclusion).map s = r₂ ≫ (Over.post B.inclusion).map s) :
    (schemeHom B S hS r₃).appTop (branchIdempotent B S hS s t C hBC) =
      (schemeHom B S hS r₁).appTop (branchIdempotent B S hS s t C hBC) +
        (schemeHom B S hS r₂).appTop (branchIdempotent B S hS s t C hBC) -
          2 * (schemeHom B S hS r₁).appTop (branchIdempotent B S hS s t C hBC) *
            (schemeHom B S hS r₂).appTop (branchIdempotent B S hS s t C hBC) := by
  rw [appTop_branchIdempotent, appTop_branchIdempotent, appTop_branchIdempotent,
    ← clopenIdempotent_symmDiff]
  · refine clopenIdempotent_congr ?_ _ _
    ext p
    simp only [Set.mem_preimage, branchSet, Set.mem_ofPred_eq, Set.mem_symmDiff]
    rw [apply_eq_of_comp_eq B S hS h₂ p, apply_eq_of_comp_eq B S hS h₃ p,
      apply_eq_of_comp_eq B S hS h₁ p]
    tauto
  · have h₁' := hBC.preimage (schemeHom B S hS r₁).continuous
    have h₂' := hBC.preimage (schemeHom B S hS r₂).continuous
    rw [Set.symmDiff_def]
    exact (h₁'.diff h₂').union (h₂'.diff h₁')

end Idempotent

/-! ### Points of represented presheaves -/

/-- Under the identification of points of a represented sheaf with points of the scheme, the
map induced by `yoneda.map h` is the map of schemes underlying `h`. -/
theorem pointsEquivScheme_symm_pointsMap {U W : BigFppfOver B S hS} (h : U ⟶ W)
    (a : (BigFppfOver.toScheme B S hS).obj U) :
    pointsMap B S hS (yoneda.obj U) (yoneda.map h) ((pointsEquivScheme B S hS U).symm a) =
      (pointsEquivScheme B S hS W).symm ((BigFppfOver.toScheme B S hS).map h a) := by
  apply (pointsEquivScheme B S hS W).injective
  rw [Equiv.apply_symm_apply]
  change pointsToScheme B S hS W _ = _
  rw [pointsToScheme_pointsMap_yoneda]
  change (BigFppfOver.toScheme B S hS).map h ((pointsEquivScheme B S hS U)
    ((pointsEquivScheme B S hS U).symm a)) = _
  rw [Equiv.apply_symm_apply]

/-! ### The twisted affine line is not catenary -/

section Main

open Stack.AlgebraicStacks (affineSpaceChart affineSpaceChartHom)
open _root_.AlgebraicGeometry.AffineSpace

attribute [local instance] pointTopology

/-- **No immediate specialization lies on a branch glued to a branch of codimension two.**

Let `s, t : E ⇉ V` be an étale equivalence relation on an object `V` of the site with affine
underlying scheme, with `s` quasi-compact, and let `ψ : V ⟶ T` be a morphism locally of finite
type, invariant under the relation, to an algebraic space `T` all of whose decent algebraic
spaces locally of finite type are catenary. Suppose that `ψ` separates every point from its
proper specializations. Let `x ⤳ y` be an immediate specialization of `V` and let `C` be the
closure of `x`. Suppose that the closure of the complement of `C` meets `C` inside a set `Y`, and
that near every point of `E` over `Y` the two projections agree. Then no point `x'` related to `x`
has a strict chain `x' ⤳ x₁ ⤳ y` of length two. -/
theorem false_of_branches {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hcat : IsUniversallyCatenary B S hS T)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [hrel : Stacks.Groupoids.IsEtaleEquivalenceRelation (Space.relation B S hS s t)]
    (hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map s))
    (φ : yoneda.obj V ⟶ T) (hφ : IsLocallyOfFiniteType B S hS φ)
    (hinv : yoneda.map s ≫ φ = yoneda.map t ≫ φ)
    (hφsep : ∀ a b : (BigFppfOver.toScheme B S hS).obj V, b ⤳ a →
      pointsMap B S hS (yoneda.obj V) φ ((pointsEquivScheme B S hS V).symm a) =
        pointsMap B S hS (yoneda.obj V) φ ((pointsEquivScheme B S hS V).symm b) → a = b)
    (x y : (BigFppfOver.toScheme B S hS).obj V) (hxy : x ⤳ y) (hxy' : x ≠ y)
    (himm : ∀ z, x ⤳ z → z ⤳ y → z = x ∨ z = y)
    (Y : Set ((BigFppfOver.toScheme B S hS).obj V))
    (hsep : closure (closure {x})ᶜ ∩ closure {x} ⊆ Y)
    (hloc : ∀ ε : (BigFppfOver.toScheme B S hS).obj E,
      (BigFppfOver.toScheme B S hS).map s ε ∈ Y ∨ (BigFppfOver.toScheme B S hS).map t ε ∈ Y →
        ∃ U : Set ((BigFppfOver.toScheme B S hS).obj E), IsOpen U ∧ ε ∈ U ∧
          ∀ ε' ∈ U, (BigFppfOver.toScheme B S hS).map s ε' =
            (BigFppfOver.toScheme B S hS).map t ε')
    (x' x₁ : (BigFppfOver.toScheme B S hS).obj V) (ε : (BigFppfOver.toScheme B S hS).obj E)
    (hσε : (BigFppfOver.toScheme B S hS).map s ε = x)
    (hτε : (BigFppfOver.toScheme B S hS).map t ε = x')
    (h₁ : x' ⤳ x₁) (h₂ : x₁ ⤳ y) (h₃ : x₁ ≠ x') (h₄ : x₁ ≠ y) : False := by
  classical
  set σ := (BigFppfOver.toScheme B S hS).map s with hσ
  set τ := (BigFppfOver.toScheme B S hS).map t with hτ
  set C : Set ((BigFppfOver.toScheme B S hS).obj V) := closure {x} with hC
  have hBC := isClopen_branchSet B S hS s t C isClosed_closure Y hsep hloc
  set e := branchIdempotent B S hS s t C hBC with he_def
  have he : IsIdempotentElem e := isIdempotentElem_branchIdempotent B S hS s t C hBC
  -- The twisted relation and its quotient.
  have htw := isEtaleEquivalenceRelation_twisted B S hS s t e he
    (branchIdempotent_cocycle₀ B S hS s t C hBC) (branchIdempotent_cocycle₁ B S hS s t C hBC)
    (branchIdempotent_cocycle₂ B S hS s t C hBC)
  have : HasSheafify (BigFppfOver.topology B S hS) (Type u) := BigFppfOver.hasSheafify_type B S hS
  set P := quotientPresentation_unconditional B S hS (twistedSource B S hS s)
    (twistedTarget B S hS t e) with hP
  set Z := (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
    (Space.relation B S hS (twistedSource B S hS s) (twistedTarget B S hS t e))).obj with hZ_def
  have hZ : IsAlgebraicSpace B S hS Z := isAlgebraicSpace_quotient_unconditional B S hS _ _
  -- The twisted line is decent.
  have hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj P.U) :=
    inferInstanceAs (IsAffine 𝔸(Idx; (BigFppfOver.toScheme B S hS).obj V))
  have hsrc : QuasiCompact ((BigFppfOver.toScheme B S hS).map P.source) := by
    change QuasiCompact (AffineSpace.map Idx σ)
    exact MorphismProperty.of_isPullback (AffineSpace.isPullback_map _).flip hqc
  have hZqs := isAbsolutelyQuasiSeparated_of_presentation B S hS hZ P B.contains_terminal
    inferInstance hsrc
  have hZdec : IsDecentSpace B S hS Z :=
    isDecentSpace_of_isAbsolutelyQuasiSeparated B S hS Z hZ hZqs
  -- The structure morphism of the twisted line to `T`.
  set k : yoneda.obj (affineSpaceChart B S hS V 1) ⟶ T :=
    yoneda.map (affineSpaceChartHom B S hS V 1) ≫ φ with hk
  have htgt : twistedTarget B S hS t e ≫ affineSpaceChartHom B S hS V 1 =
      affineSpaceChartHom B S hS E 1 ≫ t := by
    ext1
    apply ObjectProperty.hom_ext
    change (twist e ≫ AffineSpace.map Idx τ) ≫ 𝔸(Idx; (BigFppfOver.toScheme B S hS).obj V) ↘ _ =
      (𝔸(Idx; (BigFppfOver.toScheme B S hS).obj E) ↘ _) ≫ τ
    rw [Category.assoc, AffineSpace.map_over, twist_over_assoc]
  have hsrcp : twistedSource B S hS s ≫ affineSpaceChartHom B S hS V 1 =
      affineSpaceChartHom B S hS E 1 ≫ s := by
    ext1
    apply ObjectProperty.hom_ext
    change AffineSpace.map Idx σ ≫ 𝔸(Idx; (BigFppfOver.toScheme B S hS).obj V) ↘ _ =
      (𝔸(Idx; (BigFppfOver.toScheme B S hS).obj E) ↘ _) ≫ σ
    rw [AffineSpace.map_over]
  have hkk : yoneda.map (twistedTarget B S hS t e) ≫ k =
      yoneda.map (twistedSource B S hS s) ≫ k := by
    rw [hk, ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, htgt,
      hsrcp, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hinv]
  obtain ⟨f, hf, -⟩ := existsUnique_hom_of_atlas_invariant B S hS hZ.isSheaf hT.isSheaf
    P.toSpace P.surjective P.etale k (fun R' s' t' hsq ↦ by
      obtain ⟨l, hl, hr⟩ : ∃ l, l ≫ yoneda.map (twistedTarget B S hS t e) = yoneda.map s' ∧
          l ≫ yoneda.map (twistedSource B S hS s) = yoneda.map t' :=
        ⟨_, P.isPullback.lift_fst _ _ hsq.w, P.isPullback.lift_snd _ _ hsq.w⟩
      rw [← hl, ← hr]
      exact (Category.assoc _ _ _).trans ((congrArg (l ≫ ·) hkk).trans
        (Category.assoc _ _ _).symm))
  -- It is locally of finite type.
  have hUalg := isAlgebraicSpace_yoneda B S hS (affineSpaceChart B S hS V 1)
  have hValg := isAlgebraicSpace_yoneda B S hS V
  have hklft : IsLocallyOfFiniteType B S hS k := by
    refine isLocallyOfFiniteType_comp B S hS hUalg hValg hT _ _ ?_
      hφ
    rw [isLocallyOfFiniteType_yoneda_map_iff]
    change LocallyOfFiniteType (𝔸(Idx; (BigFppfOver.toScheme B S hS).obj V) ↘ _)
    infer_instance
  have hflft : IsLocallyOfFiniteType B S hS f :=
    isLocallyOfFiniteType_of_exists_surjective_etale_source_chart B S hS
      ⟨P.U, P.toSpace, P.surjective, P.etale, by rw [hf]; exact hklft⟩
  -- So its point space is catenary, and sober.
  have hZcat := hcat Z hZ hZdec f hflft
  have hsober := stacksSober_points_of_isDecentSpace B S hS hZ hZdec
  have : T0Space (points B S hS Z) := (stacksSober_iff_t0_and_quasiSober.mp hsober).1
  have : QuasiSober (points B S hS Z) := (stacksSober_iff_t0_and_quasiSober.mp hsober).2
  /- The points of the twisted line, read on the affine line over `V`. -/
  set π := 𝔸(Idx; (BigFppfOver.toScheme B S hS).obj V) ↘ (BigFppfOver.toScheme B S hS).obj V
    with hπ
  set πE := 𝔸(Idx; (BigFppfOver.toScheme B S hS).obj E) ↘ (BigFppfOver.toScheme B S hS).obj E
    with hπE
  set hU := schemePointsHomeomorph B S hS P.U with hU_def
  set Q : 𝔸(Idx; (BigFppfOver.toScheme B S hS).obj V) → points B S hS Z :=
    fun a ↦ pointsMap B S hS (yoneda.obj P.U) P.toSpace (hU.symm a) with hQ
  set φpt : (BigFppfOver.toScheme B S hS).obj V → points B S hS T :=
    fun v ↦ pointsMap B S hS (yoneda.obj V) φ ((pointsEquivScheme B S hS V).symm v) with hφpt
  have hQc : Continuous Q := (continuous_pointsMap B S hS P.toSpace).comp hU.symm.continuous
  have hQgen : ∀ {a : 𝔸(Idx; (BigFppfOver.toScheme B S hS).obj V)} {w : points B S hS Z},
      w ⤳ Q a → ∃ a', a' ⤳ a ∧ Q a' = w := by
    intro a w h
    obtain ⟨p, hp, rfl⟩ := generalizingMap_pointsMap_of_isDecentSpace B S hS Z hZ hZdec P.U
      P.toSpace P.etale h
    refine ⟨hU p, ?_, ?_⟩
    · exact hU.symm.isInducing.specializes_iff.1 (by rwa [Homeomorph.symm_apply_apply])
    · change pointsMap B S hS (yoneda.obj P.U) P.toSpace (hU.symm (hU p)) = _
      rw [Homeomorph.symm_apply_apply]
  have hQeq : ∀ {a b : 𝔸(Idx; (BigFppfOver.toScheme B S hS).obj V)}, b ⤳ a → Q a = Q b →
      a = b := fun {a b} h hab ↦
    eq_of_specializes_of_pointsMap_eq_of_isDecentSpace B S hS hZ hZdec P.U P.toSpace
      (isEtale_of_presheaf_etale B S hS P.etale) a b hab h
  have hVeq : ∀ {a b : (BigFppfOver.toScheme B S hS).obj V}, b ⤳ a → φpt a = φpt b →
      a = b := fun {a b} h hab ↦ hφsep a b h hab
  have hP1 : ∀ a, pointsMap B S hS Z f (Q a) = φpt (π a) := by
    intro a
    change pointsMap B S hS Z f (pointsMap B S hS (yoneda.obj P.U) P.toSpace
      ((pointsEquivScheme B S hS P.U).symm a)) = _
    rw [← pointsMap_comp_apply, hf, hk]
    exact (pointsMap_comp_apply B S hS (yoneda.map (affineSpaceChartHom B S hS V 1)) φ
      ((pointsEquivScheme B S hS (affineSpaceChart B S hS V 1)).symm a)).trans
      (congrArg (pointsMap B S hS (yoneda.obj V) φ)
        (pointsEquivScheme_symm_pointsMap B S hS (affineSpaceChartHom B S hS V 1) a))
  have hrelQ : ∀ a b, Q a = Q b → ∃ ρ : 𝔸(Idx; (BigFppfOver.toScheme B S hS).obj E),
      (twist e ≫ AffineSpace.map Idx τ) ρ = a ∧ AffineSpace.map Idx σ ρ = b := by
    intro a b hab
    obtain ⟨r, hr1, hr2⟩ := (P.pointsRelation_iff _ _).2 hab
    refine ⟨pointsEquivScheme B S hS P.R r, ?_, ?_⟩
    · have h := pointsEquivScheme_symm_pointsMap B S hS P.target (pointsEquivScheme B S hS P.R r)
      rw [Equiv.symm_apply_apply, hr1] at h
      exact ((pointsEquivScheme B S hS P.U).symm.injective h).symm
    · have h := pointsEquivScheme_symm_pointsMap B S hS P.source (pointsEquivScheme B S hS P.R r)
      rw [Equiv.symm_apply_apply, hr2] at h
      exact ((pointsEquivScheme B S hS P.U).symm.injective h).symm
  have hrelQ' : ∀ ρ : 𝔸(Idx; (BigFppfOver.toScheme B S hS).obj E),
      Q ((twist e ≫ AffineSpace.map Idx τ) ρ) = Q (AffineSpace.map Idx σ ρ) := by
    intro ρ
    refine (P.pointsRelation_iff _ _).1 ⟨(pointsEquivScheme B S hS P.R).symm ρ, ?_, ?_⟩
    · exact pointsEquivScheme_symm_pointsMap B S hS P.target ρ
    · exact pointsEquivScheme_symm_pointsMap B S hS P.source ρ
  have hπσ : ∀ ρ, π (AffineSpace.map Idx σ ρ) = σ (πE ρ) := by
    intro ρ
    rw [← Scheme.Hom.comp_apply, AffineSpace.map_over, Scheme.Hom.comp_apply]
  have hπτ : ∀ ρ, π ((twist e ≫ AffineSpace.map Idx τ) ρ) = τ (πE ρ) := by
    intro ρ
    rw [← Scheme.Hom.comp_apply, Category.assoc, AffineSpace.map_over, twist_over_assoc,
      Scheme.Hom.comp_apply]
  /- Facts about the fibres of the affine line over `V`. -/
  have hc_over : ∀ (c : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) v,
      π (constSection c v) = v := fun c v ↦ constSection_apply_over c v
  have hgen_mem : ∀ {p : 𝔸(Idx; (BigFppfOver.toScheme B S hS).obj V)},
      (∀ r, π r = π p → p ⤳ r) →
        p ∈ (𝔸(Idx; (BigFppfOver.toScheme B S hS).obj V)).basicOpen
          (coord ((BigFppfOver.toScheme B S hS).obj V) c₀) := fun {p} h ↦
    (h (constSection 1 (π p)) (hc_over _ _)).mem_open (Scheme.basicOpen _ _).isOpen
      (constSection_one_mem_basicOpen_coord _)
  have hz0_ne : ∀ {p : 𝔸(Idx; (BigFppfOver.toScheme B S hS).obj V)} {v},
      π p = v → (∀ r, π r = v → p ⤳ r) → p ≠ constSection 0 v := by
    rintro p v rfl h heq
    exact constSection_zero_notMem_basicOpen_coord (π p) (heq ▸ hgen_mem h)
  have hπz : ∀ {p : 𝔸(Idx; (BigFppfOver.toScheme B S hS).obj V)} {v},
      p ⤳ constSection 0 v → π p ⤳ v := fun {p v} h ↦ by
    have := h.map π.continuous
    rwa [hc_over] at this
  /- Two points of a fibre which both specialize to every point of the fibre are equal. -/
  have hfib : ∀ {v} {g g' : 𝔸(Idx; (BigFppfOver.toScheme B S hS).obj V)}, π g = v → π g' = v →
      (∀ r, π r = v → g ⤳ r) → (∀ r, π r = v → g' ⤳ r) → g = g' := fun hg hg' h h' ↦
    eq_of_fibre_generic (hg'.trans hg.symm) (fun r hr ↦ h r (hr.trans hg))
      (fun r hr ↦ h' r (hr.trans hg))
  /- The generic points of the fibres over `x` and `x'` are identified. -/
  obtain ⟨gx, hgxπ, hgx⟩ := exists_generic_fibre x
  obtain ⟨gx', hgx'π, hgx'⟩ := exists_generic_fibre x'
  change π gx = x at hgxπ
  change π gx' = x' at hgx'π
  obtain ⟨gε, hgεπ, hgε⟩ := exists_generic_fibre ε
  change πE gε = ε at hgεπ
  have hgε0 : gε ⤳ constSection 0 ε := hgε _ (constSection_apply_over 0 ε)
  have hgε1 : gε ⤳ constSection 1 ε := hgε _ (constSection_apply_over 1 ε)
  have hσc : ∀ c : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤),
      AffineSpace.map Idx σ (constSection (σ.appTop c) ε) = constSection c x := by
    intro c
    rw [← Scheme.Hom.comp_apply, constSection_comp_map, Scheme.Hom.comp_apply, hσε]
  have hσ0 := hσc 0
  have hσ1 := hσc 1
  rw [map_zero] at hσ0
  rw [map_one] at hσ1
  have hgx_eq : AffineSpace.map Idx σ gε = gx := by
    have hA : AffineSpace.map Idx σ gε ⤳ constSection 0 x := by
      rw [← hσ0]; exact hgε0.map (AffineSpace.map Idx σ).continuous
    have hB : AffineSpace.map Idx σ gε ⤳ constSection 1 x := by
      rw [← hσ1]; exact hgε1.map (AffineSpace.map Idx σ).continuous
    have hπg : π (AffineSpace.map Idx σ gε) = x := by rw [hπσ, hgεπ, hσε]
    exact (hfib hgxπ hπg hgx fun r hr ↦ specializes_of_specializes_two hA hB
      (constSection_zero_ne_one x) ((hc_over 0 x).trans hπg.symm) ((hc_over 1 x).trans hπg.symm) r
      (hr.trans hπg.symm)).symm
  have hmemT : ∀ c : Γ((BigFppfOver.toScheme B S hS).obj E, ⊤),
      (twist e ≫ AffineSpace.map Idx τ) (constSection c ε) ∈
          (𝔸(Idx; (BigFppfOver.toScheme B S hS).obj V)).basicOpen
            (coord ((BigFppfOver.toScheme B S hS).obj V) c₀) ↔
        ε ∈ ((BigFppfOver.toScheme B S hS).obj E).basicOpen (c + e * (1 - 2 * c)) := by
    intro c
    rw [← Scheme.Hom.comp_apply]
    change ε ∈ (constSection c ≫ twist e ≫ AffineSpace.map Idx τ) ⁻¹ᵁ
      (𝔸(Idx; (BigFppfOver.toScheme B S hS).obj V)).basicOpen
        (coord ((BigFppfOver.toScheme B S hS).obj V) c₀) ↔ _
    rw [Scheme.preimage_basicOpen_top, constSection_twist_map, homOfVector_appTop_coord]
  have hneT : (twist e ≫ AffineSpace.map Idx τ) (constSection 0 ε) ≠
      (twist e ≫ AffineSpace.map Idx τ) (constSection 1 ε) := by
    intro heq
    have h0 := hmemT 0
    rw [heq, hmemT 1] at h0
    have hz : (0 : Γ((BigFppfOver.toScheme B S hS).obj E, ⊤)) + e * (1 - 2 * 0) = e := by ring
    have ho : (1 : Γ((BigFppfOver.toScheme B S hS).obj E, ⊤)) + e * (1 - 2 * 1) = 1 - e := by
      ring
    rw [hz, ho] at h0
    by_cases hεe : ε ∈ ((BigFppfOver.toScheme B S hS).obj E).basicOpen e
    · have h' := h0.2 hεe
      rw [Scheme.mem_basicOpen_top, map_sub, map_one,
        (Scheme.germ_eq_one_iff_mem_basicOpen_of_isIdempotentElem he ε).2 hεe, sub_self] at h'
      exact not_isUnit_zero h'
    · refine hεe (h0.1 ?_)
      rw [Scheme.mem_basicOpen_top, map_sub, map_one,
        Scheme.germ_eq_zero_of_isIdempotentElem_of_notMem he ε hεe, sub_zero]
      exact isUnit_one
  have hgx'_eq : (twist e ≫ AffineSpace.map Idx τ) gε = gx' := by
    have hA := hgε0.map (twist e ≫ AffineSpace.map Idx τ).continuous
    have hB := hgε1.map (twist e ≫ AffineSpace.map Idx τ).continuous
    have hπg : π ((twist e ≫ AffineSpace.map Idx τ) gε) = x' := by rw [hπτ, hgεπ, hτε]
    have hπc : ∀ c, π ((twist e ≫ AffineSpace.map Idx τ) (constSection c ε)) = x' := by
      intro c
      rw [hπτ]
      change τ ((𝔸(Idx; (BigFppfOver.toScheme B S hS).obj E) ↘ _) (constSection c ε)) = x'
      rw [constSection_apply_over, hτε]
    exact (hfib hgx'π hπg hgx' fun r hr ↦ specializes_of_specializes_two hA hB hneT
      ((hπc 0).trans hπg.symm) ((hπc 1).trans hπg.symm) r (hr.trans hπg.symm)).symm
  have hQg : Q gx' = Q gx := by rw [← hgx_eq, ← hgx'_eq]; exact hrelQ' gε
  /- The two chains. -/
  have hz0c := (constSection (0 : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))).continuous
  have hgxz : gx ⤳ constSection 0 x := hgx _ (hc_over 0 x)
  have hgx'z : gx' ⤳ constSection 0 x' := hgx' _ (hc_over 0 x')
  have hgxz' : gx ≠ constSection 0 x := hz0_ne hgxπ hgx
  have hgx'z' : gx' ≠ constSection 0 x' := hz0_ne hgx'π hgx'
  have hQne : ∀ {a b : 𝔸(Idx; (BigFppfOver.toScheme B S hS).obj V)}, a ⤳ b → a ≠ b →
      Q a ≠ Q b := fun {a b} h hne hQ ↦ hne (hQeq h hQ.symm).symm
  have hz0ne : ∀ {v w : (BigFppfOver.toScheme B S hS).obj V}, v ≠ w →
      constSection (0 : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) v ≠ constSection 0 w :=
    fun {v w} hvw h ↦ hvw (by rw [← hc_over 0 v, h, hc_over])
  have hab : Q gx ⤳ Q (constSection 0 x) := hgxz.map hQc
  have hbc : Q (constSection 0 x) ⤳ Q (constSection 0 y) := (hxy.map hz0c).map hQc
  have hab' : Q gx ≠ Q (constSection 0 x) := hQne hgxz hgxz'
  have hbc' : Q (constSection 0 x) ≠ Q (constSection 0 y) := hQne (hxy.map hz0c) (hz0ne hxy')
  have hap : Q gx ⤳ Q (constSection 0 x') := hQg ▸ hgx'z.map hQc
  have hpq : Q (constSection 0 x') ⤳ Q (constSection 0 x₁) := (h₁.map hz0c).map hQc
  have hqc : Q (constSection 0 x₁) ⤳ Q (constSection 0 y) := (h₂.map hz0c).map hQc
  have hap' : Q gx ≠ Q (constSection 0 x') := hQg ▸ hQne hgx'z hgx'z'
  have hpq' : Q (constSection 0 x') ≠ Q (constSection 0 x₁) :=
    hQne (h₁.map hz0c) (hz0ne (Ne.symm h₃))
  have hqc' : Q (constSection 0 x₁) ≠ Q (constSection 0 y) := hQne (h₂.map hz0c) (hz0ne h₄)
  /- The first step of the short chain is a covering. -/
  have hcov₁ : ∀ w, Q gx ⤳ w → w ⤳ Q (constSection 0 x) → w = Q gx ∨ w = Q (constSection 0 x) := by
    intro w hw₁ hw₂
    obtain ⟨w', hw'z, rfl⟩ := hQgen hw₂
    obtain ⟨g'', hg''w, hg''⟩ := hQgen hw₁
    have hπ1 : π g'' ⤳ π w' := hg''w.map π.continuous
    have hπ2 : π w' ⤳ x := hπz hw'z
    have hφeq : φpt x = φpt (π g'') := by
      rw [← hP1, hg'', hP1, hgxπ]
    have hg''x : x = π g'' := hVeq (hπ1.trans hπ2) hφeq
    have hw'x : π w' = x := (hπ2.antisymm (hg''x ▸ hπ1)).eq
    by_cases hw'eq : w' = constSection 0 x
    · right; rw [hw'eq]
    · left
      have hall := specializes_of_specializes_of_ne hw'z hw'eq (by rw [hc_over, hw'x])
      exact congrArg Q (hfib hgxπ hw'x hgx fun r hr ↦ hall r (hr.trans hw'x.symm)).symm
  /- The second step of the short chain is a covering: this is where the twist is used. -/
  have hcov₂ : ∀ w, Q (constSection 0 x) ⤳ w → w ⤳ Q (constSection 0 y) →
      w = Q (constSection 0 x) ∨ w = Q (constSection 0 y) := by
    intro w hw₁ hw₂
    obtain ⟨w', hw'z, rfl⟩ := hQgen hw₂
    obtain ⟨u, huw, hu⟩ := hQgen hw₁
    obtain ⟨ρ, hρ1, hρ2⟩ := hrelQ u (constSection 0 x) hu
    have hσρ : σ (πE ρ) = x := by rw [← hπσ, hρ2, hc_over]
    have hτρ : τ (πE ρ) = π u := by rw [← hπτ, hρ1]
    have hρ0 : ρ ∉ (𝔸(Idx; (BigFppfOver.toScheme B S hS).obj E)).basicOpen
        (coord ((BigFppfOver.toScheme B S hS).obj E) c₀) := by
      rw [← map_mem_basicOpen_coord_iff σ, hρ2]
      exact constSection_zero_notMem_basicOpen_coord x
    have huz : u ⤳ constSection 0 y := huw.trans hw'z
    have hbranch : (((BigFppfOver.toScheme B S hS).obj E).basicOpen e : Set _) =
        branchSet B S hS s t C := Scheme.coe_basicOpen_clopenIdempotent _ _
    by_cases hbr : πE ρ ∈ branchSet B S hS s t C
    · exfalso
      have he₁ : πE ρ ∈ ((BigFppfOver.toScheme B S hS).obj E).basicOpen e := by
        change πE ρ ∈ (((BigFppfOver.toScheme B S hS).obj E).basicOpen e : Set _)
        rw [hbranch]; exact hbr
      have h := twist_map_notMem_basicOpen_coord_sub_one τ he hρ0 he₁
      rw [hρ1] at h
      exact h (huz.mem_open (Scheme.basicOpen _ _).isOpen
        (constSection_zero_mem_basicOpen_coord_sub_one y))
    · have he₀ : πE ρ ∉ ((BigFppfOver.toScheme B S hS).obj E).basicOpen e := by
        intro h
        apply hbr
        have h' : πE ρ ∈ (((BigFppfOver.toScheme B S hS).obj E).basicOpen e : Set _) := h
        rwa [hbranch] at h'
      have hu0 := twist_map_notMem_basicOpen_coord τ he hρ0 he₀
      rw [hρ1] at hu0
      have huC : π u ∈ C := by
        simp only [branchSet, Set.mem_ofPred_eq, not_not] at hbr
        rw [← hτρ]
        exact hbr.1 (hσρ ▸ subset_closure rfl)
      have hxu : x ⤳ π u := specializes_iff_mem_closure.2 huC
      have huy : π u ⤳ y := hπz huz
      have hux : π u = x := by
        rcases himm _ hxu huy with h | h
        · exact h
        · exfalso
          have hφ : φpt y = φpt x := by
            rw [← h, ← hP1, hu, hP1, hc_over]
          exact hxy' (hVeq hxy hφ).symm
      have hw'1 : π u ⤳ π w' := huw.map π.continuous
      have hw'2 : π w' ⤳ y := hπz hw'z
      rw [hux] at hw'1
      rcases himm _ hw'1 hw'2 with h | h
      · left
        by_cases hneq : u = w'
        · rw [← hneq, hu]
        · exfalso
          have hall := specializes_of_specializes_of_ne huw hneq (by rw [h, hux])
          exact hu0 (hgen_mem hall)
      · right
        by_cases hneq : w' = constSection 0 y
        · rw [hneq]
        · exfalso
          have hall := specializes_of_specializes_of_ne hw'z hneq (by rw [hc_over, h])
          have hw'mem := hgen_mem hall
          exact hu0 (huw.mem_open (Scheme.basicOpen _ _).isOpen hw'mem)
  exact TopologicalSpace.not_isCatenarySpace_of_specializes hab hbc hab' hbc' hcov₁ hcov₂
    hap hpq hqc hap' hpq' hqc' hZcat

end Main

end AlgebraicGeometry.Space.ChartBranch

end
