module

public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitLocalFactorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOfAffineEtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticConditionCriteria
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductDecomposition
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Comparison
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ConstantSheaf

/-!
# Stacks 0AJ1 is false for a large index

**Stacks 0AJ1** states: let `{Xᵢ ⟶ X}_{i ∈ I}` be a family of maps of sheaves on the big fppf
site of `S` such that (a) each `Xᵢ` is a formal algebraic space, (b) each `Xᵢ ⟶ X` is
representable by algebraic spaces and étale, and (c) `∐ Xᵢ ⟶ X` is a surjection of sheaves;
then `X` is a formal algebraic space. A formal algebraic space (Definition 0AIM) is required to
satisfy the set-theoretic condition of **Stacks 0AIS**: an object `U` of the site surjects onto
it. The source's proof composes the atlases of the `Xᵢ` and does not address that condition,
and this file shows that it can fail when the index set `I` is at least as large as the size
cutoff of the site. Observation (3) of Remark 0AIS makes the corresponding proviso, *if `I` is
not too large*; under it the tag holds
(`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_etaleCover_of_admitsCoproductIndex`).

## The counterexample

Let `σ` be a discrete set and let `X` be the sheaf `T ↦ C(|T|, σ)` of locally constant
`σ`-valued functions, an fppf (indeed fpqc) sheaf. For each `s ∈ σ` let `Xₛ = h_S` be the
sheaf of the final object `S` of the site, a formal algebraic space, with `Xₛ ⟶ X` the constant
function `s`. The base change of `Xₛ ⟶ X` along a point `φ : h_T ⟶ X` is the open subscheme
`φ⁻¹(s)` of `T`, so `Xₛ ⟶ X` is representable and étale; and a function `φ ∈ X(T)` is constant
on the members of the open cover `{φ⁻¹(φ(t))}` of `T`, so `∐ Xₛ ⟶ X` is a surjection of
sheaves. But a surjection `h_U ⟶ X` from an object `U` of the site is impossible once
`#σ ≥ cutoff`: it is given by one function `φ_U : |U| → σ`, whose image has fewer than
`2 ^ size U < cutoff` elements; for `s` outside that image, the constant section `s` over the
nonempty object `S` does not lift to `U` over any nonempty object, whereas it must lift over the
members of a covering sieve, and these cover the points of `S`.

## Main results

* `AlgebraicGeometry.FormalSpace.EtaleCoverCounterexample.isRepresentableEtale_constMap`,
  `…isLocallySurjective_sigmaDesc_constMap`: the family `{h_S ⟶ X}` satisfies (a)–(c).
* `AlgebraicGeometry.FormalSpace.EtaleCoverCounterexample.not_isFormalAlgebraicSpace_contSheaf`:
  for `#σ` at least the cutoff, `X` is not a formal algebraic space.
* `AlgebraicGeometry.FormalSpace.not_forall_isFormalAlgebraicSpace_of_etaleCover`: over a
  nonempty scheme `S` of the site, the statement of Stacks 0AJ1 with no bound on the index is
  false.

## References

* [Stacks Project, Tag 0AJ1](https://stacks.math.columbia.edu/tag/0AJ1)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

namespace AlgebraicGeometry.FormalSpace.EtaleCoverCounterexample

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (σ : Type (u + 1)) [TopologicalSpace σ] [DiscreteTopology σ]

/-- The presheaf `T ↦ C(|T|, σ)` of continuous, that is locally constant, `σ`-valued functions
on the big fppf site of `S`. -/
def contPresheaf : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) :=
  (BigFppfOver.toScheme B S hS).op ⋙ continuousMapPresheaf.{u + 1, u} σ

omit [DiscreteTopology σ] in
/-- Locally constant `σ`-valued functions form an fppf sheaf: they form an fpqc sheaf on all
schemes, and restrict to a sheaf on the big fppf site of `S`. -/
theorem isSheaf_contPresheaf :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (contPresheaf B S hS σ) :=
  isSheaf_bigFppf_of_isSheaf_fpqc B S hS ((Over.forget S).op ⋙ continuousMapPresheaf σ)
    ((Over.forget S).op_comp_isSheaf_of_isSheaf _ _ _
      (isSheaf_fpqcTopology_continuousMapPresheaf σ))

/-- The fppf sheaf of locally constant `σ`-valued functions. -/
def contSheaf : FppfSheaf B S hS := ⟨contPresheaf B S hS σ, isSheaf_contPresheaf B S hS σ⟩

/-- The final object `S` of the big fppf site of `S`. -/
def base : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))

/-- The structure morphism of an object of the big fppf site of `S`, as a morphism to the final
object. -/
def toBase (W : BigFppfOver B S hS) : W ⟶ base B S hS :=
  Over.homMk W.hom (by simp [base])

/-- A morphism to the final object is unique. -/
instance (W : BigFppfOver B S hS) : Subsingleton (W ⟶ base B S hS) := by
  refine ⟨fun a b ↦ ?_⟩
  ext1
  exact (cancel_mono (𝟙 _)).1 ((Over.w a).trans (Over.w b).symm)

/-- The constant function `s`, as a morphism into the sheaf of locally constant functions. -/
def constMap (s : σ) (Y : FppfSheaf B S hS) : Y ⟶ contSheaf B S hS σ :=
  ⟨{ app := fun _W => ↾fun _ => ContinuousMap.const _ s
     naturality := fun _ _ _ => rfl }⟩

omit [DiscreteTopology σ] in
/-- A morphism `h_U ⟶ X` into the sheaf of locally constant functions is given by one function
`φ` on `U`, and sends a point `c : V ⟶ U` to `φ ∘ c`. -/
theorem app_eq_comp {U V : BigFppfOver B S hS}
    (ξ : uliftYoneda.{u + 1}.obj U ⟶ contPresheaf B S hS σ) (c : V ⟶ U) :
    ξ.app (op V) (ULift.up c) =
      (uliftYonedaEquiv ξ).comp ((BigFppfOver.toScheme B S hS).map c).base.hom := by
  conv_lhs => rw [← Equiv.symm_apply_apply uliftYonedaEquiv ξ]
  rfl

variable [(BigFppfOver.topology B S hS).Subcanonical]

/-- The base change of the constant function `s : h_S ⟶ X` along a point `φ : h_U ⟶ X` is the
open subscheme `φ⁻¹(s)` of `U`. -/
theorem exists_isPullback_constMap (s : σ) (U : BigFppfOver B S hS)
    (ξ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ contSheaf B S hS σ) :
    ∃ (W : BigFppfOver B S hS) (p : W ⟶ U)
      (r : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj W ⟶
        (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj (base B S hS)),
      IsPullback r ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map p)
        (constMap B S hS σ s _) ξ ∧
      IsOpenImmersion ((BigFppfOver.toScheme B S hS).map p) := by
  let J := BigFppfOver.topology B S hS
  let φ : C((BigFppfOver.toScheme B S hS).obj U, σ) := uliftYonedaEquiv ξ.hom
  let O : ((BigFppfOver.toScheme B S hS).obj U).Opens :=
    ⟨φ ⁻¹' {s}, (isOpen_discrete _).preimage φ.continuous⟩
  obtain ⟨W, p, hp, hrange, huniv⟩ := exists_restrict_bigFppfOver U O
  have hmono : Mono p := (BigFppfOver.toScheme B S hS).mono_of_mono_map (IsOpenImmersion.mono _)
  refine ⟨W, p, J.uliftYoneda.{u + 1}.map (toBase B S hS W), ?_, hp⟩
  have hpre : IsPullback (J.uliftYoneda.{u + 1}.map (toBase B S hS W)).hom
      (J.uliftYoneda.{u + 1}.map p).hom (constMap B S hS σ s _).hom ξ.hom := by
    refine IsPullback.of_forall_isPullback_app fun V ↦ ?_
    rw [Types.isPullback_iff]
    refine ⟨?_, ?_, ?_⟩
    · ext ⟨a⟩
      change ContinuousMap.const _ s = ξ.hom.app V (ULift.up (a ≫ p))
      refine Eq.trans ?_ (app_eq_comp B S hS σ ξ.hom (a ≫ p)).symm
      ext y
      have hy : ((BigFppfOver.toScheme B S hS).map p)
          (((BigFppfOver.toScheme B S hS).map a) y) ∈ (O : Set _) := by
        rw [← hrange]
        exact Set.mem_range_self _
      exact hy.symm
    · rintro ⟨a⟩ ⟨a'⟩ ⟨-, h⟩
      have h' : a ≫ p = a' ≫ p := congrArg ULift.down h
      rw [cancel_mono] at h'
      rw [h']
    · rintro ⟨b⟩ ⟨c⟩ h
      have h' : ContinuousMap.const _ s = φ.comp ((BigFppfOver.toScheme B S hS).map c).base.hom :=
        h.trans (app_eq_comp B S hS σ ξ.hom c)
      have hsub : Set.range ((BigFppfOver.toScheme B S hS).map c) ⊆ (O : Set _) := by
        rintro _ ⟨y, rfl⟩
        simpa [O] using (congrArg (fun F ↦ F y) h').symm
      obtain ⟨a, ha⟩ := huniv c hsub
      refine ⟨ULift.up a, ?_, congrArg ULift.up ha⟩
      apply ULift.ext
      exact Subsingleton.elim (α := unop V ⟶ base B S hS) _ _
  exact IsPullback.of_map (sheafToPresheaf J (Type (u + 1)))
    ((sheafToPresheaf J (Type (u + 1))).map_injective (by simpa using hpre.w)) hpre

/-- Condition (b) of Stacks 0AJ1 for the counterexample: each constant function `h_S ⟶ X` is
representable by algebraic spaces and étale, its base changes being open immersions. -/
theorem isRepresentableEtale_constMap (s : σ) :
    IsRepresentableEtale B S hS (constMap B S hS σ s
      ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj (base B S hS))) :=
  isRepresentableEtale_of_relative_openImmersion B S hS _ fun U ξ ↦
    exists_isPullback_constMap B S hS σ s U ξ

/-- Condition (c) of Stacks 0AJ1 for the counterexample: the constant functions are jointly
surjective, a locally constant function being constant on the members of an open cover. -/
theorem isLocallySurjective_sigmaDesc_constMap :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    Sheaf.IsLocallySurjective (Sigma.desc fun s : σ ↦ constMap B S hS σ s
      ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj (base B S hS))) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let J := BigFppfOver.topology B S hS
  let G : σ → FppfSheaf B S hS := fun _ ↦ J.uliftYoneda.{u + 1}.obj (base B S hS)
  refine ⟨fun {V} x ↦ ?_⟩
  change C((BigFppfOver.toScheme B S hS).obj V, σ) at x
  let O : (BigFppfOver.toScheme B S hS).obj V → ((BigFppfOver.toScheme B S hS).obj V).Opens :=
    fun v ↦ ⟨x ⁻¹' {x v}, (isOpen_discrete _).preimage x.continuous⟩
  have hO : TopologicalSpace.IsOpenCover O :=
    TopologicalSpace.IsOpenCover.mk
      (eq_top_iff.2 fun v _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨v, rfl⟩)
  obtain ⟨I, W, a, r, hcov, hmem⟩ := bigFppfOver_openCoverData B S hS O hO
  refine J.superset_covering ((Sieve.generate_le_iff _ _).2 ?_) hcov
  rintro _ _ ⟨i⟩
  refine ⟨(Sigma.ι G (x (r i))).hom.app (op (W i)) (ULift.up (toBase B S hS (W i))), ?_⟩
  have h := congrArg (fun φ : G (x (r i)) ⟶ contSheaf B S hS σ ↦
    φ.hom.app (op (W i)) (ULift.up (toBase B S hS (W i))))
    (Sigma.ι_comp_desc (fun s : σ ↦ constMap B S hS σ s (G s)) (x (r i)))
  refine (Eq.trans ?_ h).trans ?_
  · rfl
  · exact ContinuousMap.ext fun y ↦ (hmem i y).symm

omit [DiscreteTopology σ] [(BigFppfOver.topology B S hS).Subcanonical] in
/-- For `#σ` at least the size cutoff of the site, the sheaf of locally constant `σ`-valued
functions over a nonempty `S` does not satisfy the set-theoretic condition of Stacks 0AIS: a
function on an object `U` of the site takes fewer values than the cutoff, and a missed value
cannot be lifted locally. -/
theorem not_satisfiesSetTheoreticCondition_contSheaf [Nonempty S]
    (hσ : Cardinal.lift.{u + 1} B.cutoff ≤ #σ) :
    ¬ SatisfiesSetTheoreticCondition B S hS (contSheaf B S hS σ) := by
  intro h
  let : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  obtain ⟨U, t, ht⟩ := exists_epi_uliftYoneda_of_satisfiesSetTheoreticCondition h
  let φ : C((BigFppfOver.toScheme B S hS).obj U, σ) := uliftYonedaEquiv t.hom
  have hU : #((BigFppfOver.toScheme B S hS).obj U) < B.cutoff :=
    (Scheme.mk_le_two_pow_size _).trans_lt (B.cutoff_isStrongPrelimit U.left.property)
  have hle : #(Set.range φ) ≤ Cardinal.lift.{u + 1} #((BigFppfOver.toScheme B S hS).obj U) := by
    have h0 := Cardinal.mk_range_le_lift (f := φ)
    rwa [Cardinal.lift_id'.{u, u + 1}] at h0
  have hrange : #(Set.range φ) < #σ := hle.trans_lt ((Cardinal.lift_lt.2 hU).trans_le hσ)
  obtain ⟨s, hs⟩ : ∃ s, s ∉ Set.range φ := by
    by_contra! hcon
    rw [Set.eq_univ_of_forall hcon, Cardinal.mk_univ] at hrange
    exact lt_irrefl _ hrange
  let x : (contSheaf B S hS σ).obj.obj (op (base B S hS)) := ContinuousMap.const _ s
  obtain ⟨w⟩ := ‹Nonempty S›
  obtain ⟨Y, g, ⟨⟨c⟩, hc⟩, ⟨y, -⟩⟩ := BigFppfOver.exists_mem_arrows_mem_range B S hS
    (((Sheaf.isLocallySurjective_iff_epi t).2 ht).imageSieve_mem x)
    (w : (BigFppfOver.toScheme B S hS).obj (base B S hS))
  have h1 : t.hom.app (op Y) (ULift.up c) =
      φ.comp ((BigFppfOver.toScheme B S hS).map c).base.hom :=
    app_eq_comp B S hS σ t.hom c
  have h2 := congrArg (fun F : C((BigFppfOver.toScheme B S hS).obj Y, σ) ↦ F y) (hc.symm.trans h1)
  exact hs ⟨((BigFppfOver.toScheme B S hS).map c) y, h2.symm⟩

omit [DiscreteTopology σ] [(BigFppfOver.topology B S hS).Subcanonical] in
/-- For `#σ` at least the size cutoff of the site, the sheaf of locally constant `σ`-valued
functions over a nonempty `S` is not a formal algebraic space. -/
theorem not_isFormalAlgebraicSpace_contSheaf [Nonempty S]
    (hσ : Cardinal.lift.{u + 1} B.cutoff ≤ #σ) :
    ¬ IsFormalAlgebraicSpace B S hS (contSheaf B S hS σ) :=
  fun h ↦ not_satisfiesSetTheoreticCondition_contSheaf B S hS σ hσ h.1

end AlgebraicGeometry.FormalSpace.EtaleCoverCounterexample

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

open EtaleCoverCounterexample in
/-- **Stacks 0AJ1 is false without a bound on the index.** Over a nonempty scheme `S` of a big
fppf site, it is not the case that every fppf sheaf `X` with a family `{Xᵢ ⟶ X}` satisfying
conditions (a), (b) and (c) of Stacks 0AJ1 is a formal algebraic space: the sheaf of locally
constant functions with values in a discrete set as large as the cutoff of the site, with its
family of constant functions out of `h_S`, satisfies (a)–(c) but not the set-theoretic
condition of Stacks 0AIS that Definition 0AIM asks of a formal algebraic space. -/
@[stacks 0AJ1 "the statement as printed is false: over any nonempty S, the sheaf of locally \
constant functions to a discrete set as large as the size cutoff of the site, with the family of \
its constant sections out of h_S, satisfies (a)-(c) but fails the set-theoretic condition of \
Stacks 0AIS; the corrected form is \
AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_etaleCover_of_admitsCoproductIndex"]
theorem not_forall_isFormalAlgebraicSpace_of_etaleCover [Nonempty S] :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    ¬ ∀ (I : Type (u + 1)) (X : FppfSheaf B S hS) (Xi : I → FppfSheaf B S hS)
      (f : ∀ i, Xi i ⟶ X),
      (∀ i, IsFormalAlgebraicSpace B S hS (Xi i)) →
      (∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f i).hom,
        Space.HasPropertyULift.{u + 1} B S hS
          (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (f i).hom hfi) →
      Sheaf.IsLocallySurjective (Sigma.desc f) →
      IsFormalAlgebraicSpace B S hS X := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  intro h
  let σ : Type (u + 1) := ULift.{u + 1} B.cutoff.out
  let : TopologicalSpace σ := ⊥
  have : DiscreteTopology σ := ⟨rfl⟩
  have hσ : Cardinal.lift.{u + 1} B.cutoff ≤ #σ := by
    rw [Cardinal.mk_uLift, Cardinal.mk_out]
  exact not_isFormalAlgebraicSpace_contSheaf B S hS σ hσ
    (h σ (contSheaf B S hS σ) _ _
      (fun _ ↦ isFormalAlgebraicSpace_uliftYoneda B S hS (base B S hS))
      (fun s ↦ isRepresentableEtale_constMap B S hS σ s)
      (isLocallySurjective_sigmaDesc_constMap B S hS σ))

end AlgebraicGeometry.FormalSpace
