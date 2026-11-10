module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismLimitPresentationNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartLimitAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineCanonicalFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.PropertyMonotone
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal

/-!
# Quasi-affine morphisms of finite type of spaces are closed in finitely presented ones

**Stacks 0871** over an arbitrary quasi-compact quasi-separated algebraic space `Y`: a morphism
`f : X ⟶ Y` of algebraic spaces which is locally of finite type and quasi-affine is a closed
immersion into an algebraic space of finite presentation over `Y`.

## Main results

* `exists_isFinitePresentation_isClosedImmersion_of_isQuasiAffineHom_of_noetherianApproximation`:
  Stacks 0871 over an arbitrary algebraic space, granted Stacks 07SU over `Spec ℤ`.

## Implementation notes

The source's route: factor a quasi-affine `f` as a quasi-compact open immersion into an affine
morphism (Stacks 086S), write that affine morphism as a limit of finitely presented ones
(Stacks 0870), and conclude with Stacks 0828.  The form over a representable target, which needs
none of the held statements, is
`AlgebraicGeometry.Space.exists_isFinitePresentation_isClosedImmersion_of_isQuasiAffineHom`.

## References

* [Stacks Project, Tag 0871](https://stacks.math.columbia.edu/tag/0871)
* [Stacks Project, Tag 086S](https://stacks.math.columbia.edu/tag/086S)
* [Stacks Project, Tag 0870](https://stacks.math.columbia.edu/tag/0870)
* [Stacks Project, Tag 0828](https://stacks.math.columbia.edu/tag/0828)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A quasi-affine morphism of algebraic spaces is quasi-compact and quasi-separated. -/
theorem isQuasiCompact_and_isQuasiSeparated_of_isQuasiAffineHom
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hqa : IsQuasiAffineHom B S hS f) :
    IsQuasiCompact B S hS f ∧ IsQuasiSeparated B S hS f := by
  have hpre := presheaf_isQuasiAffineHom_of_isQuasiAffineHom_of_isAlgebraicSpace B S hS hX hY hqa
  exact ⟨isQuasiCompact_of_presheaf_quasiCompact B S hS
      (HasSchemeProperty.of_le (fun _ _ k hk => by have := hk; infer_instance) hpre),
    (isQuasiSeparated_iff_presheaf B S hS f hX hY hpre.rep).2
      (HasSchemeProperty.of_le (fun _ _ k hk => by have := hk; infer_instance) hpre)⟩

/-- The transition morphisms of a diagram of algebraic spaces affine over an algebraic space `Y`
are affine. -/
theorem isAffineHom_map_homOfLE_of_isAffineHom_app {I : Type*} [Preorder I]
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {D : Iᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)} (t : D ⟶ (Functor.const Iᵒᵖ).obj Y)
    (hDalg : ∀ i, IsAlgebraicSpace B S hS (D.obj i)) (hDaff : ∀ i, IsAffineHom B S hS (t.app i))
    ⦃i k : I⦄ (h : i ≤ k) : IsAffineHom B S hS (D.map (homOfLE h).op) := by
  have hn : D.map (homOfLE h).op ≫ t.app (Opposite.op i) = t.app (Opposite.op k) := by simp
  exact isAffineHom_of_isAffineHom_comp_of_isSeparated B S hS _ (t.app (Opposite.op i))
    (hn ▸ hDaff (Opposite.op k)) (isSeparated_of_isAffineHom B S hS _ (hDalg _) hY (hDaff _))

/-- **Stacks 0871**, over an arbitrary quasi-compact quasi-separated algebraic space `Y`, granted
Stacks 07SU over `Spec ℤ` (`h07SU`), the statement of a tag not yet proved here.  A morphism
`f : X ⟶ Y` of algebraic spaces which is locally of finite type and quasi-affine is a closed
immersion into an algebraic space of finite presentation over `Y`.

The source's proof: `X ⟶ \underline{Spec}_Y(f_* 𝒪_X)` is a quasi-compact open immersion (Stacks
086S, as `AlgebraicGeometry.Space.isQuasiAffineHom_iff_isOpenImmersion_toDirectImageSpec`); the
relative spectrum is a directed limit of spaces `Z_i` affine and of finite presentation over `Y`
(Stacks 0870, as
`AlgebraicGeometry.Space.exists_directed_limit_of_isAffineHom_of_noetherianApproximation`);
`X ⟶ Z_i` is an immersion for `i` large (Stacks 0828, part (2), as
`AlgebraicGeometry.Space.eventually_isImmersion_comp_limitπ`, which needs no bound on the index
set of Stacks 082A, the stages being quasi-separated as they are of finite presentation over `Y`);
and an immersion of a quasi-compact space is a closed immersion into a quasi-compact open
subspace, which is of finite presentation over `Y`. -/
theorem exists_isFinitePresentation_isClosedImmersion_of_isQuasiAffineHom_of_noetherianApproximation
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hft : IsLocallyOfFiniteType B S hS f) (hqa : IsQuasiAffineHom B S hS f)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (h07SU : ∀ Z : (BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B (⊤_ Scheme.{u}) B.contains_terminal Z →
        IsQuasiCompactSpace B (⊤_ Scheme.{u}) B.contains_terminal Z →
        IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal Z →
          HasNoetherianApproximation B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal Z) :
    ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f' : X' ⟶ Y) (i : X ⟶ X'),
      IsAlgebraicSpace B S hS X' ∧ IsFinitePresentation B S hS f' ∧
        IsClosedImmersion B S hS i ∧ i ≫ f' = f := by
  classical
  let X' : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Y' : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let g : X' ⟶ Y' := ObjectProperty.homMk f
  -- `f` is quasi-compact and quasi-separated, being quasi-affine
  obtain ⟨hfqc, hfqs⟩ :=
    isQuasiCompact_and_isQuasiSeparated_of_isQuasiAffineHom B S hS f hX hY hqa
  -- the canonical factorization `X ⟶ Spec_Y(f_* 𝒪_X) ⟶ Y`, an open immersion by Stacks 086S
  let Z := directImageSpec B S hS g hfqc hfqs
  let j := (toDirectImageSpec B S hS g hfqc hfqs).left
  have hjZ : j ≫ Z.obj.hom = g := (directImageSpec_factorization B S hS g hfqc hfqs).2.1
  have hjf : j.hom ≫ Z.obj.hom.hom = f := congrArg (fun k => k.hom) hjZ
  have hoi : IsOpenImmersion B S hS j.hom :=
    (isQuasiAffineHom_iff_isOpenImmersion_toDirectImageSpec B S hS g hfqc hfqs).1 hqa
  have hXqc : IsQuasiCompactSpace B S hS X :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS hY hYqc hfqc
  -- Stacks 0870 for the affine morphism `Spec_Y(f_* 𝒪_X) ⟶ Y`
  obtain ⟨I, hIpre, hIne, hIdir, D, t, p, hlim, hDalg, hDaff, hDfp, hpt⟩ :=
    exists_directed_limit_of_isAffineHom_of_noetherianApproximation B S hS Z.obj.hom.hom
      Z.obj.left.property hY Z.property hYqc hYqs h07SU
  let _ : Preorder I := hIpre
  let _ : Nonempty I := hIne
  let _ : IsDirected I (· ≤ ·) := hIdir
  have hcomm : (Cone.mk _ p).π ≫ t = (Functor.const Iᵒᵖ).map Z.obj.hom.hom :=
    NatTrans.ext (funext fun a => (hpt a).trans (Category.comp_id _).symm)
  -- the stages are quasi-separated, being of finite presentation over `Y`
  have hDqs : ∀ i : I,
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal (D.obj (Opposite.op i)) := fun i =>
    isAbsolutelyQuasiSeparated_of_isFinitePresentation B S hS B.contains_terminal (hDalg _) hYqs
      (hDfp _)
  -- Stacks 0828, part (2): `X ⟶ Z_i` is an immersion for `i` large
  have hjft : IsLocallyOfFiniteType B S hS (j.hom ≫ Z.obj.hom.hom) := by rwa [hjf]
  obtain ⟨i, hi⟩ := (eventually_isImmersion_comp_limitπ B S hS Y hY D
    (fun i => hDalg _) t (Cone.mk _ p) hlim Z.obj.hom.hom hcomm X hX hXqc j.hom
    (isAffineHom_map_homOfLE_of_isAffineHom_app B S hS hY t hDalg hDaff) hDqs
    hjft (isImmersion_of_isOpenImmersion B S hS hoi)).exists
  -- shrink to a closed immersion into a quasi-compact open subspace of `Z_i`
  obtain ⟨U, h, hUopen, hUqc, hhclosed, hhι⟩ :=
    exists_isQuasiCompactSpace_isClosedImmersion_of_isImmersion B S hS (hDalg _) hX hXqc _ hi
  have hUfp : IsFinitePresentation B S hS U.ι :=
    ⟨isLocallyOfFinitePresentation_of_isOpenImmersion B S hS hUopen.2,
      isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal (hDalg _) (hDqs i) hUqc _,
      isQuasiSeparated_of_mono B S hS _ inferInstance⟩
  refine ⟨U.toFunctor, U.ι ≫ t.app (Opposite.op i), h, hUopen.1,
    isFinitePresentation_comp B S hS hUopen.1 (hDalg _) hY _ _ hUfp (hDfp _), hhclosed, ?_⟩
  rw [← Category.assoc, hhι, Category.assoc]
  change j.hom ≫ (p.app (Opposite.op i) ≫ t.app (Opposite.op i)) = f
  rw [hpt, hjf]

end AlgebraicGeometry.Space

end
