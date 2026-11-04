module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType.Basis
public import StacksFrontier.Algebra.Module.Reflexive
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Depth
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TorsionFree
public import StacksFrontier.AlgebraicGeometry.Reflexive.Basic
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.Topology.Sheaves.Modules.Coherent

/-!
# An isomorphism criterion for a map to a torsion-free sheaf

Let `F ⟶ G` be a map of quasi-coherent modules on an integral locally Noetherian scheme, with
`F` coherent and `G` torsion free. If at every point the map on stalks is an isomorphism, or the
stalk of `F` has depth at least two and the point is not associated to `G`, then the map is an
isomorphism. This is Tag 0AVS, with alternative (2) in the form Tag 0AV8 gives it.

## Main results

* `AlgebraicGeometry.isIso_of_stalk_isIso_or_depth_two_and_not_associated_of_isTorsionFree`
  carries Tag 0AVS.
* `AlgebraicGeometry.isIso_of_stalk_isIso_or_depth_two_of_isTorsionFree` is the form in which the
  generic point is handled by a hypothesis on the map rather than by the clause on associated
  points, and
  `AlgebraicGeometry.isIso_of_stalk_isIso_or_depth_two_of_isTorsionFree_of_nontrivial_genericStalk`
  is that form with the generic-point condition replaced by `F_η ≠ 0`, which implies it.
* `AlgebraicGeometry.exists_counterexample_to_displayed_statement_of_tag_0AVS` and
  `AlgebraicGeometry.exists_counterexample_to_displayed_statement_of_tag_0AVS_specInt` are the
  counterexample to the statement of Tag 0AVS as displayed, the second on `Spec ℤ` with
  `G = 𝒪_X`.

## Implementation notes

The stalk map is the morphism of additive groups induced by the sheaf map, and the source stalk
carries its canonical module structure over the local ring. The point of the proof is that a
torsion-free quasi-coherent sheaf on an integral scheme has no associated point other than the
generic point: that is `eq_genericPoint_of_isAssociatedPoint_of_isTorsionFree` below, with
`associatedPrime_eq_bot_of_isTorsionFree` as its algebraic form. So at every point other than
the generic one the clause `x ∉ Ass(G)` of alternative (2) of
`isIso_of_stalk_isIso_or_depth_two_and_not_associated` (Tag 0AVM) holds of itself, which is why
the theorem carrying Tag 0AVS asks for it only at the generic point, and the criterion of that
theorem then applies.

**The form of alternative (2).** Tag 0AVS is proved in the source by "a translation of More on
Algebra, Lemma 0AV9 into the language of schemes", Tag 0AV9 by "a special case of Lemma 0AV8",
and the alternative (2) of Tag 0AV8 reads `depth(M_p) ≥ 2` **and** `p ∉ Ass(N)`. That clause is
the one the theorem here uses, and it cannot be dropped: alternative (2) of Tag 0AVS as
displayed, taken alone, holds vacuously on the zero sheaf, since the depth of the zero module
along any ideal is `⊤` by `Module.depth_eq_top_of_subsingleton`
(`StacksFrontier/RingTheory/Depth/Defs/Defs.lean:80`), the convention Tag 00LI fixes ("if `IM = M`
we set `depth_I(M) = ∞`"). So for `F = 0` and `G` any nonzero torsion-free sheaf — say `𝒪_X` on
`Spec ℤ` — `F` is coherent, `G` is torsion free, every source stalk has depth `⊤`, and `0 ⟶ G`
is not an isomorphism. `exists_counterexample_to_displayed_statement_of_tag_0AVS` and
`exists_counterexample_to_displayed_statement_of_tag_0AVS_specInt` below prove exactly this, so
the gap in the displayed statement is recorded here as a theorem rather than as a remark.
Alternative (2) of Tag 0AV8 excludes that configuration: a nonzero torsion-free sheaf on an
integral scheme has the generic point among its associated points, so alternative (1) is the one
available there.

The algebraic antecedent `bijective_of_bijective_localized_or_depth_two_of_isTorsionFree`
(Tag 0AV9) covers the same point from `[Nontrivial M]`; the corollary
`isIso_of_stalk_isIso_or_depth_two_of_isTorsionFree_of_nontrivial_genericStalk` is the form of
that precedent, and is less general, because `F_η ≠ 0` yields `hgeneric`: the local ring at `η`
is the function field, over which a nonzero module has depth `0`, so alternative (2) is
unavailable at `η`.

## References

* [Stacks Project, Tag 0AVS](https://stacks.math.columbia.edu/tag/0AVS)
* [Stacks Project, Tag 0AVM](https://stacks.math.columbia.edu/tag/0AVM)
* [Stacks Project, Tag 0AV8](https://stacks.math.columbia.edu/tag/0AV8)
* [Stacks Project, Tag 0AV9](https://stacks.math.columbia.edu/tag/0AV9)
* [Stacks Project, Tag 00LI](https://stacks.math.columbia.edu/tag/00LI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry


/-- A torsion-free sheaf on an integral scheme has no associated points away from the generic
point. -/
private theorem eq_genericPoint_of_isAssociatedPoint_of_isTorsionFree
    {X : Scheme.{u}} [IsIntegral X] {G : X.Modules} [G.IsQuasicoherent]
    (hG : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree G) {x : X}
    (hx : Stacks.Divisors.IsAssociatedPoint G x) : x = genericPoint X := by
  let : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) G.val x
  have hTF : Module.IsTorsionFree (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
    (isTorsionFree_iff_forall_stalk G).mp hG x
  change IsAssociatedPrimeStacks (X.presheaf.stalk x)
    (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x)
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) at hx
  rcases hx with ⟨_, m, hm⟩
  have hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk x) = ⊥ := by
    apply le_antisymm
    · intro r hr
      have hmkill : r • m = 0 := by
        have hmem : r ∈ (⊥ : Submodule (X.presheaf.stalk x)
            (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x)).colon
            (Submodule.span (X.presheaf.stalk x) {m}) := by
          simpa [hm] using hr
        simpa using Submodule.mem_colon_span_singleton.mp hmem
      have hmne : m ≠ 0 := by
        intro hm0
        rw [hm0] at hm
        have hcolon : (⊥ : Submodule (X.presheaf.stalk x)
            (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x)).colon
            (Submodule.span (X.presheaf.stalk x)
              ({(0 : TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x)} :
                Set (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x))) = ⊤ := by
          ext r
          simp
        exact (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk x)).ne_top
          (hm.symm.trans hcolon)
      by_contra hr0
      exact hmne (hTF.isSMulRegular (IsRegular.of_ne_zero hr0) (by simpa using hmkill))
    · exact bot_le
  let i := X.affineCover.idx x
  let U : X.Opens := (X.affineCover.f i).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.f i)
  let xU : U := ⟨x, X.affineCover.covers x⟩
  let : Nonempty U := ⟨xU⟩
  let p := hU.primeIdealOf xU
  let := X.presheaf.algebra_section_stalk xU
  let : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal := by
    simpa [p] using hU.isLocalization_stalk xU
  let : FaithfulSMul Γ(X, U) (X.presheaf.stalk x) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (IsLocalization.injective (S := X.presheaf.stalk x)
        p.asIdeal.primeCompl_le_nonZeroDivisors)
  have hunder := IsLocalization.AtPrime.under_maximalIdeal (R := Γ(X, U))
    (S := X.presheaf.stalk x) p.asIdeal
  have hp : p.asIdeal = ⊥ := by simpa [hmax] using hunder.symm
  have hpoint : p = genericPoint (Spec (CommRingCat.of Γ(X, U))) := by
    apply PrimeSpectrum.ext; simpa [genericPoint_eq_bot_of_affine] using hp
  have hgenU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U))
  let gU : U := ⟨genericPoint X, hgenU⟩
  have hpg : hU.primeIdealOf gU = genericPoint (Spec (CommRingCat.of Γ(X, U))) :=
    hU.primeIdealOf_genericPoint
  have hfrom : hU.fromSpec (genericPoint (Spec (CommRingCat.of Γ(X, U)))) = gU := by
    simpa [hpg] using hU.fromSpec_primeIdealOf gU
  have hxfrom : hU.fromSpec p = xU := hU.fromSpec_primeIdealOf xU
  have hEq := congrArg hU.fromSpec hpoint
  rwa [hxfrom, hfrom] at hEq

/-- **Stacks Project, Tag 0AVS.** Let `X` be an integral locally Noetherian scheme and
`f : F ⟶ G` a map of quasi-coherent modules with `F` coherent and `G` torsion free. If at every
point the map on stalks is an isomorphism, or the stalk of `F` has depth at least two and, at
the generic point, that point is not associated to `G`, then `f` is an isomorphism.

Alternative (2) is the one of Tag 0AV8, the lemma the source's proof of this statement reduces
to: Tag 0AVS is proved there as a translation of Tag 0AV9 into the language of schemes, Tag 0AV9
as a special case of Tag 0AV8, and the alternative (2) of Tag 0AV8 reads `depth(M_p) ≥ 2`
together with `p ∉ Ass(N)`. Over an integral base with `G` torsion free the clause on associated
points holds of itself at every point other than the generic one, by
`eq_genericPoint_of_isAssociatedPoint_of_isTorsionFree`, which is why it is asked for here only
at the generic point; that single point is where it does its work, by
`exists_counterexample_to_displayed_statement_of_tag_0AVS`, which exhibits a map satisfying
alternative (2) of Tag 0AVS as displayed at every point and failing to be an isomorphism. -/
@[stacks 0AVS "alternative (2) in the form Tag 0AV8 gives it, namely depth at least two at a
  point not associated to the target, which is the form the source's proof of this statement
  reduces to through Tag 0AV9, and asked for only at the generic point, the one point of an
  integral base at which a torsion-free target can have an associated point"]
theorem isIso_of_stalk_isIso_or_depth_two_and_not_associated_of_isTorsionFree
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] [F.IsCoherent]
    (f : F ⟶ G) (hG : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree G)
    (hf : ∀ x : X,
      let : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f.val)) ∨
      ((2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) ∧
        (x = genericPoint X → x ∉ Stacks.Divisors.associatedPoints G))) :
    IsIso f := by
  apply AlgebraicGeometry.isIso_of_stalk_isIso_or_depth_two_and_not_associated f
  intro x
  rcases hf x with h | ⟨hdepth, hass⟩
  · exact Or.inl h
  · refine Or.inr ⟨hdepth, ?_⟩
    by_cases hx : x = genericPoint X
    · exact hass hx
    · exact fun hxassoc => hx
        (eq_genericPoint_of_isAssociatedPoint_of_isTorsionFree hG hxassoc)

/-- **The criterion of Stacks Project, Tag 0AVS, with its generic-point clause as a hypothesis on
the map.** A map from a coherent sheaf to a torsion-free quasi-coherent sheaf on an integral
locally Noetherian scheme is an isomorphism if it is an isomorphism at the generic point and, at
every point, it is an isomorphism on stalks or the source stalk has depth at least two.

This is `isIso_of_stalk_isIso_or_depth_two_and_not_associated_of_isTorsionFree`, which carries
Tag 0AVS, in the form in which the generic point is handled by `hgeneric` rather than by the
clause on associated points of alternative (2). -/
theorem isIso_of_stalk_isIso_or_depth_two_of_isTorsionFree
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] [F.IsCoherent]
    (f : F ⟶ G) (hG : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree G)
    (hgeneric : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
      (genericPoint X)).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f.val)))
    (hf : ∀ x : X,
      let : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f.val)) ∨
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)) :
    IsIso f := by
  refine isIso_of_stalk_isIso_or_depth_two_and_not_associated_of_isTorsionFree f hG fun x ↦ ?_
  by_cases hx : x = genericPoint X
  · subst x; exact Or.inl hgeneric
  · exact (hf x).imp_right fun h ↦ ⟨h, fun h' ↦ absurd h' hx⟩

/-- Over a field a nonzero module has depth `0`: the maximal ideal is `⊥`, which admits no
regular sequence on a nonzero module. So such a module never has depth at least two. -/
private theorem not_two_le_depth_of_field {R : Type*} [Field R] (M : Type*)
    [AddCommGroup M] [Module R M] [Nontrivial M] :
    ¬ (2 : ℕ∞) ≤ Module.depth R (IsLocalRing.maximalIdeal R) M := by
  rw [IsLocalRing.maximalIdeal_eq_bot, Module.depth_bot_eq_zero]
  simp

/-- **The criterion of Stacks Project, Tag 0AVS** with the nondegeneracy hypothesis in the shape
of its algebraic antecedent `bijective_of_bijective_localized_or_depth_two_of_isTorsionFree`
(Tag 0AV9), which assumes the source nonzero: a nonzero stalk at the generic point yields the
generic-point hypothesis of `isIso_of_stalk_isIso_or_depth_two_of_isTorsionFree`, because the
local ring at the generic point of an integral scheme is the function field, over which a
nonzero module has depth `0`, so alternative (2) is unavailable there. This is therefore less
general than that theorem, which also covers `F = G = 0`. -/
theorem isIso_of_stalk_isIso_or_depth_two_of_isTorsionFree_of_nontrivial_genericStalk
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] [F.IsCoherent]
    (f : F ⟶ G) (hG : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree G)
    (hFgen : Nontrivial
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf (genericPoint X)))
    (hf : ∀ x : X,
      let : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f.val)) ∨
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)) :
    IsIso f := by
  refine isIso_of_stalk_isIso_or_depth_two_of_isTorsionFree f hG ?_ hf
  rcases hf (genericPoint X) with h | h
  · exact h
  · exact absurd h (not_two_le_depth_of_field _)

/-! ### The displayed alternative (2) of Tag 0AVS, taken alone -/

section Counterexample

open CategoryTheory.Limits ZeroObject

/-- A sheaf of modules which is a zero object has a subsingleton stalk at every point: the stalk
is the value at a zero object of two additive forgetful functors followed by the additive stalk
functor. -/
private theorem subsingleton_stalk_of_isZero {X : Scheme.{u}} {F : X.Modules} (hF : IsZero F)
    (x : X) : Subsingleton ↑(TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
  AddCommGrpCat.subsingleton_of_isZero
    (Functor.map_isZero (TopCat.Presheaf.stalkFunctor Ab.{u} x)
      (Functor.map_isZero (PresheafOfModules.toPresheaf X.ringCatSheaf.obj)
        (Functor.map_isZero (SheafOfModules.forget X.ringCatSheaf) hF)))

/-- A sheaf of modules which is a zero object is quasi-coherent: the empty family of sections
generates it, and the empty family of relations presents it. -/
private theorem isQuasicoherent_of_isZero {X : Scheme.{u}} {F : X.Modules} (hF : IsZero F) :
    F.IsQuasicoherent := by
  let G : F.GeneratingSections :=
    { I := PEmpty
      s := PEmpty.elim
      epi := hF.epi _ }
  have hfree : IsZero (SheafOfModules.free (R := X.ringCatSheaf) PEmpty) := by
    rw [IsZero.iff_id_eq_zero]
    exact Sigma.hom_ext _ _ fun n ↦ n.elim
  have : Mono G.π := hfree.mono _
  let Pres : F.Presentation :=
    { generators := G
      relations :=
        { I := PEmpty
          s := PEmpty.elim
          epi := (isZero_kernel_of_mono G.π).epi _ } }
  exact Pres.isQuasicoherent

/-- **The statement of Tag 0AVS as displayed is false, and this is the counterexample.** On an
integral locally Noetherian scheme, let `G` be a nonzero torsion-free quasi-coherent module and
take `F = 0` and `f = 0`. Then `F` is coherent and quasi-coherent, every stalk of `F` is the zero
module, whose depth along the maximal ideal is `⊤` by `Module.depth_eq_top_of_subsingleton` — the
convention Tag 00LI fixes, `depth_I(M) = ∞` when `IM = M` — so alternative (2) of Tag 0AVS holds
at every point, while `f` is not an isomorphism since `G` is not a zero object.

So the displayed hypotheses of Tag 0AVS do not imply its conclusion, and the clause on associated
points of alternative (2) of Tag 0AV8, the lemma the source's proof of Tag 0AVS reduces to, is
what rules this configuration out: the generic point of an integral scheme is associated to a
nonzero torsion-free module. That clause is the form in which
`isIso_of_stalk_isIso_or_depth_two_and_not_associated_of_isTorsionFree` carries Tag 0AVS. -/
theorem exists_counterexample_to_displayed_statement_of_tag_0AVS {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (G : X.Modules) [G.IsQuasicoherent]
    (_hG : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree G) (hG0 : ¬ IsZero G) :
    ∃ (F : X.Modules) (_ : F.IsQuasicoherent) (_ : F.IsCoherent) (f : F ⟶ G),
      (∀ x : X,
        let : Module (X.presheaf.stalk x)
            (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) F.val x
        IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f.val)) ∨
        (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)) ∧
      ¬ IsIso f := by
  have hcoh : (0 : X.Modules).IsCoherent :=
    let h := Stacks.SheafOfModules.isCoherent_of_isZero (isZero_zero (X.Modules))
    ⟨h.isFiniteType, h.kernel_isFiniteType⟩
  refine ⟨0, isQuasicoherent_of_isZero (isZero_zero _), hcoh, 0, fun x ↦ Or.inr ?_, ?_⟩
  · have : Subsingleton ↑(TopCat.Presheaf.stalk (C := Ab.{u}) (0 : X.Modules).val.presheaf x) :=
      subsingleton_stalk_of_isZero (isZero_zero _) x
    exact le_top.trans (Module.depth_eq_top_of_subsingleton _).ge
  · intro hiso
    exact hG0 (IsZero.of_iso (isZero_zero X.Modules)
      (asIso (0 : (0 : X.Modules) ⟶ G)).symm)

/-- The structure sheaf of an integral scheme is torsion free: on an affine open its sections are
the ring of functions there, acting on itself by multiplication, and a ring is torsion free over
itself. -/
private theorem isTorsionFree_unit {X : Scheme.{u}} [IsIntegral X] :
    Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree
      (SheafOfModules.unit X.ringCatSheaf) := by
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isQuasicoherent_unit
  refine (isTorsionFree_iff_forall_isAffineOpen _).mpr fun U _ ↦ ?_
  exact (inferInstance : Module.IsTorsionFree Γ(X, U) Γ(X, U))

/-- The structure sheaf of a scheme with a point is not a zero object: were it one, its sections
over `⊤` would form a subsingleton, so `1 = 0` there, hence `1 = 0` in the local ring at that
point, which is nontrivial. -/
private theorem not_isZero_unit {X : Scheme.{u}} (x : X) :
    ¬ IsZero (SheafOfModules.unit X.ringCatSheaf) := by
  intro h
  have h1 : IsZero ((PresheafOfModules.evaluation X.ringCatSheaf.obj (Opposite.op ⊤)).obj
      ((SheafOfModules.forget X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf))) :=
    Functor.map_isZero _ (Functor.map_isZero _ h)
  have hsub : Subsingleton Γ(X, (⊤ : X.Opens)) := ModuleCat.subsingleton_of_isZero h1
  have h10 : (1 : Γ(X, (⊤ : X.Opens))) = 0 := Subsingleton.elim _ _
  have hone : (1 : X.presheaf.stalk x) = 0 := by
    rw [← map_one (X.presheaf.germ ⊤ x trivial).hom, h10, map_zero]
  exact one_ne_zero hone

/-- **The counterexample of `exists_counterexample_to_displayed_statement_of_tag_0AVS` on a
concrete scheme.** Take `X = Spec ℤ`, which is integral and locally Noetherian, `G = 𝒪_X`, which
is quasi-coherent, torsion free and not a zero object, `F = 0`, which is coherent and
quasi-coherent, and `f = 0`. Then alternative (2) of Tag 0AVS as displayed holds at every point,
because every stalk of `F` is the zero module and the depth of the zero module is `⊤`, while `f`
is not an isomorphism. -/
theorem exists_counterexample_to_displayed_statement_of_tag_0AVS_specInt :
    ∃ (F : (Spec (CommRingCat.of ℤ)).Modules) (_ : F.IsQuasicoherent) (_ : F.IsCoherent)
      (f : F ⟶ SheafOfModules.unit (Spec (CommRingCat.of ℤ)).ringCatSheaf),
      (∀ x : (Spec (CommRingCat.of ℤ) : Scheme.{0}),
        let : Module ((Spec (CommRingCat.of ℤ)).presheaf.stalk x)
            (TopCat.Presheaf.stalk (C := Ab.{0}) F.val.presheaf x) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := (Spec (CommRingCat.of ℤ)).presheaf) F.val x
        IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
          ((PresheafOfModules.toPresheaf (Spec (CommRingCat.of ℤ)).ringCatSheaf.obj).map f.val)) ∨
        (2 : ℕ∞) ≤ Module.depth ((Spec (CommRingCat.of ℤ)).presheaf.stalk x)
          (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of ℤ)).presheaf.stalk x))
          (TopCat.Presheaf.stalk (C := Ab.{0}) F.val.presheaf x)) ∧
      ¬ IsIso f := by
  have : (SheafOfModules.unit (Spec (CommRingCat.of ℤ)).ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isQuasicoherent_unit
  exact exists_counterexample_to_displayed_statement_of_tag_0AVS _ isTorsionFree_unit
    (not_isZero_unit (genericPoint _))

end Counterexample


end AlgebraicGeometry
