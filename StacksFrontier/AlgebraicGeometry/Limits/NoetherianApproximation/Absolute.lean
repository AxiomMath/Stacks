module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.Induction
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic

/-!
# Absolute Noetherian approximation

A quasi-compact and quasi-separated scheme is the inverse limit of a directed system of schemes
of finite type over the integers whose transition morphisms are affine. This is the absolute
form of Noetherian approximation; the relative form, which approximates the scheme compatibly
with a prescribed system on a quasi-compact open subscheme, is
`AlgebraicGeometry.exists_finiteTypeApproximation`. The absolute form is the relative one applied
to the empty open subscheme, approximated by the one-stage system consisting of the empty scheme
itself.

A scheme of finite type over the integers is Noetherian; this is recorded here because it is
what makes the stages of such an approximation Noetherian, which is the point of the
approximation.

## Main results

* `AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType_terminalFrom`: a scheme of finite type
  over the terminal scheme is Noetherian.
* `AlgebraicGeometry.exists_isLimit_finiteType`: absolute Noetherian approximation.
* `AlgebraicGeometry.exists_isLimit_finiteType_isNoetherian`: the same approximation with its
  stages recorded as Noetherian schemes, hence quasi-compact and quasi-separated.

## Implementation notes

Finite type over the integers is expressed, following Mathlib's convention, as
`AlgebraicGeometry.LocallyOfFiniteType` together with `AlgebraicGeometry.QuasiCompact` for the
structural morphism to the terminal scheme; the terminal scheme of `Scheme.{u}` is the spectrum
of a universe lift of `ℤ`, by `AlgebraicGeometry.specULiftZIsTerminal`.

A directed inverse system indexed by a preorder `I` is presented as a functor out of `Iᵒᵖ`, which
is the shape the descent results for such limits take; the relative form produces a functor out
of the order dual `Iᵒᵈ`, and the two are exchanged by
`CategoryTheory.orderDualEquivalence`. The limit is presented as a cone whose vertex is the given
scheme rather than as an abstract limit object, so that the legs of the cone are available as
morphisms out of it.

## References

* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A scheme of finite type over the terminal scheme is Noetherian: the terminal scheme is the
spectrum of a universe lift of `ℤ`, which is Noetherian, and both finite type and
quasi-compactness of the structural morphism pass to the source. -/
@[ega "IV 1.3.3" "special case"]
public lemma isNoetherian_of_locallyOfFiniteType_terminalFrom (Y : Scheme.{u})
    (hft : LocallyOfFiniteType (terminal.from Y))
    (hqc : QuasiCompact (terminal.from Y)) : IsNoetherian Y := by
  let e : (⊤_ Scheme.{u}) ≅ Spec (.of (ULift.{u} ℤ)) :=
    terminalIsTerminal.uniqueUpToIso AlgebraicGeometry.specULiftZIsTerminal
  have : LocallyOfFiniteType (terminal.from Y) := hft
  have : QuasiCompact (terminal.from Y) := hqc
  have : LocallyOfFiniteType (terminal.from Y ≫ e.hom) := inferInstance
  have : QuasiCompact (terminal.from Y ≫ e.hom) := inferInstance
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  exact isNoetherian_of_locallyOfFiniteType (terminal.from Y ≫ e.hom)

/-- **Stacks Project, Tag 01ZA.** A quasi-compact and quasi-separated scheme is the inverse
limit of a directed system of schemes of finite type over the integers with affine transition
morphisms. -/
@[stacks 01ZA]
public theorem exists_isLimit_finiteType (S : Scheme.{u}) [CompactSpace S]
    [QuasiSeparatedSpace S] :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D),
      (∀ {i j : Iᵒᵖ} (v : i ⟶ j), IsAffineHom (D.map v)) ∧
      (∀ i, LocallyOfFiniteType (terminal.from (D.obj i))) ∧
      (∀ i, QuasiCompact (terminal.from (D.obj i))) ∧
      Nonempty (IsLimit c) ∧ c.pt = S := by
  let E : Scheme.{u} := ((⊥ : S.Opens) : Scheme.{u})
  have : IsEmpty E := Subtype.isEmpty_false
  let D₀ : PUnit.{u + 1}ᵒᵈ ⥤ Scheme.{u} := (Functor.const _).obj E
  have : ∀ {i j : PUnit.{u + 1}ᵒᵈ} (v : i ⟶ j), IsAffineHom (D₀.map v) := fun _ =>
    (inferInstance : IsAffineHom (𝟙 E))
  have : ∀ i, LocallyOfFiniteType (terminal.from (D₀.obj i)) := fun _ =>
    (inferInstance : LocallyOfFiniteType (terminal.from E))
  have : ∀ i, QuasiCompact (terminal.from (D₀.obj i)) := fun _ =>
    (inferInstance : QuasiCompact (terminal.from E))
  let p : (Functor.const PUnit.{u + 1}ᵒᵈ).obj E ⟶ D₀ := { app := fun _ => 𝟙 E }
  have hp : IsLimit (Cone.mk E p) := by
    refine { lift := fun s => s.π.app (OrderDual.toDual PUnit.unit), fac := ?_, uniq := ?_ }
    · intro s j
      obtain rfl : j = OrderDual.toDual PUnit.unit := rfl
      exact Category.comp_id _
    · intro s m hm
      simpa [p] using hm (OrderDual.toDual PUnit.unit)
  have : CompactSpace ((⊥ : S.Opens) : Scheme.{u}) := inferInstanceAs (CompactSpace E)
  obtain ⟨A⟩ := exists_finiteTypeApproximation D₀ S ⊥ p hp
  let _ : Preorder A.indexType := A.indexPreorder
  let e : A.indexTypeᵒᵖ ≌ A.indexTypeᵒᵈ := (orderDualEquivalence A.indexType).symm
  refine ⟨A.indexType, A.indexPreorder, A.indexNonempty, A.indexDirected,
    e.functor ⋙ A.ambient, (Cone.mk S A.ambientCone).whisker e.functor,
    fun v => A.transition_affine _, fun i => A.locallyOfFiniteType _,
    fun i => A.quasiCompact _, ⟨A.ambientCone_isLimit.whiskerEquivalence e⟩, rfl⟩

/-- **Absolute Noetherian approximation, with the stages recorded as Noetherian schemes.** A
quasi-compact and quasi-separated scheme is the inverse limit of a directed system of schemes of
finite type over the integers with affine transition morphisms, every stage of which is a
Noetherian scheme and hence quasi-compact and quasi-separated.

Finite type over the integers already makes a stage Noetherian, by
`AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType_terminalFrom`, and a Noetherian scheme has
a Noetherian underlying space, whose every pair of quasi-compact opens meets in a quasi-compact
open. The quasi-separatedness of the stages is not recorded by
`AlgebraicGeometry.exists_isLimit_finiteType`, and it is what an approximation of an algebraic
space by stages quasi-separated and of finite type over `Spec ℤ` asks of the stages that happen
to be schemes: it is clause (2) of Stacks 07SU, and a field of
`AlgebraicGeometry.Space.NoetherianApproximation`, which the bare finite-type clauses do not
supply.

No `@[stacks 01ZA]` attribute is attached: Stacks 01ZA is registered on
`AlgebraicGeometry.exists_isLimit_finiteType` above, whose conclusion is the tag's, and the
clauses added here are not part of the tag's statement. -/
@[ega "IV 8.13.5" "partial", sga "3 VIB 10.10" "partial", sga "3 XI 4.3" "Base approximation"]
public theorem exists_isLimit_finiteType_isNoetherian (S : Scheme.{u}) [CompactSpace S]
    [QuasiSeparatedSpace S] :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D),
      (∀ {i j : Iᵒᵖ} (v : i ⟶ j), IsAffineHom (D.map v)) ∧
      (∀ i, LocallyOfFiniteType (terminal.from (D.obj i))) ∧
      (∀ i, QuasiCompact (terminal.from (D.obj i))) ∧
      (∀ i, IsNoetherian (D.obj i)) ∧
      (∀ i, CompactSpace (D.obj i)) ∧
      (∀ i, QuasiSeparatedSpace (D.obj i)) ∧
      Nonempty (IsLimit c) ∧ c.pt = S := by
  obtain ⟨I, hI, hne, hdir, D, c, haffine, hft, hqc, hlim, hpt⟩ := exists_isLimit_finiteType S
  have hnoetherian : ∀ i, IsNoetherian (D.obj i) := fun i =>
    isNoetherian_of_locallyOfFiniteType_terminalFrom (D.obj i) (hft i) (hqc i)
  refine ⟨I, hI, hne, hdir, D, c, haffine, hft, hqc, hnoetherian, fun i => ?_, fun i => ?_,
    hlim, hpt⟩
  · have := hnoetherian i
    infer_instance
  · have := hnoetherian i
    have : TopologicalSpace.NoetherianSpace (D.obj i) := IsNoetherian.noetherianSpace
    infer_instance

end AlgebraicGeometry
