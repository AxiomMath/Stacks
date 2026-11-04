module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RelativeDiagonal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafCondition
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical

/-!
# The uniqueness half of the fpqc sheaf property of a formal algebraic space

Let `S` be a scheme contained in a big fppf site `B` and let `X` be a formal algebraic space
over `S`, that is, an fppf sheaf on the big fppf site of `S` satisfying **Stacks 0AIM**.
**Stacks 0AQD** says that `X` satisfies the sheaf property for the fpqc topology of that site.
The tag is proved in `StacksFrontier.AlgebraicGeometry.FormalSpace.FpqcSheafGlueing`, as
`AlgebraicGeometry.FormalSpace.isSheaf_fpqc`. This file contains the first paragraph of the
source's proof, the uniqueness half, and two general facts the rest of the proof uses.

*Uniqueness.* Two sections of `X` over an object `T` of the site which agree on the members of
an fpqc covering family of `T` are equal. The equaliser of the two sections is the base change
of the diagonal `X ⟶ X ⨯ X` along the morphism they define to `X ⨯ X`; the diagonal of a formal
algebraic space is representable (**Stacks 0AIP**,
`AlgebraicGeometry.FormalSpace.relativelyRepresentable_diag_of_isFormalAlgebraicSpace`) and a
split monomorphism, so the equaliser is an object `E` of the site and `E ⟶ T` is a
monomorphism. Every member of the covering family factors through `E`, so the base change of
`E ⟶ T` along it is a monomorphism with a section, hence an isomorphism; being an isomorphism
is fpqc local on the target, so `E ⟶ T` is an isomorphism and the two sections coincide (the
source's appeal to Descent, Lemma 02L4 is replaced by Mathlib's
`CategoryTheory.MorphismProperty.isomorphisms.IsLocalAtTarget`, as in the corresponding
argument for algebraic spaces, `AlgebraicGeometry.IsAlgebraicSpace.isSeparatedFor_fpqc`).

## Main results

* `AlgebraicGeometry.FormalSpace.isSheaf_fpqc_of_isSheafFor`: the fpqc sheaf condition is the
  sheaf condition for every fpqc covering presieve.
* `AlgebraicGeometry.FormalSpace.isSeparatedFor_fpqc`: the uniqueness half, for an fppf sheaf
  whose diagonal is representable by objects of the site.
* `AlgebraicGeometry.FormalSpace.isSheafFor_of_isSheafFor_pullback`: the sheaf condition for a
  sieve is fppf local on the base.
* `AlgebraicGeometry.FormalSpace.isSeparatedFor_fpqc_of_isFormalAlgebraicSpace`: the uniqueness
  half for an arbitrary formal algebraic space.

## References

* [Stacks Project, Tag 0AQD](https://stacks.math.columbia.edu/tag/0AQD)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 02L4](https://stacks.math.columbia.edu/tag/02L4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An fppf sheaf on the big fppf site of `S` is a sheaf for the fpqc topology as soon as it
satisfies the sheaf condition for every fpqc covering presieve.

This is the large-valued counterpart of `AlgebraicGeometry.isSheaf_fpqc_of_isSheafFor`: the
sheaves carrying formal algebraic spaces take values in `Type (u + 1)` rather than in the value
universe `Type u` of the site. -/
theorem isSheaf_fpqc_of_isSheafFor {X : FppfSheaf B S hS}
    (h : ∀ ⦃T : BigFppfOver B S hS⦄ (R : Presieve T),
      R ∈ Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS) T →
      Presieve.IsSheafFor X.obj R) :
    Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck) X.obj := by
  rw [isSheaf_iff_isSheaf_of_type,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  exact h

/-- **The uniqueness half of Stacks 0AQD**, which is the first paragraph of the source's proof.
Two sections of an fppf sheaf `X` on the big fppf site of `S` over an object `T` of the site
which agree on the members of an fpqc covering presieve of `T` are equal, provided the diagonal
`X ⟶ X ⨯ X` is representable by objects of the site.

Representability of the diagonal is the hypothesis `hdiag`; for a formal algebraic space it is
the representability assertion of **Stacks 0AIP**. No other property of `X` is used.

For a formal algebraic space `hdiag` is supplied by
`AlgebraicGeometry.FormalSpace.relativelyRepresentable_diag_of_isFormalAlgebraicSpace`, in
`AlgebraicGeometry.FormalSpace.isSeparatedFor_fpqc_of_isFormalAlgebraicSpace` below. -/
theorem isSeparatedFor_fpqc {X : FppfSheaf B S hS}
    (hdiag : (fppfYoneda B S hS).relativelyRepresentable (diag X))
    {T : BigFppfOver B S hS} {R : Presieve T}
    (hR : R ∈ Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS) T) :
    Presieve.IsSeparatedFor X.obj R := by
  intro x t₁ t₂ h₁ h₂
  -- Pass from sections to morphisms out of a sheafified representable.
  set a : (fppfYoneda B S hS).obj T ⟶ X :=
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm t₁ with ha
  set b : (fppfYoneda B S hS).obj T ⟶ X :=
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm t₂ with hb
  have key : ∀ ⦃Z : BigFppfOver B S hS⦄ (f : Z ⟶ T), R f →
      (fppfYoneda B S hS).map f ≫ a = (fppfYoneda B S hS).map f ≫ b := by
    intro Z f hf
    apply (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).injective
    rw [Sheaf.sectionEquiv_map_comp, Sheaf.sectionEquiv_map_comp, ha, hb,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply, h₁ f hf, h₂ f hf]
  -- The equaliser of the two sections is represented by `E`.
  set E := hdiag.pullback (prod.lift a b) with hE
  set p : E ⟶ T := hdiag.snd (prod.lift a b) with hp
  have hpb := hdiag.isPullback (prod.lift a b)
  -- The diagonal is a split monomorphism, hence so is `p`.
  have : IsSplitMono (diag X) := IsSplitMono.mk' ⟨prod.fst, by simp⟩
  have : Mono ((fppfYoneda B S hS).map p) := hpb.mono_snd_of_mono
  have hmono : Mono p := (fppfYoneda B S hS).mono_of_mono_map this
  -- Every member of the covering family factors through `E`.
  have hfac : ∀ ⦃Z : BigFppfOver B S hS⦄ (f : Z ⟶ T), R f → ∃ l : Z ⟶ E, l ≫ p = f := by
    intro Z f hf
    refine ⟨hdiag.lift ((fppfYoneda B S hS).map f ≫ a) f ?_, hdiag.lift_snd _ _ _⟩
    rw [diag, prod.comp_lift, prod.comp_lift, key f hf, Category.comp_id]
  -- `p` becomes an isomorphism after base change along the covering family.
  have hbc : ∀ ⦃Z : BigFppfOver B S hS⦄ (v : Z ⟶ T), R v →
      MorphismProperty.isomorphisms Scheme.{u}
        (pullback.snd ((BigFppfOver.toScheme B S hS).map p)
          ((BigFppfOver.toScheme B S hS).map v)) := by
    intro Z v hv
    obtain ⟨l, hl⟩ := hfac v hv
    have : Mono (pullback.snd p v) := (IsPullback.of_hasPullback p v).mono_snd_of_mono
    have hsec : pullback.lift l (𝟙 Z) (by simp [hl]) ≫ pullback.snd p v = 𝟙 Z :=
      pullback.lift_snd _ _ _
    have : IsSplitEpi (pullback.snd p v) := IsSplitEpi.mk' ⟨_, hsec⟩
    have : IsIso (pullback.snd p v) := isIso_of_mono_of_isSplitEpi _
    have hcomp : IsIso (pullbackComparison (BigFppfOver.toScheme B S hS) p v ≫
        pullback.snd ((BigFppfOver.toScheme B S hS).map p)
          ((BigFppfOver.toScheme B S hS).map v)) := by
      rw [pullbackComparison_comp_snd]
      infer_instance
    exact IsIso.of_isIso_comp_left
      (pullbackComparison (BigFppfOver.toScheme B S hS) p v) _
  have hiso : MorphismProperty.isomorphisms Scheme.{u}
      ((BigFppfOver.toScheme B S hS).map p) := by
    refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
      (K := Scheme.fpqcPrecoverage) hR ?_
    intro U g _ hg
    obtain ⟨hv⟩ := hg
    exact hbc _ hv
  -- Hence `p` is an isomorphism, since the canonical functor to schemes reflects them.
  have : IsIso ((BigFppfOver.toScheme B S hS).map p) := hiso
  have : IsIso (B.inclusion.map ((BigFppfOver.forget B S hS).map p)) := this
  have : IsIso ((BigFppfOver.forget B S hS).map p) := isIso_of_reflects_iso _ B.inclusion
  have : IsIso p := isIso_of_reflects_iso _ (Over.forget (B.obj hS))
  have : IsIso ((fppfYoneda B S hS).map p) := inferInstance
  -- Therefore the two sections coincide.
  have hab : prod.lift a b =
      (inv ((fppfYoneda B S hS).map p) ≫ hdiag.fst (prod.lift a b)) ≫ diag X := by
    rw [Category.assoc, hpb.w, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have hfst := congrArg (fun φ ↦ φ ≫ (prod.fst : X ⨯ X ⟶ X)) hab
  have hsnd := congrArg (fun φ ↦ φ ≫ (prod.snd : X ⨯ X ⟶ X)) hab
  simp only [prod.lift_fst, prod.lift_snd, Category.assoc, diag] at hfst hsnd
  exact (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm.injective
    (hfst.trans hsnd.symm)

/-- The uniqueness half of **Stacks 0AQD** for a base change of an fpqc covering sieve: an fppf
sheaf with representable diagonal is separated for the pullback, along any morphism of the site,
of the sieve generated by an fpqc covering presieve.

The pullback of that sieve is generated by the pullback family, which is again an fpqc covering
presieve because the fpqc precoverage is stable under base change, so this is
`AlgebraicGeometry.FormalSpace.isSeparatedFor_fpqc` again. -/
theorem isSeparatedFor_fpqc_pullback {X : FppfSheaf B S hS}
    (hdiag : (fppfYoneda B S hS).relativelyRepresentable (diag X))
    {T : BigFppfOver B S hS} {R : Presieve T}
    (hR : R ∈ Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS) T)
    {Y : BigFppfOver B S hS} (f : Y ⟶ T) :
    Presieve.IsSeparatedFor X.obj ((Sieve.generate R).pullback f : Presieve Y) := by
  rw [← Sieve.pullbackArrows_comm, ← Presieve.isSeparatedFor_iff_generate]
  exact isSeparatedFor_fpqc hdiag (Precoverage.pullbackArrows_mem f hR)

/-- **The sheaf condition for a sieve is local on the base for the fppf topology.** Let `X` be an
fppf sheaf on the big fppf site of `S`, let `𝒮` be a sieve on an object `T` of the site, and let
`W` be an fppf covering sieve of `T`. If `X` satisfies the sheaf condition for the pullback of
`𝒮` along every arrow of `W`, then it satisfies it for `𝒮`.

This is the last step of the proof of **Stacks 0AQD**: a section of `X` produced only étale
locally on `T` glues to a section over `T`, because `X` is an étale — indeed fppf — sheaf. It is
Mathlib's `CategoryTheory.Presieve.isSheafFor_trans` fed by the sheaf condition of `X` for the
covering sieve `W` and for its pullbacks, the latter being covering sieves as well. -/
theorem isSheafFor_of_isSheafFor_pullback {X : FppfSheaf B S hS}
    {T : BigFppfOver B S hS} (𝒮 : Sieve T) {W : Sieve T}
    (hW : W ∈ BigFppfOver.topology B S hS T)
    (hloc : ∀ ⦃Y : BigFppfOver B S hS⦄ ⦃f : Y ⟶ T⦄, W f →
      Presieve.IsSheafFor X.obj (𝒮.pullback f : Presieve Y)) :
    Presieve.IsSheafFor X.obj (𝒮 : Presieve T) := by
  have hX : Presieve.IsSheaf (BigFppfOver.topology B S hS) X.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).1 X.property
  refine Presieve.isSheafFor_trans X.obj W 𝒮 (hX W hW) (fun {Y} {f} _ ↦ ?_) hloc
  exact (hX _ ((BigFppfOver.topology B S hS).pullback_stable f hW)).isSeparatedFor

/-! ### The uniqueness half for a formal algebraic space -/

/-- **The uniqueness half of Stacks 0AQD, for an arbitrary formal algebraic space.** Two
sections of a formal algebraic space over an object `T` of the big fppf site which agree on the
members of an fpqc covering presieve of `T` are equal.

Representability of the diagonal, which `AlgebraicGeometry.FormalSpace.isSeparatedFor_fpqc`
takes as the hypothesis `hdiag`, is the library's **Stacks 0AIP** for an arbitrary formal
algebraic space,
`AlgebraicGeometry.FormalSpace.relativelyRepresentable_diag_of_isFormalAlgebraicSpace`.
The tag itself is on `AlgebraicGeometry.FormalSpace.isSheaf_fpqc`. -/
theorem isSeparatedFor_fpqc_of_isFormalAlgebraicSpace {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) {T : BigFppfOver B S hS} {R : Presieve T}
    (hR : R ∈ Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS) T) :
    Presieve.IsSeparatedFor X.obj R :=
  isSeparatedFor_fpqc (relativelyRepresentable_diag_of_isFormalAlgebraicSpace B S hS hX) hR

end AlgebraicGeometry.FormalSpace

end
