module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.BaseIsoTransport
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcStandardReduction
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.SingletonFullness

/-!
# Effectivity of quasi-coherent descent data along a standard affine covering, reduced to one
morphism

`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/StandardAffineComparison.lean` reduces the
essential surjectivity half of Stacks 023S to effectivity along the **single** morphism
`Spec (∏ₖ A k) ⟶ Spec R` through which a standard family out of `Spec R` factors.  This file
carries that reduction over to an arbitrary affine base, and so turns the hypothesis `hstd` of
`Stacks.Descent.isStackFor_qcohPseudofunctor_of_isAffine` into the one-element statement
`Stacks.Descent.AffineSingletonEffective`, which is the exact counterpart of
`Stacks.Descent.AffineSingletonFullness` for the other half.

Two things have to be done, and neither is about modules.  The passage from a finite family to
the single morphism it factors through is the same construction as in
`Stacks.Descent.standardAffineFullness_of_affineSingletonFullness`, with fullness replaced by
essential surjectivity.  The passage from `T = Spec R` to an arbitrary affine `T` is
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/BaseIsoTransport.lean` applied at
`AlgebraicGeometry.Scheme.isoSpec`, together with the full faithfulness of `Spec` on affines,
which is what rewrites the transported family as a family of the form `Spec.map ρ`.

## Main definitions

* `Stacks.Descent.AffineSingletonEffective`: **the one-element case of the essential surjectivity
  half of Stacks 023S** — for a single morphism `Spec B ⟶ T` out of the spectrum of a ring whose
  presieve is an fpqc covering of an affine scheme, every descent datum of
  `Stacks.Descent.qcohPseudofunctor` is effective.
* `Stacks.Descent.AffineSingletonEffectiveSpec`: the same statement restricted to a base of the
  form `Spec R` and a morphism of the form `Spec.map φ`, which is the shape in which the
  algebraic side of the problem is stated.

## Main results

* `Stacks.Descent.affineSingletonEffective_of_specMap`: **the two are equivalent** — the
  restricted form implies the general one.  This is the base-isomorphism transport.
* `Stacks.Descent.standardAffineEffective_of_affineSingletonEffective`: the essential
  surjectivity half of Stacks 023S for a standard covering follows from its one-element case.
* `Stacks.Descent.isEquivalence_qcohToDescentData_standard_of_affineSingletonEffective`: hence,
  under the fpqc prestack condition, the hypothesis `hstd` of
  `Stacks.Descent.isStackFor_qcohPseudofunctor_of_isAffine` follows from
  `Stacks.Descent.AffineSingletonEffective`.
* `Stacks.Descent.isStackFor_qcohPseudofunctor_of_isAffine_of_affineSingletonEffective`: **the
  fpqc stack condition for quasi-coherent modules over an affine base, from the two one-element
  hypotheses `Stacks.Descent.AffineSingletonFullness` and
  `Stacks.Descent.AffineSingletonEffective` alone** — in particular with the fpqc prestack
  condition no longer a hypothesis, since
  `Stacks.Descent.isPrestack_qcohPseudofunctor_fpqc_of_standard` derives it from the first of the
  two.  Passing from an affine base to an arbitrary one is the locality of the stack condition on
  the base, which is recorded as absent in
  `StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/FpqcStandardReduction.lean` and is not
  touched here.

## Implementation notes

`Stacks.Descent.essSurj_toDescentData_of_sieve_eq` is the essential-surjectivity counterpart of
`Stacks.Descent.full_toDescentData_of_sieve_eq`; Mathlib has the `Iff` for being an
equivalence and for full faithfulness, but not for essential surjectivity alone, and the
reindexing of the index type along `ULift.down` needs exactly that form.

The index type of `Stacks.Descent.AffineSingletonEffective` is pinned at `PUnit.{1}`, i.e.
`Unit`, because that is the index type of the hypothesis of
`Stacks.Descent.essSurj_qcohToDescentData_of_essSurj_single`.

No stacks attribute is placed in this file: both conclusions remain conditional on the two
one-element hypotheses.

## References

* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe t w v u

namespace Stacks.Descent

section Abstract

variable {C : Type u} [Category.{v} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, u}}

/-- **Essential surjectivity of the canonical descent functor depends only on the sieve the
family generates.**  The counterpart of `Stacks.Descent.full_toDescentData_of_sieve_eq`. -/
theorem essSurj_toDescentData_of_sieve_eq {ι : Type t} {T : C} {V : ι → C} (f : ∀ i, V i ⟶ T)
    {ι' : Type w} {V' : ι' → C} (f' : ∀ j, V' j ⟶ T)
    (h : Sieve.ofArrows _ f = Sieve.ofArrows _ f') [(F.toDescentData f).EssSurj] :
    (F.toDescentData f').EssSurj := by
  obtain ⟨e, ⟨i⟩⟩ := Pseudofunctor.DescentData.exists_equivalence_of_sieve_eq F f f' h
  have : e.functor.EssSurj := inferInstance
  exact Functor.essSurj_of_iso i

end Abstract

section Statements

/-- **The one-element case of the essential surjectivity half of Stacks 023S**: every descent
datum of `Stacks.Descent.qcohPseudofunctor` for a *single* morphism from the spectrum of a ring
which is an fpqc covering of an affine scheme is effective.

This is the exact counterpart of `Stacks.Descent.AffineSingletonFullness` for the other half of
Stacks 023S. -/
def AffineSingletonEffective : Prop :=
  ∀ (T : Scheme.{u}) (_ : IsAffine T) (B : CommRingCat.{u}) (b : Spec B ⟶ T)
    (_ : Presieve.ofArrows (fun _ : Unit ↦ Spec B) (fun _ ↦ b) ∈ Scheme.fpqcPrecoverage.{u} T),
    (qcohPseudofunctor.toDescentData (fun _ : Unit ↦ b)).EssSurj

/-- `Stacks.Descent.AffineSingletonEffective` with the base of the form `Spec R` and the morphism
of the form `Spec.map φ`.  This is the shape in which the problem is algebraic: `φ` is a
faithfully flat ring map. -/
def AffineSingletonEffectiveSpec : Prop :=
  ∀ (R B : CommRingCat.{u}) (φ : R ⟶ B)
    (_ : Presieve.ofArrows (fun _ : Unit ↦ Spec B) (fun _ ↦ Spec.map φ) ∈
      Scheme.fpqcPrecoverage.{u} (Spec R)),
    (qcohPseudofunctor.toDescentData (fun _ : Unit ↦ Spec.map φ)).EssSurj

end Statements

section BaseTransport

/-- A flat surjective morphism from an affine scheme, as a one-element family, is an fpqc
covering. -/
private theorem ofArrows_unit_mem_fpqcPrecoverage {B : CommRingCat.{u}} {T : Scheme.{u}}
    [IsAffine T] (b : Spec B ⟶ T) [Flat b] [Surjective b] :
    Presieve.ofArrows (fun _ : Unit ↦ Spec B) (fun _ ↦ b) ∈ Scheme.fpqcPrecoverage.{u} T := by
  rw [Presieve.ofArrows_pUnit]
  exact b.singleton_mem_fpqcPrecoverage

/-- **The base of a one-element fpqc covering of an affine scheme may be taken to be
`Spec Γ(T, ⊤)`.**  Transporting along `AlgebraicGeometry.Scheme.isoSpec` replaces `T` by
`Spec Γ(T, ⊤)` and `b` by a morphism of affine spectra, which is `Spec.map` of a ring map by the
full faithfulness of `Spec`. -/
theorem affineSingletonEffective_of_specMap (h : AffineSingletonEffectiveSpec.{u}) :
    AffineSingletonEffective.{u} := by
  intro T hT B b hmem
  have := hT
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (b ≫ T.isoSpec.hom)
  have hmem' : Presieve.ofArrows (fun _ : Unit ↦ Spec B) (fun _ ↦ Spec.map φ) ∈
      Scheme.fpqcPrecoverage.{u} (Spec Γ(T, ⊤)) := by
    obtain ⟨hsurj, hflat⟩ := (Scheme.ofArrows_mem_precoverage_iff _).1
      (Scheme.propQCPrecoverage_le_precoverage (P := @Flat) _ hmem)
    have hflatb : Flat b := hflat ()
    have hsurjb : Surjective b := by
      refine ⟨fun t ↦ ?_⟩
      obtain ⟨_, y, hy⟩ := hsurj t
      exact ⟨y, hy⟩
    have : Flat (Spec.map φ) := hφ ▸ inferInstance
    have : Surjective (Spec.map φ) := hφ ▸ inferInstance
    exact ofArrows_unit_mem_fpqcPrecoverage _
  have hess := h Γ(T, ⊤) B φ hmem'
  exact essSurj_toDescentData_of_baseIso qcohPseudofunctor T.isoSpec
    (f := fun _ : Unit ↦ Spec.map φ) (f' := fun _ : Unit ↦ b) (fun _ ↦ hφ.symm) hess

end BaseTransport

section StandardAffine

variable {T : Scheme.{u}}

/-- **The essential surjectivity half of Stacks 023S for a standard covering follows from its
one-element case.**  The family `Spec (A k) ⟶ T` is replaced by the single morphism
`Spec (∏ₖ A k) ⟶ T` through which it factors, exactly as in
`Stacks.Descent.standardAffineFullness_of_affineSingletonFullness`: the factorisations are the
spectra of the projections of the product, which are open immersions covering
`Spec (∏ₖ A k)` by `Stacks.Descent.iSup_opensRange_specMap_piComponent`, and the single morphism
comes from `AlgebraicGeometry.sigmaSpec`, an isomorphism because the index type is finite.

Essential surjectivity passes from the single morphism to the family by
`Stacks.Descent.essSurj_qcohToDescentData_of_essSurj_single`, and the reindexing of the index
type along `ULift.down` changes neither the presieve nor therefore the conclusion, by
`Stacks.Descent.presieve_ofArrows_comp_of_surjective` and
`Stacks.Descent.essSurj_toDescentData_of_sieve_eq`. -/
theorem standardAffineEffective_of_affineSingletonEffective (h : AffineSingletonEffective.{u})
    (hT : IsAffine T) (K : Type) (hK : Finite K) (A : K → CommRingCat.{u})
    (g : ∀ k, Spec (A k) ⟶ T)
    (hmem : Presieve.ofArrows (fun k ↦ Spec (A k)) g ∈ Scheme.fpqcPrecoverage.{u} T) :
    (qcohPseudofunctor.toDescentData g).EssSurj := by
  have := hT
  have := hK
  have hpre : Presieve.ofArrows (fun k' : ULift.{u} K ↦ Spec (A k'.down))
      (fun k' ↦ g k'.down) = Presieve.ofArrows (fun k ↦ Spec (A k)) g :=
    presieve_ofArrows_comp_of_surjective g ULift.down ULift.down_surjective
  have hmem' : Presieve.ofArrows (fun k' : ULift.{u} K ↦ Spec (A k'.down))
      (fun k' ↦ g k'.down) ∈ Scheme.fpqcPrecoverage.{u} T := hpre ▸ hmem
  obtain ⟨hsurj', hflat'⟩ := (Scheme.ofArrows_mem_precoverage_iff _).1
    (Scheme.propQCPrecoverage_le_precoverage (P := @Flat) _ hmem')
  set A' : ULift.{u} K → CommRingCat.{u} := fun k' ↦ A k'.down with hA'
  set B : CommRingCat.{u} := CommRingCat.of (∀ k', (A' k' : Type u)) with hB
  set b : Spec B ⟶ T := inv (sigmaSpec A') ≫ Sigma.desc (fun k' ↦ g k'.down) with hbdef
  have hb : ∀ k', Spec.map (piComponent A' k') ≫ b = g k'.down := fun k' ↦ by
    rw [hbdef, ← ι_sigmaSpec A' k', Category.assoc, IsIso.hom_inv_id_assoc, Sigma.ι_comp_desc]
  have hloc : IsZariskiLocalAtSource @Flat :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
  have hriso : MorphismProperty.RespectsIso @Flat :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hflatb : Flat b := by
    refine IsZariskiLocalAtSource.of_iSup_eq_top
      (fun k' ↦ (Spec.map (piComponent A' k')).opensRange)
      (iSup_opensRange_specMap_piComponent A') fun k' ↦ ?_
    rw [← IsOpenImmersion.isoOfRangeEq_inv_fac (Spec.map (piComponent A' k'))
      (Scheme.Opens.ι (Spec.map (piComponent A' k')).opensRange)
      (by rw [Scheme.Opens.range_ι, Scheme.Hom.coe_opensRange]), Category.assoc,
      MorphismProperty.cancel_left_of_respectsIso (P := @Flat) _ _, hb k']
    exact hflat' k'
  have hsurjb : Surjective b := by
    refine ⟨fun t ↦ ?_⟩
    obtain ⟨k', y, hy⟩ := hsurj' t
    refine ⟨(Spec.map (piComponent A' k')).base y, ?_⟩
    rw [← Scheme.Hom.comp_apply, hb k']
    exact hy
  have hmemb : Presieve.ofArrows (fun _ : Unit ↦ Spec B) (fun _ ↦ b) ∈
      Scheme.fpqcPrecoverage.{u} T := by
    exact ofArrows_unit_mem_fpqcPrecoverage b
  have hess : (qcohPseudofunctor.toDescentData (fun k' : ULift.{u} K ↦ g k'.down)).EssSurj :=
    essSurj_qcohToDescentData_of_essSurj_single hb
      (iSup_opensRange_specMap_piComponent A') (h T ‹_› B b hmemb)
  exact essSurj_toDescentData_of_sieve_eq _ g (congrArg Sieve.generate hpre)

/-- **The hypothesis `hstd` of `Stacks.Descent.isStackFor_qcohPseudofunctor_of_isAffine`, from the
one-element case.**  Full faithfulness of the canonical descent functor comes from the fpqc
prestack condition, and essential surjectivity from
`Stacks.Descent.standardAffineEffective_of_affineSingletonEffective`. -/
theorem isEquivalence_qcohToDescentData_standard_of_affineSingletonEffective
    [qcohPseudofunctor.{u}.IsPrestack Scheme.fpqcTopology.{u}]
    (h : AffineSingletonEffective.{u}) (hT : IsAffine T) (K : Type) (hK : Finite K)
    (A : K → CommRingCat.{u}) (g : ∀ k, Spec (A k) ⟶ T)
    (hmem : Presieve.ofArrows (fun k ↦ Spec (A k)) g ∈ Scheme.fpqcPrecoverage.{u} T) :
    (qcohPseudofunctor.toDescentData g).IsEquivalence := by
  have ff := Pseudofunctor.fullyFaithfulToDescentData (F := qcohPseudofunctor)
    (J := Scheme.fpqcTopology.{u}) (f := g) (Precoverage.generate_mem_toGrothendieck hmem)
  have := ff.full
  have := ff.faithful
  have := standardAffineEffective_of_affineSingletonEffective h hT K hK A g hmem
  exact { }

/-- **The fpqc stack condition for quasi-coherent modules over an affine base, from the two
one-element hypotheses.**  This is
`Stacks.Descent.isStackFor_qcohPseudofunctor_of_isAffine` with its hypothesis `hstd` supplied. -/
theorem isStackFor_qcohPseudofunctor_of_isAffine_of_affineSingletonEffective
    (hfull : AffineSingletonFullness.{u}) (heff : AffineSingletonEffective.{u}) [IsAffine T]
    (R : Presieve T) (hR : R ∈ Scheme.fpqcPrecoverage.{u} T) :
    qcohPseudofunctor.IsStackFor R :=
  have : qcohPseudofunctor.{u}.IsPrestack Scheme.fpqcTopology.{u} :=
    isPrestack_qcohPseudofunctor_fpqc_of_standard
      (standardAffineFullness_of_affineSingletonFullness hfull)
  isStackFor_qcohPseudofunctor_of_isAffine
    (fun _ hT' K hK A g hmem ↦
      isEquivalence_qcohToDescentData_standard_of_affineSingletonEffective heff hT' K hK A g hmem)
    R hR

end StandardAffine

end Stacks.Descent

end

end
