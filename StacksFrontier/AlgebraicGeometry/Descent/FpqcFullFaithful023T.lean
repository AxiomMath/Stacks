module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcEffective023T
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcPrestackReduction
public import StacksFrontier.CategoryTheory.Sites.Descent.FullOfRefinement

/-!
# The full faithfulness clause of fpqc descent for quasi-coherent modules, over any base

Stacks 023T asserts, for an fpqc covering family `f i : X i ⟶ S` of an arbitrary scheme, that the
canonical descent functor of Stacks 023D on quasi-coherent modules is **fully faithful** and that
every quasi-coherent descent datum is **effective**.  The faithful half of the first clause is
`Stacks.Descent.faithful_canonicalDescentFunctor_fpqc`.  This file reduces full faithfulness,
over an arbitrary base and for an arbitrary fpqc covering family, to a single statement about one
standard fpqc covering of one affine scheme:

`Stacks.Descent.StandardAffineFullness`, the fullness half of Stacks 023S.

This is a strictly smaller case of the conclusion: the conclusion speaks about an arbitrary scheme
`S`, about covering families of arbitrary index type, and about members which need not be affine.

## Main results

* `Stacks.Descent.StandardAffineFullness`: the hypothesis, namely fullness of
  `CategoryTheory.Pseudofunctor.toDescentData` for `Stacks.Descent.qcohPseudofunctor` along a
  finite family of morphisms from spectra of rings which is an fpqc covering of an affine scheme.
* `Stacks.Descent.full_qcohToDescentData_of_isAffine`: **over an affine base the standard case
  implies the general one.**  Under the hypothesis, `toDescentData` is full for *every* fpqc
  covering presieve of an affine scheme.
* `Stacks.Descent.isPrestackFor_qcohPseudofunctor_of_isAffine`: hence
  `CategoryTheory.Pseudofunctor.IsPrestackFor` holds for every fpqc covering presieve of an
  affine scheme, the faithful half being `Stacks.Descent.faithful_qcohToDescentData_fpqc`.
* `Stacks.Descent.isPrestack_qcohPseudofunctor_fpqc_of_standard`: hence quasi-coherent modules
  form a prestack for the fpqc topology, by the reduction to affine bases
  `Stacks.Descent.isPrestack_qcohPseudofunctor_fpqc_of_isAffine`.
* `Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_fpqc`: hence the full
  faithfulness clause of Stacks 023T, in the shape in which Stacks 023T states it.

## Implementation notes

The reduction over an affine base is Stacks 022E, in the form
`AlgebraicGeometry.exists_affineCover_flat_sieve_le_of_mem_fpqcPrecoverage`, fed to
`CategoryTheory.Pseudofunctor.DescentData.full_toDescentData_of_refinement`.  Only the arrows of
the refining family are used from the sieve inclusion: each `g k` factors through some member
`f (α k)` of the given family, which is the refinement datum that lemma consumes.

The only hypothesis of `CategoryTheory.Pseudofunctor.DescentData.full_toDescentData_of_refinement`
about the given family is that a morphism between quasi-coherent modules on `X i` is determined by
its pullbacks along morphisms into `X i` factoring through the refining family.  That hypothesis
is discharged by the general-base separatedness `Stacks.Descent.hom_ext_of_pullback_map_eq_fpqc`
applied to the base change of the refining family to `X i`, which is an fpqc covering of `X i` by
`CategoryTheory.Precoverage.mem_coverings_of_isPullback`.

The equality of pullbacks that `Stacks.Descent.hom_ext_of_pullback_map_eq_fpqc` consumes is
stated for `AlgebraicGeometry.Scheme.Modules.pullback`, while the hypothesis supplies it for the
pullback functors of `Stacks.Descent.qcohPseudofunctor`.  The two agree definitionally, by
`Stacks.Descent.hom_map_map`; the identification is made by naming the `congrArg` with its type
**inferred** and discharging the goal with `exact`.

## References

* [Stacks Project, Tag 022E](https://stacks.math.columbia.edu/tag/022E)
* [Stacks Project, Tag 023D](https://stacks.math.columbia.edu/tag/023D)
* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.Descent

/-- **The fullness half of Stacks 023S**, as a hypothesis: for every standard fpqc covering of an
affine scheme — a finite family of morphisms from spectra of rings whose presieve is an fpqc
covering — the canonical descent functor of `Stacks.Descent.qcohPseudofunctor` is full.

Flatness and joint surjectivity of the family are not listed separately, being part of
membership of the presieve in `AlgebraicGeometry.Scheme.fpqcPrecoverage`.  The shape is the one
`Stacks.Descent.isStackFor_qcohPseudofunctor_of_isAffine` uses for the corresponding
equivalence. -/
abbrev StandardAffineFullness : Prop :=
  ∀ (T : Scheme.{u}) (_ : IsAffine T) (K : Type) (_ : Finite K)
    (A : K → CommRingCat.{u}) (g : ∀ k, Spec (A k) ⟶ T)
    (_ : Presieve.ofArrows (fun k ↦ Spec (A k)) g ∈ Scheme.fpqcPrecoverage.{u} T),
    (qcohPseudofunctor.toDescentData g).Full

/-- **Fullness of the canonical descent functor over an affine base, for an arbitrary fpqc
covering family.**  Granting the fullness half of Stacks 023S for standard coverings, the
canonical descent functor of `Stacks.Descent.qcohPseudofunctor` is full along every fpqc covering
family of an affine scheme, with no finiteness hypothesis on the index type and no affineness of
the members.

The given family is refined by a standard one with Stacks 022E, and fullness passes from the
refinement to it by
`CategoryTheory.Pseudofunctor.DescentData.full_toDescentData_of_refinement`, whose hypothesis is
the general-base separatedness applied over each member of the given family. -/
theorem full_qcohToDescentData_of_isAffine (hstd : StandardAffineFullness.{u})
    {T : Scheme.{u}} [IsAffine T] {I : Type v} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ T)
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} T) :
    (qcohPseudofunctor.toDescentData f).Full := by
  obtain ⟨K, hK, A, g, hmem, hle⟩ :=
    exists_affineCover_flat_sieve_le_of_mem_fpqcPrecoverage f hf
  have H : ∀ k, ∃ (i : I) (b : Spec (A k) ⟶ X i), b ≫ f i = g k := fun k ↦ by
    obtain ⟨_, b, _, ⟨i⟩, fac⟩ := hle _ (Sieve.ofArrows_mk _ g k)
    exact ⟨i, b, fac⟩
  choose α p' hp using H
  have := hstd T ‹_› K hK A g hmem
  refine Pseudofunctor.DescentData.full_toDescentData_of_refinement
    (f := f) (f' := g) (α := α) (p' := p')
    (fun k ↦ by rw [Category.comp_id]; exact hp k) ?_
  intro i M N θ θ' h
  apply ObjectProperty.hom_ext
  have hcov : Presieve.ofArrows (fun k ↦ pullback (f i) (g k))
      (fun k ↦ pullback.fst (f i) (g k)) ∈ Scheme.fpqcPrecoverage.{u} (X i) :=
    Precoverage.mem_coverings_of_isPullback g hmem (f i) _
      (fun k ↦ pullback.snd (f i) (g k)) fun k ↦ IsPullback.of_hasPullback (f i) (g k)
  have hM : M.obj.IsQuasicoherent := M.property
  have hN : N.obj.IsQuasicoherent := N.property
  refine hom_ext_of_pullback_map_eq_fpqc (M := M.obj) (N := N.obj) _ hcov fun k ↦ ?_
  have hk := congrArg InducedCategory.Hom.hom
    (h k _ (pullback.fst (f i) (g k)) (pullback.snd (f i) (g k)) pullback.condition.symm)
  exact hk

/-- **Descent of morphisms of quasi-coherent modules along every fpqc covering presieve of an
affine scheme**, granting the fullness half of Stacks 023S.  This is the hypothesis `haff` of
`Stacks.Descent.isPrestack_qcohPseudofunctor_fpqc_of_isAffine`; the faithful half is
`Stacks.Descent.faithful_qcohToDescentData_fpqc`. -/
theorem isPrestackFor_qcohPseudofunctor_of_isAffine (hstd : StandardAffineFullness.{u})
    {T : Scheme.{u}} [IsAffine T] (R : Presieve T)
    (hR : R ∈ Scheme.fpqcPrecoverage.{u} T) :
    qcohPseudofunctor.IsPrestackFor R := by
  obtain ⟨I, Y, f, rfl⟩ := R.exists_eq_ofArrows
  rw [Pseudofunctor.isPrestackFor_ofArrows_iff]
  have := full_qcohToDescentData_of_isAffine hstd f hR
  have := faithful_qcohToDescentData_fpqc f hR
  exact ⟨.ofFullyFaithful _⟩

/-- **Quasi-coherent modules form a prestack for the fpqc topology**, granting the fullness half
of Stacks 023S.  The Zariski prestack condition and the locality of the prestack condition on the
base are `Stacks.Descent.isPrestack_qcohPseudofunctor` and
`Stacks.Descent.isPrestack_qcohPseudofunctor_fpqc_of_isAffine`. -/
theorem isPrestack_qcohPseudofunctor_fpqc_of_standard (hstd : StandardAffineFullness.{u}) :
    qcohPseudofunctor.{u}.IsPrestack Scheme.fpqcTopology.{u} :=
  isPrestack_qcohPseudofunctor_fpqc_of_isAffine
    fun T _hT R hR ↦ isPrestackFor_qcohPseudofunctor_of_isAffine hstd (T := T) R hR

/-- **The full faithfulness clause of Stacks 023T, granting the fullness half of Stacks 023S.**
For an arbitrary fpqc covering family of an arbitrary scheme, the canonical descent functor of
Stacks 023D on quasi-coherent modules is fully faithful. -/
theorem nonempty_fullyFaithful_canonicalDescentFunctor_fpqc (hstd : StandardAffineFullness.{u})
    {S : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hfpqc : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S) :
    Nonempty (canonicalDescentFunctor f).FullyFaithful := by
  have := isPrestack_qcohPseudofunctor_fpqc_of_standard hstd
  exact nonempty_fullyFaithful_canonicalDescentFunctor_of_isPrestack hfpqc

end Stacks.Descent

end

end
