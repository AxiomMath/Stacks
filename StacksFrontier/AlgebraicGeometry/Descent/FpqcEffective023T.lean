module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcStandardReduction
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.StandardAffineSeparated

/-!
# The separated half of fpqc descent for quasi-coherent modules, over an arbitrary base

Stacks 023T asserts two things for an fpqc covering family `f i : X i ⟶ S` of an arbitrary
scheme: that the canonical descent functor of Stacks 023D on quasi-coherent modules is **fully
faithful**, and that every quasi-coherent descent datum is **effective**.  This file proves, with
no hypotheses beyond the fpqc covering condition, the *separated* part of the first assertion:
the canonical descent functor is **faithful**.  Equivalently, a morphism of quasi-coherent
modules on `S` is determined by its pullbacks along the members of the family.

The two inputs from the library are strictly weaker than this.  The affine case,
`Stacks.Descent.hom_ext_of_pullback_map_eq_of_isAffine'`, needs the base affine, the index type
finite and the sources spectra of rings.  The Zariski case,
`Stacks.Descent.hom_ext_of_pullback_map_eq`, needs the members to be open immersions.  What is
carried out here is the combination of the two: separatedness is tested on an affine open cover
of the base, and over each affine chart the given family is replaced by a standard one using
Stacks 022E.

## Main results

* `Stacks.Descent.pullback_map_eq_of_comp` and `Stacks.Descent.pullback_comp_map_eq`: an equality
  of pullbacks of two morphisms of sheaves of modules propagates along a composite, in both of
  the two directions in which the pseudofunctoriality of pullback is used below.
* `Stacks.Descent.hom_ext_of_pullback_map_eq_of_mem_fpqcPrecoverage_of_isAffine`: the
  affine separatedness with its covering hypotheses packaged as membership of
  `AlgebraicGeometry.Scheme.fpqcPrecoverage`.
* `Stacks.Descent.hom_ext_of_pullback_map_eq_fpqc`: **a morphism of quasi-coherent modules on an
  arbitrary scheme is determined by its pullbacks along an arbitrary fpqc covering family.**
* `Stacks.Descent.faithful_qcohToDescentData_fpqc` and
  `Stacks.Descent.faithful_canonicalDescentFunctor_fpqc`: the same, read as faithfulness of
  `CategoryTheory.Pseudofunctor.toDescentData` for `Stacks.Descent.qcohPseudofunctor` and of
  `AlgebraicGeometry.canonicalDescentFunctor`.

## What this is not

This is the **faithfulness** half of the full faithfulness clause of Stacks 023T, not that
clause.  The separating content is fullness: the gluing of a compatible family of morphisms of
the pulled-back modules into a morphism on the base.  Over an affine base that is the
surjectivity of `Hom_R(M, N) → Hom_B(M ⊗ B, N ⊗ B)` onto the maps whose two base changes to
`B ⊗[R] B` agree, for `R ⟶ B` faithfully flat; the ring-level statement is proved as
`Stacks.Descent.existsUnique_baseChange_eq_of_tensorInl_eq_tensorInr`, and the transport of a
*morphism* of module descent data across `Spec` is absent.  So neither
`fpqcDescentData_isEffective` nor `fpqcDescentFunctor_fullyFaithful` is proved here, and no
`@[stacks 023T]` attribute is placed **in this file**.

That is a statement about this file.  **Both halves of Stacks 023T are proved and tagged**, by
another route: effectivity is
`AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage`
(`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/FpqcEffectiveUnconditional.lean:63`), with
no hypothesis and at an arbitrary index universe, and full faithfulness is
`AlgebraicGeometry.nonempty_fullyFaithful_canonicalDescentFunctor'`
(`StacksFrontier/AlgebraicGeometry/Descent/FpqcHomSheafRefinement.lean:418`).  What this file
contributes to the tag is the general-base **faithfulness** below, obtained from the Zariski
separatedness rather than from
`AlgebraicGeometry.fpqcDescentOfQuasicoherentHoms`, and it remains the input of the reduction in
`StacksFrontier/AlgebraicGeometry/Descent/FpqcFullFaithful023T.lean`.

What this does settle is one of the two obligations recorded in the section "What this leaves
open" of
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/FpqcPrestackReduction.lean`: the
general-base separatedness which the refinement step of that file consumes, and which was
expected there to come from the affine faithfulness by the `1`-hypercover locality argument.  It
is obtained here without that machinery, directly from the Zariski separatedness.

## Implementation notes

The reduction to an affine chart is `Stacks.Descent.hom_ext_of_pullback_map_eq` applied to
`AlgebraicGeometry.Scheme.affineCover`.  Its components are spectra, so their affineness is
supplied as `inferInstanceAs (IsAffine (Spec _))`; instance search does not unfold the cover to
see it.

The family is transported to the chart `v : V ⟶ S` by base change.  Only
`CategoryTheory.Precoverage.mem_coverings_of_isPullback` is used for this, never
`CategoryTheory.Precoverage.pullbackArrows_mem`: the former delivers the base change already in
the `CategoryTheory.Presieve.ofArrows` form that Stacks 022E consumes and places no restriction
on the index universe, whereas the latter delivers a
`CategoryTheory.Presieve.pullbackArrows` that then has to be converted.

Over the chart, Stacks 022E in the form
`AlgebraicGeometry.exists_affineCover_flat_sieve_le_of_mem_fpqcPrecoverage` supplies a standard
family `g k : Spec (A k) ⟶ V` together with an inclusion of generated sieves.  The inclusion is
used only on the arrows `g k` themselves: each factors through some member
`Limits.pullback.fst v (f i)` of the base-changed family, and composing that factorisation with
`Limits.pullback.condition` exhibits `g k ≫ v` as factoring through `f i`.  This is why the
base change is taken with `v` in the *first* argument of `Limits.pullback`: the projection that
has to be post-composed with `v` is then `Limits.pullback.fst`, and `pullback.condition` rewrites
it to `Limits.pullback.snd ≫ f i` in one step.

The two propagation lemmas are deliberately separate and are proved in term mode from
`CategoryTheory.NatIso.naturality_1` and `CategoryTheory.NatIso.naturality_2` respectively.  Each
rewrites the pullback of a morphism into a conjugate of the other pullback by components of
`AlgebraicGeometry.Scheme.Modules.pullbackComp`, so that the hypothesis can be substituted with
no cancellation of isomorphisms; the direction of the comparison decides which of the two
naturality lemmas applies, and using one for both would require cancelling the components of the
comparison, whose `IsIso` instances are not found on the nose.

## References

* [Stacks Project, Tag 022E](https://stacks.math.columbia.edu/tag/022E)
* [Stacks Project, Tag 023D](https://stacks.math.columbia.edu/tag/023D)
* [Stacks Project, Tag 023E](https://stacks.math.columbia.edu/tag/023E)
* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.Descent

section Propagate

variable {S Y Z : Scheme.{u}} {M N : S.Modules} {φ ψ : M ⟶ N} {c : Z ⟶ S}

/-- **Propagation of an equality of pullbacks along a composite, outwards.**  If two morphisms of
sheaves of modules agree after pullback along `c`, they agree after pullback along `b ≫ c`. -/
theorem pullback_map_eq_of_comp (b : Y ⟶ Z)
    (h : (Scheme.Modules.pullback c).map φ = (Scheme.Modules.pullback c).map ψ) :
    (Scheme.Modules.pullback (b ≫ c)).map φ = (Scheme.Modules.pullback (b ≫ c)).map ψ := by
  have key : ∀ θ : M ⟶ N, (Scheme.Modules.pullback (b ≫ c)).map θ =
      (Scheme.Modules.pullbackComp b c).inv.app M ≫
        (Scheme.Modules.pullback b).map ((Scheme.Modules.pullback c).map θ) ≫
          (Scheme.Modules.pullbackComp b c).hom.app N :=
    fun θ ↦ (NatIso.naturality_1 (Scheme.Modules.pullbackComp b c) θ).symm
  rw [key φ, key ψ, h]

/-- **Propagation of an equality of pullbacks along a composite, inwards.**  If two morphisms of
sheaves of modules agree after pullback along `b ≫ c`, they agree after pullback along `c`
followed by pullback along `b`. -/
theorem pullback_comp_map_eq {b : Y ⟶ Z}
    (h : (Scheme.Modules.pullback (b ≫ c)).map φ = (Scheme.Modules.pullback (b ≫ c)).map ψ) :
    (Scheme.Modules.pullback b).map ((Scheme.Modules.pullback c).map φ) =
      (Scheme.Modules.pullback b).map ((Scheme.Modules.pullback c).map ψ) := by
  have key : ∀ θ : M ⟶ N,
      (Scheme.Modules.pullback b).map ((Scheme.Modules.pullback c).map θ) =
      (Scheme.Modules.pullbackComp b c).hom.app M ≫
        (Scheme.Modules.pullback (b ≫ c)).map θ ≫
          (Scheme.Modules.pullbackComp b c).inv.app N :=
    fun θ ↦ (NatIso.naturality_2 (Scheme.Modules.pullbackComp b c) θ).symm
  rw [key φ, key ψ, h]

end Propagate

/-- **The affine separatedness, with the covering hypotheses packaged as membership of
`AlgebraicGeometry.Scheme.fpqcPrecoverage`.**  A morphism of quasi-coherent modules on an affine
scheme is determined by its pullbacks along a finite family of morphisms from spectra of rings
which is an fpqc covering. -/
theorem hom_ext_of_pullback_map_eq_of_mem_fpqcPrecoverage_of_isAffine {T : Scheme.{u}}
    [IsAffine T] {K : Type v} [Finite K] {A : K → CommRingCat.{u}} (g : ∀ k, Spec (A k) ⟶ T)
    (hg : Presieve.ofArrows (fun k ↦ Spec (A k)) g ∈ Scheme.fpqcPrecoverage.{u} T)
    {M N : T.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] {φ ψ : M ⟶ N}
    (h : ∀ k, (Scheme.Modules.pullback (g k)).map φ = (Scheme.Modules.pullback (g k)).map ψ) :
    φ = ψ := by
  have hg' := (Scheme.ofArrows_mem_precoverage_iff _).1
    (Scheme.propQCPrecoverage_le_precoverage (P := @Flat) _ hg)
  have : ∀ k, Flat (g k) := hg'.2
  exact hom_ext_of_pullback_map_eq_of_isAffine' g (fun t ↦ (hg'.1 t).imp fun _ h ↦ h) h

/-- **Separatedness of fpqc descent for quasi-coherent modules, over an arbitrary base.**  A
morphism of quasi-coherent modules on a scheme `S` is determined by its pullbacks along the
members of an fpqc covering family `f i : X i ⟶ S`.

This is unconditional: no affineness of `S`, no finiteness of the index type and no open
immersion hypothesis.  It is the general-base form of
`Stacks.Descent.hom_ext_of_pullback_map_eq_of_isAffine'`, obtained from it by testing on an
affine open cover of `S` with the Zariski separatedness
`Stacks.Descent.hom_ext_of_pullback_map_eq`, and over each affine chart replacing the base change
of the family by a standard fpqc covering with Stacks 022E. -/
theorem hom_ext_of_pullback_map_eq_fpqc {S : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S)
    {M N : S.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] {φ ψ : M ⟶ N}
    (h : ∀ i, (Scheme.Modules.pullback (f i)).map φ = (Scheme.Modules.pullback (f i)).map ψ) :
    φ = ψ := by
  refine hom_ext_of_pullback_map_eq S.affineCover.f S.affineCover.iSup_opensRange fun j ↦ ?_
  set v := S.affineCover.f j with hv
  have : IsAffine (S.affineCover.X j) := inferInstanceAs (IsAffine (Spec _))
  have hbc : Presieve.ofArrows (fun i ↦ Limits.pullback v (f i))
      (fun i ↦ Limits.pullback.fst v (f i)) ∈
        Scheme.fpqcPrecoverage.{u} (S.affineCover.X j) :=
    Precoverage.mem_coverings_of_isPullback f hf v _ (fun i ↦ Limits.pullback.snd v (f i))
      fun i ↦ IsPullback.of_hasPullback v (f i)
  obtain ⟨K, hK, A, g, hmem, hle⟩ :=
    exists_affineCover_flat_sieve_le_of_mem_fpqcPrecoverage
      (fun i ↦ Limits.pullback.fst v (f i)) hbc
  refine hom_ext_of_pullback_map_eq_of_mem_fpqcPrecoverage_of_isAffine g hmem fun k ↦ ?_
  obtain ⟨W, b, c, hc, hfac⟩ :=
    hle _ ⟨_, 𝟙 _, g k, Presieve.ofArrows.mk k, Category.id_comp _⟩
  obtain ⟨i⟩ := hc
  refine pullback_comp_map_eq (b := g k) (c := v) ?_
  have hgv : g k ≫ v = (b ≫ Limits.pullback.snd v (f i)) ≫ f i := by
    rw [← hfac, Category.assoc, Category.assoc, Limits.pullback.condition]
  rw [hgv]
  exact pullback_map_eq_of_comp _ (h i)

/-- **The faithfulness half of Stacks 023T for `Stacks.Descent.qcohPseudofunctor`.**  For an
arbitrary fpqc covering family of an arbitrary scheme,
`CategoryTheory.Pseudofunctor.toDescentData` of the pseudofunctor of quasi-coherent modules is
faithful. -/
theorem faithful_qcohToDescentData_fpqc {S : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S) :
    (qcohPseudofunctor.toDescentData f).Faithful where
  map_injective {M N _ _} hφ := by
    have hM : M.obj.IsQuasicoherent := M.property
    have hN : N.obj.IsQuasicoherent := N.property
    apply ObjectProperty.hom_ext
    refine hom_ext_of_pullback_map_eq_fpqc (M := M.obj) (N := N.obj) f hf fun i ↦ ?_
    exact congrArg
      (fun θ ↦ InducedCategory.Hom.hom (Pseudofunctor.DescentData.Hom.hom θ i)) hφ

/-- **The faithfulness half of Stacks 023T.**  For an arbitrary fpqc covering family of an
arbitrary scheme, the canonical descent functor of Stacks 023D on quasi-coherent modules is
faithful.

This is the separated half of the full faithfulness that Stacks 023T asserts; the surjective
half, the gluing of morphisms, is not proved here.  Compare
`Stacks.Descent.faithful_canonicalDescentFunctor_of_isPrestack`, which is the same conclusion
from the fpqc prestack condition — a hypothesis that contains the surjective half as well. -/
theorem faithful_canonicalDescentFunctor_fpqc {S : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S) :
    (canonicalDescentFunctor f).Faithful where
  map_injective {_M _N φ ψ} hφ := by
    apply ObjectProperty.hom_ext
    refine hom_ext_of_pullback_map_eq_fpqc f hf fun i ↦ ?_
    exact (canonicalDescentFunctor_map_hom_hom f φ i).symm.trans
      ((congrArg (fun θ ↦ θ.hom.hom i) hφ).trans (canonicalDescentFunctor_map_hom_hom f ψ i))

end Stacks.Descent

end

end
