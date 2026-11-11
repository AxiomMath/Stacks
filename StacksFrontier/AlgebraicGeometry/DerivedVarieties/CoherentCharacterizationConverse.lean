module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.CoherentConverse.Assembly
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.CoherentCharacterizationFiniteExt
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.CoherentConverse.FourierMukaiFiniteHom

/-!
# Coherent objects via finiteness of `Ext`: the converse, and the equivalence ([Stacks, Tag 0FYD])

Let `X` be a scheme proper over a field `k` and let `K` be an object of `D_QCoh(𝒪_X)`. The
following are equivalent:

1. `K` lies in `D^b_Coh(𝒪_X)`;
2. `∑_{i ∈ ℤ} dim_k Ext^i_X(E, K) < ∞` for every perfect object `E` of `D(𝒪_X)`.

The implication (1) ⇒ (2) is
`CoherentCharacterization.hasFiniteTotalExt_of_derivedCategoryBBounded'` (in the namespace
`Stacks.AlgebraicGeometry.DerivedVarieties`). This file proves the converse,
`derivedCategoryBBounded_of_hasFiniteTotalExt`, and states the equivalence;
`derivedCategoryBBounded_iff_cardinalSum_rank_ext_lt_aleph0`, with condition (2) as the source's
sum of dimensions, carries the tag.

## Main results

* `derivedCategoryBBounded_of_hasFiniteTotalExt`: **(2) ⇒ (1)**, stated at the standard model
  exactly in the form of the hypothesis `h0FYD` of
  `Stacks.AlgebraicGeometry.DerivedVarieties.Representability.exists_iso_linearYoneda_of_converse`
  ([Stacks, Tag 0FYH]).
* `derivedCategoryBBounded_iff_hasFiniteTotalExt` and
  `derivedCategoryBBounded_iff_cardinalSum_rank_ext_lt_aleph0`: **the equivalence**, with
  condition (2) as `HasFiniteTotalExt` and as the source's `∑ dim_k < ∞` respectively.

## The proof of (2) ⇒ (1)

It is the source's. Let `K` satisfy (2). Near a point `x` of `X`, [Stacks, Tag 0CSJ] gives an
open `U ∋ x`, an `m`, an open `V ⊆ ℙᵐ_k` and a closed immersion `U ⟶ V` cut out by a closed
subscheme `Z ⊆ T = X ×_k ℙᵐ_k`; [Stacks, Tag 09IQ] gives a perfect `E'` on `T` whose restriction
to `X ×_k V` contains `𝒪_Z` as a direct summand. By adjunction, condition (2) makes the
Fourier–Mukai transform `M = Rq_*(Lp^*K ⊗^𝐋 E')` have finite total `Hom` from each member of the
exceptional sequence `𝒪(-m), …, 𝒪` of `ℙᵐ_k`; since that sequence generates `D_QCoh(ℙᵐ_k)`, `M`
lies in `D^b_Coh(ℙᵐ_k)`. By [Stacks, Tag 0CSK] the restriction `M|_V` contains
`R(U ⟶ V)_*(K|_U)` as a direct summand, so the latter is in `D^b_Coh(V)`, and since `U ⟶ V` is a
closed immersion `K|_U` lies in `D^b_Coh(U)`. Being in `D^b_Coh` is local. The steps are
`AlgebraicGeometry.CoherentConverse.derivedCategoryBBounded_of_fourierMukai` (everything except
the adjunction) and
`Stacks.AlgebraicGeometry.FourierMukaiFiniteHom.hasFiniteTotalHom_seqE_fourierMukai` (the
adjunction).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AlgebraicGeometry.DerivedVarieties.CoherentCharacterizationConverse

attribute [local instance 100000] HasDerivedCategory.standard

variable {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom]

/-- **Stacks Project, Tag 0FYD, the implication (2) ⇒ (1).** Let `X` be a scheme proper over a
field `k` and let `K ∈ D_QCoh(𝒪_X)` satisfy `∑_{i ∈ ℤ} dim_k Ext^i_X(E, K) < ∞` for every
perfect `E`. Then `K ∈ D^b_Coh(𝒪_X)`.

Stated at the standard model, exactly as the hypothesis `h0FYD` of
`Stacks.AlgebraicGeometry.DerivedVarieties.Representability.exists_iso_linearYoneda_of_converse`
([Stacks, Tag 0FYH]) asks. -/
theorem derivedCategoryBBounded_of_hasFiniteTotalExt :
    ∀ K : @DerivedCategory X.left.Modules _ _ (HasDerivedCategory.standard X.left.Modules),
      @DerivedCategoryB.derivedCategoryB X.left.Modules _ _
        (HasDerivedCategory.standard X.left.Modules)
        (SheafOfModules.isQuasicoherent X.left.ringCatSheaf) K →
      (∀ E : @DerivedCategory X.left.Modules _ _ (HasDerivedCategory.standard X.left.Modules),
        @Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} X.left.toRingedSpace
          (HasDerivedCategory.standard X.left.Modules) E →
        BeilinsonCoherentCharacterization.HasFiniteTotalExt k X E K) →
      @DerivedCategoryB.derivedCategoryBBounded X.left.Modules _ _
        (HasDerivedCategory.standard X.left.Modules) (fun M : X.left.Modules => M.IsCoherent) K :=
  fun K hK hExt => CoherentConverse.derivedCategoryBBounded_of_fourierMukai X K hK
    (FourierMukaiFiniteHom.hasFiniteTotalHom_seqE_fourierMukai X K hK hExt)

/-- **Stacks Project, Tag 0FYD.** Let `X` be a scheme proper over a field `k` and let `K` be an
object of `D_QCoh(𝒪_X)`. Then `K ∈ D^b_Coh(𝒪_X)` if and only if
`∑_{i ∈ ℤ} dim_k Ext^i_X(E, K) < ∞` for every perfect object `E` of `D(𝒪_X)`; the finiteness is
spelled `HasFiniteTotalExt`: every `Ext^i_X(E, K)` is finite-dimensional and only finitely many
are nonzero. -/
theorem derivedCategoryBBounded_iff_hasFiniteTotalExt (K : DerivedCategory X.left.Modules)
    (hK : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.left.ringCatSheaf) K) :
    DerivedCategoryB.derivedCategoryBBounded (fun M : X.left.Modules => M.IsCoherent) K ↔
      ∀ E : DerivedCategory X.left.Modules,
        Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.left.toRingedSpace) E →
          BeilinsonCoherentCharacterization.HasFiniteTotalExt k X E K :=
  ⟨fun hb E hE =>
      CoherentCharacterization.hasFiniteTotalExt_of_derivedCategoryBBounded' X K hb E hE,
    derivedCategoryBBounded_of_hasFiniteTotalExt X K hK⟩

attribute [local instance] AlgebraicGeometry.modulesLinear in
/-- **Stacks Project, Tag 0FYD, in the source's form.** Let `X` be a scheme proper over a field `k`
and let `K` be an object of `D_QCoh(𝒪_X)`. Then `K ∈ D^b_Coh(𝒪_X)` if and only if
`∑_{i ∈ ℤ} dim_k Ext^i_X(E, K) < ∞` for every perfect object `E` of `D(𝒪_X)`, the dimensions
being taken for the `k`-linear structure induced by `X ⟶ Spec k`. -/
@[stacks 0FYD "both implications, for X proper over a field and K in D_QCoh(O_X), with \
condition (2) as the source's sum of dimensions, a cardinal sum below aleph0"]
theorem derivedCategoryBBounded_iff_cardinalSum_rank_ext_lt_aleph0
    (K : DerivedCategory X.left.Modules)
    (hK : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.left.ringCatSheaf) K) :
    DerivedCategoryB.derivedCategoryBBounded (fun M : X.left.Modules => M.IsCoherent) K ↔
      ∀ E : DerivedCategory X.left.Modules,
        Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.left.toRingedSpace) E →
          Cardinal.sum (fun n : ℤ => Module.rank k (DerivedCategory.Ext E K n)) <
            Cardinal.aleph0 :=
  (derivedCategoryBBounded_iff_hasFiniteTotalExt X K hK).trans
    (forall_congr' fun E => imp_congr_right fun _ =>
      (CoherentCharacterization.cardinalSum_rank_ext_lt_aleph0_iff_hasFiniteTotalExt X E K).symm)

end Stacks.AlgebraicGeometry.DerivedVarieties.CoherentCharacterizationConverse

end
