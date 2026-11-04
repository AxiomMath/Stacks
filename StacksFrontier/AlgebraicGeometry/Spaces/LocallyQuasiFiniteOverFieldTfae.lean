module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyQuasiFiniteOverFieldRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Zero
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Algebraic spaces locally quasi-finite over a field

Let `k` be a field and `X` an algebraic space over `k`. Stacks 06S0 says that the following are
equivalent: `X` is locally quasi-finite over `k`; `X` is locally of finite type over `k` and of
dimension `0`; either of these together with `X` being a scheme; and `X` is a disjoint union of
spectra of finite-dimensional Artinian local `k`-algebras.

## Main results

* `AlgebraicGeometry.Space.tfae_isLocallyQuasiFinite_to_field`: **Stacks 06S0**.

## Implementation notes

The field is an object `K` of the big fppf site over `S` together with an isomorphism of its
underlying scheme with `Spec k`, and the structure morphism is any `g : X ⟶ h_K`. The source's
situation is `S = Spec k` with `K` the terminal object, so this is a generalization, in the
form used by `AlgebraicGeometry.Space.isRepresentable_of_isLocallyQuasiFinite_to_field`.

"`X` is a scheme" is representability of `X`. "Dimension `0`" is the dimension of Tag 04N6 being
at most `0`: that dimension is a supremum in `WithBot ℕ∞`, so the empty space has dimension `⊥`
while satisfying conditions (1), (3) and (5) (the empty disjoint union), and `= 0` would make the
equivalence false for it. This is the convention of
`AlgebraicGeometry.Space.isLocallyQuasiFinite_iff_dimension_le_zero` (Stacks 0ACA).

Condition (5) is an object `Y` of the site with `h_Y ≅ X` and an isomorphism of the underlying
scheme of `Y` with `∐ Spec Aᵢ` over `Spec k`: the composite with the morphism induced by the
`k`-algebra structures is the structure morphism `Y ⟶ K ≅ Spec k` read through `h_Y ≅ X`.

The proof is the source's: (1) and (2) are equivalent by Tag 0ACA (which is Tag 04NV over a
field), (1) and (2) make `X` a scheme by Tag 06LZ, and on the scheme Tag 06LH gives the
decomposition. Conversely each `Spec Aᵢ ⟶ Spec k` is finite, so the disjoint union is locally
quasi-finite over `k`, and a morphism of the site with locally quasi-finite underlying morphism
of schemes is locally quasi-finite as a morphism of algebraic spaces.

## References

* [Stacks Project, Tag 06S0](https://stacks.math.columbia.edu/tag/06S0)
* [Stacks Project, Tag 04NV](https://stacks.math.columbia.edu/tag/04NV)
* [Stacks Project, Tag 06LZ](https://stacks.math.columbia.edu/tag/06LZ)
* [Stacks Project, Tag 06LH](https://stacks.math.columbia.edu/tag/06LH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A nonempty scheme which is discrete has topological Krull dimension zero. -/
@[ega "0 14.1.12" "partial", ega "0 14.1.9" "sufficiency"]
private theorem topologicalKrullDim_eq_zero_of_discreteTopology (Y : Scheme.{u})
    [DiscreteTopology Y] [Nonempty Y] : topologicalKrullDim Y = 0 := by
  refine le_antisymm (topologicalKrullDim_zero_of_discreteTopology Y) ?_
  obtain ⟨y⟩ := ‹Nonempty Y›
  have : Nonempty (TopologicalSpace.IrreducibleCloseds Y) :=
    ⟨⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact Order.krullDim_nonneg

/-- **Stacks 06S0.** Let `k` be a field and `X` an algebraic space over `k`, presented as an
algebraic space over `S` with a morphism `g : X ⟶ h_K` to an object `K` of the site whose
underlying scheme is `Spec k`. The following are equivalent:
1. `X` is locally quasi-finite over `k`;
2. `X` is locally of finite type over `k` and has dimension `0`;
3. `X` is a scheme and is locally quasi-finite over `k`;
4. `X` is a scheme, is locally of finite type over `k` and has dimension `0`;
5. `X` is a disjoint union of spectra of Artinian local `k`-algebras `A` with
   `dim_k A < ∞`, over `k`.

"Dimension `0`" is read as `≤ 0`, since the empty space has dimension `⊥` and satisfies (1). -/
@[stacks 06S0]
theorem tfae_isLocallyQuasiFinite_to_field {k : Type u} [Field k]
    {K : BigFppfOver B S hS} (e : (BigFppfOver.toScheme B S hS).obj K ≅ Spec (.of k))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (g : X ⟶ yoneda.obj K) :
    [IsLocallyQuasiFinite B S hS g,
      IsLocallyOfFiniteType B S hS g ∧ dimension B S hS X hX ≤ 0,
      X.IsRepresentable ∧ IsLocallyQuasiFinite B S hS g,
      X.IsRepresentable ∧ IsLocallyOfFiniteType B S hS g ∧ dimension B S hS X hX ≤ 0,
      ∃ (Y : BigFppfOver B S hS) (eX : yoneda.obj Y ≅ X) (I : Type u) (A : I → Type u)
        (_ : ∀ i, CommRing (A i)) (_ : ∀ i, Algebra k (A i)) (_ : ∀ i, IsLocalRing (A i))
        (_ : ∀ i, IsArtinianRing (A i)) (_ : ∀ i, Module.Finite k (A i))
        (eY : (BigFppfOver.toScheme B S hS).obj Y ≅ ∐ fun i ↦ Spec (.of (A i))),
        eY.hom ≫ Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap k (A i)))) =
          (BigFppfOver.toScheme B S hS).map (yoneda.preimage (eX.hom ≫ g)) ≫ e.hom].TFAE := by
  have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj K) :=
    ⟨fun a b => e.hom.homeomorph.injective (Subsingleton.elim _ _)⟩
  let Q : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ f => IsLocallyQuasiFinite B S hS f
  have : Q.RespectsIso := holdsOnEveryEtaleChart_respectsIso_presheaf B S hS _
  tfae_have 1 ↔ 2 := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have hlft : IsLocallyOfFiniteType B S hS g := holdsOnEveryEtaleChart_mono B S hS
        (fun _ h ↦ h.1) h
      exact ⟨hlft, (isLocallyQuasiFinite_iff_dimension_le_zero B S hS hX hsub g hlft).1 h⟩
    · exact (isLocallyQuasiFinite_iff_dimension_le_zero B S hS hX hsub g h.1).2 h.2
  tfae_have 1 → 3 := fun h ↦
    ⟨isRepresentable_of_isLocallyQuasiFinite_to_field B S hS e hX g h, h⟩
  tfae_have 3 → 1 := fun h ↦ h.2
  tfae_have 2 → 4 := fun h ↦
    ⟨isRepresentable_of_dimension_le_zero_to_field B S hS e hX g h.1 h.2, h⟩
  tfae_have 4 → 2 := fun h ↦ h.2
  tfae_have 3 → 5 := by
    rintro ⟨hrep, hlqf⟩
    refine ⟨X.reprX, X.reprW, ?_⟩
    set h := yoneda.preimage (X.reprW.hom ≫ g) with hh
    have hyh : IsLocallyQuasiFinite B S hS (yoneda.map h) := by
      rw [hh, Functor.map_preimage]
      exact (Q.cancel_left_of_respectsIso X.reprW.hom g).2 hlqf
    obtain ⟨_, _⟩ := (isLocallyQuasiFinite_yoneda_map_iff B S hS h).1 hyh
    set f := (BigFppfOver.toScheme B S hS).map h ≫ e.hom
    have hdisc : DiscreteTopology ((BigFppfOver.toScheme B S hS).obj X.reprX) :=
      (locallyQuasiFinite_iff_discreteTopology_of_subsingleton f).1 inferInstance
    rcases isEmpty_or_nonempty ((BigFppfOver.toScheme B S hS).obj X.reprX) with hY | hY
    · refine ⟨PEmpty.{u + 1}, fun i ↦ i.elim, fun i ↦ i.elim, fun i ↦ i.elim, fun i ↦ i.elim,
        fun i ↦ i.elim, fun i ↦ i.elim, ⟨isInitialOfIsEmpty.to _, Sigma.desc fun i ↦ i.elim,
        isInitialOfIsEmpty.hom_ext _ _, Sigma.hom_ext _ _ fun i ↦ i.elim⟩,
        isInitialOfIsEmpty.hom_ext _ _⟩
    · obtain ⟨I, A, i₁, i₂, i₃, i₄, i₅, eY, heY⟩ :=
        exists_iso_coproduct_spec_local_artinian_of_dimension_zero k f
          (topologicalKrullDim_eq_zero_of_discreteTopology _)
      exact ⟨I, A, i₁, i₂, i₃, i₄, i₅, eY, heY⟩
  tfae_have 5 → 3 := by
    rintro ⟨Y, eX, I, A, _, _, _, _, _, eY, heY⟩
    refine ⟨Functor.IsRepresentable.mk' eX, ?_⟩
    set h := yoneda.preimage (eX.hom ≫ g)
    have hfin (i : I) :
        AlgebraicGeometry.IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k (A i)))) :=
      (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
    -- the generic `HasRingHomProperty` instance leaves the ring-hom property undetermined
    have : IsZariskiLocalAtSource @LocallyOfFiniteType.{u} :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
    have : IsZariskiLocalAtSource @LocallyQuasiFinite.{u} :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.QuasiFinite)
    have : LocallyOfFiniteType
        (Sigma.desc fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap k (A i)))) :=
      IsZariskiLocalAtSource.sigmaDesc fun i ↦ inferInstance
    have : LocallyQuasiFinite
        (Sigma.desc fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap k (A i)))) :=
      IsZariskiLocalAtSource.sigmaDesc fun i ↦ inferInstance
    have hmap : (BigFppfOver.toScheme B S hS).map h =
        (eY.hom ≫ Sigma.desc fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap k (A i)))) ≫
          e.inv := by
      rw [heY, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hyh : IsLocallyQuasiFinite B S hS (yoneda.map h) :=
      (isLocallyQuasiFinite_yoneda_map_iff B S hS h).2 (by rw [hmap]; exact ⟨inferInstance,
        inferInstance⟩)
    rw [Functor.map_preimage] at hyh
    exact (Q.cancel_left_of_respectsIso eX.hom g).1 hyh
  tfae_finish

end AlgebraicGeometry.Space

end
