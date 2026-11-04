module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ScalarExtensionTrace
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.FieldExtension
public import StacksFrontier.LinearAlgebra.SemilinearBaseChangeCriterion

/-!
# Constant coefficients `𝐙/p𝐙` under extension of an algebraically closed ground field

Let `k ⊆ k'` be algebraically closed fields of characteristic `p > 0` and `X` proper over `k`.
Restriction along `X_{k'} ⟶ X` is bijective on `H^q(X_étale, 𝐙/p𝐙)`: [Stacks, Tag 0A3P] (2).

The source's proof: both groups are the Frobenius-fixed vectors of `H^q(X, 𝒪_X)` and
`H^q(X_{k'}, 𝒪_{X_{k'}})` (Artin–Schreier and [Stacks, Tag 03P2]), the second space is the base
change of the first ([Stacks, Tag 02KH]), and fixed vectors of a Frobenius-semilinear map do not
change under extension of algebraically closed fields ([Stacks, Tag 0A3L]). Here the base-change
map `β` of `H^q(𝒪)` is the restriction of `𝐆_a`-cohomology along `X_{k'} ⟶ X` read through the
comparison of [Stacks, Tag 03P2]; it is semilinear and Frobenius-compatible by construction, it
satisfies the trace criterion of `Stacks.LinearAlgebra.injective_and_span_eq_top_of_forall_dual`
by `Stacks.ArtinSchreier.sum_smul_eq_zero_of_sum_smul_restriction_eq_zero`, and the two
cohomology spaces have the same dimension by [Stacks, Tag 02KH] over a field; so it is injective
with spanning image, which is what `Stacks.ArtinSchreier.bijective_of_frobenius_base_change`
consumes.

## Main definitions

* `Stacks.ArtinSchreier.structureSheafBaseChange`: the base-change map `β`.

## Main results

* `Stacks.ArtinSchreier.bijective_etaleCohomologyRestrictionMap_constantZMod`:
  **[Stacks, Tag 0A3P] (2)**.

## References

* [Stacks Project, Tag 0A3P](https://stacks.math.columbia.edu/tag/0A3P)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.EtaleCohomology

universe w u

namespace Stacks.ArtinSchreier

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k'] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k))

/-- The scalar extension carries the image of `c ∈ k` to the image of `c` in `k'`. -/
theorem scalarExtensionFst_appTop_baseScalarSection (c : k) :
    (scalarExtensionFst k k' f).appTop (baseScalarSection k f c) =
      baseScalarSection k' (scalarExtensionSnd (k' := k') f) (algebraMap k k' c) := by
  rw [appTop_baseScalarSection, pullback.condition, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply]
  have h := congrArg (fun φ => φ.hom c) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap k k')))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  rw [← h, baseScalarSection, CommRingCat.comp_apply, Scheme.Hom.appLE_top_top]

section Main

variable [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (scalarExtension k k' f).smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The map on the cohomology of the structure sheaf induced by extending the ground field**:
restriction of `𝐆_a`-cohomology along `X_{k'} ⟶ X`, read on `H^q(X, 𝒪_X)` and
`H^q(X_{k'}, 𝒪_{X_{k'}})` through the comparison of [Stacks, Tag 03P2]. -/
noncomputable def structureSheafBaseChange (q : ℕ) :
    cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) q →+
      cohomologyOverField k' (scalarExtensionSnd (k' := k') f)
        (SheafOfModules.unit (scalarExtension k k' f).ringCatSheaf) q :=
  (additiveSheafCohomologyOverFieldEquiv.{w} k' (scalarExtensionSnd (k' := k') f)
      q).toAddMonoidHom.comp
    ((additiveRestriction (scalarExtensionFst k k' f) q).comp
      (additiveSheafCohomologyOverFieldEquiv.{w} k f q).symm.toAddMonoidHom)

/-- Scalar multiplication on `H^q(X, 𝒪_X)` is `Sheaf.H.map` of the scalar section action,
read through the comparison equivalence. -/
private theorem symm_additiveSheafCohomologyOverFieldEquiv_smul (q : ℕ) (c : k)
    (v : cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) q) :
    (additiveSheafCohomologyOverFieldEquiv.{w} k f q).symm (c • v) =
      Sheaf.H.map (additiveSheafSmul X (baseScalarSection k f c)) q
        ((additiveSheafCohomologyOverFieldEquiv.{w} k f q).symm v) := by
  rw [AddEquiv.symm_apply_eq, additiveSheafCohomologyOverFieldEquiv_smul,
    AddEquiv.apply_symm_apply]

/-- The base-change map is semilinear over `k ⟶ k'`. -/
theorem structureSheafBaseChange_smul (q : ℕ) (c : k)
    (v : cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) q) :
    structureSheafBaseChange.{w} k k' f q (c • v) =
      algebraMap k k' c • structureSheafBaseChange.{w} k k' f q v := by
  simp only [structureSheafBaseChange, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom,
    Function.comp_apply]
  rw [symm_additiveSheafCohomologyOverFieldEquiv_smul,
    additiveRestriction_sheafH_map_of_directImage _ (additiveDirectImageComparison_smul _ _),
    scalarExtensionFst_appTop_baseScalarSection, additiveSheafCohomologyOverFieldEquiv_smul]

/-- The base-change map intertwines the Frobenius endomorphisms. -/
theorem structureSheafBaseChange_frobenius {p : ℕ} (hp : p.Prime) [CharP k p] [CharP k' p]
    (q : ℕ) (v : cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) q) :
    structureSheafBaseChange.{w} k k' f q
        ((structureSheafTopDegreeFrobeniusComparison.{w} k f hp q).frobenius v) =
      (structureSheafTopDegreeFrobeniusComparison.{w} k' (scalarExtensionSnd (k' := k') f) hp
          q).frobenius
        (structureSheafBaseChange.{w} k k' f q v) := by
  simp only [structureSheafBaseChange, structureSheafTopDegreeFrobeniusComparison,
    AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply,
    AddEquiv.symm_apply_apply]
  rw [additiveRestriction_sheafH_map_of_directImage _
    (frobeniusMap_comp_additiveDirectImageComparison _ hp _)]

/-- The base-change map on the cohomology of the structure sheaf satisfies the trace criterion:
a `k'`-linear relation among images gives `k`-linear relations after every linear form. -/
theorem structureSheafBaseChange_trace (q : ℕ) {n : ℕ} (c : Fin n → k')
    (v : Fin n → cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) q)
    (h : ∑ i, c i • structureSheafBaseChange.{w} k k' f q (v i) = 0) (ℓ : k' →ₗ[k] k) :
    ∑ i, ℓ (c i) • v i = 0 := by
  set E := additiveSheafCohomologyOverFieldEquiv.{w} k f q
  set E' := additiveSheafCohomologyOverFieldEquiv.{w} k' (scalarExtensionSnd (k' := k') f) q
  have h' : ∑ i, Sheaf.H.map (additiveSheafSmul (scalarExtension k k' f)
      (baseScalarSection k' (scalarExtensionSnd (k' := k') f) (c i))) q
        (additiveRestriction (scalarExtensionFst k k' f) q (E.symm (v i))) = 0 := by
    apply E'.injective
    rw [map_sum, map_zero, ← h]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [additiveSheafCohomologyOverFieldEquiv_smul]
    rfl
  have h2 := sum_smul_eq_zero_of_sum_smul_restriction_eq_zero f ℓ Finset.univ c
    (fun i => E.symm (v i)) h'
  have h3 := congrArg E h2
  rw [map_sum, map_zero] at h3
  refine Eq.trans ?_ h3
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← symm_additiveSheafCohomologyOverFieldEquiv_smul, AddEquiv.apply_symm_apply]

omit [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (scalarExtension k k' f).smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- The cohomology of the structure sheaf has the same dimension after extending the ground
field ([Stacks, Tag 02KH] over a field). -/
theorem finrank_cohomologyOverField_scalarExtension [IsProper f] (q : ℕ) :
    Module.finrank k' (cohomologyOverField k' (scalarExtensionSnd (k' := k') f)
        (SheafOfModules.unit (scalarExtension k k' f).ringCatSheaf) q) =
      Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) q) :=
  (finrank_cohomologyOverField_eq_of_iso k' (scalarExtensionSnd (k' := k') f)
      (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso
        (scalarExtensionFst k k' f)).symm q).trans
    (finrank_cohomologyOverField_baseChange_field k k' (scalarExtensionFst k k' f)
      (scalarExtensionSnd (k' := k') f) f (IsPullback.of_hasPullback f (specExt k k'))
      (SheafOfModules.unit X.ringCatSheaf) q)

/-- **[Stacks, Tag 0A3P] (2).** Let `k ⊆ k'` be an extension of algebraically closed fields of
characteristic `p > 0` and let `X` be a proper scheme over `k`. Then restriction along
`X_{k'} ⟶ X` is bijective on `H^q(X_étale, 𝐙/p𝐙)` for every `q`.

The target of the restriction map is the cohomology of the inverse image of the constant sheaf,
which is the constant sheaf `𝐙/p𝐙` on `X_{k'}` by
`Stacks.EtaleCohomology.etaleAbelianInverseImageConstantIso`. -/
@[stacks 0A3P "part (2)"]
theorem bijective_etaleCohomologyRestrictionMap_constantZMod {p : ℕ} (hp : 0 < p)
    [IsAlgClosed k] [IsAlgClosed k'] [CharP k p] [IsProper f] (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, w} (scalarExtensionFst k k' f)
      (etaleConstantZMod X p) q) := by
  have : NeZero p := ⟨hp.ne'⟩
  have : Fact p.Prime := CharP.char_is_prime_of_pos k p
  have : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
  let g := scalarExtensionFst k k' f
  let f' := scalarExtensionSnd (k' := k') f
  have : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback f (specExt k k')) ‹IsProper f›
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian (scalarExtension k k' f) := LocallyOfFiniteType.isLocallyNoetherian f'
  have : FiniteDimensional k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) q) :=
    finiteDimensional_cohomologyOverField_of_isProper k f _ q
  have : FiniteDimensional k' (cohomologyOverField k' f'
      (SheafOfModules.unit (scalarExtension k k' f).ringCatSheaf) q) :=
    finiteDimensional_cohomologyOverField_of_isProper k' f' _ q
  let hX := natCast_eq_zero_of_charP k p f
  let hX' := natCast_eq_zero_of_charP k' p f'
  let AS := constantArtinSchreierSequenceDatum X Fact.out hX
  let AS' := constantArtinSchreierSequenceDatum (scalarExtension k k' f) Fact.out hX'
  let e := (etaleAbelianInverseImageConstantIso.{u, 0} g).app
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod p)))
  let γ := (Sheaf.H.map e.hom q).comp
    (etaleCohomologyRestrictionMap.{u, 0, w} g (etaleConstantZMod X p) q)
  obtain ⟨hinj, hspan⟩ := Stacks.LinearAlgebra.injective_and_span_eq_top_of_forall_dual
    (finrank_cohomologyOverField_scalarExtension k k' f q) (structureSheafBaseChange.{w} k k' f q)
    (structureSheafBaseChange_smul.{w} k k' f q)
    (fun c v h ℓ => structureSheafBaseChange_trace.{w} k k' f q c v h ℓ)
  have hγ : Function.Bijective γ := by
    refine bijective_of_frobenius_base_change.{w} k k' (algebraMap k k') f f' AS AS' q hp
      (fun i => structureSheafTopDegreeFrobeniusComparison.{w} k f Fact.out i)
      (fun i => structureSheafTopDegreeFrobeniusComparison.{w} k' f' Fact.out i)
      (structureSheafBaseChange.{w} k k' f q) (structureSheafBaseChange_smul.{w} k k' f q)
      hinj hspan (structureSheafBaseChange_frobenius.{w} k k' f Fact.out q) γ (fun x => ?_)
    have key : Sheaf.H.map (zmodSheafHom.{u, u + 1} (scalarExtension k k' f) hX') q
        (Sheaf.H.map e.hom q (etaleCohomologyRestrictionMap.{u, 0, w} g _ q x)) =
          additiveRestriction g q (Sheaf.H.map (zmodSheafHom.{u, u + 1} X hX) q x) := by
      have hz : (etaleAbelianInverseImage.{u, 0} g).map (zmodSheafHom.{u, u + 1} X hX) ≫
          additiveInverseImageComparison.{u, u + 1} g =
            e.hom ≫ zmodSheafHom.{u, u + 1} (scalarExtension k k' f) hX' :=
        inverseImage_zmodSheafHom_comp_additiveInverseImageComparison.{u, u + 1} g hX
      rw [← Sheaf.H.map_comp_apply, ← hz, Sheaf.H.map_comp_apply]
      simp only [additiveRestriction, AddMonoidHom.coe_comp, Function.comp_apply]
      congr 1
      exact (etaleCohomologyRestrictionMap_comp_mk₀.{u, 0, w} g
        (zmodSheafHom.{u, u + 1} X hX) q x).symm
    have hL : artinSchreierComparison k' f' AS' q
        (structureSheafTopDegreeFrobeniusComparison.{w} k' f' Fact.out q) (γ x) =
          additiveSheafCohomologyOverFieldEquiv.{w} k' f' q
            (Sheaf.H.map (zmodSheafHom.{u, u + 1} (scalarExtension k k' f) hX') q (γ x)) := rfl
    have hR1 : artinSchreierComparison k f AS q
        (structureSheafTopDegreeFrobeniusComparison.{w} k f Fact.out q) x =
          additiveSheafCohomologyOverFieldEquiv.{w} k f q
            (Sheaf.H.map (zmodSheafHom.{u, u + 1} X hX) q x) := rfl
    have hR2 : ∀ v, structureSheafBaseChange.{w} k k' f q v =
        additiveSheafCohomologyOverFieldEquiv.{w} k' f' q (additiveRestriction g q
          ((additiveSheafCohomologyOverFieldEquiv.{w} k f q).symm v)) := fun _ => rfl
    rw [hL, hR1, hR2, AddEquiv.symm_apply_apply, ← key]
    rfl
  have hγe : ∀ y, etaleCohomologyRestrictionMap.{u, 0, w} g (etaleConstantZMod X p) q y =
      Sheaf.H.map e.inv q (γ y) := by
    intro y
    simp only [γ, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [← Sheaf.H.map_comp_apply, Iso.hom_inv_id, Sheaf.H.map_id_apply]
  have he : Function.Bijective (Sheaf.H.map e.inv q) :=
    Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso e.inv q
  rw [show (etaleCohomologyRestrictionMap.{u, 0, w} g (etaleConstantZMod X p) q :
      _ → _) = Sheaf.H.map e.inv q ∘ γ from funext hγe]
  exact he.comp hγ

end Main

end Stacks.ArtinSchreier

end
