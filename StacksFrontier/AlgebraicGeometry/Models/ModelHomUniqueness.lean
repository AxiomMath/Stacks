module

public import StacksFrontier.AlgebraicGeometry.Models.BaseChange
public import StacksFrontier.AlgebraicGeometry.ChowNoetherian.Dominance
public import StacksFrontier.AlgebraicGeometry.Topologies.V.PhVFlatteningModification
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Morphisms of models into a separated model are unique

Let `R` be a discrete valuation ring with fraction field `K`, let `V` be a `K`-scheme and let
`X`, `X'` be models of `V` (Section 0C2R of the Stacks project). If `X' ⟶ Spec R` is separated,
then there is at most one morphism of models `X ⟶ X'`. This is the uniqueness half of
[Stacks, Tag 0E97], where `X` and `X'` are stable families of curves over `R`, hence proper.

## Main results

* `Stacks.Models.IsModelHom.eq_of_isModel_of_isSeparated`: two morphisms of models from a model
  into a model which is separated over `R` are equal.
* `Stacks.Models.subsingleton_isModelHom_iso`: there is at most one isomorphism of models
  between two models, the target being separated over `R`.
* `Stacks.Models.IsModelHom.of_comp_eq`: a morphism over `R` compatible with morphisms of models
  from a common model is a morphism of models.
* `Stacks.Models.existsUnique_isModelHom_iso_of_comp_eq`: an isomorphism over `R` compatible with
  morphisms of models from a common model is the unique isomorphism of models.

## Implementation notes

The generic fibre `X_K ⟶ X` is scheme-theoretically dominant: it is the base change, along the
flat structure morphism `X ⟶ Spec R`, of the quasi-compact scheme-theoretically dominant
morphism `Spec K ⟶ Spec R`. Two morphisms of models agree on `X_K`, since they induce the same
morphism `V ≅ X_K ⟶ X'_K`, and a scheme-theoretically dominant morphism is an epimorphism
against a separated target (`AlgebraicGeometry.eq_of_comp_isSchemeTheoreticallyDominant`).

## References

* [Stacks Project, Section 0C2R](https://stacks.math.columbia.edu/tag/0C2R)
* [Stacks Project, Tag 0E97](https://stacks.math.columbia.edu/tag/0E97)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Stacks.Models

universe u

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDiscreteValuationRing R] in
/-- The generic fibre `X_K ⟶ X` of a flat `R`-scheme `X` is scheme-theoretically dominant. -/
@[sga "3 VIII 7.1" "uniqueness"]
theorem isSchemeTheoreticallyDominant_genericFiber_fst {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] :
    IsSchemeTheoreticallyDominant (pullback.fst p (genericPointInclusion R K)) := by
  have : IsSchemeTheoreticallyDominant (genericPointInclusion R K) :=
    isSchemeTheoreticallyDominant_Spec_map_algebraMap_of_isFractionRing R K
  infer_instance

omit [IsDiscreteValuationRing R] in
/-- **Morphisms of models into a separated model are unique.** If `X` is a model of `V` and
`X' ⟶ Spec R` is separated, two morphisms of models `X ⟶ X'` for `V` are equal. -/
theorem IsModelHom.eq_of_isModel_of_isSeparated {V X X' : Scheme.{u}}
    {v : V ⟶ Spec (CommRingCat.of K)} {p : X ⟶ Spec (CommRingCat.of R)}
    {p' : X' ⟶ Spec (CommRingCat.of R)} {e : V ≅ pullback p (genericPointInclusion R K)}
    {e' : V ≅ pullback p' (genericPointInclusion R K)} (hX : IsModel v p e) [IsSeparated p']
    {φ ψ : X ⟶ X'} (hφ : IsModelHom p p' e e' φ) (hψ : IsModelHom p p' e e' ψ) : φ = ψ := by
  obtain ⟨h₁, h₂⟩ := hφ
  obtain ⟨h₃, h₄⟩ := hψ
  have : Flat p := hX.1
  have := isSchemeTheoreticallyDominant_genericFiber_fst (K := K) p
  have hg : genericFiberMapOfHomOver (K := K) p p' φ h₁ = genericFiberMapOfHomOver p p' ψ h₃ := by
    rw [← cancel_epi e.hom, h₂, h₄]
  refine eq_of_comp_isSchemeTheoreticallyDominant (pullback.fst p (genericPointInclusion R K))
    φ ψ p' (h₁.trans h₃.symm) ?_
  simpa using congr($hg ≫ pullback.fst p' (genericPointInclusion R K))

omit [IsDiscreteValuationRing R] in
/-- **There is at most one isomorphism of models** `X ≅ X'` for `V` when `X'` is separated over
`R`: the uniqueness half of Stacks 0E97. -/
theorem subsingleton_isModelHom_iso {V X X' : Scheme.{u}}
    {v : V ⟶ Spec (CommRingCat.of K)} {p : X ⟶ Spec (CommRingCat.of R)}
    {p' : X' ⟶ Spec (CommRingCat.of R)} {e : V ≅ pullback p (genericPointInclusion R K)}
    {e' : V ≅ pullback p' (genericPointInclusion R K)} (hX : IsModel v p e) [IsSeparated p'] :
    {f : X ≅ X' | IsModelHom p p' e e' f.hom}.Subsingleton :=
  fun _ hf _ hg => Iso.ext (hf.eq_of_isModel_of_isSeparated hX hg)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- **A morphism over `R` compatible with morphisms of models from a common model is a morphism of
models.** If `c : W ⟶ X` and `c' : W ⟶ X'` are morphisms of models for `V` and `φ : X ⟶ X'` is a
morphism over `R` with `c ≫ φ = c'`, then `φ` is a morphism of models. -/
theorem IsModelHom.of_comp_eq {V W X X' : Scheme.{u}} {pW : W ⟶ Spec (CommRingCat.of R)}
    {p : X ⟶ Spec (CommRingCat.of R)} {p' : X' ⟶ Spec (CommRingCat.of R)}
    {eW : V ≅ pullback pW (genericPointInclusion R K)}
    {e : V ≅ pullback p (genericPointInclusion R K)}
    {e' : V ≅ pullback p' (genericPointInclusion R K)} {c : W ⟶ X} {c' : W ⟶ X'}
    (hc : IsModelHom pW p eW e c) (hc' : IsModelHom pW p' eW e' c') {φ : X ⟶ X'}
    (hφ : φ ≫ p' = p) (hcomp : c ≫ φ = c') : IsModelHom p p' e e' φ := by
  obtain ⟨h₁, h₂⟩ := hc
  obtain ⟨h₃, h₄⟩ := hc'
  refine ⟨hφ, ?_⟩
  have hmap : genericFiberMapOfHomOver (K := K) pW p c h₁ ≫ genericFiberMapOfHomOver p p' φ hφ =
      genericFiberMapOfHomOver pW p' c' h₃ := by
    subst hcomp
    apply pullback.hom_ext <;> simp [genericFiberMapOfHomOver, pullback.map]
  rw [← h₂, Category.assoc, hmap, h₄]

omit [IsDiscreteValuationRing R] in
/-- **An isomorphism over `R` compatible with morphisms of models from a common model is the
unique isomorphism of models.** Let `c : W ⟶ X` and `c' : W ⟶ X'` be morphisms of models for `V`,
with `X` a model and `X' ⟶ Spec R` separated. If `φ : X ≅ X'` is an isomorphism over `R` with
`c ≫ φ = c'`, then `φ` is an isomorphism of models, and it is the only one. This is the last step
of the proof of Stacks 0E97. -/
theorem existsUnique_isModelHom_iso_of_comp_eq {V W X X' : Scheme.{u}}
    {v : V ⟶ Spec (CommRingCat.of K)} {pW : W ⟶ Spec (CommRingCat.of R)}
    {p : X ⟶ Spec (CommRingCat.of R)} {p' : X' ⟶ Spec (CommRingCat.of R)}
    {eW : V ≅ pullback pW (genericPointInclusion R K)}
    {e : V ≅ pullback p (genericPointInclusion R K)}
    {e' : V ≅ pullback p' (genericPointInclusion R K)} (hX : IsModel v p e) [IsSeparated p']
    {c : W ⟶ X} {c' : W ⟶ X'} (hc : IsModelHom pW p eW e c) (hc' : IsModelHom pW p' eW e' c')
    (φ : X ≅ X') (hφ : φ.hom ≫ p' = p) (hcomp : c ≫ φ.hom = c') :
    ∃! f : X ≅ X', IsModelHom p p' e e' f.hom :=
  existsUnique_of_exists_of_unique ⟨φ, hc.of_comp_eq hc' hφ hcomp⟩ fun _ _ hf hg =>
    subsingleton_isModelHom_iso hX hf hg

/-- Morphisms of models into a model which is separated over `R` are unique, bundled. -/
instance Model.subsingleton_hom {V : Scheme.{u}} {v : V ⟶ Spec (CommRingCat.of K)}
    (M N : Model R v) [IsSeparated N.p] : Subsingleton (M ⟶ N) :=
  ⟨fun f g => Model.hom_ext (f.isModelHom.eq_of_isModel_of_isSeparated M.isModel g.isModelHom)⟩

end Stacks.Models

end
