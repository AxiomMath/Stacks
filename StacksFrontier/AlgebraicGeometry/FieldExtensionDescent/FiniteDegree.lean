module

public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.NormAmple.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descent of ampleness and of quasi-projectivity along a finite base change

Let `k` be a field and `X` a scheme over `k`. For a nonzero finite `k`-algebra `A`, the projection
`Spec A ×_{Spec k} X → X` is finite locally free of positive rank `Module.finrank k A`, so an ample
invertible sheaf on `Spec A ×_{Spec k} X` gives one on `X` ([Stacks, Tag 0BD4]). For a finite field
extension `K/k` this is the descent of ampleness ([Stacks, Tag 0BDC]) and of quasi-projectivity
([Stacks, Tag 0BDE]) from `X_K` to `X`.

## Main results

* `Module.IsFiniteLocallyFreeOfRank.of_basis'`: a module with a basis indexed by `Fin n` is
  finite locally free of rank `n`, with the module in a universe unrelated to that of the ring.
* `AlgebraicGeometry.isFiniteLocallyFreeOfRank_SpecMap_algebraMap`: for a field `k` and a finite
  `k`-algebra `A`, the morphism `Spec A → Spec k` is finite locally free of rank
  `Module.finrank k A`.
* `AlgebraicGeometry.exists_isAmple_of_finite_base_change`: if `Spec A ×_{Spec k} X` carries an
  ample invertible sheaf for some nonzero finite `k`-algebra `A`, then so does `X`.
* `AlgebraicGeometry.isQuasiProjective_of_finite_fieldExtension`: if `X_K` is quasi-projective
  over `K` and `K/k` is a finite field extension, then `X` is quasi-projective over `k`.

## References

* [Stacks Project, Tag 0BDC](https://stacks.math.columbia.edu/tag/0BDC)
* [Stacks Project, Tag 0BDE](https://stacks.math.columbia.edu/tag/0BDE)
* [Stacks Project, Tag 0BD4](https://stacks.math.columbia.edu/tag/0BD4)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 00FV](https://stacks.math.columbia.edu/tag/00FV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-- A module with a basis indexed by `Fin n` is finite locally free of rank `n`, for a module in a
universe unrelated to that of the ring. -/
public theorem Module.IsFiniteLocallyFreeOfRank.of_basis' {R : Type u} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] {n : ℕ} (b : Module.Basis (Fin n) R M) :
    Module.IsFiniteLocallyFreeOfRank R M n := by
  classical
  refine ⟨PUnit.{u + 1}, fun _ => 1, by simp, fun _ => ?_⟩
  let : Algebra R (Localization.Away (1 : R)) :=
    @OreLocalization.instAlgebra R _ (Submonoid.powers (1 : R)) _ R _ (Algebra.id R)
  have : IsLocalization (Submonoid.powers (1 : R)) (Localization.Away (1 : R)) :=
    Localization.isLocalization (R := R) (M := Submonoid.powers 1)
  exact ⟨b.ofIsLocalizedModule (Localization.Away (1 : R)) (Submonoid.powers (1 : R))
    (LocalizedModule.mkLinearMap (Submonoid.powers (1 : R)) M)⟩

namespace AlgebraicGeometry

/-- The spectrum of a finite algebra over a field is finite locally free over the spectrum of the
field, of rank its dimension. -/
public theorem isFiniteLocallyFreeOfRank_SpecMap_algebraMap (k A : Type u) [Field k] [CommRing A]
    [Algebra k A] [Module.Finite k A] :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) (Module.finrank k A) := by
  classical
  set φ : CommRingCat.of k ⟶ CommRingCat.of A := CommRingCat.ofHom (algebraMap k A) with hφ
  let alg : Algebra k ↑Γ(Spec (CommRingCat.of A), ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Spec.map φ).appTop).hom.toAlgebra
  have hcomm : ∀ r : k, (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (algebraMap k A r) =
      algebraMap k ↑Γ(Spec (CommRingCat.of A), ⊤) r := fun r => by
    have h := congrArg (fun g : CommRingCat.of k ⟶ Γ(Spec (CommRingCat.of A), ⊤) => g.hom r)
      (Scheme.ΓSpecIso_inv_naturality φ)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hφ,
      CommRingCat.hom_ofHom] at h
    exact h
  let e : A ≃ₗ[k] ↑Γ(Spec (CommRingCat.of A), ⊤) :=
    { ((Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv).symm.toAddEquiv with
      map_smul' := fun r x => by
        change (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (r • x) =
          r • (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom x
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, hcomm] }
  exact (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff _ _).mpr ⟨inferInstance,
    (Stacks.Morphisms.sheafOfModules_isFiniteLocallyFreeOfRank_iff_module
      (R := CommRingCat.of k) (Spec.map φ) (Module.finrank k A)).mpr
      (.of_basis' ((Module.finBasis k A).map e))⟩

/-- If the base change of a scheme over a field `k` along the spectrum of a nonzero finite
`k`-algebra `A` carries an ample invertible sheaf, then so does the scheme itself. -/
public theorem exists_isAmple_of_finite_base_change (k A : Type u) [Field k] [CommRing A]
    [Nontrivial A] [Algebra k A] [Module.Finite k A] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (h : ∃ L : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) f).Modules,
        ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible
          (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) f).toRingedSpace.presheaf
          (structureSheafRing
            (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) f).toRingedSpace).property L,
          Scheme.Modules.IsAmple
            (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) f) L) :
    ∃ M : X.Modules, ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible
        X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property M,
      Scheme.Modules.IsAmple X M := by
  obtain ⟨L, hL, hamp⟩ := h
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) (Module.finrank k A) :=
    isFiniteLocallyFreeOfRank_SpecMap_algebraMap k A
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A))) f) (Module.finrank k A) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
      (f := Spec.map (CommRingCat.ofHom (algebraMap k A))) (d := Module.finrank k A)
      (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) f)
  exact Stacks.Divisors.exists_isAmple_of_isFiniteLocallyFreeOfRank
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A))) f) (Module.finrank k A)
    Module.finrank_pos L hamp

/-- If the base change of a scheme over a field `k` to a finite extension field `K` is
quasi-projective over `K`, then the scheme is quasi-projective over `k`. -/
@[ega "II 6.6.4" "special case", ega "II 6.6.5" "more general"]
public theorem isQuasiProjective_of_finite_fieldExtension (k K : Type u) [Field k] [Field K]
    [Algebra k K] [Module.Finite k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (h : IsQuasiProjective (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    IsQuasiProjective f :=
  isQuasiProjective_of_fieldExtension_of_exists_isAmple_comm k K f
    (exists_isAmple_of_finite_base_change k K f) h

end AlgebraicGeometry

end
