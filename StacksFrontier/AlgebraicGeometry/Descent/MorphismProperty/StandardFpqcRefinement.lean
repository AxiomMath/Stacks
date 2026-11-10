module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.RingHomPi
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.StandardRefinement
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Standard fpqc refinements over an affine open

An fpqc covering of a scheme gives, over any affine open `V` of the target, a finite family of
affine schemes which are flat over `V` and jointly cover it, each realized as an affine open
subscheme of a member of the covering. The product of their coordinate rings is then
faithfully flat over the coordinate ring of `V`.

## Main results

* `AlgebraicGeometry.exists_comap_appTop_eq` — a jointly surjective family of morphisms of
  affine schemes is jointly surjective on prime spectra of global sections.
* `AlgebraicGeometry.exists_standardFpqcCovering_over_affineOpen` — the covering members, their
  open immersions into members of the given covering, and the faithfully flat product map.

## Implementation notes

The morphisms into the members `Uᵢ` of the covering and their compatibility with the maps to
the ambient scheme are stated with the fibre product `V ×[S] Uᵢ` written out rather than as a
component of the pulled back pre-zero-hypercover. The two agree definitionally, but only the
written form lets instance search and congruence see the composition, so the refinement
component is ascribed at that type once and used everywhere through that ascription.

## References

* [Stacks Project, Tag 022E](https://stacks.math.columbia.edu/tag/022E)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- A jointly surjective family of morphisms of affine schemes induces a family of ring maps on
global sections which is jointly surjective on prime spectra. -/
public lemma exists_comap_appTop_eq {R : Scheme.{u}} [IsAffine R] {I : Type v}
    {T : I → Scheme.{u}} [∀ i, IsAffine (T i)] (g : ∀ i, T i ⟶ R)
    (hg : (⋃ i, Set.range (g i)) = Set.univ) (p : PrimeSpectrum Γ(R, ⊤)) :
    ∃ (i : I) (q : PrimeSpectrum Γ(T i, ⊤)), PrimeSpectrum.comap ((g i).appTop.hom) q = p := by
  have hx : R.isoSpec.inv.base p ∈ ⋃ i, Set.range (g i) := hg ▸ trivial
  obtain ⟨i, z, hz⟩ := Set.mem_iUnion.mp hx
  refine ⟨i, (T i).isoSpec.hom.base z, ?_⟩
  have hnat := congrArg (fun k : Scheme.Hom (T i) (Spec Γ(R, ⊤)) ↦ k.base z)
    (Scheme.isoSpec_hom_naturality (g i))
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, Scheme.Hom.comp_apply,
    Spec.map_base] at hnat
  change PrimeSpectrum.comap ((g i).appTop.hom) ((T i).isoSpec.hom.base z) =
    R.isoSpec.hom.base ((g i).base z) at hnat
  rw [hz] at hnat
  have hp : R.isoSpec.hom.base (R.isoSpec.inv.base p) = p := by
    change ((R.isoSpec.inv ≫ R.isoSpec.hom) p) = p
    rw [R.isoSpec.inv_hom_id]
    rfl
  rwa [hp] at hnat

/-- An fpqc covering of a scheme has,
over every affine open `V` of its target, a standard fpqc covering of `V` by affine open
subschemes of members of the covering, compatibly with the maps to the ambient scheme.  The
induced map from the sections of `V` to the finite product of the coordinate rings of the
covering members is faithfully flat. -/
@[sga "3 VIB 11.9.1" "partial"]
public theorem exists_standardFpqcCovering_over_affineOpen {S : Scheme.{u}}
    (U : PreZeroHypercover.{v} S) (hU : U.presieve₀ ∈ Scheme.fpqcPrecoverage S)
    (V : S.affineOpens) :
    ∃ (n : ℕ) (A : Fin n → CommRingCat.{u}) (g : ∀ k, Spec (A k) ⟶ V.1.toScheme)
      (a : Fin n → U.I₀) (t : ∀ k, Spec (A k) ⟶ U.X (a k)),
      (∀ k, Flat (g k)) ∧
      (⋃ k, Set.range (g k)) = Set.univ ∧
      (∀ k, IsOpenImmersion (t k)) ∧
      (∀ k, t k ≫ U.f (a k) = g k ≫ V.1.ι) ∧
      (RingHom.pi fun k ↦ (g k).appTop.hom).FaithfullyFlat := by
  classical
  have hVaff : IsAffine (V.1.toScheme) := V.2
  obtain ⟨W, refinement, hWfin, -, hWopen⟩ :=
    exists_finite_affineCover_flat_refinement_over_affineOpen U hU V
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin W.I₀
  have hjs : Scheme.JointlySurjective (Scheme.precoverage (@Flat.{u})) :=
    @AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage.{u} (@Flat.{u})
  have hcov : (⋃ k : Fin n, Set.range (W.f (e.symm k))) = Set.univ :=
    (W.reindex e.symm).cover.iUnion_range
  have hhopen : ∀ k : Fin n, @IsOpenImmersion (Spec (W.X (e.symm k)))
      (pullback V.1.ι (U.f (refinement.s₀ (e.symm k)))) (refinement.h₀ (e.symm k)) :=
    fun k ↦ hWopen (e.symm k)
  have hheq : ∀ k : Fin n,
      (refinement.h₀ (e.symm k) :
          Spec (W.X (e.symm k)) ⟶ pullback V.1.ι (U.f (refinement.s₀ (e.symm k)))) ≫
        pullback.fst V.1.ι (U.f (refinement.s₀ (e.symm k))) = W.f (e.symm k) :=
    fun k ↦ refinement.w₀ (e.symm k)
  refine ⟨n, fun k ↦ W.X (e.symm k), fun k ↦ W.f (e.symm k),
    fun k ↦ refinement.s₀ (e.symm k),
    fun k ↦ (refinement.h₀ (e.symm k) :
        Spec (W.X (e.symm k)) ⟶ pullback V.1.ι (U.f (refinement.s₀ (e.symm k)))) ≫
      pullback.snd V.1.ι (U.f (refinement.s₀ (e.symm k))),
    fun k ↦ W.map_prop _, hcov, fun k ↦ ?_, fun k ↦ ?_, ?_⟩
  · exact @IsOpenImmersion.comp (Spec (W.X (e.symm k)))
      (pullback V.1.ι (U.f (refinement.s₀ (e.symm k)))) (U.X (refinement.s₀ (e.symm k)))
      (refinement.h₀ (e.symm k)) (pullback.snd V.1.ι (U.f (refinement.s₀ (e.symm k))))
      (hhopen k) inferInstance
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun m ↦ (refinement.h₀ (e.symm k) :
          Spec (W.X (e.symm k)) ⟶ pullback V.1.ι (U.f (refinement.s₀ (e.symm k)))) ≫ m)
          pullback.condition.symm).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun m ↦ m ≫ V.1.ι) (hheq k))))
  · have hflat : ∀ k : Fin n, ((W.f (e.symm k)).appTop.hom).Flat := fun k ↦ by
      have : Flat (W.f (e.symm k)) := W.map_prop _
      exact Scheme.Hom.flat_appTop (W.f (e.symm k))
    exact RingHom.FaithfullyFlat.pi
      (S := fun k ↦ (Γ(Spec (W.X (e.symm k)), ⊤) : Type u))
      (fun k ↦ (W.f (e.symm k)).appTop.hom) hflat
      (exists_comap_appTop_eq (fun k ↦ W.f (e.symm k)) hcov)

end AlgebraicGeometry
