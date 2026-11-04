module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricComponents
public import StacksFrontier.AlgebraicGeometry.FibreDimension.IntegralReduction
public import StacksCore.Tactic.StacksAttribute

/-!
# The geometric genus is insensitive to nilpotents

Let `k` be a field and let `X` be a proper scheme over `k`.  The geometric genus `g_geom(X/k)`
is computed from the one-dimensional irreducible components of the base change `X_{k̄}`, each
taken with its reduced closed subscheme structure, and so it only sees the underlying topology
of `X_{k̄}` together with the reduced structures it carries.  Consequently a closed subscheme of
`X` whose underlying set is all of `X` has the same geometric genus as `X`; in particular the
reduction `X_red` does.

## Main results

* `AlgebraicGeometry.geometricGenus_eq_of_surjective_isClosedImmersion`: a surjective closed
  immersion of proper schemes over a field preserves the geometric genus.
* `AlgebraicGeometry.geometricGenus_reduction`: the geometric genus of a proper scheme over a
  field equals the geometric genus of its reduction.

## References

* [Stacks Project, Tag 0CE2](https://stacks.math.columbia.edu/tag/0CE2)
* [Stacks Project, Tag 0CE0](https://stacks.math.columbia.edu/tag/0CE0)
* [Stacks Project, Tag 01J4](https://stacks.math.columbia.edu/tag/01J4)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
* [Stacks Project, Tag 07TD](https://stacks.math.columbia.edu/tag/07TD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v u

namespace AlgebraicGeometry

/-! ### Transport of a reduced closed subscheme along a closed immersion -/

/-- Let `f : A ⟶ Y` be a closed immersion, let `Z ⊆ A` be closed and let `W ⊆ Y` be its image.
The reduced closed subschemes of `A` and of `Y` cut out by `Z` and by `W` are isomorphic over
`Y`. -/
private alias exists_subschemeIso_image_eq := exists_subschemeIso_of_image_eq

/-! ### Normalization and isomorphisms over a field -/

/-- Isomorphic proper schemes over a field have normalizations of the same genus. -/
private alias genus_normalizationOverField_eq_isIso := genus_normalizationOverField_eq_of_isIso

/-! ### The contribution of an irreducible component -/

/-- The contribution of an irreducible component `C` of `X` to the geometric genus: the genus of
the normalization of `C` with its reduced structure when `C` has dimension one, and zero
otherwise. -/
private abbrev contribution (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] (C : irreducibleComponents X) : ℕ :=
  if topologicalKrullDim (irreducibleComponentIdeal C).subscheme = 1 then
    genus (normalizationOverField k ((irreducibleComponentIdeal C).subschemeι ≫ p) ≫
      ((irreducibleComponentIdeal C).subschemeι ≫ p))
  else 0

/-- A closed immersion matches the contribution of an irreducible component of its source with
the contribution of the corresponding irreducible component of its target. -/
private theorem contribution_image {k : Type u} [Field k] {A Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of k)) [IsProper p] (f : A ⟶ Y) [IsClosedImmersion f]
    (D : irreducibleComponents A) (E : irreducibleComponents Y)
    (hE : f.base '' (D : Set A) = E) :
    contribution k (f ≫ p) D = contribution k p E := by
  obtain ⟨e, he⟩ := exists_subschemeIso_image_eq f
    ⟨D.1, isClosed_of_mem_irreducibleComponents _ D.2⟩
    ⟨E.1, isClosed_of_mem_irreducibleComponents _ E.2⟩ hE
  have hd := IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph
  dsimp [contribution]
  rw [hd]
  split_ifs with h
  · exact genus_normalizationOverField_eq_isIso _ _ e.hom (by simp [← Category.assoc, he])
  · rfl

/-! ### The bijection of irreducible components under a homeomorphism -/

/-- A homeomorphism carries the irreducible components of its source bijectively onto those of
its target, a component going to its image. -/
private def componentsEquivOfHomeomorph {A : Type u} {B : Type v} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) : irreducibleComponents A ≃ irreducibleComponents B :=
  (irreducibleComponentsEquivOfIsPreirreducibleFiber e e.continuous e.isOpenMap
    (fun y ↦ by
      have hfiber : e ⁻¹' ({y} : Set B) = {e.symm y} := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact ⟨fun h ↦ by rw [← h, e.symm_apply_apply],
          fun h ↦ by rw [h, e.apply_symm_apply]⟩
      rw [hfiber]
      exact isPreirreducible_singleton) e.surjective).symm.toEquiv

private theorem componentsEquivOfHomeomorph_coe {A : Type u} {B : Type v} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) (Z : irreducibleComponents A) :
    (componentsEquivOfHomeomorph e Z).1 = e '' Z.1 := rfl

/-- The contributions of the irreducible components of the source and of the target of a
surjective closed immersion have the same sum. -/
private theorem sum_contribution_of_surjective_isClosedImmersion
    {k : Type u} [Field k] {A Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of k)) [IsProper p] (f : A ⟶ Y) [IsClosedImmersion f] [Surjective f]
    [Fintype (irreducibleComponents A)] [Fintype (irreducibleComponents Y)] :
    ∑ D : irreducibleComponents A, contribution k (f ≫ p) D =
      ∑ E : irreducibleComponents Y, contribution k p E := by
  let e := f.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective f.surjective
  refine Fintype.sum_equiv (componentsEquivOfHomeomorph e) _ _ fun D ↦ ?_
  exact contribution_image p f D _ (componentsEquivOfHomeomorph_coe e D).symm

/-! ### Invariance of the geometric genus -/

/-- **A surjective closed immersion preserves the geometric genus.** If `f : X' ⟶ X` is a closed
immersion whose underlying map is onto and `X` is proper over the field `k`, then `X'` and `X`
have the same geometric genus over `k`. -/
public theorem geometricGenus_eq_of_surjective_isClosedImmersion {k : Type u} [Field k]
    {X' X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (f : X' ⟶ X) [IsClosedImmersion f] [Surjective f] :
    geometricGenus k (f ≫ g) = geometricGenus k g := by
  classical
  let a := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let p := pullback.snd g a
  let q := pullback.snd (f ≫ g) a
  let b := pullback.lift (pullback.fst (f ≫ g) a ≫ f) q
    (by dsimp only [q]; rw [Category.assoc, pullback.condition])
  have hb : b ≫ p = q := pullback.lift_snd ..
  have hpb : IsPullback (pullback.fst (f ≫ g) a) b f (pullback.fst g a) :=
    IsPullback.of_bot (v₂₁ := p) (v₂₂ := g) (by rw [hb]; exact IsPullback.of_hasPullback (f ≫ g) a)
      (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback g a)
  have : IsClosedImmersion b := MorphismProperty.of_isPullback hpb inferInstance
  have : Surjective b := MorphismProperty.of_isPullback hpb inferInstance
  have : IsNoetherian (pullback (C := Scheme.{u}) g a) := {}
  have : IsNoetherian (pullback (C := Scheme.{u}) (f ≫ g) a) := {}
  have : Finite (irreducibleComponents (pullback (C := Scheme.{u}) g a)) :=
    finite_irreducibleComponents_of_isNoetherian.to_subtype
  have : Finite (irreducibleComponents (pullback (C := Scheme.{u}) (f ≫ g) a)) :=
    finite_irreducibleComponents_of_isNoetherian.to_subtype
  let : Fintype (irreducibleComponents (pullback (C := Scheme.{u}) g a)) := Fintype.ofFinite _
  let : Fintype (irreducibleComponents (pullback (C := Scheme.{u}) (f ≫ g) a)) :=
    Fintype.ofFinite _
  have H := sum_contribution_of_surjective_isClosedImmersion p b
  simp only [hb] at H
  exact H

/-- **The geometric genus does not see nilpotents.** Let `k` be a field and let `X` be a proper
scheme over `k`.  Then `g_geom(X/k) = g_geom(X_red/k)`: the geometric genus is unchanged by
passing to the reduction.

This is clause (1) of [Stacks, Tag 0CE2], which is stated there for `X` of dimension at most
one. -/
public theorem geometricGenus_reduction {k : Type u} [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [IsProper g] :
    geometricGenus k g = geometricGenus k (X.reductionι ≫ g) := by
  have : Surjective X.reductionι := ⟨X.surjective_reductionι⟩
  exact (geometricGenus_eq_of_surjective_isClosedImmersion g X.reductionι).symm

end AlgebraicGeometry

end
