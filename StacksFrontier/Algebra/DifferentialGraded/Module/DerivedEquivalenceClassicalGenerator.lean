module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceBimodule
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomCoproducts
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorLinear
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleCompact
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects

/-! # Generation of the compact objects gives a derived equivalence

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let `N`
be a differential graded `(A, B)`-bimodule. [Stacks, Tag 09S7] proves that `- ⊗_A^𝐋 N` is an
equivalence `D(A, d) ⥤ D(B, d)` under three hypotheses, the second of which is that an object of
`D(B, d)` receiving only zero maps from the translates of `N` is zero — that is, that the class of
`N` *weakly* generates `D(B, d)`.

[Stacks, Tag 09SS] makes two assertions about that hypothesis, and both are proved here.

The first is that it may be replaced by the requirement that `N` be a **classical generator for
`D_{compact}(B, d)`**: that the triangulated envelope of the class of `N` is exactly the
subcategory of compact objects. The mechanism is the one behind [Stacks, Tag 09SR]: an object
whose envelope contains a weak generator is itself a weak generator, and the class of the regular
module `B` is both compact (`DifferentialGradedModule.isCompactObject_q_regularModule`) and a
weak generator of `D(B, d)`
(`DifferentialGradedModule.isWeakTriangulatedGenerator_q_regularModule`), so it lies in the
envelope of `N` as soon as that envelope is the whole of `D_{compact}(B, d)`.

The second is that, if `RHom(N, B)` is known to be a compact object of `D(A, d)`, it is enough
that `N` be a **weak generator for `D_{compact}(B, d)`** — that a *compact* object of `D(B, d)`
receiving only zero maps from the translates of `N` is zero. That hypothesis is weaker than both
the original condition and the classical generation of the first assertion. The mechanism is the
counit `Φ(Ψ(B)) ⟶ B` of the adjunction `Φ = - ⊗_A^𝐋 N ⊣ Ψ = RHom(N, -)` of [Stacks, Tag 09LT]:
its cone is compact, because `Ψ(B)` is compact by hypothesis and `Φ` preserves compact objects,
and `Ψ` kills that cone, because the unit of the adjunction is invertible by
[Stacks, Tag 09R9]; so the weak generation of the compact objects makes the cone vanish, which
identifies `B` with `Φ(Ψ(B))` and upgrades the hypothesis to weak generation of all of `D(B, d)`.

## Main results

* `CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_singleton_of_prop_triangEnvelope`:
  if the triangulated envelope of a single object `N` contains a weak generator, then `N` is a
  weak generator. The left orthogonal of the translates of a fixed object is triangulated and
  closed under retracts, so it contains the envelope of `N` as soon as it contains `N`.
* `CategoryTheory.isCompactObject_obj_of_adjunction`: the left adjoint of a right adjoint which
  commutes with direct sums preserves compact objects.
* `isEquivalence_derivedTensorFunctor_of_triangEnvelope_eq_isCompactObject`, in the namespace
  `DifferentialGraded.Bimodule`: **Stacks 09SS**, the first of its two assertions — Tag 09S7 with
  hypothesis (2) replaced by classical generation of the compact objects of `D(B, d)` by the class
  of `N`.
* `isEquivalence_derivedTensorFunctor_of_isWeakTriangulatedGenerator_isCompactObject`, again in
  `DifferentialGraded.Bimodule`:
  **Stacks 09SS**, the second assertion — Tag 09S7 with hypothesis (2) replaced by weak generation
  of the compact objects of `D(B, d)` by the class of `N`, under the additional hypothesis that
  `RHom(N, B)` is a compact object of `D(A, d)`.
* `DifferentialGraded.Bimodule.linear_derivedTensorFunctor_of_isEquivalence`: **Stacks 09SS**, the
  `R`-linearity of that equivalence and of its quasi-inverse, which completes the conclusion of
  Tag 09S7 that both assertions transport.
* `isEquivalence_linear_derivedTensorFunctor_of_generator_isCompactObject`, again in
  `DifferentialGraded.Bimodule`: **Stacks 09SS** in full — both assertions together, each
  concluding that `- ⊗_A^𝐋 N` is an exact `R`-linear equivalence with `R`-linear quasi-inverse.

## Implementation notes

*The proof of the second assertion is not the source's.* The source omits it — "We omit the proof;
we will add it here if we ever need it in the Stacks project" — but states the implication, which
is a definite one, so it is proved here from the material the chapter already has. The route is
the one sketched above and spelled out at the statement; what makes it elementary, rather than a
question of Bousfield localization, is that only one object has to be shown to lie in the image
of `Φ`, namely the regular module, and that the cone of the counit there is *compact*, which is
exactly what the extra hypothesis on `RHom(N, B)` buys. The two inputs that carry the compactness
are `DifferentialGraded.Bimodule.preservesColimitsOfShape_discrete_derivedHomFunctor` — `Ψ`
commutes with direct sums, by hypothesis (1) — and its formal converse
`CategoryTheory.isCompactObject_obj_of_adjunction`, which turns that into the preservation of
compact objects by `Φ`.

*Why Tag 09SR is not cited directly.* The source deduces the replacement from Tag 09SR, which is
proved in `StacksFrontier/CategoryTheory/Triangulated/CompactObjects.lean` as
`isWeakTriangulatedGenerator_iff_triangEnvelope_eq_isCompactObject_and_isCompactlyGenerated`.
That statement is formulated for a category whose coproducts are indexed by its *morphism*
universe, and `D(A, d)` is not such a category: its objects live in `Type (u + 1)` and so do its
morphisms, while the coproducts available
(`DifferentialGradedModule.hasCoproducts_derivedCategory`) and the compactness used throughout
this chapter are indexed by `Type u`. So Tag 09SR cannot be instantiated at `D(B, d)`, and the
implication actually needed — the `(1) ⇒ (2)` half of it — is proved here instead, in the form
`CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_singleton_of_prop_triangEnvelope`,
which mentions no coproducts and no compactness and is therefore universe-insensitive.

*"Classical generator for `D_{compact}(B, d)`".* Mathlib's
`CategoryTheory.ObjectProperty.IsClassicalTriangulatedGenerator` asks for `triangEnvelope = ⊤`,
i.e. classical generation of the *whole* category; what is wanted here is classical generation of
the full subcategory of compact objects, which is the equation
`(ObjectProperty.singleton N).triangEnvelope = IsCompactObject` used by Tag 09SR and repeated
below. Only one consequence of that equation is used, namely that the class of the regular module
lies in the envelope, so the statement below is a little stronger than the source's.

*What the conclusion is.* As in
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedEquivalenceBimodule.lean`, the functor
`- ⊗_A^𝐋 N` is exact before any hypothesis (Tags 09LR and 09LS), and it is `R`-linear before any
hypothesis too, by the global instance
`DifferentialGraded.Bimodule.derivedTensorFunctor_linear` (Tag 09S7); so the conclusion below is
the source's `R`-linear equivalence of triangulated categories, the `R`-linearity of both halves
being recorded separately as
`DifferentialGraded.Bimodule.linear_derivedTensorFunctor_of_isEquivalence`.

## References

* [Stacks Project, Tag 09SS](https://stacks.math.columbia.edu/tag/09SS), the remark proved here.
* [Stacks Project, Tag 09S7](https://stacks.math.columbia.edu/tag/09S7) for the lemma being
  restated, [Tag 09SR](https://stacks.math.columbia.edu/tag/09SR) for the comparison of weak and
  classical generation and [Tag 09SK](https://stacks.math.columbia.edu/tag/09SK) for the
  orthogonality argument reproduced below.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

universe u

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **An object whose triangulated envelope contains a weak generator is a weak generator.** Let
`N` and `E` be objects of a triangulated category, let the class of `E` be a weak generator
([Stacks, Tag 09SJ](3)) and let `E` lie in the triangulated envelope of the class of `N`. Then the
class of `N` is a weak generator too.

Let `K` receive only zero maps from the translates of `N`. The objects admitting only zero maps
*into* the translates of `K` form the left orthogonal of the shift closure of the class of `K`,
which is a triangulated object property closed under retracts, so by
`CategoryTheory.ObjectProperty.triangEnvelope_le_iff` it contains the whole envelope of `N` once
it contains `N`. In particular it contains `E`, and then `E` being a weak generator forces `K` to
be a zero object.

This is the mechanism of the `(1) ⇒ (2)` half of [Stacks, Tag 09SR], with the compact generating
family of that proposition replaced by the single object `E`; unlike Tag 09SR it mentions neither
coproducts nor compact objects. -/
theorem isWeakTriangulatedGenerator_singleton_of_prop_triangEnvelope {N E : C}
    (hE : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator)
    (hN : (ObjectProperty.singleton N).triangEnvelope E) :
    (ObjectProperty.singleton N).IsWeakTriangulatedGenerator := by
  rw [isWeakTriangulatedGenerator_singleton_iff_forall_hom_eq_zero] at hE ⊢
  intro K hK
  refine hE K ?_
  have hret : ((ObjectProperty.singleton K).shiftClosure ℤ).leftOrthogonal.IsStableUnderRetracts :=
    ⟨fun r hY Z f hZ => by
      rw [show f = r.i ≫ (r.r ≫ f) by rw [← Category.assoc, r.retract, Category.id_comp],
        hY (r.r ≫ f) hZ, comp_zero]⟩
  have hle : (ObjectProperty.singleton N).triangEnvelope
      ≤ ((ObjectProperty.singleton K).shiftClosure ℤ).leftOrthogonal := by
    rw [ObjectProperty.triangEnvelope_le_iff, ObjectProperty.singleton_le_iff]
    intro Y f hY
    obtain ⟨Z, a, e, hZ⟩ := hY
    obtain rfl := (ObjectProperty.singleton_iff K Z).1 hZ
    rw [← Category.comp_id f, ← e.hom_inv_id, ← Category.assoc, hK a (f ≫ e.hom), zero_comp]
  exact fun n f => hle E hN f ⟨K, n, Iso.refl _, (ObjectProperty.singleton_iff K K).2 rfl⟩

end CategoryTheory.ObjectProperty

namespace CategoryTheory

universe v₁ v₂ u₁ u₂ w

/-- **The left adjoint of a right adjoint commuting with direct sums preserves compact objects.**
Let `L ⊣ G` be an adjunction of additive functors between preadditive categories and suppose that
`G` preserves the direct sums indexed by the types against which compactness is tested. Then
`L` carries a compact object to a compact object.

The adjunction turns the compactness map of `L.obj K` against a family `A` — the map
`⨁ᵢ (L(K) ⟶ Aᵢ) → (L(K) ⟶ ∐ A)` — into the compactness map of `K` against the family of
`G`-images, with the adjunction bijections as the two vertical maps; and the `G`-images of the
coprojections of `∐ A` form a colimit cofan precisely because `G` preserves that direct sum, so
the latter map is bijective by compactness of `K`.

This is the converse direction of
`CategoryTheory.Pretriangulated.preservesCoproducts_of_isCompactObject_map`, which deduces the
commutation of the *right* adjoint with direct sums from compactness; neither implies the other,
and both are needed below. -/
lemma isCompactObject_obj_of_adjunction {D : Type u₁} [Category.{v₁} D] [Preadditive D]
    {E : Type u₂} [Category.{v₂} E] [Preadditive E] {L : D ⥤ E} {G : E ⥤ D}
    [L.Additive] [G.Additive] (adj : L ⊣ G)
    (hG : ∀ I : Type w, Limits.PreservesColimitsOfShape (Discrete I) G) {K : D}
    (hK : IsCompactObject.{w} K) :
    IsCompactObject.{w} (L.obj K) := by
  classical
  constructor
  intro I _ A _
  change Function.Bijective (cofanMap (L.obj K) (Limits.Sigma.ι A))
  have := hG I
  have hc : Limits.IsColimit
      (Limits.Cofan.mk (G.obj (∐ A)) fun i => G.map (Limits.Sigma.ι A i)) :=
    (Limits.isColimitMapCoconeCofanMkEquiv G A (Limits.Sigma.ι A))
      (Limits.isColimitOfPreserves G (Limits.coproductIsCoproduct A))
  have hf : Function.Bijective (cofanMap K fun i => G.map (Limits.Sigma.ι A i)) :=
    bijective_cofanMap K hK _ hc
  set u : (DirectSum I fun i => (K ⟶ G.obj (A i))) →+ DirectSum I fun i => (L.obj K ⟶ A i) :=
    DirectSum.map fun i => (adj.homAddEquiv K (A i)).symm.toAddMonoidHom with hu
  have hubij : Function.Bijective u :=
    bijective_directSumMap _ fun i => (adj.homAddEquiv K (A i)).symm.bijective
  have hsq : ∀ x, (cofanMap K fun i => G.map (Limits.Sigma.ι A i)) x =
      (adj.homAddEquiv K (∐ A)) (cofanMap (L.obj K) (Limits.Sigma.ι A) (u x)) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i y =>
      rw [hu]
      simp only [cofanMap_of, DirectSum.map_of, AddEquiv.coe_toAddMonoidHom,
        Adjunction.homAddEquiv_apply, Adjunction.homAddEquiv_symm_apply]
      rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [show ((cofanMap K fun i => G.map (Limits.Sigma.ι A i)) : _ → _) =
      (adj.homAddEquiv K (∐ A)) ∘ (cofanMap (L.obj K) (Limits.Sigma.ι A)) ∘ u from
    funext hsq] at hf
  exact (Function.Bijective.of_comp_iff _ hubij).1
    ((Function.Bijective.of_comp_iff' (adj.homAddEquiv K (∐ A)).bijective _).1 hf)

end CategoryTheory

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule CategoryTheory.ObjectProperty

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-- **Stacks 09SS, first assertion.** Let `(A, d)` and `(B, d)` be differential graded algebras
over a commutative ring `R` and let `N` be a differential graded `(A, B)`-bimodule. Assume

1. the class of `N` in `D(B, d)` is a compact object,
2. `N` is a classical generator for `D_{compact}(B, d)`, that is, the triangulated envelope of the
   class of `N` is exactly the subcategory of compact objects of `D(B, d)`, and
3. the canonical map `H^k(A) → Hom_{D(B,d)}(N, N[k])` of
   `DifferentialGraded.Bimodule.cohomologyEndomorphismComparison` is bijective for every `k : ℤ`.

Then `- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` is an equivalence of categories.

This is [Stacks, Tag 09S7] with its hypothesis (2) replaced as Tag 09SS says it may be. Hypothesis
(2) above gives that the class of the regular module `B`, being a compact object of `D(B, d)`,
lies in the triangulated envelope of the class of `N`; since that class is a weak generator of
`D(B, d)`, so is the class of `N`, by
`CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_singleton_of_prop_triangEnvelope`. That
is hypothesis (2) of Tag 09S7.

As for Tag 09S7, the functor is exact and `R`-linear before any hypothesis (Tags 09LR, 09LS and
09S7), so this is the source's `R`-linear equivalence of triangulated categories, the
`R`-linearity being recorded at
`DifferentialGraded.Bimodule.linear_derivedTensorFunctor_of_isEquivalence`. The second
assertion of the remark — that a weak generator of `D_{compact}(B, d)` suffices once `RHom(N, B)`
is a compact object of `D(A, d)` — is the statement below,
`isEquivalence_derivedTensorFunctor_of_isWeakTriangulatedGenerator_isCompactObject`. -/
theorem isEquivalence_derivedTensorFunctor_of_triangEnvelope_eq_isCompactObject (N : Bimodule A B)
    [IsCompactObject.{u} ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule)]
    (h2 : (ObjectProperty.singleton ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj
        N.rightModule)).triangEnvelope =
      IsCompactObject.{u, _, _} (C := derivedCategory' B))
    (h3 : ∀ k : ℤ, Function.Bijective (N.cohomologyEndomorphismComparison k)) :
    (derivedTensorFunctor N).IsEquivalence := by
  refine isEquivalence_derivedTensorFunctor_of_isWeakTriangulatedGenerator N ?_ h3
  refine isWeakTriangulatedGenerator_singleton_of_prop_triangEnvelope
    (isWeakTriangulatedGenerator_q_regularModule B) ?_
  rw [h2]
  exact isCompactObject_q_regularModule B

/-- **Stacks 09SS, second assertion.** Let `(A, d)` and `(B, d)` be differential graded algebras
over a commutative ring `R` and let `N` be a differential graded `(A, B)`-bimodule. Assume

1. the class of `N` in `D(B, d)` is a compact object,
2. `RHom(N, B)` is a compact object of `D(A, d)`,
3. `N` is a weak generator for `D_{compact}(B, d)`: a *compact* object `X` of `D(B, d)` with
   `Hom_{D(B,d)}(N, X[n]) = 0` for every `n : ℤ` is zero, and
4. the canonical map `H^k(A) → Hom_{D(B,d)}(N, N[k])` of
   `DifferentialGraded.Bimodule.cohomologyEndomorphismComparison` is bijective for every `k : ℤ`.

Then `- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` is an equivalence of categories.

This is the second assertion of Tag 09SS: once `RHom(N, B)` is known to be compact, condition (2)
of Tag 09S7 may be replaced by weak generation of the compact objects alone, which is weaker than
both the original condition and the classical generation of the first assertion. The source omits
the proof; here is one.

Write `Φ = - ⊗_A^𝐋 N` and `Ψ = RHom(N, -)`, adjoint by Tag 09LT. Hypotheses (1) and (4) make the
unit of that adjunction invertible (Tag 09R9), so `Ψ(ε_X)` is invertible for the counit `ε` at
every `X`. Hypothesis (1) also makes `Ψ` commute with direct sums
(`DifferentialGraded.Bimodule.preservesColimitsOfShape_discrete_derivedHomFunctor`), hence makes
`Φ` preserve compact objects (`CategoryTheory.isCompactObject_obj_of_adjunction`); so by
hypothesis (2) the object `Φ(Ψ(B))` is compact, and so is the cone `C` of `ε_B`, the regular
module being compact. Applying `Ψ` to the triangle `Φ(Ψ(B)) → B → C` leaves a distinguished
triangle whose first map is invertible, so `Ψ(C)` is a zero object; that is, every morphism
`N ⟶ C[n]` vanishes, and hypothesis (3) applies to the compact object `C` and gives `C = 0`. So
`ε_B` is an isomorphism, `B ≅ Φ(Ψ(B))`.

That identification upgrades (3) to weak generation of all of `D(B, d)`, which is hypothesis (2)
of Tag 09S7. Indeed let `K` receive only zero maps from the translates of `N`. Then `Ψ(K)`
receives only zero maps from the translates of the regular module `A`, by the adjunction and
`DifferentialGraded.Bimodule.derivedTensorShiftRegularIso`, so `Ψ(K)` is a zero object
(`DifferentialGradedModule.isWeakTriangulatedGenerator_q_regularModule`) and therefore every
morphism out of an object of the form `Φ(X)` into `K` vanishes. The translates of `B` are of that
form, by `B ≅ Φ(Ψ(B))` and the commutation of `Φ` with the translation, so `K` receives only zero
maps from the translates of `B` and is zero, the regular module being a weak generator of its own
derived category. -/
theorem isEquivalence_derivedTensorFunctor_of_isWeakTriangulatedGenerator_isCompactObject
    (N : Bimodule A B)
    [IsCompactObject.{u} ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule)]
    [IsCompactObject.{u} ((derivedHomData A B N.rightModule N.leftAction).functor.obj
      ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj (regularModule B)))]
    (h2 : ∀ X : derivedCategory' B, IsCompactObject.{u} X →
      (∀ (n : ℤ) (f : (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule ⟶
        X⟦n⟧), f = 0) → IsZero X)
    (h3 : ∀ k : ℤ, Function.Bijective (N.cohomologyEndomorphismComparison k)) :
    (derivedTensorFunctor N).IsEquivalence := by
  have _ : IsCompactObject.{u} ((derivedTensorFunctor N).obj
      ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))) :=
    isCompactObject_of_iso (derivedTensorRegularIso N) ‹_›
  have hadd : (derivedHomData A B N.rightModule N.leftAction).functor.Additive :=
    (derivedTensorFunctor_adj_derivedHomFunctor N).right_adjoint_additive
  let _ : (derivedHomData A B N.rightModule N.leftAction).functor.CommShift ℤ :=
    (derivedTensorFunctor_adj_derivedHomFunctor N).rightAdjointCommShift ℤ
  have _ : (derivedTensorFunctor_adj_derivedHomFunctor N).CommShift ℤ :=
    (derivedTensorFunctor_adj_derivedHomFunctor N).commShift_of_leftAdjoint ℤ
  have _ : (derivedHomData A B N.rightModule N.leftAction).functor.IsTriangulated :=
    (derivedTensorFunctor_adj_derivedHomFunctor N).isTriangulated_rightAdjoint
  have _ := isIso_unit_derivedTensorFunctor_adj_derivedHomFunctor N h3
  -- `- ⊗_A^𝐋 N` preserves compact objects, `RHom(N, -)` commuting with direct sums.
  have _ : IsCompactObject.{u} ((derivedTensorFunctor N).obj
      ((derivedHomData A B N.rightModule N.leftAction).functor.obj
        ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj (regularModule B)))) :=
    isCompactObject_obj_of_adjunction (derivedTensorFunctor_adj_derivedHomFunctor N)
      (preservesColimitsOfShape_discrete_derivedHomFunctor N) ‹_›
  -- The cone of the counit at the regular module is compact and killed by `RHom(N, -)`.
  obtain ⟨C, i, p, hT⟩ := Pretriangulated.distinguished_cocone_triangle
    ((derivedTensorFunctor_adj_derivedHomFunctor N).counit.app
      ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj (regularModule B)))
  have hCc : IsCompactObject.{u} C :=
    isCompactObject_obj₃ _ hT ‹_› (isCompactObject_q_regularModule B)
  have hεmap : IsIso ((derivedHomData A B N.rightModule N.leftAction).functor.map
      ((derivedTensorFunctor_adj_derivedHomFunctor N).counit.app
        ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj (regularModule B)))) := by
    have h : (derivedTensorFunctor_adj_derivedHomFunctor N).unit.app
          ((derivedHomData A B N.rightModule N.leftAction).functor.obj
            ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj (regularModule B))) ≫
        (derivedHomData A B N.rightModule N.leftAction).functor.map
          ((derivedTensorFunctor_adj_derivedHomFunctor N).counit.app
            ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj (regularModule B))) = 𝟙 _ :=
      (derivedTensorFunctor_adj_derivedHomFunctor N).right_triangle_components _
    rw [← IsIso.inv_eq_of_hom_inv_id h]
    infer_instance
  have hΨC : IsZero ((derivedHomData A B N.rightModule N.leftAction).functor.obj C) :=
    Pretriangulated.Triangle.isZero₃_of_isIso₁ _
      ((derivedHomData A B N.rightModule N.leftAction).functor.map_distinguished _ hT) hεmap
  -- So the cone is zero and the counit at the regular module is an isomorphism.
  have hC : IsZero C := by
    refine h2 C hCc fun n f => ?_
    have hz : IsZero ((derivedHomData A B N.rightModule N.leftAction).functor.obj (C⟦n⟧)) :=
      IsZero.of_iso ((CategoryTheory.shiftFunctor (derivedCategory' A) n).map_isZero hΨC)
        (((derivedHomData A B N.rightModule N.leftAction).functor.commShiftIso n).app C)
    have h0 : (derivedTensorRegularIso N).hom ≫ f = 0 :=
      ((derivedTensorFunctor_adj_derivedHomFunctor N).homEquiv _ _).injective
        (hz.eq_of_tgt _ _)
    rw [← Iso.inv_hom_id_assoc (derivedTensorRegularIso N) f, h0, comp_zero]
  have _ : IsIso ((derivedTensorFunctor_adj_derivedHomFunctor N).counit.app
      ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj (regularModule B))) :=
    (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).1 hC
  -- Hence the class of `N` is a weak generator of `D(B, d)`, and Tag 09S7 applies.
  refine isEquivalence_derivedTensorFunctor_of_isWeakTriangulatedGenerator N ?_ h3
  intro K hK
  have hΦA : ∀ (n : ℤ) (g : (derivedTensorFunctor N).obj
      (((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))⟦n⟧) ⟶ K),
      g = 0 := by
    intro n g
    have h0 : (derivedTensorShiftRegularIso N n).inv ≫ g = 0 :=
      hK _ ⟨_, n, Iso.refl _, (ObjectProperty.singleton_iff _ _).2 rfl⟩
    rw [← Iso.hom_inv_id_assoc (derivedTensorShiftRegularIso N n) g, h0, comp_zero]
  have hΨK : IsZero ((derivedHomData A B N.rightModule N.leftAction).functor.obj K) := by
    refine isWeakTriangulatedGenerator_q_regularModule A _ fun {Y} f hY => ?_
    obtain ⟨Y', n, e, hY'⟩ := hY
    obtain rfl := (ObjectProperty.singleton_iff _ Y').1 hY'
    have hg : ∀ g : (((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj
        (regularModule A))⟦n⟧ : derivedCategory' A) ⟶
          (derivedHomData A B N.rightModule N.leftAction).functor.obj K, g = 0 := by
      intro g
      refine ((derivedTensorFunctor_adj_derivedHomFunctor N).homAddEquiv _ K).symm.injective ?_
      rw [map_zero, Adjunction.homAddEquiv_symm_apply]
      exact hΦA n _
    rw [← Iso.hom_inv_id_assoc e f, hg (e.inv ≫ f), comp_zero]
  have hzero : ∀ (X : derivedCategory' A) (g : (derivedTensorFunctor N).obj X ⟶ K), g = 0 := by
    intro X g
    refine ((derivedTensorFunctor_adj_derivedHomFunctor N).homAddEquiv X K).injective ?_
    rw [map_zero]
    exact hΨK.eq_of_tgt _ _
  refine isWeakTriangulatedGenerator_q_regularModule B K fun {Y} f hY => ?_
  obtain ⟨Y', n, e, hY'⟩ := hY
  obtain rfl := (ObjectProperty.singleton_iff _ Y').1 hY'
  have ei : (derivedTensorFunctor N).obj
      (((derivedHomData A B N.rightModule N.leftAction).functor.obj
        ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj (regularModule B)))⟦n⟧) ≅ Y :=
    ((derivedTensorFunctor N).commShiftIso n).app _ ≪≫
      (CategoryTheory.shiftFunctor (derivedCategory' B) n).mapIso
        (asIso ((derivedTensorFunctor_adj_derivedHomFunctor N).counit.app _)) ≪≫ e.symm
  rw [← Iso.inv_hom_id_assoc ei f, hzero _ (ei.hom ≫ f), comp_zero]

/-- **Stacks 09SS, first assertion: the equivalence is `R`-linear.** The conclusion of
[Stacks, Tag 09S7] that Tag 09SS transports is that `- ⊗_A^𝐋 N` is an *`R`-linear* equivalence of
triangulated categories; this is the `R`-linearity, for the functor and for its quasi-inverse.

It needs none of the three hypotheses:
`DifferentialGraded.Bimodule.derivedTensorFunctor_linear` (Tag 09S7) is a global instance giving
`(- ⊗_A^𝐋 N).Linear R` for every bimodule `N`, and the quasi-inverse of an `R`-linear equivalence
is `R`-linear by `CategoryTheory.Equivalence.inverseLinear`. The hypothesis below is only that the
functor *is* an equivalence, which the theorem above supplies under the hypotheses of the
remark. -/
theorem linear_derivedTensorFunctor_of_isEquivalence (N : Bimodule A B)
    [(derivedTensorFunctor N).IsEquivalence] :
    (derivedTensorFunctor N).Linear R ∧
      (derivedTensorFunctor N).asEquivalence.inverse.Linear R := by
  have hfun : (derivedTensorFunctor N).asEquivalence.functor.Linear R :=
    derivedTensorFunctor_linear N
  exact ⟨hfun, Equivalence.inverseLinear R _⟩

/-- **Stacks 09SS.** Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative
ring `R` and let `N` be a differential graded `(A, B)`-bimodule. Assume conditions (1) and (3) of
[Stacks, Tag 09S7]:

1. the class of `N` in `D(B, d)` is a compact object, and
3. the canonical map `H^k(A) → Hom_{D(B,d)}(N, N[k])` of
   `DifferentialGraded.Bimodule.cohomologyEndomorphismComparison` is bijective for every `k : ℤ`.

Then each of the following replacements of condition (2) of Tag 09S7 still makes
`- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` an `R`-linear equivalence of triangulated categories, that is,
an equivalence which is exact (`Functor.IsTriangulated`), `R`-linear, and whose quasi-inverse is
`R`-linear:

* `N` is a classical generator for `D_{compact}(B, d)`: the triangulated envelope of the class of
  `N` (the smallest strictly full triangulated subcategory closed under direct summands containing
  it) is exactly the subcategory of compact objects of `D(B, d)`;
* `RHom(N, B)` is a compact object of `D(A, d)`, and `N` is a weak generator for
  `D_{compact}(B, d)`: a compact object `X` of `D(B, d)` with `Hom_{D(B,d)}(N, X[n]) = 0` for every
  `n : ℤ` is zero.

These are the two assertions of the remark, proved respectively by
`isEquivalence_derivedTensorFunctor_of_triangEnvelope_eq_isCompactObject` and
`isEquivalence_derivedTensorFunctor_of_isWeakTriangulatedGenerator_isCompactObject` above (the
source omits the proof of the second; it is supplied there). Exactness of `- ⊗_A^𝐋 N` is
`DifferentialGraded.Bimodule.derivedTensorFunctor_isTriangulated` (Tags 09LR and 09LS), its
`R`-linearity `DifferentialGraded.Bimodule.derivedTensorFunctor_linear` (Tag 09S7), and the
`R`-linearity of the quasi-inverse is Mathlib's `CategoryTheory.Equivalence.inverseLinear`. -/
@[stacks 09SS "both assertions: classical generation of D_compact(B, d), or weak generation of \
D_compact(B, d) when RHom(N, B) is compact, may replace condition (2) of 09S7"]
theorem isEquivalence_linear_derivedTensorFunctor_of_generator_isCompactObject
    (N : Bimodule A B)
    [IsCompactObject.{u} ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule)]
    (h3 : ∀ k : ℤ, Function.Bijective (N.cohomologyEndomorphismComparison k)) :
    ((ObjectProperty.singleton ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj
        N.rightModule)).triangEnvelope = IsCompactObject.{u, _, _} (C := derivedCategory' B) →
      ∃ _ : (derivedTensorFunctor N).IsEquivalence, (derivedTensorFunctor N).IsTriangulated ∧
        (derivedTensorFunctor N).Linear R ∧ (derivedTensorFunctor N).inv.Linear R) ∧
    (IsCompactObject.{u} ((derivedHomData A B N.rightModule N.leftAction).functor.obj
        ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj (regularModule B))) →
      (∀ X : derivedCategory' B, IsCompactObject.{u} X →
        (∀ (n : ℤ) (f : (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule ⟶
          X⟦n⟧), f = 0) → IsZero X) →
      ∃ _ : (derivedTensorFunctor N).IsEquivalence, (derivedTensorFunctor N).IsTriangulated ∧
        (derivedTensorFunctor N).Linear R ∧ (derivedTensorFunctor N).inv.Linear R) := by
  have key : ∀ _ : (derivedTensorFunctor N).IsEquivalence, (derivedTensorFunctor N).IsTriangulated ∧
      (derivedTensorFunctor N).Linear R ∧ (derivedTensorFunctor N).inv.Linear R := fun _ =>
    have hfun : (derivedTensorFunctor N).asEquivalence.functor.Linear R :=
      derivedTensorFunctor_linear N
    ⟨inferInstance, derivedTensorFunctor_linear N,
      Equivalence.inverseLinear R (derivedTensorFunctor N).asEquivalence⟩
  refine ⟨fun h2 => ?_, fun hc h2 => ?_⟩
  · have := isEquivalence_derivedTensorFunctor_of_triangEnvelope_eq_isCompactObject N h2 h3
    exact ⟨this, key this⟩
  · have :=
      isEquivalence_derivedTensorFunctor_of_isWeakTriangulatedGenerator_isCompactObject N h2 h3
    exact ⟨this, key this⟩

end DifferentialGraded.Bimodule

end
