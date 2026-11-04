module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.FieldTheory.IsSepClosed
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleLocal
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparablyClosed
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Criteria

/-!
# Testing geometric irreducibility over a separable closure

For a scheme over a field, geometric irreducibility may be tested either after every finite
separable extension of the ground field or after one separable algebraic closure.

## Main results

* `AlgebraicGeometry.geometricallyIrreducible_tfae_of_isSepClosure` gives the three equivalent
  characterizations of geometric irreducibility.

## Implementation notes

A scheme over `k` is represented by its structure morphism `f : X ⟶ Spec k`. Its base change to
an extension field `K` is the categorical pullback of `f` along the morphism `Spec K ⟶ Spec k`
induced by `algebraMap k K`. A separable algebraic closure is represented abstractly by an
instance of `IsSepClosure`, so the result applies to any chosen closure.

The three entries of the `List.TFAE` are respectively items (1), (2), and (3) of the source.

## References

* [Stacks Project, Tag 038I](https://stacks.math.columbia.edu/tag/038I)
-/

@[expose] public section

open CategoryTheory Limits CommRingCat

namespace AlgebraicGeometry

universe u

/-- For a surjective `g : Spec K ⟶ Spec k` and an open immersion `j : Y ⟶ X` with `Y` nonempty,
if the base change of `f : X ⟶ Spec k` along `g` is irreducible, then so is that of `j ≫ f`. -/
private lemma irreducibleSpace_pullback_comp_open
    {k K : Type u} [Field k] [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (j : Y ⟶ X) [IsOpenImmersion j] [Nonempty Y]
    (g : Spec (.of K) ⟶ Spec (.of k)) [Surjective g]
    [IrreducibleSpace ↥(pullback f g)] :
    IrreducibleSpace ↥(pullback (j ≫ f) g) := by
  let i := pullback.map (j ≫ f) g f g j (𝟙 _) (𝟙 _) (by simp) (by simp)
  let : IsOpenImmersion i := by dsimp [i]; infer_instance
  let : Nonempty ↥(pullback (j ≫ f) g) :=
    ⟨Classical.choose ((pullback.fst (j ≫ f) g).surjective
      (Nonempty.some (inferInstance : Nonempty Y)))⟩
  exact i.isOpenEmbedding.irreducibleSpace

/-- **Stacks Project, Tag 038I.** Geometric irreducibility of a scheme over a field can be tested
after every finite separable extension, or after base change to any separable algebraic
closure. -/
@[stacks 038I, ega "IV 4.5.9"]
public lemma geometricallyIrreducible_tfae_of_isSepClosure
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (ksep : Type u) [Field ksep] [Algebra k ksep] [IsSepClosure k ksep] :
    List.TFAE
      [GeometricallyIrreducible f,
        ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
          [Algebra.IsSeparable k k'],
          IrreducibleSpace ↥(pullback f (Spec.map (ofHom (algebraMap k k')))),
    IrreducibleSpace ↥(pullback f (Spec.map (ofHom (algebraMap k ksep))))] := by
  classical
  tfae_have 1 → 2 := by
    intro h k' _ _ _ _
    exact h.geometrically_irreducibleSpace _ _ _ (.of_hasPullback _ _)
  tfae_have 2 → 3 := by
    intro h
    have hf : GeometricallyIrreducible f := by
      refine ((geometricallyIrreducible_tfae_local k f).out 2 1).mp ?_
      refine ⟨?_, ?_⟩
      · let : IrreducibleSpace
            ↥(pullback f (Spec.map (ofHom (algebraMap k k)))) := h k
        exact ⟨(pullback.fst f (Spec.map (ofHom (algebraMap k k)))).base
          (Nonempty.some inferInstance)⟩
      · intro U ⟨w, hw⟩
        let : Algebra k Γ(X, U) :=
          ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom.toAlgebra
        refine ((AlgebraicGeometry.geometricallyIrreducible_tfae k Γ(X, U) ksep
          (AlgebraicClosure k)).out 2 5).mp ?_
        intro k' _ _ _ _
        have hq : Spec.map (ofHom (algebraMap k Γ(X, U))) =
            U.2.fromSpec ≫ f := by
          calc
            _ = Spec.map (f.appLE ⊤ U (by simp)) ≫
                (isAffineOpen_top (Spec (.of k))).fromSpec := by
              rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
              congr 1
            _ = _ := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) U.2 (by simp)
        let : Nonempty (Spec Γ(X, U)) := ⟨U.2.isoSpec.hom ⟨w, hw⟩⟩
        let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
        have hi : IrreducibleSpace ↥(pullback
            (Spec.map (ofHom (algebraMap k Γ(X, U))))
            (Spec.map (ofHom (algebraMap k k')))) := by
          rw [hq]
          exact irreducibleSpace_pullback_comp_open f U.2.fromSpec _
        exact (pullbackSpecIso k Γ(X, U) k').schemeIsoToHomeo.irreducibleSpace_iff.mp hi
    exact hf.geometrically_irreducibleSpace _ _ _ (.of_hasPullback _ _)
  tfae_have 3 → 1 := by
    intro h
    let : IsSepClosed ksep := IsSepClosure.sep_closed k
    exact (geometricallyIrreducible_iff_baseChange_fieldExtension k ksep f).mpr
      (geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed ksep _
        (pullback.snd f (Spec.map (ofHom (algebraMap k ksep)))))
  tfae_finish

end AlgebraicGeometry
