module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.Cover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafFrobenius
public import Mathlib.FieldTheory.Finite.Trace

/-!
# Frobenius on the fibres of the Artin–Schreier cover

At a closed point `y` with finite residue field, the arithmetic Frobenius moves the fibre of the
Artin–Schreier cover `t^q - t = g` by `Tr_{κ(y)/𝔽_q}(g(y))`.

## Main results

* `Stacks.ArtinSchreier.smul_eq_of_arithmeticFrobenius`,
  `Stacks.ArtinSchreier.character_localElement`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial Stacks.Frobenius Stacks.EtaleCohomology

universe u

namespace Stacks.ArtinSchreier

variable (k : Type u) [Field k] [Fintype k] (A : Type u) [CommRing A] [Algebra k A] (g : A)

/-- The evaluation `A → κ(y)` at a point `y` of `Spec A`. -/
public def residueRingHom (y : Spec (.of A)) : A →+* (Spec (.of A)).residueField y :=
  (Spec.preimage ((Spec (.of A)).fromSpecResidueField y)).hom

/-- The `𝔽_q`-algebra structure on the residue field `κ(y)` through `A`. -/
@[instance_reducible]
public def residueAlgebra (y : Spec (.of A)) : Algebra k ((Spec (.of A)).residueField y) :=
  ((residueRingHom A y).comp (algebraMap k A)).toAlgebra

variable {k A g}

/-- The ring homomorphism of a point of the fibre at the geometric point at `y`, on `A`, is the
evaluation at `y` followed by `κ(y) ⊆ κ(y)^alg`. -/
public theorem fiberRingHom_algebraMap_geometricPointAt (y : Spec (.of A))
    (p : (finiteEtaleFiberFunctor (geometricPointAt _ y)).obj (cover k A g)) (x : A) :
    (fiberRingHom p).hom (algebraMap A (Ring k g) x) =
      algebraMap ((Spec (.of A)).residueField y) (AlgebraicClosure ((Spec (.of A)).residueField y))
        (residueRingHom A y x) := by
  have h : CommRingCat.ofHom (algebraMap A (Ring k g)) ≫ fiberRingHom p =
      Spec.preimage ((Spec (.of A)).fromSpecResidueField y) ≫
        CommRingCat.ofHom (algebraMap ((Spec (.of A)).residueField y)
          (AlgebraicClosure ((Spec (.of A)).residueField y))) := by
    apply Spec.map_injective
    refine (Spec.map_comp _ _).trans (Eq.trans ?_ (Spec.map_comp _ _).symm)
    rw [spec_map_fiberRingHom, Spec.map_preimage]
    exact p.2
  exact congrArg (fun f => f.hom x) h

/-- **An element of `π₁` acting on geometric fibres at `y` as the arithmetic Frobenius moves the
fibre of the Artin–Schreier cover by `Tr_{κ(y)/𝔽_q}(g(y))`**: a root `t` of `T^q - T - g(y)` goes
to `t ^ #κ(y) = t + ∑_{i < [κ(y):𝔽_q]} g(y) ^ (q ^ i)`. -/
public theorem smul_eq_of_arithmeticFrobenius [ConnectedSpace (Spec (.of A))]
    (y : Spec (.of A)) [Finite ((Spec (.of A)).residueField y)]
    (σ : EtaleFundamentalGroup (Spec (.of A)) (geometricPointAt _ y))
    (hσ : ∀ (V : FiniteEtaleOver (Spec (.of A))) (q : finiteEtaleFiber (geometricPointAt _ y) V),
      ((σ.app V).hom q).1 =
        Spec.map (CommRingCat.ofHom (residueGeometricFrobenius _ y).symm.toAlgHom.toRingHom) ≫ q.1)
    (p : (finiteEtaleFiberFunctor (geometricPointAt _ y)).obj (cover k A g)) :
    σ • p = (finiteEtaleFiberFunctor _).map (coverTranslate k A g
        (letI := residueAlgebra k A y; Algebra.trace k _ (residueRingHom A y g))) p := by
  let := residueAlgebra k A y
  let : Algebra k (AlgebraicClosure ((Spec (.of A)).residueField y)) :=
    ((fiberRingHom p).hom.comp (algebraMap k (Ring k g))).toAlgebra
  have hk : ∀ a : k, algebraMap k (AlgebraicClosure ((Spec (.of A)).residueField y)) a =
      algebraMap ((Spec (.of A)).residueField y) (AlgebraicClosure ((Spec (.of A)).residueField y))
        (algebraMap k ((Spec (.of A)).residueField y) a) := fun a => by
    show (fiberRingHom p).hom (algebraMap k (Ring k g) a) = _
    rw [IsScalarTower.algebraMap_apply k A (Ring k g), fiberRingHom_algebraMap_geometricPointAt]
    rfl
  have hσp : fiberRingHom (σ • p) = fiberRingHom p ≫
      CommRingCat.ofHom (residueGeometricFrobenius _ y).symm.toAlgHom.toRingHom := by
    apply Spec.map_injective
    refine (spec_map_fiberRingHom _).trans (Eq.trans ?_ (Spec.map_comp _ _).symm)
    refine (hσ (cover k A g) p).trans ?_
    rw [spec_map_fiberRingHom]
    rfl
  apply fiber_ext
  apply CommRingCat.hom_ext
  refine AdjoinRoot.ringHom_ext ?_ ?_
  · ext x
    exact (fiberRingHom_algebraMap _ p x).trans (fiberRingHom_algebraMap p _ x)
  · show fiberRoot _ = fiberRoot _
    rw [fiberRoot, hσp, fiberRoot, fiberRingHom_map_coverTranslate]
    show (residueGeometricFrobenius _ y).symm (fiberRoot p) =
      (fiberRingHom p).hom (translate k g _ (AdjoinRoot.root (poly k g)))
    rw [residueGeometricFrobenius_symm_apply, translate_root, map_add]
    show fiberRoot p ^ Nat.card ((Spec (.of A)).residueField y) =
      fiberRoot p + algebraMap k (AlgebraicClosure ((Spec (.of A)).residueField y)) _
    rw [Module.natCard_eq_pow_finrank (K := k), Nat.card_eq_fintype_card,
      pow_card_pow_of_pow_card_eq k (fiberRoot_pow_card p), hk,
      FiniteField.algebraMap_trace_eq_sum_pow, map_sum, fiberRingHom_algebraMap_geometricPointAt,
      Nat.card_eq_fintype_card]
    simp only [map_pow]

/-- **The Artin–Schreier character of the arithmetic Frobenius element at a closed point `y` is
`Tr_{κ(y)/𝔽_q}(g(y))`**, at the geometric point over `y`. -/
public theorem character_localElement [ConnectedSpace (Spec (.of A))]
    (y : closedPoints (Spec (.of A))) [Finite ((Spec (.of A)).residueField y.1)]
    (base : GeometricPoint (Spec (.of A)))
    (t : finiteEtaleFiberFunctor (geometricPointAt _ y.1) ≅ finiteEtaleFiberFunctor base)
    (p₀ : (finiteEtaleFiberFunctor (geometricPointAt _ y.1)).obj (cover k A g)) :
    Multiplicative.toAdd ((torsorCover k A g).character (geometricPointAt _ y.1) p₀
      (frobeniusDataOfPath base y t).localElement) =
      (letI := residueAlgebra k A y.1; Algebra.trace k _ (residueRingHom A y.1 g)) :=
  (torsorCover k A g).character_eq_of_smul _ p₀ _ p₀
    (smul_eq_of_arithmeticFrobenius y.1 _ (localElement_app_coe base y t) p₀)

end Stacks.ArtinSchreier
