module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.Algebra
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TorsorCharacter
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# The Artin–Schreier cover is an `𝔽_q`-torsor

`Spec A[T]/(T^q - T - g) → Spec A` is a finite étale cover on which `𝔽_q` acts by translations,
simply transitively on every geometric fibre.

## Main definitions

* `Stacks.ArtinSchreier.cover`, `Stacks.ArtinSchreier.coverTranslate`,
  `Stacks.ArtinSchreier.torsorCover`.

## Main results

* `Stacks.ArtinSchreier.existsUnique_map_coverTranslate`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial

universe u

namespace Stacks.ArtinSchreier

variable (k : Type u) [Field k] [Fintype k] (A : Type u) [CommRing A] [Algebra k A] (g : A)

/-- The structure morphism `Spec A[T]/(T^q - T - g) → Spec A` of the Artin–Schreier cover. -/
public abbrev coverHom : Spec (.of (Ring k g)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Ring k g)))

public instance isFinite_coverHom : IsFinite (coverHom k A g) := by
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.2 inferInstance

public instance etale_coverHom : Etale (coverHom k A g) := by
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  exact RingHom.etale_algebraMap.2 inferInstance

/-- **The Artin–Schreier cover** `t^q - t = g` of `Spec A`, a finite étale cover. -/
public def cover : FiniteEtaleOver (Spec (.of A)) :=
  MorphismProperty.Over.mk ⊤ (coverHom k A g) ⟨inferInstance, inferInstance⟩

/-- The translation `t ↦ t + a` as an automorphism of the cover over `Spec A`. -/
public def coverTranslate (a : k) : cover k A g ⟶ cover k A g :=
  MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom (translate k g a).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact (translate k g a).commutes x)

public theorem coverTranslate_zero : coverTranslate k A g 0 = 𝟙 _ := by
  ext : 1
  change Spec.map _ = 𝟙 _
  rw [translate_zero]
  exact Spec.map_id _

public theorem coverTranslate_add (a b : k) :
    coverTranslate k A g (a + b) = coverTranslate k A g a ≫ coverTranslate k A g b := by
  ext : 1
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, translate_add]
  rfl

/-! ### The cover is a `𝔽_q`-torsor -/

variable {k A g}

/-- The ring homomorphism `A[T]/(T^q - T - g) → Ω` of a point of a geometric fibre. -/
public def fiberRingHom {s : GeometricPoint (Spec (.of A))}
    (p : (finiteEtaleFiberFunctor s).obj (cover k A g)) :
    CommRingCat.of (Ring k g) ⟶ .of s.residueField :=
  Spec.preimage p.1

public theorem spec_map_fiberRingHom {s : GeometricPoint (Spec (.of A))}
    (p : (finiteEtaleFiberFunctor s).obj (cover k A g)) : Spec.map (fiberRingHom p) = p.1 :=
  Spec.map_preimage _

/-- Points of a geometric fibre are determined by their ring homomorphisms. -/
public theorem fiber_ext {s : GeometricPoint (Spec (.of A))}
    {p q : (finiteEtaleFiberFunctor s).obj (cover k A g)} (h : fiberRingHom p = fiberRingHom q) :
    p = q := by
  apply Subtype.ext
  rw [← spec_map_fiberRingHom p, ← spec_map_fiberRingHom q, h]

/-- All points of a geometric fibre induce the same homomorphism on `A`. -/
public theorem fiberRingHom_algebraMap {s : GeometricPoint (Spec (.of A))}
    (p q : (finiteEtaleFiberFunctor s).obj (cover k A g)) (x : A) :
    (fiberRingHom p).hom (algebraMap A (Ring k g) x) =
      (fiberRingHom q).hom (algebraMap A (Ring k g) x) := by
  have h : CommRingCat.ofHom (algebraMap A (Ring k g)) ≫ fiberRingHom p =
      CommRingCat.ofHom (algebraMap A (Ring k g)) ≫ fiberRingHom q := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, spec_map_fiberRingHom, spec_map_fiberRingHom]
    exact p.2.trans q.2.symm
  exact congrArg (fun f => f.hom x) h

/-- The action of a translation on the ring homomorphism of a fibre point. -/
public theorem fiberRingHom_map_coverTranslate {s : GeometricPoint (Spec (.of A))} (a : k)
    (p : (finiteEtaleFiberFunctor s).obj (cover k A g)) :
    fiberRingHom ((finiteEtaleFiberFunctor s).map (coverTranslate k A g a) p) =
      CommRingCat.ofHom (translate k g a).toRingHom ≫ fiberRingHom p := by
  apply Spec.map_injective
  rw [spec_map_fiberRingHom, Spec.map_comp, spec_map_fiberRingHom]
  rfl

/-- The value of the fibre point at the root `t`. -/
public abbrev fiberRoot {s : GeometricPoint (Spec (.of A))}
    (p : (finiteEtaleFiberFunctor s).obj (cover k A g)) : s.residueField :=
  (fiberRingHom p).hom (AdjoinRoot.root (poly k g))

public theorem fiberRoot_pow_card {s : GeometricPoint (Spec (.of A))}
    (p : (finiteEtaleFiberFunctor s).obj (cover k A g)) :
    fiberRoot p ^ Fintype.card k =
      fiberRoot p + (fiberRingHom p).hom (algebraMap A (Ring k g) g) := by
  rw [fiberRoot, ← map_pow, root_pow_card, map_add]

/-- **The Artin–Schreier cover is an `𝔽_q`-torsor**: `𝔽_q` acts simply transitively on every
geometric fibre, the roots of `T^q - T - g(s̄)` differing by the roots of `T^q - T`. -/
public theorem existsUnique_map_coverTranslate (s : GeometricPoint (Spec (.of A)))
    (p q : (finiteEtaleFiberFunctor s).obj (cover k A g)) :
    ∃! a : k, (finiteEtaleFiberFunctor s).map (coverTranslate k A g a) p = q := by
  let : Algebra k s.residueField :=
    ((fiberRingHom p).hom.comp (algebraMap k (Ring k g))).toAlgebra
  have hk : ∀ a : k,
      (fiberRingHom p).hom (algebraMap k (Ring k g) a) = algebraMap k s.residueField a :=
    fun _ => rfl
  have hkq : ∀ a : k, (fiberRingHom q).hom (algebraMap k (Ring k g) a) =
      algebraMap k s.residueField a := fun a => by
    rw [← hk, IsScalarTower.algebraMap_apply k A (Ring k g), fiberRingHom_algebraMap q p]
  have hval : ∀ a : k, fiberRoot ((finiteEtaleFiberFunctor s).map (coverTranslate k A g a) p) =
      fiberRoot p + algebraMap k s.residueField a := fun a => by
    rw [fiberRoot, fiberRingHom_map_coverTranslate]
    change (fiberRingHom p).hom (translate k g a (AdjoinRoot.root (poly k g))) = _
    rw [translate_root, map_add, hk]
  have hpow : (fiberRoot q - fiberRoot p) ^ Fintype.card k = fiberRoot q - fiberRoot p := by
    have h := add_pow_card k (fiberRoot q - fiberRoot p) (fiberRoot p)
    rw [sub_add_cancel, fiberRoot_pow_card, fiberRoot_pow_card,
      fiberRingHom_algebraMap q p] at h
    linear_combination h.symm
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_pow_card_eq k hpow
  refine ⟨a, ?_, fun b hb => ?_⟩
  · apply fiber_ext
    apply CommRingCat.hom_ext
    refine AdjoinRoot.ringHom_ext ?_ ?_
    · ext x
      rw [RingHom.comp_apply, RingHom.comp_apply, fiberRingHom_map_coverTranslate]
      change (fiberRingHom p).hom (translate k g a (algebraMap A (Ring k g) x)) = _
      rw [AlgHom.commutes, fiberRingHom_algebraMap p q]
      rfl
    · change fiberRoot ((finiteEtaleFiberFunctor s).map (coverTranslate k A g a) p) = fiberRoot q
      rw [hval, ha]
      ring
  · have h := congrArg fiberRoot hb
    rw [hval] at h
    refine (algebraMap k s.residueField).injective ?_
    rw [ha]
    linear_combination h

/-- **The Artin–Schreier cover as a torsor cover** with group `𝔽_q`. -/
public def torsorCover (k : Type u) [Field k] [Fintype k] (A : Type u) [CommRing A] [Algebra k A]
    (g : A) [ConnectedSpace (Spec (.of A))] : TorsorCover (Spec (.of A)) k where
  cover := cover k A g
  τ := coverTranslate k A g
  τ_zero := coverTranslate_zero k A g
  τ_add := coverTranslate_add k A g
  existsUnique := existsUnique_map_coverTranslate

end Stacks.ArtinSchreier
