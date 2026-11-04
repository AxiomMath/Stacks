module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.Cover
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GenericPoint

/-!
# The Artin–Schreier character on the Galois group of the function field

Let `A` be a `k`-algebra, `k` a finite field with `q` elements, with `Spec A` irreducible, `K` its
function field, `L` a separable closure of `K` inside an algebraic closure `Ω`, and `x̄` the
geometric generic point given by `Ω`. A point `p₀` of the fibre at `x̄` of the Artin–Schreier cover
`t ^ q - t = g` is a root `t₀ ∈ Ω` of `t ^ q - t = g`; it lies in `L`, and the character of the
cover, composed with `Gal(L/K) → π₁(Spec A, x̄)`, is `σ ↦ σ(t₀) - t₀`.

## Main results

* `Stacks.ArtinSchreier.exists_algebraMap_eq_fiberRoot_galoisToFundamentalGroup`: the root of a
  point of the fibre at `x̄` comes from some `t ∈ L`, and the character of the cover at the image
  of `σ ∈ Gal(L/K)` in `π₁(Spec A, x̄)` is `σ t - t`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.ArtinSchreier

variable {k : Type u} [Field k] [Fintype k] {A : Type u} [CommRing A] [Algebra k A] {g : A}

/-- A translation moves the root of a fibre point by the translating element. -/
theorem fiberRoot_map_coverTranslate {s : GeometricPoint (Spec (.of A))} (a : k)
    (p : (finiteEtaleFiberFunctor s).obj (cover k A g)) :
    fiberRoot ((finiteEtaleFiberFunctor s).map (coverTranslate k A g a) p) =
      fiberRoot p + (fiberRingHom p).hom (algebraMap k (Ring k g) a) := by
  rw [fiberRoot, fiberRingHom_map_coverTranslate]
  show (fiberRingHom p).hom (translate k g a (AdjoinRoot.root (poly k g))) = _
  rw [translate_root, map_add]

/-- The root of a fibre point whose underlying morphism is `Spec.map ψ` is the image of the
root under `ψ`. -/
theorem fiberRoot_eq_of_val_eq_spec_map {s : GeometricPoint (Spec (.of A))}
    {p : (finiteEtaleFiberFunctor s).obj (cover k A g)}
    {ψ : CommRingCat.of (Ring k g) ⟶ .of s.residueField}
    (h : (p.1 : Spec (.of s.residueField) ⟶ Spec (.of (Ring k g))) = Spec.map ψ) :
    fiberRoot p = ψ.hom (AdjoinRoot.root (poly k g)) := by
  rw [fiberRoot, fiberRingHom, h, Spec.preimage_map]

variable (k A g) [ConnectedSpace (Spec (.of A))] [IrreducibleSpace (Spec (.of A))]
  (L Ω : Type u) [Field L] [Field Ω]
  [Algebra ((Spec (.of A)).residueField (genericPoint (Spec (.of A)))) L]
  [IsSepClosure ((Spec (.of A)).residueField (genericPoint (Spec (.of A)))) L]
  [Algebra L Ω] [Algebra ((Spec (.of A)).residueField (genericPoint (Spec (.of A)))) Ω]
  [IsScalarTower ((Spec (.of A)).residueField (genericPoint (Spec (.of A)))) L Ω]
  [IsAlgClosed Ω]
  [Algebra.IsAlgebraic ((Spec (.of A)).residueField (genericPoint (Spec (.of A)))) Ω]

/-- **The Artin–Schreier character on the Galois group of the function field.** A point `p₀` of
the fibre of the Artin–Schreier cover `t ^ q - t = g` at the geometric generic point is a root
`t ∈ L`, and for `σ ∈ Gal(L/K)` the character of the cover at the image of `σ` in
`π₁(Spec A, x̄)` is `σ t - t`. -/
theorem exists_algebraMap_eq_fiberRoot_galoisToFundamentalGroup
    (p₀ : (finiteEtaleFiberFunctor ((algebraicClosureGeometricPoint
      ((Spec (.of A)).residueField (genericPoint (Spec (.of A)))) Ω).map
        ((Spec (.of A)).fromSpecResidueField (genericPoint (Spec (.of A)))))).obj
          (cover k A g)) :
    ∃ t : L, algebraMap L Ω t = fiberRoot p₀ ∧
      ∀ σ : Gal(L / (Spec (.of A)).residueField (genericPoint (Spec (.of A)))),
        algebraMap L Ω (σ t - t) = (fiberRingHom p₀).hom (algebraMap k (Ring k g)
          (Multiplicative.toAdd ((torsorCover k A g).character _ p₀
            (galoisToFundamentalGroup (Spec (.of A)) L Ω σ)))) := by
  let K := (Spec (.of A)).residueField (genericPoint (Spec (.of A)))
  let j := (Spec (.of A)).fromSpecResidueField (genericPoint (Spec (.of A)))
  let x₀ := algebraicClosureGeometricPoint K Ω
  let Y := cover k A g
  let Y' := (finiteEtaleBaseChange j).obj Y
  let q₀ := (finiteEtaleFiberProjectionEquiv j x₀ Y).symm p₀
  have hq₀ : finiteEtaleFiberProjection j x₀ Y q₀ = p₀ :=
    (finiteEtaleFiberProjectionEquiv j x₀ Y).apply_symm_apply p₀
  let y := (finiteEtaleFiberIso K L Ω).inv.app Y' q₀
  let f := (separableFiberEquiv K L Ω Y' y).1
  have hf : q₀.1 = Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ f := by
    rw [← finiteEtaleFiberIso_apply K L Ω Y' y]
    exact (congrArg (fun η => Subtype.val (η.app Y' q₀))
      (finiteEtaleFiberIso K L Ω).inv_hom_id).symm
  let φf : CommRingCat.of (Ring k g) ⟶ CommRingCat.of L :=
    Spec.preimage (f ≫ pullback.fst Y.hom j)
  let t := φf.hom (AdjoinRoot.root (poly k g))
  have key : ∀ (ψ : CommRingCat.of L ⟶ CommRingCat.of Ω) (p : (finiteEtaleFiberFunctor
      (x₀.map j)).obj Y), (p.1 : Spec (.of Ω) ⟶ Spec (.of (Ring k g))) =
        Spec.map ψ ≫ (f ≫ pullback.fst Y.hom j) → fiberRoot p = ψ.hom t := by
    intro ψ p h
    refine fiberRoot_eq_of_val_eq_spec_map (ψ := φf ≫ ψ) (h.trans (Eq.symm ?_))
    refine (Spec.map_comp _ _).trans ?_
    rw [Spec.map_preimage]
    rfl
  have hp₀ : fiberRoot p₀ = algebraMap L Ω t := by
    refine (key (CommRingCat.ofHom (algebraMap L Ω)) p₀ ?_)
    rw [← hq₀]
    exact (congrArg (· ≫ pullback.fst Y.hom j) hf).trans (Category.assoc _ _ _)
  have ht : algebraMap L Ω t = fiberRoot p₀ := hp₀.symm
  refine ⟨t, ht, fun σ => ?_⟩
  let σ' := galoisEquivEtaleFundamentalGroup K L Ω σ
  let φσ := galoisToFundamentalGroup (Spec (.of A)) L Ω σ
  have h5 : fiberRoot (φσ • p₀) = algebraMap L Ω (σ t) := by
    refine key (CommRingCat.ofHom σ.toAlgHom.toRingHom ≫ CommRingCat.ofHom (algebraMap L Ω)) _ ?_
    have h := etaleFundamentalGroupMap_finiteEtaleFiberProjection j x₀ Y σ' q₀
    rw [hq₀] at h
    refine (congrArg Subtype.val h).symm.trans ((congrArg (· ≫ pullback.fst Y.hom j)
      (galoisEquivEtaleFundamentalGroup_apply K L Ω Y' σ q₀ f hf)).trans ?_)
    rw [Spec.map_comp]
    exact (Category.assoc _ _ _).trans (congrArg
      (Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ ·) (Category.assoc _ _ _))
  rw [map_sub, ht, ← h5]
  exact sub_eq_of_eq_add' ((congrArg fiberRoot ((torsorCover k A g).smul_eq_character _ p₀ φσ
    p₀)).trans (fiberRoot_map_coverTranslate _ p₀))

end Stacks.ArtinSchreier
