module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceSiteObject

/-!
# Two affine-space bundles over a common middle object (Stacks 0F9U, step 2)

Let `p : T₁ → V` and `q : T' → Y'` be affine-space bundles in the sense of Stacks 0F82, of
relative dimensions `n₁` and `n'`, with `T₁` and `T'` affine, and let `V'` be a scheme with affine
morphisms `V' → V` and `V' → Y'`. Then the fibre products `T₁ ×_V V'` and `V' ×_{Y'} T'` are
affine, and there is the chain of isomorphisms of Stacks 0F9U, step 2:

```
A^{n'}_{T₁ ×_V V'}  ≅  T₁ ×_V V' ×_{Y'} T'  ≅  A^{n₁}_{V' ×_{Y'} T'}
```

The two spellings of the middle term differ by associativity and symmetry of fibre products,
`CategoryTheory.Limits.pullbackAssoc` and `CategoryTheory.Limits.pullbackSymmetry`.

## Main results

* `AlgebraicGeometry.exists_iso_over_affineSpace_of_affineSpaceBundles`: affine `n'`-space over
  `T₁ ×_V V'` is isomorphic over `V'` to affine `n₁`-space over `V' ×_{Y'} T'`.
* `AlgebraicGeometry.exists_iso_affineSpace_of_affineSpaceBundles`: the same isomorphism of
  schemes, without the compatibility over `V'`.

## Implementation notes

The hypotheses on the two bundles have the form of
`AlgebraicGeometry.exists_contains_affine_pullback_iso_affineSpace` (Stacks 0F82): for every
morphism `k : X' ⟶ V` from an affine scheme, an isomorphism in `CategoryTheory.Over X'` between
`Over.mk (pullback.fst k p)` and `Over.mk (AffineSpace.over _ X').hom`.

## References

* [Stacks Project, Tag 0F82](https://stacks.math.columbia.edu/tag/0F82)
* [Stacks Project, Tag 0F9U](https://stacks.math.columbia.edu/tag/0F9U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks 0F9U, step 2: the displayed chain of isomorphisms.** Let `p : T₁ ⟶ V` and
`q : T' ⟶ Y'` be affine-space bundles in the sense of Stacks 0F82, of relative dimensions `n₁`
and `n'`, with `T₁` and `T'` affine. Let `V'` be an object with affine morphisms `v : V' ⟶ V` and
`y : V' ⟶ Y'`. Then affine `n'`-space over `T₁ ×_V V'` is isomorphic over `V'` to affine `n₁`-space
over `V' ×_{Y'} T'`:

```
A^{n'}_{T₁ ×_V V'} ≅ T₁ ×_V V' ×_{Y'} T' ≅ A^{n₁}_{V' ×_{Y'} T'}
```
-/
theorem exists_iso_over_affineSpace_of_affineSpaceBundles {n₁ n' : ℕ}
    {V V' Y' T₁ T' : Scheme.{u}}
    (p : T₁ ⟶ V) (q : T' ⟶ Y') (v : V' ⟶ V) (y : V' ⟶ Y')
    (hT₁ : IsAffine T₁) (hT' : IsAffine T')
    (hv : IsAffineHom v) (hy : IsAffineHom y)
    (hp : ∀ (X' : Scheme.{u}) (_ : IsAffine X') (k : X' ⟶ V),
      Nonempty (Over.mk (pullback.fst k p) ≅
        Over.mk (AffineSpace.over (ULift.{u} (Fin n₁)) X').hom))
    (hq : ∀ (X' : Scheme.{u}) (_ : IsAffine X') (k : X' ⟶ Y'),
      Nonempty (Over.mk (pullback.fst k q) ≅
        Over.mk (AffineSpace.over (ULift.{u} (Fin n')) X').hom)) :
    Nonempty
      ((Over.mk ((𝔸(ULift.{u} (Fin n'); pullback p v) ↘ pullback p v) ≫
          pullback.snd p v) : Over V') ≅
        Over.mk ((𝔸(ULift.{u} (Fin n₁); pullback y q) ↘ pullback y q) ≫
          pullback.fst y q)) := by
  obtain ⟨eA⟩ := hq (pullback p v) inferInstance (pullback.snd p v ≫ y)
  obtain ⟨eB⟩ := hp (pullback y q) inferInstance (pullback.fst y q ≫ v)
  have hwA : eA.inv.left ≫ pullback.fst (pullback.snd p v ≫ y) q =
      𝔸(ULift.{u} (Fin n'); pullback p v) ↘ pullback p v := Over.w eA.inv
  have hwB : eB.hom.left ≫ (𝔸(ULift.{u} (Fin n₁); pullback y q) ↘ pullback y q) =
      pullback.fst (pullback.fst y q ≫ v) p := Over.w eB.hom
  refine ⟨Over.isoMk (((Over.forget _).mapIso eA).symm ≪≫
    pullbackAssoc p v y q ≪≫ pullbackSymmetry _ _ ≪≫ (Over.forget _).mapIso eB) ?_⟩
  change (eA.inv.left ≫ (pullbackAssoc p v y q).hom ≫
      (pullbackSymmetry p (pullback.fst y q ≫ v)).hom ≫ eB.hom.left) ≫
      (𝔸(ULift.{u} (Fin n₁); pullback y q) ↘ pullback y q) ≫ pullback.fst y q =
    (𝔸(ULift.{u} (Fin n'); pullback p v) ↘ pullback p v) ≫ pullback.snd p v
  rw [Category.assoc, Category.assoc, Category.assoc, ← Category.assoc eB.hom.left, hwB,
    ← Category.assoc (pullbackSymmetry p (pullback.fst y q ≫ v)).hom,
    pullbackSymmetry_hom_comp_fst, pullbackAssoc_hom_snd_fst, ← Category.assoc, hwA]

/-- **Stacks 0F9U, step 2: the displayed chain, on total spaces.** The underlying schemes of
`AlgebraicGeometry.exists_iso_over_affineSpace_of_affineSpaceBundles`, with the compatibility
over `V'` forgotten. -/
theorem exists_iso_affineSpace_of_affineSpaceBundles {n₁ n' : ℕ} {V V' Y' T₁ T' : Scheme.{u}}
    (p : T₁ ⟶ V) (q : T' ⟶ Y') (v : V' ⟶ V) (y : V' ⟶ Y')
    (hT₁ : IsAffine T₁) (hT' : IsAffine T')
    (hv : IsAffineHom v) (hy : IsAffineHom y)
    (hp : ∀ (X' : Scheme.{u}) (_ : IsAffine X') (k : X' ⟶ V),
      Nonempty (Over.mk (pullback.fst k p) ≅
        Over.mk (AffineSpace.over (ULift.{u} (Fin n₁)) X').hom))
    (hq : ∀ (X' : Scheme.{u}) (_ : IsAffine X') (k : X' ⟶ Y'),
      Nonempty (Over.mk (pullback.fst k q) ≅
        Over.mk (AffineSpace.over (ULift.{u} (Fin n')) X').hom)) :
    Nonempty (𝔸(ULift.{u} (Fin n'); pullback p v) ≅
      𝔸(ULift.{u} (Fin n₁); pullback y q)) :=
  (exists_iso_over_affineSpace_of_affineSpaceBundles p q v y hT₁ hT' hv hy hp hq).map
    (Over.forget V').mapIso

end AlgebraicGeometry

end
