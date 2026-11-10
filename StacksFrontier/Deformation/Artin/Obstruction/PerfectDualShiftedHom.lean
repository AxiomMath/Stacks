module

public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.CochainAction
public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClass
public import StacksFrontier.Deformation.Artin.Obstruction.PerfectDualTensor

/-!
# Perfect duality in every degree, read on shifted morphisms

Let `P` be a perfect object of `D(A)`. Perfect duality ([Stacks, Tag 07VI]) provides a perfect
`K` with `H⁰(X ⊗ᴸ K) ≅ Hom_{D(A)}(P, X)` naturally in `X`. Shifting gives

`Hⁿ(X ⊗ᴸ K) ≅ Hom_{D(A)}(P, X[n])`

for every `n`, naturally in `X`, and these identifications carry the connecting maps of the
long exact cohomology sequence of `(- ⊗ᴸ K)` applied to a triangle `X₁ → X₂ → X₃ → X₁[1]` to
composition with its third morphism. This is the form in which the complex `K` of a dual
deformation situation (Stacks 07YX) is produced in the first proof of Stacks 08WA: there the
groups `Hom(P, M[n])` are Ext groups computed on the base change `X_A`.

## Main results

* `Deformation.Artin.exists_perfect_shiftedHomEquiv`: for perfect `P` there are a perfect `K`
  and additive bijections `Hⁿ(X ⊗ᴸ K) ≃+ ShiftedHom P X n`, natural in `X` and carrying the
  connecting maps to composition with the third morphism of the triangle.

## Implementation notes

The identifications are written through the universal element `u ∈ H⁰(P ⊗ᴸ K)` corresponding
to the identity of `P`: the class corresponding to `f : P ⟶ X[n]` is the image of `u` under the
shifted map `H⁰(P ⊗ᴸ K) ⟶ Hⁿ(X ⊗ᴸ K)` induced by `f`. Naturality and the compatibility with the
connecting maps are then the functoriality of shifted maps, `ShiftedHom.map_comp` and
`CategoryTheory.Functor.shiftMap_comp_shiftMap`; no sign enters.

## References

* [Stacks Project, Tag 07VI](https://stacks.math.columbia.edu/tag/07VI)
* [Stacks Project, Tag 07YX](https://stacks.math.columbia.edu/tag/07YX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Deformation.Artin

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A]

/-- **Perfect duality in every degree.** For a perfect object `P` of `D(A)` there are a perfect
`K` and additive bijections `Hⁿ(X ⊗ᴸ K) ≃+ Hom_{D(A)}(P, X[n])`, natural in `X`, which carry the
connecting map `H¹(X₃ ⊗ᴸ K) ⟶ H²(X₁ ⊗ᴸ K)` of a triangle `X₁ → X₂ → X₃ → X₁[1]` to composition
with its third morphism. -/
theorem exists_perfect_shiftedHomEquiv (P : DerivedCategory (ModuleCat.{u} A))
    (hP : StacksDraft.Perfect.IsPerfect P) :
    ∃ (K : DerivedCategory (ModuleCat.{u} A)), StacksDraft.Perfect.IsPerfect K ∧
      ∃ Ψ : ∀ (n : ℤ) (X : DerivedCategory (ModuleCat.{u} A)),
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
            ((CochainComplex.DerivedTensor.derivedTensorProduct K).obj X) : Type u) ≃+
            ShiftedHom P X n,
        (∀ (n : ℤ) (X Y : DerivedCategory (ModuleCat.{u} A)) (g : X ⟶ Y)
          (a : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
            ((CochainComplex.DerivedTensor.derivedTensorProduct K).obj X)),
          Ψ n Y ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
              ((CochainComplex.DerivedTensor.derivedTensorProduct K).map g) a) =
            (Ψ n X a).comp (ShiftedHom.mk₀ (0 : ℤ) rfl g) (zero_add n)) ∧
        (∀ (T : Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u} A)))
          (a : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).obj
            ((CochainComplex.DerivedTensor.derivedTensorProduct K).obj T.obj₃)),
          Ψ 2 T.obj₁ ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).homologySequenceδ
              ((CochainComplex.DerivedTensor.derivedTensorProduct K).mapTriangle.obj T) 1 2
              (by omega) a) =
            (Ψ 1 T.obj₃ a).comp T.mor₃ (by omega)) := by
  obtain ⟨K, hK, Φ, hΦ⟩ := exists_perfect_homologyZeroEquiv A P hP
  let G := CochainComplex.DerivedTensor.derivedTensorProduct K
  let H0 := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  -- the universal element
  let uP : (H0.obj (G.obj P) : Type u) := (Φ P).symm (𝟙 P)
  have hsymm : ∀ (X : DerivedCategory (ModuleCat.{u} A)) (g : P ⟶ X),
      (Φ X).symm g = H0.map (G.map g) uP := by
    intro X g
    apply (Φ X).injective
    rw [AddEquiv.apply_symm_apply, hΦ P X g uP, AddEquiv.apply_symm_apply, Category.id_comp]
  -- the inverse bijection
  let Ψinv : ∀ (n : ℤ) (X : DerivedCategory (ModuleCat.{u} A)),
      ShiftedHom P X n ≃+ ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        (G.obj X) : Type u) := fun n X =>
    ((Φ (X⟦n⟧)).symm.trans
      (H0.mapIso ((G.commShiftIso n).app X)).toLinearEquiv.toAddEquiv).trans
      ((H0.shiftIso n 0 n (add_zero n)).app (G.obj X)).toLinearEquiv.toAddEquiv
  have hΨinv : ∀ (n : ℤ) (X : DerivedCategory (ModuleCat.{u} A)) (f : ShiftedHom P X n),
      Ψinv n X f = H0.shiftMap (f.map G) 0 n (add_zero n) uP := by
    intro n X f
    change ((H0.shiftIso n 0 n (add_zero n)).app (G.obj X)).hom
        (H0.map ((G.commShiftIso n).app X).hom ((Φ (X⟦n⟧)).symm f)) = _
    rw [hsymm]
    simp only [Functor.shiftMap, ShiftedHom.map, Functor.map_comp]
    rfl
  refine ⟨K, hK, fun n X => (Ψinv n X).symm, ?_, ?_⟩
  · intro n X Y g a
    obtain ⟨f, rfl⟩ := (Ψinv n X).surjective a
    rw [AddEquiv.symm_apply_apply]
    apply (Ψinv n Y).injective
    rw [AddEquiv.apply_symm_apply, hΨinv, hΨinv, ShiftedHom.map_comp, ShiftedHom.map_mk₀,
      ShiftedHom.comp_mk₀, Functor.shiftMap_comp]
    rfl
  · intro T a
    obtain ⟨f, rfl⟩ := (Ψinv 1 T.obj₃).surjective a
    have key : ∀ y : ShiftedHom P T.obj₃ 1,
        H0.homologySequenceδ (G.mapTriangle.obj T) 1 2 (by omega)
            (H0.shiftMap (y.map G) 0 1 (add_zero 1) uP) =
          H0.shiftMap ((y.comp T.mor₃ (by omega)).map G) 0 2 (add_zero 2) uP := by
      intro y
      rw [ShiftedHom.map_comp]
      change (H0.shiftMap (y.map G) 0 1 (add_zero 1) ≫
        H0.shiftMap (ShiftedHom.map (show ShiftedHom T.obj₃ T.obj₁ (1 : ℤ) from T.mor₃) G) 1 2
          (show (1 : ℤ) + 1 = 2 by norm_num)) uP = _
      rw [H0.shiftMap_comp_shiftMap (y.map G)
        (ShiftedHom.map (show ShiftedHom T.obj₃ T.obj₁ (1 : ℤ) from T.mor₃) G) 2
          (show (1 : ℤ) + 1 = 2 by norm_num)]
      rfl
    refine ((AddEquiv.symm_apply_eq _).2 ?_).trans
      (congrArg (fun y : ShiftedHom P T.obj₃ 1 => y.comp T.mor₃ (by omega))
        ((Ψinv 1 T.obj₃).symm_apply_apply f)).symm
    change H0.homologySequenceδ (G.mapTriangle.obj T) 1 2 (by omega) (Ψinv 1 T.obj₃ f) =
      Ψinv 2 T.obj₁ (f.comp T.mor₃ (by omega))
    rw [hΨinv 2 T.obj₁, ← key f]
    exact congrArg _ (hΨinv 1 T.obj₃ f)

end Deformation.Artin

end
