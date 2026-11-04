module

public import StacksFrontier.AlgebraicGeometry.RestrictScalarsColimits.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.PredicateDevissage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.BiproductSum
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.DirectSummands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.DistinguishedTriangles
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.ShiftedUnitLeftFactor

/-!
# Tensoring with a strictly perfect complex bounds the Tor amplitude over a subring

Let `(C, J)` be a site with two sheaves of rings `O₁` and `O₂` and a map `ψ : O₁ ⟶ O₂`, and let
`N` be an object of `D(O₂)` which, read over `O₁` through restriction of scalars along `ψ`, has
Tor amplitude in `[c, e]`. If `P` is a strictly perfect complex of `O₂`-modules whose nonzero
terms sit in degrees `[p, q]`, then `P ⊗^𝐋_{O₂} N`, read over `O₁`, has Tor amplitude in
`[c + p, e + q]`.

This is the local step of the second assertion of Stacks 0DKS (and of Stacks 0DI4): with
`O₁ = f⁻¹𝒪_Y` and `O₂ = 𝒪_X`, a perfect object is locally a strictly perfect complex, and the
statement bounds the Tor amplitude over `f⁻¹𝒪_Y` of its derived tensor product with a
`Y`-perfect object there.

## Main results

* `DerivedTensorProduct.hasTorAmplitude_restrictScalars_tensor_of_isStrictlyPerfect`:
  the statement above.

## Implementation notes

The proof is the dévissage of Stacks 08FL in predicate form,
`Stacks.Cohomology.StrictlyPerfectDevissage.property_of_isStrictlyPerfect`, applied to the
property "`A ⊗^𝐋_{O₂} N`, read over `O₁`, has Tor amplitude in `[c + p, e + q]`". Its closure
properties hold because `- ⊗^𝐋_{O₂} N` and derived restriction of scalars are both exact
functors: a retract goes to a retract (`hasTorAmplitude_of_retract`), a finite direct sum to a
finite direct sum (`hasTorAmplitude_biproduct`), and a distinguished triangle to a
distinguished triangle (Stacks 08G2 (2), `hasTorAmplitude_obj₂`). The base case is
`O₂[i] ⊗^𝐋_{O₂} N ≅ N⟦-i⟧` (`shiftedUnitLeftIso`), whose restriction of scalars is
`(N read over O₁)⟦-i⟧`, of Tor amplitude `[c + i, e + i] ⊆ [c + p, e + q]`.

## References

* [Stacks Project, Tag 0DKS](https://stacks.math.columbia.edu/tag/0DKS)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08G2](https://stacks.math.columbia.edu/tag/08G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

namespace Stacks.SheafOfModules.DerivedTensorProduct

universe u d₁ d₂

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {O₁ O₂ : Sheaf J CommRingCat.{u}}
  [HasDerivedCategory.{d₁} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₁))]
  [HasDerivedCategory.{d₂} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} O₁).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} O₁).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₁)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor O₁)
      (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} O₂).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} O₂).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor O₂)
      (ComplexShape.up ℤ)]
  (ψ : Stacks.SheafOfModules.Tensor.ringSheaf O₁ ⟶ Stacks.SheafOfModules.Tensor.ringSheaf O₂)

/-- **Tensoring with a strictly perfect complex bounds the Tor amplitude over a subring.** Let
`ψ : O₁ ⟶ O₂` be a map of sheaves of rings on a site, `T₁` and `T₂` derived tensor products over
`O₁` and `O₂`, and `N` an object of `D(O₂)` which, read over `O₁`, has Tor amplitude in
`[c, e]`. If `P` is a strictly perfect complex of `O₂`-modules whose nonzero terms lie in degrees
`[p, q]`, then `P ⊗^𝐋_{O₂} N`, read over `O₁`, has Tor amplitude in `[c + p, e + q]`.

This is the dévissage of Stacks 08FL: the property is stable under isomorphisms, retracts,
finite direct sums and extensions because `- ⊗^𝐋_{O₂} N` and restriction of scalars are exact,
and at `O₂[i]` it is the Tor amplitude of a shift of `N`. -/
theorem hasTorAmplitude_restrictScalars_tensor_of_isStrictlyPerfect
    (T₁ : DerivedTensorProduct.{u + 1, u, u, d₁} (RingedSite.mk C J O₁))
    (T₂ : DerivedTensorProduct.{u + 1, u, u, d₂} (RingedSite.mk C J O₂))
    (N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)))
    (c e : ℤ)
    (hN : HasTorAmplitude T₁ ((SheafOfModules.restrictScalars.{u} ψ).mapDerivedCategory.obj N)
      c e)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) ℤ)
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf O₂) P) (p q : ℤ)
    (hpq : ∀ i : ℤ, ¬ IsZero (P.X i) → p ≤ i ∧ i ≤ q) :
    HasTorAmplitude T₁ ((SheafOfModules.restrictScalars.{u} ψ).mapDerivedCategory.obj
      ((T₂.tensor.obj (DerivedCategory.Q.obj P)).obj N)) (c + p) (e + q) := by
  let rs := (SheafOfModules.restrictScalars.{u} ψ).mapDerivedCategory
  let := T₂.commShift₂.commShiftFlipObj N
  have : (T₂.tensor.flip.obj N).IsTriangulated := T₂.exact_left N
  let G := T₂.tensor.flip.obj N ⋙ rs
  let Pr : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) →
      Prop := fun A => HasTorAmplitude T₁ (G.obj A) (c + p) (e + q)
  refine Stacks.Cohomology.StrictlyPerfectDevissage.property_of_isStrictlyPerfect O₂ Pr
    (fun A B eAB h => h.of_iso (G.mapIso eAB)) (fun A hA => ?_)
    (fun A B i r hir h => hasTorAmplitude_of_retract T₁ (G.map i) (G.map r)
      (by rw [← G.map_comp, hir, G.map_id]) _ _ h)
    (fun {ι} _ f _ hf => ?_) (fun tri htri h₁ h₃ => ?_) P hP (fun i hi => ?_)
  · -- a zero object goes to a zero object, and tensoring a zero object gives a zero object
    intro F i _
    let F₀ := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₁)) 0).obj F
    let := T₁.commShift₂.commShiftFlipObj F₀
    have : (T₁.tensor.flip.obj F₀).IsTriangulated := T₁.exact_left F₀
    exact Functor.map_isZero _ ((T₁.tensor.flip.obj F₀).map_isZero (G.map_isZero hA))
  · exact (hasTorAmplitude_biproduct T₁ (fun j => G.obj (f j)) _ _ hf).of_iso
      (G.mapBiproduct f).symm
  · exact hasTorAmplitude_obj₂ T₁ (rs.mapTriangle.obj ((T₂.tensor.flip.obj N).mapTriangle.obj tri))
      (rs.map_distinguished _ ((T₂.tensor.flip.obj N).map_distinguished tri htri)) _ _ h₁ h₃
  · obtain ⟨hpi, hiq⟩ := hpq i hi
    exact ((hasTorAmplitude_shift (-i) hN).mono (by omega) (by omega)).of_iso
      (((rs.commShiftIso (-i)).app N).symm ≪≫ rs.mapIso (T₂.shiftedUnitLeftIso N i).symm)

end Stacks.SheafOfModules.DerivedTensorProduct

end
