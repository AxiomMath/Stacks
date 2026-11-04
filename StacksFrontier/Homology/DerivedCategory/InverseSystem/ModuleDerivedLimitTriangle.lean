module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact

/-!
# The defining triangle of a derived limit of modules, and the Milnor sequence

Let `R` be a ring and let `F : ℕᵒᵖ ⥤ D(ModuleCat R)` be a countable inverse system in the derived
category of `R`-modules. A *derived limit* of `F` is an object `K` fitting into a distinguished
triangle `K ⟶ ∏ₙ Fₙ ⟶ ∏ₙ Fₙ ⟶ K⟦1⟧` whose middle map is `1 - shift`, i.e. the predicate
`CategoryTheory.Pretriangulated.IsDerivedLimit`.

This file records the two basic facts about such an object: its isomorphism class does not depend
on the construction, and its cohomology sits in the Milnor short exact sequence
`0 ⟶ R¹ lim H^{r-1}(Fₙ) ⟶ Hʳ(K) ⟶ lim Hʳ(Fₙ) ⟶ 0`, where `R¹ lim` is the cokernel of `1 - shift`
on the product of the cohomology modules.

## Main definitions

There are no new definitions; the derived-limit predicate is
`CategoryTheory.Pretriangulated.IsDerivedLimit` and the Milnor sequence is supplied by
`DerivedCategory.isDerivedLimit_homology_shortExact`.

## Main results

* `ModuleDerivedLimitTriangle.derivedLimit_iso_and_homology_shortExact`: any two derived limits of
  one countable inverse system of complexes of modules are isomorphic, and every derived limit
  carries the Milnor short exact sequence in each degree, with the two maps characterized by the
  connecting morphism of the defining triangle and by the limit projections.

## Implementation notes

The statement is made for an arbitrary countable inverse system in the derived category of
modules; this is the invariant form of the Stacks remark, of which the situation there (a
compatible family `Kₙ ∈ D(Aₙ)`, lifted to the derived category of module systems and pushed
through the derived inverse limit) is an instance. Uniqueness is the standard rotation argument:
the two defining triangles have identical second and third vertices and identical middle map, so
`isoTriangleOfIso₁₂` on the rotated triangles produces an isomorphism of the shifted first
vertices, and the shift functor is fully faithful. Exactness of countable products in
`ModuleCat R` is what makes the Milnor sequence available.

## References

* [Stacks: Tag 07KZ](https://stacks.math.columbia.edu/tag/07KZ)
-/
@[expose] public noncomputable section

open CategoryTheory Limits Opposite

namespace ModuleDerivedLimitTriangle

open Pretriangulated

universe u v w

/-- **Stacks 07KZ.** Any two derived limits of the same countable inverse system of complexes of
modules are isomorphic. Moreover, after exhibiting a derived limit by its defining distinguished
triangle, for every `r : ℤ` there is a canonical short exact sequence
`0 ⟶ R¹ lim H⁽ʳ⁻¹⁾(Fₙ) ⟶ Hʳ(K) ⟶ lim Hʳ(Fₙ) ⟶ 0`.

Here `R¹ lim` is the cokernel of `1 - shift`. The left map is characterized as the factorization
of the connecting map of the defining triangle through that cokernel (using the canonical
comparison between the homology of a product and the product of the homologies), and the right
map is characterized by all its composites with the limit projections. -/
@[stacks 07KZ]
public theorem derivedLimit_iso_and_homology_shortExact
    (R : Type u) [Ring R] [HasDerivedCategory.{w} (ModuleCat.{max v u} R)]
    (F : CategoryTheory.Functor ℕᵒᵖ (DerivedCategory (ModuleCat.{max v u} R)))
    [HasProduct fun n : ℕ => F.obj (op n)] :
    (∀ (K K' : DerivedCategory (ModuleCat.{max v u} R)),
      Pretriangulated.IsDerivedLimit F K →
        Pretriangulated.IsDerivedLimit F K' → Nonempty (K ≅ K')) ∧
      ∀ (K : DerivedCategory (ModuleCat.{max v u} R)),
        Pretriangulated.IsDerivedLimit F K →
          let X : ℕ → DerivedCategory (ModuleCat.{max v u} R) := fun n ↦ F.obj (op n)
          let d : (∏ᶜ X) ⟶ ∏ᶜ X := Pi.lift fun n : ℕ ↦
            Pi.π X n - Pi.π X (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
          ∃ (a : K ⟶ ∏ᶜ X) (b : (∏ᶜ X) ⟶ K⟦(1 : ℤ)⟧),
            let T := Pretriangulated.Triangle.mk a d b
            T ∈ distTriang (DerivedCategory (ModuleCat.{max v u} R)) ∧
              ∀ r : ℤ,
                let H := DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) r
                let H₁ := DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) (r - 1)
                let homologySystem : ℕᵒᵖ ⥤ ModuleCat.{max v u} R := F ⋙ H
                let shiftedHomologySystem : ℕᵒᵖ ⥤ ModuleCat.{max v u} R := F ⋙ H₁
                let P : ModuleCat.{max v u} R :=
                  ∏ᶜ fun n : ℕ ↦ shiftedHomologySystem.obj (op n)
                let δ : P ⟶ P := Pi.lift fun n : ℕ ↦
                  Pi.π (fun n : ℕ ↦ shiftedHomologySystem.obj (op n)) n -
                    Pi.π (fun n : ℕ ↦ shiftedHomologySystem.obj (op n)) (n + 1) ≫
                      shiftedHomologySystem.map (homOfLE (Nat.le_succ n)).op
                ∃ (e : H₁.obj (∏ᶜ X) ≅ P)
                  (i : cokernel δ ⟶ H.obj K) (q : H.obj K ⟶ limit homologySystem)
                  (w : i ≫ q = 0),
                  e.hom = piComparison H₁ X ∧
                    cokernel.π δ ≫ i = e.inv ≫
                      DerivedCategory.HomologySequence.δ T (r - 1) r ∧
                    (∀ n : ℕ, q ≫ limit.π homologySystem (op n) =
                      H.map a ≫ H.map (Pi.π X n)) ∧
                    (ShortComplex.mk i q w).ShortExact := by
  refine ⟨fun K K' ⟨a, b, hT⟩ ⟨a', b', hT'⟩ => ?_, ?_⟩
  · let d := Pi.lift fun n : ℕ =>
      Pi.π (fun n : ℕ => F.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ => F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
    let T := Triangle.mk a d b
    let T' := Triangle.mk a' d b'
    let e := isoTriangleOfIso₁₂ T.rotate T'.rotate
      (rot_of_distTriang _ hT) (rot_of_distTriang _ hT') (Iso.refl _) (Iso.refl _)
      (by exact (Category.comp_id d).trans (Category.id_comp d).symm)
    exact ⟨(shiftFunctor (DerivedCategory (ModuleCat.{max v u} R)) (1 : ℤ)).preimageIso
      (Triangle.π₃.mapIso e)⟩
  · have : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{max v u} R) :=
      HasExactLimitsOfShape.domain_of_functor (Discrete ℕ)
        (forget₂ (ModuleCat.{max v u} R) AddCommGrpCat.{max v u})
    exact DerivedCategory.isDerivedLimit_homology_shortExact F

end ModuleDerivedLimitTriangle

end
