module

public import StacksFrontier.Cotangent.Triangle.ProductDescent

/-!
# The fundamental triangle from the base-changed resolution

[Stacks, Remark 08SD] sketches an alternative proof of the fundamental triangle
`L_{B/A} ⊗^𝐋_B C → L_{C/A} → L_{C/B} → (L_{B/A} ⊗^𝐋_B C)[1]` of a sequence of ring maps
`A → B → C`. It has two paragraphs, and this file states each of them whole.

**`B → C` injective.** Let `P_•` and `Q_•` be the standard resolutions of `B` and of `C` over `A`.
Then

* every `Q_n` is a polynomial algebra over `P_n`
  (`CommAlgCat.standardResolution_isPolynomialAlgebra`);
* `Q̄_• = Q_• ⊗_{P_•} B` is a resolution of `C` over `B` — the remark's *key fact*, from Tag 08RX
  applied on `Δ` to `P_• → B` and the flat `P_•`-module `Q_•`
  (`CommAlgCat.isResolution_baseChangedStandardResolution_of_injective`);
* the sequence of simplicial `C`-modules
  `0 → Ω_{P_•/A} ⊗_{P_•} C → Ω_{Q_•/A} ⊗_{Q_•} C → Ω_{Q̄_•/B} ⊗_{Q̄_•} C → 0`, deduced from the
  degreewise sequences of Algebra, Lemma 031K, is short exact
  (`CommAlgCat.cotangentDifferentialComplexes_shortExact`);
* the distinguished triangle associated to it **is** the fundamental triangle: it is isomorphic,
  as a triangle, to the triangle on the vertices `L_{B/A} ⊗^𝐋_B C`, `L_{C/A}`, `L_{C/B}` whose
  first two morphisms are the canonical maps `CommAlgCat.fundamentalMor₁` and
  `CommAlgCat.fundamentalMor₂` (`CommAlgCat.cotangentTriangleIsoFundamentalTriangle`). The third
  component of the isomorphism is the identification of the right-hand complex with `L_{C/B}`,
  which is where the key fact enters (through Remark 08QI and the comparison of Remark 08SE).

That is `CommAlgCat.fundamentalTriangle_of_injective`.

**`B → C` arbitrary.** The map `B → B × C`, `b ↦ (b, f b)`, is injective, so the first paragraph
gives the fundamental triangle of `A → B → B × C`. By Tag 08SC over the bases `A` and `B`,
`L_{B × C/A} → L_{B/A} ⊕ L_{C/A}` and `L_{B × C/B} → L_{B/B} ⊕ L_{C/B}` are isomorphisms, so base
change along the flat projection `B × C → C` carries that triangle to a distinguished triangle in
`D(C)` which is isomorphic to the fundamental triangle of `A → B → C`, with its canonical first two
morphisms. That is `CommAlgCat.fundamentalTriangle_of_productDescent`.

## Main definitions

* `CategoryTheory.Pretriangulated.Triangle.isoMkOfConj`: a triangle is isomorphic to the triangle
  obtained by conjugating its morphisms along isomorphisms of its vertices.
* `CommAlgCat.cotangentTriangleIsoFundamentalTriangle`: the triangle of the differential sequence
  is isomorphic to the fundamental triangle, for `B → C` injective.
* `CommAlgCat.productDescentTriangleIsoFundamentalTriangle`: the base change along `B × C → C` of
  the fundamental triangle of `A → B → B × C` is isomorphic to the fundamental triangle of
  `A → B → C`.

## Main results

* `CommAlgCat.fundamentalTriangle_of_injective`: **[Stacks, Remark 08SD], first paragraph.**
* `CommAlgCat.fundamentalTriangle_of_productDescent`: **[Stacks, Remark 08SD], second
  paragraph.**

## References

* [Stacks Project, Tag 08SD](https://stacks.math.columbia.edu/tag/08SD)
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
* [Stacks Project, Tag 08SC](https://stacks.math.columbia.edu/tag/08SC)
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
* [Stacks Project, Tag 031K](https://stacks.math.columbia.edu/tag/031K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace CategoryTheory.Pretriangulated.Triangle

/-- A triangle `T` is isomorphic to the triangle on the targets of three isomorphisms
`dᵢ : T.objᵢ ≅ Xᵢ` whose first two morphisms are the conjugates of those of `T` and whose third is
`d₃.inv ≫ T.mor₃ ≫ d₁.hom⟦1⟧'`; the components of the isomorphism are the `dᵢ`. -/
def isoMkOfConj {D : Type*} [Category* D] [HasShift D ℤ] (T : Triangle D) {X Y Z : D}
    (d₁ : T.obj₁ ≅ X) (d₂ : T.obj₂ ≅ Y) (d₃ : T.obj₃ ≅ Z) {α : X ⟶ Y} {β : Y ⟶ Z}
    (hα : d₁.inv ≫ T.mor₁ ≫ d₂.hom = α) (hβ : d₂.inv ≫ T.mor₂ ≫ d₃.hom = β) :
    T ≅ Triangle.mk α β (d₃.inv ≫ T.mor₃ ≫ d₁.hom⟦(1 : ℤ)⟧') :=
  Triangle.isoMk _ _ d₁ d₂ d₃ (by subst hα; simp) (by subst hβ; simp) (by simp)

end CategoryTheory.Pretriangulated.Triangle

namespace CommAlgCat

attribute [local instance] HasDerivedCategory.standard

section Tower

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/-- **The triangle of the differential sequence is the fundamental triangle**, for `B → C`
injective. The triangle in `D(C)` associated to the short exact sequence
`0 → Ω_{P_•/A} ⊗_{P_•} C → Ω_{Q_•/A} ⊗_{Q_•} C → Ω_{Q̄_•/B} ⊗_{Q̄_•} C → 0` is isomorphic to the
triangle `L_{B/A} ⊗^𝐋_B C → L_{C/A} → L_{C/B} → (L_{B/A} ⊗^𝐋_B C)[1]` whose first two morphisms
are the canonical maps. The components are the identification of the degreewise with the derived
base change of `L_{B/A}`, the identity of `L_{C/A}`, and the identification of
`Ω_{Q̄_•/B} ⊗_{Q̄_•} C` with `L_{C/B}`, which rests on `Q̄_•` being a resolution of `C`
over `B`. -/
def cotangentTriangleIsoFundamentalTriangle (hf : Function.Injective (algebraMap B C)) :
    cotangentTriangle A (towerHom A B C)
        (show Function.Injective (towerHom A B C).hom from hf) ≅
      Triangle.mk (fundamentalMor₁.{u} A B C) (fundamentalMor₂.{u} A B C)
        (fundamentalMor₃ A B C hf) :=
  Triangle.isoMkOfConj _
    (cotangentTriangle_obj₁DerivedBaseChangeIso A (towerHom A B C)
      (show Function.Injective (towerHom A B C).hom from hf))
    (Iso.refl _) (fundamentalDisplayVertex₃Iso A B C hf)
    ((congrArg (fun z =>
      (cotangentTriangle_obj₁DerivedBaseChangeIso A (towerHom A B C)
        (show Function.Injective (towerHom A B C).hom from hf)).inv ≫ z)
        (Category.comp_id _)).trans (cotangentTriangle_mor₁_eq_fundamentalMor₁ A B C hf))
    ((Category.id_comp _).trans (fundamentalDisplayMor₂_eq_fundamentalMor₂ A B C hf))

/-- **Stacks Project, Remark 08SD, first paragraph.** Let `A → B → C` be ring maps with `B → C`
injective, let `P_• → B` be the standard resolution of `B` over `A`, `Q_• → C` that of `C` over
`A`, and `Q̄_• = Q_• ⊗_{P_•} B`. Then

1. every `Q_n` is a polynomial algebra over `P_n`;
2. `Q̄_• → C` is a resolution of `C` over `B` (the key fact);
3. the sequence of complexes of `C`-modules
   `0 → Ω_{P_•/A} ⊗_{P_•} C → Ω_{Q_•/A} ⊗_{Q_•} C → Ω_{Q̄_•/B} ⊗_{Q̄_•} C → 0` is short exact;
4. the distinguished triangle associated to that short exact sequence is isomorphic to the
   fundamental triangle `L_{B/A} ⊗^𝐋_B C → L_{C/A} → L_{C/B} → (L_{B/A} ⊗^𝐋_B C)[1]` with its
   canonical first two morphisms, which is therefore distinguished in `D(C)`. -/
@[stacks 08SD "the first paragraph of the remark, for `A → B → C` with `B → C` injective: `Q_n` \
  is polynomial over `P_n`; `Q̄_• = Q_• ⊗_{P_•} B` is a resolution of `C` over `B`; \
  the sequence of \
  differentials is short exact; and its triangle is the fundamental triangle, with the canonical \
  first two morphisms, on the vertices `L_{B/A} ⊗^𝐋_B C`, `L_{C/A}`, `L_{C/B}`"]
theorem fundamentalTriangle_of_injective (hf : Function.Injective (algebraMap B C)) :
    (∀ n : SimplexCategoryᵒᵖ,
      letI : Algebra ((standardResolution A (CommAlgCat.of A B)).left.obj n)
          ((standardResolution A (CommAlgCat.of A C)).left.obj n) :=
        (((standardResolutionFunctor A).map (towerHom A B C)).left.app n).hom.toAlgebra
      IsPolynomialAlgebra ((standardResolution A (CommAlgCat.of A B)).left.obj n)
        (CommAlgCat.of ((standardResolution A (CommAlgCat.of A B)).left.obj n)
          ((standardResolution A (CommAlgCat.of A C)).left.obj n))) ∧
    @IsResolution ↥(CommAlgCat.of A B) (CommAlgCat.of A B).commRing
      ↥(algebraOver (towerHom A B C)) (algebraOver (towerHom A B C)).commRing
      (algebraOver (towerHom A B C)).algebra
      (baseChangedStandardResolution A (towerHom A B C)).left
      (baseChangedStandardResolution A (towerHom A B C)).hom ∧
    (cotangentDifferentialComplexes A (towerHom A B C)).ShortExact ∧
    Nonempty (cotangentTriangle A (towerHom A B C)
        (show Function.Injective (towerHom A B C).hom from hf) ≅
      Triangle.mk (fundamentalMor₁.{u} A B C) (fundamentalMor₂.{u} A B C)
        (fundamentalMor₃ A B C hf)) ∧
    Triangle.mk (fundamentalMor₁.{u} A B C) (fundamentalMor₂.{u} A B C)
        (fundamentalMor₃ A B C hf) ∈ distTriang (DerivedCategory (ModuleCat.{u} C)) :=
  ⟨standardResolution_isPolynomialAlgebra.{u, u} A (towerHom A B C) hf,
    isResolution_baseChangedStandardResolution_of_injective (towerHom A B C) hf,
    cotangentDifferentialComplexes_shortExact A (towerHom A B C) hf,
    ⟨cotangentTriangleIsoFundamentalTriangle A B C hf⟩,
    isomorphic_distinguished _
      (cotangentTriangle_distinguished A (towerHom A B C)
        (show Function.Injective (towerHom A B C).hom from hf)) _
      (cotangentTriangleIsoFundamentalTriangle A B C hf).symm⟩

/-- The fundamental triangle of `A → B → B × C`, where `B → B × C` is `b ↦ (b, f b)`, base changed
along the projection `B × C → C`. -/
abbrev productDescentTriangle : Triangle (DerivedCategory (ModuleCat.{u} C)) :=
  (ModuleCat.extendScalars.{u, u, u} (RingHom.snd B C)).mapDerivedCategory.mapTriangle.obj
    (Triangle.mk (fundamentalMor₁.{u} A B (B × C)) (fundamentalMor₂.{u} A B (B × C))
      (fundamentalMor₃ A B (B × C) (injective_algebraMap_prod B C)))

/-- **The descended triangle is the fundamental triangle.** The base change along `B × C → C` of
the fundamental triangle of `A → B → B × C` is isomorphic to the fundamental triangle of
`A → B → C` with its canonical first two morphisms; the components are the identifications of the
three base-changed vertices, the last two of which are Tag 08SC over the bases `A` and `B`. -/
def productDescentTriangleIsoFundamentalTriangle :
    productDescentTriangle A B C ≅
      Triangle.mk (fundamentalMor₁.{u} A B C) (fundamentalMor₂.{u} A B C)
        (productFundamentalMor₃ A B C) :=
  let e := Triangle.isoMkOfConj (productDescentTriangle A B C) (descentIso₁ A B C)
    (descentIso₂ A B C) (descentIso₃ B C)
    (productDisplayMor₁_eq_fundamentalMor₁ A B C) (productDisplayMor₂_eq_fundamentalMor₂ A B C)
  e

/-- **Stacks Project, Remark 08SD, second paragraph.** Let `A → B → C` be arbitrary ring maps.
Then `B → B × C`, `b ↦ (b, f b)`, is injective, so the first paragraph gives the fundamental
triangle of `A → B → B × C`; its base change along the flat ring map `B × C → C` is a
distinguished triangle in `D(C)`, and by Tag 08SC it is isomorphic to the fundamental triangle
`L_{B/A} ⊗^𝐋_B C → L_{C/A} → L_{C/B} → (L_{B/A} ⊗^𝐋_B C)[1]` with its canonical first two
morphisms, which is therefore distinguished. -/
@[stacks 08SD "the second paragraph of the remark, for arbitrary `A → B → C`: `B → B × C` is \
  injective, the base change along the flat `B × C → C` of the fundamental triangle of \
  `A → B → B × C` is distinguished in `D(C)` and, by Tag 08SC, isomorphic to the fundamental \
  triangle of `A → B → C` with its canonical first two morphisms"]
theorem fundamentalTriangle_of_productDescent :
    Function.Injective (algebraMap B (B × C)) ∧
    productDescentTriangle A B C ∈ distTriang (DerivedCategory (ModuleCat.{u} C)) ∧
    Nonempty (productDescentTriangle A B C ≅
      Triangle.mk (fundamentalMor₁.{u} A B C) (fundamentalMor₂.{u} A B C)
        (productFundamentalMor₃ A B C)) ∧
    Triangle.mk (fundamentalMor₁.{u} A B C) (fundamentalMor₂.{u} A B C)
        (productFundamentalMor₃ A B C) ∈ distTriang (DerivedCategory (ModuleCat.{u} C)) :=
  have hT : productDescentTriangle A B C ∈ distTriang (DerivedCategory (ModuleCat.{u} C)) :=
    (ModuleCat.extendScalars.{u, u, u} (RingHom.snd B C)).mapDerivedCategory.map_distinguished _
      (fundamentalTriangle_of_injective A B (B × C) (injective_algebraMap_prod B C)).2.2.2.2
  ⟨injective_algebraMap_prod B C, hT, ⟨productDescentTriangleIsoFundamentalTriangle A B C⟩,
    isomorphic_distinguished _ hT _ (productDescentTriangleIsoFundamentalTriangle A B C).symm⟩

end Tower

end CommAlgCat

end
