module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.Resolution
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCohomologyProductCycles

/-!
# The cohomology product of a derived tensor product is natural in the derived category

Let `(X, O_X)` be a ringed space. `Stacks.SheafOfModules.derivedCohomologyTensorProduct` is the
pairing

`Hⁱ(K) ⊗_{O_X} Hʲ(L) ⟶ Hⁱ⁺ʲ(K ⊗^L_{O_X} L)`

formed on the *chosen* K-flat representatives of `K` and `L`. Those representatives are a
`Classical.choose`, and K-flat replacement is not functorial, so nothing about the pairing was
natural in `K` and `L`. This file proves that it is.

## Main definitions

* `Stacks.SheafOfModules.kFlatTensorHomology`: the same pairing for two K-flat complexes,
  computed on those complexes themselves rather than on the chosen representatives.

## Main results

* `Stacks.SheafOfModules.kFlatTensorHomology_naturality`: the K-flat pairing is natural in
  morphisms of complexes.
* `Stacks.SheafOfModules.exists_kFlat_roof`: a morphism of the derived category between the
  classes of two complexes is a right fraction whose apex is K-flat.
* `Stacks.SheafOfModules.kFlatTensorHomology_naturality_derived`: the K-flat pairing is natural
  in arbitrary morphisms of the derived category between the classes of K-flat complexes.
* `Stacks.SheafOfModules.derivedCohomologyTensorProduct_naturality`: **the cohomology product of
  a derived tensor product is natural in both variables in `D(O_X)`.**
* `Stacks.SheafOfModules.homologyComposition_strictlyPerfectHomComparison`: **the composition
  product on Ext sheaves is the cycle-level composition pairing of internal Hom complexes, read
  through the comparison of Stacks 08JH.** This is what the naturality was needed for: the
  derived composition product `Stacks.SheafOfModules.sheafExtProduct` pairs on the derived
  internal Homs `RSheafHom(L, M)` and `RSheafHom(K, L)`, the cycle-level pairing
  `Stacks.SheafOfModules.homologyComposition` pairs on the classes of the internal Hom complexes
  `SheafHom^•(L, M)` and `SheafHom^•(K, L)`, and moving the pairing between the two along
  `Stacks.SheafOfModules.strictlyPerfectHomComparison` is an instance of that naturality.

## Implementation notes

**Why the chosen representative is not in the way.** The pairing is defined from
`Stacks.SheafOfModules.tensorComplexHomology` on the chosen representatives, conjugated by the
identification `Stacks.SheafOfModules.kFlatRepresentativeIso` of each representative with the
object it represents. Factoring that conjugation out — `kFlatTensorHomology` below, together
with `Stacks.SheafOfModules.derivedCohomologyTensorProduct_eq` — leaves a construction attached
to two K-flat complexes and no choice at all, and the naturality of the pairing becomes the
naturality of *that* in morphisms of the derived category between the classes of two K-flat
complexes.

**How a morphism of the derived category is handled.** It does not lift to a morphism of
complexes, and a K-flat complex is not K-injective, so `CochainComplex.realizeDerivedIso` does
not apply. The morphism is written as a right fraction `inv (Q s₀) ≫ Q g₀`
(`CategoryTheory.DerivedCategory.right_fac`) and the apex of that roof is replaced by a K-flat
resolution of it (Stacks 06YS, `Stacks.SheafOfModules.exists_kFlat_quasiIso`), which gives a roof
`P ⟵ P₁ ⟶ P'` with all three complexes K-flat and the left leg invertible in `D(O_X)`. The
square for a morphism of complexes between K-flat complexes is available at each leg, and the
square for the given morphism follows by cancelling the invertible leg. This is the idiom
`AlgebraicGeometry.RingedSite.canonicalDerivedDiagonal_natural_left` uses, for the same reason.

**What the square for a morphism of complexes rests on.** Three inputs, none of which needs a
quasi-isomorphism: naturality of `CategoryTheory.DerivedCategory.homologyFunctorFactors`, the
chain-level naturality `CochainComplex.tensorHomology_naturality` of the product induced by
tensoring cocycles, and the naturality of the K-flat comparison of the derived tensor
product, `Stacks.SheafOfModules.DerivedTensorProduct.comparison_naturality`, which is stated for
morphisms of complexes between K-flat complexes and so applies at all four vertices of the
square.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0A8V](https://stacks.math.columbia.edu/tag/0A8V)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Category Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

attribute [local instance_reducible] CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive monoidalSpace' symmetricSpace'
  monoidalPreadditiveSpace' monoidalClosedSpace' preservesColimitTensorRightSpace'
  preservesFiniteColimitsTensorRight' preservesFiniteColimitsTensorLeft'
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- `⊗_{O_X}` preserves the zero morphism in its first variable, at the spelling
`StructureSheafModules Rc` of its three categories -- the spelling the complexes below are
stated in, and so the one the total-complex machinery asks the instance for.  Two things are
named here that instance search does not take on its own: the step from
`CategoryTheory.Functor.Additive` to `CategoryTheory.Functor.PreservesZeroMorphisms`, as it is
named beside every other consumer of `Stacks.SheafOfModules.Tensor.sheafTensor`; and the
additivity itself, handed over from
`Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive`, which states it at the
`SheafOfModules (Tensor.ringSheaf Rc)` spelling of the same three categories. -/
local instance sheafTensorPreservesZero :
    Functor.PreservesZeroMorphisms (Tensor.sheafTensor.{u, u, u, u, u} Rc :
      StructureSheafModules Rc ⥤ StructureSheafModules Rc ⥤ StructureSheafModules Rc) :=
  letI : Functor.Additive (Tensor.sheafTensor.{u, u, u, u, u} Rc :
      StructureSheafModules Rc ⥤ StructureSheafModules Rc ⥤ StructureSheafModules Rc) :=
    Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive Rc
  Functor.preservesZeroMorphisms_of_additive _

/-- `ℱ ⊗_{O_X} -` preserves the zero morphism; the second-variable companion of
`Stacks.SheafOfModules.sheafTensorPreservesZero`, named for the same reasons. -/
local instance sheafTensorObjPreservesZero (A : StructureSheafModules Rc) :
    Functor.PreservesZeroMorphisms ((Tensor.sheafTensor.{u, u, u, u, u} Rc :
      StructureSheafModules Rc ⥤ StructureSheafModules Rc ⥤ StructureSheafModules Rc).obj A) :=
  letI : Functor.Additive ((Tensor.sheafTensor.{u, u, u, u, u} Rc :
      StructureSheafModules Rc ⥤ StructureSheafModules Rc ⥤ StructureSheafModules Rc).obj A) :=
    Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive Rc A
  Functor.preservesZeroMorphisms_of_additive _

/-- `⊗_{O_X}` as a monoidal structure on `Mod(O_X)`, with its universes pinned.
`SheafOfModules.monoidalCategorySheafTensor`, registered above, is this very term; but it is
stated with the sections universe tied to the site universes as `max u v`, and instance search
will not solve `max ?u ?v =?= u` against this cluster's diagonal `u`, so the registration is
unreachable from a goal over `SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)`.  Supplying the
site makes it reachable.  Nothing is bridged: the type is the one
`SheafOfModules.monoidalCategorySheafTensor` is already stated at, and
`Stacks.SheafOfModules.monoidalSpace'` is the same structure at the `StructureSheafModules Rc`
spelling, which remains registered beside it.  This is the device
`StacksFrontier/Topology/Sheaves/Cohomology/InternalHom/DerivedAssociatorComparison.lean` uses, for
the same query and the same reason. -/
@[instance_reducible]
local instance monoidalCategoryModDCPN :
    MonoidalCategory (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) :=
  SheafOfModules.monoidalCategorySheafTensor (J := Opens.grothendieckTopology X) Rc

/-! ### Elementary squares in a category

The five lemmas of this section are pure category theory, and they are stated separately for a
reason of elaboration and not of taste: in the development below the ambient category is
`D(O_X)` for `O_X` a sheaf of rings on a space, whose objects are spelled through
`Stacks.SheafOfModules.StructureSheafModules`, and the type-correctness check that `rw` performs
does not see through that spelling, while `rw (transparency := .default)` unfolds the chosen
K-flat representatives and their identifications instead. Stated for an abstract category the
same rewriting is unproblematic, and every square below is then applied with `exact`, which is
up to definitional unfolding. -/

section Squares

variable {C : Type*} [Category C]

/-- **An isomorphism's inverse, from a commuting square of the isomorphisms' forward maps.** -/
theorem Square.inv_comp_of_comp_hom {A B A' B' : C} (e : A ≅ B) (e' : A' ≅ B')
    {d : A ⟶ A'} {q : B ⟶ B'} (h : d ≫ e'.hom = e.hom ≫ q) :
    e.inv ≫ d = q ≫ e'.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **A commuting square of two isomorphisms' inverses, from the square of their forward
maps.** -/
theorem Square.comp_inv_of_hom_comp {A B A' B' : C} (e : A ≅ B) (e' : A' ≅ B')
    {n : A ⟶ A'} {m : B ⟶ B'} (h : n ≫ e'.hom = e.hom ≫ m) :
    m ≫ e'.inv = e.inv ≫ n := by
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

/-- **An isomorphism's inverse computed from a factorisation of its forward map.** -/
theorem Square.iso_inv_eq {A B D : C} (e : A ≅ B) (e' : D ≅ B) {a : A ⟶ D} {b : D ⟶ A}
    (hhom : e.hom = a ≫ e'.hom) (hid : a ≫ b = 𝟙 A) : e.inv = e'.inv ≫ b := by
  refine (cancel_epi e.hom).1 ?_
  rw [Iso.hom_inv_id, hhom, Category.assoc, Iso.hom_inv_id_assoc, hid]

/-- **A functor carries a commuting square to a commuting square**, written so that the
composites on both sides are the images of the two factorisations. -/
theorem Square.map_comp_square {D' : Type*} [Category D'] (F : C ⥤ D') {A B B' A' : C}
    {n : A ⟶ B} {d' : B ⟶ A'} {d : A ⟶ B'} {t : B' ⟶ A'} (h : d ≫ t = n ≫ d') :
    F.map n ≫ F.map d' = F.map d ≫ F.map t := by
  rw [← F.map_comp, ← F.map_comp, h]

/-- **A functor carries a factorisation to a factorisation.** -/
theorem Square.map_eq_map_comp {D' : Type*} [Category D'] (F : C ⥤ D') {A B B' : C}
    {u : A ⟶ B'} {a : A ⟶ B} {b : B ⟶ B'} (h : a ≫ b = u) :
    F.map u = F.map a ≫ F.map b := by
  rw [← h, F.map_comp]

/-- **Four commuting squares compose.** -/
theorem Square.comp_four {X₀ X₁ Y₀ Y₁ Y₂ Y₃ Z₀ Z₁ Z₂ Z₃ : C}
    {E : X₀ ⟶ X₁} {a : X₀ ⟶ Y₀} {a' : X₁ ⟶ Z₀} {m : Y₀ ⟶ Z₀}
    {b : Y₀ ⟶ Y₁} {b' : Z₀ ⟶ Z₁} {M : Y₁ ⟶ Z₁}
    {c : Y₁ ⟶ Y₂} {c' : Z₁ ⟶ Z₂} {N : Y₂ ⟶ Z₂}
    {d : Y₂ ⟶ Y₃} {d' : Z₂ ⟶ Z₃} {T : Y₃ ⟶ Z₃}
    (h₁ : E ≫ a' = a ≫ m) (h₂ : m ≫ b' = b ≫ M) (h₃ : M ≫ c' = c ≫ N)
    (h₄ : N ≫ d' = d ≫ T) :
    E ≫ a' ≫ b' ≫ c' ≫ d' = (a ≫ b ≫ c ≫ d) ≫ T := by
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]

/-- **Three commuting squares compose.** -/
theorem Square.comp_three {X₀ X₁ Y₀ Y₁ Y₂ Z₀ Z₁ Z₂ : C}
    {E : X₀ ⟶ X₁} {a : X₀ ⟶ Y₀} {a' : X₁ ⟶ Z₀} {m : Y₀ ⟶ Z₀}
    {b : Y₀ ⟶ Y₁} {b' : Z₀ ⟶ Z₁} {M : Y₁ ⟶ Z₁}
    {c : Y₁ ⟶ Y₂} {c' : Z₁ ⟶ Z₂} {N : Y₂ ⟶ Z₂}
    (h₁ : E ≫ a' = a ≫ m) (h₂ : m ≫ b' = b ≫ M) (h₃ : M ≫ c' = c ≫ N) :
    E ≫ a' ≫ b' ≫ c' = (a ≫ b ≫ c) ≫ N := by
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]

/-- **Regrouping a composite of six morphisms**, in the one way the identification of the
cohomology product with the K-flat pairing needs. -/
theorem Square.assoc_six {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : C} (E : X₀ ⟶ X₁) (A : X₁ ⟶ X₂)
    (b : X₂ ⟶ X₃) (c : X₃ ⟶ X₄) (d : X₄ ⟶ X₅) (t : X₅ ⟶ X₆) :
    (E ≫ A) ≫ b ≫ c ≫ d ≫ t = E ≫ (A ≫ b ≫ c ≫ d) ≫ t := by
  simp only [Category.assoc]

/-- **Cancelling an isomorphism's inverse against its forward map inside a composite.** -/
theorem Square.assoc_comp_inv_comp_hom {A A' B D : C} (e : B ≅ D) (g : A' ⟶ D) (f : A ⟶ A') :
    (f ≫ g ≫ e.inv) ≫ e.hom = f ≫ g := by
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **Two commuting squares compose.** -/
theorem Square.comp_two {X₀ X₁ Y₀ Y₁ Z₀ Z₁ : C} {E : X₀ ⟶ X₁} {a : X₀ ⟶ Y₀} {a' : X₁ ⟶ Z₀}
    {m : Y₀ ⟶ Z₀} {b' : Z₀ ⟶ Z₁} {n : Y₀ ⟶ Y₁} {t : Y₁ ⟶ Z₁}
    (h₁ : E ≫ a' = a ≫ m) (h₂ : m ≫ b' = n ≫ t) :
    E ≫ a' ≫ b' = a ≫ n ≫ t := by
  rw [← Category.assoc, h₁, Category.assoc, h₂]

/-- **A composite conjugated by two isomorphisms, with the conjugation cancelled.** -/
theorem Square.conj_cancel {X Y A A' B W : C} (e : X ≅ Y) (e' : A' ≅ B)
    {c : Y ⟶ B} {r₁ : X ⟶ A} {r₂ : A ⟶ A'} {w : A' ⟶ W}
    (h : c = e.inv ≫ r₁ ≫ r₂ ≫ e'.hom) :
    e.hom ≫ c ≫ e'.inv ≫ w = r₁ ≫ r₂ ≫ w := by
  rw [h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- **A commuting square whose left edge is invertible descends to the square with that edge
removed.** -/
theorem Square.of_isIso_edge {X Y Z A B D : C} (u : X ⟶ Y) [IsIso u] {m : Y ⟶ Z} {p : Z ⟶ A}
    {b : X ⟶ B} {n : B ⟶ D} {t : D ⟶ A} {q : Y ⟶ D}
    (h₁ : (u ≫ m) ≫ p = b ≫ n ≫ t) (h₂ : u ≫ q = b ≫ n) :
    m ≫ p = q ≫ t := by
  refine (cancel_epi u).1 ?_
  rw [← Category.assoc, h₁, ← Category.assoc u q t, h₂, Category.assoc]

end Squares

section MonoidalSquares

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- **The tensor product of two commuting squares is a commuting square.** -/
theorem Square.tensor {X₁ X₂ Y₁ Y₂ Z₁ Z₂ W₁ W₂ : C}
    {a₁ : X₁ ⟶ Y₁} {a₂ : X₂ ⟶ Y₂} {b₁ : Y₁ ⟶ W₁} {b₂ : Y₂ ⟶ W₂}
    {c₁ : X₁ ⟶ Z₁} {c₂ : X₂ ⟶ Z₂} {d₁ : Z₁ ⟶ W₁} {d₂ : Z₂ ⟶ W₂}
    (h₁ : a₁ ≫ b₁ = c₁ ≫ d₁) (h₂ : a₂ ≫ b₂ = c₂ ≫ d₂) :
    (a₁ ⊗ₘ a₂) ≫ (b₁ ⊗ₘ b₂) = (c₁ ⊗ₘ c₂) ≫ (d₁ ⊗ₘ d₂) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
    h₁, h₂]

/-- **A square whose left edge is a tensor product of two factorisations.** The square for the
composites is rewritten as a square whose left edge is the composite of the two tensor products,
which is the shape `Stacks.SheafOfModules.Square.of_isIso_edge` consumes. -/
theorem Square.of_tensor_factor {X₁ X₂ Y₁ Y₂ Z₁ Z₂ A B D : C}
    {s₁ : X₁ ⟶ Y₁} {s₂ : X₂ ⟶ Y₂} {m₁ : Y₁ ⟶ Z₁} {m₂ : Y₂ ⟶ Z₂}
    {g₁ : X₁ ⟶ Z₁} {g₂ : X₂ ⟶ Z₂}
    {p : Z₁ ⊗ Z₂ ⟶ A} {b : X₁ ⊗ X₂ ⟶ B} {n : B ⟶ D} {t : D ⟶ A} {v : B ⟶ A}
    (hg₁ : g₁ = s₁ ≫ m₁) (hg₂ : g₂ = s₂ ≫ m₂) (hv : v = n ≫ t)
    (h : (g₁ ⊗ₘ g₂) ≫ p = b ≫ v) :
    ((s₁ ⊗ₘ s₂) ≫ (m₁ ⊗ₘ m₂)) ≫ p = b ≫ n ≫ t := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom, ← hg₁, ← hg₂, h, hv]

/-- **A tensor product of composites, regrouped as a composite of tensor products.** -/
theorem Square.tensorHom_comp_tensorIso_hom {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (e₁ : Y₁ ≅ Z₁) (e₂ : Y₂ ≅ Z₂) :
    (f₁ ≫ e₁.hom) ⊗ₘ (f₂ ≫ e₂.hom) = (f₁ ⊗ₘ f₂) ≫ (e₁ ⊗ᵢ e₂).hom := by
  rw [tensorIso_hom, MonoidalCategory.tensorHom_comp_tensorHom]

end MonoidalSquares

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### The pairing attached to two K-flat complexes -/

/-- **The cohomology product of the derived tensor product of two K-flat complexes, computed on
those complexes.** For K-flat `P` and `Q` the derived tensor product of their classes is the
class of their total tensor complex, so the product induced by tensoring cocycles,
`Stacks.SheafOfModules.tensorComplexHomology`, transports to a pairing

`Hⁱ(P) ⊗_{O_X} Hʲ(Q) ⟶ Hⁱ⁺ʲ(P ⊗^L_{O_X} Q)`

on the cohomology sheaves of the classes. No choice is involved: unlike
`Stacks.SheafOfModules.derivedCohomologyTensorProduct` this is attached to the two complexes
themselves and not to a chosen representative of an object of the derived category. -/
def kFlatTensorHomology (P Q : CochainComplex (StructureSheafModules Rc) ℤ)
    (hP : IsKFlat (ringedSite Rc).O P) (hQ : IsKFlat (ringedSite Rc).O Q) (i j : ℤ) :
    (DerivedCategory.homologyFunctor (StructureSheafModules Rc) i).obj
          (DerivedCategory.Q.obj P) ⊗
        (DerivedCategory.homologyFunctor (StructureSheafModules Rc) j).obj
          (DerivedCategory.Q.obj Q) ⟶
      (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (i + j)).obj
        (((derivedTensor Rc).obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj Q)) :=
  (((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) i).app P) ⊗ᵢ
      ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) j).app Q)).hom ≫
    tensorComplexHomology Rc P Q i j ≫
      ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) (i + j)).app
        (HomologicalComplex.tensorObj P Q)).inv ≫
      (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (i + j)).map
        ((canonicalDerivedTensorProduct (ringedSite Rc)).comparison P Q hP hQ).inv

/-! ### Naturality in a morphism of complexes -/

/-- **The K-flat comparison of the derived tensor product, read on inverses.** The naturality of
`Stacks.SheafOfModules.DerivedTensorProduct.comparison` solved so that the comparison inverse
carries the morphism of derived tensor products induced by two classes of morphisms of complexes
to the morphism of total tensor complexes they induce. -/
theorem comparison_inv_derivedTensorMap
    {P Q P' Q' : CochainComplex (StructureSheafModules Rc) ℤ}
    (hP : IsKFlat (ringedSite Rc).O P) (hQ : IsKFlat (ringedSite Rc).O Q)
    (hP' : IsKFlat (ringedSite Rc).O P') (hQ' : IsKFlat (ringedSite Rc).O Q')
    (f : P ⟶ P') (g : Q ⟶ Q') :
    ((canonicalDerivedTensorProduct (ringedSite Rc)).comparison P Q hP hQ).inv ≫
        derivedTensorMap Rc (DerivedCategory.Q.map f) (DerivedCategory.Q.map g) =
      DerivedCategory.Q.map (HomologicalComplex.tensorHom f g) ≫
        ((canonicalDerivedTensorProduct (ringedSite Rc)).comparison P' Q' hP' hQ').inv := by
  have h' : derivedTensorMap Rc (DerivedCategory.Q.map f) (DerivedCategory.Q.map g) ≫
      ((canonicalDerivedTensorProduct (ringedSite Rc)).comparison P' Q' hP' hQ').hom =
      ((canonicalDerivedTensorProduct (ringedSite Rc)).comparison P Q hP hQ).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.tensorHom f g) := by
    have h := (canonicalDerivedTensorProduct (ringedSite Rc)).comparison_naturality
      f g hP hP' hQ hQ'
    rw (transparency := .default) [← Category.assoc] at h
    exact h
  exact Square.inv_comp_of_comp_hom _ _ h'

/-- **The K-flat pairing is natural in morphisms of complexes.** For morphisms `f` and `g` of
K-flat complexes the square comparing `Stacks.SheafOfModules.kFlatTensorHomology` at the sources
with the one at the targets commutes.

Three inputs, each applicable with no quasi-isomorphism hypothesis: naturality of
`CategoryTheory.DerivedCategory.homologyFunctorFactors`, the chain-level naturality
`CochainComplex.tensorHomology_naturality`, and
`Stacks.SheafOfModules.comparison_inv_derivedTensorMap`.

The chain-level naturality is cited in its general form, for a complex over an arbitrary
preadditive monoidal category, rather than through its form over a ringed space
`Stacks.SheafOfModules.tensorComplexHomology_naturality`, which is that general lemma
specialized and nothing more. The morphism of total tensor complexes that the square shares
with the other two is written as `HomologicalComplex.tensorHom`, the spelling the general lemma
states it at, and the squares meet along it syntactically. That spelling names one category,
read off `f` and `g` themselves, so every instance the shared edge asks for is asked for at
`StructureSheafModules Rc`, the spelling the complexes are stated in; written instead as
`HomologicalComplex.mapBifunctorMap` at `Stacks.SheafOfModules.Tensor.sheafTensor`, the
bifunctor's own source and target categories enter as further arguments at the
`SheafOfModules (Tensor.ringSheaf Rc)` spelling and the target's
`CategoryTheory.Preadditive` instance is then asked for across the two spellings at once. For
the same reason `hffinv` is stated for an arbitrary morphism of complexes: the shared edge is
then fixed by `hnat` alone and never has to be unified across two spellings. -/
theorem kFlatTensorHomology_naturality
    {P Q P' Q' : CochainComplex (StructureSheafModules Rc) ℤ}
    (hP : IsKFlat (ringedSite Rc).O P) (hQ : IsKFlat (ringedSite Rc).O Q)
    (hP' : IsKFlat (ringedSite Rc).O P') (hQ' : IsKFlat (ringedSite Rc).O Q')
    (f : P ⟶ P') (g : Q ⟶ Q') (i j : ℤ) :
    ((DerivedCategory.homologyFunctor (StructureSheafModules Rc) i).map
            (DerivedCategory.Q.map f) ⊗ₘ
          (DerivedCategory.homologyFunctor (StructureSheafModules Rc) j).map
            (DerivedCategory.Q.map g)) ≫
        kFlatTensorHomology Rc P' Q' hP' hQ' i j =
      kFlatTensorHomology Rc P Q hP hQ i j ≫
        (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (i + j)).map
          (derivedTensorMap Rc (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) := by
  have hffinv : ∀ {A B : CochainComplex (StructureSheafModules Rc) ℤ} (φ : A ⟶ B),
      HomologicalComplex.homologyMap φ (i + j) ≫
          ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) (i + j)).app B).inv =
        ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) (i + j)).app A).inv ≫
          (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (i + j)).map
            (DerivedCategory.Q.map φ) := fun φ =>
    Square.comp_inv_of_hom_comp _ _
      ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) (i + j)).hom.naturality φ)
  have hnat := CochainComplex.tensorHomology_naturality P Q f g i j
  exact Square.comp_four (C := StructureSheafModules Rc)
    (Square.tensor ((DerivedCategory.homologyFunctorFactors _ i).hom.naturality f)
      ((DerivedCategory.homologyFunctorFactors _ j).hom.naturality g))
    hnat.symm (hffinv _)
    (Square.map_comp_square (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (i + j))
      (comparison_inv_derivedTensorMap Rc hP hQ hP' hQ' f g))

/-! ### Naturality in a morphism of the derived category -/

/-- **A morphism of the derived category between the classes of two complexes is a right fraction
through a K-flat complex.** Every morphism `Q(P) ⟶ Q(P')` is `inv (Q s₀) ≫ Q g₀`
(`CategoryTheory.DerivedCategory.right_fac`), and the apex of that roof may be taken K-flat by
replacing it with a K-flat resolution (Stacks 06YS).

No K-flatness of `P` or `P'` is used; what the statement provides is a K-flat apex, which is what
a construction defined only on K-flat complexes needs in order to be compared along the roof. -/
theorem exists_kFlat_roof (P P' : CochainComplex (StructureSheafModules Rc) ℤ)
    (γ : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj P') :
    ∃ (P₁ : CochainComplex (StructureSheafModules Rc) ℤ) (s : P₁ ⟶ P) (g : P₁ ⟶ P'),
      IsKFlat (ringedSite Rc).O P₁ ∧ IsIso (DerivedCategory.Q.map s) ∧
        DerivedCategory.Q.map s ≫ γ = DerivedCategory.Q.map g := by
  obtain ⟨P₀, s₀, hs₀, g₀, hfac₀⟩ := DerivedCategory.right_fac γ
  obtain ⟨P₁, p, hP₁, hp⟩ := Stacks.SheafOfModules.exists_kFlat_quasiIso (ringedSite Rc) P₀
  have := hs₀
  have : QuasiIso p := hp
  have := (DerivedCategory.isIso_Q_map_iff_quasiIso (StructureSheafModules Rc) p).2 hp
  refine ⟨P₁, p ≫ s₀, p ≫ g₀, hP₁, ?_, ?_⟩
  · rw (transparency := .default) [Functor.map_comp]; infer_instance
  · rw (transparency := .default) [hfac₀, Functor.map_comp, Functor.map_comp, Category.assoc,
      IsIso.hom_inv_id_assoc]

/-- **The K-flat pairing is natural in morphisms of the derived category.** For K-flat `P`, `Q`,
`P'`, `Q'` and arbitrary morphisms `γ : Q(P) ⟶ Q(P')` and `δ : Q(Q) ⟶ Q(Q')` of `D(O_X)` the
square comparing `Stacks.SheafOfModules.kFlatTensorHomology` at the two pairs commutes.

Each of `γ` and `δ` is written as a right fraction through a K-flat complex
(`Stacks.SheafOfModules.exists_kFlat_roof`); the square for a morphism of complexes
(`Stacks.SheafOfModules.kFlatTensorHomology_naturality`) holds at both legs of each roof, and the
square for `γ` and `δ` follows by cancelling the invertible legs. -/
theorem kFlatTensorHomology_naturality_derived
    {P Q P' Q' : CochainComplex (StructureSheafModules Rc) ℤ}
    (hP : IsKFlat (ringedSite Rc).O P) (hQ : IsKFlat (ringedSite Rc).O Q)
    (hP' : IsKFlat (ringedSite Rc).O P') (hQ' : IsKFlat (ringedSite Rc).O Q')
    (γ : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj P')
    (δ : DerivedCategory.Q.obj Q ⟶ DerivedCategory.Q.obj Q') (i j : ℤ) :
    ((DerivedCategory.homologyFunctor (StructureSheafModules Rc) i).map γ ⊗ₘ
          (DerivedCategory.homologyFunctor (StructureSheafModules Rc) j).map δ) ≫
        kFlatTensorHomology Rc P' Q' hP' hQ' i j =
      kFlatTensorHomology Rc P Q hP hQ i j ≫
        (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (i + j)).map
          (derivedTensorMap Rc γ δ) := by
  obtain ⟨P₁, s, g, hP₁, hs, hsg⟩ := exists_kFlat_roof Rc P P' γ
  obtain ⟨Q₁, t, h, hQ₁, ht, hth⟩ := exists_kFlat_roof Rc Q Q' δ
  have := hs
  have := ht
  have hsq := kFlatTensorHomology_naturality Rc hP₁ hQ₁ hP hQ s t i j
  have hgh := kFlatTensorHomology_naturality Rc hP₁ hQ₁ hP' hQ' g h i j
  have hB : (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (i + j)).map
        (derivedTensorMap Rc (DerivedCategory.Q.map g) (DerivedCategory.Q.map h)) =
      (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (i + j)).map
          (derivedTensorMap Rc (DerivedCategory.Q.map s) (DerivedCategory.Q.map t)) ≫
        (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (i + j)).map
          (derivedTensorMap Rc γ δ) := by
    refine Square.map_eq_map_comp
      (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (i + j)) ?_
    rw (transparency := .default) [RingedSite.derivedTensorMap_comp, hsg, hth]
  exact Square.of_isIso_edge
    ((DerivedCategory.homologyFunctor (StructureSheafModules Rc) i).map
        (DerivedCategory.Q.map s) ⊗ₘ
      (DerivedCategory.homologyFunctor (StructureSheafModules Rc) j).map
        (DerivedCategory.Q.map t))
    (Square.of_tensor_factor
      (Square.map_eq_map_comp (DerivedCategory.homologyFunctor (StructureSheafModules Rc) i) hsg)
      (Square.map_eq_map_comp (DerivedCategory.homologyFunctor (StructureSheafModules Rc) j) hth)
      hB hgh) hsq

/-! ### Naturality of the cohomology product of a derived tensor product -/

/-- **The comparison identifying a derived tensor product with the total tensor complex of the
chosen K-flat representatives, read on inverses.** It is the inverse of the K-flat comparison
followed by the morphism of derived tensor products induced by the two identifications.

The reassociation `hhom` names its three morphisms rather than leaving them to be inferred:
`Stacks.SheafOfModules.derivedTensorKFlatRepresentativeIso` is a composite of three isomorphisms
whose first two compose to `AlgebraicGeometry.RingedSite.derivedTensorMap`, and the two
spellings of that composite -- through `CategoryTheory.Functor.mapIso` as the isomorphism is
built, and through `AlgebraicGeometry.RingedSite.derivedTensorMap` as the statement reads it --
agree by unfolding alone. Written in the first spelling, both sides of the kernel's check reduce
to the same term by projection. -/
theorem derivedTensorKFlatRepresentativeIso_inv
    (K L : DerivedCategory (StructureSheafModules Rc)) :
    (derivedTensorKFlatRepresentativeIso Rc K L).inv =
      ((canonicalDerivedTensorProduct (ringedSite Rc)).comparison
          (kFlatRepresentative Rc K) (kFlatRepresentative Rc L)
          (isKFlat_kFlatRepresentative Rc K) (isKFlat_kFlatRepresentative Rc L)).inv ≫
        derivedTensorMap Rc (kFlatRepresentativeIso Rc K).hom
          (kFlatRepresentativeIso Rc L).hom := by
  have hhom : (derivedTensorKFlatRepresentativeIso Rc K L).hom =
      derivedTensorMap Rc (kFlatRepresentativeIso Rc K).inv
          (kFlatRepresentativeIso Rc L).inv ≫
        ((canonicalDerivedTensorProduct (ringedSite Rc)).comparison
          (kFlatRepresentative Rc K) (kFlatRepresentative Rc L)
          (isKFlat_kFlatRepresentative Rc K) (isKFlat_kFlatRepresentative Rc L)).hom :=
    (Category.assoc (((derivedTensor Rc).mapIso (kFlatRepresentativeIso Rc K).symm).app L).hom
      ((((derivedTensor Rc).obj
          (DerivedCategory.Q.obj (kFlatRepresentative Rc K))).mapIso
            (kFlatRepresentativeIso Rc L).symm).hom)
      (((canonicalDerivedTensorProduct (ringedSite Rc)).comparison
          (kFlatRepresentative Rc K) (kFlatRepresentative Rc L)
          (isKFlat_kFlatRepresentative Rc K) (isKFlat_kFlatRepresentative Rc L)).hom)).symm
  have hid : derivedTensorMap Rc (kFlatRepresentativeIso Rc K).inv
          (kFlatRepresentativeIso Rc L).inv ≫
        derivedTensorMap Rc (kFlatRepresentativeIso Rc K).hom
          (kFlatRepresentativeIso Rc L).hom =
      𝟙 (((derivedTensor Rc).obj K).obj L) := by
    rw (transparency := .default) [RingedSite.derivedTensorMap_comp, Iso.inv_hom_id,
      Iso.inv_hom_id, RingedSite.derivedTensorMap_id]
  exact Square.iso_inv_eq _ _ hhom hid

/-- **The cohomology product of a derived tensor product is the K-flat pairing of the chosen
representatives, conjugated by the two identifications.** Written this way the product carries no
choice beyond the two identifications `Stacks.SheafOfModules.kFlatRepresentativeIso`, and its
naturality becomes the naturality of `Stacks.SheafOfModules.kFlatTensorHomology`. -/
theorem derivedCohomologyTensorProduct_eq
    (K L : DerivedCategory (StructureSheafModules Rc)) (i j : ℤ) :
    derivedCohomologyTensorProduct Rc K L i j =
      ((DerivedCategory.homologyFunctor (StructureSheafModules Rc) i).map
            (kFlatRepresentativeIso Rc K).inv ⊗ₘ
          (DerivedCategory.homologyFunctor (StructureSheafModules Rc) j).map
            (kFlatRepresentativeIso Rc L).inv) ≫
        kFlatTensorHomology Rc (kFlatRepresentative Rc K) (kFlatRepresentative Rc L)
            (isKFlat_kFlatRepresentative Rc K) (isKFlat_kFlatRepresentative Rc L) i j ≫
          (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (i + j)).map
            (derivedTensorMap Rc (kFlatRepresentativeIso Rc K).hom
              (kFlatRepresentativeIso Rc L).hom) := by
  have hgen : ((homologyKFlatRepresentativeIso Rc K i) ⊗ᵢ
        (homologyKFlatRepresentativeIso Rc L j)).inv =
      ((DerivedCategory.homologyFunctor (StructureSheafModules Rc) i).map
            (kFlatRepresentativeIso Rc K).inv ⊗ₘ
          (DerivedCategory.homologyFunctor (StructureSheafModules Rc) j).map
            (kFlatRepresentativeIso Rc L).inv) ≫
        (((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) i).app
              (kFlatRepresentative Rc K)) ⊗ᵢ
          ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) j).app
            (kFlatRepresentative Rc L))).hom :=
    Square.tensorHom_comp_tensorIso_hom
      ((DerivedCategory.homologyFunctor (StructureSheafModules Rc) i).map
        (kFlatRepresentativeIso Rc K).inv)
      ((DerivedCategory.homologyFunctor (StructureSheafModules Rc) j).map
        (kFlatRepresentativeIso Rc L).inv)
      ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) i).app
        (kFlatRepresentative Rc K))
      ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) j).app
        (kFlatRepresentative Rc L))
  have htail : (homologyDerivedTensorKFlatIso Rc K L (i + j)).inv =
      ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) (i + j)).app
          (HomologicalComplex.tensorObj (kFlatRepresentative Rc K)
            (kFlatRepresentative Rc L))).inv ≫
        (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (i + j)).map
            ((canonicalDerivedTensorProduct (ringedSite Rc)).comparison
              (kFlatRepresentative Rc K) (kFlatRepresentative Rc L)
              (isKFlat_kFlatRepresentative Rc K) (isKFlat_kFlatRepresentative Rc L)).inv ≫
          (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (i + j)).map
            (derivedTensorMap Rc (kFlatRepresentativeIso Rc K).hom
              (kFlatRepresentativeIso Rc L).hom) :=
    congrArg
      (fun z => ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) (i + j)).app
          (HomologicalComplex.tensorObj (kFlatRepresentative Rc K)
            (kFlatRepresentative Rc L))).inv ≫ z)
      (Square.map_eq_map_comp (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (i + j))
        (derivedTensorKFlatRepresentativeIso_inv Rc K L).symm)
  rw (transparency := .default) [derivedCohomologyTensorProduct, hgen, htail]
  exact Square.assoc_six _ _ _ _ _ _

/-- **The cohomology product of a derived tensor product is natural in both variables.** For
morphisms `k : K ⟶ K'` and `l : L ⟶ L'` of `D(O_X)` the square

`(Hⁱ(k) ⊗ Hʲ(l)) ≫ product_{K', L'} = product_{K, L} ≫ Hⁱ⁺ʲ(k ⊗^L l)`

commutes. This is what the pairing `Stacks.SheafOfModules.derivedCohomologyTensorProduct`, formed
on a `Classical.choose` of a K-flat representative, was missing; the implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCohomologyProduct` record that no
coherence across choices of model is asserted by the construction, and this is that coherence. -/
theorem derivedCohomologyTensorProduct_naturality
    {K K' L L' : DerivedCategory (StructureSheafModules Rc)} (k : K ⟶ K') (l : L ⟶ L')
    (i j : ℤ) :
    ((DerivedCategory.homologyFunctor (StructureSheafModules Rc) i).map k ⊗ₘ
          (DerivedCategory.homologyFunctor (StructureSheafModules Rc) j).map l) ≫
        derivedCohomologyTensorProduct Rc K' L' i j =
      derivedCohomologyTensorProduct Rc K L i j ≫
        (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (i + j)).map
          (derivedTensorMap Rc k l) := by
  have hnat := kFlatTensorHomology_naturality_derived Rc
    (isKFlat_kFlatRepresentative Rc K) (isKFlat_kFlatRepresentative Rc L)
    (isKFlat_kFlatRepresentative Rc K') (isKFlat_kFlatRepresentative Rc L')
    ((kFlatRepresentativeIso Rc K).hom ≫ k ≫ (kFlatRepresentativeIso Rc K').inv)
    ((kFlatRepresentativeIso Rc L).hom ≫ l ≫ (kFlatRepresentativeIso Rc L').inv) i j
  have hgam : derivedTensorMap Rc (kFlatRepresentativeIso Rc K).hom
          (kFlatRepresentativeIso Rc L).hom ≫ derivedTensorMap Rc k l =
      derivedTensorMap Rc
          ((kFlatRepresentativeIso Rc K).hom ≫ k ≫ (kFlatRepresentativeIso Rc K').inv)
          ((kFlatRepresentativeIso Rc L).hom ≫ l ≫ (kFlatRepresentativeIso Rc L').inv) ≫
        derivedTensorMap Rc (kFlatRepresentativeIso Rc K').hom
          (kFlatRepresentativeIso Rc L').hom := by
    rw (transparency := .default) [RingedSite.derivedTensorMap_comp,
      RingedSite.derivedTensorMap_comp,
      Square.assoc_comp_inv_comp_hom (kFlatRepresentativeIso Rc K') k
        (kFlatRepresentativeIso Rc K).hom,
      Square.assoc_comp_inv_comp_hom (kFlatRepresentativeIso Rc L') l
        (kFlatRepresentativeIso Rc L).hom]
  rw (transparency := .default) [derivedCohomologyTensorProduct_eq Rc K L i j,
    derivedCohomologyTensorProduct_eq Rc K' L' i j]
  exact Square.comp_three (C := StructureSheafModules Rc)
    (Square.tensor
      (Square.map_comp_square (DerivedCategory.homologyFunctor (StructureSheafModules Rc) i)
        ((kFlatRepresentativeIso Rc K).inv_hom_id_assoc _))
      (Square.map_comp_square (DerivedCategory.homologyFunctor (StructureSheafModules Rc) j)
        ((kFlatRepresentativeIso Rc L).inv_hom_id_assoc _))) hnat
    (Square.map_comp_square
      (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (i + j)) hgam)

/-! ### The composition product on Ext sheaves -/

section ExtProduct

variable (K L M : CochainComplex (StructureSheafModules Rc) ℤ)
  [(RingedSite.sheafHomComplex (ringedSite Rc) L M).obj.IsKInjective]
  [(RingedSite.sheafHomComplex (ringedSite Rc) K L).obj.IsKInjective]

/-- **The composition product on Ext sheaves is the cycle-level composition pairing of internal
Hom complexes.** For complexes `K`, `L`, `M` of `O_X`-modules the composition product

`Ext^i_{O_X}(L, M) ⊗_{O_X} Ext^j_{O_X}(K, L) ⟶ Ext^{i + j}_{O_X}(K, M)`

of `Stacks.SheafOfModules.sheafExtProduct`, which is built in the derived category out of the
derived composition morphism of Stacks 0A8V, agrees — after the canonical comparison of Stacks
08JH from the internal Hom complex to the derived internal Hom — with
`Stacks.SheafOfModules.homologyComposition`, the pairing induced by tensoring cocycles followed
by the composition morphism of internal Hom complexes of Stacks 0A91.

This is the identification that the derived composition product on Ext sheaves was missing. The
composition *morphisms* were already matched, by
`Stacks.SheafOfModules.strictlyPerfectHomComparison_derivedSheafExtComposition`; what was not
matched is the other factor of `Stacks.SheafOfModules.sheafExtProduct`, the pairing
`Stacks.SheafOfModules.derivedCohomologyTensorProduct`, and moving that pairing along the
comparison is exactly `Stacks.SheafOfModules.derivedCohomologyTensorProduct_naturality`. With
the pairing moved, `Stacks.SheafOfModules.homologyComposition_eq_derived_of_isKInjective`
identifies what is left with the cycle-level pairing and no residue remains.

The hypotheses are K-injectivity of the two internal Hom complexes the pairing is formed on,
which by `Stacks.SheafOfModules.isKInjective_sheafHomComplex_of_isKFlat` holds whenever `M` is
K-injective and `L` is K-flat, and whenever `L` is K-injective and `K` is K-flat. No hypothesis
on the three complexes themselves is used: in particular the comparison of Stacks 08JH need not
be invertible for the statement to hold, strict perfectness entering only when one wants to read
it as an identification of the two products. -/
theorem homologyComposition_strictlyPerfectHomComparison (i j : ℤ) :
    ((((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) i).app
            (RingedSite.sheafHomComplex (ringedSite Rc) L M).obj) ⊗ᵢ
          ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) j).app
            (RingedSite.sheafHomComplex (ringedSite Rc) K L).obj)).hom) ≫
        homologyComposition Rc K L M i j ≫
          ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) (i + j)).app
            (RingedSite.sheafHomComplex (ringedSite Rc) K M).obj).inv ≫
          (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (i + j)).map
            (RingedSite.strictlyPerfectHomComparison (ringedSite Rc)
              (derivedInternalHom Rc) K M) =
      ((DerivedCategory.homologyFunctor (StructureSheafModules Rc) i).map
            (RingedSite.strictlyPerfectHomComparison (ringedSite Rc)
              (derivedInternalHom Rc) L M) ⊗ₘ
          (DerivedCategory.homologyFunctor (StructureSheafModules Rc) j).map
            (RingedSite.strictlyPerfectHomComparison (ringedSite Rc)
              (derivedInternalHom Rc) K L)) ≫
        sheafExtProduct Rc (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
          (DerivedCategory.Q.obj M) i j := by
  have hnat := derivedCohomologyTensorProduct_naturality Rc
    (RingedSite.strictlyPerfectHomComparison (ringedSite Rc) (derivedInternalHom Rc) L M)
    (RingedSite.strictlyPerfectHomComparison (ringedSite Rc) (derivedInternalHom Rc) K L) i j
  have hcomp := strictlyPerfectHomComparison_derivedSheafExtComposition Rc K L M (i + j)
  have hcyc := homologyComposition_eq_derived_of_isKInjective Rc K L M i j
  exact (Square.conj_cancel _ _ hcyc).trans (Square.comp_two hnat hcomp).symm

end ExtProduct

end Stacks.SheafOfModules

end
