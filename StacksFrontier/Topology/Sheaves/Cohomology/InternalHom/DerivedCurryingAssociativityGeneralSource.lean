module

public import
  StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCompositionTransposeReduction

/-! # The associativity coherence of Stacks 08DI at an arbitrary source has a single instance

Let `(X, O_X)` be a ringed space and let `A`, `B`, `M` be objects of `D(O_X)`.  Write `Φ` for the
bijection of **Stacks 08DI** (`Stacks.SheafOfModules.derivedSheafHomTensorEquiv`), `ε` for the
application morphism of **Stacks 08J8** (`Stacks.SheafOfModules.derivedSheafHomCounit`) and
`E = RSheafHom(A, RSheafHom(B, M))`.  The *associativity coherence* of Stacks 08DI against a
morphism `cur : E ⟶ RSheafHom(A ⊗^L_{O_X} B, M)` is the family of identities

`α_{P,A,B}.hom ≫ Φ_{P, A ⊗^L B, M}(y ≫ cur) = Φ_{P ⊗^L A, B, M}(Φ_{P, A, RSheafHom(B,M)}(y))`

indexed by an object `P` of `D(O_X)` and a morphism `y : P ⟶ E`.
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCurryingAssociativityAtTheUnit`
proves it at `P = O_X`, unconditionally, and records that the general source is what the
equation `htr` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCompositionDoubleContraction` still
owes.

**This file shows that the whole family has a single instance.**  The identity at an arbitrary
`(P, y)` is the identity at `(E, 𝟙)` precomposed with `(y ▷ A) ▷ B`, so the two are equivalent:
the family is *not* a family, and the coherence that the derived-duality cluster of Example 0FPC
needs is the one equation

`α_{E,A,B}.hom ≫ cur ▷ (A ⊗^L B) ≫ ε_{A ⊗^L B, M} = ε_{A, RSheafHom(B,M)} ▷ B ≫ ε_{B,M}`,

`derivedCurryCounitSourceCoherence` below.

## Main results

* `Stacks.SheafOfModules.derivedCurryCounitSourceCoherence`: the single equation, as a
  proposition.
* `Stacks.SheafOfModules.derivedSheafHomTensorEquiv_assoc_of_counitSource`: **the coherence at an
  arbitrary source, from that one equation.**
* `Stacks.SheafOfModules.derivedCurryCounitSourceCoherence_of_assoc`: the converse — the one
  equation is the coherence at `P = E`, `y = 𝟙`.  So nothing is lost by reducing to it.
* `SheafOfModules.derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_of_coherence`:
  **(C) from the derived passage and that one equation**, by
  `SheafOfModules.derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_of_laws`.
  The coherence instance it consumes is the one above at `A := RSheafHom(K, L)` and `B := K`.

## Nothing here is tagged

Stacks 08DI is carried by `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` and Stacks 08J9 by
`Stacks.SheafOfModules.derivedCurryingData`; a coherence between the two is a compatibility that
neither published statement asserts, which is the reason
`…InternalHom.DerivedCurryingAssociativityAtTheUnit` and
`…InternalHom.DerivedCompositionDoubleContraction` give for carrying no attribute either.

## Implementation notes

*The reduction is three moves in an arbitrary monoidal category* —
`CategoryTheory.MonoidalCategory.associator_naturality_left`, `comp_whiskerRight` and
`Category.assoc` — and they are packaged as `assoc_whiskerRight_paste`, stated over an abstract
monoidal category with every object and morphism a variable.  That is the discipline the sibling
files of this cluster use whenever a goal mentions the derived tensor product at two
definitionally equal spellings: the crossing is then paid once, by the `exact` that applies the
abstract lemma, instead of at every rewrite.

*The instances are carried as binders*, as in `…InternalHom.DerivedCompositionDoubleContraction`
and for the reason recorded there: the sibling `…InternalHom.DerivedApplicationCompositionLaw`
pins them to file-local constants, and a single declaration crossing that boundary exceeds the
recursion limit.

*The middle object is written at the bifunctor spelling* `((derivedTensor Rc).obj A).obj B`, never
`A ⊗ B`, except inside the type of an associator, for the reason
`…InternalHom.DerivedCompositionDoubleContraction` records: a goal carrying both spellings is
rejected by `rw [Category.assoc]`.

## References

* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 0A8V](https://stacks.math.columbia.edu/tag/0A8V)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

/-- **The reduction, over an arbitrary monoidal category.**  If the associativity-shaped identity
`α_{E,A,B}.hom ≫ t = eA ▷ B ≫ eB` holds, then its precomposition with `y ▷ (A ⊗ B)` holds with
`α` reassociated to the new source and `eA` precomposed with `y ▷ A`.

Stated with every object and morphism a variable, and applied by `exact` below: the
derived-level goal it is applied to mentions the derived tensor product at two definitionally
equal spellings, across which no rewriting tactic fires, and one `exact` pays that crossing
once.  The three moves are `CategoryTheory.MonoidalCategory.associator_naturality_left`,
`comp_whiskerRight` and `Category.assoc`; no braiding and no coherence diagram is used. -/
private lemma assoc_whiskerRight_paste {C : Type*} [Category C] [MonoidalCategory C]
    {P E A B M W : C} (y : P ⟶ E) (t : E ⊗ (A ⊗ B) ⟶ M) (eA : E ⊗ A ⟶ W) (eB : W ⊗ B ⟶ M)
    (h : (α_ E A B).hom ≫ t = eA ▷ B ≫ eB) :
    (α_ P A B).hom ≫ y ▷ (A ⊗ B) ≫ t = (y ▷ A ≫ eA) ▷ B ≫ eB := by
  rw [← Category.assoc, ← associator_naturality_left, Category.assoc, h, comp_whiskerRight,
    Category.assoc]

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

section Monoidal

attribute [local instance] derivedMonoidalStructure

/-- **The one instance of the associativity coherence of Stacks 08DI**, as a proposition: for
objects `A`, `B`, `M` of `D(O_X)` and a morphism
`cur : RSheafHom(A, RSheafHom(B, M)) ⟶ RSheafHom(A ⊗^L_{O_X} B, M)`,

`α_{E,A,B}.hom ≫ cur ▷ (A ⊗^L B) ≫ ε_{A ⊗^L B, M} = ε_{A, RSheafHom(B,M)} ▷ B ≫ ε_{B,M}`,

`E = RSheafHom(A, RSheafHom(B, M))` being the source of `cur`.  This is the `hA9` hypothesis of
`Stacks.SheafOfModules.derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_of_laws`
read at `A := RSheafHom(K, L)` and `B := K`, and — by the two theorems below — it is equivalent
to the whole family of coherence identities indexed by a source object and a morphism into `E`.

It is a `def` of type `Prop` so that the two theorems below, and a consumer, can name it without
re-elaborating the equation; that is the device
`Stacks.SheafOfModules.DerivedMonoidal.CanonicalComparisonAssociator` uses, for the same
reason. -/
def derivedCurryCounitSourceCoherence (A B M : DerivedCategory (StructureSheafModules Rc))
    (cur : ((derivedSheafHom Rc).obj (op A)).obj (((derivedSheafHom Rc).obj (op B)).obj M) ⟶
      ((derivedSheafHom Rc).obj (op (((derivedTensor Rc).obj A).obj B))).obj M) : Prop :=
  (α_ (((derivedSheafHom Rc).obj (op A)).obj (((derivedSheafHom Rc).obj (op B)).obj M)) A B).hom ≫
      cur ▷ ((derivedTensor Rc).obj A).obj B ≫
        derivedSheafHomCounit Rc (((derivedTensor Rc).obj A).obj B) M =
    derivedSheafHomCounit Rc A (((derivedSheafHom Rc).obj (op B)).obj M) ▷ B ≫
      derivedSheafHomCounit Rc B M

/-- **The associativity coherence of Stacks 08DI at an arbitrary source, from its single
instance.**  For every object `P` of `D(O_X)` and every morphism
`y : P ⟶ RSheafHom(A, RSheafHom(B, M))`,

`α_{P,A,B}.hom ≫ Φ_{P, A ⊗^L B, M}(y ≫ cur) = Φ_{P ⊗^L A, B, M}(Φ_{P, A, RSheafHom(B,M)}(y))`,

as soon as `Stacks.SheafOfModules.derivedCurryCounitSourceCoherence` holds.

Both sides are turned into whiskerings of application morphisms by
`Stacks.SheafOfModules.derivedSheafHomCounit_whiskerRight_eq'` and the source naturality
`Stacks.SheafOfModules.derivedSheafHomTensorEquiv_comp_left`, after which the identity is
`assoc_whiskerRight_paste`.  So the coherence at an arbitrary source is *not* stronger than the
coherence at the source of `cur`: the module docstring of
`…InternalHom.DerivedCurryingAssociativityAtTheUnit`, which calls the general source "strictly
more" than the unit source, is right about the *unit* source and this is the precise statement of
how much more it is — exactly the one equation above. -/
theorem derivedSheafHomTensorEquiv_assoc_of_counitSource
    (A B M : DerivedCategory (StructureSheafModules Rc))
    (cur : ((derivedSheafHom Rc).obj (op A)).obj (((derivedSheafHom Rc).obj (op B)).obj M) ⟶
      ((derivedSheafHom Rc).obj (op (((derivedTensor Rc).obj A).obj B))).obj M)
    (h : derivedCurryCounitSourceCoherence Rc A B M cur)
    (P : DerivedCategory (StructureSheafModules Rc))
    (y : P ⟶ ((derivedSheafHom Rc).obj (op A)).obj
      (((derivedSheafHom Rc).obj (op B)).obj M)) :
    (α_ P A B).hom ≫
        derivedSheafHomTensorEquiv Rc P (((derivedTensor Rc).obj A).obj B) M (y ≫ cur) =
      derivedSheafHomTensorEquiv Rc (((derivedTensor Rc).obj P).obj A) B M
        (derivedSheafHomTensorEquiv Rc P A (((derivedSheafHom Rc).obj (op B)).obj M) y) := by
  rw [derivedSheafHomTensorEquiv_comp_left Rc (((derivedTensor Rc).obj A).obj B) M y cur,
    ← derivedSheafHomCounit_whiskerRight_eq' Rc _ B M
      (derivedSheafHomTensorEquiv Rc P A (((derivedSheafHom Rc).obj (op B)).obj M) y),
    ← derivedSheafHomCounit_whiskerRight_eq' Rc P A
      (((derivedSheafHom Rc).obj (op B)).obj M) y,
    ← derivedSheafHomCounit_whiskerRight_eq' Rc _ (((derivedTensor Rc).obj A).obj B) M cur]
  exact assoc_whiskerRight_paste y _
    (derivedSheafHomCounit Rc A (((derivedSheafHom Rc).obj (op B)).obj M))
    (derivedSheafHomCounit Rc B M) h

/-- **The converse: the single instance is the coherence at `P = E` and `y = 𝟙`.**  So the
reduction performed by `derivedSheafHomTensorEquiv_assoc_of_counitSource` loses nothing, and the
residual of the cluster is exactly one equation. -/
theorem derivedCurryCounitSourceCoherence_of_assoc
    (A B M : DerivedCategory (StructureSheafModules Rc))
    (cur : ((derivedSheafHom Rc).obj (op A)).obj (((derivedSheafHom Rc).obj (op B)).obj M) ⟶
      ((derivedSheafHom Rc).obj (op (((derivedTensor Rc).obj A).obj B))).obj M)
    (h : ∀ (P : DerivedCategory (StructureSheafModules Rc))
      (y : P ⟶ ((derivedSheafHom Rc).obj (op A)).obj
        (((derivedSheafHom Rc).obj (op B)).obj M)),
      (α_ P A B).hom ≫
          derivedSheafHomTensorEquiv Rc P (((derivedTensor Rc).obj A).obj B) M (y ≫ cur) =
        derivedSheafHomTensorEquiv Rc (((derivedTensor Rc).obj P).obj A) B M
          (derivedSheafHomTensorEquiv Rc P A (((derivedSheafHom Rc).obj (op B)).obj M) y)) :
    derivedCurryCounitSourceCoherence Rc A B M cur := by
  have hE := h (((derivedSheafHom Rc).obj (op A)).obj (((derivedSheafHom Rc).obj (op B)).obj M))
    (𝟙 _)
  rw [Category.id_comp, ← derivedSheafHomCounit_whiskerRight_eq' Rc _ B M
      (derivedSheafHomTensorEquiv Rc _ A (((derivedSheafHom Rc).obj (op B)).obj M) (𝟙 _)),
    ← derivedSheafHomCounit_whiskerRight_eq' Rc _ (((derivedTensor Rc).obj A).obj B) M cur] at hE
  rw [derivedCurryCounitSourceCoherence, hE,
    derivedSheafHomCounit_eq Rc A (((derivedSheafHom Rc).obj (op B)).obj M)]

/-- **(C), the compatibility of Stacks 0A8V with Stacks 08J8, from the derived passage and the
single coherence instance.**

`hcmp` is the derived passage — that the composition morphism of Stacks 0A8V is the
`Φ`-transpose of `RSheafHom(ε_{K,L}, M)` run through `cur⁻¹`, which is the derived form of the
chain-level `AlgebraicGeometry.RingedSite.curryHomEquiv_doubleContraction`; `hcoh` is
`Stacks.SheafOfModules.derivedCurryCounitSourceCoherence` at `A := RSheafHom(K, L)`, `B := K`.
The conclusion is (C).

This is
`SheafOfModules.derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_of_curryIso`
with its `hA9` hypothesis read off `hcoh`: the two are the same equation, `hA9` writing the
right-hand side of `hcoh` through `Φ` at the identity and `hcoh` writing it as a whiskered
application morphism. -/
theorem derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_of_coherence
    (K L M : DerivedCategory (StructureSheafModules Rc))
    (cur : ((derivedSheafHom Rc).obj (op (((derivedSheafHom Rc).obj (op K)).obj L))).obj
          (((derivedSheafHom Rc).obj (op K)).obj M) ≅
        ((derivedSheafHom Rc).obj
          (op (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op K)).obj L)).obj K))).obj M)
    (hcmp : derivedSheafHomTensorEquiv Rc (((derivedSheafHom Rc).obj (op L)).obj M)
          (((derivedSheafHom Rc).obj (op K)).obj L)
          (((derivedSheafHom Rc).obj (op K)).obj M)
          (((derivedSheafHom Rc).map (derivedSheafHomCounit Rc K L).op).app M ≫ cur.inv) =
        derivedSheafHomComposition Rc K L M)
    (hcoh : derivedCurryCounitSourceCoherence Rc (((derivedSheafHom Rc).obj (op K)).obj L) K M
      cur.hom) :
    derivedSheafHomComposition Rc K L M ▷ K ≫ derivedSheafHomCounit Rc K M =
      (α_ (((derivedSheafHom Rc).obj (op L)).obj M)
          (((derivedSheafHom Rc).obj (op K)).obj L) K).hom ≫
        (((derivedSheafHom Rc).obj (op L)).obj M ◁ derivedSheafHomCounit Rc K L) ≫
          derivedSheafHomCounit Rc L M := by
  refine derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_of_curryIso Rc K L M
    cur hcmp ?_
  rw [← derivedSheafHomCounit_whiskerRight_eq' Rc _
    (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op K)).obj L)).obj K) M cur.hom]
  exact hcoh.symm

end Monoidal

end Stacks.SheafOfModules

end
