module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCompositionDoubleContraction

/-! # The associativity coherence of Stacks 08DI at source the structure sheaf

Let `(X, O_X)` be a ringed space and let `A`, `B`, `M` be objects of `D(O_X)`.  Write `Φ` for the
tensor–internal-Hom bijection of **Stacks 08DI**
(`Stacks.SheafOfModules.derivedSheafHomTensorEquiv`) and `cur` for the currying isomorphism of
**Stacks 08J9** (`Stacks.SheafOfModules.derivedCurryIso`).  The *associativity coherence* of the
pair is the family of identities

`α_{P,A,B}.hom ≫ Φ_{P, A ⊗^L B, M}(y ≫ cur_{A,B,M}) = Φ_{P ⊗^L A, B, M}(Φ_{P,A,RSheafHom(B,M)}(y))`

indexed by an object `P` of `D(O_X)` and a morphism `y : P ⟶ RSheafHom(A, RSheafHom(B, M))`.
The module docstring of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationCompositionReduction`
records, as its fourth search result, that **no instance of it is in the library**: "nothing
relates `derivedCurryHomEquiv X (A ⊗ B) C Z` to `derivedCurryHomEquiv X A (B ⊗ C) Z` through the
associator and the currying isomorphism of Stacks 08J9, and there is no chain-level analogue for
`AlgebraicGeometry.RingedSite.curryHomEquiv`."

**This file proves the coherence at `P = O_X`**, unconditionally, for arbitrary `A`, `B`, `M`.

## Why the unit source is free and the general source is not

`Φ_{P,A,M}` is by construction (`Stacks.SheafOfModules.derivedSheafHomTensorEquiv_globalSections`,
the last assertion of Stacks 08J9) the degree-zero global hypercohomology of `cur_{P,A,M}`, read
through the identification of Stacks 08DK at the two ends.  So the only available handle on
`cur_{A,B,M}` is its action on degree-zero global hypercohomology classes, i.e. on morphisms
`O_X ⟶ RSheafHom(A, RSheafHom(B, M))`, and the coherence at an arbitrary source `P` is strictly
more than that: it is the pentagon of Stacks 08J9, which compares `cur` at three different
triples.

At `P = O_X` the extra input needed is exactly the unit law **(UL)** of
`…InternalHom.DerivedApplicationUnitLaw`, `Stacks.SheafOfModules.derivedSheafHomCounit_unit_law`,
which says that `Φ` at source the structure sheaf *is* the identification of Stacks 08DK,
prefixed by the left unit constraint.  Feeding that to the global-sections description of `Φ`
turns both sides of the coherence into one and the same global hypercohomology class, prefixed on
one side by `α_{O_X,A,B}.hom ≫ λ_{A ⊗ B}.hom` and on the other by `λ_A.hom ▷ B`; and those two
agree in every monoidal category (`assoc_leftUnitor_whiskerRight` below).  No chain-level input,
no model comparison and no K-flatness enters.

## Main results

* `Stacks.SheafOfModules.derivedSheafHomTensorEquiv_unitSource`: **`Φ` at source the structure
  sheaf is the identification of Stacks 08DK prefixed by the left unit constraint.**  This is
  (UL) with the whiskering recognised as a value of `Φ`.
* `Stacks.SheafOfModules.derivedSheafHomTensorEquiv_unitSource_assoc`: **the associativity
  coherence of Stacks 08DI at source the structure sheaf.**
* `Stacks.SheafOfModules.derivedCounitCurry_comp_unitSource`: the transpose of the double
  contraction of `…InternalHom.DerivedCompositionDoubleContraction` and the currying isomorphism
  of Stacks 08J9 **agree after precomposition with every morphism out of the structure sheaf**.
  Equivalently: `Stacks.SheafOfModules.derivedCounitCurry` and
  `Stacks.SheafOfModules.derivedCurryIso` have the same image under degree-zero global
  hypercohomology.

## What this does and does not settle

`…InternalHom.DerivedCompositionDoubleContraction` leaves open whether its
`derivedCounitCurry` *is* the currying comparison of Stacks 08J9, and records that the question
is not decided there.  It is decided here on global sections, and only there: the last result
below says the two morphisms `RSheafHom(G, RSheafHom(K, M)) ⟶ RSheafHom(G ⊗^L K, M)` agree on
`Hom_{D(O_X)}(O_X, -)`, which is not enough to conclude that they are equal, `O_X` not being a
generator of `D(O_X)`.  What is still owed for the equation `htr` of that module is the coherence
at the general source, i.e. the pentagon of Stacks 08J9.

## Nothing here is tagged

Stacks 08DI is carried by `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` and Stacks 08J9 by
`Stacks.SheafOfModules.derivedCurryingData`; a coherence between the two is a compatibility that
neither published statement asserts, which is the reason
`…InternalHom.DerivedApplicationUnitLaw` and `…InternalHom.DerivedCompositionDoubleContraction`
give for carrying no attribute either.  So no declaration below carries a `@[stacks]` attribute.

## Implementation notes

*The instances are carried as binders*, as in `…InternalHom.DerivedCompositionDoubleContraction`
and for the reason recorded there.

*The category is named wherever `O_X` would otherwise name it.*
`AlgebraicGeometry.RingedSite.derivedStructureSheaf (ringedSite Rc)` is typed at
`DerivedCategory (SheafOfModules (Tensor.ringSheaf (ringedSite Rc).O))` and this file works in
`DerivedCategory (StructureSheafModules Rc)`; the two are the same category, but a notation that
reads its category off that object — `⟶` in the two `u` binders, `α_` at the three places whose
left argument is `O_X` — reads it at the first spelling, and the monoidal structure of
Stacks 0FPT is registered at the second.  Instance synthesis does not cross the gap: the
`DerivedCategory` applications carry their `Category`, `Abelian` and `HasDerivedCategory`
arguments, synthesized separately at each spelling, so no transparency setting closes it, and a
type ascription on the object does not help either, since it leaves the object's own type
unchanged and that is what the notation reads.  Those occurrences are therefore written as
`@Quiver.Hom` and `@MonoidalCategoryStruct.associator` with the category supplied, which is the
same term `⟶` and `α_` abbreviate and leaves every statement as it was.  It has to be the
re-seated structure and not the ringed site's own: the two are isomorphic and not equal, so
seating the site's would change what `α_` means.

*The middle object is written at the bifunctor spelling* `((derivedTensor Rc).obj A).obj B`
throughout, never `A ⊗ B`, for the reason that module records: a goal carrying both spellings is
rejected by `rw [Category.assoc]`.  The one place where `⊗` is unavoidable is the type of the
associator, and the crossing is paid once, in the monoidal coherence lemma, which is stated over
an arbitrary monoidal category where it is free.

## References

* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry
  Stacks.Cohomology.ModuleSections

universe u

namespace Stacks.SheafOfModules

/-- **The unit coherence of a monoidal category, in the shape the associativity coherence of
Stacks 08DI reduces to:** reassociating `(𝟙_ ⊗ A) ⊗ B` and then collapsing the unit is
collapsing the unit in the left factor.  Stated over an arbitrary monoidal category, where it is
one of the standard coherence identities; this is the only place in the file where the `⊗`
spelling of the derived tensor product occurs. -/
private lemma assoc_leftUnitor_whiskerRight {C : Type*} [Category C] [MonoidalCategory C]
    (A B : C) :
    (α_ (𝟙_ C) A B).hom ≫ (λ_ (A ⊗ B)).hom = (λ_ A).hom ▷ B := by
  simp

/-- **The associator is natural in its left variable**, in the form in which it occurs below:
with a trailing morphism absorbed, so that a consumer can rewrite with it without first
reassociating.  Stated over an arbitrary monoidal category, which is where the crossing between
the `⊗` spelling of the whiskered object and the bifunctor spelling of the derived tensor
product is free. -/
private lemma whiskerRight_associator_inv_assoc {C : Type*} [Category C] [MonoidalCategory C]
    {P E : C} (f : P ⟶ E) (Y Z : C) {T : C} (t : (E ⊗ Y) ⊗ Z ⟶ T) :
    f ▷ (Y ⊗ Z) ≫ (α_ E Y Z).inv ≫ t = (α_ P Y Z).inv ≫ ((f ▷ Y) ▷ Z) ≫ t := by
  simp

/-- **Two right whiskerings in a row paste**, with a trailing morphism absorbed; the companion of
`whiskerRight_associator_inv_assoc`, stated over an arbitrary monoidal category for the same
reason. -/
private lemma whiskerRight_comp_whiskerRight_assoc {C : Type*} [Category C] [MonoidalCategory C]
    {P E E' : C} (f : P ⟶ E) (g : E ⟶ E') (Z : C) {T : C} (t : E' ⊗ Z ⟶ T) :
    (f ▷ Z) ≫ (g ▷ Z) ≫ t = ((f ≫ g) ▷ Z) ≫ t := by
  rw [← Category.assoc, ← comp_whiskerRight]

attribute [local instance 10000] HasDerivedCategory.standard

-- The ring sheaf of `StructureSheafModules Rc` is `structureSheaf Rc`, i.e.
-- `CategoryTheory.sheafCompose` applied to `Rc`, while
-- `AlgebraicGeometry.RingedSite.derivedStructureSheaf (ringedSite Rc)` -- the source every
-- statement below is read at -- is typed at `Stacks.SheafOfModules.Tensor.ringSheaf Rc`, which
-- writes that composite presheaf out.  The two are the same sheaf of rings and elaboration
-- unfolds the gap, but `rw` matches at the `instances` transparency, where neither plain `def`
-- unfolds; both are therefore made `implicit_reducible` for this file, as the files upstream of
-- it already do for `sheafCompose`.  This is not enough for instance *synthesis* across the two
-- spellings -- see the implementation note above on where the category has to be named.
attribute [local implicit_reducible] CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

section Monoidal

attribute [local instance] derivedMonoidalStructure

/-- **The bijection of Stacks 08DI at source the structure sheaf is the identification of
Stacks 08DK, prefixed by the left unit constraint.**  For a degree-zero global hypercohomology
class `x` of `RSheafHom(A, M)`,

`Φ_{O_X, A, M}(Stacks 08JA of x) = (λ_ A).hom ≫ (Stacks 08DK of x)`,

the left unit constraint being written at the pinned spelling
`Stacks.SheafOfModules.derivedLeftUnitorHom` of `…InternalHom.DerivedApplicationUnitLaw`.

This is the unit law (UL) of that file in its elementwise form,
`Stacks.SheafOfModules.derivedSheafHomCounit_unit_law_apply`, with the left-hand whiskering
recognised as a value of `Φ` by
`Stacks.SheafOfModules.derivedTensor_map_app_comp_derivedSheafHomCounit`.  The two are chained
with `Eq.trans` and applied at their arguments rather than rewritten with: the ring sheaf of
`StructureSheafModules Rc` and the canonical ring sheaf of `ringedSite Rc` are two definitionally
equal spellings of one sheaf of rings, and a `rw` can only match the one it is handed. -/
theorem derivedSheafHomTensorEquiv_unitSource
    (A M : DerivedCategory (StructureSheafModules Rc))
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite Rc)).obj
        (((derivedSheafHom Rc).obj (op A)).obj M)) : Type u)) :
    derivedSheafHomTensorEquiv Rc (RingedSite.derivedStructureSheaf (ringedSite Rc)) A M
        (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
          (((derivedSheafHom Rc).obj (op A)).obj M) x) =
      derivedLeftUnitorHom Rc A ≫ derivedSheafHomGlobalSectionsEquiv Rc A M x :=
  (Stacks.SheafOfModules.derivedTensor_map_app_comp_derivedSheafHomCounit Rc
        (RingedSite.derivedStructureSheaf (ringedSite Rc)) A M
        (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
          (((derivedSheafHom Rc).obj (op A)).obj M) x)).symm.trans
    (derivedSheafHomCounit_unit_law_apply Rc A M x)

/-- **The associativity coherence of Stacks 08DI at source the structure sheaf.**  For objects
`A`, `B`, `M` of `D(O_X)` and a morphism `u : O_X ⟶ RSheafHom(A, RSheafHom(B, M))`,

`α_{O_X,A,B}.hom ≫ Φ_{O_X, A ⊗^L B, M}(u ≫ cur_{A,B,M}) =
  Φ_{O_X ⊗^L A, B, M}(Φ_{O_X, A, RSheafHom(B,M)}(u))`,

`cur` being the currying isomorphism of Stacks 08J9 and `Φ` the bijection of Stacks 08DI.  The
source is written `AlgebraicGeometry.RingedSite.derivedStructureSheaf (ringedSite Rc)` and not
`𝟙_`; the two are equal by `rfl`, but the library's clauses of Stacks 08DI are stated at the former
and a `rw` with one of them against a goal carrying the latter is rejected.

The proof is the one the module docstring describes: `u` is the morphism Stacks 08JA attaches to
a degree-zero global hypercohomology class `x` of `RSheafHom(A, RSheafHom(B, M))`; postcomposing
`u` with `cur` pushes `x` along degree-zero global hypercohomology of `cur`
(`AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsEquiv_naturality`), which by
the last assertion of Stacks 08J9
(`Stacks.SheafOfModules.derivedSheafHomTensorEquiv_globalSections`) is what `Φ_{A,B,M}` does to
the Stacks 08DK class of `x`; `derivedSheafHomTensorEquiv_unitSource` then reduces both sides to
that one class, and the two prefixes agree by `assoc_leftUnitor_whiskerRight`. -/
theorem derivedSheafHomTensorEquiv_unitSource_assoc
    (A B M : DerivedCategory (StructureSheafModules Rc))
    (u : @Quiver.Hom (DerivedCategory (StructureSheafModules Rc)) _
      (RingedSite.derivedStructureSheaf (ringedSite Rc))
      (((derivedSheafHom Rc).obj (op A)).obj (((derivedSheafHom Rc).obj (op B)).obj M))) :
    (@MonoidalCategoryStruct.associator (DerivedCategory (StructureSheafModules Rc)) _ _
        (RingedSite.derivedStructureSheaf (ringedSite Rc)) A B).hom ≫
        derivedSheafHomTensorEquiv Rc (RingedSite.derivedStructureSheaf (ringedSite Rc))
          (((derivedTensor Rc).obj A).obj B) M (u ≫ (derivedCurryIso Rc A B M).hom) =
      derivedSheafHomTensorEquiv Rc
          (((derivedTensor Rc).obj
            (RingedSite.derivedStructureSheaf (ringedSite Rc))).obj A) B M
        (derivedSheafHomTensorEquiv Rc (RingedSite.derivedStructureSheaf (ringedSite Rc)) A
          (((derivedSheafHom Rc).obj (op B)).obj M) u) := by
  obtain ⟨x, rfl⟩ : ∃ x, RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
      (((derivedSheafHom Rc).obj (op A)).obj
        (((derivedSheafHom Rc).obj (op B)).obj M)) x = u :=
    ⟨_, (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
      (((derivedSheafHom Rc).obj (op A)).obj
        (((derivedSheafHom Rc).obj (op B)).obj M))).apply_symm_apply u⟩
  have hcoh : (@MonoidalCategoryStruct.associator (DerivedCategory (StructureSheafModules Rc)) _ _
        (RingedSite.derivedStructureSheaf (ringedSite Rc)) A B).hom ≫
      derivedLeftUnitorHom Rc (((derivedTensor Rc).obj A).obj B) =
    derivedLeftUnitorHom Rc A ▷ B :=
    assoc_leftUnitor_whiskerRight (C := DerivedCategory (StructureSheafModules Rc)) A B
  have hG := derivedSheafHomTensorEquiv_globalSections Rc A B M x
  have hcl := derivedSheafHomTensorEquiv_comp_left Rc B M (derivedLeftUnitorHom Rc A)
    (derivedSheafHomGlobalSectionsEquiv Rc A (((derivedSheafHom Rc).obj (op B)).obj M) x)
  rw [← RingedSite.derivedStructureSheafGlobalSectionsEquiv_naturality (ringedSite Rc)
      (derivedCurryIso Rc A B M).hom x,
    derivedSheafHomTensorEquiv_unitSource Rc (((derivedTensor Rc).obj A).obj B) M,
    derivedSheafHomTensorEquiv_unitSource Rc A (((derivedSheafHom Rc).obj (op B)).obj M) x,
    hcl, hG, ← Category.assoc, hcoh]

/-- **The transpose of the double contraction agrees with the currying isomorphism of Stacks 08J9
on global sections.**  For objects `K`, `L`, `M` of `D(O_X)`, with `G = RSheafHom(K, L)`, every
morphism `u : O_X ⟶ RSheafHom(G, RSheafHom(K, M))` satisfies

`u ≫ derivedCounitCurry Rc K L M = u ≫ (derivedCurryIso Rc G K M).hom`.

Equivalently, `Stacks.SheafOfModules.derivedCounitCurry` and the currying comparison of
Stacks 08J9 have the same image under degree-zero global hypercohomology.

`derivedCounitCurry` is the `Φ`-transpose of the double contraction, so the left-hand side
transposes — by source naturality of `Φ`
(`Stacks.SheafOfModules.derivedSheafHomTensorEquiv_comp_left`), the naturality of the associator
in its left variable and `comp_whiskerRight` — into
`α_{O_X,G,K}.inv ≫ Φ_{O_X ⊗^L G, K, M}(Φ_{O_X, G, RSheafHom(K,M)}(u))`, which is the right-hand
side of `derivedSheafHomTensorEquiv_unitSource_assoc`.

This does **not** say that the two morphisms are equal: `O_X` is not a generator of `D(O_X)`.
What it says is that the only thing separating `derivedCounitCurry` from the comparison of
Stacks 08J9 is the associativity coherence at a source other than the structure sheaf. -/
theorem derivedCounitCurry_comp_unitSource
    (K L M : DerivedCategory (StructureSheafModules Rc))
    (u : @Quiver.Hom (DerivedCategory (StructureSheafModules Rc)) _
      (RingedSite.derivedStructureSheaf (ringedSite Rc))
      (((derivedSheafHom Rc).obj (op (((derivedSheafHom Rc).obj (op K)).obj L))).obj
        (((derivedSheafHom Rc).obj (op K)).obj M))) :
    u ≫ derivedCounitCurry Rc K L M =
      u ≫ (derivedCurryIso Rc (((derivedSheafHom Rc).obj (op K)).obj L) K M).hom := by
  refine (derivedSheafHomTensorEquiv Rc (RingedSite.derivedStructureSheaf (ringedSite Rc))
    (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op K)).obj L)).obj K) M).injective ?_
  have hnat : u ▷ (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op K)).obj L)).obj K) ≫
        (α_ (((derivedSheafHom Rc).obj (op (((derivedSheafHom Rc).obj (op K)).obj L))).obj
              (((derivedSheafHom Rc).obj (op K)).obj M))
            (((derivedSheafHom Rc).obj (op K)).obj L) K).inv ≫
          (derivedSheafHomCounit Rc (((derivedSheafHom Rc).obj (op K)).obj L)
              (((derivedSheafHom Rc).obj (op K)).obj M) ▷ K ≫
            derivedSheafHomCounit Rc K M) =
      (@MonoidalCategoryStruct.associator (DerivedCategory (StructureSheafModules Rc)) _ _
          (RingedSite.derivedStructureSheaf (ringedSite Rc))
          (((derivedSheafHom Rc).obj (op K)).obj L) K).inv ≫
        ((u ▷ ((derivedSheafHom Rc).obj (op K)).obj L) ▷ K) ≫
          (derivedSheafHomCounit Rc (((derivedSheafHom Rc).obj (op K)).obj L)
              (((derivedSheafHom Rc).obj (op K)).obj M) ▷ K ≫
            derivedSheafHomCounit Rc K M) :=
    whiskerRight_associator_inv_assoc u (((derivedSheafHom Rc).obj (op K)).obj L) K _
  have hpaste : ((u ▷ ((derivedSheafHom Rc).obj (op K)).obj L) ▷ K) ≫
        (derivedSheafHomCounit Rc (((derivedSheafHom Rc).obj (op K)).obj L)
            (((derivedSheafHom Rc).obj (op K)).obj M) ▷ K ≫
          derivedSheafHomCounit Rc K M) =
      (((u ▷ ((derivedSheafHom Rc).obj (op K)).obj L) ≫
            derivedSheafHomCounit Rc (((derivedSheafHom Rc).obj (op K)).obj L)
              (((derivedSheafHom Rc).obj (op K)).obj M)) ▷ K) ≫
        derivedSheafHomCounit Rc K M :=
    whiskerRight_comp_whiskerRight_assoc (u ▷ ((derivedSheafHom Rc).obj (op K)).obj L)
      (derivedSheafHomCounit Rc (((derivedSheafHom Rc).obj (op K)).obj L)
        (((derivedSheafHom Rc).obj (op K)).obj M)) K (derivedSheafHomCounit Rc K M)
  rw [derivedSheafHomTensorEquiv_comp_left Rc
      (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op K)).obj L)).obj K) M u,
    derivedCounitCurry, AddEquiv.apply_symm_apply, hnat, hpaste,
    derivedSheafHomCounit_whiskerRight_eq' Rc _ _ _ u,
    derivedSheafHomCounit_whiskerRight_eq'
      Rc (((derivedTensor Rc).obj (RingedSite.derivedStructureSheaf (ringedSite Rc))).obj
        (((derivedSheafHom Rc).obj (op K)).obj L)) K M, Iso.inv_comp_eq,
    derivedSheafHomTensorEquiv_unitSource_assoc Rc
      (((derivedSheafHom Rc).obj (op K)).obj L) K M u]

end Monoidal

end Stacks.SheafOfModules

end
