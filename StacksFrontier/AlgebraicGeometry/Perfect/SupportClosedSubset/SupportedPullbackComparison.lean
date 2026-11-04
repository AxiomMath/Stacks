module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportPushExcision
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestrictionNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.LocalCohomologyExcisionCounit
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedPullbackBaseChangeDegreewise

/-!
# The canonical map of Tag 0G78 is the comparison from uniqueness of right derived functors

Let `f : (X', 𝒪_{X'}) ⟶ (X, 𝒪_X)` be an **open immersion** of ringed spaces, let `Z ⊆ X` be
closed and let `Z' = f^{-1}(Z)`.  The library has two natural isomorphisms

`R𝓗_Z ⋙ L(f|_{Z'})^* ≅ Lf^* ⋙ R𝓗_{Z'}`,

built in completely different ways:

* the **canonical map of [Stacks, Tag 0G78]**,
  `Stacks.Perfect.SupportPushExcision.supportedPullbackNatTrans`, the transpose along the
  adjunction `i'_* ⊣ R𝓗_{Z'}` of [Stacks, Tag 0A3B] of the displayed composite of the source,
  invertible along an open immersion; and
* the **comparison from uniqueness of right derived functors**,
  `Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsOnClosedPullbackNatIso`, produced
  by `CategoryTheory.Functor.rightDerivedNatIso` from the degreewise excision
  `Stacks.Cohomology.SupportedComplexes.supportedSectionsOnClosedPullbackNatIso`.

This file proves that **they are the same**.

## Main results

* `derivedSupportedSectionsOnClosedPullbackNatIso_hom_app_eq_supportedPullbackMap`: the
  identification at an object of `D(𝒪_X)`.
* `supportedPullbackNatTrans_eq_derivedSupportedSectionsOnClosedPullbackNatIso` and
  `asIso_supportedPullbackNatTrans_eq_derivedSupportedSectionsOnClosedPullbackNatIso`: **the
  identification**, as natural transformations and as isomorphisms of functors.

## Implementation notes

**The route.**  The canonical map is pinned down by one adjunction equation,
`Stacks.Cohomology.SupportedComplexes.supportedPullbackMap_unique`: it is the only map whose
transpose along `i'_* ⊣ R𝓗_{Z'}` is the displayed composite of [Stacks, Tag 0G78].  Clearing the
three invertible factors of that composite — the two comparisons of the exact direct image of
[Stacks, Tag 0E2K] and the base-change transformation of [Stacks, Tag 08HY] — turns the equation
into the counit compatibility

`Θ_K ≫ (i'_* R𝓗_{Z'}(Lf^* K) ⟶ Lf^* K) = Lf^*(i_* R𝓗_Z(K) ⟶ K)`

of `Stacks.Perfect.SupportPushExcision.derivedSupportedPushforwardPullbackIso_hom_comp_counit`,
asked of the comparison from uniqueness in place of the canonical map.  Both sides of *that* are
natural transformations out of `R𝓗_Z ⋙ i_* ⋙ Lf^*`, which is a right derived functor of
`H_Z ⋙ i_* ⋙ f^*` because `i_*` and `Lf^*` are left adjoints, so
`CategoryTheory.Functor.rightDerived_ext` reduces it to an equation at a complex.  There it
becomes degreewise, and what remains is

* `Stacks.Cohomology.SupportedComplexes.supportedPullbackBaseChangeMap_eq_mapDerivedCategory_Qh`:
  the base-change transformation of [Stacks, Tag 08HY] for the square of the restriction is the
  derived image of the underived base change
  `Stacks.Cohomology.SupportedComplexes.closedSubsetPushforwardPullbackNatIso`; and
* `Stacks.Cohomology.SupportedComplexes.closedSubsetPushforwardPullbackNatIso_comp_counit`: the
  degreewise excision is compatible with that base change and with the two inclusions
  `i_* H_Z ⟶ 𝟭` of [Stacks, Tag 0G6P],

the second read on complexes and then in the homotopy category by `counit_compat_complex` and
`counit_compat_homotopy`.

**Why the anonymous factors are named.**  `derivedSupportedSectionsOnClosedPullbackNatIso` is a
composite of three isomorphisms whose middle factor is a `rightDerivedNatTrans` built from two
transformations the library leaves anonymous inside the definition.  Instantiating
`CategoryTheory.Functor.rightDerivedNatTrans_app` at those anonymous composites exhausts the
default heartbeat budget, and `set_option` is not permitted, so they are named here —
`uniquenessSourceIso`, `uniquenessTargetUnit`, `uniquenessComparison` — each written exactly as
it occurs there, after which the defining factorization is one `exact`.  For the same reason
every diagram chase is a `private` lemma at a variable category with the objects implicit and the
morphisms explicit.

**No `@[stacks ...]` attribute is attached.**  This is a compatibility of two constructions of
the library, one of which realizes [Stacks, Tag 0G78]; the tag is registered where that map is
built.

## References

* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Lemma 20.34.1 (Tag 0A3B)](https://stacks.math.columbia.edu/tag/0A3B)
* [Stacks Project, Lemma 17.5.7 (Tag 0G6P)](https://stacks.math.columbia.edu/tag/0G6P)
* [Stacks Project, Remark 20.28.3 (Tag 08HY)](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedOpenImmersion (derivedPullbackOpenImmersionIso)
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance 10000] HasDerivedCategory.standard

/-- Cancelling three invertible factors from the left of a composite.  Stated at a variable
category with the objects implicit and the morphisms explicit. -/
private theorem cancel_three {C : Type*} [Category* C] {a b c d e : C}
    (p : a ⟶ b) (p' : b ⟶ a) (q : b ⟶ c) (q' : c ⟶ b) (r : c ⟶ d) (r' : d ⟶ c)
    (x : d ⟶ e) (y : a ⟶ e) (hp : p' ≫ p = CategoryStruct.id b)
    (hq : q' ≫ q = CategoryStruct.id c) (hr : r' ≫ r = CategoryStruct.id d)
    (h : p ≫ q ≫ r ≫ x = y) : x = r' ≫ q' ≫ p' ≫ y := by
  subst h
  rw [show p' ≫ p ≫ q ≫ r ≫ x = q ≫ r ≫ x by
    rw [← Category.assoc, hp, Category.id_comp]]
  rw [show q' ≫ q ≫ r ≫ x = r ≫ x by rw [← Category.assoc, hq, Category.id_comp]]
  rw [← Category.assoc, hr, Category.id_comp]

/-- Dropping the identity that the unitor of a functor contributes at both ends of an equation.
Stated at a variable category with the objects implicit and the morphisms explicit, so that it
applies by `exact` across the two spellings of the codomain. -/
private theorem strip_identity {C : Type*} [Category* C] {a b c d : C}
    (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d) (y : a ⟶ d)
    (h : u ≫ v ≫ w ≫ CategoryStruct.id d = y ≫ CategoryStruct.id d) : u ≫ v ≫ w = y := by
  rw [Category.comp_id, Category.comp_id] at h
  exact h

/-- The chase behind the component formula for the comparison of right derived functors: one
naturality square followed by one factorization.  Stated at a variable category with the objects
implicit and the morphisms explicit. -/
private theorem chase_naturality_fac {C : Type*} [Category* C] {a b c d e g h : C}
    (m : a ⟶ b) (i1 : b ⟶ c) (u : c ⟶ d) (w : d ⟶ e)
    (i0 : a ⟶ g) (n : g ⟶ c) (s1 : g ⟶ h) (s2 : h ⟶ d)
    (hnat : m ≫ i1 = i0 ≫ n) (hfac : n ≫ u = s1 ≫ s2) :
    m ≫ i1 ≫ u ≫ w = i0 ≫ s1 ≫ s2 ≫ w := by
  rw [← Category.assoc, hnat, Category.assoc, ← Category.assoc n u, hfac]
  simp only [Category.assoc]

/-- Expanding two factors of a four-fold composite into two factors each.  Stated at a variable
category with the objects implicit and the morphisms explicit. -/
private theorem expand_two_factors {C : Type*} [Category* C] {a b c d e g h : C}
    (i : a ⟶ b) (s : b ⟶ c) (t : c ⟶ d) (w : d ⟶ e)
    (s1 : b ⟶ g) (s2 : g ⟶ c) (t1 : c ⟶ h) (t2 : h ⟶ d)
    (hs : s = s1 ≫ s2) (ht : t = t1 ≫ t2) :
    i ≫ s ≫ t ≫ w = i ≫ s1 ≫ s2 ≫ t1 ≫ t2 ≫ w := by
  rw [hs, ht]
  simp only [Category.assoc]

/-- The formal chase behind the counit equation of the comparison from uniqueness: two
naturality squares for the factorization of the direct image, two for the identifications of a
derived pullback with the degreewise pullback, the two counit factorizations of
[Stacks, Tag 0A3B], the base-change identification and the degreewise identity, with three pairs
of mutually inverse morphisms cancelled.  Stated at a variable category with the objects implicit
and the morphisms explicit. -/
private theorem chase_counit {C : Type*} [Category* C]
    {x1 x2 x3 x4 x5 x6 pa pb pb2 pc pd pe s1' t1 t2 t2b t3 t4 : C}
    (A1 : x1 ⟶ x2) (S1 : x2 ⟶ x3) (Psi : x3 ⟶ x4) (E1 : x4 ⟶ x5) (Y : x2 ⟶ x5)
    (S0 : x1 ⟶ x6) (B1 : x6 ⟶ x3) (PI0 : x6 ⟶ pa) (PGh : pa ⟶ pb) (PGi : pb ⟶ pa)
    (Pa : pb ⟶ pb2) (Pb : pb2 ⟶ pc) (Pal : pc ⟶ pd) (PRf : pd ⟶ pe) (PRi : pe ⟶ x4)
    (LFp : x1 ⟶ s1') (D1 : s1' ⟶ t1) (QS : t1 ⟶ t2) (Pi2 : t2 ⟶ pb) (Ph2 : pb ⟶ t2)
    (Ph2b : pb2 ⟶ t2b) (Ph3 : pc ⟶ t3) (Qa : t2 ⟶ t2b) (Qb : t2b ⟶ t3) (Qc : t3 ⟶ t4)
    (E2 : pd ⟶ t4) (gg : t4 ⟶ x5) (LFc : s1' ⟶ x5) (D2 : x5 ⟶ t4) (QF : t1 ⟶ t4)
    (h1 : A1 ≫ S1 = S0 ≫ B1)
    (h2 : B1 ≫ Psi = PI0 ≫ PGh ≫ Pa ≫ Pb ≫ Pal ≫ PRf ≫ PRi)
    (h3 : S0 ≫ PI0 = LFp ≫ D1 ≫ QS ≫ Pi2 ≫ PGi)
    (h4 : PGi ≫ PGh = CategoryStruct.id pb)
    (h5 : PRf ≫ PRi ≫ E1 = E2 ≫ gg)
    (h6 : Pal ≫ E2 = Ph3 ≫ Qc)
    (h7a : Pa ≫ Ph2b = Ph2 ≫ Qa)
    (h7b : Pb ≫ Ph3 = Ph2b ≫ Qb)
    (h8 : Pi2 ≫ Ph2 = CategoryStruct.id t2)
    (h9 : QS ≫ Qa ≫ Qb ≫ Qc = QF)
    (h10 : A1 ≫ Y = LFp ≫ LFc)
    (h11 : LFc ≫ D2 = D1 ≫ QF)
    (h12 : D2 ≫ gg = CategoryStruct.id x5) :
    A1 ≫ S1 ≫ Psi ≫ E1 = A1 ≫ Y := by
  have e1 : A1 ≫ S1 ≫ Psi ≫ E1 = LFp ≫ D1 ≫ QF ≫ gg := by
    calc A1 ≫ S1 ≫ Psi ≫ E1 = S0 ≫ B1 ≫ Psi ≫ E1 := by
          rw [← Category.assoc A1 S1 (Psi ≫ E1), h1, Category.assoc]
      _ = S0 ≫ (PI0 ≫ PGh ≫ Pa ≫ Pb ≫ Pal ≫ PRf ≫ PRi) ≫ E1 := by
          rw [← Category.assoc B1 Psi E1, h2]
      _ = (S0 ≫ PI0) ≫ PGh ≫ Pa ≫ Pb ≫ Pal ≫ PRf ≫ PRi ≫ E1 := by
          simp only [Category.assoc]
      _ = LFp ≫ D1 ≫ QS ≫ Pi2 ≫ PGi ≫ PGh ≫ Pa ≫ Pb ≫ Pal ≫ PRf ≫ PRi ≫ E1 := by
          rw [h3]
          simp only [Category.assoc]
      _ = LFp ≫ D1 ≫ QS ≫ Pi2 ≫ Pa ≫ Pb ≫ Pal ≫ PRf ≫ PRi ≫ E1 := by
          rw [← Category.assoc PGi PGh (Pa ≫ Pb ≫ Pal ≫ PRf ≫ PRi ≫ E1), h4,
            Category.id_comp]
      _ = LFp ≫ D1 ≫ QS ≫ Pi2 ≫ Pa ≫ Pb ≫ Pal ≫ E2 ≫ gg := by rw [h5]
      _ = LFp ≫ D1 ≫ QS ≫ Pi2 ≫ Pa ≫ Pb ≫ Ph3 ≫ Qc ≫ gg := by
          rw [← Category.assoc Pal E2 gg, h6, Category.assoc]
      _ = LFp ≫ D1 ≫ QS ≫ Pi2 ≫ Pa ≫ Ph2b ≫ Qb ≫ Qc ≫ gg := by
          rw [← Category.assoc Pb Ph3 (Qc ≫ gg), h7b, Category.assoc]
      _ = LFp ≫ D1 ≫ QS ≫ Pi2 ≫ Ph2 ≫ Qa ≫ Qb ≫ Qc ≫ gg := by
          rw [← Category.assoc Pa Ph2b (Qb ≫ Qc ≫ gg), h7a, Category.assoc]
      _ = LFp ≫ D1 ≫ QS ≫ Qa ≫ Qb ≫ Qc ≫ gg := by
          rw [← Category.assoc Pi2 Ph2 (Qa ≫ Qb ≫ Qc ≫ gg), h8, Category.id_comp]
      _ = LFp ≫ D1 ≫ QF ≫ gg := by
          have h9' : QS ≫ Qa ≫ Qb ≫ Qc ≫ gg = QF ≫ gg := by
            rw [← Category.assoc Qb Qc gg, ← Category.assoc Qa (Qb ≫ Qc) gg,
              ← Category.assoc QS (Qa ≫ Qb ≫ Qc) gg, h9]
          rw [h9']
  rw [e1, h10, ← Category.assoc D1 QF gg, ← h11, Category.assoc, h12, Category.comp_id]

/-- A functor applied to a four-fold composite, factor by factor.  Stated at variable categories
with the objects implicit and the morphisms explicit, so that it applies by `exact` across
definitionally equal spellings of the intermediate objects. -/
private theorem map_four_factors {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {a b c d e : C} (p : a ⟶ b) (q : b ⟶ c) (r : c ⟶ d) (s : d ⟶ e) (t : a ⟶ e)
    (h : p ≫ q ≫ r ≫ s = t) :
    F.map p ≫ F.map q ≫ F.map r ≫ F.map s = F.map t := by
  rw [← F.map_comp, ← F.map_comp, ← F.map_comp, h]

/-- Cancelling two nested pairs of mutually inverse morphisms.  Stated at a variable category
with the objects implicit and the morphisms explicit. -/
private theorem cancel_inner {C : Type*} [Category* C] {a b c : C}
    (p : a ⟶ b) (q : b ⟶ c) (q' : c ⟶ b) (p' : b ⟶ a)
    (hq : q ≫ q' = CategoryStruct.id b) (hp : p ≫ p' = CategoryStruct.id a) :
    (p ≫ q) ≫ q' ≫ p' = CategoryStruct.id a := by
  rw [Category.assoc, ← Category.assoc q q' p', hq, Category.id_comp, hp]

/-- A functor applied to the inverse and then the forward component of a natural isomorphism is the
identity. -/
private theorem map_inv_app_comp_map_hom_app {C D E : Type*} [Category* C] [Category* D]
    [Category* E] (F : D ⥤ E) {G H : C ⥤ D} (e : G ≅ H) (X : C) :
    F.map (e.inv.app X) ≫ F.map (e.hom.app X) = CategoryStruct.id _ := by
  rw [← F.map_comp, e.inv_hom_id_app, F.map_id]

/-- Appending the identity that a unitor contributes at both ends of an equation.  Stated at a
variable category with the objects implicit and the morphisms explicit. -/
private theorem append_identity {C : Type*} [Category* C] {a b c d e g : C}
    (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d) (x : d ⟶ e) (y : a ⟶ g) (z : g ⟶ e)
    (h : u ≫ v ≫ w ≫ x = y ≫ z) :
    u ≫ v ≫ w ≫ x ≫ CategoryStruct.id e = y ≫ z ≫ CategoryStruct.id e := by
  rw [Category.comp_id, Category.comp_id]
  exact h

/-- Cancelling a tail factor against the inverse it is composed with.  Stated at a variable
category with the objects implicit and the morphisms explicit. -/
private theorem cancel_tail {C : Type*} [Category* C] {a b c d e g h : C}
    (L : a ⟶ h) (p : a ⟶ b) (q : b ⟶ c) (r : c ⟶ d) (u : d ⟶ e) (m : e ⟶ h) (t : h ⟶ g)
    (s : e ⟶ g) (hL : L = p ≫ q ≫ r ≫ u ≫ m) (hm : m ≫ t = s) :
    L ≫ t = p ≫ q ≫ r ≫ u ≫ s := by
  rw [hL]
  simp only [Category.assoc]
  rw [hm]

variable {X' X : RingedSpace.{u, u}} (f : X' ⟶ X) [SheafedSpace.IsOpenImmersion f]
  (Z : Set X.carrier) (hZ : IsClosed Z)

section Counit

variable (hZ' : IsClosed (closedSubsetPreimage f Z))
  [PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteLimits
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))]
  [PreservesFiniteColimits
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))]

/-- The three invertible factors that precede the canonical map of [Stacks, Tag 0G78] in the
excision isomorphism `derivedSupportedPushforwardPullbackIso`, as a natural transformation
`i_* ⋙ Lf^* ⟶ L(f|_{Z'})^* ⋙ i'_*`: the comparison of the exact direct image on `X`, the
base-change transformation of [Stacks, Tag 08HY], and the comparison on `X'` inverted.

Kept `private`: `Stacks.Gysin.pullbackPushforwardIso` is this composite read at an object and as
an isomorphism, and nothing outside this file needs a second entry point to it. -/
private def closedPushforwardBaseChangeNatTrans :
    (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory ⋙ derivedPullback f ⟶
      derivedPullback (closedSubsetRestriction f Z) ⋙
        (modulePushforward
          (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory :=
  Functor.whiskerRight (closedPushforwardComparison X Z).hom (derivedPullback f) ≫
    (Stacks.Perfect.SupportPushExcision.supportedPullbackBaseChangeNatIso f Z).hom ≫
    Functor.whiskerLeft (derivedPullback (closedSubsetRestriction f Z))
      (closedPushforwardComparison X' (closedSubsetPreimage f Z)).inv

/-! ### The three anonymous factors of the comparison of right derived functors

`derivedSupportedSectionsOnClosedPullbackNatIso` is built from three transformations that the
library leaves anonymous inside its definition: the degreewise comparison of the two sources on
the homotopy category, the derivation unit of `Lf^* ⋙ R𝓗_{Z'}`, and the comparison of right
derived functors they produce.  They are named here so that the defining factorization of the
comparison can be stated and used; each is written exactly as it occurs there. -/

/-- The degreewise comparison of the two sources on the homotopy category, the `τ` of
`derivedSupportedSectionsOnClosedPullbackNatIso`: the factorization of `(f|_{Z'})^*` through the
homotopy category, followed by the degreewise excision
`supportedSectionsOnClosedPullbackNatIso` read on complexes. -/
private def uniquenessSourceIso :
    (supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⋙
          (modulePullback (closedSubsetRestriction f Z)).mapDerivedCategory ≅
      (modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        ((supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z)
          hZ').mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :=
  Functor.isoWhiskerLeft
      ((supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ))
      (modulePullback (closedSubsetRestriction f Z)).mapDerivedCategoryFactorsh ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso (supportedSectionsOnClosedPullbackNatIso f Z hZ hZ')
          (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomotopyCategoryCompIso
          (Iso.refl (modulePullback f ⋙
            supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ'))
          (ComplexShape.up ℤ)).symm) DerivedCategory.Qh

/-- The derivation unit exhibiting `Lf^* ⋙ R𝓗_{Z'}` as a right derived functor of
`f^* ⋙ H_{Z'}`, the `α'` of `derivedSupportedSectionsOnClosedPullbackNatIso`. -/
private def uniquenessTargetUnit :
    (modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        ((supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z)
          hZ').mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⟶
      DerivedCategory.Qh ⋙ (modulePullback f).mapDerivedCategory ⋙
        derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ' :=
  Functor.whiskerLeft ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ))
      (derivedSupportedSectionsOnClosedUnit X' (closedSubsetPreimage f Z) hZ') ≫
    Functor.whiskerRight (modulePullback f).mapDerivedCategoryFactorsh.inv
      (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ')

/-- The comparison of right derived functors `R𝓗_Z ⋙ D((f|_{Z'})^*) ⟶ D(f^*) ⋙ R𝓗_{Z'}` that
`derivedSupportedSectionsOnClosedPullbackNatIso` is the conjugate of. -/
private def uniquenessComparison :
    derivedSupportedSectionsOnClosed X Z hZ ⋙
        (modulePullback (closedSubsetRestriction f Z)).mapDerivedCategory ⟶
      (modulePullback f).mapDerivedCategory ⋙
        derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ' :=
  letI := isRightDerivedFunctor_derivedSupportedSectionsOnClosed_comp f Z hZ
  Functor.rightDerivedNatTrans _ _ (derivedSupportedSectionsOnClosedCompUnit f Z hZ)
    (uniquenessTargetUnit f Z hZ')
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    (uniquenessSourceIso f Z hZ hZ').hom

omit [PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteLimits
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))]
  [PreservesFiniteColimits
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))] in
/-- **The comparison of [Stacks, Tag 0G78] obtained from the uniqueness of right derived
functors is the conjugate of `uniquenessComparison`** by the two identifications of a derived
pullback along an open immersion with the degreewise pullback.  This is its definition read
through `CategoryTheory.Functor.rightDerivedNatIso_hom`. -/
private theorem derivedSupportedSectionsOnClosedPullbackNatIso_hom_eq :
    (derivedSupportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom =
      Functor.whiskerLeft (derivedSupportedSectionsOnClosed X Z hZ)
          (derivedPullbackOpenImmersionIso (closedSubsetRestriction f Z)).hom ≫
        uniquenessComparison f Z hZ hZ' ≫
        Functor.whiskerRight (derivedPullbackOpenImmersionIso f).inv
          (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ') :=
  rfl

omit [PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteLimits
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))]
  [PreservesFiniteColimits
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))] in
/-- **The defining factorization of `uniquenessComparison`**: composed with the derivation unit
of `R𝓗_Z ⋙ D((f|_{Z'})^*)` it is the degreewise comparison followed by the derivation unit of
`D(f^*) ⋙ R𝓗_{Z'}`.  This is `CategoryTheory.Functor.rightDerivedNatTrans_fac`. -/
private theorem uniquenessComparison_fac :
    derivedSupportedSectionsOnClosedCompUnit f Z hZ ≫
        Functor.whiskerLeft DerivedCategory.Qh (uniquenessComparison f Z hZ hZ') =
      (uniquenessSourceIso f Z hZ hZ').hom ≫ uniquenessTargetUnit f Z hZ' := by
  let := isRightDerivedFunctor_derivedSupportedSectionsOnClosed_comp f Z hZ
  exact Functor.rightDerivedNatTrans_fac _ _ _ _ _ _

omit [PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteLimits
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))]
  [PreservesFiniteColimits
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))] in
/-- **The comparison of [Stacks, Tag 0G78] from uniqueness, read on the derivation unit of
`R𝓗_Z`.**  Composed with `L(f|_{Z'})^*` of the derivation unit at a complex `M`, the comparison
is the degreewise comparison followed by the derivation unit on `X'`, between the two
identifications of a derived pullback along an open immersion with the degreewise pullback. -/
private theorem derivedSupportedSectionsOnClosedPullbackNatIso_hom_app_comp_unit
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (derivedPullback (closedSubsetRestriction f Z)).map
          ((derivedSupportedSectionsOnClosedUnit X Z hZ).app M) ≫
        (derivedSupportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom.app
          (DerivedCategory.Qh.obj M) =
      (derivedPullbackOpenImmersionIso (closedSubsetRestriction f Z)).hom.app
          (DerivedCategory.Qh.obj
            (((supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj M)) ≫
        (uniquenessSourceIso f Z hZ hZ').hom.app M ≫
        (uniquenessTargetUnit f Z hZ').app M ≫
        (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ').map
          ((derivedPullbackOpenImmersionIso f).inv.app (DerivedCategory.Qh.obj M)) := by
  have hfac := NatTrans.congr_app (uniquenessComparison_fac f Z hZ hZ') M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    derivedSupportedSectionsOnClosedCompUnit] at hfac
  have hnat := (derivedPullbackOpenImmersionIso (closedSubsetRestriction f Z)).hom.naturality
    ((derivedSupportedSectionsOnClosedUnit X Z hZ).app M)
  rw [derivedSupportedSectionsOnClosedPullbackNatIso_hom_eq]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  exact chase_naturality_fac _ _ _ _ _ _ _ _ hnat hfac

omit [PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteLimits
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))]
  [PreservesFiniteColimits
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))] in
/-- The components of `uniquenessSourceIso`, factor by factor. -/
private theorem uniquenessSourceIso_hom_app
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (uniquenessSourceIso f Z hZ hZ').hom.app M =
      (modulePullback (closedSubsetRestriction f Z)).mapDerivedCategoryFactorsh.hom.app
          (((supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj M) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso
                (supportedSectionsOnClosedPullbackNatIso f Z hZ hZ')
                (ComplexShape.up ℤ)).hom.app M ≫
            (Functor.mapHomotopyCategoryCompIso
              (Iso.refl (modulePullback f ⋙
                supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ'))
              (ComplexShape.up ℤ)).inv.app M) := by
  simp only [uniquenessSourceIso, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom]

omit [PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteLimits
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))]
  [PreservesFiniteColimits
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))] in
/-- The components of `uniquenessTargetUnit`, factor by factor. -/
private theorem uniquenessTargetUnit_app
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (uniquenessTargetUnit f Z hZ').app M =
      (derivedSupportedSectionsOnClosedUnit X' (closedSubsetPreimage f Z) hZ').app
          (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
        (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ').map
          ((modulePullback f).mapDerivedCategoryFactorsh.inv.app M) := by
  simp only [uniquenessTargetUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]

omit [PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteLimits
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))]
  [PreservesFiniteColimits
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))] in
/-- `derivedSupportedSectionsOnClosedPullbackNatIso_hom_app_comp_unit` with the two named
factors written out. -/
private theorem psi_comp_unit_expanded
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (derivedPullback (closedSubsetRestriction f Z)).map
          ((derivedSupportedSectionsOnClosedUnit X Z hZ).app M) ≫
        (derivedSupportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom.app
          (DerivedCategory.Qh.obj M) =
      (derivedPullbackOpenImmersionIso (closedSubsetRestriction f Z)).hom.app
          (DerivedCategory.Qh.obj
            (((supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj M)) ≫
        (modulePullback (closedSubsetRestriction f Z)).mapDerivedCategoryFactorsh.hom.app
          (((supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj M) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso
                (supportedSectionsOnClosedPullbackNatIso f Z hZ hZ')
                (ComplexShape.up ℤ)).hom.app M ≫
            (Functor.mapHomotopyCategoryCompIso
              (Iso.refl (modulePullback f ⋙
                supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ'))
              (ComplexShape.up ℤ)).inv.app M) ≫
        (derivedSupportedSectionsOnClosedUnit X' (closedSubsetPreimage f Z) hZ').app
          (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
        (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ').map
          ((modulePullback f).mapDerivedCategoryFactorsh.inv.app M) ≫
        (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ').map
          ((derivedPullbackOpenImmersionIso f).inv.app (DerivedCategory.Qh.obj M)) := by
  refine (derivedSupportedSectionsOnClosedPullbackNatIso_hom_app_comp_unit f Z hZ hZ' M).trans ?_
  exact expand_two_factors _ _ _ _ _ _ _ _ (uniquenessSourceIso_hom_app f Z hZ hZ' M)
    (uniquenessTargetUnit_app f Z hZ' M)

/-- **The identification of the base-change transformation of [Stacks, Tag 08HY] with the derived
image of the underived base change**, in the form the counit equation consumes: at a complex `M₁`
of `𝒪_X|_Z`-modules, the three factors `i_* ⟶ Ri_*`, the base-change transformation and
`Ri'_* ⟶ i'_*` of `closedPushforwardBaseChangeNatTrans`, followed by the identification of the
derived pullback along `f|_{Z'}` with the degreewise one, are the degreewise base change
`closedSubsetPushforwardPullbackNatIso` read through the four factorizations of a degreewise
functor through the homotopy category. -/
private def BaseChangeIsDegreewise : Prop :=
  ∀ M₁ : HomotopyCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z))) (ComplexShape.up ℤ),
    (closedPushforwardBaseChangeNatTrans f Z).app
        (DerivedCategory.Qh.obj M₁) ≫
      (modulePushforward (closedSubsetInclusion X'
          (closedSubsetPreimage f Z))).mapDerivedCategory.map
        ((derivedPullbackOpenImmersionIso (closedSubsetRestriction f Z)).hom.app
          (DerivedCategory.Qh.obj M₁)) =
    (derivedPullback f).map
        ((modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategoryFactorsh.hom.app
          M₁) ≫
      (derivedPullbackComparison f).app
        (((modulePushforward (closedSubsetInclusion X Z)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj
          M₁) ≫
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory (closedSubsetPushforwardPullbackNatIso f Z).hom
            (ComplexShape.up ℤ)).app
          M₁) ≫
      (modulePushforward (closedSubsetInclusion X'
          (closedSubsetPreimage f Z))).mapDerivedCategoryFactorsh.inv.app
        (((modulePullback (closedSubsetRestriction f Z)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj
          M₁) ≫
      (modulePushforward (closedSubsetInclusion X'
          (closedSubsetPreimage f Z))).mapDerivedCategory.map
        ((modulePullback (closedSubsetRestriction f Z)).mapDerivedCategoryFactorsh.inv.app
          M₁)

/-- **From the counit compatibility to the identification of the two comparisons, at an
object.**  If the comparison `derivedSupportedSectionsOnClosedPullbackNatIso` obtained from the
uniqueness of right derived functors satisfies the counit equation of
`Stacks.Perfect.SupportPushExcision.derivedSupportedPushforwardPullbackIso_hom_comp_counit`, then
it is the canonical map of [Stacks, Tag 0G78]: the equation is the adjunction equation
`supportedPullbackMap_mate` with the three invertible factors cleared, and
`supportedPullbackMap_unique` says that equation has only one solution. -/
private theorem derivedSupportedSectionsOnClosedPullbackNatIso_hom_app_eq_of_counit
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hcounit :
      (derivedPullback f).map ((closedPushforwardComparison X Z).hom.app
              ((derivedSupportedSectionsOnClosed X Z hZ).obj K)) ≫
            supportedPullbackBaseChangeMap f Z
              ((derivedSupportedSectionsOnClosed X Z hZ).obj K) ≫
            (closedPushforwardComparison X' (closedSubsetPreimage f Z)).inv.app
              ((derivedPullback (closedSubsetRestriction f Z)).obj
                ((derivedSupportedSectionsOnClosed X Z hZ).obj K)) ≫
            (modulePushforward (closedSubsetInclusion X'
                (closedSubsetPreimage f Z))).mapDerivedCategory.map
              ((derivedSupportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom.app K) ≫
            (derivedPushforwardAdjunction X' (closedSubsetPreimage f Z) hZ').counit.app
              ((derivedPullback f).obj K) =
          (derivedPullback f).map ((derivedPushforwardAdjunction X Z hZ).counit.app K)) :
    (derivedSupportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom.app K =
      supportedPullbackMap f Z hZ hZ' K := by
  have := isIso_supportedPullbackBaseChangeMap_of_isOpenImmersion f Z
    ((derivedSupportedSectionsOnClosed X Z hZ).obj K)
  refine supportedPullbackMap_unique f Z hZ hZ' K _ ?_
  refine cancel_three
    ((derivedPullback f).map ((closedPushforwardComparison X Z).hom.app
      ((derivedSupportedSectionsOnClosed X Z hZ).obj K)))
    ((derivedPullback f).map ((closedPushforwardComparison X Z).inv.app
      ((derivedSupportedSectionsOnClosed X Z hZ).obj K)))
    (supportedPullbackBaseChangeMap f Z ((derivedSupportedSectionsOnClosed X Z hZ).obj K))
    (CategoryTheory.inv (supportedPullbackBaseChangeMap f Z
      ((derivedSupportedSectionsOnClosed X Z hZ).obj K)))
    ((closedPushforwardComparison X' (closedSubsetPreimage f Z)).inv.app _)
    ((closedPushforwardComparison X' (closedSubsetPreimage f Z)).hom.app _)
    _ _ ?_ ?_ ?_ hcounit
  · exact map_inv_app_comp_map_hom_app _ _ _
  · exact IsIso.inv_hom_id _
  · exact Iso.hom_inv_id_app _ _


/-! ### Degreewise excision and the counit, on complexes and in the homotopy category -/

omit [PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteLimits
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))]
  [PreservesFiniteColimits
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))] in
/-- **Degreewise excision is compatible with the counit of [Stacks, Tag 0G6P], on a complex.**
Each degree is `closedSubsetPushforwardPullbackNatIso_comp_counit` at the module in that degree,
the two comparisons of the degreewise action on complexes contributing `δ` in each degree and an
identity. -/
private theorem counit_compat_complex
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (NatTrans.mapHomologicalComplex (closedSubsetPushforwardPullbackNatIso f Z).hom
            (ComplexShape.up ℤ)).app
          (((supportedSectionsOnClosedFunctor X Z hZ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C) ≫
        ((modulePushforward (closedSubsetInclusion X'
              (closedSubsetPreimage f Z))).mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((Functor.mapHomologicalComplexCompIso
              (supportedSectionsOnClosedPullbackNatIso f Z hZ hZ')
              (ComplexShape.up ℤ)).hom.app C) ≫
          ((modulePushforward (closedSubsetInclusion X'
                (closedSubsetPreimage f Z))).mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((Functor.mapHomologicalComplexCompIso
                (Iso.refl (modulePullback f ⋙
                  supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ'))
                (ComplexShape.up ℤ)).inv.app C) ≫
            (Adjunction.mapHomologicalComplexAdjunction
              (modulePushforward_supportedSectionsOnClosed_adjunction X'
                (closedSubsetPreimage f Z) hZ') (ComplexShape.up ℤ)).counit.app
              (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) =
      ((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((Adjunction.mapHomologicalComplexAdjunction
          (modulePushforward_supportedSectionsOnClosed_adjunction X Z hZ)
          (ComplexShape.up ℤ)).counit.app C) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  show (closedSubsetPushforwardPullbackNatIso f Z).hom.app
          ((supportedSectionsOnClosedFunctor X Z hZ).obj (C.X n)) ≫
      (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z))).map
        ((supportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom.app (C.X n)) ≫
      (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z))).map
        (CategoryStruct.id _) ≫
      (modulePushforward_supportedSectionsOnClosed_adjunction X'
        (closedSubsetPreimage f Z) hZ').counit.app ((modulePullback f).obj (C.X n)) =
    (modulePullback f).map
      ((modulePushforward_supportedSectionsOnClosed_adjunction X Z hZ).counit.app (C.X n))
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact closedSubsetPushforwardPullbackNatIso_comp_counit f Z hZ hZ' (C.X n)

omit [PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteLimits
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))]
  [PreservesFiniteColimits
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))] in
/-- **Degreewise excision is compatible with the counit of [Stacks, Tag 0G6P], in the homotopy
category.**  Every term is the class of a map of complexes, so this is `congrArg` of
`counit_compat_complex` at the representing complex. -/
private theorem counit_compat_homotopy
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (NatTrans.mapHomotopyCategory (closedSubsetPushforwardPullbackNatIso f Z).hom
            (ComplexShape.up ℤ)).app
          (((supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj M) ≫
        ((modulePushforward (closedSubsetInclusion X'
              (closedSubsetPreimage f Z))).mapHomotopyCategory (ComplexShape.up ℤ)).map
            ((Functor.mapHomotopyCategoryCompIso
              (supportedSectionsOnClosedPullbackNatIso f Z hZ hZ')
              (ComplexShape.up ℤ)).hom.app M) ≫
          ((modulePushforward (closedSubsetInclusion X'
                (closedSubsetPreimage f Z))).mapHomotopyCategory (ComplexShape.up ℤ)).map
              ((Functor.mapHomotopyCategoryCompIso
                (Iso.refl (modulePullback f ⋙
                  supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ'))
                (ComplexShape.up ℤ)).inv.app M) ≫
            (Adjunction.mapHomotopyCategoryAdjunction
              (modulePushforward_supportedSectionsOnClosed_adjunction X'
                (closedSubsetPreimage f Z) hZ') (ComplexShape.up ℤ)).counit.app
              (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) =
      ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((Adjunction.mapHomotopyCategoryAdjunction
          (modulePushforward_supportedSectionsOnClosed_adjunction X Z hZ)
          (ComplexShape.up ℤ)).counit.app M) := by
  have h := congrArg
    (HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X'))
      (ComplexShape.up ℤ)).map (counit_compat_complex f Z hZ hZ' M.as)
  simp only [CategoryTheory.Functor.map_comp] at h
  exact h

/-- **The counit equation of the comparison from uniqueness, on the derivation unit of `R𝓗_Z`**,
granted the identification `hbc` of the base-change transformation of [Stacks, Tag 08HY] with the
derived image of the underived one.  This is the equation that
`CategoryTheory.Functor.rightDerived_ext` reduces the counit compatibility of
`derivedSupportedSectionsOnClosedPullbackNatIso` to. -/
private theorem counit_compat_unit_app
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    (hbc : BaseChangeIsDegreewise f Z) :
    ((modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory ⋙
            derivedPullback f).map ((derivedSupportedSectionsOnClosedUnit X Z hZ).app M) ≫
        (closedPushforwardBaseChangeNatTrans f Z).app
          ((derivedSupportedSectionsOnClosed X Z hZ).obj (DerivedCategory.Qh.obj M)) ≫
        (modulePushforward (closedSubsetInclusion X'
            (closedSubsetPreimage f Z))).mapDerivedCategory.map
          ((derivedSupportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom.app
            (DerivedCategory.Qh.obj M)) ≫
        (derivedPushforwardAdjunction X' (closedSubsetPreimage f Z) hZ').counit.app
          ((derivedPullback f).obj (DerivedCategory.Qh.obj M)) =
      ((modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory ⋙
            derivedPullback f).map ((derivedSupportedSectionsOnClosedUnit X Z hZ).app M) ≫
        (derivedPullback f).map
          ((derivedPushforwardAdjunction X Z hZ).counit.app (DerivedCategory.Qh.obj M)) := by
  have h1 := (closedPushforwardBaseChangeNatTrans f Z).naturality
    ((derivedSupportedSectionsOnClosedUnit X Z hZ).app M)
  have h2 := congrArg (modulePushforward (closedSubsetInclusion X'
    (closedSubsetPreimage f Z))).mapDerivedCategory.map (psi_comp_unit_expanded f Z hZ hZ' M)
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at h2
  have h4 : (modulePushforward (closedSubsetInclusion X'
          (closedSubsetPreimage f Z))).mapDerivedCategory.map
        ((modulePullback (closedSubsetRestriction f Z)).mapDerivedCategoryFactorsh.inv.app
          (((supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj M)) ≫
      (modulePushforward (closedSubsetInclusion X'
          (closedSubsetPreimage f Z))).mapDerivedCategory.map
        ((modulePullback (closedSubsetRestriction f Z)).mapDerivedCategoryFactorsh.hom.app
          (((supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj M)) = CategoryStruct.id _ := by
    exact map_inv_app_comp_map_hom_app _ _ _
  have h5 := (derivedPushforwardAdjunction X' (closedSubsetPreimage f Z) hZ').counit.naturality
    ((modulePullback f).mapDerivedCategoryFactorsh.inv.app M ≫
      (derivedPullbackOpenImmersionIso f).inv.app (DerivedCategory.Qh.obj M))
  simp only [CategoryTheory.Functor.map_comp, Functor.comp_map, Functor.id_map,
    Category.assoc] at h5
  have h6 := Stacks.Perfect.SupportCounitComparison.derivedPushforwardAdjunction_counit_app X'
    (closedSubsetPreimage f Z) hZ'
    (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M)
  have h7 := (modulePushforward (closedSubsetInclusion X'
      (closedSubsetPreimage f Z))).mapDerivedCategoryFactorsh.hom.naturality
  have h7a := h7 ((Functor.mapHomotopyCategoryCompIso
    (supportedSectionsOnClosedPullbackNatIso f Z hZ hZ') (ComplexShape.up ℤ)).hom.app M)
  have h7b := h7 ((Functor.mapHomotopyCategoryCompIso
      (Iso.refl (modulePullback f ⋙
        supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ'))
      (ComplexShape.up ℤ)).inv.app M)
  have h8 := (modulePushforward (closedSubsetInclusion X'
      (closedSubsetPreimage f Z))).mapDerivedCategoryFactorsh.inv_hom_id_app
    (((modulePullback (closedSubsetRestriction f Z)).mapHomotopyCategory
      (ComplexShape.up ℤ)).obj
      (((supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj M))
  have h9 := map_four_factors DerivedCategory.Qh _ _ _ _ _
    (counit_compat_homotopy f Z hZ hZ' M)
  have h10 := congrArg (derivedPullback f).map
    (Stacks.Perfect.SupportCounitComparison.derivedPushforwardAdjunction_counit_app X Z hZ M)
  simp only [CategoryTheory.Functor.map_comp] at h10
  have h11 := (derivedPullbackComparison f).naturality
    ((Adjunction.mapHomotopyCategoryAdjunction
      (modulePushforward_supportedSectionsOnClosed_adjunction X Z hZ)
      (ComplexShape.up ℤ)).counit.app M)
  have hd : (derivedPullbackComparison f).app M =
      (derivedPullbackOpenImmersionIso f).hom.app (DerivedCategory.Qh.obj M) ≫
        (modulePullback f).mapDerivedCategoryFactorsh.hom.app M :=
    (Stacks.Homology.leftDerivedIsoMapDerivedCategory_hom_app (modulePullback f)
      (derivedPullback f) (derivedPullbackComparison f) M).symm
  have h12 : (derivedPullbackComparison f).app M ≫
      (modulePullback f).mapDerivedCategoryFactorsh.inv.app M ≫
        (derivedPullbackOpenImmersionIso f).inv.app (DerivedCategory.Qh.obj M) =
      CategoryStruct.id _ := by
    rw [hd]
    exact cancel_inner _ _ _ _
      ((modulePullback f).mapDerivedCategoryFactorsh.hom_inv_id_app M)
      ((derivedPullbackOpenImmersionIso f).hom_inv_id_app (DerivedCategory.Qh.obj M))
  exact chase_counit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    h1 h2 (hbc _) h4 h5 h6 h7a h7b h8 h9 h10 h11 h12

private theorem counit_compat_of_baseChange
    (hbc : BaseChangeIsDegreewise f Z)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (closedPushforwardBaseChangeNatTrans f Z).app
          ((derivedSupportedSectionsOnClosed X Z hZ).obj K) ≫
        (modulePushforward (closedSubsetInclusion X'
            (closedSubsetPreimage f Z))).mapDerivedCategory.map
          ((derivedSupportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom.app K) ≫
        (derivedPushforwardAdjunction X' (closedSubsetPreimage f Z) hZ').counit.app
          ((derivedPullback f).obj K) =
      (derivedPullback f).map ((derivedPushforwardAdjunction X Z hZ).counit.app K) := by
  let : (derivedPullback f).IsLeftAdjoint := ⟨_, ⟨derivedAdjunction f⟩⟩
  let : ((modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory ⋙
      derivedPullback f).IsLeftAdjoint :=
    ⟨_, ⟨(derivedPushforwardAdjunction X Z hZ).comp (derivedAdjunction f)⟩⟩
  have key := Functor.rightDerived_ext
    (derivedSupportedSectionsOnClosed X Z hZ ⋙
      ((modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory ⋙ derivedPullback f))
    (Functor.whiskerRight (derivedSupportedSectionsOnClosedUnit X Z hZ)
        ((modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory ⋙
          derivedPullback f) ≫
      (Functor.associator _ _ _).hom)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    (derivedPullback f)
    (Functor.whiskerLeft (derivedSupportedSectionsOnClosed X Z hZ)
        (closedPushforwardBaseChangeNatTrans f Z) ≫
      Functor.whiskerRight (derivedSupportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom
        (modulePushforward (closedSubsetInclusion X'
          (closedSubsetPreimage f Z))).mapDerivedCategory ≫
      Functor.whiskerLeft (derivedPullback f)
        (derivedPushforwardAdjunction X' (closedSubsetPreimage f Z) hZ').counit ≫
      (Functor.rightUnitor (derivedPullback f)).hom)
    (Functor.whiskerRight (derivedPushforwardAdjunction X Z hZ).counit (derivedPullback f) ≫
      (Functor.leftUnitor (derivedPullback f)).hom) ?_
  · have h := NatTrans.congr_app key K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.rightUnitor, Functor.leftUnitor] at h
    exact strip_identity _ _ _ _ h
  · ext M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.rightUnitor, Functor.leftUnitor, Functor.comp_obj,
      Category.id_comp, Category.assoc]
    exact append_identity _ _ _ _ _ _ (counit_compat_unit_app f Z hZ hZ' M hbc)

/-- The components of `closedPushforwardBaseChangeNatTrans`, factor by factor. -/
private theorem closedPushforwardBaseChangeNatTrans_app
    (N : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z)))) :
    (closedPushforwardBaseChangeNatTrans f Z).app N =
      (derivedPullback f).map ((closedPushforwardComparison X Z).hom.app N) ≫
        supportedPullbackBaseChangeMap f Z N ≫
        (closedPushforwardComparison X' (closedSubsetPreimage f Z)).inv.app
          ((derivedPullback (closedSubsetRestriction f Z)).obj N) :=
  rfl

/-- **The canonical map of [Stacks, Tag 0G78] is the comparison obtained from the uniqueness of
right derived functors**, granted the identification `hbc` of the base-change transformation of
[Stacks, Tag 08HY] with the derived image of the underived one. -/
private theorem psi_app_eq_of_baseChange (hbc : BaseChangeIsDegreewise f Z)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedSupportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom.app K =
      supportedPullbackMap f Z hZ hZ' K := by
  refine derivedSupportedSectionsOnClosedPullbackNatIso_hom_app_eq_of_counit f Z hZ hZ' K ?_
  have h := counit_compat_of_baseChange f Z hZ hZ' hbc K
  rw [closedPushforwardBaseChangeNatTrans_app] at h
  simpa only [Category.assoc] using h

include hZ hZ' in
/-- **The base-change transformation of [Stacks, Tag 08HY] for the square of the restriction is
the derived image of the underived one**, in the form the counit equation consumes.  This is
`supportedPullbackBaseChangeMap_eq_mapDerivedCategory_Qh` with the identification of the derived
pullback along `f|_{Z'}` with the degreewise one moved to the other side. -/
private theorem baseChangeIsDegreewise : BaseChangeIsDegreewise f Z := by
  intro M₁
  refine cancel_tail _ _ _ _ _ _ _ _
    ((closedPushforwardBaseChangeNatTrans_app f Z (DerivedCategory.Qh.obj M₁)).trans
      (supportedPullbackBaseChangeMap_eq_mapDerivedCategory_Qh f Z hZ hZ' M₁)) ?_
  rw [← CategoryTheory.Functor.map_comp, Category.assoc, Iso.inv_hom_id_app]
  exact congrArg (modulePushforward (closedSubsetInclusion X'
    (closedSubsetPreimage f Z))).mapDerivedCategory.map (Category.comp_id _)

/-- **The comparison of [Stacks, Tag 0G78] obtained from the uniqueness of right derived functors
is the canonical map**, at an object of `D(𝒪_X)`. -/
private theorem psi_app_eq
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedSupportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom.app K =
      supportedPullbackMap f Z hZ hZ' K :=
  psi_app_eq_of_baseChange f Z hZ hZ' (baseChangeIsDegreewise f Z hZ hZ') K

end Counit

/-! ### The identification -/

/-- **The canonical comparison of [Stacks, Tag 0G78] agrees with the one obtained from the
uniqueness of right derived functors**, at an object of `D(𝒪_X)`.

For an open immersion of ringed spaces `f : X' ⟶ X`, a closed `Z ⊆ X` and `Z' = f^{-1}(Z)`, the
comparison `derivedSupportedSectionsOnClosedPullbackNatIso`, built from the uniqueness of right
derived functors out of the degreewise excision
`supportedSectionsOnClosedPullbackNatIso`, has as its component at `K` the canonical map
`supportedPullbackMap` of [Stacks, Tag 0G78]. -/
theorem derivedSupportedSectionsOnClosedPullbackNatIso_hom_app_eq_supportedPullbackMap
    (hZ' : IsClosed (closedSubsetPreimage f Z))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    letI := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
    letI := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z) hZ'
    (derivedSupportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom.app K =
      supportedPullbackMap f Z hZ hZ' K := by
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  let := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
  let := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z) hZ'
  exact psi_app_eq f Z hZ hZ' K

/-- **The canonical map of [Stacks, Tag 0G78] is the comparison obtained from the uniqueness of
right derived functors**, as natural transformations
`R𝓗_Z ⋙ L(f|_{Z'})^* ⟶ Lf^* ⋙ R𝓗_{Z'}`.

`Stacks.Perfect.SupportPushExcision.supportedPullbackNatTrans` is the canonical map of
[Stacks, Tag 0G78], the transpose along the adjunction of [Stacks, Tag 0A3B] of the displayed
composite of the source, and `derivedSupportedSectionsOnClosedPullbackNatIso` is the comparison
that the uniqueness of right derived functors produces from the degreewise excision
`supportedSectionsOnClosedPullbackNatIso`.  They are the same transformation. -/
theorem supportedPullbackNatTrans_eq_derivedSupportedSectionsOnClosedPullbackNatIso :
    Stacks.Perfect.SupportPushExcision.supportedPullbackNatTrans f Z hZ =
      (derivedSupportedSectionsOnClosedPullbackNatIso f Z hZ
        (isClosed_closedSubsetPreimage f Z hZ)).hom := by
  refine NatTrans.ext (funext fun K => ?_)
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  let := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
  let := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z)
    (isClosed_closedSubsetPreimage f Z hZ)
  rw [Stacks.Perfect.SupportPushExcision.supportedPullbackNatTrans_app]
  exact (psi_app_eq f Z hZ (isClosed_closedSubsetPreimage f Z hZ) K).symm

/-- **The two isomorphisms `R𝓗_Z ⋙ L(f|_{Z'})^* ≅ Lf^* ⋙ R𝓗_{Z'}` of the library are equal.**
The canonical map of [Stacks, Tag 0G78], invertible along an open immersion by
`Stacks.Perfect.SupportPushExcision.isIso_supportedPullbackNatTrans`, is the comparison
`derivedSupportedSectionsOnClosedPullbackNatIso` obtained from the uniqueness of right derived
functors.  This is the form the excision isomorphism
`Stacks.Perfect.SupportPushExcision.derivedSupportedPushforwardPullbackIso` is built from. -/
theorem asIso_supportedPullbackNatTrans_eq_derivedSupportedSectionsOnClosedPullbackNatIso :
    asIso (Stacks.Perfect.SupportPushExcision.supportedPullbackNatTrans f Z hZ) =
      derivedSupportedSectionsOnClosedPullbackNatIso f Z hZ
        (isClosed_closedSubsetPreimage f Z hZ) :=
  Iso.ext (supportedPullbackNatTrans_eq_derivedSupportedSectionsOnClosedPullbackNatIso f Z hZ)


end Stacks.Cohomology.SupportedComplexes

end
