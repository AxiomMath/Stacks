module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Homology of complexes under an exact functor

An exact additive functor `E : A ⥤ B` between abelian categories commutes with the homology
of cochain complexes. This file records that comparison in the forms used downstream: on
`HomologicalComplex`, on the homotopy category, and after inverting quasi-isomorphisms.

The comparison on the homotopy category is obtained from the one on complexes by the universal
property of the localization `HomotopyCategory.quotient`, so `quotHomologyIso` — the version
before descending along that quotient — is kept available: it is the form in which a statement
about the comparison can be checked, since a natural transformation out of a localization is
determined by its restriction along the localization functor.

## Main definitions

* `Stacks.Homology.mapHomotopyCategoryIso`: an isomorphism of additive functors induces an
  isomorphism of the induced functors on homotopy categories.
* `Stacks.Homology.exactHomologyIso`: an exact functor commutes with the homology functor on
  cochain complexes.
* `Stacks.Homology.derivedHomologyIso`: the same comparison on the derived category.
* `Stacks.Homology.quotHomologyIso`: the same comparison, restricted along
  `HomotopyCategory.quotient`.
* `Stacks.Homology.homotopyHomologyIso`: the comparison on homotopy categories.
* `Stacks.Homology.derivedSourceIso`: for an additive `F : A ⥤ P` and an exact `E : P ⥤ G`,
  the comparison between the homology in degree `q` of the complex of `F`-images, evaluated
  through `E`, and the homology of the complex of `F ⋙ E`-images.
* `Stacks.Homology.mapDerivedCategoryIdIso`: the identity functor induces the identity functor on
  the unbounded derived category.

## Main results

* `Stacks.Homology.mapHomologyIso_homologyπ`: **the comparison of the homology of a short
  complex with the homology of its image carries the class of a cycle to the class of that
  cycle**, the two cycle objects being identified by `ShortComplex.mapCyclesIso`.
* `Stacks.Homology.exactHomologyIso_hom_app_homologyπ` and
  `Stacks.Homology.map_homologyπ_exactHomologyIso_inv_app`: the same for a complex, which is
  the compatibility of `exactHomologyIso` with `HomologicalComplex.homologyπ`.

## Implementation notes

`derivedSourceIso` is the comparison of the *sources* of two right derived functors; it is
stated on homotopy categories rather than on derived categories because that is where the
universal property of the right derived functor consumes it.

The compatibility of the comparison with the class of a cycle is proved by identifying both
`ShortComplex.mapCyclesIso` and `ShortComplex.mapHomologyIso` with the comparisons attached to
the chosen left homology data of `S`, where it is
`ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom`. The chain is written in term
mode: `ShortComplex.LeftHomologyData.map` is a definition produced by a tactic block, so a goal
mentioning both `(h.map F).H` and `F.obj h.H` is not type-correct at the transparency a rewrite
uses, and only `exact` sees the two as the same object.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Homology

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]

/-- An isomorphism of additive functors induces an isomorphism on homotopy categories. -/
public def mapHomotopyCategoryIso [Preadditive A] [Preadditive B] {F G : A ⥤ B}
    [F.Additive] [G.Additive] (e : F ≅ G) (c : ComplexShape ℤ) :
    F.mapHomotopyCategory c ≅ G.mapHomotopyCategory c where
  hom := NatTrans.mapHomotopyCategory e.hom c
  inv := NatTrans.mapHomotopyCategory e.inv c
  hom_inv_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id, NatTrans.mapHomotopyCategory_id]
  inv_hom_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id, NatTrans.mapHomotopyCategory_id]

/-- The isomorphism on homotopy categories induced by `F ⋙ G ≅ H`, followed by the one induced
by `H ≅ H'`, is the one induced by the composite `F ⋙ G ≅ H'`. -/
public theorem mapHomotopyCategoryCompIso_trans_mapHomotopyCategoryIso {C : Type u₃}
    [Category.{v₃} C] [Preadditive A] [Preadditive B] [Preadditive C] {F : A ⥤ B} {G : B ⥤ C}
    {H H' : A ⥤ C} [F.Additive] [G.Additive] [H.Additive] [H'.Additive] (e₁ : F ⋙ G ≅ H)
    (e₂ : H ≅ H') (c : ComplexShape ℤ) :
    Functor.mapHomotopyCategoryCompIso e₁ c ≪≫ mapHomotopyCategoryIso e₂ c =
      Functor.mapHomotopyCategoryCompIso (e₁ ≪≫ e₂) c := by
  refine Iso.ext (NatTrans.ext (funext fun K => ?_))
  rcases K with ⟨K⟩
  show (HomotopyCategory.quotient C c).map
      ((Functor.mapHomologicalComplexCompIso e₁ c).hom.app K) ≫
      (HomotopyCategory.quotient C c).map ((NatTrans.mapHomologicalComplex e₂.hom c).app K) =
    (HomotopyCategory.quotient C c).map
      ((Functor.mapHomologicalComplexCompIso (e₁ ≪≫ e₂) c).hom.app K)
  rw [← Functor.map_comp]
  congr 1

section Cycles

variable [Limits.HasZeroMorphisms A] [Limits.HasZeroMorphisms B]

/-- **The comparison of the homology of a short complex with the homology of its image under a
functor preserving its left homology is compatible with the projection from cycles.** The class
of a cycle of the image is the image of the class of that cycle.

Mathlib has the two naturality statements of `ShortComplex.mapHomologyIso` in the short complex
and the two characterisations of `ShortComplex.mapCyclesIso` by the inclusion of cycles, but not
this compatibility of the two comparisons with `ShortComplex.homologyπ`; everything used in the
proof is the identification of both comparisons with the ones attached to the chosen left
homology data of `S`. -/
public theorem mapHomologyIso_homologyπ (S : ShortComplex A) (F : A ⥤ B)
    [F.PreservesZeroMorphisms] [S.HasHomology] [(S.map F).HasHomology]
    [F.PreservesLeftHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  have hce : S.leftHomologyData.cyclesIso = Iso.refl S.cycles :=
    Iso.ext (ShortComplex.cyclesMap'_id _)
  have hci : S.leftHomologyData.cyclesIso.inv = 𝟙 S.cycles := congrArg (fun e => e.inv) hce
  have h2 : S.leftHomologyData.π ≫ S.leftHomologyData.homologyIso.inv = S.homologyπ := by
    rw [ShortComplex.LeftHomologyData.π_comp_homologyIso_inv, hci]
    exact Category.id_comp _
  calc (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom
      = (S.map F).homologyπ ≫ (S.leftHomologyData.map F).homologyIso.hom ≫
          F.map S.leftHomologyData.homologyIso.inv :=
        congrArg (fun z => (S.map F).homologyπ ≫ z)
          (congrArg (fun e => e.hom) (S.leftHomologyData.mapHomologyIso_eq F))
    _ = ((S.map F).homologyπ ≫ (S.leftHomologyData.map F).homologyIso.hom) ≫
          F.map S.leftHomologyData.homologyIso.inv := (Category.assoc _ _ _).symm
    _ = ((S.mapCyclesIso F).hom ≫ (S.leftHomologyData.map F).π) ≫
          F.map S.leftHomologyData.homologyIso.inv :=
        congrArg (fun z => z ≫ F.map S.leftHomologyData.homologyIso.inv)
          (ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom _
            (S.leftHomologyData.map F))
    _ = (S.mapCyclesIso F).hom ≫ (S.leftHomologyData.map F).π ≫
          F.map S.leftHomologyData.homologyIso.inv := Category.assoc _ _ _
    _ = (S.mapCyclesIso F).hom ≫ F.map S.leftHomologyData.π ≫
          F.map S.leftHomologyData.homologyIso.inv :=
        congrArg (fun z => (S.mapCyclesIso F).hom ≫ z ≫
            F.map S.leftHomologyData.homologyIso.inv)
          (ShortComplex.LeftHomologyData.map_π S.leftHomologyData F)
    _ = (S.mapCyclesIso F).hom ≫
          F.map (S.leftHomologyData.π ≫ S.leftHomologyData.homologyIso.inv) :=
        congrArg (fun z => (S.mapCyclesIso F).hom ≫ z) (F.map_comp _ _).symm
    _ = (S.mapCyclesIso F).hom ≫ F.map S.homologyπ :=
        congrArg (fun z => (S.mapCyclesIso F).hom ≫ F.map z) h2

end Cycles

section Abelian

variable [Abelian A] [Abelian B] (E : A ⥤ B) [E.Additive]
  [PreservesFiniteLimits E] [PreservesFiniteColimits E] (n : ℤ)

/-- An exact functor commutes canonically with homology of complexes. -/
public def exactHomologyIso :
    E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) n ≅
      HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n ⋙ E :=
  NatIso.ofComponents (fun K => (K.sc n).mapHomologyIso E) (fun φ =>
    ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) n).map φ) E)

/-- The component of `exactHomologyIso E n` at a complex `K` is the comparison isomorphism
`(K.sc n).mapHomologyIso E` of the degree-`n` short complex of `K`. -/
public theorem exactHomologyIso_hom_app (K : CochainComplex A ℤ) :
    (exactHomologyIso E n).hom.app K = ((K.sc n).mapHomologyIso E).hom := rfl

/-- **The comparison is compatible with the class of a cocycle.** For a complex `K`, the class
of a degree-`n` cocycle of the complex of `E`-images is carried by the comparison to the image
of the class of that cocycle, the two cycle objects being identified by
`ShortComplex.mapCyclesIso` of the degree-`n` short complex of `K`.

This is the statement `Stacks.Homology.exactHomologyIso` had no compatibility with
`HomologicalComplex.homologyπ`; it is `mapHomologyIso_homologyπ` at `S = K.sc n`, the cycles and
the homology of a complex in degree `n` being those of that short complex. -/
public theorem exactHomologyIso_hom_app_homologyπ (K : CochainComplex A ℤ) :
    ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ n ≫
        (exactHomologyIso E n).hom.app K =
      ((K.sc n).mapCyclesIso E).hom ≫ E.map (K.homologyπ n) :=
  mapHomologyIso_homologyπ (K.sc n) E

/-- **The inverse comparison is compatible with the class of a cocycle**, which is the form a
consumer holding a section of the restricted cohomology sheaf uses: the image of the class of a
cocycle is the class of the corresponding cocycle of the complex of `E`-images. -/
public theorem map_homologyπ_exactHomologyIso_inv_app (K : CochainComplex A ℤ) :
    E.map (K.homologyπ n) ≫ (exactHomologyIso E n).inv.app K =
      ((K.sc n).mapCyclesIso E).inv ≫
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ n := by
  refine (Iso.eq_inv_comp ((K.sc n).mapCyclesIso E)).2 ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ (exactHomologyIso E n).inv.app K)
    (exactHomologyIso_hom_app_homologyπ E n K).symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg
    (fun z => ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ n ≫ z)
    ((exactHomologyIso E n).hom_inv_id_app K)).trans ?_
  exact Category.comp_id _

/-- **An exact functor commutes canonically with homology on the derived category.**  The
comparison is `exactHomologyIso` descended along the localization `DerivedCategory.Q`, which it
does descend because both sides of the statement are functors on the derived category and the
comparison on complexes is natural. -/
public def derivedHomologyIso [HasDerivedCategory A] [HasDerivedCategory B] :
    E.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor B n ≅
      DerivedCategory.homologyFunctor A n ⋙ E :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (E.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor B n))
    (DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor A n ⋙ E)) _ _
    (Functor.isoWhiskerRight E.mapDerivedCategoryFactors
        (DerivedCategory.homologyFunctor B n) ≪≫
      Functor.isoWhiskerLeft (E.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.homologyFunctorFactors B n) ≪≫
      exactHomologyIso E n ≪≫
      Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors A n).symm E)

end Abelian

section Chains

/-- Three horizontally composable commuting squares compose. Stated abstractly so that the
chain can be assembled without `rw` having to re-elaborate a composite written in two
`rfl`-equal spellings of the same functor. -/
public theorem three_squares {X : Type*} [Category* X] {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : X}
    {a : x₁ ⟶ y₁} {p₁ : x₁ ⟶ x₂} {p₂ : x₂ ⟶ x₃} {p₃ : x₃ ⟶ x₄}
    {q₁ : y₁ ⟶ y₂} {q₂ : y₂ ⟶ y₃} {q₃ : y₃ ⟶ y₄}
    {b : x₂ ⟶ y₂} {c : x₃ ⟶ y₃} {d : x₄ ⟶ y₄}
    (h₁ : a ≫ q₁ = p₁ ≫ b) (h₂ : b ≫ q₂ = p₂ ≫ c) (h₃ : c ≫ q₃ = p₃ ≫ d) :
    a ≫ q₁ ≫ q₂ ≫ q₃ = (p₁ ≫ p₂ ≫ p₃) ≫ d := by
  rw [← Category.assoc, h₁, Category.assoc, ← Category.assoc b, h₂, Category.assoc, h₃]
  simp

/-- Four horizontally composable commuting squares compose. -/
public theorem four_squares {X : Type*} [Category* X] {x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ y₅ : X}
    {a : x₁ ⟶ y₁} {p₁ : x₁ ⟶ x₂} {p₂ : x₂ ⟶ x₃} {p₃ : x₃ ⟶ x₄} {p₄ : x₄ ⟶ x₅}
    {q₁ : y₁ ⟶ y₂} {q₂ : y₂ ⟶ y₃} {q₃ : y₃ ⟶ y₄} {q₄ : y₄ ⟶ y₅}
    {b : x₂ ⟶ y₂} {c : x₃ ⟶ y₃} {d : x₄ ⟶ y₄} {e : x₅ ⟶ y₅}
    (h₁ : a ≫ q₁ = p₁ ≫ b) (h₂ : b ≫ q₂ = p₂ ≫ c) (h₃ : c ≫ q₃ = p₃ ≫ d)
    (h₄ : d ≫ q₄ = p₄ ≫ e) :
    a ≫ q₁ ≫ q₂ ≫ q₃ ≫ q₄ = (p₁ ≫ p₂ ≫ p₃ ≫ p₄) ≫ e := by
  simp only [Category.assoc] at *
  rw [reassoc_of% (three_squares h₁ h₂ h₃), h₄]

/-- The combination of five commuting squares used to compare two natural transformations out
of a right derived functor: two paths from `a` to `c` through the comparison isomorphisms. -/
public theorem comp_eq_of_squares {X : Type*} [Category* X] {x x' y y' m n k t : X}
    {a : x ⟶ x'} {u : x' ⟶ y'} {w : y' ⟶ t} {r : x ⟶ y} {b : y ⟶ y'} {s : y ⟶ m}
    {c : m ⟶ t} {v : x' ⟶ n} {z : n ⟶ t} {p : x ⟶ k} {d : k ⟶ n} {e : k ⟶ m}
    (h₁ : a ≫ u = r ≫ b) (h₂ : b ≫ w = s ≫ c) (h₃ : a ≫ v = p ≫ d)
    (h₄ : d ≫ z = e ≫ c) (h₅ : r ≫ s = p ≫ e) :
    a ≫ u ≫ w = a ≫ v ≫ z := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc, h₅, Category.assoc, ← h₄,
    ← Category.assoc, ← h₃, Category.assoc]

end Chains

section Abelian2

variable [Abelian A] [Abelian B] (E : A ⥤ B) [E.Additive]
  [PreservesFiniteLimits E] [PreservesFiniteColimits E] (n : ℤ)

/-- The comparison on homotopy categories, before descending along the quotient functor.
Only three factors appear because `HomotopyCategory.quotient A c ⋙ E.mapHomotopyCategory c`
and `E.mapHomologicalComplex c ⋙ HomotopyCategory.quotient B c` are the same functor. -/
public def quotHomologyIso :
    HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        (HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n ⋙ E) ≅
      HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        (E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) n) :=
  Functor.isoWhiskerRight
      (HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) n) E ≪≫
    (exactHomologyIso E n).symm ≪≫
    Functor.isoWhiskerLeft (E.mapHomologicalComplex (ComplexShape.up ℤ))
      (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) n).symm

/-- The component of `quotHomologyIso E n` at a complex `K`, written as the composite of its
three factors. -/
public theorem quotHomologyIso_hom_app (K : CochainComplex A ℤ) :
    (quotHomologyIso E n).hom.app K =
      E.map ((HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) n).hom.app K) ≫
        (exactHomologyIso E n).inv.app K ≫
        (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) n).inv.app
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := rfl

/-- The homology comparison for an exact functor descends to homotopy categories. -/
public def homotopyHomologyIso :
    HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n ⋙ E ≅
      E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) n :=
  Localization.liftNatIso (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ)) _ _
    (HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n ⋙ E)
    (E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) n) (quotHomologyIso E n)

/-- On the image of a complex `K` in the homotopy category, the component of
`homotopyHomologyIso E n` is the component of `quotHomologyIso E n` at `K`. -/
public theorem homotopyHomologyIso_hom_app_quotient (K : CochainComplex A ℤ) :
    (homotopyHomologyIso E n).hom.app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) =
      (quotHomologyIso E n).hom.app K := by
  rw [homotopyHomologyIso, Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  simp

end Abelian2

section Naturality

variable [Abelian A] [Abelian B] {E₁ E₂ : A ⥤ B} [E₁.Additive] [E₂.Additive]
  [PreservesFiniteLimits E₁] [PreservesFiniteColimits E₁]
  [PreservesFiniteLimits E₂] [PreservesFiniteColimits E₂]

/-- The comparison on complexes is natural in the exact functor. -/
public theorem exactHomologyIso_hom_naturality (ρ : E₁ ⟶ E₂) (n : ℤ) :
    Functor.whiskerRight (NatTrans.mapHomologicalComplex ρ (ComplexShape.up ℤ))
          (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) n) ≫
        (exactHomologyIso E₂ n).hom =
      (exactHomologyIso E₁ n).hom ≫
        Functor.whiskerLeft (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n) ρ := by
  ext K
  have h : ShortComplex.homologyMap ((K.sc n).mapNatTrans ρ) ≫
      ((K.sc n).mapHomologyIso E₂).hom =
      ((K.sc n).mapHomologyIso E₁).hom ≫ ρ.app ((K.sc n).homology) := by
    rw [ShortComplex.homologyMap_mapNatTrans]
    simp
  exact h

/-- The inverse of the comparison on complexes is natural in the exact functor. -/
public theorem exactHomologyIso_inv_naturality (ρ : E₁ ⟶ E₂) (n : ℤ) :
    Functor.whiskerLeft (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n) ρ ≫
        (exactHomologyIso E₂ n).inv =
      (exactHomologyIso E₁ n).inv ≫
        Functor.whiskerRight (NatTrans.mapHomologicalComplex ρ (ComplexShape.up ℤ))
          (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) n) := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact (exactHomologyIso_hom_naturality ρ n).symm

/-- The comparison `quotHomologyIso` is natural in the exact functor: its components at a
complex `K` commute with the maps induced by a natural transformation `ρ : E₁ ⟶ E₂`. -/
public theorem quotHomologyIso_hom_naturality (ρ : E₁ ⟶ E₂) (n : ℤ)
    (K : CochainComplex A ℤ) :
    ρ.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n).obj K) ≫
        (quotHomologyIso E₂ n).hom.app K =
      (quotHomologyIso E₁ n).hom.app K ≫
        (HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) n).map
          ((NatTrans.mapHomotopyCategory ρ (ComplexShape.up ℤ)).app
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) :=
  three_squares
    (b := ρ.app ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n).obj K))
    (c := (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) n).map
      ((NatTrans.mapHomologicalComplex ρ (ComplexShape.up ℤ)).app K))
    ((ρ.naturality _).symm)
    (congr_app (exactHomologyIso_inv_naturality ρ n) K)
    ((HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) n).inv.naturality _)

/-- The comparison on homotopy categories is natural in the exact functor. -/
public theorem homotopyHomologyIso_hom_naturality (ρ : E₁ ⟶ E₂) (n : ℤ) :
    Functor.whiskerLeft (HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n) ρ ≫
        (homotopyHomologyIso E₂ n).hom =
      (homotopyHomologyIso E₁ n).hom ≫
        Functor.whiskerRight (NatTrans.mapHomotopyCategory ρ (ComplexShape.up ℤ))
          (HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) n) := by
  refine Localization.natTrans_ext (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ)) (fun K => ?_)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [homotopyHomologyIso_hom_app_quotient, homotopyHomologyIso_hom_app_quotient]
  exact quotHomologyIso_hom_naturality ρ n K

end Naturality

section Source

variable {P : Type u₂} {G : Type u₃} [Category.{v₂} P] [Category.{v₃} G]
  [Abelian A] [Abelian P] [Abelian G] [HasDerivedCategory P] [HasDerivedCategory G]
  (F : A ⥤ P) [F.Additive] (E : P ⥤ G) [E.Additive]
  [PreservesFiniteLimits E] [PreservesFiniteColimits E] (q : ℤ)

/-- The comparison of the sources of the two right derived functors computing, respectively,
the `q`-th homology of the complex of `F`-images seen through `E`, and the `q`-th homology of
the complex of `F ⋙ E`-images.

No associator appears: `(F.mapHomotopyCategory c ⋙ DerivedCategory.Qh) ⋙ H` and
`F.mapHomotopyCategory c ⋙ (DerivedCategory.Qh ⋙ H)` are the same functor, and keeping the
chain to four factors is what makes `derivedSourceIso_hom_app` hold by `rfl`. -/
public def derivedSourceIso :
    ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙
        DerivedCategory.homologyFunctor P q) ⋙ E ≅
      (F ⋙ E).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Qh ⋙ DerivedCategory.homologyFunctor G q) :=
  Functor.isoWhiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ))
      (Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactorsh P q) E) ≪≫
    Functor.isoWhiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ))
      (homotopyHomologyIso E q) ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ E)) (ComplexShape.up ℤ))
      (HomotopyCategory.homologyFunctor G (ComplexShape.up ℤ) q) ≪≫
    Functor.isoWhiskerLeft ((F ⋙ E).mapHomotopyCategory (ComplexShape.up ℤ))
      (DerivedCategory.homologyFunctorFactorsh G q).symm

/-- The component of `derivedSourceIso F E q` at an object `I` of the homotopy category,
written as the composite of its four factors. -/
public theorem derivedSourceIso_hom_app (I : HomotopyCategory A (ComplexShape.up ℤ)) :
    (derivedSourceIso F E q).hom.app I =
      E.map ((DerivedCategory.homologyFunctorFactorsh P q).hom.app
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj I)) ≫
        (homotopyHomologyIso E q).hom.app
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj I) ≫
        (HomotopyCategory.homologyFunctor G (ComplexShape.up ℤ) q).map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ E))
            (ComplexShape.up ℤ)).hom.app I) ≫
        (DerivedCategory.homologyFunctorFactorsh G q).inv.app
          (((F ⋙ E).mapHomotopyCategory (ComplexShape.up ℤ)).obj I) := rfl

end Source

section SourceNaturality

variable {P : Type u₂} {G : Type u₃} [Category.{v₂} P] [Category.{v₃} G]
  [Abelian A] [Abelian P] [Abelian G] [HasDerivedCategory P] [HasDerivedCategory G]
  (F : A ⥤ P) [F.Additive] (q : ℤ) {E₁ E₂ : P ⥤ G} [E₁.Additive] [E₂.Additive]
  [PreservesFiniteLimits E₁] [PreservesFiniteColimits E₁]
  [PreservesFiniteLimits E₂] [PreservesFiniteColimits E₂]

omit [HasDerivedCategory P] [HasDerivedCategory G] in
/-- On a complex, the comparison between `F.mapHomotopyCategory c ⋙ E.mapHomotopyCategory c`
and `(F ⋙ E).mapHomotopyCategory c` is the identity. -/
public theorem mapHomotopyCategoryCompIso_refl_app_quotient (E : P ⥤ G) [E.Additive]
    (K : HomologicalComplex A (ComplexShape.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ E)) (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) = 𝟙 _ := by
  have h1 : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ E))
      (ComplexShape.up ℤ)).hom.app K = 𝟙 _ :=
    congr_app (NatTrans.mapHomologicalComplex_id (ComplexShape.up ℤ) (F ⋙ E)) K
  have h2 : (HomotopyCategory.quotient G (ComplexShape.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ E))
        (ComplexShape.up ℤ)).hom.app K) = 𝟙 _ :=
    (congrArg (HomotopyCategory.quotient G (ComplexShape.up ℤ)).map h1).trans
      ((HomotopyCategory.quotient G (ComplexShape.up ℤ)).map_id _)
  exact h2

omit [HasDerivedCategory P] [HasDerivedCategory G] in
/-- The identification above, after applying the homology functor. -/
public theorem homologyFunctor_map_mapHomotopyCategoryCompIso_refl (E : P ⥤ G) [E.Additive]
    (K : HomologicalComplex A (ComplexShape.up ℤ)) :
    (HomotopyCategory.homologyFunctor G (ComplexShape.up ℤ) q).map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ E)) (ComplexShape.up ℤ)).hom.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) = 𝟙 _ := by
  rw [mapHomotopyCategoryCompIso_refl_app_quotient]
  exact (HomotopyCategory.homologyFunctor G (ComplexShape.up ℤ) q).map_id _

/-- The source comparison is natural in the exact functor. This is what upgrades an objectwise
identification of hypercohomology groups to an identification of presheaves. -/
public theorem derivedSourceIso_hom_naturality (ρ : E₁ ⟶ E₂) :
    Functor.whiskerLeft ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙
        DerivedCategory.homologyFunctor P q) ρ ≫ (derivedSourceIso F E₂ q).hom =
      (derivedSourceIso F E₁ q).hom ≫
        Functor.whiskerRight
          (NatTrans.mapHomotopyCategory (Functor.whiskerLeft F ρ) (ComplexShape.up ℤ))
          (DerivedCategory.Qh ⋙ DerivedCategory.homologyFunctor G q) := by
  ext I
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective I
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [derivedSourceIso_hom_app, derivedSourceIso_hom_app]
  refine four_squares
    (b := ρ.app ((HomotopyCategory.homologyFunctor P (ComplexShape.up ℤ) q).obj
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))))
    (c := (HomotopyCategory.homologyFunctor G (ComplexShape.up ℤ) q).map
      ((NatTrans.mapHomotopyCategory ρ (ComplexShape.up ℤ)).app
        ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))))
    (d := (HomotopyCategory.homologyFunctor G (ComplexShape.up ℤ) q).map
      ((NatTrans.mapHomotopyCategory (Functor.whiskerLeft F ρ) (ComplexShape.up ℤ)).app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)))
    ((ρ.naturality _).symm)
    (congr_app (homotopyHomologyIso_hom_naturality ρ q) _)
    ?_
    ((DerivedCategory.homologyFunctorFactorsh G q).inv.naturality _)
  rw [homologyFunctor_map_mapHomotopyCategoryCompIso_refl,
    homologyFunctor_map_mapHomotopyCategoryCompIso_refl]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

end SourceNaturality

section Identity

universe w₁

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]

/-- **The identity functor induces the identity functor on the unbounded derived category.**
`CategoryTheory.Functor.mapHomologicalComplexIdIso` lifted through the localization of the
category of cochain complexes at the quasi-isomorphisms. -/
public def mapDerivedCategoryIdIso : (𝟭 C₁).mapDerivedCategory ≅ 𝟭 (DerivedCategory C₁) :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    ((𝟭 C₁).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    DerivedCategory.Q (𝟭 C₁).mapDerivedCategory (𝟭 _)
    (Functor.isoWhiskerRight (Functor.mapHomologicalComplexIdIso C₁ (ComplexShape.up ℤ))
      DerivedCategory.Q ≪≫ Functor.leftUnitor _)

end Identity

end Stacks.Homology

end
