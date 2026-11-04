module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.Simple
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Triangulated
public import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived functors on bounded homotopy categories (Stacks 05T5)

This file formalizes [Stacks, Tag 05T5]: for an additive functor `F : A ⥤ B` of abelian
categories and `X` in `K⁺(A)`, the right derived functor of `K(A) ⥤ D(B)` is defined at `X` iff
that of `K⁺(A) ⥤ D⁺(B)` is, with canonically isomorphic values, and `X` computes the one iff it
computes the other; dually for `K⁻(A)` and left derived functors. "Defined at", the value and
"computes" are those of Tags 05S9 and 05SX.

## References

* [Stacks, Tag 05T5](https://stacks.math.columbia.edu/tag/05T5)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

This file formalizes Lemma 13.15.2 (Stacks Tag 05T5) in the setting of
Situation 13.15.1 (Stacks Tag 05T4): an additive functor `F : A ⥤ B` between
abelian categories induces exact functors on homotopy categories of cochain
complexes, and, after composing with the localization functors to the derived
categories, exact functors of triangulated categories

  `F : K(A) ⥤ D(B)`,  `F : K⁺(A) ⥤ D⁺(B)`,  `F : K⁻(A) ⥤ D⁻(B)`.

The lemma compares the right (resp. left) derived functor computed in the
"big" homotopy category `K(A)` with the one computed in the bounded-below
(resp. bounded-above) homotopy category `K⁺(A)` (resp. `K⁻(A)`).

## Abstract framework (Situation 13.14.1, Tag 05S8)

An exact functor `F : D ⥤ D'` of triangulated categories together with a
(saturated, triangulated-compatible) multiplicative system `S ⊆ Arrows(D)`.

* "Defined at", value and "computes" (Tags 05S9, 05SX) are
  `CategoryTheory.Functor.IsRightDerivedValueAt` and
  `CategoryTheory.Functor.ComputesRightDerived` (and their duals): a value of `RF` at `X` is a
  cocone on the ind-object `X/S ⥤ D'`, `(s : X → X') ↦ F(X')`, carrying the essential-constancy
  data of Tag 05PU, and `X` computes `RF` when some value has an invertible coprojection at
  `id_X`, the canonical map `F(X) → RF(X)`.  Dually for `LF` via `S/X`.
* The proof is the source's: `X/Qis⁺(A)` is cofinal in `X/Qis(A)` (Tag 05RV), which carries
  essential constancy back and forth (`plusComparison`, `minusComparison`).

## Notes on interpretation

* `K⁺(A)` is `HomotopyCategory.Plus A`; its inclusion into `K(A)` is
  `HomotopyCategory.Plus.ι A`. Tag 014X provides the bounded-above
  homotopy category `K⁻(A)`, mirroring `HomotopyCategory.Plus`
  (full subcategory of `K(A)` on the strictMap-image of strictly bounded-above
  cochain complexes).
* Mathlib does not provide `D⁺(B)`, `D⁻(B)`.  We define them as the genuine
  full triangulated subcategories of `D(B)` on the bounded-below (`IsGE`)
  resp. bounded-above (`IsLE`) objects, with their inclusions into `D(B)`, and
  we make the bounded functors `F⁺ : K⁺(A) ⥤ D⁺(B)` and `F⁻ : K⁻(A) ⥤ D⁻(B)`
  genuinely land in these subcategories (using that an additive `F` preserves
  boundedness).  "Defined at" for the bounded functors is therefore essential
  constancy *inside* `D⁺(B)` / `D⁻(B)`, as in the informal statement.
* The comparison of values is via the embeddings `D⁺(B) ↪ D(B)`,
  `D⁻(B) ↪ D(B)`: we exhibit an actual isomorphism between the big value and
  the image of the bounded value, compatible with the canonical maps.
-/

open CategoryTheory Limits

namespace StacksDerivedFunctorComparison

/-! ## The abstract framework of Situation 13.14.1 (Tag 05S8) -/

section Abstract

variable {D : Type*} [Category D] (S : MorphismProperty D)
variable {D' : Type*} [Category D'] (F : D ⥤ D')

/-- The comma category `X/S`: objects are arrows `s : X ⟶ X'` with `s ∈ S`,
realized as the full subcategory of `StructuredArrow X (𝟭 D)` on the arrows
lying in `S`.  By Tag 05S9 this category is filtered (assumed where needed). -/
abbrev UnderS (X : D) : Type _ :=
  ObjectProperty.FullSubcategory (fun (f : StructuredArrow X (𝟭 D)) => S f.hom)

/-- The comma category `S/X`: objects are arrows `s : X' ⟶ X` with `s ∈ S`,
realized as the full subcategory of `CostructuredArrow (𝟭 D) X` on the arrows
lying in `S`.  By Tag 05S9 this category is cofiltered (assumed where needed). -/
@[sga "4 I 8.7.5" "more general", sga "4 VI 6.5"]
abbrev OverS (X : D) : Type _ :=
  ObjectProperty.FullSubcategory (fun (f : CostructuredArrow (𝟭 D) X) => S f.hom)

/-! ### Comparison machinery across a functor `G : D ⥤ D₀`

The comparison of derived functors in `Lemma 13.15.2` is, abstractly, a
comparison of essentially-constant ind/pro-objects along the inclusion of one
comma category into another, induced by an inclusion functor `G : D ⥤ D₀`
(here `G = ι : K⁺(A) ⥤ K(A)` resp. `ι : K⁻(A) ⥤ K(A)`).  When the bounded
multiplicative system `S` is the inverse image `S₀.inverseImage G` of the big
system `S₀`, `G` sends `X/S` into `(G X)/S₀`, and the whole comparison is
governed by whether this comparison functor is *final* (resp. *initial*). -/

section Comparison

variable {D₀ : Type*} [Category D₀] (G : D ⥤ D₀)

/-- The functor `StructuredArrow X (𝟭 D) ⥤ StructuredArrow (G X) (𝟭 D₀)`
sending `(s : X ⟶ X')` to `(G s : G X ⟶ G X')`.  It is the action of `G` on
"objects under `X`". -/
noncomputable def saMap (X : D) :
    StructuredArrow X (𝟭 D) ⥤ StructuredArrow (G.obj X) (𝟭 D₀) where
  obj f := StructuredArrow.mk (Y := G.obj f.right) (G.map f.hom)
  map {f g} φ := StructuredArrow.homMk (G.map φ.right) (by
    have hw : f.hom ≫ φ.right = g.hom := by
      have h := StructuredArrow.w φ; simp only [Functor.id_map] at h; exact h
    simp only [Functor.id_obj, Functor.id_map, StructuredArrow.mk_hom_eq_self]
    exact (G.map_comp f.hom φ.right).symm.trans (congrArg G.map hw))
  map_id := by intro f; apply StructuredArrow.hom_ext; simp
  map_comp := by intro f g h φ ψ; apply StructuredArrow.hom_ext; simp

/-- Dually, `CostructuredArrow (𝟭 D) X ⥤ CostructuredArrow (𝟭 D₀) (G X)`,
the action of `G` on "objects over `X`". -/
noncomputable def caMap (X : D) :
    CostructuredArrow (𝟭 D) X ⥤ CostructuredArrow (𝟭 D₀) (G.obj X) where
  obj f := CostructuredArrow.mk (Y := G.obj f.left) (G.map f.hom)
  map {f g} φ := CostructuredArrow.homMk (G.map φ.left) (by
    have hw : φ.left ≫ g.hom = f.hom := by
      have h := CostructuredArrow.w φ; simp only [Functor.id_map] at h; exact h
    simp only [Functor.id_obj, Functor.id_map, CostructuredArrow.mk_hom_eq_self]
    exact (G.map_comp φ.left g.hom).symm.trans (congrArg G.map hw))
  map_id := by intro f; apply CostructuredArrow.hom_ext; simp
  map_comp := by intro f g h φ ψ; apply CostructuredArrow.hom_ext; simp

/-- The comparison functor `(X / S₀.inverseImage G) ⥤ ((G X) / S₀)` between the
"under" comma categories, induced by `G`.  An arrow `s : X ⟶ X'` whose `G`-image
lies in `S₀` is sent to `G s : G X ⟶ G X'`. -/
noncomputable def underCmp (S₀ : MorphismProperty D₀) (X : D) :
    UnderS (S₀.inverseImage G) X ⥤ UnderS S₀ (G.obj X) :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ saMap G X)
    (fun Y => by
      have hY : (S₀.inverseImage G) Y.1.hom := Y.2
      simpa [saMap, MorphismProperty.inverseImage] using hY)

/-- The comparison functor `(S₀.inverseImage G / X) ⥤ (S₀ / (G X))` between the
"over" comma categories, induced by `G`. -/
noncomputable def overCmp (S₀ : MorphismProperty D₀) (X : D) :
    OverS (S₀.inverseImage G) X ⥤ OverS S₀ (G.obj X) :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ caMap G X)
    (fun Y => by
      have hY : (S₀.inverseImage G) Y.1.hom := Y.2
      simpa [caMap, MorphismProperty.inverseImage] using hY)

/-- The comparison functor `X/(S₀.inverseImage G) ⥤ (G X)/S₀` on Mathlib's comma categories
`MorphismProperty.Under`, the index categories of Tag 05S9: an arrow `s : X ⟶ X'` whose `G`-image
lies in `S₀` is sent to `G s : G X ⟶ G X'`. -/
@[simps]
def underComparison (S₀ : MorphismProperty D₀) (X : D) :
    (S₀.inverseImage G).Under ⊤ X ⥤ S₀.Under ⊤ (G.obj X) where
  obj s := MorphismProperty.Under.mk ⊤ (G.map s.hom) s.prop
  map f := MorphismProperty.Under.homMk (G.map f.right)
    (by simp [← G.map_comp])

/-- The comparison functor `(S₀.inverseImage G)/X ⥤ S₀/(G X)` on Mathlib's comma categories
`MorphismProperty.Over`. -/
@[simps]
def overComparison (S₀ : MorphismProperty D₀) (X : D) :
    (S₀.inverseImage G).Over ⊤ X ⥤ S₀.Over ⊤ (G.obj X) where
  obj s := MorphismProperty.Over.mk ⊤ (G.map s.hom) s.prop
  map f := MorphismProperty.Over.homMk (G.map f.left)
    (by simp [← G.map_comp])

/-- If `G` is faithful, then so is `underComparison G S₀ X`. -/
instance [G.Faithful] (S₀ : MorphismProperty D₀) (X : D) : (underComparison G S₀ X).Faithful :=
  ⟨fun h => MorphismProperty.Under.Hom.ext (G.map_injective (congrArg (fun g => g.right) h))⟩

/-- If `G` is fully faithful, then `underComparison G S₀ X` is full. -/
instance [G.Full] [G.Faithful] (S₀ : MorphismProperty D₀) (X : D) :
    (underComparison G S₀ X).Full :=
  ⟨fun g => ⟨MorphismProperty.Under.homMk (G.preimage g.right)
    (G.map_injective (by rw [G.map_comp, G.map_preimage]; exact MorphismProperty.Under.w g)),
    MorphismProperty.Under.Hom.ext (by simp)⟩⟩

/-- If `G` is faithful, then so is `overComparison G S₀ X`. -/
instance [G.Faithful] (S₀ : MorphismProperty D₀) (X : D) : (overComparison G S₀ X).Faithful :=
  ⟨fun h => MorphismProperty.Over.Hom.ext (G.map_injective (congrArg (fun g => g.left) h))⟩

/-- If `G` is fully faithful, then `overComparison G S₀ X` is full. -/
instance [G.Full] [G.Faithful] (S₀ : MorphismProperty D₀) (X : D) :
    (overComparison G S₀ X).Full :=
  ⟨fun g => ⟨MorphismProperty.Over.homMk (G.preimage g.left)
    (G.map_injective (by rw [G.map_comp, G.map_preimage]; exact MorphismProperty.Over.w g)),
    MorphismProperty.Over.Hom.ext (by simp)⟩⟩

end Comparison


end Abstract

/-! ## Situation 13.15.1 (Tag 05T4): the concrete homotopy-category setting -/

section Concrete

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]

/-- `K(A)`, the homotopy category of cochain complexes in `A`. -/
@[ega "0 20.6.26",
  sga "4 XVII 2.2.8" "absolute case of K(A/B)",
  sga "4½ Etat_0 1.2.2" "special case",
  sga "6 I 1.1.5" "The fiber K(C_X)"]
abbrev Kbig (A : Type*) [Category A] [Abelian A] : Type _ :=
  HomotopyCategory A (ComplexShape.up ℤ)

/-- `Qis(A) ⊆ Arrows(K(A))`, the multiplicative system of quasi-isomorphisms. -/
abbrev qisBig (A : Type*) [Category A] [Abelian A] : MorphismProperty (Kbig A) :=
  HomotopyCategory.quasiIso A (ComplexShape.up ℤ)

/-- `Qis⁺(A) ⊆ Arrows(K⁺(A))`, the quasi-isomorphisms in `K⁺(A)`. -/
abbrev qisPlus (A : Type*) [Category A] [Abelian A] :
    MorphismProperty (HomotopyCategory.Plus A) :=
  HomotopyCategory.Plus.quasiIso A

/-- The "big" functor `F : K(A) ⥤ D(B)`, the induced functor on homotopy
categories composed with the localization `K(B) ⥤ D(B)`. -/
noncomputable abbrev Fbig : Kbig A ⥤ DerivedCategory B :=
  F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-! ### The bounded-below derived category `D⁺(B)` -/

/-- `D⁺(B)`: the full subcategory of `D(B)` on the bounded-below objects. -/
@[sga "4 Vbis 1.3.8", sga "4 Vbis 2.4.1", sga "4½ Rapport 4.1"]
def DplusProp (B : Type*) [Category B] [Abelian B] [HasDerivedCategory B] :
    ObjectProperty (DerivedCategory B) := fun Y => ∃ n, DerivedCategory.IsGE Y n

/-- `D⁺(B)`. -/
@[sga "4 Vbis 1.3.8",
  sga "4 Vbis 2.4.1",
  sga "4½ Etat_0 3.1.1",
  sga "4½ Etat_0 3.1.2",
  sga "4½ Etat_0 3.1.3",
  sga "4½ Rapport 4.1",
  sga "6 I 1.1.5" "partial"]
abbrev Dplus (B : Type*) [Category B] [Abelian B] [HasDerivedCategory B] : Type _ :=
  (DplusProp B).FullSubcategory

/-- The embedding `D⁺(B) ↪ D(B)`. -/
@[sga "4½ Etat_0 3.1.2"]
noncomputable def Dplus.ι (B : Type*) [Category B] [Abelian B] [HasDerivedCategory B] :
    Dplus B ⥤ DerivedCategory B := (DplusProp B).ι

/-- A quasi-isomorphism of `K(A)` preserves exactness of the underlying complexes at `i`. -/
private lemma exactAt_iff_of_quasiIso_homotopyCategory {K L : Kbig A} (s : K ⟶ L)
    (hs : qisBig A s) (i : ℤ) : K.as.ExactAt i ↔ L.as.ExactAt i := by
  have := (HomotopyCategory.mem_quasiIso_iff s).mp hs i
  have e := HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) i
  rw [HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((e.app K.as).isZero_iff.symm.trans
    (asIso ((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) i).map s)).isZero_iff).trans
    (e.app L.as).isZero_iff

/-- An object of `K⁺(A)` is strictly bounded below by some `n`. -/
private lemma exists_isStrictlyGE (X : HomotopyCategory.Plus A) :
    ∃ n, CochainComplex.IsStrictlyGE X.obj.as n := by
  have hX : (CochainComplex.plus A).strictMap
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)) X.obj := X.property
  rw [ObjectProperty.strictMap_iff] at hX
  obtain ⟨K, ⟨n, hn⟩, hKeq⟩ := hX
  exact ⟨n, by rw [← hKeq]; exact hn⟩

/-- An additive functor sends a bounded-below object of `K⁺(A)` to a
bounded-below object of `D(B)`. -/
theorem Fbig_obj_mem_Dplus (X : HomotopyCategory.Plus A) :
    DplusProp B ((Fbig F).obj ((HomotopyCategory.Plus.ι A).obj X)) := by
  obtain ⟨n, hbound⟩ := exists_isStrictlyGE X
  refine ⟨n, ?_⟩
  have hF : CochainComplex.IsStrictlyGE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X.obj.as) n := by
    rw [CochainComplex.isStrictlyGE_iff] at hbound ⊢
    intro i hi
    exact F.map_isZero (hbound i hi)
  -- `(Fbig F).obj (ι X) = Qh (quotient (F X.obj.as))`, which Mathlib's
  -- `DerivedCategory.quotientCompQhIso` identifies with `Q (F X.obj.as)`; the latter is
  -- bounded below because `F X.obj.as` is strictly bounded below (`hF`).
  have hQ : (DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X.obj.as)).IsGE n := inferInstance
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((DerivedCategory.quotientCompQhIso B).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X.obj.as)).symm n

/-- The bounded-below functor `F⁺ : K⁺(A) ⥤ D⁺(B)`. -/
noncomputable def Fplus : HomotopyCategory.Plus A ⥤ Dplus B :=
  ObjectProperty.lift (DplusProp B) (HomotopyCategory.Plus.ι A ⋙ Fbig F) (Fbig_obj_mem_Dplus F)

/-- `F⁺` followed by the embedding into `D(B)` is `ι ⋙ Fbig`. -/
theorem Fplus_comp_ι : Fplus F ⋙ Dplus.ι B = HomotopyCategory.Plus.ι A ⋙ Fbig F := rfl

/-! ### The bounded-above homotopy category `K⁻(A)` and derived category `D⁻(B)`

Tag 014X provides the bounded-above analogue of `HomotopyCategory.Plus`;
the names below preserve this file's established comparison API. -/

/-- Bounded-above cochain complexes. -/
@[ega "0 11.2.1", sga "4½ Etat_0 1.2.3"]
def cochainMinus (A : Type*) [Category A] [Abelian A] : ObjectProperty (CochainComplex A ℤ) :=
  CochainComplex.minus A

/-- Bounded-above object property on `K(A)`, mirroring `HomotopyCategory.plus`. -/
@[sga "4 XVII 2.2.10" "partial", sga "4½ Etat_0 1.2.3"]
def homotopyMinus (A : Type*) [Category A] [Abelian A] : ObjectProperty (Kbig A) :=
  HomotopyCategory.minus A

/-- `K⁻(A)`, the bounded-above homotopy category. -/
@[sga "4 XVII 2.2.10" "special case", sga "4½ Etat_0 1.2.3", sga "6 I 1.1.5" "The fiber K^-(C_X)"]
abbrev KMinus (A : Type*) [Category A] [Abelian A] : Type _ :=
  HomotopyCategory.Minus A

/-- The inclusion `ι : K⁻(A) ⥤ K(A)`. -/
@[sga "4½ Etat_0 1.2.3", sga "6 I 1.1.5" "partial"]
noncomputable def KMinus.ι (A : Type*) [Category A] [Abelian A] :
    KMinus A ⥤ Kbig A := HomotopyCategory.Minus.ι A

/-- `Qis⁻(A) ⊆ Arrows(K⁻(A))`, the quasi-isomorphisms in `K⁻(A)`, obtained as
the inverse image of `Qis(A)` along the inclusion. -/
def qisMinus (A : Type*) [Category A] [Abelian A] : MorphismProperty (KMinus A) :=
  (qisBig A).inverseImage (KMinus.ι A)

/-- Every identity morphism of `K⁻(A)` is a quasi-isomorphism. -/
instance (A : Type*) [Category A] [Abelian A] : (qisMinus A).ContainsIdentities := by
  unfold qisMinus; infer_instance

/-- The quasi-isomorphisms in `K⁻(A)` contain the identities and are closed under composition. -/
instance (A : Type*) [Category A] [Abelian A] : (qisMinus A).IsMultiplicative := by
  unfold qisMinus; infer_instance

/-- `D⁻(B)`: the full subcategory of `D(B)` on the bounded-above objects. -/
@[sga "4½ Etat_0 3.1.3", sga "4½ Rapport 4.1", sga "6 I 1.1.5" "partial"]
def DminusProp (B : Type*) [Category B] [Abelian B] [HasDerivedCategory B] :
    ObjectProperty (DerivedCategory B) := fun Y => ∃ n, DerivedCategory.IsLE Y n

/-- `D⁻(B)`. -/
@[sga "4½ Etat_0 3.1.2", sga "4½ Etat_0 3.1.3", sga "4½ Rapport 4.1", sga "6 I 1.1.5" "partial"]
abbrev Dminus (B : Type*) [Category B] [Abelian B] [HasDerivedCategory B] : Type _ :=
  (DminusProp B).FullSubcategory

/-- The embedding `D⁻(B) ↪ D(B)`. -/
@[sga "4½ Etat_0 3.1.2"]
noncomputable def Dminus.ι (B : Type*) [Category B] [Abelian B] [HasDerivedCategory B] :
    Dminus B ⥤ DerivedCategory B := (DminusProp B).ι

/-- An object of `K⁻(A)` is strictly bounded above by some `n`. -/
private lemma exists_isStrictlyLE (X : KMinus A) :
    ∃ n, CochainComplex.IsStrictlyLE X.obj.as n := by
  have hX : (cochainMinus A).strictMap
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)) X.obj := X.property
  rw [ObjectProperty.strictMap_iff] at hX
  obtain ⟨K, ⟨n, hn⟩, hKeq⟩ := hX
  exact ⟨n, by rw [← hKeq]; exact hn⟩

/-- An additive functor sends a bounded-above object of `K⁻(A)` to a
bounded-above object of `D(B)`. -/
theorem Fbig_obj_mem_Dminus (X : KMinus A) :
    DminusProp B ((Fbig F).obj ((KMinus.ι A).obj X)) := by
  obtain ⟨n, hbound⟩ := exists_isStrictlyLE X
  refine ⟨n, ?_⟩
  have hF : CochainComplex.IsStrictlyLE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X.obj.as) n := by
    rw [CochainComplex.isStrictlyLE_iff] at hbound ⊢
    intro i hi
    exact F.map_isZero (hbound i hi)
  -- Dual of `Fbig_obj_mem_Dplus`: transport `IsLE` along `DerivedCategory.quotientCompQhIso`.
  have hQ : (DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X.obj.as)).IsLE n := inferInstance
  exact DerivedCategory.TStructure.t.isLE_of_iso
    ((DerivedCategory.quotientCompQhIso B).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X.obj.as)).symm n

/-- The bounded-above functor `F⁻ : K⁻(A) ⥤ D⁻(B)`. -/
noncomputable def Fminus : KMinus A ⥤ Dminus B :=
  ObjectProperty.lift (DminusProp B) (KMinus.ι A ⋙ Fbig F) (Fbig_obj_mem_Dminus F)

/-- `F⁻` followed by the embedding into `D(B)` is `ι ⋙ Fbig`. -/
theorem Fminus_comp_ι : Fminus F ⋙ Dminus.ι B = KMinus.ι A ⋙ Fbig F := rfl

/-! ## Main Statements: Lemma 13.15.2 (Tag 05T5)

### The cofinality core (Stacks Tag 05RV)

The mathematical heart of `Lemma 13.15.2` is that, for `X` bounded below, the
comma category `X/Qis⁺(A)` is *cofinal* in `X/Qis(A)`; dually, for `X` bounded
above, `Qis⁻(A)/X` is *coinitial* in `Qis(A)/X`.  Everything else is formal
transfer of essential constancy along these (co)final inclusions. -/

/-! **Cofinality (Tag 05RV / 05T5).**  The comparison functor
`underCmp ι (qisBig A) X : (X / Qis⁺(A)) ⥤ (ιX / Qis(A))` is final, for `X`
bounded below.

Argument (Stacks 05T5 ⟸ 05RV(1)): an object of `ιX / Qis(A)` is a quasi-iso
`s : ιX ⟶ Y` in `K(A)`.  Since `X` is bounded below, `H^n(X) = 0` for `n ≪ 0`,
and `s` a quasi-iso forces `H^n(Y) = 0` for `n ≪ 0` too.  By Lemma 13.11.5(1)
(Tag 05RV) the canonical truncation `Y → τ^{≥n} Y` is a quasi-isomorphism with
`τ^{≥n} Y` bounded below, providing a quasi-iso `s' : ιX ⟶ τ^{≥n}Y = ι Y'` with
`Y'` in `K⁺(A)`, factoring through `s`.  Thus every comma object receives a map
from one in the image of `underCmp`. Since the comparison is fully faithful and `ιX/Qis(A)` is
filtered, this already makes it final (`plusComparison_final`). -/
/-- **Finality, nonemptiness half (R/+).**  Every object `d` of `ιX/Qis(A)` (a
quasi-iso `s : ιX ⟶ Y` in `K(A)`) receives a morphism from an object in the image
of `underCmp`.  ANALYTIC (Tag 05RV(1)): `Y` has cohomology bounded below (because
`X` is strictly bounded below and `s` is a quasi-iso), so the canonical truncation
`Y → τ^{≥n}Y` is a quasi-iso into a bounded-below `τ^{≥n}Y ∈ K⁺(A)`, and
`ιX → Y → τ^{≥n}Y` is the required comma object in the image.  Key Mathlib API:
`CochainComplex.πTruncGE`, `CochainComplex.quasiIso_πTruncGE_iff`,
`HomotopyCategory.quotient_map_mem_quasiIso_iff`, `HomotopyCategory.Plus.quasiIso_iff`. -/
theorem underComparisonPlus_final_nonempty (X : HomotopyCategory.Plus A)
    (d : UnderS (qisBig A) ((HomotopyCategory.Plus.ι A).obj X)) :
    ∃ c, Nonempty (d ⟶ (underCmp (HomotopyCategory.Plus.ι A) (qisBig A) X).obj c) := by
  -- Underlying data: `s : ιX ⟶ Y` a quasi-iso in `K(A)`.
  set Y : Kbig A := d.1.right with hY_def
  set s : (HomotopyCategory.Plus.ι A).obj X ⟶ Y := d.1.hom with hs_def
  have hs : qisBig A s := d.2
  -- `X` is strictly bounded below by some `n₀`.
  obtain ⟨n₀, hn₀⟩ := exists_isStrictlyGE X
  -- Transport `IsGE n₀` from `ιX = X.obj` to `Y` along the quasi-iso `s`.
  have hYGE : CochainComplex.IsGE Y.as n₀ := by
    have hXGE : CochainComplex.IsGE (X.obj.as) n₀ := inferInstance
    rw [CochainComplex.isGE_iff] at hXGE ⊢
    exact fun i hi => (exactAt_iff_of_quasiIso_homotopyCategory s hs i).1 (hXGE i hi)
  -- The bounded-below object `Yp ∈ K⁺(A)` from the truncation.
  set Yp : HomotopyCategory.Plus A :=
    ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (CochainComplex.truncGE Y.as n₀), by
      show (CochainComplex.plus A).strictMap
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)) _
      rw [ObjectProperty.strictMap_iff]
      exact ⟨CochainComplex.truncGE Y.as n₀, ⟨n₀, inferInstance⟩, rfl⟩⟩ with hYp_def
  -- The truncation map `g : Y ⟶ Yp.obj`, a quasi-iso.
  set g : Y ⟶ Yp.obj :=
    (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (CochainComplex.πTruncGE Y.as n₀)
    with hg_def
  have hgqis : qisBig A g := by
    show HomotopyCategory.quasiIso A (ComplexShape.up ℤ) g
    rw [hg_def, HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff, CochainComplex.quasiIso_πTruncGE_iff]
    exact hYGE
  -- The comma object `c` in the image, and the morphism `d ⟶ underCmp.obj c`.
  refine ⟨⟨StructuredArrow.mk (Y := Yp) (ObjectProperty.homMk (s ≫ g)), ?_⟩, ⟨?_⟩⟩
  · -- membership of `s'` in `(qisBig A).inverseImage (Plus.ι A)`
    show qisBig A ((HomotopyCategory.Plus.ι A).map (ObjectProperty.homMk (s ≫ g)))
    have hmap : (HomotopyCategory.Plus.ι A).map (ObjectProperty.homMk (s ≫ g) : X ⟶ Yp) = s ≫ g :=
      rfl
    rw [hmap]
    exact MorphismProperty.comp_mem _ _ _ hs hgqis
  · -- the morphism `d ⟶ underCmp.obj c`
    refine ObjectProperty.homMk (StructuredArrow.homMk (f := d.1) g ?_)
    show s ≫ g = (HomotopyCategory.Plus.ι A).map (ObjectProperty.homMk (s ≫ g) : X ⟶ Yp)
    rfl

/-- **Coinitiality, nonemptiness half (L/−), dual.**  Every object `d` of
`Qis(A)/ιX` (a quasi-iso `s : Y ⟶ ιX` in `K(A)`) receives a morphism from an
object in the image of `overCmp`.  Dual to `underComparisonPlus_final_nonempty`,
using the bounded-above truncation `τ^{≤n}`. -/
theorem overComparisonMinus_initial_nonempty (X : KMinus A)
    (d : OverS (qisBig A) ((KMinus.ι A).obj X)) :
    ∃ c, Nonempty ((overCmp (KMinus.ι A) (qisBig A) X).obj c ⟶ d) := by
  -- Underlying data: `s : Y ⟶ ιX` a quasi-iso in `K(A)`.
  set Y : Kbig A := d.1.left with hY_def
  set s : Y ⟶ (KMinus.ι A).obj X := d.1.hom with hs_def
  have hs : qisBig A s := d.2
  -- `X` is strictly bounded above by some `n₀`.
  obtain ⟨n₀, hn₀⟩ := exists_isStrictlyLE X
  -- Transport `IsLE n₀` from `ιX = X.obj` to `Y` along the quasi-iso `s`.
  have hYLE : CochainComplex.IsLE Y.as n₀ := by
    have hXLE : CochainComplex.IsLE (X.obj.as) n₀ := inferInstance
    rw [CochainComplex.isLE_iff] at hXLE ⊢
    exact fun i hi => (exactAt_iff_of_quasiIso_homotopyCategory s hs i).2 (hXLE i hi)
  -- The bounded-above object `Yp ∈ K⁻(A)` from the truncation.
  set Yp : KMinus A :=
    ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (CochainComplex.truncLE Y.as n₀), by
      show (cochainMinus A).strictMap
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)) _
      rw [ObjectProperty.strictMap_iff]
      exact ⟨CochainComplex.truncLE Y.as n₀, ⟨n₀, inferInstance⟩, rfl⟩⟩ with hYp_def
  -- The truncation map `g : Yp.obj ⟶ Y`, a quasi-iso.
  set g : (KMinus.ι A).obj Yp ⟶ Y :=
    (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (CochainComplex.ιTruncLE Y.as n₀)
    with hg_def
  have hgqis : qisBig A g := by
    show HomotopyCategory.quasiIso A (ComplexShape.up ℤ) g
    rw [hg_def, HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff, CochainComplex.quasiIso_ιTruncLE_iff]
    exact hYLE
  -- The comma object `c` in the image, and the morphism `overCmp.obj c ⟶ d`.
  refine ⟨⟨CostructuredArrow.mk (Y := Yp) (ObjectProperty.homMk (g ≫ s) : Yp ⟶ X), ?_⟩, ⟨?_⟩⟩
  · -- membership of `s'` in `(qisBig A).inverseImage (KMinus.ι A)`
    show qisBig A ((KMinus.ι A).map (ObjectProperty.homMk (g ≫ s) : Yp ⟶ X))
    have hmap : (KMinus.ι A).map (ObjectProperty.homMk (g ≫ s) : Yp ⟶ X) = g ≫ s :=
      rfl
    rw [hmap]
    exact MorphismProperty.comp_mem _ _ _ hgqis hs
  · -- the morphism `overCmp.obj c ⟶ d`
    refine ObjectProperty.homMk (CostructuredArrow.homMk (f' := d.1) g ?_)
    show g ≫ s = (KMinus.ι A).map (ObjectProperty.homMk (g ≫ s) : Yp ⟶ X)
    rfl

/-! ### The comparison on the index categories of Tag 05S9

`plusComparison X : X/Qis⁺(A) ⥤ ιX/Qis(A)` and `minusComparison X : Qis⁻(A)/X ⥤ Qis(A)/ιX` are
the comparison functors on Mathlib's comma categories, the index categories of the values of
Tag 05S9. They are fully faithful (the inclusions `K^±(A) ↪ K(A)` are), every object of the target
receives a map from, resp. maps to, an object of the image (the cofinality of Tag 05RV), and the
big ind-object, resp. pro-object, restricted along them is the bounded one followed by the
embedding `D^±(B) ↪ D(B)`, on the nose. -/

/-- The comparison functor `X/Qis⁺(A) ⥤ ιX/Qis(A)`. -/
noncomputable abbrev plusComparison (X : HomotopyCategory.Plus A) :
    (qisPlus A).Under ⊤ X ⥤ (qisBig A).Under ⊤ ((HomotopyCategory.Plus.ι A).obj X) :=
  underComparison (HomotopyCategory.Plus.ι A) (qisBig A) X

/-- The comparison functor `Qis⁻(A)/X ⥤ Qis(A)/ιX`. -/
noncomputable abbrev minusComparison (X : KMinus A) :
    (qisMinus A).Over ⊤ X ⥤ (qisBig A).Over ⊤ ((KMinus.ι A).obj X) :=
  overComparison (KMinus.ι A) (qisBig A) X

/-- The functor `plusComparison X` is full. -/
instance (X : HomotopyCategory.Plus A) : (plusComparison X).Full :=
  inferInstanceAs (underComparison (HomotopyCategory.Plus.ι A) (qisBig A) X).Full

/-- The functor `plusComparison X` is faithful. -/
instance (X : HomotopyCategory.Plus A) : (plusComparison X).Faithful :=
  inferInstanceAs (underComparison (HomotopyCategory.Plus.ι A) (qisBig A) X).Faithful

/-- The inclusion `K⁻(A) ⥤ K(A)` is full. -/
instance : (KMinus.ι A).Full := inferInstanceAs (HomotopyCategory.Minus.ι A).Full

/-- The inclusion `K⁻(A) ⥤ K(A)` is faithful. -/
instance : (KMinus.ι A).Faithful := inferInstanceAs (HomotopyCategory.Minus.ι A).Faithful

/-- The functor `minusComparison X` is full. -/
instance (X : KMinus A) : (minusComparison X).Full :=
  inferInstanceAs (overComparison (KMinus.ι A) (qisBig A) X).Full

/-- The functor `minusComparison X` is faithful. -/
instance (X : KMinus A) : (minusComparison X).Faithful :=
  inferInstanceAs (overComparison (KMinus.ι A) (qisBig A) X).Faithful

omit [HasDerivedCategory B] in
/-- **Cofinality (Tag 05RV(1)).** Every object of `ιX/Qis(A)` maps to an object in the image of
`plusComparison X`. -/
theorem plusComparison_dominated (X : HomotopyCategory.Plus A)
    (d : (qisBig A).Under ⊤ ((HomotopyCategory.Plus.ι A).obj X)) :
    ∃ c, Nonempty (d ⟶ (plusComparison X).obj c) := by
  obtain ⟨c, ⟨f⟩⟩ :=
    underComparisonPlus_final_nonempty (A := A) X ⟨StructuredArrow.mk d.hom, d.prop⟩
  exact ⟨MorphismProperty.Under.mk ⊤ c.obj.hom c.property,
    ⟨MorphismProperty.Under.homMk f.hom.right (StructuredArrow.w f.hom)⟩⟩

omit [HasDerivedCategory B] in
/-- **Coinitiality (Tag 05RV(2)).** Every object of `Qis(A)/ιX` receives a map from an object in
the image of `minusComparison X`. -/
theorem minusComparison_dominated (X : KMinus A)
    (d : (qisBig A).Over ⊤ ((KMinus.ι A).obj X)) :
    ∃ c, Nonempty ((minusComparison X).obj c ⟶ d) := by
  obtain ⟨c, ⟨f⟩⟩ := overComparisonMinus_initial_nonempty (A := A) X
    ⟨CostructuredArrow.mk d.hom, d.prop⟩
  exact ⟨MorphismProperty.Over.mk ⊤ c.obj.hom c.property,
    ⟨MorphismProperty.Over.homMk f.hom.left (CostructuredArrow.w f.hom)⟩⟩

omit [HasDerivedCategory B] in
/-- The comparison functor `plusComparison X : X/Qis⁺(A) ⥤ ιX/Qis(A)` is final. -/
theorem plusComparison_final (X : HomotopyCategory.Plus A) : (plusComparison X).Final :=
  Functor.final_of_exists_of_isFiltered_of_fullyFaithful _ (plusComparison_dominated X)

omit [HasDerivedCategory B] in
/-- The comparison functor `minusComparison X : Qis⁻(A)/X ⥤ Qis(A)/ιX` is initial. -/
theorem minusComparison_initial (X : KMinus A) : (minusComparison X).Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _ (minusComparison_dominated X)

/-- A retract of a bounded below object of `D(B)` is bounded below. -/
private lemma dplusProp_of_retract {Y Z : DerivedCategory B} (i : Y ⟶ Z) (p : Z ⟶ Y)
    (hip : i ≫ p = 𝟙 Y) (hZ : DplusProp B Z) : DplusProp B Y := by
  obtain ⟨n, hn⟩ := hZ
  refine ⟨n, (DerivedCategory.isGE_iff Y n).2 fun j hj => ?_⟩
  rw [IsZero.iff_id_eq_zero, ← (DerivedCategory.homologyFunctor B j).map_id, ← hip,
    Functor.map_comp, (DerivedCategory.isZero_of_isGE Z n j hj).eq_of_tgt
      ((DerivedCategory.homologyFunctor B j).map i) 0, zero_comp]

/-- A retract of a bounded above object of `D(B)` is bounded above. -/
private lemma dminusProp_of_retract {Y Z : DerivedCategory B} (i : Y ⟶ Z) (p : Z ⟶ Y)
    (hip : i ≫ p = 𝟙 Y) (hZ : DminusProp B Z) : DminusProp B Y := by
  obtain ⟨n, hn⟩ := hZ
  refine ⟨n, (DerivedCategory.isLE_iff Y n).2 fun j hj => ?_⟩
  rw [IsZero.iff_id_eq_zero, ← (DerivedCategory.homologyFunctor B j).map_id, ← hip,
    Functor.map_comp, (DerivedCategory.isZero_of_isLE Z n j hj).eq_of_tgt
      ((DerivedCategory.homologyFunctor B j).map i) 0, zero_comp]

/-! ### Lemma 13.15.2 (Tag 05T5)

"Defined at", the value and "computes" are those of Tags 05S9 and 05SX
(`CategoryTheory.Functor.IsRightDerivedValueAt`, `CategoryTheory.Functor.ComputesRightDerived`
and their duals), for `F : K(A) ⥤ D(B)` relative to `Qis(A)`, `F⁺ : K⁺(A) ⥤ D⁺(B)` relative to
`Qis⁺(A)` and `F⁻ : K⁻(A) ⥤ D⁻(B)` relative to `Qis⁻(A)`. As in the source, everything follows
from the cofinality of `X/Qis⁺(A)` in `ιX/Qis(A)`: an essentially constant ind-object restricts to
an essentially constant ind-object along the fully faithful cofinal `plusComparison X` and extends
back along it, a value of the bounded ind-object is carried to `D(B)` by the fully faithful
embedding `D⁺(B) ↪ D(B)`, and conversely a value in `D(B)` of the restricted ind-object lies in
`D⁺(B)`, being a retract of a bounded below object. -/

/-- **Statement (1), "defined at".** For `X` an object of `K⁺(A)`, the right derived functor of
`F : K(A) ⥤ D(B)` is defined at `X` (viewed in `K(A)` via `ι`) if and only if the right derived
functor of `F⁺ : K⁺(A) ⥤ D⁺(B)` is defined at `X`. -/
@[stacks 05T5 "(1)", sga "4 XVII 1.2.4" "Definedness clause"]
theorem definedAtR_big_iff_plus (X : HomotopyCategory.Plus A) :
    (∃ c, (Fbig F).IsRightDerivedValueAt (qisBig A) ((HomotopyCategory.Plus.ι A).obj X) c) ↔
      ∃ c, (Fplus F).IsRightDerivedValueAt (qisPlus A) X c := by
  rw [Functor.exists_isRightDerivedValueAt_iff, Functor.exists_isRightDerivedValueAt_iff]
  have hdom := plusComparison_dominated (A := A) X
  constructor
  · rintro ⟨c, i, r, h⟩
    -- restrict along the cofinal `plusComparison X`; the value is a retract of a bounded below
    -- object, hence lies in `D⁺(B)`
    obtain ⟨a, r', h'⟩ := h.exists_whisker (plusComparison X) hdom
    have hmem : DplusProp B c.pt :=
      dplusProp_of_retract r' _ h'.retraction (Fbig_obj_mem_Dplus F a.right)
    exact EssentiallyConstantInd.IsEssentiallyConstantInd.of_comp_fullyFaithful
      (G := Dplus.ι B) (ObjectProperty.fullyFaithfulι _) h' (Y := ⟨c.pt, hmem⟩) (Iso.refl _)
  · rintro ⟨c, i, r, h⟩
    -- carry the value to `D(B)` and extend it along the final `plusComparison X`
    have := plusComparison_final (A := A) X
    let c' : Cocone (plusComparison X ⋙ MorphismProperty.Under.forget (qisBig A) ⊤ _ ⋙
      Under.forget _ ⋙ Fbig F) := (Dplus.ι B).mapCocone c
    let e : c' ≅ ((Functor.Final.extendCocone (F := plusComparison X)).obj c').whisker
        (plusComparison X) :=
      Cocone.ext (Iso.refl _) fun j => by
        rw [Cocone.whisker_ι, Functor.whiskerLeft_app,
          Functor.Final.extendCocone_obj_ι_app' c' (𝟙 ((plusComparison X).obj j))]
        simp
    have hE : EssentiallyConstantInd.IsEssentiallyConstantWith (plusComparison X ⋙
        MorphismProperty.Under.forget (qisBig A) ⊤ _ ⋙ Under.forget _ ⋙ Fbig F) c' i
        ((Dplus.ι B).map r) := h.map (Dplus.ι B)
    exact ⟨_, _, _, (hE.of_iso e).of_whisker _ hdom⟩

/-- **Statement (1), values.** When the right derived functors of `F : K(A) ⥤ D(B)` and of
`F⁺ : K⁺(A) ⥤ D⁺(B)` are defined at `X`, with values `cbig.pt` and `cplus.pt`, the values are
canonically isomorphic in `D(B)` via the embedding `D⁺(B) ↪ D(B)`: there is an isomorphism
`RF(X) ≅ ι(RF⁺(X))` compatible with the structure maps `F(X') ⟶ RF(X)` and `F⁺(X') ⟶ RF⁺(X)` of
every `s : X ⟶ X'` in `Qis⁺(A)`, in particular with the canonical maps at `𝟙 X`. -/
@[stacks 05T5 "(1), values", sga "4 XVII 1.2.4" "Value clause", sga "4½ Etat_0 4.2.3.2" "(A)"]
theorem valueR_big_iso_plus (X : HomotopyCategory.Plus A)
    {cbig : Cocone (MorphismProperty.Under.forget (qisBig A) ⊤ ((HomotopyCategory.Plus.ι A).obj X) ⋙
      Under.forget _ ⋙ Fbig F)}
    (hbig : (Fbig F).IsRightDerivedValueAt (qisBig A) ((HomotopyCategory.Plus.ι A).obj X) cbig)
    {cplus : Cocone (MorphismProperty.Under.forget (qisPlus A) ⊤ X ⋙ Under.forget X ⋙ Fplus F)}
    (hplus : (Fplus F).IsRightDerivedValueAt (qisPlus A) X cplus) :
    ∃ e : cbig.pt ≅ (Dplus.ι B).obj cplus.pt,
      ∀ s : (qisPlus A).Under ⊤ X,
        cbig.ι.app (MorphismProperty.Under.mk ⊤ ((HomotopyCategory.Plus.ι A).map s.hom) s.prop) ≫
          e.hom = (Dplus.ι B).map (cplus.ι.app s) := by
  have := plusComparison_final (A := A) X
  obtain ⟨i, r, h⟩ := (Functor.isRightDerivedValueAt_iff _ _ _ _).1 hplus
  -- both cocones are colimits of `plusComparison X ⋙ (big ind-object) = (bounded ind-object) ⋙ ι`
  have colBig : IsColimit (cbig.whisker (plusComparison X)) :=
    (Functor.Final.isColimitWhiskerEquiv _ cbig).symm hbig.isColimit
  have colPlus : IsColimit ((Dplus.ι B).mapCocone cplus) := (h.map (Dplus.ι B)).isColimit
  exact ⟨colBig.coconePointUniqueUpToIso colPlus,
    fun s => colBig.comp_coconePointUniqueUpToIso_hom colPlus s⟩

/-- **Statement (2).** For `X` an object of `K⁺(A)`, `X` computes the right derived functor of
`F : K(A) ⥤ D(B)` (viewed in `K(A)`) if and only if `X` computes the right derived functor of
`F⁺ : K⁺(A) ⥤ D⁺(B)`. -/
@[stacks 05T5 "(2)"]
theorem computesR_big_iff_plus (X : HomotopyCategory.Plus A) :
    (Fbig F).ComputesRightDerived (qisBig A) ((HomotopyCategory.Plus.ι A).obj X) ↔
      (Fplus F).ComputesRightDerived (qisPlus A) X := by
  -- The "defined at" parts agree by (1); the compatibility of (1, values) at `s = 𝟙 X` identifies
  -- the two canonical maps up to the isomorphism of values and the fully faithful `D⁺(B) ↪ D(B)`.
  have : (Dplus.ι B).Full := (ObjectProperty.fullyFaithfulι _).full
  have : (Dplus.ι B).Faithful := (ObjectProperty.fullyFaithfulι _).faithful
  constructor
  · rintro ⟨cbig, hbig, hiso⟩
    obtain ⟨cplus, hplus⟩ := (definedAtR_big_iff_plus F X).1 ⟨cbig, hbig⟩
    obtain ⟨e, he⟩ := valueR_big_iso_plus F X hbig hplus
    refine ⟨cplus, hplus, ?_⟩
    have : IsIso ((Dplus.ι B).map
        (cplus.ι.app (MorphismProperty.Under.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X)))) := by
      rw [← he (MorphismProperty.Under.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X))]
      exact IsIso.comp_isIso' hiso inferInstance
    exact isIso_of_fully_faithful (Dplus.ι B) _
  · rintro ⟨cplus, hplus, hiso⟩
    obtain ⟨cbig, hbig⟩ := (definedAtR_big_iff_plus F X).2 ⟨cplus, hplus⟩
    obtain ⟨e, he⟩ := valueR_big_iso_plus F X hbig hplus
    refine ⟨cbig, hbig, ?_⟩
    have h := he (MorphismProperty.Under.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X))
    rw [← Iso.eq_comp_inv] at h
    have key : IsIso ((Dplus.ι B).map
        (cplus.ι.app (MorphismProperty.Under.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X))) ≫
          e.inv) := inferInstance
    rwa [← h] at key

/-- **Statement (3), "defined at".** For `X` an object of `K⁻(A)`, the left derived functor of
`F : K(A) ⥤ D(B)` is defined at `X` (viewed in `K(A)` via `ι`) if and only if the left derived
functor of `F⁻ : K⁻(A) ⥤ D⁻(B)` is defined at `X`. -/
@[stacks 05T5 "(3)", sga "4 XVII 1.2.5" "(iv), single functor"]
theorem definedAtL_big_iff_minus (X : KMinus A) :
    (∃ c, (Fbig F).IsLeftDerivedValueAt (qisBig A) ((KMinus.ι A).obj X) c) ↔
      ∃ c, (Fminus F).IsLeftDerivedValueAt (qisMinus A) X c := by
  rw [Functor.exists_isLeftDerivedValueAt_iff, Functor.exists_isLeftDerivedValueAt_iff]
  have hdom := minusComparison_dominated (A := A) X
  constructor
  · rintro ⟨c, i, r, h⟩
    obtain ⟨a, r', h'⟩ := h.exists_whisker (minusComparison X) hdom
    have hmem : DminusProp B c.pt :=
      dminusProp_of_retract _ r' h'.retraction (Fbig_obj_mem_Dminus F a.left)
    exact EssentiallyConstantPro.IsEssentiallyConstantPro.of_comp_fullyFaithful
      (G := Dminus.ι B) (ObjectProperty.fullyFaithfulι _) h' (Y := ⟨c.pt, hmem⟩) (Iso.refl _)
  · rintro ⟨c, i, r, h⟩
    have := minusComparison_initial (A := A) X
    let c' : Cone (minusComparison X ⋙ MorphismProperty.Over.forget (qisBig A) ⊤ _ ⋙
      Over.forget _ ⋙ Fbig F) := (Dminus.ι B).mapCone c
    let e : c' ≅ ((Functor.Initial.extendCone (F := minusComparison X)).obj c').whisker
        (minusComparison X) :=
      Cone.ext (Iso.refl _) fun j => by
        rw [Cone.whisker_π, Functor.whiskerLeft_app,
          Functor.Initial.extendCone_obj_π_app' c' (𝟙 ((minusComparison X).obj j))]
        simp
    have hE : EssentiallyConstantPro.IsEssentiallyConstantWith (minusComparison X ⋙
        MorphismProperty.Over.forget (qisBig A) ⊤ _ ⋙ Over.forget _ ⋙ Fbig F) c' i
        ((Dminus.ι B).map r) := h.map (Dminus.ι B)
    exact ⟨_, _, _, (hE.of_iso e).of_whisker _ hdom⟩

/-- **Statement (3), values.** When the left derived functors of `F : K(A) ⥤ D(B)` and of
`F⁻ : K⁻(A) ⥤ D⁻(B)` are defined at `X`, with values `cbig.pt` and `cminus.pt`, the values are
canonically isomorphic in `D(B)` via the embedding `D⁻(B) ↪ D(B)`, compatibly with the structure
maps `LF(X) ⟶ F(X')` and `LF⁻(X) ⟶ F⁻(X')` of every `s : X' ⟶ X` in `Qis⁻(A)`, in particular
with the canonical maps at `𝟙 X`. -/
@[stacks 05T5 "(3), values", sga "4 XVII 1.2.5" "(iv)", sga "4½ Etat_0 4.2.3.2" "(A)"]
theorem valueL_big_iso_minus (X : KMinus A)
    {cbig : Cone (MorphismProperty.Over.forget (qisBig A) ⊤ ((KMinus.ι A).obj X) ⋙
      Over.forget _ ⋙ Fbig F)}
    (hbig : (Fbig F).IsLeftDerivedValueAt (qisBig A) ((KMinus.ι A).obj X) cbig)
    {cminus : Cone (MorphismProperty.Over.forget (qisMinus A) ⊤ X ⋙ Over.forget X ⋙ Fminus F)}
    (hminus : (Fminus F).IsLeftDerivedValueAt (qisMinus A) X cminus) :
    ∃ e : cbig.pt ≅ (Dminus.ι B).obj cminus.pt,
      ∀ s : (qisMinus A).Over ⊤ X,
        e.hom ≫ (Dminus.ι B).map (cminus.π.app s) =
          cbig.π.app (MorphismProperty.Over.mk ⊤ ((KMinus.ι A).map s.hom) s.prop) := by
  have := minusComparison_initial (A := A) X
  obtain ⟨i, r, h⟩ := (Functor.isLeftDerivedValueAt_iff _ _ _ _).1 hminus
  have limBig : IsLimit (cbig.whisker (minusComparison X)) :=
    (Functor.Initial.isLimitWhiskerEquiv _ cbig).symm hbig.isLimit
  have limMinus : IsLimit ((Dminus.ι B).mapCone cminus) := isLimitOfOp
    (EssentiallyConstantPro.isEssentiallyConstantWith_op (h.map (Dminus.ι B))).isColimit
  exact ⟨limBig.conePointUniqueUpToIso limMinus,
    fun s => limBig.conePointUniqueUpToIso_hom_comp limMinus s⟩

/-- **Statement (4).** For `X` an object of `K⁻(A)`, `X` computes the left derived functor of
`F : K(A) ⥤ D(B)` (viewed in `K(A)`) if and only if `X` computes the left derived functor of
`F⁻ : K⁻(A) ⥤ D⁻(B)`. -/
@[stacks 05T5 "(4)", sga "4 XVII 1.2.5" "(iv), single functor"]
theorem computesL_big_iff_minus (X : KMinus A) :
    (Fbig F).ComputesLeftDerived (qisBig A) ((KMinus.ι A).obj X) ↔
      (Fminus F).ComputesLeftDerived (qisMinus A) X := by
  have : (Dminus.ι B).Full := (ObjectProperty.fullyFaithfulι _).full
  have : (Dminus.ι B).Faithful := (ObjectProperty.fullyFaithfulι _).faithful
  constructor
  · rintro ⟨cbig, hbig, hiso⟩
    obtain ⟨cminus, hminus⟩ := (definedAtL_big_iff_minus F X).1 ⟨cbig, hbig⟩
    obtain ⟨e, he⟩ := valueL_big_iso_minus F X hbig hminus
    refine ⟨cminus, hminus, ?_⟩
    have : IsIso (e.hom ≫ (Dminus.ι B).map
        (cminus.π.app (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X)))) := by
      rwa [he (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X))]
    have := IsIso.of_isIso_comp_left e.hom ((Dminus.ι B).map
      (cminus.π.app (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X))))
    exact isIso_of_fully_faithful (Dminus.ι B) _
  · rintro ⟨cminus, hminus, hiso⟩
    obtain ⟨cbig, hbig⟩ := (definedAtL_big_iff_minus F X).2 ⟨cminus, hminus⟩
    obtain ⟨e, he⟩ := valueL_big_iso_minus F X hbig hminus
    refine ⟨cbig, hbig, ?_⟩
    have h := he (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X))
    have key : IsIso (e.hom ≫ (Dminus.ι B).map
        (cminus.π.app (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X)))) :=
      inferInstance
    rwa [h] at key

end Concrete

end StacksDerivedFunctorComparison
