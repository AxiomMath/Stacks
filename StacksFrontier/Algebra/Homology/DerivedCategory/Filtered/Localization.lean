module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.InjectiveResolutionDegreeZero
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The kernel of the localisation of the finitely filtered complexes

This file proves a model-level analogue of [Stacks, Tag 05S1] on the filtered cochain complexes.
The statement of [Stacks, Tag 05S1] in the triangulated category `K(Fil^f(𝒜))` is
`HomotopyCategory.filteredAcyclic_isTriangulated_and_trW_eq_filteredQuasiIso`, in
`StacksFrontier.Homology.FilteredDerivedCategory.Basic`.

The source deduces [Stacks, Tag 05S1] from [Stacks, Tag 05RM] applied to the homological functor
`H^0 ∘ gr` of [Stacks, Tag 05S0]. That route is unavailable in this model: `FAc(𝒜)` and `FQis(𝒜)`
are recorded on filtered *complexes* rather than on `K(Fil^f(𝒜))`, and no triangulated structure is
constructed on the filtered complexes, so there is no shift, no distinguished triangle and no cone.
What the proof of 05RM uses about `H^0 ∘ gr`, however, is only that the family `H^n ∘ gr^p` kills
exactly the filtered acyclic complexes and inverts exactly the filtered quasi-isomorphisms, both by
definition, and that is enough. Writing `Z` for the zero filtered complex: if `K` is filtered
acyclic then `Z ⟶ K` is a filtered quasi-isomorphism, so `L` inverts it and `L(K) ≅ L(Z)`, a zero
object; conversely if `L(K)` is zero then the identity of `L(K)` is the image of `K ⟶ Z ⟶ K`, and
pushing this along the functor `D ⥤ 𝒜` through which `H^n ∘ gr^p` factors exhibits the identity of
`H^n(gr^p K)` as factoring through `H^n(gr^p Z) = 0`. The same functor gives
`FQis(𝒜) = (isomorphisms _).inverseImage L`, the inclusion `≤` being `Localization.inverts`. Strict
fullness and closure under retracts are the same computation: a retract of `K` gives a retract of
`H^n(gr^p K)`, and a retract of a zero object is a zero object.

That a localization functor `L : C ⥤ D` at `W` sends a zero object of `C` to a zero object of `D`
is a general fact about localizations that Mathlib does not have; it is proved by reduction to the
canonical model `W.Q` and then by the induction principle
`Localization.Construction.morphismProperty_eq_top` on the morphisms of `W.Localization`. Mathlib
has no zero object on `FilteredObject C I` either; `zeroFiltered` is the zero object of `C` with
the constant filtration by itself.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite HomologicalComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]


section FilteredAcyclicKernel

universe v' v'' u' u''

namespace CochainComplex

namespace filteredAcyclicKernel

section Localization

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (W : MorphismProperty C) {Z : C}

/-- The morphism `Q(Z) ⟶ X` of `W.Localization` induced by the unique morphism out of a zero
object `Z` of `C`. -/
private noncomputable def qFrom (hZ : IsZero Z) (X : W.Localization) : W.Q.obj Z ⟶ X :=
  W.Q.map (hZ.to_ X.as.obj)

/-- The morphism `X ⟶ Q(Z)` of `W.Localization` induced by the unique morphism into a zero
object `Z` of `C`. -/
private noncomputable def qTo (hZ : IsZero Z) (X : W.Localization) : X ⟶ W.Q.obj Z :=
  W.Q.map (hZ.from_ X.as.obj)

private theorem qFrom_Q_obj (hZ : IsZero Z) (X : C) :
    qFrom W hZ (W.Q.obj X) = W.Q.map (hZ.to_ X) := rfl

private theorem qTo_Q_obj (hZ : IsZero Z) (X : C) :
    qTo W hZ (W.Q.obj X) = W.Q.map (hZ.from_ X) := rfl

/-- The canonical localization functor `W.Q : C ⥤ W.Localization` sends a zero object to a zero
object. -/
private theorem isZero_Q_obj (hZ : IsZero Z) : IsZero (W.Q.obj Z) := by
  constructor
  · intro Y
    refine ⟨⟨qFrom W hZ Y⟩, fun f => show f = qFrom W hZ Y from ?_⟩
    let P : MorphismProperty W.Localization :=
      fun X Y f => qFrom W hZ X ≫ f = qFrom W hZ Y
    have hfac : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), qFrom W hZ (W.Q.obj X) ≫ W.Q.map f
        = qFrom W hZ (W.Q.obj Y) := fun {X Y} f => by
      simp only [qFrom_Q_obj, ← W.Q.map_comp]
      congr 1
      exact hZ.eq_of_src _ _
    have hcomp : P.IsStableUnderComposition :=
      ⟨fun f g hf hg => by simp only [P, ← Category.assoc, hf] at *; exact hg⟩
    have htop : P = ⊤ := Localization.Construction.morphismProperty_eq_top P hfac
      (fun {X Y} w hw => by
        change qFrom W hZ (W.Q.obj Y) ≫ (Localization.Construction.wIso w hw).inv = _
        rw [← hfac w, Category.assoc]
        change _ ≫ (Localization.Construction.wIso w hw).hom ≫ _ = _
        rw [Iso.hom_inv_id, Category.comp_id])
    have hP : P f := by simp [htop]
    have h2 : qFrom W hZ (W.Q.obj Z) = 𝟙 _ := by
      rw [qFrom_Q_obj, hZ.eq_of_src (hZ.to_ Z) (𝟙 Z), W.Q.map_id]
    rw [show f = qFrom W hZ (W.Q.obj Z) ≫ f by rw [h2, Category.id_comp], hP]
  · intro Y
    refine ⟨⟨qTo W hZ Y⟩, fun f => show f = qTo W hZ Y from ?_⟩
    let P : MorphismProperty W.Localization :=
      fun X Y f => f ≫ qTo W hZ Y = qTo W hZ X
    have hfac : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W.Q.map f ≫ qTo W hZ (W.Q.obj Y)
        = qTo W hZ (W.Q.obj X) := fun {X Y} f => by
      simp only [qTo_Q_obj, ← W.Q.map_comp]
      congr 1
      exact hZ.eq_of_tgt _ _
    have hcomp : P.IsStableUnderComposition :=
      ⟨fun f g hf hg => by simp only [P, Category.assoc, hg] at *; exact hf⟩
    have htop : P = ⊤ := Localization.Construction.morphismProperty_eq_top P hfac
      (fun {X Y} w hw => by
        change (Localization.Construction.wIso w hw).inv ≫ qTo W hZ (W.Q.obj X) = _
        rw [← hfac w, ← Category.assoc]
        change ((Localization.Construction.wIso w hw).inv ≫
          (Localization.Construction.wIso w hw).hom) ≫ _ = _
        rw [Iso.inv_hom_id, Category.id_comp])
    have hP : P f := by simp [htop]
    have h2 : qTo W hZ (W.Q.obj Z) = 𝟙 _ := by
      rw [qTo_Q_obj, hZ.eq_of_tgt (hZ.from_ Z) (𝟙 Z), W.Q.map_id]
    rw [show f = f ≫ qTo W hZ (W.Q.obj Z) by rw [h2, Category.comp_id], hP]

/-- An equivalence of categories preserves and reflects zero objects. Neither category is
assumed to have a zero object. -/
private theorem Equivalence.isZero_iff (e : C ≌ D) (X : C) :
    IsZero X ↔ IsZero (e.functor.obj X) := by
  refine ⟨fun h ↦ ⟨fun Y ↦ ⟨?_⟩, fun Y ↦ ⟨?_⟩⟩,
    IsZero.of_full_of_faithful_of_isZero e.functor X⟩
  · have : Unique (X ⟶ e.inverse.obj Y) := (h.unique_to _).some
    exact (e.toAdjunction.homEquiv X Y).unique
  · have : Unique (e.symm.functor.obj Y ⟶ X) := (h.unique_from _).some
    exact (e.symm.toAdjunction.homEquiv Y X).symm.unique

/-- Any localization functor sends a zero object to a zero object. -/
private theorem isZero_map_of_isZero (L : C ⥤ D) [L.IsLocalization W] (hZ : IsZero Z) :
    IsZero (L.obj Z) :=
  ((Localization.qCompEquivalenceFromModelFunctorIso L W).app Z).symm.isZero_iff.mpr
    ((Equivalence.isZero_iff (Localization.equivalenceFromModel L W) _).mp (isZero_Q_obj W hZ))

end Localization

/-! ### Detecting the kernel of a localization by a functor that inverts the class -/

section Detect

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E] [HasZeroMorphisms E]

/-- An object whose identity factors through a zero object is a zero object. -/
private theorem isZero_of_id_eq_comp {X Y : E} (hY : IsZero Y) (f : X ⟶ Y) (g : Y ⟶ X)
    (h : 𝟙 X = f ≫ g) : IsZero X := by
  rw [IsZero.iff_id_eq_zero, h, hY.eq_of_tgt f 0, zero_comp]

/-- If `F : C ⥤ E` inverts `W` and `L : C ⥤ D` is a localization of `C` at `W`, then `F` kills
every object that `L` kills, provided it kills some object that the given one maps to and from.
This is the elementary form of "the kernel of the localization is contained in the kernel of
`F`". -/
private theorem isZero_map_of_isZero_map_of_isInvertedBy
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] (F : C ⥤ E)
    (hF : W.IsInvertedBy F) {K Z : C} (hK : IsZero (L.obj K)) (hZ : IsZero (F.obj Z))
    (u : K ⟶ Z) (v : Z ⟶ K) : IsZero (F.obj K) := by
  set G := Localization.lift F hF L with hG
  set e := Localization.fac F hF L with he
  have hz : IsZero ((L ⋙ G).obj Z) := (e.app Z).isZero_iff.mpr hZ
  refine (e.app K).isZero_iff.mp (isZero_of_id_eq_comp hz ((L ⋙ G).map u) ((L ⋙ G).map v) ?_)
  calc 𝟙 ((L ⋙ G).obj K) = G.map (𝟙 (L.obj K)) := (G.map_id _).symm
    _ = G.map (L.map u ≫ L.map v) :=
        congrArg G.map (hK.eq_of_src (𝟙 (L.obj K)) (L.map u ≫ L.map v))
    _ = (L ⋙ G).map u ≫ (L ⋙ G).map v := G.map_comp _ _

end Detect

/-! ### The zero filtered object -/

section ZeroFiltered

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]
  (I : Type u') [Category.{v'} I]

open scoped ZeroObject

/-- The zero filtered object: the zero object of `C`, filtered by itself in every degree. -/
private noncomputable def zeroFiltered : FilteredObject C I where
  X := 0
  filtration := ⟨(Functor.const I).obj (MonoOver.mk (𝟙 (0 : C)))⟩

private theorem isZero_zeroFiltered : IsZero (zeroFiltered C I) :=
  ⟨fun _ => ⟨⟨⟨FilteredObject.homMk 0 (fun _ => 0) (by simp)⟩,
      fun _ => by ext; exact (isZero_zero C).eq_of_src _ _⟩⟩,
    fun _ => ⟨⟨⟨FilteredObject.homMk 0 (fun _ => 0) (by simp)⟩,
      fun _ => by ext; exact (isZero_zero C).eq_of_tgt _ _⟩⟩⟩

end ZeroFiltered

/-! ### Graded pieces -/

section GradedPiece

variable {A : Type u} [Category.{v} A] [Abelian A]

private theorem isZero_gradedPiece_zeroFiltered (p : ℤ) :
    IsZero ((FilteredObject.gr p).obj
      (zeroFiltered (CochainComplex A ℤ) ℤᵒᵖ)) :=
  FilteredObject.isZero_gr_obj_of_isZero _ le_rfl (isZero_zero _)

/-- A filtered complex is filtered acyclic exactly when every `H^n(gr^p K)` vanishes. -/
private theorem filteredAcyclic_iff (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) :
    filteredAcyclic A K ↔ ∀ p n : ℤ,
      IsZero (((FilteredObject.gr p).obj K).homology n) := by
  simp [filteredAcyclic, HomologicalComplex.acyclic_iff,
    HomologicalComplex.exactAt_iff_isZero_homology]

/-- The family of functors `H^n ∘ gr^p` on filtered cochain complexes. -/
private noncomputable abbrev grHomology (p n : ℤ) :
    FilteredObject (CochainComplex A ℤ) ℤᵒᵖ ⥤ A :=
  FilteredObject.gr p ⋙
    HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n

/-- A morphism of filtered complexes is a filtered quasi-isomorphism exactly when `H^n ∘ gr^p`
sends it to an isomorphism for all `p` and `n`. -/
private theorem filteredQuasiIso_iff_isIso_grHomology
    {X Y : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ} (f : X ⟶ Y) :
    filteredQuasiIso A f ↔ ∀ p n : ℤ, IsIso ((grHomology (A := A) p n).map f) := by
  simp only [filteredQuasiIso, quasiIso_iff, quasiIsoAt_iff_isIso_homologyMap]
  exact Iff.rfl

/-- Each `H^n ∘ gr^p` inverts the filtered quasi-isomorphisms: this is the definition of a
filtered quasi-isomorphism. -/
private theorem isInvertedBy_grHomology (p n : ℤ) :
    (filteredQuasiIso A).IsInvertedBy (grHomology (A := A) p n) :=
  fun _ _ f hf => (filteredQuasiIso_iff_isIso_grHomology f).mp hf p n

/-- A filtered complex is filtered acyclic exactly when it is killed by every `H^n ∘ gr^p`. -/
private theorem filteredAcyclic_iff' (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) :
    filteredAcyclic A K ↔ ∀ p n : ℤ, IsZero ((grHomology (A := A) p n).obj K) :=
  filteredAcyclic_iff K

private theorem isZero_grHomology_zeroFiltered (p n : ℤ) :
    IsZero ((grHomology (A := A) p n).obj (zeroFiltered (CochainComplex A ℤ) ℤᵒᵖ)) :=
  Functor.map_isZero (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n)
    (isZero_gradedPiece_zeroFiltered p)

private theorem filteredAcyclic_zeroFiltered :
    filteredAcyclic A (zeroFiltered (CochainComplex A ℤ) ℤᵒᵖ) :=
  (filteredAcyclic_iff' _).mpr isZero_grHomology_zeroFiltered

end GradedPiece

end filteredAcyclicKernel

section

open filteredAcyclicKernel

variable {A : Type u} [Category.{v} A] [Abelian A] {D : Type u'} [Category.{v'} D]

/-- A model-level form of [Stacks, Tag 05S1] on all filtered cochain complexes of `𝒜` (filtered by
subcomplexes, with no finiteness condition), not on `K(Fil^f(𝒜))`: the filtered acyclic complexes
`filteredAcyclic A` are closed under isomorphisms and retracts, every localisation `L` of the
filtered complexes at `filteredQuasiIso A` has kernel exactly `filteredAcyclic A` and inverts
exactly the filtered quasi-isomorphisms, and each `H^n ∘ gr^p` inverts `filteredQuasiIso A`. No
triangulated structure is involved. The statement of [Stacks, Tag 05S1] itself, in the triangulated
category `K(Fil^f(𝒜))` — `FAc(𝒜)` a strictly full saturated triangulated subcategory whose
multiplicative system is `FQis(𝒜)`, the kernel of `K(Fil^f(𝒜)) ⥤ DF(𝒜)` being `FAc(𝒜)` and
`H^0 ∘ gr` factoring through `DF(𝒜)` — is
`HomotopyCategory.filteredAcyclic_isTriangulated_and_trW_eq_filteredQuasiIso`. -/
@[sga "4 Vbis 2.5.1" "Σ saturated", sga "4½ Etat_0 2.4.1" "filtered complexes"]
public theorem kernel_eq_filteredAcyclic_and_filteredQuasiIso_eq_inverseImage_isomorphisms :
    (filteredAcyclic A).IsClosedUnderIsomorphisms ∧
      (filteredAcyclic A).IsStableUnderRetracts ∧
      (∀ (L : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ ⥤ D)
          [L.IsLocalization (filteredQuasiIso A)],
        L.kernel = filteredAcyclic A ∧
          filteredQuasiIso A = (MorphismProperty.isomorphisms D).inverseImage L) ∧
      (∀ p n : ℤ, (filteredQuasiIso A).IsInvertedBy
        (FilteredObject.gr p ⋙
          HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n)) := by
  have hretract : (filteredAcyclic A).IsStableUnderRetracts := by
    refine ⟨fun {X Y} r hY => (filteredAcyclic_iff' X).mpr fun p n => ?_⟩
    refine isZero_of_id_eq_comp ((filteredAcyclic_iff' Y).mp hY p n)
      ((grHomology p n).map r.i) ((grHomology p n).map r.r) ?_
    rw [← Functor.map_comp, r.retract]
    exact ((grHomology p n).map_id X).symm
  refine ⟨inferInstance, hretract, fun L _ => ⟨?_, ?_⟩, isInvertedBy_grHomology⟩
  · ext K
    refine ⟨fun hK => (filteredAcyclic_iff' K).mpr fun p n => ?_, fun hK => ?_⟩
    · exact isZero_map_of_isZero_map_of_isInvertedBy L (filteredQuasiIso A) (grHomology p n)
        (isInvertedBy_grHomology p n) hK (isZero_grHomology_zeroFiltered p n)
        ((isZero_zeroFiltered _ _).from_ K) ((isZero_zeroFiltered _ _).to_ K)
    · have hqi : filteredQuasiIso A ((isZero_zeroFiltered (CochainComplex A ℤ) ℤᵒᵖ).to_ K) :=
        (filteredQuasiIso_iff_isIso_grHomology _).mpr fun p n =>
          IsZero.isIso (isZero_grHomology_zeroFiltered p n)
            ((filteredAcyclic_iff' K).mp hK p n) _
      have : IsIso (L.map ((isZero_zeroFiltered (CochainComplex A ℤ) ℤᵒᵖ).to_ K)) :=
        Localization.inverts L (filteredQuasiIso A) _ hqi
      exact IsZero.of_iso
        (isZero_map_of_isZero (filteredQuasiIso A) L (isZero_zeroFiltered _ _))
        (asIso (L.map ((isZero_zeroFiltered (CochainComplex A ℤ) ℤᵒᵖ).to_ K))).symm
  · ext X Y f
    refine ⟨fun hf => Localization.inverts L (filteredQuasiIso A) f hf, fun hf => ?_⟩
    have hf' : IsIso (L.map f) := hf
    refine (filteredQuasiIso_iff_isIso_grHomology f).mpr fun p n => ?_
    have hlift : IsIso ((L ⋙ Localization.lift (grHomology (A := A) p n)
        (isInvertedBy_grHomology p n) L).map f) := by
      dsimp only [Functor.comp_map]
      infer_instance
    exact (NatIso.isIso_map_iff
      (Localization.fac (grHomology (A := A) p n) (isInvertedBy_grHomology p n) L) f).mp hlift

end

end CochainComplex

end FilteredAcyclicKernel

end
