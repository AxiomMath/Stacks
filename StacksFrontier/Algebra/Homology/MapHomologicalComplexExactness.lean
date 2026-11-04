module

public import Mathlib.Algebra.Homology.Augment
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Exactness, opcycles and augmentation under `Functor.mapHomologicalComplex`

Let `F : C ⥤ D` be an additive functor which preserves homology, and let
`F.mapHomologicalComplex c : HomologicalComplex C c ⥤ HomologicalComplex D c` be the induced
functor on complexes. This file records the four ways in which such an `F` interacts with the
homological vocabulary of `HomologicalComplex`, none of which Mathlib has at the level of
complexes (it has them all for `ShortComplex`):

* exactness at an index is preserved by `F`, and exactness and acyclicity are *detected* by `F`
  as soon as `F` is faithful;
* a natural transformation `τ : F ⟶ G` between two homology-preserving functors is a
  quasi-isomorphism on the image of a complex as soon as its components at the homology objects
  are isomorphisms (this one needs no additivity);
* the object of opcycles in a fixed degree commutes with `F`, naturally in the complex;
* for `ℕ`-indexed cochain complexes, `F` commutes with `CochainComplex.augment`.

Together these let a statement proved in one category be applied in another along a faithful
exact functor: hypotheses of the form "this augmented complex is acyclic" or "these complexes
of opcycles are acyclic" push forward along `F`, and a conclusion of the form "this map is a
quasi-isomorphism" comes back along `F` by Mathlib's
`HomologicalComplex.quasiIso_map_iff_of_preservesHomology`. The motivating instance is
`forget₂ (ModuleCat R) AddCommGrpCat`, used by `HomologicalComplex₂.quasiIso_of_isProductTotal`
to transport the resolution theorem Stacks 09J0 from abelian groups to `R`-modules.

## Main results

* `HomologicalComplex.ExactAt.map`: exactness at an index is preserved. Acyclicity therefore is
  too, pointwise; the named form of that under the stronger hypothesis that `F` preserves finite
  limits and colimits is `HomologicalComplex.Acyclic.map`.
* `HomologicalComplex.exactAt_map_iff_of_preservesHomology` and
  `HomologicalComplex.acyclic_map_iff_of_preservesHomology`: a faithful such functor detects
  exactness and acyclicity.
* `HomologicalComplex.quasiIsoAt_mapNatTrans_app` and
  `HomologicalComplex.quasiIso_mapNatTrans_app`: the component of
  `NatTrans.mapHomologicalComplex τ c` at a complex `K` is a quasi-isomorphism as soon as the
  components of `τ` at the homology objects `K.homology i` are isomorphisms.
* `CategoryTheory.Functor.mapHomologicalComplexOpcyclesFunctorIso`: the natural isomorphism
  `F.mapHomologicalComplex c ⋙ opcyclesFunctor D c i ≅ opcyclesFunctor C c i ⋙ F`.
* `CochainComplex.mapHomologicalComplexAugmentIso`: the isomorphism, with identity components,
  between the image under `F` of an augmented complex and the augmentation of its image.

## Implementation notes

All of this is mechanical because `((F.mapHomologicalComplex c).obj K).sc i` is *definitionally*
`(K.sc i).map F`: the short complex extracted from the image is the image of the short complex.
So the `ShortComplex`-level results `ShortComplex.Exact.map`,
`ShortComplex.exact_map_iff_of_faithful`, `ShortComplex.homologyMap_mapNatTrans` and
`ShortComplex.mapOpcyclesIso` apply verbatim, and only the naturality of the last one has to be
assembled. That definitional equality is not a *reducible* one, so the two spellings are crossed
in term position (by `exact`) rather than by a rewrite, which fails on it.

`CochainComplex.augment` is defined by a match on the index, so the two complexes compared by
`CochainComplex.mapHomologicalComplexAugmentIso` have definitionally equal terms in every
degree; the isomorphism has identity components and only the commutation with the differentials
needs proof.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

section Preserves

variable {ι : Type*} {c : ComplexShape ι} {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D]

/-- Exactness at an index is preserved by an additive functor which preserves homology. -/
lemma ExactAt.map {K : HomologicalComplex C c} {i : ι} (hK : K.ExactAt i) (F : C ⥤ D)
    [F.Additive] [F.PreservesHomology] :
    ((F.mapHomologicalComplex c).obj K).ExactAt i :=
  ShortComplex.Exact.map hK F

end Preserves

section Detects

variable {ι : Type*} {c : ComplexShape ι} {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [CategoryWithHomology C]
  (K : HomologicalComplex C c) (F : C ⥤ D) [F.Additive] [F.PreservesHomology] [F.Faithful]

/-- A faithful additive functor which preserves homology detects exactness at an index. -/
lemma exactAt_map_iff_of_preservesHomology (i : ι) :
    ((F.mapHomologicalComplex c).obj K).ExactAt i ↔ K.ExactAt i :=
  (K.sc i).exact_map_iff_of_faithful F

/-- A faithful additive functor which preserves homology detects acyclicity. -/
lemma acyclic_map_iff_of_preservesHomology :
    ((F.mapHomologicalComplex c).obj K).Acyclic ↔ K.Acyclic :=
  forall_congr' fun i => K.exactAt_map_iff_of_preservesHomology F i

end Detects

section NatTrans

variable {ι : Type*} {c : ComplexShape ι} {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] {F G : C ⥤ D}
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
  [F.PreservesHomology] [G.PreservesHomology] (τ : F ⟶ G) (K : HomologicalComplex C c)

/-- A natural transformation `τ : F ⟶ G` between functors which preserve homology induces a
quasi-isomorphism at `i` between the two images of a complex `K`, as soon as its component at
the homology object `K.homology i` is an isomorphism.  Additivity is not needed: forming the
image of a complex only uses preservation of zero morphisms. -/
lemma quasiIsoAt_mapNatTrans_app (i : ι) [K.HasHomology i]
    [((F.mapHomologicalComplex c).obj K).HasHomology i]
    [((G.mapHomologicalComplex c).obj K).HasHomology i]
    (h : IsIso (τ.app (K.homology i))) :
    QuasiIsoAt ((NatTrans.mapHomologicalComplex τ c).app K) i := by
  have h' : IsIso (τ.app (K.sc i).homology) := h
  have key : IsIso (ShortComplex.homologyMap ((K.sc i).mapNatTrans τ)) := by
    rw [ShortComplex.homologyMap_mapNatTrans]
    infer_instance
  rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
  exact key

/-- A natural transformation between functors which preserve homology induces a
quasi-isomorphism between the two images of a complex `K`, as soon as all of its components at
the homology objects of `K` are isomorphisms. -/
lemma quasiIso_mapNatTrans_app [∀ i, K.HasHomology i]
    [∀ i, ((F.mapHomologicalComplex c).obj K).HasHomology i]
    [∀ i, ((G.mapHomologicalComplex c).obj K).HasHomology i]
    (h : ∀ i, IsIso (τ.app (K.homology i))) :
    QuasiIso ((NatTrans.mapHomologicalComplex τ c).app K) where
  quasiIsoAt i := quasiIsoAt_mapNatTrans_app τ K i (h i)

end NatTrans

end HomologicalComplex

namespace CategoryTheory.Functor

variable {ι : Type*} (c : ComplexShape ι) {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [CategoryWithHomology C] [CategoryWithHomology D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology] (i : ι)

/-- For an additive functor `F : C ⥤ D` which preserves homology, the object of opcycles in
degree `i` commutes with `F`, naturally in the complex: the natural isomorphism
`F.mapHomologicalComplex c ⋙ opcyclesFunctor D c i ≅ opcyclesFunctor C c i ⋙ F`. -/
def mapHomologicalComplexOpcyclesFunctorIso :
    F.mapHomologicalComplex c ⋙ HomologicalComplex.opcyclesFunctor D c i ≅
      HomologicalComplex.opcyclesFunctor C c i ⋙ F :=
  NatIso.ofComponents (fun K => (K.sc i).mapOpcyclesIso F)
    (fun φ => ShortComplex.mapOpcyclesIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor C c i).map φ) F)

/-- The components of `Functor.mapHomologicalComplexOpcyclesFunctorIso` are the comparison
isomorphisms `ShortComplex.mapOpcyclesIso` of the short complexes in degree `i`. -/
@[simp]
lemma mapHomologicalComplexOpcyclesFunctorIso_hom_app (K : HomologicalComplex C c) :
    (F.mapHomologicalComplexOpcyclesFunctorIso c i).hom.app K =
      ((K.sc i).mapOpcyclesIso F).hom :=
  rfl

end CategoryTheory.Functor

namespace CochainComplex

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (K : CochainComplex C ℕ) {X : C} (f : X ⟶ K.X 0) (w : f ≫ K.d 0 1 = 0)

include w

/-- The witness that the image under an additive functor `F` of a morphism `f : X ⟶ K.X 0`
killed by `K.d 0 1` is killed by the differential of the image complex, so that the image
complex can be augmented by it. -/
lemma map_augment_w (F : C ⥤ D) [F.Additive] :
    F.map f ≫ ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).d 0 1 = 0 := by
  simp [← F.map_comp, w]

/-- An additive functor commutes with augmentation of an `ℕ`-indexed cochain complex: the image
under `F` of `K` augmented by `f` is the image of `K` augmented by the image of `f`. The
components of the isomorphism are identities. -/
def mapHomologicalComplexAugmentIso (F : C ⥤ D) [F.Additive] :
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (augment K f w) ≅
      augment ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) (F.map f)
        (map_augment_w K f w F) where
  hom :=
    { f := fun | 0 => 𝟙 _ | _ + 1 => 𝟙 _
      comm' := fun i j _ => by rcases j with (_ | _ | j) <;> cases i <;> aesop }
  inv :=
    { f := fun | 0 => 𝟙 _ | _ + 1 => 𝟙 _
      comm' := fun i j _ => by rcases j with (_ | _ | j) <;> cases i <;> aesop }
  hom_inv_id := by ext i; cases i <;> simp
  inv_hom_id := by ext i; cases i <;> simp

end CochainComplex
