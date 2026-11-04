module

public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import StacksFrontier.CategoryTheory.Monoidal.Reseat
public import StacksFrontier.Homology.KFlat.BifunctorLocalization

/-!
# The symmetric monoidal derived category of a monoidal abelian category

Let `A` be an abelian category with a symmetric monoidal structure whose tensor product is
additive in each variable, and suppose the total complexes of the tensor double complexes
exist, so that `Comp(A)` is symmetric monoidal under the total tensor product.  If every
cochain complex of objects of `A` receives a quasi-isomorphism from a K-flat one, then the
derived category `D(A)` is symmetric monoidal.

Everything is obtained by localizing twice, so that no coherence diagram is checked here.
The homotopy category `K(A)` is the localization of `Comp(A)` at the homotopy equivalences,
which are stable under tensoring, so Mathlib's `CategoryTheory.Localization.Monoidal` makes
`K(A)` symmetric monoidal.  The K-flat objects of `K(A)` are then a full symmetric monoidal
subcategory, `D(A)` is its localization at the quasi-isomorphisms
(`CochainComplex.KFlatBifunctor.kFlatQ_isLocalization`), and the quasi-isomorphisms between
K-flat objects are stable under tensoring because tensoring with a K-flat complex preserves
quasi-isomorphisms.  The same machinery therefore makes `D(A)` symmetric monoidal.

## Main definitions

* `CochainComplex.KFlatMonoidal.homotopyMonoidal`,
  `CochainComplex.KFlatMonoidal.homotopyBraided`,
  `CochainComplex.KFlatMonoidal.homotopySymmetric`: the symmetric monoidal structure on
  `K(A)`.
* `CochainComplex.KFlatMonoidal.derivedMonoidal`,
  `CochainComplex.KFlatMonoidal.derivedSymmetric`: the symmetric monoidal structure on
  `D(A)`.

## Main results

* `CochainComplex.KFlatMonoidal.kFlat_tensorUnit`,
  `CochainComplex.KFlatMonoidal.kFlat_tensor`,
  `CochainComplex.KFlatMonoidal.kFlatLeft_of_kFlat`: the K-flat complexes contain the unit,
  are stable under the tensor product, and are K-flat in the first variable as well.  None of
  these is a hypothesis: the right unitor, the associator and the braiding of `Comp(A)` prove
  them in one line each.
* `CochainComplex.KFlatMonoidal.derivedTensorIso`: on K-flat complexes the tensor product of
  `D(A)` is the image of the total tensor product of complexes.  This is what identifies the
  structure as the *derived* tensor product.
* `CochainComplex.KFlatMonoidal.derivedUnitIso`: the unit of `D(A)` is the image of the unit
  of `Comp(A)`.

## Implementation notes

`Localization.Monoidal.LocalizedMonoidal L W ε` is a type synonym for the target of `L`
carrying the localized structure.  All the structures below are therefore obtained by
`inferInstanceAs` through that synonym and then used at the underlying category; the
definitional unfolding of the synonym is what makes this typecheck, and it is also why each
structure has to be named rather than left to instance synthesis — `K(A)` and `D(A)` have no
monoidal structure in scope until one of these definitions is seated.

The two whiskering stability conditions for the quasi-isomorphisms are genuinely different
facts.  Tensoring on the right with a K-flat complex preserves quasi-isomorphisms by
`CochainComplex.KFlatBifunctor.quasiIso_of_kFlat`; tensoring on the left needs the mirror
predicate `KFlatLeft`, and that is where the braiding of `Comp(A)` is used.

`homotopyMu_natural_left` and `homotopyMu_natural_right` pass the localization functor, the
morphism property and the unit isomorphism explicitly rather than by `_`.  Left to
unification they are solved against the unfolding of `HomotopyCategory.quotient`, for which
Mathlib's `IsLocalization` instance does not fire.

## References

* [The Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [The Stacks Project, Tag 0GWP](https://stacks.math.columbia.edu/tag/0GWP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Localization

universe w v u

namespace CochainComplex.KFlatMonoidal

variable (A : Type u) [Category.{v} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ A), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-! ### Homotopy equivalences are stable under the tensor product -/

/-- The tensor product of two homotopy equivalences of complexes is a homotopy equivalence.
Both homotopies are the ones `HomologicalComplex.mapBifunctorMapHomotopy` produces for the
total complex, composed in the two variables. -/
def tensorHomotopyEquiv {K₁ K₂ L₁ L₂ : CochainComplex A ℤ}
    (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) :
    HomotopyEquiv (K₁ ⊗ K₂) (L₁ ⊗ L₂) where
  hom := e₁.hom ⊗ₘ e₂.hom
  inv := e₁.inv ⊗ₘ e₂.inv
  homotopyHomInvId := by
    rw [tensorHom_comp_tensorHom]
    exact (((HomologicalComplex.mapBifunctorMapHomotopy₁ e₁.homotopyHomInvId
        (e₂.hom ≫ e₂.inv) (curriedTensor A) (ComplexShape.up ℤ)).trans
      (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 K₁) e₂.homotopyHomInvId
        (curriedTensor A) (ComplexShape.up ℤ))).trans
      (Homotopy.ofEq (id_tensorHom_id K₁ K₂)))
  homotopyInvHomId := by
    rw [tensorHom_comp_tensorHom]
    exact (((HomologicalComplex.mapBifunctorMapHomotopy₁ e₁.homotopyInvHomId
        (e₂.inv ≫ e₂.hom) (curriedTensor A) (ComplexShape.up ℤ)).trans
      (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 L₁) e₂.homotopyInvHomId
        (curriedTensor A) (ComplexShape.up ℤ))).trans
      (Homotopy.ofEq (id_tensorHom_id L₁ L₂)))

/-- The homotopy equivalences of cochain complexes form a monoidal class of morphisms. -/
instance homotopyEquivalences_isMonoidal :
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ)).IsMonoidal := by
  apply MorphismProperty.IsMonoidal.mk'
  rintro _ _ _ _ _ _ ⟨e₁, rfl⟩ ⟨e₂, rfl⟩
  exact ⟨tensorHomotopyEquiv A e₁ e₂, rfl⟩

/-! ### The symmetric monoidal homotopy category -/

/-- The unit of `K(A)`: the image of the unit of `Comp(A)`. -/
abbrev homotopyUnit : HomotopyCategory A (ComplexShape.up ℤ) :=
  (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (𝟙_ (CochainComplex A ℤ))

/-- `K(A)` as the monoidal localization of `Comp(A)` at the homotopy equivalences. -/
abbrev HomotopyLocalized :=
  LocalizedMonoidal (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (Iso.refl (homotopyUnit A))

/-- **The homotopy category of complexes is monoidal**, with the total tensor product. -/
@[instance_reducible]
def homotopyMonoidal : MonoidalCategory (HomotopyCategory A (ComplexShape.up ℤ)) :=
  inferInstanceAs (MonoidalCategory (HomotopyLocalized A))

/-- **The homotopy category of complexes is braided** whenever `Comp(A)` is. -/
@[instance_reducible]
def homotopyBraided [BraidedCategory (CochainComplex A ℤ)] :
    @BraidedCategory (HomotopyCategory A (ComplexShape.up ℤ)) _ (homotopyMonoidal A) :=
  inferInstanceAs (BraidedCategory (HomotopyLocalized A))

/-- **The homotopy category of complexes is symmetric** whenever `Comp(A)` is. -/
@[instance_reducible]
def homotopySymmetric [SymmetricCategory (CochainComplex A ℤ)] :
    @SymmetricCategory (HomotopyCategory A (ComplexShape.up ℤ)) _ (homotopyMonoidal A) :=
  inferInstanceAs (SymmetricCategory (HomotopyLocalized A))

attribute [local instance] homotopyMonoidal homotopyBraided homotopySymmetric

/-- The comparison isomorphism between the tensor product of `K(A)` and the image of the
total tensor product of complexes.  This is `Localization.Monoidal.μ`, read at `K(A)`. -/
abbrev homotopyMu (X Y : CochainComplex A ℤ) :
    (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj X ⊗
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y ≅
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (X ⊗ Y) :=
  Localization.Monoidal.μ (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (Iso.refl (homotopyUnit A)) X Y

/-- The comparison isomorphism `homotopyMu` is natural in its first argument. -/
lemma homotopyMu_natural_left {X₁ X₂ : CochainComplex A ℤ} (f : X₁ ⟶ X₂)
    (Y : CochainComplex A ℤ) :
    (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f ▷
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Y ≫
        (homotopyMu A X₂ Y).hom =
      (homotopyMu A X₁ Y).hom ≫
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (f ▷ Y) :=
  Localization.Monoidal.μ_natural_left (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (Iso.refl (homotopyUnit A)) f Y

/-- The comparison isomorphism `homotopyMu` is natural in its second argument. -/
lemma homotopyMu_natural_right (X : CochainComplex A ℤ) {Y₁ Y₂ : CochainComplex A ℤ}
    (g : Y₁ ⟶ Y₂) :
    (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj X ◁
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map g ≫
        (homotopyMu A X Y₂).hom =
      (homotopyMu A X Y₁).hom ≫
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (X ◁ g) :=
  Localization.Monoidal.μ_natural_right (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (Iso.refl (homotopyUnit A)) X g

/-! ### The K-flat complexes are a monoidal class of objects -/

open CochainComplex.KFlatBifunctor

/-- K-flatness of an object of `K(A)` is stable under isomorphism in `K(A)`: by
`kFlatObjects_iff` it is an intersection of preimages of the acyclic objects, each of which
is stable under isomorphism.  This is *not* automatic from
`kFlatObjects_isTriangulated`. -/
instance kFlatObjects_isClosedUnderIsomorphisms :
    (kFlatObjects (curriedTensor A)).IsClosedUnderIsomorphisms where
  of_iso {_ _} e hX := by
    rw [kFlatObjects_iff] at hX ⊢
    intro G hG
    exact (acyclicPreimage (curriedTensor A) G).prop_of_iso e (hX G hG)

omit [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- **The unit of `Comp(A)` is K-flat**: tensoring with it is the right unitor, so it carries
an acyclic complex to an isomorphic, hence acyclic, complex. -/
lemma kFlat_tensorUnit : KFlat (curriedTensor A) (𝟙_ (CochainComplex A ℤ)) :=
  fun G hG n ↦ HomologicalComplex.ExactAt.of_iso (hG n) (ρ_ G).symm

omit [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- **The tensor product of two K-flat complexes is K-flat.**  The associator of `Comp(A)`
rewrites `G ⊗ (K ⊗ L)` as `(G ⊗ K) ⊗ L`, and K-flatness of `K` then of `L` is applied in
turn.  For sheaves of modules this is Stacks Tag 079R; here the associator makes it one
line. -/
lemma kFlat_tensor {K L : CochainComplex A ℤ} (hK : KFlat (curriedTensor A) K)
    (hL : KFlat (curriedTensor A) L) : KFlat (curriedTensor A) (K ⊗ L) :=
  fun G hG n ↦ HomologicalComplex.ExactAt.of_iso (hL (G ⊗ K) (hK G hG) n) (α_ G K L)

/-- **A K-flat complex is K-flat in the first variable as well**, when `Comp(A)` is braided:
the braiding identifies `Tot(K ⊗ G)` with `Tot(G ⊗ K)`.  This is the statement whose cost in
`StacksDraft.Ch21.Sec17.Tag06YUFlatSymmetry` is the Koszul-sign symmetry of the total tensor
product. -/
lemma kFlatLeft_of_kFlat [BraidedCategory (CochainComplex A ℤ)] {K : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K) : KFlatLeft (curriedTensor A) K :=
  fun G hG n ↦ HomologicalComplex.ExactAt.of_iso (hK G hG n) (β_ G K)

/-- The unit of `K(A)` is K-flat. -/
instance kFlatObjects_containsUnit :
    (kFlatObjects (curriedTensor A)).ContainsUnit where
  prop_unit := kFlat_tensorUnit A

/-- The K-flat objects of `K(A)` are stable under the tensor product: their tensor product in
`K(A)` is isomorphic, by `homotopyMu`, to the image of the total tensor product of the
underlying complexes. -/
instance kFlatObjects_tensorLE :
    (kFlatObjects (curriedTensor A)).TensorLE (kFlatObjects (curriedTensor A))
      (kFlatObjects (curriedTensor A)) where
  prop_tensor X Y hX hY :=
    (kFlatObjects (curriedTensor A)).prop_of_iso (homotopyMu A X.as Y.as).symm
      (kFlat_tensor A hX hY)

/-- The K-flat objects of `K(A)` are a monoidal object property, hence a full monoidal
subcategory of `K(A)`. -/
instance kFlatObjects_isMonoidal : (kFlatObjects (curriedTensor A)).IsMonoidal where

/-! ### Quasi-isomorphisms between K-flat objects are stable under the tensor product -/

/-- **Right-whiskering by a K-flat complex preserves quasi-isomorphisms in `K(A)`.**  The
whiskering is conjugate, by `homotopyMu`, to the total tensor product of the morphism with
the identity, and that is a quasi-isomorphism by
`CochainComplex.KFlatBifunctor.quasiIso_of_kFlat`. -/
lemma quasiIso_whiskerRight {K₁ K₂ : CochainComplex A ℤ} (f : K₁ ⟶ K₂) (hf : QuasiIso f)
    (L : CochainComplex A ℤ) (hL : KFlat (curriedTensor A) L) :
    HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f ▷
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L) :=
  (MorphismProperty.arrow_mk_iso_iff _
    (Arrow.isoMk (homotopyMu A K₁ L) (homotopyMu A K₂ L)
      (homotopyMu_natural_left A f L).symm)).2
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
      (CochainComplex.KFlatBifunctor.quasiIso_of_kFlat (curriedTensor A) L hL f hf))

/-- **Left-whiskering by a K-flat complex preserves quasi-isomorphisms in `K(A)`.**  This is
the mirror of `quasiIso_whiskerRight`, and it is the one that needs a K-flat complex to be
K-flat for the *flipped* tensor bifunctor as well. -/
lemma quasiIso_whiskerLeft [BraidedCategory (CochainComplex A ℤ)] (K : CochainComplex A ℤ)
    (hK : KFlat (curriedTensor A) K)
    {L₁ L₂ : CochainComplex A ℤ} (g : L₁ ⟶ L₂) (hg : QuasiIso g) :
    HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K ◁
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map g) :=
  (MorphismProperty.arrow_mk_iso_iff _
    (Arrow.isoMk (homotopyMu A K L₁) (homotopyMu A K L₂)
      (homotopyMu_natural_right A K g).symm)).2
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
      (CochainComplex.KFlatBifunctor.quasiIso_of_kFlatLeft (curriedTensor A) K
        (kFlatLeft_of_kFlat A hK) g hg))

/-- `quasiIso_whiskerRight` with the objects of `K(A)` left as they are rather than named as
images of complexes.  Every object of `K(A)` *is* the image of its underlying complex, so this
is the same statement; it is the form the monoidality of the quasi-isomorphisms consumes. -/
lemma quasiIso_whiskerRight' {U₁ U₂ V : HomotopyCategory A (ComplexShape.up ℤ)} (f : U₁ ⟶ U₂)
    (hf : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) f)
    (hV : kFlatObjects (curriedTensor A) V) :
    HomotopyCategory.quasiIso A (ComplexShape.up ℤ) (f ▷ V) := by
  obtain ⟨f', rfl⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective
    (X := U₁.as) (Y := U₂.as) f
  exact quasiIso_whiskerRight A f'
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff f').1 hf) V.as hV

/-- The mirror of `quasiIso_whiskerRight'`. -/
lemma quasiIso_whiskerLeft' [BraidedCategory (CochainComplex A ℤ)]
    (V : HomotopyCategory A (ComplexShape.up ℤ))
    (hV : kFlatObjects (curriedTensor A) V)
    {U₁ U₂ : HomotopyCategory A (ComplexShape.up ℤ)} (g : U₁ ⟶ U₂)
    (hg : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) g) :
    HomotopyCategory.quasiIso A (ComplexShape.up ℤ) (V ◁ g) := by
  obtain ⟨g', rfl⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective
    (X := U₁.as) (Y := U₂.as) g
  exact quasiIso_whiskerLeft A V.as hV g'
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff g').1 hg)

/-- **The quasi-isomorphisms between K-flat objects are a monoidal class of morphisms.** -/
instance kFlatQuasiIso_isMonoidal [BraidedCategory (CochainComplex A ℤ)] :
    (kFlatQuasiIso (curriedTensor A)).IsMonoidal where
  whiskerLeft X _ _ _ hg := quasiIso_whiskerLeft' A X.1 X.2 _ hg
  whiskerRight _ hf Y := quasiIso_whiskerRight' A _ hf Y.2

/-! ### The symmetric monoidal derived category -/

section Monoidal

variable [HasDerivedCategory.{w} A] [BraidedCategory (CochainComplex A ℤ)]
  (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    KFlat (curriedTensor A) P ∧ QuasiIso f)

/-- `D(A)` as the monoidal localization of the K-flat objects of `K(A)` at the
quasi-isomorphisms. -/
abbrev DerivedLocalized :=
  letI := kFlatQ_isLocalization (curriedTensor A) hres
  LocalizedMonoidal (kFlatQ (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
    (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _)))

include hres in
/-- **The derived category of `A` is monoidal**, under the derived tensor product.  Both the
tensor bifunctor and the coherence constraints are obtained by localizing the K-flat
subcategory of `K(A)`; no coherence diagram is checked here. -/
@[instance_reducible]
def derivedMonoidal : MonoidalCategory (DerivedCategory A) :=
  letI := kFlatQ_isLocalization (curriedTensor A) hres
  inferInstanceAs (MonoidalCategory (DerivedLocalized A hres))

/-- The image in `D(A)` of a complex, seen through the homotopy category.  This is the
identification `quotient ⋙ Qh ≅ Q` of Mathlib. -/
abbrev derivedQIso (K : CochainComplex A ℤ) :
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ≅
      DerivedCategory.Q.obj K :=
  (DerivedCategory.quotientCompQhIso A).app K

include hres in
/-- **For K-flat complexes the tensor product of `D(A)` is the image of the total tensor
product of complexes.**  This is what identifies the monoidal structure of `derivedMonoidal`
as the *derived* tensor product: the comparison is `Localization.Monoidal.μ` of the second
localization followed by `homotopyMu`, the comparison of the first. -/
def derivedTensorIso {K L : CochainComplex A ℤ} (hK : KFlat (curriedTensor A) K)
    (hL : KFlat (curriedTensor A) L) :
    letI := derivedMonoidal A hres
    DerivedCategory.Q.obj K ⊗ DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj (K ⊗ L) :=
  letI := kFlatQ_isLocalization (curriedTensor A) hres
  letI := derivedMonoidal A hres
  ((derivedQIso A K).symm ⊗ᵢ (derivedQIso A L).symm) ≪≫
    Localization.Monoidal.μ (kFlatQ (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
      (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _)))
      ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩
      ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L, hL⟩ ≪≫
    (kFlatQ (curriedTensor A)).mapIso
      ((kFlatObjects (curriedTensor A)).isoMk
        (Y := ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (K ⊗ L),
          kFlat_tensor A hK hL⟩) (homotopyMu A K L)) ≪≫
    derivedQIso A (K ⊗ L)

include hres in
/-- **The unit of `D(A)` is the image of the unit of `Comp(A)`.** -/
def derivedUnitIso :
    letI := derivedMonoidal A hres
    𝟙_ (DerivedCategory A) ≅ DerivedCategory.Q.obj (𝟙_ (CochainComplex A ℤ)) :=
  derivedQIso A (𝟙_ (CochainComplex A ℤ))

end Monoidal

section Symmetric

variable [HasDerivedCategory.{w} A] [SymmetricCategory (CochainComplex A ℤ)]
  (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    KFlat (curriedTensor A) P ∧ QuasiIso f)

include hres in
/-- **The derived category of a symmetric monoidal `A` is symmetric monoidal.**  The braiding
is the one induced by the braiding of `Comp(A)`, which for complexes of modules is the Koszul
symmetry. -/
@[instance_reducible]
def derivedSymmetric :
    @SymmetricCategory (DerivedCategory A) _ (derivedMonoidal A hres) :=
  letI := kFlatQ_isLocalization (curriedTensor A) hres
  inferInstanceAs (SymmetricCategory (DerivedLocalized A hres))

end Symmetric

end CochainComplex.KFlatMonoidal

end
