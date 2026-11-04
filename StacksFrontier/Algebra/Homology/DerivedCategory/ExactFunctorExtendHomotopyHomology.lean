module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorExtendHomology
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose

/-!
# An exact functor commutes with the homology of an extension by zero, on homotopy categories

Let `e : c.Embedding c'` be an embedding of complex shapes with `e.IsRelIff`, let `G : B ⥤ D` be
an additive functor between abelian categories which preserves homology, and let `j, j'` be
degrees with `e.f j = j'`. There are two routes from the degree-`j'` homology of the extension by
zero of `G` applied termwise to a complex to `G` applied to its degree-`j` homology, and
`Stacks.DerivedIndexing.homologyMap_mapExtendIso_hom_comp` says they agree *on complexes*. Its
consumers live one level up, on homotopy categories: the comparison of the two indexings of the
right derived functors, `Stacks.DerivedIndexing.rightDerivedIsoRes`, is assembled there, out of
the three lifts `Stacks.DerivedIndexing.mapExtendHomotopyNatIso`,
`Stacks.DerivedIndexing.extendHomotopyHomologyNatIso` and
`CategoryTheory.Functor.mapHomotopyCategoryHomologyIso`. This file carries the coherence across
the quotient functor.

## Main results

* `Stacks.DerivedIndexing.homologyMap_mapExtendHomotopyNatIso_hom_comp`: **an exact functor
  commutes with the comparison of the homology of an extension by zero, read on homotopy
  categories.**
* `Stacks.DerivedIndexing.mapHomotopyCategoryHomologyIso_comp_extendHomotopy_inv`: the same
  identity transposed, with the two isomorphisms that the indexing comparison takes in the
  inverse direction moved to the other side. This is the form a consumer uses: its right-hand
  side is `Stacks.DerivedIndexing.extendMapHomologyIso`.
* `Stacks.DerivedIndexing.mapHomotopyCategoryHomologyIso_hom_app_quotient`,
  `Stacks.DerivedIndexing.extendHomotopyHomologyNatIso_hom_app_quotient`: the components of two
  of the three lifts at the class of a complex.

## Implementation notes

**The components of a `CategoryTheory.Quotient.natIsoLift`.** All three lifts are
`CategoryTheory.Quotient.natIsoLift`s, so each has, at the class of a complex, the component of
the datum it was lifted from — by `rfl`, since `HomotopyCategory.quotient` *is* the quotient
functor and `CategoryTheory.Quotient.natTransLift` is defined by cases on the object. The datum
of `mapExtendHomotopyNatIso` is the comparison of complexes and nothing else, which is
`mapExtendHomotopyNatIso_hom_app`; the data of the other two insert
`ComplexShape.Embedding.extendHomotopyFunctorFactors` resp.
`CategoryTheory.Functor.mapHomotopyCategoryFactors`, each of which is `CategoryTheory.Iso.refl`,
and `HomotopyCategory.homologyFunctorFactors`. The two lemmas here remove the first: the homology
functor applied to an identity morphism is an identity, which `rw` and `simp` cannot see — the
two objects agree only through semireducible definitions — and which is therefore taken in two
term-mode steps, a `congrArg` into `CategoryTheory.Functor.map_id`.

**The chase.** With the components in hand the identity is one naturality square for
`HomotopyCategory.homologyFunctorFactors`, the complex-level coherence
`homologyMap_mapExtendIso_hom_comp`, one splitting of `G.map` over a composite and one
cancellation of `HomotopyCategory.homologyFunctorFactors` against its inverse. These are pasted
by the file-scoped `chase_post`, stated at an arbitrary category with the objects implicit and
the morphisms explicit so that no pattern is ever matched against the goal. The splitting step
is term mode for the reason above: `rw [← Functor.map_comp]` on it reports that the rewrite
motive is not type-correct at `implicit` transparency, `(homologyFunctor B c' j').obj (M.extend
e)` and `(M.extend e).homology j'` being two spellings of one object.

**No natural-transformation form.** The identity is stated componentwise only. Reading it as an
equality of natural transformations would need the five whiskerings to compose, and
`(E ⋙ G) ⋙ H` and `E ⋙ (G ⋙ H)`, while definitionally equal, are not unifiable as applications
of `CategoryTheory.Functor.comp`; the consumers evaluate at an object anyway.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits HomologicalComplex

namespace Stacks.DerivedIndexing

universe v v' u u'

variable {B : Type u} {D : Type u'} [Category.{v} B] [Category.{v'} D] [Abelian B] [Abelian D]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (G : B ⥤ D) [G.Additive] [G.PreservesHomology]

/-- A functor applied to a morphism that is the identity (up to defeq of its endpoints) is
removed from a composite. -/
private lemma map_comp_eq_of_eq_id {C E : Type*} [Category* C] [Category* E] (F : C ⥤ E) {X : C}
    (f : X ⟶ X) (hf : f = 𝟙 X) {W : E} (w : F.obj X ⟶ W) : F.map f ≫ w = w := by
  simp [hf]

/-- **The components of `CategoryTheory.Functor.mapHomotopyCategoryHomologyIso` at the class of a
complex.** The identity morphism contributed by
`CategoryTheory.Functor.mapHomotopyCategoryFactors` is removed. -/
lemma mapHomotopyCategoryHomologyIso_hom_app_quotient (M : HomologicalComplex B c) (i : ι) :
    (G.mapHomotopyCategoryHomologyIso c i).hom.app ((HomotopyCategory.quotient B c).obj M) =
      (HomotopyCategory.homologyFunctorFactors D c i).hom.app
          ((G.mapHomologicalComplex c).obj M) ≫
        (mapExactHomologyIso G M i).hom ≫
          G.map ((HomotopyCategory.homologyFunctorFactors B c i).inv.app M) := by
  exact map_comp_eq_of_eq_id (HomotopyCategory.homologyFunctor D c i)
    ((G.mapHomotopyCategoryFactors c).hom.app M) rfl
    ((HomotopyCategory.homologyFunctorFactors D c i).hom.app
        ((G.mapHomologicalComplex c).obj M) ≫
      (mapExactHomologyIso G M i).hom ≫
        G.map ((HomotopyCategory.homologyFunctorFactors B c i).inv.app M))

section Factors

variable (e : c.Embedding c') [e.IsRelIff] {j : ι} {j' : ι'} (hj : e.f j = j')

/-- **The components of `extendHomotopyHomologyNatIso` at the class of a complex.** The identity
morphism contributed by `ComplexShape.Embedding.extendHomotopyFunctorFactors` is removed. -/
lemma extendHomotopyHomologyNatIso_hom_app_quotient (M : HomologicalComplex B c) :
    (extendHomotopyHomologyNatIso e hj).hom.app ((HomotopyCategory.quotient B c).obj M) =
      (HomotopyCategory.homologyFunctorFactors B c' j').hom.app (M.extend e) ≫
        (M.extendHomologyIso e hj).hom ≫
          (HomotopyCategory.homologyFunctorFactors B c j).inv.app M := by
  exact map_comp_eq_of_eq_id (HomotopyCategory.homologyFunctor B c' j')
    ((e.extendHomotopyFunctorFactors B).hom.app M) rfl
    ((HomotopyCategory.homologyFunctorFactors B c' j').hom.app (M.extend e) ≫
      (M.extendHomologyIso e hj).hom ≫
        (HomotopyCategory.homologyFunctorFactors B c j).inv.app M)

end Factors

/-- The chase behind `homologyMap_mapExtendHomotopyNatIso_hom_comp`: one naturality square, the
complex-level coherence, one splitting of a functor over a composite and one cancellation,
pasted. Stated at an arbitrary category with the objects implicit and the morphisms explicit. -/
private lemma chase_post {E : Type*} [Category* E]
    {S T U V V' R P Q Z W : E}
    (x : S ⟶ T) (y : T ⟶ U) (x' : S ⟶ P) (m : P ⟶ U) (a : U ⟶ V) (i : V ⟶ V') (k : V' ⟶ R)
    (b : V ⟶ W) (d : P ⟶ Q) (z : Q ⟶ Z) (z' : Z ⟶ Q) (f : Q ⟶ W) (l : W ⟶ R)
    (hnat : x ≫ y = x' ≫ m) (hkey : m ≫ a ≫ b = d ≫ f) (hsplit : i ≫ k = b ≫ l)
    (hcancel : z ≫ z' = 𝟙 Q) :
    x ≫ (y ≫ a ≫ i) ≫ k = (x' ≫ d ≫ z) ≫ z' ≫ f ≫ l := by
  simp only [Category.assoc, reassoc_of% hnat, hsplit, reassoc_of% hkey, reassoc_of% hcancel]

/-- A commuting square whose two right-hand edges are invertible, transposed to their inverses.
Stated at an arbitrary category with the objects implicit and the morphisms explicit. -/
private lemma comm_inv_transpose {E : Type*} [Category* E] {X₁ X₂ Y₁ Y₂ Y₃ : E}
    (u : X₁ ≅ Y₁) (a : X₁ ⟶ X₂) (b : X₂ ≅ Y₂) (d : Y₂ ≅ Y₃) (g : Y₁ ⟶ Y₃)
    (h : a ≫ b.hom ≫ d.hom = u.hom ≫ g) : g ≫ d.inv ≫ b.inv = u.inv ≫ a := by
  have h1 : u.hom ≫ g ≫ d.inv ≫ b.inv = a := by
    rw [← Category.assoc u.hom g, ← h]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← cancel_epi u.hom, h1, Iso.hom_inv_id_assoc]

section Main

variable (e : c.Embedding c') [e.IsRelIff] {j : ι} {j' : ι'} (hj : e.f j = j')

/-- `homologyMap_mapExtendHomotopyNatIso_hom_comp` at the class of a complex, with every object
spelled through the quotient functor so that the three component lemmas apply as rewrites. -/
private lemma homologyMap_mapExtendHomotopyNatIso_hom_comp_quotient (M : HomologicalComplex B c) :
    (HomotopyCategory.homologyFunctor D c' j').map
          ((mapExtendHomotopyNatIso G e).hom.app ((HomotopyCategory.quotient B c).obj M)) ≫
        (G.mapHomotopyCategoryHomologyIso c' j').hom.app
            ((HomotopyCategory.quotient B c').obj (M.extend e)) ≫
          G.map ((extendHomotopyHomologyNatIso e hj).hom.app
            ((HomotopyCategory.quotient B c).obj M)) =
      (extendHomotopyHomologyNatIso (A := D) e hj).hom.app
          ((HomotopyCategory.quotient D c).obj ((G.mapHomologicalComplex c).obj M)) ≫
        (G.mapHomotopyCategoryHomologyIso c j).hom.app
          ((HomotopyCategory.quotient B c).obj M) := by
  rw [mapExtendHomotopyNatIso_hom_app,
    mapHomotopyCategoryHomologyIso_hom_app_quotient G (M.extend e) j',
    mapHomotopyCategoryHomologyIso_hom_app_quotient G M j,
    extendHomotopyHomologyNatIso_hom_app_quotient e hj M,
    extendHomotopyHomologyNatIso_hom_app_quotient (B := D) e hj
      ((G.mapHomologicalComplex c).obj M)]
  exact chase_post _ _ _ _ _ _ _ _ _ _ _ _ _
    ((HomotopyCategory.homologyFunctorFactors D c' j').hom.naturality
      (mapExtendIso G e M).hom)
    (homologyMap_mapExtendIso_hom_comp G e M hj)
    (((G.map_comp ((HomotopyCategory.homologyFunctorFactors B c' j').inv.app (M.extend e))
          ((HomotopyCategory.homologyFunctorFactors B c' j').hom.app (M.extend e) ≫
            (M.extendHomologyIso e hj).hom ≫
              (HomotopyCategory.homologyFunctorFactors B c j).inv.app M)).symm.trans
        (congrArg G.map (Iso.inv_hom_id_app_assoc
          (HomotopyCategory.homologyFunctorFactors B c' j') (M.extend e)
          ((M.extendHomologyIso e hj).hom ≫
            (HomotopyCategory.homologyFunctorFactors B c j).inv.app M)))).trans
      (G.map_comp (M.extendHomologyIso e hj).hom
        ((HomotopyCategory.homologyFunctorFactors B c j).inv.app M)))
    ((HomotopyCategory.homologyFunctorFactors D c j).inv_hom_id_app
      ((G.mapHomologicalComplex c).obj M))

/-- **An exact functor commutes with the comparison of the homology of an extension by zero, read
on homotopy categories.** This is the homotopy-category form of
`homologyMap_mapExtendIso_hom_comp`: both routes from the degree-`j'` homology of the extension
by zero of `G` applied termwise to `K` to `G` applied to the degree-`j` homology of `K` agree. -/
theorem homologyMap_mapExtendHomotopyNatIso_hom_comp (K : HomotopyCategory B c) :
    (HomotopyCategory.homologyFunctor D c' j').map
          ((mapExtendHomotopyNatIso G e).hom.app K) ≫
        (G.mapHomotopyCategoryHomologyIso c' j').hom.app
            ((e.extendHomotopyFunctor B).obj K) ≫
          G.map ((extendHomotopyHomologyNatIso e hj).hom.app K) =
      (extendHomotopyHomologyNatIso (A := D) e hj).hom.app
          ((G.mapHomotopyCategory c).obj K) ≫
        (G.mapHomotopyCategoryHomologyIso c j).hom.app K := by
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  exact homologyMap_mapExtendHomotopyNatIso_hom_comp_quotient G e hj M

/-- **`homologyMap_mapExtendHomotopyNatIso_hom_comp`, transposed.** The two comparisons that the
indexing comparison uses in the inverse direction are moved to the other side, so that the
right-hand side is the composite `Stacks.DerivedIndexing.extendMapHomologyIso` is built from. -/
theorem mapHomotopyCategoryHomologyIso_comp_extendHomotopy_inv (K : HomotopyCategory B c) :
    (G.mapHomotopyCategoryHomologyIso c j).hom.app K ≫
        G.map ((extendHomotopyHomologyNatIso e hj).inv.app K) ≫
          (G.mapHomotopyCategoryHomologyIso c' j').inv.app
            ((e.extendHomotopyFunctor B).obj K) =
      (extendHomotopyHomologyNatIso (A := D) e hj).inv.app
          ((G.mapHomotopyCategory c).obj K) ≫
        (HomotopyCategory.homologyFunctor D c' j').map
          ((mapExtendHomotopyNatIso G e).hom.app K) :=
  comm_inv_transpose ((extendHomotopyHomologyNatIso (A := D) e hj).app
      ((G.mapHomotopyCategory c).obj K))
    ((HomotopyCategory.homologyFunctor D c' j').map
      ((mapExtendHomotopyNatIso G e).hom.app K))
    ((G.mapHomotopyCategoryHomologyIso c' j').app ((e.extendHomotopyFunctor B).obj K))
    (G.mapIso ((extendHomotopyHomologyNatIso e hj).app K))
    ((G.mapHomotopyCategoryHomologyIso c j).hom.app K)
    (homologyMap_mapExtendHomotopyNatIso_hom_comp G e hj K)

end Main

end Stacks.DerivedIndexing

end
