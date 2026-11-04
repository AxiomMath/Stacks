module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.HomComplexFromSingle
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.RightDerivedSheafToPresheaf

/-!
# The Hom complex out of a single complex, naturally in the second variable

`CochainComplex.HomComplex.homComplexSingleIsoCoyonedaComplex` identifies the Hom complex out of
`X[0]` with the degreewise `Hom(X, -)`. This file records that the identification is natural in
the second variable: it carries postcomposition with `g : L ⟶ L'` on Hom complexes
(`homComplexPostcomp`) to the map `((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex _).map
g` induced degreewise.

Degreewise both maps are `φ ↦ φ ≫ g.f n` once a cochain out of `X[0]` has been read as a map out
of `X`, which is `fromSingleEquiv_comp_ofHom`: composing a cochain with `Cochain.ofHom g`
composes its one nonzero component with `g`.

The consequence used downstream is `isIso_homologyMap_coyonedaComplexMap_iff`: the degree-`n`
homology maps of the two complexes are invertible together. Composed with
`isIso_homologyMap_homComplexPostcomp` this turns a statement about postcomposition in the
homotopy category into invertibility of the homology of a degreewise `Hom(X, -)` — and hence,
for a sections functor, into a quasi-isomorphism of complexes of sections.

## Main results

* `CochainComplex.HomComplex.fromSingleEquiv_comp_ofHom`: reading a cochain out of `X[0]` as a
  map out of `X` carries composition with `Cochain.ofHom g` to composition with `g`.
* `CochainComplex.HomComplex.homComplexSingleIsoCoyonedaComplex_naturality`: the square.
* `CochainComplex.HomComplex.isIso_homologyMap_coyonedaComplexMap_iff`: the two homology maps
  are invertible together.
-/

@[expose] public section

open CategoryTheory Category Limits Preadditive Opposite

universe v u

namespace CochainComplex.HomComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- **Composing a cochain out of `X[0]` with `Cochain.ofHom g`.** Under the identification of a
degree-`n` cochain `X[0] ⟶ L` with a map `X ⟶ L.X n`, composition with `Cochain.ofHom g` is
composition with `g.f n`: a cochain out of a single complex has one nonzero component. -/
theorem fromSingleEquiv_comp_ofHom {X : A} {L L' : CochainComplex A ℤ} (g : L ⟶ L') (n : ℤ)
    (z : Cochain ((singleFunctor A 0).obj X) L n) :
    Cochain.fromSingleEquiv (zero_add n) (z.comp (Cochain.ofHom g) (add_zero n)) =
      Cochain.fromSingleEquiv (zero_add n) z ≫ g.f n := by
  dsimp only [Cochain.fromSingleEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk]
  rw [Cochain.comp_v z (Cochain.ofHom g) (add_zero n) 0 n n (zero_add n) (add_zero n),
    Cochain.ofHom_v, assoc]

/-- **The identification of the Hom complex out of `X[0]` with the degreewise `Hom(X, -)` is
natural in the second variable.** It carries `homComplexPostcomp` to the map induced degreewise
by `g`. -/
theorem homComplexSingleIsoCoyonedaComplex_naturality (X : A) {L L' : CochainComplex A ℤ}
    (g : L ⟶ L') :
    (homComplexSingleIsoCoyonedaComplex X L).hom ≫
        ((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (ComplexShape.up ℤ)).map g =
      homComplexPostcomp ((singleFunctor A 0).obj X) g ≫
        (homComplexSingleIsoCoyonedaComplex X L').hom := by
  ext n z
  exact (fromSingleEquiv_comp_ofHom g n z).symm

/-- Invertibility of the degree-`n` homology of `homComplexPostcomp` transports along the
identification to the map induced degreewise by `g` on `Hom(X, -)`. -/
theorem isIso_homologyMap_coyonedaComplexMap (X : A) {L L' : CochainComplex A ℤ}
    (g : L ⟶ L') (n : ℤ)
    [IsIso (HomologicalComplex.homologyMap
      (homComplexPostcomp ((singleFunctor A 0).obj X) g) n)] :
    IsIso (HomologicalComplex.homologyMap
      (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (ComplexShape.up ℤ)).map g) n) := by
  have hi (M : CochainComplex A ℤ) : IsIso (HomologicalComplex.homologyMap
      (homComplexSingleIsoCoyonedaComplex X M).hom n) :=
    inferInstanceAs (IsIso ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v}
      (ComplexShape.up ℤ) n).map (homComplexSingleIsoCoyonedaComplex X M).hom))
  have h := congrArg (fun φ => HomologicalComplex.homologyMap φ n)
    (homComplexSingleIsoCoyonedaComplex_naturality X g)
  simp only [HomologicalComplex.homologyMap_comp] at h
  have key : HomologicalComplex.homologyMap
      (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (ComplexShape.up ℤ)).map g) n =
      inv (HomologicalComplex.homologyMap (homComplexSingleIsoCoyonedaComplex X L).hom n) ≫
        HomologicalComplex.homologyMap
            (homComplexPostcomp ((singleFunctor A 0).obj X) g) n ≫
          HomologicalComplex.homologyMap
            (homComplexSingleIsoCoyonedaComplex X L').hom n := by
    rw [← h, IsIso.inv_hom_id_assoc]
  rw [key]
  infer_instance

end CochainComplex.HomComplex

end
