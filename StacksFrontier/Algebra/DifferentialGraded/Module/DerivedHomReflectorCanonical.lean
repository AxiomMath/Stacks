module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomFunctorAssembly
public import StacksFrontier.CategoryTheory.Triangulated.AdmissibleSubcategories

/-!
# The functor `R Hom(K, -) : D(A) ⥤ D(E, d)` of Tag 09LK does not depend on the reflector

The functor `CochainComplex.derivedHomReflectorFunctor` of [Stacks, Tag 09LK] is built from a
reflector `L` on `K(Mod^dg(Comp^dg A))` with unit `η : 𝟭 ⟶ L`, subject to two clauses: every
`L X` is `N`-local, and the cone of every `η.app X` lies in `N`. This file shows that the result
is canonical: any two such pairs `(L, η)`, `(L', η')` are related by a unique isomorphism
`L ≅ L'` carrying `η` to `η'`, and that isomorphism descends to an isomorphism of the functors
`D(A) ⥤ D(E, d)` built from them.

## Main definitions

* `CategoryTheory.ObjectProperty.reflectorIsoOfUnits`: the isomorphism `L ≅ L'` of two
  reflectors with units whose values are `N`-local and whose unit cones lie in `N`.
* `DGCategory.derivedHomReflectorIsoOfIso`: an isomorphism `L ≅ L'` induces an isomorphism of
  the functors `R̃ : D(A) ⥤ D(E)` of `DGCategory.derivedHomReflector` built from them.
* `CochainComplex.derivedHomReflectorFunctorIso`: the functor of Tag 09LK is isomorphic to the
  functor `DGCategory.phiReflector` built from any other reflector satisfying the clauses of
  steps 1 and 2.

## Main results

* `CategoryTheory.ObjectProperty.bijective_precomp_of_distTriang_mem`: precomposition with a
  morphism whose cone lies in a shift-stable `N` is bijective on morphisms into an `N`-local
  object.
* `CategoryTheory.ObjectProperty.unit_comp_reflectorIsoOfUnits_hom` and
  `CategoryTheory.ObjectProperty.eq_reflectorIsoOfUnits`: the isomorphism of reflectors carries
  `η` to `η'`, and it is the only one that does.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Pretriangulated

namespace CategoryTheory.ObjectProperty

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  (N : ObjectProperty C) [N.IsStableUnderShift ℤ]

/-- **Precomposition with a morphism whose cone lies in `N` is bijective into a local object.**
Let `N` be stable under shifts, let `u : X ⟶ Y` be a morphism such that the first vertex of every
distinguished triangle `Z ⟶ X ⟶ Y ⟶ Z⟦1⟧` on `u` lies in `N`, and let `W` be `N`-local. Then
`φ ↦ u ≫ φ` is a bijection `(Y ⟶ W) → (X ⟶ W)`. -/
theorem bijective_precomp_of_distTriang_mem {X Y W : C} (u : X ⟶ Y)
    (hW : N.rightOrthogonal W)
    (hu : ∀ (Z : C) (f : Z ⟶ X) (g : Y ⟶ Z⟦(1 : ℤ)⟧),
      Triangle.mk f u g ∈ distTriang C → N Z) :
    Function.Bijective (fun φ : Y ⟶ W ↦ u ≫ φ) := by
  obtain ⟨Z, f, g, hT⟩ := distinguished_cocone_triangle₁ u
  have hB : Stacks.Triangulated.AdmissibleSubcategories.ShiftInvariant
      (fun V : C ↦ N.rightOrthogonal V) := fun V hV n ↦ N.rightOrthogonal.le_shift n V hV
  exact (Stacks.Triangulated.AdmissibleSubcategories.isLeftOrthogonal_iff_bijective_precompMap
    (fun V : C ↦ N.rightOrthogonal V) hB (Triangle.mk f u g) hT).1
    (fun V hV φ ↦ hV φ (hu Z f g hT)) W hW

variable {N} {L L' : C ⥤ C} (η : 𝟭 C ⟶ L) (η' : 𝟭 C ⟶ L')

/-- The comparison `L X ⟶ L' X` of two reflectors: the unique morphism through which `η'.app X`
factors along `η.app X`. -/
def reflectorCompare
    (hη : ∀ (X Z : C) (f : Z ⟶ X) (g : L.obj X ⟶ Z⟦(1 : ℤ)⟧),
      Triangle.mk f (η.app X) g ∈ distTriang C → N Z)
    (hL' : ∀ X, N.rightOrthogonal (L'.obj X)) (X : C) : L.obj X ⟶ L'.obj X :=
  ((N.bijective_precomp_of_distTriang_mem (η.app X) (hL' X) (hη X)).2 (η'.app X)).choose

@[reassoc (attr := simp)]
lemma unit_comp_reflectorCompare
    (hη : ∀ (X Z : C) (f : Z ⟶ X) (g : L.obj X ⟶ Z⟦(1 : ℤ)⟧),
      Triangle.mk f (η.app X) g ∈ distTriang C → N Z)
    (hL' : ∀ X, N.rightOrthogonal (L'.obj X)) (X : C) :
    η.app X ≫ reflectorCompare η η' hη hL' X = η'.app X :=
  ((N.bijective_precomp_of_distTriang_mem (η.app X) (hL' X) (hη X)).2 (η'.app X)).choose_spec

variable (hL : ∀ X, N.rightOrthogonal (L.obj X))
  (hη : ∀ (X Z : C) (f : Z ⟶ X) (g : L.obj X ⟶ Z⟦(1 : ℤ)⟧),
    Triangle.mk f (η.app X) g ∈ distTriang C → N Z)
  (hL' : ∀ X, N.rightOrthogonal (L'.obj X))
  (hη' : ∀ (X Z : C) (f : Z ⟶ X) (g : L'.obj X ⟶ Z⟦(1 : ℤ)⟧),
    Triangle.mk f (η'.app X) g ∈ distTriang C → N Z)

include hL hη hL' hη' in
/-- **Two reflectors with units are isomorphic.** If every `L X` and every `L' X` is `N`-local,
and the cones of the units `η.app X` and `η'.app X` lie in `N`, then `L ≅ L'`, by the
isomorphism characterised by `η.app X ≫ e.hom.app X = η'.app X`. -/
def reflectorIsoOfUnits : L ≅ L' :=
  NatIso.ofComponents
    (fun X ↦
      { hom := reflectorCompare η η' hη hL' X
        inv := reflectorCompare η' η hη' hL X
        hom_inv_id := (N.bijective_precomp_of_distTriang_mem (η.app X) (hL X) (hη X)).1
          ((unit_comp_reflectorCompare_assoc η η' hη hL' X _).trans
            ((unit_comp_reflectorCompare η' η hη' hL X).trans (comp_id _).symm))
        inv_hom_id := (N.bijective_precomp_of_distTriang_mem (η'.app X) (hL' X) (hη' X)).1
          ((unit_comp_reflectorCompare_assoc η' η hη' hL X _).trans
            ((unit_comp_reflectorCompare η η' hη hL' X).trans (comp_id _).symm)) })
    (fun {X Y} f ↦ (N.bijective_precomp_of_distTriang_mem (η.app X) (hL' Y) (hη X)).1
      (calc η.app X ≫ L.map f ≫ reflectorCompare η η' hη hL' Y
          = (η.app X ≫ L.map f) ≫ reflectorCompare η η' hη hL' Y := (assoc _ _ _).symm
        _ = ((𝟭 C).map f ≫ η.app Y) ≫ reflectorCompare η η' hη hL' Y :=
          congrArg (· ≫ reflectorCompare η η' hη hL' Y) (η.naturality f).symm
        _ = (𝟭 C).map f ≫ η'.app Y :=
          (assoc _ _ _).trans
            (congrArg ((𝟭 C).map f ≫ ·) (unit_comp_reflectorCompare η η' hη hL' Y))
        _ = η'.app X ≫ L'.map f := η'.naturality f
        _ = η.app X ≫ reflectorCompare η η' hη hL' X ≫ L'.map f :=
          (unit_comp_reflectorCompare_assoc η η' hη hL' X _).symm))

include hL hη hL' hη' in
@[reassoc (attr := simp)]
lemma unit_comp_reflectorIsoOfUnits_hom (X : C) :
    η.app X ≫ (reflectorIsoOfUnits η η' hL hη hL' hη').hom.app X = η'.app X :=
  unit_comp_reflectorCompare η η' hη hL' X

include hL hη hL' hη' in
/-- **The isomorphism of reflectors is unique**: any natural transformation `L ⟶ L'` carrying
`η` to `η'` is the one of `CategoryTheory.ObjectProperty.reflectorIsoOfUnits`. -/
theorem eq_reflectorIsoOfUnits (τ : L ⟶ L') (hτ : ∀ X, η.app X ≫ τ.app X = η'.app X) :
    τ = (reflectorIsoOfUnits η η' hL hη hL' hη').hom := by
  ext X
  exact (N.bijective_precomp_of_distTriang_mem (η.app X) (hL' X) (hη X)).1
    ((hτ X).trans (unit_comp_reflectorIsoOfUnits_hom η η' hL hη hL' hη' X).symm)

end CategoryTheory.ObjectProperty

namespace DGCategory

universe v₂ u₂ v₁ u₁ v u r

variable {R : Type r} [CommRing R] (C : DGCategory.{v, u} R) (K : C.Obj)
  {L L' : (rightModuleCategory.{v} C).K ⥤ (rightModuleCategory.{v} C).K}
  [L.CommShift ℤ] [L.IsTriangulated] [L'.CommShift ℤ] [L'.IsTriangulated]
  {S : Type u₁} [Category.{v₁} S] [HasZeroObject S] [HasShift S ℤ] [Preadditive S]
  [∀ n : ℤ, (shiftFunctor S n).Additive] [Pretriangulated S] [IsTriangulated S]
  (Φ : S ⥤ (rightModuleCategory.{v} C).K) [Φ.CommShift ℤ] [Φ.IsTriangulated]
  (Z : ObjectProperty S) [Z.IsTriangulated]
  {DA : Type u₂} [Category.{v₂} DA] [HasZeroObject DA] [HasShift DA ℤ] [Preadditive DA]
  [∀ n : ℤ, (shiftFunctor DA n).Additive] [Pretriangulated DA]
  (q : S ⥤ DA) [q.IsLocalization Z.trW] [q.CommShift ℤ] [q.IsTriangulated]

/-- **An isomorphism of reflectors induces an isomorphism of the functors `R̃ : D(A) ⥤ D(E)`.**
The descents `J` of `X ↦ L (Φ X)` and of `X ↦ L' (Φ X)` through the localization `q` are
related by the lift of the isomorphism `Φ ⋙ L ⋙ Q ≅ Φ ⋙ L' ⋙ Q` that `e` induces, and
`R̃ = J ⋙ ev_K`. -/
def derivedHomReflectorIsoOfIso (e : L ≅ L')
    (hΦ : ∀ X, Z X → IsZero ((Φ ⋙ L).obj X)) (hΦ' : ∀ X, Z X → IsZero ((Φ ⋙ L').obj X)) :
    derivedHomReflector C K L Φ Z q hΦ ≅ derivedHomReflector C K L' Φ Z q hΦ' :=
  Functor.isoWhiskerRight
    (Localization.liftNatIso q Z.trW (Φ ⋙ L ⋙ RightModule.derivedQ C)
      (Φ ⋙ L' ⋙ RightModule.derivedQ C) (derivedReflectorDescent C L Φ Z q hΦ)
      (derivedReflectorDescent C L' Φ Z q hΦ')
      (Functor.isoWhiskerLeft Φ (Functor.isoWhiskerRight e (RightModule.derivedQ C))))
    (derivedEvaluation C K)

end DGCategory

namespace CochainComplex

universe v

variable (A : Type) [Category.{0} A] [Abelian A]
  [((DGCategory.yonedaDGFunctor (CochainComplex.dgCategory A)).onK).CommShift ℤ]
  [((DGCategory.yonedaDGFunctor (CochainComplex.dgCategory A)).onK).IsTriangulated]
  (K : CochainComplex A ℤ) [HasDerivedCategory.{v} A]

/-- **The functor `R Hom(K, -) : D(A) ⥤ D(E, d)` of [Stacks, Tag 09LK] is canonical.** Let `L'`
be any exact reflector on `K(Mod^dg(Comp^dg A))` with a unit `η'` satisfying the clauses of
steps 1 and 2: every `L' X` is local, the cone of every `η'.app X` lies in `N`, and `L'` kills
the preimage of `N`. Then the functor `DGCategory.phiReflector` built from `L'` is isomorphic to
`CochainComplex.derivedHomReflectorFunctor`, through the isomorphism of reflectors
`CategoryTheory.ObjectProperty.reflectorIsoOfUnits`, which is the unique one compatible with the
units (`CategoryTheory.ObjectProperty.eq_reflectorIsoOfUnits`). -/
@[stacks 09LK "canonicity of R Hom(K, -) : D(A) ⥤ D(E, d): the functor is independent of the \
reflector used to construct it, up to the isomorphism induced by the unique isomorphism of \
reflectors compatible with the units"]
def derivedHomReflectorFunctorIso
    (L' : derivedHomModuleK A ⥤ derivedHomModuleK A)
    [L'.CommShift ℤ] [L'.IsTriangulated] (η' : 𝟭 _ ⟶ L')
    (hL' : ∀ X, (DGCategory.RightModule.yonedaLocalizing (CochainComplex.dgCategory A)
      (DGCategory.phiGen A)).rightOrthogonal (L'.obj X))
    (hη' : ∀ (X Z : derivedHomModuleK A) (f : Z ⟶ X)
      (g : L'.obj X ⟶ Z⟦(1 : ℤ)⟧),
      Triangle.mk f (η'.app X) g ∈ distTriang (derivedHomModuleK A) →
        DGCategory.RightModule.yonedaLocalizing (CochainComplex.dgCategory A)
          (DGCategory.phiGen A) Z)
    (hΦ' : ∀ X, DGCategory.RightModule.yonedaInverseImage (CochainComplex.dgCategory A)
      (DGCategory.phiGen A) X →
      IsZero ((((DGCategory.yonedaDGFunctor (CochainComplex.dgCategory A)).onK) ⋙ L').obj X)) :
    derivedHomReflectorFunctor A K ≅ DGCategory.phiReflector A K L' hΦ' :=
  DGCategory.derivedHomReflectorIsoOfIso (CochainComplex.dgCategory A) K _ _ _
    (ObjectProperty.reflectorIsoOfUnits (derivedHomReflectorEta A) η'
      (derivedHomReflector_local A) (derivedHomReflector_cone A) hL' hη')
    (derivedHomReflector_isZero A) hΦ'

end CochainComplex

end
