module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.SheavesOfRings.SectionsComparisonNaturality
public import StacksFrontier.Cotangent.SheavesOfRings.SquareFunctoriality

/-!
# Naturality in squares of the comparison of sections of Stacks 08SX

Let `C` be a site and let `a : A ⟶ A'`, `b : B ⟶ B'` be a commutative square between two
homomorphisms `f : A ⟶ B` and `f' : A' ⟶ B'` of sheaves of commutative rings on `C`. Over every
object `U` of the site the square restricts to a commutative square of ring maps
`A(U) → A'(U)`, `B(U) → B'(U)`, so there are two ways to go from the cotangent complex
`L_{B(U)/A(U)}` of the ring map on sections to the sections over `U` of `L_{B'/A'}`:

* the canonical map `L_{B(U)/A(U)} ⟶ L_{B/A}(U)` of Remark 08SX followed by the sections over
  `U` of the map `L_{B/A} ⟶ L_{B'/A'}` that the square induces on cotangent complexes of sheaves;
* the map `L_{B(U)/A(U)} ⟶ L_{B'(U)/A'(U)}` that the square of ring maps induces on cotangent
  complexes of rings, followed by the canonical map `L_{B'(U)/A'(U)} ⟶ L_{B'/A'}(U)`.

This file proves that the two agree. It is the counterpart for squares of the naturality in `U`
proved in `StacksFrontier.Cotangent.SheavesOfRings.SectionsComparisonNaturality`, and it is what
compares a map of cotangent complexes of sheaves of rings, such as the comparison map of
Tag 08SY, with the sectionwise maps of cotangent complexes of rings.

## Main definitions

* `CategoryTheory.Sheaf.sectionsSquare` is the commutative square of ring maps on sections over
  `U`.
* `CategoryTheory.Sheaf.sectionsSquareHom` is a morphism of sheaves of `A`-algebras into a sheaf
  of `A'`-algebras read over `A`, taken on sections over `U`.

## Main results

* `CategoryTheory.Sheaf.standardResolutionComonadSquareHom_variable`: the comparison of the two
  free–forgetful comonads sends the image of a section under the unit over `A` to its image
  under the unit over `A'`.
* `CategoryTheory.Sheaf.resolutionSectionsComparison_square`: **the naturality square in squares
  of the comparison of standard resolutions of Tag 08SX.**
* `CategoryTheory.Sheaf.sectionsCotangentComplexComparison_square_degree` and
  `CategoryTheory.Sheaf.sectionsCotangentComplexComparison_square`: **the canonical maps
  `L_{B(U)/A(U)} ⟶ L_{B/A}(U)` of Tag 08SX commute with the maps induced by a square**, in every
  cohomological degree.

## Implementation notes

As for the naturality in `U`, the comparison of the free sides of the two squares of adjunctions
is only lax, so the two composites of ring homomorphisms out of each stage of the tower of
iterated polynomial algebras are compared on the base ring and on the variables
(`CommAlgCat.standardTower_succ_hom_ext`), and the statement is propagated up the tower by
induction. On a variable the sheaf-level comparison of comonads is read off its transpose
`CategoryTheory.Adjunction.unit_comp_map_comonadSquareHom`, which says that it carries the unit
over `A` to the unit over `A'`.

## References

* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 08SY](https://stacks.math.columbia.edu/tag/08SY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace CategoryTheory.Functor

universe v₁ u₁ v₂ u₂

variable {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]
  {G : D ⥤ D} {G' : E ⥤ E} {K : E ⥤ D}

/-- The recursion satisfied by the transported iterated comparison: the next stage is the image
of the previous one under the endofunctor, followed by the comparison. -/
lemma iterateCompHomObj_succ (e : K ⋙ G ⟶ G' ⋙ K) (n : ℕ) {X : D} {Z : E}
    (u : X ⟶ K.obj Z) :
    Functor.iterateCompHomObj e (n + 1) u =
      G.map (Functor.iterateCompHomObj e n u) ≫ e.app ((G'.iterate n).obj Z) := by
  rw [Functor.iterateCompHomObj, Functor.iterateCompHomObj, Functor.iterateCompHom_succ_app,
    G.map_comp, Category.assoc]
  rfl

end CategoryTheory.Functor

namespace CommAlgCat

universe u v w

variable {A : Type u} [CommRing A] {A' : Type w} [CommRing A']
  {B : CommAlgCat.{max u w v} A} {B' : CommAlgCat.{max u w v} A'}

/-- The map of cotangent complexes of rings induced by a square, in cohomological degree `-n`,
evaluated on an element of the degree-`n` term of base-changed differentials read in that
degree. -/
theorem squareCotangentComplexMap_degreeIso_inv (sq : AlgebraSquare.{u, v, w} A A' B B') (n : ℕ)
    (z : cotangentTerm.{u, max w v} A B (op ⦋n⦌)) :
    (squareCotangentComplexMap.{u, v, w} sq).f (-(n : ℤ))
        ((cotangentComplex_degreeIso.{u, max w v} A B n).inv z) =
      (cotangentComplex_degreeIso.{w, max u v} A' B' n).inv
        (squareCotangentTermMap.{u, v, w} sq (op ⦋n⦌) z) := by
  have h : (cotangentComplex_degreeIso.{u, max w v} A B n).inv ≫
      (squareCotangentComplexMap.{u, v, w} sq).f (-(n : ℤ)) =
      squareCotangentTermMap.{u, v, w} sq (op ⦋n⦌) ≫
        (ModuleCat.restrictScalars sq.map).map
          (cotangentComplex_degreeIso.{w, max u v} A' B' n).inv := by
    rw [squareCotangentComplexMap_f, Iso.inv_hom_id_assoc]
  exact ConcreteCategory.congr_hom h z

end CommAlgCat

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A A' B B' : Sheaf J CommRingCat.{max u v w}} {f : A ⟶ B} {f' : A' ⟶ B'}

/-! ## The square on sections -/

section Sections

variable (a : A ⟶ A')

/-- A morphism of sheaves of `A`-algebras into a sheaf of `A'`-algebras read over `A` along
`a : A ⟶ A'`, taken on sections over `U`. -/
noncomputable def sectionsSquareHom (U : Cᵒᵖ) {X : Under A} {Y : Under A'}
    (φ : X ⟶ (squareAlgebras J a).obj Y) :
    (sectionsAlgebraFunctor J U (A := A)).obj X →+*
      (sectionsAlgebraFunctor J U (A := A')).obj Y :=
  (φ.right.hom.app U).hom

/-- On sections, a morphism into a sheaf of `A'`-algebras read over `A` carries the image of the
base ring `A(U)` to the image of `A'(U)`, along `a`. -/
lemma sectionsSquareHom_algebraMap (U : Cᵒᵖ) {X : Under A} {Y : Under A'}
    (φ : X ⟶ (squareAlgebras J a).obj Y) (x : A.obj.obj U) :
    sectionsSquareHom J a U φ
        (algebraMap (A.obj.obj U) ((sectionsAlgebraFunctor J U (A := A)).obj X) x) =
      algebraMap (A'.obj.obj U) ((sectionsAlgebraFunctor J U (A := A')).obj Y)
        ((a.hom.app U).hom x) :=
  congrArg (fun k : A ⟶ Y.right => (k.hom.app U).hom x) (Under.w φ)

/-- On sections, the comparison of the two free–forgetful comonads attached to `a : A ⟶ A'`
sends the image of a section under the unit of the free–forgetful adjunction over `A` to its
image under the unit over `A'`. -/
theorem standardResolutionComonadSquareHom_variable (U : Cᵒᵖ) (Z : Under A')
    (x : (sectionsOfSets J U).obj ((forgetAlgebraSheaf.{v, u, w} J A').obj Z)) :
    sectionsSquareHom J a U ((standardResolutionComonadSquareHom.{u, v, w} J a).app Z)
        ((sectionsOfSets J U).map ((freeAlgebraSheafAdjunction.{v, u, w} J A).unit.app
          ((forgetAlgebraSheaf.{v, u, w} J A).obj ((squareAlgebras J a).obj Z))) x) =
      (sectionsOfSets J U).map ((freeAlgebraSheafAdjunction.{v, u, w} J A').unit.app
        ((forgetAlgebraSheaf.{v, u, w} J A').obj Z)) x := by
  have h := congrArg (fun k => (sectionsOfSets J U).map k x)
    (Adjunction.unit_comp_map_comonadSquareHom (F := freeAlgebraSheaf.{v, u, w} J A)
      (U := forgetAlgebraSheaf.{v, u, w} J A) (F' := freeAlgebraSheaf.{v, u, w} J A')
      (U' := forgetAlgebraSheaf.{v, u, w} J A') (K := squareAlgebras J a)
      (freeAlgebraSheafAdjunction.{v, u, w} J A) (freeAlgebraSheafAdjunction.{v, u, w} J A')
      (Iso.refl _) Z)
  simp only [Iso.refl_hom, Iso.refl_inv, NatTrans.id_app] at h
  exact h

/-- On sections, the unit of the free–forgetful adjunction over `A` is natural. -/
lemma freeAlgebraSheafAdjunction_unit_sections (U : Cᵒᵖ) {X Y : Under A} (φ : X ⟶ Y)
    (x : (sectionsOfSets J U).obj ((forgetAlgebraSheaf.{v, u, w} J A).obj X)) :
    (sectionsOfSets J U).map ((forgetAlgebraSheaf.{v, u, w} J A).map
        ((standardResolutionComonad.{v, u, w} J A : Under A ⥤ Under A).map φ))
      ((sectionsOfSets J U).map ((freeAlgebraSheafAdjunction.{v, u, w} J A).unit.app
        ((forgetAlgebraSheaf.{v, u, w} J A).obj X)) x) =
    (sectionsOfSets J U).map ((freeAlgebraSheafAdjunction.{v, u, w} J A).unit.app
        ((forgetAlgebraSheaf.{v, u, w} J A).obj Y))
      ((sectionsOfSets J U).map ((forgetAlgebraSheaf.{v, u, w} J A).map φ) x) := by
  have h := congrArg (fun k => (sectionsOfSets J U).map k x)
    ((freeAlgebraSheafAdjunction.{v, u, w} J A).unit.naturality
      ((forgetAlgebraSheaf.{v, u, w} J A).map φ))
  simp only [Functor.map_comp, types_comp_apply] at h
  exact h.symm

end Sections

section Square

variable (a : A ⟶ A') (b : B ⟶ B') (hsq : f ≫ b = a ≫ f')

/-- The commutative square of ring maps `A(U) → A'(U)`, `B(U) → B'(U)` obtained by taking
sections over `U` of a commutative square of homomorphisms of sheaves of commutative rings. -/
noncomputable def sectionsSquare (U : Cᵒᵖ) :
    CommAlgCat.AlgebraSquare.{max u v w, max u v w, max u v w}
      (A.obj.obj U) (A'.obj.obj U) (sectionsAlgebra J f U) (sectionsAlgebra J f' U) where
  base := (a.hom.app U).hom
  map := (b.hom.app U).hom
  map_algebraMap x := by
    change (b.hom.app U).hom ((f.hom.app U).hom x) = (f'.hom.app U).hom ((a.hom.app U).hom x)
    exact congrArg (fun k : A ⟶ B' => (k.hom.app U).hom x) hsq

/-- **The iterated comparison of comonads is natural in squares on sections.** On the stage-`n`
tower of iterated polynomial algebras over `A(U)`, the iterated comparison of the free–forgetful
comonads attached to `a`, taken on sections, intertwines the two iterated comparisons of
Tag 08SX, the ring-level map being the tower map of the square on sections. -/
theorem iterateCompHomObj_sectionsComonadLax (U : Cᵒᵖ) (n : ℕ)
    (q : CommAlgCat.standardTower.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U) n) :
    sectionsSquareHom J a U (Functor.iterateCompHomObj
        (standardResolutionComonadSquareHom.{u, v, w} J a) n
        (squareAlgebraMap.{u, v, w} J a b hsq))
      (((Functor.iterateLaxHom (sectionsComonadLax J U) n).app (Under.mk f)).hom q) =
    ((Functor.iterateLaxHom (sectionsComonadLax J (A := A') U) n).app (Under.mk f')).hom
      (CommAlgCat.standardTowerMap.{max u v w, max u v w, max u v w}
        (sectionsSquare J a b hsq U) n q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have key : (sectionsSquareHom J a U (Functor.iterateCompHomObj
          (standardResolutionComonadSquareHom.{u, v, w} J a) (n + 1)
          (squareAlgebraMap.{u, v, w} J a b hsq))).comp
        ((Functor.iterateLaxHom (sectionsComonadLax J U) (n + 1)).app
          (Under.mk f)).hom.toRingHom =
      (((Functor.iterateLaxHom (sectionsComonadLax J (A := A') U) (n + 1)).app
          (Under.mk f')).hom.toRingHom).comp
        (CommAlgCat.standardTowerMap.{max u v w, max u v w, max u v w}
          (sectionsSquare J a b hsq U) (n + 1)) := by
      refine CommAlgCat.standardTower_succ_hom_ext.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U) n (fun x => ?_) (fun q' => ?_)
      · have h1 := ((Functor.iterateLaxHom (sectionsComonadLax J U) (n + 1)).app
          (Under.mk f)).hom.commutes x
        have h2 := CommAlgCat.standardTowerMap_algebraMap.{max u v w, max u v w, max u v w}
          (sectionsSquare J a b hsq U) (n + 1) x
        have h3 := ((Functor.iterateLaxHom (sectionsComonadLax J (A := A') U) (n + 1)).app
          (Under.mk f')).hom.commutes ((a.hom.app U).hom x)
        refine (RingHom.comp_apply _ _ _).trans (Eq.trans ?_ (RingHom.comp_apply _ _ _).symm)
        show sectionsSquareHom J a U (Functor.iterateCompHomObj
              (standardResolutionComonadSquareHom.{u, v, w} J a) (n + 1)
              (squareAlgebraMap.{u, v, w} J a b hsq))
            (((Functor.iterateLaxHom (sectionsComonadLax J U) (n + 1)).app
              (Under.mk f)).hom (algebraMap (A.obj.obj U) _ x)) =
          ((Functor.iterateLaxHom (sectionsComonadLax J (A := A') U) (n + 1)).app
              (Under.mk f')).hom
            (CommAlgCat.standardTowerMap.{max u v w, max u v w, max u v w}
              (sectionsSquare J a b hsq U) (n + 1) (algebraMap (A.obj.obj U) _ x))
        rw [h1, h2]
        exact (sectionsSquareHom_algebraMap J a U _ x).trans h3.symm
      · -- the stage `n + 1` of the sheaf-level iterated comparison, applied to the image of a
        -- variable: first the unit over `A`, then the comparison of comonads.
        have hL : ((Functor.iterateLaxHom (sectionsComonadLax J U) (n + 1)).app
              (Under.mk f)).hom (CommAlgCat.standardTowerX.{max u v w, max u v w}
                (A.obj.obj U) (sectionsAlgebra J f U) n q') =
            (sectionsOfSets J U).map ((freeAlgebraSheafAdjunction.{v, u, w} J A).unit.app
              ((forgetAlgebraSheaf.{v, u, w} J A).obj
                ((((standardResolutionComonad.{v, u, w} J A : Comonad (Under A)) :
                  Under A ⥤ Under A).iterate n).obj (Under.mk f))))
              (((Functor.iterateLaxHom (sectionsComonadLax J U) n).app (Under.mk f)).hom q') :=
          (iterateSectionsComonadLax_succ_apply J f U n _).trans
            ((congrArg (fun z => ((sectionsComonadLax J U).app
                ((((standardResolutionComonad.{v, u, w} J A : Comonad (Under A)) :
                  Under A ⥤ Under A).iterate n).obj (Under.mk f))).hom z)
              (CommAlgCat.polynomialComonad_map_X.{max u v w, max u v w} (A.obj.obj U)
                ((Functor.iterateLaxHom (sectionsComonadLax J U) n).app (Under.mk f)) q')).trans
              (sectionsComonadLax_variable J U _ _))
        have hR : ((Functor.iterateLaxHom (sectionsComonadLax J (A := A') U) (n + 1)).app
              (Under.mk f')).hom
                (CommAlgCat.standardTowerMap.{max u v w, max u v w, max u v w}
                  (sectionsSquare J a b hsq U) (n + 1)
                  (CommAlgCat.standardTowerX.{max u v w, max u v w}
                    (A.obj.obj U) (sectionsAlgebra J f U) n q')) =
            (sectionsOfSets J U).map ((freeAlgebraSheafAdjunction.{v, u, w} J A').unit.app
              ((forgetAlgebraSheaf.{v, u, w} J A').obj
                ((((standardResolutionComonad.{v, u, w} J A' : Comonad (Under A')) :
                  Under A' ⥤ Under A').iterate n).obj (Under.mk f'))))
              (((Functor.iterateLaxHom (sectionsComonadLax J (A := A') U) n).app
                (Under.mk f')).hom
                (CommAlgCat.standardTowerMap.{max u v w, max u v w, max u v w}
                  (sectionsSquare J a b hsq U) n q')) :=
          (congrArg (fun z => ((Functor.iterateLaxHom (sectionsComonadLax J (A := A') U)
              (n + 1)).app (Under.mk f')).hom z)
            (CommAlgCat.standardTowerMap_standardTowerX.{max u v w, max u v w, max u v w}
              (sectionsSquare J a b hsq U) n q')).trans
          ((iterateSectionsComonadLax_succ_apply J f' U n _).trans
            ((congrArg (fun z => ((sectionsComonadLax J (A := A') U).app
                ((((standardResolutionComonad.{v, u, w} J A' : Comonad (Under A')) :
                  Under A' ⥤ Under A').iterate n).obj (Under.mk f'))).hom z)
              (CommAlgCat.polynomialComonad_map_X.{max u v w, max u v w} (A'.obj.obj U)
                ((Functor.iterateLaxHom (sectionsComonadLax J (A := A') U) n).app
                  (Under.mk f')) _)).trans
              (sectionsComonadLax_variable J U _ _)))
        refine (RingHom.comp_apply _ _ _).trans (Eq.trans ?_ (RingHom.comp_apply _ _ _).symm)
        show sectionsSquareHom J a U (Functor.iterateCompHomObj
              (standardResolutionComonadSquareHom.{u, v, w} J a) (n + 1)
              (squareAlgebraMap.{u, v, w} J a b hsq))
            (((Functor.iterateLaxHom (sectionsComonadLax J U) (n + 1)).app
              (Under.mk f)).hom (CommAlgCat.standardTowerX.{max u v w, max u v w}
                (A.obj.obj U) (sectionsAlgebra J f U) n q')) =
          ((Functor.iterateLaxHom (sectionsComonadLax J (A := A') U) (n + 1)).app
              (Under.mk f')).hom
            (CommAlgCat.standardTowerMap.{max u v w, max u v w, max u v w}
              (sectionsSquare J a b hsq U) (n + 1)
              (CommAlgCat.standardTowerX.{max u v w, max u v w}
                (A.obj.obj U) (sectionsAlgebra J f U) n q'))
        rw [hL, hR, Functor.iterateCompHomObj_succ, ← ih]
        exact (congrArg (sectionsSquareHom J a U
            ((standardResolutionComonadSquareHom.{u, v, w} J a).app
              ((((standardResolutionComonad.{v, u, w} J A' : Comonad (Under A')) :
                Under A' ⥤ Under A').iterate n).obj (Under.mk f'))))
          (freeAlgebraSheafAdjunction_unit_sections J U _ _)).trans
          (standardResolutionComonadSquareHom_variable J a U _ _)
    exact RingHom.congr_fun key q

/-- Transporting a morphism into a sheaf of `A'`-algebras read over `A` along equalities of its
source and target does not change it on sections, up to the same transports. -/
lemma transportObjHom_sections (U : Cᵒᵖ) {X₁ X₁' : Under A} {Y₁ Y₁' : Under A'}
    (p : X₁ = X₁') (q : Y₁ = Y₁') (φ : X₁' ⟶ (squareAlgebras J a).obj Y₁')
    (y : (sectionsAlgebraFunctor J U (A := A)).obj X₁') :
    sectionsSquareHom J a U (Functor.transportObjHom (squareAlgebras J a) p q φ)
        ((sectionsAlgebraFunctor J U).map (eqToHom p.symm) y) =
      (sectionsAlgebraFunctor J U (A := A')).map (eqToHom q.symm)
        (sectionsSquareHom J a U φ y) := by
  subst p q
  rfl

/-- **Naturality in squares of the Tag 08SX comparison of standard resolutions.** For a
commutative square `a : A ⟶ A'`, `b : B ⟶ B'`, the map of standard resolutions of sheaves of
rings that it induces, taken on sections over `U`, intertwines the two comparisons of
Tag 08SX with the map of standard resolutions of rings induced by the square on sections. -/
theorem resolutionSectionsComparison_square (U : Cᵒᵖ) (i : SimplexCategoryᵒᵖ)
    (p : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj i) :
    ((resolutionSquareMap.{u, v, w} J a b hsq).resolution i).hom.app U
        (((resolutionSectionsComparison J f U).app i).hom p) =
      ((resolutionSectionsComparison J f' U).app i).hom
        ((CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
          (sectionsSquare J a b hsq U)).resolution i p) := by
  obtain ⟨⟨n⟩⟩ := i
  show sectionsSquareHom J a U (squareResolutionTermMap.{u, v, w} J a b hsq n)
      (resolutionSectionsComparisonApp J f U n p) =
    resolutionSectionsComparisonApp J f' U n
      (CommAlgCat.standardResolutionSquareMap.{max u v w, max u v w, max u v w}
        (sectionsSquare J a b hsq U) (op ⦋n⦌) p)
  have hkey : CommAlgCat.standardTowerMap.{max u v w, max u v w, max u v w}
          (sectionsSquare J a b hsq U) (n + 1)
          (eqToHom (CommAlgCat.standardResolution_obj.{max u v w, max u v w} (A.obj.obj U)
            (sectionsAlgebra J f U) n) p) =
      eqToHom (CommAlgCat.standardResolution_obj.{max u v w, max u v w} (A'.obj.obj U)
          (sectionsAlgebra J f' U) n)
        (CommAlgCat.standardResolutionSquareMap.{max u v w, max u v w, max u v w}
          (sectionsSquare J a b hsq U) (op ⦋n⦌) p) :=
    (CommAlgCat.eqToHom_eqToHom_apply.{max u v w, max u v w}
        (CommAlgCat.standardResolution_obj.{max u v w, max u v w} (A'.obj.obj U)
          (sectionsAlgebra J f' U) n).symm
        (CommAlgCat.standardResolution_obj.{max u v w, max u v w} (A'.obj.obj U)
          (sectionsAlgebra J f' U) n) _).symm.trans
      (congrArg (fun z => eqToHom (CommAlgCat.standardResolution_obj.{max u v w, max u v w}
          (A'.obj.obj U) (sectionsAlgebra J f' U) n) z)
        (CommAlgCat.standardResolutionSquareMap_apply.{max u v w, max u v w, max u v w}
          (sectionsSquare J a b hsq U) n p).symm)
  refine ((congrArg (sectionsSquareHom J a U (squareResolutionTermMap.{u, v, w} J a b hsq n))
      (resolutionSectionsComparisonApp_apply J f U n p)).trans ?_).trans
    (resolutionSectionsComparisonApp_apply J f' U n _).symm
  refine (transportObjHom_sections J a U (standardResolution_obj.{v, u, w} J f n)
    (standardResolution_obj.{v, u, w} J f' n) _ _).trans ?_
  refine congrArg (fun z => (sectionsAlgebraFunctor J U (A := A')).map
    (eqToHom (standardResolution_obj.{v, u, w} J f' n).symm) z) ?_
  refine (iterateCompHomObj_sectionsComonadLax J a b hsq U (n + 1) _).trans ?_
  exact congrArg (fun z => ((Functor.iterateLaxHom (sectionsComonadLax J (A := A') U)
    (n + 1)).app (Under.mk f')).hom z) hkey

/-! ## The comparison of cotangent complexes -/

/-- On sections, the degreewise map of base-changed sheaves of differentials induced by a square
carries the universal derivation of a term of the standard resolution of `f` to the universal
derivation of the corresponding term of the standard resolution of `f'`, precomposed with the
map of standard resolutions. -/
lemma squareCotangentTermMap_universalSheafDerivation
    (sq : ResolutionSquareMap.{u, v, w} J f f' a b) (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ)
    (x : (resolutionTerm.{u, v, w} J f n).obj.obj U) :
    (squareCotangentTermMap sq n).val.app U ((universalSheafDerivation J f n).d x) =
      (universalSheafDerivation J f' n).d ((sq.resolution n).hom.app U x) := by
  have h := PresheafOfModules.Derivation.congr_d (X := U)
    ((cotangentSimplicialModule.{u, v, w} J f).derivationEquiv_eq_postcomp n
      (squareCotangentTermMap sq n)) x
  rw [squareCotangentTermMap_d] at h
  exact h.symm

/-- The canonical map of Tag 08SX in cohomological degree `-n`, evaluated on an element of the
degree-`n` term of base-changed differentials read in that degree. -/
lemma sectionsCotangentComplexComparison_degreeIso_inv {D E : Sheaf J CommRingCat.{max u v w}}
    (g : D ⟶ E) (W : Cᵒᵖ) (n : ℕ)
    (z : CommAlgCat.cotangentTerm.{max u v w, max u v w} (D.obj.obj W) (sectionsAlgebra J g W)
      (op ⦋n⦌)) :
    (sectionsCotangentComplexComparison J g W).f (-(n : ℤ))
        ((CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w} (D.obj.obj W)
          (sectionsAlgebra J g W) n).inv z) =
      (cotangentComplex_degreeIso J g n).inv.val.app W
        (cotangentTermComparison J g W (op ⦋n⦌) z) := by
  have h := ConcreteCategory.congr_hom (sectionsCotangentComplexComparison_f J g W n)
    ((CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w} (D.obj.obj W)
      (sectionsAlgebra J g W) n).inv z)
  simp only [ConcreteCategory.comp_apply] at h
  refine h.trans (congrArg (fun y => (moduleSections J g W).map
    (cotangentComplex_degreeIso J g n).inv (cotangentTermComparison J g W (op ⦋n⦌) y)) ?_)
  exact Iso.inv_hom_id_apply (CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w}
    (D.obj.obj W) (sectionsAlgebra J g W) n) z

/-- The map of cotangent complexes of sheaves induced by a square, in cohomological degree `-n`,
evaluated on sections of the degree-`n` term of base-changed differentials. -/
lemma squareCotangentComplexMap_degreeIso_inv (sq : ResolutionSquareMap.{u, v, w} J f f' a b)
    (n : ℕ) (U : Cᵒᵖ)
    (z : ((cotangentSimplicialModule.{u, v, w} J f).object.obj (op ⦋n⦌)).val.obj U) :
    ((squareCotangentComplexMap sq).f (-(n : ℤ))).val.app U
        ((cotangentComplex_degreeIso.{u, v, w} J f n).inv.val.app U z) =
      (cotangentComplex_degreeIso.{u, v, w} J f' n).inv.val.app U
        ((squareCotangentTermMap sq (op ⦋n⦌)).val.app U z) := by
  have h : (cotangentComplex_degreeIso.{u, v, w} J f n).inv ≫
      (squareCotangentComplexMap sq).f (-(n : ℤ)) =
      squareCotangentTermMap sq (op ⦋n⦌) ≫
        (squareRestrict.{u, v, w} J b).map (cotangentComplex_degreeIso.{u, v, w} J f' n).inv := by
    rw [squareCotangentComplexMap_f, Iso.inv_hom_id_assoc]
  exact congrArg (fun k => k.val.app U z) h

/-- **Naturality in squares of the canonical map of Tag 08SX, in one cohomological degree.**
For a commutative square `a : A ⟶ A'`, `b : B ⟶ B'` of homomorphisms of sheaves of commutative
rings, the canonical map `L_{B(U)/A(U)} ⟶ L_{B/A}(U)` followed by the sections over `U` of the
map `L_{B/A} ⟶ L_{B'/A'}` induced by the square agrees with the map
`L_{B(U)/A(U)} ⟶ L_{B'(U)/A'(U)}` induced by the square on sections followed by the canonical
map `L_{B'(U)/A'(U)} ⟶ L_{B'/A'}(U)`. -/
theorem sectionsCotangentComplexComparison_square_degree (U : Cᵒᵖ) (j : ℤ) :
    (sectionsCotangentComplexComparison J f U).f j ≫
        (moduleSections J f U).map
          ((squareCotangentComplexMap (resolutionSquareMap.{u, v, w} J a b hsq)).f j) =
      (CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
          (sectionsSquare J a b hsq U)).f j ≫
        (ModuleCat.restrictScalars (sectionsSquare J a b hsq U).map).map
          ((sectionsCotangentComplexComparison J f' U).f j) := by
  by_cases hpos : 0 < j
  · exact (CommAlgCat.cotangentComplex_isZero_pos.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U) j hpos).eq_of_src _ _
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by omega⟩
    refine (cancel_epi (CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w}
      (A.obj.obj U) (sectionsAlgebra J f U) n).inv).mp ?_
    refine CommAlgCat.cotangentTerm_hom_ext.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U) (op ⦋n⦌) _ _ fun p => ?_
    show ((squareCotangentComplexMap (resolutionSquareMap.{u, v, w} J a b hsq)).f
          (-(n : ℤ))).val.app U
        ((sectionsCotangentComplexComparison J f U).f (-(n : ℤ))
          ((CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w} (A.obj.obj U)
            (sectionsAlgebra J f U) n).inv
            (CommAlgCat.cotangentTermDifferential.{max u v w, max u v w} (A.obj.obj U)
              (sectionsAlgebra J f U) (op ⦋n⦌) p))) =
      (sectionsCotangentComplexComparison J f' U).f (-(n : ℤ))
        ((CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
          (sectionsSquare J a b hsq U)).f (-(n : ℤ))
          ((CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w} (A.obj.obj U)
            (sectionsAlgebra J f U) n).inv
            (CommAlgCat.cotangentTermDifferential.{max u v w, max u v w} (A.obj.obj U)
              (sectionsAlgebra J f U) (op ⦋n⦌) p)))
    have e1 := sectionsCotangentComplexComparison_degreeIso_inv J f U n
      (CommAlgCat.cotangentTermDifferential.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U) (op ⦋n⦌) p)
    have e2 := CommAlgCat.squareCotangentComplexMap_degreeIso_inv (sectionsSquare J a b hsq U) n
      (CommAlgCat.cotangentTermDifferential.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U) (op ⦋n⦌) p)
    have e3 := squareCotangentComplexMap_degreeIso_inv J a b
      (resolutionSquareMap.{u, v, w} J a b hsq) n U
      (cotangentTermComparison J f U (op ⦋n⦌)
        (CommAlgCat.cotangentTermDifferential.{max u v w, max u v w} (A.obj.obj U)
          (sectionsAlgebra J f U) (op ⦋n⦌) p))
    have e4 := sectionsCotangentComplexComparison_degreeIso_inv J f' U n
      (CommAlgCat.cotangentTermDifferential.{max u v w, max u v w} (A'.obj.obj U)
        (sectionsAlgebra J f' U) (op ⦋n⦌)
        (CommAlgCat.standardResolutionSquareMap.{max u v w, max u v w, max u v w}
          (sectionsSquare J a b hsq U) (op ⦋n⦌) p))
    rw [e1, e2, CommAlgCat.squareCotangentTermMap_D, e4]
    refine e3.trans ?_
    refine congrArg (fun z => (cotangentComplex_degreeIso J f' n).inv.val.app U z) ?_
    refine (congrArg (fun z => (squareCotangentTermMap (resolutionSquareMap.{u, v, w} J a b hsq)
        (op ⦋n⦌)).val.app U z) (cotangentTermComparison_differential J f U (op ⦋n⦌) p)).trans ?_
    refine (squareCotangentTermMap_universalSheafDerivation J a b
      (resolutionSquareMap.{u, v, w} J a b hsq) (op ⦋n⦌) U
      (((resolutionSectionsComparison J f U).app (op ⦋n⦌)).hom p)).trans ?_
    refine (congrArg (fun z => (universalSheafDerivation J f' (op ⦋n⦌)).d z)
      (resolutionSectionsComparison_square J a b hsq U (op ⦋n⦌) p)).trans ?_
    exact (cotangentTermComparison_differential J f' U (op ⦋n⦌) _).symm

/-- **Naturality in squares of the canonical map of Tag 08SX.** The canonical maps
`L_{B(U)/A(U)} ⟶ L_{B/A}(U)` commute with the maps of cotangent complexes induced by a
commutative square of homomorphisms of sheaves of commutative rings and by the square of ring
maps it restricts to on sections over `U`, on every element of every degree. -/
theorem sectionsCotangentComplexComparison_square (U : Cᵒᵖ) (j : ℤ)
    (x : (CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).X j) :
    ((squareCotangentComplexMap (resolutionSquareMap.{u, v, w} J a b hsq)).f j).val.app U
        ((sectionsCotangentComplexComparison J f U).f j x) =
      (sectionsCotangentComplexComparison J f' U).f j
        ((CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
          (sectionsSquare J a b hsq U)).f j x) :=
  ConcreteCategory.congr_hom (sectionsCotangentComplexComparison_square_degree J a b hsq U j) x

end Square

end CategoryTheory.Sheaf

end
