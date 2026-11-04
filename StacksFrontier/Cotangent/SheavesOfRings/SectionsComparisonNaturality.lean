module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.SheavesOfRings.SectionsCotangentComparison

/-!
# Naturality in `U` of the sections comparison of the cotangent complex

Let `A ⟶ B` be a homomorphism of sheaves of commutative rings on a site. For every object `U`
of the site there is a comparison `P'_• ⟶ P_•(U)` of the standard resolution of the ring map
`A(U) → B(U)` with the sections over `U` of the standard resolution of `A ⟶ B`, and a canonical
map `L_{B(U)/A(U)} ⟶ L_{B/A}(U)` induced by it. This file proves that both are natural in `U`.

Restricting along `g : U ⟶ V` moves both rings, so the ring-level restriction of the source is
the functoriality of the standard resolution in the square of ring maps
`CategoryTheory.Sheaf.sectionsRestrictionSquare`.

## Main results

* `CategoryTheory.Sheaf.resolutionSectionsComparison_restriction` and
  `CategoryTheory.Sheaf.resolutionSectionsComparison_restriction_square`: the naturality square
  in `U` of the comparison of standard resolutions, on elements and as an equality of ring
  homomorphisms.
* `CategoryTheory.Sheaf.cotangentTermComparison_restriction`: the degreewise comparison of
  base-changed differentials is natural in `U`, evaluated at a pure differential `1 ⊗ d p`.
* `CategoryTheory.Sheaf.sectionsCotangentComplexComparison_restriction_degree` and
  `CategoryTheory.Sheaf.sectionsCotangentComplexComparison_restriction`: the canonical maps
  `L_{B(U)/A(U)} ⟶ L_{B/A}(U)` are compatible with the restriction maps, in every cohomological
  degree.
* `CategoryTheory.Sheaf.sectionsComonadLax_variable`: the comonad comparison sends the variable
  `[x]` to the sheaf-level unit evaluated at `x`.

## Implementation notes

Restriction along `g` is packaged as `CategoryTheory.Sheaf.sectionsRestrictionHom`, a ring
homomorphism whose source and target are written through
`CategoryTheory.Sheaf.sectionsAlgebraFunctor`; its underlying map is `X.right.obj.map g`.

## References

* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 08SW](https://stacks.math.columbia.edu/tag/08SW)
* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

/-- Restriction along `g : U ⟶ V` on the sections of a sheaf of `A`-algebras. -/
noncomputable def sectionsRestrictionHom {U V : Cᵒᵖ} (g : U ⟶ V) (X : Under A) :
    (sectionsAlgebraFunctor J U (A := A)).obj X →+*
      (sectionsAlgebraFunctor J V (A := A)).obj X :=
  (X.right.obj.map g).hom

/-- Restriction is compatible with the structure map from the base sheaf. -/
theorem sectionsRestrictionHom_algebraMap {U V : Cᵒᵖ} (g : U ⟶ V) (X : Under A)
    (a : A.obj.obj U) :
    sectionsRestrictionHom J g X
        (algebraMap (A.obj.obj U) ((sectionsAlgebraFunctor J U (A := A)).obj X) a) =
      algebraMap (A.obj.obj V) ((sectionsAlgebraFunctor J V (A := A)).obj X)
        ((A.obj.map g).hom a) :=
  congrArg (fun k : A.obj.obj U ⟶ X.right.obj.obj V => k.hom a) (X.hom.hom.naturality g).symm

/-- Restriction commutes with the sections of a morphism of sheaves of `A`-algebras. -/
theorem sectionsRestrictionHom_map {U V : Cᵒᵖ} (g : U ⟶ V) {X Y : Under A} (h : X ⟶ Y)
    (x : (sectionsAlgebraFunctor J U (A := A)).obj X) :
    sectionsRestrictionHom J g Y ((sectionsAlgebraFunctor J U).map h x) =
      (sectionsAlgebraFunctor J V).map h (sectionsRestrictionHom J g X x) :=
  congrArg (fun k : X.right.obj.obj U ⟶ Y.right.obj.obj V => k.hom x)
    (h.right.hom.naturality g).symm

/-- The comonad comparison sends the variable `[x]` of the free `A(U)`-algebra on the sections
of `X` to the image of `x` under the sheaf-level unit, taken on sections over `U`. -/
theorem sectionsComonadLax_variable (U : Cᵒᵖ) (X : Under A)
    (x : (sectionsAlgebraFunctor J U (A := A)).obj X) :
    ((sectionsComonadLax J U).app X).hom (MvPolynomial.X x) =
      (sectionsOfSets J U).map
        ((freeAlgebraSheafAdjunction.{v, u, w} J A).unit.app
          ((forgetAlgebraSheaf.{v, u, w} J A).obj X)) x := by
  have h := ConcreteCategory.congr_hom
    (Adjunction.unit_comp_comonadLaxApp (freeAlgebraSheafAdjunction.{v, u, w} J A)
      (CommAlgCat.adj.{max u v w, max u v w} (A.obj.obj U)) (sectionsForgetIso J U) X) x
  simp only [ConcreteCategory.comp_apply, sectionsForgetIso] at h
  exact h

/-- A morphism of sheaves of sets commutes with the restriction maps of the site. -/
theorem sectionsOfSets_map_restriction {U V : Cᵒᵖ} (g : U ⟶ V)
    {E E' : Sheaf J (Type (max u v w))} (η : E ⟶ E') (x : (sectionsOfSets J U).obj E) :
    (sectionsOfSets J V).map η (E.obj.map g x) =
      E'.obj.map g ((sectionsOfSets J U).map η x) := by
  have h := ConcreteCategory.congr_hom
    (((sheafToPresheaf J (Type (max u v w))).map η).naturality g) x
  simp only [ConcreteCategory.comp_apply] at h
  exact h

/-- Restricting the image under the comonad comparison of the variable `[x]` gives the image of
the variable indexed by the restriction of `x`. -/
theorem sectionsComonadLax_variable_restriction {U V : Cᵒᵖ} (g : U ⟶ V) (X : Under A)
    (x : (sectionsAlgebraFunctor J U (A := A)).obj X) :
    sectionsRestrictionHom J g
        ((((standardResolutionComonad.{v, u, w} J A : Comonad (Under A)) :
          Under A ⥤ Under A).obj X))
        (((sectionsComonadLax J U).app X).hom (MvPolynomial.X x)) =
      ((sectionsComonadLax J V).app X).hom
        (MvPolynomial.X (sectionsRestrictionHom J g X x)) :=
  (congrArg (fun z => sectionsRestrictionHom J g
      ((((standardResolutionComonad.{v, u, w} J A : Comonad (Under A)) :
        Under A ⥤ Under A).obj X)) z) (sectionsComonadLax_variable J U X x)).trans
    (((sectionsOfSets_map_restriction J g
        ((freeAlgebraSheafAdjunction.{v, u, w} J A).unit.app
          ((forgetAlgebraSheaf.{v, u, w} J A).obj X)) x).symm).trans
      (sectionsComonadLax_variable J V X (sectionsRestrictionHom J g X x)).symm)

/-- The `(n + 1)`-fold iterate of the comonad comparison factors through the `n`-fold one. -/
theorem iterateSectionsComonadLax_succ_apply (W : Cᵒᵖ) (n : ℕ)
    (p : CommAlgCat.standardTower.{max u v w, max u v w} (A.obj.obj W)
      (sectionsAlgebra J f W) (n + 1)) :
    ((Functor.iterateLaxHom (sectionsComonadLax J W) (n + 1)).app (Under.mk f)).hom p =
      ((sectionsComonadLax J W).app
          ((((standardResolutionComonad.{v, u, w} J A : Comonad (Under A)) :
            Under A ⥤ Under A).iterate n).obj (Under.mk f))).hom
        ((CommAlgCat.polynomialComonad.{max u v w, max u v w} (A.obj.obj W)).toFunctor.map
          ((Functor.iterateLaxHom (sectionsComonadLax J W) n).app (Under.mk f)) p) := rfl

/-- On the stage-`n` tower of iterated polynomial algebras the restriction maps intertwine the
two iterated comonad comparisons, the ring-level restriction being the tower map of the
restriction square. -/
theorem iterateSectionsComonadLax_restriction {U V : Cᵒᵖ} (g : U ⟶ V) (n : ℕ)
    (q : CommAlgCat.standardTower.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U) n) :
    sectionsRestrictionHom J g ((((standardResolutionComonad.{v, u, w} J A : Comonad (Under A)) :
          Under A ⥤ Under A).iterate n).obj (Under.mk f))
        (((Functor.iterateLaxHom (sectionsComonadLax J U) n).app (Under.mk f)).hom q) =
      ((Functor.iterateLaxHom (sectionsComonadLax J V) n).app (Under.mk f)).hom
        (CommAlgCat.standardTowerMap.{max u v w, max u v w, max u v w}
          (sectionsRestrictionSquare J f g) n q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have key : ((sectionsRestrictionHom J g
            ((((standardResolutionComonad.{v, u, w} J A : Comonad (Under A)) :
              Under A ⥤ Under A).iterate (n + 1)).obj (Under.mk f))).comp
          ((Functor.iterateLaxHom (sectionsComonadLax J U) (n + 1)).app
            (Under.mk f)).hom.toRingHom) =
        (((Functor.iterateLaxHom (sectionsComonadLax J V) (n + 1)).app
            (Under.mk f)).hom.toRingHom.comp
          (CommAlgCat.standardTowerMap.{max u v w, max u v w, max u v w}
            (sectionsRestrictionSquare J f g) (n + 1))) := by
      refine CommAlgCat.standardTower_succ_hom_ext.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U) n (fun a => ?_) (fun q' => ?_)
      · have h1 := ((Functor.iterateLaxHom (sectionsComonadLax J U) (n + 1)).app
          (Under.mk f)).hom.commutes a
        have h2 := CommAlgCat.standardTowerMap_algebraMap.{max u v w, max u v w, max u v w}
          (sectionsRestrictionSquare J f g) (n + 1) a
        have h3 := ((Functor.iterateLaxHom (sectionsComonadLax J V) (n + 1)).app
          (Under.mk f)).hom.commutes ((A.obj.map g).hom a)
        show sectionsRestrictionHom J g _
            (((Functor.iterateLaxHom (sectionsComonadLax J U) (n + 1)).app
              (Under.mk f)).hom (algebraMap (A.obj.obj U) _ a)) =
          ((Functor.iterateLaxHom (sectionsComonadLax J V) (n + 1)).app (Under.mk f)).hom
            (CommAlgCat.standardTowerMap.{max u v w, max u v w, max u v w}
              (sectionsRestrictionSquare J f g) (n + 1) (algebraMap (A.obj.obj U) _ a))
        rw [h1, h2]
        exact (sectionsRestrictionHom_algebraMap J g _ a).trans h3.symm
      · have hU := (iterateSectionsComonadLax_succ_apply J f U n
              (CommAlgCat.standardTowerX.{max u v w, max u v w}
                (A.obj.obj U) (sectionsAlgebra J f U) n q')).trans
            (congrArg (fun z => ((sectionsComonadLax J U).app
                ((((standardResolutionComonad.{v, u, w} J A : Comonad (Under A)) :
                  Under A ⥤ Under A).iterate n).obj (Under.mk f))).hom z)
              (CommAlgCat.polynomialComonad_map_X.{max u v w, max u v w} (A.obj.obj U)
                ((Functor.iterateLaxHom (sectionsComonadLax J U) n).app (Under.mk f)) q'))
        have hV := (congrArg
              (fun z => ((Functor.iterateLaxHom (sectionsComonadLax J V) (n + 1)).app
                (Under.mk f)).hom z)
              (CommAlgCat.standardTowerMap_standardTowerX.{max u v w, max u v w, max u v w}
                (sectionsRestrictionSquare J f g) n q')).trans
            ((iterateSectionsComonadLax_succ_apply J f V n _).trans
              (congrArg (fun z => ((sectionsComonadLax J V).app
                  ((((standardResolutionComonad.{v, u, w} J A : Comonad (Under A)) :
                    Under A ⥤ Under A).iterate n).obj (Under.mk f))).hom z)
                (CommAlgCat.polynomialComonad_map_X.{max u v w, max u v w} (A.obj.obj V)
                  ((Functor.iterateLaxHom (sectionsComonadLax J V) n).app (Under.mk f))
                  (CommAlgCat.standardTowerMap.{max u v w, max u v w, max u v w}
                    (sectionsRestrictionSquare J f g) n q'))))
        refine (congrArg (sectionsRestrictionHom J g _) hU).trans (Eq.trans ?_ hV.symm)
        exact (sectionsComonadLax_variable_restriction J g _ _).trans
          (congrArg (fun z => ((sectionsComonadLax J V).app _).hom (MvPolynomial.X z)) (ih q'))
    exact RingHom.congr_fun key q

/-- The degreewise comparison of standard resolutions, written as a composite applied to an
element. -/
theorem resolutionSectionsComparisonApp_apply (W : Cᵒᵖ) (n : ℕ)
    (p : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj W)
      (sectionsAlgebra J f W)).left.obj (op ⦋n⦌)) :
    resolutionSectionsComparisonApp J f W n p =
      (sectionsAlgebraFunctor J W).map (eqToHom (standardResolution_obj.{v, u, w} J f n).symm)
        (((Functor.iterateLaxHom (sectionsComonadLax J W) (n + 1)).app (Under.mk f)).hom
          (eqToHom (CommAlgCat.standardResolution_obj.{max u v w, max u v w} (A.obj.obj W)
            (sectionsAlgebra J f W) n) p)) := rfl

/-- In each degree `n`, restriction along `g : U ⟶ V` intertwines the comparisons of standard
resolutions over `U` and `V`, the restriction of the source being the map of standard resolutions
of the restriction square. -/
theorem resolutionSectionsComparisonApp_restriction {U V : Cᵒᵖ} (g : U ⟶ V) (n : ℕ)
    (p : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj (op ⦋n⦌)) :
    sectionsRestrictionHom J g ((standardResolution J f).left.obj (op ⦋n⦌))
        (resolutionSectionsComparisonApp J f U n p) =
      resolutionSectionsComparisonApp J f V n
        (CommAlgCat.standardResolutionSquareMap.{max u v w, max u v w, max u v w}
          (sectionsRestrictionSquare J f g) (op ⦋n⦌) p) := by
  have hkey : CommAlgCat.standardTowerMap.{max u v w, max u v w, max u v w}
          (sectionsRestrictionSquare J f g) (n + 1)
          (eqToHom (CommAlgCat.standardResolution_obj.{max u v w, max u v w} (A.obj.obj U)
            (sectionsAlgebra J f U) n) p) =
      eqToHom (CommAlgCat.standardResolution_obj.{max u v w, max u v w} (A.obj.obj V)
          (sectionsAlgebra J f V) n)
        (CommAlgCat.standardResolutionSquareMap.{max u v w, max u v w, max u v w}
          (sectionsRestrictionSquare J f g) (op ⦋n⦌) p) :=
    (CommAlgCat.eqToHom_eqToHom_apply.{max u v w, max u v w}
        (CommAlgCat.standardResolution_obj.{max u v w, max u v w} (A.obj.obj V)
          (sectionsAlgebra J f V) n).symm
        (CommAlgCat.standardResolution_obj.{max u v w, max u v w} (A.obj.obj V)
          (sectionsAlgebra J f V) n) _).symm.trans
      (congrArg (fun z => eqToHom (CommAlgCat.standardResolution_obj.{max u v w, max u v w}
          (A.obj.obj V) (sectionsAlgebra J f V) n) z)
        (CommAlgCat.standardResolutionSquareMap_apply.{max u v w, max u v w, max u v w}
          (sectionsRestrictionSquare J f g) n p).symm)
  refine ((congrArg (sectionsRestrictionHom J g _)
      (resolutionSectionsComparisonApp_apply J f U n p)).trans ?_).trans
    (resolutionSectionsComparisonApp_apply J f V n _).symm
  refine (sectionsRestrictionHom_map J g _ _).trans ?_
  exact congrArg (fun z => (sectionsAlgebraFunctor J V).map
      (eqToHom (standardResolution_obj.{v, u, w} J f n).symm) z)
    ((iterateSectionsComonadLax_restriction J f g (n + 1) _).trans
      (congrArg (fun z => ((Functor.iterateLaxHom (sectionsComonadLax J V) (n + 1)).app
        (Under.mk f)).hom z) hkey))

/-- Restriction along `g : U ⟶ V` intertwines the comparisons `resolutionSectionsComparison`
over `U` and `V`, the restriction of the source being the functoriality of the standard
resolution in the restriction square. -/
theorem resolutionSectionsComparison_restriction {U V : Cᵒᵖ} (g : U ⟶ V)
    (i : SimplexCategoryᵒᵖ)
    (p : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj i) :
    sectionsRestrictionHom J g ((standardResolution J f).left.obj i)
        (((resolutionSectionsComparison J f U).app i).hom p) =
      ((resolutionSectionsComparison J f V).app i).hom
        ((CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
          (sectionsRestrictionSquare J f g)).resolution i p) := by
  obtain ⟨⟨n⟩⟩ := i
  exact resolutionSectionsComparisonApp_restriction J f g n p

/-- Restriction along `g : U ⟶ V` in the sheaf underlying the degree-`i` term of the standard
resolution intertwines the comparisons `resolutionSectionsComparison` over `U` and `V`. -/
theorem resolutionTerm_map_resolutionSectionsComparison {U V : Cᵒᵖ} (g : U ⟶ V)
    (i : SimplexCategoryᵒᵖ)
    (p : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj i) :
    ((resolutionTerm J f i).obj.map g).hom
        (((resolutionSectionsComparison J f U).app i).hom p) =
      ((resolutionSectionsComparison J f V).app i).hom
        ((CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
          (sectionsRestrictionSquare J f g)).resolution i p) :=
  resolutionSectionsComparison_restriction J f g i p

/-- The naturality square in `U` of `resolutionSectionsComparison`, as an equality of ring
homomorphisms. -/
theorem resolutionSectionsComparison_restriction_square {U V : Cᵒᵖ} (g : U ⟶ V)
    (i : SimplexCategoryᵒᵖ) :
    (sectionsRestrictionHom J g ((standardResolution J f).left.obj i)).comp
        ((resolutionSectionsComparison J f U).app i).hom.toRingHom =
      (((resolutionSectionsComparison J f V).app i).hom.toRingHom).comp
        ((CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
          (sectionsRestrictionSquare J f g)).resolution i) :=
  RingHom.ext fun p => resolutionSectionsComparison_restriction J f g i p

/-- Restriction of scalars along the augmentation does not change the restriction maps of the
underlying presheaf of modules. -/
private theorem restrictScalars_val_map_apply {U V : Cᵒᵖ} (g : U ⟶ V) (i : SimplexCategoryᵒᵖ)
    (z : ((cotangentSimplicialModule J f).object.obj i).val.obj U) :
    (((SheafOfModules.restrictScalars (resolutionAugmentationRing J f i)).obj
        ((cotangentSimplicialModule J f).object.obj i)).val.map g) z =
      ((cotangentSimplicialModule J f).object.obj i).val.map g z := rfl

/-- The comparison `cotangentTermComparison` of base-changed differentials commutes with the
restriction maps along `g : U ⟶ V`, on pure differentials `1 ⊗ d p`. -/
theorem cotangentTermComparison_restriction {U V : Cᵒᵖ} (g : U ⟶ V) (i : SimplexCategoryᵒᵖ)
    (p : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj i) :
    ((cotangentSimplicialModule J f).object.obj i).val.map g
        (cotangentTermComparison J f U i
          (CommAlgCat.cotangentTermDifferential.{max u v w, max u v w} (A.obj.obj U)
            (sectionsAlgebra J f U) i p)) =
      cotangentTermComparison J f V i
        (CommAlgCat.cotangentTermDifferential.{max u v w, max u v w} (A.obj.obj V)
          (sectionsAlgebra J f V) i
          ((CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
            (sectionsRestrictionSquare J f g)).resolution i p)) := by
  refine (congrArg (fun z => ((cotangentSimplicialModule J f).object.obj i).val.map g z)
    (cotangentTermComparison_differential J f U i p)).trans ?_
  refine Eq.trans ?_ (cotangentTermComparison_differential J f V i
    ((CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
      (sectionsRestrictionSquare J f g)).resolution i p)).symm
  refine Eq.trans ?_ (congrArg (fun z => (universalSheafDerivation J f i).d z)
    (resolutionSectionsComparison_restriction J f g i p))
  exact ((restrictScalars_val_map_apply J f g i _).symm).trans
    ((universalSheafDerivation J f i).d_map g
      (((resolutionSectionsComparison J f U).app i).hom p)).symm

/-- The pure differential `1 ⊗ d p` of the cotangent complex of `A(U) → B(U)`, read in
cohomological degree `-n`. -/
noncomputable def sectionsCotangentDifferential' (W : Cᵒᵖ) (n : ℕ)
    (p : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj W)
      (sectionsAlgebra J f W)).left.obj (op ⦋n⦌)) :
    (CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj W)
      (sectionsAlgebra J f W)).X (-(n : ℤ)) :=
  (CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w} (A.obj.obj W)
      (sectionsAlgebra J f W) n).inv
    (CommAlgCat.cotangentTermDifferential.{max u v w, max u v w} (A.obj.obj W)
      (sectionsAlgebra J f W) (op ⦋n⦌) p)

/-- The value of `sectionsCotangentComplexComparison` on a pure differential. -/
theorem sectionsCotangentComplexComparison_sectionsCotangentDifferential' (W : Cᵒᵖ)
    (n : ℕ)
    (p : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj W)
      (sectionsAlgebra J f W)).left.obj (op ⦋n⦌)) :
    (sectionsCotangentComplexComparison J f W).f (-(n : ℤ))
        (sectionsCotangentDifferential' J f W n p) =
      (cotangentComplex_degreeIso J f n).inv.val.app W
        (cotangentTermComparison J f W (op ⦋n⦌)
          (CommAlgCat.cotangentTermDifferential.{max u v w, max u v w} (A.obj.obj W)
            (sectionsAlgebra J f W) (op ⦋n⦌) p)) := by
  have h := ConcreteCategory.congr_hom (sectionsCotangentComplexComparison_f J f W n)
    (sectionsCotangentDifferential' J f W n p)
  simp only [ConcreteCategory.comp_apply] at h
  refine h.trans (congrArg (fun z => (moduleSections J f W).map
    (cotangentComplex_degreeIso J f n).inv (cotangentTermComparison J f W (op ⦋n⦌) z)) ?_)
  exact Iso.inv_hom_id_apply (CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w}
    (A.obj.obj W) (sectionsAlgebra J f W) n) _

/-- The comparison map of the restriction square carries pure differentials to pure
differentials. -/
theorem squareCotangentComplexMap_sectionsCotangentDifferential' {U V : Cᵒᵖ} (g : U ⟶ V)
    (n : ℕ)
    (p : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj (op ⦋n⦌)) :
    (CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
          (sectionsRestrictionSquare J f g)).f (-(n : ℤ))
        (sectionsCotangentDifferential' J f U n p) =
      sectionsCotangentDifferential' J f V n
        ((CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
          (sectionsRestrictionSquare J f g)).resolution (op ⦋n⦌) p) :=
  (Iso.hom_inv_id_apply (CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w}
      (A.obj.obj V) (sectionsAlgebra J f V) n) _).symm.trans
    (congrArg (fun z => (CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w}
        (A.obj.obj V) (sectionsAlgebra J f V) n).inv z)
      (CommAlgCat.squareCotangentComplexMap_differential.{max u v w, max u v w, max u v w}
        (sectionsRestrictionSquare J f g) n p))

/-- The canonical maps `L_{B(U)/A(U)} ⟶ L_{B/A}(U)` commute with the restriction maps along
`g : U ⟶ V`, on pure differentials. -/
private theorem sectionsCotangentComplexComparison_restriction_differential {U V : Cᵒᵖ}
    (g : U ⟶ V) (n : ℕ)
    (p : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj (op ⦋n⦌)) :
    ((cotangentComplex J f).X (-(n : ℤ))).val.map g
        ((sectionsCotangentComplexComparison J f U).f (-(n : ℤ))
          (sectionsCotangentDifferential' J f U n p)) =
      (sectionsCotangentComplexComparison J f V).f (-(n : ℤ))
        (sectionsCotangentDifferential' J f V n
          ((CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
            (sectionsRestrictionSquare J f g)).resolution (op ⦋n⦌) p)) := by
  rw [sectionsCotangentComplexComparison_sectionsCotangentDifferential',
    sectionsCotangentComplexComparison_sectionsCotangentDifferential']
  refine Eq.trans ?_ (congrArg (fun z => (cotangentComplex_degreeIso J f n).inv.val.app V z)
    (cotangentTermComparison_restriction J f g (op ⦋n⦌) p))
  exact (PresheafOfModules.naturality_apply (cotangentComplex_degreeIso J f n).inv.val g _).symm

/-- In each cohomological degree `j`, the canonical maps `L_{B(U)/A(U)} ⟶ L_{B/A}(U)` commute
with the restriction maps along `g : U ⟶ V`. -/
@[stacks 08SX "CLAUSE (2), the compatibility with the restriction maps of the site, in every \
cohomological degree. Remark 08SX makes three assertions: that for every U there is a canonical \
map L_{B(U)/A(U)} ⟶ L_{B/A}(U), that these maps are compatible with the restriction maps, and \
that L_{B/A} is the sheafification of U ↦ L_{B(U)/A(U)}. The first is \
`sectionsCotangentComplexComparison`, whose attribute records that only that clause is claimed \
and that this one needs naturality in U of `sectionsComonadLax`, hence of \
`resolutionSectionsComparison` — which is what is proved here, as \
`resolutionSectionsComparison_restriction_square`, and propagated to the complex. CARRIES \
NOTHING beyond the ambient variables of the comparison itself: arbitrary site, arbitrary \
Grothendieck topology, arbitrary morphism of sheaves of commutative rings, arbitrary g. No \
sheaf-condition, smallness or site hypothesis is added, because the proof is a \
variables-to-variables induction over the standard resolution tower. The SHEAFIFICATION clause \
(3) is not claimed here; it is `sectionwiseComplexIso` of \
`StacksFrontier/Cotangent/SheavesOfRings/SectionwiseCotangentComplexIso.lean`"]
theorem sectionsCotangentComplexComparison_restriction_degree {U V : Cᵒᵖ} (g : U ⟶ V) (j : ℤ) :
    (sectionsCotangentComplexComparison J f U).f j ≫
        ((cotangentComplex J f).X j).val.map g =
      (CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
          (sectionsRestrictionSquare J f g)).f j ≫
        (ModuleCat.restrictScalars (sectionsRestrictionSquare J f g).map).map
          ((sectionsCotangentComplexComparison J f V).f j) := by
  by_cases hpos : 0 < j
  · exact (CommAlgCat.cotangentComplex_isZero_pos.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U) j hpos).eq_of_src _ _
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by omega⟩
    refine (cancel_epi (CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w}
      (A.obj.obj U) (sectionsAlgebra J f U) n).inv).mp ?_
    refine CommAlgCat.cotangentTerm_hom_ext.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U) (op ⦋n⦌) _ _ fun p => ?_
    show ((cotangentComplex J f).X (-(n : ℤ))).val.map g
        ((sectionsCotangentComplexComparison J f U).f (-(n : ℤ))
          (sectionsCotangentDifferential' J f U n p)) =
      (sectionsCotangentComplexComparison J f V).f (-(n : ℤ))
        ((CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
            (sectionsRestrictionSquare J f g)).f (-(n : ℤ))
          (sectionsCotangentDifferential' J f U n p))
    rw [squareCotangentComplexMap_sectionsCotangentDifferential']
    exact sectionsCotangentComplexComparison_restriction_differential J f g n p

/-- The canonical maps `L_{B(U)/A(U)} ⟶ L_{B/A}(U)` commute with the restriction maps along
every `g : U ⟶ V` of the site, on elements: the source's restriction maps are the maps of
cotangent complexes of the restriction squares, and the target's are the restriction maps of the
terms of `CategoryTheory.Sheaf.cotangentComplex`. -/
theorem sectionsCotangentComplexComparison_restriction {U V : Cᵒᵖ} (g : U ⟶ V) (j : ℤ)
    (x : (CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).X j) :
    ((cotangentComplex J f).X j).val.map g
        ((sectionsCotangentComplexComparison J f U).f j x) =
      (sectionsCotangentComplexComparison J f V).f j
        ((CommAlgCat.cotangentComplexAbMap.{max u v w, max u v w, max u v w}
          (sectionsRestrictionSquare J f g)).f j x) :=
  ConcreteCategory.congr_hom
    (sectionsCotangentComplexComparison_restriction_degree J f g j) x

/-- The canonical maps `L_{B(U)/A(U)} ⟶ L_{B/A}(U)` commute with the restriction maps along
`g : U ⟶ V`, the restriction of the source being that of the presheaf
`CategoryTheory.Sheaf.sectionwiseCotangentComplex`. -/
theorem sectionwiseCotangentComplex_map_sectionsCotangentComplexComparison {U V : Cᵒᵖ}
    (g : U ⟶ V) (j : ℤ)
    (x : ((sectionwiseCotangentComplex J f).obj U).X j) :
    ((cotangentComplex J f).X j).val.map g
        ((sectionsCotangentComplexComparison J f U).f j x) =
      (sectionsCotangentComplexComparison J f V).f j
        (((sectionwiseCotangentComplex J f).map g).f j x) :=
  sectionsCotangentComplexComparison_restriction J f g j x

end CategoryTheory.Sheaf

end
