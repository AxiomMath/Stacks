module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RestrictionOfDerivedGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalHomNaturality
public import StacksFrontier.Homology.HomComplex.TargetShiftDegree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restricting a global section of the internal Hom complex to an object of the site

Let `(C, O)` be a ringed site, `U` an object of `C` and `L`, `M` complexes of `O`-modules. A
global section of the internal Hom complex `SheafHom^•(L, M)` of Stacks 0A8X is a compatible
family of sections, and it represents a cochain `L ⟶ M` by Stacks 0A8Z; its section over `U`
represents a cochain `L|_U ⟶ M|_U` by Stacks 0A8Y. **The second cochain is the restriction of the
first to the slice over `U`.** That is the one piece of mathematics in this file, and everything
else is the passage from it to the comparison of Stacks 0A8Z with Stacks 0A8Y in degree zero:

`H⁰(Γ(C, SheafHom^•(L, M))) ⟶ Hom_{K(O)}(L, M)` restricted to `U` is
`H⁰(Γ(U, SheafHom^•(L, M))) ⟶ Hom_{K(O|_U)}(L|_U, M|_U)`.

## Main definitions

* `homComplexFunctorMap`, `cocycleFunctorMap`, `cohomologyClassFunctorMap`: the action of an
  additive functor on the Hom complex, on its cocycles and on its cohomology classes, from
  `CochainComplex.HomComplex.Cochain.map`.
* `AlgebraicGeometry.RingedSite.uliftDown` and `AlgebraicGeometry.RingedSite.uliftComplexIso`:
  stripping a degreewise universe lift of a complex of abelian groups.

## Main results

* `homologyAddEquiv_homComplexFunctorMap`: the identification of the cohomology of the Hom
  complex with cohomology classes is compatible with an additive functor.
* `toHom_mk_comp_shiftFunctorZero`: in degree zero, Tag 0A5X sends the class of a `0`-cocycle to
  the class of the morphism of complexes it is.
* `AlgebraicGeometry.RingedSite.homologyMap_uliftComplexIso`: the universe lift that Stacks 0A8Z
  carries, crossed on homology.
* `AlgebraicGeometry.RingedSite.sectionsIso_globalSectionsComplexRestriction`: **the restriction
  of a global section of the internal Hom complex represents the restricted cochain.**
* `AlgebraicGeometry.RingedSite.homologyAddEquiv_globalSectionsComplexRestriction`: the same on
  cohomology classes.
* **Stacks 0A8Z is compatible with Stacks 0A8Y under restriction to an object of the site**:
  `AlgebraicGeometry.RingedSite`
  `.sheafHomSectionHomotopyCategoryHom_globalSectionsComplexRestriction`.

## Implementation notes

*What makes the main statement true.* `AlgebraicGeometry.RingedSite.SheafHomComplex` carries both
the local descriptions of the sections of the internal Hom complex and their compatibility
`restrict_natural` with restriction along arrows of the site, and
`AlgebraicGeometry.RingedSite.sheafHomComplex_globalSectionsIso_v_app` says that the global
description agrees with the local one over `U`, evaluated at the identity arrow of `U`. For a
slice object `V ⟶ U` the two are matched by `restrict_natural` along `V ⟶ U` together with the
compatibility of the global section as a family; the only friction is that `restrict_natural`
presents the slice object as `Over.mk (g ≫ f)`, so an arrow equal to the one of the slice object
has to be transported, which `over_mk_eq_app` does.

*The universe-lift layer.* Globally the sections of the internal Hom complex are identified with
the degreewise lift of `Hom^•(L, M)` along `AddCommGrpCat.uliftFunctor`, because the global
sections of a sheaf of modules on a site live in a larger universe than the sections over an
object; over `U` no lift appears. Both must therefore be compared across the lift, which
`AlgebraicGeometry.RingedSite.homologyMap_uliftComplexIso` does: the map induced on homology by
the degreewise `ULift.down` is `AlgebraicGeometry.RingedSite.uliftHomologyIso` with the lift
stripped off. Its proof is `CategoryTheory.ShortComplex.LeftHomologyMapData.homologyMap_eq` for
the left homology map data that `ULift.down` defines between the image of the chosen left
homology data under the lifting functor and that data itself; the identity functor is avoided,
because `CategoryTheory.ShortComplex.mapHomologyIso` at the identity functor is *not* the
identity by construction and identifying it would need its own argument.

*The universes are the diagonal ones*, `AlgebraicGeometry.RingedSite.{u, u, u}` with modules in
`SheafOfModules.{u}`, as in the whole Section 34 cluster; see the implementation notes of
`StacksDraft.Ch21.Sec34.DerivedInternalHomOnASite`. The lifting functor is then
`AddCommGrpCat.uliftFunctor.{u, u}`, which is an endofunctor of `AddCommGrpCat.{u}`, so
`AlgebraicGeometry.RingedSite.uliftComplexIso` is an isomorphism of complexes in one category.

## References

* [Stacks Project, Tag 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
* [Stacks Project, Tag 0A8Y](https://stacks.math.columbia.edu/tag/0A8Y)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0A5X](https://stacks.math.columbia.edu/tag/0A5X)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CochainComplex.HomComplex

universe u

/-! ### The Hom complex under an additive functor -/

section FunctorMap

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  (Φ : C ⥤ D) [Φ.Additive]

/-- **An additive functor acts on the Hom complex.** Degreewise it sends a cochain to its
image `CochainComplex.HomComplex.Cochain.map`; this commutes with the Hom-complex differential
because `CochainComplex.HomComplex.δ_map` does. -/
def homComplexFunctorMap (K L : CochainComplex C ℤ) :
    CochainComplex.HomComplex K L ⟶
      CochainComplex.HomComplex ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) where
  f n := AddCommGrpCat.ofHom
    { toFun := fun z ↦ Cochain.map z Φ
      map_zero' := by simp
      map_add' := by simp }
  comm' i j hij := by
    subst hij
    ext z
    exact δ_map _ _ z Φ

/-- The components of `homComplexFunctorMap`. -/
lemma homComplexFunctorMap_f_apply (K L : CochainComplex C ℤ) (n : ℤ) (z : Cochain K L n) :
    AddCommGrpCat.Hom.hom ((homComplexFunctorMap Φ K L).f n) z = z.map Φ := rfl

/-- The image of a cocycle under an additive functor. -/
def cocycleFunctorMap {K L : CochainComplex C ℤ} {n : ℤ} (z : Cocycle K L n) :
    Cocycle ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) n :=
  Cocycle.mk ((z : Cochain K L n).map Φ) (n + 1) rfl
    (by rw [δ_map, Cocycle.δ_eq_zero z (n + 1), Cochain.map_zero])

/-- The degree-zero morphism of complexes attached to the image of a `0`-cocycle is the image
of the morphism attached to it. -/
lemma homOf_cocycleFunctorMap {K L : CochainComplex C ℤ} (z : Cocycle K L 0) :
    Cocycle.homOf (cocycleFunctorMap Φ z) =
      (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map (Cocycle.homOf z) := by
  ext p
  rfl

/-- `cocycleFunctorMap` as an additive map on cocycles. -/
def cocycleFunctorMapAddMonoidHom (K L : CochainComplex C ℤ) (n : ℤ) :
    Cocycle K L n →+
      Cocycle ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) n where
  toFun z := cocycleFunctorMap Φ z
  map_zero' := by ext p q hpq; simp [cocycleFunctorMap]
  map_add' _ _ := by ext p q hpq; simp [cocycleFunctorMap]

/-- **An additive functor acts on cohomology classes of the Hom complex.** A coboundary is
carried to a coboundary because `CochainComplex.HomComplex.δ_map` commutes with the
differential. -/
def cohomologyClassFunctorMap {K L : CochainComplex C ℤ} {n : ℤ} :
    CohomologyClass K L n →+
      CohomologyClass ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom _ _ n).comp (cocycleFunctorMapAddMonoidHom Φ K L n)) (by
      rintro z ⟨m, hm, β, hβ⟩
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
        CohomologyClass.mkAddMonoidHom_apply, CohomologyClass.mk_eq_zero_iff]
      rw [mem_coboundaries_iff _ m hm]
      exact ⟨Cochain.map β Φ, by rw [δ_map _ _ β Φ, hβ]; rfl⟩)

/-- `cohomologyClassFunctorMap` sends the class of a cocycle `z` to the class of
`cocycleFunctorMap Φ z`. -/
@[simp]
lemma cohomologyClassFunctorMap_mk {K L : CochainComplex C ℤ} {n : ℤ} (z : Cocycle K L n) :
    cohomologyClassFunctorMap Φ (CohomologyClass.mk z) =
      CohomologyClass.mk (cocycleFunctorMap Φ z) := rfl

/-- `homologyAddEquiv` sends the class of a cycle to the class of the cocycle it defines. -/
private theorem homologyAddEquiv_homologyπ (K L : CochainComplex C ℤ) (n : ℤ)
    (w : (CochainComplex.HomComplex K L).cycles n) :
    homologyAddEquiv K L n ((CochainComplex.HomComplex K L).homologyπ n w) =
      CohomologyClass.mk ((leftHomologyData K L n).cyclesIso.hom w) :=
  ConcreteCategory.congr_hom
    (ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom
      ((CochainComplex.HomComplex K L).sc n) (leftHomologyData K L n)) w

/-- **The identification of the cohomology of the Hom complex with cohomology classes is
compatible with an additive functor.** -/
theorem homologyAddEquiv_homComplexFunctorMap (K L : CochainComplex C ℤ) (n : ℤ)
    (η : (CochainComplex.HomComplex K L).homology n) :
    homologyAddEquiv ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) n
        (HomologicalComplex.homologyMap (homComplexFunctorMap Φ K L) n η) =
      cohomologyClassFunctorMap Φ (homologyAddEquiv K L n η) := by
  let h := leftHomologyData K L n
  let h' := leftHomologyData ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) n
  have hπ : Function.Surjective
      (ConcreteCategory.hom ((CochainComplex.HomComplex K L).homologyπ n)) :=
    (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨z, rfl⟩ := hπ η
  let a : Cocycle K L n := h.cyclesIso.hom z
  have hmap : h'.cyclesIso.hom
      ((HomologicalComplex.cyclesMap (homComplexFunctorMap Φ K L) n) z) =
      cocycleFunctorMap Φ a := by
    apply Subtype.ext
    have h1 := ConcreteCategory.congr_hom h'.cyclesIso_hom_comp_i
      ((HomologicalComplex.cyclesMap (homComplexFunctorMap Φ K L) n) z)
    have h2 := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (homComplexFunctorMap Φ K L) n) z
    have h3 := ConcreteCategory.congr_hom h.cyclesIso_hom_comp_i z
    simp only [ConcreteCategory.comp_apply] at h1 h2 h3
    refine h1.trans (h2.trans ?_)
    exact congrArg (fun w ↦ Cochain.map w Φ) h3
  have hnat := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (homComplexFunctorMap Φ K L) n) z
  simp only [ConcreteCategory.comp_apply] at hnat
  rw [hnat, homologyAddEquiv_homologyπ K L n z]
  exact (homologyAddEquiv_homologyπ _ _ _ _).trans (congrArg CohomologyClass.mk hmap)

end FunctorMap

/-- **The homotopy-category morphism attached to a degree-zero cohomology class of the Hom
complex.**  After normalising the degree-zero shift of the target away, Tag 0A5X in degree zero
sends the class of a `0`-cocycle to the class of the morphism of complexes it is. -/
@[sga "2 V 1.1" "Degree-zero clause"]
theorem toHom_mk_comp_shiftFunctorZero {C : Type*} [Category C] [Abelian C]
    {K L : CochainComplex C ℤ} (z : Cocycle K L 0) :
    CohomologyClass.toHom (CohomologyClass.mk z) ≫
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
          ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).app L).hom =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (Cocycle.homOf z) := by
  rw [CohomologyClass.toHom_mk, Cocycle.equivHomShift_symm_apply,
    ← CategoryTheory.Functor.map_comp, homOf_rightShift_zero]

namespace AlgebraicGeometry.RingedSite

/-! ### The degreewise universe lift of a complex of abelian groups -/

/-- Stripping the universe lift of a group, as a natural transformation out of the lifting
functor. -/
def uliftDown :
    AddCommGrpCat.uliftFunctor.{u, u} ⟶ CategoryTheory.Functor.id AddCommGrpCat.{u} where
  app _ := AddCommGrpCat.ofHom AddEquiv.ulift.toAddMonoidHom
  naturality _ _ _ := rfl

/-- The degreewise universe lift of a complex of abelian groups, compared with the complex
itself. -/
def uliftComplexIso (A : CochainComplex AddCommGrpCat.{u} ℤ) :
    (AddCommGrpCat.uliftFunctor.{u, u}.mapHomologicalComplex (ComplexShape.up ℤ)).obj A ≅ A :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ ↦ AddEquiv.ulift.toAddCommGrpIso) (fun _ _ _ ↦ rfl)

private def uliftDownMapData (S : ShortComplex AddCommGrpCat.{u}) [S.HasHomology] :
    ShortComplex.LeftHomologyMapData (S.mapNatTrans uliftDown.{u})
      (S.homologyData.left.map AddCommGrpCat.uliftFunctor.{u, u}) S.homologyData.left where
  φK := uliftDown.app S.homologyData.left.K
  φH := uliftDown.app S.homologyData.left.H

private theorem shortComplexFunctor_map_uliftComplexIso
    (A : CochainComplex AddCommGrpCat.{u} ℤ) (n : ℤ) :
    (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) n).map
        (uliftComplexIso A).hom =
      (A.sc n).mapNatTrans uliftDown.{u} := rfl

/-- **Stripping the universe lift on homology.** The map induced on homology by the comparison
`AlgebraicGeometry.RingedSite.uliftComplexIso` is the identification
`AlgebraicGeometry.RingedSite.uliftHomologyIso` with the lift stripped off. -/
theorem homologyMap_uliftComplexIso (A : CochainComplex AddCommGrpCat.{u} ℤ) (n : ℤ)
    (w : ((AddCommGrpCat.uliftFunctor.{u, u}.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      A).homology n) :
    HomologicalComplex.homologyMap (uliftComplexIso A).hom n w =
      AddEquiv.ulift ((uliftHomologyIso A n).hom w) := by
  have h : HomologicalComplex.homologyMap (uliftComplexIso A).hom n =
      (uliftHomologyIso A n).hom ≫ uliftDown.app ((A.sc n).homology) :=
    ((uliftDownMapData (A.sc n)).homologyMap_eq).trans
      (congrArg (fun f => (uliftHomologyIso A n).hom ≫ f)
        ((congrArg (fun g => uliftDown.app ((A.sc n).homology) ≫ g)
          ((A.sc n).leftHomologyIso.inv_hom_id)).trans
          (Category.comp_id _)))
  exact ConcreteCategory.congr_hom h w

/-! ### The global description of the internal Hom complex restricted to an object -/

variable (X : RingedSite.{u, u, u}) (U : X.C)

/-- A slice object is `Over.mk` of its own arrow, so a section of a restricted module read at
`Over.mk` of any arrow equal to it is the section read at the object itself. -/
private theorem over_mk_eq_app
    {A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (c : (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj A ⟶
      (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj B)
    (V : (Over U)ᵒᵖ) {h : V.unop.left ⟶ U} (hh : h = V.unop.hom)
    (x : A.val.obj (op V.unop.left)) :
    (c.val.app (op (Over.mk h))) x = (c.val.app V) x :=
  congrArg
    (fun (h' : V.unop.left ⟶ U) ↦
      show B.val.obj (op V.unop.left) from (c.val.app (op (Over.mk h'))) x)
    hh

/-- **Restricting a global section of the internal Hom complex to `U` restricts the cochain it
represents.**  A global section of `SheafHom^•(L, M)` is a compatible family; its section over
`U` represents, by `AlgebraicGeometry.RingedSite.SheafHomComplex.sectionsIso`, a cochain from
`L|_U` to `M|_U`, and that cochain is the restriction to the slice over `U` of the cochain from
`L` to `M` that the family represents.

This is the one input of this file that is not formal: it is
`AlgebraicGeometry.RingedSite.sheafHomComplex_globalSectionsIso_v_app` at every object of the
site, glued by the compatibility
`AlgebraicGeometry.RingedSite.SheafHomComplex.restrict_natural` of the local descriptions with
restriction along arrows of the site. -/
theorem sectionsIso_globalSectionsComplexRestriction
    (L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ)
    (s : (globalSectionsComplex X (sheafHomComplex X L M).obj).X n) :
    AddCommGrpCat.Hom.hom (((sheafHomComplex X L M).sectionsIso U).hom.f n)
        (AddCommGrpCat.Hom.hom
          ((Stacks.Cohomology.ModuleSections.globalSectionsComplexRestriction X U
            (sheafHomComplex X L M).obj).f n) s) =
      Cochain.map
        ((AddCommGrpCat.Hom.hom ((sheafHomComplex X L M).globalSectionsIso.hom.f n) s).down)
        (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have e2 := over_mk_eq_app X U
    ((AddCommGrpCat.Hom.hom (((sheafHomComplex X L M).sectionsIso U).hom.f n)
      (s.val (op U))).v p q hpq) V (Category.id_comp V.unop.hom) x
  have h3 := sheafHomComplex_globalSectionsIso_v_app X L M n p q hpq s V.unop.left
    (show (L.X p).val.obj (op V.unop.left) from x)
  have h4 := (sheafHomComplex X L M).restrict_natural_app V.unop.hom n p q hpq (s.val (op U))
    (op (Over.mk (𝟙 V.unop.left))) (show ((restrictComplex X L V.unop.left).X p).val.obj
      (op (Over.mk (𝟙 V.unop.left))) from x)
  have h5 : ((sheafHomComplex X L M).obj.X n).val.map V.unop.hom.op (s.val (op U)) =
      s.val (op V.unop.left) := s.property V.unop.hom.op
  rw [h5] at h4
  exact e2.symm.trans (h4.trans h3.symm)

/-- `AlgebraicGeometry.RingedSite.sectionsIso_globalSectionsComplexRestriction` as a square of
morphisms of complexes of abelian groups. -/
theorem globalSectionsComplexRestriction_sectionsIso
    (L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    Stacks.Cohomology.ModuleSections.globalSectionsComplexRestriction X U
          (sheafHomComplex X L M).obj ≫
        ((sheafHomComplex X L M).sectionsIso U).hom =
      (sheafHomComplex X L M).globalSectionsIso.hom ≫
        (AddCommGrpCat.uliftFunctor.{u, u}.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (homComplexFunctorMap
              (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) L M) ≫
          (uliftComplexIso (CochainComplex.HomComplex (restrictComplex X L U)
            (restrictComplex X M U))).hom :=
  HomologicalComplex.hom_ext _ _ fun n => AddCommGrpCat.hom_ext <| AddMonoidHom.ext
    (sectionsIso_globalSectionsComplexRestriction X U L M n)

/-- **The cohomology class over `U` of a restricted global section of the internal Hom complex
is the restriction of the class it represents.**  This is Tag 0A8Z compared with Tag 0A8Y under
restriction to the slice over `U`. -/
theorem homologyAddEquiv_globalSectionsComplexRestriction
    (L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ)
    (η : (globalSectionsComplex X (sheafHomComplex X L M).obj).homology n) :
    homologyAddEquiv (restrictComplex X L U) (restrictComplex X M U) n
        (HomologicalComplex.homologyMap ((sheafHomComplex X L M).sectionsIso U).hom n
          (HomologicalComplex.homologyMap
            (Stacks.Cohomology.ModuleSections.globalSectionsComplexRestriction X U
              (sheafHomComplex X L M).obj) n η)) =
      cohomologyClassFunctorMap
          (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
        (homologyAddEquiv L M n
          (AddEquiv.ulift ((uliftHomologyIso (CochainComplex.HomComplex L M) n).hom
            (HomologicalComplex.homologyMap
              (sheafHomComplex X L M).globalSectionsIso.hom n η)))) := by
  have hhom : HomologicalComplex.homologyMap ((sheafHomComplex X L M).sectionsIso U).hom n
        (HomologicalComplex.homologyMap
          (Stacks.Cohomology.ModuleSections.globalSectionsComplexRestriction X U
            (sheafHomComplex X L M).obj) n η) =
      HomologicalComplex.homologyMap
          (uliftComplexIso (CochainComplex.HomComplex (restrictComplex X L U)
            (restrictComplex X M U))).hom n
        (HomologicalComplex.homologyMap
          ((AddCommGrpCat.uliftFunctor.{u, u}.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (homComplexFunctorMap
              (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) L M)) n
          (HomologicalComplex.homologyMap
            (sheafHomComplex X L M).globalSectionsIso.hom n η)) := by
    simpa only [HomologicalComplex.homologyMap_comp, ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom (congrArg (fun f => HomologicalComplex.homologyMap f n)
        (globalSectionsComplexRestriction_sectionsIso X U L M)) η
  rw [hhom, homologyMap_uliftComplexIso, ulift_mapHomologyIso_naturality,
    homologyAddEquiv_homComplexFunctorMap]

/-- **Tag 0A8Z is compatible with Tag 0A8Y under restriction to an object of the site.**  The
homotopy-category morphism `L|_U ⟶ M|_U` attached to the restriction to `U` of a degree-zero
class of the global section complex of `SheafHom^•(L, M)` is the restriction to the slice over
`U` of the homotopy-category morphism `L ⟶ M` attached to that class. -/
theorem sheafHomSectionHomotopyCategoryHom_globalSectionsComplexRestriction
    (L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (η : (globalSectionsComplex X (sheafHomComplex X L M).obj).homology 0) :
    sheafHomSectionHomotopyCategoryHom X L M U
        (HomologicalComplex.homologyMap
          (Stacks.Cohomology.ModuleSections.globalSectionsComplexRestriction X U
            (sheafHomComplex X L M).obj) 0 η) =
      ((SheafOfModules.overFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomotopyCategory
        (ComplexShape.up ℤ)).map (sheafHomGlobalHomotopyCategoryHom X L M η) := by
  obtain ⟨z, hz⟩ := CohomologyClass.mk_surjective (homologyAddEquiv L M 0
    (AddEquiv.ulift ((uliftHomologyIso (CochainComplex.HomComplex L M) 0).hom
      (HomologicalComplex.homologyMap
        (sheafHomComplex X L M).globalSectionsIso.hom 0 η))))
  rw [sheafHomSectionHomotopyCategoryHom_eq, sheafHomGlobalHomotopyCategoryHom_eq,
    homologyAddEquiv_globalSectionsComplexRestriction, ← hz, cohomologyClassFunctorMap_mk]
  simp only [CohomologyClass.homAddEquiv_apply, Category.id_comp]
  rw [toHom_mk_comp_shiftFunctorZero, toHom_mk_comp_shiftFunctorZero,
    homOf_cocycleFunctorMap]
  exact (CategoryTheory.Functor.mapHomotopyCategory_map
    (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
    (Cocycle.homOf z)).symm

end AlgebraicGeometry.RingedSite

end
