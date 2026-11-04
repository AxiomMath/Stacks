module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShiftNaturality
public import StacksFrontier.Homology.HomComplex.TargetShiftIso

/-!
# The factors of the canonical map against the translation

Let `(C, O)` be a ringed site. The canonical map
`Hom^•(F, G) ⟶ RHom_O(F, G)` of
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom` is a composite of three morphisms —
the global description of the internal Hom complex of Tag 0A8Z with its universe lift, the unit
`AlgebraicGeometry.RingedSite.globalSectionsDerivedUnit` of derived global sections, and the
comparison `AlgebraicGeometry.RingedSite.sheafHomComplexUnit` with the derived internal Hom. The
degree-`n` reading of that map, which the central clause of Tag 0CS6 consumes, needs each factor
to be compatible with the translation in the covariant variable; this file collects those
compatibilities.

## Main results

* `AlgebraicGeometry.RingedSite.sheafHomComplexUnit_derivedSheafHomTargetShiftIsoOfKInjective`:
  the comparison with the derived internal Hom is compatible with the translation in its
  covariant variable, at a K-injective target.
* `AlgebraicGeometry.RingedSite.globalSectionsComplexShiftIso` and
  `AlgebraicGeometry.RingedSite.globalSectionsComplexShiftIso_hom_f`: the complex of global
  sections commutes with the translation, degreewise by the identity.
* `AlgebraicGeometry.RingedSite.uliftComplexSelfIso_shift`: the comparison of a complex of
  abelian groups with its degreewise universe lift is compatible with the translation.
* `AlgebraicGeometry.RingedSite.globalSectionsIso_sheafHomTargetShiftIso`: the global
  description of the internal Hom complex of Tag 0A8Z is compatible with the translation in its
  covariant variable — the sheaf-side target shift
  `AlgebraicGeometry.RingedSite.sheafHomTargetShiftIso` becomes the Hom-complex target shift
  `CochainComplex.HomComplex.homComplexTargetShiftIso`.
* `AlgebraicGeometry.RingedSite.globalSectionsDerivedUnit_shift`: the unit of derived global
  sections is compatible with the translation.
* `AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIso_eq_ofKInjective`: the commutation
  with the translation built from the chosen models is the commutation at a representative pair.

## Implementation notes

*The comparison with the derived internal Hom is free.* On a K-injective target
`AlgebraicGeometry.RingedSite.sheafHomComplexUnit` is the inverse of the comparison of Tag 0A97
(`AlgebraicGeometry.RingedSite.sheafHomComplexUnit_eq_derivedSheafHomComparison_inv`), and
`AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIsoOfKInjective` is *built* from that
comparison and the commutation `AlgebraicGeometry.RingedSite.sheafHomTargetShiftIso` of the
ordinary internal Hom complex with the translation. So the compatibility is a cancellation of
the comparison against its own inverse, and no computation is involved.

*The signs of the global description cancel.* The global description of Tag 0A8Z is the only
factor of the canonical map with a sign-bearing identification on either side, and the two signs
are both absent. On the sheaf side
`AlgebraicGeometry.RingedSite.sectionsEquiv_sheafHomTargetShiftIso_hom` describes
`AlgebraicGeometry.RingedSite.sheafHomTargetShiftIso` on sections by
`AlgebraicGeometry.RingedSite.cochainTargetShift`, which is Mathlib's
`CochainComplex.HomComplex.Cochain.rightShift` conjugated by the identification of the
restriction of a shifted complex with the shift of the restriction, and `rightShift` reindexes
homogeneous components with no sign. On the module side
`CochainComplex.HomComplex.homComplexTargetShiftIso` is that same `rightShift`, so the two
reindexings agree degreewise and the compatibility is an identity of homogeneous components
rather than a sign computation.

The sections description to compute against is
`AlgebraicGeometry.RingedSite.sheafHomComplex_globalSectionsIso_v_app`, which evaluates a global
section of the internal Hom complex at the identity of an object of the site — **not**
`AlgebraicGeometry.RingedSite.globalSectionsIso_homMap_v`, with which it is easily confused.
The two are companions, but `globalSectionsIso_homMap_v` describes the global description against
`AlgebraicGeometry.RingedSite.homMap`, the functoriality of the internal Hom complex in its two
*complex* arguments, whereas the statement here is about a single global section being carried
through the target shift; only the first of the pair is in the right shape for it.

*Global sections commute with the translation on the nose.*
`AlgebraicGeometry.RingedSite.globalSectionsComplex` is
`CategoryTheory.Functor.mapHomologicalComplex` of the global-sections functor, and Mathlib's
`CochainComplex` instance makes any such functor commute with the translation by an isomorphism
whose components are identities; the content is only that global sections, being additive,
commute with the sign `(-1)^n` by which the differential of a shifted complex differs from the
original.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-! ### The comparison with the derived internal Hom -/

/-- **The comparison with the derived internal Hom is compatible with the translation in its
covariant variable, at a K-injective target.** For a K-injective `G`, the comparison
`Q SheafHom(F, G[n]) ⟶ RSheafHom(Q F, Q (G[n]))` followed by
`AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIsoOfKInjective` is the commutation
`AlgebraicGeometry.RingedSite.sheafHomTargetShiftIso` of the ordinary internal Hom complex with
the translation, followed by the commutation of the localization functor with the translation
and the `n`-shift of the comparison at `(F, G)`.

On a K-injective target the comparison is the inverse of the comparison of Tag 0A97, out of which
`AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIsoOfKInjective` is built, so this is a
cancellation. -/
theorem sheafHomComplexUnit_derivedSheafHomTargetShiftIsoOfKInjective
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [G.IsKInjective] (n : ℤ) :
    sheafHomComplexUnit X F (G⟦n⟧) ≫
        (derivedSheafHomTargetShiftIsoOfKInjective X F G n).hom =
      DerivedCategory.Q.map (sheafHomTargetShiftIso X (K := F) (M := G) n).inv ≫
        (DerivedCategory.Q.commShiftIso n).hom.app ((sheafHomComplex X F G).obj) ≫
          (CategoryTheory.shiftFunctor
            (DerivedCategory (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n).map
            (sheafHomComplexUnit X F G) := by
  rw [sheafHomComplexUnit_eq_derivedSheafHomComparison_inv,
    sheafHomComplexUnit_eq_derivedSheafHomComparison_inv,
    derivedSheafHomTargetShiftIsoOfKInjective_hom, Iso.inv_hom_id_assoc]

/-! ### The complex of global sections against the translation -/

/-- **The complex of global sections commutes with the translation.** For a complex `H` of
`O`-modules, `Γ(C, H[n]) = Γ(C, H)[n]` as complexes of abelian groups.

This is Mathlib's commutation of `CategoryTheory.Functor.mapHomologicalComplex` with the
translation, of which `AlgebraicGeometry.RingedSite.globalSectionsComplex` is an instance; its
components are identities. -/
def globalSectionsComplexShiftIso
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    globalSectionsComplex X (H⟦n⟧) ≅ (globalSectionsComplex X H)⟦n⟧ :=
  (((moduleGlobalSections X).mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).app H

/-- The commutation of the complex of global sections with the translation is the identity in
each degree. -/
@[simp]
theorem globalSectionsComplexShiftIso_hom_f
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n i : ℤ) :
    (globalSectionsComplexShiftIso X H n).hom.f i = 𝟙 _ := rfl

/-- The inverse of the commutation of the complex of global sections with the translation is the
identity in each degree. -/
@[simp]
theorem globalSectionsComplexShiftIso_inv_f
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n i : ℤ) :
    (globalSectionsComplexShiftIso X H n).inv.f i = 𝟙 _ := rfl

/-! ### The universe lift against the translation -/

/-- **The comparison of a complex of abelian groups with its degreewise universe lift is
compatible with the translation.** Both sides are `ULift.down` in each degree. -/
theorem uliftComplexSelfIso_shift (D : CochainComplex AddCommGrpCat.{u} ℤ) (n : ℤ) :
    (uliftComplexSelfIso (D⟦n⟧)).hom =
      ((AddCommGrpCat.uliftFunctor.{u, u}.mapHomologicalComplex
            (ComplexShape.up ℤ)).commShiftIso n).hom.app D ≫
        (CategoryTheory.shiftFunctor (CochainComplex AddCommGrpCat.{u} ℤ) n).map
          (uliftComplexSelfIso D).hom := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  simp only [HomologicalComplex.comp_f,
    CategoryTheory.Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
  rfl

/-! ### The global description of Tag 0A8Z against the translation -/

section GlobalDescription

open CochainComplex.HomComplex

/-- **The global description of the internal Hom complex is compatible with the translation in
its covariant variable.** For complexes `F` and `G` of `O`-modules and `a : ℤ`, the two routes
from `Γ(C, SheafHom(F, G))[a]` to the Hom complex `Hom^•(F, G[a])` agree: moving the shift into
the covariant variable on the sheaf side, by the commutation of global sections with the
translation followed by `AlgebraicGeometry.RingedSite.sheafHomTargetShiftIso`, and then applying
Tag 0A8Z; or applying Tag 0A8Z first and moving the shift on the module side, by the Hom-complex
target shift `CochainComplex.HomComplex.homComplexTargetShiftIso`.

This is the fourth and last factor of
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom` against the translation. Both shifts
are the sign-free reindexing `CochainComplex.HomComplex.Cochain.rightShift`, so no sign survives;
see the implementation notes. -/
theorem globalSectionsIso_sheafHomTargetShiftIso
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (a : ℤ) :
    (globalSectionsComplexShiftIso X (sheafHomComplex X F G).obj a).inv ≫
        globalSectionsComplexMap X (sheafHomTargetShiftIso X (K := F) (M := G) a).hom ≫
          (sheafHomComplex X F (G⟦a⟧)).globalSectionsIso.hom =
      (CategoryTheory.shiftFunctor (CochainComplex AddCommGrpCat.{u} ℤ) a).map
          (sheafHomComplex X F G).globalSectionsIso.hom ≫
        ((AddCommGrpCat.uliftFunctor.{u, u}.mapHomologicalComplex
            (ComplexShape.up ℤ)).commShiftIso a).inv.app (F.HomComplex G) ≫
          (AddCommGrpCat.uliftFunctor.{u, u}.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (homComplexTargetShiftIso F G a).hom := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply ULift.ext
  refine Cochain.ext _ _ fun p q hpq => ?_
  ext U x
  obtain ⟨U⟩ := U
  simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply,
    globalSectionsComplexShiftIso_inv_f,
    CategoryTheory.Functor.mapHomologicalComplex_commShiftIso_inv_app_f,
    ConcreteCategory.id_apply]
  simp only [Functor.comp_obj, ConcreteCategory.id_apply]
  -- The module side: `Tag 0A8Z` in degree `n + a`, then `rightShift`.
  have hR : (AddCommGrpCat.Hom.hom
        (((AddCommGrpCat.uliftFunctor.{u, u}.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (homComplexTargetShiftIso F G a).hom).f n)
        (AddCommGrpCat.Hom.hom
          (((CategoryTheory.shiftFunctor (CochainComplex AddCommGrpCat.{u} ℤ) a).map
            (sheafHomComplex X F G).globalSectionsIso.hom).f n) s)).down =
      (AddCommGrpCat.Hom.hom ((sheafHomComplex X F G).globalSectionsIso.hom.f (n + a))
        s).down.rightShift a n rfl := rfl
  have hR2 : ((AddCommGrpCat.Hom.hom ((sheafHomComplex X F G).globalSectionsIso.hom.f (n + a))
        s).down.rightShift a n rfl).v p q hpq =
      (AddCommGrpCat.Hom.hom ((sheafHomComplex X F G).globalSectionsIso.hom.f (n + a))
        s).down.v p (q + a) (by omega) ≫
          (G.shiftFunctorObjXIso a q (q + a) rfl).inv :=
    Cochain.rightShift_v _ a n rfl p q hpq (q + a) (by omega)
  rw [hR, hR2,
    sheafHomComplex_globalSectionsIso_v_app X F (G⟦a⟧) n p q hpq _ U x]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq,
    eqToIso.inv, eqToHom_refl, Category.comp_id]
  rw [sheafHomComplex_globalSectionsIso_v_app X F G (n + a) p (q + a) (by omega) s U x]
  -- The sheaf side, on sections over `U`: the same reindexing, by `cochainTargetShift`.
  have hS : (Cochain.v (AddCommGrpCat.Hom.hom
        (((sheafHomComplex X F (G⟦a⟧)).sectionsIso U).hom.f n)
        ((AddCommGrpCat.Hom.hom
          ((globalSectionsComplexMap X (sheafHomTargetShiftIso X (K := F) (M := G) a).hom).f n)
          s).val (op U))) p q hpq) =
      (Cochain.v (AddCommGrpCat.Hom.hom (((sheafHomComplex X F G).sectionsIso U).hom.f (n + a))
        (s.val (op U))) p (q + a) (by omega)) :=
    (congrArg (fun c : Cochain (restrictComplex X F U) (restrictComplex X (G⟦a⟧) U) n =>
        c.v p q hpq)
      (sectionsEquiv_sheafHomTargetShiftIso_hom X (K := F) (M := G) a n U
        (show ((((sheafHomComplex X F G).obj)⟦a⟧).X n).val.obj (op U) from
          s.val (op U)))).trans
    (cochainTargetShift_v X U a (n + a) n (by omega) _ p q hpq)
  rw [hS]

end GlobalDescription

/-! ### The unit of derived global sections against the translation -/

/-- **The comparison from global sections to derived global sections is compatible with the
translation**, as a compatibility of the natural transformation
`AlgebraicGeometry.RingedSite.globalSectionsDerivedUnitNatTrans` with the shift.

The transformation is the composite of four whiskerings, and each of the four is compatible with
the shift: the two comparisons `CategoryTheory.DerivedCategory.quotientCompQhIso` and
`CategoryTheory.Functor.mapHomotopyCategoryFactors` by Mathlib's instances for them, and the unit
of the derived functor by Mathlib's
`CategoryTheory.Functor.RightDerivedCommShift.natTrans_commShift`. Their four compatibilities
telescope.

*Why this is proved by hand rather than inferred.* `CategoryTheory.Functor.CommShift` is a class
of *data*, and the functor through which two consecutive whiskerings are composed —
`Γ(C, -) ⋙ K(O) ⟶ D(Ab)` — receives two different instances depending on how the composition is
bracketed, one from each neighbour. So `CategoryTheory.NatTrans.CommShift.comp` does not apply to
the composite even though each factor has the instance, and instance search for the composite
fails. Fixing the two functors by stating
`CategoryTheory.NatTrans.CommShiftCore` ourselves pins the canonical instances and the four
compatibilities then chain. -/
theorem commShiftCore_globalSectionsDerivedUnitNatTrans (n : ℤ) :
    NatTrans.CommShiftCore (globalSectionsDerivedUnitNatTrans X) n := by
  constructor
  ext H
  have p1 := NatTrans.shift_app_comm (Functor.whiskerLeft
    ((moduleGlobalSections X).mapHomologicalComplex (ComplexShape.up ℤ))
    (DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).inv) n H
  have p2 := NatTrans.shift_app_comm (Functor.whiskerRight
    (((moduleGlobalSections X).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv)
    DerivedCategory.Qh) n H
  have p3 := NatTrans.shift_app_comm (Functor.whiskerLeft
    (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))
    (derivedModuleGlobalSectionsUnit X)) n H
  have p4 := NatTrans.shift_app_comm (Functor.whiskerRight
    (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom
    (derivedModuleGlobalSections X)) n H
  simp only [globalSectionsDerivedUnitNatTrans, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
    Functor.comp_map, CategoryTheory.Functor.map_comp, Category.assoc] at p1 p2 p3 p4 ⊢
  rw [reassoc_of% p1, reassoc_of% p2, reassoc_of% p3, p4]

/-- **The comparison from global sections to derived global sections is compatible with the
translation**, read at a complex: the comparison for `H[n]`, followed by the commutation of
derived global sections with the translation, is the commutation of the complex of global
sections and of the localization functor with the translation, followed by the `n`-shift of the
comparison for `H`.

This is `AlgebraicGeometry.RingedSite.commShiftCore_globalSectionsDerivedUnitNatTrans` read on
components. -/
theorem globalSectionsDerivedUnit_shift
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    DerivedCategory.Q.map (globalSectionsComplexShiftIso X H n).hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app (globalSectionsComplex X H) ≫
          (CategoryTheory.shiftFunctor (DerivedCategory AddCommGrpCat.{u}) n).map
            (globalSectionsDerivedUnit X H) =
      globalSectionsDerivedUnit X (H⟦n⟧) ≫
        (derivedModuleGlobalSections X).map
            ((DerivedCategory.Q.commShiftIso n).hom.app H) ≫
          ((derivedModuleGlobalSections X).commShiftIso n).hom.app (DerivedCategory.Q.obj H) := by
  have h := NatTrans.CommShiftCore.shift_app_comm (globalSectionsDerivedUnitNatTrans X)
    (commShiftCore_globalSectionsDerivedUnitNatTrans X n) H
  simp only [globalSectionsDerivedUnitNatTrans_app, Functor.commShiftIso_comp_hom_app,
    Functor.comp_obj, Category.assoc] at h
  exact h

/-! ### The commutation with the translation at a representative pair -/

/-- The morphism induced on the derived internal Hom by a pair of identities is the identity. -/
private theorem derivedSheafHom_induced_id
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedSheafHomBifunctor X).map (𝟙 L).op).app M ≫
        ((derivedSheafHomBifunctor X).obj (op L)).map (𝟙 M) =
      𝟙 (((derivedSheafHomBifunctor X).obj (op L)).obj M) := by
  simp

/-- The inverse form of `AlgebraicGeometry.RingedSite.derivedSheafHomObjectsModelIso_refl`. -/
private theorem derivedSheafHomObjectsModelIso_refl_inv
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (derivedSheafHomObjectsModelIso X (Iso.refl (DerivedCategory.Q.obj A))
        (Iso.refl (DerivedCategory.Q.obj I))).inv = 𝟙 _ := by
  simp [derivedSheafHomObjectsModelIso]

variable [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The commutation of the derived internal Hom with the translation, read at a representative
pair, is the commutation at that pair.** For a K-injective complex `G` and an arbitrary complex
`F`, the identification `RSheafHom(Q F, (Q G)[n]) ≅ RSheafHom(Q F, Q G)[n]` built from the chosen
K-injective models is, after moving the covariant variable from `(Q G)[n]` to `Q (G[n])` along the
commutation of the localization functor with the translation, the identification
`AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIsoOfKInjective` at `(F, G)` itself.

This is the analogue for the target-shift identification of
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_eq_ofKFlat`, and it is what the
degree-`n` reading of the canonical map needs in order to use that one: the degree-`n` form of the
global derived hom is built from
`AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIso` at the chosen models, whereas the
degree-zero reading of the canonical map lives at the pair `(F, G[n])`.

Unlike the degree-zero statement it needs **no** K-flat refinement: the chosen model is
K-injective, so `AlgebraicGeometry.RingedSite.exists_Q_map_eq_of_isKInjective` realizes the
comparison of the covariant variable by a morphism of complexes, and *also* realizes the
comparison of the contravariant variable, because there the chosen model is the *target* of the
morphism needed. Both comparisons are therefore classes of morphisms of complexes and the
naturality
`AlgebraicGeometry.RingedSite.derivedSheafHomTargetShiftIsoOfKInjective_hom_naturality`
applies directly. -/
theorem derivedSheafHomTargetShiftIso_eq_ofKInjective
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [G.IsKInjective] (n : ℤ) :
    (((derivedSheafHomBifunctor X).map (𝟙 (DerivedCategory.Q.obj F)).op).app
            ((DerivedCategory.Q.obj G)⟦n⟧) ≫
          ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj F))).map
            ((DerivedCategory.Q.commShiftIso n).inv.app G)) ≫
        (derivedSheafHomTargetShiftIsoOfKInjective X F G n).hom =
      (derivedSheafHomTargetShiftIso X (DerivedCategory.Q.obj F)
        (DerivedCategory.Q.obj G) n).hom := by
  obtain ⟨a, ha⟩ := exists_Q_map_eq_of_isKInjective X
    (kInjectiveModelIso X (DerivedCategory.Q.obj F)).inv
  obtain ⟨b, hb⟩ := exists_Q_map_eq_of_isKInjective X
    (kInjectiveModelIso X (DerivedCategory.Q.obj G)).hom
  have ha' : DerivedCategory.Q.map a =
      (Iso.refl (DerivedCategory.Q.obj F)).hom ≫ 𝟙 (DerivedCategory.Q.obj F) ≫
        (kInjectiveModelIso X (DerivedCategory.Q.obj F)).inv := by
    rw [ha]
    simp
  have hb' : DerivedCategory.Q.map
        ((CategoryTheory.shiftFunctor
          (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
            n).map b) =
      ((DerivedCategory.Q.commShiftIso n).app
            (kInjectiveModel X (DerivedCategory.Q.obj G)) ≪≫
          (CategoryTheory.shiftFunctor
            (DerivedCategory (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n).mapIso
            (kInjectiveModelIso X (DerivedCategory.Q.obj G))).hom ≫
        (DerivedCategory.Q.commShiftIso n).inv.app G ≫
          (Iso.refl (DerivedCategory.Q.obj (G⟦n⟧))).inv := by
    have h := CategoryTheory.Functor.commShiftIso_hom_naturality
      (F := DerivedCategory.Q
        (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) b n
    rw [hb] at h
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
    rw [← h]
    simp
  have h1 := derivedSheafHomObjectsModelIso_hom_naturality X
    (kInjectiveModelIso X (DerivedCategory.Q.obj F))
    (Iso.refl (DerivedCategory.Q.obj F))
    ((DerivedCategory.Q.commShiftIso n).app (kInjectiveModel X (DerivedCategory.Q.obj G)) ≪≫
      (CategoryTheory.shiftFunctor
        (DerivedCategory (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n).mapIso
        (kInjectiveModelIso X (DerivedCategory.Q.obj G)))
    (Iso.refl (DerivedCategory.Q.obj (G⟦n⟧)))
    (𝟙 (DerivedCategory.Q.obj F)) ((DerivedCategory.Q.commShiftIso n).inv.app G)
    a ((CategoryTheory.shiftFunctor
        (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
        n).map b)
    ha' hb'
  have h2 := derivedSheafHomObjectsModelIso_inv_naturality X
    (kInjectiveModelIso X (DerivedCategory.Q.obj F))
    (Iso.refl (DerivedCategory.Q.obj F))
    (kInjectiveModelIso X (DerivedCategory.Q.obj G))
    (Iso.refl (DerivedCategory.Q.obj G))
    (𝟙 (DerivedCategory.Q.obj F)) (𝟙 (DerivedCategory.Q.obj G)) a b ha' (by rw [hb]; simp)
  rw [derivedSheafHomObjectsModelIso_refl X F (G⟦n⟧), Category.comp_id] at h1
  rw [derivedSheafHomObjectsModelIso_refl_inv X F G, Category.comp_id,
    derivedSheafHom_induced_id X, Category.comp_id] at h2
  have hs := derivedSheafHomTargetShiftIsoOfKInjective_hom_naturality X a b n
  rw [h1, derivedSheafHomTargetShiftIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc] at hs ⊢
  rw [hs, h2]

end AlgebraicGeometry.RingedSite

end
