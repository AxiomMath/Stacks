module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.RepresentativeHomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopSingleProjection
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TruncGESingleHomology

/-!
# The canonical map `K ⟶ Hᵈ(K)[-d]` computed on a representative

For an object `K` of a derived category with no cohomology above `d` there is a canonical
morphism `κ : K ⟶ Hᵈ(K)[-d]`, the truncation projection followed by the identification of
`τ^{≥d} K` with a single complex, and `Stacks.TruncGESingleHomology` shows that `κ` is the
**only** morphism inducing the identity on `Hᵈ`. That characterization is useless until some
*other* description of a morphism `K ⟶ Hᵈ(K)[-d]` is available to be recognized as `κ`.

This file supplies one. If `K` is the class of a cochain complex `P` with no terms above `d`,
then `P` has the canonical projection onto the single complex on `Hᵈ(P)`
(`Stacks.TopSingleProjection.toSingleTop`), and carrying that into the derived category and
along the identification of `Hᵈ(P)` with `Hᵈ(K)` gives a morphism `K ⟶ Hᵈ(K)[-d]`. It is `κ`.

## Main definitions

* `Stacks.RepresentativeSingle.representativeToSingle`: that morphism.

## Main results

* `Stacks.RepresentativeSingle.eq_truncGEπ_comp`: it **is** `κ`. This is the bridge between a
  statement about the truncation of an object of the derived category and a statement about a
  complex, and it is what lets a cycle-class identity at the top degree be discharged.
* `Stacks.RepresentativeSingle.homologyMap_comp_classOfRepresentative`: the cohomology class of
  a representative, read back through the identification of the derived category with the
  homotopy category, is the class of the identification itself. This is the `Qh`-to-`Q`
  translation of `Stacks.RepresentativeHomology.classOfRepresentative`, and the only input of
  the main result that is not formal.
* `Stacks.RepresentativeSingle.homologyFunctorFactorsh_hom_app_comp`: the same translation for
  the factorization of `Hᵈ` itself.
* `Stacks.RepresentativeSingle.singleFunctorIsoCompQh_inv_app`: the inverse half of
  `Stacks.TopSingleProjection.singleFunctorIsoCompQh_hom_app`.

## Implementation notes

*Two identifications of `Hᵈ` have to be brought together, and Mathlib's bridge between them is
only stated in a bracketing that `Category.assoc` cannot repair here.* The derived category
factorizes `Hᵈ` twice, once over `DerivedCategory.Q` and once over `DerivedCategory.Qh`, and
`DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj` relates the two. Its
`@[reassoc]` form is what is used: substituting the plain form leaves a goal bracketed as
`f ≫ (g ≫ h ≫ k) ≫ l`, and `Category.assoc` refuses it — the objects
`HomologicalComplex.homology P d` and
`(HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) d).obj P` are `rfl`-equal but not
interchangeable while a motive is being formed. The `_assoc` form produces the composite
already right-associated, and the two isomorphism cancellations that remain are applied in
**term mode**, which forms no motive.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category HomologicalComplex
open Stacks.TopSingleProjection Stacks.RepresentativeHomology

namespace Stacks.RepresentativeSingle

open DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- **The factorization of `Hᵈ` over the homotopy category, in terms of the factorization over
the derived category.** Mathlib relates the two by
`DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj`, which leaves the
homotopy-category factorization on the right; this is the form with it cancelled, which is the
one a consumer that works with cochain complexes needs. -/
theorem homologyFunctorFactorsh_hom_app_comp (Y : CochainComplex C ℤ) (d : ℤ) :
    (homologyFunctorFactorsh C d).hom.app
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj Y) ≫
        (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) d).hom.app Y =
      (homologyFunctor C d).map ((quotientCompQhIso C).hom.app Y) ≫
        (homologyFunctorFactors C d).hom.app Y := by
  simp only [homologyFunctorFactorsh_hom_app_quotient_obj_assoc]
  refine Eq.trans (congrArg (fun t =>
      (homologyFunctor C d).map ((quotientCompQhIso C).hom.app Y) ≫
        (homologyFunctorFactors C d).hom.app Y ≫ t)
    (Iso.inv_hom_id_app
      (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) d) Y)) ?_
  exact congrArg (fun t =>
    (homologyFunctor C d).map ((quotientCompQhIso C).hom.app Y) ≫ t) (comp_id _)

/-- **The cohomology class of a representative is the class of its identification.** Read
through the identification of the derived category with the homotopy category and the
factorization of `Hᵈ` over the derived category, `classOfRepresentative P e d` is `Hᵈ(e)`. -/
theorem homologyMap_comp_classOfRepresentative (P : CochainComplex C ℤ)
    {K : DerivedCategory C}
    (e : Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P) ≅ K) (d : ℤ) :
    (homologyFunctor C d).map ((quotientCompQhIso C).hom.app P) ≫
        (homologyFunctorFactors C d).hom.app P ≫ classOfRepresentative P e d =
      (homologyFunctor C d).map e.hom := by
  simp only [classOfRepresentative, homologyFunctorFactorsh_inv_app_quotient_obj_assoc]
  refine Eq.trans (congrArg (fun t =>
      (homologyFunctor C d).map ((quotientCompQhIso C).hom.app P) ≫
        (homologyFunctorFactors C d).hom.app P ≫ t)
    (Iso.inv_hom_id_app_assoc
      (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) d) P _)) ?_
  refine Eq.trans (congrArg (fun t =>
      (homologyFunctor C d).map ((quotientCompQhIso C).hom.app P) ≫ t)
    (Iso.hom_inv_id_app_assoc (homologyFunctorFactors C d) P _)) ?_
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, id_comp]

/-- **The cohomology class of a representative is an isomorphism**, being a composite of three
of them. -/
instance isIso_classOfRepresentative (P : CochainComplex C ℤ) {K : DerivedCategory C}
    (e : Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P) ≅ K) (d : ℤ) :
    IsIso (classOfRepresentative P e d) :=
  inferInstanceAs (IsIso
    ((((HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) d).app P).symm ≪≫
      ((homologyFunctorFactorsh C d).app
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P)).symm ≪≫
      (homologyFunctor C d).mapIso e).hom))

/-- The inverse half of `Stacks.TopSingleProjection.singleFunctorIsoCompQh_hom_app`. -/
theorem singleFunctorIsoCompQh_inv_app (M : C) (d : ℤ) :
    (singleFunctorIsoCompQh C d).inv.app M =
      (quotientCompQhIso C).hom.app ((CochainComplex.singleFunctor C d).obj M) :=
  (Iso.comp_inv_eq_id
      ((quotientCompQhIso C).app ((CochainComplex.singleFunctor C d).obj M))).mp
    ((congrArg (fun t => (singleFunctorIsoCompQh C d).inv.app M ≫ t)
        (singleFunctorIsoCompQh_hom_app M d)).symm.trans
      ((singleFunctorIsoCompQh C d).inv_hom_id_app M))

/-- **The `Qh`-spelled map induced by a morphism into a single complex.** Carrying a chain map
into a single complex through `DerivedCategory.Q` and then into the single functor of the
derived category is the same as carrying it through the homotopy category. -/
theorem quotientCompQhIso_hom_app_comp_QToSingle {Y : CochainComplex C ℤ} {M : C} {d : ℤ}
    (v : Y ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) d).obj M) :
    (quotientCompQhIso C).hom.app Y ≫ QToSingle v ≫
        (singleFunctorIsoCompQh C d).hom.app M =
      Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map v) := by
  have hnat : Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map v) ≫
      (quotientCompQhIso C).hom.app
        ((HomologicalComplex.single C (ComplexShape.up ℤ) d).obj M) =
      (quotientCompQhIso C).hom.app Y ≫ QToSingle v :=
    (quotientCompQhIso C).hom.naturality v
  rw [singleFunctorIsoCompQh_hom_app]
  exact (assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ (quotientCompQhIso C).inv.app
        ((HomologicalComplex.single C (ComplexShape.up ℤ) d).obj M)) hnat.symm).trans
      ((assoc _ _ _).trans ((congrArg (fun t =>
          Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map v) ≫ t)
        (Iso.hom_inv_id_app (quotientCompQhIso C) _)).trans (comp_id _))))

/-- The companion of `quotientCompQhIso_hom_app_comp_QToSingle` for the inverse
identification. -/
theorem Qh_map_quotient_map_comp_singleFunctorIsoCompQh_inv {Y : CochainComplex C ℤ} {M : C}
    {d : ℤ} (w : Y ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) d).obj M) :
    Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map w) ≫
        (singleFunctorIsoCompQh C d).inv.app M =
      (quotientCompQhIso C).hom.app Y ≫ QToSingle w := by
  rw [singleFunctorIsoCompQh_inv_app]
  exact (quotientCompQhIso C).hom.naturality w

/-- **A representative of an object with no cohomology above `d` has none either.** -/
theorem isLE_of_representative (P : CochainComplex C ℤ) (d : ℤ) {K : DerivedCategory C}
    (e : Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P) ≅ K)
    (hK : TStructure.t.IsLE K d) : P.IsLE d :=
  (DerivedCategory.isLE_Q_obj_iff P d).1
    (TStructure.t.isLE_of_iso (e.symm ≪≫ (quotientCompQhIso C).app P) d)

/-- **The canonical map `K ⟶ Hᵈ(K)[-d]`, built from a representative.** For a cochain complex
`P` with no terms above `d` and an identification `e` of its class with `K`, this is the
canonical projection of `P` onto the single complex on `Hᵈ(P)`, read in the derived category
and transported along `e` and the induced identification of `Hᵈ(P)` with `Hᵈ(K)`. -/
def representativeToSingle (P : CochainComplex C ℤ) (d : ℤ) [P.IsStrictlyLE d]
    {K : DerivedCategory C}
    (e : Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P) ≅ K) :
    K ⟶ (singleFunctor C d).obj ((homologyFunctor C d).obj K) :=
  e.inv ≫ (quotientCompQhIso C).hom.app P ≫
    QToSingle (toSingleTop P d ≫ (HomologicalComplex.single C (ComplexShape.up ℤ) d).map
      (classOfRepresentative P e d))

/-- **`representativeToSingle` is `κ`.** Given any isomorphism `ε : τ^{≥d} K ≅ Hᵈ(K)[-d]` whose
composite with the truncation projection induces the identity on `Hᵈ` — which is what
`Stacks.TruncGESingleHomology.homologyMap_truncGEπ_truncGELTIso` says of the canonical one — the
morphism built from a representative with no terms above `d` is that composite.

The proof is the uniqueness
`Stacks.TruncGESingleHomology.eq_truncGEπ_comp_of_homologyMap_eq_id`, whose hypothesis is
checked by `Stacks.TopSingleProjection.homologyMap_QToSingle_toSingleTop` — the canonical
projection of `P` induces the identity on `Hᵈ` — together with
`homologyMap_comp_classOfRepresentative`. -/
theorem eq_truncGEπ_comp (P : CochainComplex C ℤ) (d : ℤ) [P.IsStrictlyLE d]
    {K : DerivedCategory C}
    (e : Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P) ≅ K)
    (ε : (TStructure.t.truncGE d).obj K ≅
      (singleFunctor C d).obj ((homologyFunctor C d).obj K))
    (hε : (homologyFunctor C d).map ((TStructure.t.truncGEπ d).app K ≫ ε.hom) ≫
        (singleFunctorCompHomologyFunctorIso C d).hom.app ((homologyFunctor C d).obj K) =
      𝟙 ((homologyFunctor C d).obj K)) :
    (TStructure.t.truncGEπ d).app K ≫ ε.hom = representativeToSingle P d e := by
  have hc : HomologicalComplex.homologyMap (toSingleTop P d) d ≫
      ((HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) d (P.homology d)).hom ≫
        classOfRepresentative P e d) = classOfRepresentative P e d :=
    (assoc _ _ _).symm.trans ((congrArg (fun t => t ≫ classOfRepresentative P e d)
      (homologyMap_toSingleTop P d)).trans (id_comp _))
  have hΨ : (homologyFunctor C d).map ((quotientCompQhIso C).hom.app P) ≫
        (homologyFunctor C d).map (QToSingle (toSingleTop P d ≫
          (HomologicalComplex.single C (ComplexShape.up ℤ) d).map
            (classOfRepresentative P e d))) ≫
        (singleFunctorCompHomologyFunctorIso C d).hom.app ((homologyFunctor C d).obj K) =
      (homologyFunctor C d).map e.hom := by
    rw [homologyMap_QToSingle_comp]
    exact (congrArg (fun t =>
        (homologyFunctor C d).map ((quotientCompQhIso C).hom.app P) ≫
          (homologyFunctorFactors C d).hom.app P ≫ t) hc).trans
      (homologyMap_comp_classOfRepresentative P e d)
  have hφ : (homologyFunctor C d).map (representativeToSingle P d e) ≫
      (singleFunctorCompHomologyFunctorIso C d).hom.app ((homologyFunctor C d).obj K) =
      𝟙 ((homologyFunctor C d).obj K) := by
    rw [representativeToSingle, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp, assoc, assoc, hΨ,
      ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id]
  exact (Stacks.TruncGESingleHomology.eq_truncGEπ_comp_of_homologyMap_eq_id K d ε hε _ hφ).symm

section Assembly

variable {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]

/-- Reassociation of a five-fold composite against a trailing morphism. Stated in a bare
category, where the two `rfl`-equal spellings of the single functor cannot occur, so that
`Category.assoc` goes through as a rewrite; it is then applied as a **term** at the mixed
spellings, where `Category.assoc` as a rewrite is refused. -/
theorem assoc₅ {W : Type*} [Category W] {X₁ X₂ X₃ X₄ X₅ X₆ X₇ : W}
    (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) (c : X₃ ⟶ X₄) (g : X₄ ⟶ X₅) (s : X₅ ⟶ X₆) (t : X₆ ⟶ X₇) :
    (a ≫ b ≫ c ≫ g ≫ s) ≫ t = a ≫ b ≫ c ≫ g ≫ s ≫ t := by
  simp only [assoc]

/-- Reassociation of a four-fold composite against a trailing morphism; see `assoc₅`. -/
theorem assoc₄ {W : Type*} [Category W] {X₁ X₂ X₃ X₄ X₅ X₆ : W}
    (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) (c : X₃ ⟶ X₄) (g : X₄ ⟶ X₅) (t : X₅ ⟶ X₆) :
    (a ≫ b ≫ c ≫ g) ≫ t = a ≫ b ≫ c ≫ g ≫ t := by
  simp only [assoc]

/-- **What a chain map into a single complex does on `Hᵈ`, in the `Qh` spelling.** This is
`Stacks.TopSingleProjection.homologyMap_QToSingle` transported to the spelling in which a
comparison of derived functors has its components, with a trailing morphism `t` carried along so
that no reassociation is needed at the point of use. -/
theorem homologyMap_Qh_map_quotient_map_comp {Y : CochainComplex D ℤ} {M Z : D} {d : ℤ}
    (w : Y ⟶ (HomologicalComplex.single D (ComplexShape.up ℤ) d).obj M) (t : M ⟶ Z) :
    (homologyFunctor D d).map
          (Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map w)) ≫
        (homologyFunctor D d).map ((singleFunctorIsoCompQh D d).inv.app M) ≫
        (singleFunctorCompHomologyFunctorIso D d).hom.app M ≫ t =
      ((homologyFunctorFactorsh D d).hom.app
            ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj Y) ≫
          (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) d).hom.app Y) ≫
        HomologicalComplex.homologyMap w d ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) d M).hom ≫ t := by
  have h1 : (homologyFunctor D d).map
        (Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map w)) ≫
      (homologyFunctor D d).map ((singleFunctorIsoCompQh D d).inv.app M) =
      (homologyFunctor D d).map ((quotientCompQhIso D).hom.app Y) ≫
        (homologyFunctor D d).map (QToSingle w) :=
    ((homologyFunctor D d).map_comp _ _).symm.trans
      ((congrArg ((homologyFunctor D d).map)
          (Qh_map_quotient_map_comp_singleFunctorIsoCompQh_inv w)).trans
        ((homologyFunctor D d).map_comp _ _))
  rw [homologyFunctorFactorsh_hom_app_comp]
  refine Eq.trans (assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫
      (singleFunctorCompHomologyFunctorIso D d).hom.app M ≫ t) h1) ?_
  refine Eq.trans (assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z =>
      (homologyFunctor D d).map ((quotientCompQhIso D).hom.app Y) ≫ z)
    ((assoc _ _ _).symm.trans ((congrArg (fun z => z ≫ t) (homologyMap_QToSingle w)).trans
      ((assoc _ _ _).trans (congrArg (fun z =>
        (homologyFunctorFactors D d).hom.app Y ≫ z) (assoc _ _ _)))))) ?_
  exact (assoc _ _ _).symm

omit [HasDerivedCategory C] [HasDerivedCategory D] in
/-- **The image of the canonical projection, read on `Hᵈ`, inverts the comparison
`mapHomology`.** -/
theorem homologyMap_eq_id (G : C ⥤ D) [G.Additive] [PreservesFiniteColimits G]
    (P : CochainComplex C ℤ) (d : ℤ) [P.IsStrictlyLE d] {M : C}
    (g : P.homology d ⟶ M) [IsIso g]
    (w : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶
      (HomologicalComplex.single D (ComplexShape.up ℤ) d).obj (G.obj M))
    (hw : w = mapToSingleTop G P d ≫
      (HomologicalComplex.single D (ComplexShape.up ℤ) d).map (G.map g)) :
    HomologicalComplex.homologyMap w d ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) d
          (G.obj M)).hom ≫ inv (G.map g) ≫ Stacks.MapHomologyCycles.mapHomology G P d =
      𝟙 (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology d) := by
  subst hw
  rw [HomologicalComplex.homologyMap_comp]
  refine Eq.trans (assoc _ _ _) ?_
  refine Eq.trans (congrArg
    (fun r => HomologicalComplex.homologyMap (mapToSingleTop G P d) d ≫ r)
    ((assoc _ _ _).symm.trans
      ((congrArg (fun r => r ≫ inv (G.map g) ≫
            Stacks.MapHomologyCycles.mapHomology G P d)
          (singleObjHomologySelfIso_hom_naturality (ComplexShape.up ℤ) d (G.map g))).trans
        ((assoc _ _ _).trans (congrArg
          (fun r => (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) d
            (G.obj (P.homology d))).hom ≫ r)
          (IsIso.hom_inv_id_assoc _ _)))))) ?_
  exact homologyMap_mapToSingleTop G P d

/-- **The cycle-free top-degree identity, in a form with no geometry in it.**

Let `G` be an additive right exact functor, `L` a functor of the derived categories, `P` a
cochain complex with no terms above `d`, and `e` an identification of its class with `K`. Suppose
given, in the consumer's spelling rather than as a natural transformation:

* two components `c₁`, `c₂` of a comparison `L(Qh -) ⟶ Qh(G -)`, at `P` and at the single complex
  on `Hᵈ(K)`, together with the **one** naturality square `hsq` between them;
* the counit `hdps` on degree-`d` cohomology at that single complex, together with its unfolding
  `hhdps` into `c₂` and the identifications of the single functors;
* the canonical map `κ : K ⟶ Hᵈ(K)[-d]`, identified by `hκ` with the one a representative
  supplies (`Stacks.RepresentativeSingle.eq_truncGEπ_comp`);
* the top-degree comparison `u`, identified by `hu` with `Hᵈ(L κ)` followed by the counit.

Then the identity holds. The reason the comparison is taken as components plus one square is the
declared target of a natural transformation's component: for
`cmp : Qh ⋙ L ⟶ G.mapHomotopyCategory _ ⋙ Qh` the component at `quot P` has declared target
`(G.mapHomotopyCategory _ ⋙ Qh).obj (quot P)`, which is only `rfl`-equal to
`Qh.obj (quot (G P))`, and a goal mixing the two is not type-correct at the `implicit`
transparency level — after which `rw`, `simp only` **and** `Category.assoc` all refuse it. -/
theorem classOfRepresentative_comp_eq_mapHomology
    (G : C ⥤ D) [G.Additive] [PreservesFiniteColimits G]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (P : CochainComplex C ℤ) (d : ℤ) [P.IsStrictlyLE d]
    {K : DerivedCategory C}
    (e : Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P) ≅ K)
    (v : P ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) d).obj
      ((homologyFunctor C d).obj K))
    (hv : v = toSingleTop P d ≫ (HomologicalComplex.single C (ComplexShape.up ℤ) d).map
      (classOfRepresentative P e d))
    (c₁ : L.obj (Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P)) ⟶
      Qh.obj ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))
    (c₂ : L.obj (Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single C (ComplexShape.up ℤ) d).obj
            ((homologyFunctor C d).obj K)))) ⟶
      Qh.obj ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single C (ComplexShape.up ℤ) d).obj
            ((homologyFunctor C d).obj K)))))
    (hsq : L.map (Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map v)) ≫ c₂ =
      c₁ ≫ Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map v)))
    (hdps : (homologyFunctor D d).obj
          (L.obj ((singleFunctor C d).obj ((homologyFunctor C d).obj K))) ⟶
      G.obj ((homologyFunctor C d).obj K))
    (hhdps : hdps =
      (homologyFunctor D d).map
          (L.map ((singleFunctorIsoCompQh C d).hom.app ((homologyFunctor C d).obj K)) ≫ c₂ ≫
            Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
              ((singleMapHomologicalComplex G (ComplexShape.up ℤ) d).hom.app
                ((homologyFunctor C d).obj K))) ≫
            (singleFunctorIsoCompQh D d).inv.app
              (G.obj ((homologyFunctor C d).obj K))) ≫
        (singleFunctorCompHomologyFunctorIso D d).hom.app
          (G.obj ((homologyFunctor C d).obj K)))
    (κ : K ⟶ (singleFunctor C d).obj ((homologyFunctor C d).obj K))
    (hκ : κ = e.inv ≫ (quotientCompQhIso C).hom.app P ≫ QToSingle v)
    (u : G.obj ((homologyFunctor C d).obj K) ≅ (homologyFunctor D d).obj (L.obj K))
    (hu : u.inv = (homologyFunctor D d).map (L.map κ) ≫ hdps)
    (comparison : (homologyFunctor D d).obj (L.obj K) ⟶
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology d)
    (hcomparison : comparison =
      (homologyFunctor D d).map (L.map e.inv ≫ c₁) ≫
        (homologyFunctorFactorsh D d).hom.app
          ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) d).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :
    G.map (classOfRepresentative P e d) ≫ u.hom ≫ comparison =
      Stacks.MapHomologyCycles.mapHomology G P d := by
  have hD : (G.mapHomologicalComplex (ComplexShape.up ℤ)).map v ≫
      (singleMapHomologicalComplex G (ComplexShape.up ℤ) d).hom.app
        ((homologyFunctor C d).obj K) =
      mapToSingleTop G P d ≫ (HomologicalComplex.single D (ComplexShape.up ℤ) d).map
        (G.map (classOfRepresentative P e d)) := by
    rw [hv]
    exact map_toSingleTop_comp_singleMap G P d (classOfRepresentative P e d)
  have hL5 := homologyMap_eq_id G P d (classOfRepresentative P e d)
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map v ≫
      (singleMapHomologicalComplex G (ComplexShape.up ℤ) d).hom.app
        ((homologyFunctor C d).obj K)) hD
  have hcomb : (homologyFunctor D d).map (Qh.map
          ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map v))) ≫
        (homologyFunctor D d).map (Qh.map
          ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
            ((singleMapHomologicalComplex G (ComplexShape.up ℤ) d).hom.app
              ((homologyFunctor C d).obj K)))) =
      (homologyFunctor D d).map (Qh.map
        ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map v ≫
            (singleMapHomologicalComplex G (ComplexShape.up ℤ) d).hom.app
              ((homologyFunctor C d).obj K)))) :=
    by simp only [Functor.map_comp]
  have key3 : (homologyFunctor D d).map (Qh.map
          ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map v))) ≫
        (homologyFunctor D d).map (Qh.map
          ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
            ((singleMapHomologicalComplex G (ComplexShape.up ℤ) d).hom.app
              ((homologyFunctor C d).obj K)))) ≫
        (homologyFunctor D d).map ((singleFunctorIsoCompQh D d).inv.app
          (G.obj ((homologyFunctor C d).obj K))) ≫
        (singleFunctorCompHomologyFunctorIso D d).hom.app
          (G.obj ((homologyFunctor C d).obj K)) ≫
        (inv (G.map (classOfRepresentative P e d)) ≫
          Stacks.MapHomologyCycles.mapHomology G P d) =
      (homologyFunctorFactorsh D d).hom.app
          ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) d).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
    refine Eq.trans (assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun z => z ≫
        (homologyFunctor D d).map ((singleFunctorIsoCompQh D d).inv.app
          (G.obj ((homologyFunctor C d).obj K))) ≫
        (singleFunctorCompHomologyFunctorIso D d).hom.app
          (G.obj ((homologyFunctor C d).obj K)) ≫
        (inv (G.map (classOfRepresentative P e d)) ≫
          Stacks.MapHomologyCycles.mapHomology G P d)) hcomb) ?_
    refine Eq.trans (homologyMap_Qh_map_quotient_map_comp _ _) ?_
    refine Eq.trans (congrArg (fun z =>
      ((homologyFunctorFactorsh D d).hom.app
          ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) d).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫ z) hL5) ?_
    exact comp_id _
  have h2a : (homologyFunctor D d).map (L.map ((quotientCompQhIso C).hom.app P ≫
          QToSingle v)) ≫
        (homologyFunctor D d).map (L.map
          ((singleFunctorIsoCompQh C d).hom.app ((homologyFunctor C d).obj K))) =
      (homologyFunctor D d).map (L.map (Qh.map
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map v))) :=
    by
    rw [← Functor.map_comp, ← L.map_comp, assoc]
    exact congrArg (fun t => (homologyFunctor D d).map (L.map t))
      (quotientCompQhIso_hom_app_comp_QToSingle v)
  have h2b : (homologyFunctor D d).map (L.map (Qh.map
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map v))) ≫
        (homologyFunctor D d).map c₂ =
      (homologyFunctor D d).map c₁ ≫
        (homologyFunctor D d).map (Qh.map
          ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map v))) :=
    by rw [← Functor.map_comp, hsq, Functor.map_comp]
  have hhdps' : hdps =
      (homologyFunctor D d).map
          (L.map ((singleFunctorIsoCompQh C d).hom.app ((homologyFunctor C d).obj K))) ≫
        (homologyFunctor D d).map c₂ ≫
        (homologyFunctor D d).map (Qh.map
          ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
            ((singleMapHomologicalComplex G (ComplexShape.up ℤ) d).hom.app
              ((homologyFunctor C d).obj K)))) ≫
        (homologyFunctor D d).map ((singleFunctorIsoCompQh D d).inv.app
          (G.obj ((homologyFunctor C d).obj K))) ≫
        (singleFunctorCompHomologyFunctorIso D d).hom.app
          (G.obj ((homologyFunctor C d).obj K)) := by
    rw [hhdps]
    refine Eq.trans (congrArg (fun z => z ≫
        (singleFunctorCompHomologyFunctorIso D d).hom.app
          (G.obj ((homologyFunctor C d).obj K)))
      (((homologyFunctor D d).map_comp _ _).trans (congrArg (fun z =>
          (homologyFunctor D d).map (L.map ((singleFunctorIsoCompQh C d).hom.app
            ((homologyFunctor C d).obj K))) ≫ z)
        (((homologyFunctor D d).map_comp _ _).trans (congrArg (fun z =>
            (homologyFunctor D d).map c₂ ≫ z)
          ((homologyFunctor D d).map_comp _ _)))))) ?_
    exact assoc₄ _ _ _ _ _
  have key2 : (homologyFunctor D d).map (L.map ((quotientCompQhIso C).hom.app P ≫
          QToSingle v)) ≫
        hdps ≫ (inv (G.map (classOfRepresentative P e d)) ≫
          Stacks.MapHomologyCycles.mapHomology G P d) =
      (homologyFunctor D d).map c₁ ≫
        (homologyFunctorFactorsh D d).hom.app
          ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) d).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
    rw [hhdps']
    refine Eq.trans (congrArg (fun z =>
      (homologyFunctor D d).map (L.map ((quotientCompQhIso C).hom.app P ≫
        QToSingle v)) ≫ z) (assoc₅ _ _ _ _ _ _)) ?_
    refine Eq.trans (assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun z => z ≫ _) h2a) ?_
    refine Eq.trans (assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun z => z ≫ _) h2b) ?_
    refine Eq.trans (assoc _ _ _) ?_
    exact congrArg (fun z => (homologyFunctor D d).map c₁ ≫ z) key3
  have hXe : (homologyFunctor D d).map (L.map e.inv) ≫
      (homologyFunctor D d).map (L.map ((quotientCompQhIso C).hom.app P ≫ QToSingle v)) =
      (homologyFunctor D d).map (L.map κ) :=
    by rw [← Functor.map_comp, ← L.map_comp, hκ]
  have hcomp2 : comparison = u.inv ≫ (inv (G.map (classOfRepresentative P e d)) ≫
      Stacks.MapHomologyCycles.mapHomology G P d) := by
    rw [hcomparison, CategoryTheory.Functor.map_comp]
    refine Eq.trans (assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun z =>
      (homologyFunctor D d).map (L.map e.inv) ≫ z) key2.symm) ?_
    refine Eq.trans (assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun z => z ≫ hdps ≫ (inv (G.map
      (classOfRepresentative P e d)) ≫ Stacks.MapHomologyCycles.mapHomology G P d)) hXe) ?_
    exact (assoc _ _ _).symm.trans (congrArg (fun z => z ≫ (inv (G.map
      (classOfRepresentative P e d)) ≫ Stacks.MapHomologyCycles.mapHomology G P d)) hu.symm)
  exact (congrArg (fun z => G.map (classOfRepresentative P e d) ≫ z)
      ((congrArg (fun z => u.hom ≫ z) hcomp2).trans (u.hom_inv_id_assoc _))).trans
    (IsIso.hom_inv_id_assoc _ _)

end Assembly

end Stacks.RepresentativeSingle

end
