module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CochainComplexPlusDerivedUnit
public import StacksFrontier.Homology.DerivedIndexing.Composite

/-!
# The derived-functor unit at a complex concentrated in one degree

Let `P : 𝒜 ⥤ ℬ` be an additive functor between abelian categories, with `𝒜` having enough
injectives, and let `ℱ` be an object of `𝒜`. There are two canonical maps

`(Pℱ)[-q] ⟶ RP(ℱ[-q])`

in `D⁺(ℬ)` on offer, and they are built in different worlds. The first is assembled from the
morphism of complexes `HomologicalComplex.singleMapHomologicalComplex` identifying `P` of a
complex concentrated in degree `q` with the complex concentrated in degree `q` on `Pℱ`, followed
by the generic derived-functor unit `CategoryTheory.Functor.mapCochainComplexPlusDerivedUnit` on
bounded-below *complexes*; it is available in every degree `q`. The second is
`Stacks.DerivedIndexing.rightDerivedPlusUnitSingle`, assembled out of the comparisons of single
functors in the bounded-below *homotopy* category, and is the one
`Stacks.DerivedIndexing.rightDerivedPlusEdge` — hence [Stacks, Tag 09NU]'s pullback read in the
`ℤ`-indexing — is built from; it is stated only in degree `q = 0`.

This file identifies the two in degree zero, and gives the first one a closed form in every
degree, in the shape the degree-zero comparison takes. That is what lets a statement about the
degreewise comparison of a composite of right derived functors be moved to the complex-level
pullback maps the de Rham first Chern class of [Stacks, Tag 0FLE] is built from.

## Main definitions

* `Stacks.DerivedIndexing.singlePlusFunctor`: an object placed in cohomological degree `q`, as a
  *bounded-below* complex; composed with the localization it is
  `DerivedCategory.Plus.singleFunctor`, on the nose.
* `Stacks.DerivedIndexing.mapSinglePlus`: the morphism of bounded-below complexes
  `(Pℱ)[-q] ⟶ P(ℱ[-q])`, i.e. `HomologicalComplex.singleMapHomologicalComplex` read in
  bounded-below complexes.
* `Stacks.DerivedIndexing.singleDerivedUnit`: the canonical map `(Pℱ)[-q] ⟶ RP(ℱ[-q])` in
  `D⁺(ℬ)` assembled from `mapSinglePlus` and the derived-functor unit on bounded-below complexes.

## Main results

* `Stacks.DerivedIndexing.singleFunctorPlusIsoCompQh_hom_app`: **the comparison of the single
  functor into `D⁺(𝒜)` with the one into `K⁺(𝒜)` is the comparison of the two localizations**,
  evaluated at the complex concentrated in degree `q`. Both are preimages under the fully
  faithful inclusion `D⁺(𝒜) ⥤ D(𝒜)`, and on the unbounded derived category the identity is the
  definition of `DerivedCategory.singleFunctors` as a postcomposition.
* `Stacks.DerivedIndexing.singleDerivedUnit_eq`: **the closed form of the degree-`q` unit**: the
  comparison of the two localizations at `(Pℱ)[-q]`, the class of the morphism of complexes, the
  unit of `RP`, and the comparison of the two localizations at `ℱ[-q]`.
* `Stacks.DerivedIndexing.singleDerivedUnit_zero`: **in degree zero the unit assembled here is
  `Stacks.DerivedIndexing.rightDerivedPlusUnitSingle`**, the map the degreewise comparison of a
  composite of right derived functors is built from.

## Implementation notes

Every identity here is between two preimages under the fully faithful inclusion
`DerivedCategory.Plus.ι`, so each is proved by `CategoryTheory.Functor.map_injective` followed by
a computation in the unbounded derived category, where the comparisons involved
(`DerivedCategory.Plus.QhCompιIsoιCompQh`, `HomotopyCategory.Plus.quotientCompιIso`) have
identity components. That computation is done by `show`-ing the reduced form, exactly as in
`AlgebraicGeometry.Scheme.Hom.plusQIsoOn_eq`: the two readings of a complex concentrated in one
degree — as the value of `singlePlusFunctor` and as the value of
`DerivedCategory.Plus.singleFunctor` — agree only definitionally, so a `rw` that moves a
morphism between them builds a motive that is not type-correct at `implicit` transparency. For
the same reason `singleDerivedUnit_eq` is assembled by a chain of term-mode `congrArg`s rather
than by rewriting.

## References

* [Stacks Project, Tag 0FMD](https://stacks.math.columbia.edu/tag/0FMD)
* [Stacks Project, Tag 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v v' u u' w w'

namespace Stacks.DerivedIndexing

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]

/-- **An object placed in cohomological degree `q`, as a bounded-below complex.** Composed with
the localization `DerivedCategory.Plus.Q` it is `DerivedCategory.Plus.singleFunctor` on the
nose. -/
def singlePlusFunctor (C : Type u) [Category.{v} C] [Abelian C] (q : ℤ) :
    C ⥤ CochainComplex.Plus C :=
  ObjectProperty.lift _ (CochainComplex.singleFunctor C q) (fun _ => ⟨q, inferInstance⟩)

/-- The localization of a complex concentrated in degree `q` is the single functor into the
bounded-below derived category. True by definition. -/
theorem singlePlusFunctor_comp_Q (q : ℤ) :
    singlePlusFunctor C q ⋙ DerivedCategory.Plus.Q =
      DerivedCategory.Plus.singleFunctor C q := rfl

/-- **The comparison of the two localizations of bounded-below complexes, read through the
inclusion of the bounded-below derived category in the unbounded one.** The two extra factors
the bounded-below comparison carries are identities. -/
theorem ι_map_quotientCompQhIso_hom_app (L : CochainComplex.Plus C) :
    DerivedCategory.Plus.ι.map
        ((DerivedCategory.Plus.quotientCompQhIso C).hom.app L) =
      (DerivedCategory.quotientCompQhIso C).hom.app L.obj :=
  rfl

/-- `ι_map_quotientCompQhIso_hom_app` for the inverse, by uniqueness of inverses. -/
theorem ι_map_quotientCompQhIso_inv_app (L : CochainComplex.Plus C) :
    DerivedCategory.Plus.ι.map
        ((DerivedCategory.Plus.quotientCompQhIso C).inv.app L) =
      (DerivedCategory.quotientCompQhIso C).inv.app L.obj :=
  congrArg Iso.inv (Iso.ext (ι_map_quotientCompQhIso_hom_app L) :
    DerivedCategory.Plus.ι.mapIso ((DerivedCategory.Plus.quotientCompQhIso C).app L) =
      (DerivedCategory.quotientCompQhIso C).app L.obj)

/-- **The comparison of the two single functors, read through the inclusion of the bounded-below
derived category in the unbounded one**: it is the unbounded comparison, by definition, the
bounded-below one being its preimage. -/
theorem ι_map_singleFunctorPlusIsoCompQh_hom_app (q : ℤ) (Z : C) :
    DerivedCategory.Plus.ι.map
        ((CategoryTheory.Functor.singleFunctorPlusIsoCompQh (A := C) q).hom.app Z) =
      (DerivedCategory.singleFunctorIsoCompQh C q).hom.app Z :=
  DerivedCategory.Plus.ι.map_preimage _

/-- **On the unbounded derived category, the comparison of the single functor with the single
functor into the homotopy category is the comparison of the two localizations**, evaluated at
the complex concentrated in degree `q`. This is the definition of
`DerivedCategory.singleFunctors` as the postcomposition of the single functors on complexes with
the localization: the only other factor is an associator, with identity components. -/
theorem singleFunctorIsoCompQh_hom_app (q : ℤ) (Z : C) :
    (DerivedCategory.singleFunctorIsoCompQh C q).hom.app Z =
      (DerivedCategory.quotientCompQhIso C).inv.app
        ((CochainComplex.singleFunctor C q).obj Z) := by
  change (DerivedCategory.quotientCompQhIso C).inv.app
      ((CochainComplex.singleFunctor C q).obj Z) ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- **The comparison of the single functor into `D⁺(𝒜)` with the single functor into `K⁺(𝒜)` is
the comparison of the two localizations of bounded-below complexes**, evaluated at the complex
concentrated in degree `q`. -/
theorem singleFunctorPlusIsoCompQh_hom_app (q : ℤ) (Z : C) :
    (CategoryTheory.Functor.singleFunctorPlusIsoCompQh (A := C) q).hom.app Z =
      (DerivedCategory.Plus.quotientCompQhIso C).inv.app ((singlePlusFunctor C q).obj Z) :=
  DerivedCategory.Plus.ι.map_injective
    ((ι_map_singleFunctorPlusIsoCompQh_hom_app q Z).trans
      ((singleFunctorIsoCompQh_hom_app q Z).trans
        (ι_map_quotientCompQhIso_inv_app ((singlePlusFunctor C q).obj Z)).symm))

/-- `singleFunctorPlusIsoCompQh_hom_app` read in the other direction, by uniqueness of
inverses. -/
theorem quotientCompQhIso_hom_app_singlePlus (q : ℤ) (Z : C) :
    (DerivedCategory.Plus.quotientCompQhIso C).hom.app ((singlePlusFunctor C q).obj Z) =
      (CategoryTheory.Functor.singleFunctorPlusIsoCompQh (A := C) q).inv.app Z :=
  (congrArg Iso.inv (Iso.ext (singleFunctorPlusIsoCompQh_hom_app q Z) :
    (CategoryTheory.Functor.singleFunctorPlusIsoCompQh (A := C) q).app Z =
      ((DerivedCategory.Plus.quotientCompQhIso C).app
        ((singlePlusFunctor C q).obj Z)).symm)).symm

section Unit

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable (P : C ⥤ D) [P.Additive] [EnoughInjectives C]

/-- **`(Pℱ)[-q] ⟶ P(ℱ[-q])`**: the comparison of an additive functor with the formation of a
complex concentrated in degree `q`, read in bounded-below complexes. The subcategory of
bounded-below complexes is full, so this is
`HomologicalComplex.singleMapHomologicalComplex` and nothing else. -/
def mapSinglePlus (q : ℤ) :
    P ⋙ singlePlusFunctor D q ⟶ singlePlusFunctor C q ⋙ P.mapCochainComplexPlus where
  app X := ObjectProperty.homMk
    ((HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) q).inv.app X)
  naturality _ _ g := ObjectProperty.hom_ext _
    ((HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) q).inv.naturality g)

omit [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C] in
/-- **A morphism out of a complex concentrated in degree `q` whose degree-`q` component factors
through `P` of the degree-`q` term factors through
`HomologicalComplex.singleMapHomologicalComplex`.** Both sides are morphisms out of a complex
concentrated in one degree, so there is a single degree to check, and there the identity is the
cancellation of `HomologicalComplex.singleObjXSelf` against its inverse.

It is stated on abstract data because at the instances it is consumed at — a morphism of sheaves
of abelian groups written in one of the two definitionally equal spellings of that category — the
rewriting tactics build a motive that is not type-correct. -/
theorem mkHomFromSingle_eq_single_map_comp (q : ℤ) {A : D} {Z : C} (u : A ⟶ P.obj Z)
    (hu : ∀ k : ℤ, (ComplexShape.up ℤ).Rel q k →
      (u ≫ P.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q Z).inv) ≫
        ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor C q).obj Z)).d q k = 0) :
    HomologicalComplex.mkHomFromSingle
        (u ≫ P.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q Z).inv) hu =
      (CochainComplex.singleFunctor D q).map u ≫
        (HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) q).inv.app Z := by
  refine HomologicalComplex.from_single_hom_ext ?_
  rw [HomologicalComplex.mkHomFromSingle_f, HomologicalComplex.comp_f]
  simp [CochainComplex.singleFunctor, HomologicalComplex.single_map_f_self]


/-- **The canonical map `(Pℱ)[-q] ⟶ RP(ℱ[-q])` in `D⁺(ℬ)`**: the comparison
`Stacks.DerivedIndexing.mapSinglePlus` of complexes, followed by the derived-functor unit
`CategoryTheory.Functor.mapCochainComplexPlusDerivedUnit` on bounded-below complexes. In degree
zero it is `Stacks.DerivedIndexing.rightDerivedPlusUnitSingle`, by
`Stacks.DerivedIndexing.singleDerivedUnit_zero`. -/
def singleDerivedUnit (q : ℤ) (X : C) :
    (DerivedCategory.Plus.singleFunctor D q).obj (P.obj X) ⟶
      P.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C q).obj X) :=
  DerivedCategory.Plus.Q.map ((mapSinglePlus P q).app X) ≫
    (Functor.mapCochainComplexPlusDerivedUnit P).app ((singlePlusFunctor C q).obj X)

/-- **The closed form of the degree-`q` unit**: the comparison of the two localizations at
`(Pℱ)[-q]`, the class in the bounded-below homotopy category of the morphism of complexes
`(Pℱ)[-q] ⟶ P(ℱ[-q])`, the unit of `RP`, and the comparison of the two localizations at
`ℱ[-q]`. It is the naturality of `DerivedCategory.Plus.quotientCompQhIso.inv` at that morphism
of complexes, together with
`Stacks.DerivedIndexing.singleFunctorPlusIsoCompQh_hom_app` at both ends. -/
theorem singleDerivedUnit_eq (q : ℤ) (X : C) :
    singleDerivedUnit P q X =
      (CategoryTheory.Functor.singleFunctorPlusIsoCompQh (A := D) q).hom.app (P.obj X) ≫
        DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient D).map
          ((mapSinglePlus P q).app X)) ≫
        P.rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.quotient C).obj ((singlePlusFunctor C q).obj X)) ≫
        P.rightDerivedFunctorPlus.map
          ((CategoryTheory.Functor.singleFunctorPlusIsoCompQh (A := C) q).inv.app X) := by
  have hnat := (DerivedCategory.Plus.quotientCompQhIso D).inv.naturality
    ((mapSinglePlus P q).app X)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  have hu := Functor.mapCochainComplexPlusDerivedUnit_app P ((singlePlusFunctor C q).obj X)
  refine Eq.trans (congrArg (fun z =>
    DerivedCategory.Plus.Q.map ((mapSinglePlus P q).app X) ≫ z) hu) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫
    (P.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient C).obj ((singlePlusFunctor C q).obj X)) ≫
      P.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.quotientCompQhIso C).hom.app
          ((singlePlusFunctor C q).obj X)))) hnat) ?_
  refine Eq.trans (congrArg (fun z => (z ≫ DerivedCategory.Plus.Qh.map
      ((HomotopyCategory.Plus.quotient D).map ((mapSinglePlus P q).app X))) ≫
      (P.rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.quotient C).obj ((singlePlusFunctor C q).obj X)) ≫
        P.rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.quotientCompQhIso C).hom.app
            ((singlePlusFunctor C q).obj X))))
    (singleFunctorPlusIsoCompQh_hom_app q (P.obj X)).symm) ?_
  refine Eq.trans (congrArg (fun z =>
      ((CategoryTheory.Functor.singleFunctorPlusIsoCompQh (A := D) q).hom.app (P.obj X) ≫
        DerivedCategory.Plus.Qh.map
          ((HomotopyCategory.Plus.quotient D).map ((mapSinglePlus P q).app X))) ≫
      (P.rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.quotient C).obj ((singlePlusFunctor C q).obj X)) ≫
        P.rightDerivedFunctorPlus.map z))
    (quotientCompQhIso_hom_app_singlePlus q X)) ?_
  exact Category.assoc _ _ _

omit [HasDerivedCategory C] [EnoughInjectives C] in
/-- **The closed form of `CategoryTheory.Functor.mapSingleFunctorCompQhIso`**: it is the
comparison of the two localizations at `(Pℱ)[0]`, followed by the class of the morphism of
complexes `(Pℱ)[0] ⟶ P(ℱ[0])`. Both sides are preimages under the inclusion of the
bounded-below derived category of the same morphism, by
`Stacks.DerivedIndexing.ι_map_mapSingleFunctorCompQhIso_inv_app`. -/
theorem mapSingleFunctorCompQhIso_inv_app_eq (X : C) :
    (CategoryTheory.Functor.mapSingleFunctorCompQhIso P).inv.app X =
      (CategoryTheory.Functor.singleFunctorPlusIsoCompQh (A := D) 0).hom.app (P.obj X) ≫
        DerivedCategory.Plus.Qh.map
          ((HomotopyCategory.Plus.quotient D).map ((mapSinglePlus P 0).app X)) := by
  refine DerivedCategory.Plus.ι.map_injective ?_
  refine (ι_map_mapSingleFunctorCompQhIso_inv_app P X).trans ?_
  refine Eq.trans ?_ (DerivedCategory.Plus.ι.map_comp _ _).symm
  exact congrArg (fun z => z ≫ DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map
      ((HomotopyCategory.Plus.quotient D).map ((mapSinglePlus P 0).app X))))
    (ι_map_singleFunctorPlusIsoCompQh_hom_app 0 (P.obj X)).symm

/-- **In degree zero the unit assembled from the comparison of complexes is
`Stacks.DerivedIndexing.rightDerivedPlusUnitSingle`**, the canonical map `(Pℱ)[0] ⟶ RP(ℱ[0])`
that the degreewise comparison `Stacks.DerivedIndexing.rightDerivedPlusEdge` of a composite of
right derived functors is built from. -/
theorem singleDerivedUnit_zero (X : C) :
    singleDerivedUnit P 0 X = (rightDerivedPlusUnitSingle P).app X := by
  refine (singleDerivedUnit_eq P 0 X).trans ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (fun z => z ≫
      P.rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.quotient C).obj ((singlePlusFunctor C 0).obj X)) ≫
        P.rightDerivedFunctorPlus.map
          ((CategoryTheory.Functor.singleFunctorPlusIsoCompQh (A := C) 0).inv.app X))
    (mapSingleFunctorCompQhIso_inv_app_eq P X).symm

end Unit

end Stacks.DerivedIndexing

end
