module

public import StacksCore.Algebra.Homology.TotalComplexHomotopy
public import StacksFrontier.AlgebraicGeometry.ProEtale.BigSmall.HypercoverTotalComplex
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerived.CechIsTheDerivedFunctor
public import StacksFrontier.CategoryTheory.Limits.FormalCoproductAdditive
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The hypercovering comparison in the bounded below derived category

Let `K` be a hypercovering of an object `U` of a site. Evaluating a bounded below complex `E` of
abelian sheaves on the levels of `K` gives a double complex, and its total complex is a functor
of `E` which descends to the bounded below homotopy category. Its right derived functor is
identified with the derived sections `RΓ(U, -)`, the identification being the one induced by the
augmentation of the hypercover cochain complex by the complex of sections — a quasi-isomorphism on
complexes of injectives, which is Stacks 01GV together with Stacks 01GW and Weibel's acyclic
assembly lemma.

## Main definitions

* `hypercoverTotalCochainFunctor` is `E ↦ Tot(s(E(K)))` on cochain complexes of abelian sheaves;
  `hypercoverTotalHomotopyFunctor` and `hypercoverTotalPlusFunctor` are its descents to the
  homotopy category and to bounded below complexes, and `hypercoverTotalDerivedFunctor` is the
  resulting functor `Θ : K⁺(Sheaf) ⥤ D⁺(Ab)`.
* `hypercoverAug` is the augmentation `Γ(U, -) ⟶ Θ` in `D⁺(Ab)`.
* `hypercoverRightDerived` is the right derived functor `RΘ` of `Θ`, with unit
  `hypercoverRightDerivedUnit`.
* `derivedSectionsToHypercoverRightDerived` is the comparison `RΓ(U, -) ⟶ RΘ`.
* `hypercoverComparisonMap` is the comparison map `s(F(K)) ⟶ RΓ(U, F)` of Stacks 01GY, and
  `hypercoverCohomologyComparison` is the map it induces on cohomology in each degree.

## Main results

* `quasiIso_hypercoverAugCochain`: the augmentation is a quasi-isomorphism at a bounded below
  complex of injective abelian sheaves.
* `isIso_derivedSectionsToHypercoverRightDerived_app`: the comparison `RΓ(U, -) ⟶ RΘ` is an
  isomorphism.
* `rightDerivedFunctorPlusUnit_comp_derivedSectionsToHypercoverRightDerived`: the comparison is
  normalised by the augmentation, which is what pins it down.
* `hypercoverCochainTotalSingleIso` and `hypercoverDerivedSingleIso`: `s(F(K))` is the hypercover
  total complex of `F[0]`, naturally in `F`.
* `hypercoverAugDerivedSections_comp_hypercoverComparisonMap`: the comparison map of
  Stacks 01GY is normalised by the augmentation `Γ(U, F) ⟶ s(F(K))`.

## Implementation notes

The total complex is taken with the degree of the complex of sheaves as the first degree, so that
a homotopy of complexes of sheaves induces a homotopy of total complexes by
`HomologicalComplex₂.totalMapHomotopy₁` and the descent to the homotopy category is a quotient
lift. A bicomplex of abelian groups has a total complex because the coproducts involved are
coproducts of abelian groups, and the total complex of a complex bounded below by `n` is bounded
below by `n` because every summand has either negative hypercover degree or complex degree `< n`.

The derived functor of `Θ` exists because every functor out of the bounded below homotopy category
of an abelian category with enough injectives has one, and the comparison with `RΓ(U, -)` is the
map produced by the universal property of `RΓ(U, -)` as a right derived functor; it is invertible
because both units are invertible on complexes of injectives and the augmentation is a
quasi-isomorphism there.

`HomologicalComplex₂.HasTotal` is data, not a proposition, so two independently synthesized total
complexes of one double complex are two distinct terms and a rewrite cannot identify them. The
identification of `s(F(K))` with the total complex of the double complex of `F[0]` is therefore
assembled out of isomorphisms *of functors* — `shiftIsoTotalSingleColumn` and
`HomologicalComplex.singleMapHomologicalComplex` — rather than out of their components, so that
every total complex occurring in it is the value of one functor and no two such terms ever have
to be compared.

## References

* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ComplexShape Simplicial

universe w v u

namespace StacksDraft.TotalComplexQuasiIso

variable (A : Type u) [Category.{v} A] [Abelian A] [HasCoproducts.{0} A]

/-- The total complex of a double complex of abelian groups, as a functor. It is spelled with
`HomologicalComplex₂.total.map` on morphisms and with a total complex synthesized for each object
separately, which is what makes it interchangeable with the hypercover total complex functor; see
the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Hypercovering.DerivedComparisonBoundedBelow`. -/
@[sga "4 Vbis 2.3.2" "partial"]
def totalComplexFunctor :
    HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⥤ CochainComplex A ℤ where
  obj Z := Z.total (ComplexShape.up ℤ)
  map f := HomologicalComplex₂.total.map f (ComplexShape.up ℤ)
  map_id Z := by
    change HomologicalComplex₂.total.map (𝟙 Z) (ComplexShape.up ℤ) = _
    rw [HomologicalComplex₂.total.map_id]
  map_comp f g := by
    change HomologicalComplex₂.total.map (f ≫ g) (ComplexShape.up ℤ) = _
    rw [HomologicalComplex₂.total.map_comp]

/-- **The total complex of a double complex concentrated in the column `0` is that column**, as an
isomorphism of functors: the shift by `-0` of a complex is the total complex of the double complex
it spans in the column `0`. This is `totalSingleColumnUnit` and `totalSingleColumnUnit_naturality`
assembled, and assembling them is what makes the identification usable, since the two total
complexes of a naturality square then carry the *same* `HasTotal` term rather than two
independently synthesized ones. -/
def shiftIsoTotalSingleColumn :
    CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-0 : ℤ) ≅
      HomologicalComplex.single (CochainComplex A ℤ) (ComplexShape.up ℤ) 0 ⋙
        totalComplexFunctor A :=
  NatIso.ofComponents
    (fun W ↦ @asIso _ _ _ _ (totalSingleColumnUnit W (0 : ℤ))
      (isIso_totalSingleColumnUnit W 0))
    (fun g ↦ totalSingleColumnUnit_naturality g 0)

end StacksDraft.TotalComplexQuasiIso

namespace Stacks.CategoryTheory.Hypercovering

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  (J : Pretopology C) (U : C)
  (K : SimplicialObject (FormalCoproduct.{w} (Over U)))

/-- The double complex `A^{p,q} = s(E^p(K))^q` of a cochain complex `E` of abelian sheaves,
functorially in `E`. The first degree is the degree in `E`. -/
def hypercoverBicomplexFunctor :
    CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℤ ⥤
      HomologicalComplex₂ AddCommGrpCat.{max u v w} (up ℤ) (up ℤ) :=
  (hypercoverCochainIntFunctor J U K).mapHomologicalComplex (up ℤ)

/-- The total complex of `hypercoverBicomplexFunctor`, functorially in the complex of sheaves. -/
def hypercoverTotalCochainFunctor :
    CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℤ ⥤
      CochainComplex AddCommGrpCat.{max u v w} ℤ where
  obj E := ((hypercoverBicomplexFunctor J U K).obj E).total (up ℤ)
  map f := HomologicalComplex₂.total.map ((hypercoverBicomplexFunctor J U K).map f) (up ℤ)
  map_id E := by
    change HomologicalComplex₂.total.map ((hypercoverBicomplexFunctor J U K).map (𝟙 E)) (up ℤ) = _
    rw [CategoryTheory.Functor.map_id, HomologicalComplex₂.total.map_id]
  map_comp f g := by
    change HomologicalComplex₂.total.map ((hypercoverBicomplexFunctor J U K).map (f ≫ g)) (up ℤ) = _
    rw [CategoryTheory.Functor.map_comp, HomologicalComplex₂.total.map_comp]

/-- Homotopic maps of complexes of abelian sheaves have homotopic images under
`hypercoverTotalCochainFunctor`: a homotopy of the complexes of columns induces one on the
total complexes. -/
def hypercoverTotalHomotopy
    {E E' : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℤ}
    {f g : E ⟶ E'} (h : Homotopy f g) :
    Homotopy ((hypercoverTotalCochainFunctor J U K).map f)
      ((hypercoverTotalCochainFunctor J U K).map g) :=
  HomologicalComplex₂.totalMapHomotopy₁
    ((hypercoverCochainIntFunctor J U K).mapHomotopy h) (up ℤ)

/-- `hypercoverTotalCochainFunctor` descends to the homotopy categories. -/
def hypercoverTotalHomotopyFunctor :
    HomotopyCategory (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (up ℤ) ⥤
      HomotopyCategory AddCommGrpCat.{max u v w} (up ℤ) :=
  CategoryTheory.Quotient.lift _
    (hypercoverTotalCochainFunctor J U K ⋙
      HomotopyCategory.quotient AddCommGrpCat.{max u v w} (up ℤ))
    (fun _ _ _ _ ⟨h⟩ ↦ HomotopyCategory.eq_of_homotopy _ _ (hypercoverTotalHomotopy J U K h))

/-- The hypercover bicomplex of a complex bounded below by `n` vanishes in negative hypercover
degrees and in complex degrees `< n`. -/
private lemma isZero_hypercoverBicomplex_X
    (E : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℤ) (n : ℤ)
    [E.IsStrictlyGE n] :
    (∀ p q, q < 0 → IsZero ((((hypercoverBicomplexFunctor J U K).obj E).X p).X q)) ∧
      ∀ p, p < n → IsZero (((hypercoverBicomplexFunctor J U K).obj E).X p) :=
  ⟨fun p q hq ↦ CochainComplex.isZero_of_isStrictlyGE
      (((hypercoverCochainNatFunctor J U K).obj (E.X p)).extend embeddingUpNat) 0 q hq,
    fun p hp ↦ (hypercoverCochainIntFunctor J U K).map_isZero (E.isZero_of_isStrictlyGE n p hp)⟩

/-- The total complex of the hypercover bicomplex of a complex bounded below by `n` is bounded
below by `n`: every summand has either negative hypercover degree or complex degree `< n`. -/
lemma isStrictlyGE_hypercoverTotal
    (E : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℤ) (n : ℤ)
    [E.IsStrictlyGE n] :
    ((hypercoverTotalCochainFunctor J U K).obj E).IsStrictlyGE n := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  have h := isZero_hypercoverBicomplex_X J U K E n
  exact StacksDraft.TotalComplexQuasiIso.isZero_total_X
    ((hypercoverBicomplexFunctor J U K).obj E) n h.1 h.2 i hi

/-- The hypercover total complex functor on bounded below complexes up to homotopy. -/
def hypercoverTotalPlusFunctor :
    HomotopyCategory.Plus (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ⥤
      HomotopyCategory.Plus AddCommGrpCat.{max u v w} :=
  (HomotopyCategory.plus AddCommGrpCat.{max u v w}).lift
    (HomotopyCategory.Plus.ι _ ⋙ hypercoverTotalHomotopyFunctor J U K) (by
      rintro ⟨X, hX⟩
      obtain ⟨E, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
      rw [HomotopyCategory.plus_quotient_obj_iff] at hX
      obtain ⟨n, _⟩ := hX
      change HomotopyCategory.plus AddCommGrpCat.{max u v w}
        ((HomotopyCategory.quotient AddCommGrpCat.{max u v w} (up ℤ)).obj
          ((hypercoverTotalCochainFunctor J U K).obj E))
      rw [HomotopyCategory.plus_quotient_obj_iff]
      exact ⟨n, isStrictlyGE_hypercoverTotal J U K E n⟩)

/-- `Θ`: the hypercover total complex of a bounded below complex of abelian sheaves, as an object
of `D⁺(Ab)`, functorially in the complex up to homotopy. -/
def hypercoverTotalDerivedFunctor :
    HomotopyCategory.Plus (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ⥤
      DerivedCategory.Plus AddCommGrpCat.{max u v w} :=
  hypercoverTotalPlusFunctor J U K ⋙ DerivedCategory.Plus.Qh

section Augmentation

open StacksDraft.TotalComplexQuasiIso

/-- The action of `hypercoverTotalCochainFunctor` on a morphism is the total complex of the
action of `hypercoverBicomplexFunctor`. -/
lemma hypercoverTotalCochainFunctor_map
    {E E' : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℤ} (f : E ⟶ E') :
    (hypercoverTotalCochainFunctor J U K).map f =
      HomologicalComplex₂.total.map ((hypercoverBicomplexFunctor J U K).map f) (up ℤ) :=
  rfl

/-- The naturality of `totalSingleRowZeroUnit` at the complexes of sections. -/
@[reassoc]
lemma sectionsRowZeroUnit_naturality
    {E E' : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℤ} (f : E ⟶ E') :
    ((sheafSectionsFunctor J U).mapHomologicalComplex (up ℤ)).map f ≫
        totalSingleRowZeroUnit
          (((sheafSectionsFunctor J U).mapHomologicalComplex (up ℤ)).obj E') =
      totalSingleRowZeroUnit
          (((sheafSectionsFunctor J U).mapHomologicalComplex (up ℤ)).obj E) ≫
        HomologicalComplex₂.total.map
          (((HomologicalComplex.single AddCommGrpCat.{max u v w} (up ℤ) 0).mapHomologicalComplex
            (up ℤ)).map (((sheafSectionsFunctor J U).mapHomologicalComplex (up ℤ)).map f))
          (up ℤ) :=
  (totalSingleRowZeroUnit_naturality _).symm

variable [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]

/-- The comparison of double complexes `Γ(X, E)[0] ⟶ A_E` induced by the augmentation of the
hypercover cochain complex of Stacks 01GV and 01GW. -/
def hypercoverBicomplexComparison (hK : IsHypercovering J K)
    (E : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℤ) :
    singleRowZero (((sheafSectionsFunctor J U).mapHomologicalComplex (up ℤ)).obj E) ⟶
      (hypercoverBicomplexFunctor J U K).obj E :=
  (NatTrans.mapHomologicalComplex (sectionsComparisonInt J U K hK) (up ℤ)).app E

/-- `hypercoverBicomplexComparison` is natural in the complex of abelian sheaves. -/
@[reassoc]
lemma hypercoverBicomplexComparison_naturality (hK : IsHypercovering J K)
    {E E' : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℤ} (f : E ⟶ E') :
    ((HomologicalComplex.single AddCommGrpCat.{max u v w} (up ℤ) 0).mapHomologicalComplex
          (up ℤ)).map (((sheafSectionsFunctor J U).mapHomologicalComplex (up ℤ)).map f) ≫
        hypercoverBicomplexComparison J U K hK E' =
      hypercoverBicomplexComparison J U K hK E ≫ (hypercoverBicomplexFunctor J U K).map f :=
  (NatTrans.mapHomologicalComplex (sectionsComparisonInt J U K hK) (up ℤ)).naturality f

/-- The augmentation `Γ(X, E) ⟶ Tot(A_E)` of the hypercover total complex by the complex of
sections, at the level of cochain complexes and natural in the complex `E`. -/
def hypercoverAugCochain (hK : IsHypercovering J K) :
    (sheafSectionsFunctor J U).mapHomologicalComplex (up ℤ) ⟶
      hypercoverTotalCochainFunctor J U K where
  app E := totalSingleRowZeroUnit
      (((sheafSectionsFunctor J U).mapHomologicalComplex (up ℤ)).obj E) ≫
    HomologicalComplex₂.total.map (hypercoverBicomplexComparison J U K hK E) (up ℤ)
  naturality E E' f := by
    have key :
        ((sheafSectionsFunctor J U).mapHomologicalComplex (up ℤ)).map f ≫
            (totalSingleRowZeroUnit
                (((sheafSectionsFunctor J U).mapHomologicalComplex (up ℤ)).obj E') ≫
              HomologicalComplex₂.total.map
                (hypercoverBicomplexComparison J U K hK E') (up ℤ)) =
          (totalSingleRowZeroUnit
                (((sheafSectionsFunctor J U).mapHomologicalComplex (up ℤ)).obj E) ≫
              HomologicalComplex₂.total.map
                (hypercoverBicomplexComparison J U K hK E) (up ℤ)) ≫
            HomologicalComplex₂.total.map
              ((hypercoverBicomplexFunctor J U K).map f) (up ℤ) := by
      rw [Category.assoc, ← HomologicalComplex₂.total.map_comp,
        ← hypercoverBicomplexComparison_naturality J U K hK f,
        HomologicalComplex₂.total.map_comp, ← sectionsRowZeroUnit_naturality_assoc J U f]
    exact key

/-- The augmentation of the hypercover total complex, on the homotopy categories. -/
def hypercoverAugHomotopy (hK : IsHypercovering J K) :
    (sheafSectionsFunctor J U).mapHomotopyCategory (up ℤ) ⟶
      hypercoverTotalHomotopyFunctor J U K :=
  CategoryTheory.Quotient.natTransLift _
    (Functor.whiskerRight (hypercoverAugCochain J U K hK)
      (HomotopyCategory.quotient AddCommGrpCat.{max u v w} (up ℤ)))

/-- The augmentation of the hypercover total complex, on bounded below complexes. -/
def hypercoverAugPlus (hK : IsHypercovering J K) :
    (sheafSectionsFunctor J U).mapHomotopyCategoryPlus ⟶ hypercoverTotalPlusFunctor J U K where
  app X := ObjectProperty.homMk ((hypercoverAugHomotopy J U K hK).app X.obj)
  naturality _ _ f := by
    ext
    exact (hypercoverAugHomotopy J U K hK).naturality f.hom

/-- `Γ(X, -) ⟶ Θ`: the augmentation of the hypercover total complex, in `D⁺(Ab)`. -/
def hypercoverAug (hK : IsHypercovering J K) :
    (sheafSectionsFunctor J U).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      hypercoverTotalDerivedFunctor J U K :=
  Functor.whiskerRight (hypercoverAugPlus J U K hK) DerivedCategory.Plus.Qh

end Augmentation

section Comparison

open StacksDraft.TotalComplexQuasiIso

variable [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]

/-- The comparison `Γ(X, I)[0] ⟶ A_I` of double complexes becomes a quasi-isomorphism on total
complexes for a bounded below complex `I` of injective abelian sheaves: Weibel's acyclic assembly
lemma applies, the comparison being a quasi-isomorphism in each hypercover degree by
Stacks 01GV and 01GW. -/
lemma quasiIso_total_hypercoverBicomplexComparison (hK : IsHypercovering J K)
    (I : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℤ) (n : ℤ)
    [I.IsStrictlyGE n] [∀ p, Injective (I.X p)] :
    QuasiIso (HomologicalComplex₂.total.map
      (hypercoverBicomplexComparison J U K hK I) (up ℤ)) := by
  apply quasiIso_total_map_of_bounded _ n 0
  · intro p q hq
    exact HomologicalComplex.isZero_single_obj_X (up ℤ) 0 _ q (by lia)
  · intro p hp
    exact (sheafSectionsFunctor J U ⋙
      HomologicalComplex.single AddCommGrpCat.{max u v w} (up ℤ) 0).map_isZero
        (I.isZero_of_isStrictlyGE n p hp)
  · exact (isZero_hypercoverBicomplex_X J U K I n).1
  · exact (isZero_hypercoverBicomplex_X J U K I n).2
  · intro p
    exact quasiIso_sectionsComparisonInt J U K hK (I.X p)

/-- The augmentation of the hypercover total complex is a quasi-isomorphism at a bounded below
complex of injective abelian sheaves. -/
lemma quasiIso_hypercoverAugCochain (hK : IsHypercovering J K)
    (I : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℤ) (n : ℤ)
    [I.IsStrictlyGE n] [∀ p, Injective (I.X p)] :
    QuasiIso ((hypercoverAugCochain J U K hK).app I) := by
  have h₁ : QuasiIso (totalSingleRowZeroUnit
      (((sheafSectionsFunctor J U).mapHomologicalComplex (up ℤ)).obj I)) :=
    have := isIso_totalSingleRowZeroUnit
      (((sheafSectionsFunctor J U).mapHomologicalComplex (up ℤ)).obj I)
    quasiIso_of_isIso _
  have h₂ := quasiIso_total_hypercoverBicomplexComparison J U K hK I n
  exact quasiIso_comp (hφ := h₁) (hφ' := h₂) _ _

variable [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})]

/-- The functor `Θ` admits a pointwise right derived functor with respect to the quasi-isomorphisms
of the bounded below homotopy category of abelian sheaves. -/
instance hasPointwiseRightDerivedFunctor_hypercoverTotalDerivedFunctor :
    (hypercoverTotalDerivedFunctor J U K).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
    (hypercoverTotalDerivedFunctor J U K)).hasPointwiseRightDerivedFunctor

/-- The functor `Θ` admits a right derived functor with respect to the quasi-isomorphisms of the
bounded below homotopy category of abelian sheaves. -/
instance hasRightDerivedFunctor_hypercoverTotalDerivedFunctor :
    (hypercoverTotalDerivedFunctor J U K).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})) :=
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

/-- `RΘ`: the right derived functor of `Θ`, which exists because every functor out of the
bounded below homotopy category of an abelian category with enough injectives has one. -/
def hypercoverRightDerived :
    DerivedCategory.Plus (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ⥤
      DerivedCategory.Plus AddCommGrpCat.{max u v w} :=
  (hypercoverTotalDerivedFunctor J U K).totalRightDerived DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}))

/-- The unit `Θ ⟶ Qh ⋙ RΘ` of the right derived functor of `Θ`. -/
def hypercoverRightDerivedUnit :
    hypercoverTotalDerivedFunctor J U K ⟶
      DerivedCategory.Plus.Qh ⋙ hypercoverRightDerived J U K :=
  (hypercoverTotalDerivedFunctor J U K).totalRightDerivedUnit DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}))

/-- `RΘ`, together with the unit `Θ ⟶ Qh ⋙ RΘ`, is a right derived functor of `Θ`. -/
instance isRightDerivedFunctor_hypercoverRightDerived :
    (hypercoverRightDerived J U K).IsRightDerivedFunctor
      (hypercoverRightDerivedUnit J U K)
      (HomotopyCategory.Plus.quasiIso (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})) := by
  dsimp only [hypercoverRightDerived, hypercoverRightDerivedUnit]
  infer_instance

omit [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})] in
/-- The augmentation `Γ(X, -) ⟶ Θ` is invertible in `D⁺(Ab)` at a bounded below complex of
injective abelian sheaves. -/
lemma isIso_hypercoverAug_app (hK : IsHypercovering J K)
    (Z : HomotopyCategory.Plus
      (InjectiveObject (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}))) :
    IsIso ((hypercoverAug J U K hK).app
      ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj Z)) := by
  obtain ⟨W, hW⟩ := Z
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective W
  rw [HomotopyCategory.plus_quotient_obj_iff] at hW
  obtain ⟨n, _⟩ := hW
  have : ∀ p, Injective ((((InjectiveObject.ι
      (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})).mapHomologicalComplex
      (up ℤ)).obj L).X p) := fun p ↦ (L.X p).property
  have : CochainComplex.IsStrictlyGE (((InjectiveObject.ι
      (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})).mapHomologicalComplex
      (up ℤ)).obj L) n := inferInstance
  have hmem : HomotopyCategory.Plus.quasiIso AddCommGrpCat.{max u v w}
      ((hypercoverAugPlus J U K hK).app
        ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj ⟨_, hW⟩)) := by
    rw [HomotopyCategory.Plus.quasiIso_iff]
    show HomotopyCategory.quasiIso _ _
      ((HomotopyCategory.quotient AddCommGrpCat.{max u v w} (up ℤ)).map
        ((hypercoverAugCochain J U K hK).app
          (((InjectiveObject.ι _).mapHomologicalComplex (up ℤ)).obj L)))
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact quasiIso_hypercoverAugCochain J U K hK _ n
  exact Localization.inverts DerivedCategory.Plus.Qh _ _ hmem

/-- `RΓ(X, -) ⟶ RΘ`: the comparison of the two derived functors induced by the augmentation. -/
def derivedSectionsToHypercoverRightDerived (hK : IsHypercovering J K) :
    (sheafSectionsFunctor J U).rightDerivedFunctorPlus ⟶ hypercoverRightDerived J U K :=
  ((sheafSectionsFunctor J U).rightDerivedFunctorPlus).rightDerivedDesc
    ((sheafSectionsFunctor J U).rightDerivedFunctorPlusUnit)
    (HomotopyCategory.Plus.quasiIso (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}))
    (hypercoverRightDerived J U K)
    (hypercoverAug J U K hK ≫ hypercoverRightDerivedUnit J U K)

omit [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- **The normalisation of the comparison map.** The unit `Γ(X, E) ⟶ RΓ(X, E)` of the derived
functor of sections, followed by the comparison `RΓ(X, -) ⟶ RΘ`, is the augmentation of the
hypercover total complex followed by the unit of `RΘ`. This is what pins the comparison map of
Stacks 01GY down: in degree zero it is the canonical identification. -/
@[reassoc]
lemma rightDerivedFunctorPlusUnit_comp_derivedSectionsToHypercoverRightDerived
    (hK : IsHypercovering J K)
    (X : HomotopyCategory.Plus (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})) :
    (sheafSectionsFunctor J U).rightDerivedFunctorPlusUnit.app X ≫
        (derivedSectionsToHypercoverRightDerived J U K hK).app
          (DerivedCategory.Plus.Qh.obj X) =
      (hypercoverAug J U K hK).app X ≫ (hypercoverRightDerivedUnit J U K).app X :=
  Functor.rightDerived_fac_app _ _ _ _ _ X

/-- The comparison `RΓ(X, -) ⟶ RΘ` is an isomorphism: both functors are right derived, and the
augmentation relating them is invertible on complexes of injectives, which exhaust `D⁺` up to
isomorphism. -/
instance isIso_derivedSectionsToHypercoverRightDerived_app (hK : IsHypercovering J K)
    (Y : DerivedCategory.Plus (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})) :
    IsIso ((derivedSectionsToHypercoverRightDerived J U K hK).app Y) := by
  obtain ⟨Z, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (F := (InjectiveObject.ι
      (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh) Y
  rw [← NatTrans.isIso_app_iff_of_iso (derivedSectionsToHypercoverRightDerived J U K hK) e]
  change IsIso ((derivedSectionsToHypercoverRightDerived J U K hK).app
    (DerivedCategory.Plus.Qh.obj ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj Z)))
  have h₃ := isIso_hypercoverAug_app J U K hK Z
  have hcomp : IsIso ((sheafSectionsFunctor J U).rightDerivedFunctorPlusUnit.app
      ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj Z) ≫
        (derivedSectionsToHypercoverRightDerived J U K hK).app
          (DerivedCategory.Plus.Qh.obj
            ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj Z))) := by
    rw [rightDerivedFunctorPlusUnit_comp_derivedSectionsToHypercoverRightDerived]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((sheafSectionsFunctor J U).rightDerivedFunctorPlusUnit.app
      ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj Z)) _

end Comparison

section Identification

open StacksDraft.TotalComplexQuasiIso DerivedCategory.Plus

variable [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
  [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

/-- **`s(F(K))` is the hypercover total complex of `F` placed in degree zero**, naturally in the
abelian sheaf `F`: the double complex of `F[0]` is `s(F(K))` placed in the hypercover-degree-zero
column, and the total complex of a one-column double complex is that column. -/
def hypercoverCochainTotalSingleIso :
    hypercoverCochainIntFunctor J U K ≅
      HomologicalComplex.single (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (up ℤ) 0 ⋙
        hypercoverTotalCochainFunctor J U K :=
  (hypercoverCochainIntFunctor J U K).rightUnitor.symm ≪≫
    Functor.isoWhiskerLeft _
      (CategoryTheory.shiftFunctorZero' (CochainComplex AddCommGrpCat.{max u v w} ℤ)
        (-0 : ℤ) neg_zero).symm ≪≫
    Functor.isoWhiskerLeft _ (shiftIsoTotalSingleColumn AddCommGrpCat.{max u v w}) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (HomologicalComplex.singleMapHomologicalComplex
      (hypercoverCochainIntFunctor J U K) (up ℤ) 0).symm _ ≪≫
    Functor.associator _ _ _

/-- **`Θ` evaluated at `F[0]` is `s(F(K))` in `D⁺(Ab)`**, naturally in `F`: the identification of
cochain complexes of `hypercoverCochainTotalSingleIso`, transported to the bounded below derived
category. Both functors become, after the fully faithful inclusion of `D⁺(Ab)` in `D(Ab)`, the
localization of a cochain complex, so the identification is the cochain-level one. -/
def hypercoverDerivedSingleIso :
    hypercoverDerivedFunctor J U K ≅
      HomotopyCategory.Plus.singleFunctor
          (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) 0 ⋙
        hypercoverTotalDerivedFunctor J U K :=
  Functor.fullyFaithfulCancelRight DerivedCategory.Plus.ι
    (Functor.isoWhiskerRight (hypercoverCochainTotalSingleIso J U K) DerivedCategory.Q ≪≫
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft (hypercoverTotalCochainFunctor J U K)
        (DerivedCategory.quotientCompQhIso AddCommGrpCat.{max u v w}).symm))

variable [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})]

/-- `Θ ⟶ Qh ⋙ RΓ(X, -)`: the unit of `RΘ` followed by the inverse of the comparison
`RΓ(X, -) ⟶ RΘ`, which is an isomorphism. -/
def hypercoverRightDerivedToDerivedSections (hK : IsHypercovering J K) :
    hypercoverTotalDerivedFunctor J U K ⟶
      DerivedCategory.Plus.Qh ⋙ (sheafSectionsFunctor J U).rightDerivedFunctorPlus :=
  haveI : IsIso (derivedSectionsToHypercoverRightDerived J U K hK) :=
    NatIso.isIso_of_isIso_app _
  hypercoverRightDerivedUnit J U K ≫
    Functor.whiskerLeft DerivedCategory.Plus.Qh
      (inv (derivedSectionsToHypercoverRightDerived J U K hK))

omit [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- The augmentation `Γ(X, -) ⟶ Θ` followed by `Θ ⟶ Qh ⋙ RΓ(X, -)` is the unit of the derived
functor of sections. This is the normalisation of the comparison `RΓ(X, -) ⟶ RΘ` with the
comparison inverted. -/
lemma hypercoverAug_comp_hypercoverRightDerivedToDerivedSections (hK : IsHypercovering J K) :
    hypercoverAug J U K hK ≫ hypercoverRightDerivedToDerivedSections J U K hK =
      (sheafSectionsFunctor J U).rightDerivedFunctorPlusUnit := by
  ext X
  rw [NatTrans.comp_app, hypercoverRightDerivedToDerivedSections, NatTrans.comp_app,
    Functor.whiskerLeft_app, NatIso.isIso_inv_app, ← Category.assoc,
    ← rightDerivedFunctorPlusUnit_comp_derivedSectionsToHypercoverRightDerived J U K hK X,
    Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- **The comparison map of Stacks 01GY**: for a hypercovering `K` of `X`, the natural
transformation `s(F(K)) ⟶ RΓ(X, F)` in `D⁺(Ab)`.

It is `s(F(K)) ≅ Θ(F[0]) ⟶ RΘ(F[0]) ≅ RΓ(X, F)`: the identification of `s(F(K))` with the
hypercover total complex of `F[0]`, the unit of the right derived functor of `Θ`, and the inverse
of the comparison `RΓ(X, -) ⟶ RΘ` induced by the augmentation. It is pinned down by
`hypercoverAugDerivedSections_comp_hypercoverComparisonMap`. -/
@[stacks 01GY "comparison_map"]
def hypercoverComparisonMap (hK : IsHypercovering J K) :
    hypercoverDerivedFunctor J U K ⟶ derivedSectionsFunctor J U :=
  (hypercoverDerivedSingleIso J U K).hom ≫
    Functor.whiskerLeft _ (hypercoverRightDerivedToDerivedSections J U K hK) ≫
    Functor.whiskerRight
      (Functor.singleFunctorPlusIsoCompQh
        (A := Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) 0).inv
      (sheafSectionsFunctor J U).rightDerivedFunctorPlus

/-- The augmentation `Γ(X, F) ⟶ s(F(K))` in `D⁺(Ab)`: the augmentation of the hypercover total
complex by the complex of sections, read through the identification of `Θ(F[0])` with
`s(F(K))`. -/
def hypercoverAugDerivedSections (hK : IsHypercovering J K) :
    HomotopyCategory.Plus.singleFunctor
          (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) 0 ⋙
        (sheafSectionsFunctor J U).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      hypercoverDerivedFunctor J U K :=
  Functor.whiskerLeft _ (hypercoverAug J U K hK) ≫ (hypercoverDerivedSingleIso J U K).inv

/-- The comparison map `s(F(K)) ⟶ RΓ(X, F)` of Stacks 01GY for a hypercovering `K` of `X` is
normalised by the augmentation: the augmentation `Γ(X, F) ⟶ s(F(K))` followed by the comparison
is the unit `Γ(X, F) ⟶ RΓ(X, F)` of the derived functor of sections.

This equation is what pins the comparison down — the mere existence of a natural transformation
`s(F(K)) ⟶ RΓ(X, F)` says nothing, being witnessed by the zero map. -/
theorem hypercoverAugDerivedSections_comp_hypercoverComparisonMap (hK : IsHypercovering J K) :
    hypercoverAugDerivedSections J U K hK ≫ hypercoverComparisonMap J U K hK =
      Functor.whiskerLeft _ (sheafSectionsFunctor J U).rightDerivedFunctorPlusUnit ≫
        Functor.whiskerRight (Functor.singleFunctorPlusIsoCompQh
          (A := Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) 0).inv
          (sheafSectionsFunctor J U).rightDerivedFunctorPlus := by
  rw [hypercoverAugDerivedSections, hypercoverComparisonMap, Category.assoc,
    Iso.inv_hom_id_assoc, ← hypercoverAug_comp_hypercoverRightDerivedToDerivedSections J U K hK,
    Functor.whiskerLeft_comp, Category.assoc]
  rfl

/-- The natural map from the Čech cohomology of a hypercovering `K` of `X` to sheaf cohomology in
degree `i`, induced by the comparison map `hypercoverComparisonMap`. -/
@[stacks 01GY "cohomology_comparison"]
def hypercoverCohomologyComparison (hK : IsHypercovering J K) (i : ℤ) :
    (hypercoverDerivedFunctor J U K ⋙ homologyFunctor AddCommGrpCat.{max u v w} i) ⟶
      (derivedSectionsFunctor J U ⋙ homologyFunctor AddCommGrpCat.{max u v w} i) :=
  Functor.whiskerRight (hypercoverComparisonMap J U K hK)
    (homologyFunctor AddCommGrpCat.{max u v w} i)

end Identification

end Stacks.CategoryTheory.Hypercovering

end
