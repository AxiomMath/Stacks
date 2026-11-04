module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDual
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexComparisonNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexCompositionComparison

/-!
# The comparison to derived internal Hom commutes with restriction to a slice

Let `(C, O)` be a ringed site, let `U` be an object of `C` and let `E` and `F` be complexes of
`O`-modules. There are two canonical comparisons from a naive internal Hom complex to a derived
internal Hom in play: the one on `(C, O)`,

`Q(SheafHom(E, F)) ⟶ RSheafHom(QE, QF)`,

and the one on the slice site `(C/U, O|_U)`,

`Q(SheafHom(E|_U, F|_U)) ⟶ RSheafHom(Q(E|_U), Q(F|_U))`.

This file proves that restricting the first to `C/U` gives the second. The two sides of the
square are identified by the restriction isomorphisms already available:

* on the naive side, the chain-level restriction isomorphism
  `AlgebraicGeometry.RingedSite.sheafHomRestrictionComplexIso`, whose local homogeneous
  components are the canonical restriction isomorphisms of Stacks 0E8H, preceded by the
  identification of the restriction of a class with the class of the degreewise restriction;
* on the derived side, Stacks 08JB, `AlgebraicGeometry.RingedSite.derivedHomRestriction`,
  followed by the same identification in each of the two arguments.

No hypothesis on `E` or `F` is needed. The square is proved first for a K-injective target,
where both comparisons are the inverses of their K-injective model comparisons, so that the
square is the model characterisation of Stacks 08JB; it is then transported to an arbitrary
target along the augmentation into the chosen K-injective resolution. That transport does not
need the augmentation to induce an isomorphism of naive internal Hom complexes — which is
exactly what fails for a general source, and is the content of Stacks 08JH — because it is
carried out by cancelling the isomorphism the augmentation induces on the *derived* internal
Hom over `U`.

Since every side of the square other than the two comparisons is an isomorphism, the comparison
over `(C, O)` restricts to an isomorphism precisely when the comparison over `U` is one. That is
the form in which a local computation of a derived internal Hom is globalised.

## Main definitions

* `AlgebraicGeometry.RingedSite.restrictedSheafHomClassIso`: the restriction to `C/U` of the
  class of `SheafHom(E, F)` is the class of `SheafHom(E|_U, F|_U)`.
* `AlgebraicGeometry.RingedSite.restrictedDerivedHomArgumentsIso`: reading both arguments of the
  derived internal Hom over `U` through the restriction of classes.
* `AlgebraicGeometry.RingedSite.restrictedDerivedHomClassIso`: the restriction to `C/U` of
  `RSheafHom(QE, QF)` is `RSheafHom(Q(E|_U), Q(F|_U))`.

## Main results

* `AlgebraicGeometry.RingedSite.eq_of_isInternalHomRestrictionMap`: a map of internal Hom
  complexes is determined by being the canonical restriction on every local homogeneous
  component.
* `AlgebraicGeometry.RingedSite.derivedHomRestriction_complexMap_eq`: consequently the
  chain-level map carried by `derivedHomRestriction` is `sheafHomRestrictionComplexIso`.
* `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_restriction`: **the comparison to
  derived internal Hom commutes with restriction to the slice over `U`**, for arbitrary
  complexes.
* `AlgebraicGeometry.RingedSite.isIso_restricted_strictlyPerfectHomComparison_iff`: the
  restriction of the comparison over `(C, O)` is an isomorphism if and only if the comparison
  over `U` is.

## Implementation notes

The statements are given at the derived internal Hom datum
`AlgebraicGeometry.RingedSite.derivedInternalHomOfBifunctor`, whose bifunctor is literally
`RSheafHom(-, -)`, rather than at an arbitrary
`AlgebraicGeometry.RingedSite.DerivedInternalHom`: Stacks 08JB is stated for that bifunctor, so
only there do the two sides of the square live in the same objects. The universes are the
diagonal `RingedSite.{u, u, u}` with the standard derived category, as in Stacks 08JB.

Restriction to a slice is exact, and the slice of a site carrying the two sheafification
hypotheses carries them again, so the hypotheses are exactly those of Stacks 08JB.

## References

* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) (U : X.C)

/-- A section of an internal Hom complex is determined by its local homogeneous components. -/
private lemma sections_ext
    {Y : RingedSite.{u, u, u}}
    {A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (H : SheafHomComplex Y A B) (V : Y.C) (n : ℤ)
    {s t : (H.obj.X n).val.obj (op V)}
    (h : ∀ p q (hpq : p + n = q),
      ((H.sectionsIso V).hom.f n s).v p q hpq = ((H.sectionsIso V).hom.f n t).v p q hpq) :
    s = t := by
  have he : (H.sectionsIso V).hom.f n s = (H.sectionsIso V).hom.f n t :=
    CochainComplex.HomComplex.Cochain.ext _ _ h
  exact (Iso.hom_inv_id_apply ((HomologicalComplex.eval _ _ n).mapIso
    (H.sectionsIso V)) s).symm.trans
      ((congrArg (fun z => (H.sectionsIso V).inv.f n z) he).trans
        (Iso.hom_inv_id_apply ((HomologicalComplex.eval _ _ n).mapIso (H.sectionsIso V)) t))

/-- **A restriction map of internal Hom complexes is unique.** Being, on every local homogeneous
component, the canonical restriction isomorphism of Stacks 0E8H determines a map of internal Hom
complexes, because a section of an internal Hom complex is determined by its local homogeneous
components. -/
theorem eq_of_isInternalHomRestrictionMap
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {f g : restrictComplex X (sheafHomComplex X A B).obj U ⟶
      (sheafHomComplex (X.over U) (restrictComplex X A U) (restrictComplex X B U)).obj}
    (hf : IsInternalHomRestrictionMap X U A B f)
    (hg : IsInternalHomRestrictionMap X U A B g) : f = g := by
  ext n V s
  apply sections_ext (sheafHomComplex (X.over U) (restrictComplex X A U)
    (restrictComplex X B U)) V.unop n
  intro p q hpq
  apply SheafOfModules.hom_ext
  rw [hf V n p q hpq s, hg V n p q hpq s]

section Restriction

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible]
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  CochainComplex.HomComplex
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [PreservesFiniteLimits (SheafOfModules.overFunctor.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [PreservesFiniteColimits (SheafOfModules.overFunctor.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]

omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The chain-level map carried by the canonical comparison of Stacks 08JB is the chain-level
restriction isomorphism, by uniqueness of a restriction map of internal Hom complexes. In
particular it is an isomorphism of complexes. -/
theorem derivedHomRestriction_complexMap_eq
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (derivedHomRestriction X U).complexMap A B = (sheafHomRestrictionComplexIso X U A B).hom :=
  eq_of_isInternalHomRestrictionMap X U A B
    (derivedHomRestriction_complexMap_isRestriction X U A B)
    (sheafHomRestrictionComplexIso_isRestriction X U A B)

omit [PreservesFiniteLimits (SheafOfModules.overFunctor.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [PreservesFiniteColimits (SheafOfModules.overFunctor.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)] in
attribute [local instance] restriction_isKInjective

/-- A functor carries a commuting square to a commuting square. -/
private lemma map_comp_eq_map_comp {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {W X Y Z : C} {f : W ⟶ X} {g : X ⟶ Z} {f' : W ⟶ Y} {g' : Y ⟶ Z} (h : f ≫ g = f' ≫ g') :
    G.map f ≫ G.map g = G.map f' ≫ G.map g' := by
  rw [← G.map_comp, h, G.map_comp]

/-- Restricting the class of a complex to the slice over `U` is natural: it is the naturality of
the identification of the restriction of a class with the class of the degreewise
restriction. -/
private lemma restrictionComparison_naturality
    {A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : A ⟶ B) :
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
        (DerivedCategory.Q.map f) ≫ (restrictionComparison X U B).hom =
      (restrictionComparison X U A).hom ≫
        DerivedCategory.Q.map (restrictComplexMap X U f) :=
  (SheafOfModules.overFunctor.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategoryFactors.hom.naturality f

variable (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **The restriction of the class of an internal Hom complex.** The restriction to the slice
over `U` of the class of `SheafHom(E, F)` is the class of `SheafHom(E|_U, F|_U)`: restriction is
exact, so it carries the class of a complex to the class of its degreewise restriction, and that
degreewise restriction is the internal Hom complex of the restrictions by the chain-level form of
Stacks 08JB. -/
def restrictedSheafHomClassIso :
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (sheafHomComplex X E F).obj) ≅
      DerivedCategory.Q.obj
        (sheafHomComplex (X.over U) (restrictComplex X E U) (restrictComplex X F U)).obj :=
  restrictionComparison X U (sheafHomComplex X E F).obj ≪≫
    DerivedCategory.Q.mapIso (sheafHomRestrictionComplexIso X U E F)

/-- Reading both arguments of the derived internal Hom over `U` through the identification of the
restriction of a class with the class of the degreewise restriction. -/
def restrictedDerivedHomArgumentsIso :
    ((derivedSheafHomBifunctor (X.over U)).obj
          (op ((SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj
            (DerivedCategory.Q.obj E)))).obj
        ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj
          (DerivedCategory.Q.obj F)) ≅
      ((derivedSheafHomBifunctor (X.over U)).obj
          (op (DerivedCategory.Q.obj (restrictComplex X E U)))).obj
        (DerivedCategory.Q.obj (restrictComplex X F U)) :=
  ((derivedSheafHomBifunctor (X.over U)).mapIso
      (restrictionComparison X U E).symm.op).app
        ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj
          (DerivedCategory.Q.obj F)) ≪≫
    ((derivedSheafHomBifunctor (X.over U)).obj
      (op (DerivedCategory.Q.obj (restrictComplex X E U)))).mapIso
        (restrictionComparison X U F)

/-- **The restriction of a derived internal Hom.** The restriction to the slice over `U` of
`RSheafHom(QE, QF)` is `RSheafHom(Q(E|_U), Q(F|_U))`: Stacks 08JB, followed by the
identification of the restriction of a class with the class of the degreewise restriction in
each of the two arguments. -/
def restrictedDerivedHomClassIso :
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj E))).obj
          (DerivedCategory.Q.obj F)) ≅
      ((derivedSheafHomBifunctor (X.over U)).obj
          (op (DerivedCategory.Q.obj (restrictComplex X E U)))).obj
        (DerivedCategory.Q.obj (restrictComplex X F U)) :=
  (derivedHomRestriction X U).iso (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj F) ≪≫
    restrictedDerivedHomArgumentsIso X U E F

/-- The K-injective model comparison of Stacks 08JB, with the change of arguments split off as
`restrictedDerivedHomArgumentsIso`. -/
private lemma restrictionTargetComparison_hom_eq [F.IsKInjective] :
    (restrictionTargetComparison X U E F).hom =
      (restrictedDerivedHomArgumentsIso X U E F).hom ≫
        (derivedSheafHomComparison (X.over U) (restrictComplex X E U)
          (restrictComplex X F U)).hom :=
  (Category.assoc _ _ _).symm

/-- **The square at a K-injective target.** There both comparisons are the inverses of their
K-injective model comparisons, so the square is the model characterisation of Stacks 08JB. -/
private lemma strictlyPerfectHomComparison_restriction_of_isKInjective [F.IsKInjective] :
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
        (strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) E F) ≫
      (restrictedDerivedHomClassIso X U E F).hom =
    (restrictedSheafHomClassIso X U E F).hom ≫
      strictlyPerfectHomComparison (X.over U) (derivedInternalHomOfBifunctor (X.over U))
        (restrictComplex X E U) (restrictComplex X F U) := by
  have hmodel := derivedHomRestriction_model X U E F
  rw [derivedHomRestriction_complexMap_eq, restrictionTargetComparison_hom_eq] at hmodel
  rw [strictlyPerfectHomComparison_eq_homComparison_inv X (derivedInternalHomOfBifunctor X) E F,
    strictlyPerfectHomComparison_eq_homComparison_inv (X.over U)
      (derivedInternalHomOfBifunctor (X.over U)) (restrictComplex X E U) (restrictComplex X F U)]
  let globalComparison :=
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.mapIso
      (derivedSheafHomComparison X E F)
  let sliceComparison := derivedSheafHomComparison (X.over U)
    (restrictComplex X E U) (restrictComplex X F U)
  let derivedRestriction := restrictedDerivedHomClassIso X U E F
  let naiveRestriction := restrictedSheafHomClassIso X U E F
  have square : derivedRestriction.hom ≫ sliceComparison.hom =
      globalComparison.hom ≫ naiveRestriction.hom :=
    (Category.assoc _ _ _).trans (hmodel.trans (Category.assoc _ _ _))
  refine (Iso.eq_comp_inv sliceComparison).mpr ?_
  exact (Category.assoc globalComparison.inv derivedRestriction.hom sliceComparison.hom).trans
    ((congrArg (globalComparison.inv ≫ ·) square).trans
      (globalComparison.inv_hom_id_assoc naiveRestriction.hom))

/-- The restriction of the class of an internal Hom complex is natural in the target: on the
naive side this is the naturality of the chain-level restriction isomorphism, and on the derived
side the naturality of the identification of the restriction of a class with the class of the
degreewise restriction. -/
private lemma restrictedSheafHomClassIso_naturality_target
    {F F' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (g : F ⟶ F') :
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
        (DerivedCategory.Q.map (homMap X (𝟙 E) g)) ≫
      (restrictedSheafHomClassIso X U E F').hom =
    (restrictedSheafHomClassIso X U E F).hom ≫
      DerivedCategory.Q.map
        (homMap (X.over U) (𝟙 (restrictComplex X E U)) (restrictComplexMap X U g)) := by
  have hchain := sheafHomRestrictionComplexIso_natural X U (𝟙 E) g
  rw [CategoryTheory.Functor.map_id] at hchain
  let sourceComparison := restrictionComparison X U (sheafHomComplex X E F).obj
  let targetComparison := restrictionComparison X U (sheafHomComplex X E F').obj
  let sourceIso := sheafHomRestrictionComplexIso X U E F
  let targetIso := sheafHomRestrictionComplexIso X U E F'
  let restrictionMap := restrictComplexMap X U (homMap X (𝟙 E) g)
  let localMap := homMap (X.over U) (𝟙 (restrictComplex X E U)) (restrictComplexMap X U g)
  let quotient : CochainComplex
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ ⥤
      DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :=
    DerivedCategory.Q
  have chainNaturality := map_comp_eq_map_comp quotient hchain
  have factorNaturality := restrictionComparison_naturality X U (homMap X (𝟙 E) g)
  exact (Category.assoc _ targetComparison.hom (quotient.map targetIso.hom)).symm.trans
    ((congrArg (· ≫ quotient.map targetIso.hom) factorNaturality).trans
      ((Category.assoc sourceComparison.hom _ _).trans
        ((congrArg (sourceComparison.hom ≫ ·) chainNaturality).trans
          (Category.assoc sourceComparison.hom (quotient.map sourceIso.hom)
            (quotient.map localMap)).symm)))

/-- The restriction of a derived internal Hom is natural in the target: Stacks 08JB is natural in
its covariant argument, and the identification of the restriction of a class with the class of
the degreewise restriction is natural. -/
private lemma restrictedDerivedHomClassIso_naturality_target
    {F F' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (g : F ⟶ F') :
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj E))).map
          (DerivedCategory.Q.map g)) ≫
      (restrictedDerivedHomClassIso X U E F').hom =
    (restrictedDerivedHomClassIso X U E F).hom ≫
      ((derivedSheafHomBifunctor (X.over U)).obj
        (op (DerivedCategory.Q.obj (restrictComplex X E U)))).map
          (DerivedCategory.Q.map (restrictComplexMap X U g)) := by
  have hiso := (derivedHomRestriction X U).natural_right
    (K := DerivedCategory.Q.obj E) (DerivedCategory.Q.map g)
  have hargs := ((derivedSheafHomBifunctor (X.over U)).map
    (restrictionComparison X U E).symm.op.hom).naturality
      ((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
        (DerivedCategory.Q.map g))
  have hfac := restrictionComparison_naturality X U g
  let targetFunctor := (derivedSheafHomBifunctor (X.over U)).obj
    (op (DerivedCategory.Q.obj (restrictComplex X E U)))
  let argumentMap := (derivedSheafHomBifunctor (X.over U)).map
    (restrictionComparison X U E).symm.op.hom
  let restrictedSource :=
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj
      (DerivedCategory.Q.obj F)
  let restrictedTarget :=
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj
      (DerivedCategory.Q.obj F')
  let restrictionMap :=
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
      (DerivedCategory.Q.map g)
  let localMap := DerivedCategory.Q.map (restrictComplexMap X U g)
  have mappedFactor := map_comp_eq_map_comp targetFunctor hfac
  have argumentNaturality :
      argumentMap.app restrictedSource ≫ targetFunctor.map restrictionMap ≫
        targetFunctor.map (restrictionComparison X U F').hom =
      (argumentMap.app restrictedSource ≫ targetFunctor.map (restrictionComparison X U F).hom) ≫
        targetFunctor.map localMap :=
    (congrArg (argumentMap.app restrictedSource ≫ ·) mappedFactor).trans
      (Category.assoc _ _ _).symm
  have tailNaturality := (Category.assoc _ (argumentMap.app restrictedTarget)
      (targetFunctor.map (restrictionComparison X U F').hom)).symm.trans
    ((congrArg (· ≫ targetFunctor.map (restrictionComparison X U F').hom) hargs).trans
      ((Category.assoc _ _ _).trans argumentNaturality))
  exact (Category.assoc _ _ (restrictedDerivedHomArgumentsIso X U E F').hom).symm.trans
    ((congrArg (· ≫ (restrictedDerivedHomArgumentsIso X U E F').hom) hiso).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (((derivedHomRestriction X U).iso (DerivedCategory.Q.obj E)
          (DerivedCategory.Q.obj F)).hom ≫ ·) tailNaturality).trans
          (Category.assoc _ _ _).symm)))

/-- **The transport of the square from a K-injective target to an arbitrary one.** It is enough
to have *some* morphism `a : F ⟶ I` with `I` K-injective whose class in the derived category is
an isomorphism; the chosen K-injective resolution supplies one.

Both verticals and both comparisons are natural in the target, so the square at `F` follows from
the square at `I` once the map that `a` induces on the derived internal Hom over `U` has been
cancelled. That map is an isomorphism because `a` becomes one in the derived category, which is
why no hypothesis on `E` is needed: the map `a` induces on the *naive* internal Hom complexes
need not be an isomorphism. -/
private lemma strictlyPerfectHomComparison_restriction_aux
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] (a : F ⟶ I)
    [IsIso (DerivedCategory.Q.map a)] :
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
        (strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) E F) ≫
      (restrictedDerivedHomClassIso X U E F).hom =
    (restrictedSheafHomClassIso X U E F).hom ≫
      strictlyPerfectHomComparison (X.over U) (derivedInternalHomOfBifunctor (X.over U))
        (restrictComplex X E U) (restrictComplex X F U) := by
  have hiso : IsIso ((restrictionComparison X U F).hom ≫
      DerivedCategory.Q.map (restrictComplexMap X U a)) := by
    rw [← restrictionComparison_naturality X U a]
    infer_instance
  have restrictedIsIso : IsIso (DerivedCategory.Q.map (restrictComplexMap X U a)) :=
    IsIso.of_isIso_comp_left (restrictionComparison X U F).hom _
  have key := strictlyPerfectHomComparison_restriction_of_isKInjective X U E I
  have hNX := strictlyPerfectHomComparison_naturality_target X
    (derivedInternalHomOfBifunctor X) E _ _ a
  have hNU := strictlyPerfectHomComparison_naturality_target (X.over U)
    (derivedInternalHomOfBifunctor (X.over U)) (restrictComplex X E U) _ _
    (restrictComplexMap X U a)
  have hL := restrictedSheafHomClassIso_naturality_target X U E a
  have hR := restrictedDerivedHomClassIso_naturality_target X U E a
  let targetFunctor := (derivedSheafHomBifunctor (X.over U)).obj
    (op (DerivedCategory.Q.obj (restrictComplex X E U)))
  have : IsIso (targetFunctor.map (DerivedCategory.Q.map (restrictComplexMap X U a))) :=
    (targetFunctor.mapIso (@asIso _ _ _ _
      (DerivedCategory.Q.map (restrictComplexMap X U a)) restrictedIsIso)).isIso_hom
  let restriction :=
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory
  let sourceComparison := strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) E F
  let targetComparison := strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) E I
  let sourceMap := DerivedCategory.Q.map (homMap X (𝟙 E) a)
  let derivedMap := ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj E))).map
    (DerivedCategory.Q.map a)
  have mappedNaturality := map_comp_eq_map_comp restriction hNX.symm
  apply (cancel_mono (targetFunctor.map (DerivedCategory.Q.map (restrictComplexMap X U a)))).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (restriction.map sourceComparison ≫ ·) hR.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (restrictedDerivedHomClassIso X U E I).hom) mappedNaturality).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (restriction.map sourceMap ≫ ·) key).trans
              ((Category.assoc _ _ _).symm.trans
                ((congrArg (· ≫ strictlyPerfectHomComparison (X.over U)
                  (derivedInternalHomOfBifunctor (X.over U))
                  (restrictComplex X E U) (restrictComplex X I U)) hL).trans
                  ((Category.assoc _ _ _).trans
                    ((congrArg ((restrictedSheafHomClassIso X U E F).hom ≫ ·) hNU).trans
                      (Category.assoc _ _ _).symm)))))))))

/-- **The comparison to derived internal Hom commutes with restriction to a slice.** For
arbitrary complexes `E` and `F` of `O`-modules the square

```
  (Q SheafHom(E, F))|_U  ⟶  (RSheafHom(QE, QF))|_U
          ↓                            ↓
  Q SheafHom(E|_U, F|_U) ⟶  RSheafHom(Q(E|_U), Q(F|_U))
```

commutes, the horizontal maps being the canonical comparisons of Stacks 08JH over `(C, O)` and
over `(C/U, O|_U)`, the left vertical map the restriction of the naive internal Hom complex and
the right vertical map Stacks 08JB.

The square is proved at a K-injective target from the model characterisation of Stacks 08JB, and
transported to an arbitrary target along the augmentation `F ⟶ I` into the chosen K-injective
resolution: both verticals and both comparisons are natural in the target, and the map that the
augmentation induces on the derived internal Hom over `U` is an isomorphism, so it may be
cancelled. The map it induces on the *naive* internal Hom complexes need not be one, which is
why no hypothesis on `E` is required. -/
theorem strictlyPerfectHomComparison_restriction :
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
        (strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) E F) ≫
      (restrictedDerivedHomClassIso X U E F).hom =
    (restrictedSheafHomClassIso X U E F).hom ≫
      strictlyPerfectHomComparison (X.over U) (derivedInternalHomOfBifunctor (X.over U))
        (restrictComplex X E U) (restrictComplex X F U) := by
  have hKI : ((kInjectiveResolution X).obj F).IsKInjective :=
    Stacks.Injectives.kInjectiveResolutionFunctor_obj_isKInjective
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) F
  exact strictlyPerfectHomComparison_restriction_aux X U E F
    ((kInjectiveResolution X).obj F) ((kInjectiveAugmentation X).app F)

/-- The restriction of the comparison over `(C, O)`, read through the two restriction
isomorphisms, is the comparison over `U`. -/
theorem restricted_strictlyPerfectHomComparison_eq :
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
        (strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) E F) =
      (restrictedSheafHomClassIso X U E F).hom ≫
        strictlyPerfectHomComparison (X.over U) (derivedInternalHomOfBifunctor (X.over U))
          (restrictComplex X E U) (restrictComplex X F U) ≫
        (restrictedDerivedHomClassIso X U E F).inv :=
  ((Iso.eq_comp_inv (restrictedDerivedHomClassIso X U E F)).mpr
    (strictlyPerfectHomComparison_restriction X U E F)).trans (Category.assoc _ _ _)

/-- **The comparison restricts to an isomorphism exactly when the comparison over `U` is one.**
Both verticals of the restriction square are isomorphisms, so invertibility of the comparison
over `(C, O)` after restriction to `U` is invertibility of the comparison over `U`. This is the
step by which Stacks 08JH, which is local on the site, is globalised. -/
theorem isIso_restricted_strictlyPerfectHomComparison_iff :
    IsIso ((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map
        (strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) E F)) ↔
      IsIso (strictlyPerfectHomComparison (X.over U) (derivedInternalHomOfBifunctor (X.over U))
        (restrictComplex X E U) (restrictComplex X F U)) := by
  rw [restricted_strictlyPerfectHomComparison_eq, isIso_comp_left_iff]
  exact ⟨fun h => @IsIso.of_isIso_comp_right _ _ _ _ _ _ (restrictedDerivedHomClassIso X U E F).inv
      (restrictedDerivedHomClassIso X U E F).isIso_inv h,
    fun h => (@asIso _ _ _ _ _ h ≪≫ (restrictedDerivedHomClassIso X U E F).symm).isIso_hom⟩

end Restriction

end AlgebraicGeometry.RingedSite

end
