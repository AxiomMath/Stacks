module

public import StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraSheafPolynomial
public import StacksFrontier.Cotangent.SheavesOfRings.SectionsComparisonNaturality

/-!
# The standard resolution of the sections is a local isomorphism

Let `A ⟶ B` be a homomorphism of sheaves of commutative rings on a site. Over every object `U`
of the site, Tag 08SX compares the standard resolution of the ring map `A(U) → B(U)` with the
sections over `U` of the standard resolution of `A ⟶ B`. This file assembles that comparison
into a morphism of presheaves of commutative rings and proves that it is a **local
isomorphism**: the sheafification of `U ↦ P'_n(U)` is `P_n`.

## Main definitions

* `CategoryTheory.Sheaf.sheafTower` is the tower of iterated free algebra sheaves, whose stage
  `n + 1` is the degree-`n` term of the standard resolution of `A ⟶ B`.
* `CategoryTheory.Sheaf.towerPresheaf` is the presheaf `U ↦ A(U)[A(U)[⋯[B(U)]⋯]]` of iterated
  polynomial algebras on the sections, with the tower maps of the restriction squares as
  restriction maps.
* `CategoryTheory.Sheaf.laxPresheaf` is the comonad comparison of Tag 08SX at a fixed sheaf of
  `A`-algebras, as a morphism of presheaves of commutative rings.
* `CategoryTheory.Sheaf.towerComparison` is the comparison of the two towers.

## Main results

* `CategoryTheory.Sheaf.laxPresheaf_eq`: the comonad comparison is the unit of sheafification,
  read through the identification of the free algebra sheaf with the sheafified polynomial
  presheaf.
* `CategoryTheory.Sheaf.towerComparison_succ`: the comparison at stage `n + 1` is renaming the
  variables along the comparison at stage `n`, followed by the comonad comparison.
* `CategoryTheory.Sheaf.isLocallyInjective_towerComparison` and
  `CategoryTheory.Sheaf.isLocallySurjective_towerComparison`: **the comparison of towers is a
  local isomorphism**.
* `CategoryTheory.Sheaf.W_towerComparison`: equivalently, sheafification inverts it, so the
  sheafification of the presheaf of iterated polynomial algebras on the sections is the
  corresponding stage of the tower of free algebra sheaves
  (`CategoryTheory.Sheaf.sheafifiedTowerIso`).
* `CategoryTheory.Sheaf.resolutionTermSheafifiedIso`: the degree-`n` term of the standard
  resolution of `A ⟶ B` is the sheafification of the presheaf of degree-`n` terms of the
  standard resolutions of the section maps.

## References

* [Stacks Project, Tag 08SW](https://stacks.math.columbia.edu/tag/08SW)
* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 08SR](https://stacks.math.columbia.edu/tag/08SR)
* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

open Stacks.Sites.FreeAlgebra (polynomialPresheaf polynomialPresheafMap polynomialVariable
  underlyingPresheaf freeAlgebraSheafVariable freeAlgebraSheafCoefficientMap)

universe t u v w

namespace CategoryTheory.Sheaf

/-! ## Sheafification of presheaves of sets and of rings in a large coefficient universe -/

/-- Sheafification of presheaves of sets valued in the universe of a small site. -/
private theorem smallSiteHasSheafifyType {D : Type t} [SmallCategory D]
    (K : GrothendieckTopology D) : HasSheafify K (Type t) := inferInstance

/-- On a small site, sheafification of presheaves of sets inverts exactly the locally bijective
maps. -/
private theorem smallSiteWEqualsLocallyBijectiveType {D : Type t} [SmallCategory D]
    (K : GrothendieckTopology D) : K.WEqualsLocallyBijective (Type t) := inferInstance

/-- On a small site, sheafification of presheaves of commutative rings inverts exactly the
locally bijective maps. -/
private theorem smallSiteWEqualsLocallyBijectiveCommRingCat {D : Type t} [SmallCategory D]
    (K : GrothendieckTopology D) : K.WEqualsLocallyBijective CommRingCat.{t} := inferInstance

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Presheaves of sets in a universe containing the site admit sheafification. -/
instance hasSheafifyType : HasSheafify J (Type (max u v w)) := by
  let : HasSheafify ((equivSmallModel.{max u v w} C).inverse.inducedTopology J)
      (Type (max u v w)) := smallSiteHasSheafifyType _
  exact hasSheafifyEssentiallySmallSite.{v, _, u, _, max u v w} J _

/-- In this universe, sheafification of presheaves of sets inverts exactly the locally bijective
maps. -/
instance wEqualsLocallyBijectiveType : J.WEqualsLocallyBijective (Type (max u v w)) := by
  let : ((equivSmallModel.{max u v w} C).inverse.inducedTopology J).WEqualsLocallyBijective
      (Type (max u v w)) := smallSiteWEqualsLocallyBijectiveType _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, _, u, _, max u v w} J

/-- In this universe, sheafification of presheaves of commutative rings inverts exactly the
locally bijective maps. -/
instance wEqualsLocallyBijectiveCommRingCat :
    J.WEqualsLocallyBijective CommRingCat.{max u v w} := by
  let : ((equivSmallModel.{max u v w} C).inverse.inducedTopology J).WEqualsLocallyBijective
      CommRingCat.{max u v w} := smallSiteWEqualsLocallyBijectiveCommRingCat _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, _, u, _, max u v w} J

variable {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

/-! ## The two towers -/

/-- The stage-`n` tower of iterated free algebra sheaves, `A[A[⋯[B]⋯]]` with `n` pairs of
brackets. The degree-`n` term of the standard resolution is stage `n + 1`. -/
noncomputable abbrev sheafTower (n : ℕ) : Under A :=
  (((standardResolutionComonad.{v, u, w} J A : Comonad (Under A)) :
    Under A ⥤ Under A).iterate n).obj (Under.mk f)

/-- The presheaf of stage-`n` towers of iterated polynomial algebras on the sections, with the
tower maps of the restriction squares as restriction maps. -/
noncomputable def towerPresheaf (n : ℕ) : Cᵒᵖ ⥤ CommRingCat.{max u v w} where
  obj U := CommRingCat.of (CommAlgCat.standardTower.{max u v w, max u v w}
    (A.obj.obj U) (sectionsAlgebra J f U) n)
  map g := CommRingCat.ofHom (CommAlgCat.standardTowerMap.{max u v w, max u v w, max u v w}
    (sectionsRestrictionSquare J f g) n)
  map_id U := by
    apply CommRingCat.hom_ext
    rw [sectionsRestrictionSquare_id,
      CommAlgCat.standardTowerMap_id.{max u v w, max u v w}]
    rfl
  map_comp g h := by
    apply CommRingCat.hom_ext
    rw [sectionsRestrictionSquare_comp,
      CommAlgCat.standardTowerMap_comp.{max u v w, max u v w}]
    rfl

/-- The restriction map of `towerPresheaf J f n` along `g` is the tower map of the restriction
square of `g`. -/
@[simp]
theorem towerPresheaf_map {U V : Cᵒᵖ} (g : U ⟶ V) (n : ℕ) :
    ((towerPresheaf J f n).map g).hom =
      CommAlgCat.standardTowerMap.{max u v w, max u v w, max u v w}
        (sectionsRestrictionSquare J f g) n :=
  rfl

/-- The restriction maps of stage `n + 1` of the sections tower are those of the presheaf of
polynomial rings on stage `n`. -/
theorem towerPresheaf_succ_map_eq {U V : Cᵒᵖ} (g : U ⟶ V) (n : ℕ) :
    ((towerPresheaf J f (n + 1)).map g).hom =
      ((polynomialPresheaf J A (towerPresheaf J f n ⋙
        forget CommRingCat.{max u v w})).map g).hom := by
  have htgt : ((polynomialPresheaf J A (towerPresheaf J f n ⋙
        forget CommRingCat.{max u v w})).map g).hom =
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp (A.obj.map g).hom)
        (fun e ↦ MvPolynomial.X
          (CommAlgCat.standardTowerMap.{max u v w, max u v w, max u v w}
            (sectionsRestrictionSquare J f g) n e)) := rfl
  rw [towerPresheaf_map, htgt]
  refine CommAlgCat.standardTower_succ_hom_ext.{max u v w, max u v w}
    (A.obj.obj U) (sectionsAlgebra J f U) n (fun a => ?_) (fun q => ?_)
  · exact (CommAlgCat.standardTowerMap_algebraMap
      (sectionsRestrictionSquare J f g) (n + 1) a).trans
      (MvPolynomial.eval₂Hom_C (MvPolynomial.C.comp (A.obj.map g).hom) _ a).symm
  · change CommAlgCat.standardTowerMap.{max u v w, max u v w, max u v w}
        (sectionsRestrictionSquare J f g) (n + 1) (MvPolynomial.X q) =
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp (A.obj.map g).hom)
        (fun e ↦ MvPolynomial.X
          (CommAlgCat.standardTowerMap.{max u v w, max u v w, max u v w}
            (sectionsRestrictionSquare J f g) n e)) (MvPolynomial.X q)
    rw [MvPolynomial.eval₂Hom_X']
    exact CommAlgCat.standardTowerMap_standardTowerX
      (sectionsRestrictionSquare J f g) n q

/-- Stage `n + 1` of the sections tower is the presheaf of polynomial rings on stage `n`. -/
noncomputable def towerPresheafSuccIso (n : ℕ) :
    towerPresheaf J f (n + 1) ≅
      polynomialPresheaf J A (towerPresheaf J f n ⋙ forget CommRingCat.{max u v w}) where
  hom :=
    { app := fun U => 𝟙 ((towerPresheaf J f (n + 1)).obj U)
      naturality := fun _ _ g =>
        (Category.comp_id _).trans
          ((CommRingCat.hom_ext (towerPresheaf_succ_map_eq J f g n)).trans
            (Category.id_comp _).symm) }
  inv :=
    { app := fun U => 𝟙 ((towerPresheaf J f (n + 1)).obj U)
      naturality := fun _ _ g =>
        (Category.comp_id _).trans
          ((CommRingCat.hom_ext (towerPresheaf_succ_map_eq J f g n).symm).trans
            (Category.id_comp _).symm) }
  hom_inv_id := NatTrans.ext (funext fun _ => Category.id_comp _)
  inv_hom_id := NatTrans.ext (funext fun _ => Category.id_comp _)

/-! ## The comonad comparison as a morphism of presheaves -/

/-- Renaming the variables leaves a constant polynomial alone. -/
theorem mvPolynomialRenameHom_C {R : Type t} [CommRing R] {σ τ : Type t} (h : σ → τ) (a : R) :
    MvPolynomial.eval₂Hom (MvPolynomial.C : R →+* MvPolynomial τ R)
        (fun y ↦ MvPolynomial.X (h y)) (MvPolynomial.C a) = MvPolynomial.C a :=
  MvPolynomial.eval₂Hom_C _ _ a

/-- The comonad comparison of Tag 08SX at a fixed sheaf of `A`-algebras, as a morphism of
presheaves of commutative rings `U ↦ A(U)[X(U)]` to the sections of the free algebra sheaf. -/
noncomputable def laxPresheaf (X : Under A) :
    polynomialPresheaf J A (underlyingPresheaf J X.right) ⟶
      ((((standardResolutionComonad.{v, u, w} J A : Comonad (Under A)) :
        Under A ⥤ Under A).obj X).right).obj where
  app U := CommRingCat.ofHom ((sectionsComonadLax J U).app X).hom.toRingHom
  naturality U V g := by
    apply CommRingCat.hom_ext
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun x => ?_)
    · have hU : ((sectionsComonadLax J U).app X).hom (MvPolynomial.C a) =
          algebraMap (A.obj.obj U)
            ((sectionsAlgebraFunctor J U).obj
              ((((standardResolutionComonad.{v, u, w} J A : Comonad (Under A)) :
                Under A ⥤ Under A).obj X))) a :=
        ((sectionsComonadLax J U).app X).hom.commutes a
      have hV : ((sectionsComonadLax J V).app X).hom
            (MvPolynomial.C ((A.obj.map g).hom a)) =
          algebraMap (A.obj.obj V)
            ((sectionsAlgebraFunctor J V).obj
              ((((standardResolutionComonad.{v, u, w} J A : Comonad (Under A)) :
                Under A ⥤ Under A).obj X))) ((A.obj.map g).hom a) :=
        ((sectionsComonadLax J V).app X).hom.commutes _
      change ((sectionsComonadLax J V).app X).hom
          (MvPolynomial.eval₂Hom (MvPolynomial.C.comp (A.obj.map g).hom)
            (fun e ↦ MvPolynomial.X ((underlyingPresheaf J X.right).map g e))
            (MvPolynomial.C a)) =
        sectionsRestrictionHom J g
          ((((standardResolutionComonad.{v, u, w} J A : Comonad (Under A)) :
            Under A ⥤ Under A).obj X))
          (((sectionsComonadLax J U).app X).hom (MvPolynomial.C a))
      refine Eq.trans (congrArg (fun z => ((sectionsComonadLax J V).app X).hom z)
        (MvPolynomial.eval₂Hom_C (MvPolynomial.C.comp (A.obj.map g).hom)
          (fun e ↦ MvPolynomial.X ((underlyingPresheaf J X.right).map g e)) a)) ?_
      refine Eq.trans hV ?_
      refine Eq.trans (sectionsRestrictionHom_algebraMap J g
        ((((standardResolutionComonad.{v, u, w} J A : Comonad (Under A)) :
          Under A ⥤ Under A).obj X)) a).symm ?_
      exact congrArg (fun z => sectionsRestrictionHom J g
          ((((standardResolutionComonad.{v, u, w} J A : Comonad (Under A)) :
            Under A ⥤ Under A).obj X)) z) hU.symm
    · change ((sectionsComonadLax J V).app X).hom
          (MvPolynomial.eval₂Hom (MvPolynomial.C.comp (A.obj.map g).hom)
            (fun e ↦ MvPolynomial.X ((underlyingPresheaf J X.right).map g e))
            (MvPolynomial.X x)) =
        sectionsRestrictionHom J g
          ((((standardResolutionComonad.{v, u, w} J A : Comonad (Under A)) :
            Under A ⥤ Under A).obj X))
          (((sectionsComonadLax J U).app X).hom (MvPolynomial.X x))
      rw [MvPolynomial.eval₂Hom_X']
      exact (sectionsComonadLax_variable_restriction J g X x).symm

/-- The sections of the free algebra sheaf on a sheaf of `A`-algebras are the sheafification of
the presheaf of polynomial rings on its sections. -/
noncomputable def laxTargetIso (X : Under A) :
    sheafify J (polynomialPresheaf J A (underlyingPresheaf J X.right)) ≅
      ((((standardResolutionComonad.{v, u, w} J A : Comonad (Under A)) :
        Under A ⥤ Under A).obj X).right).obj :=
  (sheafToPresheaf J CommRingCat.{max u v w}).mapIso
    (freeAlgebraSheafRightIso J A ((forgetAlgebraSheaf.{v, u, w} J A).obj X)).symm

/-- **The comonad comparison is the unit of sheafification.** Read through the identification of
the free algebra sheaf with the sheafification of the presheaf of polynomial rings, the
comparison of Tag 08SX is the sheafification unit. -/
theorem laxPresheaf_eq (X : Under A) :
    laxPresheaf J X =
      toSheafify J (polynomialPresheaf J A (underlyingPresheaf J X.right)) ≫
        (laxTargetIso J X).hom := by
  refine NatTrans.ext (funext fun U => ?_)
  apply CommRingCat.hom_ext
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun x => ?_)
  · refine Eq.trans (((sectionsComonadLax J U).app X).hom.commutes a) ?_
    exact (congrArg
      (fun k : A ⟶ (((freeAlgebraSheaf J A).obj
          ((forgetAlgebraSheaf.{v, u, w} J A).obj X)).right) => (k.hom.app U).hom a)
      (Under.w (freeAlgebraSheafComparisonInv J A
        ((forgetAlgebraSheaf.{v, u, w} J A).obj X)))).symm
  · refine Eq.trans (sectionsComonadLax_variable J U X x) ?_
    exact (congrArg (fun k => k.app U x)
      (variable_comp_freeAlgebraSheafComparisonInv J A
        ((forgetAlgebraSheaf.{v, u, w} J A).obj X))).symm

/-- The comonad comparison `laxPresheaf J X` is locally injective. -/
instance isLocallyInjective_laxPresheaf (X : Under A) :
    Presheaf.IsLocallyInjective J (laxPresheaf J X) := by
  rw [laxPresheaf_eq]
  infer_instance

/-- The comonad comparison `laxPresheaf J X` is locally surjective. -/
instance isLocallySurjective_laxPresheaf (X : Under A) :
    Presheaf.IsLocallySurjective J (laxPresheaf J X) := by
  rw [laxPresheaf_eq]
  infer_instance

/-- **The comonad comparison is inverted by sheafification.** -/
theorem W_laxPresheaf (X : Under A) : J.W (laxPresheaf J X) :=
  J.W_of_isLocallyBijective _

/-! ## The comparison of the two towers -/

/-- The comparison of the stage-`n` towers: over every object of the site it is the `n`-fold
iterate of the comonad comparison of Tag 08SX. -/
noncomputable def towerComparison (n : ℕ) :
    towerPresheaf J f n ⟶ (sheafTower J f n).right.obj where
  app U := CommRingCat.ofHom
    ((Functor.iterateLaxHom (sectionsComonadLax J U) n).app (Under.mk f)).hom.toRingHom
  naturality U V g := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun q => ?_
    exact (iterateSectionsComonadLax_restriction J f g n q).symm

/-- The comparison at stage `n + 1` renames the variables along the comparison at stage `n` and
then applies the comonad comparison. -/
theorem towerComparison_succ (n : ℕ) :
    towerComparison J f (n + 1) =
      (towerPresheafSuccIso J f n).hom ≫
        polynomialPresheafMap J A (Functor.whiskerRight (towerComparison J f n)
            (forget CommRingCat.{max u v w})) ≫
          laxPresheaf J (sheafTower J f n) := by
  refine NatTrans.ext (funext fun U => ?_)
  apply CommRingCat.hom_ext
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun q => ?_)
  · refine Eq.trans
      (((Functor.iterateLaxHom (sectionsComonadLax J U) (n + 1)).app
        (Under.mk f)).hom.commutes a) ?_
    refine Eq.trans
      (((sectionsComonadLax J U).app (sheafTower J f n)).hom.commutes a).symm ?_
    exact congrArg (fun z => ((sectionsComonadLax J U).app (sheafTower J f n)).hom z)
      (mvPolynomialRenameHom_C
        (⇑((Functor.iterateLaxHom (sectionsComonadLax J U) n).app (Under.mk f)).hom) a).symm
  · refine Eq.trans (iterateSectionsComonadLax_succ_apply J f U n (MvPolynomial.X q)) ?_
    exact congrArg (fun z => ((sectionsComonadLax J U).app (sheafTower J f n)).hom z)
      ((MvPolynomial.rename_X
          (⇑((Functor.iterateLaxHom (sectionsComonadLax J U) n).app (Under.mk f)).hom) q).trans
        (MvPolynomial.eval₂Hom_X' MvPolynomial.C (fun y ↦ MvPolynomial.X
          (((Functor.iterateLaxHom (sectionsComonadLax J U) n).app (Under.mk f)).hom y)) q).symm)

/-- **The comparison of towers is inverted by sheafification**: the sheafification of the
presheaf of iterated polynomial algebras on the sections is the stage-`n` tower of free algebra
sheaves. -/
theorem W_towerComparison (n : ℕ) : J.W (towerComparison J f n) := by
  induction n with
  | zero =>
      have hi : Presheaf.IsLocallyInjective J (towerComparison J f 0) :=
        Presheaf.isLocallyInjective_of_injective J _ (fun _ _ _ hxy => hxy)
      have hs : Presheaf.IsLocallySurjective J (towerComparison J f 0) :=
        Presheaf.isLocallySurjective_of_surjective J _ (fun _ x => ⟨x, rfl⟩)
      exact J.W_of_isLocallyBijective _
  | succ n ih =>
      have := ih.isLocallyInjective
      have := ih.isLocallySurjective
      rw [towerComparison_succ]
      exact MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso _ _)
        (MorphismProperty.comp_mem _ _ _
          (Stacks.Sites.FreeAlgebra.W_polynomialPresheafMap J A _
            (J.W_of_isLocallyBijective _))
          (W_laxPresheaf J _))

/-- The comparison of the stage-`n` towers is locally injective. -/
instance isLocallyInjective_towerComparison (n : ℕ) :
    Presheaf.IsLocallyInjective J (towerComparison J f n) :=
  (W_towerComparison J f n).isLocallyInjective

/-- The comparison of the stage-`n` towers is locally surjective. -/
instance isLocallySurjective_towerComparison (n : ℕ) :
    Presheaf.IsLocallySurjective J (towerComparison J f n) :=
  (W_towerComparison J f n).isLocallySurjective

/-- The sheafification of the comparison of the stage-`n` towers is an isomorphism. -/
instance isIso_presheafToSheaf_map_towerComparison (n : ℕ) :
    IsIso ((presheafToSheaf J CommRingCat.{max u v w}).map (towerComparison J f n)) :=
  (J.W_iff _).mp (W_towerComparison J f n)

/-- **The sheafification of the presheaf of iterated polynomial algebras on the sections is the
tower of free algebra sheaves.** -/
noncomputable def sheafifiedTowerIso (n : ℕ) :
    (presheafToSheaf J CommRingCat.{max u v w}).obj (towerPresheaf J f n) ≅
      (sheafTower J f n).right :=
  asIso ((presheafToSheaf J CommRingCat.{max u v w}).map (towerComparison J f n)) ≪≫
    asIso ((sheafificationAdjunction J CommRingCat.{max u v w}).counit.app
      (sheafTower J f n).right)

/-- Stage `n + 1` of the tower of free algebra sheaves is the degree-`n` term of the standard
resolution. -/
theorem sheafTower_succ_right (n : ℕ) :
    (sheafTower J f (n + 1)).right = resolutionTerm J f (op ⦋n⦌) :=
  congrArg Under.right (standardResolution_obj.{v, u, w} J f n).symm

/-- **The degree-`n` term of the standard resolution of `A ⟶ B` is the sheafification of the
presheaf of degree-`n` terms of the standard resolutions of the section maps `A(U) → B(U)`.** -/
noncomputable def resolutionTermSheafifiedIso (n : ℕ) :
    (presheafToSheaf J CommRingCat.{max u v w}).obj (towerPresheaf J f (n + 1)) ≅
      resolutionTerm J f (op ⦋n⦌) :=
  sheafifiedTowerIso J f (n + 1) ≪≫ eqToIso (sheafTower_succ_right J f n)

end CategoryTheory.Sheaf

end
