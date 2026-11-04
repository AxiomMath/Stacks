module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriekAffineEtale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedHomFromGenerators
public import StacksFrontier.CategoryTheory.Sites.SmallSiteSheafification

/-!
# Cohomology sheaves on the small affine étale site as associated sheaves

Let `X` be a scheme, `Λ` a ring and `M` an object of the unbounded derived category
`D(X_étale, Λ)` of sheaves of `Λ`-modules on the small étale site.  This file proves that the
cohomology sheaf `H^n(M)`, restricted to the small affine étale site `X_{affine, étale}`, is the
sheaf associated to the presheaf
```
U ↦ Hom_X((j_U)_! Λ, M[n]) = H^n(U, M).
```
This is the form of [Stacks, Tag 0BKV], together with the recollection
`Hom_X(j_! Λ, M[n]) = H^n(U, M)`, that the proof of [Stacks, Tag 0GLK] uses.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleFreeYonedaHomEquiv`: morphisms
  `(j_W)_! Λ ⟶ F` are sections of `F` over `W`.
* `Stacks.EtaleCohomology.affineEtaleHomPresheafUnbounded`: the presheaf
  `U ↦ Hom_X((j_U)_! Λ, M[n])` on `X_{affine, étale}`.
* `Stacks.EtaleCohomology.affineEtaleHomPresheafToHomology`: its comparison with `H^n(M)`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleFreeYoneda_epiLiftSieve_mem` and
  `affineEtaleFreeYoneda_epiLiftSieve_mem`: the objects `(j_U)_! Λ` are locally projective.
* `Stacks.EtaleCohomology.affineEtaleHomPresheafSheafificationIso`: the associated sheaf of
  `U ↦ Hom_X((j_U)_! Λ, M[n])` is the restriction of `H^n(M)`.

## Implementation notes

The comparison is shown to be locally injective and locally surjective by
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedHomFromGenerators`, whose only input is the
local projectivity of the objects `(j_U)_! Λ`; that input is the local surjectivity of an
epimorphism of sheaves applied to the generator of `(j_U)_! Λ`.  The derived category is the
standard model, as for `Stacks.EtaleCohomology.derivedLowerShriekUnbounded`, which the consumer
of this file composes with.

## References

* [Stacks Project, Tag 0BKV](https://stacks.math.columbia.edu/tag/0BKV)
* [Stacks Project, Tag 0GLK](https://stacks.math.columbia.edu/tag/0GLK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

open Stacks.Cohomology.DerivedHomFromGenerators

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] (X : Scheme.{u})

/-! ### Morphisms out of `(j_W)_! Λ` are sections over `W` -/

section FreeModule

variable {Λ}

universe s

/-- Morphisms out of the free module on a type are the maps out of the type: a morphism is
determined by the images of the generators. -/
def freeModuleOfTypeHomEquiv {S : Type (max s r)} {M : ModuleCat.{max s r} Λ} :
    ((freeModuleOfType.{r, max s r} Λ).obj S ⟶ M) ≃ (S ⟶ (forget (ModuleCat.{max s r} Λ)).obj M)
    where
  toFun φ := ↾fun x ↦ φ (Finsupp.single x 1)
  invFun ψ := ModuleCat.ofHom (Finsupp.linearCombination Λ ψ)
  left_inv φ := ModuleCat.hom_ext (Finsupp.lhom_ext' fun x ↦ LinearMap.ext_ring (by
    change Finsupp.linearCombination Λ _ (Finsupp.single x 1) = _
    simp
    rfl))
  right_inv ψ := by
    ext x
    change Finsupp.linearCombination Λ _ (Finsupp.single x 1) = _
    simp

variable (Λ) in
/-- The free module functor on types is left adjoint to the forgetful functor. -/
def freeModuleOfTypeAdj :
    freeModuleOfType.{r, max s r} Λ ⊣ forget (ModuleCat.{max s r} Λ) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ ↦ freeModuleOfTypeHomEquiv
      homEquiv_naturality_left_symm := fun {S T M} f g ↦ ModuleCat.hom_ext
        (Finsupp.lhom_ext' fun x ↦ LinearMap.ext_ring (by
          change Finsupp.linearCombination Λ _ (Finsupp.single x 1) =
            Finsupp.linearCombination Λ _ (Finsupp.lmapDomain Λ Λ f (Finsupp.single x 1))
          simp)) }

end FreeModule

/-- **Morphisms out of `(j_W)_! Λ` are sections over `W`.**  For a sheaf of `Λ`-modules `F` on the
small étale site of `X` and an object `W` of the site, morphisms
`Stacks.EtaleCohomology.etaleModuleFreeYoneda Λ X W ⟶ F` correspond to the sections of `F` over
`W`.  The bijection is the composite of the sheafification adjunction, the free-forgetful
adjunction and the Yoneda lemma. -/
def etaleModuleFreeYonedaHomEquiv (W : X.Etale) (F : EtaleModules.{u, r} Λ X) :
    ((etaleModuleFreeYoneda.{u, r} Λ X).obj W ⟶ F) ≃ F.val.obj (op W) :=
  ((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).homEquiv _ F).trans
    ((((freeModuleOfTypeAdj.{r, u + 1} Λ).whiskerRight (C := X.Etaleᵒᵖ)).homEquiv _ _).trans
      uliftYonedaEquiv)

variable {Λ X}

/-- The bijection `etaleModuleFreeYonedaHomEquiv` is natural in the sheaf. -/
lemma etaleModuleFreeYonedaHomEquiv_comp {W : X.Etale} {F F' : EtaleModules.{u, r} Λ X}
    (k : (etaleModuleFreeYoneda.{u, r} Λ X).obj W ⟶ F) (π : F ⟶ F') :
    etaleModuleFreeYonedaHomEquiv Λ X W F' (k ≫ π) =
      π.hom.app (op W) (etaleModuleFreeYonedaHomEquiv Λ X W F k) := by
  simp only [etaleModuleFreeYonedaHomEquiv, Equiv.trans_apply,
    Adjunction.homEquiv_naturality_right]
  rfl

/-- The bijection `etaleModuleFreeYonedaHomEquiv` is natural in the object of the site. -/
lemma etaleModuleFreeYonedaHomEquiv_map_comp {W' W : X.Etale} (w : W' ⟶ W)
    {F : EtaleModules.{u, r} Λ X} (k : (etaleModuleFreeYoneda.{u, r} Λ X).obj W ⟶ F) :
    etaleModuleFreeYonedaHomEquiv Λ X W' F ((etaleModuleFreeYoneda.{u, r} Λ X).map w ≫ k) =
      F.val.map w.op (etaleModuleFreeYonedaHomEquiv Λ X W F k) := by
  simp only [etaleModuleFreeYonedaHomEquiv, Equiv.trans_apply]
  rw [show (etaleModuleFreeYoneda.{u, r} Λ X).map w =
      (presheafToSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).map
        (((Functor.whiskeringRight _ _ _).obj (freeModuleOfType.{r, max (u + 1) r} Λ)).map
          (uliftYoneda.{max (u + 1) r}.map w)) from rfl,
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
  exact (uliftYonedaEquiv_naturality _ w.op).symm

/-- The bijection `etaleModuleFreeYonedaHomEquiv` is evaluation at the generator. -/
lemma etaleModuleFreeYonedaHomEquiv_eq {W : X.Etale} {F : EtaleModules.{u, r} Λ X}
    (k : (etaleModuleFreeYoneda.{u, r} Λ X).obj W ⟶ F) :
    etaleModuleFreeYonedaHomEquiv Λ X W F k =
      k.hom.app (op W) (etaleModuleFreeYonedaHomEquiv Λ X W _ (𝟙 _)) := by
  rw [← etaleModuleFreeYonedaHomEquiv_comp, Category.id_comp]

/-- The bijection `etaleModuleFreeYonedaHomEquiv` is additive. -/
lemma etaleModuleFreeYonedaHomEquiv_add {W : X.Etale} {F : EtaleModules.{u, r} Λ X}
    (k k' : (etaleModuleFreeYoneda.{u, r} Λ X).obj W ⟶ F) :
    etaleModuleFreeYonedaHomEquiv Λ X W F (k + k') =
      etaleModuleFreeYonedaHomEquiv Λ X W F k + etaleModuleFreeYonedaHomEquiv Λ X W F k' := by
  rw [etaleModuleFreeYonedaHomEquiv_eq, etaleModuleFreeYonedaHomEquiv_eq k,
    etaleModuleFreeYonedaHomEquiv_eq k']
  rfl

variable (Λ X) in
/-- `etaleModuleFreeYonedaHomEquiv` as an additive equivalence. -/
def etaleModuleFreeYonedaHomAddEquiv (W : X.Etale) (F : EtaleModules.{u, r} Λ X) :
    ((etaleModuleFreeYoneda.{u, r} Λ X).obj W ⟶ F) ≃+ F.val.obj (op W) where
  __ := etaleModuleFreeYonedaHomEquiv Λ X W F
  map_add' := etaleModuleFreeYonedaHomEquiv_add

variable (Λ X)

attribute [local instance] moduleCat_hasLimitsOfSize in
/-- On the small étale site, sheafification of presheaves of `Λ`-modules inverts exactly the
locally bijective morphisms.  It is transported from a small model of the site. -/
instance etaleModules_wEqualsLocallyBijective :
    X.smallEtaleTopology.WEqualsLocallyBijective (ModuleCat.{max (u + 1) r} Λ) := by
  let K := (equivSmallModel.{max (u + 1) r} X.Etale).inverse.inducedTopology X.smallEtaleTopology
  have : HasSheafify K (ModuleCat.{max (u + 1) r} Λ) := moduleCat_hasSheafify Λ K
  let : PreservesColimits (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max (u + 1) r, r, max (u + 1) r, max (u + 1) r} Λ
  have : PreservesFilteredColimits (forget (ModuleCat.{max (u + 1) r} Λ)) :=
    comp_preservesFilteredColimits
      (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat) (forget AddCommGrpCat)
  have : K.WEqualsLocallyBijective (ModuleCat.{max (u + 1) r} Λ) := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

variable {Λ X}

/-- **`(j_W)_! Λ` is locally projective on the small étale site.**  Along an epimorphism onto
`(j_W)_! Λ`, the morphisms `(j_{W'})_! Λ ⟶ (j_W)_! Λ` induced by the arrows `W' ⟶ W` of a
covering sieve lift: the generator, a section over `W`, lifts locally because an epimorphism of
sheaves is locally surjective. -/
theorem etaleModuleFreeYoneda_epiLiftSieve_mem {W : X.Etale} {A' : EtaleModules.{u, r} Λ X}
    (π : A' ⟶ (etaleModuleFreeYoneda.{u, r} Λ X).obj W) [Epi π] :
    Stacks.Cohomology.DerivedHomFromGenerators.epiLiftSieve (etaleModuleFreeYoneda.{u, r} Λ X) π ∈
      X.smallEtaleTopology W := by
  have hπ : Sheaf.IsLocallySurjective π :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := π)).2 inferInstance
  refine X.smallEtaleTopology.superset_covering ?_
    (Presheaf.imageSieve_mem X.smallEtaleTopology π.hom
      (etaleModuleFreeYonedaHomEquiv Λ X W _ (𝟙 _)))
  rintro W' w ⟨t, ht⟩
  refine ⟨(etaleModuleFreeYonedaHomEquiv Λ X W' A').symm t,
    (etaleModuleFreeYonedaHomEquiv Λ X W' _).injective ?_⟩
  rwa [etaleModuleFreeYonedaHomEquiv_comp, Equiv.apply_symm_apply, ← Category.comp_id
    ((etaleModuleFreeYoneda.{u, r} Λ X).map w), etaleModuleFreeYonedaHomEquiv_map_comp]

/-- **`(j_U)_! Λ` is locally projective on the small affine étale site**: the statement of
`etaleModuleFreeYoneda_epiLiftSieve_mem` for the objects of the affine étale site, which is a
dense subsite of the étale site. -/
theorem affineEtaleFreeYoneda_epiLiftSieve_mem {U : X.AffineEtale} {A' : EtaleModules.{u, r} Λ X}
    (π : A' ⟶ (AffineEtale.Spec X ⋙ etaleModuleFreeYoneda.{u, r} Λ X).obj U) [Epi π] :
    epiLiftSieve (AffineEtale.Spec X ⋙ etaleModuleFreeYoneda.{u, r} Λ X) π ∈
      AffineEtale.topology X U := by
  rw [← Functor.functorPushforward_mem_iff (AffineEtale.topology X) X.smallEtaleTopology
    (AffineEtale.Spec X)]
  refine X.smallEtaleTopology.superset_covering (Sieve.functorPushforward_monotone _ _ ?_)
    (Functor.IsCoverDense.functorPullback_pushforward_covering
      ⟨_, etaleModuleFreeYoneda_epiLiftSieve_mem π⟩)
  intro V v hv
  exact hv

/-! ### The presheaf `U ↦ Hom_X((j_U)_! Λ, M[n])` on the unbounded derived category -/

section Presheaf

attribute [local instance] HasDerivedCategory.standard

variable (Λ X)

/-- `U ↦ (j_U)_! Λ` on the small affine étale site, placed in degree zero of the unbounded derived
category `D(X_étale, Λ)`. -/
abbrev affineEtaleConstantUnbounded :
    X.AffineEtale ⥤ DerivedCategory (EtaleModules.{u, r} Λ X) :=
  AffineEtale.Spec X ⋙ etaleModuleFreeYoneda.{u, r} Λ X ⋙
    DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X) 0

/-- The presheaf `U ↦ Hom_X((j_U)_! Λ, M[n])` on the small affine étale site of `X`, for `M` in
the unbounded derived category `D(X_étale, Λ)`.  This is the presheaf `U ↦ H^n(U, M)` of the
source's recollection `Hom_X(j_! Λ, M[n]) = H^n(U, M)`. -/
abbrev affineEtaleHomPresheafUnbounded (M : DerivedCategory (EtaleModules.{u, r} Λ X)) (n : ℤ) :
    X.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) r + 1} :=
  (affineEtaleConstantUnbounded.{u, r} Λ X).op ⋙
    preadditiveYoneda.obj (M⟦n⟧) ⋙ AddCommGrpCat.uliftFunctor.{max (u + 1) r + 1}

variable {Λ X}

/-- The comparison at one object `U` of the affine étale site: a morphism
`(j_U)_! Λ ⟶ M[n]` of the derived category induces `(j_U)_! Λ ⟶ H^0(M[n]) = H^n(M)`, which is a
section of `H^n(M)` over `U`. -/
def affineEtaleHomToSection (M : DerivedCategory (EtaleModules.{u, r} Λ X)) (n : ℤ)
    (U : X.AffineEtale) :
    ((affineEtaleConstantUnbounded.{u, r} Λ X).obj U ⟶ M⟦n⟧) →+
      ((DerivedCategory.homologyFunctor _ n).obj M).val.obj (op ((AffineEtale.Spec X).obj U)) :=
  (etaleModuleFreeYonedaHomAddEquiv Λ X _ _).toAddMonoidHom.comp
    ((Preadditive.rightComp _ (homologyZeroShiftIso M n).hom).comp
      (homToHomologyZero _ (M⟦n⟧)))

/-- `affineEtaleHomToSection` sends `φ` to the section of `H^n(M)` over `U` corresponding to the
composite of `homToHomologyZero` applied to `φ` with `H^0(M[n]) ≅ H^n(M)`. -/
lemma affineEtaleHomToSection_apply (M : DerivedCategory (EtaleModules.{u, r} Λ X)) (n : ℤ)
    (U : X.AffineEtale) (φ : (affineEtaleConstantUnbounded.{u, r} Λ X).obj U ⟶ M⟦n⟧) :
    affineEtaleHomToSection M n U φ = etaleModuleFreeYonedaHomEquiv Λ X _ _
      (homToHomologyZero _ (M⟦n⟧) φ ≫
        (homologyZeroShiftIso M n).hom) := rfl

/-- `affineEtaleHomToSection` is natural in the object of the affine étale site. -/
lemma affineEtaleHomToSection_naturality (M : DerivedCategory (EtaleModules.{u, r} Λ X)) (n : ℤ)
    {V U : X.AffineEtale} (v : V ⟶ U)
    (φ : (affineEtaleConstantUnbounded.{u, r} Λ X).obj U ⟶ M⟦n⟧) :
    affineEtaleHomToSection M n V ((affineEtaleConstantUnbounded.{u, r} Λ X).map v ≫ φ) =
      ((DerivedCategory.homologyFunctor _ n).obj M).val.map ((AffineEtale.Spec X).map v).op
        (affineEtaleHomToSection M n U φ) := by
  rw [affineEtaleHomToSection_apply, affineEtaleHomToSection_apply, Functor.comp_map,
    Functor.comp_map, homToHomologyZero_comp_left, Category.assoc,
    etaleModuleFreeYonedaHomEquiv_map_comp]

/-- The comparison of `U ↦ Hom_X((j_U)_! Λ, M[n])` with the restriction of the cohomology sheaf
`H^n(M)` to the small affine étale site, assembled from `affineEtaleHomToSection`. -/
def affineEtaleHomPresheafToHomology (M : DerivedCategory (EtaleModules.{u, r} Λ X)) (n : ℤ) :
    affineEtaleHomPresheafUnbounded.{u, r} Λ X M n ⟶
      ((affineEtaleAbelianRestriction.{u, r} Λ X).obj
        ((DerivedCategory.homologyFunctor _ n).obj M)).val where
  app U := AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
    ((affineEtaleHomToSection M n U.unop).comp AddEquiv.ulift.toAddMonoidHom))
  naturality U U' g := by
    ext ⟨φ⟩
    exact ULift.ext _ _ (affineEtaleHomToSection_naturality M n g.unop φ)

/-- Two morphisms `(j_U)_! Λ ⟶ M[n]` with the same section of `H^n(M)` agree locally on `U`. -/
theorem affineEtaleHomToSection_vanishingSieve_mem (M : DerivedCategory (EtaleModules.{u, r} Λ X))
    (n : ℤ) {U : X.AffineEtale} (x y : (affineEtaleConstantUnbounded.{u, r} Λ X).obj U ⟶ M⟦n⟧)
    (h : affineEtaleHomToSection M n U x = affineEtaleHomToSection M n U y) :
    vanishingSieve (AffineEtale.Spec X ⋙ etaleModuleFreeYoneda.{u, r} Λ X) (M⟦n⟧) (x - y) ∈
      AffineEtale.topology X U := by
  refine homToHomologyZero_locallyInjective.{max (u + 1) r}
    (fun _ _ π _ ↦ affineEtaleFreeYoneda_epiLiftSieve_mem π) (M⟦n⟧) (x - y) ?_
  rw [affineEtaleHomToSection_apply, affineEtaleHomToSection_apply] at h
  have h' := (etaleModuleFreeYonedaHomEquiv Λ X _ _).injective h
  rw [cancel_mono] at h'
  exact (map_sub _ x y).trans (sub_eq_zero.2 h')

/-- Morphisms whose difference vanishes along `v` agree after restriction along `v`. -/
lemma affineEtaleConstantUnbounded_map_comp_eq (M : DerivedCategory (EtaleModules.{u, r} Λ X))
    (n : ℤ) {V U : X.AffineEtale} (v : V ⟶ U)
    (x y : (affineEtaleConstantUnbounded.{u, r} Λ X).obj U ⟶ M⟦n⟧)
    (hv : (vanishingSieve (AffineEtale.Spec X ⋙ etaleModuleFreeYoneda.{u, r} Λ X) (M⟦n⟧)
      (x - y)).arrows v) :
    (affineEtaleConstantUnbounded.{u, r} Λ X).map v ≫ x =
      (affineEtaleConstantUnbounded.{u, r} Λ X).map v ≫ y := by
  rwa [← sub_eq_zero, ← Preadditive.comp_sub]

/-- A section of `H^n(M)` over `U` comes, locally on `U`, from morphisms `(j_V)_! Λ ⟶ M[n]`. -/
theorem affineEtaleHomToSection_liftSieve_mem (M : DerivedCategory (EtaleModules.{u, r} Λ X))
    (n : ℤ) {U : X.AffineEtale}
    (s : ((DerivedCategory.homologyFunctor _ n).obj M).val.obj (op ((AffineEtale.Spec X).obj U))) :
    homologyLiftSieve (AffineEtale.Spec X ⋙ etaleModuleFreeYoneda.{u, r} Λ X) (M⟦n⟧)
        ((etaleModuleFreeYonedaHomEquiv Λ X _ _).symm s ≫ (homologyZeroShiftIso M n).inv) ∈
      AffineEtale.topology X U :=
  homToHomologyZero_locallySurjective (fun _ _ π _ ↦ affineEtaleFreeYoneda_epiLiftSieve_mem π)
    (M⟦n⟧) _

/-- The image of a lift produced by `affineEtaleHomToSection_liftSieve_mem` is the restricted
section. -/
lemma affineEtaleHomToSection_eq_of_homToHomologyZero_eq
    (M : DerivedCategory (EtaleModules.{u, r} Λ X)) (n : ℤ) {V U : X.AffineEtale} (v : V ⟶ U)
    (s : ((DerivedCategory.homologyFunctor _ n).obj M).val.obj (op ((AffineEtale.Spec X).obj U)))
    (ψ : (affineEtaleConstantUnbounded.{u, r} Λ X).obj V ⟶ M⟦n⟧)
    (hψ : homToHomologyZero _ (M⟦n⟧) ψ =
      (AffineEtale.Spec X ⋙ etaleModuleFreeYoneda.{u, r} Λ X).map v ≫
        (etaleModuleFreeYonedaHomEquiv Λ X _ _).symm s ≫ (homologyZeroShiftIso M n).inv) :
    affineEtaleHomToSection M n V ψ =
      ((DerivedCategory.homologyFunctor _ n).obj M).val.map ((AffineEtale.Spec X).map v).op s := by
  rw [affineEtaleHomToSection_apply, hψ, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, Functor.comp_map, etaleModuleFreeYonedaHomEquiv_map_comp,
    Equiv.apply_symm_apply]

/-- The comparison `affineEtaleHomPresheafToHomology` is locally injective. -/
instance affineEtaleHomPresheafToHomology_isLocallyInjective
    (M : DerivedCategory (EtaleModules.{u, r} Λ X)) (n : ℤ) :
    Presheaf.IsLocallyInjective (AffineEtale.topology X)
      (affineEtaleHomPresheafToHomology M n) where
  equalizerSieve_mem := by
    rintro U ⟨x⟩ ⟨y⟩ h
    refine (AffineEtale.topology X).superset_covering ?_
      (affineEtaleHomToSection_vanishingSieve_mem M n x y (congrArg ULift.down h))
    intro V v hv
    exact ULift.ext _ _ (affineEtaleConstantUnbounded_map_comp_eq M n v x y hv)

/-- The comparison `affineEtaleHomPresheafToHomology` is locally surjective. -/
instance affineEtaleHomPresheafToHomology_isLocallySurjective
    (M : DerivedCategory (EtaleModules.{u, r} Λ X)) (n : ℤ) :
    Presheaf.IsLocallySurjective (AffineEtale.topology X)
      (affineEtaleHomPresheafToHomology M n) where
  imageSieve_mem := by
    rintro U ⟨s⟩
    refine (AffineEtale.topology X).superset_covering ?_
      (affineEtaleHomToSection_liftSieve_mem M n s)
    rintro V v ⟨ψ, hψ⟩
    exact ⟨ULift.up ψ, ULift.ext _ _
      (affineEtaleHomToSection_eq_of_homToHomologyZero_eq M n v s ψ hψ)⟩

variable (X) in
/-- On the small affine étale site, sheafification of abelian presheaves inverts exactly the
locally bijective morphisms.  It is transported from a small model of the site. -/
theorem affineEtale_wEqualsLocallyBijective :
    (AffineEtale.topology X).WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) r + 1} := by
  have : ((equivSmallModel.{max (u + 1) r + 1} X.AffineEtale).inverse.inducedTopology
      (AffineEtale.topology X)).WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) r + 1} :=
    inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- The sheafification of the comparison `affineEtaleHomPresheafToHomology` is an isomorphism,
the comparison being locally injective and locally surjective. -/
instance isIso_presheafToSheaf_map_affineEtaleHomPresheafToHomology
    (M : DerivedCategory (EtaleModules.{u, r} Λ X)) (n : ℤ) :
    IsIso ((presheafToSheaf (AffineEtale.topology X) AddCommGrpCat.{max (u + 1) r + 1}).map
      (affineEtaleHomPresheafToHomology M n)) := by
  have := affineEtale_wEqualsLocallyBijective.{u, r} X
  have : (AffineEtale.topology X).HasSheafCompose (forget AddCommGrpCat.{max (u + 1) r + 1}) :=
    ⟨fun _ hP ↦ Presheaf.isSheaf_comp_of_isSheaf _ _ _ hP⟩
  exact (Sheaf.isLocallyBijective_iff_isIso (A := AddCommGrpCat.{max (u + 1) r + 1}) _).1
    ⟨(Presheaf.isLocallyInjective_presheafToSheaf_map_iff _ _).2 inferInstance,
      (Presheaf.isLocallySurjective_presheafToSheaf_map_iff _ _).2 inferInstance⟩

/-- **The cohomology sheaf `H^n(M)` on the small affine étale site is the sheaf associated to
`U ↦ Hom_X((j_U)_! Λ, M[n])`**, for `M` in the unbounded derived category `D(X_étale, Λ)`.

This is the form of [Stacks, Tag 0BKV] that the proof of [Stacks, Tag 0GLK] uses, together with
its recollection `Hom_X(j_! Λ, M[n]) = H^n(U, M)`: the comparison
`affineEtaleHomPresheafToHomology` is locally injective and locally surjective, and its target is
already a sheaf. -/
def affineEtaleHomPresheafSheafificationIso (M : DerivedCategory (EtaleModules.{u, r} Λ X))
    (n : ℤ) :
    (presheafToSheaf (AffineEtale.topology X) AddCommGrpCat.{max (u + 1) r + 1}).obj
        (affineEtaleHomPresheafUnbounded.{u, r} Λ X M n) ≅
      (affineEtaleAbelianRestriction.{u, r} Λ X).obj
        ((DerivedCategory.homologyFunctor _ n).obj M) :=
  asIso ((presheafToSheaf (AffineEtale.topology X) AddCommGrpCat.{max (u + 1) r + 1}).map
      (affineEtaleHomPresheafToHomology M n)) ≪≫ (sheafificationIso _).symm

end Presheaf

end Stacks.EtaleCohomology
