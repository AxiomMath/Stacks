module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationLocality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.SheafificationOfTheCohomologyPresheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EvaluationConservative
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomProducts
public import StacksFrontier.Homology.DerivedCategory.KInjectiveProducts
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# Cohomology sheaves of products of shifted acyclic sheaves of modules

Let `(C, J)` be a site, `R` a sheaf of rings on it and `ℬ` a class of objects of `C` such that
every object has a covering by objects of `ℬ`. Let `(F_i)_{i ∈ I}` be a family of sheaves of
`R`-modules which are acyclic on `ℬ`, i.e. `H^q(U, F_i) = 0` for `q > 0` and `U ∈ ℬ`, and let
`k : I → ℤ`. Products in the unbounded derived category `D(R)` are not computed termwise on
cohomology sheaves in general, because products of sheaves of modules need not be exact; but for
such a family they are:
`H^j(∏_i F_i[k_i]) ≅ ∏_{k_i = -j} F_i`, compatibly with the projections.

The argument computes the product by termwise products of the shifted injective resolutions,
which are K-injective. The `j`-th cohomology sheaf of a complex of sheaves is the sheafification
of the presheaf cohomology of the underlying complex of presheaves. On sections over an object `U`
of `ℬ`, presheaf cohomology commutes with products (products of modules are exact), and the
factors with `k_i ≠ -j` contribute `H^{j + k_i}(U, F_i) = 0`. A map of presheaves of modules which
is bijective on sections over the objects of a covering class becomes an isomorphism after
sheafification, which concludes.

As an application, a complex `Z(F)` with zero differentials and `F` in every degree `n ≥ 0`
represents the product `∏_n F[-n]` in `D(R)`.

## Main definitions

* `Stacks.Cohomology.CohomologySheafOfProducts.homologyShiftSingleIso`: the canonical
  isomorphism `H^j(F[0]⟦k⟧) ≅ F` when `k + j = 0`.
* `Stacks.Cohomology.CohomologySheafOfProducts.homologyPiShiftSingleIso`: the isomorphism
  `H^j(∏_i F_i[0]⟦k_i⟧) ≅ ∏_{k_i = -j} F_i`.
* `Stacks.Cohomology.CohomologySheafOfProducts.zeroDifferentialComplex`: the complex with zero
  differentials, `F` in every degree `n ≥ 0` and `0` in negative degrees.
* `Stacks.Cohomology.CohomologySheafOfProducts.zeroDifferentialComplexToPi`: the morphism
  `Z(F) ⟶ ∏_n F[0]⟦-n⟧` in the derived category.

## Main results

* `Stacks.Cohomology.CohomologySheafOfProducts.homologyPiShiftSingleIso_hom_π`: the
  isomorphism `homologyPiShiftSingleIso` is compatible with the projections.
* `Stacks.Cohomology.CohomologySheafOfProducts.isIso_zeroDifferentialComplexToPi`: the
  morphism `Z(F) ⟶ ∏_n F[0]⟦-n⟧` is an isomorphism.

## Implementation notes

The universe `w` of the sheaf of rings and the universe `v` of the modules are independent, as in
the situation of a ringed site whose structure sheaf lives in a smaller universe than the
modules considered. The index type `I` lies in `Type` and is small with respect to the module
universe; countable index types such as `ℕ` and `ℕ × ℕ` qualify.

The computation of the cohomology sheaves is carried out on complexes rather than through the
derived presheaf of sections of Tag 0BKV, whose construction is tied to a ringed site with ring
and modules in one universe: the comparison used is `sheafificationHomologyIso`, the
sheafification of presheaf cohomology of a complex of sheaves.

The acyclicity hypothesis is phrased with Mathlib's right derived functors
`(SheafOfModules.evaluation R (op U)).rightDerived q` of the sections functor.

## References

* [Stacks Project, Tag 0BKV](https://stacks.math.columbia.edu/tag/0BKV)
* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
* [Stacks Project, Tag 0H6Y](https://stacks.math.columbia.edu/tag/0H6Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

/- The global instances `Abelian (SheafOfModules.{max u v r w} O)` and its Grothendieck and
enough-injectives counterparts leave a stuck universe constraint against the modules here,
whose universe is independent of that of the site; the structures used are those at the module
universe `v`. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

/- Products of sheaves of modules come from `SheafOfModules.hasLimitsOfShape`; with the global
instances above removed, the instance search otherwise times out in countable and finite products
before reaching it. -/
attribute [local instance 1100] SheafOfModules.hasLimitsOfShape

universe w v u u' t d

namespace Stacks.Cohomology.CohomologySheafOfProducts

section Products

variable {𝒞 : Type*} [Category* 𝒞]

/-- If the factors of a product outside a subset of the index type are zero, the projection of
the product onto the subproduct over that subset is an isomorphism. -/
theorem isIso_pi_lift_π_of_isZero [HasZeroMorphisms 𝒞] {I : Type*} (Y : I → 𝒞) (p : I → Prop)
    [HasProduct Y] [HasProduct fun s : Subtype p => Y s.1]
    (hY : ∀ i, ¬ p i → IsZero (Y i)) :
    IsIso (Pi.lift fun s : Subtype p => Pi.π Y s.1) := by
  classical
  refine ⟨Pi.lift fun i => if h : p i then Pi.π (fun s : Subtype p => Y s.1) ⟨i, h⟩ else 0,
    ?_, ?_⟩
  · refine Pi.hom_ext _ _ fun i => ?_
    by_cases h : p i
    · simp [h]
    · exact (hY i h).eq_of_tgt _ _
  · refine Pi.hom_ext _ _ fun s => ?_
    simp [s.2]

/-- A morphism into a product over a subsingleton index type is an isomorphism as soon as its
component at one index is. -/
theorem isIso_pi_lift_of_subsingleton {S : Type*} [Subsingleton S] (f : S → 𝒞) [HasProduct f]
    {Y : 𝒞} (c : ∀ s, Y ⟶ f s) (s₀ : S) [IsIso (c s₀)] : IsIso (Pi.lift c) := by
  refine ⟨Pi.π f s₀ ≫ inv (c s₀), by simp, Pi.hom_ext _ _ fun s => ?_⟩
  obtain rfl := Subsingleton.elim s s₀
  simp

/-- A product over an empty index type in a category with a zero object is zero. -/
theorem isZero_pi_of_isEmpty [HasZeroMorphisms 𝒞] [HasZeroObject 𝒞] {S : Type*} [IsEmpty S]
    (f : S → 𝒞) [HasProduct f] : IsZero (∏ᶜ f) :=
  (IsZero.iff_id_eq_zero _).2 (Pi.hom_ext _ _ fun s => isEmptyElim s)

end Products

section KInjective

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{d} A]

/-- The derived category of a Grothendieck abelian category has every product indexed by a type
in `Type` which exists in the category itself. -/
instance hasProductsOfShape_derivedCategory [IsGrothendieckAbelian.{t} A] (I : Type)
    [HasProductsOfShape I A] : HasProductsOfShape I (DerivedCategory A) :=
  Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_of_exists_quasiIso_isKInjective
    (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian A)

end KInjective

section ShiftSingle

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{d} A]

/-- The canonical isomorphism `H^j(F[0]⟦k⟧) ≅ F` when `k + j = 0`: the shift compatibility of
the cohomology functors on the derived category, followed by `H^0(F[0]) ≅ F`. -/
def homologyShiftSingleIso (F : A) (k j : ℤ) (h : k + j = 0) :
    (DerivedCategory.homologyFunctor A j).obj
        ((shiftFunctor (DerivedCategory A) k).obj ((DerivedCategory.singleFunctor A 0).obj F)) ≅
      F :=
  ((DerivedCategory.homologyFunctor A 0).shiftIso k j 0 h).app _ ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app F

/-- The isomorphism `Q(I) ≅ F[0]` in the derived category, for the chosen injective resolution
`F → I` of `F`. -/
def resolutionIso (F : A) [HasInjectiveResolution F] :
    DerivedCategory.Q.obj (injectiveResolution F).cochainComplex ≅
      (DerivedCategory.singleFunctor A 0).obj F :=
  (asIso (DerivedCategory.Q.map (injectiveResolution F).ι')).symm ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ A 0).app F).symm

/-- The isomorphism `Q(I⟦k⟧) ≅ F[0]⟦k⟧` in the derived category, for the chosen injective
resolution `F → I` of `F`. -/
def shiftResolutionIso (F : A) [HasInjectiveResolution F] (k : ℤ) :
    DerivedCategory.Q.obj ((injectiveResolution F).cochainComplex⟦k⟧) ≅
      ((DerivedCategory.singleFunctor A 0).obj F)⟦k⟧ :=
  (DerivedCategory.Q.commShiftIso k).app _ ≪≫ (shiftFunctor _ k).mapIso (resolutionIso F)

instance isKInjective_shift_cochainComplex (F : A) [HasInjectiveResolution F] (k : ℤ) :
    ((injectiveResolution F).cochainComplex⟦k⟧).IsKInjective :=
  (CochainComplex.isKInjective_shift_iff _ _).2 inferInstance

/-- The product of the objects `F_i[0]⟦k_i⟧` of the derived category is represented by the
termwise product of the shifted injective resolutions. -/
def piShiftSingleIso {I : Type} [HasProductsOfShape I A]
    [HasProductsOfShape I (DerivedCategory A)] [HasInjectiveResolutions A]
    (F : I → A) (k : I → ℤ) :
    DerivedCategory.Q.obj (∏ᶜ fun i => (injectiveResolution (F i)).cochainComplex⟦k i⟧) ≅
      ∏ᶜ fun i => ((DerivedCategory.singleFunctor A 0).obj (F i))⟦k i⟧ :=
  IsLimit.conePointUniqueUpToIso
      (AlgebraicGeometry.RingedSite.isLimit_fan_Q_pi
        (fun i => (injectiveResolution (F i)).cochainComplex⟦k i⟧)
        (fun _ => inferInstance))
      (limit.isLimit _) ≪≫
    Pi.mapIso fun i => shiftResolutionIso (F i) (k i)

theorem piShiftSingleIso_hom_π {I : Type} [HasProductsOfShape I A]
    [HasProductsOfShape I (DerivedCategory A)] [HasInjectiveResolutions A]
    (F : I → A) (k : I → ℤ) (i : I) :
    (piShiftSingleIso F k).hom ≫ Pi.π _ i =
      DerivedCategory.Q.map (Pi.π (fun i => (injectiveResolution (F i)).cochainComplex⟦k i⟧) i) ≫
        (shiftResolutionIso (F i) (k i)).hom := by
  simp only [piShiftSingleIso, Iso.trans_hom, Category.assoc, Pi.mapIso_hom_π,
    limit.conePointUniqueUpToIso_hom_comp_assoc, Fan.mk_π_app]

end ShiftSingle

section Resolutions

variable {A : Type*} [Category* A] [Abelian A] {A' : Type*} [Category* A'] [Abelian A']

/-- For an injective resolution `I` of `X` and an additive functor `G`, the short complex of
`G(I)` in degree `m + 1`, read on the `ℤ`-indexed complex, is the one read on the `ℕ`-indexed
complex. -/
def scIsoCochainComplex {X : A} (Rs : InjectiveResolution X) (G : A ⥤ A') [G.Additive]
    (m : ℕ) :
    ((G.mapHomologicalComplex _).obj Rs.cochainComplex).sc' (m : ℤ) ((m : ℤ) + 1)
        ((m : ℤ) + 2) ≅
      ((G.mapHomologicalComplex _).obj Rs.cocomplex).sc' m (m + 1) (m + 2) :=
  ShortComplex.isoMk (G.mapIso (Rs.cochainComplexXIso (m : ℤ) m rfl))
    (G.mapIso (Rs.cochainComplexXIso ((m : ℤ) + 1) (m + 1) (by omega)))
    (G.mapIso (Rs.cochainComplexXIso ((m : ℤ) + 2) (m + 2) (by omega)))
    (by
      change G.map _ ≫ G.map (Rs.cocomplex.d m (m + 1)) =
        G.map (Rs.cochainComplex.d (m : ℤ) ((m : ℤ) + 1)) ≫ G.map _
      rw [Rs.cochainComplex_d (m : ℤ) ((m : ℤ) + 1) m (m + 1) rfl (by omega)]
      simp only [← G.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id])
    (by
      change G.map _ ≫ G.map (Rs.cocomplex.d (m + 1) (m + 2)) =
        G.map (Rs.cochainComplex.d ((m : ℤ) + 1) ((m : ℤ) + 2)) ≫ G.map _
      rw [Rs.cochainComplex_d ((m : ℤ) + 1) ((m : ℤ) + 2) (m + 1) (m + 2) (by omega)
        (by omega)]
      simp only [← G.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- The homology in positive degree of `G` applied to the `ℤ`-indexed injective resolution is
the homology of `G` applied to the `ℕ`-indexed one. -/
def homologyCochainComplexIso {X : A} (Rs : InjectiveResolution X) (G : A ⥤ A') [G.Additive]
    (m : ℕ) :
    ((G.mapHomologicalComplex _).obj Rs.cochainComplex).homology ((m : ℤ) + 1) ≅
      ((G.mapHomologicalComplex _).obj Rs.cocomplex).homology (m + 1) :=
  ShortComplex.homologyMapIso (((G.mapHomologicalComplex _).obj Rs.cochainComplex).isoSc'
      (m : ℤ) ((m : ℤ) + 1) ((m : ℤ) + 2)
      (by rw [CochainComplex.prev]; ring) (by rw [CochainComplex.next]; ring)) ≪≫
    ShortComplex.homologyMapIso (scIsoCochainComplex Rs G m) ≪≫
    (ShortComplex.homologyMapIso (((G.mapHomologicalComplex _).obj Rs.cocomplex).isoSc'
      m (m + 1) (m + 2) (CochainComplex.prev_nat_succ m)
      (CochainComplex.next ℕ (m + 1)))).symm

/-- The homology in degree `0` of the `ℤ`-indexed injective resolution of `X` is `X`. -/
def homologyZeroCochainComplexIso {X : A} (Rs : InjectiveResolution X) :
    Rs.cochainComplex.homology 0 ≅ X :=
  (asIso (HomologicalComplex.homologyMap Rs.ι' 0)).symm ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X

end Resolutions

section ZeroDifferential

open ZeroObject

variable {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A]

/-- The complex with zero differentials, `F` in every degree `n ≥ 0` and `0` in every negative
degree. -/
def zeroDifferentialComplex (F : A) : CochainComplex A ℤ where
  X n := match n with
    | Int.ofNat _ => F
    | Int.negSucc _ => 0
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := zero_comp

@[simp]
lemma zeroDifferentialComplex_X_natCast (F : A) (n : ℕ) :
    (zeroDifferentialComplex F).X n = F := rfl

@[simp]
lemma zeroDifferentialComplex_d (F : A) (i j : ℤ) :
    (zeroDifferentialComplex F).d i j = 0 := rfl

lemma isZero_zeroDifferentialComplex_X (F : A) {n : ℤ} (hn : n < 0) :
    IsZero ((zeroDifferentialComplex F).X n) := by
  cases n with
  | ofNat m => exact absurd hn (by simp)
  | negSucc m => exact isZero_zero A

/-- The projection of `Z(F)` onto its term in degree `n`, as a morphism to the complex `F`
concentrated in degree `n`. -/
def zeroDifferentialComplexπ (F : A) (n : ℕ) :
    zeroDifferentialComplex F ⟶ (CochainComplex.singleFunctor A (n : ℤ)).obj F :=
  HomologicalComplex.mkHomToSingle (𝟙 F) (fun _ _ => zero_comp)

lemma zeroDifferentialComplexπ_f (F : A) (n : ℕ) :
    (zeroDifferentialComplexπ F n).f n =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (n : ℤ) F).inv :=
  (HomologicalComplex.mkHomToSingle_f _ _).trans (Category.id_comp _)

end ZeroDifferential

section ZeroDifferentialDerived

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

/-- The projection `Z(F) ⟶ F[0]⟦-n⟧` in the derived category: the image of the projection of
`Z(F)` onto its term in degree `n`, identified with `F[0]⟦-n⟧`. -/
def zeroDifferentialComplexToSingle (F : A) (n : ℕ) :
    DerivedCategory.Q.obj (zeroDifferentialComplex F) ⟶
      ((DerivedCategory.singleFunctor A 0).obj F)⟦-(n : ℤ)⟧ :=
  DerivedCategory.Q.map (zeroDifferentialComplexπ F n) ≫
    ((DerivedCategory.singleFunctorIsoCompQ A n).app F).inv ≫
      ((DerivedCategory.singleFunctors A).shiftIso (-(n : ℤ)) n 0 (by omega)).inv.app F

/-- The morphism `Z(F) ⟶ ∏_n F[0]⟦-n⟧` in the derived category whose `n`-th component is
`zeroDifferentialComplexToSingle F n`. -/
def zeroDifferentialComplexToPi [HasProductsOfShape ℕ (DerivedCategory A)] (F : A) :
    DerivedCategory.Q.obj (zeroDifferentialComplex F) ⟶
      ∏ᶜ fun n : ℕ => ((DerivedCategory.singleFunctor A 0).obj F)⟦-(n : ℤ)⟧ :=
  Pi.lift (zeroDifferentialComplexToSingle F)

@[reassoc (attr := simp)]
lemma zeroDifferentialComplexToPi_π [HasProductsOfShape ℕ (DerivedCategory A)] (F : A)
    (n : ℕ) :
    zeroDifferentialComplexToPi F ≫ Pi.π _ n = zeroDifferentialComplexToSingle F n :=
  Pi.lift_comp_π _ _

/-- The projection of `Z(F)` onto its term in degree `n` is an isomorphism on cohomology in
degree `n`. -/
instance quasiIsoAt_zeroDifferentialComplexπ (F : A) (n : ℕ) :
    QuasiIsoAt (zeroDifferentialComplexπ F n) n := by
  rw [quasiIsoAt_iff' _ ((n : ℤ) - 1) n ((n : ℤ) + 1) (by simp) (by simp),
    ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
  refine ⟨(ShortComplex.exact_iff_mono _ rfl).2 ?_, ?_⟩
  · change Mono ((zeroDifferentialComplexπ F n).f n)
    rw [zeroDifferentialComplexπ_f]
    exact SplitMono.mono ⟨(HomologicalComplex.singleObjXSelf _ _ F).hom, by simp⟩
  · change Epi ((zeroDifferentialComplexπ F n).f n)
    rw [zeroDifferentialComplexπ_f]
    exact SplitEpi.epi ⟨(HomologicalComplex.singleObjXSelf _ _ F).hom, by simp⟩

instance isIso_homologyFunctor_map_zeroDifferentialComplexToSingle (F : A) (n : ℕ) :
    IsIso ((DerivedCategory.homologyFunctor A n).map (zeroDifferentialComplexToSingle F n)) := by
  have : IsIso ((DerivedCategory.homologyFunctor A n).map
      (DerivedCategory.Q.map (zeroDifferentialComplexπ F n))) :=
    (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors A n) _).2
      (by
        change IsIso (HomologicalComplex.homologyMap (zeroDifferentialComplexπ F n) n)
        infer_instance)
  rw [zeroDifferentialComplexToSingle, Functor.map_comp]
  infer_instance

end ZeroDifferentialDerived

section Sheaves

variable {C : Type u} [Category.{u'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- Sheafification of presheaves of modules is left adjoint to the forgetful functor from
sheaves of modules to presheaves of modules. -/
def sheafificationForgetAdjunction :
    PresheafOfModules.sheafification.{v} (𝟙 R.obj) ⊣ SheafOfModules.forget.{v} R :=
  PresheafOfModules.sheafificationAdjunction.{v} (𝟙 R.obj)

instance isIso_sheafificationForgetAdjunction_counit :
    IsIso (sheafificationForgetAdjunction (R := R)).counit :=
  inferInstanceAs (IsIso (PresheafOfModules.sheafificationAdjunction.{v} (𝟙 R.obj)).counit)

/-- The `j`-th cohomology sheaf of a complex of sheaves of modules is the sheafification of the
`j`-th cohomology presheaf of the underlying complex of presheaves of modules. -/
def sheafificationHomologyIso (j : ℤ) :
    (SheafOfModules.forget.{v} R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j ⋙
          PresheafOfModules.sheafification.{v} (𝟙 R.obj) ≅
      HomologicalComplex.homologyFunctor (SheafOfModules.{v} R) (ComplexShape.up ℤ) j :=
  Functor.isoWhiskerLeft _ (Stacks.Homology.exactHomologyIso _ j).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (asIso (sheafificationForgetAdjunction (R := R)).counit) _ ≪≫
        Functor.mapHomologicalComplexIdIso _ _) _ ≪≫
    Functor.leftUnitor _

omit [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}] in
/-- Products of modules over a ring exist at any index type small with respect to the universe
of the modules. -/
instance hasLimitsOfShape_discrete_moduleCat (S : Type*) [Ring S] (I : Type*) [Small.{v} I] :
    HasLimitsOfShape (Discrete I) (ModuleCat.{v} S) :=
  ModuleCat.hasLimitsOfShape

omit [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}] in
/-- Products of modules over a ring are exact, at any index type small with respect to the
universe of the modules; the universe of the ring is arbitrary. -/
theorem hasExactLimitsOfShape_discrete_moduleCat (S : Type*) [Ring S] (I : Type*)
    [Small.{v} I] : HasExactLimitsOfShape (Discrete I) (ModuleCat.{v} S) := by
  have : HasExactLimitsOfShape (Discrete I) AddCommGrpCat.{v} :=
    HasExactLimitsOfShape.of_domain_equivalence AddCommGrpCat.{v}
      (Discrete.equivalence (equivShrink.{v} I).symm)
  have : PreservesLimitsOfShape (Discrete I) (forget₂ (ModuleCat.{v} S) AddCommGrpCat.{v}) :=
    ⟨inferInstance⟩
  have : PreservesFiniteColimits (forget₂ (ModuleCat.{v} S) AddCommGrpCat.{v}) :=
    { preservesFiniteColimits := fun K _ _ =>
        ModuleCat.forget₂PreservesColimitsOfShape.{v} S K }
  have : ReflectsFiniteColimits (forget₂ (ModuleCat.{v} S) AddCommGrpCat.{v}) :=
    { reflects := fun K _ _ => ModuleCat.reflectsColimitsOfShape.{v} S K }
  exact HasExactLimitsOfShape.domain_of_functor (Discrete I)
    (forget₂ (ModuleCat.{v} S) AddCommGrpCat.{v})

/-- **Cohomology sheaves of a product of complexes.** Let `L_i` be a family of complexes of
sheaves of modules and `p` a predicate on the index type. Suppose that, on sections over every
object of a covering class `ℬ`, the `j`-th cohomology of the underlying complex of presheaves of
`L_i` vanishes when `p i` fails, and that for `p s` the `j`-th cohomology presheaf of `L_s` is
the underlying presheaf of a sheaf `G_s`. Then the `j`-th cohomology sheaf of the termwise
product `∏ L_i` is `∏_{p s} G_s`, through the cohomology of the projections. -/
theorem isIso_pi_lift_homologyMap {B : ObjectProperty C} (hB : J.HasEnoughObjects B)
    {I : Type*} [Small.{v} I] (L : I → CochainComplex (SheafOfModules.{v} R) ℤ) (p : I → Prop)
    (G : Subtype p → SheafOfModules.{v} R) (j : ℤ)
    (hzero : ∀ i, ¬ p i → ∀ ⦃U : C⦄, B U →
      IsZero ((PresheafOfModules.evaluation R.obj (op U)).obj
        ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).obj
          (((SheafOfModules.forget R).mapHomologicalComplex (ComplexShape.up ℤ)).obj (L i)))))
    (δ : ∀ s : Subtype p, (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).obj
      (((SheafOfModules.forget R).mapHomologicalComplex (ComplexShape.up ℤ)).obj (L s.1)) ≅
        (SheafOfModules.forget R).obj (G s))
    (e : ∀ s : Subtype p,
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).obj (L s.1) ≅ G s) :
    IsIso (Pi.lift fun s : Subtype p =>
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).map (Pi.π L s.1) ≫
        (e s).hom) := by
  classical
  let θ := sheafificationHomologyIso (R := R) j
  let ε : ∀ s : Subtype p,
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).obj (L s.1) ≅ G s := fun s =>
    (θ.app (L s.1)).symm ≪≫ (PresheafOfModules.sheafification.{v} (𝟙 R.obj)).mapIso (δ s) ≪≫
      asIso ((sheafificationForgetAdjunction (R := R)).counit.app (G s))
  let ψ : (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).obj (∏ᶜ L) ⟶ ∏ᶜ G :=
    Pi.lift fun s : Subtype p =>
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).map (Pi.π L s.1) ≫ (ε s).hom
  suffices hψ : IsIso ψ by
    have : (Pi.lift fun s : Subtype p =>
        (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).map (Pi.π L s.1) ≫
          (e s).hom) = ψ ≫ Limits.Pi.map fun s => (ε s).inv ≫ (e s).hom := by
      refine Pi.hom_ext _ _ fun s => ?_
      rw [Pi.lift_comp_π, Category.assoc, Limits.Pi.map_π]
      simp only [ψ, Pi.lift_comp_π_assoc, Category.assoc, Iso.hom_inv_id_assoc]
    rw [this]
    infer_instance
  let χ := (sheafificationForgetAdjunction (R := R)).homEquiv _ _ (θ.hom.app (∏ᶜ L) ≫ ψ)
  have hχ : (PresheafOfModules.sheafification.{v} (𝟙 R.obj)).map χ ≫
      (sheafificationForgetAdjunction (R := R)).counit.app _ = θ.hom.app (∏ᶜ L) ≫ ψ := by
    exact ((sheafificationForgetAdjunction (R := R)).homEquiv_counit (g := χ)).symm.trans
      (((sheafificationForgetAdjunction (R := R)).homEquiv _ _).symm_apply_apply _)
  have hcomp : ∀ s : Subtype p, χ ≫ (SheafOfModules.forget R).map (Pi.π G s) =
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).map
        (((SheafOfModules.forget R).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (Pi.π L s.1)) ≫ (δ s).hom := by
    intro s
    have h1 := θ.hom.naturality (Pi.π L s.1)
    simp only [Functor.comp_map] at h1
    have h2 : θ.hom.app (L s.1) ≫ (ε s).hom =
        ((sheafificationForgetAdjunction (R := R)).homEquiv _ _).symm (δ s).hom := by
      rw [Adjunction.homEquiv_counit]
      simp [ε]
    have h3 : (θ.hom.app (∏ᶜ L) ≫ ψ) ≫ Pi.π G s =
        (PresheafOfModules.sheafification.{v} (𝟙 R.obj)).map
          ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).map
            (((SheafOfModules.forget R).mapHomologicalComplex (ComplexShape.up ℤ)).map
              (Pi.π L s.1))) ≫
          ((sheafificationForgetAdjunction (R := R)).homEquiv _ _).symm (δ s).hom := by
      rw [← h2, reassoc_of% h1]
      simp [ψ]
    change (sheafificationForgetAdjunction (R := R)).homEquiv _ _ (θ.hom.app (∏ᶜ L) ≫ ψ) ≫ _ = _
    rw [← Adjunction.homEquiv_naturality_right, h3, Adjunction.homEquiv_naturality_left,
      Equiv.apply_symm_apply]
  have hU : ∀ ⦃U : C⦄, B U → IsIso ((PresheafOfModules.evaluation R.obj (op U)).map χ) := by
    intro U hU
    have := hasExactLimitsOfShape_discrete_moduleCat.{v} (R.obj.obj (op U)) I
    have h₃ := Stacks.DerivedProducts.preservesLimitsOfShape_homologyFunctor
      (A := ModuleCat.{v} (R.obj.obj (op U))) (I := I) j
    have : HasLimitsOfShape (Discrete I) (SheafOfModules.{v} R) :=
      SheafOfModules.hasLimitsOfShape (R := R) (Discrete I)
    have : HasLimitsOfShape (Discrete I) (PresheafOfModules.{v} R.obj) :=
      PresheafOfModules.hasLimitsOfShape R.obj (Discrete I)
    have : PreservesLimitsOfShape (Discrete I) (SheafOfModules.forget.{v} R) :=
      SheafOfModules.forgetPreservesLimitsOfShape (R := R) (Discrete I)
    have : PreservesLimitsOfShape (Discrete I) (PresheafOfModules.evaluation.{v} R.obj (op U)) :=
      inferInstance
    have h₁ : PreservesLimitsOfShape (Discrete I)
        ((SheafOfModules.forget R).mapHomologicalComplex (ComplexShape.up ℤ)) := inferInstance
    have h₂ : PreservesLimitsOfShape (Discrete I)
        ((PresheafOfModules.evaluation R.obj (op U)).mapHomologicalComplex
          (ComplexShape.up ℤ)) := inferInstance
    have h₄ : PreservesLimitsOfShape (Discrete I)
        ((SheafOfModules.forget R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (PresheafOfModules.evaluation R.obj (op U)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j) :=
      @comp_preservesLimitsOfShape _ _ _ _ _ _ _ _ _ _ h₁
        (@comp_preservesLimitsOfShape _ _ _ _ _ _ _ _ _ _ h₂ h₃)
    have : PreservesLimitsOfShape (Discrete I)
        ((SheafOfModules.forget R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j ⋙
            PresheafOfModules.evaluation R.obj (op U)) :=
      @preservesLimitsOfShape_of_natIso _ _ _ _ _ _ _ _
        (Functor.isoWhiskerLeft ((SheafOfModules.forget R).mapHomologicalComplex _)
          (Stacks.Homology.exactHomologyIso (PresheafOfModules.evaluation R.obj (op U)) j)) h₄
    have key : (PresheafOfModules.evaluation R.obj (op U)).map χ ≫
        piComparison (SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj (op U)) G =
          piComparison ((SheafOfModules.forget R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j ⋙
              PresheafOfModules.evaluation R.obj (op U)) L ≫
          Pi.lift (fun s : Subtype p => Pi.π _ s.1) ≫
            Limits.Pi.map (f := fun s : Subtype p =>
              ((SheafOfModules.forget R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
                HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j ⋙
                  PresheafOfModules.evaluation R.obj (op U)).obj (L s.1))
              (g := fun s => (SheafOfModules.forget R ⋙
                PresheafOfModules.evaluation R.obj (op U)).obj (G s))
              fun s => (PresheafOfModules.evaluation R.obj (op U)).map (δ s).hom := by
      refine Pi.hom_ext _ _ fun s => ?_
      rw [Category.assoc, piComparison_comp_π, Category.assoc, Category.assoc, Limits.Pi.map_π,
        Pi.lift_comp_π_assoc, piComparison_comp_π_assoc]
      refine ((PresheafOfModules.evaluation R.obj (op U)).map_comp _ _).symm.trans ?_
      rw [hcomp, Functor.map_comp]
      rfl
    have : IsIso (Pi.lift fun s : Subtype p => Pi.π (fun i =>
        ((SheafOfModules.forget R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j ⋙
            PresheafOfModules.evaluation R.obj (op U)).obj (L i)) s.1) :=
      isIso_pi_lift_π_of_isZero _ p (fun i hi => hzero i hi hU)
    have : IsIso ((PresheafOfModules.evaluation R.obj (op U)).map χ ≫
        piComparison (SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj (op U)) G) := by
      rw [key]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (piComparison (SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj (op U)) G)
  have : IsIso ((PresheafOfModules.sheafification.{v} (𝟙 R.obj)).map χ) :=
    PresheafOfModules.isIso_sheafification_map_of_isIso_evaluation hB χ hU
  have : IsIso (θ.hom.app (∏ᶜ L) ≫ ψ) := by
    rw [← hχ]
    infer_instance
  exact IsIso.of_isIso_comp_left (θ.hom.app (∏ᶜ L)) ψ

variable [IsGrothendieckAbelian.{t} (SheafOfModules.{v} R)]

/-- On an object `U` over which `X` is acyclic, the cohomology presheaf of a shifted injective
resolution of `X` vanishes at `U` away from the degree in which `X` sits. -/
theorem isZero_evaluation_homology_shift {X : SheafOfModules.{v} R} {U : C}
    (hX : ∀ q : ℕ, 0 < q →
      IsZero (((SheafOfModules.evaluation R (op U)).rightDerived q).obj X))
    (k j : ℤ) (hkj : k + j ≠ 0) :
    IsZero ((PresheafOfModules.evaluation R.obj (op U)).obj
      ((((SheafOfModules.forget R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((injectiveResolution X).cochainComplex⟦k⟧)).homology j)) := by
  have e : (PresheafOfModules.evaluation R.obj (op U)).obj
      ((((SheafOfModules.forget R).mapHomologicalComplex _).obj
        ((injectiveResolution X).cochainComplex⟦k⟧)).homology j) ≅
      (((SheafOfModules.evaluation R (op U)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (injectiveResolution X).cochainComplex).homology (k + j) :=
    ((Stacks.Homology.exactHomologyIso (PresheafOfModules.evaluation R.obj (op U)) j).app
        _).symm ≪≫
      (HomologicalComplex.homologyFunctor _ _ j).mapIso
        ((Functor.mapHomologicalComplexCompIso (Iso.refl _ : SheafOfModules.forget R ⋙
          PresheafOfModules.evaluation R.obj (op U) ≅ SheafOfModules.evaluation R (op U))
            _).app _ ≪≫
          ((SheafOfModules.evaluation R (op U)).mapCochainComplexShiftIso k).app
            (injectiveResolution X).cochainComplex) ≪≫
      (CochainComplex.ShiftSequence.shiftIso _ k j (k + j) rfl).app _
  refine IsZero.of_iso ?_ e
  rcases lt_or_gt_of_ne hkj with h | h
  · refine ShortComplex.isZero_homology_of_isZero_X₂ _ ?_
    exact (SheafOfModules.evaluation R (op U)).map_isZero
      ((injectiveResolution X).cochainComplex.isZero_of_isStrictlyGE 0 (k + j) h)
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, k + j = (m : ℤ) + 1 := ⟨(k + j - 1).toNat, by omega⟩
    rw [hm]
    refine IsZero.of_iso ?_
      (homologyCochainComplexIso (injectiveResolution X) (SheafOfModules.evaluation R (op U)) m)
    exact IsZero.of_iso (hX (m + 1) (by omega))
      ((injectiveResolution X).isoRightDerivedObj (SheafOfModules.evaluation R (op U)) (m + 1)).symm

/-- The cohomology presheaf of a shifted injective resolution of `X`, in the degree in which
`X` sits, is the underlying presheaf of `X`. -/
def homologyShiftCochainComplexIso (X : SheafOfModules.{v} R) (k j : ℤ) (hkj : k + j = 0) :
    (((SheafOfModules.forget R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((injectiveResolution X).cochainComplex⟦k⟧)).homology j ≅
      (SheafOfModules.forget R).obj X :=
  haveI hf : ((injectiveResolution X).cochainComplex.sc 0).f = 0 :=
    ((injectiveResolution X).cochainComplex.isZero_of_isStrictlyGE 0
      ((ComplexShape.up ℤ).prev 0) (by simp)).eq_of_src _ _
  haveI : (SheafOfModules.forget R).PreservesLeftHomologyOf
      ((injectiveResolution X).cochainComplex.sc 0) :=
    Functor.preservesLeftHomology_of_zero_f _ _ hf
  (HomologicalComplex.homologyFunctor _ _ j).mapIso
      (((SheafOfModules.forget R).mapCochainComplexShiftIso k).app _) ≪≫
    (CochainComplex.ShiftSequence.shiftIso _ k j 0 hkj).app _ ≪≫
    ((injectiveResolution X).cochainComplex.sc 0).mapHomologyIso (SheafOfModules.forget R) ≪≫
    (SheafOfModules.forget R).mapIso (homologyZeroCochainComplexIso _)

variable [HasDerivedCategory.{d} (SheafOfModules.{v} R)]

/-- The morphism `H^j(∏_i F_i[0]⟦k_i⟧) ⟶ ∏_{k_i = -j} F_i` induced by the cohomology of the
projections, followed by the canonical isomorphisms `homologyShiftSingleIso`. -/
def homologyPiShiftSingleHom {I : Type} [Small.{v} I] (F : I → SheafOfModules.{v} R)
    (k : I → ℤ) (j : ℤ) :
    (DerivedCategory.homologyFunctor _ j).obj
        (∏ᶜ fun i => ((DerivedCategory.singleFunctor _ 0).obj (F i))⟦k i⟧) ⟶
      ∏ᶜ fun i : {i // k i = -j} => F i.1 :=
  Pi.lift fun s : {i // k i = -j} =>
    (DerivedCategory.homologyFunctor _ j).map
      (Pi.π (fun i => ((DerivedCategory.singleFunctor _ 0).obj (F i))⟦k i⟧) s.1) ≫
    (homologyShiftSingleIso (F s.1) (k s.1) j (by have := s.2; omega)).hom

/-- The morphism `homologyPiShiftSingleHom` is an isomorphism when every `F_i` is acyclic on the
objects of a covering class. -/
theorem isIso_homologyPiShiftSingleHom {B : ObjectProperty C} (hB : J.HasEnoughObjects B)
    {I : Type} [Small.{v} I] (F : I → SheafOfModules.{v} R)
    (hF : ∀ i ⦃U : C⦄, B U → ∀ q : ℕ, 0 < q →
      IsZero (((SheafOfModules.evaluation R (op U)).rightDerived q).obj (F i)))
    (k : I → ℤ) (j : ℤ) : IsIso (homologyPiShiftSingleHom F k j) := by
  classical
  let L := fun i => (injectiveResolution (F i)).cochainComplex⟦k i⟧
  let H := DerivedCategory.homologyFunctor (SheafOfModules.{v} R) j
  let eS : ∀ s : {i // k i = -j}, H.obj (((DerivedCategory.singleFunctor _ 0).obj
      (F s.1))⟦k s.1⟧) ≅ F s.1 := fun s =>
    homologyShiftSingleIso (F s.1) (k s.1) j (by have := s.2; omega)
  let e'' : ∀ s : {i // k i = -j},
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).obj (L s.1) ≅ F s.1 := fun s =>
    (DerivedCategory.homologyFunctorFactors _ j).symm.app (L s.1) ≪≫
      H.mapIso (shiftResolutionIso (F s.1) (k s.1)) ≪≫ eS s
  have hA := isIso_pi_lift_homologyMap hB L (fun i => k i = -j) (fun s => F s.1) j
    (fun i hi U hU => isZero_evaluation_homology_shift (hF i hU) (k i) j (by omega))
    (fun s => homologyShiftCochainComplexIso (F s.1) (k s.1) j (by have := s.2; omega)) e''
  have heq : (Pi.lift fun s : {i // k i = -j} =>
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).map (Pi.π L s.1) ≫
        (e'' s).hom) =
        (DerivedCategory.homologyFunctorFactors _ j).inv.app (∏ᶜ L) ≫
          H.map (piShiftSingleIso F k).hom ≫
            (Pi.lift fun s : {i // k i = -j} =>
              H.map (Pi.π (fun i => ((DerivedCategory.singleFunctor _ 0).obj (F i))⟦k i⟧)
                s.1) ≫ (eS s).hom) := by
    refine Pi.hom_ext _ _ fun s => ?_
    have hn := (DerivedCategory.homologyFunctorFactors (SheafOfModules.{v} R) j).inv.naturality
      (Pi.π L s.1)
    simp only [Pi.lift_comp_π, Category.assoc]
    rw [← H.map_comp_assoc, piShiftSingleIso_hom_π, H.map_comp_assoc]
    simp only [e'', Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom]
    simp only [← Category.assoc]
    congr 2
  rw [heq] at hA
  have := IsIso.of_isIso_comp_left
    ((DerivedCategory.homologyFunctorFactors _ j).inv.app (∏ᶜ L))
    (H.map (piShiftSingleIso F k).hom ≫
      (Pi.lift fun s : {i // k i = -j} =>
        H.map (Pi.π (fun i => ((DerivedCategory.singleFunctor _ 0).obj (F i))⟦k i⟧)
          s.1) ≫ (eS s).hom))
  exact IsIso.of_isIso_comp_left (H.map (piShiftSingleIso F k).hom)
    (Pi.lift fun s : {i // k i = -j} =>
        H.map (Pi.π (fun i => ((DerivedCategory.singleFunctor _ 0).obj (F i))⟦k i⟧)
          s.1) ≫ (eS s).hom)

/-- **Cohomology sheaves of a product of shifted acyclic sheaves.** If every `F_i` is acyclic on
the objects of a covering class `ℬ`, then the `j`-th cohomology sheaf of the product
`∏_i F_i[0]⟦k_i⟧` in the derived category is the product of the `F_i` with `k_i = -j`. It is
the morphism `homologyPiShiftSingleHom` induced by the cohomology of the projections, followed
by the canonical isomorphisms `homologyShiftSingleIso`; see `homologyPiShiftSingleIso_hom_π`. -/
def homologyPiShiftSingleIso {B : ObjectProperty C} (hB : J.HasEnoughObjects B)
    {I : Type} [Small.{v} I] (F : I → SheafOfModules.{v} R)
    (hF : ∀ i ⦃U : C⦄, B U → ∀ q : ℕ, 0 < q →
      IsZero (((SheafOfModules.evaluation R (op U)).rightDerived q).obj (F i)))
    (k : I → ℤ) (j : ℤ) :
    (DerivedCategory.homologyFunctor _ j).obj
        (∏ᶜ fun i => ((DerivedCategory.singleFunctor _ 0).obj (F i))⟦k i⟧) ≅
      ∏ᶜ fun i : {i // k i = -j} => F i.1 :=
  haveI := isIso_homologyPiShiftSingleHom hB F hF k j
  asIso (homologyPiShiftSingleHom F k j)

/-- **Compatibility with the projections.** The isomorphism `homologyPiShiftSingleIso`,
followed by the projection onto the factor `i₀` with `k i₀ = -j`, is the cohomology of the
projection of the product onto `F_{i₀}[0]⟦k i₀⟧`, followed by the canonical isomorphism
`H^j(F_{i₀}[0]⟦-j⟧) ≅ F_{i₀}`. -/
@[reassoc]
theorem homologyPiShiftSingleIso_hom_π {B : ObjectProperty C} (hB : J.HasEnoughObjects B)
    {I : Type} [Small.{v} I] (F : I → SheafOfModules.{v} R)
    (hF : ∀ i ⦃U : C⦄, B U → ∀ q : ℕ, 0 < q →
      IsZero (((SheafOfModules.evaluation R (op U)).rightDerived q).obj (F i)))
    (k : I → ℤ) (j : ℤ) (i₀ : I) (h : k i₀ = -j) :
    (homologyPiShiftSingleIso hB F hF k j).hom ≫
        Pi.π (fun i : {i // k i = -j} => F i.1) ⟨i₀, h⟩ =
      (DerivedCategory.homologyFunctor _ j).map
          (Pi.π (fun i => ((DerivedCategory.singleFunctor _ 0).obj (F i))⟦k i⟧) i₀) ≫
        (homologyShiftSingleIso (F i₀) (k i₀) j (by omega)).hom := by
  simp [homologyPiShiftSingleIso, homologyPiShiftSingleHom]

/-- **A complex with zero differentials of an acyclic sheaf is the product of its shifted
terms.** If `F` is acyclic on the objects of a covering class `ℬ`, the morphism
`Z(F) ⟶ ∏_n F[0]⟦-n⟧` of the derived category induced by the projections of `Z(F)` onto its
terms is an isomorphism. -/
theorem isIso_zeroDifferentialComplexToPi {B : ObjectProperty C} (hB : J.HasEnoughObjects B)
    (F : SheafOfModules.{v} R)
    (hF : ∀ ⦃U : C⦄, B U → ∀ q : ℕ, 0 < q →
      IsZero (((SheafOfModules.evaluation R (op U)).rightDerived q).obj F)) :
    IsIso (zeroDifferentialComplexToPi F) := by
  rw [DerivedCategory.isIso_iff]
  intro j
  suffices IsIso ((DerivedCategory.homologyFunctor _ j).map (zeroDifferentialComplexToPi F) ≫
      (homologyPiShiftSingleIso hB (fun _ : ℕ => F) (fun _ => hF)
        (fun n : ℕ => -(n : ℤ)) j).hom) from
    IsIso.of_isIso_comp_right _ (homologyPiShiftSingleIso hB (fun _ : ℕ => F) (fun _ => hF)
        (fun n : ℕ => -(n : ℤ)) j).hom
  have hc : (DerivedCategory.homologyFunctor _ j).map (zeroDifferentialComplexToPi F) ≫
      (homologyPiShiftSingleIso hB (fun _ : ℕ => F) (fun _ => hF)
        (fun n : ℕ => -(n : ℤ)) j).hom =
      Pi.lift fun s : {n : ℕ // -(n : ℤ) = -j} =>
        (DerivedCategory.homologyFunctor _ j).map (zeroDifferentialComplexToSingle F s.1) ≫
          (homologyShiftSingleIso F (-(s.1 : ℤ)) j (by have := s.2; omega)).hom := by
    refine Pi.hom_ext _ _ fun s => ?_
    obtain ⟨n, hn⟩ := s
    rw [Category.assoc, homologyPiShiftSingleIso_hom_π, Pi.lift_comp_π, ← Functor.map_comp_assoc,
      zeroDifferentialComplexToPi_π]
  rw [hc]
  rcases lt_or_ge j 0 with hj | hj
  · have : IsEmpty {n : ℕ // -(n : ℤ) = -j} := ⟨fun s => by have := s.2; omega⟩
    refine isIso_of_source_target_iso_zero _ (IsZero.isoZero ?_)
      (IsZero.isoZero (isZero_pi_of_isEmpty _))
    exact IsZero.of_iso (ShortComplex.isZero_homology_of_isZero_X₂
      ((zeroDifferentialComplex F).sc j) (isZero_zeroDifferentialComplex_X F hj))
        ((DerivedCategory.homologyFunctorFactors _ j).app _)
  · obtain ⟨n₀, rfl⟩ : ∃ n₀ : ℕ, j = n₀ := ⟨j.toNat, by omega⟩
    have : Subsingleton {n : ℕ // -(n : ℤ) = -(n₀ : ℤ)} :=
      ⟨fun a b => Subtype.ext (by have := a.2; have := b.2; omega)⟩
    exact isIso_pi_lift_of_subsingleton _ _ ⟨n₀, rfl⟩

end Sheaves

end Stacks.Cohomology.CohomologySheafOfProducts

end
