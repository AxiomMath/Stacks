module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteBaseChangeSiteTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.CategoryTheory.Adjunction.MatesChangeOfCategoriesApp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedSectionsAlongAFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.RingTheory.FinitePresentation.ModuleDescent

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ForgetEtaleModuleStructure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransferUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeHorizontalMate
public import StacksFrontier.CategoryTheory.Adjunction.MatesChangeOfCategories
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareCochain
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImageUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Exactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ExactnessUnconditional
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompIsoOnHomotopyCategory
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting

/-!
# The base change map for étale sheaves of `Λ`-modules, and its agreement with the abelian one

Let `Λ` be a ring and let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes. This file constructs the base change map
`g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}` of [Stacks, Tag 0A2A] on the unbounded derived categories
`D(-_étale, Λ)` of sheaves of `Λ`-modules, on which the derived lower shriek
`Stacks.EtaleCohomology.derivedLowerShriekUnbounded` is built, and shows that forgetting the
module structure carries it to the base change map
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange` of abelian sheaves. In particular it is
invertible wherever the abelian one is, so every base change theorem proved for abelian sheaves
(proper base change, [Stacks, Tag 0DDE]; open base change) holds for sheaves of `Λ`-modules.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleInverseImageForget` and
  `Stacks.EtaleCohomology.etaleModuleExtensionByZeroForget`: the comparisons of `f^{-1}` and of
  `j_!` with forgetting the module structure, both invertible.
* `Stacks.EtaleCohomology.etaleModuleDerivedInverseImageForgetIso` and
  `Stacks.EtaleCohomology.etaleModuleExtensionByZeroMapDerivedCategoryForgetIso`: the same on
  unbounded derived categories.
* `Stacks.EtaleCohomology.etaleModuleBaseChangeGeneral`: the underived base change map
  `g^{-1} f_* ⟶ f'_* (g')^{-1}` of sheaves of `Λ`-modules.
* `Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeGeneral`: the derived base change map.

## Main results

* `Stacks.EtaleCohomology.etaleModuleBaseChange_forget`: forgetting the module structure carries
  the underived base change map to `Stacks.EtaleCohomology.etaleAbelianBaseChange`.
* `Stacks.EtaleCohomology.etaleModuleDerivedBaseChange_fac_general`: the defining property of the
  derived base change map on complexes.
* `Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChange_app_of_isIso`: **the base change map
  for sheaves of `Λ`-modules is invertible at `K` as soon as the abelian base change map is
  invertible at the underlying object of `K`.**

## Implementation notes

The derived base change map is not transported from the abelian one: both are instances of a
construction generic in the coefficients. The underived map is the mate, along the two
inverse-image/direct-image adjunctions of the horizontal arrows, of the comparison of composite
direct images, exactly as `Stacks.EtaleCohomology.etaleAbelianBaseChange` is
(`Stacks.EtaleCohomology.etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso`); the
derived map is `Stacks.Homology.DerivedSquare.cochainDerivedSquare` of it, the descent of the
degreewise map along the universal property of `Rf_* ⋙ g^{-1}` formed along the localization of
cochain complexes, which is where `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded`
lives.

The underived agreement is the calculus of mates: the comparison of `f^{-1}` with forgetting is
defined as the mate of the identity comparison of `f_*` with forgetting, so
`Stacks.CategoryTheory.mateEquiv_symm_hComp_eq_app` applies, and its hypothesis is that the
comparisons of composite direct images commute with forgetting, which holds on sections. That
comparison is invertible because the mate along the explicit construction of the inverse image is
(`Stacks.EtaleCohomology.isIso_coefficientPullbackTwoSquare`) and the inverse mate does not
depend on the choice of left adjoints
(`Stacks.CategoryTheory.isIso_mateEquiv_symm_of_leftAdjointUniq_general`).

The derived agreement is checked at a K-injective complex `I`, where the units of `Rf_*` are
invertible both for `I` and for its underlying complex
(`Stacks.EtaleCohomology.isIso_etaleAbelianDerivedDirectImageUnit_app_forget_of_isKInjective`);
the two defining factorizations are then compared through
`Stacks.EtaleCohomology.etaleModuleDerivedDirectImageForgetIso_hom_fac`. The comparison is
stated for variable transformations (`Stacks.EtaleCohomology.isIso_forget_comparison_of_fac`):
the kernel must never compare the base change maps with their definitions, which unfold to
sheafifications of Kan extensions.

## References

* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.TwoSquare
open AlgebraicGeometry.SmallEtale (ts_vComp_app ts_whiskerLeft_app ts_whiskerRight_app)
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.Limits.comp_preservesFiniteLimits
    CategoryTheory.Limits.comp_preservesFiniteColimits

universe u r

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.CategoryTheory

section LeftAdjointUniq

variable {C : Type*} {D : Type*} {E : Type*} {F : Type*} [Category* C] [Category* D]
  [Category* E] [Category* F] {L₁ L₁' : C ⥤ D} {R₁ : D ⥤ C} {L₂ L₂' : E ⥤ F} {R₂ : F ⥤ E}
  {G : C ⥤ E} {H : D ⥤ F}

/-- **The inverse mate does not depend on the choice of left adjoints**, up to the canonical
comparisons of left adjoints. -/
theorem mateEquiv_symm_app_eq_leftAdjointUniq (adj₁ : L₁ ⊣ R₁) (adj₁' : L₁' ⊣ R₁)
    (adj₂ : L₂ ⊣ R₂) (adj₂' : L₂' ⊣ R₂) (β : TwoSquare R₁ H G R₂) (c : C) :
    ((mateEquiv adj₁ adj₂).symm β).app c =
      (adj₂.leftAdjointUniq adj₂').hom.app (G.obj c) ≫
        ((mateEquiv adj₁' adj₂').symm β).app c ≫
          H.map ((adj₁'.leftAdjointUniq adj₁).hom.app c) := by
  refine (adj₂.homEquiv _ _).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine (unit_mateEquiv_symm adj₁ adj₂ β c).symm.trans ?_
  rw [R₂.map_comp, R₂.map_comp, ← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app,
    ← Category.assoc]
  refine Eq.trans ?_ (congrArg (· ≫ R₂.map (H.map ((adj₁'.leftAdjointUniq adj₁).hom.app c)))
    (unit_mateEquiv_symm adj₁' adj₂' β c))
  have hn := β.naturality ((adj₁'.leftAdjointUniq adj₁).hom.app c)
  dsimp at hn ⊢
  rw [Category.assoc, ← hn, ← Category.assoc, ← G.map_comp,
    Adjunction.unit_leftAdjointUniq_hom_app]

/-- The inverse mate along one choice of left adjoints is invertible as soon as it is along
another. -/
theorem isIso_mateEquiv_symm_of_leftAdjointUniq_general (adj₁ : L₁ ⊣ R₁) (adj₁' : L₁' ⊣ R₁)
    (adj₂ : L₂ ⊣ R₂) (adj₂' : L₂' ⊣ R₂) (β : TwoSquare R₁ H G R₂)
    [IsIso ((mateEquiv adj₁' adj₂').symm β)] :
    IsIso ((mateEquiv adj₁ adj₂).symm β) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro c
  rw [mateEquiv_symm_app_eq_leftAdjointUniq adj₁ adj₁' adj₂ adj₂' β c]
  infer_instance

end LeftAdjointUniq

section HorizontalVerticalMate

variable {A : Type*} {B : Type*} {C : Type*} {D : Type*} [Category* A] [Category* B]
  [Category* C] [Category* D] {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B} {LP : A ⥤ D} {RP : D ⥤ A}

/-- **The two base change maps of a square of four adjunctions through a common diagonal
agree.** Let `L₁ ⊣ R₁`, `L₂ ⊣ R₂` (vertical) and `F₁ ⊣ U₁`, `F₂ ⊣ U₂` (horizontal) be the four
sides of a square, and `LP ⊣ RP` an adjunction along its diagonal, with the two composite right
adjoints identified with `RP` by `e₁ : U₂ ⋙ R₁ ≅ RP` and `e₂ : R₂ ⋙ U₁ ≅ RP`. The base change
map `R₁ ⋙ F₁ ⟶ F₂ ⋙ R₂` taken as the inverse mate, along the horizontal adjunctions, of the
comparison `U₂ ⋙ R₁ ≅ RP ≅ R₂ ⋙ U₁` of composite right adjoints equals the one taken as the mate,
along the vertical adjunctions, of the comparison `F₁ ⋙ L₂ ≅ LP ≅ L₁ ⋙ F₂` of the composite left
adjoints attached to `e₂` and `e₁` by `CategoryTheory.Adjunction.leftAdjointCompIso`.

Iterating the two mate operations gives the conjugate (`iterated_mateEquiv_conjugateEquiv`), the
conjugate of a composite splits at `adjP` (`conjugateEquiv_comp`), and the two factors are
conjugate to `e₁` and `e₂`. -/
theorem mateEquiv_symm_comp_eq_mateEquiv_leftAdjointCompIso (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₃ : F₁ ⊣ U₁) (adj₄ : F₂ ⊣ U₂) (adjP : LP ⊣ RP) (e₁ : U₂ ⋙ R₁ ≅ RP)
    (e₂ : R₂ ⋙ U₁ ≅ RP) :
    (mateEquiv adj₄ adj₃).symm (TwoSquare.mk _ _ _ _ (e₁.hom ≫ e₂.inv)) =
      mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _
        ((Adjunction.leftAdjointCompIso adj₃ adj₂ adjP e₂).hom ≫
          (Adjunction.leftAdjointCompIso adj₁ adj₄ adjP e₁).inv)) := by
  refine (Equiv.symm_apply_eq _).2 ?_
  refine Eq.trans ?_ (iterated_mateEquiv_conjugateEquiv adj₁ adj₂ adj₃ adj₄ _).symm
  rw [← conjugateEquiv_comp (adj₁.comp adj₄) adjP (adj₃.comp adj₂),
    Adjunction.conjugateEquiv_leftAdjointCompIso_inv,
    Stacks.Cohomology.BaseChange.conjugateEquiv_leftAdjointCompIso_hom]

end HorizontalVerticalMate

section IsIsoComp

variable {C : Type*} [Category* C]

/-- Dropping an invertible last factor of a fivefold composite. -/
theorem isIso_comp₄_comp_iff {P Q₀ R S T T' : C} (a : P ⟶ Q₀) (b : Q₀ ⟶ R) (c : R ⟶ S)
    (d : S ⟶ T) (w : T ⟶ T') [IsIso w] :
    IsIso (a ≫ b ≫ c ≫ d ≫ w) ↔ IsIso (a ≫ b ≫ c ≫ d) := by
  simp only [← Category.assoc]
  exact isIso_comp_right_iff _ w

/-- Replacing the first two factors of a composite by two others with the same composite. -/
theorem isIso_comp_comp_iff_of_eq {P Q₀ Q₁ R S : C} {a : P ⟶ Q₀} {b : Q₀ ⟶ R} {a' : P ⟶ Q₁}
    {b' : Q₁ ⟶ R} (e : a ≫ b = a' ≫ b') (r : R ⟶ S) :
    IsIso (a ≫ b ≫ r) ↔ IsIso (a' ≫ b' ≫ r) := by
  rw [← Category.assoc, e, Category.assoc]

/-- Moving the two isomorphisms of a commutative square to the other side. -/
theorem comp_inv_eq_inv_comp_of_iso {P Q₀ R T : C} (t : P ≅ Q₀) (k : T ≅ R) {x : Q₀ ⟶ R}
    {y : P ⟶ T} (e : t.hom ≫ x = y ≫ k.hom) : x ≫ k.inv = t.inv ≫ y := by
  rw [Iso.eq_inv_comp, ← Category.assoc, e, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Invertibility of a composite `a ≫ u` through a naturality square for `u` and a square for `a`
with invertible horizontal sides. -/
theorem isIso_comp_of_squares {P Q₀ R R' Q' S : C} {a : P ⟶ Q₀} {u : Q₀ ⟶ R} {r : R ⟶ R'}
    [IsIso r] {p : Q₀ ⟶ Q'} {u' : Q' ⟶ R'} {s : P ⟶ S} [IsIso s] {b : S ⟶ Q'}
    (hnat : u ≫ r = p ≫ u') (hsq : a ≫ p = s ≫ b) (h : IsIso (b ≫ u')) : IsIso (a ≫ u) := by
  have e : a ≫ u = s ≫ (b ≫ u') ≫ inv r := by
    rw [← Category.assoc, ← Category.assoc, ← hsq, Category.assoc a p u', ← hnat]
    simp
  rw [e]
  infer_instance

/-- With `a`, `b`, `z` invertible, a factorization `a ≫ b ≫ c = x ≫ y ≫ z` identifies the
invertibility of `c` with that of `x ≫ y`. -/
private theorem isIso_iff_of_fac {P Q₀ R S Q' R' : C} (a : P ⟶ Q₀) (b : Q₀ ⟶ R) (c : R ⟶ S)
    (x : P ⟶ Q') (y : Q' ⟶ R') {z : R' ⟶ S} (e : a ≫ b ≫ c = x ≫ y ≫ z) [IsIso a] [IsIso b]
    [IsIso z] : IsIso c ↔ IsIso (x ≫ y) := by
  refine ⟨fun hc => ?_, fun hxy => ?_⟩
  · have : IsIso ((x ≫ y) ≫ z) := by rw [Category.assoc, ← e]; infer_instance
    exact IsIso.of_isIso_comp_right _ z
  · have : IsIso (a ≫ b ≫ c) := by rw [e, ← Category.assoc]; infer_instance
    rw [← Category.assoc] at this
    exact (isIso_comp_left_iff _ _).mp this

/-- From a factorization `a ≫ b ≫ c = x ≫ y ≫ z` with `a`, `b`, `z` invertible, invertibility of
`c` gives invertibility of `x ≫ y`. -/
theorem isIso_of_fac_of_isIso {P Q₀ R S Q' R' : C} (a : P ⟶ Q₀) (b : Q₀ ⟶ R) (c : R ⟶ S)
    (x : P ⟶ Q') (y : Q' ⟶ R') {z : R' ⟶ S} (e : a ≫ b ≫ c = x ≫ y ≫ z) [IsIso a] [IsIso b]
    [IsIso z] (hc : IsIso c) : IsIso (x ≫ y) :=
  (isIso_iff_of_fac a b c x y e).mp hc

end IsIsoComp

end Stacks.CategoryTheory

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

section InverseImage

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Sheafification on the small étale site commutes with forgetting the module structure. -/
instance preservesSheafification_smallEtale_forget₂_moduleCat (X : Scheme.{u}) :
    X.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}) :=
  have : HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{max (u + 1) r} Λ) :=
    ModuleCat.hasLimitsOfSize.{u + 1, u + 1, max (u + 1) r, r}
  have : PreservesFilteredColimits (CategoryTheory.forget (ModuleCat.{max (u + 1) r} Λ)) :=
    preservesFilteredColimits_forget_moduleCat.{max (u + 1) r} Λ
  have : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (CategoryTheory.forget (ModuleCat.{max (u + 1) r} Λ)) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) r, max (u + 1) r, u + 1, u + 1} _
  have : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (CategoryTheory.forget AddCommGrpCat.{max (u + 1) r}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) r, max (u + 1) r, u + 1, u + 1} _
  GrothendieckTopology.instPreservesSheafification X.smallEtaleTopology
    (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r})

/-- Direct image commutes with forgetting the module structure on the nose. -/
def etaleModuleDirectImageForget :
    TwoSquare (etaleModuleDirectImage.{u, r} Λ f)
      (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X)
      (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y)
        (etaleAbelianDirectImage.{u, r} f) :=
  TwoSquare.mk _ _ _ _ (𝟙 _)

/-- The component of `Stacks.EtaleCohomology.etaleModuleDirectImageForget` at a sheaf of
`Λ`-modules is the identity. -/
@[simp]
theorem etaleModuleDirectImageForget_app (c : EtaleModules.{u, r} Λ X) :
    (etaleModuleDirectImageForget.{u, r} Λ f).app c = 𝟙 _ :=
  rfl

/-- The image under any functor `G` of a component of
`Stacks.EtaleCohomology.etaleModuleDirectImageForget`, followed by a morphism `y`, is `y`. -/
theorem map_etaleModuleDirectImageForget_app_comp {D : Type*} [Category* D]
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) r} ⥤ D)
    (c : EtaleModules.{u, r} Λ X) {T : D}
    (y : G.obj ((etaleAbelianDirectImage.{u, r} f).obj
      ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).obj c)) ⟶
      T) :
    G.map ((etaleModuleDirectImageForget.{u, r} Λ f).app c) ≫ y = y := by
  change G.map (𝟙 _) ≫ y = y
  rw [G.map_id, Category.id_comp]

/-- The identity square of `Stacks.EtaleCohomology.etaleModuleDirectImageForget`, read in the
other direction. -/
def etaleModuleDirectImageForgetInv :
    _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X ⋙
      etaleAbelianDirectImage.{u, r} f ⟶
      etaleModuleDirectImage.{u, r} Λ f ⋙
        _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y :=
  𝟙 _

/-- The component of `Stacks.EtaleCohomology.etaleModuleDirectImageForgetInv` at a sheaf of
`Λ`-modules is the identity. -/
@[simp]
theorem etaleModuleDirectImageForgetInv_app (c : EtaleModules.{u, r} Λ X) :
    (etaleModuleDirectImageForgetInv.{u, r} Λ f).app c = 𝟙 _ :=
  rfl

/-- A morphism `x` followed by a component of
`Stacks.EtaleCohomology.etaleModuleDirectImageForgetInv` is `x`. -/
theorem comp_etaleModuleDirectImageForgetInv_app (c : EtaleModules.{u, r} Λ X)
    {T : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}}
    (x : T ⟶ (etaleAbelianDirectImage.{u, r} f).obj
      ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).obj c)) :
    x ≫ (etaleModuleDirectImageForgetInv.{u, r} Λ f).app c = x :=
  Category.comp_id x

/-- Inverse image versus forget: the mate of the identity. -/
def etaleModuleInverseImageForget :
    TwoSquare (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y)
      (etaleModuleInverseImage.{u, r} Λ f)
      (etaleAbelianInverseImage.{u, r} f)
        (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X) :=
  (mateEquiv (etaleModuleInverseImageAdj.{u, r} Λ f)
    (etaleAbelianInverseImageDirectImageAdj.{u, r} f)).symm (etaleModuleDirectImageForget Λ f)

/-- **Forgetting the module structure commutes with inverse image.** -/
instance isIso_etaleModuleInverseImageForget :
    IsIso (etaleModuleInverseImageForget.{u, r} Λ f) := by
  have : IsIso ((mateEquiv
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange f)
        (ModuleCat.{max (u + 1) r} Λ) Y.smallEtaleTopology X.smallEtaleTopology)
      (etaleAbelianInverseImageDirectImageAdj.{u, r} f)).symm
        (etaleModuleDirectImageForget Λ f)) :=
    isIso_coefficientPullbackTwoSquare (smallEtaleBaseChange f) Y.smallEtaleTopology
      X.smallEtaleTopology (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r})
  exact Stacks.CategoryTheory.isIso_mateEquiv_symm_of_leftAdjointUniq_general
    (etaleModuleInverseImageAdj.{u, r} Λ f)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange f)
      (ModuleCat.{max (u + 1) r} Λ) Y.smallEtaleTopology X.smallEtaleTopology)
    (etaleAbelianInverseImageDirectImageAdj.{u, r} f)
    (etaleAbelianInverseImageDirectImageAdj.{u, r} f) _

end InverseImage

section ExtensionByZero

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- Extension by zero versus forgetting the module structure: the comparison of the two
composites, built from the Kan extension and from sheafification. -/
abbrev etaleModuleExtensionByZeroForget :
    TwoSquare (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ U)
      (etaleModuleExtensionByZero.{u, r} Λ j)
      (extensionByZero.{u, r} j) (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X) :=
  coefficientPullbackTwoSquare (Scheme.Etale.smallEtaleCompose j) U.smallEtaleTopology
    X.smallEtaleTopology (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r})

end ExtensionByZero

section Derived

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Forgetting the module structure commutes with the derived inverse image**: the image in
`D(X_étale)` of `f⁻¹ K` is `f⁻¹` of the image of `K`, naturally in `K ∈ D(Y_étale, Λ)`. -/
def etaleModuleDerivedInverseImageForgetIso :
    etaleModuleDerivedInverseImageGeneral.{u, r} Λ f ⋙ etaleModuleForgetDerived.{u, r} Λ X ≅
      etaleModuleForgetDerived.{u, r} Λ Y ⋙ etaleAbelianDerivedInverseImage.{u, r} f :=
  Functor.mapDerivedCategoryCompIsoOfCompIso (Iso.refl _) ≪≫
    (Functor.mapDerivedCategoryCompIsoOfCompIso (asIso
      (etaleModuleInverseImageForget.{u, r} Λ f))).symm

variable {U : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- **Forgetting the module structure commutes with extension by zero applied degreewise.** -/
def etaleModuleExtensionByZeroMapDerivedCategoryForgetIso :
    (etaleModuleExtensionByZero.{u, r} Λ j).mapDerivedCategory ⋙
        etaleModuleForgetDerived.{u, r} Λ X ≅
      etaleModuleForgetDerived.{u, r} Λ U ⋙ (extensionByZero.{u, r} j).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIsoOfCompIso (Iso.refl _) ≪≫
    (Functor.mapDerivedCategoryCompIsoOfCompIso
      (asIso (etaleModuleExtensionByZeroForget.{u, r} Λ j))).symm

end Derived

section BaseChange

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- The direct-image composition comparison commutes with a change of coefficients. -/
theorem sheafCompose_map_smallEtalePushforwardComp'_hom {X₁ X₂ X₃ : Scheme.{u}} (a : X₁ ⟶ X₂)
    (b : X₂ ⟶ X₃) (ab : X₁ ⟶ X₃) (hab : ab = a ≫ b) {A B : Type*} [Category* A] [Category* B]
    (G : A ⥤ B) [X₁.smallEtaleTopology.HasSheafCompose G]
    [X₃.smallEtaleTopology.HasSheafCompose G] (F : Sheaf X₁.smallEtaleTopology A) :
    (sheafCompose X₃.smallEtaleTopology G).map
        ((smallEtalePushforwardComp' a b ab hab A).hom.app F) =
      (smallEtalePushforwardComp' a b ab hab B).hom.app
        ((sheafCompose X₁.smallEtaleTopology G).obj F) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  simp [smallEtalePushforwardComp']
  rfl

/-- The inverse direct-image composition comparison commutes with a change of coefficients. -/
theorem sheafCompose_map_smallEtalePushforwardComp'_inv {X₁ X₂ X₃ : Scheme.{u}} (a : X₁ ⟶ X₂)
    (b : X₂ ⟶ X₃) (ab : X₁ ⟶ X₃) (hab : ab = a ≫ b) {A B : Type*} [Category* A] [Category* B]
    (G : A ⥤ B) [X₁.smallEtaleTopology.HasSheafCompose G]
    [X₃.smallEtaleTopology.HasSheafCompose G] (F : Sheaf X₁.smallEtaleTopology A) :
    (sheafCompose X₃.smallEtaleTopology G).map
        ((smallEtalePushforwardComp' a b ab hab A).inv.app F) =
      (smallEtalePushforwardComp' a b ab hab B).inv.app
        ((sheafCompose X₁.smallEtaleTopology G).obj F) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  simp [smallEtalePushforwardComp']
  rfl

/-- The comparison `g'_* ⋙ f_* ⟶ f'_* ⋙ g_*` of the two composite direct images around a
commutative square, for sheaves with values in an arbitrary category. -/
def smallEtaleDirectImageSquare (A : Type*) [Category* A] :
    TwoSquare (smallEtalePushforward g' A) (smallEtalePushforward f' A)
      (smallEtalePushforward f A) (smallEtalePushforward g A) :=
  TwoSquare.mk _ _ _ _ ((smallEtalePushforwardComp' g' f (g' ≫ f) rfl A).hom ≫
    (smallEtalePushforwardComp' f' g (g' ≫ f) h A).inv)

/-- **The base change map `g^{-1} f_* ⟶ f'_* (g')^{-1}` for sheaves of `Λ`-modules** on the
small étale sites, attached to a commutative square `g' ≫ f = f' ≫ g`: the mate, along the two
inverse-image/direct-image adjunctions of `g'` and `g`, of the comparison of the two composite
direct images around the square. -/
def etaleModuleBaseChangeGeneral :
    etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleInverseImage.{u, r} Λ g ⟶
      etaleModuleInverseImage.{u, r} Λ g' ⋙ etaleModuleDirectImage.{u, r} Λ f' :=
  ((mateEquiv (etaleModuleInverseImageAdj.{u, r} Λ g') (etaleModuleInverseImageAdj.{u, r} Λ g)).symm
    (smallEtaleDirectImageSquare f g g' f' h (ModuleCat.{max (u + 1) r} Λ)))

/-- **The base change map commutes with forgetting the module structure**: after forgetting, it
is the base change map `Stacks.EtaleCohomology.etaleAbelianBaseChange` of the underlying abelian
sheaves, up to the comparisons of the inverse images. -/
theorem etaleModuleBaseChange_forget (c : EtaleModules.{u, r} Λ X) :
    (etaleModuleInverseImageForget.{u, r} Λ g).app
      ((etaleModuleDirectImage.{u, r} Λ f).obj c) ≫
        (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y').map
          ((etaleModuleBaseChangeGeneral.{u, r} Λ f g g' f' h).app c) =
      (etaleAbelianBaseChange.{u, r} f g g' f' h).app
        ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).obj c) ≫
        (etaleAbelianDirectImage.{u, r} f').map
          ((etaleModuleInverseImageForget.{u, r} Λ g').app c) := by
  rw [etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso.{u, r} f g g' f' h (g' ≫ f)
    rfl h]
  have key := Stacks.CategoryTheory.mateEquiv_symm_hComp_eq_app
    (etaleModuleInverseImageAdj.{u, r} Λ g') (etaleModuleInverseImageAdj.{u, r} Λ g)
    (etaleAbelianInverseImageDirectImageAdj.{u, r} g')
    (etaleAbelianInverseImageDirectImageAdj.{u, r} g)
    (etaleModuleInverseImageForget.{u, r} Λ g') (etaleModuleInverseImageForget.{u, r} Λ g)
    (etaleModuleDirectImageForget.{u, r} Λ f)
    (etaleModuleDirectImageForgetInv.{u, r} Λ f')
    (smallEtaleDirectImageSquare f g g' f' h (ModuleCat.{max (u + 1) r} Λ))
    (smallEtaleDirectImageSquare f g g' f' h AddCommGrpCat.{max (u + 1) r}) (by
      rw [etaleModuleInverseImageForget, etaleModuleInverseImageForget, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply]
      refine NatTrans.ext (funext fun d => ?_)
      rw [ts_whiskerLeft_app, ts_whiskerRight_app, ts_vComp_app, ts_vComp_app]
      simp only [etaleModuleDirectImageForget_app, etaleModuleDirectImageForgetInv_app]
      change _ = (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y).map
        ((smallEtalePushforwardComp' g' f (g' ≫ f) rfl _).hom.app d ≫
          (smallEtalePushforwardComp' f' g (g' ≫ f) h _).inv.app _)
      rw [Functor.map_comp, sheafCompose_map_smallEtalePushforwardComp'_hom,
        sheafCompose_map_smallEtalePushforwardComp'_inv]
      rfl) c
  rw [map_etaleModuleDirectImageForget_app_comp,
    comp_etaleModuleDirectImageForgetInv_app] at key
  exact key

end BaseChange

/-! ### The derived base change map -/

section DerivedBaseChange

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- **Stacks 0A2A for sheaves of `Λ`-modules.** The base change map
`g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}` on the unbounded derived categories of sheaves of `Λ`-modules
for the small étale topologies, attached to a commutative square `g' ≫ f = f' ≫ g` of schemes:
the derived transformation `Stacks.Homology.DerivedSquare.cochainDerivedSquare` of the underived
base change map `Stacks.EtaleCohomology.etaleModuleBaseChangeGeneral`. -/
def etaleModuleDerivedBaseChangeGeneral :
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ⋙
      etaleModuleDerivedInverseImageGeneral.{u, r} Λ g ⟶
      etaleModuleDerivedInverseImageGeneral.{u, r} Λ g' ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f' :=
  Stacks.Homology.DerivedSquare.cochainDerivedSquare
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f)
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f')
    (etaleModuleBaseChangeGeneral.{u, r} Λ f g g' f' h)

/-- The defining property of `Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeGeneral` on
a complex `K`: precomposed with the derived-functor unit of `Rf_*`, it is the degreewise base
change map followed by the derived-functor unit of `Rf'_*`. -/
theorem etaleModuleDerivedBaseChange_fac_general (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    (etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategoryFactors.inv.app
        (((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      (etaleModuleDerivedInverseImageGeneral.{u, r} Λ g).map
        ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f).app K) ≫
      (etaleModuleDerivedBaseChangeGeneral.{u, r} Λ f g g' f' h).app (DerivedCategory.Q.obj K) =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (etaleModuleBaseChangeGeneral.{u, r} Λ f g g' f' h) (ComplexShape.up ℤ)).app K) ≫
      (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f').app
        (((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f').map
        ((etaleModuleInverseImage.{u, r} Λ g').mapDerivedCategoryFactors.inv.app K) :=
  Stacks.Homology.DerivedSquare.cochainDerivedSquare_fac_app _ _ _ K

/-- At a K-injective complex `I`, the derived base change map is invertible exactly when the
degreewise base change map followed by the derived-functor unit of `Rf'_*` is. -/
theorem isIso_etaleModuleDerivedBaseChange_app_Q_iff
    (I : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) [I.IsKInjective] :
    IsIso ((etaleModuleDerivedBaseChangeGeneral.{u, r} Λ f g g' f' h).app
      (DerivedCategory.Q.obj I)) ↔
      IsIso (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (etaleModuleBaseChangeGeneral.{u, r} Λ f g g' f' h) (ComplexShape.up ℤ)).app I) ≫
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f').app
          (((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I)) := by
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, r} Λ f I inferInstance
  have hfac := etaleModuleDerivedBaseChange_fac_general.{u, r} Λ f g g' f' h I
  exact Stacks.CategoryTheory.isIso_iff_of_fac _ _ _ _ _ hfac

/-- The comparison `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageForgetIsoUnconditional` at
a complex, read as a square: forgetting the unit of `Rf_*` on sheaves of `Λ`-modules is the unit of
`Rf_*` on abelian sheaves at the underlying complex, up to the exactness comparisons. -/
theorem etaleModuleDerivedDirectImageForget_unit_square {X₁ Y₁ : Scheme.{u}} (f₁ : X₁ ⟶ Y₁)
    (M : CochainComplex (EtaleModules.{u, r} Λ X₁) ℤ) :
    (DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (etaleModuleDirectImage.{u, r} Λ f₁ ⋙
          _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y₁))
          (ComplexShape.up ℤ)).inv.app M) ≫
      (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r}
        Λ Y₁).mapDerivedCategoryFactors.inv.app
        (((etaleModuleDirectImage.{u, r} Λ f₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ≫
      (etaleModuleForgetDerived.{u, r} Λ Y₁).map
        ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f₁).app M) ≫
      (etaleModuleDerivedDirectImageForgetIsoUnconditional.{u, r} Λ f₁).hom.app
        (DerivedCategory.Q.obj M) =
    ((etaleModuleDirectImageForgetToDerivedCategoryIso.{u, r} Λ f₁).hom.app M ≫
      (etaleAbelianDerivedDirectImageUnit.{u, r} f₁).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X₁).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M))) ≫
      (forgetQuotientQhIso.{u, r} Λ f₁).hom.app M := by
  have := NatTrans.congr_app (etaleModuleDerivedDirectImageForgetIso_hom_fac.{u, r} Λ f₁) M
  simp only [etaleModuleDerivedDirectImageForgetUnit, forgetEtaleAbelianDerivedDirectImageUnit,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.assoc] at this
  simp only [Category.assoc]
  exact this

/-- **The complex-level square behind the agreement of the two base change maps**, for variable
transformations `β` (in place of the base change map of sheaves of `Λ`-modules) and `α` (in place
of that of abelian sheaves) and variable comparisons `τ`, `τ'` of the inverse images with the
forgetful functors, satisfying the underived agreement `hC`. It is stated for variables so that
no proof term unfolds the base change maps themselves. -/
theorem forget_complex_square_of_comp_eq
    (β : etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleInverseImage.{u, r} Λ g ⟶
      etaleModuleInverseImage.{u, r} Λ g' ⋙ etaleModuleDirectImage.{u, r} Λ f')
    (α : etaleAbelianDirectImage.{u, r} f ⋙ etaleAbelianInverseImage.{u, r} g ⟶
      etaleAbelianInverseImage.{u, r} g' ⋙ etaleAbelianDirectImage.{u, r} f')
    (τ : _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y ⋙
      etaleAbelianInverseImage.{u, r} g ≅
      etaleModuleInverseImage.{u, r} Λ g ⋙
        _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y')
    (τ' : _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X ⋙
      etaleAbelianInverseImage.{u, r} g' ≅
      etaleModuleInverseImage.{u, r} Λ g' ⋙
        _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X')
    (hC : ∀ c : EtaleModules.{u, r} Λ X,
      τ.hom.app ((etaleModuleDirectImage.{u, r} Λ f).obj c) ≫
          (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y').map (β.app c) =
        α.app ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).obj c) ≫
          (etaleAbelianDirectImage.{u, r} f').map (τ'.hom.app c))
    (I : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y').mapHomologicalComplex
      (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app I) ≫
        ((etaleAbelianDirectImage.{u, r} f').mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatIso.mapHomologicalComplex τ' (ComplexShape.up ℤ)).inv.app I) =
      (NatIso.mapHomologicalComplex τ (ComplexShape.up ℤ)).inv.app
          (((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
        (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app
          (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I) := by
  ext n : 1
  have hC' := hC (I.X n)
  have e : (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y').map (β.app (I.X n)) ≫
      (etaleAbelianDirectImage.{u, r} f').map (τ'.inv.app (I.X n)) =
      τ.inv.app ((etaleModuleDirectImage.{u, r} Λ f).obj (I.X n)) ≫
        α.app ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).obj (I.X n)) :=
    Stacks.CategoryTheory.comp_inv_eq_inv_comp_of_iso (τ.app _)
      ((etaleAbelianDirectImage.{u, r} f').mapIso (τ'.app (I.X n))) hC'
  exact e

/-- The degreewise comparison on homotopy categories built from a transformation `α`, at the class
of a complex `K`, is the class of the degreewise comparison on `K`. Stated for a variable `α`. -/
theorem homotopyComparison_app_quotient
    (α : etaleAbelianDirectImage.{u, r} f ⋙ etaleAbelianInverseImage.{u, r} g ⟶
      etaleAbelianInverseImage.{u, r} g' ⋙ etaleAbelianDirectImage.{u, r} f')
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}) ℤ) :
    ((Functor.mapHomotopyCategoryCompIso
        (Iso.refl (etaleAbelianDirectImage.{u, r} f ⋙ etaleAbelianInverseImage.{u, r} g))
        (ComplexShape.up ℤ)).hom ≫
      NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ) ≫
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (etaleAbelianInverseImage.{u, r} g' ⋙ etaleAbelianDirectImage.{u, r} f'))
        (ComplexShape.up ℤ)).inv).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K) := by
  have e₁ : (Functor.mapHomologicalComplexCompIso
      (Iso.refl (etaleAbelianDirectImage.{u, r} f ⋙ etaleAbelianInverseImage.{u, r} g))
      (ComplexShape.up ℤ)).hom.app K = 𝟙 _ := by ext; simp
  have e₂ : (Functor.mapHomologicalComplexCompIso
      (Iso.refl (etaleAbelianInverseImage.{u, r} g' ⋙ etaleAbelianDirectImage.{u, r} f'))
      (ComplexShape.up ℤ)).inv.app K = 𝟙 _ := by ext; simp
  simp only [Functor.mapHomotopyCategoryCompIso, NatTrans.comp_app]
  change (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (etaleAbelianDirectImage.{u, r} f ⋙ etaleAbelianInverseImage.{u, r} g))
        (ComplexShape.up ℤ)).hom.app K) ≫ _ ≫ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (etaleAbelianInverseImage.{u, r} g' ⋙ etaleAbelianDirectImage.{u, r} f'))
        (ComplexShape.up ℤ)).inv.app K) = _
  rw [e₁, e₂, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact Category.comp_id _

/-- **The transfer of invertibility through the forgetful functor, on complexes**, for variable
transformations `β` and `α` and variable comparisons `τ`, `τ'` satisfying the underived agreement
`hC`: if the degreewise comparison built from `α` followed by the unit of `Rf'_*` is invertible at
the underlying complex of `I`, then so is the image of the degreewise `β` followed by the unit of
`Rf'_*` at the underlying complex of `(g')^{-1} I`. -/
theorem isIso_forget_comparison_of_isIso
    (β : etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleInverseImage.{u, r} Λ g ⟶
      etaleModuleInverseImage.{u, r} Λ g' ⋙ etaleModuleDirectImage.{u, r} Λ f')
    (α : etaleAbelianDirectImage.{u, r} f ⋙ etaleAbelianInverseImage.{u, r} g ⟶
      etaleAbelianInverseImage.{u, r} g' ⋙ etaleAbelianDirectImage.{u, r} f')
    (τ : _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y ⋙
      etaleAbelianInverseImage.{u, r} g ⟶
      etaleModuleInverseImage.{u, r} Λ g ⋙
        _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y') [IsIso τ]
    (τ' : _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X ⋙
      etaleAbelianInverseImage.{u, r} g' ⟶
      etaleModuleInverseImage.{u, r} Λ g' ⋙
        _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X') [IsIso τ']
    (hC : ∀ c : EtaleModules.{u, r} Λ X,
      τ.app ((etaleModuleDirectImage.{u, r} Λ f).obj c) ≫
          (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y').map (β.app c) =
        α.app ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).obj c) ≫
          (etaleAbelianDirectImage.{u, r} f').map (τ'.app c))
    (I : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    (hα : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app
          (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I))) ≫
      (etaleAbelianDerivedDirectImageUnit.{u, r} f').app
        (((etaleAbelianInverseImage.{u, r} g').mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I))))) :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y').mapHomologicalComplex
          (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app I))) ≫
      (etaleAbelianDerivedDirectImageUnit.{u, r} f').app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
            (((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I)))) := by
  have hcx := forget_complex_square_of_comp_eq.{u, r} Λ f g g' f' β α (asIso τ) (asIso τ') hC I
  have hsq := (DerivedCategory.Qh.map_comp _ _).symm.trans
    ((congrArg DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_comp
      _ _).symm).trans ((congrArg (fun t => DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map t)) hcx).trans
      ((congrArg DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_comp
        _ _)).trans (DerivedCategory.Qh.map_comp _ _))))
  exact Stacks.CategoryTheory.isIso_comp_of_squares
    ((etaleAbelianDerivedDirectImageUnit.{u, r} f').naturality
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatIso.mapHomologicalComplex (asIso τ') (ComplexShape.up ℤ)).inv.app I))).symm hsq hα

/-- `Stacks.EtaleCohomology.isIso_forget_comparison_of_isIso`, with the hypothesis on the abelian
side read off a factorization of an invertible morphism `bc` of the shape of
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_fac`. Everything is a variable, so that
the kernel never compares the base change maps with their definitions. -/
theorem isIso_forget_comparison_of_fac
    (β : etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleInverseImage.{u, r} Λ g ⟶
      etaleModuleInverseImage.{u, r} Λ g' ⋙ etaleModuleDirectImage.{u, r} Λ f')
    (α : etaleAbelianDirectImage.{u, r} f ⋙ etaleAbelianInverseImage.{u, r} g ⟶
      etaleAbelianInverseImage.{u, r} g' ⋙ etaleAbelianDirectImage.{u, r} f')
    (τ : _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y ⋙
      etaleAbelianInverseImage.{u, r} g ⟶
      etaleModuleInverseImage.{u, r} Λ g ⋙
        _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y') [IsIso τ]
    (τ' : _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X ⋙
      etaleAbelianInverseImage.{u, r} g' ⟶
      etaleModuleInverseImage.{u, r} Λ g' ⋙
        _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X') [IsIso τ']
    (hC : ∀ c : EtaleModules.{u, r} Λ X,
      τ.app ((etaleModuleDirectImage.{u, r} Λ f).obj c) ≫
          (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y').map (β.app c) =
        α.app ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).obj c) ≫
          (etaleAbelianDirectImage.{u, r} f').map (τ'.app c))
    (I : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) [I.IsKInjective]
    (bc : (etaleAbelianDerivedDirectImage.{u, r} f ⋙ etaleAbelianDerivedInverseImage.{u, r} g).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I))) ⟶
      (etaleAbelianDerivedInverseImage.{u, r} g' ⋙ etaleAbelianDerivedDirectImage.{u, r} f').obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I))))
    (w : (etaleAbelianDirectImage.{u, r} f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (etaleAbelianInverseImage.{u, r} g).mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      (etaleAbelianInverseImage.{u, r} g').mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (etaleAbelianDirectImage.{u, r} f').mapHomotopyCategory (ComplexShape.up ℤ))
    (hw : w = (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (etaleAbelianDirectImage.{u, r} f ⋙ etaleAbelianInverseImage.{u, r} g))
        (ComplexShape.up ℤ)).hom ≫
      NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ) ≫
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (etaleAbelianInverseImage.{u, r} g' ⋙ etaleAbelianDirectImage.{u, r} f'))
        (ComplexShape.up ℤ)).inv)
    (hfac : (etaleAbelianInverseImage.{u, r} g).mapDerivedCategoryFactorsh.inv.app
        (((etaleAbelianDirectImage.{u, r} f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I))) ≫
      (etaleAbelianDerivedInverseImage.{u, r} g).map
        ((etaleAbelianDerivedDirectImageUnit.{u, r} f).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I))) ≫
      bc =
    DerivedCategory.Qh.map (w.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I))) ≫
      (etaleAbelianDerivedDirectImageUnit.{u, r} f').app
        (((etaleAbelianInverseImage.{u, r} g').mapHomotopyCategory
          (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I))) ≫
      (etaleAbelianDerivedDirectImage.{u, r} f').map
        ((etaleAbelianInverseImage.{u, r} g').mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I))))
    (hbc : IsIso bc) :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y').mapHomologicalComplex
          (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app I))) ≫
      (etaleAbelianDerivedDirectImageUnit.{u, r} f').app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
            (((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I)))) := by
  have hu := isIso_etaleAbelianDerivedDirectImageUnit_app_forget_of_isKInjective.{u, r} Λ f I
  have hα := Stacks.CategoryTheory.isIso_of_fac_of_isIso _ _ _ _ _ hfac hbc
  rw [hw, homotopyComparison_app_quotient] at hα
  exact isIso_forget_comparison_of_isIso.{u, r} Λ f g g' f' β α τ τ' hC I hα

/-- Forgetting the module structure of the unit of `Rf_*` on sheaves of `Λ`-modules: it is the
unit of `Rf_*` on abelian sheaves at the underlying complex, up to the exactness comparison of
the forgetful functor, the comparison of the two localizations, and invertible maps on the
target. -/
theorem etaleModuleForgetDerived_map_unit {X₁ Y₁ : Scheme.{u}} (f₁ : X₁ ⟶ Y₁)
    (M : CochainComplex (EtaleModules.{u, r} Λ X₁) ℤ) :
    (etaleModuleForgetDerived.{u, r} Λ Y₁).map
        ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f₁).app M) =
      (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r}
        Λ Y₁).mapDerivedCategoryFactors.hom.app
          (((etaleModuleDirectImage.{u, r} Λ f₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
        (DerivedCategory.quotientCompQhIso _).inv.app
          (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y₁).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
            (((etaleModuleDirectImage.{u, r} Λ f₁).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)) ≫
        (etaleAbelianDerivedDirectImageUnit.{u, r} f₁).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X₁).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)) ≫
        (forgetQuotientQhIso.{u, r} Λ f₁).hom.app M ≫
        (etaleModuleDerivedDirectImageForgetIsoUnconditional.{u, r} Λ f₁).inv.app
          (DerivedCategory.Q.obj M) := by
  have hsq := etaleModuleDerivedDirectImageForget_unit_square.{u, r} Λ f₁ M
  have hc₀ : DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (etaleModuleDirectImage.{u, r} Λ f₁ ⋙
        _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y₁))
        (ComplexShape.up ℤ)).inv.app M) = 𝟙 _ := by
    exact DerivedCategory.Q.map_id _
  have he₁ : DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
      (etaleModuleDirectImageCompForgetIso.{u, r} Λ f₁).symm (ComplexShape.up ℤ)).hom.app M) =
        𝟙 _ := by
    exact DerivedCategory.Q.map_id _
  have hmHF : DerivedCategory.Qh.map
      (((etaleAbelianDirectImage.{u, r} f₁).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
        (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X₁).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)) =
        𝟙 _ := by
    exact DerivedCategory.Qh.map_id _
  have hA : (etaleModuleDirectImageForgetToDerivedCategoryIso.{u, r} Λ f₁).hom.app M =
      (DerivedCategory.quotientCompQhIso _).inv.app
        (((etaleAbelianDirectImage.{u, r} f₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X₁).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M)) := by
    have : (etaleModuleDirectImageForgetToDerivedCategoryIso.{u, r} Λ f₁).hom.app M =
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (etaleModuleDirectImageCompForgetIso.{u, r} Λ f₁).symm (ComplexShape.up ℤ)).hom.app M) ≫
        (DerivedCategory.quotientCompQhIso _).inv.app
          (((etaleAbelianDirectImage.{u, r} f₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X₁).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)) ≫
        DerivedCategory.Qh.map
          (((etaleAbelianDirectImage.{u, r} f₁).mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).inv.app
            (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X₁).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)) := by
      simp [etaleModuleDirectImageForgetToDerivedCategoryIso]
    rw [this, he₁, hmHF]
    exact (Category.id_comp _).trans (Category.comp_id _)
  rw [hc₀, hA] at hsq
  have h2 : (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r}
      Λ Y₁).mapDerivedCategoryFactors.inv.app
        (((etaleModuleDirectImage.{u, r} Λ f₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
      (etaleModuleForgetDerived.{u, r} Λ Y₁).map
        ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f₁).app M) ≫
      (etaleModuleDerivedDirectImageForgetIsoUnconditional.{u, r} Λ f₁).hom.app
        (DerivedCategory.Q.obj M) =
      ((DerivedCategory.quotientCompQhIso _).inv.app
        (((etaleAbelianDirectImage.{u, r} f₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X₁).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M)) ≫
        (etaleAbelianDerivedDirectImageUnit.{u, r} f₁).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X₁).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M))) ≫
        (forgetQuotientQhIso.{u, r} Λ f₁).hom.app M :=
    (Category.id_comp _).symm.trans ((Category.assoc _ _ _).symm.trans hsq)
  rw [← cancel_mono ((etaleModuleDerivedDirectImageForgetIsoUnconditional.{u, r} Λ f₁).hom.app
      (DerivedCategory.Q.obj M)),
    ← cancel_epi ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r}
      Λ Y₁).mapDerivedCategoryFactors.inv.app
      (((etaleModuleDirectImage.{u, r} Λ f₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))]
  refine h2.trans ?_
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  have e : ((etaleAbelianDerivedDirectImageUnit.{u, r} f₁).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X₁).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M)) ≫
      (forgetQuotientQhIso.{u, r} Λ f₁).hom.app M ≫
        (etaleModuleDerivedDirectImageForgetIsoUnconditional.{u, r} Λ f₁).inv.app
          (DerivedCategory.Q.obj M)) ≫
      (etaleModuleDerivedDirectImageForgetIsoUnconditional.{u, r} Λ f₁).hom.app
        (DerivedCategory.Q.obj M) =
      (etaleAbelianDerivedDirectImageUnit.{u, r} f₁).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X₁).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M)) ≫
      (forgetQuotientQhIso.{u, r} Λ f₁).hom.app M := by
    simp
  exact congrArg (_ ≫ ·) e.symm


/-- **The base change map for sheaves of `Λ`-modules is invertible at a K-injective complex as
soon as the base change map of the underlying abelian sheaves is.** -/
theorem isIso_etaleModuleDerivedBaseChange_app_Q_of_isIso
    (I : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) [I.IsKInjective]
    (hI : IsIso ((etaleAbelianDerivedBaseChange.{u, r} f g g' f' h).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I))))) :
    IsIso ((etaleModuleDerivedBaseChangeGeneral.{u, r} Λ f g g' f' h).app
      (DerivedCategory.Q.obj I)) := by
  rw [isIso_etaleModuleDerivedBaseChange_app_Q_iff,
    ← isIso_iff_of_reflects_iso _ (etaleModuleForgetDerived.{u, r} Λ Y'),
    CategoryTheory.Functor.map_comp, etaleModuleForgetDerived_map_unit]
  refine (Stacks.CategoryTheory.isIso_comp₄_comp_iff _ _ _ _ _).mpr ?_
  -- move the degreewise base change map past the two comparisons
  have n1 : (etaleModuleForgetDerived.{u, r} Λ Y').map (DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (etaleModuleBaseChangeGeneral.{u, r} Λ f g g' f' h)
          (ComplexShape.up ℤ)).app I)) ≫
      (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r}
        Λ Y').mapDerivedCategoryFactors.hom.app
        (((etaleModuleDirectImage.{u, r} Λ f').mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I)) =
      (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r}
        Λ Y').mapDerivedCategoryFactors.hom.app
        (((etaleModuleDirectImage.{u, r} Λ f ⋙
          etaleModuleInverseImage.{u, r} Λ g).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ≫
      DerivedCategory.Q.map
        (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y').mapHomologicalComplex
        (ComplexShape.up ℤ)).map ((NatTrans.mapHomologicalComplex
          (etaleModuleBaseChangeGeneral.{u, r} Λ f g g' f' h) (ComplexShape.up ℤ)).app I)) :=
    (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r}
      Λ Y').mapDerivedCategoryFactors.hom.naturality _
  have n2 : DerivedCategory.Q.map
      (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y').mapHomologicalComplex
        (ComplexShape.up ℤ)).map ((NatTrans.mapHomologicalComplex
          (etaleModuleBaseChangeGeneral.{u, r} Λ f g g' f' h) (ComplexShape.up ℤ)).app I)) ≫
      (DerivedCategory.quotientCompQhIso _).inv.app
        (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y').mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          (((etaleModuleDirectImage.{u, r} Λ f').mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I))) =
      (DerivedCategory.quotientCompQhIso _).inv.app
        (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y').mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          (((etaleModuleDirectImage.{u, r} Λ f ⋙
            etaleModuleInverseImage.{u, r} Λ g).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y').mapHomologicalComplex
          (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (etaleModuleBaseChangeGeneral.{u, r} Λ f g g' f' h)
            (ComplexShape.up ℤ)).app I))) :=
    (DerivedCategory.quotientCompQhIso _).inv.naturality _
  refine (Stacks.CategoryTheory.isIso_comp_comp_iff_of_eq n1 _).mpr ?_
  refine (isIso_comp_left_iff _ _).mpr ?_
  refine (Stacks.CategoryTheory.isIso_comp_comp_iff_of_eq n2 _).mpr ?_
  refine (isIso_comp_left_iff _ _).mpr ?_
  exact isIso_forget_comparison_of_fac.{u, r} Λ f g g' f'
    (etaleModuleBaseChangeGeneral.{u, r} Λ f g g' f' h) (etaleAbelianBaseChange.{u, r} f g g' f' h)
    (etaleModuleInverseImageForget.{u, r} Λ g)
    (etaleModuleInverseImageForget.{u, r} Λ g')
    (etaleModuleBaseChange_forget.{u, r} Λ f g g' f' h) I _ _
    (by rw [etaleAbelianHomotopyBaseChange])
    (etaleAbelianDerivedBaseChange_fac.{u, r} f g g' f' h _) hI

/-- **The base change map for sheaves of `Λ`-modules is invertible wherever the base change map
of the underlying abelian sheaves is.** For a commutative square `g' ≫ f = f' ≫ g` of schemes and
`K` in `D(X_étale, Λ)`, if the base change map `g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}` of abelian sheaves
is invertible at the image of `K` in `D(X_étale)`, then the base change map of sheaves of
`Λ`-modules is invertible at `K`. -/
theorem isIso_etaleModuleDerivedBaseChange_app_of_isIso
    (K : DerivedCategory (EtaleModules.{u, r} Λ X))
    (hK : IsIso ((etaleAbelianDerivedBaseChange.{u, r} f g g' f' h).app
      ((etaleModuleForgetDerived.{u, r} Λ X).obj K))) :
    IsIso ((etaleModuleDerivedBaseChangeGeneral.{u, r} Λ f g g' f' h).app K) := by
  obtain ⟨M, ⟨e₀⟩⟩ : ∃ M, Nonempty (DerivedCategory.Q.obj M ≅ K) :=
    ⟨_, ⟨(Localization.essSurj DerivedCategory.Q
      (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ))).mem_essImage
        K |>.getIso⟩⟩
  obtain ⟨I, t, hI, ht⟩ :=
    Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian
      (C := EtaleModules.{u, r} Λ X) M
  have : IsIso (DerivedCategory.Q.map t) :=
    Localization.inverts DerivedCategory.Q
      (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)) _
      ((HomologicalComplex.mem_quasiIso_iff _).2 ht)
  let e : DerivedCategory.Q.obj I ≅ K := (asIso (DerivedCategory.Q.map t)).symm ≪≫ e₀
  rw [← NatTrans.isIso_app_iff_of_iso _ e]
  have := hI
  refine isIso_etaleModuleDerivedBaseChange_app_Q_of_isIso.{u, r} Λ f g g' f' h I ?_
  let e' : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)) ≅
      (etaleModuleForgetDerived.{u, r} Λ X).obj K :=
    (DerivedCategory.quotientCompQhIso _).app _ ≪≫
      ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).mapDerivedCategoryFactors.app
        I).symm ≪≫
      (etaleModuleForgetDerived.{u, r} Λ X).mapIso e
  exact (NatTrans.isIso_app_iff_of_iso _ e').2 hK

end DerivedBaseChange

end Stacks.EtaleCohomology

end
