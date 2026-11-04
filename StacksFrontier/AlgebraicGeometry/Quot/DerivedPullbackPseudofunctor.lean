module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackSectionFunctor
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionAssociativity
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackInvertsQuasiIsoOfToposHom
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesCompare

/-!
# The derived pullback of modules on algebraic spaces is a coherent pseudofunctor

## Main definitions

* `CategoryTheory.PullbackData.ofEq`: a pullback pseudofunctor datum transported along a
  pointwise equality of its inverse images.
* `CategoryTheory.PullbackData.mapHomotopyCategory`: the datum induced on the unbounded homotopy
  categories by a datum of additive functors.
* `CategoryTheory.PullbackData.LeftDerived`: a datum of left derived functors of a pullback
  pseudofunctor datum on homotopy categories, computed on a resolving class which the inverse
  images preserve; and `CategoryTheory.PullbackData.LeftDerived.toPullbackData`, the induced
  pseudofunctor datum of the derived functors.
* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`: the derived pullback of `𝒪`-modules
  along morphisms of algebraic spaces as a pullback pseudofunctor datum, with the canonical
  comparisons.

## Main results

* `CategoryTheory.PullbackData.IsCoherent.ofEq`,
  `CategoryTheory.PullbackData.IsCoherent.mapHomotopyCategory` and
  `CategoryTheory.PullbackData.LeftDerived.isCoherent`: coherence is inherited by each of the
  three constructions.
* `AlgebraicGeometry.Space.hasDerivedModulePullbacks`: the derived pullback exists along every
  morphism of algebraic spaces (Stacks 06YY).
* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData_isCoherent`: the derived pullback of
  `𝒪`-modules on algebraic spaces is a coherent pseudofunctor.

## Implementation notes

The comparisons of the derived datum are the canonical ones: the composition comparison
`Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` is the comparison of two left derived functors of degreewise pullback
along `f ≫ g` (Stacks 0D6D), and the unit law is the comparison of `L(𝟙)^*` with the identity
functor, a left derived functor of degreewise pullback along `𝟙` because the latter is
isomorphic to the identity.  Their coherence is checked on a left derived functor by
`CategoryTheory.Functor.leftDerived_ext`, which reduces it to the coherence of the underived
datum.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.PullbackData

variable {A : Type u₁} [Category.{v₁} A]

/-! ### Transport along an equality of inverse images -/

section OfEq

variable {D : A → Type u₂} [∀ a, Category.{v₂} (D a)]

/-- The pullback pseudofunctor datum `P` with its inverse images replaced by equal functors,
the comparisons being transported along the equalities. -/
abbrev ofEq (P : PullbackData A D) (pull : ∀ {a b : A}, (a ⟶ b) → (D b ⥤ D a))
    (h : ∀ {a b : A} (f : a ⟶ b), pull f = P.pull f) : PullbackData A D where
  pull := pull
  idIso a := eqToIso (h (𝟙 a)) ≪≫ P.idIso a
  compIso f g := eqToIso (h (f ≫ g)) ≪≫ P.compIso f g ≪≫ eqToIso (by rw [h f, h g])

/-- Transporting a datum along the reflexive equalities of its own inverse images returns the
datum. -/
theorem ofEq_self (P : PullbackData A D)
    (h : ∀ {a b : A} (f : a ⟶ b), P.pull f = P.pull f) : P.ofEq P.pull h = P := by
  cases P
  simp only [ofEq, eqToIso_refl, Iso.refl_trans, Iso.trans_refl]

/-- Coherence is inherited by a transport along an equality of the inverse images. -/
theorem IsCoherent.ofEq {P : PullbackData A D} (hP : P.IsCoherent)
    (pull : ∀ {a b : A}, (a ⟶ b) → (D b ⥤ D a))
    (h : ∀ {a b : A} (f : a ⟶ b), pull f = P.pull f) : (P.ofEq pull h).IsCoherent := by
  obtain rfl : @pull = @P.pull := by
    funext a b f
    exact h f
  rw [ofEq_self]
  exact hP

end OfEq

/-! ### The induced datum on homotopy categories -/

section HomotopyCategory

variable {M : A → Type u₂} [∀ a, Category.{v₂} (M a)] [∀ a, Preadditive (M a)]
  (P : PullbackData A M) [hadd : ∀ {a b : A} (f : a ⟶ b), (P.pull f).Additive]

/-- The pullback pseudofunctor datum induced on the unbounded homotopy categories by a datum of
additive functors: the inverse image along `f` is degreewise inverse image. -/
def mapHomotopyCategory :
    PullbackData A (fun a => HomotopyCategory (M a) (ComplexShape.up ℤ)) where
  pull f := (P.pull f).mapHomotopyCategory (ComplexShape.up ℤ)
  idIso a := Stacks.Homology.mapHomotopyCategoryIso (P.idIso a) (ComplexShape.up ℤ) ≪≫
    Stacks.Cohomology.DerivedPushforwardAssociativity.mapHomotopyCategoryIdIso (M a)
      (ComplexShape.up ℤ)
  compIso f g := Stacks.Homology.mapHomotopyCategoryIso (P.compIso f g) (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (ComplexShape.up ℤ)).symm

variable {P}

/-- The unit comparison of the induced datum, at the image of a complex `K`, is the image of the
degreewise unit comparison at `K`. -/
theorem mapHomotopyCategory_idIso_hom_app (a : A) (K : CochainComplex (M a) ℤ) :
    (P.mapHomotopyCategory.idIso a).hom.app ((HomotopyCategory.quotient _ _).obj K) =
      (HomotopyCategory.quotient _ _).map
        ((NatTrans.mapHomologicalComplex (P.idIso a).hom (ComplexShape.up ℤ)).app K) :=
  Category.comp_id _

/-- The inverse unit comparison of the induced datum, at the image of a complex `K`, is the
image of the degreewise inverse unit comparison at `K`. -/
theorem mapHomotopyCategory_idIso_inv_app (a : A) (K : CochainComplex (M a) ℤ) :
    (P.mapHomotopyCategory.idIso a).inv.app ((HomotopyCategory.quotient _ _).obj K) =
      (HomotopyCategory.quotient _ _).map
        ((NatTrans.mapHomologicalComplex (P.idIso a).inv (ComplexShape.up ℤ)).app K) :=
  Category.id_comp _

/-- The comparison of a presented composite for the induced datum, at the image of a complex
`K`, is the image of the degreewise comparison at `K`. -/
theorem mapHomotopyCategory_triangle_hom_app {a b c : A} {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c}
    (hk : f ≫ g = k) (K : CochainComplex (M c) ℤ) :
    (P.mapHomotopyCategory.triangle hk).hom.app ((HomotopyCategory.quotient _ _).obj K) =
      (HomotopyCategory.quotient _ _).map
        ((NatTrans.mapHomologicalComplex (P.triangle hk).hom (ComplexShape.up ℤ)).app K) := by
  subst hk
  rw [triangle_rfl, triangle_rfl]
  exact Category.comp_id _

/-- The inverse comparison of a presented composite for the induced datum, at the image of a
complex `K`, is the image of the degreewise inverse comparison at `K`. -/
theorem mapHomotopyCategory_triangle_inv_app {a b c : A} {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c}
    (hk : f ≫ g = k) (K : CochainComplex (M c) ℤ) :
    (P.mapHomotopyCategory.triangle hk).inv.app ((HomotopyCategory.quotient _ _).obj K) =
      (HomotopyCategory.quotient _ _).map
        ((NatTrans.mapHomologicalComplex (P.triangle hk).inv (ComplexShape.up ℤ)).app K) := by
  subst hk
  rw [triangle_rfl, triangle_rfl]
  exact Category.id_comp _

/-- Coherence is inherited by the induced datum on homotopy categories. -/
theorem IsCoherent.mapHomotopyCategory (hP : P.IsCoherent) : P.mapHomotopyCategory.IsCoherent where
  triangle_id {a b} g hk := by
    ext X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    rw [mapHomotopyCategory_triangle_hom_app, hP.triangle_id g hk]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.rightUnitor_inv_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp,
      NatTrans.mapHomologicalComplex_comp]
    have hi := mapHomotopyCategory_idIso_inv_app (P := P) a
      (((P.pull g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    refine Eq.trans ?_ hi.symm
    congr 1
    ext n
    simp
  triangle_comp {a b c d} f g p k q r hk hq hr hkr := by
    ext X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    have h1 := mapHomotopyCategory_triangle_hom_app (P := P) hkr K
    have h2 := mapHomotopyCategory_triangle_hom_app (P := P) hk
      (((P.pull p).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    have h3 := mapHomotopyCategory_triangle_hom_app (P := P) hr K
    have h4 := mapHomotopyCategory_triangle_hom_app (P := P) hq K
    have hc := NatTrans.congr_app (congrArg Iso.hom (hP.triangle_comp hk hq hr hkr))
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.associator_hom_app, Category.comp_id] at hc ⊢
    rw [h1, h3, h4]
    refine (congrArg (fun m => _ ≫ m) h2).trans ?_
    erw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    ext n
    simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f]
    exact hc (K.X n)

end HomotopyCategory

/-! ### Left derived functors of a pullback pseudofunctor datum -/

section LeftDerived

variable {K : A → Type u₂} [∀ a, Category.{v₂} (K a)]
  {D : A → Type u₃} [∀ a, Category.{v₃} (D a)]

/-- **Left derived functors of a pullback pseudofunctor datum, computed by resolutions.**  For
each object `a` a localization `Q a : K a ⥤ D a` at a class `W a` admitting a right calculus of
fractions, and for each morphism `f : a ⟶ b` a functor `L f : D b ⥤ D a` with a comparison
`α f : Q b ⋙ L f ⟶ f^* ⋙ Q a`; together with a class `R a` of objects which resolves every
object, on which every `f^*` inverts `W`, which every `f^*` preserves, and on which every `α f`
is invertible.  Then `L f` is the left derived functor of `f^*`. -/
structure LeftDerived (P : PullbackData A K) (D : A → Type u₃) [∀ a, Category.{v₃} (D a)] where
  /-- The localization functors. -/
  Q : ∀ a, K a ⥤ D a
  /-- The classes of weak equivalences. -/
  W : ∀ a, MorphismProperty (K a)
  /-- Each `Q a` is a localization at `W a`. -/
  isLocalization : ∀ a, (Q a).IsLocalization (W a)
  /-- Each `W a` admits a right calculus of fractions. -/
  hasRightCalculusOfFractions : ∀ a, (W a).HasRightCalculusOfFractions
  /-- The derived inverse images. -/
  L : ∀ {a b : A}, (a ⟶ b) → (D b ⥤ D a)
  /-- The comparisons of the derived inverse images with the underived ones. -/
  α : ∀ {a b : A} (f : a ⟶ b), Q b ⋙ L f ⟶ P.pull f ⋙ Q a
  /-- The resolving classes. -/
  R : ∀ a, ObjectProperty (K a)
  /-- Every object receives a weak equivalence from an object of the resolving class. -/
  resolves : ∀ a (M : K a), ∃ (N : K a) (_ : R a N) (s : N ⟶ M), W a s
  /-- Each `f^* ⋙ Q a` inverts the weak equivalences between objects of the resolving class. -/
  inverts : ∀ {a b : A} (f : a ⟶ b) {M N : K b} (s : M ⟶ N), W b s → R b M → R b N →
    IsIso ((P.pull f ⋙ Q a).map s)
  /-- Each `f^*` carries the resolving class into the resolving class. -/
  preserves : ∀ {a b : A} (f : a ⟶ b) (M : K b), R b M → R a ((P.pull f).obj M)
  /-- Each `α f` is invertible at the objects of the resolving class. -/
  isIso_α : ∀ {a b : A} (f : a ⟶ b) (M : K b), R b M → IsIso ((α f).app M)

namespace LeftDerived

variable {P : PullbackData A K} (E : P.LeftDerived D)

attribute [instance] isLocalization hasRightCalculusOfFractions

/-- The derived inverse image is a left derived functor of the underived one. -/
instance isLeftDerivedFunctor {a b : A} (f : a ⟶ b) :
    (E.L f).IsLeftDerivedFunctor (E.α f) (E.W b) :=
  LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions (E.W b) (E.R b)
    (E.resolves b) (P.pull f ⋙ E.Q a) (E.inverts f) (E.Q b) (E.L f) (E.α f) (E.isIso_α f)

/-- The comparison of the composite of two derived inverse images with the underived inverse
image along the composite. -/
def compCounit {a b c : A} (f : a ⟶ b) (g : b ⟶ c) :
    E.Q c ⋙ (E.L g ⋙ E.L f) ⟶ P.pull (f ≫ g) ⋙ E.Q a :=
  Functor.whiskerRight (E.α g) (E.L f) ≫ Functor.whiskerLeft (P.pull g) (E.α f) ≫
    Functor.whiskerRight (P.compIso f g).inv (E.Q a)

/-- The components of `compCounit`. -/
theorem compCounit_app {a b c : A} (f : a ⟶ b) (g : b ⟶ c) (M : K c) :
    (E.compCounit f g).app M = (E.L f).map ((E.α g).app M) ≫ (E.α f).app ((P.pull g).obj M) ≫
      (E.Q a).map ((P.compIso f g).inv.app M) :=
  rfl

/-- The composite of two derived inverse images is a left derived functor of the inverse image
along the composite. -/
instance isLeftDerivedFunctor_comp {a b c : A} (f : a ⟶ b) (g : b ⟶ c) :
    (E.L g ⋙ E.L f).IsLeftDerivedFunctor (E.compCounit f g) (E.W c) :=
  LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions (E.W c) (E.R c)
    (E.resolves c) (P.pull (f ≫ g) ⋙ E.Q a) (E.inverts (f ≫ g)) (E.Q c) (E.L g ⋙ E.L f)
    (E.compCounit f g) fun M hM => by
      have := E.isIso_α g M hM
      have := E.isIso_α f _ (E.preserves g M hM)
      rw [compCounit_app]
      infer_instance

/-- **The composition comparison** `Lg^* ⋙ Lf^* ⟶ L(f ≫ g)^*`, induced by the universal
property of the left derived functor along the composite. -/
def compHom {a b c : A} (f : a ⟶ b) (g : b ⟶ c) : E.L g ⋙ E.L f ⟶ E.L (f ≫ g) :=
  (E.L (f ≫ g)).leftDerivedLift (E.α (f ≫ g)) (E.W c) _ (E.compCounit f g)

/-- The composition comparison is an isomorphism. -/
instance isIso_compHom {a b c : A} (f : a ⟶ b) (g : b ⟶ c) : IsIso (E.compHom f g) :=
  ((E.L (f ≫ g)).isLeftDerivedFunctor_iff_isIso_leftDerivedLift (E.α (f ≫ g)) (E.W c) _
    (E.compCounit f g)).1 inferInstance

/-- The comparison of the identity functor with the underived inverse image along an
identity. -/
def idCounit (a : A) : E.Q a ⋙ 𝟭 (D a) ⟶ P.pull (𝟙 a) ⋙ E.Q a :=
  (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (P.idIso a).inv (E.Q a)

/-- The components of `idCounit`. -/
theorem idCounit_app (a : A) (M : K a) :
    (E.idCounit a).app M = (E.Q a).map ((P.idIso a).inv.app M) := by
  simp [idCounit]

/-- The identity functor is a left derived functor of the inverse image along an identity. -/
instance isLeftDerivedFunctor_id (a : A) :
    (𝟭 (D a)).IsLeftDerivedFunctor (E.idCounit a) (E.W a) :=
  LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions (E.W a) (E.R a)
    (E.resolves a) (P.pull (𝟙 a) ⋙ E.Q a) (E.inverts (𝟙 a)) (E.Q a) (𝟭 (D a))
    (E.idCounit a) fun M _ => by
      rw [idCounit_app]
      infer_instance

/-- **The unit comparison** `𝟭 ⟶ L(𝟙 a)^*`, induced by the universal property of the left
derived functor along the identity. -/
def idHom (a : A) : 𝟭 (D a) ⟶ E.L (𝟙 a) :=
  (E.L (𝟙 a)).leftDerivedLift (E.α (𝟙 a)) (E.W a) _ (E.idCounit a)

/-- The unit comparison is an isomorphism. -/
instance isIso_idHom (a : A) : IsIso (E.idHom a) :=
  ((E.L (𝟙 a)).isLeftDerivedFunctor_iff_isIso_leftDerivedLift (E.α (𝟙 a)) (E.W a) _
    (E.idCounit a)).1 inferInstance

/-- **The pullback pseudofunctor datum of the derived inverse images**, with the canonical unit
and composition comparisons. -/
abbrev toPullbackData : PullbackData A D where
  pull f := E.L f
  idIso a := (asIso (E.idHom a)).symm
  compIso f g := (asIso (E.compHom f g)).symm

/-- The inverse image along `f` of the derived datum is the derived inverse image `L f`. -/
theorem toPullbackData_pull {a b : A} (f : a ⟶ b) : E.toPullbackData.pull f = E.L f := rfl

/-- The comparison of a presented composite, followed by the comparison of the derived inverse
image along it, is computed by the comparisons of the factors and the underived comparison. -/
theorem triangle_inv_app_comp_α {a b c : A} {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c}
    (hk : f ≫ g = k) (M : K c) :
    (E.toPullbackData.triangle hk).inv.app ((E.Q c).obj M) ≫ (E.α k).app M =
      (E.L f).map ((E.α g).app M) ≫ (E.α f).app ((P.pull g).obj M) ≫
        (E.Q a).map ((P.triangle hk).inv.app M) := by
  subst hk
  rw [triangle_rfl, triangle_rfl, ← compCounit_app]
  exact (E.L (f ≫ g)).leftDerived_fac_app (E.α (f ≫ g)) (E.W c) _ (E.compCounit f g) M

/-- The unit comparison of the derived inverse images, at an object in the image of the
localization functor. -/
theorem idIso_hom_app (a : A) (M : K a) :
    (E.toPullbackData.idIso a).hom.app ((E.Q a).obj M) =
      (E.α (𝟙 a)).app M ≫ (E.Q a).map ((P.idIso a).hom.app M) := by
  have h : (E.idHom a).app ((E.Q a).obj M) ≫ (E.α (𝟙 a)).app M =
      (E.Q a).map ((P.idIso a).inv.app M) := by
    rw [← idCounit_app]
    exact (E.L (𝟙 a)).leftDerived_fac_app (E.α (𝟙 a)) (E.W a) _ (E.idCounit a) M
  have e : (E.idHom a).app ((E.Q a).obj M) ≫
      (E.toPullbackData.idIso a).hom.app ((E.Q a).obj M) = 𝟙 _ :=
    (E.toPullbackData.idIso a).inv_hom_id_app _
  rw [← cancel_epi ((E.idHom a).app ((E.Q a).obj M)), e, reassoc_of% h, ← Functor.map_comp,
    Iso.inv_hom_id_app]
  exact ((E.Q a).map_id M).symm

/-- **The derived pseudofunctor datum is coherent** when the underived one is. -/
theorem isCoherent (hP : P.IsCoherent) : E.toPullbackData.IsCoherent where
  triangle_id {a b} g hk := by
    refine Iso.ext ((Iso.inv_eq_inv _ _).1 ((E.L g).leftDerived_ext (E.α g) (E.W b) _ _ _ ?_))
    ext M
    have hP' := NatTrans.congr_app (congrArg Iso.inv (hP.triangle_id g hk)) M
    simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
      Functor.whiskerLeft_app, Iso.symm_hom, Functor.rightUnitor_hom_app] at hP' ⊢
    have hn := (E.toPullbackData.idIso a).hom.naturality ((E.α g).app M)
    have hi := E.idIso_hom_app a ((P.pull g).obj M)
    simp only [Functor.id_map, Iso.symm_hom, Functor.comp_obj] at hn hi
    rw [hi] at hn
    rw [E.triangle_inv_app_comp_α hk M, hP']
    simpa using hn
  triangle_comp {a b c d} f g p k q r hk hq hr hkr := by
    refine Iso.ext ((Iso.inv_eq_inv _ _).1
      ((E.L r).leftDerived_ext (E.α r) (E.W d) _ _ _ ?_))
    ext M
    have hc := NatTrans.congr_app (congrArg Iso.inv (hP.triangle_comp hk hq hr hkr)) M
    have n1 := (E.toPullbackData.triangle hk).inv.naturality ((E.α p).app M)
    have t1 := E.triangle_inv_app_comp_α hk ((P.pull p).obj M)
    have t2 := E.triangle_inv_app_comp_α hkr M
    have t3 := E.triangle_inv_app_comp_α hq M
    have t4 := E.triangle_inv_app_comp_α hr M
    have n2 := (E.α f).naturality ((P.triangle hq).inv.app M)
    simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
      Functor.whiskerLeft_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
      Functor.associator_inv_app, Category.id_comp, Category.assoc, Functor.comp_map,
      Functor.comp_obj] at hc n1 n2 t1 ⊢
    rw [t2, ← reassoc_of% n1, reassoc_of% t1, t4,
      ← Functor.map_comp_assoc (E.L f) ((E.toPullbackData.triangle hq).inv.app _)
        ((E.α q).app M), t3]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% n2, ← Functor.map_comp, ← Functor.map_comp, hc]

end LeftDerived

end LeftDerived

end CategoryTheory.PullbackData

/-! ### The derived pullback of modules along morphisms of algebraic spaces -/

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The derived pullback `Lf^*` exists along every morphism of algebraic spaces**: degreewise
pullback along the morphism of small étale ringed topoi of Stacks 03G8 has an everywhere defined
left derived functor, the K-flat complexes with flat terms resolving (Stacks 06YS) and being
carried to isomorphisms (Stacks 06YY). -/
theorem hasDerivedModulePullbacks : BottomRankStratum.HasDerivedModulePullbacks B S hS :=
  fun f => Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy
    (smallEtaleRingedToposHom B S hS f)

/-- The inverse image of `𝒪`-modules along morphisms of algebraic spaces of Stacks 03LU, with
its unit law and its composition comparison, as a pullback pseudofunctor datum. -/
def modulePullbackData :
    PullbackData (AlgebraicSpaces B S hS) (fun X => Modules.{u, u} B S hS X.1 X.2) where
  pull f := modulePullback B S hS f
  idIso X := (modulePushforwardCoherence B S hS).modulePullbackIdIso X
  compIso f g := (modulePullbackCompIso B S hS f g).symm

/-- The inverse image of `𝒪`-modules is a coherent pseudofunctor (Stacks 03LU). -/
theorem modulePullbackData_isCoherent : (modulePullbackData B S hS).IsCoherent where
  triangle_id _ hk := (modulePushforwardCoherence B S hS).modulePullbackTriangle_id hk
  triangle_comp hk hq hr hkr :=
    (modulePushforwardCoherence B S hS).modulePullbackTriangle_comp hk hq hr hkr

/-- The pullback of modules along the morphism of ringed topoi
`(smallEtaleRingedToposHom f).toModulesHom`, which the derived pullback of Stacks 06YY derives, is
the inverse image of `𝒪`-modules of Stacks 03LU. -/
theorem toModulesHom_pullbackModules_eq_modulePullback {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) :
    (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules =
      modulePullback B S hS f :=
  congrArg (fun φ : Stacks.Sheaves.RingedToposModules.RingedToposHom
      (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y) => φ.pullbackModules)
    (RingedToposHom.toModulesHom_eq_toRingedToposModulesHom (smallEtaleRingedToposHom B S hS f))

/-- The inverse image of `𝒪`-modules in the spelling of the derived pullback of Stacks 06YY:
the pullback of modules of the morphism of ringed topoi
`(smallEtaleRingedToposHom f).toModulesHom`. -/
abbrev modulePullbackDataTopos :
    PullbackData (AlgebraicSpaces B S hS) (fun X => Modules.{u, u} B S hS X.1 X.2) :=
  (modulePullbackData B S hS).ofEq
    (fun f => (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules)
    (fun f => toModulesHom_pullbackModules_eq_modulePullback B S hS f)

/-- The inverse image of `𝒪`-modules along a morphism of algebraic spaces is additive. -/
instance modulePullbackDataTopos_additive {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    ((modulePullbackDataTopos B S hS).pull f).Additive :=
  RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHom B S hS f)

/-- **The derived pullback of `𝒪`-modules along morphisms of algebraic spaces as left derived
functors of degreewise pullback**, computed on the K-flat complexes with flat terms. -/
def derivedModulePullbackLeftDerived :
    (modulePullbackDataTopos B S hS).mapHomotopyCategory.LeftDerived
      (fun X => derivedModules B S hS X) where
  Q X := DerivedCategory.Qh
  W X := HomotopyCategory.quasiIso _ _
  isLocalization X := inferInstance
  hasRightCalculusOfFractions X := inferInstance
  L f := derivedPull B S hS (hasDerivedModulePullbacks B S hS) f
  α f := haveI := hasDerivedModulePullbacks B S hS f
    Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackComparison
      (smallEtaleRingedToposHom B S hS f)
  R X := Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
    (Y := smallEtaleRingedTopos B S hS X)
  resolves X M := Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat
    (Y := smallEtaleRingedTopos B S hS X) M
  inverts f := Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackInvertsQuasiIso_isKFlat
    (smallEtaleRingedToposHom B S hS f)
  preserves f M hM :=
    Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isKFlat_pullbackMapHomotopy
      (smallEtaleRingedToposHom B S hS f) M hM
  isIso_α f M hM := by
    open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom in
    exact isIso_derivedPullbackComparison_app_isKFlat (smallEtaleRingedToposHom B S hS f) M hM

/-- **The derived pullback of `𝒪`-modules on algebraic spaces as a pullback pseudofunctor
datum**: the inverse image along `f` is `Lf^*`, the unit law is the comparison
`L(𝟙)^* ≅ 𝟭`, and the composition comparison is the canonical isomorphism
`L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` of Stacks 0D6D. -/
def smallEtaleDerivedPullbackData :
    PullbackData (AlgebraicSpaces B S hS) (derivedModules B S hS) :=
  (derivedModulePullbackLeftDerived B S hS).toPullbackData

/-- The inverse image along `f` of the derived pullback datum is the derived pullback `Lf^*`. -/
theorem smallEtaleDerivedPullbackData_pull {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (smallEtaleDerivedPullbackData B S hS).pull f =
      derivedPull B S hS (hasDerivedModulePullbacks B S hS) f :=
  rfl

/-- **The derived pullback of `𝒪`-modules on algebraic spaces is a coherent pseudofunctor**: its
unit law and its composition comparisons satisfy the unit and associativity coherences. -/
theorem smallEtaleDerivedPullbackData_isCoherent :
    (smallEtaleDerivedPullbackData B S hS).IsCoherent :=
  (derivedModulePullbackLeftDerived B S hS).isCoherent
    (((modulePullbackData_isCoherent B S hS).ofEq _
      (fun f => toModulesHom_pullbackModules_eq_modulePullback B S hS f)).mapHomotopyCategory)

end AlgebraicGeometry.Space
