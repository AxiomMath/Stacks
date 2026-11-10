module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Separated
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Subgroups.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageValuativeDiagram
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedProduct
public import StacksFrontier.Topology.Spectral.BijectionHomeomorph
public import StacksFrontier.Topology.Spectral.ConstructiblyClosedStable

/-!
# Connected group schemes over a field are irreducible

The underlying topological space of a connected group scheme over a field is irreducible.
After base change to a large algebraically closed field the scheme stays connected and becomes
Jacobson with rational closed points; there the identity component is a closed subgroup scheme,
hence quasi-compact, and the set of its translates by points of a compact open neighbourhood is
clopen, so it is everything, which forces the identity component to be the whole space.

## Main results

* `AlgebraicGeometry.irreducibleSpace_of_connectedSpace` states that a connected group scheme
  over a field is irreducible.

## Implementation notes

A group scheme over `k` is represented as a group object in the category of schemes over
`Spec k`. Connectedness and irreducibility are properties of its underlying scheme.

## References

* [Stacks Project, Tag 0B7Q](https://stacks.math.columbia.edu/tag/0B7Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.CartesianMonoidalCategory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Stacks.AlgebraicGeometry.ClosedPointResidue
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

universe u


private theorem exists_factor_through_vanishingIdeal
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced X]
    (T : TopologicalSpace.Closeds Y) (h : Set.range f ⊆ T) :
    ∃ g : X ⟶ (Scheme.IdealSheafData.vanishingIdeal T).subscheme,
      g ≫ (Scheme.IdealSheafData.vanishingIdeal T).subschemeι = f := by
  let I := Scheme.IdealSheafData.vanishingIdeal T
  have htop : (I.comap f).support = ⊤ := by
    rw [Scheme.IdealSheafData.support_comap]
    apply SetLike.coe_injective
    ext x
    simp only [TopologicalSpace.Closeds.coe_preimage, Set.mem_preimage,
      TopologicalSpace.Closeds.coe_top, Set.mem_univ, I,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact ⟨fun _ => trivial, fun _ => h ⟨x, rfl⟩⟩
  have hbot : I.comap f = ⊥ :=
    (Scheme.IdealSheafData.support_eq_top_iff).mp htop
  let e := I.comapIso f
  have hfst : IsIso (pullback.fst f I.subschemeι) := by
    have hcomp : e.hom ≫ pullback.fst f I.subschemeι = (I.comap f).subschemeι :=
      Scheme.IdealSheafData.comapIso_hom_fst I f
    have : IsIso (e.hom ≫ pullback.fst f I.subschemeι) := by
      rw [hcomp, hbot]
      infer_instance
    exact IsIso.of_isIso_comp_left e.hom _
  let g := inv (pullback.fst f I.subschemeι) ≫ pullback.snd f I.subschemeι
  refine ⟨g, ?_⟩
  dsimp [g]
  calc
    inv (pullback.fst f I.subschemeι) ≫ pullback.snd f I.subschemeι ≫ I.subschemeι =
        inv (pullback.fst f I.subschemeι) ≫ pullback.fst f I.subschemeι ≫ f := by
          rw [pullback.condition]
    _ = f := by simp


/-- A morphism over the base whose image lies in a closed set factors through its vanishing
ideal. -/
private theorem exists_overHom_factor_through_vanishingIdeal
    {S X : Scheme.{u}} {f : X ⟶ S} {A : Over S} [IsReduced A.left] (a : A ⟶ Over.mk f)
    (T : TopologicalSpace.Closeds X) (I : X.IdealSheafData)
    (hI : I = Scheme.IdealSheafData.vanishingIdeal T) (h : Set.range a.left ⊆ (T : Set X)) :
    ∃ a' : A ⟶ Over.mk (I.subschemeι ≫ f),
      a' ≫ (Over.homMk I.subschemeι : Over.mk (I.subschemeι ≫ f) ⟶ Over.mk f) = a := by
  subst hI
  obtain ⟨g, hg⟩ := exists_factor_through_vanishingIdeal a.left T h
  exact ⟨Over.homMk g (by change g ≫ _ ≫ f = _; rw [← Category.assoc, hg]; exact a.w),
    Over.OverMorphism.ext hg⟩

/-- An irreducible set through the identity lies in every component through the identity. -/
private theorem range_subset_component_of_contains_identity
    {X A : Type u} [TopologicalSpace X] [TopologicalSpace A] [IrreducibleSpace A]
    (f : A → X) (hf : Continuous f) (e : X)
    (he : e ∈ Set.range f)
    (hunique : ∃! Z : irreducibleComponents X, e ∈ (Z : Set X))
    (Z : irreducibleComponents X) (hZ : e ∈ (Z : Set X)) :
    Set.range f ⊆ Z := by
  have hirr : IsIrreducible (Set.range f) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ A).image f hf.continuousOn
  obtain ⟨C, hC, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (Set.range f) hirr
  exact hsub.trans (congrArg Subtype.val (hunique.unique (y₁ := ⟨C, hC⟩) (hsub he) hZ)).le

/-- The underlying space of the reduced subscheme on an irreducible component is the component. -/
private noncomputable def componentHomeo {X : Scheme.{u}} (Z : irreducibleComponents X) :
    (componentIdeal Z.1 Z.2).subscheme ≃ₜ (Z : Set X) :=
  (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (componentIdeal Z.1 Z.2).subschemeIso)).trans
    (componentIdeal Z.1 Z.2).gluedHomeo |>.trans
      (Homeomorph.setCongr (Scheme.IdealSheafData.coe_support_vanishingIdeal _))

/-- An isomorphism over the base induces a homeomorphism of the total spaces. -/
private noncomputable def overIsoHomeo {S : Scheme.{u}} {A B : Over S} (e : A ≅ B) :
    A.left ≃ₜ B.left :=
  TopCat.homeoOfIso (Scheme.forgetToTop.mapIso ((Over.forget S).mapIso e))

/-- A composition identity over the base gives the corresponding identity on points. -/
private theorem left_apply_comp_of_comp_eq {S : Scheme.{u}} {A B C : Over S} {f : A ⟶ B}
    {g : B ⟶ C} {k : A ⟶ C} (h : f ≫ g = k) (x : A.left) : g.left (f.left x) = k.left x := by
  rw [← h]
  rfl

/-- The only point of the tensor unit over `Spec K` is the closed point. -/
private theorem eq_closedPoint_of_tensorUnit {K : Type u} [Field K]
    (s : (𝟙_ (Over (Spec (.of K)))).left) : s = IsLocalRing.closedPoint K :=
  Subsingleton.elim (α := PrimeSpectrum K) _ _

/-- The identity section of a group scheme over a field lies in any set containing the identity
point. -/
private theorem range_identity_subset
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [GrpObj (Over.mk f)]
    (Z : irreducibleComponents X)
    (hidentity : (η[Over.mk f]).left (IsLocalRing.closedPoint k) ∈ (Z : Set X)) :
    Set.range (η[Over.mk f]).left ⊆ (Z : Set X) := by
  rintro _ ⟨s, rfl⟩
  simpa [eq_closedPoint_of_tensorUnit s] using hidentity

/-- The residue fields of the closed points of `X` are algebraic over the base field `K`. -/
private def ResidueAlgebraic (K : Type u) [Field K] (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) :
    Prop :=
  ∀ x : X, x ∈ closedPoints X →
    letI : (f x).asIdeal.IsPrime := (f x).isPrime
    letI := ((CommRingCat.ofHom (algebraMap K (f x).asIdeal.ResidueField)) ≫
      (Scheme.Spec.residueFieldIso (.of K) (f x)).inv ≫ f.residueFieldMap x).hom.toAlgebra
    Algebra.IsAlgebraic K (X.residueField x)

@[sga "3 VIB 1.4.1", sga "3 VIB 2.1"]
private noncomputable def rightTranslation
    {B : Scheme.{u}} (G : Over B) [GrpObj G]
    (p : (𝟙_ (Over B)) ⟶ G) : G ⟶ G :=
  𝟙 G * (toUnit G ≫ p)

private theorem rightTranslation_comp
    {B : Scheme.{u}} (G : Over B) [GrpObj G]
    (p q : (𝟙_ (Over B)) ⟶ G) :
    rightTranslation G p ≫ rightTranslation G q = rightTranslation G (p * q) := by
  have hconst : (toUnit G ≫ p) * (toUnit G ≫ q) = toUnit G ≫ (p * q) := by
    rw [← MonObj.comp_mul (toUnit G) p q]
  calc
    rightTranslation G p ≫ rightTranslation G q =
        (rightTranslation G p ≫ 𝟙 G) *
          (rightTranslation G p ≫ (toUnit G ≫ q)) := MonObj.comp_mul _ _ _
    _ = rightTranslation G p * (toUnit G ≫ q) := by simp
    _ = (𝟙 G * (toUnit G ≫ p)) * (toUnit G ≫ q) := rfl
    _ = 𝟙 G * ((toUnit G ≫ p) * (toUnit G ≫ q)) := by simp [mul_assoc]
    _ = rightTranslation G (p * q) := by
      rw [hconst]
      rfl

@[sga "3 VIB 1.4.1", sga "3 VIB 2.1"]
private noncomputable def rightTranslationIso
    {B : Scheme.{u}} (G : Over B) [GrpObj G]
    (p : (𝟙_ (Over B)) ⟶ G) : G ≅ G where
  hom := rightTranslation G p
  inv := rightTranslation G p⁻¹
  hom_inv_id := by
    rw [rightTranslation_comp, mul_inv_cancel]
    simp [rightTranslation]
  inv_hom_id := by
    rw [rightTranslation_comp, inv_mul_cancel]
    simp [rightTranslation]

private noncomputable def leftTranslateFirst
    {B : Scheme.{u}} (T G : Over B) [GrpObj T] [GrpObj G]
    (p : (𝟙_ (Over B)) ⟶ T) :
  MonoidalCategoryStruct.tensorObj T G ⟶ MonoidalCategoryStruct.tensorObj T G :=
  CategoryTheory.CartesianMonoidalCategory.lift
    (CategoryTheory.CartesianMonoidalCategory.fst T G ≫ leftTranslation T p)
    (CategoryTheory.CartesianMonoidalCategory.snd T G)

private theorem leftTranslateFirst_mul
    {B : Scheme.{u}} (T G : Over B) [GrpObj T] [GrpObj G]
    (ψ : T ⟶ G) [IsMonHom ψ] (p : (𝟙_ (Over B)) ⟶ T) :
    leftTranslateFirst T G p ≫
        (CategoryTheory.CartesianMonoidalCategory.lift
          (CategoryTheory.CartesianMonoidalCategory.fst T G ≫ ψ)
          (CategoryTheory.CartesianMonoidalCategory.snd T G) ≫ μ[G]) =
      (CategoryTheory.CartesianMonoidalCategory.lift
          (CategoryTheory.CartesianMonoidalCategory.fst T G ≫ ψ)
          (CategoryTheory.CartesianMonoidalCategory.snd T G) ≫ μ[G]) ≫
        leftTranslation G (p ≫ ψ) := by
  let a := CategoryTheory.CartesianMonoidalCategory.fst T G ≫ ψ
  let b := CategoryTheory.CartesianMonoidalCategory.snd T G
  have hnat : leftTranslation T p ≫ ψ = ψ ≫ leftTranslation G (p ≫ ψ) := by
    dsimp [leftTranslation]
    rw [MonObj.mul_comp, MonObj.comp_mul]
    simp [Category.assoc]
  have hfst : leftTranslateFirst T G p ≫ a =
      a ≫ leftTranslation G (p ≫ ψ) := by
    calc
      leftTranslateFirst T G p ≫ a =
          (CategoryTheory.CartesianMonoidalCategory.fst T G ≫ leftTranslation T p) ≫ ψ := by
            dsimp [leftTranslateFirst, a]
            rw [CategoryTheory.CartesianMonoidalCategory.lift_fst_assoc]
      _ = (CategoryTheory.CartesianMonoidalCategory.fst T G ≫ ψ) ≫
          leftTranslation G (p ≫ ψ) := by
            rw [Category.assoc, hnat, ← Category.assoc]
      _ = a ≫ leftTranslation G (p ≫ ψ) := rfl
  have hsnd : leftTranslateFirst T G p ≫ b = b := by
    simp [leftTranslateFirst, b]
  rw [show leftTranslateFirst T G p ≫
        (CategoryTheory.CartesianMonoidalCategory.lift
          (CategoryTheory.CartesianMonoidalCategory.fst T G ≫ ψ)
          (CategoryTheory.CartesianMonoidalCategory.snd T G) ≫ μ[G]) =
      CategoryTheory.CartesianMonoidalCategory.lift
          (leftTranslateFirst T G p ≫
            (CategoryTheory.CartesianMonoidalCategory.fst T G ≫ ψ))
          (leftTranslateFirst T G p ≫
            CategoryTheory.CartesianMonoidalCategory.snd T G) ≫ μ[G] by
      rw [CategoryTheory.CartesianMonoidalCategory.comp_lift_assoc]]
  rw [hfst, hsnd]
  simp only [leftTranslation, MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id,
    MonObj.mul_eq_mul, lift_fst, lift_snd, mul_assoc, mul_right_inj]
  rfl

private theorem point_comp_rightTranslation
    {B : Scheme.{u}} (G : Over B) [GrpObj G]
    (p q : (𝟙_ (Over B)) ⟶ G) :
    p ≫ rightTranslation G q = p * q := by
  change p ≫ (𝟙 G * (toUnit G ≫ q)) = p * q
  rw [MonObj.comp_mul]
  simp

@[ega "IV 17.12.7" "partial"]
private theorem point_comp_leftTranslation
    {B : Scheme.{u}} (G : Over B) [GrpObj G]
    (p q : (𝟙_ (Over B)) ⟶ G) :
    p ≫ leftTranslation G q = q * p := by
  change p ≫ ((toUnit G ≫ q) * 𝟙 G) = q * p
  rw [MonObj.comp_mul]
  simp

private theorem image_mem_irreducibleComponents_of_homeomorph
    {X : Type u} [TopologicalSpace X] (h : X ≃ₜ X)
    (Z : irreducibleComponents X) : h '' (Z : Set X) ∈ irreducibleComponents X :=
  image_mem_irreducibleComponents_of_isPreirreducible_fiber h h.continuous h.isOpenMap
    (fun _ => Set.Subsingleton.isPreirreducible fun _ ha _ hb =>
      h.injective ((Set.mem_preimage.mp ha).trans (Set.mem_preimage.mp hb).symm))
    h.surjective Z.property

private theorem exists_compact_open_between
    (X : Scheme.{u}) (A C : Set X)
    (hAcompact : IsCompact A) (hCclosed : IsClosed C) (hdisj : Disjoint A C) :
    ∃ U : X.Opens, A ⊆ U ∧ Disjoint (U : Set X) C ∧ IsCompact (U : Set X) := by
  classical
  let N : X.Opens := ⟨Cᶜ, hCclosed.isOpen_compl⟩
  have hAN : A ⊆ (N : Set X) := fun _ hx hxC => Set.disjoint_left.mp hdisj hx hxC
  have hchoose : ∀ x : A, ∃ V : X.affineOpens,
      (x : X) ∈ (V : Set X) ∧ (V : Set X) ⊆ (N : Set X) := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVN⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (hAN x.property) N.2
    exact ⟨⟨V, hV⟩, hxV, hVN⟩
  choose V hVmem hVsub using hchoose
  have hcover : A ⊆ ⋃ x : A, (V x : Set X) := fun x hx =>
    Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hVmem ⟨x, hx⟩⟩
  obtain ⟨s, hscover⟩ := hAcompact.elim_finite_subcover
    (fun x : A => (V x : Set X)) (fun x => (V x).1.2) hcover
  let Uset : Set X := ⋃ x ∈ s, (V x : Set X)
  have hUopen : IsOpen Uset := isOpen_iUnion fun x => isOpen_iUnion fun _ => (V x).1.2
  have hUcompact : IsCompact Uset :=
    s.finite_toSet.isCompact_biUnion (fun x _ => (V x).2.isCompact)
  have hUsubN : Uset ⊆ (N : Set X) := Set.iUnion₂_subset fun a _ => hVsub a
  exact ⟨⟨Uset, hUopen⟩, hscover, Set.disjoint_left.mpr fun _ hxU hxC => hUsubN hxU hxC,
    hUcompact⟩


/-- Every closed point is the image of a rational point of the group scheme. -/
private theorem exists_point_of_mem_closedPoints
    (K : Type u) [Field K] [IsAlgClosed K] (X : Scheme.{u}) (f : X ⟶ Spec (.of K))
    (x : X) (hxclosed : x ∈ closedPoints X) (hres : ResidueAlgebraic K X f) :
    ∃ px : (𝟙_ (Over (Spec (.of K)))) ⟶ Over.mk f,
      px.left.base (IsLocalRing.closedPoint K) = x := by
  let : (f x).asIdeal.IsPrime := (f x).isPrime
  let : Algebra K (X.residueField x) :=
    ((CommRingCat.ofHom (algebraMap K (f x).asIdeal.ResidueField)) ≫
      (Scheme.Spec.residueFieldIso (.of K) (f x)).inv ≫ f.residueFieldMap x).hom.toAlgebra
  have hxalg : Algebra.IsAlgebraic K (X.residueField x) := hres x hxclosed
  exact ⟨Over.homMk (rationalPointOfClosedPoint K X x hxalg)
      (rationalPointOfClosedPoint_comp K X f x hxalg rfl),
    (congrArg _ (Subsingleton.elim _ _)).trans (rationalPointOfClosedPoint_apply K X x hxalg)⟩

/-- Translating the identity component by a closed rational point reaches every component
through that point. -/
private theorem exists_homeo_component_translate
    (K : Type u) [Field K] [IsAlgClosed K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) [GrpObj (Over.mk f)]
    (Z : irreducibleComponents X)
    (hZ : (η[Over.mk f]).left (IsLocalRing.closedPoint K) ∈ (Z : Set X))
    (x : X) (hxclosed : x ∈ closedPoints X) (hres : ResidueAlgebraic K X f) :
    ∃ (px : (𝟙_ (Over (Spec (.of K)))) ⟶ Over.mk f),
      px.left.base (IsLocalRing.closedPoint K) = x ∧
      ∃ ht : X ≃ₜ X,
        ht ((η[Over.mk f]).left (IsLocalRing.closedPoint K)) = x ∧
        (∀ y, ht y = (rightTranslation (Over.mk f) px).left.base y) ∧
        ∀ C : irreducibleComponents X, x ∈ (C : Set X) → ht '' (Z : Set X) = (C : Set X) := by
  obtain ⟨px, hpx⟩ := exists_point_of_mem_closedPoints K X f x hxclosed hres
  let ht := overIsoHomeo (rightTranslationIso (Over.mk f) px)
  have htrunit : η[Over.mk f] ≫ rightTranslation (Over.mk f) px = px := by
    rw [point_comp_rightTranslation, mul_eq_right]
    exact MonObj.one_eq_one _
  have hte : ht ((η[Over.mk f]).left (IsLocalRing.closedPoint K)) = x :=
    (left_apply_comp_of_comp_eq htrunit _).trans hpx
  refine ⟨px, hpx, ht, hte, fun _ => rfl, fun C hxC => ?_⟩
  let C' : irreducibleComponents X :=
    ⟨ht.symm '' (C : Set X), image_mem_irreducibleComponents_of_homeomorph ht.symm C⟩
  have hC' := congrArg Subtype.val
    ((existsUnique_irreducibleComponent_containing_identity f).unique
      (y₁ := C') ⟨x, hxC, ht.symm_apply_eq.mpr hte.symm⟩ hZ)
  rw [← hC']
  ext y
  simp [C']

/-- Two components meeting in a closed point of a Jacobson group scheme coincide. -/
private theorem irreducibleComponent_eq_of_intersection
    (K : Type u) [Field K] [IsAlgClosed K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) [GrpObj (Over.mk f)]
    [JacobsonSpace X]
    (Z Z' : irreducibleComponents X)
    (hinter : ((Z : Set X) ∩ (Z' : Set X)).Nonempty)
    (hres : ResidueAlgebraic K X f) :
    Z' = Z := by
  obtain ⟨x, ⟨hxZ, hxZ'⟩, hxclosed⟩ := nonempty_inter_closedPoints hinter
    ((isClosed_of_mem_irreducibleComponents _ Z.property).inter
      (isClosed_of_mem_irreducibleComponents _ Z'.property)).isLocallyClosed
  obtain ⟨Z₀, hZ₀⟩ := (existsUnique_irreducibleComponent_containing_identity f).exists
  obtain ⟨_, _, _, _, _, himage⟩ :=
    exists_homeo_component_translate K X f Z₀ hZ₀ x hxclosed hres
  exact Subtype.ext ((himage Z' hxZ').symm.trans (himage Z hxZ))

private theorem exists_closed_subgroup_on_identity_component
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [GrpObj (Over.mk f)]
    (Z : irreducibleComponents X)
    (hidentity : (η[Over.mk f]).left (IsLocalRing.closedPoint k) ∈ (Z : Set X)) :
    ∃ (K : ClosedSubgroupScheme (Grp.mk (Over.mk f)))
      (e : (Over.mk ((componentIdeal Z.1 Z.2).subschemeι ≫ f)) ≅ K.carrier.X),
      Over.homMk (componentIdeal Z.1 Z.2).subschemeι = e.hom ≫ K.ι.hom.hom := by
  classical
  let U : Over (Spec (.of k)) := Over.mk f
  have hunitRange := range_identity_subset k X f Z hidentity
  let T : TopologicalSpace.Closeds X :=
    ⟨(Z : Set X), isClosed_of_mem_irreducibleComponents _ Z.property⟩
  let I := componentIdeal Z.1 Z.2
  let H : Over (Spec (.of k)) := Over.mk (I.subschemeι ≫ f)
  let j : H ⟶ U := Over.homMk I.subschemeι
  have hjClosed : IsClosedImmersion j.left := by
    change IsClosedImmersion I.subschemeι
    infer_instance
  have : IrreducibleSpace I.subscheme :=
    ((componentHomeo Z).irreducibleSpace_iff).2 (Subtype.irreducibleSpace Z.property.1)
  have : IsReduced I.subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal T
  let : IrreducibleSpace H.left := by
    change IrreducibleSpace I.subscheme
    infer_instance
  let : IsReduced H.left := by
    change IsReduced I.subscheme
    infer_instance
  let hgeom :=
    geometricallyIrreducible_irreducibleComponent_of_identity
      k X f Z (by simpa using hunitRange)
  let p := I.subschemeι ≫ f
  let : GeometricallyIrreducible p := by simpa [p, I, componentIdeal] using hgeom
  let : UniversallyOpen p := by infer_instance
  have : PerfectField k := inferInstance
  let D := MonoidalCategoryStruct.tensorObj H H
  have : IrreducibleSpace D.left := by
    change IrreducibleSpace ↥(CategoryTheory.Limits.pullback p p)
    infer_instance
  have : IsReduced D.left := by
    change IsReduced (CategoryTheory.Limits.pullback p p)
    exact isReduced_pullback_over_perfectField
      p p
  have : IsReduced ((𝟙_ (Over (Spec (.of k)))).left) := by
    change IsReduced (Spec (.of k))
    infer_instance
  obtain ⟨e, he⟩ := exists_overHom_factor_through_vanishingIdeal η[U] T I rfl hunitRange
  let m : D ⟶ U := (j ⊗ₘ j) ≫ μ[U]
  let w : (𝟙_ (Over (Spec (.of k)))) ⟶ D :=
    (MonoidalCategoryStruct.leftUnitor (𝟙_ (Over (Spec (.of k))))).inv ≫ (e ⊗ₘ e)
  have hten := tensorHom_comp_tensorHom e e j j
  have hw : w ≫ m = η[U] := by
    dsimp [w, m, D]
    simp only [Category.assoc]
    rw [← Category.assoc (e ⊗ₘ e) (j ⊗ₘ j) μ[U], hten, he, MonObj.one_mul_hom,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have huniq := existsUnique_irreducibleComponent_containing_identity f
  have hmRange : Set.range m.left ⊆ (Z : Set X) :=
    range_subset_component_of_contains_identity m.left m.left.continuous
      ((η[U]).left (IsLocalRing.closedPoint k))
      ⟨w.left (IsLocalRing.closedPoint k), left_apply_comp_of_comp_eq hw _⟩ huniq Z hidentity
  obtain ⟨m', hm'⟩ := exists_overHom_factor_through_vanishingIdeal m T I rfl hmRange
  have hinvRange : Set.range (j ≫ ι[U]).left ⊆ (Z : Set X) :=
    range_subset_component_of_contains_identity (j ≫ ι[U]).left (j ≫ ι[U]).left.continuous
      ((η[U]).left (IsLocalRing.closedPoint k))
      ⟨e.left (IsLocalRing.closedPoint k),
        left_apply_comp_of_comp_eq (by rw [← Category.assoc, he]; simp) _⟩
      huniq Z hidentity
  obtain ⟨i, hi⟩ := exists_overHom_factor_through_vanishingIdeal (j ≫ ι[U]) T I rfl hinvRange
  exact (isClosedSubgroupScheme_iff_factor (Grp.mk U) j).2 ⟨⟨e, he⟩, ⟨m', hm'⟩, ⟨i, hi⟩⟩

private theorem exists_rational_point_lift_to_identityComponent
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [GrpObj (Over.mk f)]
    (Z : irreducibleComponents X)
    (H : Over (Spec (.of k))) (e : (Over.mk ((componentIdeal Z.1 Z.2).subschemeι ≫ f)) ≅ H)
    (ψ : H ⟶ Over.mk f)
    (hψ : Over.homMk (componentIdeal Z.1 Z.2).subschemeι = e.hom ≫ ψ)
    (x : X) (hxclosed : x ∈ closedPoints X) (hxZ : x ∈ (Z : Set X))
    (hres : ResidueAlgebraic k X f) :
    ∃ p : (𝟙_ (Over (Spec (.of k)))) ⟶ H,
      (p ≫ ψ).left.base (IsLocalRing.closedPoint k) = x := by
  obtain ⟨px, hpx⟩ := exists_point_of_mem_closedPoints k X f x hxclosed hres
  have : IsReduced ((𝟙_ (Over (Spec (.of k)))).left) := by
    change IsReduced (Spec (.of k))
    infer_instance
  obtain ⟨q, hq⟩ := exists_overHom_factor_through_vanishingIdeal px
    ⟨(Z : Set X), isClosed_of_mem_irreducibleComponents _ Z.property⟩ (componentIdeal Z.1 Z.2) rfl
    (by
      rintro _ ⟨s, rfl⟩
      rw [eq_closedPoint_of_tensorUnit s]
      exact hpx ▸ hxZ)
  refine ⟨q ≫ e.hom, ?_⟩
  rw [Category.assoc, ← hψ, hq]
  exact hpx

private theorem isCompact_identityComponent
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [GrpObj (Over.mk f)]
    (Z : irreducibleComponents X)
    (hidentity : (η[Over.mk f]).left (IsLocalRing.closedPoint k) ∈ (Z : Set X)) :
    IsCompact (Z : Set X) := by
  obtain ⟨K, e, _⟩ := exists_closed_subgroup_on_identity_component k X f Z hidentity
  have : IrreducibleSpace K.carrier.X.left :=
    (overIsoHomeo e).irreducibleSpace_iff.1
      ((componentHomeo Z).irreducibleSpace_iff.2 (Subtype.irreducibleSpace Z.property.1))
  have : CompactSpace K.carrier.X.left :=
    compactSpace_of_irreducibleSpace_grpObj k K.carrier.X
  have : CompactSpace (componentIdeal Z.1 Z.2).subscheme :=
    Homeomorph.compactSpace (overIsoHomeo e).symm
  have : CompactSpace (Z : Set X) := Homeomorph.compactSpace (componentHomeo Z)
  simpa using (isCompact_range continuous_subtype_val :
    IsCompact (Set.range (fun x : (Z : Set X) => (x : X))))

@[sga "3 VIA 2.6.5" "(iii)"]
private theorem irreducibleSpace_of_connected_jacobson_group
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [GrpObj (Over.mk f)]
    [ConnectedSpace X] [JacobsonSpace X]
    (hres : ResidueAlgebraic k X f) :
    IrreducibleSpace X := by
  classical
  let huniq :=
    existsUnique_irreducibleComponent_containing_identity f
  let Z : irreducibleComponents X := Classical.choose huniq
  have hidentity : (η[Over.mk f]).left (IsLocalRing.closedPoint k) ∈ (Z : Set X) :=
    huniq.choose_spec.1
  by_contra hnot
  have hZne : (Z : Set X) ≠ Set.univ := by
    intro htop
    have hX : IrreducibleSpace X := by
      have hpre : IsPreirreducible (Set.univ : Set X) := by
        rw [← htop]
        exact Z.property.1.2
      exact {
        isPreirreducible_univ := hpre
        toNonempty := ⟨(η[Over.mk f]).left (IsLocalRing.closedPoint k)⟩
      }
    exact hnot hX
  have hnotSub : ¬(Set.univ : Set X) ⊆ (Z : Set X) := fun h => hZne (Set.univ_subset_iff.mp h)
  obtain ⟨x, _, hxnot⟩ := Set.not_subset.mp hnotSub
  let Z' : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  have hxZ' : x ∈ (Z' : Set X) := mem_irreducibleComponent
  have hclosedZ' : IsClosed (Z' : Set X) := isClosed_of_mem_irreducibleComponents _ Z'.property
  have hdisj : Disjoint (Z : Set X) (Z' : Set X) := Set.disjoint_left.mpr fun y hyZ hyZ' =>
    hxnot (irreducibleComponent_eq_of_intersection k X f Z Z' ⟨y, hyZ, hyZ'⟩ hres ▸ hxZ')
  have hZcompact : IsCompact (Z : Set X) :=
    isCompact_identityComponent k X f Z hidentity
  obtain ⟨U, hZU, hUZ', hUcompact⟩ :=
    exists_compact_open_between X (Z : Set X) (Z' : Set X)
      hZcompact hclosedZ' hdisj
  obtain ⟨H, eH, hH⟩ := exists_closed_subgroup_on_identity_component k X f Z hidentity
  let G : Over (Spec (.of k)) := Over.mk f
  let T : Over (Spec (.of k)) := H.carrier.X
  let ψ : T ⟶ G := H.ι.hom.hom
  let D := MonoidalCategoryStruct.tensorObj T G
  let m : D ⟶ G :=
    CategoryTheory.CartesianMonoidalCategory.lift
      (CategoryTheory.CartesianMonoidalCategory.fst T G ≫ ψ)
      (CategoryTheory.CartesianMonoidalCategory.snd T G) ≫ μ[G]
  let W : Set X := Set.image
    (CategoryTheory.CartesianMonoidalCategory.lift
      (CategoryTheory.CartesianMonoidalCategory.fst T G ≫ ψ)
      (CategoryTheory.CartesianMonoidalCategory.snd T G) ≫ μ[G]).left.base
    ((CategoryTheory.CartesianMonoidalCategory.snd T G).left.base ⁻¹' (U : Set X))
  have hWopen : IsOpen W := by
    simpa [W, G, T, ψ] using isOpen_image_mul_of_open G T ψ U
  let Hscheme : Over (Spec (.of k)) := Over.mk ((componentIdeal Z.1 Z.2).subschemeι ≫ f)
  have : CompactSpace (Z : Set X) := isCompact_iff_compactSpace.mp hZcompact
  have : CompactSpace Hscheme.left := Homeomorph.compactSpace (componentHomeo Z).symm
  have : CompactSpace T.left := Homeomorph.compactSpace (overIsoHomeo eH)
  have : QuasiCompact T.hom := inferInstance
  have : QuasiCompact ((snd T G).left) := by
    change QuasiCompact (pullback.snd T.hom f)
    infer_instance
  have hprecompact : IsCompact ((snd T G).left ⁻¹ᵁ U : Set D.left) :=
    (snd T G).left.isCompact_preimage hUcompact
  have hWcompact : IsCompact W := by
    change IsCompact (Set.image m.left.base ((snd T G).left.base ⁻¹' (U : Set X)))
    simpa [m] using hprecompact.image m.left.continuous
  have hqsecond (p : (𝟙_ (Over (Spec (.of k)))) ⟶ T) :
      leftTranslateFirst T G p ≫ snd T G = snd T G := by
    simp [leftTranslateFirst]
  have hWstable (p : (𝟙_ (Over (Spec (.of k)))) ⟶ T) :
      ∀ x ∈ W, (leftTranslation G (p ≫ ψ)).left.base x ∈ W := by
    intro x hx
    obtain ⟨d, hdu, hd⟩ := (Set.mem_image _ _ _).mp hx
    refine ⟨(leftTranslateFirst T G p).left.base d, ?_, ?_⟩
    · change (snd T G).left _ ∈ (U : Set X)
      rwa [left_apply_comp_of_comp_eq (hqsecond p) d]
    · rw [← hd]
      exact left_apply_comp_of_comp_eq (leftTranslateFirst_mul T G ψ p) d
  have hcomponentSubsetW (C : irreducibleComponents X)
      (hCW : ((C : Set X) ∩ W).Nonempty) : (C : Set X) ⊆ W := by
    classical
    have hCl : IsClosed (C : Set X) := isClosed_of_mem_irreducibleComponents _ C.property
    obtain ⟨x, hxCW, hxclosed⟩ := nonempty_inter_closedPoints hCW
      (hCl.isLocallyClosed.inter hWopen.isLocallyClosed)
    have hxC : x ∈ (C : Set X) := hxCW.1
    have hxW : x ∈ W := hxCW.2
    obtain ⟨px, hpx, ht, -, hteval, hCimage⟩ :=
      exists_homeo_component_translate k X f Z hidentity x hxclosed hres
    by_contra hsub
    obtain ⟨y, hyC, hyWc⟩ := Set.not_subset.mp hsub
    have hbad : ((C : Set X) ∩ Wᶜ).Nonempty := ⟨y, hyC, hyWc⟩
    obtain ⟨y, hybad, hyclosed⟩ := nonempty_inter_closedPoints hbad
      (hCl.inter hWopen.isClosed_compl).isLocallyClosed
    have hyC' : y ∈ (C : Set X) := hybad.1
    have hyWc' : y ∈ Wᶜ := hybad.2
    have hyimage : y ∈ ht '' (Z : Set X) := by rw [hCimage C hxC]; exact hyC'
    obtain ⟨z, hzZ, hzy⟩ := hyimage
    have hzclosed : z ∈ closedPoints X := by
      apply mem_closedPoints_iff.mpr
      have hpre : ht ⁻¹' ({y} : Set X) = {z} := by
        ext a
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · intro ha
          apply ht.injective
          rw [hzy, ha]
        · rintro rfl
          exact hzy
      rw [← hpre]
      exact hyclosed.preimage ht.continuous
    obtain ⟨p, hp⟩ := exists_rational_point_lift_to_identityComponent
      k X f Z T eH ψ hH z hzclosed hzZ hres
    have hsections : (p ≫ ψ) ≫ rightTranslation G px =
        px ≫ leftTranslation G (p ≫ ψ) :=
      (point_comp_rightTranslation G (p ≫ ψ) px).trans
        (point_comp_leftTranslation G px (p ≫ ψ)).symm
    have heval : (rightTranslation G px).left.base z =
        (leftTranslation G (p ≫ ψ)).left.base x := by
      have h := left_apply_comp_of_comp_eq hsections (IsLocalRing.closedPoint k)
      change (rightTranslation G px).left.base
          ((p ≫ ψ).left.base (IsLocalRing.closedPoint k)) =
        (leftTranslation G (p ≫ ψ)).left.base
          (px.left.base (IsLocalRing.closedPoint k)) at h
      rwa [hp, hpx] at h
    have htranslated : ht z ∈ W := by
      rw [hteval z, heval]
      exact hWstable p x hxW
    exact hyWc' (hzy ▸ htranslated)
  have : X.IsSeparated :=
    isSeparated_of_groupScheme_over_field (Grp.mk G)
  have : QuasiSeparatedSpace X := inferInstance
  let Wopen : X.Opens := ⟨W, hWopen⟩
  have : CompactSpace Wopen.toScheme := by
    change CompactSpace (W : Set X)
    exact isCompact_iff_compactSpace.mp hWcompact
  let g : Wopen.toScheme ⟶ X := Wopen.ι
  have : QuasiCompact g := inferInstance
  have hgrange : Set.range g.base = W := by
    simp [g, Wopen]
  have hgrangeImage : Set.range g.base ⊆ Set.range g.imageι.base := by
    rintro y ⟨y', rfl⟩
    exact ⟨g.toImage y', congrArg (fun h : Wopen.toScheme ⟶ X => h y') g.toImage_imageι⟩
  have hWclosed : IsClosed W := by
    rw [← closure_eq_iff_isClosed]
    refine Set.Subset.antisymm ?_ subset_closure
    intro x hxcl
    have hxImage : x ∈ Set.range g.imageι.base := by
      apply (g.imageι.isClosedEmbedding.isClosed_range.closure_subset_iff.mpr hgrangeImage)
      simpa [hgrange] using hxcl
    obtain ⟨z, hz⟩ := hxImage
    have hxEq : x = g.imageι.base z := hz.symm
    obtain ⟨yw, hspec⟩ := AlgebraicGeometry.exists_specializes_of_image_point g z
    let y : X := g yw
    have hyW : y ∈ W := by
      rw [← hgrange]
      exact ⟨yw, rfl⟩
    have hspec' : y ⤳ g.imageι.base z := by simpa [y] using hspec
    let Cx : irreducibleComponents X := ⟨irreducibleComponent x,
      irreducibleComponent_mem_irreducibleComponents x⟩
    let Cy : irreducibleComponents X := ⟨irreducibleComponent y,
      irreducibleComponent_mem_irreducibleComponents y⟩
    have hxCx : x ∈ (Cx : Set X) := mem_irreducibleComponent
    have hyCy : y ∈ (Cy : Set X) := mem_irreducibleComponent
    have hxCy : x ∈ (Cy : Set X) := by
      have hspecCy := (specializes_iff_forall_closed.mp hspec')
        (Cy : Set X) (isClosed_of_mem_irreducibleComponents _ Cy.property) hyCy
      exact hxEq.symm ▸ hspecCy
    have hcompEq := irreducibleComponent_eq_of_intersection k X f Cy Cx
      ⟨x, hxCy, hxCx⟩ hres
    have hyCx : y ∈ (Cx : Set X) := hcompEq.symm ▸ hyCy
    exact hcomponentSubsetW Cx ⟨y, hyCx, hyW⟩ hxCx
  have hgeom : GeometricallyIrreducible Hscheme.hom :=
    geometricallyIrreducible_irreducibleComponent_of_identity k X f Z
      (range_identity_subset k X f Z hidentity)
  have : GeometricallyIrreducible T.hom := by
    let eS : Hscheme.left ≅ T.left := (Over.forget _).mapIso eH
    have sq : IsPullback eS.inv T.hom Hscheme.hom (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by
        change eH.inv.left ≫ Hscheme.hom = T.hom ≫ 𝟙 _
        simpa only [Category.comp_id] using eH.inv.w⟩
    exact MorphismProperty.of_isPullback sq hgeom
  have : GeometricallyIrreducible (snd T G).left := by
    change GeometricallyIrreducible (pullback.snd T.hom G.hom)
    infer_instance
  have : UniversallyOpen T.hom := inferInstance
  have : UniversallyOpen (snd T G).left := by
    change UniversallyOpen (pullback.snd T.hom G.hom)
    infer_instance
  let j : G ⟶ D := lift (toUnit G ≫ η[T]) (𝟙 G)
  have hjsecond : j ≫ snd T G = 𝟙 G := by simp [j]
  have hjmul : j ≫ m = 𝟙 G := by
    simp only [j, m, comp_lift_assoc, lift_fst_assoc, lift_snd,
      Category.assoc, IsMonHom.one_hom]
    change (1 : G ⟶ G) * 𝟙 G = 𝟙 G
    exact one_mul _
  have hpreserves (C : irreducibleComponents X) :
      m.left '' ((snd T G).left ⁻¹' (C : Set X)) ⊆ (C : Set X) := by
    have hirr := ((snd T G).left.isIrreducible_preimage
      (snd T G).left.isOpenMap C.property.1).image m.left m.left.continuous.continuousOn
    apply C.property.2 hirr
    intro y hy
    refine ⟨j.left y, ?_, ?_⟩
    · change (snd T G).left (j.left y) ∈ (C : Set X)
      rwa [left_apply_comp_of_comp_eq hjsecond y]
    · exact left_apply_comp_of_comp_eq hjmul y
  let v : D ⟶ D := lift (fst T G ≫ ι[T]) m
  have hvsecond : v ≫ snd T G = m := by simp [v]
  have hvmul : v ≫ m = snd T G := by
    simp only [v, m, comp_lift_assoc, lift_fst_assoc, lift_snd]
    change ((fst T G ≫ ι[T]) ≫ ψ) *
      ((fst T G ≫ ψ) * snd T G) = snd T G
    rw [Category.assoc, GrpObj.inv_hom, ← Category.assoc]
    change (fst T G ≫ ψ)⁻¹ * ((fst T G ≫ ψ) * snd T G) = snd T G
    exact inv_mul_cancel_left _ _
  have hWdisjoint : Disjoint W (Z' : Set X) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨d, hdU, hdy⟩ hy
    have hvC : (snd T G).left (v.left d) ∈ (Z' : Set X) := by
      rw [left_apply_comp_of_comp_eq hvsecond d]
      exact hdy.symm ▸ hy
    have hsecondC := hpreserves Z' ⟨v.left d, hvC, rfl⟩
    rw [left_apply_comp_of_comp_eq hvmul d] at hsecondC
    exact Set.disjoint_left.mp hUZ' hdU hsecondC
  have hWnonempty : W.Nonempty := by
    let y := (η[G]).left (IsLocalRing.closedPoint k)
    refine ⟨y, j.left y, ?_, ?_⟩
    · change (snd T G).left (j.left y) ∈ (U : Set X)
      rw [left_apply_comp_of_comp_eq hjsecond y]
      exact hZU hidentity
    · exact left_apply_comp_of_comp_eq hjmul y
  have hWtop : W = Set.univ := IsClopen.eq_univ ⟨hWclosed, hWopen⟩ hWnonempty
  exact Set.disjoint_left.mp hWdisjoint (hWtop ▸ Set.mem_univ x) hxZ'

@[sga "3 VIA 2.4" "(i), special case", sga "3 VIA 2.6.5" "(iii)"]
private theorem irreducibleSpace_of_connected_groupScheme
    (k : Type u) [Field k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [GrpObj (Over.mk f)]
    [ConnectedSpace X] : IrreducibleSpace X := by
  classical
  let s : Spec (.of k) ⟶ X :=
    (Over.tensorUnit_left (C := Scheme) (X := Spec (.of k))).symm ▸
      (η[Over.mk f]).left
  have hs : s ≫ f = 𝟙 _ := by
    dsimp [s]
    exact Over.Hom.w (η[Over.mk f])
  let hgc : GeometricallyConnected f :=
    geometricallyConnected_of_connectedSpace_of_section f s hs
  let : GeometricallyConnected f := hgc
  obtain ⟨κJ, hJ⟩ :=
    jacobsonSpace_pullback_of_large_cardinality k X f
  obtain ⟨κR, hR⟩ :=
    exists_cardinal_isAlgebraic_residueField_of_mem_closedPoints_baseChange
      k X f
  let κ := max κJ κR
  let K := largeAlgebraicallyClosedField k κ
  let : Field K := by dsimp [K, largeAlgebraicallyClosedField]; infer_instance
  let : IsAlgClosed K := by dsimp [K, largeAlgebraicallyClosedField]; infer_instance
  let : Algebra k K := by dsimp [K, largeAlgebraicallyClosedField]; infer_instance
  have hKlarge := cardinal_le_largeAlgebraicallyClosedField k κ
  have hKJ : κJ ≤ Cardinal.mk K := by
    simpa [K, κ] using (le_max_left κJ κR).trans hKlarge
  have hKR : κR ≤ Cardinal.mk K := by
    simpa [K, κ] using (le_max_right κJ κR).trans hKlarge
  let g : Spec (.of K) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  let XK : Scheme.{u} := pullback f g
  let fK : XK ⟶ Spec (.of K) := pullback.snd f g
  have : JacobsonSpace XK := hJ K hKJ
  have hres : ResidueAlgebraic K XK fK := fun x hx => hR K hKR x hx
  have : GrpObj (Over.mk fK) := by
    dsimp [fK, XK]
    exact Over.grpObjMkPullbackSnd
  let : ConnectedSpace XK := hgc.geometrically_connectedSpace (K := K) g
    (pullback.fst f g) (pullback.snd f g) (IsPullback.of_hasPullback f g)
  let : IrreducibleSpace XK :=
    irreducibleSpace_of_connected_jacobson_group K XK fK hres
  have : Surjective g := ⟨fun y => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  exact Function.Surjective.irreducibleSpace (pullback.fst f g).continuous
    (by simpa only [surjective_iff] using
      (inferInstance : Surjective (pullback.fst f g)))

/-- A connected group scheme over a field is irreducible. -/
@[stacks 0B7Q,
  sga "3 VIB 5.8.1" "X = G acting on itself",
  sga "3 VIA 2.4" "(i), special case",
  sga "3 VIA 2.6.5" "(iii)"]
theorem irreducibleSpace_of_connectedSpace
    {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
    [ConnectedSpace G.left] : IrreducibleSpace G.left := by
  have hG : G = Over.mk G.hom := by cases G; rfl
  let : GrpObj (Over.mk G.hom) := hG ▸ (inferInstance : GrpObj G)
  exact irreducibleSpace_of_connected_groupScheme k G.left G.hom

end AlgebraicGeometry

end

@[expose] public section
open CategoryTheory CategoryTheory.CartesianMonoidalCategory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Stacks.AlgebraicGeometry.ClosedPointResidue
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry
universe u

private theorem point_comp_mulRight
    {B : Scheme.{u}} (G : Over B) [GrpObj G]
    (p q : (𝟙_ (Over B)) ⟶ G) :
    p ≫ (GrpObj.mulRight q).hom = p * q :=
  point_comp_rightTranslation G p q

end AlgebraicGeometry
end
