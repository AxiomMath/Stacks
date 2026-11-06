module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleSummandNoSliceSheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleSummandSheafify
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Small

/-!
# Invertible modules on a ringed site form a set

Let `O` be a sheaf of commutative rings on a site `(C, J)`, with `C : Type u`,
`Category.{v} C` and sections in universe `w`. This file proves that the isomorphism classes of
invertible sheaves of `O`-modules form a *set* of size `max u v w`: the class
`Stacks.SheafOfModules.IsInvertible O hO` is
`CategoryTheory.ObjectProperty.EssentiallySmall.{max u v w}`.

## Main definitions

* `Stacks.SheafOfModules.InvertibleSmall.HasCoordsAt`: the sections of `L` over an object admit
  countably many `O`-linear coordinate functions to the structure sheaf which jointly detect the
  zero section.
* `Stacks.SheafOfModules.InvertibleSmall.HasCoordsCover`: every object of the site has a
  covering family on whose members `L` has detecting coordinates.
* `Stacks.SheafOfModules.InvertibleSmall.coordMap`: the complete coordinate invariant of a
  section — all coordinates of all of its restrictions. Its values lie in a type of size
  `max u v w` that does not depend on `L`, and this is what makes the set of isomorphism classes
  small.

## Main results

* `Stacks.SheafOfModules.InvertibleSmall.exists_detecting_of_isSplitMono`: a split monomorphism
  into a finite product of copies of the structure sheaf yields finitely many morphisms to the
  structure sheaf which jointly detect zero on sections over every object.
* `Stacks.SheafOfModules.InvertibleSmall.coordMap_injective` and
  `Stacks.SheafOfModules.InvertibleSmall.isoOfCoordRangeEq`: the coordinate invariant is
  injective on sections, and two sheaves of modules whose coordinate ranges agree over every
  object are isomorphic. Together these say that the coordinate ranges are a complete invariant.
* `Stacks.SheafOfModules.essentiallySmall_of_hasCoordsCover`: any property of sheaves of modules
  all of whose members have a covering family with detecting coordinates is essentially small at
  `max u v w`.
* `Stacks.SheafOfModules.essentiallySmall_isInvertible` and
  `Stacks.SheafOfModules.essentiallySmall_isInvertible_algebraicGeometry`: the isomorphism
  classes of invertible sheaves of modules form a set of size `max u v w`, for each of the two
  invertibility classes of Tag 01CS.

## Implementation notes

**The universe, and why it is `max u v w`.** A section of `L` over `X` is sent to the family of
all values `θ (L(f)(s))`, indexed by an object `V` of the site, an arrow `f : X ⟶ V` of `Cᵒᵖ`
and a natural number, where `θ` runs over a chosen countable family of coordinate functions at
`V`. That index type has size `max u v`, and the values are sections of the structure sheaf, of
size `w`; so the coordinate space is of size `max u v w` and so is the type of its subsets.
A sheaf of modules carries sections in `Type w`, so for `max u v > w` its *sections* cannot be
replaced by subsets of the coordinate space — which is why the proof does not transport the
module along a bijection, but instead uses the coordinate ranges as a complete invariant and
selects a representative of each isomorphism class by choice. Nothing here needs `max u v ≤ w`.

**What invertibility is used for.** Only the production of local coordinates. The Stacks proof
of Tag 040B defers to the ringed-space Lemma 01CW, which produces local data from the fact that
an invertible module is locally a direct summand of a finite free module. That statement is
Tag 0B8N (b), available on a site as
`Stacks.SheafOfModules.exists_cover_isDirectSummand_finiteFree`; the split monomorphism it
produces over the slice site is read at the terminal object of that site, where the
identifications of the module, the structure sheaf and their sections are all definitional, and
its components are the coordinate functions. A split monomorphism is sectionwise injective
because the sum of the composites of the projections with the insertions is the identity, so the
components detect zero with no computation of the sections of the product.

**The hypotheses this adds to the tag, and why.**
`exists_cover_isDirectSummand_finiteFree` assumes `HasWeakSheafify J AddCommGrpCat.{w}`,
`J.WEqualsLocallyBijective AddCommGrpCat.{w}` and
`∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}`. The third is not derivable from
the second in the pinned Mathlib: the general instance for a concrete category requires the
section universe to be `max u v` of the site, which is not assumed here. So
`essentiallySmall_isInvertible` carries all three, and the `@[stacks 040B]` attribute is
*withheld* from it — Tag 040B assumes none of them.
`essentiallySmall_of_hasCoordsCover` assumes none of them and is the form into which a
hypothesis-free Tag 0B8N (b) would fold.

## References

* [Stacks Project, Tag 040B](https://stacks.math.columbia.edu/tag/040B)
* [Stacks Project, Tag 01CW](https://stacks.math.columbia.edu/tag/01CW)
* [Stacks Project, Tag 0B8N](https://stacks.math.columbia.edu/tag/0B8N)
-/

@[expose] public section

open CategoryTheory Opposite Limits MonoidalCategory

universe v u w

namespace Stacks.SheafOfModules.InvertibleSmall

section Detect

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- The identity of a finite product of copies of one object is the sum of the composites of the
projections with the insertions. -/
private lemma sum_pi_eq_id {n : ℕ} (G : SheafOfModules.{w} R) :
    ∑ j : Fin n, Pi.π (fun _ : Fin n ↦ G) j ≫
        Pi.lift (fun k : Fin n ↦ if j = k then 𝟙 G else 0) = 𝟙 (∏ᶜ fun _ : Fin n ↦ G) := by
  classical
  refine Pi.hom_ext _ _ (fun k ↦ ?_)
  rw [Preadditive.sum_comp, Category.id_comp]
  have h : ∀ j : Fin n, (Pi.π (fun _ : Fin n ↦ G) j ≫
      Pi.lift (fun k : Fin n ↦ if j = k then 𝟙 G else 0)) ≫ Pi.π _ k
      = if j = k then Pi.π (fun _ : Fin n ↦ G) k else 0 := by
    intro j
    rw [Category.assoc, Pi.lift_comp_π]
    by_cases hjk : j = k
    · subst hjk; simp
    · simp [hjk]
  rw [Finset.sum_congr rfl (fun j _ ↦ h j), Finset.sum_ite_eq' Finset.univ k
    (fun _ ↦ Pi.π (fun _ : Fin n ↦ G) k)]
  simp

/-- A split monomorphism into a finite product of copies of the structure sheaf yields finitely
many morphisms to the structure sheaf which jointly detect the zero section over every object of
the site. -/
theorem exists_detecting_of_isSplitMono {A : SheafOfModules.{w} R} {n : ℕ}
    (s : A ⟶ ∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit R) [IsSplitMono s] :
    ∃ α : Fin n → (A ⟶ SheafOfModules.unit R),
      ∀ (X : Cᵒᵖ) (x : ToType (A.val.obj X)), (∀ j, (α j).val.app X x = 0) → x = 0 := by
  classical
  refine ⟨fun j ↦ s ≫ Pi.π _ j, fun X x hx ↦ ?_⟩
  set ρ : Fin n → (SheafOfModules.unit R ⟶ A) := fun j ↦
    Pi.lift (fun k : Fin n ↦ if j = k then 𝟙 (SheafOfModules.unit R) else 0) ≫ retraction s
    with hρ
  have key : ∑ j : Fin n, (s ≫ Pi.π _ j) ≫ ρ j = 𝟙 A := by
    simp only [hρ, Category.assoc]
    rw [← Preadditive.comp_sum]
    simp only [← Category.assoc]
    rw [← Preadditive.sum_comp, sum_pi_eq_id, Category.id_comp, IsSplitMono.id]
  have hid : x = ∑ j : Fin n, ((s ≫ Pi.π _ j) ≫ ρ j).val.app X x := by
    conv_lhs => rw [show x = (𝟙 A : A ⟶ A).val.app X x from rfl]
    rw [← key]
    exact app_sum Finset.univ _ X x
  rw [hid]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  show (ρ j).val.app X ((s ≫ Pi.π _ j).val.app X x) = 0
  rw [hx j, map_zero]

end Detect

section Coords

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)}

/-- The sections of the structure sheaf over `X`, as a module over itself: the target of a
coordinate function. -/
noncomputable abbrev unitObj (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
      (X : Cᵒᵖ) :=
  (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).val.obj X

variable (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))

/-- `L` admits countably many coordinate functions over `X` which jointly detect the zero
section. -/
def HasCoordsAt (X : Cᵒᵖ) : Prop :=
  ∃ θ : ℕ → (L.val.obj X ⟶ unitObj O hO X),
    ∀ x : ToType (L.val.obj X), (∀ j, θ j x = 0) → x = 0

/-- Every object of the site has a covering family on whose members `L` has detecting
coordinates. -/
def HasCoordsCover : Prop :=
  ∀ X : Cᵒᵖ, ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ X.unop),
    Sieve.generate (Presieve.ofArrows V f) ∈ J X.unop ∧ ∀ i, HasCoordsAt L (op (V i))

/-- A countable family of coordinate functions at `X`, detecting the zero section whenever `L`
has coordinates at `X`: the chosen one if there is any, and the zero family otherwise. -/
lemma exists_coordFamily (X : Cᵒᵖ) :
    ∃ θ : ℕ → (L.val.obj X ⟶ unitObj O hO X),
      HasCoordsAt L X → ∀ x : ToType (L.val.obj X), (∀ j, θ j x = 0) → x = 0 := by
  by_cases h : HasCoordsAt L X
  · obtain ⟨θ, hθ⟩ := h
    exact ⟨θ, fun _ ↦ hθ⟩
  · exact ⟨fun _ ↦ 0, fun h' ↦ absurd h' h⟩

/-- A chosen countable family of coordinate functions on the sections of `L` over `X`. It detects
the zero section exactly when `L` has coordinates at `X`. -/
noncomputable def coord (X : Cᵒᵖ) (j : ℕ) : L.val.obj X ⟶ unitObj O hO X :=
  (exists_coordFamily L X).choose j

/-- If `L` has coordinates at `X`, a section over `X` whose chosen coordinates all vanish is
zero. -/
lemma coord_detect {X : Cᵒᵖ} (hX : HasCoordsAt L X) (x : ToType (L.val.obj X))
    (hx : ∀ j, coord L X j x = 0) : x = 0 :=
  (exists_coordFamily L X).choose_spec hX x hx

/-- The space of coordinate data of a section over `X`: for every object `V` of the site, every
arrow `X ⟶ V` of the opposite category and every index, a section of the structure sheaf over
`V`. It lies in `Type (max u v w)` and does not depend on `L`. -/
abbrev CoordSpace (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
      (X : Cᵒᵖ) : Type max u v w :=
  ∀ V : Cᵒᵖ, (X ⟶ V) → ℕ → ToType (unitObj O hO V)

/-- All coordinates of all restrictions of a section: the complete coordinate invariant. -/
noncomputable def coordMap (X : Cᵒᵖ) (x : ToType (L.val.obj X)) : CoordSpace O hO X :=
  fun V f j ↦ coord L V j (L.val.restrictₛₗ f x)

/-- The value of `coordMap` at `V`, `f` and `j` is the `j`-th coordinate of the restriction along
`f`. -/
lemma coordMap_apply (X : Cᵒᵖ) (x : ToType (L.val.obj X)) (V : Cᵒᵖ) (f : X ⟶ V) (j : ℕ) :
    coordMap L X x V f j = coord L V j (L.val.restrictₛₗ f x) := rfl

/-- `coordMap` is additive. -/
lemma coordMap_add (X : Cᵒᵖ) (x y : ToType (L.val.obj X)) (V : Cᵒᵖ) (f : X ⟶ V) (j : ℕ) :
    coordMap L X (x + y) V f j = coordMap L X x V f j + coordMap L X y V f j := by
  rw [coordMap_apply, coordMap_apply, coordMap_apply, map_add, map_add]

/-- `coordMap` preserves subtraction. -/
lemma coordMap_sub (X : Cᵒᵖ) (x y : ToType (L.val.obj X)) (V : Cᵒᵖ) (f : X ⟶ V) (j : ℕ) :
    coordMap L X (x - y) V f j = coordMap L X x V f j - coordMap L X y V f j := by
  rw [coordMap_apply, coordMap_apply, coordMap_apply, map_sub, map_sub]

/-- `coordMap` of a scalar multiple is the restricted scalar times the coordinate. -/
lemma coordMap_smul (X : Cᵒᵖ)
    (c : ToType ((Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj.obj X))
    (x : ToType (L.val.obj X)) (V : Cᵒᵖ) (f : X ⟶ V) (j : ℕ) :
    coordMap L X (c • x) V f j
      = (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj.map f c • coordMap L X
        x V f j := by
  rw [coordMap_apply, coordMap_apply, map_smulₛₗ, map_smul]

/-- The coordinates of the restriction of `x` along `g`, read along `f`, are those of `x` read
along `g ≫ f`. -/
lemma coordMap_restrict (X Y : Cᵒᵖ) (g : X ⟶ Y) (x : ToType (L.val.obj X))
    (V : Cᵒᵖ) (f : Y ⟶ V) (j : ℕ) :
    coordMap L Y (L.val.restrictₛₗ g x) V f j = coordMap L X x V (g ≫ f) j := by
  rw [coordMap_apply, coordMap_apply,
    show L.val.restrictₛₗ f (L.val.restrictₛₗ g x) = L.val.restrictₛₗ (g ≫ f) x from
      (PresheafOfModules.map_comp_apply L.val g f x).symm]

/-- **The coordinate invariant determines a section.** -/
theorem coordMap_injective (hc : HasCoordsCover L) (X : Cᵒᵖ) :
    Function.Injective (coordMap L X) := by
  intro x y hxy
  obtain ⟨I, V, f, hcov, hV⟩ := hc X
  have hzero : ∀ i : I, L.val.restrictₛₗ (f i).op (x - y) = 0 := by
    intro i
    refine coord_detect L (hV i) _ (fun j ↦ ?_)
    rw [show coord L (op (V i)) j (L.val.restrictₛₗ (f i).op (x - y))
        = coordMap L X (x - y) (op (V i)) (f i).op j from rfl,
      coordMap_sub, hxy, sub_self]
  have hsieve : ∀ (W : C) (g : W ⟶ X.unop), (Sieve.generate (Presieve.ofArrows V f)).arrows g →
      L.val.restrictₛₗ g.op (x - y) = 0 := by
    intro W g hg
    obtain ⟨Y, h, g', hg', hcomp⟩ := hg
    cases hg' with
    | mk i =>
      rw [← hcomp, show (h ≫ f i).op = (f i).op ≫ h.op from rfl,
        show L.val.restrictₛₗ ((f i).op ≫ h.op) (x - y)
          = L.val.restrictₛₗ h.op (L.val.restrictₛₗ (f i).op (x - y)) from
          PresheafOfModules.map_comp_apply L.val (f i).op h.op (x - y),
        hzero i, map_zero]
  refine sub_eq_zero.mp (L.isSheaf.isSeparated X.unop _ hcov (x - y) 0 (fun W g hgm ↦ ?_))
  show L.val.map g.op (x - y) = L.val.map g.op (0 : ToType (L.val.obj X))
  rw [map_zero]
  exact hsieve W g hgm

end Coords

section Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)}

omit [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **An invertible sheaf of modules has local coordinates.** This is Tag 0B8N (b) read at the
terminal object of each slice site: the split monomorphism into a finite free module has
sectionwise detecting components. -/
theorem hasCoordsCover_of_isInvertible
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      [IsInvertible O hO L] :
    HasCoordsCover L := by
  classical
  intro X
  obtain ⟨I, V, f, hcov, hsplit⟩ := exists_cover_isDirectSummand_finiteFree hO L X.unop
  refine ⟨I, V, f, hcov, fun i ↦ ?_⟩
  obtain ⟨n, s, hs⟩ := hsplit i
  have := hs
  obtain ⟨α, hα⟩ := exists_detecting_of_isSplitMono s
  refine ⟨fun j ↦ if h : j < n then (α ⟨j, h⟩).val.app (op (Over.mk (𝟙 (V i)))) else 0,
    fun x hx ↦ ?_⟩
  refine hα (op (Over.mk (𝟙 (V i)))) x (fun jj ↦ ?_)
  have h : (if hj : (jj : ℕ) < n then (α ⟨(jj : ℕ), hj⟩).val.app (op (Over.mk (𝟙 (V i))))
      else 0) x = 0 := hx (jj : ℕ)
  rwa [dite_eq_left jj.isLt, Fin.eta] at h

end Invertible

section Reconstruct

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)}
  {L N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}

/-- The coordinates of a section of `L` are the coordinates of a section of `N`. -/
lemma mem_range_coordMap
    (h : ∀ X : Cᵒᵖ, Set.range (coordMap L X) = Set.range (coordMap N X))
    (X : Cᵒᵖ) (x : ToType (L.val.obj X)) : coordMap L X x ∈ Set.range (coordMap N X) := by
  rw [← h X]; exact Set.mem_range_self x

/-- The section of `N` with the same coordinates as a given section of `L`. -/
noncomputable def coordTransfer
    (h : ∀ X : Cᵒᵖ, Set.range (coordMap L X) = Set.range (coordMap N X))
    (X : Cᵒᵖ) (x : ToType (L.val.obj X)) : ToType (N.val.obj X) :=
  (mem_range_coordMap h X x).choose

/-- `coordTransfer h X x` has the same coordinates as `x`. -/
lemma coordMap_coordTransfer
    (h : ∀ X : Cᵒᵖ, Set.range (coordMap L X) = Set.range (coordMap N X))
    (X : Cᵒᵖ) (x : ToType (L.val.obj X)) :
    coordMap N X (coordTransfer h X x) = coordMap L X x :=
  (mem_range_coordMap h X x).choose_spec

/-- `coordTransfer` commutes with restriction when `N` has local coordinates. -/
lemma coordTransfer_restrict (hN : HasCoordsCover N)
    (h : ∀ X : Cᵒᵖ, Set.range (coordMap L X) = Set.range (coordMap N X))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : ToType (L.val.obj X)) :
    coordTransfer h Y (L.val.restrictₛₗ f x) = N.val.restrictₛₗ f (coordTransfer h X x) := by
  refine coordMap_injective N hN Y (funext fun V ↦ funext fun g ↦ funext fun j ↦ ?_)
  rw [coordMap_coordTransfer, coordMap_restrict, coordMap_restrict, coordMap_coordTransfer]

/-- Two sheaves of modules with the same coordinate ranges have isomorphic modules of sections
over every object, by the linear bijection matching coordinates. -/
noncomputable def coordEquiv (hL : HasCoordsCover L) (hN : HasCoordsCover N)
    (h : ∀ X : Cᵒᵖ, Set.range (coordMap L X) = Set.range (coordMap N X)) (X : Cᵒᵖ) :
    ToType (L.val.obj X) ≃ₗ[ToType ((Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO).obj.obj X)]
      ToType (N.val.obj X) where
  toFun := coordTransfer h X
  invFun := coordTransfer (fun Y ↦ (h Y).symm) X
  map_add' x y := by
    refine coordMap_injective N hN X (funext fun V ↦ funext fun g ↦ funext fun j ↦ ?_)
    rw [coordMap_coordTransfer, coordMap_add N, coordMap_coordTransfer, coordMap_coordTransfer,
      coordMap_add L]
  map_smul' c x := by
    refine coordMap_injective N hN X (funext fun V ↦ funext fun g ↦ funext fun j ↦ ?_)
    rw [coordMap_coordTransfer, coordMap_smul N, coordMap_coordTransfer, coordMap_smul L]
    rfl
  left_inv x := by
    refine coordMap_injective L hL X (funext fun V ↦ funext fun g ↦ funext fun j ↦ ?_)
    rw [coordMap_coordTransfer, coordMap_coordTransfer]
  right_inv y := by
    refine coordMap_injective N hN X (funext fun V ↦ funext fun g ↦ funext fun j ↦ ?_)
    rw [coordMap_coordTransfer, coordMap_coordTransfer]

/-- **The coordinate ranges are a complete invariant**: two sheaves of modules with local
coordinates whose coordinate ranges agree over every object are isomorphic. -/
noncomputable def isoOfCoordRangeEq (hL : HasCoordsCover L) (hN : HasCoordsCover N)
    (h : ∀ X : Cᵒᵖ, Set.range (coordMap L X) = Set.range (coordMap N X)) : L ≅ N :=
  (SheafOfModules.fullyFaithfulForget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
    hO)).preimageIso
    (PresheafOfModules.isoMk (fun X ↦ (coordEquiv hL hN h X).toModuleIso)
      (fun {_ _} f ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦
        coordTransfer_restrict hN h f x)))

end Reconstruct

end Stacks.SheafOfModules.InvertibleSmall

namespace Stacks.SheafOfModules

open InvertibleSmall

section Main

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))

/-- **Sheaves of modules with local coordinates form a set.** A property of sheaves of
`O`-modules all of whose members have a covering family with detecting coordinates is
essentially small at `max u v w`: the coordinate ranges are a complete invariant valued in a
type of that size. -/
theorem essentiallySmall_of_hasCoordsCover
    (P : ObjectProperty (SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)))
    (hP : ∀ L, P L → HasCoordsCover L) :
    ObjectProperty.EssentiallySmall.{max u v w} P := by
  classical
  refine ⟨ObjectProperty.ofObj (fun d : (∀ X : Cᵒᵖ, Set (CoordSpace O hO X)) ↦
      if hd : ∃ A : Subtype P, ∀ X, Set.range (coordMap A.1 X) = d X then hd.choose.1
      else SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)),
    inferInstance, fun L hL ↦ ?_⟩
  have hex : ∃ A : Subtype P, ∀ X : Cᵒᵖ,
      Set.range (coordMap A.1 X) = Set.range (coordMap L X) := ⟨⟨L, hL⟩, fun _ ↦ rfl⟩
  refine ⟨_, ⟨fun X ↦ Set.range (coordMap L X)⟩, ⟨?_⟩⟩
  rw [dite_eq_left hex]
  exact isoOfCoordRangeEq (hP L hL) (hP _ hex.choose.2) fun X ↦ (hex.choose_spec X).symm

end Main

end Stacks.SheafOfModules

end
