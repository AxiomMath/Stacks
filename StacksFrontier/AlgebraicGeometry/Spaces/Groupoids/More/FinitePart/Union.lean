module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringRestrictionCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Operations
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces

/-!
# The union operation on the finite part, and its `F₂`-algebra structure

Let `f : X ⟶ Y` be a separated morphism of algebraic spaces over a scheme `S`. A section of
the finite part `(X/Y)_fin` over `T` lying over `a : T ⟶ Y` is an open subspace of `T ×_Y X`
finite over `T`, recorded as `AlgebraicGeometry.Space.FinitePartFibre`. This file constructs
the fourth operation `⋆₁` of Stacks 04PI on such sections, the union, and the `F₂`-algebra
structure the remark attaches to the finite part: the multiplication is the intersection `⋆₂`,
the addition is `⋆₁(⋆₃(s, s'), ⋆₄(s, s'))`, which is the symmetric difference, the zero is
`(a, ∅)`, and every section is its own additive inverse. When `f` is finite the algebra has a
unit `1 = (a, T ×_Y X)` and the two differences are expressed through it by
`⋆₃(s, s') = s (1 + s')` and `⋆₄(s, s') = (1 + s) s'`.

What needs proof is that the union of two sections is again finite over `T`. Unlike the
intersection and the two differences it is contained in neither factor, so it is not a closed
subspace of a piece already finite over `T`. Instead `Z₁ ∪ Z₂` is the *disjoint* union of the
open and closed pieces `Z₁` and `Z₂ ∖ Z₁`, hence their coproduct as a sheaf on the big fppf
site, and a morphism out of a finite coproduct of algebraic spaces whose restriction to each
summand is finite is finite, which is Stacks 0CZ2.

## Main definitions

* `AlgebraicGeometry.Space.FinitePartFibre.star₁`: the operation `⋆₁` of Stacks 04PI, the
  union of two sections of `(X/Y)_fin` over `T` lying over the same `a`.
* `AlgebraicGeometry.Space.FinitePartFibre.add`: the addition
  `s + s' = ⋆₁(⋆₃(s, s'), ⋆₄(s, s'))` of the `F₂`-algebra.

## Main results

* `AlgebraicGeometry.Space.isFinite_ι_openSubspaceOfPoints_union_of_disjoint`: the open
  subspace cut out by the union of two disjoint open sets of points, each cutting out an open
  subspace finite over the base, is finite over the base.
* `AlgebraicGeometry.Space.FinitePartFibre.pointSet_star₁` and
  `AlgebraicGeometry.Space.FinitePartFibre.pointSet_add`: on points, `⋆₁` is the union and the
  addition is the symmetric difference.
* `AlgebraicGeometry.Space.FinitePartFibre.add_comm`,
  `AlgebraicGeometry.Space.FinitePartFibre.add_assoc`,
  `AlgebraicGeometry.Space.FinitePartFibre.add_zero`,
  `AlgebraicGeometry.Space.FinitePartFibre.zero_add`,
  `AlgebraicGeometry.Space.FinitePartFibre.add_self` and
  `AlgebraicGeometry.Space.FinitePartFibre.star₂_add`: the addition is a commutative group law
  with neutral element the zero section in which every element is its own inverse, and the
  multiplication distributes over it.
* `AlgebraicGeometry.Space.FinitePartFibre.star₃_eq_star₂_one_add` and
  `AlgebraicGeometry.Space.FinitePartFibre.star₄_eq_star₂_one_add`: for `f` finite, the two
  differences are `s (1 + s')` and `(1 + s) s'`.

## Implementation notes

The union is cut out by the union of the two point sets through the correspondence of
Stacks 03BZ, as the other three operations are in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/Operations.lean`; the pointwise
union of two open subspaces is not a sheaf, so the point sets are the only available route.

That the union is the coproduct of its two disjoint pieces is deduced from
`AlgebraicGeometry.isIso_hom_desc_of_decomposition`, whose hypotheses are supplied by the
geometry: an object of the site carrying a section of the union is split by the preimages of
the two point sets into two disjoint open subobjects covering it, over each of which the
section comes from the corresponding piece, and two sections of the two pieces with the same
image live over an object with no points because the point sets are disjoint.

The zero section is `AlgebraicGeometry.Space.FinitePartFibre.zero`, which takes a section as
an argument and inherits the ambient space from it, rather than being produced from nothing;
`AlgebraicGeometry.Space.FinitePartFibre.zero_eq_zero` says it does not depend on that
argument.

## References

* [Stacks Project, Tag 04PI](https://stacks.math.columbia.edu/tag/04PI)
* [Stacks Project, Tag 04PH](https://stacks.math.columbia.edu/tag/04PH)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 0CZ2](https://stacks.math.columbia.edu/tag/0CZ2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped symmDiff

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inclusion of a subfunctor into a larger one is injective on sections. -/
theorem injective_homOfLe_app {C : Type*} [Category C] {F : Cᵒᵖ ⥤ Type u}
    {V W : Subfunctor F} (h : V ≤ W) (A : Cᵒᵖ) :
    Function.Injective ((Subfunctor.homOfLe h).app A) := by
  intro x z e
  have e' : (((Subfunctor.homOfLe h).app A x : W.toFunctor.obj A) : F.obj A) =
      (((Subfunctor.homOfLe h).app A z : W.toFunctor.obj A) : F.obj A) := by rw [e]
  exact Subtype.ext e'

/-- Two sections of subfunctors cut out by disjoint sets of points with the same image in a
larger subfunctor live over an object with no points. -/
theorem isEmpty_of_homOfLe_app_eq_of_disjoint
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (D₁ D₂ : Set (points B S hS F))
    (hdisj : Disjoint D₁ D₂) {R : Subfunctor F}
    (h₁ : openSubspaceOfPoints B S hS F D₁ ≤ R) (h₂ : openSubspaceOfPoints B S hS F D₂ ≤ R)
    (A : BigFppfOver B S hS)
    (x : (openSubspaceOfPoints B S hS F D₁).toFunctor.obj (op A))
    (z : (openSubspaceOfPoints B S hS F D₂).toFunctor.obj (op A))
    (h : (Subfunctor.homOfLe h₁).app (op A) x = (Subfunctor.homOfLe h₂).app (op A) z) :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj A) := by
  have hval : (x : F.obj (op A)) = (z : F.obj (op A)) := congrArg Subtype.val h
  refine ⟨fun t => ?_⟩
  obtain ⟨w, -⟩ := surjective_pointsToScheme B S hS A t
  have h1 : pointsMap B S hS (yoneda.obj A) (yonedaEquiv.symm (x : F.obj (op A))) w ∈ D₁ :=
    x.2 ⟨w, rfl⟩
  have h2 : pointsMap B S hS (yoneda.obj A) (yonedaEquiv.symm (x : F.obj (op A))) w ∈ D₂ := by
    rw [hval]
    exact z.2 ⟨w, rfl⟩
  exact Set.disjoint_left.1 hdisj h1 h2

/-- The restriction of a section to an open subobject on which its points all lie in a given
set lies in the subspace that set cuts out. -/
theorem map_mem_openSubspaceOfPoints_of_range_subset
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (D : Set (points B S hS F))
    {A b : BigFppfOver B S hS} (x : F.obj (op A)) (i : b ⟶ A)
    (Vo : Set ((BigFppfOver.toScheme B S hS).obj A))
    (hr : Set.range ((BigFppfOver.toScheme B S hS).map i) ⊆ Vo)
    (hchar : ∀ p : FieldValuedPoint B S hS (yoneda.obj A),
      pointsMap B S hS (yoneda.obj A) (yonedaEquiv.symm x) (p.class B S hS (yoneda.obj A)) ∈ D ↔
        schemePoint B S hS A p ∈ Vo) :
    F.map i.op x ∈ (openSubspaceOfPoints B S hS F D).obj (op b) := by
  have hkey : yonedaEquiv.symm (F.map i.op x) = yoneda.map i ≫ yonedaEquiv.symm x :=
    yonedaEquiv_symm_map i.op x
  rw [mem_openSubspaceOfPoints_iff]
  change Set.range (pointsMap B S hS (yoneda.obj b) (yonedaEquiv.symm (F.map i.op x))) ⊆ D
  rw [hkey]
  rintro z ⟨w, rfl⟩
  obtain ⟨p, rfl⟩ := Quot.exists_rep w
  rw [pointsMap_comp_apply, pointsMap_class,
    hchar (FieldValuedPoint.map B S hS (yoneda.obj b) (yoneda.map i) p), schemePoint_map_yoneda]
  exact hr ⟨_, rfl⟩

/-- **The union of two disjoint open subspaces finite over the base is finite over the base.**
-/
theorem isFinite_ι_openSubspaceOfPoints_union_of_disjoint
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (g : F ⟶ G)
    (D : Bool → Set (points B S hS F)) (hDopen : ∀ b, IsOpen (D b))
    (hDdisj : ∀ b b', b ≠ b' → Disjoint (D b) (D b'))
    (hDfin : ∀ b, IsFinite B S hS ((openSubspaceOfPoints B S hS F (D b)).ι ≫ g)) :
    IsFinite B S hS ((openSubspaceOfPoints B S hS F (D true ∪ D false)).ι ≫ g) := by
  classical
  let := bigFppfOver_hasSheafify B S hS
  let : HasWeakSheafify (BigFppfOver.topology B S hS) (Type u) :=
    (bigFppfOver_hasSheafify B S hS).isRightAdjoint
  let : HasColimitsOfShape (Discrete Bool)
      (Sheaf (BigFppfOver.topology B S hS) (Type u)) := Sheaf.instHasColimitsOfShape
  have hDW : ∀ b, D b ⊆ D true ∪ D false := by
    rintro (_ | _)
    exacts [Set.subset_union_right, Set.subset_union_left]
  have hVopen : ∀ b, IsOpenSubspace B S hS (openSubspaceOfPoints B S hS F (D b)) := fun b =>
    isOpenSubspace_openSubspaceOfPoints B S hS hF (D b) (hDopen b)
  have hRsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (openSubspaceOfPoints B S hS F (D true ∪ D false)).toFunctor :=
    isSheaf_openSubspaceOfPoints B S hS hF.isSheaf _
  have hle : ∀ b, openSubspaceOfPoints B S hS F (D b) ≤
      openSubspaceOfPoints B S hS F (D true ∪ D false) := fun b =>
    openSubspaceOfPoints_mono B S hS (hDW b)
  have hFalg : ∀ b, IsAlgebraicSpace B S hS
      (openSubspaceOfPoints B S hS F (D b)).toFunctor := fun b => (hVopen b).1
  let Fi : Bool → Sheaf (BigFppfOver.topology B S hS) (Type u) :=
    fun b => ⟨(openSubspaceOfPoints B S hS F (D b)).toFunctor, (hFalg b).isSheaf⟩
  let Xs : Sheaf (BigFppfOver.topology B S hS) (Type u) :=
    ⟨(openSubspaceOfPoints B S hS F (D true ∪ D false)).toFunctor, hRsheaf⟩
  let κ : ∀ b, Fi b ⟶ Xs := fun b => ⟨Subfunctor.homOfLe (hle b)⟩
  let : HasColimit (Discrete.functor Fi) := HasColimitsOfShape.has_colimit _
  let ιc : ∀ b, Fi b ⟶ ∐ Fi := fun b => Sigma.ι Fi b
  have hcop : IsColimit (Cofan.mk (∐ Fi) ιc) := coproductIsCoproduct Fi
  have hinj : ∀ (b : Bool) (A : BigFppfOver B S hS),
      Function.Injective ((Subfunctor.homOfLe (hle b)).app (op A)) := fun b A =>
    injective_homOfLe_app (hle b) (op A)
  have hdisj' : ∀ (b b' : Bool), b ≠ b' → ∀ (A : BigFppfOver B S hS)
      (x : (openSubspaceOfPoints B S hS F (D b)).toFunctor.obj (op A))
      (z : (openSubspaceOfPoints B S hS F (D b')).toFunctor.obj (op A)),
      (Subfunctor.homOfLe (hle b)).app (op A) x = (Subfunctor.homOfLe (hle b')).app (op A) z →
      IsEmpty ((BigFppfOver.toScheme B S hS).obj A) := fun b b' hbb' A x z h =>
    isEmpty_of_homOfLe_app_eq_of_disjoint B S hS (D b) (D b') (hDdisj b b' hbb')
      (hle b) (hle b') A x z h
  have hdecomp : ∀ (A : BigFppfOver B S hS)
      (y : (openSubspaceOfPoints B S hS F (D true ∪ D false)).toFunctor.obj (op A)),
      ∃ (Wd : Bool → BigFppfOver B S hS) (p : ∀ i, Wd i ⟶ A),
        (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
          ((BigFppfOver.toScheme B S hS).map (p i))) ∧
        (∀ i i', i ≠ i' → ∀ (y₁ : (BigFppfOver.toScheme B S hS).obj (Wd i))
          (y₂ : (BigFppfOver.toScheme B S hS).obj (Wd i')),
          (BigFppfOver.toScheme B S hS).map (p i) y₁ ≠
            (BigFppfOver.toScheme B S hS).map (p i') y₂) ∧
        (∀ t : (BigFppfOver.toScheme B S hS).obj A,
          ∃ i, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p i))) ∧
        (∀ i, ∃ z : (openSubspaceOfPoints B S hS F (D i)).toFunctor.obj (op (Wd i)),
          (Subfunctor.homOfLe (hle i)).app (op (Wd i)) z =
            (openSubspaceOfPoints B S hS F (D true ∪ D false)).toFunctor.map (p i).op y) := by
    intro A y
    have hyW : Set.range (pointsMap B S hS (yoneda.obj A)
        (yonedaEquiv.symm (y : F.obj (op A)))) ⊆ D true ∪ D false := y.2
    choose Vs hVsopen hVsmem using fun b =>
      (isOpen_pointTopology_iff B S hS (D b)).mp (hDopen b) A
        (yonedaEquiv.symm (y : F.obj (op A)))
    simp only [Set.mem_preimage] at hVsmem
    choose Ab ib hoib hrb hunivb using fun b =>
      exists_restrict_bigFppfOver A ⟨Vs b, hVsopen b⟩
    have hrb' : ∀ b, Set.range ((BigFppfOver.toScheme B S hS).map (ib b)) = Vs b := hrb
    refine ⟨Ab, ib, hoib, ?_, ?_, ?_⟩
    · intro b b' hbb' y₁ y₂ heq
      have h1 : (BigFppfOver.toScheme B S hS).map (ib b) y₁ ∈ Vs b :=
        (hrb' b).le ⟨y₁, rfl⟩
      have h2 : (BigFppfOver.toScheme B S hS).map (ib b) y₁ ∈ Vs b' :=
        (hrb' b').le ⟨y₂, heq.symm⟩
      obtain ⟨p, hp⟩ := exists_fieldValuedPoint_schemePoint_eq B S hS A
        ((BigFppfOver.toScheme B S hS).map (ib b) y₁)
      exact Set.disjoint_left.1 (hDdisj b b' hbb')
        ((hVsmem b p).2 (hp ▸ h1)) ((hVsmem b' p).2 (hp ▸ h2))
    · intro t
      obtain ⟨p, hp⟩ := exists_fieldValuedPoint_schemePoint_eq B S hS A t
      have hcov : ∀ c, pointsMap B S hS (yoneda.obj A) (yonedaEquiv.symm (y : F.obj (op A)))
          (p.class B S hS (yoneda.obj A)) ∈ D c →
          ∃ i, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (ib i)) := fun c h =>
        ⟨c, (hrb' c).ge (hp ▸ (hVsmem c p).1 h)⟩
      exact (hyW (Set.mem_range_self (p.class B S hS (yoneda.obj A)))).elim (hcov true) (hcov false)
    · intro b
      exact ⟨⟨_, map_mem_openSubspaceOfPoints_of_range_subset B S hS (D b)
        (y : F.obj (op A)) (ib b) (Vs b) (hrb' b).le (hVsmem b)⟩, rfl⟩
  have hiso := isIso_hom_desc_of_decomposition ιc hcop κ hinj hdisj' hdecomp
  have hisoS : IsIso (hcop.desc (Cofan.mk Xs κ)) :=
    ⟨⟨⟨inv (hcop.desc (Cofan.mk Xs κ)).hom⟩, Sheaf.hom_ext (by simp), Sheaf.hom_ext (by simp)⟩⟩
  have hXcolim : IsColimit (Cofan.mk Xs κ) := by
    have := hisoS
    exact IsColimit.ofPointIso hcop
  have hfac : ∀ b, (κ b).hom ≫ ((openSubspaceOfPoints B S hS F (D true ∪ D false)).ι ≫ g) =
      (openSubspaceOfPoints B S hS F (D b)).ι ≫ g := by
    intro b
    rw [← Category.assoc]
    change (Subfunctor.homOfLe (hle b) ≫ _) ≫ g = _
    rw [Subfunctor.homOfLe_ι]
  exact isFinite_coproduct B S hS
    (fun b => (openSubspaceOfPoints B S hS F (D b)).toFunctor) hFalg hG Xs κ hXcolim
    (fun b => (openSubspaceOfPoints B S hS F (D b)).ι ≫ g)
    ((openSubspaceOfPoints B S hS F (D true ∪ D false)).ι ≫ g) hfac hDfin


namespace FinitePartFibre

variable {B S hS} {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} {T : AlgebraicSpaces B S hS}
  {a : T ⟶ Y}

/-- The point set of a section of the finite part is open, the section being an open
subspace. -/
theorem isOpen_pointSet (Z : FinitePartFibre B S hS f a) : IsOpen Z.pointSet :=
  isOpen_range_pointsMap_of_isOpenImmersion B S hS Z.subspace.ι Z.isOpen.2

/-- A section of the finite part is the open subspace of `T ×_Y X` cut out by its own set of
points, by the correspondence of Stacks 03BZ. -/
theorem subspace_eq_openSubspaceOfPoints (Z : FinitePartFibre B S hS f a) :
    Z.subspace = openSubspaceOfPoints B S hS (pullback a.hom f.hom) Z.pointSet :=
  eq_openSubspaceOfPoints_range_pointsMap B S hS (isAlgebraicSpace_ambient B S hS f a)
    Z.subspace Z.isOpen

section Union

variable (hf : IsSeparated B S hS f.hom) (Z₁ Z₂ : FinitePartFibre B S hS f a)

/-- **Stacks 04PI, the operation `⋆₁`.** The union `(a, Z₁ ∪ Z₂)` of two sections of the finite
part lying over the same morphism to `Y`.

Its projection to `T` is finite because `Z₁ ∪ Z₂` is the disjoint union of the open and closed
pieces `Z₁` and `Z₂ ∖ Z₁`, hence their coproduct as a sheaf, and a morphism out of a finite
coproduct whose restriction to each summand is finite is finite. -/
@[stacks 04PI "star_1_on_sections"]
def star₁ : FinitePartFibre B S hS f a where
  subspace := openSubspaceOfPoints B S hS (pullback a.hom f.hom) (Z₁.pointSet ∪ Z₂.pointSet)
  isOpen := isOpenSubspace_openSubspaceOfPoints B S hS (isAlgebraicSpace_ambient B S hS f a) _
    (Z₁.isOpen_pointSet.union Z₂.isOpen_pointSet)
  finite_projection := by
    have hU : Z₁.pointSet ∪ Z₂.pointSet = Z₁.pointSet ∪ (Z₂.pointSet \ Z₁.pointSet) :=
      Set.union_sdiff_self.symm
    rw [hU]
    refine isFinite_ι_openSubspaceOfPoints_union_of_disjoint B S hS
      (isAlgebraicSpace_ambient B S hS f a) T.property _
      (fun b => bif b then Z₁.pointSet else Z₂.pointSet \ Z₁.pointSet) ?_ ?_ ?_
    · intro b
      cases b
      · exact Z₂.isOpen_pointSet.sdiff (Z₁.isClopen_pointSet hf).1
      · exact Z₁.isOpen_pointSet
    · intro b b' h
      cases b <;> cases b' <;>
        first
          | exact absurd rfl h
          | exact Set.disjoint_left.2 fun _ hx hx' => hx'.2 hx
          | exact Set.disjoint_left.2 fun _ hx hx' => hx.2 hx'
    · intro b
      cases b
      · exact (star₄ hf Z₁ Z₂).finite_projection
      · change IsFinite B S hS ((openSubspaceOfPoints B S hS (pullback a.hom f.hom)
            Z₁.pointSet).ι ≫ pullback.fst a.hom f.hom)
        rw [← Z₁.subspace_eq_openSubspaceOfPoints]
        exact Z₁.finite_projection

/-- **Stacks 04PI, the operation `⋆₁`.** On points, `⋆₁(s, s')` is the union `Z₁ ∪ Z₂`. -/
@[simp, stacks 04PI "star_1_on_points"]
theorem pointSet_star₁ : (star₁ hf Z₁ Z₂).pointSet = Z₁.pointSet ∪ Z₂.pointSet :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS _

end Union

section Algebra

variable (hf : IsSeparated B S hS f.hom) (Z₁ Z₂ : FinitePartFibre B S hS f a)

/-- **Stacks 04PI, the addition of the `F₂`-algebra.** `s + s' = ⋆₁(⋆₃(s, s'), ⋆₄(s, s'))`. -/
@[stacks 04PI "addition_of_the_f2_algebra"]
def add : FinitePartFibre B S hS f a := star₁ hf (star₃ hf Z₁ Z₂) (star₄ hf Z₁ Z₂)

/-- **Stacks 04PI.** The addition `s + s' = ⋆₁(⋆₃(s, s'), ⋆₄(s, s'))` of the `F₂`-algebra is
the symmetric difference. -/
@[simp, stacks 04PI "addition_is_the_symmetric_difference"]
theorem pointSet_add : (add hf Z₁ Z₂).pointSet = Z₁.pointSet ∆ Z₂.pointSet := by
  rw [add, pointSet_star₁, pointSet_star₃, pointSet_star₄]
  rfl

/-- **Stacks 04PI.** The addition of the `F₂`-algebra is commutative. -/
@[stacks 04PI "addition_is_commutative"]
theorem add_comm : add hf Z₁ Z₂ = add hf Z₂ Z₁ :=
  ext_pointSet (by simp only [pointSet_add]; exact symmDiff_comm _ _)

/-- **Stacks 04PI.** The addition of the `F₂`-algebra is associative. -/
@[stacks 04PI "addition_is_associative"]
theorem add_assoc (Z₃ : FinitePartFibre B S hS f a) :
    add hf (add hf Z₁ Z₂) Z₃ = add hf Z₁ (add hf Z₂ Z₃) :=
  ext_pointSet (by simp only [pointSet_add]; exact symmDiff_assoc _ _ _)

/-- **Stacks 04PI.** The zero section `0 = (a, ∅)` is neutral for the addition. -/
@[stacks 04PI "zero_is_neutral_for_addition"]
theorem add_zero : add hf Z₁ (zero Z₁) = Z₁ :=
  ext_pointSet (by
    rw [pointSet_add, pointSet_zero]
    ext x
    simp only [Set.mem_symmDiff, Set.mem_empty_iff_false, not_false_eq_true, and_true,
      false_and, or_false])

/-- **Stacks 04PI.** The zero section `0 = (a, ∅)` is neutral for the addition. -/
theorem zero_add : add hf (zero Z₁) Z₁ = Z₁ := by
  rw [add_comm]
  exact add_zero hf Z₁

/-- **Stacks 04PI.** `s + s = 0` for every local section: the algebra is an `F₂`-algebra, every
section being its own additive inverse. -/
@[stacks 04PI "section_plus_itself_is_zero"]
theorem add_self : add hf Z₁ Z₁ = zero Z₁ :=
  ext_pointSet (by
    rw [pointSet_add, pointSet_zero]
    exact symmDiff_self _)

/-- **Stacks 04PI.** The multiplication `s s' = ⋆₂(s, s')` distributes over the addition. -/
@[stacks 04PI "multiplication_distributes_over_addition"]
theorem star₂_add (Z₃ : FinitePartFibre B S hS f a) :
    star₂ hf (add hf Z₁ Z₂) Z₃ = add hf (star₂ hf Z₁ Z₃) (star₂ hf Z₂ Z₃) :=
  ext_pointSet (by
    simp only [pointSet_add, pointSet_star₂]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_symmDiff]
    tauto)

/-- In the finite case, adding the unit complements the point set. -/
private theorem pointSet_add_one (hfin : IsFinite B S hS f.hom) :
    (add hf (one hfin) Z₁).pointSet = Z₁.pointSetᶜ := by
  rw [pointSet_add, pointSet_one]
  exact top_symmDiff _

/-- **Stacks 04PI, the finite case.** `⋆₃(s, s') = s (1 + s')`. -/
@[stacks 04PI "star_3_through_the_unit"]
theorem star₃_eq_star₂_one_add (hfin : IsFinite B S hS f.hom) :
    star₃ hf Z₁ Z₂ = star₂ hf Z₁ (add hf (one hfin) Z₂) :=
  ext_pointSet (by rw [pointSet_star₃, pointSet_star₂, pointSet_add_one, Set.sdiff_eq])

/-- **Stacks 04PI, the finite case.** `⋆₄(s, s') = (1 + s) s'`. -/
@[stacks 04PI "star_4_through_the_unit"]
theorem star₄_eq_star₂_one_add (hfin : IsFinite B S hS f.hom) :
    star₄ hf Z₁ Z₂ = star₂ hf (add hf (one hfin) Z₁) Z₂ :=
  ext_pointSet (by
    rw [pointSet_star₄, pointSet_star₂, pointSet_add_one, Set.sdiff_eq, Set.inter_comm])

end Algebra

end FinitePartFibre


end AlgebraicGeometry.Space

end
