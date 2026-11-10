module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EmptyOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.PresheafOperations
public import StacksFrontier.CategoryTheory.Sites.CoproductUniversality

/-!
# The finite part as a sheaf of `F₂`-algebras over the base

Let `f : X ⟶ Y` be a separated morphism of algebraic spaces over a scheme `S`. Stacks 04PI
reads the finite part `(X/Y)_fin` as an `F₂`-algebra without unit over `Y`, with multiplication
the intersection `⋆₂` and addition the symmetric difference, zero the pair `(1_Y, ∅)`, and a
unit `(1_Y, X)` when `f` is finite. This file supplies the zero and the unit as sections of
`(X/Y)_fin` over `Y`, and the algebra structure on the sections lying over a fixed morphism to
`Y` as a commutative ring without unit which is an algebra over `F₂`.

The zero needs the empty open subspace to have finite projection to the base, which the
argument for the other operations does not give: it is contained in every section, but no
section need be given in advance. The empty open subspace is instead an initial object among
sheaves on the big fppf site -- a section of it forces the object it lives on to have no
points, and a sheaf is a singleton there -- hence the coproduct of the empty family of
algebraic spaces, and a morphism out of a finite coproduct whose restriction to each summand is
finite is finite.

## Main definitions

* `AlgebraicGeometry.Space.FinitePartFibre.zeroFibre`: the zero section `(a, ∅)` over an
  arbitrary morphism `a : T ⟶ Y`.
* `AlgebraicGeometry.Space.FinitePartPresheaf.zeroSection` and
  `AlgebraicGeometry.Space.FinitePartPresheaf.oneSection`: the zero and, for `f` finite, the
  unit, as sections of the finite part over `Y`.
* `AlgebraicGeometry.Space.FinitePartFibre.nonUnitalCommRing` and
  `AlgebraicGeometry.Space.FinitePartFibre.zmodModule`: the `F₂`-algebra without unit on the
  sections lying over a fixed morphism to `Y`.
* `AlgebraicGeometry.Space.FinitePartFibre.commRing`: for `f` finite, the same algebra with its
  unit `(a, T ×_Y X)`.
* `AlgebraicGeometry.Space.FinitePartPresheaf.sectionMap`: the section of the finite part over
  `Y` determined by a rule on sections which commutes with restriction.

## Main results

* `AlgebraicGeometry.Space.isFinite_ι_openSubspaceOfPoints_empty`: the empty open subspace of
  an algebraic space has finite projection to anything.
* `AlgebraicGeometry.Space.homOfOpenSubspaceOfPointsEmpty` and
  `AlgebraicGeometry.Space.hom_ext_openSubspaceOfPointsEmpty`: the empty open subspace has
  exactly one morphism to every sheaf.
* `AlgebraicGeometry.Space.FinitePartPresheaf.zeroSection_comp_baseMap` and
  `AlgebraicGeometry.Space.FinitePartPresheaf.oneSection_comp_baseMap`: both are sections of
  the projection to `Y`.
* `AlgebraicGeometry.Space.FinitePartFibre.zero_eq_zeroFibre`: the zero produced from a given
  section is the canonical one.
* `AlgebraicGeometry.Space.FinitePartFibre.star₃_eq_mul_one_add` and
  `AlgebraicGeometry.Space.FinitePartFibre.star₄_eq_one_add_mul`: for `f` finite, the two
  differences are `s (1 + s')` and `(1 + s) s'` in the ring above.

## Implementation notes

The operations depend on the separatedness of `f`, and the unit on its finiteness, neither of
which is a class, so the ring structures are definitions rather than instances; the `Zero`,
`Add`, `Neg`, `Mul` and `One` they are assembled from are introduced locally in their bodies,
which is what makes the recursive scalar actions and powers available.

## References

* [Stacks Project, Tag 04PI](https://stacks.math.columbia.edu/tag/04PI)
* [Stacks Project, Tag 0CZ2](https://stacks.math.columbia.edu/tag/0CZ2)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Empty

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An object of the site carrying a section of the empty open subspace has no points. -/
theorem isEmpty_of_mem_openSubspaceOfPoints_empty {A : BigFppfOver B S hS}
    {x : F.obj (op A)} (hx : x ∈ (openSubspaceOfPoints B S hS F ∅).obj (op A)) :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj A) := by
  refine ⟨fun t => ?_⟩
  obtain ⟨w, -⟩ := surjective_pointsToScheme B S hS A t
  exact hx ⟨w, rfl⟩

/-- The empty open subspace is an initial object among sheaves: it has a unique morphism to
every sheaf, there being no sections except over objects with no points. -/
def homOfOpenSubspaceOfPointsEmpty {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hQ : Presieve.IsSheaf (BigFppfOver.topology B S hS) Q) :
    (openSubspaceOfPoints B S hS F ∅).toFunctor ⟶ Q where
  app A := ↾fun x =>
    (hQ.nonempty_obj_of_bot_mem (BigFppfOver.topology B S hS)
      (BigFppfOver.bot_mem_topology A.unop
        (isEmpty_of_mem_openSubspaceOfPoints_empty B S hS x.2))).some
  naturality := by
    intro A A' k
    ext x
    have := hQ.subsingleton_obj_of_bot_mem (BigFppfOver.topology B S hS)
      (BigFppfOver.bot_mem_topology A'.unop (isEmpty_of_mem_openSubspaceOfPoints_empty B S hS
        ((openSubspaceOfPoints B S hS F ∅).toFunctor.map k x).2))
    exact Subsingleton.elim _ _

/-- Two morphisms from the empty open subspace to a sheaf are equal. -/
theorem hom_ext_openSubspaceOfPointsEmpty {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hQ : Presieve.IsSheaf (BigFppfOver.topology B S hS) Q)
    (m₁ m₂ : (openSubspaceOfPoints B S hS F ∅).toFunctor ⟶ Q) : m₁ = m₂ := by
  ext A x
  have := hQ.subsingleton_obj_of_bot_mem (BigFppfOver.topology B S hS)
    (BigFppfOver.bot_mem_topology A.unop
      (isEmpty_of_mem_openSubspaceOfPoints_empty B S hS x.2))
  exact Subsingleton.elim _ _

/-- **The empty open subspace has finite projection to anything.** It is the initial object
among sheaves, hence the coproduct of the empty family of algebraic spaces, and a morphism out
of a finite coproduct whose restriction to each summand is finite is finite. -/
theorem isFinite_ι_openSubspaceOfPoints_empty (hF : IsAlgebraicSpace B S hS F)
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hG : IsAlgebraicSpace B S hS G) (g : F ⟶ G) :
    IsFinite B S hS ((openSubspaceOfPoints B S hS F (∅ : Set (points B S hS F))).ι ≫ g) := by
  have hEsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (openSubspaceOfPoints B S hS F ∅).toFunctor :=
    isSheaf_openSubspaceOfPoints B S hS hF.isSheaf ∅
  refine isFinite_coproduct B S hS (I := Empty) (fun i => i.elim) (fun i => i.elim) hG
    ⟨_, hEsheaf⟩ (fun i => i.elim) ?_ (fun i => i.elim) _ (fun i => i.elim) (fun i => i.elim)
  exact Cofan.IsColimit.mk _
    (fun s => ⟨homOfOpenSubspaceOfPointsEmpty B S hS
      ((isSheaf_iff_isSheaf_of_type _ _).1 s.pt.property)⟩)
    (fun _ i => i.elim)
    (fun s m _ => Sheaf.hom_ext (hom_ext_openSubspaceOfPointsEmpty B S hS
      ((isSheaf_iff_isSheaf_of_type _ _).1 s.pt.property) _ _))

end Empty

namespace FinitePartFibre

variable {B S hS} {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
  {T T' : AlgebraicSpaces B S hS} {a : T ⟶ Y}

/-- **Stacks 04PI, the zero of the `F₂`-algebra.** The section `0 = (a, ∅)` cut out by no
point at all, whose projection to `T` is finite because the empty open subspace is the
coproduct of the empty family. -/
@[stacks 04PI "zero_as_a_section_over_any_base"]
def zeroFibre (a : T ⟶ Y) : FinitePartFibre B S hS f a where
  subspace := openSubspaceOfPoints B S hS (pullback a.hom f.hom) ∅
  isOpen := isOpenSubspace_openSubspaceOfPoints B S hS
    (isAlgebraicSpace_ambient B S hS f a) ∅ isOpen_empty
  finite_projection := isFinite_ι_openSubspaceOfPoints_empty B S hS
    (isAlgebraicSpace_ambient B S hS f a) T.property (pullback.fst a.hom f.hom)

/-- The set of points of the zero section `zeroFibre a` is empty. -/
@[simp]
theorem pointSet_zeroFibre :
    (zeroFibre (B := B) (f := f) a).pointSet = (∅ : Set (points B S hS (pullback a.hom f.hom))) :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS _

/-- **Stacks 04PI.** The zero section produced from any section of the finite part is the
canonical one. -/
theorem zero_eq_zeroFibre (Z : FinitePartFibre B S hS f a) : zero Z = zeroFibre a :=
  ext_pointSet (by rw [pointSet_zero, pointSet_zeroFibre])

/-- **Stacks 04PI.** The zero commutes with restriction along `T' ⟶ T`. -/
theorem restrict_zeroFibre (h : T' ⟶ T) :
    (zeroFibre (B := B) (f := f) a).restrict h = zeroFibre (h ≫ a) :=
  ext_pointSet (by
    rw [pointSet_restrict, pointSet_zeroFibre, pointSet_zeroFibre, Set.preimage_empty])

end FinitePartFibre

namespace FinitePartPresheaf

variable {B S hS} {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
  (P : FinitePartPresheaf B S hS f)

/-- A rule assigning to every morphism `T ⟶ Y` a section of the finite part over it, which
commutes with restriction, is a section of the finite part over `Y`. -/
def sectionMap
    (opr : ∀ {T : AlgebraicSpaces B S hS} (a : T ⟶ Y), FinitePartFibre B S hS f a)
    (hres : ∀ {T T' : AlgebraicSpaces B S hS} (a : T ⟶ Y) (h : T' ⟶ T),
      (opr a).restrict h = opr (h ≫ a)) :
    Y.obj ⟶ P.toFunctor where
  app T := ↾fun y => (P.sections T.unop).symm
    (opr (ObjectProperty.homMk (yonedaEquiv.symm y) : schemeSpace T.unop ⟶ Y)).toPair
  naturality := by
    intro T T' k
    ext y
    apply (P.sections T'.unop).injective
    change P.sections T'.unop ((P.sections T'.unop).symm (opr _).toPair) =
      P.sections T'.unop (P.toFunctor.map k ((P.sections T.unop).symm (opr _).toPair))
    rw [Equiv.apply_symm_apply, P.sections_map_eq_baseChangePair k, Equiv.apply_symm_apply,
      ← FinitePartFibre.toPair_restrict, hres]
    refine congrArg (fun a => (opr a).toPair) ?_
    apply ObjectProperty.hom_ext
    change yonedaEquiv.symm (Y.obj.map k y) = yoneda.map k.unop ≫ yonedaEquiv.symm y
    exact yonedaEquiv_symm_map k y

/-- The pair of the section of the finite part over `Y` produced by a rule on sections. -/
theorem sections_sectionMap
    (opr : ∀ {T : AlgebraicSpaces B S hS} (a : T ⟶ Y), FinitePartFibre B S hS f a)
    (hres : ∀ {T T' : AlgebraicSpaces B S hS} (a : T ⟶ Y) (h : T' ⟶ T),
      (opr a).restrict h = opr (h ≫ a))
    (T : BigFppfOver B S hS) (y : Y.obj.obj (op T)) :
    P.sections T ((sectionMap P opr hres).app (op T) y) =
      (opr (ObjectProperty.homMk (yonedaEquiv.symm y) : schemeSpace T ⟶ Y)).toPair :=
  Equiv.apply_symm_apply _ _

/-- A section of the finite part over `Y` produced by a rule on sections is a section of the
projection to `Y`. -/
theorem sectionMap_comp_baseMap
    (opr : ∀ {T : AlgebraicSpaces B S hS} (a : T ⟶ Y), FinitePartFibre B S hS f a)
    (hres : ∀ {T T' : AlgebraicSpaces B S hS} (a : T ⟶ Y) (h : T' ⟶ T),
      (opr a).restrict h = opr (h ≫ a)) :
    sectionMap P opr hres ≫ P.baseMap = 𝟙 Y.obj := by
  ext T y
  apply yonedaEquiv.symm.injective
  change yonedaEquiv.symm (P.baseMap.app T ((sectionMap P opr hres).app T y)) =
    yonedaEquiv.symm y
  rw [P.baseMap_spec, sections_sectionMap]
  rfl

/-- **Stacks 04PI.** The zero section `0 = (1_Y, ∅)` of the `F₂`-algebra, as a section of the
finite part over `Y`. -/
@[stacks 04PI "zero_section_over_the_base"]
def zeroSection : Y.obj ⟶ P.toFunctor :=
  sectionMap P (fun a => FinitePartFibre.zeroFibre a)
    (fun _ h => FinitePartFibre.restrict_zeroFibre h)

/-- **Stacks 04PI.** On sections, the zero is the empty open subspace. -/
@[stacks 04PI "zero_section_is_the_empty_subspace"]
theorem sections_zeroSection (T : BigFppfOver B S hS) (y : Y.obj.obj (op T)) :
    P.sections T ((zeroSection P).app (op T) y) =
      (FinitePartFibre.zeroFibre
        (ObjectProperty.homMk (yonedaEquiv.symm y) : schemeSpace T ⟶ Y)).toPair :=
  sections_sectionMap P _ _ T y

/-- **Stacks 04PI.** The zero is a section of the projection to `Y`. -/
@[stacks 04PI "zero_section_lies_over_the_base"]
theorem zeroSection_comp_baseMap : zeroSection P ≫ P.baseMap = 𝟙 Y.obj :=
  sectionMap_comp_baseMap P _ _

/-- **Stacks 04PI, the finite case.** The unit `1 = (1_Y, X)` of the `F₂`-algebra, as a section
of the finite part over `Y`. -/
@[stacks 04PI "unit_section_over_the_base"]
def oneSection (hfin : IsFinite B S hS f.hom) : Y.obj ⟶ P.toFunctor :=
  sectionMap P (fun _ => FinitePartFibre.one hfin)
    (fun _ h => FinitePartFibre.restrict_one h hfin)

/-- **Stacks 04PI, the finite case.** On sections, the unit is the whole fibre product. -/
@[stacks 04PI "unit_section_is_the_whole_fibre_product"]
theorem sections_oneSection (hfin : IsFinite B S hS f.hom) (T : BigFppfOver B S hS)
    (y : Y.obj.obj (op T)) :
    P.sections T ((oneSection P hfin).app (op T) y) =
      (FinitePartFibre.one (a := (ObjectProperty.homMk (yonedaEquiv.symm y) :
        schemeSpace T ⟶ Y)) hfin).toPair :=
  sections_sectionMap P _ _ T y

/-- **Stacks 04PI, the finite case.** The unit is a section of the projection to `Y`. -/
@[stacks 04PI "unit_section_lies_over_the_base"]
theorem oneSection_comp_baseMap (hfin : IsFinite B S hS f.hom) :
    oneSection P hfin ≫ P.baseMap = 𝟙 Y.obj :=
  sectionMap_comp_baseMap P _ _

end FinitePartPresheaf

namespace FinitePartFibre

variable {B S hS} {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} {T : AlgebraicSpaces B S hS}

/-- **Stacks 04PI.** The sections of the finite part over `T` lying over a fixed `a : T ⟶ Y`
form a commutative ring without unit: the multiplication is the intersection `⋆₂`, the addition
is the symmetric difference `⋆₁(⋆₃(s, s'), ⋆₄(s, s'))` and the zero is `(a, ∅)`. -/
@[instance_reducible, stacks 04PI "f2_algebra_without_unit"]
noncomputable def nonUnitalCommRing (hf : IsSeparated B S hS f.hom) (a : T ⟶ Y) :
    NonUnitalCommRing (FinitePartFibre B S hS f a) :=
  let : Zero (FinitePartFibre B S hS f a) := ⟨zeroFibre a⟩
  let : Add (FinitePartFibre B S hS f a) := ⟨add hf⟩
  let : Neg (FinitePartFibre B S hS f a) := ⟨id⟩
  let : Mul (FinitePartFibre B S hS f a) := ⟨star₂ hf⟩
  { add := (· + ·)
    zero := 0
    neg := Neg.neg
    sub x y := add hf x y
    mul := (· * ·)
    nsmul := nsmulRec
    zsmul := zsmulRec
    add_assoc x y z := add_assoc hf x y z
    zero_add x := by
      change add hf (zeroFibre a) x = x
      rw [← zero_eq_zeroFibre x]
      exact zero_add hf x
    add_zero x := by
      change add hf x (zeroFibre a) = x
      rw [← zero_eq_zeroFibre x]
      exact add_zero hf x
    add_comm x y := add_comm hf x y
    neg_add_cancel x := by
      change add hf x x = zeroFibre a
      rw [add_self hf x, zero_eq_zeroFibre]
    mul_assoc x y z := star₂_assoc hf x y z
    mul_comm x y := star₂_comm hf x y
    left_distrib x y z := by
      change star₂ hf x (add hf y z) = add hf (star₂ hf x y) (star₂ hf x z)
      rw [star₂_comm hf x (add hf y z), star₂_add hf y z x, star₂_comm hf y x,
        star₂_comm hf z x]
    right_distrib x y z := star₂_add hf x y z
    zero_mul x := by
      change star₂ hf (zeroFibre a) x = zeroFibre a
      rw [← zero_eq_zeroFibre x, star₂_comm hf, star₂_zero hf x]
    mul_zero x := by
      change star₂ hf x (zeroFibre a) = zeroFibre a
      rw [← zero_eq_zeroFibre x, star₂_zero hf x] }

/-- **Stacks 04PI.** Every section is its own additive inverse, so the ring of sections over a
fixed `a : T ⟶ Y` is an algebra over `F₂`. -/
@[instance_reducible, stacks 04PI "f2_algebra_scalars"]
noncomputable def zmodModule (hf : IsSeparated B S hS f.hom) (a : T ⟶ Y) :
    letI := nonUnitalCommRing hf a
    Module (ZMod 2) (FinitePartFibre B S hS f a) :=
  let := nonUnitalCommRing hf a
  AddCommGroup.zmodModule fun x => by
    rw [two_nsmul]
    change add hf x x = zeroFibre a
    rw [add_self hf x, zero_eq_zeroFibre]

/-- **Stacks 04PI, the finite case.** When `f` is finite the sections of the finite part over a
fixed `a : T ⟶ Y` form a commutative ring, the unit being the section `(a, T ×_Y X)` and the
remaining structure that of the `F₂`-algebra. -/
@[instance_reducible, stacks 04PI "f2_algebra_with_its_unit_in_the_finite_case"]
noncomputable def commRing (hf : IsSeparated B S hS f.hom) (hfin : IsFinite B S hS f.hom)
    (a : T ⟶ Y) : CommRing (FinitePartFibre B S hS f a) :=
  let := nonUnitalCommRing hf a
  let : One (FinitePartFibre B S hS f a) := ⟨one hfin⟩
  { nonUnitalCommRing hf a with
    one := one hfin
    one_mul x := star₂_one hf x hfin
    mul_one x := star₂_one' hf x hfin
    npow := npowRec
    natCast := Nat.unaryCast }

/-- **Stacks 04PI, the finite case.** `⋆₃(s, s') = s (1 + s')`. -/
@[stacks 04PI "star_3_is_s_times_one_plus_s_prime"]
theorem star₃_eq_mul_one_add (hf : IsSeparated B S hS f.hom) (hfin : IsFinite B S hS f.hom)
    {a : T ⟶ Y} (Z₁ Z₂ : FinitePartFibre B S hS f a) :
    letI := commRing hf hfin a
    star₃ hf Z₁ Z₂ = Z₁ * (1 + Z₂) :=
  star₃_eq_star₂_one_add hf Z₁ Z₂ hfin

/-- **Stacks 04PI, the finite case.** `⋆₄(s, s') = (1 + s) s'`. -/
@[stacks 04PI "star_4_is_one_plus_s_times_s_prime"]
theorem star₄_eq_one_add_mul (hf : IsSeparated B S hS f.hom) (hfin : IsFinite B S hS f.hom)
    {a : T ⟶ Y} (Z₁ Z₂ : FinitePartFibre B S hS f a) :
    letI := commRing hf hfin a
    star₄ hf Z₁ Z₂ = (1 + Z₁) * Z₂ :=
  star₄_eq_star₂_one_add hf Z₁ Z₂ hfin

end FinitePartFibre

end AlgebraicGeometry.Space

end
