module

public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Free
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.DominantGenericPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidueField
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RationalMaps

/-!
# The degree of a dominant morphism of integral algebraic spaces

Let `f : X ⟶ Y` be a dominant morphism locally of finite type of integral algebraic spaces
over a scheme `S`, and let `x` and `y` be the generic points of `|X|` and `|Y|`. The degree of
`X` over `Y` is the degree `[κ(x) : κ(y)]` of the extension of residue fields at those points,
which is a positive integer under the equivalent conditions of **Stacks 0AD5**. Degrees
multiply in a tower, by the tower law for field extensions.

## Main definitions

* `AlgebraicGeometry.Space.residueFieldAlgebra`: the residue field at a point of a decent
  algebraic space over `S` is an algebra over the residue field at the image of that point,
  through the homomorphism `AlgebraicGeometry.Space.residueFieldHom` of Stacks 0EMW.
* `AlgebraicGeometry.Space.residueFieldDegreeAt`: the degree of that extension.
* `AlgebraicGeometry.Space.HasFiniteResidueFieldExtensionAt`: finiteness of that extension,
  which is condition (2) of **Stacks 0AD5**.
* `AlgebraicGeometry.Space.degree`: **Stacks 0AD6**, the degree of `X` over `Y`, namely the
  degree of the residue field extension at the generic point of `|X|`.

## Main results

* `AlgebraicGeometry.Space.degree_pos`: the degree of `X` over `Y` is a positive integer once
  the residue field extension at the generic point is finite. This is the other half of
  **Stacks 0AD6**.
* `AlgebraicGeometry.Space.degree_comp`: **Stacks 0ENH**, the degree of a composite is the
  product of the degrees.
* `AlgebraicGeometry.Space.degree_eq_residueFieldDegreeAt`: the degree of `X` over `Y` is
  computed at every generic point of `|X|`, not only at the chosen one.

## Implementation notes

The generic point of `|X|` is `genericPoint`, which exists because the point space of an
integral algebraic space is irreducible by definition (Stacks 0AD4) and quasi-sober by
Stacks 03K6, the latter being
`AlgebraicGeometry.Space.quasiSober_points_of_isDecentSpace`. It is unique because that point
space is Kolmogorov, again by decency, so
`AlgebraicGeometry.Space.degree_eq_residueFieldDegreeAt` lets a client use whichever generic
point it already has; the neighbouring files carry a generic point and a proof that it is one
rather than choosing, and that is the form that lemma takes.

The degree is a natural number and its positivity is a separate statement, as for
`Algebra.IsCentralSimple.degree` and as `Module.finrank` itself is stated: positivity is
exactly the content of condition (2) of Stacks 0AD5, which the definition in the source
assumes, so it is carried as the hypothesis
`AlgebraicGeometry.Space.HasFiniteResidueFieldExtensionAt`. Of the five equivalent conditions
of Stacks 0AD5, conditions (4) and (5) are compared by
`AlgebraicGeometry.Space.isQuasiFiniteAt_iff_forall_eq_of_pointsMap_eq`, and (4) implies (1) by
`AlgebraicGeometry.Space.hasTranscendenceDegreeAt_zero_of_isQuasiFiniteAt`; conditions (2) and
(3) are compared with (1) at the scheme level by Stacks 02NX, but the source's reduction of the
space-level conditions to the scheme-level ones through the schematic loci is not carried out
here, so condition (2) is not deduced from the others and is assumed where it is needed.

The residue field extension of a composite is the composite extension because the
homomorphism of residue fields a morphism induces is characterized, not constructed: the two
squares of `AlgebraicGeometry.Space.IsInducedResidueFieldHom` paste into the square for the
composite, and `AlgebraicGeometry.Space.existsUnique_isInducedResidueFieldHom` identifies the
pasted homomorphism with the induced one. The point of `|Z|` under the composite and the
image of the image agree definitionally on a representing field-valued point, which is why
the statement of `AlgebraicGeometry.Space.residueFieldDegreeAt_comp`, whose three sides are
natural numbers, is proved by induction on the class of such a point.

Multiplicativity needs neither finiteness of the two extensions nor local finiteness of type
of the two morphisms: `Module.finrank_mul_finrank` is the tower law for free modules, and a
vector space is free. Dominance of `f` is needed, to know that the generic point of `|X|`
maps to the generic point of `|Y|`; dominance of `g` is not. The statement proved here is
therefore stronger than Stacks 0ENH, which assumes all of these.

## References

* [Stacks Project, Tag 0AD4](https://stacks.math.columbia.edu/tag/0AD4)
* [Stacks Project, Tag 0AD5](https://stacks.math.columbia.edu/tag/0AD5)
* [Stacks Project, Tag 0AD6](https://stacks.math.columbia.edu/tag/0AD6)
* [Stacks Project, Tag 0EMW](https://stacks.math.columbia.edu/tag/0EMW)
* [Stacks Project, Tag 0ENH](https://stacks.math.columbia.edu/tag/0ENH)
* [Stacks Project, Tag 09G9](https://stacks.math.columbia.edu/tag/09G9)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The residue field extension at a point -/

/-- The residue field of a decent algebraic space over `S` at a point is an algebra over the
residue field of the target at the image of that point, through the homomorphism of residue
fields induced by the morphism. -/
@[instance_reducible]
noncomputable def residueFieldAlgebra (hY : IsAlgebraicSpace B S hS Y)
    (hDX : IsDecentSpace B S hS X) (hDY : IsDecentSpace B S hS Y) (f : X ⟶ Y)
    (x : points B S hS X) :
    Algebra (residueField B S hS Y hDY (pointsMap B S hS X f x))
      (residueField B S hS X hDX x) :=
  (residueFieldHom B S hS X Y hY hDX hDY f x).toAlgebra

/-- The degree of the extension of residue fields that a morphism of decent algebraic spaces
over `S` induces at a point of its source. -/
noncomputable def residueFieldDegreeAt (hY : IsAlgebraicSpace B S hS Y)
    (hDX : IsDecentSpace B S hS X) (hDY : IsDecentSpace B S hS Y) (f : X ⟶ Y)
    (x : points B S hS X) : ℕ :=
  letI := residueFieldAlgebra B S hS hY hDX hDY f x
  Module.finrank (residueField B S hS Y hDY (pointsMap B S hS X f x))
    (residueField B S hS X hDX x)

/-- **Condition (2) of Stacks 0AD5**, at an arbitrary point: the extension of residue fields
that a morphism of decent algebraic spaces over `S` induces at a point of its source is
finite. -/
def HasFiniteResidueFieldExtensionAt (hY : IsAlgebraicSpace B S hS Y)
    (hDX : IsDecentSpace B S hS X) (hDY : IsDecentSpace B S hS Y) (f : X ⟶ Y)
    (x : points B S hS X) : Prop :=
  letI := residueFieldAlgebra B S hS hY hDX hDY f x
  Module.Finite (residueField B S hS Y hDY (pointsMap B S hS X f x))
    (residueField B S hS X hDX x)

/-- A finite extension of residue fields has positive degree, the residue field of the source
being nonzero. -/
theorem residueFieldDegreeAt_pos (hY : IsAlgebraicSpace B S hS Y)
    (hDX : IsDecentSpace B S hS X) (hDY : IsDecentSpace B S hS Y) (f : X ⟶ Y)
    (x : points B S hS X)
    (hfin : HasFiniteResidueFieldExtensionAt B S hS hY hDX hDY f x) :
    0 < residueFieldDegreeAt B S hS hY hDX hDY f x := by
  let _ := residueFieldAlgebra B S hS hY hDX hDY f x
  let _ : Module.Finite (residueField B S hS Y hDY (pointsMap B S hS X f x))
      (residueField B S hS X hDX x) := hfin
  show 0 < Module.finrank (residueField B S hS Y hDY (pointsMap B S hS X f x))
    (residueField B S hS X hDX x)
  exact Module.finrank_pos

/-! ### The residue field extension of a composite -/

/-- The homomorphism of residue fields induced by a composite of morphisms of decent
algebraic spaces over `S` at the class of a field-valued point is the composite of the two
induced homomorphisms: the two squares over the intermediate and the final space paste into
the square for the composite, which characterizes it. -/
private theorem residueFieldHom_comp (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (hDX : IsDecentSpace B S hS X)
    (hDY : IsDecentSpace B S hS Y) (hDZ : IsDecentSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (p : FieldValuedPoint B S hS X) :
    residueFieldHom B S hS X Z hZ hDX hDZ (f ≫ g) (p.class B S hS X) =
      (residueFieldHom B S hS X Y hY hDX hDY f (p.class B S hS X)).comp
        (residueFieldHom B S hS Y Z hZ hDY hDZ g
          (pointsMap B S hS X f (p.class B S hS X))) := by
  obtain ⟨mf, hmfSpec, hmfSq⟩ :=
    residueFieldHom_spec B S hS X Y hY hDX hDY f (p.class B S hS X)
  obtain ⟨mg, hmgSpec, hmgSq⟩ :=
    residueFieldHom_spec B S hS Y Z hZ hDY hDZ g (pointsMap B S hS X f (p.class B S hS X))
  refine (existsUnique_isInducedResidueFieldHom B S hS X Z hZ hDX hDZ (f ≫ g)
    (p.class B S hS X)).unique
      (residueFieldHom_spec B S hS X Z hZ hDX hDZ (f ≫ g) (p.class B S hS X))
      ⟨mf ≫ mg, ?_, ?_⟩
  · show B.inclusion.map (mf.left ≫ mg.left) = _
    rw [Functor.map_comp, hmfSpec, hmgSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  · show yoneda.map (mf ≫ mg) ≫
      residueFieldMorphism B S hS Z hDZ
        (pointsMap B S hS Y g (pointsMap B S hS X f (p.class B S hS X))) = _
    rw [Functor.map_comp, Category.assoc, hmgSq, ← Category.assoc, hmfSq, Category.assoc]

/-- The degree of the residue field extension of a composite of morphisms of decent algebraic
spaces over `S` at a point is the product of the two degrees: the induced homomorphisms
compose, so the three residue fields form a tower, and the tower law applies. -/
theorem residueFieldDegreeAt_comp (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (hDX : IsDecentSpace B S hS X)
    (hDY : IsDecentSpace B S hS Y) (hDZ : IsDecentSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : points B S hS X) :
    residueFieldDegreeAt B S hS hZ hDX hDZ (f ≫ g) x =
      residueFieldDegreeAt B S hS hY hDX hDY f x *
        residueFieldDegreeAt B S hS hZ hDY hDZ g (pointsMap B S hS X f x) := by
  induction x using Quot.ind with
  | _ p =>
    have hmap := residueFieldHom_comp B S hS hY hZ hDX hDY hDZ f g p
    let _ := residueFieldAlgebra B S hS hY hDX hDY f (p.class B S hS X)
    let _ := residueFieldAlgebra B S hS hZ hDX hDZ (f ≫ g) (p.class B S hS X)
    let _ : Algebra
        (residueField B S hS Z hDZ (pointsMap B S hS X (f ≫ g) (p.class B S hS X)))
        (residueField B S hS Y hDY (pointsMap B S hS X f (p.class B S hS X))) :=
      residueFieldAlgebra B S hS hZ hDY hDZ g (pointsMap B S hS X f (p.class B S hS X))
    have _ : IsScalarTower
        (residueField B S hS Z hDZ (pointsMap B S hS X (f ≫ g) (p.class B S hS X)))
        (residueField B S hS Y hDY (pointsMap B S hS X f (p.class B S hS X)))
        (residueField B S hS X hDX (p.class B S hS X)) :=
      IsScalarTower.of_algebraMap_eq fun a => RingHom.congr_fun hmap a
    exact (Module.finrank_mul_finrank
      (residueField B S hS Z hDZ (pointsMap B S hS X (f ≫ g) (p.class B S hS X)))
      (residueField B S hS Y hDY (pointsMap B S hS X f (p.class B S hS X)))
      (residueField B S hS X hDX (p.class B S hS X))).symm.trans (mul_comm _ _)

/-! ### The degree of an integral algebraic space over another -/

/-- **Stacks 0AD6.** The degree of `X` over `Y` for a morphism `f : X ⟶ Y` of integral
algebraic spaces over `S`: the degree `[κ(x) : κ(y)]` of the extension of residue fields at
the generic point `x` of `|X|` and its image `y`. -/
@[stacks 0AD6 "the degree of X over Y"]
noncomputable def degree (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXint : IsIntegralSpace B S hS X) (hYint : IsIntegralSpace B S hS Y) (f : X ⟶ Y) : ℕ :=
  have : IrreducibleSpace (points B S hS X) := hXint.irreducibleSpace
  have : QuasiSober (points B S hS X) :=
    quasiSober_points_of_isDecentSpace B S hS hX hXint.isDecentSpace
  residueFieldDegreeAt B S hS hY hXint.isDecentSpace hYint.isDecentSpace f
    (genericPoint (points B S hS X))

/-- The degree of `X` over `Y` is the degree of the residue field extension at any generic
point of `|X|`: the point space of an integral algebraic space is Kolmogorov, so its generic
point is unique. -/
theorem degree_eq_residueFieldDegreeAt (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXint : IsIntegralSpace B S hS X)
    (hYint : IsIntegralSpace B S hS Y) (f : X ⟶ Y) {x : points B S hS X}
    (hx : IsGenericPoint x (Set.univ : Set (points B S hS X))) :
    degree B S hS hX hY hXint hYint f =
      residueFieldDegreeAt B S hS hY hXint.isDecentSpace hYint.isDecentSpace f x := by
  have : IrreducibleSpace (points B S hS X) := hXint.irreducibleSpace
  have : QuasiSober (points B S hS X) :=
    quasiSober_points_of_isDecentSpace B S hS hX hXint.isDecentSpace
  have : T0Space (points B S hS X) :=
    t0Space_points_of_isDecentSpace B S hS hX hXint.isDecentSpace
  exact congrArg
    (residueFieldDegreeAt B S hS hY hXint.isDecentSpace hYint.isDecentSpace f)
    ((genericPoint_spec (points B S hS X)).eq hx)

/-- **Stacks 0AD6.** The degree of `X` over `Y` is a positive integer once the extension of
residue fields at the generic point is finite, which is condition (2) of Stacks 0AD5. -/
@[stacks 0AD6 "positivity of the degree, under condition (2) of Stacks 0AD5, which this \
development cannot yet deduce from the other four"]
theorem degree_pos (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXint : IsIntegralSpace B S hS X) (hYint : IsIntegralSpace B S hS Y) (f : X ⟶ Y)
    {x : points B S hS X}
    (hx : IsGenericPoint x (Set.univ : Set (points B S hS X)))
    (hfin : HasFiniteResidueFieldExtensionAt B S hS hY hXint.isDecentSpace
      hYint.isDecentSpace f x) :
    0 < degree B S hS hX hY hXint hYint f := by
  rw [degree_eq_residueFieldDegreeAt B S hS hX hY hXint hYint f hx]
  exact residueFieldDegreeAt_pos B S hS hY hXint.isDecentSpace hYint.isDecentSpace f x hfin

/-- The point space of an integral algebraic space has a generic point. -/
private theorem exists_isGenericPoint (hX : IsAlgebraicSpace B S hS X)
    (hXint : IsIntegralSpace B S hS X) :
    ∃ x : points B S hS X, IsGenericPoint x (Set.univ : Set (points B S hS X)) := by
  have : IrreducibleSpace (points B S hS X) := hXint.irreducibleSpace
  have : QuasiSober (points B S hS X) :=
    quasiSober_points_of_isDecentSpace B S hS hX hXint.isDecentSpace
  exact ⟨_, genericPoint_spec _⟩

/-- **Stacks 0ENH.** For a dominant morphism `f : X ⟶ Y` and a morphism `g : Y ⟶ Z` of
integral algebraic spaces over `S`, the degree of `X` over `Z` is the degree of `X` over `Y`
times the degree of `Y` over `Z`.

The generic point of `|X|` maps to the generic point of `|Y|` because `f` is dominant, so all
three degrees are read off the same tower of residue fields, and degrees multiply in a tower
of field extensions (Stacks 09G9). -/
@[stacks 0ENH "multiplicativity of the degree; local finiteness of type of the two morphisms, \
finiteness of the two residue field extensions and dominance of g are not needed"]
theorem degree_comp (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (hXint : IsIntegralSpace B S hS X)
    (hYint : IsIntegralSpace B S hS Y) (hZint : IsIntegralSpace B S hS Z) (f : X ⟶ Y)
    (g : Y ⟶ Z) (hf : IsDominant B S hS f) :
    degree B S hS hX hZ hXint hZint (f ≫ g) =
      degree B S hS hX hY hXint hYint f * degree B S hS hY hZ hYint hZint g := by
  obtain ⟨x, hx⟩ := exists_isGenericPoint B S hS hX hXint
  have hfx : IsGenericPoint (pointsMap B S hS X f x)
      (Set.univ : Set (points B S hS Y)) :=
    isGenericPoint_pointsMap_of_isDominant B S hS f hf hx
  rw [degree_eq_residueFieldDegreeAt B S hS hX hZ hXint hZint (f ≫ g) hx,
    degree_eq_residueFieldDegreeAt B S hS hX hY hXint hYint f hx,
    degree_eq_residueFieldDegreeAt B S hS hY hZ hYint hZint g hfx,
    residueFieldDegreeAt_comp B S hS hY hZ hXint.isDecentSpace hYint.isDecentSpace
      hZint.isDecentSpace f g x]

end AlgebraicGeometry.Space

end
