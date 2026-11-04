module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Restriction
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SerreCondition
public import StacksFrontier.AlgebraicGeometry.Divisors.EmbeddedPoints.DimensionOne
public import StacksFrontier.AlgebraicGeometry.Meromorphic.NoEmbeddedPoints
public import StacksFrontier.AlgebraicGeometry.Properties.SerreStructureSheaf

/-!
# A function vanishing at every generic point of an `(S₁)` scheme is zero

On a locally Noetherian scheme satisfying Serre's condition `(S₁)` — equivalently, with no
embedded points — a global function whose germ at the generic point of every irreducible
component is zero is itself zero. On an effective Cartier divisor in a locally Noetherian
normal scheme that hypothesis holds, so the same conclusion is available there.

This is the step of [Stacks, Tag 0AXA] which concludes, from the vanishing of a function at the
generic points of the components of a divisor `Z`, that the function is a section of the ideal
sheaf of `Z`. The source assembles it from three results, all of which this library already
has: `Z` is `(S₁)` by [Stacks, Tag 0B3S], so it has no embedded associated points by
[Stacks, Tag 0346], so restriction of sections of a quasi-coherent sheaf to an open containing
the generic points is injective by [Stacks, Tag 0B3M]. What was missing is the assembly, which
is what this file supplies.

## Main definitions

* `AlgebraicGeometry.vanishingOpen`: the largest open on which a global function vanishes,
  namely the union of all the opens on which it restricts to zero.

## Main results

* `AlgebraicGeometry.eq_zero_of_germ_genericPoints_eq_zero_of_hasNoEmbeddedPoints`: the
  conclusion from the absence of embedded points.
* `AlgebraicGeometry.hasNoEmbeddedPoints_iff_hasPropertySk_one`: [Stacks, Tag 0346] for the
  structure sheaf, so that the absence of embedded points is Serre's condition `(S₁)` for the
  scheme and not merely for a module on it.
* `AlgebraicGeometry.eq_zero_of_germ_genericPoints_eq_zero`: the conclusion from `(S₁)`.
* `AlgebraicGeometry.eq_zero_of_germ_genericPoints_eq_zero_of_isEffectiveCartierDivisor`: the
  conclusion on an effective Cartier divisor in a locally Noetherian normal scheme, which is
  the form [Stacks, Tag 0AXA] uses.

## Implementation notes

[Stacks, Tag 0B3M] is stated for an *open* containing every weakly associated point, and the
generic points of the irreducible components are not open. The open interposed here is
`AlgebraicGeometry.vanishingOpen`, the union of the opens on which the function restricts to
zero: a function whose germ at a point is zero restricts to zero on some neighbourhood of that
point, so vanishing at the generic points puts them all inside that union, and the function
restricts to zero on the union itself by the sheaf axiom.

Serre's condition on a scheme, `AlgebraicGeometry.HasPropertySk`, compares the depth of a local
ring with its Krull dimension, while the condition on a sheaf of modules,
`AlgebraicGeometry.SheafHasPropertySk`, compares the depth of a stalk with the dimension of the
support of that stalk; [Stacks, Tag 0346] is stated in the second form. The two agree for the
structure sheaf read as a module over itself, because its stalk is the local ring; the
comparison is `AlgebraicGeometry.structureSheaf_sheafHasPropertySk_one_iff` and it needs the
two definitionally equal module structures on the stalk of a presheaf of modules to be
identified, which is `Stacks.SheafOfModules.stalkModule_eq`.

No `@[stacks]` attribute is placed here. Tag 0346 is already carried by
`AlgebraicGeometry.hasNoEmbeddedAssociatedPoints_iff_hasPropertySk_one` in its stated
generality, and the declarations below are its specialization to the structure sheaf together
with the sheaf-theoretic assembly, not a further clause of the tag.

## References

* [Stacks Project, Tag 0AXA](https://stacks.math.columbia.edu/tag/0AXA)
* [Stacks Project, Tag 0346](https://stacks.math.columbia.edu/tag/0346)
* [Stacks Project, Tag 0B3M](https://stacks.math.columbia.edu/tag/0B3M)
* [Stacks Project, Tag 0B3S](https://stacks.math.columbia.edu/tag/0B3S)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-! ### The open on which a global function vanishes -/

/-- The union of the opens on which a global function restricts to zero. -/
def vanishingOpen (X : Scheme.{u}) (s : Γ(X, ⊤)) : X.Opens :=
  ⨆ V : {V : X.Opens //
    (ConcreteCategory.hom (X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op)) s = 0}, V.1

/-- A global function restricts to zero on the union of the opens on which it restricts to
zero: the restrictions agree locally, so the sheaf axiom identifies them. -/
theorem res_vanishingOpen (X : Scheme.{u}) (s : Γ(X, ⊤)) :
    (ConcreteCategory.hom
      (X.presheaf.map (homOfLE le_top : vanishingOpen X s ⟶ ⊤).op)) s = 0 := by
  refine TopCat.Presheaf.IsSheaf.section_ext
    (X.sheaf.property : TopCat.Presheaf.IsSheaf X.presheaf) (U := op (vanishingOpen X s)) ?_
  intro x hx
  obtain ⟨V, hxV⟩ := Opens.mem_iSup.mp hx
  have key : (ConcreteCategory.hom (X.presheaf.map
        (homOfLE (le_iSup _ V) : V.1 ⟶ vanishingOpen X s).op))
      ((ConcreteCategory.hom (X.presheaf.map
        (homOfLE le_top : vanishingOpen X s ⟶ ⊤).op)) s) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    exact V.2
  exact ⟨V.1, le_iSup _ V, hxV, key.trans (map_zero _).symm⟩

/-- A point at which the germ of a global function is zero lies in the open on which the
function vanishes: the germ of a section of a presheaf is zero only if the section restricts to
zero on some neighbourhood. -/
theorem mem_vanishingOpen (X : Scheme.{u}) (s : Γ(X, ⊤)) {x : X}
    (hx : (ConcreteCategory.hom (X.presheaf.germ ⊤ x (by trivial))) s = 0) :
    x ∈ vanishingOpen X s := by
  have hx' : X.presheaf.germ ⊤ x (by trivial) s = X.presheaf.germ ⊤ x (by trivial) 0 := by
    rw [map_zero]; exact hx
  obtain ⟨W, hxW, iU, iV, e⟩ := X.presheaf.germ_eq x (by trivial) (by trivial) s 0 hx'
  have hW : (ConcreteCategory.hom (X.presheaf.map (homOfLE le_top : W ⟶ ⊤).op)) s = 0 := by
    have hiU : (homOfLE le_top : W ⟶ ⊤) = iU := Subsingleton.elim _ _
    rw [hiU, e, map_zero]
  exact le_iSup (fun V : {V : X.Opens //
    (ConcreteCategory.hom (X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op)) s = 0} => V.1)
    ⟨W, hW⟩ hxW

/-! ### Vanishing at the generic points -/

/-- **The glue step of [Stacks, Tag 0AXA].** On a locally Noetherian scheme with no embedded
points, a global function whose germ at the generic point of every irreducible component is
zero is itself zero.

The weakly associated points of such a scheme are exactly those generic points
(`AlgebraicGeometry.schemeWeaklyAssociatedPoints_eq_genericPoints_of_hasNoEmbeddedPoints`), so
they all lie in the open on which the function vanishes, and restriction of sections to an open
containing every weakly associated point is injective by [Stacks, Tag 0B3M]. -/
theorem eq_zero_of_germ_genericPoints_eq_zero_of_hasNoEmbeddedPoints (X : Scheme.{u})
    [IsLocallyNoetherian X] (hX : HasNoEmbeddedPoints X) (s : Γ(X, ⊤))
    (hs : ∀ x ∈ genericPoints X,
      (ConcreteCategory.hom (X.presheaf.germ ⊤ x (by trivial))) s = 0) :
    s = 0 := by
  have hsub : Stacks.Divisors.weaklyAssociatedPoints (structureSheafModule X) ⊆
      (vanishingOpen X s : Set X) := by
    intro x hx
    refine mem_vanishingOpen X s (hs x ?_)
    rw [← schemeWeaklyAssociatedPoints_eq_genericPoints_of_hasNoEmbeddedPoints X hX]
    exact hx
  exact restriction_injective_of_weaklyAssociatedPoints_subset (structureSheafModule X)
    (vanishingOpen X s) hsub ((res_vanishingOpen X s).trans (map_zero _).symm)

/-! ### Serre's condition `(S₁)` for a scheme and for its structure sheaf -/


/-- [Stacks, Tag 0346] for the structure sheaf: a locally Noetherian scheme has no embedded
points exactly when it satisfies Serre's condition `(S₁)`. -/
theorem hasNoEmbeddedPoints_iff_hasPropertySk_one (X : Scheme.{u}) [IsLocallyNoetherian X] :
    HasNoEmbeddedPoints X ↔ HasPropertySk X 1 := by
  let F := SheafOfModules.unit X.ringCatSheaf
  let : F.IsCoherent := by
    dsimp [F]
    infer_instance
  rw [← structureSheaf_sheafHasPropertySk_one_iff X]
  simpa only [HasNoEmbeddedPoints, IsEmbeddedPoint] using
    hasNoEmbeddedAssociatedPoints_iff_hasPropertySk_one X F

/-- **The glue step of [Stacks, Tag 0AXA], in its `(S₁)` form.** On a locally Noetherian scheme
satisfying Serre's condition `(S₁)`, a global function whose germ at the generic point of every
irreducible component is zero is itself zero. -/
theorem eq_zero_of_germ_genericPoints_eq_zero (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hX : HasPropertySk X 1) (s : Γ(X, ⊤))
    (hs : ∀ x ∈ genericPoints X,
      (ConcreteCategory.hom (X.presheaf.germ ⊤ x (by trivial))) s = 0) :
    s = 0 :=
  eq_zero_of_germ_genericPoints_eq_zero_of_hasNoEmbeddedPoints X
    ((hasNoEmbeddedPoints_iff_hasPropertySk_one X).mpr hX) s hs

/-- **The glue step of [Stacks, Tag 0AXA], at an effective Cartier divisor.** On an effective
Cartier divisor `Z` in a locally Noetherian normal scheme, a global function on `Z` whose germ
at the generic point of every irreducible component of `Z` is zero is itself zero.

`Z` satisfies Serre's condition `(S₁)` by [Stacks, Tag 0B3S], so it has no embedded points by
[Stacks, Tag 0346], so its weakly associated points are its generic points, and restriction to
the open on which the function vanishes is injective by [Stacks, Tag 0B3M]. -/
theorem eq_zero_of_germ_genericPoints_eq_zero_of_isEffectiveCartierDivisor (X : Scheme.{u})
    [IsLocallyNoetherian X] [IsNormal X] (I : X.IdealSheafData)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (s : Γ(I.subscheme, ⊤))
    (hs : ∀ x ∈ genericPoints I.subscheme,
      (ConcreteCategory.hom (I.subscheme.presheaf.germ ⊤ x (by trivial))) s = 0) :
    s = 0 :=
  have : IsLocallyNoetherian I.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  eq_zero_of_germ_genericPoints_eq_zero I.subscheme
    (isNormal_effectiveCartierDivisor_hasPropertySk_one X I hI) s hs

end AlgebraicGeometry

end
