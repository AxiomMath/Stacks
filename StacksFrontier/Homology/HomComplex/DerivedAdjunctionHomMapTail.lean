module

public import StacksFrontier.Homology.HomComplex.DerivedAdjunctionTensorPrefix

/-!
# Absorbing an internal-Hom tail into the transpose of [stacks 0A63]

`StacksDraft.DerivedHom.DerivedHomAdjunction.tensor_map_id_comp_homEquiv` absorbs a prefix of the
source variable into a [stacks 0A63] transpose.  A transpose is just as often followed by a
morphism of the internal Hom it lands in, and when that morphism is the bifunctor applied to a
pair -- contravariantly to a morphism `lam` of the Hom-source and covariantly to a morphism `rho`
of the Hom-target -- it is absorbed too, by dinaturality and naturality in the target.

Composing the two, a transpose with a prefix of its source and a tail of that shape is **one**
transpose, at the triple the prefix and the tail reach, of the tensoring of the prefix with `lam`
followed by the original transposed map and `rho`.  Every variable moves at once: the intermediate
transposes never have to be named.

That is the shape a change-of-rings comparison presents.  Its value is a transpose taken at a pair
of localized complexes -- a K-flat one in the Hom-source and a K-injective one in the Hom-target,
because those are the representatives at which the chain-level map exists -- while the equation it
has to be compared against is a transpose at the pair the comparison is natural at.  The passage
between them is a composite of localization comparisons and K-flat/K-injective presentations in
each variable, and every one of them enters as `lam` or as `rho`.

## Main results

* `StacksDraft.DerivedHom.DerivedHomAdjunction.hom_map_comp_hom_map` -- two internal-Hom tails
  merge into one.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.homEquiv_symm_comp_hom_map` -- a transpose followed
  by the internal Hom of a pair is the transpose of the tensoring of the identity with `lam`,
  followed by the transposed map and `rho`.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.comp_homEquiv_symm_comp_hom_map` -- **the
  absorption**: with a prefix of the source variable as well, still one transpose.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.comp_homEquiv_symm_comp_hom_map_eq_iff` -- so an
  equation between such a composite and a transpose at the triple it reaches is an equation of
  morphisms out of a tensor product, with no transpose on either side.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.comp_homEquiv_symm_comp_nested_hom_map` -- the
  absorption at the nesting a change-of-rings comparison presents: four prefix factors and three
  tails, no two of them adjacent, the tails given as data with their identifications.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace StacksDraft.DerivedHom.DerivedHomAdjunction

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
  (d : DerivedHomAdjunction R)

/-- **Two internal-Hom tails merge into one.**

Functoriality of the internal-Hom bifunctor of [stacks 0A63], written with both Hom-source
morphisms in the covariant direction: the Hom-source morphisms compose in the order opposite to the
Hom-target ones. -/
@[reassoc] public theorem hom_map_comp_hom_map
    {L₁ L₂ L₃ M₁ M₂ M₃ : DerivedCategory (ModuleCat.{v} R)} (a₁ : L₂ ⟶ L₁) (b₁ : M₁ ⟶ M₂)
    (a₂ : L₃ ⟶ L₂) (b₂ : M₂ ⟶ M₃) :
    d.hom.map (show (Opposite.op L₁, M₁) ⟶ (Opposite.op L₂, M₂) from (a₁.op, b₁)) ≫
        d.hom.map (show (Opposite.op L₂, M₂) ⟶ (Opposite.op L₃, M₃) from (a₂.op, b₂)) =
      d.hom.map (show (Opposite.op L₁, M₁) ⟶ (Opposite.op L₃, M₃) from
        ((a₂ ≫ a₁).op, b₁ ≫ b₂)) := by
  rw [← d.hom.map_comp]
  rfl

/-- **A transpose followed by the internal Hom of a pair is again a transpose.**

Dinaturality of the transpose of [stacks 0A63] in the Hom-source variable and naturality in its
target, on the inverse transpose: the inverse transpose of `c` followed by
`hom.map (lam.op, rho)` is the inverse transpose of `lam` tensored into the second variable, then
`c`, then `rho`.

Both `lam` and `rho` are arbitrary morphisms, in particular neither has to be invertible and no
object has to be presented as a localized complex. -/
public theorem homEquiv_symm_comp_hom_map
    {X L L' M M' : DerivedCategory (ModuleCat.{v} R)} (lam : L ⟶ L') (rho : M' ⟶ M)
    (c : d.tensor.obj (X, L') ⟶ M') :
    (d.homEquiv X L' M').symm c ≫
        d.hom.map (show (Opposite.op L', M') ⟶ (Opposite.op L, M) from (lam.op, rho)) =
      (d.homEquiv X L M).symm
        (d.tensor.map (show (X, L) ⟶ (X, L') from (𝟙 X, lam)) ≫ c ≫ rho) := by
  apply (d.homEquiv X L M).injective
  have hsplit :
      d.hom.map (show (Opposite.op L', M') ⟶ (Opposite.op L, M) from (lam.op, rho)) =
        d.hom.map (show (Opposite.op L', M') ⟶ (Opposite.op L, M') from (lam.op, 𝟙 M')) ≫
          d.hom.map (show (Opposite.op L, M') ⟶ (Opposite.op L, M) from
            (𝟙 (Opposite.op L), rho)) := by
    rw [← d.hom.map_comp, CategoryTheory.prod_comp, Category.comp_id, Category.id_comp]
  rw [AddEquiv.apply_symm_apply, hsplit, ← Category.assoc, d.homEquiv_naturality_right,
    d.homEquiv_dinaturality, AddEquiv.apply_symm_apply, Category.assoc]

/-- **The absorption: a transpose with a prefix of its source and an internal-Hom tail is one
transpose.**

`StacksDraft.DerivedHom.DerivedHomAdjunction.homEquiv_symm_comp_hom_map` followed by naturality of
the transpose of [stacks 0A63] in its source variable, with the two tensor prefixes merged by
`StacksDraft.DerivedHom.DerivedHomAdjunction.tensor_map_id_comp_tensor_map_id`-style
functoriality: `tensor.map (p, 𝟙 L)` after `tensor.map (𝟙 X', lam)` is `tensor.map (p, lam)`.

The transpose on the right-hand side sits at the triple `(X, L, M)` reached by the prefix and the
tail, not at the triple `(X', L', M')` the given one sits at. -/
public theorem comp_homEquiv_symm_comp_hom_map
    {X X' L L' M M' : DerivedCategory (ModuleCat.{v} R)} (p : X ⟶ X') (lam : L ⟶ L')
    (rho : M' ⟶ M) (c : d.tensor.obj (X', L') ⟶ M') :
    p ≫ (d.homEquiv X' L' M').symm c ≫
          d.hom.map (show (Opposite.op L', M') ⟶ (Opposite.op L, M) from (lam.op, rho)) =
      (d.homEquiv X L M).symm
        (d.tensor.map (show (X, L) ⟶ (X', L') from (p, lam)) ≫ c ≫ rho) := by
  apply (d.homEquiv X L M).injective
  rw [d.homEquiv_naturality_left, d.homEquiv_symm_comp_hom_map, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply, ← Category.assoc, ← Category.assoc, d.tensor_map_comp,
    Category.comp_id, Category.id_comp, Category.assoc]

/-- **An equation between such a composite and a transpose is an equation out of a tensor
product.**

By `StacksDraft.DerivedHom.DerivedHomAdjunction.comp_homEquiv_symm_comp_hom_map` both sides are
transposes at the same triple `(X, L, M)`, and the transpose of [stacks 0A63] is a bijection, so
the equation holds if and only if the morphisms out of `tensor.obj (X, L)` they are the transposes
of agree. -/
public theorem comp_homEquiv_symm_comp_hom_map_eq_iff
    {X X' L L' M M' : DerivedCategory (ModuleCat.{v} R)} (p : X ⟶ X') (lam : L ⟶ L')
    (rho : M' ⟶ M) (c : d.tensor.obj (X', L') ⟶ M') (g : d.tensor.obj (X, L) ⟶ M) :
    p ≫ (d.homEquiv X' L' M').symm c ≫
            d.hom.map (show (Opposite.op L', M') ⟶ (Opposite.op L, M) from (lam.op, rho)) =
          (d.homEquiv X L M).symm g ↔
      d.tensor.map (show (X, L) ⟶ (X', L') from (p, lam)) ≫ c ≫ rho = g := by
  rw [d.comp_homEquiv_symm_comp_hom_map p lam rho c]
  exact (d.homEquiv X L M).symm.injective.eq_iff

/-- **The absorption at the nesting a change-of-rings comparison presents.**

`StacksDraft.DerivedHom.DerivedHomAdjunction.comp_homEquiv_symm_comp_hom_map` with the prefix
split into four factors and the tail into three, nested the way the value of such a comparison
nests them: the innermost tail sits beside the transpose, the middle one one level out and the
outermost one level further, so that no two of them are adjacent.

The three tails are taken as data `θ₁`, `θ₂`, `θ₃` together with the equations identifying them
with `hom.map` of a pair.  The whole nested composite is **one** transpose at the triple the
outermost tail reaches, with the prefix collected in front of it and the three Hom-target morphisms
composed behind the transposed map. -/
public theorem comp_homEquiv_symm_comp_nested_hom_map
    {X₁ X₂ X₃ X₄ P L₁ L₂ M₁ M₂ M₃ M₄ : DerivedCategory (ModuleCat.{v} R)}
    (A : X₁ ⟶ X₂) (B : X₂ ⟶ X₃) (C : X₃ ⟶ X₄) (D : X₄ ⟶ P)
    (c : d.tensor.obj (P, L₁) ⟶ M₁) (b₁ : M₁ ⟶ M₂) (lam : L₂ ⟶ L₁) (b₂ : M₂ ⟶ M₃)
    (b₃ : M₃ ⟶ M₄)
    (θ₁ : d.hom.obj (Opposite.op L₁, M₁) ⟶ d.hom.obj (Opposite.op L₁, M₂))
    (θ₂ : d.hom.obj (Opposite.op L₁, M₂) ⟶ d.hom.obj (Opposite.op L₂, M₃))
    (θ₃ : d.hom.obj (Opposite.op L₂, M₃) ⟶ d.hom.obj (Opposite.op L₂, M₄))
    (h₁ : θ₁ = d.hom.map (show (Opposite.op L₁, M₁) ⟶ (Opposite.op L₁, M₂) from
      ((𝟙 L₁).op, b₁)))
    (h₂ : θ₂ = d.hom.map (show (Opposite.op L₁, M₂) ⟶ (Opposite.op L₂, M₃) from (lam.op, b₂)))
    (h₃ : θ₃ = d.hom.map (show (Opposite.op L₂, M₃) ⟶ (Opposite.op L₂, M₄) from
      ((𝟙 L₂).op, b₃))) :
    A ≫ ((B ≫ (C ≫ D ≫ (d.homEquiv P L₁ M₁).symm c ≫ θ₁) ≫ θ₂) ≫ θ₃) =
      (A ≫ B ≫ C ≫ D) ≫ (d.homEquiv P L₁ M₁).symm c ≫
        d.hom.map (show (Opposite.op L₁, M₁) ⟶ (Opposite.op L₂, M₄) from
          (lam.op, b₁ ≫ b₂ ≫ b₃)) := by
  subst h₁ h₂ h₃
  simp only [Category.assoc, d.hom_map_comp_hom_map, Category.comp_id, Category.id_comp]

end StacksDraft.DerivedHom.DerivedHomAdjunction

end
