module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LineBundleAffineSpaceBundle
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LocalizationSurjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.DecompositionExistence
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Composition

/-!
# The branch projections of Tag 0F97 are flat of relative dimension one

Let `Y` be a scheme, let `L₁` and `L₂` be invertible `𝒪_Y`-modules, let `s` be a global section
of `L₁ ⊗_{𝒪_Y} L₂` and let `i : D → Y` be its zero scheme, as in [Stacks, Tag 0F97]. Condition
(4) of the tag identifies each branch `Dᵢ` of the zero scheme of `z₁ ⊗ z₂ - p^*s` with the line
bundle `\underline{\Spec}_D(\Sym^*(L^{⊗ -1}|_D))` over `D`, by an isomorphism over `D`. The
structure morphism of the total space of a line bundle is locally of finite type
(`Stacks.LineBundle.Situation.locallyOfFiniteType_totalSpaceToBase`), flat
(`Stacks.LineBundle.Situation.flat_totalSpaceToBase`) and of relative dimension one
(`Stacks.LineBundle.Situation.relativeDimension_totalSpaceToBase`); this file carries those three
properties across the identification of condition (4), so that the two projections `pᵢ : Dᵢ ⟶ D`
of the tag's diagram have them.

All three properties are `Prop`-valued, so there is nothing to transport but the morphism: an
isomorphism is an open immersion and hence flat and locally of finite type, so the composite
`branchᵢ.hom ≫ totalSpaceToBase` inherits each property from `totalSpaceToBase`, and the field
equation `Decomposition.branchᵢ_toBase` says that composite is `pᵢ`.

## Main results

* `Stacks.Chow.TensorZeroScheme.Decomposition.locallyOfFiniteType_p₁`, `flat_p₁` and
  `relativeDimension_p₁`, and their companions `locallyOfFiniteType_p₂`, `flat_p₂`,
  `relativeDimension_p₂`: **each branch projection of a decomposition of [Stacks, Tag 0F97] is
  locally of finite type, flat, and of relative dimension one.**
* `Stacks.Chow.TensorZeroScheme.locallyOfFiniteType_proj₁`, `flat_proj₁`,
  `relativeDimension_proj₁` and their companions for `proj₂`: the same three properties for the
  two projections of the canonical decomposition `Stacks.Chow.TensorZeroScheme.decomposition`.

## Implementation notes

The three transports are proved once, for an arbitrary line-bundle situation `D` and an arbitrary
morphism presented as an isomorphism onto `D.totalSpace` followed by `D.totalSpaceToBase`
(`Stacks.Chow.TensorZeroScheme.locallyOfFiniteType_of_iso_totalSpace` and its two companions).
Stating them that way is what makes them usable here: the base of
`Stacks.Chow.TensorZeroScheme.branchSituation` agrees with the zero scheme `D` only at default
transparency, so a goal about `pᵢ`, whose target is spelled as the zero scheme, offers instance
search a morphism into `(branchSituation …).X` that it cannot see through. In the general lemmas
every target is `D.X`, instance search succeeds, and the single transparency crossing happens once
at the use site, where `exact` performs it for free.

The morphism is a variable in those lemmas, so the equation presenting it is discharged by
`subst`: no `eqToHom` and no recursor on data appears anywhere below.
`AlgebraicGeometry.RelativeDimension` takes a `[LocallyOfFiniteType f]` argument, and that class
is `Prop`-valued, so after the substitution the two finite-type proofs in play are equal by proof
irrelevance.

The two finite-type results are `theorem`s rather than `instance`s, matching the field
`Stacks.Chow.TensorZeroScheme.Decomposition.p_locallyOfFiniteType` of
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.WholeTag`: they are consumed as the `letI`
supplying the argument of `AlgebraicGeometry.RelativeDimension`.

No `@[stacks]` attribute is attached. Condition (4) is registered where the identification is
built, and condition (2) is registered on the structure morphism `p : L ⟶ Y` in
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.FlatRelativeDimension`; the statements here
are consequences of condition (4), not further clauses of the tag.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.TensorZeroScheme

section Transport

variable {D : Stacks.LineBundle.Situation.{u}} {Z : Scheme.{u}} (e : Z ≅ D.totalSpace)
  {g : Z ⟶ D.X} (hg : e.hom ≫ D.totalSpaceToBase = g)

include hg in
/-- **A morphism identifying its source with the total space of a line bundle over the target is
locally of finite type.** An isomorphism is an open immersion and so locally of finite type, and
so is the structure morphism of the total space of a line bundle. -/
theorem locallyOfFiniteType_of_iso_totalSpace : LocallyOfFiniteType g := by
  subst hg
  exact locallyOfFiniteType_comp _ _

include hg in
/-- **A morphism identifying its source with the total space of a line bundle over the target is
flat.** An isomorphism is an open immersion and so flat, and the total space of a line bundle is
flat over the scheme the bundle lives on. -/
theorem flat_of_iso_totalSpace : AlgebraicGeometry.Flat g := by
  subst hg
  have : AlgebraicGeometry.Flat D.totalSpaceToBase := D.flat_totalSpaceToBase
  infer_instance

include hg in
/-- **A morphism identifying its source with the total space of a line bundle over the target has
relative dimension one.** The isomorphism is flat of relative dimension zero and the structure
morphism of the total space has relative dimension one, so the composite has relative dimension
`0 + 1`. -/
theorem relativeDimension_of_iso_totalSpace :
    letI : LocallyOfFiniteType g := locallyOfFiniteType_of_iso_totalSpace e hg
    AlgebraicGeometry.RelativeDimension g 1 := by
  subst hg
  have h := AlgebraicGeometry.RelativeDimension.comp_of_flat e.hom D.totalSpaceToBase
    (Stacks.Chow.relativeDimension_of_isIso _) D.relativeDimension_totalSpaceToBase
  rwa [Nat.zero_add] at h

end Transport

variable (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤))

include h₁ h₂ in
/-- **The first branch projection `p₁ : D₁ ⟶ D` of [Stacks, Tag 0F97] is locally of finite
type.** Condition (4) presents it as an isomorphism onto the total space of a line bundle over
`D` followed by that bundle's structure morphism. -/
theorem Decomposition.locallyOfFiniteType_p₁ (R : Decomposition Y L₁ L₂ s) :
    LocallyOfFiniteType R.p₁ :=
  locallyOfFiniteType_of_iso_totalSpace R.branch₁ R.branch₁_toBase

include h₁ h₂ in
/-- **The second branch projection `p₂ : D₂ ⟶ D` of [Stacks, Tag 0F97] is locally of finite
type.** -/
theorem Decomposition.locallyOfFiniteType_p₂ (R : Decomposition Y L₁ L₂ s) :
    LocallyOfFiniteType R.p₂ :=
  locallyOfFiniteType_of_iso_totalSpace R.branch₂ R.branch₂_toBase

include h₁ h₂ in
/-- **The first branch projection `p₁ : D₁ ⟶ D` of [Stacks, Tag 0F97] is flat.** -/
theorem Decomposition.flat_p₁ (R : Decomposition Y L₁ L₂ s) :
    AlgebraicGeometry.Flat R.p₁ :=
  flat_of_iso_totalSpace R.branch₁ R.branch₁_toBase

include h₁ h₂ in
/-- **The second branch projection `p₂ : D₂ ⟶ D` of [Stacks, Tag 0F97] is flat.** -/
theorem Decomposition.flat_p₂ (R : Decomposition Y L₁ L₂ s) :
    AlgebraicGeometry.Flat R.p₂ :=
  flat_of_iso_totalSpace R.branch₂ R.branch₂_toBase

include h₁ h₂ in
/-- **The first branch projection `p₁ : D₁ ⟶ D` of [Stacks, Tag 0F97] has relative dimension
one.** It is the structure morphism of a line bundle over `D` read through condition (4). -/
theorem Decomposition.relativeDimension_p₁ (R : Decomposition Y L₁ L₂ s) :
    letI : LocallyOfFiniteType R.p₁ := Decomposition.locallyOfFiniteType_p₁ Y L₁ L₂ s R
    AlgebraicGeometry.RelativeDimension R.p₁ 1 :=
  relativeDimension_of_iso_totalSpace R.branch₁ R.branch₁_toBase

include h₁ h₂ in
/-- **The second branch projection `p₂ : D₂ ⟶ D` of [Stacks, Tag 0F97] has relative dimension
one.** -/
theorem Decomposition.relativeDimension_p₂ (R : Decomposition Y L₁ L₂ s) :
    letI : LocallyOfFiniteType R.p₂ := Decomposition.locallyOfFiniteType_p₂ Y L₁ L₂ s R
    AlgebraicGeometry.RelativeDimension R.p₂ 1 :=
  relativeDimension_of_iso_totalSpace R.branch₂ R.branch₂_toBase

/-! ### The two projections of the canonical decomposition

The projections of `Stacks.Chow.TensorZeroScheme.decomposition` are literally
`Stacks.Chow.TensorZeroScheme.proj₁` and `proj₂`, so the six results above specialize with no
transport. -/

include h₁ h₂ in
/-- **The projection `p₁ : D₁ ⟶ D` of the diagram of [Stacks, Tag 0F97] is locally of finite
type.** -/
theorem locallyOfFiniteType_proj₁ : LocallyOfFiniteType (proj₁ Y L₁ L₂ s) :=
  Decomposition.locallyOfFiniteType_p₁ Y L₁ L₂ s (decomposition Y L₁ L₂ s)

include h₁ h₂ in
/-- **The projection `p₂ : D₂ ⟶ D` of the diagram of [Stacks, Tag 0F97] is locally of finite
type.** -/
theorem locallyOfFiniteType_proj₂ : LocallyOfFiniteType (proj₂ Y L₁ L₂ s) :=
  Decomposition.locallyOfFiniteType_p₂ Y L₁ L₂ s (decomposition Y L₁ L₂ s)

include h₁ h₂ in
/-- **The projection `p₁ : D₁ ⟶ D` of the diagram of [Stacks, Tag 0F97] is flat.** -/
theorem flat_proj₁ : AlgebraicGeometry.Flat (proj₁ Y L₁ L₂ s) :=
  Decomposition.flat_p₁ Y L₁ L₂ s (decomposition Y L₁ L₂ s)

include h₁ h₂ in
/-- **The projection `p₂ : D₂ ⟶ D` of the diagram of [Stacks, Tag 0F97] is flat.** -/
theorem flat_proj₂ : AlgebraicGeometry.Flat (proj₂ Y L₁ L₂ s) :=
  Decomposition.flat_p₂ Y L₁ L₂ s (decomposition Y L₁ L₂ s)

include h₁ h₂ in
/-- **The projection `p₁ : D₁ ⟶ D` of the diagram of [Stacks, Tag 0F97] has relative dimension
one.** -/
theorem relativeDimension_proj₁ :
    letI : LocallyOfFiniteType (proj₁ Y L₁ L₂ s) := locallyOfFiniteType_proj₁ Y L₁ L₂ s
    AlgebraicGeometry.RelativeDimension (proj₁ Y L₁ L₂ s) 1 :=
  Decomposition.relativeDimension_p₁ Y L₁ L₂ s (decomposition Y L₁ L₂ s)

include h₁ h₂ in
/-- **The projection `p₂ : D₂ ⟶ D` of the diagram of [Stacks, Tag 0F97] has relative dimension
one.** -/
theorem relativeDimension_proj₂ :
    letI : LocallyOfFiniteType (proj₂ Y L₁ L₂ s) := locallyOfFiniteType_proj₂ Y L₁ L₂ s
    AlgebraicGeometry.RelativeDimension (proj₂ Y L₁ L₂ s) 1 :=
  Decomposition.relativeDimension_p₂ Y L₁ L₂ s (decomposition Y L₁ L₂ s)

end Stacks.Chow.TensorZeroScheme

end
