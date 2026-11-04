module

public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import StacksFrontier.AlgebraicGeometry.EulerCharTruncation.Basic

/-!
# The Euler characteristic of the structure sheaf and the genus

For a scheme `Z` proper over a field `k` and of dimension at most one, the Euler characteristic
of the structure sheaf and the genus of `Z` are the two halves of one computation: cohomology
vanishes above degree one, so the alternating sum is `h⁰ - h¹`, and `h¹` is the genus by
definition while `h⁰` is the dimension of the ring of global functions. This file records that
comparison.

## Main results

* `AlgebraicGeometry.eulerCharacteristic_unit_eq_finrank_globalSections_sub_genus`:
  `χ(Z, 𝒪_Z) = dim_k Γ(Z, 𝒪_Z) - g_Z`.
* `AlgebraicGeometry.genus_eq_finrank_globalSections_mul_genus_toSpecΓ`: when the global
  functions `κ = Γ(Z, 𝒪_Z)` form a field, `g_Z = [κ : k] · g_{Z/κ}`, the genus over `k` being the
  genus over `κ` scaled by the degree of `κ` over `k`.
* `AlgebraicGeometry.one_sub_genus_eq_eulerCharacteristic_unit`: the familiar `1 - g = χ(𝒪)`,
  under the hypothesis `dim_k Γ(Z, 𝒪_Z) = 1` that makes it true.
* `AlgebraicGeometry.finrank_cohomologyOverField_eq_finrank_mul`: the tower law for cohomology
  over a field and over an extension of it, of which the genus statement above is the case of the
  canonical morphism to the spectrum of the global functions.

## Implementation notes

**`1 - g = χ(𝒪)` does not hold in general.** The general identity is
`χ(𝒪_Z) = h⁰(𝒪_Z) - g_Z`, and `h⁰(𝒪_Z) = dim_k Γ(Z, 𝒪_Z)` is `1` only when the global functions
are `k` itself. For a curve whose global functions are a larger field `κ` the value is `[κ : k]`.
So the main statement carries `dim_k Γ(Z, ⊤)` and the specialization
`AlgebraicGeometry.one_sub_genus_eq_eulerCharacteristic_unit` takes `dim_k Γ(Z, ⊤) = 1` as a
hypothesis.

**The two statements are kept separate.** The comparison of cohomology over `k` and over `κ`
holds for any structure morphism to the spectrum of a field compatible with `f`, not only for the
canonical `AlgebraicGeometry.Scheme.toSpecΓ`; for instance the structure morphism of the generic
fibre of a model is of this kind. Combining the two statements gives
`χ_k(Z, 𝒪_Z) = [κ : k] · (1 - g_{Z/κ})` where `κ` is a field.

**No hypothesis beyond properness and the dimension bound.** The following three inputs are
proved, not assumed.

* Vanishing above degree one is Grothendieck's theorem,
  `AlgebraicGeometry.isZero_cohomologyOverField_of_topologicalKrullDim_le`, which needs only
  properness and the dimension bound.
* Coherence of the structure sheaf is
  `Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit`, again from properness alone. It is
  supplied in the statement rather than taken as an instance argument, which is harmless because
  `Stacks.SheafOfModules.IsCoherent` is a `Prop`.
* `h⁰` as the dimension of the global functions is
  `AlgebraicGeometry.finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections`.

Finite dimensionality of the cohomology is never needed: `Module.finrank` is zero on a module
that is not finite dimensional, and every statement below is an equality transported along an
isomorphism or the tower law, both of which hold in that degenerate case too. It is available
from properness, as `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isProper`.

**Joining the two presentations of cohomology.** `AlgebraicGeometry.genus` is defined from
`AlgebraicGeometry.structureSheafCohomology`, the derived functor of global sections taken after
pushforward, whereas `AlgebraicGeometry.eulerCharacteristic` is defined from
`AlgebraicGeometry.cohomologyOverField`, the derived functor of evaluation with scalars
restricted. `AlgebraicGeometry.structureSheafCohomologyIsoCohomologyOverField` identifies them
and is what lets the two definitions meet.

**Why the tower law applies.** `AlgebraicGeometry.cohomologyOverField` restricts scalars on one
and the same derived module — the derived functor of evaluation does not see the structure
morphism — so the cohomology over `k` and the cohomology over `κ` have the same carrier, with
`k` acting through `κ`. That makes the scalar tower definitional, and
`Module.finrank_mul_finrank` applies with no finiteness hypothesis, both modules being free over
a field.

## References

* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
* [Stacks Project, Tag 0BEJ](https://stacks.math.columbia.edu/tag/0BEJ)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The Euler characteristic of the structure sheaf is `dim_k Γ(Z, 𝒪_Z) - g_Z`.** On a scheme
proper over `k` of dimension at most one the cohomology of the structure sheaf vanishes above
degree one, so the alternating sum is `h⁰ - h¹`; the first term is the dimension of the ring of
global functions and the second is the genus.

The familiar `1 - g = χ(𝒪)` is the case `dim_k Γ(Z, ⊤) = 1`, which is
`AlgebraicGeometry.one_sub_genus_eq_eulerCharacteristic_unit`. It is *not* true in general: for a
curve whose global functions form a field `κ` strictly larger than `k` the first term is
`[κ : k]`. -/
public theorem eulerCharacteristic_unit_eq_finrank_globalSections_sub_genus (k : Type u)
    [Field k] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim Z ≤ 1) :
    letI : (SheafOfModules.unit Z.ringCatSheaf).IsCoherent :=
      Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
    letI : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    eulerCharacteristic k f (SheafOfModules.unit Z.ringCatSheaf) =
      (Module.finrank k Γ(Z, ⊤) : ℤ) - (genus f : ℤ) := by
  let : (SheafOfModules.unit Z.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
  let : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have hvan : ∀ m, 2 ≤ m →
      IsZero (cohomologyOverField k f (SheafOfModules.unit Z.ringCatSheaf) m) := fun m hm =>
    isZero_cohomologyOverField_of_topologicalKrullDim_le k f _ (d := 1)
      (by simpa using hdim) (by omega)
  rw [eulerCharacteristic_eq_sub_of_isZero k f _ hvan,
    finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections k f,
    genus_eq_finrank_structureSheafCohomology,
    (structureSheafCohomologyIsoCohomologyOverField k f 1).toLinearEquiv.finrank_eq]

/-- **`1 - g = χ(𝒪)`**, under the hypothesis on the global functions that makes it true.

The hypothesis is stated as an implication inside the statement rather than as a binder because
it mentions the `k`-algebra structure on `Γ(Z, ⊤)` that the structure morphism induces, which the
statement itself has to introduce. -/
public theorem one_sub_genus_eq_eulerCharacteristic_unit (k : Type u) [Field k]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim Z ≤ 1) :
    letI : (SheafOfModules.unit Z.ringCatSheaf).IsCoherent :=
      Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
    letI : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    Module.finrank k Γ(Z, ⊤) = 1 →
      1 - (genus f : ℤ) = eulerCharacteristic k f (SheafOfModules.unit Z.ringCatSheaf) := by
  intro h1
  rw [eulerCharacteristic_unit_eq_finrank_globalSections_sub_genus k f hdim, h1]
  norm_num

/-! ### The genus over the field of global functions -/

/-- The tower law for a module obtained by restricting scalars along a composite ring map: the
`k`-dimension of an `R`-module whose `k`-structure comes from `κ → R` precomposed with `k → κ` is
`[κ : k]` times its `κ`-dimension.

Restriction of scalars along a composite is restriction along each factor in turn, so both scalar
actions are the one `R`-action read through a ring map and the scalar tower is definitional. No
finiteness is needed: a module over a field is free, which is all `Module.finrank_mul_finrank`
asks, and in the infinite-dimensional case both sides are zero. -/
private theorem finrank_restrictScalars_comp {k κ R : Type u} [Field k] [Field κ] [Algebra k κ]
    [Ring R] (ψ : κ →+* R) (D : ModuleCat.{u} R) :
    Module.finrank k ((ModuleCat.restrictScalars (ψ.comp (algebraMap k κ))).obj D) =
      Module.finrank k κ * Module.finrank κ ((ModuleCat.restrictScalars ψ).obj D) := by
  let : Module κ (D : Type u) := ((ModuleCat.restrictScalars ψ).obj D).isModule
  let : Module k (D : Type u) :=
    ((ModuleCat.restrictScalars (ψ.comp (algebraMap k κ))).obj D).isModule
  have : IsScalarTower k κ (D : Type u) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact (Module.finrank_mul_finrank k κ (D : Type u)).symm

/-- **Cohomology over a field and over an extension of it agree up to the degree of the
extension**, for two structure morphisms on the same scheme whose induced maps on global
functions are compatible.

Both sides restrict scalars on the *same* derived module — the derived functor of evaluation on
`Z` does not see the structure morphism — so this is the tower law and nothing more.

The two structure morphisms are arbitrary, not only the canonical
`AlgebraicGeometry.Scheme.toSpecΓ` of
`AlgebraicGeometry.genus_eq_finrank_globalSections_mul_genus_toSpecΓ` below: the compatibility
hypothesis is the whole input. -/
public theorem finrank_cohomologyOverField_eq_finrank_mul (k κ : Type u) [Field k] [Field κ]
    [Algebra k κ] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) (g : Z ⟶ Spec (.of κ))
    (hcompat : ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom =
      ((Scheme.ΓSpecIso (.of κ)).inv ≫ g.appTop).hom.comp (algebraMap k κ))
    (F : Z.Modules) (n : ℕ) :
    Module.finrank k (cohomologyOverField k f F n) =
      Module.finrank k κ * Module.finrank κ (cohomologyOverField κ g F n) := by
  unfold cohomologyOverField
  rw [appLE_top_top_eq_appTop f (by simp), appLE_top_top_eq_appTop g (by simp), hcompat]
  exact finrank_restrictScalars_comp _ _

/-- **The genus over the ground field is the degree of the global functions times the genus over
them.** If the ring `κ = Γ(Z, 𝒪_Z)` of global functions of a scheme `Z` over a field `k` is
itself a field, then `g_{Z/k} = [κ : k] · g_{Z/κ}`, the genus over `κ` being taken along the
canonical morphism `AlgebraicGeometry.Scheme.toSpecΓ`.

This is the tower law applied to `H¹(Z, 𝒪_Z)`: that group is one and the same, carrying an action
of `κ` of which the action of `k` is the restriction.

No properness and no dimension hypothesis: both genera are formed for any scheme over a field,
and the identity is the tower law, which needs neither. -/
public theorem genus_eq_finrank_globalSections_mul_genus_toSpecΓ (k : Type u) [Field k]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) (hκ : IsField Γ(Z, ⊤)) :
    letI : Field Γ(Z, ⊤) := hκ.toField
    letI : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    genus f = Module.finrank k Γ(Z, ⊤) * genus Z.toSpecΓ := by
  let : Field Γ(Z, ⊤) := hκ.toField
  let : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have hcompat : ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom =
      ((Scheme.ΓSpecIso (.of Γ(Z, ⊤))).inv ≫ Z.toSpecΓ.appTop).hom.comp
        (algebraMap k Γ(Z, ⊤)) := by
    have hid : (Scheme.ΓSpecIso (.of Γ(Z, ⊤))).inv ≫ Z.toSpecΓ.appTop = 𝟙 Γ(Z, ⊤) := by
      rw [Scheme.toSpecΓ_appTop]
      exact (Scheme.ΓSpecIso Γ(Z, ⊤)).inv_hom_id
    rw [hid, RingHom.algebraMap_toAlgebra]
    ext x
    rfl
  rw [genus_eq_finrank_structureSheafCohomology,
    (structureSheafCohomologyIsoCohomologyOverField k f 1).toLinearEquiv.finrank_eq,
    genus_eq_finrank_structureSheafCohomology,
    (structureSheafCohomologyIsoCohomologyOverField Γ(Z, ⊤) Z.toSpecΓ
      1).toLinearEquiv.finrank_eq]
  exact finrank_cohomologyOverField_eq_finrank_mul k Γ(Z, ⊤) f Z.toSpecΓ hcompat _ 1

end AlgebraicGeometry

end
