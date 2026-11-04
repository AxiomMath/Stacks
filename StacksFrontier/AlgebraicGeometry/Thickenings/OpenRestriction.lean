module

public import StacksFrontier.AlgebraicGeometry.Conormal.SquareFlatIso
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange

/-!
# Universal first-order thickenings commute with restriction to opens

Let `h : Z ⟶ X` be a formally unramified morphism of schemes and let `V ⊆ Z` and `U ⊆ X` be
opens with `h(V) ⊆ U`. Let `Z ⊂ Z'` be a universal first-order thickening of `h` over `X`.
Then:

* the restriction `h|_V : V ⟶ U` is again formally unramified;
* the universal first-order thickening of `V` over `U` is the open subscheme `V' ⊆ Z'`
  characterised by `V = Z ∩ V'`;
* consequently `𝒞_{Z/X}|_V = 𝒞_{V/U}`.

This is [Stacks Project, Tag 04FA].

## Main definitions

* `Stacks.Thickenings.UniversalFirstOrderThickening.ambientOpens` is the open `V' ⊆ Z'` of the
  ambient scheme of a universal first-order thickening attached to an open `V ⊆ Z`.
* `Stacks.Thickenings.UniversalFirstOrderThickening.restrict` is the resulting universal
  first-order thickening of `h|_V : V ⟶ U`, with ambient scheme `V'`.

## Main results

* `Stacks.Thickenings.formallyUnramified_resLE`: the restriction of a formally unramified
  morphism to compatible opens of source and target is formally unramified.
* `Stacks.Thickenings.UniversalFirstOrderThickening.preimage_ambientOpens` and
  `Stacks.Thickenings.UniversalFirstOrderThickening.ambientOpens_le_preimage`: the open `V'`
  attached to `V` meets the closed subscheme in exactly `V`, and lies over `U`;
  `Stacks.Thickenings.UniversalFirstOrderThickening.isUniversal_resLE` is the universal property
  there.
* `Stacks.Thickenings.isIso_universalImmersionConormalSheafMap_resLE` and
  `Stacks.Thickenings.isIso_universalConormalSheafMap_resLE`: the canonical morphism of conormal
  sheaves `𝒞_{Z/X}|_V ⟶ 𝒞_{V/U}` of [Stacks Project, Tag 04F7] is an isomorphism — the second at
  the thickenings chosen by `Stacks.Thickenings.universalFirstOrderThickening`, so that the two
  sheaves are literally the conormal sheaves of [Stacks Project, Tag 04F4]. Both come from
  `Stacks.Thickenings.isIso_universalImmersionConormalSheafMap_of_isPullback`, which asks only
  for a flat cartesian comparison.
* `Stacks.Thickenings.isPullback_resLE_of_preimage_eq`: the restriction square of a morphism over
  an open of the target is cartesian, which is what makes those comparisons flat base changes.

## Implementation notes

The open `V'` attached to `V` is produced by `Stacks.Thickenings.IsThickening.opensCongr`: the
inclusion of a first-order thickening is a homeomorphism on points, so the opens of `Z` and of
`Z'` correspond, and the correspondence inverts taking preimages along the inclusion. That is
exactly the characterisation `V = Z ∩ V'` of the source, so the universal property is stated for
an arbitrary open `V'` of `Z'` satisfying it rather than only for the one so produced.

Everything is stated for an *arbitrary* universal first-order thickening of `h` rather than for
the one chosen by `Stacks.Thickenings.universalFirstOrderThickening`; the statements at the chosen
thickening are the specialisations. The universal property of the restriction to an arbitrary
open `V'` with `V = Z ∩ V'` is `Stacks.Thickenings.isUniversalFirstOrderThickening_resLE`.

The conormal clause is deduced from flat base change for the conormal sheaf of an immersion,
`Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat` ([Stacks Project, Tag 0473]), and not
from an affine computation. The canonical morphism of thickenings
`Stacks.Thickenings.universalFirstOrderThickeningMap` out of a universal first-order thickening
of `h|_V` is the canonical isomorphism onto `V'` followed by the open immersion `V' ⟶ Z'`, by the
uniqueness clause of [Stacks Project, Tag 04F7]; so the square of inclusions is cartesian — it is
the restriction square of `Z ⊂ Z'` over `V'`, pasted with a square whose vertical morphisms are
isomorphisms — and its ambient vertical morphism is flat.

## References

* [Stacks Project, Tag 04FA](https://stacks.math.columbia.edu/tag/04FA)
* [Stacks Project, Tag 04F3](https://stacks.math.columbia.edu/tag/04F3)
* [Stacks Project, Tag 04F4](https://stacks.math.columbia.edu/tag/04F4)
* [Stacks Project, Tag 04F7](https://stacks.math.columbia.edu/tag/04F7)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
* [Stacks Project, Tag 09ZU](https://stacks.math.columbia.edu/tag/09ZU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

variable {Z X : Scheme.{u}} {h : Z ⟶ X}

/-! ### Formal unramifiedness of a restriction to opens -/

/-- **Formal unramifiedness restricts to opens.** If `h : Z ⟶ X` is formally unramified and
`V ⊆ Z`, `U ⊆ X` are opens with `h(V) ⊆ U`, then `h|_V : V ⟶ U` is formally unramified. -/
@[stacks 04FA "formal unramifiedness of the restriction"]
theorem formallyUnramified_resLE (h : Z ⟶ X) [FormallyUnramified h] {U : X.Opens} {V : Z.Opens}
    (hVU : V ≤ h ⁻¹ᵁ U) : FormallyUnramified (h.resLE U V hVU) :=
  let : IsZariskiLocalAtSource (@FormallyUnramified : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @FormallyUnramified) (Q := @RingHom.FormallyUnramified)
  let : IsZariskiLocalAtTarget (@FormallyUnramified : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (P := @FormallyUnramified) (Q := @RingHom.FormallyUnramified)
  IsZariskiLocalAtSource.resLE (P := @FormallyUnramified) hVU inferInstance

/-! ### The restriction square of a morphism over an open of the target -/

/-- **The restriction square of a morphism over an open of the target is cartesian**, for an open
`V` of the source which is exactly the preimage of the open `W` of the target: the morphisms
`i.resLE W V`, `ι_V`, `ι_W` and `i` form a pullback square. This generalises
`AlgebraicGeometry.isPullback_resLE_preimage`, which is the case `V = i^{-1}W` on the nose. -/
theorem isPullback_resLE_of_preimage_eq {Z' : Scheme.{u}} (i : Z ⟶ Z') {W : Z'.Opens}
    {V : Z.Opens} (hWV : i ⁻¹ᵁ W = V) : IsPullback (i.resLE W V hWV.ge) V.ι W.ι i :=
  IsOpenImmersion.isPullback _ _ _ _ (Scheme.Hom.resLE_comp_ι i hWV.ge).symm
    (by simp only [Scheme.Opens.opensRange_ι, hWV])

namespace UniversalFirstOrderThickening

/-! ### The open of the thickening attached to an open of the closed subscheme -/

/-- **The open `V' ⊆ Z'` of the ambient scheme of a universal first-order thickening attached to
an open `V ⊆ Z`.** The inclusion `Z ⟶ Z'` is a homeomorphism on points, so it matches the opens
of `Z` with the opens of `Z'`; `V'` is the open matching `V`, and it is characterised by
`V = Z ∩ V'` (`Stacks.Thickenings.UniversalFirstOrderThickening.preimage_ambientOpens`). -/
noncomputable def ambientOpens (t : UniversalFirstOrderThickening h) (V : Z.Opens) :
    t.ambient.Opens :=
  t.isUniversal.isFirstOrderThickening.isThickening.opensCongr V

/-- **The open `V'` meets the closed subscheme in exactly `V`**, that is `V = Z ∩ V'`. This is
the characterisation of `V'` in [Stacks Project, Tag 04FA]. -/
theorem preimage_ambientOpens (t : UniversalFirstOrderThickening h) (V : Z.Opens) :
    t.inclusion ⁻¹ᵁ t.ambientOpens V = V :=
  t.isUniversal.isFirstOrderThickening.isThickening.preimage_opensCongr V

/-- **The open `V'` lies over `U`**: if `h(V) ⊆ U`, then the structure morphism `Z' ⟶ X`
maps `V'` into `U`. -/
theorem ambientOpens_le_preimage (t : UniversalFirstOrderThickening h) {U : X.Opens}
    {V : Z.Opens} (hVU : V ≤ h ⁻¹ᵁ U) : t.ambientOpens V ≤ t.toBase ⁻¹ᵁ U := by
  intro y hy
  obtain ⟨z, hz⟩ := t.isUniversal.isFirstOrderThickening.isThickening.2 y
  have hzV : z ∈ V := (t.preimage_ambientOpens V).le (show t.inclusion.base z ∈ _ from hz ▸ hy)
  have hzU : (t.inclusion ≫ t.toBase).base z ∈ U := by
    rw [t.isUniversal.inclusion_toBase]
    exact hVU hzV
  rw [← hz]
  simpa using hzU

/-- **Stacks Project, Tag 04FA, the second assertion at the open attached to `V`.** The
restrictions of the inclusion and of the structure morphism of a universal first-order thickening
of `h : Z ⟶ X` to the open `V'` attached to `V ⊆ Z` are a universal first-order thickening of
`h|_V : V ⟶ U` over `U`. -/
theorem isUniversal_resLE (t : UniversalFirstOrderThickening h) {U : X.Opens} {V : Z.Opens}
    (hVU : V ≤ h ⁻¹ᵁ U) :
    IsUniversalFirstOrderThickening (h.resLE U V hVU)
      (t.inclusion.resLE (t.ambientOpens V) V (t.preimage_ambientOpens V).ge)
      (t.toBase.resLE U (t.ambientOpens V) (t.ambientOpens_le_preimage hVU)) :=
  isUniversalFirstOrderThickening_resLE t.isUniversal (t.preimage_ambientOpens V)
    (t.ambientOpens_le_preimage hVU) hVU

/-- **Stacks Project, Tag 04FA, the second assertion, as a universal first-order thickening.**
The universal first-order thickening of `h|_V : V ⟶ U` whose ambient scheme is the open
`V' ⊆ Z'` of `Stacks.Thickenings.UniversalFirstOrderThickening.ambientOpens`. -/
noncomputable def restrict (t : UniversalFirstOrderThickening h) {U : X.Opens} {V : Z.Opens}
    (hVU : V ≤ h ⁻¹ᵁ U) : UniversalFirstOrderThickening (h.resLE U V hVU) where
  ambient := (t.ambientOpens V).toScheme
  inclusion := t.inclusion.resLE (t.ambientOpens V) V (t.preimage_ambientOpens V).ge
  toBase := t.toBase.resLE U (t.ambientOpens V) (t.ambientOpens_le_preimage hVU)
  isUniversal := t.isUniversal_resLE hVU

/-- The ambient scheme of `Stacks.Thickenings.UniversalFirstOrderThickening.restrict` is the
open subscheme `V'` of `Z'`. -/
@[simp]
theorem restrict_ambient (t : UniversalFirstOrderThickening h) {U : X.Opens} {V : Z.Opens}
    (hVU : V ≤ h ⁻¹ᵁ U) : (t.restrict hVU).ambient = (t.ambientOpens V).toScheme :=
  rfl

/-- The inclusion of `Stacks.Thickenings.UniversalFirstOrderThickening.restrict` is the
restriction of the inclusion `Z ⟶ Z'` to `V ⟶ V'`. -/
@[simp]
theorem restrict_inclusion (t : UniversalFirstOrderThickening h) {U : X.Opens} {V : Z.Opens}
    (hVU : V ≤ h ⁻¹ᵁ U) : (t.restrict hVU).inclusion =
      t.inclusion.resLE (t.ambientOpens V) V (t.preimage_ambientOpens V).ge :=
  rfl

/-- The structure morphism of `Stacks.Thickenings.UniversalFirstOrderThickening.restrict` is the
restriction of the structure morphism `Z' ⟶ X` to `V' ⟶ U`. -/
@[simp]
theorem restrict_toBase (t : UniversalFirstOrderThickening h) {U : X.Opens} {V : Z.Opens}
    (hVU : V ≤ h ⁻¹ᵁ U) : (t.restrict hVU).toBase =
      t.toBase.resLE U (t.ambientOpens V) (t.ambientOpens_le_preimage hVU) :=
  rfl

end UniversalFirstOrderThickening

/-! ### The conormal sheaf of a restriction to opens -/

/-- **Stacks Project, Tag 04FA, the third assertion, for a flat cartesian comparison.** Let
`Z ⊂ Z'` be a universal first-order thickening of `h : Z ⟶ X`, let `V ⊂ V''` and `V ⊂ W` be
universal first-order thickenings of `h|_V : V ⟶ U`, and let `w : W ⟶ Z'` be a flat morphism over
`X` making the square of inclusions cartesian. Then the canonical morphism of conormal sheaves
`(ι_V)^* 𝒞_{Z/X} ⟶ 𝒞_{V/U}` of [Stacks Project, Tag 04F7] at `V''` is an isomorphism. -/
theorem isIso_universalImmersionConormalSheafMap_of_isPullback
    (t : UniversalFirstOrderThickening h) {U : X.Opens} {V : Z.Opens} (hVU : V ≤ h ⁻¹ᵁ U)
    (tV tW : UniversalFirstOrderThickening (h.resLE U V hVU)) (w : tW.ambient ⟶ t.ambient)
    (hwFlat : Flat w) (hwBase : w ≫ t.toBase = tW.toBase ≫ U.ι)
    (hwSq : IsPullback tW.inclusion V.ι w t.inclusion) :
    IsIso (universalImmersionConormalSheafMap tV t V.ι U.ι (Scheme.Hom.resLE_comp_ι h hVU)) := by
  have := hwFlat
  have : IsIso (UniversalFirstOrderThickening.canonicalMap tV tW) :=
    UniversalFirstOrderThickening.isIso_of_inclusion_of_toBase tV tW _
      (UniversalFirstOrderThickening.canonicalMap_inclusion tV tW)
      (UniversalFirstOrderThickening.canonicalMap_toBase tV tW)
  have hmap : universalFirstOrderThickeningMap tV t V.ι U.ι (Scheme.Hom.resLE_comp_ι h hVU) =
      UniversalFirstOrderThickening.canonicalMap tV tW ≫ w := by
    refine (universalFirstOrderThickeningMap_unique tV t V.ι U.ι
      (Scheme.Hom.resLE_comp_ι h hVU) _ ?_ ?_).symm
    · rw [← Category.assoc, UniversalFirstOrderThickening.canonicalMap_inclusion]
      exact hwSq.w
    · rw [Category.assoc, hwBase, ← Category.assoc,
        UniversalFirstOrderThickening.canonicalMap_toBase]
  have hsqQ : IsPullback tV.inclusion (𝟙 V.toScheme)
      (UniversalFirstOrderThickening.canonicalMap tV tW) tW.inclusion :=
    IsPullback.of_vert_isIso
      ⟨(UniversalFirstOrderThickening.canonicalMap_inclusion tV tW).trans (Category.id_comp _).symm⟩
  have hsq : IsPullback tV.inclusion V.ι
      (UniversalFirstOrderThickening.canonicalMap tV tW ≫ w) t.inclusion := by
    simpa using hsqQ.paste_vert hwSq
  have key : ∀ (k : tV.ambient ⟶ t.ambient) (hk : tV.inclusion ≫ k = V.ι ≫ t.inclusion),
      k = UniversalFirstOrderThickening.canonicalMap tV tW ≫ w →
        IsIso (Stacks.Immersion.immersionConormalSheafMap tV.inclusion t.inclusion V.ι k
          (Stacks.Immersion.toShHom_square hk)) := by
    rintro k hk rfl
    exact Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat tV.inclusion t.inclusion V.ι _
      hsq
  exact key _ (universalFirstOrderThickeningMap_inclusion tV t V.ι U.ι
    (Scheme.Hom.resLE_comp_ι h hVU)) hmap

/-- **`𝒞_{Z/X}|_V = 𝒞_{V/U}`.** For universal first-order thickenings `Z ⊂ Z'` of `h : Z ⟶ X`
and `V ⊂ V''` of `h|_V : V ⟶ U`, the canonical morphism of conormal sheaves
`(ι_V)^* 𝒞_{Z/X} ⟶ 𝒞_{V/U}` of [Stacks Project, Tag 04F7] is an isomorphism. -/
@[stacks 04FA "restriction of the conormal sheaf"]
theorem isIso_universalImmersionConormalSheafMap_resLE
    (t : UniversalFirstOrderThickening h) {U : X.Opens} {V : Z.Opens} (hVU : V ≤ h ⁻¹ᵁ U)
    (tV : UniversalFirstOrderThickening (h.resLE U V hVU)) :
    IsIso (universalImmersionConormalSheafMap tV t V.ι U.ι (Scheme.Hom.resLE_comp_ι h hVU)) :=
  isIso_universalImmersionConormalSheafMap_of_isPullback t hVU tV (t.restrict hVU)
    (t.ambientOpens V).ι (inferInstance : Flat (t.ambientOpens V).ι)
    (Scheme.Hom.resLE_comp_ι t.toBase (t.ambientOpens_le_preimage hVU)).symm
    (isPullback_resLE_of_preimage_eq t.inclusion (t.preimage_ambientOpens V))

/-- **`𝒞_{Z/X}|_V = 𝒞_{V/U}` at the chosen thickenings.** For a formally unramified
`h : Z ⟶ X` and opens `V ⊆ Z`, `U ⊆ X` with `h(V) ⊆ U`, the canonical morphism
`(ι_V)^* 𝒞_{Z/X} ⟶ 𝒞_{V/U}` between the conormal sheaves
`Stacks.Thickenings.universalConormalSheaf h` and
`Stacks.Thickenings.universalConormalSheaf (h|_V)` is an isomorphism. -/
@[stacks 04FA "restriction of the conormal sheaf, at the chosen thickenings"]
theorem isIso_universalConormalSheafMap_resLE (h : Z ⟶ X) [FormallyUnramified h] {U : X.Opens}
    {V : Z.Opens} (hVU : V ≤ h ⁻¹ᵁ U) :
    letI : FormallyUnramified (h.resLE U V hVU) := formallyUnramified_resLE h hVU
    IsIso (universalImmersionConormalSheafMap
      (universalFirstOrderThickening (h.resLE U V hVU)) (universalFirstOrderThickening h)
      V.ι U.ι (Scheme.Hom.resLE_comp_ι h hVU)) :=
  have : FormallyUnramified (h.resLE U V hVU) := formallyUnramified_resLE h hVU
  isIso_universalImmersionConormalSheafMap_resLE (universalFirstOrderThickening h) hVU
    (universalFirstOrderThickening (h.resLE U V hVU))

end Stacks.Thickenings

end
