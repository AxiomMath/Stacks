module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.RingTheory.Length.SemilinearTransfer
public import StacksFrontier.Topology.Sheaves.Stalk.PushforwardLocalIso

/-!
# The stalk of a direct image at a point over which the morphism is an isomorphism

Let `π : Y ⟶ Z` be a morphism of schemes which is an isomorphism above an open `U` of `Z`, in
the sense that `π ∣_ U` is an isomorphism, and let `y` be a point of `π ⁻¹ᵁ U`. Then the
comparison map on stalks of a direct image along `π` is invertible at `y`, even though `π` is
in general nowhere near inducing: above `U` it is a homeomorphism, and only the open
neighbourhoods of `y` matter.

The topological input is `TopCat.Presheaf.isIso_stalkPushforward_of_exists_preimage_le`, whose
hypothesis — every open neighbourhood of `y` contains the preimage of an open neighbourhood of
`π y` — is verified here by taking the neighbourhood `U.ι ''ᵁ ((π ∣_ U) ''ᵁ ((π ⁻¹ᵁ U).ι ⁻¹ᵁ W))`
of `π y`, whose preimage is `(π ⁻¹ᵁ U).ι ''ᵁ ((π ⁻¹ᵁ U).ι ⁻¹ᵁ W)` by
`AlgebraicGeometry.image_morphismRestrict_preimage` and hence contained in `W`.

Composing with a closed immersion `i : Z ⟶ X` keeps the comparison invertible, since the
comparison of a composite factors as the two comparisons
(`TopCat.Presheaf.stalkPushforward.comp`) and a closed immersion is inducing. The composite's
germ map on structure sheaves is surjective, being a surjection followed by an isomorphism, so
`Module.length_eq_of_surjective_of_addEquiv` carries the length of the stalk of `(π ≫ i)_* M`
at `(π ≫ i) y` over `𝒪_{X, (π ≫ i) y}` to the length of the stalk of `M` at `y` over
`𝒪_{Y,y}`.

## Main results

* `Stacks.AlgebraicGeometry.IsoOverOpen.exists_preimage_le`: the cofinality of preimages at a
  point of `π ⁻¹ᵁ U`.
* `Stacks.AlgebraicGeometry.IsoOverOpen.isIso_stalkMap`: the germ map `𝒪_{Z,π y} ⟶ 𝒪_{Y,y}` is
  an isomorphism at a point of `π ⁻¹ᵁ U`.
* `Stacks.AlgebraicGeometry.IsoOverOpen.bijective_stalkPushforwardComparison_comp`: the stalk
  comparison for `π ≫ i` is bijective at a point of `π ⁻¹ᵁ U`.
* `Stacks.AlgebraicGeometry.IsoOverOpen.length_stalk_pushforward_comp`: hence the two lengths
  agree.

## References

* [Stacks Project, Tag 0EE3](https://stacks.math.columbia.edu/tag/0EE3)
* [Stacks Project, Tag 00IX](https://stacks.math.columbia.edu/tag/00IX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.IsoOverOpen

variable {X Y Z : Scheme.{u}}

/-- **Preimages are cofinal at a point above the isomorphism locus.** If `π ∣_ U` is an
isomorphism and `y ∈ π ⁻¹ᵁ U`, then every open `W` containing `y` contains the preimage of an
open containing `π y`, namely the image of `W ∩ π ⁻¹ᵁ U` under the homeomorphism `π ∣_ U`. -/
theorem exists_preimage_le (π : Y ⟶ Z) (U : Z.Opens) [IsIso (π ∣_ U)] {y : Y}
    (hy : y ∈ π ⁻¹ᵁ U) (W : Y.Opens) (hyW : y ∈ W) :
    ∃ V : Z.Opens, π.base y ∈ V ∧ π ⁻¹ᵁ V ≤ W := by
  have key : π ⁻¹ᵁ (U.ι ''ᵁ ((π ∣_ U) ''ᵁ ((π ⁻¹ᵁ U).ι ⁻¹ᵁ W))) =
      (π ⁻¹ᵁ U).ι ''ᵁ ((π ⁻¹ᵁ U).ι ⁻¹ᵁ W) := by
    rw [← image_morphismRestrict_preimage π U ((π ∣_ U) ''ᵁ ((π ⁻¹ᵁ U).ι ⁻¹ᵁ W)),
      Scheme.Hom.preimage_image_eq]
  refine ⟨U.ι ''ᵁ ((π ∣_ U) ''ᵁ ((π ⁻¹ᵁ U).ι ⁻¹ᵁ W)), ?_, ?_⟩
  · change y ∈ π ⁻¹ᵁ (U.ι ''ᵁ ((π ∣_ U) ''ᵁ ((π ⁻¹ᵁ U).ι ⁻¹ᵁ W)))
    rw [key]
    exact (Scheme.Opens.mem_ι_image_iff (x := (⟨y, hy⟩ : π ⁻¹ᵁ U))).mpr hyW
  · rw [key]
    exact Scheme.Hom.image_preimage_le _ W

/-- **A point of the isomorphism locus is hit.** If `π ∣_ U` is an isomorphism then every point
of `U` is the image of a point of `π ⁻¹ᵁ U`, namely of its preimage under the homeomorphism
`π ∣_ U`. -/
theorem exists_mem_preimage (π : Y ⟶ Z) (U : Z.Opens) [IsIso (π ∣_ U)] {z : Z} (hz : z ∈ U) :
    ∃ y : Y, y ∈ π ⁻¹ᵁ U ∧ π.base y = z := by
  obtain ⟨⟨y, hy⟩, hyz⟩ := (Scheme.Hom.homeomorph (π ∣_ U)).surjective ⟨z, hz⟩
  refine ⟨y, hy, ?_⟩
  rw [← morphismRestrict_base_coe π U ⟨y, hy⟩]
  exact congrArg Subtype.val hyz

/-- **The stalk comparison of a direct image along `π` is invertible above the isomorphism
locus.** -/
theorem isIso_stalkPushforward (π : Y ⟶ Z) (U : Z.Opens) [IsIso (π ∣_ U)] (M : Y.Modules)
    {y : Y} (hy : y ∈ π ⁻¹ᵁ U) :
    IsIso (TopCat.Presheaf.stalkPushforward Ab.{u} π.base M.val.presheaf y) :=
  TopCat.Presheaf.isIso_stalkPushforward_of_exists_preimage_le _ _ _
    fun W hW => exists_preimage_le π U hy W hW

/-- **The germ map of `π` is an isomorphism above the isomorphism locus.** -/
theorem isIso_stalkMap (π : Y ⟶ Z) (U : Z.Opens) [IsIso (π ∣_ U)] {y : Y}
    (hy : y ∈ π ⁻¹ᵁ U) : IsIso (π.stalkMap y) := by
  rw [← Arrow.isIso_iff_isIso_of_isIso
    (morphismRestrictStalkMap π U (⟨y, hy⟩ : π ⁻¹ᵁ U)).hom]
  exact ((AlgebraicGeometry.isIso_iff_isIso_stalkMap (π ∣_ U)).mp inferInstance).2 ⟨y, hy⟩

/-- **The germ map of `π ≫ i` is surjective above the isomorphism locus**, for `i` surjective
on stalks: it is the germ map of `i` followed by the germ map of `π`, the first surjective and
the second invertible. -/
theorem surjective_stalkMap_comp (i : Z ⟶ X) [SurjectiveOnStalks i] (π : Y ⟶ Z) (U : Z.Opens)
    [IsIso (π ∣_ U)] {y : Y} (hy : y ∈ π ⁻¹ᵁ U) :
    Function.Surjective ((π ≫ i).stalkMap y) := by
  have hπ : IsIso (π.stalkMap y) := isIso_stalkMap π U hy
  have h2 : Function.Surjective (π.stalkMap y) := (ConcreteCategory.bijective_of_isIso _).2
  have h1 : Function.Surjective (i.stalkMap (π.base y)) := i.stalkMap_surjective _
  simp only [Scheme.Hom.stalkMap_comp]
  exact h2.comp h1

/-- **The stalk comparison for `π ≫ i` is bijective above the isomorphism locus.** The
comparison of a composite is the composite of the comparisons, the one for the inducing `i`
being invertible by `Stacks.Chow.bijective_stalkPushforwardComparison` and the one for `π` by
`Stacks.AlgebraicGeometry.IsoOverOpen.isIso_stalkPushforward`. -/
theorem bijective_stalkPushforwardComparison_comp (i : Z ⟶ X)
    (hi : Topology.IsInducing (ConcreteCategory.hom i.base)) (π : Y ⟶ Z) (U : Z.Opens)
    [IsIso (π ∣_ U)] (M : Y.Modules) {y : Y} (hy : y ∈ π ⁻¹ᵁ U) :
    Function.Bijective (Stacks.Chow.stalkPushforwardComparison (π ≫ i) M y) := by
  have hiiso : IsIso (TopCat.Presheaf.stalkPushforward Ab.{u} i.base
      (π.base _* M.val.presheaf) (π.base y)) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing Ab.{u} hi _ _
  have hπiso := isIso_stalkPushforward π U M hy
  have hcomp : TopCat.Presheaf.stalkPushforward Ab.{u} (π ≫ i).base M.val.presheaf y =
      TopCat.Presheaf.stalkPushforward Ab.{u} i.base (π.base _* M.val.presheaf) (π.base y) ≫
        TopCat.Presheaf.stalkPushforward Ab.{u} π.base M.val.presheaf y :=
    TopCat.Presheaf.stalkPushforward.comp Ab.{u} M.val.presheaf π.base i.base y
  have : IsIso (TopCat.Presheaf.stalkPushforward Ab.{u} (π ≫ i).base M.val.presheaf y) := by
    rw [hcomp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hiiso hπiso
  exact ConcreteCategory.bijective_of_isIso
    (TopCat.Presheaf.stalkPushforward Ab.{u} (π ≫ i).base M.val.presheaf y)

/-- **The length of the stalk of `(π ≫ i)_* M` above the isomorphism locus.** For `i : Z ⟶ X`
inducing and surjective on stalks — a closed immersion, say — and `π : Y ⟶ Z` an isomorphism
above an open `U`, the length of the stalk of `(π ≫ i)_* M` at the image of a point `y` of
`π ⁻¹ᵁ U` is the length of the stalk of `M` at `y`.

This is [Stacks, Tag 0EE3] for the composite: the comparison map is an additive bijection,
semilinear over the germ map of `π ≫ i`, and that germ map is surjective, so
`Module.length_eq_of_surjective_of_addEquiv` applies. -/
theorem length_stalk_pushforward_comp (i : Z ⟶ X)
    (hi : Topology.IsInducing (ConcreteCategory.hom i.base)) [SurjectiveOnStalks i]
    (π : Y ⟶ Z) (U : Z.Opens) [IsIso (π ∣_ U)] (M : Y.Modules) {y : Y} (hy : y ∈ π ⁻¹ᵁ U) :
    Module.length (X.presheaf.stalk ((π ≫ i).base y))
        (((Scheme.Modules.pushforward (π ≫ i)).obj M).presheaf.stalk ((π ≫ i).base y)) =
      Module.length (Y.presheaf.stalk y) (M.presheaf.stalk y) := by
  have hbij := bijective_stalkPushforwardComparison_comp i hi π U M hy
  let c : (((Scheme.Modules.pushforward (π ≫ i)).obj M).presheaf.stalk ((π ≫ i).base y)) ≃+
      M.presheaf.stalk y :=
    AddEquiv.ofBijective
      (AddMonoidHom.mk' (Stacks.Chow.stalkPushforwardComparison (π ≫ i) M y)
        (Stacks.Chow.stalkPushforwardComparison_add (π ≫ i) M y)) hbij
  refine Module.length_eq_of_surjective_of_addEquiv ((π ≫ i).stalkMap y).hom
    (surjective_stalkMap_comp i π U hy) c.symm fun r n => ?_
  have hsmul := Stacks.Chow.stalkPushforwardComparison_smul (π ≫ i) M y r (c.symm n)
  have hc : c (r • c.symm n) = ((π ≫ i).stalkMap y) r • n := by
    rw [show c (r • c.symm n) = Stacks.Chow.stalkPushforwardComparison (π ≫ i) M y
        (r • c.symm n) from rfl, hsmul,
      show Stacks.Chow.stalkPushforwardComparison (π ≫ i) M y (c.symm n) = c (c.symm n) from rfl,
      c.apply_symm_apply]
  rw [← hc, c.symm_apply_apply]

end Stacks.AlgebraicGeometry.IsoOverOpen

end
