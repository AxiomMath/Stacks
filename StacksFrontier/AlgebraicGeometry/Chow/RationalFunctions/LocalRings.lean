module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Stalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local rings at generic points as subrings of the rational functions

On an integral separated scheme the local rings at the generic points of the irreducible closed
subsets sit inside the field of rational functions, and the inclusion relation among them
reflects the inclusion relation among the subsets: if `Z₁ ⊄ Z₂` then `𝒪_{X, η₁} ⊄ 𝒪_{X, η₂}`,
where `ηᵢ` is the generic point of `Zᵢ`. Taking `Z₁ = {x}` for a closed point `x` not lying in
`Z₂`, there is then a function regular near `x` which is not regular at `η₂`.

The rational functions of an integral scheme are its function field, the stalk at the generic
point, by Stacks Tag 01RV (`Stacks.Chow.rationalFunctionsEquivFunctionField`), and the local
rings are embedded in it by `algebraMap`, which is injective because the function field is the
fraction field of each of those local rings.

## Main results

* `Stacks.Chow.not_subset_range_genericStalk_of_not_le`: the local rings are not ordered by
  inclusion when the subsets are not.
* `Stacks.Chow.exists_section_notMem_range_genericStalk`: the neighbourhood form at a closed
  point.

## Implementation notes

An irreducible closed subset is Mathlib's `TopologicalSpace.IrreducibleCloseds`, whose generic
point is available because a scheme is a sober space. Separatedness enters through
`AlgebraicGeometry.ext_of_isDominant`: from an inclusion `𝒪_{X, η₁} ⊆ 𝒪_{X, η₂}` one builds two
morphisms `Spec 𝒪_{X, η₂} ⟶ X` which agree after composing with the dominant morphism
`Spec R(X) ⟶ Spec 𝒪_{X, η₂}`, hence agree; evaluating at the closed point puts `η₂` in the
range of `X.fromSpecStalk η₁`, which is the set of points `η₁` specializes from, and so
`Z₂ ⊇ Z₁`.

## References

* [Stacks Project, Tag 02NF](https://stacks.math.columbia.edu/tag/02NF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing

universe u

namespace Stacks.Chow

/-- A ring homomorphism whose range is contained in the range of an injective one factors
through it. -/
private theorem exists_comp_eq_of_range_subset {A B K : Type*} [CommRing A] [CommRing B]
    [CommRing K] (fA : A →+* K) (fB : B →+* K) (hfB : Function.Injective fB)
    (h : Set.range fA ⊆ Set.range fB) :
    ∃ q : A →+* B, fB.comp q = fA := by
  classical
  let e : B ≃+* fB.range := RingEquiv.ofBijective fB.rangeRestrict
    ⟨fun a b hab ↦ hfB (congrArg Subtype.val hab), fB.rangeRestrict_surjective⟩
  let g : A →+* fB.range := fA.codRestrict fB.range fun a ↦ h ⟨a, rfl⟩
  exact ⟨e.symm.toRingHom.comp g, by ext a; exact congrArg Subtype.val (e.apply_symm_apply (g a))⟩

/-- **Stacks Project, Tag 02NF.** On an integral separated scheme, if an irreducible closed
subset `Z₁` is not contained in an irreducible closed subset `Z₂`, then the local ring at the
generic point of `Z₁` is not contained in the local ring at the generic point of `Z₂`, as
subrings of the field of rational functions. -/
@[stacks 02NF "noninclusion of local rings", ega "I 8.2.4", ega "I 8.2.3" "sufficiency direction"]
theorem not_subset_range_genericStalk_of_not_le (X : Scheme.{u})
    [IsIntegral X] [Scheme.IsSeparated X] (Z₁ Z₂ : IrreducibleCloseds X) (hZ : ¬ Z₁ ≤ Z₂) :
    ¬ Set.range (algebraMap (X.presheaf.stalk Z₁.isIrreducible.genericPoint) X.functionField) ⊆
      Set.range (algebraMap (X.presheaf.stalk Z₂.isIrreducible.genericPoint)
        X.functionField) := by
  classical
  intro hsubset
  let η₁ : X := Z₁.isIrreducible.genericPoint
  let η₂ : X := Z₂.isIrreducible.genericPoint
  let f₁ : X.presheaf.stalk η₁ →+* X.functionField :=
    algebraMap (X.presheaf.stalk η₁) X.functionField
  let f₂ : X.presheaf.stalk η₂ →+* X.functionField :=
    algebraMap (X.presheaf.stalk η₂) X.functionField
  have hf₂ : Function.Injective f₂ := IsFractionRing.injective _ _
  obtain ⟨q, hq⟩ := exists_comp_eq_of_range_subset f₁ f₂ hf₂ hsubset
  let F : Spec (X.presheaf.stalk η₂) ⟶ X :=
    Spec.map (CommRingCat.ofHom q) ≫ X.fromSpecStalk η₁
  let G : Spec (X.presheaf.stalk η₂) ⟶ X := X.fromSpecStalk η₂
  let ι : Spec X.functionField ⟶ Spec (X.presheaf.stalk η₂) :=
    Spec.map (CommRingCat.ofHom f₂)
  have hcan : ∀ η : X, Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk η) X.functionField)) ≫ X.fromSpecStalk η =
      X.fromSpecStalk (genericPoint X) := fun η ↦
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes η)
  have hmaps : ι ≫ F = ι ≫ G :=
    calc ι ≫ F
        = (Spec.map (CommRingCat.ofHom f₂) ≫ Spec.map (CommRingCat.ofHom q)) ≫
            X.fromSpecStalk η₁ := rfl
      _ = Spec.map (CommRingCat.ofHom (f₂.comp q)) ≫ X.fromSpecStalk η₁ := by
          rw [← Spec.map_comp]; rfl
      _ = X.fromSpecStalk (genericPoint X) := by rw [hq]; exact hcan η₁
      _ = ι ≫ G := (hcan η₂).symm
  have hgeneric : ι (genericPoint (Spec X.functionField)) =
      genericPoint (Spec (X.presheaf.stalk η₂)) := by
    show PrimeSpectrum.comap (CommRingCat.Hom.hom (CommRingCat.ofHom f₂))
      (genericPoint (Spec X.functionField)) = genericPoint (Spec (X.presheaf.stalk η₂))
    rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
    ext a
    simp only [PrimeSpectrum.comap, Ideal.mem_comap]
    exact ⟨fun h ↦ hf₂ (by simpa using h), fun h ↦ by simp [show a = 0 by simpa using h]⟩
  have hdom : IsDominant ι := by
    rw [isDominant_iff, DenseRange, dense_iff_closure_eq]
    refine le_antisymm le_top ?_
    calc (Set.univ : Set (Spec (X.presheaf.stalk η₂)))
        = closure ({genericPoint (Spec (X.presheaf.stalk η₂))} : Set _) :=
          (genericPoint_spec (Spec (X.presheaf.stalk η₂))).symm
      _ ≤ closure (Set.range ι) := closure_mono (Set.singleton_subset_iff.mpr ⟨_, hgeneric⟩)
  have hspec : η₂ ⤳ η₁ := by
    let p : Spec (X.presheaf.stalk η₂) := closedPoint (X.presheaf.stalk η₂)
    have hmem : η₂ ∈ Set.range (X.fromSpecStalk η₁) := by
      refine ⟨Spec.map (CommRingCat.ofHom q) p, ?_⟩
      have hp := congrArg (fun k : Spec (X.presheaf.stalk η₂) ⟶ X ↦ k p)
        (ext_of_isDominant ι hmaps)
      calc X.fromSpecStalk η₁ (Spec.map (CommRingCat.ofHom q) p)
          = F p := by
            show _ = (Spec.map (CommRingCat.ofHom q) ≫ X.fromSpecStalk η₁) p
            rw [Scheme.Hom.comp_apply]
        _ = G p := hp
        _ = η₂ := Scheme.fromSpecStalk_closedPoint
    rw [Scheme.range_fromSpecStalk] at hmem
    exact hmem
  refine hZ ?_
  show (Z₁ : Set X) ⊆ (Z₂ : Set X)
  rw [← Z₁.isIrreducible.isGenericPoint_genericPoint Z₁.isClosed,
    ← Z₂.isIrreducible.isGenericPoint_genericPoint Z₂.isClosed]
  exact closure_minimal (Set.singleton_subset_iff.mpr hspec.mem_closure) isClosed_closure

/-- **Stacks Project, Tag 02NF.** On an integral separated scheme, a closed point `x` outside an
irreducible closed subset `Z` carries a function regular on a neighbourhood of `x` whose class
in the field of rational functions does not lie in the local ring at the generic point of
`Z`. -/
@[stacks 02NF "closed-point neighbourhood form",
  ega "I 8.2.4" "closed point case",
  ega "I 8.2.3" "closed point, separated"]
theorem exists_section_notMem_range_genericStalk (X : Scheme.{u})
    [IsIntegral X] [Scheme.IsSeparated X] (Z : IrreducibleCloseds X) (x : X)
    (hx : IsClosed ({x} : Set X)) (hxZ : x ∉ Z) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (s : Γ(X, U)),
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hxU s) ∉
        Set.range (algebraMap (X.presheaf.stalk Z.isIrreducible.genericPoint)
          X.functionField) := by
  classical
  let Zx : IrreducibleCloseds X := ⟨{x}, isIrreducible_singleton, hx⟩
  have hgenx : Zx.isIrreducible.genericPoint = x :=
    (Zx.isIrreducible.isGenericPoint_genericPoint Zx.isClosed).eq
      (show IsGenericPoint x ({x} : Set X) from hx.closure_eq)
  have hnot : ¬ Set.range (algebraMap (X.presheaf.stalk x) X.functionField) ⊆
      Set.range (algebraMap (X.presheaf.stalk Z.isIrreducible.genericPoint)
        X.functionField) := by
    intro hsub
    refine not_subset_range_genericStalk_of_not_le X Zx Z ?_ (hgenx ▸ hsub)
    exact fun hle ↦ hxZ (hle (show x ∈ (Zx : Set X) by simp [Zx]))
  obtain ⟨y, ⟨a, rfl⟩, ha⟩ := Set.not_subset.mp hnot
  obtain ⟨U, hxU, s, hs⟩ := X.presheaf.exists_germ_eq a
  exact ⟨U, hxU, s, by simpa only [hs] using ha⟩

end Stacks.Chow

end
