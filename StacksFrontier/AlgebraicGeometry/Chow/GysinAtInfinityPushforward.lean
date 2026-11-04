module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityLift
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardPulledBackModule
public import StacksFrontier.AlgebraicGeometry.Chow.GysinGysinCommute
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.TowerChow
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.PointSectionCartier
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierBaseChange

/-!
# The pushforward identity of the class at infinity

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, and let
`g : T ⟶ X` be locally of finite type. The second paragraph of the proof of Stacks 0F9J shows
`i_{∞,*}(C ∩ α) = i_{0,*} α`: the fibres `W_0` and `W_∞` of `W ×_X T` are the pullbacks of the two
rationally equivalent divisors `D_0` and `D_∞` of `𝐏¹`, so for every `β` the classes `i_∞^* β` and
`i_0^* β` have the same image in `W ×_X T`; and for a lift `β` of `α` one has `i_0^* β = α`.

This file proves both, and with them the identity.

## Main definitions

* `Stacks.Chow.modificationGraph` — the graph `W ×_X T ⟶ (W ×_X T) ×_S 𝐏¹_S` of the coordinate
  `W ×_X T ⟶ 𝐏¹_S`.

## Main results

* `Stacks.Chow.chowPushforward_gysinCapOfLift` — **Stacks 0F9J, the pushforward identity**:
  `i_{∞,*}(C ∩ α) = i_{0,*} α` on every test scheme locally of finite type over `X`.
* `Stacks.Chow.modificationZeroGysin_eq_infinityGysin` — for every `β ∈ A_{k+1}(W ×_X T)`, the
  Gysin images of `β` along the pulled-back divisors `D_0` and `D_∞` have the same pushforward to
  `W ×_X T`.
* `Stacks.Chow.chowPushforward_zeroGysin_of_isModificationLift` — for a lift `β` of `α`, the
  Gysin image of `β` along `D_0` is `α`, read through the section at zero.
* `Stacks.Chow.gysinSystemOfInvertible_onChow_flatPullbackChow_of_isIso` — Stacks 02TR, first
  equality, for a relative effective Cartier divisor mapping isomorphically to the base: the
  Gysin map is a left inverse of flat pullback.

## Implementation notes

The rational equivalence of the two divisors is used through the family of projective lines
`(W ×_X T) ×_S 𝐏¹_S` over `W ×_X T`: there the two section Gysin maps agree on Chow groups
(`Stacks.Chow.eq_of_chowPushforwardOfIso_onChow_sections`, from Stacks 02S4 and Remark 0B6Z, with
`Stacks.Chow.gysinSystemOfInvertible_onChowEqGysinCycleMap`), and pushing `β` forward along the
graph and applying Stacks 02TA
(`Stacks.Chow.gysinSystemOfInvertible_properPushforward_pullbackModule`)
brings the two Gysin maps of the family back to `W ×_X T`. The divisors `D_0` and `D_∞` are those
of `𝐏¹_S`, so all the invertible modules involved are pulled back from `𝐏¹_S`.

The identity `i_0^* β = α` is computed on the chart `b^{-1}(𝐀¹_X) ×_X T`, which contains the
fibre over zero: the Gysin map commutes with restriction to that open, where `β` restricts to the
flat pullback of `α` along an affine line and the fibre over zero is a relative effective Cartier
divisor isomorphic to `T`, the base change of the zero section of `𝐀¹_S`.

## References

* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 0B6Z](https://stacks.math.columbia.edu/tag/0B6Z)
* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Morphisms landing in a constant section of `𝐏¹_S` -/

/-- A morphism `φ : Y ⟶ 𝐏¹_S`, restricted to the inverse image of the image of a constant section
`σ` of `𝐏¹_S ⟶ S`, is the composite of its image in `S` with `σ`. -/
theorem comap_ker_subschemeι_comp_eq {S Y : Scheme.{u}}
    (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)) (φ : Y ⟶ relativeProjectiveLine S) :
    (((lineConstantSection S e).ker.comap φ).subschemeι ≫ φ) =
      (((lineConstantSection S e).ker.comap φ).subschemeι ≫ φ ≫ (relativeProjectiveLine S ↘ S)) ≫
        lineConstantSection S e := by
  set I := (lineConstantSection S e).ker
  set ι := isoSubschemeOfKer (lineConstantSection S e) I rfl
  have hI : I.subschemeι = (I.subschemeι ≫ (relativeProjectiveLine S ↘ S)) ≫
      lineConstantSection S e := by
    have h1 : I.subschemeι = ι.inv ≫ lineConstantSection S e := by
      rw [Iso.eq_inv_comp, isoSubschemeOfKer_hom_subschemeι]
    have h2 : I.subschemeι ≫ (relativeProjectiveLine S ↘ S) = ι.inv := by
      rw [h1, Category.assoc, lineConstantSection_comp, Category.comp_id]
    rw [h2, ← h1]
  have hm := Scheme.IdealSheafData.subschemeMap_subschemeι (I.comap φ) I φ (I.le_map_comap φ)
  rw [← hm, hI]
  simp only [Category.assoc]
  rw [← Category.assoc (Scheme.IdealSheafData.subschemeMap (I.comap φ) I φ _) I.subschemeι, hm]
  simp only [Category.assoc]

/-! ### The graph of the coordinate -/

section Graph

variable {X S W T : Scheme.{u}} (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f) (g : T ⟶ X)

/-- The coordinate `W ×_X T ⟶ 𝐏¹_S` lies over the structure morphism of `W ×_X T`. -/
theorem modificationBaseChangeToRelativeLine_over :
    modificationBaseChangeToRelativeLine f b g ≫ (relativeProjectiveLine S ↘ S) =
      modificationBaseChangeOver f b g := by
  simp only [modificationBaseChangeToRelativeLine, modificationBaseChangeToLine,
    modificationBaseChangeOver, modificationProjection, Category.assoc, ← pullback.condition]

/-- **The graph of the coordinate**, `W ×_X T ⟶ (W ×_X T) ×_S 𝐏¹_S`. -/
def modificationGraph :
    modificationBaseChange f b g ⟶ projectiveLineProduct (modificationBaseChangeOver f b g) :=
  pullback.lift (𝟙 _) (modificationBaseChangeToRelativeLine f b g)
    (by rw [Category.id_comp, modificationBaseChangeToRelativeLine_over])

/-- The graph of the coordinate is a section of the projection to `W ×_X T`. -/
@[reassoc (attr := simp)]
theorem modificationGraph_fst :
    modificationGraph f b g ≫ pullback.fst _ _ = 𝟙 _ :=
  pullback.lift_fst _ _ _

/-- The second component of the graph of the coordinate is the coordinate itself. -/
@[reassoc (attr := simp)]
theorem modificationGraph_snd :
    modificationGraph f b g ≫ pullback.snd _ _ = modificationBaseChangeToRelativeLine f b g :=
  pullback.lift_snd _ _ _

/-- The graph is a closed immersion, being a section of a separated morphism. -/
instance isClosedImmersion_modificationGraph : IsClosedImmersion (modificationGraph f b g) := by
  have : IsClosedImmersion (modificationGraph f b g ≫
      pullback.fst (modificationBaseChangeOver f b g) (relativeProjectiveLine S ↘ S)) := by
    rw [modificationGraph_fst]
    infer_instance
  exact IsClosedImmersion.of_comp _
    (pullback.fst (modificationBaseChangeOver f b g) (relativeProjectiveLine S ↘ S))

/-- The graph is a morphism over the base. -/
theorem modificationGraph_over :
    modificationGraph f b g ≫ familyStructureMorphism (modificationBaseChangeOver f b g) =
      modificationBaseChangeOver f b g := by
  rw [familyStructureMorphism, modificationGraph_fst_assoc]

end Graph

/-! ### The two section Gysin maps, brought back along the graph -/

section GraphGysin

variable (C : ChowSituation.{u}) {X W T : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b] (g : T ⟶ X) [LocallyOfFiniteType g]

/-- A constant section of a family of projective lines is the constant section of `𝐏¹_S` on the
second factor. -/
theorem constantSection_comp_snd_eq {Y S : Scheme.{u}} (q : Y ⟶ S)
    (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)) :
    constantSection q e ≫ pullback.snd q (relativeProjectiveLine S ↘ S) =
      q ≫ lineConstantSection S e := by
  rw [constantSection_comp_snd]
  refine pullback.hom_ext ?_ ?_
  · rw [pullback.lift_fst, Category.assoc, lineConstantSection, pullback.lift_fst,
      Category.comp_id]
  · rw [pullback.lift_snd, Category.assoc, lineConstantSection, pullback.lift_snd,
      ← Category.assoc, terminal.comp_from]

/-- The zero scheme of the pullback of the canonical section of `𝒪(D)` along `φ` is the inverse
image of `D`. -/
theorem zeroScheme_pullback_divisorSheafGlobalSection {Y Z : Scheme.{u}} (φ : Y ⟶ Z)
    (D : Z.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    Stacks.Divisors.zeroScheme Y ((Scheme.Modules.pullback φ).obj (Stacks.Divisors.divisorSheaf D))
        (AlgebraicGeometry.pullbackGlobalSections φ _
          (Stacks.Divisors.divisorSheafGlobalSection D)) =
      D.comap φ := by
  rw [Stacks.Divisors.zeroScheme_pullback]
  exact congrArg (fun I : Z.IdealSheafData ↦ I.comap φ)
    (Stacks.Divisors.zeroScheme_canonicalSection D)

/-- **Stacks 02TA along the graph, for a constant section.** Let `D` be the image of a constant
section `σ_e` of `𝐏¹_S`, and let `σ` be the corresponding section of the family
`(W ×_X T) ×_S 𝐏¹_S`, identified with the zero scheme of the pulled-back canonical section of
`𝒪(D)`. Then the Gysin map of the family at `σ`, applied to the pushforward of `β` along the graph,
is the pushforward to `W ×_X T` of the Gysin map of `W ×_X T` at the pulled-back divisor. -/
theorem chowPushforwardOfIso_gysin_eq_gysin_modificationGraph
    (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ))
    (D : (relativeProjectiveLine C.S).IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hD : D = (lineConstantSection C.S e).ker)
    (ε : modificationBaseChange f b g ≅
      (Stacks.Divisors.zeroScheme (projectiveLineProduct (modificationBaseChangeOver f b g))
        ((Scheme.Modules.pullback (pullback.snd (modificationBaseChangeOver f b g)
          (relativeProjectiveLine C.S ↘ C.S))).obj (Stacks.Divisors.divisorSheaf D))
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (modificationBaseChangeOver f b g)
          (relativeProjectiveLine C.S ↘ C.S)) _
          (Stacks.Divisors.divisorSheafGlobalSection D))).subscheme)
    (hε : ε.hom ≫ (Stacks.Divisors.zeroScheme
        (projectiveLineProduct (modificationBaseChangeOver f b g))
        ((Scheme.Modules.pullback (pullback.snd (modificationBaseChangeOver f b g)
          (relativeProjectiveLine C.S ↘ C.S))).obj (Stacks.Divisors.divisorSheaf D))
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (modificationBaseChangeOver f b g)
          (relativeProjectiveLine C.S ↘ C.S)) _
          (Stacks.Divisors.divisorSheafGlobalSection D))).subschemeι =
      constantSection (modificationBaseChangeOver f b g) e)
    (hb : ε.hom ≫
        ((Stacks.Divisors.zeroScheme (projectiveLineProduct (modificationBaseChangeOver f b g))
          ((Scheme.Modules.pullback (pullback.snd (modificationBaseChangeOver f b g)
            (relativeProjectiveLine C.S ↘ C.S))).obj (Stacks.Divisors.divisorSheaf D))
          (AlgebraicGeometry.pullbackGlobalSections
            (pullback.snd (modificationBaseChangeOver f b g) (relativeProjectiveLine C.S ↘ C.S))
            _ (Stacks.Divisors.divisorSheafGlobalSection D))).subschemeι ≫
          familyStructureMorphism (modificationBaseChangeOver f b g)) =
        modificationBaseChangeOver f b g)
    (k : ℤ) (β : chowGroup C (modificationBaseChangeOver f b g) (k + 1)) :
    chowPushforwardOfIso C (modificationBaseChangeOver f b g)
        ((Stacks.Divisors.zeroScheme (projectiveLineProduct (modificationBaseChangeOver f b g))
          ((Scheme.Modules.pullback (pullback.snd (modificationBaseChangeOver f b g)
            (relativeProjectiveLine C.S ↘ C.S))).obj (Stacks.Divisors.divisorSheaf D))
          (AlgebraicGeometry.pullbackGlobalSections
            (pullback.snd (modificationBaseChangeOver f b g) (relativeProjectiveLine C.S ↘ C.S))
            _ (Stacks.Divisors.divisorSheafGlobalSection D))).subschemeι ≫
          familyStructureMorphism (modificationBaseChangeOver f b g))
        ε.hom hb k
        (chowPushforwardOfIsClosedImmersion C _ (modificationBaseChangeOver f b g)
          (Stacks.Divisors.zeroScheme (modificationBaseChange f b g)
            ((Scheme.Modules.pullback (modificationBaseChangeToRelativeLine f b g)).obj
              (Stacks.Divisors.divisorSheaf D))
            (AlgebraicGeometry.pullbackGlobalSections (modificationBaseChangeToRelativeLine f b g) _
              (Stacks.Divisors.divisorSheafGlobalSection D))).subschemeι rfl k
          ((gysinSystemOfInvertible C).onChow (modificationBaseChangeOver f b g)
            ((Scheme.Modules.pullback (modificationBaseChangeToRelativeLine f b g)).obj
              (Stacks.Divisors.divisorSheaf D))
            (AlgebraicGeometry.pullbackGlobalSections (modificationBaseChangeToRelativeLine f b g) _
              (Stacks.Divisors.divisorSheafGlobalSection D)) k β)) =
      (gysinSystemOfInvertible C).onChow
        (familyStructureMorphism (modificationBaseChangeOver f b g))
        ((Scheme.Modules.pullback (pullback.snd (modificationBaseChangeOver f b g)
          (relativeProjectiveLine C.S ↘ C.S))).obj (Stacks.Divisors.divisorSheaf D))
        (AlgebraicGeometry.pullbackGlobalSections
          (pullback.snd (modificationBaseChangeOver f b g) (relativeProjectiveLine C.S ↘ C.S)) _
          (Stacks.Divisors.divisorSheafGlobalSection D)) k
        (chowPushforwardOfIsClosedImmersion C (modificationBaseChangeOver f b g)
          (familyStructureMorphism (modificationBaseChangeOver f b g)) (modificationGraph f b g)
          (modificationGraph_over f b g) (k + 1) β) := by
  let Z := Stacks.Divisors.zeroScheme (projectiveLineProduct (modificationBaseChangeOver f b g))
      ((Scheme.Modules.pullback (pullback.snd (modificationBaseChangeOver f b g)
        (relativeProjectiveLine C.S ↘ C.S))).obj (Stacks.Divisors.divisorSheaf D))
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (modificationBaseChangeOver f b g)
        (relativeProjectiveLine C.S ↘ C.S)) _ (Stacks.Divisors.divisorSheafGlobalSection D))
  let Z' := Stacks.Divisors.zeroScheme (modificationBaseChange f b g)
      ((Scheme.Modules.pullback (modificationBaseChangeToRelativeLine f b g)).obj
        (Stacks.Divisors.divisorSheaf D))
      (AlgebraicGeometry.pullbackGlobalSections (modificationBaseChangeToRelativeLine f b g) _
        (Stacks.Divisors.divisorSheafGlobalSection D))
  have hZ'W : Z' = D.comap (modificationBaseChangeToRelativeLine f b g) :=
    zeroScheme_pullback_divisorSheafGlobalSection _ D
  have hcomap : Z.comap (modificationGraph f b g) = Z' := by
    rw [show Z = _ from zeroScheme_pullback_divisorSheafGlobalSection _ D, hZ'W,
      ← Scheme.IdealSheafData.comap_comp, modificationGraph_snd]
  let j := Scheme.IdealSheafData.subschemeMap _ _ (modificationGraph f b g)
    (Scheme.IdealSheafData.le_map_iff_comap_le.2 (le_of_eq hcomap))
  have hjsq := Scheme.IdealSheafData.subschemeMap_subschemeι _ _ (modificationGraph f b g)
    (Scheme.IdealSheafData.le_map_iff_comap_le.2 (le_of_eq hcomap))
  have : IsClosedImmersion (j ≫ Z.subschemeι) := by rw [hjsq]; infer_instance
  have : IsClosedImmersion j := IsClosedImmersion.of_comp j Z.subschemeι
  have hj : j ≫ (Z.subschemeι ≫ familyStructureMorphism (modificationBaseChangeOver f b g)) =
      Z'.subschemeι ≫ modificationBaseChangeOver f b g := by
    rw [← Category.assoc, hjsq, Category.assoc, modificationGraph_over]
  have hcomp : Z'.subschemeι ≫ ε.hom = j := by
    refine (cancel_mono Z.subschemeι).1 ?_
    rw [Category.assoc, hε, hjsq]
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, constantSection_comp_fst, modificationGraph_fst]
    · rw [Category.assoc, Category.assoc, constantSection_comp_snd_eq, modificationGraph_snd]
      have h := comap_ker_subschemeι_comp_eq e (modificationBaseChangeToRelativeLine f b g)
      rw [← hD, ← hZ'W] at h
      rw [h, Category.assoc, modificationBaseChangeToRelativeLine_over]
      simp only [Category.assoc]
  have h02TA := gysinSystemOfInvertible_properPushforward_pullbackModule C
    (modificationBaseChangeOver f b g) (familyStructureMorphism (modificationBaseChangeOver f b g))
    (modificationBaseChangeToRelativeLine f b g)
    (pullback.snd (modificationBaseChangeOver f b g) (relativeProjectiveLine C.S ↘ C.S))
    (modificationGraph f b g) (modificationGraph_over f b g) (modificationGraph_snd f b g)
    (Stacks.Divisors.divisorSheaf D) (Stacks.Divisors.divisorSheafGlobalSection D) k j hjsq hj β
  refine Eq.trans ?_ h02TA.symm
  exact (properChowPushforward_comp_apply C _ (modificationBaseChangeOver f b g) _ _ ε.hom j hcomp
    rfl hb hj k _ _ _ _).symm

attribute [local instance] lineZeroDivisor_isEffectiveCartierDivisor
  lineInfinityDivisor_isEffectiveCartierDivisor

/-- **The fibres of `W ×_X T` over `0` and `∞` are rationally equivalent, on Gysin images.** For
every class `β` on `W ×_X T`, the Gysin images of `β` along the pulled-back divisors `D_0` and
`D_∞` of `𝐏¹_S` have the same pushforward to `W ×_X T`. -/
theorem modificationZeroGysin_eq_infinityGysin (k : ℤ)
    (β : chowGroup C (modificationBaseChangeOver f b g) (k + 1)) :
    chowPushforwardOfIsClosedImmersion C _ (modificationBaseChangeOver f b g)
        (Stacks.Divisors.zeroScheme (modificationBaseChange f b g)
          (lineZeroModule (modificationBaseChangeToRelativeLine f b g))
          (lineZeroModuleSection (modificationBaseChangeToRelativeLine f b g))).subschemeι rfl k
        ((gysinSystemOfInvertible C).onChow (modificationBaseChangeOver f b g)
          (lineZeroModule (modificationBaseChangeToRelativeLine f b g))
          (lineZeroModuleSection (modificationBaseChangeToRelativeLine f b g)) k β) =
      chowPushforwardOfIsClosedImmersion C _ (modificationBaseChangeOver f b g)
        (Stacks.Divisors.zeroScheme (modificationBaseChange f b g)
          (lineInfinityModule (modificationBaseChangeToRelativeLine f b g))
          (lineInfinityModuleSection (modificationBaseChangeToRelativeLine f b g))).subschemeι rfl k
        ((gysinSystemOfInvertible C).onChow (modificationBaseChangeOver f b g)
          (lineInfinityModule (modificationBaseChangeToRelativeLine f b g))
          (lineInfinityModuleSection (modificationBaseChangeToRelativeLine f b g)) k β) := by
  have hker₀ : (zeroSection (modificationBaseChangeOver f b g) ≫
      (Iso.refl (projectiveLineProduct (modificationBaseChangeOver f b g))).hom).ker =
      Stacks.Divisors.zeroScheme (projectiveLineProduct (modificationBaseChangeOver f b g))
        (lineZeroModule (pullback.snd (modificationBaseChangeOver f b g)
          (relativeProjectiveLine C.S ↘ C.S)))
        (lineZeroModuleSection (pullback.snd (modificationBaseChangeOver f b g)
          (relativeProjectiveLine C.S ↘ C.S))) := by
    rw [Iso.refl_hom, Category.comp_id, ker_zeroSection, zeroScheme_lineZeroModuleSection]
  have hkerI : (infinitySection (modificationBaseChangeOver f b g) ≫
      (Iso.refl (projectiveLineProduct (modificationBaseChangeOver f b g))).hom).ker =
      Stacks.Divisors.zeroScheme (projectiveLineProduct (modificationBaseChangeOver f b g))
        (lineInfinityModule (pullback.snd (modificationBaseChangeOver f b g)
          (relativeProjectiveLine C.S ↘ C.S)))
        (lineInfinityModuleSection (pullback.snd (modificationBaseChangeOver f b g)
          (relativeProjectiveLine C.S ↘ C.S))) := by
    rw [Iso.refl_hom, Category.comp_id, ker_infinitySection, zeroScheme_lineInfinityModuleSection]
  have aux : ∀ (s : modificationBaseChange f b g ⟶
        projectiveLineProduct (modificationBaseChangeOver f b g)) [IsClosedImmersion s]
      (Z : (projectiveLineProduct (modificationBaseChangeOver f b g)).IdealSheafData)
      (hker : (s ≫ (Iso.refl _).hom).ker = Z),
      s ≫ familyStructureMorphism (modificationBaseChangeOver f b g) =
        modificationBaseChangeOver f b g →
      (isoSubschemeOfKer _ _ hker).hom ≫ Z.subschemeι = s ∧
        (isoSubschemeOfKer _ _ hker).hom ≫ (Z.subschemeι ≫
          familyStructureMorphism (modificationBaseChangeOver f b g)) =
          modificationBaseChangeOver f b g := fun s _ Z hker hs ↦ by
    have h := (isoSubschemeOfKer_hom_subschemeι _ _ hker).trans (Category.comp_id _)
    exact ⟨h, by rw [← Category.assoc, h, hs]⟩
  obtain ⟨he₀, hb₀⟩ := aux _ _ hker₀ (zeroSection_comp_familyStructureMorphism _)
  obtain ⟨heI, hbI⟩ := aux _ _ hkerI (infinitySection_comp_familyStructureMorphism _)
  refine eq_of_chowPushforwardOfIso_onChow_sections C (gysinSystemOfInvertible C)
    (gysinSystemOfInvertible_onChowEqGysinCycleMap C) (modificationBaseChangeOver f b g)
    (familyStructureMorphism (modificationBaseChangeOver f b g)) k (Iso.refl _)
    (Category.id_comp _) _ _ (isTrivial_lineZeroModule _) hker₀ (isoSubschemeOfKer _ _ hker₀)
    (isoSubschemeOfKer_hom_subschemeι _ _ hker₀) hb₀ _ _ (isTrivial_lineInfinityModule _) hkerI
    (isoSubschemeOfKer _ _ hkerI) (isoSubschemeOfKer_hom_subschemeι _ _ hkerI) hbI
    (chowPushforwardOfIsClosedImmersion C (modificationBaseChangeOver f b g)
      (familyStructureMorphism (modificationBaseChangeOver f b g)) (modificationGraph f b g)
      (modificationGraph_over f b g) (k + 1) β) _ _ ?_ ?_
  · exact chowPushforwardOfIso_gysin_eq_gysin_modificationGraph C f b g integralZeroSection
      (lineZeroDivisor C.S) rfl (isoSubschemeOfKer _ _ hker₀)
      he₀ hb₀ k β
  · exact chowPushforwardOfIso_gysin_eq_gysin_modificationGraph C f b g integralInfinitySection
      (lineInfinityDivisor C.S) rfl (isoSubschemeOfKer _ _ hkerI)
      heI hbI k β

end GraphGysin

/-! ### Stacks 02TR for a divisor mapping isomorphically to the base -/

section RelativeDivisor

variable (C : ChowSituation.{u})

/-- The Gysin cycle of the component rule of an invertible module does not see how its degree is
written. -/
theorem val_gysinRule_extendCycleGroup_congr {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) {K K' : ℤ} (h : K = K') (c : CycleGroup C p (K + 1))
    (c' : CycleGroup C p (K' + 1)) (hc : c.1 = c'.1) :
    ((gysinRule C p K L s (firstChernComponentClass C p K L)).extendCycleGroup c).1 =
      ((gysinRule C p K' L s (firstChernComponentClass C p K' L)).extendCycleGroup c').1 := by
  subst h
  rw [Subtype.ext hc]

/-- **Stacks 02TR, first equality, for a relative effective Cartier divisor isomorphic to the
base.** Let `p : X ⟶ Y` be flat of relative dimension one and let `D = Z(t)` be a relative
effective Cartier divisor on `X/Y`, the zero scheme of a section of an invertible module, such
that `D ⟶ Y` is an isomorphism. Then the Gysin map of `t` is a left inverse of flat pullback:
`i^* p^* α` is `α`, read on `D` through the isomorphism `D ≅ Y`. -/
theorem gysinSystemOfInvertible_onChow_flatPullbackChow_of_isIso {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (p : X ⟶ Y) [LocallyOfFiniteType p] [Flat p] (hbase : p ≫ sY = sX)
    (hp : RelativeDimension p 1) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (t : Γ(L, ⊤))
    (hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor p (Stacks.Divisors.zeroScheme X L t))
    [IsIso ((Stacks.Divisors.zeroScheme X L t).subschemeι ≫ p)] (k : ℤ)
    (α : chowGroup C sY (k + 1)) :
    (gysinSystemOfInvertible C).onChow sX L t (k + 1)
        (flatPullbackChow C sX sY p hbase 1 hp (k + 1) (flatPullbackDescends C _ _ _ _ _ _ _) α) =
      chowPushforwardOfIso C sY ((Stacks.Divisors.zeroScheme X L t).subschemeι ≫ sX)
        (inv ((Stacks.Divisors.zeroScheme X L t).subschemeι ≫ p))
        (by rw [IsIso.inv_comp_eq, Category.assoc, hbase]) (k + 1) α := by
  obtain ⟨σ, rfl⟩ := exists_sections_eval_eq L t
  have hq : RelativeDimension ((Stacks.Divisors.zeroScheme X L (σ.eval (.op ⊤))).subschemeι ≫ p)
      0 := relativeDimension_of_isIso _
  induction α using QuotientAddGroup.induction_on with
  | H a =>
    refine congrArg (QuotientAddGroup.mk' _) (Subtype.ext ?_)
    have hcast : k + 1 + ((0 + 1 : ℕ) : ℤ) = k + 1 + ((0 : ℕ) : ℤ) + 1 := by push_cast; ring
    have h02TR := gysinRule_extendCycleGroup_flatPullback C sX sY p hbase 0 hp k L σ hD hq hcast a
    have hrestr := cycleGroupRestrict_eq_flatPullback C sY
      ((Stacks.Divisors.zeroScheme X L (σ.eval (.op ⊤))).subschemeι ≫ sX)
      ((Stacks.Divisors.zeroScheme X L (σ.eval (.op ⊤))).subschemeι ≫ p)
      (by rw [Category.assoc, hbase]) hq (k + 1) a
    rw [cycleGroupRestrict_of_isIso] at hrestr
    refine (val_gysinRule_extendCycleGroup_congr C sX L (σ.eval (.op ⊤))
      (show k + 1 = k + 1 + ((0 : ℕ) : ℤ) by push_cast; ring) _
      (hcast ▸ flatPullback C sX sY p hbase (0 + 1) hp (k + 1) a)
      (val_cycleGroup_cast C sX hcast _).symm).trans ?_
    rw [h02TR]
    exact hrestr.symm

end RelativeDivisor

/-! ### The Gysin map at zero inverts the lift -/

section ZeroGysin

variable {X S W T : Scheme.{u}} (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f) (g : T ⟶ X)

/-- The chart `b^{-1}(𝐀¹_X) ×_X T` maps to `𝐀¹_S` as the base change of `𝐀¹_S ⟶ S`. -/
theorem isPullback_modificationAffineChart_affineLineOverMap
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) :
    IsPullback (pullback.snd (modificationBaseChangeToLine f b g) (projectiveLineAffineChart f) ≫
        affineLineOverMap f)
      (modificationAffineChartProjection f b g)
      (pullback.fst (terminal.from S) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))))
      (g ≫ f) :=
  (isPullback_modificationAffineChartProjection f b g hA).paste_horiz
    (isPullback_affineLineOverMap f)

/-- The coordinate of the chart over `𝐀¹_X` factors through the affine chart of `𝐏¹_S`. -/
theorem modificationAffineChartι_comp_toRelativeLine :
    modificationAffineChartι f b g ≫ modificationBaseChangeToRelativeLine f b g =
      pullback.snd (modificationBaseChangeToLine f b g) (projectiveLineAffineChart f) ≫
        affineLineOverMap f ≫ affineChart S := by
  rw [modificationBaseChangeToRelativeLine, ← Category.assoc, pullback.condition,
    Category.assoc, projectiveLineAffineChart_snd]

/-- The zero section of `𝐀¹_S` is an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_ker_affineLineZeroSection (S : Scheme.{u}) :
    Stacks.Divisors.IsEffectiveCartierDivisor (affineLineZeroSection S).ker := by
  rw [← comap_lineZeroDivisor_affineChart]
  exact Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion _
    (lineZeroDivisor_isEffectiveCartierDivisor S) _

/-- The closed subscheme cut out by the zero section of `𝐀¹_S` maps isomorphically to `S`. -/
instance isIso_ker_affineLineZeroSection_comp (S : Scheme.{u}) :
    IsIso ((affineLineZeroSection S).ker.subschemeι ≫
      pullback.fst (terminal.from S) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ)))))) := by
  set e := isoSubschemeOfKer (affineLineZeroSection S) _ rfl
  have h : (affineLineZeroSection S).ker.subschemeι ≫
      pullback.fst (terminal.from S) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))) =
      e.inv := by
    have he : (affineLineZeroSection S).ker.subschemeι = e.inv ≫ affineLineZeroSection S :=
      (Iso.eq_inv_comp e).2 (isoSubschemeOfKer_hom_subschemeι _ _ rfl)
    rw [he, Category.assoc]
    dsimp only [affineLineZeroSection, affineLineConstantSection]
    rw [pullback.lift_fst, Category.comp_id]
  rw [h]
  infer_instance

/-- The inverse image of a closed subscheme along the top of a cartesian square maps to the
bottom-left corner isomorphically as soon as the closed subscheme maps isomorphically to the
bottom-right corner. -/
theorem isIso_comap_subschemeι_comp_of_isPullback {U A T B : Scheme.{u}} {p' : U ⟶ A}
    {q : U ⟶ T} {h : A ⟶ B} {k : T ⟶ B} (sq : IsPullback p' q h k) (J : A.IdealSheafData)
    [IsIso (J.subschemeι ≫ h)] : IsIso ((J.comap p').subschemeι ≫ q) := by
  have htop : IsPullback (Scheme.IdealSheafData.subschemeMap (J.comap p') J p'
      (J.le_map_comap p')) (J.comap p').subschemeι J.subschemeι p' :=
    (IsPullback.of_iso_pullback (fst := (J.comap p').subschemeι)
      (snd := Scheme.IdealSheafData.subschemeMap (J.comap p') J p' (J.le_map_comap p'))
      ⟨(Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _).symm⟩
      (J.comapIso p') (J.comapIso_hom_fst p') (J.comapIso_hom_snd p')).flip
  exact (htop.paste_vert sq).isIso_snd_of_isIso inferInstance

/-- The pulled-back divisor `D_0` on the chart over `𝐀¹_X`. -/
abbrev modificationAffineZeroScheme :
    (modificationAffineChart f b g).IdealSheafData :=
  Stacks.Divisors.zeroScheme (modificationAffineChart f b g)
    ((Scheme.Modules.pullback (modificationAffineChartι f b g)).obj
      (lineZeroModule (modificationBaseChangeToRelativeLine f b g)))
    (AlgebraicGeometry.pullbackGlobalSections (modificationAffineChartι f b g) _
      (lineZeroModuleSection (modificationBaseChangeToRelativeLine f b g)))

/-- The pulled-back divisor `D_0` on the chart over `𝐀¹_X` is the inverse image of the zero
section of `𝐀¹_S`. -/
theorem modificationAffineZeroScheme_eq :
    modificationAffineZeroScheme f b g =
      (affineLineZeroSection S).ker.comap
        (pullback.snd (modificationBaseChangeToLine f b g) (projectiveLineAffineChart f) ≫
          affineLineOverMap f) := by
  rw [modificationAffineZeroScheme, Stacks.Divisors.zeroScheme_pullback,
    zeroScheme_lineZeroModuleSection, ← Scheme.IdealSheafData.comap_comp,
    modificationAffineChartι_comp_toRelativeLine, ← comap_lineZeroDivisor_affineChart,
    ← Scheme.IdealSheafData.comap_comp, Category.assoc]

/-- The pulled-back divisor `D_0` on the chart over `𝐀¹_X` maps isomorphically to `T`. -/
theorem isIso_modificationAffineZeroScheme_comp
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) :
    IsIso ((modificationAffineZeroScheme f b g).subschemeι ≫
      modificationAffineChartProjection f b g) := by
  rw [modificationAffineZeroScheme_eq]
  exact isIso_comap_subschemeι_comp_of_isPullback
    (isPullback_modificationAffineChart_affineLineOverMap f b g hA) _

/-- **The pulled-back divisor `D_0` on the chart over `𝐀¹_X` is a relative effective Cartier
divisor over `T`.** It is the base change along `T ⟶ S` of the zero section of `𝐀¹_S`, which is
an effective Cartier divisor isomorphic to `S`. -/
theorem isRelativeEffectiveCartierDivisor_modificationAffineZeroScheme
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) :
    Stacks.Divisors.IsRelativeEffectiveCartierDivisor (modificationAffineChartProjection f b g)
      (modificationAffineZeroScheme f b g) := by
  have := isIso_modificationAffineZeroScheme_comp f b g hA
  refine ⟨?_, inferInstance⟩
  rw [modificationAffineZeroScheme_eq]
  exact AlgebraicGeometry.isEffectiveCartierDivisor_comap_of_isPullback _ _
    (isPullback_modificationAffineChart_affineLineOverMap f b g hA).flip _
    (isEffectiveCartierDivisor_ker_affineLineZeroSection S)

/-- The pulled-back divisor `D_0` of `W ×_X T` lies in the chart over `𝐀¹_X`. -/
theorem range_lineZeroModule_subschemeι_subset :
    Set.range (Stacks.Divisors.zeroScheme (modificationBaseChange f b g)
        (lineZeroModule (modificationBaseChangeToRelativeLine f b g))
        (lineZeroModuleSection (modificationBaseChangeToRelativeLine f b g))).subschemeι.base ⊆
      Set.range (modificationAffineChartι f b g).base := by
  rw [Scheme.IdealSheafData.range_subschemeι, zeroScheme_lineZeroModuleSection,
    Scheme.IdealSheafData.support_comap,
    range_fst_of_isPullback (IsPullback.of_hasPullback (modificationBaseChangeToLine f b g)
      (projectiveLineAffineChart f)),
    range_fst_of_isPullback (isPullback_affineLineOverMap_projectiveLineAffineChart f).flip]
  intro x hx
  have hx' : (modificationBaseChangeToRelativeLine f b g).base x ∈
      ((lineZeroDivisor S).support : Set (relativeProjectiveLine S)) := hx
  rw [coe_support_lineZeroDivisor] at hx'
  exact range_lineZeroSection_subset_range_affineChart S hx'

/-- The open immersion of the pulled-back divisor `D_0` of the chart into that of `W ×_X T`. -/
abbrev modificationAffineZeroSchemeMap :
    (modificationAffineZeroScheme f b g).subscheme ⟶
      (Stacks.Divisors.zeroScheme (modificationBaseChange f b g)
        (lineZeroModule (modificationBaseChangeToRelativeLine f b g))
        (lineZeroModuleSection (modificationBaseChangeToRelativeLine f b g))).subscheme :=
  Stacks.Divisors.zeroSchemePullbackMap (modificationAffineChartι f b g) _ _

/-- The inclusion of the pulled-back divisor `D_0` of the chart into that of `W ×_X T` is an open
immersion, being a base change of the open immersion of the chart. -/
instance isOpenImmersion_modificationAffineZeroSchemeMap :
    IsOpenImmersion (modificationAffineZeroSchemeMap f b g) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion)
    (Stacks.Divisors.isPullback_zeroSchemePullbackMap _ _ _) inferInstance

/-- The pulled-back divisor `D_0` of `W ×_X T` is that of the chart over `𝐀¹_X`. -/
instance isIso_modificationAffineZeroSchemeMap :
    IsIso (modificationAffineZeroSchemeMap f b g) := by
  refine (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, ⟨fun z ↦ ?_⟩⟩
  have h := range_fst_of_isPullback (Stacks.Divisors.isPullback_zeroSchemePullbackMap
    (modificationAffineChartι f b g) (lineZeroModule (modificationBaseChangeToRelativeLine f b g))
    (lineZeroModuleSection (modificationBaseChangeToRelativeLine f b g))).flip
  have hz : z ∈ Set.range (modificationAffineZeroSchemeMap f b g).base := by
    rw [h]
    exact range_lineZeroModule_subschemeι_subset f b g ⟨z, rfl⟩
  exact hz

/-- **The base-changed section at zero, read on the chart.** It is the inverse of the isomorphism
of the pulled-back divisor `D_0` of the chart over `𝐀¹_X` with `T`, followed by the inclusion. -/
theorem modificationSectionAtZeroBaseChange_eq
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) :
    haveI := isIso_modificationAffineZeroScheme_comp f b g hA
    modificationSectionAtZeroBaseChange f b (isIso_modificationFibreAtZeroProjection f b hA)
        (modificationSectionAtZero_comp_projection f b hA) g =
      inv ((modificationAffineZeroScheme f b g).subschemeι ≫
          modificationAffineChartProjection f b g) ≫
        (modificationAffineZeroScheme f b g).subschemeι ≫ modificationAffineChartι f b g := by
  have := isIso_modificationAffineZeroScheme_comp f b g hA
  have := isIso_modificationFibreAtZeroProjection f b hA
  set τ := inv ((modificationAffineZeroScheme f b g).subschemeι ≫
      modificationAffineChartProjection f b g) ≫
    (modificationAffineZeroScheme f b g).subschemeι ≫ modificationAffineChartι f b g
  have hτsnd : τ ≫ pullback.snd (modificationProjection f b) g = 𝟙 T := by
    simp only [τ, Category.assoc]
    exact IsIso.inv_hom_id _
  -- `τ` followed by the coordinate lands in the zero section of `𝐏¹_S`
  have hτψ : τ ≫ modificationBaseChangeToRelativeLine f b g = g ≫ f ≫ lineZeroSection S := by
    have hD : modificationAffineZeroScheme f b g = (lineZeroSection S).ker.comap
        (modificationAffineChartι f b g ≫ modificationBaseChangeToRelativeLine f b g) := by
      rw [modificationAffineZeroScheme, Stacks.Divisors.zeroScheme_pullback,
        zeroScheme_lineZeroModuleSection, ← Scheme.IdealSheafData.comap_comp]
      rfl
    have h := comap_ker_subschemeι_comp_eq integralZeroSection
      (modificationAffineChartι f b g ≫ modificationBaseChangeToRelativeLine f b g)
    rw [← hD] at h
    have h2 : (modificationAffineZeroScheme f b g).subschemeι ≫
        (modificationAffineChartι f b g ≫ modificationBaseChangeToRelativeLine f b g) ≫
          (relativeProjectiveLine S ↘ S) =
        ((modificationAffineZeroScheme f b g).subschemeι ≫
          modificationAffineChartProjection f b g) ≫ g ≫ f := by
      rw [Category.assoc (modificationAffineChartι f b g),
        modificationBaseChangeToRelativeLine_over, ← modificationBaseChange_snd_over]
      simp only [Category.assoc]
    calc τ ≫ modificationBaseChangeToRelativeLine f b g =
        inv ((modificationAffineZeroScheme f b g).subschemeι ≫
          modificationAffineChartProjection f b g) ≫
          ((modificationAffineZeroScheme f b g).subschemeι ≫
            (modificationAffineChartι f b g ≫ modificationBaseChangeToRelativeLine f b g)) := by
          simp only [τ, Category.assoc]
      _ = inv ((modificationAffineZeroScheme f b g).subschemeι ≫
          modificationAffineChartProjection f b g) ≫
          (((modificationAffineZeroScheme f b g).subschemeι ≫
            (modificationAffineChartι f b g ≫ modificationBaseChangeToRelativeLine f b g) ≫
              (relativeProjectiveLine S ↘ S)) ≫ lineConstantSection S integralZeroSection) := by
          rw [h]
      _ = g ≫ f ≫ lineZeroSection S := by
          rw [h2, Category.assoc, IsIso.inv_hom_id_assoc, Category.assoc]
  -- hence `τ` followed by `W ×_X T ⟶ W` is `g` followed by the section at zero
  have hτfst : τ ≫ pullback.fst (modificationProjection f b) g =
      g ≫ modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA) := by
    have hp : τ ≫ pullback.fst (modificationProjection f b) g ≫ modificationProjection f b = g := by
      rw [pullback.condition, ← Category.assoc, hτsnd, Category.id_comp]
    have hb : (τ ≫ pullback.fst (modificationProjection f b) g) ≫ b =
        g ≫ zeroSection f := by
      refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, zeroSection_comp_fst, Category.comp_id]
        exact hp
      · simp only [Category.assoc, zeroSection_comp_snd]
        exact hτψ
    have hl := pullback.lift_fst (τ ≫ pullback.fst (modificationProjection f b) g) g hb
    have hr : pullback.lift (τ ≫ pullback.fst (modificationProjection f b) g) g hb =
        g ≫ inv (modificationFibreAtZeroProjection f b) := by
      rw [IsIso.eq_comp_inv]
      exact pullback.lift_snd _ _ _
    rw [← hl, hr, Category.assoc]
    rfl
  refine pullback.hom_ext ?_ ?_
  · rw [modificationSectionAtZeroBaseChange, pullback.lift_fst, hτfst]
  · rw [modificationSectionAtZeroBaseChange_comp_snd, hτsnd]


end ZeroGysin

section ZeroGysinChow

variable (C : ChowSituation.{u}) {X W T : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b] (g : T ⟶ X) [LocallyOfFiniteType g]

/-- **Stacks 0F9J, `i_0^* β = α`** (Stacks 02TR). For a lift `β` of `α`, the Gysin map at the
pulled-back divisor `D_0` sends `β` to `α`, read on `W ×_X T` through the section at zero: the
pulled-back divisor `D_0` lies in the chart over `𝐀¹_X`, where `β` is the flat pullback of `α`
along an affine line, and there the Gysin map at the zero section inverts flat pullback. -/
theorem chowPushforward_zeroGysin_of_isModificationLift
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) (k : ℤ)
    (α : chowGroup C (g ≫ f) (k + 1))
    (β : chowGroup C (modificationBaseChangeOver f b g) (k + 1 + 1))
    (hβ : IsModificationLift C f b hA g (k + 1) α β) :
    haveI := isClosedImmersion_modificationSectionAtZeroBaseChange f b g hA
    chowPushforwardOfIsClosedImmersion C _ (modificationBaseChangeOver f b g)
        (Stacks.Divisors.zeroScheme (modificationBaseChange f b g)
          (lineZeroModule (modificationBaseChangeToRelativeLine f b g))
          (lineZeroModuleSection (modificationBaseChangeToRelativeLine f b g))).subschemeι rfl
        (k + 1)
        ((gysinSystemOfInvertible C).onChow (modificationBaseChangeOver f b g)
          (lineZeroModule (modificationBaseChangeToRelativeLine f b g))
          (lineZeroModuleSection (modificationBaseChangeToRelativeLine f b g)) (k + 1) β) =
      chowPushforwardOfIsClosedImmersion C (g ≫ f) (modificationBaseChangeOver f b g)
        (modificationSectionAtZeroBaseChange f b (isIso_modificationFibreAtZeroProjection f b hA)
          (modificationSectionAtZero_comp_projection f b hA) g)
        (modificationSectionAtZeroBaseChange_over f b g _ _) (k + 1) α := by
  have := isClosedImmersion_modificationSectionAtZeroBaseChange f b g hA
  have := flat_modificationAffineChartProjection f b g hA
  have := isIso_modificationAffineZeroScheme_comp f b g hA
  have hj := Stacks.Divisors.zeroSchemePullbackMap_comp_structureMorphism
    (modificationAffineChartι f b g) (lineZeroModule (modificationBaseChangeToRelativeLine f b g))
    (lineZeroModuleSection (modificationBaseChangeToRelativeLine f b g))
    (modificationBaseChangeOver f b g) (modificationAffineChartOver C f b g) rfl
  have hnat := gysinSystemOfInvertible_isNaturalUnderOpensRestriction C
    (modificationBaseChangeOver f b g) (modificationAffineChartOver C f b g)
    (modificationAffineChartι f b g) rfl
    (lineZeroModule (modificationBaseChangeToRelativeLine f b g))
    (lineZeroModuleSection (modificationBaseChangeToRelativeLine f b g)) (k + 1)
    (modificationAffineZeroSchemeMap f b g)
    (Stacks.Divisors.zeroSchemePullbackMap_comp_subschemeι _ _ _) hj β
  unfold IsModificationLift at hβ
  rw [hβ, gysinSystemOfInvertible_onChow_flatPullbackChow_of_isIso C
      (modificationAffineChartOver C f b g) (g ≫ f) (modificationAffineChartProjection f b g)
      (modificationAffineChartProjection_over C f b g)
      (relativeDimension_modificationAffineChartProjection f b g hA) _ _
      (isRelativeEffectiveCartierDivisor_modificationAffineZeroScheme f b g hA) k α,
    chowGroupRestrict_of_isIso] at hnat
  have key : (gysinSystemOfInvertible C).onChow (modificationBaseChangeOver f b g)
      (lineZeroModule (modificationBaseChangeToRelativeLine f b g))
      (lineZeroModuleSection (modificationBaseChangeToRelativeLine f b g)) (k + 1) β =
      chowPushforwardOfIso C _ _ (modificationAffineZeroSchemeMap f b g) hj (k + 1)
        (chowPushforwardOfIso C (g ≫ f) _
          (inv ((modificationAffineZeroScheme f b g).subschemeι ≫
            modificationAffineChartProjection f b g))
          (by rw [IsIso.inv_comp_eq, Category.assoc, modificationAffineChartProjection_over])
          (k + 1) α) := by
    rw [← hnat]
    exact ((chowGroupEquivOfIso C _ _ (modificationAffineZeroSchemeMap f b g) hj
      (k + 1)).apply_symm_apply _).symm
  rw [key, chowPushforwardOfIso_comp_apply]
  have hσ : modificationSectionAtZeroBaseChange f b
      (isIso_modificationFibreAtZeroProjection f b hA)
      (modificationSectionAtZero_comp_projection f b hA) g =
      (inv ((modificationAffineZeroScheme f b g).subschemeι ≫
        modificationAffineChartProjection f b g) ≫ modificationAffineZeroSchemeMap f b g) ≫
      (Stacks.Divisors.zeroScheme (modificationBaseChange f b g)
        (lineZeroModule (modificationBaseChangeToRelativeLine f b g))
        (lineZeroModuleSection (modificationBaseChangeToRelativeLine f b g))).subschemeι := by
    rw [modificationSectionAtZeroBaseChange_eq f b g hA, Category.assoc,
      Stacks.Divisors.zeroSchemePullbackMap_comp_subschemeι]
  rw [chowPushforwardOfIsClosedImmersion_congr C _ _ _ _ hσ _ (by
      rw [Category.assoc, ← Category.assoc _ _ (modificationBaseChangeOver f b g), ← hσ,
        modificationSectionAtZeroBaseChange_over])]
  exact (properChowPushforward_comp_apply C (g ≫ f)
    ((Stacks.Divisors.zeroScheme (modificationBaseChange f b g)
      (lineZeroModule (modificationBaseChangeToRelativeLine f b g))
      (lineZeroModuleSection (modificationBaseChangeToRelativeLine f b g))).subschemeι ≫
      modificationBaseChangeOver f b g) (modificationBaseChangeOver f b g)
    (inv ((modificationAffineZeroScheme f b g).subschemeι ≫
      modificationAffineChartProjection f b g) ≫ modificationAffineZeroSchemeMap f b g)
    (Stacks.Divisors.zeroScheme (modificationBaseChange f b g)
      (lineZeroModule (modificationBaseChangeToRelativeLine f b g))
      (lineZeroModuleSection (modificationBaseChangeToRelativeLine f b g))).subschemeι
    _ rfl _ rfl _ (k + 1) _ _ _ α).symm

/-- **Stacks 0F9J, the pushforward identity.** On every test scheme `g : T ⟶ X` locally of finite
type, `i_{∞,*}(C ∩ α) = i_{0,*} α` in `A_k(W ×_X T)`, for the cap operation
`Stacks.Chow.gysinCapAtInfinity` of the class at infinity.

For a lift `β` of `α`, `C ∩ α = i_∞^* β`; the Gysin images `i_∞^* β` and `i_0^* β` have the same
pushforward to `W ×_X T`, the divisors `D_0` and `D_∞` of `𝐏¹` being rationally equivalent
(`Stacks.Chow.modificationZeroGysin_eq_infinityGysin`); and `i_0^* β = α`
(`Stacks.Chow.chowPushforward_zeroGysin_of_isModificationLift`). -/
@[stacks 0F9J "the pushforward identity i_{∞,*}(C ∩ α) = i_{0,*} α on every test scheme \
locally of finite type over X"]
theorem chowPushforward_gysinCapOfLift
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) (k : ℤ)
    (α : chowGroup C (g ≫ f) k) :
    haveI := isClosedImmersion_modificationSectionAtZeroBaseChange f b g hA
    chowPushforwardOfIsClosedImmersion C (modificationInfinityBaseChangeOver f b g)
        (modificationBaseChangeOver f b g) (modificationInfinityBaseChange f b g)
        (modificationInfinityBaseChange_over f b g) k (gysinCapAtInfinity C f b hA g k α) =
      chowPushforwardOfIsClosedImmersion C (g ≫ f) (modificationBaseChangeOver f b g)
        (modificationSectionAtZeroBaseChange f b (isIso_modificationFibreAtZeroProjection f b hA)
          (modificationSectionAtZero_comp_projection f b hA) g)
        (modificationSectionAtZeroBaseChange_over f b g _ _) k α := by
  have := isClosedImmersion_modificationSectionAtZeroBaseChange f b g hA
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, k = m + 1 := ⟨k - 1, by ring⟩
  obtain ⟨β, hβ⟩ := exists_isModificationLift C f b hA g (m + 1) α
  rw [gysinCapAtInfinity_eq_of_isModificationLift C f b hA g (m + 1) α β hβ,
    ← chowPushforward_zeroGysin_of_isModificationLift C f b g hA m α β hβ,
    modificationZeroGysin_eq_infinityGysin C f b g (m + 1) β, modificationInfinityGysin,
    AddMonoidHom.comp_apply]
  exact (properChowPushforward_comp_apply C _ (modificationInfinityBaseChangeOver f b g)
    (modificationBaseChangeOver f b g) (modificationInfinityZeroSchemeIso f b g).hom
    (modificationInfinityBaseChange f b g) _ (modificationInfinityZeroSchemeIso_hom_comp f b g)
    _ _ rfl (m + 1) _ _ _ _).symm

end ZeroGysinChow

end Stacks.Chow

end
