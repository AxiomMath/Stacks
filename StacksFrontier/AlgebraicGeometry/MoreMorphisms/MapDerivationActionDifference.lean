module

public import StacksFrontier.AlgebraicGeometry.Conormal.SquareMap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDifferenceDerivationSheaf

/-!
# Infinitesimal deformations of maps: the lift `θ ⬝ a'` and its difference derivation

Let `S` be a scheme, let `i : X ⟶ X'` be a first-order thickening, let `j : Y ⟶ Y'` be an
immersion with structure morphism `q : Y' ⟶ S`, let `a' : X' ⟶ Y'` be a lift of `a : X ⟶ Y`
along `j`, and let `θ : a^*Ω_{Y/S} ⟶ 𝒞_{X/X'}` be an `𝒪_X`-linear map.
[Stacks Project, Tag 02H5] moves `a'` to a second lift `θ ⬝ a'`, which is
`Stacks.Thickenings.derivationActionSheaf`. [Stacks Project, Tag 0CK1] explains what the notation
`θ ⬝ a'` means: that `(a')^♯` and `(θ ⬝ a')^♯` differ by a derivation `D`, and that `D` is related
to `θ` by Equation [Stacks Project, Tag 04BV], `D = d_{Y/S} ∘ θ`.

**This file proves that for arbitrary `X'`, `Y'` and `S`** — no scheme is assumed affine anywhere
— with `D` the *difference derivation* of the unrestricted [Stacks Project, Tag 04FG],
`Stacks.Thickenings.differenceDerivation` of
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/MapDifferenceDerivationSheaf.lean`. So the
derivation
the statement speaks about is the one canonically attached to the pair of lifts, not one read off
the construction of `θ ⬝ a'`. The affine case over global sections is
`Stacks.Thickenings.derivationAction_mapDifferenceDerivation` in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/MapDerivationAction.lean`; nothing here is deduced
from it.

## Main definitions

* `Stacks.Thickenings.derivationActionDifferenceDerivation`: the derivation `D` of
  [Stacks Project, Tag 04FG] for the pair `(a', θ ⬝ a')`, that is,
  `Stacks.Thickenings.differenceDerivation` with its hypotheses discharged.

## Main results

* `Stacks.Thickenings.differenceDerivation_derivationActionSheaf`:
  **[Stacks Project, Tag 0CK1]**, both of its clauses — `D = d_{Y/S} ∘ θ`, and the comorphisms of
  `a'` and of `θ ⬝ a'` differ by `D`.
* `Stacks.Thickenings.immersionConormalSheafMap_derivationActionSheaf`: `θ ⬝ a'` induces the same
  map `a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` of [Stacks Project, Tag 01R4] as `a'`, which is condition (2) of
  [Stacks Project, Tag 04FG] for the pair. This is what makes the difference derivation of that
  tag available for the pair at all, and it is proved here for arbitrary schemes.
* `Stacks.Thickenings.derivationActionDifferenceDerivation_eq`: the first clause on its own, as an
  equality of `𝒪_S`-derivations `𝒪_Y ⟶ a_*𝒞_{X/X'}`.
* `Stacks.Thickenings.conormalClass_firstOrderImmersionConormalSheafι` and
  `Stacks.Thickenings.injective_firstOrderImmersionConormalSheafι_val_app`: for a first-order
  thickening the conormal class inverts the inclusion `𝒞_{X/X'} ⟶ 𝒪_{X'}` on sections, so that
  inclusion is injective on sections.
* `Stacks.Thickenings.pullback_relativeDifferentials_hom_ext`: a morphism out of `j^*Ω_{Y'/S}` is
  determined by its transpose on the universal differentials of `𝒪_{Y'}`.

## Route

The three conditions `Stacks.Thickenings.differenceDerivation` needs for the pair `(a', θ ⬝ a')`
are discharged first. Two are immediate from the construction of `θ ⬝ a'`
(`Stacks.Thickenings.derivationActionSheaf_comm` and
`Stacks.Thickenings.derivationActionSheaf_comp`); the third is condition (2) of
[Stacks Project, Tag 04FG], and it is proved from the affine characterisation
`Stacks.Immersion.IsInducedConormalSheafMap` of [Stacks Project, Tag 01R4]. That
characterisation mentions the comorphism only on elements of an ideal cutting out `Y ∩ V` in an
affine open `V ⊆ Y'`, and on those `θ ⬝ a'` and `a'` have the same comorphism, because such an
element is killed by `j^♯` while the perturbation applies `θ ∘ d_{Y/S}` to `j^♯` of it. No
affine chart is chosen: the charts are the ones the characterisation quantifies over.

Equation [Stacks Project, Tag 04BV] is then proved by descending twice.

1. Over an open `V` of `Y'` and a section `s` of `𝒪_{Y'}`, both the difference derivation of
   [Stacks Project, Tag 04FL] for the pair and `θ (d_{Y/S}(j^♯ s))` are conormal sections of `i`,
   and both are carried to `(θ ⬝ a')^♯ s - (a')^♯ s` by the inclusion `𝒞_{X/X'} ⟶ 𝒪_{X'}`. That
   inclusion is injective on sections, which is
   `Stacks.Thickenings.injective_firstOrderImmersionConormalSheafι_val_app`, so the two agree.
2. A morphism out of `j^*Ω_{Y'/S}` is determined by the derivation its transpose induces, so
   step 1 identifies the difference map `j^*Ω_{Y'/S} ⟶ a_*𝒞_{X/X'}` of
   [Stacks Project, Tag 04FG] with `d_{Y/S}` followed by `θ`.
3. The second arrow `j^*Ω_{Y'/S} ⟶ Ω_{Y/S}` of the conormal sequence of `j` is an epimorphism
   (`Stacks.ConormalSequenceRight.differentialsMapOver_epi`), and the difference derivation is
   the descent of the difference map along it, so cancelling that epimorphism turns step 2 into
   the equality of the two morphisms out of `Ω_{Y/S}`, hence of the two derivations.

## Generality

The hypotheses are weaker than the source's. `j` need only be an immersion, not a first-order
thickening, and no structure morphism `X' ⟶ S` is assumed: the lift `θ ⬝ a'` is a morphism over
`S` for the structure morphism `a' ≫ q` of `a'`
(`Stacks.Thickenings.derivationActionSheaf_comp_self`), which is all the difference derivation
needs. For `i` the full first-order thickening hypothesis is used.

## References

* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 02H5](https://stacks.math.columbia.edu/tag/02H5)
* [Stacks Project, Tag 04BV](https://stacks.math.columbia.edu/tag/04BV)
* [Stacks Project, Tag 04FG](https://stacks.math.columbia.edu/tag/04FG)
* [Stacks Project, Tag 04FL](https://stacks.math.columbia.edu/tag/04FL)
* [Stacks Project, Tag 0CK1](https://stacks.math.columbia.edu/tag/0CK1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction AlgebraicGeometry.RingedSpace

universe u

namespace Stacks.Thickenings

/-! ### The conormal class of a conormal section -/

section ConormalClass

variable {X X' : Scheme.{u}} (i : X ⟶ X') [AlgebraicGeometry.IsClosedImmersion i]

/-- **The conormal class of a conormal section is that section**, for a first-order thickening.
The inclusion `𝒞_{X/X'} ⟶ 𝒪_{X'}` is inverse to the conormal class on sections, because for a
first-order thickening the quotient map `ℐ ⟶ i_* 𝒞_{X/X'}` is an isomorphism
(`Stacks.Thickenings.isIso_canonicalConormalQuotientMap`). -/
theorem conormalClass_firstOrderImmersionConormalSheafι (hi : i.ker ^ 2 = ⊥) (U : X'.Opens)
    (m : (Stacks.Conormal.conormalSheaf i).val.obj (op (i ⁻¹ᵁ U)))
    (hm : (i.app U).hom ((firstOrderImmersionConormalSheafι i hi).val.app (op U) m) = 0) :
    Stacks.Conormal.conormalClass i U (le_refl (i ⁻¹ᵁ U))
        ((firstOrderImmersionConormalSheafι i hi).val.app (op U) m) hm = m := by
  have := isIso_canonicalConormalQuotientMap i hi
  obtain ⟨y, hy⟩ :
      ∃ y, (Stacks.Immersion.canonicalConormalQuotientMap i).val.app (op U) y = m := by
    refine ⟨(inv (Stacks.Immersion.canonicalConormalQuotientMap i)).val.app (op U) m, ?_⟩
    have hsplit := comp_val_app_apply
      (inv (Stacks.Immersion.canonicalConormalQuotientMap i))
      (Stacks.Immersion.canonicalConormalQuotientMap i) (op U) m
    have hid := congrArg (fun φ ↦ φ.val.app (op U) m)
      (IsIso.inv_hom_id (Stacks.Immersion.canonicalConormalQuotientMap i))
    refine (hsplit.symm.trans hid).trans ?_
    rfl
  have hr : (Stacks.ClosedImmersion.idealSheafι i.toLRSHom.toShHom).val.app (op U) y =
      (firstOrderImmersionConormalSheafι i hi).val.app (op U) m := by
    have hpin := congrArg (fun φ ↦ φ.val.app (op U) y)
      (canonicalConormalQuotientMap_comp_firstOrderImmersionConormalSheafι i hi)
    have hsplit := comp_val_app_apply (Stacks.Immersion.canonicalConormalQuotientMap i)
      (firstOrderImmersionConormalSheafι i hi) (op U) y
    exact (hsplit.symm.trans hpin).symm.trans
      (congrArg (fun z ↦ (firstOrderImmersionConormalSheafι i hi).val.app (op U) z) hy)
  rw [Stacks.Conormal.conormalClass_eq_canonicalConormalQuotientMap i U (le_refl (i ⁻¹ᵁ U))
    _ hm y hr, hy]
  exact Stacks.Conormal.conormalSheaf_map_self i (le_refl (i ⁻¹ᵁ U)) m

/-- **The inclusion `𝒞_{X/X'} ⟶ 𝒪_{X'}` of a first-order thickening is injective on sections.**
A section is recovered from its image by taking the conormal class
(`Stacks.Thickenings.conormalClass_firstOrderImmersionConormalSheafι`). -/
theorem injective_firstOrderImmersionConormalSheafι_val_app (hi : i.ker ^ 2 = ⊥)
    (U : X'.Opens) :
    Function.Injective ((firstOrderImmersionConormalSheafι i hi).val.app (op U)) := by
  intro m₁ m₂ h
  have h1 := conormalClass_firstOrderImmersionConormalSheafι i hi U m₁
    (app_firstOrderImmersionConormalSheafι_eq_zero i hi U m₁)
  have h2 := conormalClass_firstOrderImmersionConormalSheafι i hi U m₂
    (app_firstOrderImmersionConormalSheafι_eq_zero i hi U m₂)
  rw [← h1, ← h2]
  exact Stacks.Conormal.conormalClass_congr i U (le_refl (i ⁻¹ᵁ U)) h _ _

end ConormalClass

/-! ### Morphisms out of a pulled-back sheaf of relative differentials -/

section Ext

/-- **The transpose of a morphism out of a pullback, read on sections.** It is the morphism
itself applied to the image of the section under the unit of `j^* ⊣ j_*`. -/
theorem homEquiv_val_app_apply {Y Y' : Scheme.{u}} (j : Y ⟶ Y') {A : Y'.Modules} {N : Y.Modules}
    (f : (Scheme.Modules.pullback j).obj A ⟶ N) (V : Y'.Opens) (x : A.val.obj (op V)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv A N f).val.app (op V)).hom x =
      (f.val.app (op (j ⁻¹ᵁ V))).hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app A).val.app (op V)).hom x) := by
  rw [Adjunction.homEquiv_unit]
  rfl

/-- **A morphism out of `j^*Ω_{Y'/S}` is determined by its transpose on the universal
differentials.** Transposing along `j^* ⊣ j_*` turns such a morphism into a morphism out of
`Ω_{Y'/S}`, and a morphism out of `Ω_{Y'/S}` is determined by the derivation it induces
(`AlgebraicGeometry.SheafOfModules.universalDerivation_isUniversal`), hence by its values on the
universal differentials `d_{Y'/S} s`. -/
theorem pullback_relativeDifferentials_hom_ext {Y Y' S : Scheme.{u}} (j : Y ⟶ Y') (q : Y' ⟶ S)
    {N : Y.Modules}
    {ψ₁ ψ₂ : (Scheme.Modules.pullback j).obj (Scheme.Hom.relativeDifferentials q) ⟶ N}
    (h : ∀ (V : Y'.Opens) (s : Γ(Y', V)),
      (((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv
            (Scheme.Hom.relativeDifferentials q) N ψ₁).val.app (op V)).hom
          ((Scheme.Hom.universalRelativeDerivation q).d s) =
        (((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv
            (Scheme.Hom.relativeDifferentials q) N ψ₂).val.app (op V)).hom
          ((Scheme.Hom.universalRelativeDerivation q).d s)) :
    ψ₁ = ψ₂ := by
  refine ((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv
    (Scheme.Hom.relativeDifferentials q) N).injective ?_
  have hd : (Scheme.Hom.universalRelativeDerivation q).postcomp
        (((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv
          (Scheme.Hom.relativeDifferentials q) N ψ₁)).val =
      (Scheme.Hom.universalRelativeDerivation q).postcomp
        (((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv
          (Scheme.Hom.relativeDifferentials q) N ψ₂)).val :=
    PresheafOfModulesOfCommRing.Derivation.ext (funext fun U ↦ AddMonoidHom.ext fun s ↦ h U.unop s)
  obtain ⟨f, -, hu⟩ := AlgebraicGeometry.SheafOfModules.universalDerivation_isUniversal
    (inverseImageStructureMap q) ((Scheme.Modules.pushforward j).obj N)
    ((Scheme.Hom.universalRelativeDerivation q).postcomp
      (((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv
        (Scheme.Hom.relativeDifferentials q) N ψ₂)).val)
  exact (hu _ hd).trans (hu _ rfl).symm

end Ext

/-! ### Condition (2) of Tag 04FG for the lift `θ ⬝ a'` -/

section Action

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y} {a' : X' ⟶ Y'}
  [AlgebraicGeometry.IsClosedImmersion i] [IsImmersion j]

variable (hi : i.ker ^ 2 = ⊥) (q : Y' ⟶ S) (ca : i ≫ a' = a ≫ j)
  (θ : (Scheme.Modules.pullback a).obj (Scheme.Hom.relativeDifferentials (j ≫ q)) ⟶
    Stacks.Conormal.conormalSheaf i)

/-- A restricted comorphism is the comorphism followed by the restriction map. -/
private theorem appLE_hom_apply {X' Y' : Scheme.{u}} (f : X' ⟶ Y') {V : Y'.Opens}
    {U : X'.Opens} (h : U ≤ f ⁻¹ᵁ V) (x : Γ(Y', V)) :
    (f.appLE V U h).hom x = (X'.presheaf.map (homOfLE h).op).hom ((f.app V).hom x) :=
  CommRingCat.comp_apply _ _ x

/-- **The lift `θ ⬝ a'` induces the same map of conormal sheaves as `a'`**, which is condition
(2) of [Stacks Project, Tag 04FG] for the pair `(a', θ ⬝ a')`, for arbitrary schemes.

The affine characterisation `Stacks.Immersion.IsInducedConormalSheafMap` of
[Stacks Project, Tag 01R4] determines the induced map
(`Stacks.Immersion.immersionConormalSheafMap_unique`), and the map induced by `a'` satisfies
it for the square of `θ ⬝ a'` as well: the characterisation only mentions the comorphism on
elements of an ideal cutting out `Y ∩ V`, and `θ ⬝ a'` has the same comorphism as `a'` there,
because such an element is killed by `j^♯` (`Stacks.Immersion.app_eq_zero_of_mem`) and the
perturbation `D = θ ∘ d_{Y/S}` is applied to `j^♯` of the element. -/
theorem immersionConormalSheafMap_derivationActionSheaf :
    Stacks.Immersion.immersionConormalSheafMap i j a (derivationActionSheaf hi q ca θ)
        (Stacks.Immersion.toShHom_square (derivationActionSheaf_comm hi q ca θ)) =
      Stacks.Immersion.immersionConormalSheafMap i j a a'
        (Stacks.Immersion.toShHom_square ca) := by
  refine (Stacks.Immersion.immersionConormalSheafMap_unique i j a
    (derivationActionSheaf hi q ca θ) (derivationActionSheaf_comm hi q ca θ)
    (Stacks.Immersion.immersionConormalSheafMap i j a a'
      (Stacks.Immersion.toShHom_square ca)) ?_).symm
  intro U hU V hV hUV I J eZ heZ eW heW x b hab
  refine Stacks.Immersion.isInducedConormalSheafMap_immersionConormalSheafMap i j a a' ca
    U hU V hV hUV I J eZ heZ eW heW x b ?_
  have hJ : (j.app V).hom (x : Γ(Y', V)) = 0 :=
    Stacks.Immersion.app_eq_zero_of_mem j V hV J eW heW (x : Γ(Y', V)) x.2
  have hD : derivationSectionι hi q ca θ V ((j.app V).hom (x : Γ(Y', V))) = 0 :=
    (congrArg (fun z ↦ derivationSectionι hi q ca θ V z) hJ).trans
      (derivationSectionι_zero hi q ca θ V)
  have happ : ((derivationActionSheaf hi q ca θ).app V).hom (x : Γ(Y', V)) =
      (a'.app V).hom (x : Γ(Y', V)) := by
    refine (derivationActionSheaf_app hi q ca θ V (x : Γ(Y', V))).trans ?_
    rw [hD, add_zero]
  rw [appLE_hom_apply _ hUV, happ] at hab
  exact hab.trans (appLE_hom_apply a' hUV _).symm

omit [IsImmersion j] in
/-- **`θ ⬝ a'` is a morphism over `S`**, with the same structure morphism as `a'`. -/
theorem derivationActionSheaf_comp_self :
    derivationActionSheaf hi q ca θ ≫ q = a' ≫ q :=
  derivationActionSheaf_comp hi q ca θ rfl

/-! ### The difference derivation of the pair `(a', θ ⬝ a')` -/

omit [IsImmersion j] in
/-- **The difference derivation of [Stacks Project, Tag 04FL] for the pair `(θ ⬝ a', a')` is
`θ ∘ d_{Y/S}`**, on a section pulled back from `𝒪_{Y'}`.

Both sides are conormal sections of `i` over `a⁻¹j⁻¹V`; the inclusion
`𝒞_{X/X'} ⟶ 𝒪_{X'}` is injective on sections
(`Stacks.Thickenings.injective_firstOrderImmersionConormalSheafι_val_app`) and sends them to the
same section of `𝒪_{X'}`, namely `(θ ⬝ a')^♯ s - (a')^♯ s`: on the left by
`Stacks.Thickenings.firstOrderImmersionConormalSheafι_liftDifferenceDerivation_d`, on the right
by `Stacks.Thickenings.map_conormalSectionι` together with
`Stacks.Thickenings.derivationActionSheaf_app`. -/
theorem liftDifferenceDerivation_d_derivationActionSheaf (V : Y'.Opens) (s : Γ(Y', V)) :
    (liftDifferenceDerivation (derivationActionSheaf_comp_self hi q ca θ).symm
          (derivationActionSheaf_comm hi q ca θ) ca).d (X := op V) s =
      (((Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv
          (Scheme.Hom.relativeDifferentials (j ≫ q)) (Stacks.Conormal.conormalSheaf i)
          θ).val.app (op (j ⁻¹ᵁ V))).hom
        ((Scheme.Hom.universalRelativeDerivation (j ≫ q)).d ((j.app V).hom s)) := by
  have hLi : i ⁻¹ᵁ liftPairOpen (derivationActionSheaf hi q ca θ) a' V = a ⁻¹ᵁ (j ⁻¹ᵁ V) :=
    preimage_liftPairOpen (derivationActionSheaf_comm hi q ca θ) ca V
  have hLa : liftPairOpen (derivationActionSheaf hi q ca θ) a' V ≤ a' ⁻¹ᵁ V := inf_le_left
  have hLb : liftPairOpen (derivationActionSheaf hi q ca θ) a' V ≤
    derivationActionSheaf hi q ca θ ⁻¹ᵁ V := inf_le_right
  -- the two comorphisms differ by the derivation `D`, over `a'⁻¹V`
  have hd : derivationSectionι hi q ca θ V ((j.app V).hom s) =
      (show Γ(X', a' ⁻¹ᵁ V) from ((derivationActionSheaf hi q ca θ).app V).hom s) -
        (a'.app V).hom s :=
    (add_sub_cancel_left ((a'.app V).hom s)
        (derivationSectionι hi q ca θ V ((j.app V).hom s))).symm.trans
      (congrArg (fun z : Γ(X', a' ⁻¹ᵁ V) ↦ z - (a'.app V).hom s)
        (derivationActionSheaf_app hi q ca θ V s).symm)
  refine module_map_injective_of_le hLi.le hLi.ge ?_
  refine injective_firstOrderImmersionConormalSheafι_val_app i hi
    (liftPairOpen (derivationActionSheaf hi q ca θ) a' V) ?_
  refine (firstOrderImmersionConormalSheafι_liftDifferenceDerivation_d hi
    (derivationActionSheaf_comp_self hi q ca θ).symm
    (derivationActionSheaf_comm hi q ca θ) ca V s).trans ?_
  refine Eq.trans ?_ (map_conormalSectionι hi ca V hLa hLi _)
  change (((derivationActionSheaf hi q ca θ).appLE V
        (liftPairOpen (derivationActionSheaf hi q ca θ) a' V) hLb).hom s -
      (a'.appLE V (liftPairOpen (derivationActionSheaf hi q ca θ) a' V) hLa).hom s) = _
  rw [appLE_hom_apply _ hLb, appLE_hom_apply _ hLa,
    ← derivationSectionι_eq, hd, map_sub]
  rfl

omit [IsImmersion j] in
/-- **The difference map of the pair `(θ ⬝ a', a')` is `d_{Y/S}` followed by `θ`.** Both are
morphisms `j^*Ω_{Y'/S} ⟶ a_*𝒞_{X/X'}`; they agree on the unit image of every universal
differential `d_{Y'/S} s`, which determines them
(`Stacks.Thickenings.pullback_relativeDifferentials_hom_ext`). -/
theorem differenceDerivationMap_derivationActionSheaf :
    differenceDerivationMap q (derivationActionSheaf_comp_self hi q ca θ).symm
        (derivationActionSheaf_comm hi q ca θ) ca =
      Scheme.Hom.relativeDifferentialsMap j q (j ≫ q) (𝟙 S) (by simp) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv
          (Scheme.Hom.relativeDifferentials (j ≫ q)) (Stacks.Conormal.conormalSheaf i) θ := by
  refine pullback_relativeDifferentials_hom_ext j q (fun V s ↦ ?_)
  rw [homEquiv_val_app_apply, homEquiv_val_app_apply]
  have hrdm : ((Scheme.Hom.relativeDifferentialsMap j q (j ≫ q) (𝟙 S)
          (by simp)).val.app (op (j ⁻¹ᵁ V))).hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
          (Scheme.Hom.relativeDifferentials q)).val.app (op V)).hom
          ((Scheme.Hom.universalRelativeDerivation q).d s)) =
      (Scheme.Hom.universalRelativeDerivation (j ≫ q)).d ((j.app V).hom s) :=
    (homEquiv_val_app_apply j (Scheme.Hom.relativeDifferentialsMap j q (j ≫ q) (𝟙 S) (by simp))
        V ((Scheme.Hom.universalRelativeDerivation q).d s)).symm.trans
      (Scheme.Hom.relativeDifferentialsMap_app_d (𝟙 S) (by simp) V s)
  refine Eq.trans ((differenceDerivationMap_unit_d q
    (derivationActionSheaf_comp_self hi q ca θ).symm
    (derivationActionSheaf_comm hi q ca θ) ca V s).trans
      (liftDifferenceDerivation_d_derivationActionSheaf hi q ca θ V s)) ?_
  exact (congrArg (fun z ↦ ((((Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv
      (Scheme.Hom.relativeDifferentials (j ≫ q)) (Stacks.Conormal.conormalSheaf i)
      θ).val.app (op (j ⁻¹ᵁ V))).hom z)) hrdm).symm

/-- **The difference derivation of the pair `(θ ⬝ a', a')` is `d_{Y/S}` followed by `θ`**, as a
morphism out of `Ω_{Y/S}`. The second arrow of the conormal sequence of `j` is an epimorphism
(`Stacks.ConormalSequenceRight.differentialsMapOver_epi`), so the equality follows from
`Stacks.Thickenings.differenceDerivationMap_derivationActionSheaf` by cancelling it. -/
theorem differenceDerivationHom_derivationActionSheaf :
    differenceDerivationHom q hi (derivationActionSheaf_comp_self hi q ca θ).symm
        (derivationActionSheaf_comm hi q ca θ) ca
        (immersionConormalSheafMap_derivationActionSheaf hi q ca θ) =
      (Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv
        (Scheme.Hom.relativeDifferentials (j ≫ q)) (Stacks.Conormal.conormalSheaf i) θ := by
  have := Stacks.ConormalSequenceRight.differentialsMapOver_epi j q
  refine (cancel_epi (Scheme.Hom.relativeDifferentialsMap j q (j ≫ q) (𝟙 S)
    (Category.comp_id (j ≫ q)).symm)).mp ?_
  exact (relativeDifferentialsMap_comp_differenceDerivationHom q hi
    (derivationActionSheaf_comp_self hi q ca θ).symm
    (derivationActionSheaf_comm hi q ca θ) ca
    (immersionConormalSheafMap_derivationActionSheaf hi q ca θ)).trans
      (differenceDerivationMap_derivationActionSheaf hi q ca θ)

/-- **The difference derivation `D` of [Stacks Project, Tag 04FG] for the pair `(a', θ ⬝ a')`.**
The `𝒪_S`-derivation `D : 𝒪_Y ⟶ a_*𝒞_{X/X'}` of `Stacks.Thickenings.differenceDerivation`, with
its five hypotheses discharged for the pair consisting of `a'` and the lift
`θ ⬝ a'` of `Stacks.Thickenings.derivationActionSheaf`: `θ ⬝ a'` is a lift of the same `a`
(`Stacks.Thickenings.derivationActionSheaf_comm`), it is a morphism over the same base
(`Stacks.Thickenings.derivationActionSheaf_comp_self`), and it induces the same map of conormal
sheaves (`Stacks.Thickenings.immersionConormalSheafMap_derivationActionSheaf`).

The two lifts are taken in the order that makes `D` the difference `(θ ⬝ a')^♯ - (a')^♯`, which
is the sign convention of [Stacks Project, Tag 02H5]. -/
def derivationActionDifferenceDerivation :
    SheafOfModules.SheafDerivation (inverseImageStructureMap (j ≫ q))
      ((Scheme.Modules.pushforward a).obj (Stacks.Conormal.conormalSheaf i)) :=
  differenceDerivation q hi (derivationActionSheaf_comp_self hi q ca θ).symm
    (derivationActionSheaf_comm hi q ca θ) ca
    (immersionConormalSheafMap_derivationActionSheaf hi q ca θ)

/-- **Equation [Stacks Project, Tag 04BV] for the lift `θ ⬝ a'`**: the difference derivation of
[Stacks Project, Tag 04FG] attached to the pair `(a', θ ⬝ a')` is `d_{Y/S}` followed by `θ`. -/
theorem derivationActionDifferenceDerivation_eq :
    derivationActionDifferenceDerivation hi q ca θ =
      (Scheme.Hom.universalRelativeDerivation (j ≫ q)).postcomp
        ((Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv
          (Scheme.Hom.relativeDifferentials (j ≫ q)) (Stacks.Conormal.conormalSheaf i) θ).val :=
  congrArg
    (fun φ : Scheme.Hom.relativeDifferentials (j ≫ q) ⟶
        (Scheme.Modules.pushforward a).obj (Stacks.Conormal.conormalSheaf i) ↦
      (Scheme.Hom.universalRelativeDerivation (j ≫ q)).postcomp φ.val)
    (differenceDerivationHom_derivationActionSheaf hi q ca θ)

/-- **[Stacks Project, Tag 0CK1], for arbitrary schemes.** Let `S` be a scheme, let
`i : X ⟶ X'` be a first-order thickening, let `j : Y ⟶ Y'` be an immersion with structure
morphism `q : Y' ⟶ S`, let `(a, a')` be a morphism of thickenings `(X ⊂ X') ⟶ (Y ⊂ Y')` over
`S`, and let `θ : a^*Ω_{Y/S} ⟶ 𝒞_{X/X'}` be an `𝒪_X`-linear map. The source writes `θ ⬝ a'` for
the lift [Stacks Project, Tag 02H5] attaches to `θ`, which is
`Stacks.Thickenings.derivationActionSheaf`, and says that this notation *means nothing else than*
the following two things.

* The derivation `D` of [Stacks Project, Tag 04FG] attached to the pair `(a', θ ⬝ a')` — the
  `𝒪_S`-derivation `𝒪_Y ⟶ a_*𝒞_{X/X'}` of
  `Stacks.Thickenings.derivationActionDifferenceDerivation` — is related to `θ` by Equation
  [Stacks Project, Tag 04BV]: it is `d_{Y/S}` followed by `θ`, read through the transpose of `θ`
  along `a^* ⊣ a_*`. That is the first conjunct.
* The comorphisms `(a')^♯` and `(θ ⬝ a')^♯` differ by `D`: on a section `s` of `𝒪_{Y'}` over an
  open `V`, `(θ ⬝ a')^♯ s = (a')^♯ s + D (j^♯ s)`, the value of `D` being read inside `𝒪_{X'}`
  through the inclusion `𝒞_{X/X'} ⟶ 𝒪_{X'}` by `Stacks.Thickenings.conormalSectionι`. That is
  the second conjunct.

Nothing is affine, and the datum is the one of the source: a morphism of sheaves of `𝒪_X`-modules
out of the pulled-back sheaf of relative differentials. The derivation is the one
[Stacks Project, Tag 04FG] attaches to the pair, with all three of that tag's hypotheses
discharged for it — in particular condition (2), which is
`Stacks.Thickenings.immersionConormalSheafMap_derivationActionSheaf`. -/
@[stacks 0CK1]
theorem differenceDerivation_derivationActionSheaf :
    derivationActionDifferenceDerivation hi q ca θ =
        (Scheme.Hom.universalRelativeDerivation (j ≫ q)).postcomp
          ((Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv
            (Scheme.Hom.relativeDifferentials (j ≫ q))
            (Stacks.Conormal.conormalSheaf i) θ).val ∧
      ∀ (V : Y'.Opens) (s : Γ(Y', V)),
        ((derivationActionSheaf hi q ca θ).app V).hom s =
          (a'.app V).hom s +
            conormalSectionι hi ca V
              ((derivationActionDifferenceDerivation hi q ca θ).d (X := op (j ⁻¹ᵁ V))
                ((j.app V).hom s)) := by
  refine ⟨derivationActionDifferenceDerivation_eq hi q ca θ, fun V s ↦ ?_⟩
  have hD : (derivationActionDifferenceDerivation hi q ca θ).d (X := op (j ⁻¹ᵁ V))
        ((j.app V).hom s) =
      (((Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv
          (Scheme.Hom.relativeDifferentials (j ≫ q)) (Stacks.Conormal.conormalSheaf i)
          θ).val.app (op (j ⁻¹ᵁ V))).hom
        ((Scheme.Hom.universalRelativeDerivation (j ≫ q)).d ((j.app V).hom s)) :=
    PresheafOfModulesOfCommRing.Derivation.congr_d
      (derivationActionDifferenceDerivation_eq hi q ca θ)
      ((j.app V).hom s)
  refine (derivationActionSheaf_app hi q ca θ V s).trans ?_
  exact congrArg (fun z : Γ(X', a' ⁻¹ᵁ V) ↦ (a'.app V).hom s + z)
    ((derivationSectionι_eq hi q ca θ V ((j.app V).hom s)).trans
      (congrArg (conormalSectionι hi ca V) hD.symm))

end Action

end Stacks.Thickenings

end
