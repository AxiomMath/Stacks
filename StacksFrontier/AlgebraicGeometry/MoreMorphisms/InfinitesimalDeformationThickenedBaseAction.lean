module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomPrecomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.TriangleMono
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationSheafHomTransitivity
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationThickenedBase
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The action on the lifting sheaf over a thickened base

Let `k : Z ⟶ Z'` be an immersion, let `i : X ⟶ X'` be a first order thickening and `j : Y ⟶ Y'`
an immersion, both over `Z'`, and assume `Y = Z ×_{Z'} Y'`. This is the situation of
[Stacks Project, Tag 0CK2]. The conormal datum `A` is then determined by `a` and the sheaf of
[Stacks Project, Tag 04FH] is the elementary rule `Stacks.Thickenings.liftsOverBasePresheaf` of
morphisms `V ⟶ Y'` over `Z'` restricting to `a` on `i⁻¹V`; both are in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationThickenedBase`.

This file supplies the remaining assertion of the remark: that
`Hom_{𝒪_X}(a^*Ω_{Y/Z}, 𝒞_{X/X'})` — the differentials taken **relative to `Z`**, as the source
writes them — acts on that elementary rule, simply transitively over an open carrying a lift,
and compatibly with the restriction maps.

## Main definitions

* `Stacks.Thickenings.compatibleLiftsEquivLiftsOverBaseOfBase`: the bijection between the lifts
  of [Stacks Project, Tag 04FI] over an open `V` and the elementary lifts over `V`, for a
  base-compatible datum. It is the identity on underlying morphisms.
* `Stacks.Thickenings.pullbackCotangentSheafIsoOfBase`: the identification
  `a^*Ω_{Y/Z'} ≅ a^*Ω_{Y/Z}`.
* `Stacks.Thickenings.baseDeformationHomSectionsEquiv`: the resulting identification of the
  acting groups, `Hom(a^*Ω_{Y/Z}, 𝒞_{X/X'})|_{i⁻¹V} ≃+ Hom(a^*Ω_{Y/Z'}, 𝒞_{X/X'})|_{i⁻¹V}`.
* `Stacks.Thickenings.liftsOverBaseVAddOfBase`: the action of a section of
  `SheafHom_{𝒪_X}(a^*Ω_{Y/Z}, 𝒞_{X/X'})` over `i⁻¹V` on an elementary lift over `V`.

## Main results

* `Stacks.Thickenings.exists_simplyTransitive_addAction_liftsOverBaseOfBase`: **the action
  clause of [Stacks Project, Tag 0CK2]**, with the group laws, the compatibility with
  restriction, and simple transitivity over an open carrying a lift.

## Route

Two transports of results already in the library, and nothing reproved.

The third condition of [Stacks Project, Tag 04FI] is automatic for a base-compatible datum
(`Stacks.Thickenings.isCompatibleLift_iff_of_isBaseCompatible`), so the lifts of that tag over
an open and the elementary lifts over it differ only in the proof component of a subtype; the
action, its group laws, its compatibility with restriction and its simple transitivity are the
unrestricted [Stacks Project, Tag 04FJ] — `Stacks.Thickenings.compatibleLiftsVAdd`,
`Stacks.Thickenings.homSectionAct_zero`, `Stacks.Thickenings.homSectionAct_add`,
`Stacks.Thickenings.compatibleLiftsRestrict_compatibleLiftsVAdd` and
`Stacks.Thickenings.existsUnique_compatibleLiftsVAdd_eq` — transported along the bijection.

Tag 04FJ acts by the differentials of `Y` relative to the base over which the lifts are taken,
here `Z'`; the source of Tag 0CK2 writes the acting sheaf with the differentials relative to
`Z`. The two agree: `k` is an immersion, hence a monomorphism, so the canonical map
`Ω_{Y/Z'} ⟶ Ω_{Y/Z}` is an isomorphism by
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsIsoOfEq`
([Stacks Project, Tag 01UX] together with [Stacks Project, Tag 01UY]). The statement below is
written with the source's `Ω_{Y/Z}`, and that isomorphism is what carries the action over.

## Implementation notes

The structure morphism of `Y` over `Z'` arrives from the cartesian square as `j ≫ h'`, which is
*equal* to `h ≫ k` rather than syntactically that composite; this is why the differentials
isomorphism is taken in the displaced form
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsIsoOfEq`, which takes the factorisation as an
equality. Nothing is transported along an equality of objects.

The passage from an isomorphism of sheaves of modules to one of the groups of sections of the
sheaves of homomorphisms over an open is precomposition, and it commutes with restriction of
sections because precomposition with a fixed map is natural in the open
(`Stacks.SheafOfModules.restrictOverHom_comp_left`); this is the pattern of
`Stacks.Smooth.deformationHomSectionsEquiv` and
`Stacks.Smooth.deformationHomSectionsEquiv_restrict`.

## References

* [Stacks Project, Tag 01UX](https://stacks.math.columbia.edu/tag/01UX)
* [Stacks Project, Tag 01UY](https://stacks.math.columbia.edu/tag/01UY)
* [Stacks Project, Tag 04FH](https://stacks.math.columbia.edu/tag/04FH)
* [Stacks Project, Tag 04FI](https://stacks.math.columbia.edu/tag/04FI)
* [Stacks Project, Tag 04FJ](https://stacks.math.columbia.edu/tag/04FJ)
* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction
open AlgebraicGeometry
open Stacks.Immersion

universe u

namespace Stacks.Thickenings

variable {X X' Y Y' Z Z' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {k : Z ⟶ Z'}
  [IsClosedImmersion i] [IsImmersion j] [IsImmersion k]
  {h : Y ⟶ Z} {h' : Y' ⟶ Z'} {g' : X' ⟶ Z'} {a : X ⟶ Y}

/-! ### The two notions of lift over an open agree -/

/-- **The lifts of [Stacks Project, Tag 04FI] are the elementary lifts over a thickened base**,
as a bijection over each open `V` of `X'`. For a base-compatible datum the third condition of
that tag is automatic by `Stacks.Thickenings.isCompatibleLift_iff_of_isBaseCompatible`, so both
sides are the morphisms `V ⟶ Y'` over `Z'` restricting to `a` on `i⁻¹V`, and the bijection is
the identity on underlying morphisms. -/
def compatibleLiftsEquivLiftsOverBaseOfBase (sq : IsPullback j h h' k)
    (ci : i ≫ g' = (a ≫ h) ≫ k)
    {A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i}
    (hA : IsBaseCompatibleConormalMap i j k h h' g' a sq.w ci A) (V : X'.Opens) :
    compatibleLifts g' h' a A V ≃ liftsOverBase i j g' h' a V where
  toFun c := ⟨c.1, (isCompatibleLift_iff_of_isBaseCompatible sq ci hA V c.1).mp c.2⟩
  invFun c := ⟨c.1, (isCompatibleLift_iff_of_isBaseCompatible sq ci hA V c.1).mpr c.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The bijection of `Stacks.Thickenings.compatibleLiftsEquivLiftsOverBaseOfBase` is the
identity on underlying morphisms. -/
theorem compatibleLiftsEquivLiftsOverBaseOfBase_coe (sq : IsPullback j h h' k)
    (ci : i ≫ g' = (a ≫ h) ≫ k)
    {A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i}
    (hA : IsBaseCompatibleConormalMap i j k h h' g' a sq.w ci A) (V : X'.Opens)
    (c : compatibleLifts g' h' a A V) :
    (compatibleLiftsEquivLiftsOverBaseOfBase sq ci hA V c).1 = c.1 := rfl

/-- **The bijection intertwines the two restriction maps.** Both
`Stacks.Thickenings.compatibleLiftsRestrict` and `Stacks.Thickenings.liftsOverBaseRestrict`
compose the lift with the inclusion `V' ⟶ V`. -/
theorem liftsOverBaseRestrict_compatibleLiftsEquivLiftsOverBaseOfBase
    (sq : IsPullback j h h' k) (ci : i ≫ g' = (a ≫ h) ≫ k)
    {A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i}
    (hA : IsBaseCompatibleConormalMap i j k h h' g' a sq.w ci A) {V V' : X'.Opens} (hV : V' ≤ V)
    (c : compatibleLifts g' h' a A V) :
    liftsOverBaseRestrict i j g' h' a hV
        (compatibleLiftsEquivLiftsOverBaseOfBase sq ci hA V c)
      = compatibleLiftsEquivLiftsOverBaseOfBase sq ci hA V'
          (compatibleLiftsRestrict g' h' a A hV c) :=
  Subtype.ext rfl

/-- **The bijection intertwines the two restriction maps**, in the direction needed for the
inverse. -/
theorem compatibleLiftsRestrict_compatibleLiftsEquivLiftsOverBaseOfBase_symm
    (sq : IsPullback j h h' k) (ci : i ≫ g' = (a ≫ h) ≫ k)
    {A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i}
    (hA : IsBaseCompatibleConormalMap i j k h h' g' a sq.w ci A) {V V' : X'.Opens} (hV : V' ≤ V)
    (c : liftsOverBase i j g' h' a V) :
    compatibleLiftsRestrict g' h' a A hV
        ((compatibleLiftsEquivLiftsOverBaseOfBase sq ci hA V).symm c)
      = (compatibleLiftsEquivLiftsOverBaseOfBase sq ci hA V').symm
          (liftsOverBaseRestrict i j g' h' a hV c) :=
  Subtype.ext rfl

/-! ### The differentials relative to `Z` and relative to `Z'` -/

/-- **`a^*Ω_{Y/Z'} ≅ a^*Ω_{Y/Z}`.** The canonical map `Ω_{Y/Z'} ⟶ Ω_{Y/Z}` is an isomorphism
because `k` is an immersion, hence a monomorphism
(`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsIsoOfEq`); this reads it in the
`Stacks.Smooth.cotangentSheaf` spelling that [Stacks Project, Tag 04FJ] acts through, and pulls
it back along `a`. -/
def pullbackCotangentSheafIsoOfBase (sq : IsPullback j h h' k) (a : X ⟶ Y) :
    Stacks.Smooth.pullbackCotangentSheaf (j ≫ h') a ≅ Stacks.Smooth.pullbackCotangentSheaf h a :=
  (Scheme.Modules.pullback a).mapIso
    ((Scheme.Hom.cotangentSheafIso (j ≫ h')).symm ≪≫
      Scheme.Hom.relativeDifferentialsIsoOfEq (j ≫ h') h k sq.w ≪≫
      Scheme.Hom.cotangentSheafIso h)

section HomSectionsTransport

variable {W : Scheme.{u}} {M M' N : W.Modules}

/-- **An isomorphism of the source identifies the sections of the two sheaves of
homomorphisms.** Precomposition with `e.hom` sends a map `M'|_U ⟶ N|_U` to a map
`M|_U ⟶ N|_U`, bijectively and additively.

The isomorphism is kept as a variable: the concrete one this file needs is a composite of three
isomorphisms pulled back along a morphism, and leaving it abstract here is what keeps it out of
the terms the kernel has to unfold. -/
def moduleHomSectionsEquivOfIso (e : M ≅ M') (U : W.Opens) :
    moduleHomSections M' N U ≃+ moduleHomSections M N U where
  toFun θ := e.hom.over U ≫ θ
  invFun φ := e.inv.over U ≫ φ
  left_inv θ := Iso.inv_hom_id_map_assoc e _ θ
  right_inv φ := Iso.hom_inv_id_map_assoc e _ φ
  map_add' _ _ := Preadditive.comp_add _ _ _ _ _ _

/-- **`Stacks.Thickenings.moduleHomSectionsEquivOfIso` commutes with restriction of sections**:
precomposition with a fixed map is natural in the open. -/
theorem moduleHomSectionsEquivOfIso_restrict (e : M ≅ M') {U U' : W.Opens} (hU : U' ≤ U)
    (θ : moduleHomSections M' N U) :
    moduleHomSectionsEquivOfIso (N := N) e U' (moduleHomSections.restrict hU θ)
      = moduleHomSections.restrict hU (moduleHomSectionsEquivOfIso (N := N) e U θ) :=
  (Stacks.SheafOfModules.restrictOverHom_comp_left _ _ hU e.hom θ).symm

end HomSectionsTransport

/-- **The acting group of [Stacks Project, Tag 0CK2] is the acting group of
[Stacks Project, Tag 04FJ].** Over the part `i⁻¹V` of `X` cut out by an open `V` of `X'`,
precomposition with `Stacks.Thickenings.pullbackCotangentSheafIsoOfBase` identifies the sections
of `SheafHom_{𝒪_X}(a^*Ω_{Y/Z}, 𝒞_{X/X'})` — the sheaf the source acts by — with the sections of
`SheafHom_{𝒪_X}(a^*Ω_{Y/Z'}, 𝒞_{X/X'})`, which is `Stacks.Thickenings.deformationHomSections`
for the base `Z'` over which the lifts are taken. -/
def baseDeformationHomSectionsEquiv (sq : IsPullback j h h' k) (a : X ⟶ Y) (V : X'.Opens) :
    deformationHomSections i a h V ≃+ deformationHomSections i a (j ≫ h') V :=
  moduleHomSectionsEquivOfIso (N := conormalModules i)
    (pullbackCotangentSheafIsoOfBase sq a) (i ⁻¹ᵁ V)

omit [IsImmersion j] in
/-- **`Stacks.Thickenings.baseDeformationHomSectionsEquiv` commutes with restriction of
sections**: precomposition with a fixed map is natural in the open. -/
theorem baseDeformationHomSectionsEquiv_restrict (sq : IsPullback j h h' k) (a : X ⟶ Y)
    {V W : X'.Opens} (hWV : W ≤ V) (θ : deformationHomSections i a h V) :
    baseDeformationHomSectionsEquiv sq a W
        (moduleHomSections.restrict (i.preimage_mono hWV) θ)
      = moduleHomSections.restrict (i.preimage_mono hWV)
          (baseDeformationHomSectionsEquiv sq a V θ) :=
  moduleHomSectionsEquivOfIso_restrict (N := conormalModules i)
    (pullbackCotangentSheafIsoOfBase sq a) (i.preimage_mono hWV) θ

/-! ### The action -/

/-- **The action of a section of `SheafHom_{𝒪_X}(a^*Ω_{Y/Z}, 𝒞_{X/X'})` on an elementary
lift.** This is `Stacks.Thickenings.compatibleLiftsVAdd` — the action of
[Stacks Project, Tag 04FJ] — read through
`Stacks.Thickenings.baseDeformationHomSectionsEquiv` on the acting group and through
`Stacks.Thickenings.compatibleLiftsEquivLiftsOverBaseOfBase` on the lifts. -/
def liftsOverBaseVAddOfBase (hsq : i.ker ^ 2 = ⊥) (sq : IsPullback j h h' k)
    (ci : i ≫ g' = (a ≫ h) ≫ k)
    {A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i}
    (hA : IsBaseCompatibleConormalMap i j k h h' g' a sq.w ci A) (V : X'.Opens)
    (θ : deformationHomSections i a h V) (c : liftsOverBase i j g' h' a V) :
    liftsOverBase i j g' h' a V :=
  compatibleLiftsEquivLiftsOverBaseOfBase sq ci hA V
    (compatibleLiftsVAdd hsq g' h' a A V (baseDeformationHomSectionsEquiv sq a V θ)
      ((compatibleLiftsEquivLiftsOverBaseOfBase sq ci hA V).symm c))

/-- **The action clause of [Stacks Project, Tag 0CK2].** Let `k : Z ⟶ Z'` be an immersion, let
`i : X ⟶ X'` be a first order thickening and `j : Y ⟶ Y'` an immersion, both over `Z'` by
`g' : X' ⟶ Z'` and `h' : Y' ⟶ Z'`, assume `Y = Z ×_{Z'} Y'`, let `a : X ⟶ Y` and let `A` be a
conormal datum compatible with the base. Then the sheaf `Hom_{𝒪_X}(a^*Ω_{Y/Z}, 𝒞_{X/X'})` —
differentials relative to `Z`, as the source writes them — **acts** on the elementary rule
`Stacks.Thickenings.liftsOverBasePresheaf` of the remark: over every open `V` of `X'` the
additive group of its sections over `i⁻¹V` acts on the morphisms `V ⟶ Y'` over `Z'` restricting
to `a` on `i⁻¹V`, the action commutes with the restriction maps of that rule, and over an open
carrying a lift it is **simply transitive**.

No affineness is assumed, of `Z'`, `X'`, `Y'` or `V`, and no condition on conormal sheaves
appears in the conclusion: this is the action on the elementary rule itself, which is what the
remark asserts.

The action is `Stacks.Thickenings.liftsOverBaseVAddOfBase`: the unrestricted
[Stacks Project, Tag 04FJ] for the base `Z'`, carried over by the identification
`Ω_{Y/Z'} ≅ Ω_{Y/Z}` of `Stacks.Thickenings.pullbackCotangentSheafIsoOfBase` and by the
identification of the two notions of lift. -/
@[stacks 0CK2 "the action of Hom(a^*Ω_{Y/Z}, 𝒞_{X/X'}) on the elementary lifting rule, with \
the group laws, the compatibility with restriction, and simple transitivity over an open \
carrying a lift", sga "3 XII 9.4" "partial"]
theorem exists_simplyTransitive_addAction_liftsOverBaseOfBase (hsq : i.ker ^ 2 = ⊥)
    (sq : IsPullback j h h' k) (ci : i ≫ g' = (a ≫ h) ≫ k)
    {A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i}
    (hA : IsBaseCompatibleConormalMap i j k h h' g' a sq.w ci A) :
    ∃ act : ∀ V : X'.Opens, deformationHomSections i a h V →
        liftsOverBase i j g' h' a V → liftsOverBase i j g' h' a V,
      (∀ (V : X'.Opens) (c : liftsOverBase i j g' h' a V), act V 0 c = c) ∧
        (∀ (V : X'.Opens) (θ η : deformationHomSections i a h V)
          (c : liftsOverBase i j g' h' a V), act V (θ + η) c = act V θ (act V η c)) ∧
        (∀ (V V' : X'.Opens) (hV : V' ≤ V) (θ : deformationHomSections i a h V)
          (c : liftsOverBase i j g' h' a V),
          liftsOverBaseRestrict i j g' h' a hV (act V θ c)
            = act V' (moduleHomSections.restrict (i.preimage_mono hV) θ)
                (liftsOverBaseRestrict i j g' h' a hV c)) ∧
        ∀ (V : X'.Opens) (b₀ c₀ : liftsOverBase i j g' h' a V),
          ∃! θ : deformationHomSections i a h V, act V θ b₀ = c₀ := by
  -- The two group laws of the action of Tag 04FJ for the base `Z'`.
  have hzero : ∀ (V : X'.Opens) (d : compatibleLifts g' h' a A V),
      compatibleLiftsVAdd hsq g' h' a A V 0 d = d :=
    fun _ _ => Subtype.ext homSectionAct_zero
  have hadd : ∀ (V : X'.Opens) (θ η : deformationHomSections i a (j ≫ h') V)
      (d : compatibleLifts g' h' a A V),
      compatibleLiftsVAdd hsq g' h' a A V (θ + η) d
        = compatibleLiftsVAdd hsq g' h' a A V θ
            (compatibleLiftsVAdd hsq g' h' a A V η d) :=
    fun _ _ _ _ => Subtype.ext homSectionAct_add
  refine ⟨liftsOverBaseVAddOfBase hsq sq ci hA, fun V c => ?_, fun V θ η c => ?_,
    fun V V' hV θ c => ?_, fun V b₀ c₀ => ?_⟩
  · simp only [liftsOverBaseVAddOfBase, map_zero, hzero, Equiv.apply_symm_apply]
  · simp only [liftsOverBaseVAddOfBase, map_add, hadd, Equiv.symm_apply_apply]
  · simp only [liftsOverBaseVAddOfBase]
    rw [liftsOverBaseRestrict_compatibleLiftsEquivLiftsOverBaseOfBase sq ci hA hV,
      compatibleLiftsRestrict_compatibleLiftsVAdd,
      ← baseDeformationHomSectionsEquiv_restrict sq a hV,
      compatibleLiftsRestrict_compatibleLiftsEquivLiftsOverBaseOfBase_symm sq ci hA hV]
  · obtain ⟨φ, hφ, huniq⟩ :=
      existsUnique_compatibleLiftsVAdd_eq hsq g' h' a A V
        ((compatibleLiftsEquivLiftsOverBaseOfBase sq ci hA V).symm b₀)
        ((compatibleLiftsEquivLiftsOverBaseOfBase sq ci hA V).symm c₀)
    refine ⟨(baseDeformationHomSectionsEquiv sq a V).symm φ, ?_, fun η hη => ?_⟩
    · simp only [liftsOverBaseVAddOfBase, AddEquiv.apply_symm_apply, hφ,
        Equiv.apply_symm_apply]
    · refine (AddEquiv.eq_symm_apply _).mpr (huniq _ ?_)
      exact (compatibleLiftsEquivLiftsOverBaseOfBase sq ci hA V).injective
        (hη.trans ((compatibleLiftsEquivLiftsOverBaseOfBase sq ci hA V).apply_symm_apply c₀).symm)

end Stacks.Thickenings

end
