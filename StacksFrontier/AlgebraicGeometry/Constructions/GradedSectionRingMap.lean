module

public import StacksFrontier.AlgebraicGeometry.Constructions.MorphismToProjRatios
public import StacksFrontier.AlgebraicGeometry.SectionRingGeometric.UnitScalar

/-!
# A graded ring map into the section ring is the datum of [Stacks, Tag 01N8]

Let `Y` be a scheme, `L` an invertible `𝒪_Y`-module and `A = ⨁_{n ≥ 0} 𝒜 n` a graded ring. The
existence half of [Stacks, Tag 01N8] takes as input a
`Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections`, the graded map
`A^{(d)} → Γ_*(Y, L)` written out degreewise. This file turns an honest ring map
`Φ : A → Γ_*(Y, L)` carrying `𝒜 n` into degree `n` into such a datum at Veronese weight `d = 1`,
and proves two facts about the degree-zero part of `Γ_*(Y, L)`: that it is the ring of functions
`Γ(Y, 𝒪_Y)`, and that multiplying a degree-one section by a degree-zero one is scaling it by the
corresponding function.

## Main definitions

* `Stacks.AlgebraicGeometry.GradedSectionRingMap.degreeZeroHom`: **the ring map
  `Γ(Y, 𝒪_Y) → Γ_*(Y, L)`** onto the degree-zero part.
* `Stacks.AlgebraicGeometry.GradedSectionRingMap.veroneseOfRingHom`: **the `VeroneseSections`
  datum at weight one attached to a graded ring map into the section ring.**

## Main results

* `Stacks.AlgebraicGeometry.GradedSectionRingMap.mul_degreeZero_one`: a degree-zero section times
  a degree-one section is their composite, so by
  `Stacks.SectionRingGeometric.globalSection_unitComp` it is a scalar multiple on sections.
* `Stacks.AlgebraicGeometry.GradedSectionRingMap.globalSection_degreeZeroHom_mul`: **the
  degree-zero part of `Γ_*(Y, L)` acts on the degree-one part by scaling sections**, for the
  graded product of [Stacks, Tag 01CV].
* `Stacks.AlgebraicGeometry.GradedSectionRingMap.degreeZeroHom_mul_of`: the same read on the
  homogeneous elements of the section ring.
* `Stacks.AlgebraicGeometry.GradedSectionRingMap.of_component_eq_self`: an element of the section
  ring vanishing outside one degree is the image of its component there.
* `Stacks.AlgebraicGeometry.GradedSectionRingMap.veroneseOfRingHom_toFun`: the degreewise value of
  that datum is the degree-`n` component of `Φ`, read on honest sections.

## Implementation notes

**Why the degree index needs no transport.** The `n`-th component of a `VeroneseSections 𝒜 1 L`
is a map out of `𝒜 (n * 1)`, and `n * 1` is not `n`. No transport appears below because the
component is computed from the *underlying element* of `A`, which forgets the index: the value is
the degree-`n` piece of `Φ x` for `x ∈ A`, and the hypothesis `x ∈ 𝒜 (n * 1)` is converted to
`x ∈ 𝒜 n` by `mul_one` where it is used, as a statement about membership rather than about types.

**The product with a degree-zero element is a composite.** `Stacks.GradedSections.mul s t` is
`t ≫ mulMap s m` with `mulMap s m` the right-whiskering of `s` by `m` copies of `L`; whiskering a
degree-zero element is not a composite, but the *other* order is, `mulMap t 0` being `t` itself.
So `mul_degreeZero_one` goes through the commutativity `Stacks.GradedSections.mul_comm'`, whose
transport `powCongr` is the identity here because `0 + 1` and `1 + 0` are both `1`.

## References

* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public noncomputable section

open CategoryTheory Category MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.GradedSections (powSections sectionRing mul mulMap powCongr)
open Stacks.SectionProduct (globalSection)
open Stacks.TensorPowers (natTensorPow)

open scoped DirectSum

universe u w

namespace Stacks.AlgebraicGeometry.GradedSectionRingMap

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

variable {Y : Scheme.{u}} (L : Y.Modules) [Stacks.Ample.IsInvertibleModule Y L]

/-! ### The degree-zero part -/

/-- **A degree-zero section times a degree-one section is their composite.** The degree-zero
tensor power is the monoidal unit, so a degree-zero section is an endomorphism of it. -/
theorem mul_degreeZero_one (a : powSections L 0) (s : powSections L 1) :
    mul a s = a ≫ s := by
  have h := Stacks.GradedSections.mul_comm' a s
  rw [show powCongr L (Nat.add_comm 0 1) = 𝟙 (natTensorPow L 1) from rfl, comp_id] at h
  rw [h, Stacks.GradedSections.mul_def, Stacks.GradedSections.mulMap_zero]

/-- The scalar of the endomorphism of the unit attached to a function `r` is `r`. -/
private theorem unitScalar_unitScalarEquiv_symm (r : Γ(Y, ⊤)) :
    Stacks.SectionRingGeometric.unitScalar Y
      ((Stacks.SectionRingGeometric.unitScalarEquiv Y).symm r) = r :=
  (Stacks.SectionRingGeometric.unitScalarEquiv Y).apply_symm_apply r

/-- **The ring map onto the degree-zero part of `Γ_*(Y, L)`.** The degree-zero tensor power is the
monoidal unit, so the degree-zero part is the ring of endomorphisms of the unit, which is
`Γ(Y, 𝒪_Y)` by `Stacks.SectionRingGeometric.unitScalarEquiv`. -/
def degreeZeroHom : Γ(Y, ⊤) →+* sectionRing L where
  toFun r := DirectSum.of (powSections L) 0 ((Stacks.SectionRingGeometric.unitScalarEquiv Y).symm r)
  map_zero' := by
    rw [show (Stacks.SectionRingGeometric.unitScalarEquiv Y).symm 0 = 0 from
      (Stacks.SectionRingGeometric.unitScalarAddEquiv Y).symm.map_zero]
    exact map_zero _
  map_one' := by
    rw [show (Stacks.SectionRingGeometric.unitScalarEquiv Y).symm 1 = 𝟙 (𝟙_ Y.Modules) from
      (Stacks.SectionRingGeometric.unitScalarEquiv Y).symm_apply_eq.mpr
        (Stacks.SectionRingGeometric.unitScalar_id Y).symm]
    exact DirectSum.of_zero_one (powSections L)
  map_add' r r' := by
    rw [show (Stacks.SectionRingGeometric.unitScalarEquiv Y).symm (r + r')
        = (Stacks.SectionRingGeometric.unitScalarEquiv Y).symm r
          + (Stacks.SectionRingGeometric.unitScalarEquiv Y).symm r' from
      (Stacks.SectionRingGeometric.unitScalarAddEquiv Y).symm.map_add r r']
    exact map_add _ _ _
  map_mul' r r' := by
    have hcomp : (Stacks.SectionRingGeometric.unitScalarEquiv Y).symm (r * r')
        = (Stacks.SectionRingGeometric.unitScalarEquiv Y).symm r'
          ≫ (Stacks.SectionRingGeometric.unitScalarEquiv Y).symm r := by
      refine (Stacks.SectionRingGeometric.unitScalarEquiv Y).symm_apply_eq.mpr ?_
      rw [Stacks.SectionRingGeometric.unitScalarEquiv_apply,
        Stacks.SectionRingGeometric.unitScalar_comp, unitScalar_unitScalarEquiv_symm,
        unitScalar_unitScalarEquiv_symm, mul_comm]
    rw [hcomp]
    exact (Stacks.SectionProduct.of_mul_of L 0 0 _ _).symm

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- The value of `degreeZeroHom` at a function `r` is the degree-zero element given by the
endomorphism of the monoidal unit corresponding to `r`. -/
@[simp] theorem degreeZeroHom_apply (r : Γ(Y, ⊤)) :
    degreeZeroHom L r
      = DirectSum.of (powSections L) 0
        ((Stacks.SectionRingGeometric.unitScalarEquiv Y).symm r) :=
  rfl

/-- The product of `degreeZeroHom L r` with a degree-one element is the composite of the
endomorphism of the unit attached to `r` with the section. -/
private theorem degreeZeroHom_mul_of_one (r : Γ(Y, ⊤)) (s : powSections L 1) :
    degreeZeroHom L r * DirectSum.of (powSections L) 1 s
      = DirectSum.of (powSections L) 1
        ((Stacks.SectionRingGeometric.unitScalarEquiv Y).symm r ≫ s) := by
  rw [degreeZeroHom_apply]
  exact (Stacks.SectionProduct.of_mul_of L 0 1 _ _).trans
    (congrArg (DirectSum.of (powSections L) 1) (mul_degreeZero_one L _ s))

/-- Composing a global section with the endomorphism of the unit of `r` scales it by `r`. -/
private theorem schemeGlobalSections_unitScalarEquiv_symm_comp (r : Γ(Y, ⊤)) {F : Y.Modules}
    (t : 𝟙_ Y.Modules ⟶ F) :
    Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y F
        ((Stacks.SectionRingGeometric.unitScalarEquiv Y).symm r ≫ t)
      = r • Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y F t := by
  rw [Stacks.SectionRingGeometric.globalSection_unitComp, unitScalar_unitScalarEquiv_symm]

/-- **The degree-zero part acts on the degree-one part by scaling global sections**, for the
graded product of [Stacks, Tag 01CV]. -/
theorem globalSection_degreeZeroHom_mul (r : Γ(Y, ⊤)) (s : powSections L 1) :
    globalSection Y (natTensorPow L 1)
        ((degreeZeroHom L r * DirectSum.of (powSections L) 1 s) 1)
      = r • globalSection Y (natTensorPow L 1) s := by
  rw [degreeZeroHom_mul_of_one, DirectSum.of_eq_same]
  exact schemeGlobalSections_unitScalarEquiv_symm_comp r s

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- **A scalar multiple of a degree-one section is the composite with the corresponding
endomorphism of the monoidal unit.** -/
theorem secOf_smul (r : Γ(Y, ⊤)) (x : Γ(natTensorPow L 1, ⊤)) :
    secOf L (r • x)
      = (Stacks.SectionRingGeometric.unitScalarEquiv Y).symm r ≫ secOf L x := by
  have h2 : Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y (natTensorPow L 1)
      ((Stacks.SectionRingGeometric.unitScalarEquiv Y).symm r ≫ secOf L x) = r • x := by
    rw [schemeGlobalSections_unitScalarEquiv_symm_comp]
    exact congrArg (r • ·) (globalSection_secOf L x)
  rw [← h2]
  exact secOf_globalSection L _

/-- **Multiplying a degree-one section by a function is scaling it**: the product of
`degreeZeroHom L r` with the degree-one element attached to a section `x` is the degree-one
element attached to `r • x`. -/
theorem degreeZeroHom_mul_of (r : Γ(Y, ⊤)) (x : Γ(natTensorPow L 1, ⊤)) :
    degreeZeroHom L r * DirectSum.of (powSections L) 1 (secOf L x)
      = DirectSum.of (powSections L) 1 (secOf L (r • x)) := by
  rw [secOf_smul, degreeZeroHom_mul_of_one]

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- **An element of the section ring vanishing outside degree `n` is the image of its degree-`n`
component.** -/
theorem of_component_eq_self {n : ℕ} (z : sectionRing L) (hz : ∀ m, m ≠ n → z m = 0) :
    DirectSum.of (powSections L) n (z n) = z := by
  refine DFinsupp.ext fun m => ?_
  obtain rfl | h := eq_or_ne m n
  · exact DirectSum.of_eq_same _ _
  · rw [DirectSum.of_eq_of_ne _ _ _ h, hz m h]

/-! ### The `VeroneseSections` datum of a graded ring map -/

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **The `VeroneseSections` datum at weight one attached to a graded ring map into the section
ring.** Its degree-`n` component is the degree-`n` piece of `Φ`, read on honest sections through
`Stacks.SectionProduct.globalSection`. -/
def veroneseOfRingHom (Φ : A →+* sectionRing L)
    (hΦ : ∀ (n : ℕ) (x : A), x ∈ 𝒜 n → DirectSum.of (powSections L) n ((Φ x) n) = Φ x) :
    VeroneseSections 𝒜 1 L where
  toFun n :=
    AddMonoidHom.mk' (fun x : 𝒜 (n * 1) => globalSection Y (natTensorPow L n) ((Φ (x : A)) n))
      fun x y => by
        rw [show ((x + y : 𝒜 (n * 1)) : A) = (x : A) + (y : A) from rfl, map_add,
          DirectSum.add_apply]
        exact map_add (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y _) _ _
  map_mul n m a b ab hab := by
    have ha : (a : A) ∈ 𝒜 n := by simpa using a.2
    have hb : (b : A) ∈ 𝒜 m := by simpa using b.2
    have h1 : Φ (ab : A) = DirectSum.of (powSections L) (n + m)
        (mul ((Φ (a : A)) n) ((Φ (b : A)) m)) := by
      rw [← Stacks.SectionProduct.of_mul_of L n m, hΦ n _ ha, hΦ m _ hb, hab, map_mul]
    change globalSection Y (natTensorPow L (n + m)) ((Φ (ab : A)) (n + m))
        = mulSections L (globalSection Y (natTensorPow L n) ((Φ (a : A)) n))
            (globalSection Y (natTensorPow L m) ((Φ (b : A)) m))
    rw [h1, DirectSum.of_eq_same, mulSections_globalSection]

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- The degree-`n` component of `veroneseOfRingHom` sends `x` to the global section underlying
the degree-`n` piece of `Φ x`. -/
@[simp] theorem veroneseOfRingHom_toFun (Φ : A →+* sectionRing L)
    (hΦ : ∀ (n : ℕ) (x : A), x ∈ 𝒜 n → DirectSum.of (powSections L) n ((Φ x) n) = Φ x)
    (n : ℕ) (x : 𝒜 (n * 1)) :
    (veroneseOfRingHom L 𝒜 Φ hΦ).toFun n x
      = globalSection Y (natTensorPow L n) ((Φ (x : A)) n) :=
  rfl

end Stacks.AlgebraicGeometry.GradedSectionRingMap

end
