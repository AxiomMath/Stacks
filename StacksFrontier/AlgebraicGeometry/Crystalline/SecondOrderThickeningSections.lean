module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalConnectionSecondOrder
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalConnectionTensor

/-!
# The formulae of [Stacks, Remark 60.14.5, Tag 07J3] on sections over an object

Let `(U, T, δ)` be an object of the big crystalline category `CRIS(X/S)` of a global crystalline
situation, let `(U, T', δ')` be its first-order universal thickening of [Stacks, Tag 07J2] and
let `(U, T'', δ'')` be its second-order universal thickening of [Stacks, Tag 07J3], with
structure sheaf

`𝒪_{T''} = 𝒪_T ⊕ Ω_{T/S,δ} ⊕ Ω_{T/S,δ} ⊕ Ω²_{T/S,δ}`.

`StacksFrontier/AlgebraicGeometry/Crystalline/SecondOrderThickeningScheme.lean` has the six
morphisms `q₀, q₁, q₂ : T'' ⟶ T` and `q₀₁, q₀₂, q₁₂ : T'' ⟶ T'` of the site and the six
composition relations between them.  This module reads the three maps out of `𝒪_{T'}` on the
**sections over the objects**, on a section of the square-zero summand `Ω_{T/S,δ}` of `𝒪_{T'}`,
and records the two identities of the remark with which the integrability argument of
[Stacks, Tag 07J6] computes:

`q₀₁^* ω + q₁₂^* ω = q₀₂^* ω + (d ω)`  and  `q₁₂^* ω · q₀₁^* ω' = ω' ∧ ω`,

where on the right-hand sides a two-form is read as a section of `𝒪_{T''}` through the top
summand `Ω²_{T/S,δ}` and `d` is the degree-one divided power de Rham differential
`Crystalline.dpDeRham`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.crysSecondFormSections` — the sections of
  `Ω²_{T/S,δ}` over the whole ambient scheme of an object.
* `Crystalline.GlobalCrystallineSituation.crysWedgeSections` and
  `Crystalline.GlobalCrystallineSituation.crysDeRham` — the exterior product `Ω × Ω → Ω²` and the
  de Rham differential `d : Ω → Ω²` on those sections.
* `Crystalline.GlobalCrystallineSituation.secondOrderTopSection` — a two-form read as a section
  of `𝒪_{T''}`, through the top summand, and
  `Crystalline.GlobalCrystallineSituation.secondOrderLeftSection`,
  `Crystalline.GlobalCrystallineSituation.secondOrderRightSection` — a one-form read through
  either middle summand.

## Main results

* `Crystalline.GlobalCrystallineSituation.crysSheafRingMap_q₀₁_add_q₁₂_diffSection` — **the first
  formula of [Stacks, Tag 07J3]** on sections: `q₀₁^* ω + q₁₂^* ω = q₀₂^* ω + d ω`.
* `Crystalline.GlobalCrystallineSituation.crysSheafRingMap_q₁₂_mul_q₀₁_diffSection` — **the second
  formula of [Stacks, Tag 07J3]** on sections: `q₁₂^* ω · q₀₁^* ω' = ω' ∧ ω`.
* `Crystalline.GlobalCrystallineSituation.secondOrderTopSection_mul_crysSheafRingMap_q₀` — the top
  summand is an ideal on which `𝒪_T` acts through `q₀`: `η · q₀^* b = b η`.
* `Crystalline.GlobalCrystallineSituation.secondOrderLeftSection_mul_crysSheafRingMap_q₀` and
  its sibling for the second middle summand — each middle summand is a module over `𝒪_T` through
  `q₀` as well.
* `Crystalline.secondOrderExt_inl_add_inr_eq`, `Crystalline.secondOrderExt_inr_mul_inl`,
  `Crystalline.secondOrderExt_top_mul`, `Crystalline.secondOrderExt_inl_mul_incl` and
  `Crystalline.secondOrderExt_inr_mul_incl` — those identities in the abstract second-order
  extension `𝒪 ⊕ M₁ ⊕ M₂ ⊕ N` along a bilinear pairing, which is where they are proved.

## Implementation notes

The identities of the multiplication are proved in the **abstract** second-order extension of a
presheaf of
commutative rings along a bilinear pairing, where the module structures on the four summands are
the canonical ones, and are then transported to the crystalline setting by `exact`.  Proving them
in place is not an option: on a section ring of the crystalline site the sections of `Ω_{T/S,δ}`
carry their module structure through `inferInstanceAs`, and `rw` and `simp` do not see through
that — a rewrite with `Crystalline.secondOrderExtFst_mul` reports that it "did not find an
occurrence of the pattern", with a transparency note.

The maps of the site act on sections as the corresponding maps of presheaves of rings at the top
open, with no transport, because the opens of `T'` and of `T''` are the opens of `T`; the three
coordinate descriptions
`Crystalline.GlobalCrystallineSituation.crysSheafRingMap_q₀₁_diffSection` and its two siblings are
therefore definitional, apart from the vanishing `d 0 = 0` in the left coordinate of `q₁₂`.

## References

* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PresheafOfModules
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline

/-! ### The three identities in the abstract second-order extension -/

section SecondOrderExt

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  {M₁ M₂ N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
  {q : Stacks.BilinearMap M₁ M₂ N} {X : Cᵒᵖ}

/-- The sum of two sections of a second-order extension is their coordinatewise sum. -/
theorem secondOrderExtMk_add (a a' : ↑(R.obj X)) (m m' : ↑(M₁.obj X)) (n n' : ↑(M₂.obj X))
    (p p' : ↑(N.obj X)) :
    secondOrderExtMk (q := q) a m n p + secondOrderExtMk (q := q) a' m' n' p' =
      secondOrderExtMk (q := q) (a + a') (m + m') (n + n') (p + p') := rfl

/-- Reading a sum in the top summand of a second-order extension is the sum of the readings. -/
theorem secondOrderExtMk_top_add (p p' : ↑(N.obj X)) :
    secondOrderExtMk (q := q) 0 0 0 (p + p') =
      secondOrderExtMk (q := q) 0 0 0 p + secondOrderExtMk (q := q) 0 0 0 p' := by
  simp [secondOrderExtMk_add]

/-- **The first formula of [Stacks, Tag 07J3], in the abstract second-order extension.**  The
quadruples `(0, m, 0, 0)`, `(0, 0, n, p)` and `(0, m, n, 0)` — the values of `q₀₁`, `q₁₂` and
`q₀₂` on a section of the square-zero summand of `𝒪_{T'}` — satisfy
`(0, m, 0, 0) + (0, 0, n, p) = (0, m, n, 0) + (0, 0, 0, p)`. -/
theorem secondOrderExt_inl_add_inr_eq (m : ↑(M₁.obj X)) (n : ↑(M₂.obj X)) (p : ↑(N.obj X)) :
    secondOrderExtMk (q := q) 0 m 0 0 + secondOrderExtMk (q := q) 0 0 n p =
      secondOrderExtMk (q := q) 0 m n 0 + secondOrderExtMk (q := q) 0 0 0 p := by
  simp [secondOrderExtMk_add]

/-- **The second formula of [Stacks, Tag 07J3], in the abstract second-order extension.**  The
product of `(0, 0, n, p)` with `(0, m, 0, 0)` is `(0, 0, 0, q m n)`: both factors have vanishing
first coordinate, so only the symmetrised pairing term of the multiplication survives, and of its
two summands only `q (left of the second) (right of the first) = q m n` is nonzero. -/
theorem secondOrderExt_inr_mul_inl (m : ↑(M₁.obj X)) (n : ↑(M₂.obj X)) (p : ↑(N.obj X)) :
    secondOrderExtMk (q := q) 0 0 n p * secondOrderExtMk (q := q) 0 m 0 0 =
      secondOrderExtMk (q := q) 0 0 0 (q.app X m n) := by
  refine secondOrderExt_ext ?_ ?_ ?_ ?_ <;> simp

/-- **The first middle summand is a module over the ring through the inclusion of the first
coordinate**: `(0, m, 0, 0) · (a, 0, 0, 0) = (0, a m, 0, 0)`. -/
theorem secondOrderExt_inl_mul_incl (a : ↑(R.obj X)) (m : ↑(M₁.obj X)) :
    secondOrderExtMk (q := q) 0 m 0 0 * secondOrderExtMk (q := q) a 0 0 0 =
      secondOrderExtMk (q := q) 0 (a • m) 0 0 := by
  refine secondOrderExt_ext ?_ ?_ ?_ ?_ <;> simp

/-- **The second middle summand is a module over the ring through the inclusion of the first
coordinate**: `(0, 0, n, 0) · (a, 0, 0, 0) = (0, 0, a n, 0)`. -/
theorem secondOrderExt_inr_mul_incl (a : ↑(R.obj X)) (n : ↑(M₂.obj X)) :
    secondOrderExtMk (q := q) 0 0 n 0 * secondOrderExtMk (q := q) a 0 0 0 =
      secondOrderExtMk (q := q) 0 0 (a • n) 0 := by
  refine secondOrderExt_ext ?_ ?_ ?_ ?_ <;> simp

/-- Reading a sum in the first middle summand is the sum of the readings. -/
theorem secondOrderExtMk_inl_add (m m' : ↑(M₁.obj X)) :
    secondOrderExtMk (q := q) 0 (m + m') 0 0 =
      secondOrderExtMk (q := q) 0 m 0 0 + secondOrderExtMk (q := q) 0 m' 0 0 := by
  simp [secondOrderExtMk_add]

/-- Reading a sum in the second middle summand is the sum of the readings. -/
theorem secondOrderExtMk_inr_add (n n' : ↑(M₂.obj X)) :
    secondOrderExtMk (q := q) 0 0 (n + n') 0 =
      secondOrderExtMk (q := q) 0 0 n 0 + secondOrderExtMk (q := q) 0 0 n' 0 := by
  simp [secondOrderExtMk_add]

/-- **The top summand of a second-order extension is an ideal on which the ring acts through its
first coordinate**: `(0, 0, 0, p) · y = (0, 0, 0, (first coordinate of y) · p)`.  In particular a
section of the top summand annihilates every section with vanishing first coordinate. -/
theorem secondOrderExt_top_mul (p : ↑(N.obj X)) (y : SecondOrderExt q X) :
    secondOrderExtMk (q := q) 0 0 0 p * y =
      secondOrderExtMk (q := q) 0 0 0 (secondOrderExtFst y • p) := by
  refine secondOrderExt_ext ?_ ?_ ?_ ?_ <;> simp [bilinearApp_apply]

end SecondOrderExt

namespace GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

/-! ### Two-forms on sections -/

/-- **The sections of `Ω²_{T/S,δ}` over the whole ambient scheme of an object**, the top summand
of the structure sheaf of the second-order universal thickening of [Stacks, Tag 07J3]. -/
abbrev crysSecondFormSections (A : Thickening S) : Type u :=
  Γ(dpSecondExteriorPower A.thickening.target S.S.scheme A.toBase.hom, ⊤)

/-- The two-forms over an object, as a module over the sections of `𝒪_{X/S}` there: the two rings
of scalars are both `Γ(T, 𝒪_T)`. -/
instance moduleSecondFormSections (A : Thickening S) :
    Module (crysSheafRing S A) (crysSecondFormSections A) :=
  inferInstanceAs (Module Γ(A.thickening.target.scheme, ⊤)
    Γ(dpSecondExteriorPower A.thickening.target S.S.scheme A.toBase.hom, ⊤))

/-- **The exterior product of two divided power differentials**, on sections over an object: the
pairing `Ω_{T/S,δ} × Ω_{T/S,δ} → Ω²_{T/S,δ}` out of which the structure sheaf of the second-order
universal thickening of [Stacks, Tag 07J3] is built. -/
def crysWedgeSections (A : Thickening S) (ω ω' : crysDiffSections A) : crysSecondFormSections A :=
  (dpWedge A.thickening.target S.S.scheme A.toBase.hom).app (op ⊤) ω ω'

/-- The exterior product is additive in its first argument. -/
theorem crysWedgeSections_add_left (A : Thickening S) (ω ω' ω'' : crysDiffSections A) :
    crysWedgeSections A (ω + ω') ω'' = crysWedgeSections A ω ω'' + crysWedgeSections A ω' ω'' :=
  congrArg (fun g : (dpDifferentialsModules A.thickening.target S.S.scheme A.toBase.hom).obj
      (op ⊤) →+ (dpSecondExteriorModules A.thickening.target S.S.scheme A.toBase.hom).obj (op ⊤) ↦
    g ω'')
    (map_add ((dpWedge A.thickening.target S.S.scheme A.toBase.hom).app (op ⊤)) ω ω')

/-- The exterior product is additive in its second argument. -/
theorem crysWedgeSections_add_right (A : Thickening S) (ω ω' ω'' : crysDiffSections A) :
    crysWedgeSections A ω (ω' + ω'') = crysWedgeSections A ω ω' + crysWedgeSections A ω ω'' :=
  map_add ((dpWedge A.thickening.target S.S.scheme A.toBase.hom).app (op ⊤) ω) ω' ω''

/-- The exterior product is linear over `Γ(T, 𝒪_T)` in its first argument,
`(b ω) ∧ ω' = b (ω ∧ ω')`. -/
theorem crysWedgeSections_smul_left (A : Thickening S) (b : crysSheafRing S A)
    (ω ω' : crysDiffSections A) :
    crysWedgeSections A (b • ω) ω' = b • crysWedgeSections A ω ω' :=
  (dpWedge A.thickening.target S.S.scheme A.toBase.hom).map_smul_left (op ⊤) b ω ω'

/-- The exterior product is linear over `Γ(T, 𝒪_T)` in its second argument,
`ω ∧ (b ω') = b (ω ∧ ω')`. -/
theorem crysWedgeSections_smul_right (A : Thickening S) (b : crysSheafRing S A)
    (ω ω' : crysDiffSections A) :
    crysWedgeSections A ω (b • ω') = b • crysWedgeSections A ω ω' :=
  (dpWedge A.thickening.target S.S.scheme A.toBase.hom).map_smul_right (op ⊤) b ω ω'

/-- **The exterior product is antisymmetric**, `ω ∧ ω' + ω' ∧ ω = 0`. -/
theorem crysWedgeSections_add_swap (A : Thickening S) (ω ω' : crysDiffSections A) :
    crysWedgeSections A ω ω' + crysWedgeSections A ω' ω = 0 :=
  dpWedge_add_swap A.thickening.target S.S.scheme A.toBase.hom (op ⊤) ω ω'

/-- **The degree-one divided power de Rham differential `d : Ω_{T/S,δ} → Ω²_{T/S,δ}`**, on
sections over an object. -/
def crysDeRham (A : Thickening S) (ω : crysDiffSections A) : crysSecondFormSections A :=
  dpDeRham A.thickening.target S.S.scheme A.toBase.hom (op ⊤) ω

/-- The de Rham differential on sections is additive. -/
theorem crysDeRham_add (A : Thickening S) (ω ω' : crysDiffSections A) :
    crysDeRham A (ω + ω') = crysDeRham A ω + crysDeRham A ω' :=
  dpDeRham_add A.thickening.target S.S.scheme A.toBase.hom (op ⊤) ω ω'

/-- **The Leibniz rule for the de Rham differential on sections**,
`d (b ω) = b (d ω) + (d b) ∧ ω`. -/
theorem crysDeRham_smul (A : Thickening S) (b : crysSheafRing S A) (ω : crysDiffSections A) :
    crysDeRham A (b • ω) =
      b • crysDeRham A ω +
        crysWedgeSections A (sheafApp A.thickening.target S.S.scheme A.toBase.hom ⊤ b) ω :=
  dpDeRham_smul A.thickening.target S.S.scheme A.toBase.hom (op ⊤) b ω

/-! ### The top summand of `𝒪_{T''}` -/

/-- **A two-form read as a section of `𝒪_{T''}`**, through the top summand of
`𝒪_{T''} = 𝒪_T ⊕ Ω_{T/S,δ} ⊕ Ω_{T/S,δ} ⊕ Ω²_{T/S,δ}` of [Stacks, Tag 07J3], `η ↦ (0, 0, 0, η)`. -/
def secondOrderTopSection (A : Thickening S) (η : crysSecondFormSections A) :
    crysSheafRing S (secondOrderThickeningObject S A) :=
  secondOrderExtMk (q := dpWedge A.thickening.target S.S.scheme A.toBase.hom)
    (0 : crysSheafRing S A) 0 0 η

/-- The top component of `secondOrderTopSection A η` is `η`. -/
@[simp]
theorem secondOrderExtTop_secondOrderTopSection (A : Thickening S)
    (η : crysSecondFormSections A) :
    secondOrderExtTop (secondOrderTopSection A η) = η := rfl

/-- The inclusion of two-forms into the top summand of `𝒪_{T''}` is additive. -/
theorem secondOrderTopSection_add (A : Thickening S) (η η' : crysSecondFormSections A) :
    secondOrderTopSection A (η + η') =
      secondOrderTopSection A η + secondOrderTopSection A η' :=
  secondOrderExtMk_top_add η η'

/-- The inclusion of two-forms into the top summand of `𝒪_{T''}` sends `0` to `0`. -/
@[simp]
theorem secondOrderTopSection_zero (A : Thickening S) :
    secondOrderTopSection A (0 : crysSecondFormSections A) = 0 := rfl

/-- **The top summand is an ideal on which the sections of `𝒪_T` act through `q₀`**:
`η · q₀^* b = b η`. -/
theorem secondOrderTopSection_mul_crysSheafRingMap_q₀ (A : Thickening S)
    (η : crysSecondFormSections A) (b : crysSheafRing S A) :
    secondOrderTopSection A η * crysSheafRingMap (secondOrderThickeningSiteQ₀ S A) b =
      secondOrderTopSection A (b • η) :=
  secondOrderExt_top_mul η (crysSheafRingMap (secondOrderThickeningSiteQ₀ S A) b)

/-! ### The two middle summands of `𝒪_{T''}` -/

/-- **A one-form read as a section of `𝒪_{T''}` in the first middle summand**, `ω ↦ (0, ω, 0, 0)`.
This is `q₀₁` of the section `ω` of the square-zero summand of `𝒪_{T'}`. -/
def secondOrderLeftSection (A : Thickening S) (ω : crysDiffSections A) :
    crysSheafRing S (secondOrderThickeningObject S A) :=
  secondOrderExtMk (q := dpWedge A.thickening.target S.S.scheme A.toBase.hom)
    (0 : crysSheafRing S A) ω 0 0

/-- **A one-form read as a section of `𝒪_{T''}` in the second middle summand**,
`ω ↦ (0, 0, ω, 0)`. -/
def secondOrderRightSection (A : Thickening S) (ω : crysDiffSections A) :
    crysSheafRing S (secondOrderThickeningObject S A) :=
  secondOrderExtMk (q := dpWedge A.thickening.target S.S.scheme A.toBase.hom)
    (0 : crysSheafRing S A) 0 ω 0

/-- The inclusion of one-forms into the first middle summand of `𝒪_{T''}` is additive. -/
theorem secondOrderLeftSection_add (A : Thickening S) (ω ω' : crysDiffSections A) :
    secondOrderLeftSection A (ω + ω') =
      secondOrderLeftSection A ω + secondOrderLeftSection A ω' :=
  secondOrderExtMk_inl_add ω ω'

/-- The inclusion of one-forms into the second middle summand of `𝒪_{T''}` is additive. -/
theorem secondOrderRightSection_add (A : Thickening S) (ω ω' : crysDiffSections A) :
    secondOrderRightSection A (ω + ω') =
      secondOrderRightSection A ω + secondOrderRightSection A ω' :=
  secondOrderExtMk_inr_add ω ω'

/-- `q₀` carries a section of `𝒪_T` to `(b, 0, 0, 0)`. -/
theorem crysSheafRingMap_q₀_eq (A : Thickening S) (b : crysSheafRing S A) :
    crysSheafRingMap (secondOrderThickeningSiteQ₀ S A) b =
      secondOrderExtMk (q := dpWedge A.thickening.target S.S.scheme A.toBase.hom) b 0 0 0 := rfl

/-- The sections of `𝒪_T` act on the first middle summand of `𝒪_{T''}` through `q₀`:
`(0, ω, 0, 0) · q₀^* b = (0, b ω, 0, 0)`. -/
theorem secondOrderLeftSection_mul_crysSheafRingMap_q₀ (A : Thickening S)
    (ω : crysDiffSections A) (b : crysSheafRing S A) :
    secondOrderLeftSection A ω * crysSheafRingMap (secondOrderThickeningSiteQ₀ S A) b =
      secondOrderLeftSection A (b • ω) :=
  secondOrderExt_inl_mul_incl b ω

/-- The sections of `𝒪_T` act on the second middle summand of `𝒪_{T''}` through `q₀`:
`(0, 0, ω, 0) · q₀^* b = (0, 0, b ω, 0)`. -/
theorem secondOrderRightSection_mul_crysSheafRingMap_q₀ (A : Thickening S)
    (ω : crysDiffSections A) (b : crysSheafRing S A) :
    secondOrderRightSection A ω * crysSheafRingMap (secondOrderThickeningSiteQ₀ S A) b =
      secondOrderRightSection A (b • ω) :=
  secondOrderExt_inr_mul_incl b ω

/-! ### The three maps out of `𝒪_{T'}` on a differential -/

/-- `q₀₁` carries the section `ω` of the square-zero summand of `𝒪_{T'}` to `(0, ω, 0, 0)`. -/
theorem crysSheafRingMap_q₀₁_diffSection (A : Thickening S) (ω : crysDiffSections A) :
    crysSheafRingMap (secondOrderThickeningSiteQ₀₁ S A)
        (firstOrderThickeningDiffSection A ω) =
      secondOrderExtMk (q := dpWedge A.thickening.target S.S.scheme A.toBase.hom)
        (0 : crysSheafRing S A) ω 0 0 := rfl

/-- `q₀₂` carries the section `ω` of the square-zero summand of `𝒪_{T'}` to `(0, ω, ω, 0)`. -/
theorem crysSheafRingMap_q₀₂_diffSection (A : Thickening S) (ω : crysDiffSections A) :
    crysSheafRingMap (secondOrderThickeningSiteQ₀₂ S A)
        (firstOrderThickeningDiffSection A ω) =
      secondOrderExtMk (q := dpWedge A.thickening.target S.S.scheme A.toBase.hom)
        (0 : crysSheafRing S A) ω ω 0 := rfl

/-- `q₁₂` carries the section `ω` of the square-zero summand of `𝒪_{T'}` to `(0, 0, ω, d ω)`:
its left coordinate is `d` of the first coordinate of the argument, which is zero. -/
theorem crysSheafRingMap_q₁₂_diffSection (A : Thickening S) (ω : crysDiffSections A) :
    crysSheafRingMap (secondOrderThickeningSiteQ₁₂ S A)
        (firstOrderThickeningDiffSection A ω) =
      secondOrderExtMk (q := dpWedge A.thickening.target S.S.scheme A.toBase.hom)
        (0 : crysSheafRing S A) 0 ω (crysDeRham A ω) := by
  refine secondOrderExt_ext rfl ?_ rfl rfl
  exact map_zero (dpDerivationHom A.thickening.target S.S.scheme A.toBase.hom (op ⊤))

/-! ### The two formulae of [Stacks, Tag 07J3] -/

/-- **The first formula of [Stacks, Remark 60.14.5, Tag 07J3] on sections over an object.**  On a
section `ω` of the square-zero summand `Ω_{T/S,δ}` of `𝒪_{T'}` the three maps out of `𝒪_{T'}` of
the remark satisfy

`q₀₁^* ω + q₁₂^* ω = q₀₂^* ω + d ω`,

the two-form `d ω` being read in `𝒪_{T''}` through the top summand.  Indeed
`q₀₁ (0, ω) = (0, ω, 0, 0)`, `q₁₂ (0, ω) = (0, 0, ω, d ω)` and `q₀₂ (0, ω) = (0, ω, ω, 0)`.  This
is the identity `q₀₁^* ω + q₁₂^* ω - q₀₂^* ω = d ω` that the proof of [Stacks, Tag 07J6] reads off
the remark. -/
@[stacks 07J3 "the first formula of the remark on the sections over an object: on a section of \
the square-zero summand of 𝒪_{T'}, q₀₁ + q₁₂ = q₀₂ + d, the two-form d ω being read through the \
top summand Ω² of 𝒪_{T''}"]
theorem crysSheafRingMap_q₀₁_add_q₁₂_diffSection (A : Thickening S)
    (ω : crysDiffSections A) :
    crysSheafRingMap (secondOrderThickeningSiteQ₀₁ S A)
          (firstOrderThickeningDiffSection A ω) +
        crysSheafRingMap (secondOrderThickeningSiteQ₁₂ S A)
          (firstOrderThickeningDiffSection A ω) =
      crysSheafRingMap (secondOrderThickeningSiteQ₀₂ S A)
          (firstOrderThickeningDiffSection A ω) +
        secondOrderTopSection A (crysDeRham A ω) := by
  rw [crysSheafRingMap_q₀₁_diffSection, crysSheafRingMap_q₁₂_diffSection,
    crysSheafRingMap_q₀₂_diffSection]
  exact secondOrderExt_inl_add_inr_eq ω ω (crysDeRham A ω)

/-- **The second formula of [Stacks, Remark 60.14.5, Tag 07J3] on sections over an object.**  The
product in `𝒪_{T''}` of a section of the square-zero summand of `𝒪_{T'}` read through `q₁₂` with
one read through `q₀₁` is their exterior product, in the other order:

`q₁₂^* ω · q₀₁^* ω' = ω' ∧ ω`. -/
@[stacks 07J3 "the second formula of the remark on the sections over an object: the product in \
𝒪_{T''} of a differential read through q₁₂ with one read through q₀₁ is their exterior product \
in the other order, read through the top summand Ω²"]
theorem crysSheafRingMap_q₁₂_mul_q₀₁_diffSection (A : Thickening S)
    (ω ω' : crysDiffSections A) :
    crysSheafRingMap (secondOrderThickeningSiteQ₁₂ S A)
          (firstOrderThickeningDiffSection A ω) *
        crysSheafRingMap (secondOrderThickeningSiteQ₀₁ S A)
          (firstOrderThickeningDiffSection A ω') =
      secondOrderTopSection A (crysWedgeSections A ω' ω) := by
  rw [crysSheafRingMap_q₀₁_diffSection, crysSheafRingMap_q₁₂_diffSection]
  exact secondOrderExt_inr_mul_inl ω' ω (crysDeRham A ω)

end GlobalCrystallineSituation

end Crystalline

end

end
