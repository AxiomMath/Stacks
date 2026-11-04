module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseAlgebras
public import StacksFrontier.AlgebraicGeometry.Crystalline.UniversalThickenings

/-!
# The second-order universal thickening of a divided power scheme

Let `(T, J, δ)` be a divided power scheme over a scheme `Y`, let `Ω_{T/Y,δ}` be its sheaf of
divided power differentials with universal divided power derivation `d_{T/Y,δ}`, and let
`Ω²_{T/Y,δ}` be the second exterior power of `Ω_{T/Y,δ}`.  The structure sheaf of the
*second-order universal thickening* `T''` of `T` is

`𝒪_{T''} = 𝒪_T ⊕ Ω_{T/Y,δ} ⊕ Ω_{T/Y,δ} ⊕ Ω²_{T/Y,δ}`,

a sheaf of commutative rings with multiplication

`(f, ω₁, ω₂, η) (f', ω₁', ω₂', η')`
` = (f f', f ω₁' + f' ω₁, f ω₂' + f' ω₂, f η' + f' η + ω₁ ∧ ω₂' + ω₁' ∧ ω₂)`,

in which the inverse image `J''` of the divided power ideal `J` of `T` carries the divided power
structure

`δ''_n (f, ω₁, ω₂, η)`
` = (δ_n f, δ_{n-1} f · ω₁, δ_{n-1} f · ω₂, δ_{n-1} f · η + δ_{n-2} f · ω₁ ∧ ω₂)`.

Three maps of sheaves of rings `q₀, q₁, q₂ : 𝒪_T → 𝒪_{T''}` are given by `f ↦ (f, 0, 0, 0)`,
`f ↦ (f, d f, 0, 0)` and `f ↦ (f, d f, d f, 0)`, and two of the three maps
`𝒪_{T'} → 𝒪_{T''}` out of the first-order thickening `T'` of
`StacksFrontier.AlgebraicGeometry.Crystalline.UniversalThickenings` are given by
`q₀₁ (f, ω) = (f, ω, 0, 0)` and `q₀₂ (f, ω) = (f, ω, ω, 0)`.  All of them are compatible with the
divided power structures, and they satisfy

`q₀ = q₀₁ ∘ p₀`, `q₁ = q₀₁ ∘ p₁`, `q₀ = q₀₂ ∘ p₀`, `q₂ = q₀₂ ∘ p₁`.

The third map `𝒪_{T'} → 𝒪_{T''}` of the source, `q₁₂ (f, ω) = (f, d f, ω, d ω)`, needs the
degree-one divided power de Rham differential `d : Ω_{T/Y,δ} → Ω²_{T/Y,δ}` of the *sheaf*; it and
its two composition relations `q₁ = q₁₂ ∘ p₀` and `q₂ = q₁₂ ∘ p₁` are in
`StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickeningDeRham`, which constructs that
differential and uses the general homomorphism criterion
`Crystalline.secondOrderExtLiftTopPresheafHom` and the general divided power criterion
`Crystalline.isDPMorphism_secondOrderExt_of_graph_top` below.

For an object `(U, T, δ)` of the big crystalline category `CRIS(X/S)` of a global crystalline
situation, taking `Y` to be the divided power base and `f` the structure morphism of `T` over it
gives the thickening `T''` of [Stacks, Tag 07J3], since `Ω_{T/S,δ}` is the restriction of
`Ω_{X/S}` to `T` by [Stacks, Tag 07IZ].

## Main definitions

* `Crystalline.SecondOrderExt` — the sections of a second-order extension
  `𝒪 ⊕ M₁ ⊕ M₂ ⊕ N` of a presheaf of commutative rings along a bilinear pairing
  `q : M₁ × M₂ → N`, with its commutative ring structure.
* `Crystalline.secondOrderExtPresheaf` — the second-order extension as a presheaf of commutative
  rings.
* `Crystalline.secondOrderExtIdeal` and `Crystalline.secondOrderExtDividedPowers` — the inverse
  image of a divided power ideal and the divided power structure on it.
* `Crystalline.dpSecondExteriorPower` — `Ω²_{T/Y,δ}`, the second exterior power of the sheaf of
  divided power differentials, and `Crystalline.dpWedge` the exterior product
  `Ω_{T/Y,δ} × Ω_{T/Y,δ} → Ω²_{T/Y,δ}`.
* `Crystalline.secondOrderThickeningPresheaf` and `Crystalline.secondOrderThickeningSheaf` — the
  structure sheaf `𝒪_{T''}` as a presheaf of commutative rings and as a sheaf, with
  `secondOrderThickeningIdeal` and `secondOrderThickeningDividedPowers` its ideal and divided
  powers.
* `Crystalline.secondOrderThickeningQ₀`, `Q₁`, `Q₂`, `Q₀₁` and `Q₀₂` — the maps to `𝒪_{T''}`.
* `Crystalline.secondOrderExtLiftTop` and
  `Crystalline.secondOrderExtLiftTopPresheafHom` — a homomorphism into a second-order extension
  with a prescribed top coordinate.

## Main results

* `Crystalline.secondOrderExtDividedPowers_dpow_add_two` — the displayed formula for `δ''`.
* `Crystalline.isSheaf_secondOrderExtPresheaf` — a second-order extension of a sheaf of rings by
  three sheaves of modules is a sheaf.
* `Crystalline.isDPMorphism_secondOrderExt_of_graph_top` and
  `Crystalline.isDPMorphism_secondOrderExt_of_graph` — the criteria for a homomorphism into a
  second-order extension to be a divided power morphism.
* `Crystalline.secondOrderThickening_restriction_isDPMorphism` — `δ''` is compatible with every
  restriction map, so `(𝒪_{T''}, J'', δ'')` is a presheaf of divided power rings.
* `Crystalline.secondOrderThickeningQ₀_isDPMorphism` and its four companions — the five maps are
  compatible with the divided powers.
* `Crystalline.secondOrderThickeningQ₀_eq`, `Q₁_eq`, `Q₂_eq`, `Q₂_eq_Q₀₂_comp_P₁` — the
  composition relations with the two maps `p₀, p₁ : 𝒪_T → 𝒪_{T'}` of the first-order thickening.

## Implementation notes

**The three module coordinates are kept separate.**  The algebraic input is Tag 07HI,
`Crystalline.exists_dividedPowers_secondOrderExtension`, which takes a second-order extension
`A ⊕ M ⊕ N` along a bilinear `Q : M × M → N`.  It is applied with `M` the *type-level* product
`M₁(X) × M₂(X)` of the two middle coordinates and `Q` the pairing
`Q (ω₁, ω₂) (ω₁', ω₂') = q ω₁ ω₂'`, whose symmetrisation `Q m m' + Q m' m` is the correction
`ω₁ ∧ ω₂' + ω₁' ∧ ω₂` of the displayed multiplication and whose diagonal value
`Q m m = q ω₁ ω₂` is the correction `ω₁ ∧ ω₂` of the displayed divided powers.  Keeping `M₁`
and `M₂` separate *as presheaves* avoids having to form their product as a presheaf of modules;
the product is only ever needed on sections, where it is the product of modules.

**Degrees zero and one of `δ''` are not the displayed formula.**  Tag 07HI supplies the formula
in degrees at least two, and that is where it is recorded here: in degree zero a divided power
structure is `1`, and in degree one it is the identity, whereas the displayed formula read at
`n = 1` would add the spurious term `δ_{-1} f · ω₁ ∧ ω₂` under truncated subtraction.  The
degree is accordingly written `k + 2`, so that the two shifts of the source stay literal.

**`Ω²` is the sheafification of the sectionwise second exterior power.**  By Tag 01CG the
second exterior power of a sheaf of modules is the sheafification of the presheaf of sectionwise
second exterior powers, and that is how `Crystalline.dpSecondExteriorPower` is built — out of
`PresheafOfModules.extPow 2` and the sheafification used for `Ω_{T/Y,δ}` itself.  The exterior
product `Crystalline.dpWedge` is the sectionwise exterior product followed by the unit of that
sheafification, exactly as the universal divided power derivation on sections,
`Crystalline.sheafApp`, is the presheaf-level derivation followed by the unit of the
sheafification defining `Ω_{T/Y,δ}`.

**What lives elsewhere.**  The third map `q₁₂ (f, ω) = (f, d f, ω, d ω)` of the source needs the
degree-one de Rham differential `d : Ω_{T/Y,δ} → Ω²_{T/Y,δ}`, read on the *sheaf* `Ω_{T/Y,δ}`;
that differential and the map are in the downstream module
`StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickeningDeRham`, which this module does
not import, so nothing below mentions them.

The realization of the extension as a *scheme*, and the object `(U, T'', δ'')` of `CRIS(X/S)`,
are likewise elsewhere: `Crystalline.secondOrderThickeningScheme` and
`Crystalline.secondOrderThickeningObject` of
`StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickeningScheme`, which carries the
`@[stacks 07J3]` registration for that clause.  Everything below is stated for the sheaf of rings
`𝒪_{T''}` and its ideal.  The two-step route that module takes is forced: unlike the
first-order case — which
`StacksFrontier.AlgebraicGeometry.Crystalline.UniversalThickeningScheme` now realizes, the sheaf of
divided power differentials being quasi-coherent by Tag 07IY — the obstruction for `T''` is that
`T → T''` is a thickening of order *two*: the ideal of `𝒪_{T''} → 𝒪_T` has vanishing cube but
not vanishing square, so `Stacks.Thickenings.squareZeroExtension_realization` does not apply to
it.  `StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickeningOrder` proves both halves
of that and sets up the two-step route that would realize `T''` over `T'`.

## References

* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07HI](https://stacks.math.columbia.edu/tag/07HI)
* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PresheafOfModules
open scoped AlgebraicGeometry

universe u

namespace Crystalline

/-! ### The second-order extension of a presheaf of commutative rings -/

section SecondOrderExt

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  {M₁ M₂ N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}

/-- **The sections of a second-order extension.**  For a presheaf of commutative rings `R`, three
presheaves of `R`-modules `M₁`, `M₂`, `N` and a bilinear pairing `q : M₁ × M₂ → N`, this is the
type `R(X) ⊕ M₁(X) ⊕ M₂(X) ⊕ N(X)` of sections over `X`, carrying the second-order ring structure
rather than the componentwise product one. -/
public structure SecondOrderExt (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ) where
  /-- The four coordinates of a section. -/
  coords : ↑(R.obj X) × ((↑(M₁.obj X) × ↑(M₂.obj X)) × ↑(N.obj X))

variable {q : Stacks.BilinearMap M₁ M₂ N} {X : Cᵒᵖ}

/-- A section of a second-order extension is its quadruple of coordinates. -/
public def SecondOrderExt.equiv (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ) :
    SecondOrderExt q X ≃
      ↑(R.obj X) × ((↑(M₁.obj X) × ↑(M₂.obj X)) × ↑(N.obj X)) where
  toFun := SecondOrderExt.coords
  invFun := SecondOrderExt.mk
  left_inv x := by cases x; rfl
  right_inv _ := rfl

/-- The additive group structure of a second-order extension, transported from its quadruple of
coordinates. -/
public instance : AddCommGroup (SecondOrderExt q X) :=
  Equiv.addCommGroup (SecondOrderExt.equiv q X)

/-- A second-order extension is additively the product of its four coordinates. -/
public def SecondOrderExt.addEquiv (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ) :
    SecondOrderExt q X ≃+
      ↑(R.obj X) × ((↑(M₁.obj X) × ↑(M₂.obj X)) × ↑(N.obj X)) where
  toEquiv := SecondOrderExt.equiv q X
  map_add' _ _ := rfl

/-- The section of a second-order extension with the given four coordinates. -/
public def secondOrderExtMk (a : ↑(R.obj X)) (m₁ : ↑(M₁.obj X)) (m₂ : ↑(M₂.obj X))
    (n : ↑(N.obj X)) : SecondOrderExt q X := ⟨(a, ((m₁, m₂), n))⟩

/-- The first coordinate of a section of a second-order extension. -/
public def secondOrderExtFst (x : SecondOrderExt q X) : ↑(R.obj X) := x.coords.1

/-- The first middle coordinate of a section of a second-order extension. -/
public def secondOrderExtLeft (x : SecondOrderExt q X) : ↑(M₁.obj X) := x.coords.2.1.1

/-- The second middle coordinate of a section of a second-order extension. -/
public def secondOrderExtRight (x : SecondOrderExt q X) : ↑(M₂.obj X) := x.coords.2.1.2

/-- The top coordinate of a section of a second-order extension. -/
public def secondOrderExtTop (x : SecondOrderExt q X) : ↑(N.obj X) := x.coords.2.2

/-- The first coordinate of `secondOrderExtMk a m₁ m₂ n` is `a`. -/
@[simp] public theorem secondOrderExtFst_mk (a : ↑(R.obj X)) (m₁ : ↑(M₁.obj X))
    (m₂ : ↑(M₂.obj X)) (n : ↑(N.obj X)) :
    secondOrderExtFst (q := q) (secondOrderExtMk a m₁ m₂ n) = a := rfl

/-- The first middle coordinate of `secondOrderExtMk a m₁ m₂ n` is `m₁`. -/
@[simp] public theorem secondOrderExtLeft_mk (a : ↑(R.obj X)) (m₁ : ↑(M₁.obj X))
    (m₂ : ↑(M₂.obj X)) (n : ↑(N.obj X)) :
    secondOrderExtLeft (q := q) (secondOrderExtMk a m₁ m₂ n) = m₁ := rfl

/-- The second middle coordinate of `secondOrderExtMk a m₁ m₂ n` is `m₂`. -/
@[simp] public theorem secondOrderExtRight_mk (a : ↑(R.obj X)) (m₁ : ↑(M₁.obj X))
    (m₂ : ↑(M₂.obj X)) (n : ↑(N.obj X)) :
    secondOrderExtRight (q := q) (secondOrderExtMk a m₁ m₂ n) = m₂ := rfl

/-- The top coordinate of `secondOrderExtMk a m₁ m₂ n` is `n`. -/
@[simp] public theorem secondOrderExtTop_mk (a : ↑(R.obj X)) (m₁ : ↑(M₁.obj X))
    (m₂ : ↑(M₂.obj X)) (n : ↑(N.obj X)) :
    secondOrderExtTop (q := q) (secondOrderExtMk a m₁ m₂ n) = n := rfl

/-- Two sections of a second-order extension with the same four coordinates are equal. -/
public theorem secondOrderExt_ext {x y : SecondOrderExt q X}
    (h₀ : secondOrderExtFst x = secondOrderExtFst y)
    (h₁ : secondOrderExtLeft x = secondOrderExtLeft y)
    (h₂ : secondOrderExtRight x = secondOrderExtRight y)
    (h₃ : secondOrderExtTop x = secondOrderExtTop y) : x = y := by
  refine (SecondOrderExt.equiv q X).injective ?_
  exact Prod.ext h₀ (Prod.ext (Prod.ext h₁ h₂) h₃)

/-- The bilinear pairing of a bilinear map of presheaves of modules, on sections. -/
public def bilinearApp (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ) :
    ↑(M₁.obj X) →ₗ[↑(R.obj X)] ↑(M₂.obj X) →ₗ[↑(R.obj X)] ↑(N.obj X) :=
  LinearMap.mk₂ _ (fun m₁ m₂ => q.app X m₁ m₂)
    (fun a b n => (congrArg (fun f : ↑(M₂.obj X) →+ ↑(N.obj X) => f n)
      (map_add (q.app X) a b)).trans (AddMonoidHom.add_apply _ _ n))
    (fun c m n => q.map_smul_left X c m n)
    (fun m n n' => map_add (q.app X m) n n')
    (fun c m n => q.map_smul_right X c m n)

/-- `bilinearApp q X` evaluates the bilinear map `q` on sections over `X`. -/
@[simp] public theorem bilinearApp_apply (m₁ : ↑(M₁.obj X)) (m₂ : ↑(M₂.obj X)) :
    bilinearApp q X m₁ m₂ = q.app X m₁ m₂ := rfl

/-- `bilinearApp q X` is additive in its first argument. -/
@[simp] public theorem bilinearApp_add_left (m₁ m₁' : ↑(M₁.obj X)) (m₂ : ↑(M₂.obj X)) :
    bilinearApp q X (m₁ + m₁') m₂ = bilinearApp q X m₁ m₂ + bilinearApp q X m₁' m₂ :=
  (congrArg (fun f : ↑(M₂.obj X) →ₗ[↑(R.obj X)] ↑(N.obj X) => f m₂)
    (map_add (bilinearApp q X) m₁ m₁')).trans (LinearMap.add_apply _ _ m₂)

/-- `bilinearApp q X` is linear in its first argument. -/
@[simp] public theorem bilinearApp_smul_left (a : ↑(R.obj X)) (m₁ : ↑(M₁.obj X))
    (m₂ : ↑(M₂.obj X)) : bilinearApp q X (a • m₁) m₂ = a • bilinearApp q X m₁ m₂ :=
  (congrArg (fun f : ↑(M₂.obj X) →ₗ[↑(R.obj X)] ↑(N.obj X) => f m₂)
    (map_smul (bilinearApp q X) a m₁)).trans (LinearMap.smul_apply _ _ m₂)

/-- `bilinearApp q X` vanishes when its first argument is zero. -/
@[simp] public theorem bilinearApp_zero_left (m₂ : ↑(M₂.obj X)) :
    bilinearApp q X 0 m₂ = 0 :=
  (congrArg (fun f : ↑(M₂.obj X) →ₗ[↑(R.obj X)] ↑(N.obj X) => f m₂)
    (map_zero (bilinearApp q X))).trans (LinearMap.zero_apply m₂)

/-- `bilinearApp q X` is additive in its second argument. -/
@[simp] public theorem bilinearApp_add_right (m₁ : ↑(M₁.obj X)) (m₂ m₂' : ↑(M₂.obj X)) :
    bilinearApp q X m₁ (m₂ + m₂') = bilinearApp q X m₁ m₂ + bilinearApp q X m₁ m₂' :=
  map_add (bilinearApp q X m₁) m₂ m₂'

/-- `bilinearApp q X` is linear in its second argument. -/
@[simp] public theorem bilinearApp_smul_right (a : ↑(R.obj X)) (m₁ : ↑(M₁.obj X))
    (m₂ : ↑(M₂.obj X)) : bilinearApp q X m₁ (a • m₂) = a • bilinearApp q X m₁ m₂ :=
  map_smul (bilinearApp q X m₁) a m₂

/-- `bilinearApp q X` vanishes when its second argument is zero. -/
@[simp] public theorem bilinearApp_zero_right (m₁ : ↑(M₁.obj X)) :
    bilinearApp q X m₁ 0 = 0 :=
  map_zero (bilinearApp q X m₁)

/-- **The pairing of the two middle coordinates.**  It sends a pair of quadruples to the pairing
of the first middle coordinate of the one with the second middle coordinate of the other; its
symmetrisation is the correction term of the second-order multiplication and its diagonal value
is the correction term of the second-order divided powers. -/
public def secondOrderPairing (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ) :
    (↑(M₁.obj X) × ↑(M₂.obj X)) →ₗ[↑(R.obj X)]
      (↑(M₁.obj X) × ↑(M₂.obj X)) →ₗ[↑(R.obj X)] ↑(N.obj X) :=
  LinearMap.compl₂ (bilinearApp q X ∘ₗ LinearMap.fst _ _ _) (LinearMap.snd _ _ _)

/-- The middle-coordinate pairing evaluates `q` on the first entry of the one pair and the second
entry of the other. -/
@[simp] public theorem secondOrderPairing_apply (m m' : ↑(M₁.obj X) × ↑(M₂.obj X)) :
    secondOrderPairing q X m m' = q.app X m.1 m'.2 := rfl

/-- The coordinates of the second-order product of two quadruples. -/
public def secondOrderMulCoords (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ)
    (x y : ↑(R.obj X) × ((↑(M₁.obj X) × ↑(M₂.obj X)) × ↑(N.obj X))) :
    ↑(R.obj X) × ((↑(M₁.obj X) × ↑(M₂.obj X)) × ↑(N.obj X)) :=
  (x.1 * y.1,
    (x.1 • y.2.1 + y.1 • x.2.1,
      x.1 • y.2.2 + y.1 • x.2.2 + secondOrderPairing q X x.2.1 y.2.1 +
        secondOrderPairing q X y.2.1 x.2.1))

/-- The second-order multiplication of a second-order extension, given in coordinates by
`Crystalline.secondOrderMulCoords`. -/
public instance : Mul (SecondOrderExt q X) :=
  ⟨fun x y => ⟨secondOrderMulCoords q X x.coords y.coords⟩⟩

/-- The unit of a second-order extension, with first coordinate `1` and the other three zero. -/
public instance : One (SecondOrderExt q X) := ⟨⟨(1, (0, 0))⟩⟩

/-- The first coordinate of a product is the product of the first coordinates. -/
@[simp] public theorem secondOrderExtFst_mul (x y : SecondOrderExt q X) :
    secondOrderExtFst (x * y) = secondOrderExtFst x * secondOrderExtFst y := rfl

/-- The first middle coordinate of a product, by the Leibniz rule. -/
@[simp] public theorem secondOrderExtLeft_mul (x y : SecondOrderExt q X) :
    secondOrderExtLeft (x * y) =
      secondOrderExtFst x • secondOrderExtLeft y + secondOrderExtFst y • secondOrderExtLeft x :=
  rfl

/-- The second middle coordinate of a product, by the Leibniz rule. -/
@[simp] public theorem secondOrderExtRight_mul (x y : SecondOrderExt q X) :
    secondOrderExtRight (x * y) =
      secondOrderExtFst x • secondOrderExtRight y + secondOrderExtFst y • secondOrderExtRight x :=
  rfl

/-- **The top coordinate of a second-order product**, the Leibniz term corrected by the
symmetrised pairing of the two middle coordinates. -/
@[simp] public theorem secondOrderExtTop_mul (x y : SecondOrderExt q X) :
    secondOrderExtTop (x * y) =
      secondOrderExtFst x • secondOrderExtTop y + secondOrderExtFst y • secondOrderExtTop x +
        bilinearApp q X (secondOrderExtLeft x) (secondOrderExtRight y) +
        bilinearApp q X (secondOrderExtLeft y) (secondOrderExtRight x) := rfl

/-- The first coordinate of a sum is the sum of the first coordinates. -/
@[simp] public theorem secondOrderExtFst_add (x y : SecondOrderExt q X) :
    secondOrderExtFst (x + y) = secondOrderExtFst x + secondOrderExtFst y := rfl

/-- The first middle coordinate of a sum is the sum of the first middle coordinates. -/
@[simp] public theorem secondOrderExtLeft_add (x y : SecondOrderExt q X) :
    secondOrderExtLeft (x + y) = secondOrderExtLeft x + secondOrderExtLeft y := rfl

/-- The second middle coordinate of a sum is the sum of the second middle coordinates. -/
@[simp] public theorem secondOrderExtRight_add (x y : SecondOrderExt q X) :
    secondOrderExtRight (x + y) = secondOrderExtRight x + secondOrderExtRight y := rfl

/-- The top coordinate of a sum is the sum of the top coordinates. -/
@[simp] public theorem secondOrderExtTop_add (x y : SecondOrderExt q X) :
    secondOrderExtTop (x + y) = secondOrderExtTop x + secondOrderExtTop y := rfl

/-- The first coordinate of `0` is `0`. -/
@[simp] public theorem secondOrderExtFst_zero :
    secondOrderExtFst (0 : SecondOrderExt q X) = 0 := rfl

/-- The first middle coordinate of `0` is `0`. -/
@[simp] public theorem secondOrderExtLeft_zero :
    secondOrderExtLeft (0 : SecondOrderExt q X) = 0 := rfl

/-- The second middle coordinate of `0` is `0`. -/
@[simp] public theorem secondOrderExtRight_zero :
    secondOrderExtRight (0 : SecondOrderExt q X) = 0 := rfl

/-- The top coordinate of `0` is `0`. -/
@[simp] public theorem secondOrderExtTop_zero :
    secondOrderExtTop (0 : SecondOrderExt q X) = 0 := rfl

/-- The first coordinate of `1` is `1`. -/
@[simp] public theorem secondOrderExtFst_one :
    secondOrderExtFst (1 : SecondOrderExt q X) = 1 := rfl

/-- The first middle coordinate of `1` is `0`. -/
@[simp] public theorem secondOrderExtLeft_one :
    secondOrderExtLeft (1 : SecondOrderExt q X) = 0 := rfl

/-- The second middle coordinate of `1` is `0`. -/
@[simp] public theorem secondOrderExtRight_one :
    secondOrderExtRight (1 : SecondOrderExt q X) = 0 := rfl

/-- The top coordinate of `1` is `0`. -/
@[simp] public theorem secondOrderExtTop_one :
    secondOrderExtTop (1 : SecondOrderExt q X) = 0 := rfl

/-- A second-order extension is a monoid under its second-order multiplication. -/
public instance : Monoid (SecondOrderExt q X) where
  mul_assoc x y z := by
    refine secondOrderExt_ext ?_ ?_ ?_ ?_
    · simp only [secondOrderExtFst_mul]; ring
    · simp only [secondOrderExtLeft_mul, secondOrderExtFst_mul, smul_add]; module
    · simp only [secondOrderExtRight_mul, secondOrderExtFst_mul, smul_add]; module
    · simp only [secondOrderExtTop_mul, secondOrderExtFst_mul, secondOrderExtLeft_mul,
        secondOrderExtRight_mul, smul_add, bilinearApp_add_left, bilinearApp_add_right,
        bilinearApp_smul_left, bilinearApp_smul_right]
      module
  one_mul x := by
    refine secondOrderExt_ext ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp
  mul_one x := by
    refine secondOrderExt_ext ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp

/-- A second-order extension is a semiring: the second-order multiplication distributes over the
coordinatewise addition. -/
public instance : Semiring (SecondOrderExt q X) where
  zero_mul x := by
    refine secondOrderExt_ext ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp
  mul_zero x := by
    refine secondOrderExt_ext ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp
  left_distrib x y z := by
    refine secondOrderExt_ext ?_ ?_ ?_ ?_
    · simp only [secondOrderExtFst_mul, secondOrderExtFst_add]; ring
    · simp only [secondOrderExtLeft_mul, secondOrderExtLeft_add, secondOrderExtFst_add]
      module
    · simp only [secondOrderExtRight_mul, secondOrderExtRight_add, secondOrderExtFst_add]
      module
    · simp only [secondOrderExtTop_mul, secondOrderExtTop_add, secondOrderExtFst_add,
        secondOrderExtLeft_add, secondOrderExtRight_add, bilinearApp_add_left,
        bilinearApp_add_right]
      module
  right_distrib x y z := by
    refine secondOrderExt_ext ?_ ?_ ?_ ?_
    · simp only [secondOrderExtFst_mul, secondOrderExtFst_add]; ring
    · simp only [secondOrderExtLeft_mul, secondOrderExtLeft_add, secondOrderExtFst_add]
      module
    · simp only [secondOrderExtRight_mul, secondOrderExtRight_add, secondOrderExtFst_add]
      module
    · simp only [secondOrderExtTop_mul, secondOrderExtTop_add, secondOrderExtFst_add,
        secondOrderExtLeft_add, secondOrderExtRight_add, bilinearApp_add_left,
        bilinearApp_add_right]
      module

/-- A second-order extension is a ring. -/
public instance : Ring (SecondOrderExt q X) where
  neg_add_cancel x := neg_add_cancel x

/-- **A second-order extension is commutative**, because the correction term of its
multiplication is symmetric in its two arguments. -/
public instance : CommRing (SecondOrderExt q X) where
  mul_comm x y := by
    refine secondOrderExt_ext ?_ ?_ ?_ ?_
    · simp only [secondOrderExtFst_mul]; ring
    · simp only [secondOrderExtLeft_mul]; module
    · simp only [secondOrderExtRight_mul]; module
    · simp only [secondOrderExtTop_mul]; module

/-! ### The second-order extension as a presheaf of divided power rings -/

/-- The restriction map of a presheaf of modules along an identity is the identity.

Private and renamed, as in
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/SqZeroExt.lean`: the general form of this
statement lives in a `Sheaf` module, and importing that here would point a `Crystalline`
module at it for one unfolding. -/
private theorem presheafMap_id_apply
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) {X : Cᵒᵖ} (x : M.obj X) :
    M.map (𝟙 X) x = x := by
  rw [← presheaf_map_apply_coe, M.presheaf.map_id]
  rfl

/-- **The restriction homomorphism of a second-order extension**: restrict each of the four
coordinates.  It is multiplicative because the pairing commutes with restriction. -/
public def secondOrderExtRingHom (q : Stacks.BilinearMap M₁ M₂ N) {X Y : Cᵒᵖ} (i : X ⟶ Y) :
    SecondOrderExt q X →+* SecondOrderExt q Y where
  toFun x := secondOrderExtMk ((R.map i).hom (secondOrderExtFst x))
    (M₁.map i (secondOrderExtLeft x)) (M₂.map i (secondOrderExtRight x))
    (N.map i (secondOrderExtTop x))
  map_one' := secondOrderExt_ext (map_one _) (map_zero _) (map_zero _) (map_zero _)
  map_zero' := secondOrderExt_ext (map_zero _) (map_zero _) (map_zero _) (map_zero _)
  map_add' x y := secondOrderExt_ext (map_add _ _ _) (map_add _ _ _) (map_add _ _ _) (map_add _ _ _)
  map_mul' x y := by
    refine secondOrderExt_ext (map_mul _ _ _) ?_ ?_ ?_
    · change M₁.map i (secondOrderExtFst x • secondOrderExtLeft y +
        secondOrderExtFst y • secondOrderExtLeft x) = _
      rw [map_add, M₁.map_smul, M₁.map_smul]
      rfl
    · change M₂.map i (secondOrderExtFst x • secondOrderExtRight y +
        secondOrderExtFst y • secondOrderExtRight x) = _
      rw [map_add, M₂.map_smul, M₂.map_smul]
      rfl
    · change N.map i (secondOrderExtFst x • secondOrderExtTop y +
        secondOrderExtFst y • secondOrderExtTop x +
        bilinearApp q X (secondOrderExtLeft x) (secondOrderExtRight y) +
        bilinearApp q X (secondOrderExtLeft y) (secondOrderExtRight x)) = _
      rw [map_add, map_add, map_add, N.map_smul, N.map_smul]
      exact congrArg₂ (· + ·)
        (congrArg₂ (· + ·) rfl (q.naturality i (secondOrderExtLeft x) (secondOrderExtRight y)))
        (q.naturality i (secondOrderExtLeft y) (secondOrderExtRight x))

/-- The first coordinate of a restriction is the restriction of the first coordinate. -/
@[simp] public theorem secondOrderExtFst_restrict {X Y : Cᵒᵖ} (i : X ⟶ Y)
    (x : SecondOrderExt q X) :
    secondOrderExtFst (secondOrderExtRingHom q i x) = (R.map i).hom (secondOrderExtFst x) := rfl

/-- The first middle coordinate of a restriction is the restriction of the first middle
coordinate. -/
@[simp] public theorem secondOrderExtLeft_restrict {X Y : Cᵒᵖ} (i : X ⟶ Y)
    (x : SecondOrderExt q X) :
    secondOrderExtLeft (secondOrderExtRingHom q i x) = M₁.map i (secondOrderExtLeft x) := rfl

/-- The second middle coordinate of a restriction is the restriction of the second middle
coordinate. -/
@[simp] public theorem secondOrderExtRight_restrict {X Y : Cᵒᵖ} (i : X ⟶ Y)
    (x : SecondOrderExt q X) :
    secondOrderExtRight (secondOrderExtRingHom q i x) = M₂.map i (secondOrderExtRight x) := rfl

/-- The top coordinate of a restriction is the restriction of the top coordinate. -/
@[simp] public theorem secondOrderExtTop_restrict {X Y : Cᵒᵖ} (i : X ⟶ Y)
    (x : SecondOrderExt q X) :
    secondOrderExtTop (secondOrderExtRingHom q i x) = N.map i (secondOrderExtTop x) := rfl

/-- **The second-order extension of a presheaf of commutative rings**, as a presheaf of
commutative rings. -/
public def secondOrderExtPresheaf (q : Stacks.BilinearMap M₁ M₂ N) : Cᵒᵖ ⥤ CommRingCat.{u} where
  obj X := CommRingCat.of (SecondOrderExt q X)
  map i := CommRingCat.ofHom (secondOrderExtRingHom q i)
  map_id X := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => secondOrderExt_ext ?_ ?_ ?_ ?_)
    · exact congrArg (fun f : R.obj X ⟶ R.obj X => f.hom (secondOrderExtFst x)) (R.map_id X)
    · exact presheafMap_id_apply M₁ (secondOrderExtLeft x)
    · exact presheafMap_id_apply M₂ (secondOrderExtRight x)
    · exact presheafMap_id_apply N (secondOrderExtTop x)
  map_comp {X Y Z} i j := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => secondOrderExt_ext ?_ ?_ ?_ ?_)
    · exact congrArg (fun f : R.obj X ⟶ R.obj Z => f.hom (secondOrderExtFst x)) (R.map_comp i j)
    · exact map_comp_apply M₁ i j (secondOrderExtLeft x)
    · exact map_comp_apply M₂ i j (secondOrderExtRight x)
    · exact map_comp_apply N i j (secondOrderExtTop x)

/-- The projection of a second-order extension onto its first coordinate. -/
public def secondOrderExtFstHom (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ) :
    SecondOrderExt q X →+* ↑(R.obj X) where
  toFun := secondOrderExtFst
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The inclusion of the first coordinate into a second-order extension. -/
public def secondOrderExtInclHom (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ) :
    ↑(R.obj X) →+* SecondOrderExt q X where
  toFun a := secondOrderExtMk a 0 0 0
  map_one' := rfl
  map_mul' a b := by
    refine secondOrderExt_ext rfl ?_ ?_ ?_
    · simp
    · simp
    · simp
  map_zero' := rfl
  map_add' a b := secondOrderExt_ext rfl (add_zero _).symm (add_zero _).symm (add_zero _).symm

/-- The inclusion of the first coordinate sends `a` to the section with coordinates
`(a, 0, 0, 0)`. -/
@[simp] public theorem secondOrderExtInclHom_apply (a : ↑(R.obj X)) :
    secondOrderExtInclHom q X a = secondOrderExtMk (q := q) a 0 0 0 := rfl

variable (q)

/-- **The ideal of a second-order extension** attached to an ideal of the first coordinate: the
sections whose first coordinate lies in it. -/
public def secondOrderExtIdeal (X : Cᵒᵖ) (I : Ideal ↑(R.obj X)) :
    Ideal (SecondOrderExt q X) :=
  Ideal.comap (secondOrderExtFstHom q X) I

variable {q}

/-- A section lies in the ideal attached to `I` exactly when its first coordinate lies in `I`. -/
public theorem mem_secondOrderExtIdeal_iff {I : Ideal ↑(R.obj X)} (x : SecondOrderExt q X) :
    x ∈ secondOrderExtIdeal q X I ↔ secondOrderExtFst x ∈ I := Iff.rfl

section DividedPowers

open scoped Classical in
/-- **The divided power operation of a second-order extension.**  It is `1` in degree zero, the
identity in degree one, and in degree `k + 2` it is
`(γ_{k+2} a, γ_{k+1} a · m₁, γ_{k+1} a · m₂, γ_{k+1} a · n + γ_k a · q m₁ m₂)` on a section of the
ideal; off the ideal it is `0`. -/
public def secondOrderExtDpow (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ)
    {I : Ideal ↑(R.obj X)} (γ : DividedPowers I) :
    ℕ → SecondOrderExt q X → SecondOrderExt q X :=
  fun n x =>
    if _hx : x ∈ secondOrderExtIdeal q X I then
      match n with
      | 0 => 1
      | 1 => x
      | k + 2 =>
          secondOrderExtMk (γ.dpow (k + 2) (secondOrderExtFst x))
            (γ.dpow (k + 1) (secondOrderExtFst x) • secondOrderExtLeft x)
            (γ.dpow (k + 1) (secondOrderExtFst x) • secondOrderExtRight x)
            (γ.dpow (k + 1) (secondOrderExtFst x) • secondOrderExtTop x +
              γ.dpow k (secondOrderExtFst x) •
                bilinearApp q X (secondOrderExtLeft x) (secondOrderExtRight x))
    else 0

/-- The second-order divided power operation vanishes off the ideal. -/
public theorem secondOrderExtDpow_of_notMem (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ)
    {I : Ideal ↑(R.obj X)} (γ : DividedPowers I) {n : ℕ} {x : SecondOrderExt q X}
    (hx : x ∉ secondOrderExtIdeal q X I) : secondOrderExtDpow q X γ n x = 0 := by
  classical
  simp only [secondOrderExtDpow, dite_eq_right hx]

/-- The second-order divided power operation is `1` in degree zero on the ideal. -/
public theorem secondOrderExtDpow_zero (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ)
    {I : Ideal ↑(R.obj X)} (γ : DividedPowers I) {x : SecondOrderExt q X}
    (hx : x ∈ secondOrderExtIdeal q X I) : secondOrderExtDpow q X γ 0 x = 1 := by
  classical
  simp only [secondOrderExtDpow, dite_eq_left hx]

/-- The second-order divided power operation is the identity in degree one. -/
public theorem secondOrderExtDpow_one (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ)
    {I : Ideal ↑(R.obj X)} (γ : DividedPowers I) {x : SecondOrderExt q X}
    (hx : x ∈ secondOrderExtIdeal q X I) : secondOrderExtDpow q X γ 1 x = x := by
  classical
  simp only [secondOrderExtDpow, dite_eq_left hx]

/-- **The second-order divided power formula.**  Writing the degree as `k + 2` keeps the two
shifts `γ_{n-1}` and `γ_{n-2}` of the source literal, with no truncated subtraction. -/
public theorem secondOrderExtDpow_add_two (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ)
    {I : Ideal ↑(R.obj X)} (γ : DividedPowers I) (k : ℕ) {x : SecondOrderExt q X}
    (hx : x ∈ secondOrderExtIdeal q X I) :
    secondOrderExtDpow q X γ (k + 2) x =
      secondOrderExtMk (γ.dpow (k + 2) (secondOrderExtFst x))
        (γ.dpow (k + 1) (secondOrderExtFst x) • secondOrderExtLeft x)
        (γ.dpow (k + 1) (secondOrderExtFst x) • secondOrderExtRight x)
        (γ.dpow (k + 1) (secondOrderExtFst x) • secondOrderExtTop x +
          γ.dpow k (secondOrderExtFst x) •
            bilinearApp q X (secondOrderExtLeft x) (secondOrderExtRight x)) := by
  classical
  simp only [secondOrderExtDpow, dite_eq_left hx]

/-- The explicit second-order operation is the divided power structure Tag 07HI produces, which
pins down all of its axioms. -/
private theorem exists_secondOrderExtDividedPowers (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ)
    {I : Ideal ↑(R.obj X)} (γ : DividedPowers I) :
    ∃ δ : DividedPowers (secondOrderExtIdeal q X I),
      δ.dpow = secondOrderExtDpow q X γ ∧
        DividedPowers.IsDPMorphism γ δ (secondOrderExtInclHom q X) := by
  classical
  let _ : Algebra ↑(R.obj X) (SecondOrderExt q X) := (secondOrderExtInclHom q X).toAlgebra
  obtain ⟨δ, hδ, hmor⟩ :=
    exists_dividedPowers_secondOrderExtension I γ (secondOrderPairing q X)
      (B := SecondOrderExt q X) (SecondOrderExt.addEquiv q X)
      (fun _ => rfl) (fun _ _ => rfl)
      (secondOrderExtIdeal q X I) (fun _ => Iff.rfl)
  refine ⟨δ, funext fun n => funext fun x => ?_, hmor⟩
  by_cases hx : x ∈ secondOrderExtIdeal q X I
  · match n with
    | 0 => rw [δ.dpow_zero hx, secondOrderExtDpow_zero q X γ hx]
    | 1 => rw [δ.dpow_one hx, secondOrderExtDpow_one q X γ hx]
    | k + 2 =>
        rw [hδ (k + 2) x (by omega) hx, secondOrderExtDpow_add_two q X γ k hx]
        rfl
  · rw [δ.dpow_null hx, secondOrderExtDpow_of_notMem q X γ hx]

/-- **The divided powers of a second-order extension.**  The ideal of the sections whose first
coordinate lies in a divided power ideal `I` of the first coordinate carries the divided power
structure whose operation is `Crystalline.secondOrderExtDpow`. -/
public def secondOrderExtDividedPowers (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ)
    {I : Ideal ↑(R.obj X)} (γ : DividedPowers I) :
    DividedPowers (secondOrderExtIdeal q X I) where
  dpow := secondOrderExtDpow q X γ
  dpow_null hx := secondOrderExtDpow_of_notMem q X γ hx
  dpow_zero hx := secondOrderExtDpow_zero q X γ hx
  dpow_one hx := secondOrderExtDpow_one q X γ hx
  dpow_mem hn hx := by
    obtain ⟨δ, hδ, -⟩ := exists_secondOrderExtDividedPowers q X γ
    rw [← hδ]; exact δ.dpow_mem hn hx
  dpow_add hx hx' := by
    obtain ⟨δ, hδ, -⟩ := exists_secondOrderExtDividedPowers q X γ
    rw [← hδ]; exact δ.dpow_add hx hx'
  dpow_mul hx := by
    obtain ⟨δ, hδ, -⟩ := exists_secondOrderExtDividedPowers q X γ
    rw [← hδ]; exact δ.dpow_mul hx
  mul_dpow hx := by
    obtain ⟨δ, hδ, -⟩ := exists_secondOrderExtDividedPowers q X γ
    rw [← hδ]; exact δ.mul_dpow hx
  dpow_comp hn hx := by
    obtain ⟨δ, hδ, -⟩ := exists_secondOrderExtDividedPowers q X γ
    rw [← hδ]; exact δ.dpow_comp hn hx

/-- The divided power operation of `Crystalline.secondOrderExtDividedPowers` is
`Crystalline.secondOrderExtDpow`. -/
@[simp] public theorem secondOrderExtDividedPowers_dpow (q : Stacks.BilinearMap M₁ M₂ N)
    (X : Cᵒᵖ) {I : Ideal ↑(R.obj X)} (γ : DividedPowers I) :
    (secondOrderExtDividedPowers q X γ).dpow = secondOrderExtDpow q X γ := rfl

/-- A divided power of the first coordinate, acting on the restriction of a section of a module,
is the restriction of the divided power acting on the section. -/
private theorem dpow_smul_map_comm {X Y : Cᵒᵖ} (i : X ⟶ Y) {IX : Ideal ↑(R.obj X)}
    {IY : Ideal ↑(R.obj Y)} {γX : DividedPowers IX} {γY : DividedPowers IY}
    (hnat : DividedPowers.IsDPMorphism γX γY (R.map i).hom)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) (n : ℕ) {a : ↑(R.obj X)}
    (ha : a ∈ IX) (m : ↑(M.obj X)) :
    γY.dpow n ((R.map i).hom a) • M.map i m = M.map i (γX.dpow n a • m) :=
  (congrArg (· • M.map i m) (hnat.dpow_comp (n := n) _ ha)).trans (M.map_smul i _ _).symm

/-- **Every restriction map of a second-order extension is compatible with the divided powers**
on the two ideals, as soon as the restriction map of the first coordinate is. -/
public theorem secondOrderExt_restriction_isDPMorphism (q : Stacks.BilinearMap M₁ M₂ N)
    {X Y : Cᵒᵖ} (i : X ⟶ Y) {IX : Ideal ↑(R.obj X)} {IY : Ideal ↑(R.obj Y)}
    (γX : DividedPowers IX) (γY : DividedPowers IY)
    (hnat : DividedPowers.IsDPMorphism γX γY (R.map i).hom) :
    DividedPowers.IsDPMorphism (secondOrderExtDividedPowers q X γX)
      (secondOrderExtDividedPowers q Y γY) (secondOrderExtRingHom q i) := by
  have hmem : ∀ a ∈ IX, (R.map i).hom a ∈ IY := fun a ha =>
    hnat.ideal_comp (Ideal.mem_map_of_mem _ ha)
  have hres : ∀ x : SecondOrderExt q X, x ∈ secondOrderExtIdeal q X IX →
      secondOrderExtRingHom q i x ∈ secondOrderExtIdeal q Y IY :=
    fun x hx => hmem _ hx
  refine ⟨Ideal.map_le_iff_le_comap.mpr fun x hx => hres x hx, ?_⟩
  intro n x hx
  have ha : secondOrderExtFst x ∈ IX := hx
  show secondOrderExtDpow q Y γY n (secondOrderExtRingHom q i x) =
    secondOrderExtRingHom q i (secondOrderExtDpow q X γX n x)
  match n with
  | 0 =>
      rw [secondOrderExtDpow_zero q Y γY (hres x hx), secondOrderExtDpow_zero q X γX hx, map_one]
  | 1 =>
      rw [secondOrderExtDpow_one q Y γY (hres x hx), secondOrderExtDpow_one q X γX hx]
  | k + 2 =>
      rw [secondOrderExtDpow_add_two q Y γY k (hres x hx),
        secondOrderExtDpow_add_two q X γX k hx]
      have hq : (bilinearApp q Y (M₁.map i (secondOrderExtLeft x))
            (M₂.map i (secondOrderExtRight x)) : ↑(N.obj Y))
          = N.map i (bilinearApp q X (secondOrderExtLeft x) (secondOrderExtRight x)) :=
        (q.naturality i (secondOrderExtLeft x) (secondOrderExtRight x)).symm
      refine secondOrderExt_ext ?_ ?_ ?_ ?_
      · exact hnat.dpow_comp (n := k + 2) _ ha
      · exact dpow_smul_map_comm i hnat M₁ (k + 1) ha _
      · exact dpow_smul_map_comm i hnat M₂ (k + 1) ha _
      · have h₁ := dpow_smul_map_comm i hnat N (k + 1) ha (secondOrderExtTop x)
        have h₂ := dpow_smul_map_comm i hnat N k ha
          (bilinearApp q X (secondOrderExtLeft x) (secondOrderExtRight x))
        rw [← hq] at h₂
        exact (congrArg₂ (fun z w : ↑(N.obj Y) => z + w) h₁ h₂).trans (map_add _ _ _).symm

/-- **A ring homomorphism into a second-order extension is a divided power morphism** as soon as
its first coordinate is one and each of its four coordinates obeys the divided power formula of
`Crystalline.secondOrderExtDpow`: the two middle coordinates the divided power chain rule, and the
top coordinate the shifted rule corrected by the pairing of the two middle coordinates.

This is the criterion the map `q₁₂` of Tag 07J3 satisfies, whose top coordinate is the de Rham
differential of its second middle coordinate and so does *not* vanish; for the five maps whose
top coordinate does vanish, `Crystalline.isDPMorphism_secondOrderExt_of_graph` is the convenient
form. -/
public theorem isDPMorphism_secondOrderExt_of_graph_top (q : Stacks.BilinearMap M₁ M₂ N)
    (X : Cᵒᵖ) {I : Ideal ↑(R.obj X)} (γ : DividedPowers I)
    {A' : Type u} [CommRing A'] {I' : Ideal A'} (γ' : DividedPowers I')
    (g : A' →+* SecondOrderExt q X)
    (hfst : DividedPowers.IsDPMorphism γ' γ ((secondOrderExtFstHom q X).comp g))
    (hleft : ∀ (k : ℕ), ∀ a ∈ I', secondOrderExtLeft (g (γ'.dpow (k + 1) a)) =
      γ.dpow k (secondOrderExtFst (g a)) • secondOrderExtLeft (g a))
    (hright : ∀ (k : ℕ), ∀ a ∈ I', secondOrderExtRight (g (γ'.dpow (k + 1) a)) =
      γ.dpow k (secondOrderExtFst (g a)) • secondOrderExtRight (g a))
    (htop : ∀ (k : ℕ), ∀ a ∈ I', secondOrderExtTop (g (γ'.dpow (k + 2) a)) =
      γ.dpow (k + 1) (secondOrderExtFst (g a)) • secondOrderExtTop (g a) +
        γ.dpow k (secondOrderExtFst (g a)) •
          bilinearApp q X (secondOrderExtLeft (g a)) (secondOrderExtRight (g a))) :
    DividedPowers.IsDPMorphism γ' (secondOrderExtDividedPowers q X γ) g := by
  have hmem : ∀ a ∈ I', g a ∈ secondOrderExtIdeal q X I := fun a ha =>
    hfst.ideal_comp (Ideal.mem_map_of_mem _ ha)
  refine ⟨Ideal.map_le_iff_le_comap.mpr fun a ha => hmem a ha, ?_⟩
  intro n a ha
  show secondOrderExtDpow q X γ n (g a) = g (γ'.dpow n a)
  match n with
  | 0 => rw [secondOrderExtDpow_zero q X γ (hmem a ha), γ'.dpow_zero ha, map_one]
  | 1 => rw [secondOrderExtDpow_one q X γ (hmem a ha), γ'.dpow_one ha]
  | k + 2 =>
      rw [secondOrderExtDpow_add_two q X γ k (hmem a ha)]
      refine secondOrderExt_ext ?_ ?_ ?_ ?_
      · exact hfst.dpow_comp (n := k + 2) a ha
      · exact (hleft (k + 1) a ha).symm
      · exact (hright (k + 1) a ha).symm
      · exact (htop k a ha).symm

/-- **A ring homomorphism into a second-order extension is a divided power morphism** as soon as
its first coordinate is one, its top coordinate vanishes on the ideal, each of its two middle
coordinates obeys the divided power chain rule, and the pairing of the two middle coordinates
vanishes on the ideal.

The last condition is what the three maps `𝒪_T → 𝒪_{T''}` and the two maps `𝒪_{T'} → 𝒪_{T''}` of
Tag 07J3 satisfy: for all but one of them one of the two middle coordinates is zero, and for the
remaining one the two middle coordinates agree, so the pairing — the exterior product — kills
them. -/
public theorem isDPMorphism_secondOrderExt_of_graph (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ)
    {I : Ideal ↑(R.obj X)} (γ : DividedPowers I)
    {A' : Type u} [CommRing A'] {I' : Ideal A'} (γ' : DividedPowers I')
    (g : A' →+* SecondOrderExt q X)
    (hfst : DividedPowers.IsDPMorphism γ' γ ((secondOrderExtFstHom q X).comp g))
    (htop : ∀ a ∈ I', secondOrderExtTop (g a) = 0)
    (hleft : ∀ (k : ℕ), ∀ a ∈ I', secondOrderExtLeft (g (γ'.dpow (k + 1) a)) =
      γ.dpow k (secondOrderExtFst (g a)) • secondOrderExtLeft (g a))
    (hright : ∀ (k : ℕ), ∀ a ∈ I', secondOrderExtRight (g (γ'.dpow (k + 1) a)) =
      γ.dpow k (secondOrderExtFst (g a)) • secondOrderExtRight (g a))
    (hpair : ∀ a ∈ I', bilinearApp q X (secondOrderExtLeft (g a)) (secondOrderExtRight (g a)) = 0) :
    DividedPowers.IsDPMorphism γ' (secondOrderExtDividedPowers q X γ) g := by
  refine isDPMorphism_secondOrderExt_of_graph_top q X γ γ' g hfst hleft hright fun k a ha => ?_
  have hdp : γ'.dpow (k + 2) a ∈ I' := γ'.dpow_mem (Nat.succ_ne_zero (k + 1)) ha
  rw [htop _ hdp, htop a ha, hpair a ha, smul_zero, smul_zero, add_zero]

/-! ### Homomorphisms into a second-order extension -/

/-- A map obeying the Leibniz rule kills the unit. -/
public theorem liftD_one_eq_zero {A' : Type u} [CommRing A'] {X : Cᵒᵖ}
    {P : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (g : A' →+* ↑(R.obj X)) (d : A' →+ ↑(P.obj X))
    (h : ∀ a b : A', d (a * b) = g a • d b + g b • d a) : d 1 = 0 := by
  have h1 := h 1 1
  rw [mul_one] at h1
  rw [map_one g, one_smul] at h1
  exact left_eq_add.mp h1

/-- A top coordinate obeying the second-order Leibniz rule kills the unit, as soon as the first
middle coordinate does. -/
public theorem liftTop_one_eq_zero {A' : Type u} [CommRing A'] {X : Cᵒᵖ}
    (g : A' →+* ↑(R.obj X)) (d₁ : A' →+ ↑(M₁.obj X)) (d₂ : A' →+ ↑(M₂.obj X))
    (t : A' →+ ↑(N.obj X)) (h₁ : d₁ 1 = 0)
    (ht : ∀ a b : A', t (a * b) = g a • t b + g b • t a +
      bilinearApp q X (d₁ a) (d₂ b) + bilinearApp q X (d₁ b) (d₂ a)) : t 1 = 0 := by
  have h := ht 1 1
  rw [mul_one, map_one g, one_smul, h₁, bilinearApp_zero_left, add_zero, add_zero] at h
  exact left_eq_add.mp h

/-- **A homomorphism into a second-order extension**, built from a homomorphism to the first
coordinate and two Leibniz maps to the two middle coordinates whose pairing is antisymmetric.
Its top coordinate vanishes. -/
public def secondOrderExtLift (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ) {A' : Type u}
    [CommRing A'] (g : A' →+* ↑(R.obj X)) (d₁ : A' →+ ↑(M₁.obj X)) (d₂ : A' →+ ↑(M₂.obj X))
    (h₁ : ∀ a b : A', d₁ (a * b) = g a • d₁ b + g b • d₁ a)
    (h₂ : ∀ a b : A', d₂ (a * b) = g a • d₂ b + g b • d₂ a)
    (hq : ∀ a b : A',
      bilinearApp q X (d₁ a) (d₂ b) + bilinearApp q X (d₁ b) (d₂ a) = 0) :
    A' →+* SecondOrderExt q X where
  toFun a := secondOrderExtMk (g a) (d₁ a) (d₂ a) 0
  map_one' := secondOrderExt_ext (map_one g) (liftD_one_eq_zero g d₁ h₁)
    (liftD_one_eq_zero g d₂ h₂) rfl
  map_mul' a b := by
    refine secondOrderExt_ext (map_mul g a b) (h₁ a b) (h₂ a b) ?_
    change (0 : ↑(N.obj X)) = g a • (0 : ↑(N.obj X)) + g b • (0 : ↑(N.obj X)) +
      bilinearApp q X (d₁ a) (d₂ b) + bilinearApp q X (d₁ b) (d₂ a)
    rw [smul_zero, smul_zero, add_zero, zero_add]
    exact (hq a b).symm
  map_zero' := secondOrderExt_ext (map_zero g) (map_zero d₁) (map_zero d₂) rfl
  map_add' a b := by
    refine secondOrderExt_ext (map_add g a b) (map_add d₁ a b) (map_add d₂ a b) ?_
    change (0 : ↑(N.obj X)) = (0 : ↑(N.obj X)) + (0 : ↑(N.obj X))
    rw [add_zero]

/-- The first coordinate of `Crystalline.secondOrderExtLift` is the homomorphism `g`. -/
@[simp] public theorem secondOrderExtLift_fst (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ)
    {A' : Type u} [CommRing A'] (g : A' →+* ↑(R.obj X)) (d₁ : A' →+ ↑(M₁.obj X))
    (d₂ : A' →+ ↑(M₂.obj X)) (h₁ h₂ hq) (a : A') :
    secondOrderExtFst (secondOrderExtLift q X g d₁ d₂ h₁ h₂ hq a) = g a := rfl

/-- The first middle coordinate of `Crystalline.secondOrderExtLift` is the map `d₁`. -/
@[simp] public theorem secondOrderExtLift_left (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ)
    {A' : Type u} [CommRing A'] (g : A' →+* ↑(R.obj X)) (d₁ : A' →+ ↑(M₁.obj X))
    (d₂ : A' →+ ↑(M₂.obj X)) (h₁ h₂ hq) (a : A') :
    secondOrderExtLeft (secondOrderExtLift q X g d₁ d₂ h₁ h₂ hq a) = d₁ a := rfl

/-- The second middle coordinate of `Crystalline.secondOrderExtLift` is the map `d₂`. -/
@[simp] public theorem secondOrderExtLift_right (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ)
    {A' : Type u} [CommRing A'] (g : A' →+* ↑(R.obj X)) (d₁ : A' →+ ↑(M₁.obj X))
    (d₂ : A' →+ ↑(M₂.obj X)) (h₁ h₂ hq) (a : A') :
    secondOrderExtRight (secondOrderExtLift q X g d₁ d₂ h₁ h₂ hq a) = d₂ a := rfl

/-- The top coordinate of `Crystalline.secondOrderExtLift` is zero. -/
@[simp] public theorem secondOrderExtLift_top (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ)
    {A' : Type u} [CommRing A'] (g : A' →+* ↑(R.obj X)) (d₁ : A' →+ ↑(M₁.obj X))
    (d₂ : A' →+ ↑(M₂.obj X)) (h₁ h₂ hq) (a : A') :
    secondOrderExtTop (secondOrderExtLift q X g d₁ d₂ h₁ h₂ hq a) = 0 := rfl

/-- **A homomorphism into a second-order extension with a prescribed top coordinate**, built from
a homomorphism to the first coordinate, two Leibniz maps to the two middle coordinates, and a map
to the top coordinate obeying the second-order Leibniz rule — the one with the correction term
`q (d₁ a) (d₂ b) + q (d₁ b) (d₂ a)` of the second-order multiplication.

Unlike `Crystalline.secondOrderExtLift`, whose top coordinate is zero and which therefore needs
the pairing of the two middle coordinates to be antisymmetric, this takes the top coordinate as
data; the antisymmetry is then whatever `ht` says it is.  It is what the map `q₁₂` of Tag 07J3
needs, the top coordinate of which is the de Rham differential of its second middle
coordinate. -/
public def secondOrderExtLiftTop (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ) {A' : Type u}
    [CommRing A'] (g : A' →+* ↑(R.obj X)) (d₁ : A' →+ ↑(M₁.obj X)) (d₂ : A' →+ ↑(M₂.obj X))
    (t : A' →+ ↑(N.obj X))
    (h₁ : ∀ a b : A', d₁ (a * b) = g a • d₁ b + g b • d₁ a)
    (h₂ : ∀ a b : A', d₂ (a * b) = g a • d₂ b + g b • d₂ a)
    (ht : ∀ a b : A', t (a * b) = g a • t b + g b • t a +
      bilinearApp q X (d₁ a) (d₂ b) + bilinearApp q X (d₁ b) (d₂ a)) :
    A' →+* SecondOrderExt q X where
  toFun a := secondOrderExtMk (g a) (d₁ a) (d₂ a) (t a)
  map_one' := secondOrderExt_ext (map_one g) (liftD_one_eq_zero g d₁ h₁)
    (liftD_one_eq_zero g d₂ h₂)
    (liftTop_one_eq_zero g d₁ d₂ t (liftD_one_eq_zero g d₁ h₁) ht)
  map_mul' a b := secondOrderExt_ext (map_mul g a b) (h₁ a b) (h₂ a b) (ht a b)
  map_zero' := secondOrderExt_ext (map_zero g) (map_zero d₁) (map_zero d₂) (map_zero t)
  map_add' a b := secondOrderExt_ext (map_add g a b) (map_add d₁ a b) (map_add d₂ a b)
    (map_add t a b)

/-- The first coordinate of `Crystalline.secondOrderExtLiftTop` is the homomorphism `g`. -/
@[simp] public theorem secondOrderExtLiftTop_fst (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ)
    {A' : Type u} [CommRing A'] (g : A' →+* ↑(R.obj X)) (d₁ : A' →+ ↑(M₁.obj X))
    (d₂ : A' →+ ↑(M₂.obj X)) (t : A' →+ ↑(N.obj X)) (h₁ h₂ ht) (a : A') :
    secondOrderExtFst (secondOrderExtLiftTop q X g d₁ d₂ t h₁ h₂ ht a) = g a := rfl

/-- The first middle coordinate of `Crystalline.secondOrderExtLiftTop` is the map `d₁`. -/
@[simp] public theorem secondOrderExtLiftTop_left (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ)
    {A' : Type u} [CommRing A'] (g : A' →+* ↑(R.obj X)) (d₁ : A' →+ ↑(M₁.obj X))
    (d₂ : A' →+ ↑(M₂.obj X)) (t : A' →+ ↑(N.obj X)) (h₁ h₂ ht) (a : A') :
    secondOrderExtLeft (secondOrderExtLiftTop q X g d₁ d₂ t h₁ h₂ ht a) = d₁ a := rfl

/-- The second middle coordinate of `Crystalline.secondOrderExtLiftTop` is the map `d₂`. -/
@[simp] public theorem secondOrderExtLiftTop_right (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ)
    {A' : Type u} [CommRing A'] (g : A' →+* ↑(R.obj X)) (d₁ : A' →+ ↑(M₁.obj X))
    (d₂ : A' →+ ↑(M₂.obj X)) (t : A' →+ ↑(N.obj X)) (h₁ h₂ ht) (a : A') :
    secondOrderExtRight (secondOrderExtLiftTop q X g d₁ d₂ t h₁ h₂ ht a) = d₂ a := rfl

/-- The top coordinate of `Crystalline.secondOrderExtLiftTop` is the map `t`. -/
@[simp] public theorem secondOrderExtLiftTop_top (q : Stacks.BilinearMap M₁ M₂ N) (X : Cᵒᵖ)
    {A' : Type u} [CommRing A'] (g : A' →+* ↑(R.obj X)) (d₁ : A' →+ ↑(M₁.obj X))
    (d₂ : A' →+ ↑(M₂.obj X)) (t : A' →+ ↑(N.obj X)) (h₁ h₂ ht) (a : A') :
    secondOrderExtTop (secondOrderExtLiftTop q X g d₁ d₂ t h₁ h₂ ht a) = t a := rfl

/-- **A morphism of presheaves of commutative rings into a second-order extension**, built from a
morphism to the first coordinate and two natural families of Leibniz maps to the two middle
coordinates whose pairing is antisymmetric. -/
public def secondOrderExtLiftPresheafHom (q : Stacks.BilinearMap M₁ M₂ N)
    {A' : Cᵒᵖ ⥤ CommRingCat.{u}} (g : A' ⟶ R)
    (d₁ : ∀ X : Cᵒᵖ, ↑(A'.obj X) →+ ↑(M₁.obj X))
    (d₂ : ∀ X : Cᵒᵖ, ↑(A'.obj X) →+ ↑(M₂.obj X))
    (h₁ : ∀ (X : Cᵒᵖ) (a b : ↑(A'.obj X)),
      d₁ X (a * b) = (g.app X).hom a • d₁ X b + (g.app X).hom b • d₁ X a)
    (h₂ : ∀ (X : Cᵒᵖ) (a b : ↑(A'.obj X)),
      d₂ X (a * b) = (g.app X).hom a • d₂ X b + (g.app X).hom b • d₂ X a)
    (hq : ∀ (X : Cᵒᵖ) (a b : ↑(A'.obj X)),
      bilinearApp q X (d₁ X a) (d₂ X b) + bilinearApp q X (d₁ X b) (d₂ X a) = 0)
    (hn₁ : ∀ {X Z : Cᵒᵖ} (i : X ⟶ Z) (a : ↑(A'.obj X)),
      M₁.map i (d₁ X a) = d₁ Z ((A'.map i).hom a))
    (hn₂ : ∀ {X Z : Cᵒᵖ} (i : X ⟶ Z) (a : ↑(A'.obj X)),
      M₂.map i (d₂ X a) = d₂ Z ((A'.map i).hom a)) :
    A' ⟶ secondOrderExtPresheaf q where
  app X := CommRingCat.ofHom
    (secondOrderExtLift q X (g.app X).hom (d₁ X) (d₂ X) (h₁ X) (h₂ X) (hq X))
  naturality X Z i := CommRingCat.hom_ext (RingHom.ext fun a => by
    refine secondOrderExt_ext ?_ (hn₁ i a).symm (hn₂ i a).symm (map_zero _).symm
    exact congrArg (fun m : A'.obj X ⟶ R.obj Z => m.hom a) (g.naturality i))

/-- **A morphism of presheaves of commutative rings into a second-order extension with a
prescribed top coordinate**, built from a morphism to the first coordinate and three natural
families of maps obeying the Leibniz rules of `Crystalline.secondOrderExtLiftTop`. -/
public def secondOrderExtLiftTopPresheafHom (q : Stacks.BilinearMap M₁ M₂ N)
    {A' : Cᵒᵖ ⥤ CommRingCat.{u}} (g : A' ⟶ R)
    (d₁ : ∀ X : Cᵒᵖ, ↑(A'.obj X) →+ ↑(M₁.obj X))
    (d₂ : ∀ X : Cᵒᵖ, ↑(A'.obj X) →+ ↑(M₂.obj X))
    (t : ∀ X : Cᵒᵖ, ↑(A'.obj X) →+ ↑(N.obj X))
    (h₁ : ∀ (X : Cᵒᵖ) (a b : ↑(A'.obj X)),
      d₁ X (a * b) = (g.app X).hom a • d₁ X b + (g.app X).hom b • d₁ X a)
    (h₂ : ∀ (X : Cᵒᵖ) (a b : ↑(A'.obj X)),
      d₂ X (a * b) = (g.app X).hom a • d₂ X b + (g.app X).hom b • d₂ X a)
    (ht : ∀ (X : Cᵒᵖ) (a b : ↑(A'.obj X)),
      t X (a * b) = (g.app X).hom a • t X b + (g.app X).hom b • t X a +
        bilinearApp q X (d₁ X a) (d₂ X b) + bilinearApp q X (d₁ X b) (d₂ X a))
    (hn₁ : ∀ {X Z : Cᵒᵖ} (i : X ⟶ Z) (a : ↑(A'.obj X)),
      M₁.map i (d₁ X a) = d₁ Z ((A'.map i).hom a))
    (hn₂ : ∀ {X Z : Cᵒᵖ} (i : X ⟶ Z) (a : ↑(A'.obj X)),
      M₂.map i (d₂ X a) = d₂ Z ((A'.map i).hom a))
    (hnt : ∀ {X Z : Cᵒᵖ} (i : X ⟶ Z) (a : ↑(A'.obj X)),
      N.map i (t X a) = t Z ((A'.map i).hom a)) :
    A' ⟶ secondOrderExtPresheaf q where
  app X := CommRingCat.ofHom
    (secondOrderExtLiftTop q X (g.app X).hom (d₁ X) (d₂ X) (t X) (h₁ X) (h₂ X) (ht X))
  naturality X Z i := CommRingCat.hom_ext (RingHom.ext fun a => by
    refine secondOrderExt_ext ?_ (hn₁ i a).symm (hn₂ i a).symm (hnt i a).symm
    exact congrArg (fun m : A'.obj X ⟶ R.obj Z => m.hom a) (g.naturality i))

/-- The identity is a divided power morphism. -/
public theorem isDPMorphism_of_eq_id {A' : Type u} [CommRing A'] {I' : Ideal A'}
    (γ' : DividedPowers I') (g : A' →+* A') (hg : ∀ a, g a = a) :
    DividedPowers.IsDPMorphism γ' γ' g :=
  ⟨Ideal.map_le_iff_le_comap.mpr fun a ha => by
      rw [Ideal.mem_comap, hg]; exact ha,
    fun a _ => by simp only [hg]⟩

end DividedPowers

end SecondOrderExt

/-! ### The sheaf condition for a second-order extension -/

/-- **The second-order extension of a sheaf of commutative rings by three sheaves of modules is a
sheaf**, because additively it is their product: a compatible family of sections glues
coordinatewise, and the multiplication and the divided powers play no part. -/
public theorem isSheaf_secondOrderExtPresheaf {X : TopCat.{u}}
    {R : (Opens (X : Type u))ᵒᵖ ⥤ CommRingCat.{u}}
    {M₁ M₂ N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (q : Stacks.BilinearMap M₁ M₂ N)
    (hR : TopCat.Presheaf.IsSheaf R) (h₁ : TopCat.Presheaf.IsSheaf M₁.presheaf)
    (h₂ : TopCat.Presheaf.IsSheaf M₂.presheaf) (hN : TopCat.Presheaf.IsSheaf N.presheaf) :
    TopCat.Presheaf.IsSheaf (secondOrderExtPresheaf q) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have cR : TopCat.Presheaf.IsCompatible R U (fun i => secondOrderExtFst (sf i)) :=
    fun i j => congrArg secondOrderExtFst (hsf i j)
  have c₁ : TopCat.Presheaf.IsCompatible M₁.presheaf U (fun i => secondOrderExtLeft (sf i)) :=
    fun i j => congrArg secondOrderExtLeft (hsf i j)
  have c₂ : TopCat.Presheaf.IsCompatible M₂.presheaf U (fun i => secondOrderExtRight (sf i)) :=
    fun i j => congrArg secondOrderExtRight (hsf i j)
  have cN : TopCat.Presheaf.IsCompatible N.presheaf U (fun i => secondOrderExtTop (sf i)) :=
    fun i j => congrArg secondOrderExtTop (hsf i j)
  obtain ⟨a, ha, haU⟩ := hR.isSheafUniqueGluing U _ cR
  obtain ⟨m₁, hm₁, hm₁U⟩ := h₁.isSheafUniqueGluing U _ c₁
  obtain ⟨m₂, hm₂, hm₂U⟩ := h₂.isSheafUniqueGluing U _ c₂
  obtain ⟨n, hn, hnU⟩ := hN.isSheafUniqueGluing U _ cN
  refine ⟨secondOrderExtMk a m₁ m₂ n, fun i => secondOrderExt_ext ?_ ?_ ?_ ?_, ?_⟩
  · exact (congrArg (R.map (Opens.leSupr U i).op) (secondOrderExtFst_mk a m₁ m₂ n)).trans (ha i)
  · exact (congrArg (M₁.presheaf.map (Opens.leSupr U i).op)
      (secondOrderExtLeft_mk a m₁ m₂ n)).trans (hm₁ i)
  · exact (congrArg (M₂.presheaf.map (Opens.leSupr U i).op)
      (secondOrderExtRight_mk a m₁ m₂ n)).trans (hm₂ i)
  · exact (congrArg (N.presheaf.map (Opens.leSupr U i).op)
      (secondOrderExtTop_mk a m₁ m₂ n)).trans (hn i)
  · intro s hs
    refine secondOrderExt_ext ?_ ?_ ?_ ?_
    · exact (haU _ fun i => congrArg secondOrderExtFst (hs i)).trans
        (secondOrderExtFst_mk a m₁ m₂ n).symm
    · exact (hm₁U _ fun i => congrArg secondOrderExtLeft (hs i)).trans
        (secondOrderExtLeft_mk a m₁ m₂ n).symm
    · exact (hm₂U _ fun i => congrArg secondOrderExtRight (hs i)).trans
        (secondOrderExtRight_mk a m₁ m₂ n).symm
    · exact (hnU _ fun i => congrArg secondOrderExtTop (hs i)).trans
        (secondOrderExtTop_mk a m₁ m₂ n).symm

/-! ### The second exterior power of the sheaf of divided power differentials -/

section Thickening

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)

/-- The presheaf of sectionwise second exterior powers of the sheaf of divided power
differentials: its sections over an open are the second exterior power of the sections of
`Ω_{T/Y,δ}` there. -/
public abbrev dpSecondExteriorPresheaf :
    PresheafOfModules.{u} (T.scheme.sheaf.obj ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.extPow 2 (dpDifferentialsModules T Y f)

/-- **The second exterior power `Ω²_{T/Y,δ}` of the sheaf of divided power differentials**: by
Tag 01CG it is the sheafification of the presheaf of sectionwise second exterior powers, and that
is how it is built here. -/
public def dpSecondExteriorPower : T.scheme.Modules :=
  (PresheafOfModules.sheafification (𝟙 T.scheme.ringCatSheaf.obj)).obj
    (dpSecondExteriorPresheaf T Y f)

/-- `Ω²_{T/Y,δ}` read as a presheaf of modules over the structure sheaf of `T` in its
`CommRingCat`-valued form. -/
public abbrev dpSecondExteriorModules :
    PresheafOfModules.{u} (T.scheme.sheaf.obj ⋙ forget₂ CommRingCat RingCat) :=
  (Scheme.Modules.toPresheafOfModules T.scheme).obj (dpSecondExteriorPower T Y f)

/-- The unit of the sheafification, comparing the presheaf of sectionwise second exterior powers
with `Ω²_{T/Y,δ}`. -/
public def dpSecondExteriorToSheaf :
    dpSecondExteriorPresheaf T Y f ⟶ dpSecondExteriorModules T Y f :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 T.scheme.ringCatSheaf.obj)).unit.app _

/-- The ring of sections of `𝒪_T` over an open, in the `RingCat`-valued spelling that a presheaf
of `𝒪_T`-modules uses for its scalars. -/
public abbrev dpSectionRing (W : (Opens ↑T.scheme)ᵒᵖ) : Type u :=
  ↑((T.scheme.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj W)

/-- The exterior algebra of the sections of `Ω_{T/Y,δ}` over an open, the ambient algebra of the
sectionwise second exterior powers. -/
public abbrev dpFormAmbient (W : (Opens ↑T.scheme)ᵒᵖ) : Type u :=
  ExteriorAlgebra (dpSectionRing T W) ↑((dpDifferentialsModules T Y f).obj W)

/-- A section of the presheaf of sectionwise second exterior powers, read as an element of the
exterior algebra of the sections of `Ω_{T/Y,δ}`. -/
public def dpFormVal {W : (Opens ↑T.scheme)ᵒᵖ}
    (z : ↑((dpSecondExteriorPresheaf T Y f).obj W)) : dpFormAmbient T Y f W :=
  (PresheafOfModules.extPowSections 2 (dpDifferentialsModules T Y f) W z).1

/-- A section of the presheaf of sectionwise second exterior powers is determined by the element
of the exterior algebra it reads as. -/
public theorem dpFormVal_injective {W : (Opens ↑T.scheme)ᵒᵖ}
    {z z' : ↑((dpSecondExteriorPresheaf T Y f).obj W)}
    (h : dpFormVal T Y f z = dpFormVal T Y f z') : z = z' := Subtype.ext h

/-- The zero section reads as `0` in the exterior algebra. -/
@[simp] public theorem dpFormVal_zero {W : (Opens ↑T.scheme)ᵒᵖ} :
    dpFormVal T Y f (0 : ↑((dpSecondExteriorPresheaf T Y f).obj W)) = 0 := rfl

/-- Reading a section in the exterior algebra is additive. -/
@[simp] public theorem dpFormVal_add {W : (Opens ↑T.scheme)ᵒᵖ}
    (z z' : ↑((dpSecondExteriorPresheaf T Y f).obj W)) :
    dpFormVal T Y f (z + z') = dpFormVal T Y f z + dpFormVal T Y f z' := rfl

/-- Reading a section in the exterior algebra commutes with scalar multiplication. -/
@[simp] public theorem dpFormVal_smul {W : (Opens ↑T.scheme)ᵒᵖ} (c : dpSectionRing T W)
    (z : ↑((dpSecondExteriorPresheaf T Y f).obj W)) :
    dpFormVal T Y f (c • z) = c • dpFormVal T Y f z := rfl

/-- The exterior product of two local divided power differentials, as a section of the presheaf
of sectionwise second exterior powers. -/
public def dpWedgePresheaf (W : (Opens ↑T.scheme)ᵒᵖ)
    (x y : ↑((dpDifferentialsModules T Y f).obj W)) :
    ↑((dpSecondExteriorPresheaf T Y f).obj W) :=
  ⟨ExteriorAlgebra.ι _ x * ExteriorAlgebra.ι _ y,
    ExteriorAlgebra.mul_mem_exteriorPower (ExteriorAlgebra.ι_mem_exteriorPower x)
      (ExteriorAlgebra.ι_mem_exteriorPower y)⟩

/-- The exterior product of `x` and `y` reads as `ι x * ι y` in the exterior algebra. -/
@[simp] public theorem dpFormVal_wedge (W : (Opens ↑T.scheme)ᵒᵖ)
    (x y : ↑((dpDifferentialsModules T Y f).obj W)) :
    dpFormVal T Y f (dpWedgePresheaf T Y f W x y) =
      ExteriorAlgebra.ι (dpSectionRing T W) x * ExteriorAlgebra.ι (dpSectionRing T W) y := rfl

/-- The sectionwise exterior product is bilinear. -/
public def dpWedgePresheafLin (W : (Opens ↑T.scheme)ᵒᵖ) :
    ↑((dpDifferentialsModules T Y f).obj W) →ₗ[dpSectionRing T W]
      ↑((dpDifferentialsModules T Y f).obj W) →ₗ[dpSectionRing T W]
        ↑((dpSecondExteriorPresheaf T Y f).obj W) :=
  LinearMap.mk₂ _ (dpWedgePresheaf T Y f W)
    (fun x x' y => dpFormVal_injective T Y f (by
      rw [dpFormVal_add, dpFormVal_wedge, dpFormVal_wedge, dpFormVal_wedge, map_add, add_mul]))
    (fun a x y => dpFormVal_injective T Y f (by
      rw [dpFormVal_smul, dpFormVal_wedge, dpFormVal_wedge, map_smul, smul_mul_assoc]))
    (fun x y y' => dpFormVal_injective T Y f (by
      rw [dpFormVal_add, dpFormVal_wedge, dpFormVal_wedge, dpFormVal_wedge, map_add, mul_add]))
    (fun a x y => dpFormVal_injective T Y f (by
      rw [dpFormVal_smul, dpFormVal_wedge, dpFormVal_wedge, map_smul, mul_smul_comm]))

/-- The exterior product of two local divided power differentials, as a section of
`Ω²_{T/Y,δ}`. -/
public def dpWedgeLin (W : (Opens ↑T.scheme)ᵒᵖ) :
    ↑((dpDifferentialsModules T Y f).obj W) →ₗ[dpSectionRing T W]
      ↑((dpDifferentialsModules T Y f).obj W) →ₗ[dpSectionRing T W]
        ↑((dpSecondExteriorModules T Y f).obj W) :=
  LinearMap.compr₂ (dpWedgePresheafLin T Y f W) ((dpSecondExteriorToSheaf T Y f).app W).hom

/-- Restriction of a section of the presheaf of sectionwise second exterior powers is the
exterior power of the restriction map of `Ω_{T/Y,δ}`. -/
public theorem dpFormVal_map {W W' : (Opens ↑T.scheme)ᵒᵖ} (i : W ⟶ W')
    (z : ↑((dpSecondExteriorPresheaf T Y f).obj W)) :
    dpFormVal T Y f ((dpSecondExteriorPresheaf T Y f).map i z) =
      ExteriorAlgebra.mapₛₗ
        ((T.scheme.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map i).hom
        ((dpDifferentialsModules T Y f).restrictₛₗ i) (dpFormVal T Y f z) :=
  PresheafOfModules.extPowSections_map 2 (dpDifferentialsModules T Y f) i z

/-- The sectionwise exterior product commutes with the restriction maps. -/
public theorem dpWedgePresheaf_map {W W' : (Opens ↑T.scheme)ᵒᵖ} (i : W ⟶ W')
    (x y : ↑((dpDifferentialsModules T Y f).obj W)) :
    (dpSecondExteriorPresheaf T Y f).map i (dpWedgePresheaf T Y f W x y) =
      dpWedgePresheaf T Y f W' ((dpDifferentialsModules T Y f).map i x)
        ((dpDifferentialsModules T Y f).map i y) := by
  refine dpFormVal_injective T Y f ?_
  rw [dpFormVal_map]
  simp only [dpFormVal_wedge, map_mul, ExteriorAlgebra.mapₛₗ_ι,
    PresheafOfModules.restrictₛₗ_apply]
  exact (dpFormVal_wedge T Y f W' _ _).symm

/-- **The exterior product `Ω_{T/Y,δ} × Ω_{T/Y,δ} → Ω²_{T/Y,δ}`**, the bilinear pairing out of
which the second-order universal thickening is built. -/
public def dpWedge : Stacks.BilinearMap (dpDifferentialsModules T Y f)
    (dpDifferentialsModules T Y f) (dpSecondExteriorModules T Y f) where
  app W := AddMonoidHom.mk' (fun x => (dpWedgeLin T Y f W x).toAddMonoidHom) (by
    intro x x'
    refine AddMonoidHom.ext fun y => ?_
    simp)
  map_smul_left W a x y := by simp
  map_smul_right W a x y := by simp
  naturality {W W'} i x y :=
    (PresheafOfModules.naturality_apply (dpSecondExteriorToSheaf T Y f) i
      (dpWedgePresheaf T Y f W x y)).symm.trans
      (congrArg (fun z => (dpSecondExteriorToSheaf T Y f).app W' z)
        (dpWedgePresheaf_map T Y f i x y))

/-- **The exterior product of a divided power differential with itself vanishes.** -/
public theorem dpWedge_self (W : (Opens ↑T.scheme)ᵒᵖ)
    (x : ↑((dpDifferentialsModules T Y f).obj W)) :
    (dpWedge T Y f).app W x x = 0 := by
  have h : dpWedgePresheaf T Y f W x x = 0 :=
    dpFormVal_injective T Y f (by
      rw [dpFormVal_wedge, dpFormVal_zero, ExteriorAlgebra.ι_sq_zero])
  show ((dpSecondExteriorToSheaf T Y f).app W).hom (dpWedgePresheaf T Y f W x x) = 0
  rw [h, map_zero]

/-- **The exterior product is antisymmetric**: the two exterior products of a pair of divided
power differentials sum to zero. -/
public theorem dpWedge_add_swap (W : (Opens ↑T.scheme)ᵒᵖ)
    (x y : ↑((dpDifferentialsModules T Y f).obj W)) :
    (dpWedge T Y f).app W x y + (dpWedge T Y f).app W y x = 0 := by
  have h : dpWedgePresheaf T Y f W x y + dpWedgePresheaf T Y f W y x = 0 := by
    refine dpFormVal_injective T Y f ?_
    rw [dpFormVal_add, dpFormVal_wedge, dpFormVal_wedge, dpFormVal_zero]
    have h0 : ExteriorAlgebra.ι (dpSectionRing T W) (x + y) *
        ExteriorAlgebra.ι (dpSectionRing T W) (x + y) = 0 := ExteriorAlgebra.ι_sq_zero _
    rw [map_add, add_mul, mul_add, mul_add, ExteriorAlgebra.ι_sq_zero,
      ExteriorAlgebra.ι_sq_zero, zero_add, add_zero] at h0
    exact h0
  show ((dpSecondExteriorToSheaf T Y f).app W).hom (dpWedgePresheaf T Y f W x y) +
    ((dpSecondExteriorToSheaf T Y f).app W).hom (dpWedgePresheaf T Y f W y x) = 0
  rw [← map_add, h, map_zero]

/-- The universal divided power derivation kills the unit section. -/
public theorem sheafApp_one (W : T.scheme.Opens) : sheafApp T Y f W 1 = 0 := by
  have h := sheafApp_mul T Y f W 1 1
  rw [mul_one, one_smul] at h
  exact left_eq_add.mp h

/-! ### The second-order universal thickening -/

/-- **The structure sheaf of the second-order universal thickening** `T''` of a divided power
scheme `T` over `Y`: the presheaf of commutative rings
`𝒪_T ⊕ Ω_{T/Y,δ} ⊕ Ω_{T/Y,δ} ⊕ Ω²_{T/Y,δ}` whose multiplication is corrected in the last
coordinate by the exterior product of the two middle coordinates.  All four summands are
sheaves. -/
@[stacks 07J3 "the structure sheaf of the second-order thickening"]
public def secondOrderThickeningPresheaf : (Opens ↑T.scheme)ᵒᵖ ⥤ CommRingCat.{u} :=
  secondOrderExtPresheaf (dpWedge T Y f)

/-- **The structure sheaf of the second-order universal thickening**, as a sheaf: all four
summands `𝒪_T`, `Ω_{T/Y,δ}`, `Ω_{T/Y,δ}` and `Ω²_{T/Y,δ}` are sheaves, so the second-order
extension satisfies the sheaf condition. -/
@[stacks 07J3 "the structure sheaf of the second-order thickening is a sheaf"]
public def secondOrderThickeningSheaf : TopCat.Sheaf CommRingCat.{u} ↑T.scheme :=
  ⟨secondOrderThickeningPresheaf T Y f,
    isSheaf_secondOrderExtPresheaf (dpWedge T Y f) T.scheme.sheaf.property
      (dpDifferentialsSheaf T Y f).isSheaf (dpDifferentialsSheaf T Y f).isSheaf
      (dpSecondExteriorPower T Y f).isSheaf⟩

/-- The underlying presheaf of the second-order thickening sheaf is
`Crystalline.secondOrderThickeningPresheaf`. -/
@[simp]
public theorem secondOrderThickeningSheaf_obj :
    (secondOrderThickeningSheaf T Y f).obj = secondOrderThickeningPresheaf T Y f := rfl

/-- **The multiplication of `𝒪_{T''}` in coordinates.** -/
@[stacks 07J3 "the multiplication of the second-order thickening"]
public theorem secondOrderThickening_mul (W : (Opens ↑T.scheme)ᵒᵖ)
    (x y : SecondOrderExt (dpWedge T Y f) W) :
    (secondOrderExtFst (x * y) = secondOrderExtFst x * secondOrderExtFst y ∧
      secondOrderExtLeft (x * y) =
        secondOrderExtFst x • secondOrderExtLeft y +
          secondOrderExtFst y • secondOrderExtLeft x) ∧
    secondOrderExtRight (x * y) =
        secondOrderExtFst x • secondOrderExtRight y +
          secondOrderExtFst y • secondOrderExtRight x ∧
      secondOrderExtTop (x * y) =
        secondOrderExtFst x • secondOrderExtTop y + secondOrderExtFst y • secondOrderExtTop x +
          (dpWedge T Y f).app W (secondOrderExtLeft x) (secondOrderExtRight y) +
          (dpWedge T Y f).app W (secondOrderExtLeft y) (secondOrderExtRight x) :=
  ⟨⟨rfl, rfl⟩, rfl, rfl⟩

/-- **The ideal `J''` of the second-order universal thickening**: the inverse image of the
divided power ideal of `T` under the projection `𝒪_{T''} → 𝒪_T`. -/
@[stacks 07J3 "the ideal J'' of the second-order thickening"]
public def secondOrderThickeningIdeal (W : (Opens ↑T.scheme)ᵒᵖ) :
    Ideal (SecondOrderExt (dpWedge T Y f) W) :=
  secondOrderExtIdeal (dpWedge T Y f) W (sectionIdeal T.scheme.sheaf T.ideal W)

/-- **The divided power structure `δ''` on the ideal `J''`** of the second-order universal
thickening. -/
@[stacks 07J3 "the divided power structure on J''"]
public def secondOrderThickeningDividedPowers (W : (Opens ↑T.scheme)ᵒᵖ) :
    DividedPowers (secondOrderThickeningIdeal T Y f W) :=
  secondOrderExtDividedPowers (dpWedge T Y f) W (T.dividedPowers.dividedPowers W)

/-- **The displayed formula for `δ''`**:
`δ''_{k+2}(f, ω₁, ω₂, η) = (δ_{k+2} f, δ_{k+1} f · ω₁, δ_{k+1} f · ω₂,
δ_{k+1} f · η + δ_k f · ω₁ ∧ ω₂)`. -/
@[stacks 07J3 "the divided power formula on J''"]
public theorem secondOrderThickeningDividedPowers_dpow_add_two (W : (Opens ↑T.scheme)ᵒᵖ) (k : ℕ)
    {x : SecondOrderExt (dpWedge T Y f) W} (hx : x ∈ secondOrderThickeningIdeal T Y f W) :
    (secondOrderThickeningDividedPowers T Y f W).dpow (k + 2) x =
      secondOrderExtMk
        ((T.dividedPowers.dividedPowers W).dpow (k + 2) (secondOrderExtFst x))
        ((T.dividedPowers.dividedPowers W).dpow (k + 1) (secondOrderExtFst x) •
          secondOrderExtLeft x)
        ((T.dividedPowers.dividedPowers W).dpow (k + 1) (secondOrderExtFst x) •
          secondOrderExtRight x)
        ((T.dividedPowers.dividedPowers W).dpow (k + 1) (secondOrderExtFst x) •
            secondOrderExtTop x +
          (T.dividedPowers.dividedPowers W).dpow k (secondOrderExtFst x) •
            (dpWedge T Y f).app W (secondOrderExtLeft x) (secondOrderExtRight x)) :=
  secondOrderExtDpow_add_two (dpWedge T Y f) W (T.dividedPowers.dividedPowers W) k hx

/-- **Every restriction map of `𝒪_{T''}` is compatible with the divided powers of `J''`**, so the
rings of sections of `𝒪_{T''}` with the ideals `J''` and the structures `δ''` form a presheaf of
divided power rings. -/
@[stacks 07J3 "the divided powers on J'' are compatible with restriction"]
public theorem secondOrderThickening_restriction_isDPMorphism
    {W W' : (Opens ↑T.scheme)ᵒᵖ} (i : W ⟶ W') :
    DividedPowers.IsDPMorphism (secondOrderThickeningDividedPowers T Y f W)
      (secondOrderThickeningDividedPowers T Y f W')
      (secondOrderExtRingHom (dpWedge T Y f) i) :=
  secondOrderExt_restriction_isDPMorphism (dpWedge T Y f) i
    (T.dividedPowers.dividedPowers W) (T.dividedPowers.dividedPowers W')
    (T.dividedPowers.naturality i)

/-! ### The three maps out of `𝒪_T` -/

/-- The universal divided power derivation on sections, as an additive map. -/
public def dpDerivationHom (W : (Opens ↑T.scheme)ᵒᵖ) :
    ↑(T.scheme.sheaf.obj.obj W) →+ ↑((dpDifferentialsModules T Y f).obj W) :=
  AddMonoidHom.mk' (sheafApp T Y f W.unop) (sheafApp_add T Y f W.unop)

/-- The universal divided power derivation on sections is `sheafApp`. -/
@[simp] public theorem dpDerivationHom_apply (W : (Opens ↑T.scheme)ᵒᵖ)
    (a : ↑(T.scheme.sheaf.obj.obj W)) :
    dpDerivationHom T Y f W a = sheafApp T Y f W.unop a := rfl

/-- The Leibniz rule for the universal divided power derivation on sections. -/
public theorem dpDerivationHom_mul (W : (Opens ↑T.scheme)ᵒᵖ)
    (a b : ↑(T.scheme.sheaf.obj.obj W)) :
    dpDerivationHom T Y f W (a * b) =
      a • dpDerivationHom T Y f W b + b • dpDerivationHom T Y f W a :=
  sheafApp_mul T Y f W.unop a b

/-- The universal divided power derivation on sections commutes with restriction. -/
public theorem dpDerivationHom_naturality {W W' : (Opens ↑T.scheme)ᵒᵖ} (i : W ⟶ W')
    (a : ↑(T.scheme.sheaf.obj.obj W)) :
    (dpDifferentialsModules T Y f).map i (dpDerivationHom T Y f W a) =
      dpDerivationHom T Y f W' ((T.scheme.sheaf.obj.map i).hom a) :=
  sheafApp_naturality T Y f i.unop a

/-- **The first of the three maps `𝒪_T → 𝒪_{T''}`**, `f ↦ (f, 0, 0, 0)`. -/
@[stacks 07J3 "the map q₀"]
public def secondOrderThickeningQ₀ :
    T.scheme.sheaf.obj ⟶ secondOrderThickeningPresheaf T Y f :=
  secondOrderExtLiftPresheafHom (dpWedge T Y f) (𝟙 T.scheme.sheaf.obj) (fun _ => 0) (fun _ => 0)
    (fun _ a b => by simp) (fun _ a b => by simp) (fun _ a b => by simp)
    (fun i a => map_zero _) (fun i a => map_zero _)

/-- **The second of the three maps `𝒪_T → 𝒪_{T''}`**, `f ↦ (f, d f, 0, 0)`. -/
@[stacks 07J3 "the map q₁"]
public def secondOrderThickeningQ₁ :
    T.scheme.sheaf.obj ⟶ secondOrderThickeningPresheaf T Y f :=
  secondOrderExtLiftPresheafHom (dpWedge T Y f) (𝟙 T.scheme.sheaf.obj)
    (dpDerivationHom T Y f) (fun _ => 0)
    (fun W a b => dpDerivationHom_mul T Y f W a b) (fun _ a b => by simp)
    (fun _ a b => by simp)
    (fun i a => dpDerivationHom_naturality T Y f i a) (fun i a => map_zero _)

/-- **The third of the three maps `𝒪_T → 𝒪_{T''}`**, `f ↦ (f, d f, d f, 0)`.  It is
multiplicative because the exterior product is antisymmetric. -/
@[stacks 07J3 "the map q₂"]
public def secondOrderThickeningQ₂ :
    T.scheme.sheaf.obj ⟶ secondOrderThickeningPresheaf T Y f :=
  secondOrderExtLiftPresheafHom (dpWedge T Y f) (𝟙 T.scheme.sheaf.obj)
    (dpDerivationHom T Y f) (dpDerivationHom T Y f)
    (fun W a b => dpDerivationHom_mul T Y f W a b)
    (fun W a b => dpDerivationHom_mul T Y f W a b)
    (fun W a b => dpWedge_add_swap T Y f W (sheafApp T Y f W.unop a) (sheafApp T Y f W.unop b))
    (fun i a => dpDerivationHom_naturality T Y f i a)
    (fun i a => dpDerivationHom_naturality T Y f i a)

/-! ### Two of the three maps out of `𝒪_{T'}` -/

/-- The differential coordinate of a section of `𝒪_{T'}`, as an additive map. -/
public def firstOrderSndHom (W : (Opens ↑T.scheme)ᵒᵖ) :
    ↑((firstOrderThickeningPresheaf T Y f).obj W) →+
      ↑((dpDifferentialsModules T Y f).obj W) :=
  AddMonoidHom.mk' sqZeroExtSnd (fun x y => sqZeroExtSnd_add x y)

/-- `firstOrderSndHom` sends a section of `𝒪_{T'}` to its differential coordinate. -/
@[simp] public theorem firstOrderSndHom_apply (W : (Opens ↑T.scheme)ᵒᵖ)
    (x : ↑((firstOrderThickeningPresheaf T Y f).obj W)) :
    firstOrderSndHom T Y f W x = sqZeroExtSnd x := rfl

/-- **The map `q₀₁ : 𝒪_{T'} → 𝒪_{T''}`**, `(f, ω) ↦ (f, ω, 0, 0)`. -/
@[stacks 07J3 "the map q₀₁"]
public def secondOrderThickeningQ₀₁ :
    firstOrderThickeningPresheaf T Y f ⟶ secondOrderThickeningPresheaf T Y f :=
  secondOrderExtLiftPresheafHom (dpWedge T Y f) (firstOrderThickeningProj T Y f)
    (firstOrderSndHom T Y f) (fun _ => 0)
    (fun _ x y => sqZeroExtSnd_mul x y) (fun _ x y => by simp) (fun _ x y => by simp)
    (fun i x => (sqZeroExtSnd_map i x).symm) (fun i x => map_zero _)

/-- **The map `q₀₂ : 𝒪_{T'} → 𝒪_{T''}`**, `(f, ω) ↦ (f, ω, ω, 0)`.  It is multiplicative
because the exterior product is antisymmetric. -/
@[stacks 07J3 "the map q₀₂"]
public def secondOrderThickeningQ₀₂ :
    firstOrderThickeningPresheaf T Y f ⟶ secondOrderThickeningPresheaf T Y f :=
  secondOrderExtLiftPresheafHom (dpWedge T Y f) (firstOrderThickeningProj T Y f)
    (firstOrderSndHom T Y f) (firstOrderSndHom T Y f)
    (fun _ x y => sqZeroExtSnd_mul x y) (fun _ x y => sqZeroExtSnd_mul x y)
    (fun W x y => dpWedge_add_swap T Y f W (sqZeroExtSnd x) (sqZeroExtSnd y))
    (fun i x => (sqZeroExtSnd_map i x).symm) (fun i x => (sqZeroExtSnd_map i x).symm)

/-! ### Compatibility with the divided power structures -/

/-- **`q₀` is compatible with the divided power structures on `J` and `J''`.** -/
@[stacks 07J3 "q₀ is compatible with the divided powers"]
public theorem secondOrderThickeningQ₀_isDPMorphism (W : (Opens ↑T.scheme)ᵒᵖ) :
    DividedPowers.IsDPMorphism (T.dividedPowers.dividedPowers W)
      (secondOrderThickeningDividedPowers T Y f W)
      (((secondOrderThickeningQ₀ T Y f).app W).hom) :=
  isDPMorphism_secondOrderExt_of_graph (dpWedge T Y f) W (T.dividedPowers.dividedPowers W)
    (T.dividedPowers.dividedPowers W) _
    (isDPMorphism_of_eq_id (T.dividedPowers.dividedPowers W) _ fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => (smul_zero _).symm) (fun _ _ _ => (smul_zero _).symm)
    (fun _ _ => bilinearApp_zero_left _)

/-- **`q₁` is compatible with the divided power structures on `J` and `J''`**, because the
universal divided power derivation obeys the divided power chain rule and the exterior product of
a differential with zero vanishes. -/
@[stacks 07J3 "q₁ is compatible with the divided powers"]
public theorem secondOrderThickeningQ₁_isDPMorphism (W : (Opens ↑T.scheme)ᵒᵖ) :
    DividedPowers.IsDPMorphism (T.dividedPowers.dividedPowers W)
      (secondOrderThickeningDividedPowers T Y f W)
      (((secondOrderThickeningQ₁ T Y f).app W).hom) :=
  isDPMorphism_secondOrderExt_of_graph (dpWedge T Y f) W (T.dividedPowers.dividedPowers W)
    (T.dividedPowers.dividedPowers W) _
    (isDPMorphism_of_eq_id (T.dividedPowers.dividedPowers W) _ fun _ => rfl)
    (fun _ _ => rfl) (fun k a ha => sheafApp_dpow T Y f W.unop k a ha)
    (fun _ _ _ => (smul_zero _).symm) (fun _ _ => bilinearApp_zero_right _)

/-- **`q₂` is compatible with the divided power structures on `J` and `J''`**, because the
universal divided power derivation obeys the divided power chain rule and the exterior product of
a differential with itself vanishes. -/
@[stacks 07J3 "q₂ is compatible with the divided powers"]
public theorem secondOrderThickeningQ₂_isDPMorphism (W : (Opens ↑T.scheme)ᵒᵖ) :
    DividedPowers.IsDPMorphism (T.dividedPowers.dividedPowers W)
      (secondOrderThickeningDividedPowers T Y f W)
      (((secondOrderThickeningQ₂ T Y f).app W).hom) :=
  isDPMorphism_secondOrderExt_of_graph (dpWedge T Y f) W (T.dividedPowers.dividedPowers W)
    (T.dividedPowers.dividedPowers W) _
    (isDPMorphism_of_eq_id (T.dividedPowers.dividedPowers W) _ fun _ => rfl)
    (fun _ _ => rfl) (fun k a ha => sheafApp_dpow T Y f W.unop k a ha)
    (fun k a ha => sheafApp_dpow T Y f W.unop k a ha)
    (fun a _ => dpWedge_self T Y f W (sheafApp T Y f W.unop a))

/-- **`q₀₁` is compatible with the divided power structures on `J'` and `J''`.** -/
@[stacks 07J3 "q₀₁ is compatible with the divided powers"]
public theorem secondOrderThickeningQ₀₁_isDPMorphism (W : (Opens ↑T.scheme)ᵒᵖ) :
    DividedPowers.IsDPMorphism (firstOrderThickeningDividedPowers T Y f W)
      (secondOrderThickeningDividedPowers T Y f W)
      (((secondOrderThickeningQ₀₁ T Y f).app W).hom) :=
  isDPMorphism_secondOrderExt_of_graph (dpWedge T Y f) W (T.dividedPowers.dividedPowers W)
    (firstOrderThickeningDividedPowers T Y f W) _
    (firstOrderThickeningProj_isDPMorphism T Y f W) (fun _ _ => rfl)
    (fun k _ hx => (congrArg sqZeroExtSnd
      (firstOrderThickeningDividedPowers_dpow_succ T Y f W k hx)).trans (sqZeroExtSnd_mk _ _))
    (fun _ _ _ => (smul_zero _).symm) (fun _ _ => bilinearApp_zero_right _)

/-- **`q₀₂` is compatible with the divided power structures on `J'` and `J''`**, because the
exterior product of a differential with itself vanishes. -/
@[stacks 07J3 "q₀₂ is compatible with the divided powers"]
public theorem secondOrderThickeningQ₀₂_isDPMorphism (W : (Opens ↑T.scheme)ᵒᵖ) :
    DividedPowers.IsDPMorphism (firstOrderThickeningDividedPowers T Y f W)
      (secondOrderThickeningDividedPowers T Y f W)
      (((secondOrderThickeningQ₀₂ T Y f).app W).hom) :=
  isDPMorphism_secondOrderExt_of_graph (dpWedge T Y f) W (T.dividedPowers.dividedPowers W)
    (firstOrderThickeningDividedPowers T Y f W) _
    (firstOrderThickeningProj_isDPMorphism T Y f W) (fun _ _ => rfl)
    (fun k _ hx => (congrArg sqZeroExtSnd
      (firstOrderThickeningDividedPowers_dpow_succ T Y f W k hx)).trans (sqZeroExtSnd_mk _ _))
    (fun k _ hx => (congrArg sqZeroExtSnd
      (firstOrderThickeningDividedPowers_dpow_succ T Y f W k hx)).trans (sqZeroExtSnd_mk _ _))
    (fun x _ => dpWedge_self T Y f W (sqZeroExtSnd x))

/-! ### The composition relations -/

/-- **`q₀ = q₀₁ ∘ p₀`.** -/
@[stacks 07J3 "q₀ = q₀₁ ∘ p₀"]
public theorem secondOrderThickeningQ₀_eq_Q₀₁_comp_P₀ :
    firstOrderThickeningP₀ T Y f ≫ secondOrderThickeningQ₀₁ T Y f =
      secondOrderThickeningQ₀ T Y f :=
  by ext; rfl

/-- **`q₁ = q₀₁ ∘ p₁`.** -/
@[stacks 07J3 "q₁ = q₀₁ ∘ p₁"]
public theorem secondOrderThickeningQ₁_eq_Q₀₁_comp_P₁ :
    firstOrderThickeningP₁ T Y f ≫ secondOrderThickeningQ₀₁ T Y f =
      secondOrderThickeningQ₁ T Y f :=
  by ext; rfl

/-- **`q₀ = q₀₂ ∘ p₀`.** -/
@[stacks 07J3 "q₀ = q₀₂ ∘ p₀"]
public theorem secondOrderThickeningQ₀_eq_Q₀₂_comp_P₀ :
    firstOrderThickeningP₀ T Y f ≫ secondOrderThickeningQ₀₂ T Y f =
      secondOrderThickeningQ₀ T Y f :=
  by ext; rfl

/-- **`q₂ = q₀₂ ∘ p₁`.** -/
@[stacks 07J3 "q₂ = q₀₂ ∘ p₁"]
public theorem secondOrderThickeningQ₂_eq_Q₀₂_comp_P₁ :
    firstOrderThickeningP₁ T Y f ≫ secondOrderThickeningQ₀₂ T Y f =
      secondOrderThickeningQ₂ T Y f :=
  by ext; rfl

end Thickening

end Crystalline

end
