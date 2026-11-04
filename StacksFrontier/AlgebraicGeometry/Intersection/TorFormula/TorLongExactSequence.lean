module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CoherentTorSheaves

/-!
# The long exact sequence of Tor sheaves

Let `X` be a scheme and let `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` be a short exact sequence of
`𝒪_X`-modules. For an `𝒪_X`-module `𝒢` the Tor sheaves of the three terms against `𝒢` sit in a
long exact sequence

`… → Tor_{p+1}(ℱ₃, 𝒢) → Tor_p(ℱ₁, 𝒢) → Tor_p(ℱ₂, 𝒢) → Tor_p(ℱ₃, 𝒢) → Tor_{p-1}(ℱ₁, 𝒢) → …`

ending in `Tor_0(ℱ₂, 𝒢) → Tor_0(ℱ₃, 𝒢) → 0`.

Nothing here is an assumption. The derived tensor product on `D(𝒪_X)` is the one of
[Stacks, Tag 06YU] read at the ringed space underlying `X`, namely
`Stacks.Cohomology.TorAmplitude.derTensor`, whose exactness in each variable is one of its
fields; fixing the second argument therefore gives a *triangulated* endofunctor
`derivedTensorRight` of `D(𝒪_X)`, with `CommShift ℤ` and `IsTriangulated` available as
instances. Applying it to the distinguished triangle
`ℱ₁[0] → ℱ₂[0] → ℱ₃[0] → ℱ₁[0][1]` of the short exact sequence
(`CategoryTheory.ShortComplex.ShortExact.singleTriangle`) gives a distinguished triangle in
`D(𝒪_X)`, and the long exact sequence is the homology sequence of that triangle for the
homological functor `DerivedCategory.homologyFunctor`, since `Tor_p(ℱ, 𝒢)` is by definition the
`(-p)`-th cohomology sheaf of `ℱ ⊗ᴸ_{𝒪_X} 𝒢`.

The right-hand end of the sequence comes from right t-exactness of the derived tensor product
([Stacks, Tag 06YU]): both factors lie in `D^{≤ 0}(𝒪_X)`, hence so does their derived tensor
product, so the cohomology sheaves of `ℱ ⊗ᴸ_{𝒪_X} 𝒢` vanish in positive degrees. The left-hand
end is the vanishing of `Tor_p` above the dimension of a regular scheme and is
`AlgebraicGeometry.TorFormula.isZero_torSheaf_of_lt`, proved elsewhere.

## Main definitions

* `AlgebraicGeometry.TorFormula.derivedTensorRight`: the triangulated endofunctor
  `- ⊗ᴸ_{𝒪_X} 𝒢` of `D(𝒪_X)`.
* `AlgebraicGeometry.TorFormula.derivedTensorTriangle`: the distinguished triangle obtained by
  tensoring the triangle of a short exact sequence with `𝒢`.
* `AlgebraicGeometry.TorFormula.torSheafMap`: the map of Tor sheaves induced by a map of
  modules in the first variable.
* `AlgebraicGeometry.TorFormula.torSheafδ`: the connecting map
  `Tor_{p+1}(ℱ₃, 𝒢) → Tor_p(ℱ₁, 𝒢)`.

## Main results

* `AlgebraicGeometry.TorFormula.isTriangulated_derivedTensorRight` and
  `AlgebraicGeometry.TorFormula.commShift_derivedTensorRight`: `- ⊗ᴸ_{𝒪_X} 𝒢` is a triangulated
  endofunctor of `D(𝒪_X)`, as instances.
* `AlgebraicGeometry.TorFormula.derivedTensorTriangle_distinguished`: the tensored triangle of a
  short exact sequence is distinguished.
* `AlgebraicGeometry.TorFormula.torSheaf_exact₁`,
  `AlgebraicGeometry.TorFormula.torSheaf_exact₂`,
  `AlgebraicGeometry.TorFormula.torSheaf_exact₃`: the three kinds of three-term piece of the long
  exact sequence of Tor sheaves.
* `AlgebraicGeometry.TorFormula.epi_torSheafMap_zero`: the sequence ends in
  `Tor_0(ℱ₂, 𝒢) → Tor_0(ℱ₃, 𝒢) → 0`.
* `AlgebraicGeometry.TorFormula.torSheafExactSequence`: the five-term exact sequence
  `Tor_{p+1}(ℱ₁) → Tor_{p+1}(ℱ₂) → Tor_{p+1}(ℱ₃) → Tor_p(ℱ₁) → Tor_p(ℱ₂)`, the long exact
  sequence read as one exact `ComposableArrows`.

## Implementation notes

The three exactness statements are the three rotations of the homology sequence of a
distinguished triangle, `CategoryTheory.Functor.homologySequence_exact₁`, `_exact₂` and
`_exact₃`, specialised to the degrees `-p`. They are stated at `torSheaf` and at the maps named
here rather than at the anonymous maps those lemmas produce, so a consumer never has to unfold
`torSheaf` or `derivedTensorTriangle`; definitional unfolding is what makes the specialisations
hold.

Degrees are written `-((p : ℕ) : ℤ)` throughout, matching the definition of
`AlgebraicGeometry.TorFormula.torSheaf`, so that the sources and targets of the maps are
syntactically the Tor sheaves.

The local instance of raised priority selects the standard model of `D(𝒪_X)`, which is the one
`AlgebraicGeometry.TorFormula.torSheaf` is defined at, over the locally small model supplied by
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0AZS](https://stacks.math.columbia.edu/tag/0AZS)
* [Stacks Project, Tag 0AZT](https://stacks.math.columbia.edu/tag/0AZT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.TorFormula

section

-- The priority selects the standard model of `D(𝒪_X)`, the one `torSheaf` is defined at.
attribute [local instance 100000] HasDerivedCategory.standard

/-! ### Derived tensoring by a module is triangulated -/

/-- **`- ⊗ᴸ_{𝒪_X} 𝒢`, derived tensoring by an `𝒪_X`-module `𝒢` placed in degree `0`.** This is
the derived tensor product of [Stacks, Tag 06YU] with its second argument fixed, so it is an
exact functor of triangulated categories; the two instances below are its two halves. -/
abbrev derivedTensorRight (X : Scheme.{u}) (G : X.Modules) :
    DerivedCategory X.Modules ⥤ DerivedCategory X.Modules :=
  (derivedTensor X).flip.obj ((DerivedCategory.singleFunctor X.Modules 0).obj G)

/-- **Derived tensoring by a module commutes with the shift.** This is the `commShift_left`
field of the derived tensor product of [Stacks, Tag 06YU]. -/
instance commShift_derivedTensorRight (X : Scheme.{u}) (G : X.Modules) :
    (derivedTensorRight X G).CommShift ℤ :=
  (Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).commShift_left _

/-- **Derived tensoring by a module is triangulated**, so it carries a distinguished triangle to
a distinguished triangle. This is the `exact_left` field of the derived tensor product of
[Stacks, Tag 06YU]. -/
instance isTriangulated_derivedTensorRight (X : Scheme.{u}) (G : X.Modules) :
    (derivedTensorRight X G).IsTriangulated :=
  (Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).exact_left _

/-- Derived tensoring by `𝒢` agrees with the derived tensor product: the two spellings of
`ℱ ⊗ᴸ_{𝒪_X} 𝒢` are the same object. -/
theorem derivedTensorRight_obj (X : Scheme.{u}) (G : X.Modules)
    (K : DerivedCategory X.Modules) :
    (derivedTensorRight X G).obj K =
      ((derivedTensor X).obj K).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj G) :=
  rfl

/-- The Tor sheaf `Tor_p^{𝒪_X}(ℱ, 𝒢)` is the `(-p)`-th cohomology sheaf of `ℱ[0] ⊗ᴸ_{𝒪_X} 𝒢`. -/
theorem torSheaf_eq (X : Scheme.{u}) (F G : X.Modules) (p : ℕ) :
    torSheaf X F G p =
      (DerivedCategory.homologyFunctor X.Modules (-(p : ℤ))).obj
        ((derivedTensorRight X G).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F)) :=
  rfl

/-! ### The triangle of a short exact sequence, tensored -/

variable {X : Scheme.{u}} {S : ShortComplex X.Modules}

/-- **The distinguished triangle `ℱ₁ ⊗ᴸ 𝒢 → ℱ₂ ⊗ᴸ 𝒢 → ℱ₃ ⊗ᴸ 𝒢 → (ℱ₁ ⊗ᴸ 𝒢)[1]`** attached to a
short exact sequence `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` of `𝒪_X`-modules and an `𝒪_X`-module `𝒢`: the
triangle of the short exact sequence, tensored with `𝒢`. -/
def derivedTensorTriangle (hS : S.ShortExact) (G : X.Modules) :
    Triangle (DerivedCategory X.Modules) :=
  (derivedTensorRight X G).mapTriangle.obj hS.singleTriangle

/-- **The tensored triangle of a short exact sequence is distinguished**, because derived
tensoring by a module is triangulated. -/
theorem derivedTensorTriangle_distinguished (hS : S.ShortExact) (G : X.Modules) :
    derivedTensorTriangle hS G ∈ distTriang (DerivedCategory X.Modules) :=
  Functor.IsTriangulated.map_distinguished _ hS.singleTriangle_distinguished

/-! ### The maps of the long exact sequence -/

/-- **The map `Tor_p^{𝒪_X}(ℱ, 𝒢) → Tor_p^{𝒪_X}(ℱ', 𝒢)` induced by `ℱ → ℱ'`.** -/
def torSheafMap {F F' : X.Modules} (f : F ⟶ F') (G : X.Modules) (p : ℕ) :
    torSheaf X F G p ⟶ torSheaf X F' G p :=
  (DerivedCategory.homologyFunctor X.Modules (-(p : ℤ))).map
    ((derivedTensorRight X G).map ((DerivedCategory.singleFunctor X.Modules 0).map f))

/-- **The connecting map `Tor_{p+1}^{𝒪_X}(ℱ₃, 𝒢) → Tor_p^{𝒪_X}(ℱ₁, 𝒢)`** of a short exact
sequence `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0`: the connecting map of the homology sequence of the tensored
triangle, in degrees `-(p+1)` and `-p`. -/
def torSheafδ (hS : S.ShortExact) (G : X.Modules) (p : ℕ) :
    torSheaf X S.X₃ G (p + 1) ⟶ torSheaf X S.X₁ G p :=
  (DerivedCategory.homologyFunctor X.Modules 0).homologySequenceδ
    (derivedTensorTriangle hS G) (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) (by push_cast; ring)

/-! ### The long exact sequence -/

/-- The two maps `Tor_p(ℱ₁, 𝒢) → Tor_p(ℱ₂, 𝒢) → Tor_p(ℱ₃, 𝒢)` compose to zero. -/
theorem torSheafMap_comp_torSheafMap (hS : S.ShortExact) (G : X.Modules) (p : ℕ) :
    torSheafMap S.f G p ≫ torSheafMap S.g G p = 0 :=
  (DerivedCategory.homologyFunctor X.Modules 0).homologySequence_comp
    (derivedTensorTriangle hS G) (derivedTensorTriangle_distinguished hS G) (-(p : ℤ))

/-- The map `Tor_{p+1}(ℱ₂, 𝒢) → Tor_{p+1}(ℱ₃, 𝒢)` followed by the connecting map is zero. -/
theorem torSheafMap_comp_torSheafδ (hS : S.ShortExact) (G : X.Modules) (p : ℕ) :
    torSheafMap S.g G (p + 1) ≫ torSheafδ hS G p = 0 :=
  (DerivedCategory.homologyFunctor X.Modules 0).comp_homologySequenceδ
    (derivedTensorTriangle hS G) (derivedTensorTriangle_distinguished hS G)
    (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) (by push_cast; ring)

/-- The connecting map followed by `Tor_p(ℱ₁, 𝒢) → Tor_p(ℱ₂, 𝒢)` is zero. -/
theorem torSheafδ_comp_torSheafMap (hS : S.ShortExact) (G : X.Modules) (p : ℕ) :
    torSheafδ hS G p ≫ torSheafMap S.f G p = 0 :=
  (DerivedCategory.homologyFunctor X.Modules 0).homologySequenceδ_comp
    (derivedTensorTriangle hS G) (derivedTensorTriangle_distinguished hS G)
    (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) (by push_cast; ring)

/-- **The long exact sequence of Tor sheaves, middle piece**: for a short exact sequence
`0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` of `𝒪_X`-modules and every `p`, the three-term sequence
`Tor_p(ℱ₁, 𝒢) → Tor_p(ℱ₂, 𝒢) → Tor_p(ℱ₃, 𝒢)` is exact. -/
theorem torSheaf_exact₂ (hS : S.ShortExact) (G : X.Modules) (p : ℕ) :
    (ShortComplex.mk (torSheafMap S.f G p) (torSheafMap S.g G p)
      (torSheafMap_comp_torSheafMap hS G p)).Exact :=
  (DerivedCategory.homologyFunctor X.Modules 0).homologySequence_exact₂
    (derivedTensorTriangle hS G) (derivedTensorTriangle_distinguished hS G) (-(p : ℤ))

/-- **The long exact sequence of Tor sheaves, at `Tor_{p+1}(ℱ₃, 𝒢)`**: the three-term sequence
`Tor_{p+1}(ℱ₂, 𝒢) → Tor_{p+1}(ℱ₃, 𝒢) → Tor_p(ℱ₁, 𝒢)` is exact. -/
theorem torSheaf_exact₃ (hS : S.ShortExact) (G : X.Modules) (p : ℕ) :
    (ShortComplex.mk (torSheafMap S.g G (p + 1)) (torSheafδ hS G p)
      (torSheafMap_comp_torSheafδ hS G p)).Exact :=
  (DerivedCategory.homologyFunctor X.Modules 0).homologySequence_exact₃
    (derivedTensorTriangle hS G) (derivedTensorTriangle_distinguished hS G)
    (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) (by push_cast; ring)

/-- **The long exact sequence of Tor sheaves, at `Tor_p(ℱ₁, 𝒢)`**: the three-term sequence
`Tor_{p+1}(ℱ₃, 𝒢) → Tor_p(ℱ₁, 𝒢) → Tor_p(ℱ₂, 𝒢)` is exact. -/
theorem torSheaf_exact₁ (hS : S.ShortExact) (G : X.Modules) (p : ℕ) :
    (ShortComplex.mk (torSheafδ hS G p) (torSheafMap S.f G p)
      (torSheafδ_comp_torSheafMap hS G p)).Exact :=
  (DerivedCategory.homologyFunctor X.Modules 0).homologySequence_exact₁
    (derivedTensorTriangle hS G) (derivedTensorTriangle_distinguished hS G)
    (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) (by push_cast; ring)

/-! ### The right-hand end of the sequence -/

/-- **`ℱ ⊗ᴸ_{𝒪_X} 𝒢` lies in `D^{≤ 0}(𝒪_X)`** when `ℱ` and `𝒢` are modules placed in degree
`0`: right t-exactness of the derived tensor product of [Stacks, Tag 06YU], with both bounds
`0`. -/
theorem isLE_derivedTensorRight_singleFunctor_obj (X : Scheme.{u}) (F G : X.Modules) :
    ((derivedTensorRight X G).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj F)).IsLE 0 := by
  have hF : ((DerivedCategory.singleFunctor X.Modules 0).obj F).IsLE 0 := inferInstance
  have hG : ((DerivedCategory.singleFunctor X.Modules 0).obj G).IsLE 0 := inferInstance
  exact @Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct _ _ _ X.sheaf _ _ _ _ _ _ _
    _ _ 0 0 hF hG

/-- **The cohomology sheaves of `ℱ ⊗ᴸ_{𝒪_X} 𝒢` vanish in positive degrees** for modules `ℱ` and
`𝒢` placed in degree `0`. Equivalently, there are no Tor sheaves in negative index. -/
theorem isZero_homology_derivedTensorRight_of_pos (X : Scheme.{u}) (F G : X.Modules) (i : ℤ)
    (hi : 0 < i) :
    IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedTensorRight X G).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F))) :=
  have := isLE_derivedTensorRight_singleFunctor_obj X F G
  DerivedCategory.isZero_of_isLE _ 0 i hi

/-- **The long exact sequence of Tor sheaves ends in `Tor_0(ℱ₂, 𝒢) → Tor_0(ℱ₃, 𝒢) → 0`**: the
map on `Tor_0` induced by the surjection `ℱ₂ → ℱ₃` is an epimorphism, because the next term
`H^1(ℱ₁ ⊗ᴸ_{𝒪_X} 𝒢)` of the sequence vanishes. -/
theorem epi_torSheafMap_zero (hS : S.ShortExact) (G : X.Modules) :
    Epi (torSheafMap S.g G 0) := by
  refine ((DerivedCategory.homologyFunctor X.Modules 0).homologySequence_exact₃
    (derivedTensorTriangle hS G) (derivedTensorTriangle_distinguished hS G)
    (-((0 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ) + 1) rfl).epi_f_iff.mpr ?_
  exact (isZero_homology_derivedTensorRight_of_pos X S.X₁ G (-((0 : ℕ) : ℤ) + 1)
    (by norm_num)).eq_of_tgt _ _

/-! ### The sequence as one exact chain -/

/-- **The long exact sequence of Tor sheaves**, as a single exact five-term chain
`Tor_{p+1}(ℱ₁, 𝒢) → Tor_{p+1}(ℱ₂, 𝒢) → Tor_{p+1}(ℱ₃, 𝒢) → Tor_p(ℱ₁, 𝒢) → Tor_p(ℱ₂, 𝒢) →
Tor_p(ℱ₃, 𝒢)`. Successive five-term chains of this form, for `p` running downwards, assemble the
whole long exact sequence; its right-hand end is `epi_torSheafMap_zero` and, on a regular scheme
of dimension at most `d`, its left-hand end is `isZero_torSheaf_of_lt`. -/
theorem torSheafExactSequence (hS : S.ShortExact) (G : X.Modules) (p : ℕ) :
    ((DerivedCategory.homologyFunctor X.Modules 0).homologySequenceComposableArrows₅
      (derivedTensorTriangle hS G) (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ))
      (by push_cast; ring)).Exact :=
  (DerivedCategory.homologyFunctor X.Modules 0).homologySequenceComposableArrows₅_exact
    (derivedTensorTriangle hS G) (derivedTensorTriangle_distinguished hS G)
    (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) (by push_cast; ring)

end

end AlgebraicGeometry.TorFormula

end
