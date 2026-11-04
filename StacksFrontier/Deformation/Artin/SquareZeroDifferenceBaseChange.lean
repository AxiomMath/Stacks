module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.SquareZeroDifference

/-!
# Differences of lifts across a morphism of square-zero deformation situations

A morphism of square-zero deformation situations is a commuting square of ring maps

```
A' ---f'---> C'
|            |
qA           qC
v            v
A ----f----> C
```

with `qA`, `qC` surjective with square-zero kernels `I`, `J`. The second commuting square of
Stacks 07YA compares the action of `T_x(I)` on the lifts of `x` over `Spec A'` with the action
of `T_y(J)` on the lifts of `y` over `Spec C'`, and that action is pinned down by the
*geometric* difference of `Deformation.Artin.IsGeometricDifference`: two lifts are glued over
the self-fibre product `A' ×_A A'`, and the gluing is transported to `A' ×_A A[I]` across the
difference isomorphism `Deformation.Artin.squareZeroDifferenceEquiv`.

Transporting that construction along the square therefore needs the square to act on the
self-fibre products and on the kernels, compatibly with the kernel-valued difference. This file
supplies exactly that algebra. Before it nothing in this development related the self-fibre
product of one surjection to that of another: every statement about `RingHom.pullback` here and
in Mathlib is about a single square, and `Deformation.Artin.kerDifference` had no compatibility
with a second ring map at all.

## Main definitions

* `Deformation.Artin.kerBaseChange` — the map `I ⟶ J` on kernels induced by the square. It is
  `f'` restricted to the kernels, and it is `f`-semilinear for the canonical module structures
  of `Stacks.Smooth.kerModule`.
* `Deformation.Artin.kerSiteBaseChange` — the same map as a morphism `I ⟶ f_*J` of `A`-modules,
  which is the shape the transitions of Stacks 07YA take their coefficient map in.
* `Deformation.Artin.pullbackBaseChange` — the induced ring map of fibre products attached to
  a morphism of squares of rings. At the self-fibre products it is the comparison
  `A' ×_A A' ⟶ C' ×_C C'`; at the mixed pair, `A' ×_A A[I] ⟶ C' ×_C C[J]`.

## Main results

* `Deformation.Artin.kerBaseChange_smul` — semilinearity of the map on kernels: both sides are
  computed by multiplying with a lift of the scalar, and `f'` carries a lift of `a` to a lift
  of `f a`.
* `Deformation.Artin.kerDifference_pullbackBaseChange` — **the comparison is compatible
  with the kernel-valued difference**: the difference of the image of a point of `A' ×_A A'` is
  the image of its difference. This is the identity the transport of
  `Deformation.Artin.IsGeometricDifference` rests on.

## References

* [Stacks Project, Tag 07YA](https://stacks.math.columbia.edu/tag/07YA)
* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

/-! ### A fibre product of rings is determined by its two projections -/

section PullbackExt

universe u₁ u₂ u₃

/-- **The two projections of a fibre product of rings are jointly injective.** `R ×_T S` is a
subring of `R × S`, so an element of it — and hence a ring map into it — is determined by its
two projections.

This is what locates the obstruction to single-valuedness of
`Deformation.Artin.IsGeometricDifference` precisely. That predicate quantifies existentially
over a structure morphism `Spec (A' ×_A A') ⟶ S` and constrains it only through its two
composites with the sections `Spec A' ⟶ Spec (A' ×_A A')` of the two projections. By this
lemma the two composites determine the morphism *as soon as the target is affine*, so a witness
whose structure morphism factors through an affine open of `S` is pinned; see
`Deformation.Artin.eq_of_comp_specMap_pullback_sections`. It also pins the difference
isomorphism `A' ×_A A' ≃+* A' ×_A A[I]` of
`Deformation.Artin.squareZeroDifferenceEquiv` by the two components the predicate prescribes
for it. -/
public theorem pullback_ext {R : Type u₁} {S : Type u₂} {T : Type u₃}
    [Ring R] [Ring S] [Semiring T] (f : R →+* T) (g : S →+* T) {y y' : f.pullback g}
    (hfst : (y : R × S).1 = (y' : R × S).1)
    (hsnd : (y : R × S).2 = (y' : R × S).2) : y = y' :=
  Subtype.ext (Prod.ext hfst hsnd)

end PullbackExt

/-! ### A fibre product of rings base-changes along a morphism of squares -/

section PullbackBaseChange

universe u₁ u₂ u₃ u₄ u₅ u₆

variable {R₁ : Type u₁} {S₁ : Type u₂} {T₁ : Type u₃}
  {R₂ : Type u₄} {S₂ : Type u₅} {T₂ : Type u₆}
  [Ring R₁] [Ring S₁] [Semiring T₁] [Ring R₂] [Ring S₂] [Semiring T₂]
  (f₁ : R₁ →+* T₁) (g₁ : S₁ →+* T₁) (f₂ : R₂ →+* T₂) (g₂ : S₂ →+* T₂)
  (uR : R₁ →+* R₂) (uS : S₁ →+* S₂) (uT : T₁ →+* T₂)
  (hf : ∀ z, f₂ (uR z) = uT (f₁ z)) (hg : ∀ z, g₂ (uS z) = uT (g₁ z))

include hf hg in
/-- **A morphism of squares of rings induces one of their fibre products.** The three ring maps
`uR`, `uS`, `uT` commuting with the two pairs of legs carry `R₁ ×_{T₁} S₁` into
`R₂ ×_{T₂} S₂`, componentwise.

At `f₁ = g₁` and `f₂ = g₂` this is the comparison `A' ×_A A' ⟶ C' ×_C C'` of the self-fibre
products over which the geometric difference of Stacks 07Y9 (2)(b) glues two lifts; at the
mixed pair it is the comparison `A' ×_A A[I] ⟶ C' ×_C C[J]` of the rings the difference
isomorphism transports the glueing to. -/
public def pullbackBaseChange (y : f₁.pullback g₁) : f₂.pullback g₂ := by
  refine ⟨(uR (y : R₁ × S₁).1, uS (y : R₁ × S₁).2), ?_⟩
  have hy : f₁ (y : R₁ × S₁).1 = g₁ (y : R₁ × S₁).2 := y.2
  change f₂ (uR (y : R₁ × S₁).1) = g₂ (uS (y : R₁ × S₁).2)
  rw [hf, hg, hy]

include hf hg in
/-- The first component of `pullbackBaseChange` is `uR` applied to the first component. -/
public theorem pullbackBaseChange_fst (y : f₁.pullback g₁) :
    (pullbackBaseChange f₁ g₁ f₂ g₂ uR uS uT hf hg y : R₂ × S₂).1 =
      uR (y : R₁ × S₁).1 := rfl

include hf hg in
/-- The second component of `pullbackBaseChange` is `uS` applied to the second component. -/
public theorem pullbackBaseChange_snd (y : f₁.pullback g₁) :
    (pullbackBaseChange f₁ g₁ f₂ g₂ uR uS uT hf hg y : R₂ × S₂).2 =
      uS (y : R₁ × S₁).2 := rfl

include hf hg in
/-- `Deformation.Artin.pullbackBaseChange` is a ring map: both fibre products carry the
componentwise ring structure of the ambient product. -/
public def pullbackBaseChangeHom : f₁.pullback g₁ →+* f₂.pullback g₂ where
  toFun := pullbackBaseChange f₁ g₁ f₂ g₂ uR uS uT hf hg
  map_one' := Subtype.ext (Prod.ext (map_one uR) (map_one uS))
  map_mul' _ _ := Subtype.ext (Prod.ext (map_mul uR _ _) (map_mul uS _ _))
  map_zero' := Subtype.ext (Prod.ext (map_zero uR) (map_zero uS))
  map_add' _ _ := Subtype.ext (Prod.ext (map_add uR _ _) (map_add uS _ _))

include hf hg in
/-- `pullbackBaseChangeHom` applies `pullbackBaseChange`. -/
public theorem pullbackBaseChangeHom_apply (y : f₁.pullback g₁) :
    pullbackBaseChangeHom f₁ g₁ f₂ g₂ uR uS uT hf hg y =
      pullbackBaseChange f₁ g₁ f₂ g₂ uR uS uT hf hg y := rfl

end PullbackBaseChange

section DifferenceBaseChange

universe u

variable {A A' C C' : Type u} [CommRing A] [CommRing A'] [CommRing C] [CommRing C']
  (qA : A' →+* A) (qC : C' →+* C) (f : A →+* C) (f' : A' →+* C')
  (hcomm : ∀ z : A', qC (f' z) = f (qA z))

include hcomm in
/-- **The map on kernels induced by a morphism of square-zero deformation situations.** The
map `f'` of thickened rings carries the kernel of `qA` into the kernel of `qC`. -/
public def kerBaseChange (z : RingHom.ker qA) : RingHom.ker qC := by
  refine ⟨f' (z : A'), ?_⟩
  have hz : qA (z : A') = 0 := z.2
  change qC (f' (z : A')) = 0
  rw [hcomm (z : A'), hz, map_zero]

include hcomm in
/-- The map on kernels is `f'` on the underlying elements. -/
public theorem kerBaseChange_val (z : RingHom.ker qA) :
    (kerBaseChange qA qC f f' hcomm z : C') = f' (z : A') := rfl

include hcomm in
/-- The map on kernels is additive. -/
public theorem kerBaseChange_add (z w : RingHom.ker qA) :
    kerBaseChange qA qC f f' hcomm (z + w) =
      kerBaseChange qA qC f f' hcomm z + kerBaseChange qA qC f f' hcomm w := by
  apply Subtype.ext
  change f' ((z : A') + (w : A')) = f' (z : A') + f' (w : A')
  exact map_add f' _ _

include hcomm in
/-- The map on kernels carries zero to zero. -/
public theorem kerBaseChange_zero :
    kerBaseChange qA qC f f' hcomm 0 = 0 := by
  apply Subtype.ext
  change f' (0 : A') = 0
  exact map_zero f'

include hcomm in
/-- **The map on kernels is semilinear over the ring map.** The action of `a : A` on `I` is
multiplication by any lift of `a` to `A'`, and `f'` carries a lift of `a` to a lift of
`f a`. -/
public theorem kerBaseChange_smul (hqA : Function.Surjective qA)
    (hsqA : RingHom.ker qA ^ 2 = ⊥) (hqC : Function.Surjective qC)
    (hsqC : RingHom.ker qC ^ 2 = ⊥) (a : A) (z : RingHom.ker qA) :
    letI := Stacks.Smooth.kerModule hqA hsqA
    letI := Stacks.Smooth.kerModule hqC hsqC
    kerBaseChange qA qC f f' hcomm (a • z) =
      f a • kerBaseChange qA qC f f' hcomm z := by
  let := Stacks.Smooth.kerModule hqA hsqA
  let := Stacks.Smooth.kerModule hqC hsqC
  -- Multiplication by any lift computes the canonical action of the quotient ring on a
  -- square-zero kernel, elementwise.  Needed here at both `qA` and `qC`.
  have smul_val : ∀ {R R' : Type u} [CommRing R] [CommRing R'] (g : R' →+* R)
      (hg : Function.Surjective g) (hsqg : RingHom.ker g ^ 2 = ⊥) (b : R')
      (w : RingHom.ker g),
      letI := Stacks.Smooth.kerModule hg hsqg
      ((g b • w : RingHom.ker g) : R') = b * (w : R') := by
    intro R R' _ _ g hg hsqg b w
    let := Stacks.Smooth.kerModule hg hsqg
    rw [Stacks.Smooth.kerModule_smul hg hsqg b w]
    rfl
  obtain ⟨a', ha'⟩ := hqA a
  have hA : ((a • z : RingHom.ker qA) : A') = a' * (z : A') := by
    rw [← ha']
    exact smul_val qA hqA hsqA a' z
  have hfa : f a = qC (f' a') := by rw [hcomm a', ha']
  have hC : ((f a • kerBaseChange qA qC f f' hcomm z : RingHom.ker qC) : C') =
      f' a' * (kerBaseChange qA qC f f' hcomm z : C') := by
    rw [hfa]
    exact smul_val qC hqC hsqC (f' a') _
  apply Subtype.ext
  rw [kerBaseChange_val, hA, hC, kerBaseChange_val]
  exact map_mul f' _ _

include hcomm in
/-- **The map on kernels as a coefficient map of Stacks 07YA.** The kernel `I` of the source
deformation situation, as an `A`-module, maps to the restriction of scalars along `f` of the
kernel `J` of the target one — which is the shape the transitions of Stacks 07YA take their
map of coefficients in. -/
public def kerSiteBaseChange (hqA : Function.Surjective qA)
    (hsqA : RingHom.ker qA ^ 2 = ⊥) (hqC : Function.Surjective qC)
    (hsqC : RingHom.ker qC ^ 2 = ⊥) :
    letI := Stacks.Smooth.kerModule hqA hsqA
    letI := Stacks.Smooth.kerModule hqC hsqC
    ModuleCat.of A (RingHom.ker qA) ⟶
      (ModuleCat.restrictScalars f).obj (ModuleCat.of C (RingHom.ker qC)) := by
  let := Stacks.Smooth.kerModule hqA hsqA
  let := Stacks.Smooth.kerModule hqC hsqC
  let : Module A (RingHom.ker qC) := Module.compHom _ f
  exact ModuleCat.ofHom
    { toFun := kerBaseChange qA qC f f' hcomm
      map_add' := kerBaseChange_add qA qC f f' hcomm
      map_smul' := kerBaseChange_smul qA qC f f' hcomm hqA hsqA hqC hsqC }

include hcomm in
/-- `kerSiteBaseChange` applies the map on kernels `kerBaseChange`. -/
public theorem kerSiteBaseChange_apply (hqA : Function.Surjective qA)
    (hsqA : RingHom.ker qA ^ 2 = ⊥) (hqC : Function.Surjective qC)
    (hsqC : RingHom.ker qC ^ 2 = ⊥) (z : RingHom.ker qA) :
    letI := Stacks.Smooth.kerModule hqA hsqA
    letI := Stacks.Smooth.kerModule hqC hsqC
    kerSiteBaseChange qA qC f f' hcomm hqA hsqA hqC hsqC z =
      kerBaseChange qA qC f f' hcomm z := rfl

include hcomm in
/-- **The comparison of the self-fibre products is compatible with the kernel-valued
difference.** The difference of the image of `(a₁, a₂)` is the image of its difference.

This is the identity on which transporting `Deformation.Artin.IsGeometricDifference` along the
ring map rests: the geometric difference glues two lifts over `A' ×_A A'` and reads the
result off through `Deformation.Artin.kerDifference`. -/
public theorem kerDifference_pullbackBaseChange (y : qA.pullback qA) :
    kerDifference qC (pullbackBaseChange qA qA qC qC f' f' f hcomm hcomm y) =
      kerBaseChange qA qC f f' hcomm (kerDifference qA y) := by
  apply Subtype.ext
  change f' y.1.2 - f' y.1.1 = f' (y.1.2 - y.1.1)
  exact (map_sub f' _ _).symm

end DifferenceBaseChange

/-! ### The sections of a self-fibre product are square-zero thickenings -/

section SelfPullbackThickening

universe u

variable {A A' : Type u} [CommRing A] [CommRing A'] (q : A' →+* A)

/-- Two elements of an ideal with zero square multiply to zero. -/
private theorem mul_eq_zero_of_mem_of_sq_eq_bot {R : Type*} [CommRing R] {I : Ideal R}
    (hI : I ^ 2 = ⊥) {x y : R} (hx : x ∈ I) (hy : y ∈ I) : x * y = 0 := by
  have hxy : x * y ∈ I ^ 2 := by simpa [pow_two] using Ideal.mul_mem_mul hx hy
  rw [hI] at hxy
  exact Ideal.mem_bot.mp hxy

/-- **The kernel of the first projection of a self-fibre product has square zero.** Its
elements are the pairs `(0, b)` with `b` in the kernel of `q`, and that kernel has square
zero. -/
public theorem ker_pullbackFst_sq_eq_bot (hsq : RingHom.ker q ^ 2 = ⊥) :
    RingHom.ker (q.pullbackFst q) ^ 2 = ⊥ := by
  rw [pow_two]
  refine le_antisymm (Ideal.mul_le.mpr ?_) bot_le
  intro w hw w' hw'
  have hsnd : ∀ v ∈ RingHom.ker (q.pullbackFst q), (v : A' × A').2 ∈ RingHom.ker q := by
    intro v hv
    have hvq : q (v : A' × A').1 = q (v : A' × A').2 := v.2
    change q (v : A' × A').2 = 0
    rw [← hvq, show (v : A' × A').1 = 0 from hv, map_zero]
  refine Ideal.mem_bot.mpr (Subtype.ext (Prod.ext ?_ ?_))
  · change (w : A' × A').1 * (w' : A' × A').1 = 0
    rw [show (w : A' × A').1 = 0 from hw, zero_mul]
  · change (w : A' × A').2 * (w' : A' × A').2 = 0
    exact mul_eq_zero_of_mem_of_sq_eq_bot hsq (hsnd w hw) (hsnd w' hw')

/-- **The first section of a self-fibre product is surjective on spectra.** The kernel of the
first projection consists of nilpotent elements, so it lies in every prime, and
`Spec A' ⟶ Spec (A' ×_A A')` is surjective.

This is the step that lets the image of a morphism out of `Spec (A' ×_A A')` be read off the
image of its restriction along the section. -/
public theorem surjective_specMap_pullbackFst (hq : Function.Surjective q)
    (hsq : RingHom.ker q ^ 2 = ⊥) :
    Function.Surjective ⇑(Spec.map (CommRingCat.ofHom (q.pullbackFst q))) := by
  have hsurj : Function.Surjective (q.pullbackFst q) :=
    RingHom.surjective_pullbackFst_of_surjective q q hq
  have key : Function.Surjective (PrimeSpectrum.comap (q.pullbackFst q)) := by
    intro z
    have hker : RingHom.ker (q.pullbackFst q) ≤ z.asIdeal := by
      intro w hw
      refine z.isPrime.mem_of_pow_mem 2 ?_
      rw [pow_two, mul_eq_zero_of_mem_of_sq_eq_bot (ker_pullbackFst_sq_eq_bot q hsq) hw hw]
      exact z.asIdeal.zero_mem
    refine ⟨⟨Ideal.map (q.pullbackFst q) z.asIdeal,
      Ideal.map_isPrime_of_surjective hsurj hker⟩, ?_⟩
    apply PrimeSpectrum.ext
    change Ideal.comap (q.pullbackFst q) (Ideal.map (q.pullbackFst q) z.asIdeal) = z.asIdeal
    rw [Ideal.comap_map_of_surjective _ hsurj]
    exact sup_eq_left.mpr hker
  exact key

end SelfPullbackThickening

end Deformation.Artin

end
