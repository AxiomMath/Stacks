module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafInclusion
public import StacksFrontier.AlgebraicGeometry.Thickenings.Infinitesimal

/-!
# The tower of infinitesimal neighbourhoods of an immersion

Let `i : Z ⟶ X` be an immersion of schemes and let `Zₙ` denote its `n`th-order infinitesimal
neighbourhood `Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood`, the closed subscheme of
the canonical open neighbourhood of the image of `i` cut out by `K ^ (n + 1)`, where `K` is the
defining ideal sheaf of the closed-immersion factorization
`AlgebraicGeometry.Scheme.Hom.liftCoborder` of `i`. This file builds the tower

`Z₀ ⟶ Z₁ ⟶ Z₂ ⟶ ⋯`

of successive inclusions and shows that each one is a **first-order** thickening.

## Main definitions

* `Stacks.Thickenings.nthOrderSucc` is the morphism `Zₙ ⟶ Zₙ₊₁`. It is
  `AlgebraicGeometry.Scheme.IdealSheafData.inclusion` for the containment
  `K ^ (n + 2) ≤ K ^ (n + 1)`.

## Main results

* `Stacks.Thickenings.ker_inclusion_pow_eq_bot` and
  `Stacks.Thickenings.isNthOrderThickening_inclusion_of_pow_le` are the general statement the
  order of a stage is read off from: for `K ≤ I` on a scheme `X`, the inclusion of the closed
  subscheme cut out by `I` into the one cut out by `K` has `m`th power of its defining ideal
  sheaf vanishing as soon as `I ^ m ≤ K`.
* `Stacks.Thickenings.nthOrderSucc_isFirstOrderThickening`: **each stage of the tower is a
  first-order thickening of the previous one.** The defining ideal sheaf of `Zₙ ⊆ Zₙ₊₁` is
  `K ^ (n + 1) / K ^ (n + 2)`, whose square lies in `K ^ (2n + 2) / K ^ (n + 2) = 0`.
* `Stacks.Thickenings.nthOrderSucc_nthOrderι`, `Stacks.Thickenings.nthOrderSucc_toBase` and
  `Stacks.Thickenings.nthOrderInclusion_nthOrderSucc`: the tower is compatible with the closed
  immersions into the ambient open subscheme, with the structure morphisms to `X`, and with the
  inclusions of `Z`.
* `Stacks.Thickenings.ker_ideal_nthOrderSucc` and `Stacks.Thickenings.ker_app_nthOrderSucc`
  compute the defining ideal sheaf of a stage on the charts of `Zₙ₊₁`: over an affine open `V`
  of the ambient open subscheme it is the image of `K(V) ^ (n + 1)` in `Γ(V) ⧸ K(V) ^ (n + 2)`.

## Implementation notes

The order of a stage is *not* an instance of
`Stacks.IdealSheaf.isNthOrderThickening_inclusion` of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.InfinitesimalNeighbourhood`, which treats the
inclusion `V(I) ⟶ V(I ^ (n + 1))` of a subscheme into its own `n`th-order neighbourhood and so
produces an `n`th-order thickening. The stages of the tower are the inclusions
`V(K ^ (n + 1)) ⟶ V(K ^ (n + 2))` of *consecutive* neighbourhoods, and these are first-order
thickenings for every `n`: the relevant containment is `(K ^ (n + 1)) ^ 2 ≤ K ^ (n + 2)`, which
holds because `n + 2 ≤ 2n + 2`. `Stacks.Thickenings.ker_inclusion_pow_eq_bot` is therefore
stated for an arbitrary containment `I ^ m ≤ K` rather than for the special shape
`(I ^ (n + 1)) ^ (n + 1) ≤ I`, and both statements are instances of it.

The computation of the defining ideal sheaf of a stage rests on
`Stacks.ClosedImmersion.ker_inclusion_ideal`, which is exactly the statement that the ideal
sheaf of `V(I) ⊆ V(K)` is `I/K` on charts; nothing beyond that is needed, and in particular no
chart-by-chart argument is repeated here.

## References

* [Stacks Project, Tag 04EY](https://stacks.math.columbia.edu/tag/04EY)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Thickenings

/-! ### Powers of a sheaf of ideals -/

variable {X : Scheme.{u}}

/-- The powers of a sheaf of ideals decrease as the exponent grows. The order on
`AlgebraicGeometry.Scheme.IdealSheafData` is the pointwise order on the ideals of sections, so
this is `Ideal.pow_le_pow_right` on each affine chart. -/
theorem idealSheaf_pow_le_pow_right {I : X.IdealSheafData} {m n : ℕ} (h : m ≤ n) :
    I ^ n ≤ I ^ m :=
  Scheme.IdealSheafData.le_def.mpr fun _ ↦ Ideal.pow_le_pow_right h

/-! ### The order of an inclusion of closed subschemes -/

/-- **An inclusion of closed subschemes is a thickening of the order its ideal sheaves
dictate.** Let `K ≤ I` be sheaves of ideals on a scheme `X`, so that the closed subscheme
`V(I)` cut out by `I` is a closed subscheme of `V(K)`, and suppose `I ^ m ≤ K`. Then the `m`th
power of the defining ideal sheaf of `V(I) ⟶ V(K)` vanishes.

The defining ideal sheaf is `I/K` on charts, by
`Stacks.ClosedImmersion.ker_inclusion_ideal`: over an affine open `V ⊆ X` it is the image of
`I(V)` under the chart map of `V(K)`, whose kernel is `K(V)` by
`AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι_app`. Its `m`th power is therefore the
image of `I(V) ^ m ≤ K(V)`, hence zero. -/
theorem ker_inclusion_pow_eq_bot {K I : X.IdealSheafData} (h : K ≤ I) {m : ℕ}
    (hm : I ^ m ≤ K) :
    (Scheme.IdealSheafData.inclusion h).ker ^ m = ⊥ := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun V : X.affineOpens ↦
      (⟨K.subschemeι ⁻¹ᵁ V.1, V.2.preimage K.subschemeι⟩ : K.subscheme.affineOpens))
    (by simpa using congrArg (fun V : X.Opens ↦ K.subschemeι ⁻¹ᵁ V) (iSup_affineOpens_eq_top X))
    fun V ↦ ?_
  have hkerV : RingHom.ker (K.subschemeι.app V.1).hom = K.ideal V := K.ker_subschemeι_app V
  have hmV : I.ideal V ^ m ≤ RingHom.ker (K.subschemeι.app V.1).hom := by
    rw [hkerV]
    exact Scheme.IdealSheafData.le_def.mp hm V
  have hzero : Ideal.map (K.subschemeι.app V.1).hom (I.ideal V ^ m) = ⊥ :=
    le_bot_iff.mp (Ideal.map_le_iff_le_comap.mpr
      (hmV.trans_eq (RingHom.ker_eq_comap_bot _)))
  show ((Scheme.IdealSheafData.inclusion h).ker ^ m).ideal _ = ⊥
  rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Stacks.ClosedImmersion.ker_inclusion_ideal h V, ← Ideal.map_pow, hzero]

/-- **An inclusion of closed subschemes `V(I) ⟶ V(K)` with `I ^ (n + 1) ≤ K` is an `n`th-order
thickening.** The closed immersion is `Stacks.ClosedImmersion.isClosedImmersion_inclusion` and
the vanishing is `Stacks.Thickenings.ker_inclusion_pow_eq_bot`. -/
theorem isNthOrderThickening_inclusion_of_pow_le {K I : X.IdealSheafData} (h : K ≤ I) {n : ℕ}
    (hn : I ^ (n + 1) ≤ K) :
    IsNthOrderThickening n (Scheme.IdealSheafData.inclusion h) :=
  ⟨Stacks.ClosedImmersion.isClosedImmersion_inclusion h, ker_inclusion_pow_eq_bot h hn⟩

/-- **An inclusion of closed subschemes `V(I) ⟶ V(K)` with `I ^ 2 ≤ K` is a first-order
thickening.** -/
theorem isFirstOrderThickening_inclusion_of_sq_le {K I : X.IdealSheafData} (h : K ≤ I)
    (hsq : I ^ 2 ≤ K) :
    IsFirstOrderThickening (Scheme.IdealSheafData.inclusion h) := by
  simpa [IsFirstOrderThickening, IsNthOrderThickening] using
    isNthOrderThickening_inclusion_of_pow_le h (n := 1) (by simpa using hsq)

/-! ### The successive inclusions of the infinitesimal neighbourhoods -/

variable {Z : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- **The `n`th stage of the tower of infinitesimal neighbourhoods**, the inclusion
`Zₙ ⟶ Zₙ₊₁` of the `n`th-order infinitesimal neighbourhood of `Z` in `X` into the
`(n+1)`st-order one.

The two neighbourhoods are cut out by `K ^ (n + 1)` and `K ^ (n + 2)` for `K` the defining ideal
sheaf of the closed-immersion factorization of `i`, and the inclusion is
`AlgebraicGeometry.Scheme.IdealSheafData.inclusion` for the containment
`K ^ (n + 2) ≤ K ^ (n + 1)`. -/
def nthOrderSucc (n : ℕ) :
    nthOrderInfinitesimalNeighbourhood i n ⟶ nthOrderInfinitesimalNeighbourhood i (n + 1) :=
  Scheme.IdealSheafData.inclusion
    (idealSheaf_pow_le_pow_right (I := i.liftCoborder.ker) (Nat.le_succ (n + 1)))

/-- The `n`th stage of the tower is the inclusion of closed subschemes attached to the
containment `K ^ (n + 2) ≤ K ^ (n + 1)`. -/
theorem nthOrderSucc_eq (n : ℕ) :
    nthOrderSucc i n = Scheme.IdealSheafData.inclusion
      (idealSheaf_pow_le_pow_right (I := i.liftCoborder.ker) (Nat.le_succ (n + 1))) :=
  rfl

/-- Each stage of the tower of infinitesimal neighbourhoods is a closed immersion. -/
instance isClosedImmersion_nthOrderSucc (n : ℕ) : IsClosedImmersion (nthOrderSucc i n) := by
  rw [nthOrderSucc_eq]
  infer_instance

/-- The stage `Zₙ ⟶ Zₙ₊₁`, followed by the closed immersion of `Zₙ₊₁` into the ambient open
subscheme, is the closed immersion of `Zₙ`. -/
@[reassoc (attr := simp)]
theorem nthOrderSucc_nthOrderι (n : ℕ) :
    nthOrderSucc i n ≫ nthOrderι i (n + 1) = nthOrderι i n :=
  Scheme.IdealSheafData.inclusion_subschemeι _

/-- The stage `Zₙ ⟶ Zₙ₊₁` is compatible with the structure morphisms to `X`. -/
@[reassoc (attr := simp)]
theorem nthOrderSucc_toBase (n : ℕ) :
    nthOrderSucc i n ≫ nthOrderToBase i (n + 1) = nthOrderToBase i n := by
  rw [nthOrderToBase_eq, nthOrderToBase_eq, ← Category.assoc, nthOrderSucc_nthOrderι]

/-- The inclusion of `Z` into its `n`th-order infinitesimal neighbourhood, followed by the stage
`Zₙ ⟶ Zₙ₊₁`, is the inclusion of `Z` into its `(n+1)`st-order neighbourhood: both are
factorizations of `i.liftCoborder` through the closed immersion of `Zₙ₊₁`, which is a
monomorphism. -/
@[reassoc (attr := simp)]
theorem nthOrderInclusion_nthOrderSucc (n : ℕ) :
    nthOrderInclusion i n ≫ nthOrderSucc i n = nthOrderInclusion i (n + 1) := by
  rw [← cancel_mono (nthOrderι i (n + 1)), Category.assoc, nthOrderSucc_nthOrderι,
    nthOrderInclusion_nthOrderι, nthOrderInclusion_nthOrderι]

/-- **Each stage of the tower of infinitesimal neighbourhoods is a first-order thickening of the
previous one.** The defining ideal sheaf of `Zₙ ⊆ Zₙ₊₁` is `K ^ (n + 1) / K ^ (n + 2)`, and its
square is the image of `K ^ (2n + 2)`, which lies in `K ^ (n + 2)` because `n + 2 ≤ 2n + 2` and
so vanishes in `Γ(Zₙ₊₁)`.

This is what makes the infinitesimal neighbourhoods of `Z` in `X` a tower of first-order
thickenings, as the proof of [Stacks Project, Tag 0F2D] uses. Note that the order is `1` for
every `n`, in contrast to the order `n` of the inclusion `Z ⟶ Zₙ` recorded by
`Stacks.Thickenings.nthOrderInclusion_isNthOrderThickening`. -/
theorem nthOrderSucc_isFirstOrderThickening (n : ℕ) :
    IsFirstOrderThickening (nthOrderSucc i n) := by
  rw [nthOrderSucc_eq]
  refine isFirstOrderThickening_inclusion_of_sq_le _ ?_
  rw [← pow_mul]
  exact idealSheaf_pow_le_pow_right (by omega)

/-- Each stage of the tower is a thickening: consecutive infinitesimal neighbourhoods have the
same underlying topological space. -/
theorem nthOrderSucc_isThickening (n : ℕ) : IsThickening (nthOrderSucc i n) :=
  (nthOrderSucc_isFirstOrderThickening i n).isThickening

/-! ### The defining ideal sheaf of a stage -/

/-- **The defining ideal sheaf of `Zₙ ⊆ Zₙ₊₁` is `K ^ (n + 1) / K ^ (n + 2)`.** On the chart of
`Zₙ₊₁` over an affine open `V` of the ambient open subscheme, the ideal that
`AlgebraicGeometry.Scheme.Hom.ker` assigns to the stage `Zₙ ⟶ Zₙ₊₁` is the image of
`K(V) ^ (n + 1)` under the chart map, whose kernel is `K(V) ^ (n + 2)` by
`Stacks.Thickenings.ker_app_nthOrderι`.

This is `Stacks.ClosedImmersion.ker_inclusion_ideal` for the containment
`K ^ (n + 2) ≤ K ^ (n + 1)`. -/
theorem ker_ideal_nthOrderSucc (n : ℕ) (V : i.coborderRange.toScheme.affineOpens) :
    (nthOrderSucc i n).ker.ideal ⟨nthOrderι i (n + 1) ⁻¹ᵁ V.1, V.2.preimage _⟩ =
      Ideal.map ((nthOrderι i (n + 1)).app V.1).hom (i.liftCoborder.ker.ideal V ^ (n + 1)) := by
  rw [nthOrderSucc_eq, Stacks.ClosedImmersion.ker_inclusion_ideal]
  rfl

/-- **The defining ideal sheaf of `Zₙ ⊆ Zₙ₊₁`, as a kernel on sections.** The section map of the
stage `Zₙ ⟶ Zₙ₊₁` over a chart of `Zₙ₊₁` has the image of `K(V) ^ (n + 1)` as its kernel. -/
theorem ker_app_nthOrderSucc (n : ℕ) (V : i.coborderRange.toScheme.affineOpens) :
    RingHom.ker ((nthOrderSucc i n).app (nthOrderι i (n + 1) ⁻¹ᵁ V.1)).hom =
      Ideal.map ((nthOrderι i (n + 1)).app V.1).hom (i.liftCoborder.ker.ideal V ^ (n + 1)) :=
  (Scheme.Hom.ker_apply (nthOrderSucc i n)
    ⟨nthOrderι i (n + 1) ⁻¹ᵁ V.1, V.2.preimage _⟩).symm.trans (ker_ideal_nthOrderSucc i n V)

end Stacks.Thickenings

end
