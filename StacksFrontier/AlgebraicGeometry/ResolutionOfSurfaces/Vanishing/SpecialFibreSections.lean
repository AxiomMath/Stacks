module

public import StacksFrontier.AlgebraicGeometry.Properties.NormalCodimensionOne
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.ModificationATorsion
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.BaseScalarTriangle
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.PolarFunctions
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.PuncturedBaseCohomology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomSlice
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ComponentStalkKernel
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ConormalDegree
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.SpecialFiberComponentDimension

/-!
# No section of `𝒪_X/a𝒪_X` is supported in the special fibre

In the vanishing situation of [Stacks, Tag 0AX8] — a two-dimensional Noetherian normal local
domain `A` with closed point `s` and punctured spectrum `U`, and a modification
`f : X ⟶ Spec(A)` — let `X` be normal and let `a ∈ A` be nonzero. This file proves that a global
section of `𝒪_X/a𝒪_X` whose restriction to `f⁻¹(U)` vanishes is zero. Equivalently, the local
cohomology `H¹_{X_s}(X, 𝒪_X)` has no `a`-torsion. This is the input the proof of
[Stacks, Tag 0AXC] needs, and it is proved here directly rather than deduced from
[Stacks, Tag 0AXB], with no Nagata hypothesis.

## Main results

* `AlgebraicGeometry.VanishingSituation.mem_stalkRange_of_liftClasses`: the core. Elements of
  the function field attached compatibly to the points of `X`, well defined up to the local
  rings and zero off the special fibre, are regular everywhere.
* `AlgebraicGeometry.VanishingSituation.eq_zero_of_res_preimagePuncturedSpectrum_eq_zero`: the
  vanishing for sections of `𝒪_X/a𝒪_X`.

## The argument

Near each point a section `σ` of `𝒪_X/a𝒪_X` is the image of a function `g`, and `g/a` is an
element of the function field determined up to the local ring. If `σ` vanishes on `f⁻¹(U)`,
these elements can only have poles along the components `C_1, …, C_r` of the special fibre, and
by algebraic Hartogs
(`AlgebraicGeometry.Scheme.mem_range_algebraMap_stalk_of_forall_coheight_eq_one`)
it suffices to rule those out. A pole along some `C_k` forces `f` not to be an isomorphism, so
every `C_k` is a curve, and the element `c ∈ 𝔪` of [Stacks, Tag 0AX9] is available. Let `n_k` be
the pole order along `C_k`, let `m_k ≥ 1` be the order of vanishing of `c` along `C_k`, and take
`i` maximizing `n_k / m_k`. Then the local functions `(g/a)^{m_i} c^{n_i}` are regular, are units
at the generic point of `C_i`, and agree on `C_i`. So they define a nonzero global function on
`C_i`, which is integral and proper over the residue field, so that function is a unit. But at
the closed point `x_i ∈ C_i` of [Stacks, Tag 0AX9], `c` has a factor vanishing at `x_i` and not
along `C_i`, so the function vanishes at `x_i`: a contradiction. This is the argument by which
Lipman proves the vanishing of `H¹_{X_s}(𝒪_X)`.

## References

* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
* [Stacks Project, Tag 0AX9](https://stacks.math.columbia.edu/tag/0AX9)
* [Stacks Project, Tag 0AXB](https://stacks.math.columbia.edu/tag/0AXB)
* [Stacks Project, Tag 0AXC](https://stacks.math.columbia.edu/tag/0AXC)
* J. Lipman, *Rational singularities with applications to algebraic surfaces and unique
  factorization*, Publ. Math. IHÉS 36 (1969), §2.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite Order
open scoped WithZero

universe u

namespace AlgebraicGeometry

/-! ### Germs of elements of the base ring -/

section BaseRingToStalk

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- On an irreducible scheme the image in the function field of the germ of an element of the
base ring does not depend on the point. -/
theorem algebraMap_baseRingToStalk_eq_of_irreducibleSpace [IrreducibleSpace X] (x y : X) (a : A) :
    algebraMap (X.presheaf.stalk x) X.functionField (baseRingToStalk f x a) =
      algebraMap (X.presheaf.stalk y) X.functionField (baseRingToStalk f y a) := by
  have hx := Scheme.algebraMap_stalkSpecializes (genericPoint_specializes x)
    (baseRingToStalk f x a)
  have hy := Scheme.algebraMap_stalkSpecializes (genericPoint_specializes y)
    (baseRingToStalk f y a)
  rw [stalkSpecializes_baseRingToStalk] at hx hy
  exact hx.symm.trans hy

/-- The germ of the global function attached to an element of the base ring is the germ of that
element. -/
theorem germ_baseSection (x : X) (a : A) :
    X.presheaf.germ ⊤ x trivial (baseSection X f a) = baseRingToStalk f x a :=
  (Scheme.Hom.germ_stalkMap_apply f ⊤ x trivial ((Scheme.ΓSpecIso (.of A)).inv a)).symm

/-- The germ of an element of a prime of the base, at a point lying over that prime, lies in the
maximal ideal of the local ring. -/
theorem baseRingToStalk_mem_maximalIdeal_of_mem {x : X} {a : A} (ha : a ∈ (f x).asIdeal) :
    baseRingToStalk f x a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  let p : PrimeSpectrum A := f x
  let : Algebra A ((Spec.structureSheaf A).presheaf.stalk p) := StructureSheaf.stalkAlgebra A p
  have := StructureSheaf.IsLocalization.to_stalk A p
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact fun hu => (IsLocalization.AtPrime.isUnit_to_map_iff
    ((Spec.structureSheaf A).presheaf.stalk p) p.asIdeal a).mp
    ((isUnit_map_iff (f.stalkMap x).hom _).mp hu) ha

/-- On an integral scheme the image in the function field of the germ of an element of the base
ring is the image of the corresponding global function. -/
theorem algebraMap_baseRingToStalk_eq_germToFunctionField [IsIntegral X] (x : X) (a : A) :
    haveI : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
    algebraMap (X.presheaf.stalk x) X.functionField (baseRingToStalk f x a) =
      X.germToFunctionField ⊤ (baseSection X f a) := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  rw [← germ_baseSection]
  exact Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := ⊤) (x := x) trivial
    (baseSection X f a)

end BaseRingToStalk

/-! ### Bookkeeping with a discrete valuation -/

section ValuationBookkeeping

variable {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰)

/-- If `v u ≤ exp n`, `v γ = exp (-m)` and `n M ≤ N m`, then `v (u^M γ^N) ≤ 1`. -/
private theorem valuation_pow_mul_pow_le_one {u γ : K} {n m M N : ℕ}
    (hu : v u ≤ WithZero.exp (n : ℤ)) (hγ : v γ = WithZero.exp (-(m : ℤ)))
    (hr : n * M ≤ N * m) : v (u ^ M * γ ^ N) ≤ 1 := by
  rw [map_mul, map_pow, map_pow, hγ]
  calc v u ^ M * WithZero.exp (-(m : ℤ)) ^ N
      ≤ WithZero.exp (n : ℤ) ^ M * WithZero.exp (-(m : ℤ)) ^ N := by
        gcongr
        exact zero_le
    _ = WithZero.exp ((n * M : ℕ) - (N * m : ℕ) : ℤ) := by
        rw [← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add]
        congr 1
        push_cast
        ring
    _ ≤ 1 := by
        rw [← WithZero.exp_zero, WithZero.exp_le_exp]
        have : ((n * M : ℕ) : ℤ) ≤ ((N * m : ℕ) : ℤ) := by exact_mod_cast hr
        linarith

/-- If `v u = exp n` and `v γ = exp (-m)`, then `v (u^m γ^n) = 1`. -/
private theorem valuation_pow_mul_pow_eq_one {u γ : K} {n m : ℕ}
    (hu : v u = WithZero.exp (n : ℤ)) (hγ : v γ = WithZero.exp (-(m : ℤ))) :
    v (u ^ m * γ ^ n) = 1 := by
  rw [map_mul, map_pow, map_pow, hu, hγ, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul,
    ← WithZero.exp_add, ← WithZero.exp_zero]
  congr 1
  simp only [nsmul_eq_mul]
  ring

/-- If `v u = v u' = exp n` with `n > 0`, `v (u - u') ≤ 1` and `v γ = exp (-m)`, then
`v (u^m γ^n - u'^m γ^n) < 1`. -/
private theorem valuation_sub_pow_mul_pow_lt_one {u u' γ : K} {n m : ℕ} (hn : 0 < n)
    (hu : v u = WithZero.exp (n : ℤ)) (hu' : v u' = WithZero.exp (n : ℤ))
    (hd : v (u - u') ≤ 1) (hγ : v γ = WithZero.exp (-(m : ℤ))) :
    v (u ^ m * γ ^ n - u' ^ m * γ ^ n) < 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hfac : u ^ m * γ ^ n - u' ^ m * γ ^ n =
      γ ^ n * ((u - u') * ∑ j ∈ Finset.range m, u ^ j * u' ^ (m - 1 - j)) := by
    rw [mul_comm (u - u'), geom_sum₂_mul]
    ring
  have hsum : v (∑ j ∈ Finset.range m, u ^ j * u' ^ (m - 1 - j)) ≤
      WithZero.exp (((m - 1 : ℕ) * n : ℕ) : ℤ) := by
    refine Valuation.map_sum_le v fun j hj => ?_
    have hj' : j ≤ m - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.mp hj)
    rw [map_mul, map_pow, map_pow, hu, hu', ← WithZero.exp_nsmul, ← WithZero.exp_nsmul,
      ← WithZero.exp_add, WithZero.exp_le_exp]
    simp only [nsmul_eq_mul]
    push_cast [Nat.cast_sub hj', Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hm.ne')]
    ring_nf
    rfl
  rw [hfac, map_mul, map_mul, map_pow, hγ]
  calc WithZero.exp (-(m : ℤ)) ^ n * (v (u - u') *
        v (∑ j ∈ Finset.range m, u ^ j * u' ^ (m - 1 - j)))
      ≤ WithZero.exp (-(m : ℤ)) ^ n * (1 * WithZero.exp (((m - 1 : ℕ) * n : ℕ) : ℤ)) := by
        gcongr
    _ = WithZero.exp (-(n : ℤ)) := by
        rw [one_mul, ← WithZero.exp_nsmul, ← WithZero.exp_add]
        congr 1
        simp only [nsmul_eq_mul]
        push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hm.ne')]
        ring
    _ < 1 := by
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
        exact_mod_cast neg_neg_of_pos (Int.natCast_pos.mpr hn)

/-- If `v u₀ = exp n` with `n > 0` and `v (u - u₀) ≤ 1`, then `v u = exp n`. -/
private theorem valuation_eq_of_sub_le_one {u u₀ : K} {n : ℕ} (hn : 0 < n)
    (hu₀ : v u₀ = WithZero.exp (n : ℤ)) (hd : v (u - u₀) ≤ 1) :
    v u = WithZero.exp (n : ℤ) := by
  have hlt : v (u - u₀) < v u₀ := by
    rw [hu₀]
    refine lt_of_le_of_lt hd ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    exact_mod_cast hn
  have := Valuation.map_add_eq_of_lt_left v hlt
  rw [add_sub_cancel] at this
  rw [this, hu₀]

/-- `v u ≤ exp ((log (v u)).toNat)`. -/
private theorem valuation_le_exp_toNat_log (u : K) :
    v u ≤ WithZero.exp ((WithZero.log (v u)).toNat : ℤ) := by
  by_cases h0 : v u = 0
  · exact h0 ▸ zero_le
  · calc v u = WithZero.exp (WithZero.log (v u)) := (WithZero.exp_log h0).symm
      _ ≤ _ := WithZero.exp_le_exp.mpr (Int.self_le_toNat _)

end ValuationBookkeeping

namespace VanishingSituation

variable (V : VanishingSituation.{u})

/-! ### The components of the special fibre as subsets of `X` -/

/-- The generic point of the `k`-th component of the special fibre, read in `X` through the
closed immersion of that component with its reduced induced structure. -/
noncomputable def componentPoint (k : Fin V.numberOfComponents) : V.X :=
  componentι V k (genericPoint (componentScheme V k))

/-- The image in `X` of the `k`-th component of the special fibre is `componentInSource V k`. -/
theorem range_componentι (k : Fin V.numberOfComponents) :
    Set.range (componentι V k) = componentInSource V k :=
  (Scheme.IdealSheafData.range_subschemeι _).trans (coe_support_componentIdeal V k)

/-- The generic point of the `k`-th component lies in that component. -/
theorem componentPoint_mem (k : Fin V.numberOfComponents) :
    componentPoint V k ∈ componentInSource V k := by
  rw [← range_componentι]
  exact ⟨_, rfl⟩

/-- The generic point of the `k`-th component specializes to every point of that component. -/
theorem componentPoint_specializes {k : Fin V.numberOfComponents} {y : V.X}
    (hy : y ∈ componentInSource V k) : componentPoint V k ⤳ y := by
  rw [← range_componentι] at hy
  obtain ⟨y', rfl⟩ := hy
  exact (genericPoint_specializes y').map (componentι V k).continuous

/-- A specialization of the generic point of the `k`-th component lies in that component. -/
theorem mem_componentInSource_of_specializes {k : Fin V.numberOfComponents} {x : V.X}
    (h : componentPoint V k ⤳ x) : x ∈ componentInSource V k :=
  h.mem_closed (isClosed_componentInSource V k) (componentPoint_mem V k)

/-- Every point of a component of the special fibre maps to the closed point of the base. -/
theorem apply_eq_closedPoint_of_mem {k : Fin V.numberOfComponents} {y : V.X}
    (hy : y ∈ componentInSource V k) : V.f y = V.closedPoint := by
  obtain ⟨z, -, rfl⟩ := hy
  change V.f.fiberι V.closedPoint z ∈ V.f ⁻¹' {V.closedPoint}
  rw [← Scheme.Hom.range_fiberι]
  exact ⟨z, rfl⟩

/-- The generic point of a component of the special fibre is not the generic point of `X`. -/
theorem componentPoint_ne_genericPoint (k : Fin V.numberOfComponents) :
    componentPoint V k ≠ genericPoint V.X := by
  intro h
  have h1 : V.f (componentPoint V k) = V.closedPoint :=
    V.apply_eq_closedPoint_of_mem (componentPoint_mem V k)
  rw [h, IsBirational.genericPoint_eq V.f V.modification.isBirational] at h1
  exact V.genericPoint_base_ne_closedPoint h1

/-- **A point of codimension one of `X` lying in the special fibre is the generic point of a
component.** It lies in some component, whose generic point specializes to it; were the two
different, the chain through the generic point of `X` would give it codimension at least two. -/
theorem exists_eq_componentPoint {y : V.X} (hy : V.f y = V.closedPoint)
    (hy1 : coheight y = 1) : ∃ k : Fin V.numberOfComponents, y = componentPoint V k := by
  obtain ⟨k, hk⟩ := V.exists_mem_componentInSource
    (by rwa [Scheme.Hom.range_fiberι])
  refine ⟨k, ?_⟩
  by_contra hne
  have hs := componentPoint_specializes V hk
  have hlt1 : y < componentPoint V k :=
    lt_iff_le_not_ge.mpr ⟨(Scheme.le_iff_specializes).mpr hs,
      fun h' => hne (((Scheme.le_iff_specializes).mp h').antisymm hs).eq⟩
  have hη := genericPoint_specializes (componentPoint V k)
  have hlt2 : componentPoint V k < genericPoint V.X :=
    lt_iff_le_not_ge.mpr ⟨(Scheme.le_iff_specializes).mpr hη,
      fun h' => componentPoint_ne_genericPoint V k
        (((Scheme.le_iff_specializes).mp h').antisymm hη).eq⟩
  have h1 := coheight_add_one_le hlt1
  have h2 := coheight_add_one_le hlt2
  rw [hy1] at h1
  have h3 : (1 : ℕ∞) ≤ coheight (componentPoint V k) := le_trans le_add_self h2
  have h5 : (1 : ℕ∞) + 1 ≤ coheight (componentPoint V k) + 1 := by gcongr
  have h4 : (1 : ℕ∞) + 1 ≤ 1 := le_trans h5 h1
  norm_num at h4

/-- The generic point of a component, read through the closed immersion, is the image of the
generic point of the component of the fibre. -/
theorem componentPoint_eq_componentGenericPoint (k : Fin V.numberOfComponents) :
    componentPoint V k = componentGenericPoint V k := by
  have hmem : componentGenericPoint V k ∈ componentInSource V k :=
    ⟨_, (componentFiberGenericPoint_spec V k).mem, rfl⟩
  have h1 : componentPoint V k ⤳ componentGenericPoint V k := componentPoint_specializes V hmem
  obtain ⟨z, hz, hzeq⟩ := componentPoint_mem V k
  have h2 : componentGenericPoint V k ⤳ componentPoint V k := by
    rw [← hzeq]
    exact ((componentFiberGenericPoint_spec V k).specializes hz).map
      (V.f.fiberι V.closedPoint).continuous
  exact (h1.antisymm h2).eq

/-- Under the dimension-one observation, the generic point of a component has codimension one. -/
theorem coheight_componentPoint
    (hdim : ∀ i : Fin V.numberOfComponents, topologicalKrullDim (V.component i) = 1)
    (k : Fin V.numberOfComponents) : coheight (componentPoint V k) = 1 := by
  rw [componentPoint_eq_componentGenericPoint]
  exact coheight_componentGenericPoint_eq_one V hdim k

/-- An element of the maximal ideal at the generic point of a component vanishes in the function
field of the component. -/
theorem stalkMap_genericPoint_eq_zero_of_mem_maximalIdeal {k : Fin V.numberOfComponents}
    {a : V.X.presheaf.stalk (componentPoint V k)}
    (ha : a ∈ IsLocalRing.maximalIdeal (V.X.presheaf.stalk (componentPoint V k))) :
    (componentι V k).stalkMap (genericPoint (componentScheme V k)) a = 0 := by
  by_contra hne
  exact (IsLocalRing.mem_maximalIdeal _).mp
    (map_nonunit ((componentι V k).stalkMap (genericPoint (componentScheme V k))).hom _ ha)
    (isUnit_iff_ne_zero (G₀ := (componentScheme V k).functionField).mpr hne)

/-- An element of the local ring at a point of a component whose image in the local ring of the
component is nonzero does not vanish at the generic point of the component. -/
theorem stalkSpecializes_notMem_maximalIdeal {k : Fin V.numberOfComponents}
    (y₀ : componentScheme V k) (g : V.X.presheaf.stalk (componentι V k y₀))
    (hg : (componentι V k).stalkMap y₀ g ≠ 0) :
    V.X.presheaf.stalkSpecializes
        ((componentι V k).base.hom.map_specializes (genericPoint_specializes y₀)) g ∉
      IsLocalRing.maximalIdeal (V.X.presheaf.stalk (componentPoint V k)) := by
  intro hm
  have key := (componentι V k).stalkSpecializes_stalkMap_apply _ y₀
    (genericPoint_specializes y₀) g
  exact hg (Scheme.stalkSpecializes_injective (genericPoint_specializes y₀)
    ((key.symm.trans (V.stalkMap_genericPoint_eq_zero_of_mem_maximalIdeal hm)).trans
      (map_zero _).symm))

/-- If `f` is an isomorphism no point of the special fibre has codimension one: the closed point
of the base has codimension two. -/
theorem coheight_ne_one_of_isIso [IsIso V.f] {y : V.X} (hy : V.f y = V.closedPoint) :
    coheight y ≠ 1 := by
  rw [← coheight_eq_of_isOpenImmersion V.f (x := y), hy]
  intro h
  have hh : (IsLocalRing.maximalIdeal V.A).height = 1 := by
    rw [show IsLocalRing.maximalIdeal V.A = (V.closedPoint : V.base).asIdeal from rfl,
      idealHeight_eq_coheight, h]
  have h2 : ((1 : ℕ∞) : WithBot ℕ∞) = 2 := by
    rw [← hh, IsLocalRing.maximalIdeal_height_eq_ringKrullDim, V.dimension_two]
  simp at h2

/-! ### No poles along the special fibre -/

section NoPoles

variable [IsNormal V.X]

/-- The local ring of `X` at a point, as a subring of the function field. -/
noncomputable abbrev stalkRange (x : V.X) : Subring V.X.functionField :=
  (algebraMap (V.X.presheaf.stalk x) V.X.functionField).range

omit [IsNormal V.X] in
/-- The image in the function field of a nonzero element of the base is nonzero. -/
theorem germToFunctionField_baseSection_ne_zero [Nonempty (⊤ : V.X.Opens)] {a : V.A}
    (ha : a ≠ 0) : V.X.germToFunctionField ⊤ (baseSection V.X V.f a) ≠ 0 := fun h0 =>
  baseSection_ne_zero_of_isModification V.X V.f V.modification ha
    (V.X.germToFunctionField_injective ⊤ (h0.trans (map_zero _).symm))

/-- **The heart of the vanishing of sections of `𝒪_X/a𝒪_X` supported in the special fibre.**

Suppose that to each point `x` of `X` a nonempty set `T x` of elements of the function field is
attached, such that two elements of `T x` differ by an element of `𝒪_{X, x}`, each element of
`T x` lies in `T z` for all `z` in a neighbourhood of `x`, and `0 ∈ T x` when `x` does not lie
over the closed point. Then every element of `T x` lies in `𝒪_{X, x}`.

(The application: `T x` is the set of `g/a` for `g` a local lift at `x` of a section of
`𝒪_X/a𝒪_X` vanishing on `f⁻¹(U)`.)

By algebraic Hartogs it is enough to see that there is no pole at the generic point `ξ_k` of a
component `C_k` of the special fibre. If there were, let `n_k ≥ 0` be the pole order of the
elements of `T ξ_k` and let `m_k ≥ 1` be the order of vanishing along `C_k` of the element `c`
of [Stacks, Tag 0AX9], and pick `i` maximizing `n_k / m_k`, so `n_i > 0`. For `u ∈ T x` the
function `h = u^{m_i} c^{n_i}` is regular at `x`, again by Hartogs, and a unit at `ξ_i`, and its
restrictions to `C_i` glue to a nonzero global function on `C_i`. That function vanishes at the
closed point `x_i` of [Stacks, Tag 0AX9], where `c` has a factor vanishing at `x_i` but not along
`C_i`. Since `C_i` is an integral scheme proper over the residue field, its global functions form
a field, which is a contradiction. -/
theorem mem_stalkRange_of_liftClasses (T : V.X → Set V.X.functionField)
    (h1 : ∀ x, (T x).Nonempty)
    (h2 : ∀ x u u', u ∈ T x → u' ∈ T x → u - u' ∈ V.stalkRange x)
    (h3 : ∀ x u, u ∈ T x → ∃ N : V.X.Opens, x ∈ N ∧ ∀ z ∈ N, u ∈ T z)
    (h4 : ∀ x, V.f x ≠ V.closedPoint → (0 : V.X.functionField) ∈ T x)
    (x : V.X) (u : V.X.functionField) (hu : u ∈ T x) : u ∈ V.stalkRange x := by
  classical
  have h3' : ∀ {x y : V.X} {u : V.X.functionField}, y ⤳ x → u ∈ T x → u ∈ T y :=
    fun {x y u} hyx hu => by
      obtain ⟨N, hxN, hN⟩ := h3 x u hu
      exact hN y (hyx.mem_open N.isOpen hxN)
  by_contra hux
  have hoff : ∀ y u, V.f y ≠ V.closedPoint → u ∈ T y → u ∈ V.stalkRange y := fun y u hy hu => by
    simpa using h2 y u 0 hu (h4 y hy)
  -- a pole at `x` comes from a pole at the generic point of a component
  obtain ⟨y, hy1, hyx, huy⟩ : ∃ y, coheight y = 1 ∧ y ⤳ x ∧ u ∉ V.stalkRange y := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact hux (Scheme.mem_range_algebraMap_stalk_of_forall_coheight_eq_one x hcon)
  have hfy : V.f y = V.closedPoint := by
    by_contra hne
    exact huy (hoff y u hne (h3' hyx hu))
  have hnotiso : ¬ IsIso V.f := fun _ => V.coheight_ne_one_of_isIso hfy hy1
  obtain ⟨k₀, rfl⟩ := V.exists_eq_componentPoint hfy hy1
  have hdim := V.topologicalKrullDim_component_eq_one_of_not_isIso hnotiso
  have hP := V.coheight_componentPoint hdim
  obtain ⟨c, hc0, hcm, hfac⟩ := V.exists_ne_zero_mem_maximalIdeal_factorization hdim
  have : Nonempty (⊤ : V.X.Opens) := ⟨⟨x, trivial⟩⟩
  -- the image `γ` of `c` in the function field
  set γ : V.X.functionField := V.X.germToFunctionField ⊤ (baseSection V.X V.f c) with hγdef
  have hγ : ∀ z : V.X, algebraMap (V.X.presheaf.stalk z) V.X.functionField
      (baseRingToStalk V.f z c) = γ := fun z =>
    algebraMap_baseRingToStalk_eq_germToFunctionField V.f z c
  have hγ0 : γ ≠ 0 := V.germToFunctionField_baseSection_ne_zero hc0
  -- the valuations along the components, and the orders `m k` of `c`
  set v : Fin V.numberOfComponents → Valuation V.X.functionField ℤᵐ⁰ :=
    fun k => Scheme.valuationAt (componentPoint V k) (hP k) with hvdef
  set m : Fin V.numberOfComponents → ℕ := fun k => (-WithZero.log (v k γ)).toNat with hmdef
  have hvγlt : ∀ k, v k γ < 1 := fun k => by
    rw [← hγ (componentPoint V k)]
    refine (Scheme.valuationAt_algebraMap_lt_one_iff (hP k) _).mpr ?_
    refine baseRingToStalk_mem_maximalIdeal_of_mem V.f ?_
    rw [V.apply_eq_closedPoint_of_mem (componentPoint_mem V k)]
    exact hcm
  have hvγ0 : ∀ k, v k γ ≠ 0 := fun k => (Valuation.ne_zero_iff _).mpr hγ0
  have hlog : ∀ k, WithZero.log (v k γ) < 0 := fun k => by
    have h := hvγlt k
    rwa [← WithZero.exp_log (hvγ0 k), ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
  have hvγ : ∀ k, v k γ = WithZero.exp (-(m k : ℤ)) := fun k => by
    rw [hmdef]
    dsimp only
    rw [Int.toNat_of_nonneg (by linarith [hlog k]), neg_neg, WithZero.exp_log (hvγ0 k)]
  have hmpos : ∀ k, 0 < m k := fun k => by
    have := hlog k
    simp only [hmdef]
    omega
  -- the pole orders `n k`, read off a chosen element `u₀ k` of `T ξ_k`
  set u₀ : Fin V.numberOfComponents → V.X.functionField :=
    fun k => (h1 (componentPoint V k)).some with hu₀def
  have hu₀ : ∀ k, u₀ k ∈ T (componentPoint V k) := fun k => (h1 (componentPoint V k)).some_mem
  set n : Fin V.numberOfComponents → ℕ :=
    fun k => (WithZero.log (v k (u₀ k))).toNat with hndef
  have hdv : ∀ k z z' w w', componentPoint V k ⤳ z → componentPoint V k ⤳ z' → w ∈ T z →
      w' ∈ T z' → v k (w - w') ≤ 1 := fun k z z' w w' hz hz' hw hw' =>
    (Scheme.valuationAt_le_one_iff (hP k) _).mpr (h2 _ _ _ (h3' hz hw) (h3' hz' hw'))
  have hbound : ∀ k z w, componentPoint V k ⤳ z → w ∈ T z →
      v k w ≤ WithZero.exp (n k : ℤ) := fun k z w hkz hw => by
    have hd : v k (w - u₀ k) ≤ 1 := hdv k z _ w _ hkz (specializes_refl _) hw (hu₀ k)
    have h0 : v k (u₀ k) ≤ WithZero.exp (n k : ℤ) := valuation_le_exp_toNat_log (v k) (u₀ k)
    have h1' : (1 : ℤᵐ⁰) ≤ WithZero.exp (n k : ℤ) := by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      exact_mod_cast Nat.zero_le _
    have := Valuation.map_add_le (v k) h0 (hd.trans h1')
    rwa [add_sub_cancel] at this
  have hpole : ∀ k, 0 < n k → v k (u₀ k) = WithZero.exp (n k : ℤ) := fun k hk => by
    have hpos : 0 < WithZero.log (v k (u₀ k)) := by
      simp only [hndef] at hk; omega
    have hne : v k (u₀ k) ≠ 0 := fun h0 => by
      rw [h0, WithZero.log_zero] at hpos
      exact lt_irrefl _ hpos
    simp only [hndef]
    rw [Int.toNat_of_nonneg hpos.le, WithZero.exp_log hne]
  have hn₀ : 0 < n k₀ := by
    by_contra h0
    have h0' : n k₀ = 0 := by omega
    have hle := hbound k₀ _ u (specializes_refl _) (h3' hyx hu)
    rw [h0', Nat.cast_zero, WithZero.exp_zero] at hle
    exact huy ((Scheme.valuationAt_le_one_iff (hP k₀) u).mp hle)
  -- the component maximizing `n k / m k`
  obtain ⟨i, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun k => (n k : ℚ) / m k) ⟨k₀, Finset.mem_univ _⟩
  have hmposQ : ∀ k, (0 : ℚ) < m k := fun k => by exact_mod_cast hmpos k
  have hni : 0 < n i := by
    have h := hmax k₀ (Finset.mem_univ _)
    have hpos : (0 : ℚ) < n k₀ / m k₀ := div_pos (by exact_mod_cast hn₀) (hmposQ k₀)
    by_contra h0
    have h0' : n i = 0 := by omega
    rw [h0', Nat.cast_zero, zero_div] at h
    linarith
  have hcross : ∀ k, n k * m i ≤ n i * m k := fun k => by
    have h := hmax k (Finset.mem_univ _)
    rw [div_le_div_iff₀ (hmposQ k) (hmposQ i)] at h
    exact_mod_cast h
  have hvexact : ∀ z w, componentPoint V i ⤳ z → w ∈ T z →
      v i w = WithZero.exp (n i : ℤ) := fun z w hiz hw =>
    valuation_eq_of_sub_le_one (v i) hni (hpole i hni)
      (hdv i z _ w _ hiz (specializes_refl _) hw (hu₀ i))
  -- the functions `h = u^{m_i} c^{n_i}`
  set U : V.X → V.X.functionField := fun z => (h1 z).some with hUdef
  have hU : ∀ z, U z ∈ T z := fun z => (h1 z).some_mem
  set H : V.X → V.X.functionField := fun z => U z ^ m i * γ ^ n i with hHdef
  have hmem : ∀ (z : V.X) (δ : V.X.functionField), (∀ y, y ⤳ z → δ ∈ V.stalkRange y) →
      (∀ k, componentPoint V k ⤳ z → v k (U z ^ m i * δ ^ n i) ≤ 1) →
      U z ^ m i * δ ^ n i ∈ V.stalkRange z := fun z δ hδ hv => by
    refine Scheme.mem_range_algebraMap_stalk_of_forall_coheight_eq_one z fun y hy hyz => ?_
    by_cases hfy : V.f y = V.closedPoint
    · obtain ⟨k, rfl⟩ := V.exists_eq_componentPoint hfy hy
      exact (Scheme.valuationAt_le_one_iff (hP k) _).mp (hv k hyz)
    · exact mul_mem (pow_mem (hoff y _ hfy (h3' hyz (hU z))) _) (pow_mem (hδ y hyz) _)
  have hH : ∀ z, H z ∈ V.stalkRange z := fun z =>
    hmem z γ (fun y _ => ⟨_, hγ y⟩) fun k hkz =>
      valuation_pow_mul_pow_le_one (v k) (hbound k z (U z) hkz (hU z)) (hvγ k) (hcross k)
  -- elements `e z` of the local rings with image `H z`
  choose e he using hH
  -- two such elements at `ξ_i` agree on the component `C_i`
  have hdiff : ∀ (a b : V.X.presheaf.stalk (componentPoint V i)) (za zb : V.X),
      componentPoint V i ⤳ za → componentPoint V i ⤳ zb →
      algebraMap _ V.X.functionField a = H za → algebraMap _ V.X.functionField b = H zb →
      (componentι V i).stalkMap (genericPoint (componentScheme V i)) a =
        (componentι V i).stalkMap (genericPoint (componentScheme V i)) b := by
    intro a b za zb hza hzb ha hb
    have hd : v i (U za - U zb) ≤ 1 := hdv i za zb _ _ hza hzb (hU za) (hU zb)
    have hlt : v i (algebraMap _ V.X.functionField (a - b)) < 1 := by
      rw [map_sub, ha, hb]
      exact valuation_sub_pow_mul_pow_lt_one (v i) hni (hvexact za (U za) hza (hU za))
        (hvexact zb (U zb) hzb (hU zb)) hd (hvγ i)
    have hm := (Scheme.valuationAt_algebraMap_lt_one_iff (hP i) (a - b)).mp hlt
    exact sub_eq_zero.mp
      ((map_sub _ a b).symm.trans (V.stalkMap_genericPoint_eq_zero_of_mem_maximalIdeal hm))
  -- the function on the generic point of `C_i`
  set φ : (componentScheme V i).functionField :=
    (componentι V i).stalkMap (genericPoint (componentScheme V i)) (e (componentPoint V i))
    with hφdef
  have hφ : ∀ z : componentScheme V i,
      algebraMap ((componentScheme V i).presheaf.stalk z) (componentScheme V i).functionField
        ((componentι V i).stalkMap z (e (componentι V i z))) = φ := by
    intro z
    have hgz : genericPoint (componentScheme V i) ⤳ z := genericPoint_specializes z
    have hiz : componentPoint V i ⤳ componentι V i z := hgz.map (componentι V i).continuous
    have key := (componentι V i).stalkSpecializes_stalkMap_apply _ z hgz (e (componentι V i z))
    have halg : algebraMap ((componentScheme V i).presheaf.stalk z)
        (componentScheme V i).functionField ((componentι V i).stalkMap z (e (componentι V i z))) =
        (componentScheme V i).presheaf.stalkSpecializes hgz
          ((componentι V i).stalkMap z (e (componentι V i z))) := rfl
    rw [halg, ← key]
    exact hdiff _ _ (componentι V i z) (componentPoint V i) hiz (specializes_refl _)
      ((Scheme.algebraMap_stalkSpecializes _ _).trans (he _)) (he _)
  have hφ0 : φ ≠ 0 := by
    have hv1 : v i (algebraMap _ V.X.functionField (e (componentPoint V i))) = 1 := by
      rw [he]
      exact valuation_pow_mul_pow_eq_one (v i) (hvexact _ _ (specializes_refl _) (hU _)) (hvγ i)
    have hnm : e (componentPoint V i) ∉ IsLocalRing.maximalIdeal _ := fun hm =>
      (ne_of_lt ((Scheme.valuationAt_algebraMap_lt_one_iff (hP i) _).mpr hm)) hv1
    have hunit := (IsLocalRing.notMem_maximalIdeal.mp hnm).map
      ((componentι V i).stalkMap (genericPoint (componentScheme V i))).hom
    exact hunit.ne_zero
  -- it is a nonzero global function on `C_i`, hence a unit
  obtain ⟨φt, hφt⟩ := Scheme.exists_globalSection_of_forall_mem_range_stalk
    (X := componentScheme V i) (z := φ) fun z => ⟨_, hφ z⟩
  have hφt0 : φt ≠ 0 := by
    rintro rfl
    exact hφ0 (by rw [← hφt, map_zero])
  obtain ⟨φinv, hφinv⟩ := (Scheme.isField_globalSections_of_isProper
    (componentToSpecResidueField V i)).mul_inv_cancel hφt0
  have hunit : IsUnit φt := ⟨⟨φt, φinv, hφinv, by rwa [mul_comm]⟩, rfl⟩
  -- but it vanishes at the closed point `x_i` of Tag 0AX9
  obtain ⟨y₀, -, -, hy₀j, g, h₀, hgm, hgne, hgfac⟩ : ∃ y₀ : componentScheme V i,
      IsClosed ({componentι V i y₀} : Set V.X) ∧ componentι V i y₀ ∈ componentInSource V i ∧
      (∀ j, j ≠ i → componentι V i y₀ ∉ componentInSource V j) ∧
      ∃ g h₀ : V.X.presheaf.stalk (componentι V i y₀),
        g ∈ IsLocalRing.maximalIdeal _ ∧ (componentι V i).stalkMap y₀ g ≠ 0 ∧
        baseRingToStalk V.f (componentι V i y₀) c = g * h₀ := hfac i
  have hgP := V.stalkSpecializes_notMem_maximalIdeal y₀ g hgne
  have hvg : v i (algebraMap _ V.X.functionField g) = 1 := by
    have e1 := Scheme.algebraMap_stalkSpecializes
      ((componentι V i).base.hom.map_specializes (genericPoint_specializes y₀)) g
    exact (congrArg (v i) e1).symm.trans (Scheme.valuationAt_algebraMap_eq_one (hP i) hgP)
  have hγfac : γ = algebraMap _ V.X.functionField g * algebraMap _ V.X.functionField h₀ := by
    rw [← map_mul, ← hgfac]
    exact (hγ _).symm
  have hvh₀ : v i (algebraMap _ V.X.functionField h₀) = WithZero.exp (-(m i : ℤ)) := by
    have := hvγ i
    rwa [hγfac, map_mul, hvg, one_mul] at this
  have hw : U (componentι V i y₀) ^ m i * algebraMap _ V.X.functionField h₀ ^ n i ∈
      V.stalkRange (componentι V i y₀) := by
    refine hmem _ _ (fun y hyz => Scheme.range_algebraMap_stalk_le_of_specializes hyz ⟨h₀, rfl⟩)
      fun k hkz => ?_
    obtain rfl : k = i := by
      by_contra hki
      exact hy₀j k hki (V.mem_componentInSource_of_specializes hkz)
    exact valuation_pow_mul_pow_le_one _ (hvexact _ _ hkz (hU _)).le hvh₀ le_rfl
  obtain ⟨w, hw'⟩ := hw
  have he₀ : e (componentι V i y₀) = w * g ^ n i := by
    apply IsFractionRing.injective (V.X.presheaf.stalk (componentι V i y₀)) V.X.functionField
    rw [he, map_mul, map_pow, hw', hHdef]
    dsimp only
    rw [hγfac]
    ring
  have hem : e (componentι V i y₀) ∈ IsLocalRing.maximalIdeal _ := by
    rw [he₀]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hgm _ hni)
  have hnon := map_nonunit ((componentι V i).stalkMap y₀).hom _ hem
  have : Nonempty (⊤ : (componentScheme V i).Opens) := ⟨⟨y₀, trivial⟩⟩
  have hgerm : (componentScheme V i).presheaf.germ ⊤ y₀ trivial φt =
      (componentι V i).stalkMap y₀ (e (componentι V i y₀)) := by
    apply IsFractionRing.injective ((componentScheme V i).presheaf.stalk y₀)
      (componentScheme V i).functionField
    rw [hφ y₀]
    exact (Scheme.algebraMap_germ_eq_germToFunctionField (componentScheme V i)
      (show y₀ ∈ (⊤ : (componentScheme V i).Opens) from trivial) φt).trans hφt
  exact (IsLocalRing.mem_maximalIdeal _).mp hnon
    (hgerm ▸ hunit.map ((componentScheme V i).presheaf.germ ⊤ y₀ trivial).hom)

end NoPoles

/-! ### Sections of `𝒪_X/a𝒪_X` -/

section ZeroScheme

attribute [local instance] Scheme.commRingRingCatSheafObj

variable [IsNormal V.X]

omit [IsNormal V.X] in
/-- Multiplication by an element of the base ring, read in the function field. -/
theorem algebraMap_germ_baseSmul (a : V.A) (W : V.X.Opens) {x : V.X} (hx : x ∈ W)
    (c : ToType ((SheafOfModules.unit V.X.ringCatSheaf).val.obj (op W))) :
    haveI : Nonempty (⊤ : V.X.Opens) := ⟨⟨x, trivial⟩⟩
    algebraMap (V.X.presheaf.stalk x) V.X.functionField (V.X.presheaf.germ W x hx
        ((baseSmulModules V.X V.f a (SheafOfModules.unit V.X.ringCatSheaf)).val.app (op W) c)) =
      V.X.germToFunctionField ⊤ (baseSection V.X V.f a) *
        algebraMap (V.X.presheaf.stalk x) V.X.functionField (V.X.presheaf.germ W x hx c) := by
  have : Nonempty (⊤ : V.X.Opens) := ⟨⟨x, trivial⟩⟩
  change algebraMap (V.X.presheaf.stalk x) V.X.functionField (V.X.presheaf.germ W x hx
      (V.X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (baseSection V.X V.f a) *
        (show Γ(V.X, W) from c))) = _
  rw [map_mul, map_mul]
  congr 1
  have e1 := V.X.presheaf.germ_res_apply (homOfLE (le_top : W ≤ ⊤)) x hx
    (show Γ(V.X, ⊤) from baseSection V.X V.f a)
  exact (congrArg (algebraMap (V.X.presheaf.stalk x) V.X.functionField) e1).trans
    (Scheme.algebraMap_germ_eq_germToFunctionField V.X (show x ∈ (⊤ : V.X.Opens) from trivial)
      (baseSection V.X V.f a))

omit [IsNormal V.X] in
/-- Every global section of `𝒪_X/a𝒪_X` lifts, near any point, to a function. -/
theorem exists_lift_zeroSchemeStructureSheaf (a : V.A)
    (s : (zeroSchemeStructureSheaf V.X V.f a).val.obj (op ⊤)) (x : V.X) :
    ∃ (W : V.X.Opens) (_ : x ∈ W)
      (g : (SheafOfModules.unit V.X.ringCatSheaf).val.obj (op W)),
      (toZeroSchemeStructureSheaf V.X V.f a).val.app (op W) g =
        (zeroSchemeStructureSheaf V.X V.f a).val.map (homOfLE (le_top : W ≤ ⊤)).op s := by
  have hls := Stacks.SheafOfModules.isLocallySurjective_cokernel_π
    (baseSmulModules V.X V.f a (SheafOfModules.unit V.X.ringCatSheaf))
  have hS := Presheaf.imageSieve_mem (Opens.grothendieckTopology V.X)
    ((PresheafOfModules.toPresheaf V.X.ringCatSheaf.obj).map
      (Limits.cokernel.π (baseSmulModules V.X V.f a (SheafOfModules.unit V.X.ringCatSheaf))).val)
    (U := op ⊤) (show ToType (((PresheafOfModules.toPresheaf V.X.ringCatSheaf.obj).obj
      (zeroSchemeStructureSheaf V.X V.f a).val).obj (op ⊤)) from s)
  obtain ⟨W, f, ⟨g, hg⟩, hxW⟩ := hS x trivial
  refine ⟨W, hxW, g, ?_⟩
  rwa [show homOfLE (le_top : W ≤ ⊤) = f from Subsingleton.elim _ _]

omit [IsNormal V.X] in
/-- A function killed in `𝒪_X/a𝒪_X` is a multiple of `a`, for `a ≠ 0`. -/
theorem exists_baseSmul_eq_of_toZeroScheme_eq_zero {a : V.A} (ha : a ≠ 0) (W : V.X.Opens)
    (g : (SheafOfModules.unit V.X.ringCatSheaf).val.obj (op W))
    (hg : (toZeroSchemeStructureSheaf V.X V.f a).val.app (op W) g = 0) :
    ∃ c : (SheafOfModules.unit V.X.ringCatSheaf).val.obj (op W),
      (baseSmulModules V.X V.f a (SheafOfModules.unit V.X.ringCatSheaf)).val.app (op W) c = g := by
  have hmono := mono_baseSmulModules_unit V.X V.f a
    (baseSection_ne_zero_of_isModification V.X V.f V.modification ha)
  have hSE := baseSmulUnit_shortExact (Over.mk V.f) a hmono
  exact SheafOfModules.exists_of_shortExact_sections hSE (op W) g hg

/-- **No nonzero section of `𝒪_X/a𝒪_X` is supported in the special fibre.** In Situation
[Stacks, Tag 0AX8] with `X` normal, let `a ≠ 0` in `A`. A global section of `𝒪_X/a𝒪_X` whose
restriction to `f⁻¹(U)` vanishes is zero.

Near each point the section is the image of a function `g`, and `g/a` is an element of the
function field well defined up to the local ring there; off the special fibre it can be taken to
be zero. `mem_stalkRange_of_liftClasses` shows that it always lies in the local ring, so that
`g` is locally a multiple of `a` and the section vanishes locally, hence vanishes. This is the
statement equivalent to `H¹_{X_s}(X, 𝒪_X) = 0` which the proof of [Stacks, Tag 0AXC] needs in
place of [Stacks, Tag 0AXB]; neither that tag nor the Nagata condition is used. -/
theorem eq_zero_of_res_preimagePuncturedSpectrum_eq_zero (a : V.A) (ha : a ≠ 0)
    (s : (zeroSchemeStructureSheaf V.X V.f a).val.obj (op ⊤))
    (hs : (zeroSchemeStructureSheaf V.X V.f a).val.map
      (homOfLE (le_top : V.preimagePuncturedSpectrum ≤ ⊤)).op s = 0) : s = 0 := by
  classical
  let M := zeroSchemeStructureSheaf V.X V.f a
  let π := toZeroSchemeStructureSheaf V.X V.f a
  have hne : Nonempty (⊤ : V.X.Opens) := ⟨⟨Classical.arbitrary V.X, trivial⟩⟩
  -- restricting a local lift of `s` to a smaller open gives a local lift of `s`
  have hres : ∀ (W W₀ : V.X.Opens) (hW : W₀ ≤ W) g,
      π.val.app (op W) g = M.val.map (homOfLE (le_top : W ≤ ⊤)).op s →
      π.val.app (op W₀) ((SheafOfModules.unit V.X.ringCatSheaf).val.map (homOfLE hW).op g) =
        M.val.map (homOfLE (le_top : W₀ ≤ ⊤)).op s := fun W W₀ hW g hg => by
    rw [PresheafOfModules.naturality_apply, hg, ← M.val.map_comp_apply]
    rfl
  set α : V.X.functionField := V.X.germToFunctionField ⊤ (baseSection V.X V.f a) with hαdef
  have hα0 : α ≠ 0 := V.germToFunctionField_baseSection_ne_zero ha
  -- the classes of the local lifts
  let T : V.X → Set V.X.functionField := fun x => {t | ∃ (W : V.X.Opens) (hx : x ∈ W)
    (g : (SheafOfModules.unit V.X.ringCatSheaf).val.obj (op W)),
      π.val.app (op W) g = M.val.map (homOfLE (le_top : W ≤ ⊤)).op s ∧
      t * α = algebraMap (V.X.presheaf.stalk x) V.X.functionField
        (V.X.presheaf.germ W x hx (show Γ(V.X, W) from g))}
  have h1 : ∀ x, (T x).Nonempty := fun x => by
    obtain ⟨W, hx, g, hg⟩ := V.exists_lift_zeroSchemeStructureSheaf a s x
    exact ⟨_, W, hx, g, hg, div_mul_cancel₀ _ hα0⟩
  have h2 : ∀ x t t', t ∈ T x → t' ∈ T x → t - t' ∈ V.stalkRange x := by
    rintro x t t' ⟨W, hx, g, hg, ht⟩ ⟨W', hx', g', hg', ht'⟩
    let W₀ := W ⊓ W'
    have hx₀ : x ∈ W₀ := ⟨hx, hx'⟩
    let d : (SheafOfModules.unit V.X.ringCatSheaf).val.obj (op W₀) :=
      (SheafOfModules.unit V.X.ringCatSheaf).val.map (homOfLE inf_le_left).op g -
        (SheafOfModules.unit V.X.ringCatSheaf).val.map (homOfLE inf_le_right).op g'
    have hd : π.val.app (op W₀) d = 0 := by
      refine (map_sub (π.val.app (op W₀)).hom _ _).trans ?_
      rw [hres W W₀ inf_le_left g hg, hres W' W₀ inf_le_right g' hg']
      exact sub_self _
    obtain ⟨c, hc⟩ := V.exists_baseSmul_eq_of_toZeroScheme_eq_zero ha W₀ d hd
    refine ⟨V.X.presheaf.germ W₀ x hx₀ (show Γ(V.X, W₀) from c), ?_⟩
    apply mul_right_cancel₀ hα0
    have e1 : V.X.presheaf.germ W₀ x hx₀ (show Γ(V.X, W₀) from
        (SheafOfModules.unit V.X.ringCatSheaf).val.map (homOfLE inf_le_left).op g) =
        V.X.presheaf.germ W x hx (show Γ(V.X, W) from g) :=
      V.X.presheaf.germ_res_apply (homOfLE inf_le_left) x hx₀ g
    have e2 : V.X.presheaf.germ W₀ x hx₀ (show Γ(V.X, W₀) from
        (SheafOfModules.unit V.X.ringCatSheaf).val.map (homOfLE inf_le_right).op g') =
        V.X.presheaf.germ W' x hx' (show Γ(V.X, W') from g') :=
      V.X.presheaf.germ_res_apply (homOfLE inf_le_right) x hx₀ g'
    have e3 : V.X.presheaf.germ W₀ x hx₀ (show Γ(V.X, W₀) from d) =
        V.X.presheaf.germ W₀ x hx₀ (show Γ(V.X, W₀) from
          (SheafOfModules.unit V.X.ringCatSheaf).val.map (homOfLE inf_le_left).op g) -
        V.X.presheaf.germ W₀ x hx₀ (show Γ(V.X, W₀) from
          (SheafOfModules.unit V.X.ringCatSheaf).val.map (homOfLE inf_le_right).op g') :=
      map_sub (V.X.presheaf.germ W₀ x hx₀).hom _ _
    rw [sub_mul, ht, ht', mul_comm, ← V.algebraMap_germ_baseSmul a W₀ hx₀ c, hc, e3, map_sub,
      e1, e2]
  have h3 : ∀ x t, t ∈ T x → ∃ N : V.X.Opens, x ∈ N ∧ ∀ z ∈ N, t ∈ T z := by
    rintro x t ⟨W, hx, g, hg, ht⟩
    refine ⟨W, hx, fun z hz => ⟨W, hz, g, hg, ?_⟩⟩
    have : Nonempty W := ⟨⟨x, hx⟩⟩
    rw [ht, Scheme.algebraMap_germ_eq_germToFunctionField V.X hx,
      Scheme.algebraMap_germ_eq_germToFunctionField V.X hz]
  have h4 : ∀ x, V.f x ≠ V.closedPoint → (0 : V.X.functionField) ∈ T x := by
    intro x hx
    refine ⟨V.preimagePuncturedSpectrum, hx, 0, ?_, ?_⟩
    · exact (map_zero _).trans hs.symm
    · rw [zero_mul]
      exact (map_zero _).symm.trans (congrArg _ (map_zero _).symm)
  have hall := V.mem_stalkRange_of_liftClasses T h1 h2 h3 h4
  -- conclusion: the section vanishes near every point
  refine Stacks.SheafOfModules.eq_zero_of_locally_zero' M s fun x _ => ?_
  obtain ⟨t, W, hx, g, hg, ht⟩ := h1 x
  obtain ⟨r, hr⟩ := hall x t ⟨W, hx, g, hg, ht⟩
  obtain ⟨W', hx', ρ, hρ⟩ := V.X.presheaf.exists_germ_eq (x := x) r
  let W₀ := W ⊓ W'
  have hx₀ : x ∈ W₀ := ⟨hx, hx'⟩
  let ρ₀ : (SheafOfModules.unit V.X.ringCatSheaf).val.obj (op W₀) :=
    (SheafOfModules.unit V.X.ringCatSheaf).val.map (homOfLE inf_le_right).op ρ
  let g₀ : (SheafOfModules.unit V.X.ringCatSheaf).val.obj (op W₀) :=
    (SheafOfModules.unit V.X.ringCatSheaf).val.map (homOfLE inf_le_left).op g
  have hgerm : V.X.presheaf.germ W₀ x hx₀ (show Γ(V.X, W₀) from g₀) =
      V.X.presheaf.germ W₀ x hx₀ (show Γ(V.X, W₀) from
        (baseSmulModules V.X V.f a (SheafOfModules.unit V.X.ringCatSheaf)).val.app (op W₀) ρ₀) := by
    apply IsFractionRing.injective (V.X.presheaf.stalk x) V.X.functionField
    rw [V.algebraMap_germ_baseSmul a W₀ hx₀ ρ₀]
    have e1 : V.X.presheaf.germ W₀ x hx₀ (show Γ(V.X, W₀) from g₀) =
        V.X.presheaf.germ W x hx (show Γ(V.X, W) from g) :=
      V.X.presheaf.germ_res_apply (homOfLE inf_le_left) x hx₀ g
    have e2 : V.X.presheaf.germ W₀ x hx₀ (show Γ(V.X, W₀) from ρ₀) = r :=
      (V.X.presheaf.germ_res_apply (homOfLE inf_le_right) x hx₀ ρ).trans hρ
    rw [e1, e2, ← ht, hr, mul_comm]
  obtain ⟨W₁, hx₁, i₁, i₂, heq⟩ := V.X.presheaf.germ_eq x hx₀ hx₀ _ _ hgerm
  refine ⟨W₁, homOfLE le_top, hx₁, ?_⟩
  have hπ0 : π.val.app (op W₁) ((SheafOfModules.unit V.X.ringCatSheaf).val.map i₁.op g₀) = 0 := by
    have heq' : (SheafOfModules.unit V.X.ringCatSheaf).val.map i₁.op g₀ =
        (SheafOfModules.unit V.X.ringCatSheaf).val.map i₂.op
          ((baseSmulModules V.X V.f a (SheafOfModules.unit V.X.ringCatSheaf)).val.app
            (op W₀) ρ₀) := heq
    have n1 := PresheafOfModules.naturality_apply
      (baseSmulModules V.X V.f a (SheafOfModules.unit V.X.ringCatSheaf)).val i₂.op ρ₀
    rw [heq', ← n1]
    have hcond := Limits.cokernel.condition
      (baseSmulModules V.X V.f a (SheafOfModules.unit V.X.ringCatSheaf))
    have := congrArg (fun φ => φ.val.app (op W₁)
      ((SheafOfModules.unit V.X.ringCatSheaf).val.map i₂.op ρ₀)) hcond
    exact this.trans rfl
  rw [PresheafOfModules.naturality_apply] at hπ0
  rw [hres W W₀ inf_le_left g hg, ← M.val.map_comp_apply] at hπ0
  exact hπ0

end ZeroScheme

end VanishingSituation

end AlgebraicGeometry

end
