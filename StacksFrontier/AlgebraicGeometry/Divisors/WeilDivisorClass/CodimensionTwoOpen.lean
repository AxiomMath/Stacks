module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.ClassGroup
public import StacksCore.Tactic.StacksAttribute

/-!
# The Weil divisor class group of an open whose complement has codimension at least two

Let `X` be an integral locally Noetherian scheme and let `U ⊆ X` be an open subscheme whose
complement has codimension at least two at every point.  A point of coheight at most one — the
generic point of `X`, and the generic point of every prime divisor — then lies in `U`, so a prime
divisor of `X` meets `U` and is determined by a point of coheight one of `U`; conversely every
point of coheight one of `U` has coheight one in `X`.  The prime divisors of `X` and of `U` are
therefore the same, a coefficient family on them is locally finite on `X` exactly when it is
locally finite on `U`, and restriction is an isomorphism `Div(X) ≅ Div(U)`.  It matches principal
divisors with principal divisors, because `U` and `X` have the same rational functions and the
order of vanishing of a rational function is computed in a local ring, so it descends to an
isomorphism `Cl(X) ≅ Cl(U)` of Weil divisor class groups.

## Main definitions

* `AlgebraicGeometry.primeDivisorRestrictEquiv` — the bijection between the prime divisors of
  `X` and those of `U`.
* `AlgebraicGeometry.weilDivisorRestrictEquiv` — the induced isomorphism `Div(X) ≅ Div(U)`.
* `AlgebraicGeometry.weilDivisorClassRestrictEquiv` — the induced isomorphism `Cl(X) ≅ Cl(U)`.

## Main results

* `AlgebraicGeometry.mem_of_coheight_lt_two` — a point of coheight less than two lies in `U`.
* `AlgebraicGeometry.exists_isOpen_finite_genericPoint_of_mem_weilDivisor` — the local finiteness
  of a Weil divisor read on the generic points of its prime divisors, the converse of
  `AlgebraicGeometry.mem_weilDivisor_of_forall_exists_open`.
* `AlgebraicGeometry.weilDivisorRestrictEquiv_principalDivisor` — restriction carries `div(f)` to
  `div(f|_U)`.
* `AlgebraicGeometry.map_principalWeilDivisors_weilDivisorRestrictEquiv` — restriction carries the
  subgroup of principal Weil divisors onto the subgroup of principal Weil divisors.
* `AlgebraicGeometry.two_le_codimension_compl_inf` — the intersection of two such opens is again
  one.

## Implementation notes

**Which clause of Tag 0EBM is here.**  Tag 0EBM asserts that on an integral locally Noetherian
normal scheme the group of isomorphism classes of rank one coherent reflexive `𝒪_X`-modules is
isomorphic to `Cl(X)`.  That isomorphism is **not** proved here and no declaration claims it.
What is proved is the clause `Cl(U) = Cl(X)` which the source asserts in the course of its proof —
the clause that lets the class of a rank one coherent reflexive module be read off from its
restriction to the open subscheme supplied by clause (3) of [Stacks, Tag 0AY6], and the only
clause of that proof that is a statement about `Cl` alone.  The independence of that class of the
chosen open is `AlgebraicGeometry.weilClassOfCodimTwoInvertible_restrict` of
`StacksFrontier/AlgebraicGeometry/Divisors/WeilDivisorClass/CodimTwoInvertibleClass.lean`, resting
on the invariance of the first Chern class under restriction to such an open,
`AlgebraicGeometry.weilDivisorClassOfInvertibleSheaf_restrict`; the resulting map is
`AlgebraicGeometry.CoherentReflexive.rankOneSkeletonToWeilClass`, and it is injective and
multiplicative for the monoid law of [Stacks, Tag 0EBL] —
`AlgebraicGeometry.CoherentReflexive.rankOneSkeletonToWeilClass_mul` of
`StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/RankOneWeilClassMultiplicative.lean`.  It is
also surjective:
`AlgebraicGeometry.CoherentReflexive.rankOneSkeletonToWeilClass_surjective` of
`StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/RankOneWeilClassSurjective.lean`, which needs
the construction of `𝒪_X(D)` for a Weil divisor `D` on a NORMAL scheme, carried out in
`StacksFrontier/AlgebraicGeometry/Divisors/WeilDivisorClass/NormalWeilDivisorInvertible.lean`.
`AlgebraicGeometry.positiveWeilIdeal` of
`StacksFrontier/AlgebraicGeometry/Divisors/WeilDivisorClass/FirstChernClassSurjective.lean` is an
effective Cartier divisor on all of `X` only under the stronger hypothesis that the local rings
are factorial, which by [Stacks, Tag 0BE9] is strictly stronger than normality; over a normal
scheme it is restricted to the open subscheme on which it is principal, and the comparison
`Cl(U) = Cl(X)` of this file is what puts the resulting class back on `X`.

**Why the prime divisors agree.**  A prime divisor is determined by its generic point and those
generic points are exactly the points of coheight one, which is
`AlgebraicGeometry.PrimeDivisor.genericPoint_injective` together with
`AlgebraicGeometry.PrimeDivisor.ofCoheightOne`; and an open immersion preserves the coheight of a
point, which is [Stacks, Tag 02I4] in the form
`AlgebraicGeometry.coheight_eq_of_isOpenImmersion`.  So no new dictionary between closed
subschemes is built: the correspondence is read entirely on generic points.

**Why local finiteness agrees.**  In the direction `X → U` it is the preimage of a neighbourhood.
In the direction `U → X` a neighbourhood of a point of `X` is needed, including of a point of the
complement, where the hypothesis gives nothing directly; an affine open neighbourhood `V` is taken
instead, its preimage in `U` is compact because `U ↪ X` is quasi-compact on a locally Noetherian
scheme ([Stacks, Tag 01OX]), and a prime divisor meeting `V` already has its generic point in `V`,
so `LocallyFinite.finite_nonempty_inter_compact` bounds the prime divisors involved.

**Which Weil divisors.**  `AlgebraicGeometry.WeilDivisor` of
`StacksFrontier/AlgebraicGeometry/Divisors/PrimeDivisor.lean`, the lineage on which
`AlgebraicGeometry.weilDivisorClassGroup` and the first Chern class of [Stacks, Tag 0BE7] are
built.

## References

* [Stacks Project, Tag 0EBM](https://stacks.math.columbia.edu/tag/0EBM)
* [Stacks Project, Tag 0BE2](https://stacks.math.columbia.edu/tag/0BE2)
* [Stacks Project, Tag 0BE4](https://stacks.math.columbia.edu/tag/0BE4)
* [Stacks Project, Tag 02I4](https://stacks.math.columbia.edu/tag/02I4)
* [Stacks Project, Tag 01OX](https://stacks.math.columbia.edu/tag/01OX)
* [Stacks Project, Tag 0AY6](https://stacks.math.columbia.edu/tag/0AY6)
-/

@[expose] public noncomputable section

open Order TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- A nonempty open subscheme of an integral scheme is dominant: its image is a nonempty open
subset of an irreducible space, hence dense. -/
theorem isDominant_opensι [IsIntegral X] (U : X.Opens) [Nonempty U.toScheme] :
    IsDominant U.ι :=
  ⟨(U.ι.isOpenEmbedding.isOpen_range).dense (Set.range_nonempty _)⟩

/-- The generic point of a prime divisor with nonzero coefficient lies in its support slot of the
locally finite family `Z ↦ if D Z = 0 then ∅ else Z.support`. -/
private theorem genericPoint_mem_ite_support {D : PrimeDivisor X → ℤ} {Z : PrimeDivisor X}
    (hZ : D Z ≠ 0) : Z.genericPoint ∈ (if D Z = 0 then (∅ : Set X) else Z.support) := by
  rw [ite_eq_right hZ, Z.support_eq_closure]
  exact subset_closure rfl

/-- **The local finiteness of a Weil divisor, read on generic points.**  Every point of `X` has an
open neighbourhood containing the generic points of only finitely many prime divisors with nonzero
coefficient.  This is the converse of
`AlgebraicGeometry.mem_weilDivisor_of_forall_exists_open`: a nonempty open subset of the support of
a prime divisor contains its generic point, so the two formulations of local finiteness agree. -/
theorem exists_isOpen_finite_genericPoint_of_mem_weilDivisor {D : PrimeDivisor X → ℤ}
    (hD : D ∈ WeilDivisor X) (x : X) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      {Z : PrimeDivisor X | Z.genericPoint ∈ V ∧ D Z ≠ 0}.Finite := by
  obtain ⟨t, ht, hfin⟩ := hD x
  refine ⟨interior t, isOpen_interior, mem_interior_iff_mem_nhds.mpr ht, hfin.subset ?_⟩
  rintro Z ⟨hZV, hZne⟩
  exact ⟨Z.genericPoint, genericPoint_mem_ite_support hZne, interior_subset hZV⟩

/-- The generic point of a prime divisor of an open subscheme, viewed in the ambient scheme, has
coheight one, because an open immersion preserves the coheight of a point. -/
theorem coheight_base_genericPoint_eq_one (U : X.Opens) (W : PrimeDivisor U.toScheme) :
    coheight (U.ι.base W.genericPoint) = 1 :=
  (coheight_eq_of_isOpenImmersion U.ι).trans W.coheight_genericPoint

/-- The intersection of two open subschemes whose complements have codimension at least two again
has a complement of codimension at least two. -/
theorem two_le_codimension_compl_inf (U V : X.Opens)
    (hU : ∀ x : X, x ∉ U → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (hV : ∀ x : X, x ∉ V → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (x : X) (hx : x ∉ U ⊓ V) :
    (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x) := by
  rw [TopologicalSpace.Opens.mem_inf] at hx
  exact (not_and_or.mp hx).elim (hU x) (hV x)

/-- A point of an open subscheme lying over the generic point of a prime divisor of the ambient
scheme has coheight one, because an open immersion preserves the coheight of a point. -/
theorem coheight_eq_one_of_base_eq_genericPoint (U : X.Opens) (Z : PrimeDivisor X)
    (y : U.toScheme) (hy : U.ι.base y = Z.genericPoint) : coheight y = 1 :=
  (coheight_eq_of_isOpenImmersion U.ι).symm.trans (by rw [hy]; exact Z.coheight_genericPoint)

section CodimensionTwoComplement

variable (U : X.Opens)
  (hU : ∀ x : X, x ∉ U → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))

include hU

/-! ### Points of small coheight lie in the open subscheme -/

/-- **A point of coheight less than two lies in an open subscheme whose complement has codimension
at least two.**  The coheight of a point is the codimension of the closure of its singleton. -/
theorem mem_of_coheight_lt_two (x : X) (hx : coheight x < 2) : x ∈ U := by
  by_contra hxU
  have h := hU x hxU
  rw [← coheight_eq_codimension_closureSingleton] at h
  exact absurd h hx.not_ge

/-- **The generic point lies in an open subscheme whose complement has codimension at least
two.**  The generic point is the top element of the specialization order, so its coheight is
zero. -/
theorem genericPoint_mem_of_two_le_codimension_compl [IsIntegral X] : genericPoint X ∈ U := by
  refine mem_of_coheight_lt_two U hU _ ?_
  rw [show genericPoint X = (⊤ : X) from rfl, coheight_top]
  norm_num

/-- **The generic point of a prime divisor lies in an open subscheme whose complement has
codimension at least two.**  That generic point has coheight one. -/
theorem primeDivisor_genericPoint_mem_of_two_le_codimension_compl (Z : PrimeDivisor X) :
    Z.genericPoint ∈ U := by
  refine mem_of_coheight_lt_two U hU _ ?_
  rw [Z.coheight_genericPoint]
  norm_num

/-- An open subscheme of an integral scheme whose complement has codimension at least two is
nonempty: it contains the generic point. -/
theorem nonempty_of_two_le_codimension_compl [IsIntegral X] : Nonempty U.toScheme :=
  ⟨⟨genericPoint X, genericPoint_mem_of_two_le_codimension_compl U hU⟩⟩

/-- An open subscheme of an integral scheme whose complement has codimension at least two is
integral: it is a nonempty open subscheme of an integral scheme. -/
theorem isIntegral_of_two_le_codimension_compl [IsIntegral X] : IsIntegral U.toScheme :=
  have := nonempty_of_two_le_codimension_compl U hU
  isIntegral_of_isOpenImmersion U.ι

/-! ### The prime divisors of the open subscheme -/

/-- **The prime divisors of an open subscheme whose complement has codimension at least two are
the prime divisors of the ambient scheme.**  A prime divisor is determined by its generic point,
its generic point has coheight one and therefore lies in the open subscheme, and an open immersion
preserves the coheight of a point. -/
def primeDivisorRestrictEquiv : PrimeDivisor X ≃ PrimeDivisor U.toScheme where
  toFun Z := PrimeDivisor.ofCoheightOne (X := U.toScheme)
    ⟨Z.genericPoint, primeDivisor_genericPoint_mem_of_two_le_codimension_compl U hU Z⟩
    (coheight_eq_one_of_base_eq_genericPoint U Z _ rfl)
  invFun W := PrimeDivisor.ofCoheightOne (U.ι.base W.genericPoint)
    (coheight_base_genericPoint_eq_one U W)
  left_inv Z := by
    refine PrimeDivisor.genericPoint_injective ?_
    refine (PrimeDivisor.genericPoint_ofCoheightOne _ _).trans ?_
    exact congrArg U.ι.base (PrimeDivisor.genericPoint_ofCoheightOne _ _)
  right_inv W := by
    refine PrimeDivisor.genericPoint_injective ?_
    refine (PrimeDivisor.genericPoint_ofCoheightOne _ _).trans (Subtype.ext ?_)
    exact PrimeDivisor.genericPoint_ofCoheightOne _ _

/-- The generic point of the restriction of a prime divisor is its generic point. -/
@[simp]
theorem base_genericPoint_primeDivisorRestrictEquiv (Z : PrimeDivisor X) :
    U.ι.base (primeDivisorRestrictEquiv U hU Z).genericPoint = Z.genericPoint :=
  congrArg U.ι.base (PrimeDivisor.genericPoint_ofCoheightOne (X := U.toScheme)
    ⟨Z.genericPoint, primeDivisor_genericPoint_mem_of_two_le_codimension_compl U hU Z⟩
    (coheight_eq_one_of_base_eq_genericPoint U Z _ rfl))

/-- The generic point of a prime divisor of `U`, viewed in `X`, is the generic point of the
corresponding prime divisor of `X`. -/
@[simp]
theorem genericPoint_primeDivisorRestrictEquiv_symm (W : PrimeDivisor U.toScheme) :
    ((primeDivisorRestrictEquiv U hU).symm W).genericPoint = U.ι.base W.genericPoint :=
  PrimeDivisor.genericPoint_ofCoheightOne (U.ι.base W.genericPoint)
    (coheight_base_genericPoint_eq_one U W)

/-! ### The Weil divisors of the open subscheme -/

/-- **The restriction of a Weil divisor is a Weil divisor.**  Local finiteness at a point of `U`
is local finiteness at its image in `X`, read on the preimage of the witnessing neighbourhood. -/
theorem mem_weilDivisor_comp_primeDivisorRestrictEquiv_symm {D : PrimeDivisor X → ℤ}
    (hD : D ∈ WeilDivisor X) :
    (fun W : PrimeDivisor U.toScheme => D ((primeDivisorRestrictEquiv U hU).symm W)) ∈
      WeilDivisor U.toScheme := by
  refine mem_weilDivisor_of_forall_exists_open fun y => ?_
  obtain ⟨V, hVopen, hyV, hfin⟩ :=
    exists_isOpen_finite_genericPoint_of_mem_weilDivisor hD (U.ι.base y)
  refine ⟨U.ι.base ⁻¹' V, hVopen.preimage U.ι.continuous, hyV, ?_⟩
  refine Set.Finite.of_finite_image (f := (primeDivisorRestrictEquiv U hU).symm)
    (hfin.subset ?_) (primeDivisorRestrictEquiv U hU).symm.injective.injOn
  rintro - ⟨W, ⟨hWV, hWne⟩, rfl⟩
  exact ⟨by rwa [genericPoint_primeDivisorRestrictEquiv_symm], hWne⟩

/-- **A Weil divisor of an open subscheme whose complement has codimension at least two extends to
a Weil divisor.**  Local finiteness at a point of `X` is read on an affine open neighbourhood `V`:
the preimage of `V` in `U` is compact because `U ↪ X` is quasi-compact, and a prime divisor whose
support meets `V` has its generic point in `V`. -/
theorem mem_weilDivisor_comp_primeDivisorRestrictEquiv [IsLocallyNoetherian X]
    {D : PrimeDivisor U.toScheme → ℤ} (hD : D ∈ WeilDivisor U.toScheme) :
    (fun Z : PrimeDivisor X => D (primeDivisorRestrictEquiv U hU Z)) ∈ WeilDivisor X := by
  refine mem_weilDivisor_of_forall_exists_open fun x => ?_
  set V : X.Opens := (X.affineCover.f (X.affineCover.idx x)).opensRange with hVdef
  have hK : IsCompact ((U.ι ⁻¹ᵁ V : U.toScheme.Opens) : Set U.toScheme) :=
    quasiCompact_iff_forall_isAffineOpen.mp inferInstance V (isAffineOpen_opensRange _)
  have hlf : LocallyFinite
      (fun W : PrimeDivisor U.toScheme => if D W = 0 then ∅ else W.support) := hD
  refine ⟨V, V.2, X.affineCover.covers x, ?_⟩
  refine Set.Finite.of_finite_image (f := primeDivisorRestrictEquiv U hU)
    ((hlf.finite_nonempty_inter_compact hK).subset ?_)
    (primeDivisorRestrictEquiv U hU).injective.injOn
  rintro - ⟨Z, ⟨hZV, hZne⟩, rfl⟩
  refine ⟨(primeDivisorRestrictEquiv U hU Z).genericPoint,
    genericPoint_mem_ite_support hZne, ?_⟩
  change U.ι.base (primeDivisorRestrictEquiv U hU Z).genericPoint ∈ V
  rwa [base_genericPoint_primeDivisorRestrictEquiv]

/-- **Restriction is an isomorphism `Div(X) ≅ Div(U)`** for an open subscheme whose complement has
codimension at least two: the prime divisors of the two schemes are the same, and a coefficient
family on them is locally finite on one exactly when it is locally finite on the other. -/
def weilDivisorRestrictEquiv [IsLocallyNoetherian X] :
    WeilDivisor X ≃+ WeilDivisor U.toScheme where
  toFun D := ⟨fun W => D.val ((primeDivisorRestrictEquiv U hU).symm W),
    mem_weilDivisor_comp_primeDivisorRestrictEquiv_symm U hU D.2⟩
  invFun D := ⟨fun Z => D.val (primeDivisorRestrictEquiv U hU Z),
    mem_weilDivisor_comp_primeDivisorRestrictEquiv U hU D.2⟩
  left_inv D := Subtype.ext (funext fun Z =>
    congrArg D.val ((primeDivisorRestrictEquiv U hU).symm_apply_apply Z))
  right_inv D := Subtype.ext (funext fun W =>
    congrArg D.val ((primeDivisorRestrictEquiv U hU).apply_symm_apply W))
  map_add' _ _ := rfl

/-- The coefficient of the restriction of a Weil divisor at a prime divisor of `U` is its
coefficient at the corresponding prime divisor of `X`. -/
@[simp]
theorem weilDivisorRestrictEquiv_apply_val [IsLocallyNoetherian X] (D : WeilDivisor X)
    (W : PrimeDivisor U.toScheme) :
    (weilDivisorRestrictEquiv U hU D).val W =
      D.val ((primeDivisorRestrictEquiv U hU).symm W) :=
  rfl

/-! ### Principal divisors and the class group -/

/-- **Restriction carries `div(f)` to `div(f|_U)`.**  The coefficient of a principal divisor at a
prime divisor is the order of vanishing of the rational function at its generic point, and that
order is unchanged by restriction to an open subscheme because the local ring there is the same. -/
theorem weilDivisorRestrictEquiv_principalDivisor [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral U.toScheme] [IsDominant U.ι] (f : (Stacks.Chow.rationalFunctions X)ˣ) :
    weilDivisorRestrictEquiv U hU (principalDivisor X f) =
      principalDivisor U.toScheme
        (Stacks.Chow.rationalFunctionsUnitsMulEquivOfOpenImmersion U.ι f) := by
  have hff : (Stacks.Chow.rationalFunctionsEquivFunctionField U.toScheme).val
        ((Stacks.Chow.rationalFunctionsUnitsMulEquivOfOpenImmersion U.ι f :
          (Stacks.Chow.rationalFunctions U.toScheme)ˣ) :
            Stacks.Chow.rationalFunctions U.toScheme) =
      Stacks.Chow.functionFieldEquiv_openImmersion U.ι
        ((Stacks.Chow.rationalFunctionsEquivFunctionField X).val f) := by
    rw [Stacks.Chow.rationalFunctionsUnitsMulEquivOfOpenImmersion_coe]
    exact Stacks.Chow.rationalFunctionsEquivFunctionField_rationalFunctionsRingEquivOfOpenImmersion
      U.ι (f : Stacks.Chow.rationalFunctions X)
  refine Subtype.ext (funext fun W => ?_)
  rw [weilDivisorRestrictEquiv_apply_val, principalDivisor_apply, principalDivisor_apply, hff,
    Stacks.Chow.ord_functionFieldEquiv_openImmersion,
    genericPoint_primeDivisorRestrictEquiv_symm]

/-- **Restriction carries the principal Weil divisors onto the principal Weil divisors.**  It
carries `div(f)` to `div(f|_U)`, and restriction of rational functions along a dominant open
immersion is a bijection. -/
theorem map_principalWeilDivisors_weilDivisorRestrictEquiv [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral U.toScheme] [IsDominant U.ι] :
    AddSubgroup.map (weilDivisorRestrictEquiv U hU : WeilDivisor X →+ WeilDivisor U.toScheme)
        (principalWeilDivisors X) =
      principalWeilDivisors U.toScheme := by
  refine le_antisymm ?_ ?_
  · rintro - ⟨-, ⟨f, rfl⟩, rfl⟩
    exact ⟨Stacks.Chow.rationalFunctionsUnitsMulEquivOfOpenImmersion U.ι f,
      (weilDivisorRestrictEquiv_principalDivisor U hU f).symm⟩
  · rintro - ⟨g, rfl⟩
    refine ⟨principalDivisor X
      ((Stacks.Chow.rationalFunctionsUnitsMulEquivOfOpenImmersion U.ι).symm g),
      ⟨_, rfl⟩, ?_⟩
    change weilDivisorRestrictEquiv U hU (principalDivisor X _) = _
    rw [weilDivisorRestrictEquiv_principalDivisor, MulEquiv.apply_symm_apply]

/-- **`Cl(U) = Cl(X)` for an open subscheme with a codimension `≥ 2` complement.**  On an integral
locally Noetherian scheme the Weil divisor class group of such an open subscheme is the Weil
divisor class group of the whole scheme: restriction is an isomorphism `Div(X) ≅ Div(U)` matching
principal divisors with principal divisors.

This is a step of the source's proof of [Stacks, Tag 0EBM], where it is what lets the class of a
rank one coherent reflexive module be read off from its restriction to the open subscheme supplied
by clause (3) of [Stacks, Tag 0AY6].

No `@[stacks 0EBM]` attribute is placed on this statement, deliberately.  The statement mentions
no module: it is an assertion about Weil divisors and their classes alone, and it is proved by
transporting divisors along a dominant open immersion, so it consumes none of the content of
Tag 0EBM, which asserts an isomorphism between `Cl(X)` and the group of isomorphism classes of
rank one coherent reflexive `𝒪_X`-modules.  That isomorphism is
`AlgebraicGeometry.CoherentReflexive.rankOneSkeletonMulEquivWeilDivisorClass` of
`StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/RankOneWeilClassSurjective.lean`, and the
injectivity direction of the tag is carried separately, in
`StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/DivisorClassFaithful.lean`. -/
@[sga "2 XI 3.8" "special case"]
def weilDivisorClassRestrictEquiv [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral U.toScheme] [IsDominant U.ι] :
    weilDivisorClassGroup X ≃+ weilDivisorClassGroup U.toScheme :=
  QuotientAddGroup.congr _ _ (weilDivisorRestrictEquiv U hU)
    (map_principalWeilDivisors_weilDivisorRestrictEquiv U hU)

/-- The restriction isomorphism of Weil divisor class groups sends the class of a Weil divisor to
the class of its restriction. -/
@[simp]
theorem weilDivisorClassRestrictEquiv_mk [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral U.toScheme] [IsDominant U.ι] (D : WeilDivisor X) :
    weilDivisorClassRestrictEquiv U hU (D : weilDivisorClassGroup X) =
      (weilDivisorRestrictEquiv U hU D : weilDivisorClassGroup U.toScheme) :=
  rfl

end CodimensionTwoComplement

end AlgebraicGeometry

end
