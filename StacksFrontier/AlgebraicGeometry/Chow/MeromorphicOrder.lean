module

public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClass.PrimeDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder.Stalk
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary.PrincipalCycle

/-!
# The order of vanishing of a meromorphic section, and its Weil divisor

Let `X` be a locally Noetherian integral scheme with generic point `η` and function field
`R(X) = 𝒪_{X, η}`, and let `L` be an invertible `𝒪_X`-module. The Stacks Project attaches to a
nonzero meromorphic section `s` of `L` and a prime divisor `Z ⊆ X` with generic point `ξ` the
integer
`ord_{Z, L}(s) = ord_{𝒪_{X, ξ}}(s / s_ξ)`,
where `s_ξ` is a generator of the stalk `L_ξ` and `s / s_ξ` is the rational function expressing
`s` in terms of it; the integer does not depend on the choice of `s_ξ` because two generators
differ by a unit of `𝒪_{X, ξ}`, which has order zero. Letting `Z` vary gives the Weil divisor
`div_L(s) = ∑_Z ord_{Z, L}(s) [Z]`, and the finiteness that makes this a divisor at all is that
`s` generates `L` over some nonempty open set, so only the prime divisors in the complement
contribute.

**Meromorphic sections.** On an integral scheme the sheaf of meromorphic sections `K_X(L)` of a
quasi-coherent `L` is the constant sheaf with value the generic stalk `L_η` (Stacks 01X5 (2)),
so a global meromorphic section of `L` is an element of `L_η`, regular exactly when it is
nonzero. Here a meromorphic section is the element `s : L.presheaf.stalk (genericPoint X)`.
Stacks 01X5 (2) is
`Stacks.AlgebraicGeometry.MeromorphicConstantModule.meromorphicSectionSheafIsoConstant` and
`AlgebraicGeometry.nonempty_meromorphicSectionSheafIsoConstant`, but nothing below is stated
against a section of `K_X(L)`, so no declaration carries the `@[stacks 02SF]` or
`@[stacks 0BE6]` attribute: the source statements are recovered only by composing the
definitions here with Stacks 01X5 (2).

**Invertibility.** It enters only through the rank-one condition
`Stacks.Divisors.IsTrivializedNear`, an explicit hypothesis: `L` is trivialized near a point when
some neighbourhood of it has a section of `L` whose germs are bases of the stalks. The order of
vanishing at `Z` needs it only at the generic point of `Z`; the Weil divisor needs it at every
point.

## Main definitions

* `Stacks.Divisors.toGenericStalk` — the specialization map `L_x → L_η`.
* `Stacks.Divisors.IsCoordinateAt` — `a ∈ R(X)` expresses `s` in terms of a basis of `L_x`.
* `Stacks.Divisors.orderOfVanishing` — `ord_{Z, L}(s)` (Stacks 02SF).
* `Stacks.Divisors.weilDivisorOfMeromorphicSection` — `div_L(s) ∈ Div(X)` (Stacks 0BE6 (1)).

## Main results

* `Stacks.Divisors.exists_isCoordinateAt` and
  `Stacks.Divisors.ord_eq_ord_of_isCoordinateAt` — a coordinate exists, and its order of
  vanishing does not depend on the chosen basis: this is the well-definedness of Stacks 02SF.
* `Stacks.Divisors.orderOfVanishing_eq` — the characterization of `ord_{Z, L}(s)` by any
  coordinate.
* `Stacks.Divisors.mem_weilDivisor_of_forall_exists_open` — a coefficient family on prime
  divisors is a Weil divisor as soon as every point has an open neighbourhood meeting only
  finitely many of the relevant generic points.
* `Stacks.Divisors.locallyFinite_orderOfVanishing_ne_zero` — the prime divisors along which `s`
  has nonzero order form a locally finite collection (Stacks 02SG, second collection).
* `Stacks.Divisors.orderOfVanishing_smul` and
  `Stacks.Divisors.orderOfVanishing_eq_add_ord_of_eq_smul` — the divisors of two nonzero
  meromorphic sections differ by the principal divisor of their ratio (Stacks 02SH), stated
  coefficientwise.
* `Stacks.Divisors.existsUnique_smul_eq` — two nonzero meromorphic sections of `L` have a
  unique ratio in `R(X)`.

## References

* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 02SG](https://stacks.math.columbia.edu/tag/02SG)
* [Stacks Project, Tag 02SH](https://stacks.math.columbia.edu/tag/02SH)
* [Stacks Project, Tag 0BE6](https://stacks.math.columbia.edu/tag/0BE6)
* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Order TopologicalSpace

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-! ### The generic stalk -/

section IrreducibleSpace

variable [IrreducibleSpace X] (L : X.Modules)

/-- The specialization map `L_x → L_η` from the stalk of `L` at a point to its stalk at the
generic point. Its value at a basis of `L_x` is the local trivialization of `L` at `x`, read
generically. -/
def toGenericStalk (x : X) (m : L.presheaf.stalk x) : L.presheaf.stalk (genericPoint X) :=
  L.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) m

variable {L}

/-- The specialization map to the generic stalk is semilinear over the structure map
`𝒪_{X, x} → R(X)`. -/
theorem toGenericStalk_smul {x : X} (r : X.presheaf.stalk x) (m : L.presheaf.stalk x) :
    toGenericStalk L x (r • m) =
      algebraMap (X.presheaf.stalk x) X.functionField r • toGenericStalk L x m := by
  rw [toGenericStalk, toGenericStalk, Scheme.Modules.stalkSpecializes_smul]
  rfl

/-- The generic value of the germ of a section at a point is its germ at the generic point. -/
theorem toGenericStalk_germ {W : X.Opens} {x : X} (hx : x ∈ W) (hη : genericPoint X ∈ W)
    (t : Γ(L, W)) :
    toGenericStalk L x (L.presheaf.germ W x hx t) = L.presheaf.germ W (genericPoint X) hη t :=
  TopCat.Presheaf.germ_stalkSpecializes_apply ..

/-- The generic point lies in every open set a trivialization of `L` is given on. -/
theorem genericPoint_mem_of_mem {W : X.Opens} {x : X} (hx : x ∈ W) : genericPoint X ∈ W :=
  ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr ⟨x, Set.mem_univ x, hx⟩

/-- Where `L` is trivialized near `x`, the generic value of a basis of `L_x` is a basis of the
generic stalk `L_η` over the function field. -/
theorem IsStalkBasis.toGenericStalk {x : X} (hL : IsTrivializedNear L x)
    {m : L.presheaf.stalk x} (hm : IsStalkBasis L x m) :
    IsStalkBasis L (genericPoint X) (toGenericStalk L x m) := by
  obtain ⟨W, hxW, t, ht⟩ := hL
  have hηW : genericPoint X ∈ W := genericPoint_mem_of_mem hxW
  obtain ⟨u, hu, hmu⟩ := exists_isUnit_smul_eq (ht x hxW) hm
  rw [hmu, toGenericStalk_smul, toGenericStalk_germ hxW hηW]
  exact (ht _ hηW).smul_of_isUnit (hu.map (algebraMap (X.presheaf.stalk x) X.functionField))

end IrreducibleSpace

/-! ### Coordinates of a meromorphic section -/

section Coordinate

variable [IsIntegral X] [IsLocallyNoetherian X] (L : X.Modules)

/-- `a ∈ R(X)` is a **coordinate at `x`** of the meromorphic section `s` of `L`, given by its
generic value `s ∈ L_η`, when `s = a · m` in `L_η` for some basis `m` of the stalk `L_x`; the
source writes `a` as `s / s_x`. -/
def IsCoordinateAt (x : X) (s : L.presheaf.stalk (genericPoint X)) (a : X.functionField) : Prop :=
  ∃ m : L.presheaf.stalk x, IsStalkBasis L x m ∧ s = a • toGenericStalk L x m

variable {L}

omit [IsLocallyNoetherian X] in
/-- Where `L` is trivialized near `x`, every meromorphic section of `L` has a coordinate at
`x`. -/
theorem exists_isCoordinateAt {x : X} (hL : IsTrivializedNear L x)
    (s : L.presheaf.stalk (genericPoint X)) : ∃ a : X.functionField, IsCoordinateAt L x s a := by
  obtain ⟨W, hxW, t, ht⟩ := hL
  obtain ⟨a, ha⟩ := (IsStalkBasis.toGenericStalk ⟨W, hxW, t, ht⟩ (ht x hxW)).surjective s
  exact ⟨a, L.presheaf.germ W x hxW t, ht x hxW, ha.symm⟩

omit [IsLocallyNoetherian X] in
/-- A coordinate of a nonzero meromorphic section is nonzero. -/
theorem IsCoordinateAt.ne_zero {x : X} {s : L.presheaf.stalk (genericPoint X)}
    {a : X.functionField} (ha : IsCoordinateAt L x s a) (hs : s ≠ 0) : a ≠ 0 := by
  obtain ⟨m, -, hsa⟩ := ha
  exact left_ne_zero_of_smul (hsa ▸ hs)

/-- **Well-definedness of the order of vanishing, Stacks 02SF.** Two coordinates of the same
meromorphic section at the same point have the same order. -/
theorem ord_eq_ord_of_isCoordinateAt {x : X} (hL : IsTrivializedNear L x)
    {s : L.presheaf.stalk (genericPoint X)} {a a' : X.functionField}
    (ha : IsCoordinateAt L x s a) (ha' : IsCoordinateAt L x s a') :
    X.ord a x = X.ord a' x := by
  by_cases! hx : coheight x ≠ 1
  · simp [hx]
  obtain ⟨m, hm, hsa⟩ := ha
  obtain ⟨m', hm', hsa'⟩ := ha'
  obtain ⟨u, hu, hmu⟩ := exists_isUnit_smul_eq hm hm'
  have hm'u : toGenericStalk L x m' =
      algebraMap (X.presheaf.stalk x) X.functionField u • toGenericStalk L x m := by
    rw [hmu, toGenericStalk_smul]
  have key : a = a' * algebraMap (X.presheaf.stalk x) X.functionField u := by
    refine (hm.toGenericStalk hL).injective ?_
    change a • toGenericStalk L x m = (a' * _) • toGenericStalk L x m
    rw [mul_smul, ← hm'u, ← hsa', hsa]
  rcases eq_or_ne a' 0 with rfl | ha'0
  · simp [key]
  rw [key, X.ord_mul ha'0 (by
      simpa using (map_ne_zero_iff _
        (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)).mpr hu.ne_zero),
    Scheme.ord_algebraMap_of_isUnit hx hu, add_zero]

end Coordinate

/-! ### The order of vanishing along a prime divisor -/

section OrderOfVanishing

variable [IsIntegral X] [IsLocallyNoetherian X] (L : X.Modules)

/-- The **order of vanishing of a meromorphic section along a prime divisor** (Stacks 02SF):
the order of vanishing in the local ring `𝒪_{X, ξ}` at the generic point `ξ` of `Z` of any
coordinate of `s` there, and `0` if `s` has no coordinate at `ξ`. The meromorphic section is
given by its generic value `s ∈ L_η`. Where `L` is trivialized near `ξ` the value does not depend
on the coordinate chosen (`Stacks.Divisors.orderOfVanishing_eq`). -/
def orderOfVanishing (s : L.presheaf.stalk (genericPoint X)) (Z : PrimeDivisor X) : ℤ :=
  open Classical in
  if h : ∃ a : X.functionField, IsCoordinateAt L Z.genericPoint s a then
    X.ord h.choose Z.genericPoint
  else 0

variable {L}

/-- **The characterization of the order of vanishing, Stacks 02SF.** Where `L` is trivialized
near the generic point of `Z`, the order of vanishing of `s` along `Z` is the order of vanishing
of any coordinate of `s` there. -/
theorem orderOfVanishing_eq {s : L.presheaf.stalk (genericPoint X)} {Z : PrimeDivisor X}
    (hL : IsTrivializedNear L Z.genericPoint) {a : X.functionField}
    (ha : IsCoordinateAt L Z.genericPoint s a) :
    orderOfVanishing L s Z = X.ord a Z.genericPoint := by
  have h : ∃ a : X.functionField, IsCoordinateAt L Z.genericPoint s a := ⟨a, ha⟩
  exact (dite_eq_left h).trans (ord_eq_ord_of_isCoordinateAt hL h.choose_spec ha)

/-- The order of vanishing of the zero section is zero. -/
@[simp]
theorem orderOfVanishing_zero {Z : PrimeDivisor X} (hL : IsTrivializedNear L Z.genericPoint) :
    orderOfVanishing L (0 : L.presheaf.stalk (genericPoint X)) Z = 0 := by
  obtain ⟨-, m, hm, -⟩ := exists_isCoordinateAt hL 0
  rw [orderOfVanishing_eq hL (a := 0) ⟨m, hm, by rw [zero_smul]⟩]
  simp

/-- **Stacks 02SH, coefficientwise.** Rescaling a nonzero meromorphic section by a nonzero
rational function adds the order of vanishing of that function. -/
theorem orderOfVanishing_smul {Z : PrimeDivisor X} (hL : IsTrivializedNear L Z.genericPoint)
    {c : X.functionField} (hc : c ≠ 0) {s : L.presheaf.stalk (genericPoint X)} (hs : s ≠ 0) :
    orderOfVanishing L (c • s) Z = X.ord c Z.genericPoint + orderOfVanishing L s Z := by
  obtain ⟨a, m, hm, hsa⟩ := exists_isCoordinateAt hL s
  rw [orderOfVanishing_eq hL ⟨m, hm, hsa⟩,
    orderOfVanishing_eq hL (a := c * a) ⟨m, hm, by rw [hsa, smul_smul]⟩]
  exact X.ord_mul hc (IsCoordinateAt.ne_zero ⟨m, hm, hsa⟩ hs)

/-- **Stacks 02SH, coefficientwise.** The orders of vanishing of two nonzero meromorphic
sections of `L` differ by the order of vanishing of their ratio. -/
theorem orderOfVanishing_eq_add_ord_of_eq_smul {Z : PrimeDivisor X}
    (hL : IsTrivializedNear L Z.genericPoint)
    {s s' : L.presheaf.stalk (genericPoint X)} (hs' : s' ≠ 0) {f : X.functionField}
    (hf : f ≠ 0) (hsf : s = f • s') :
    orderOfVanishing L s Z = orderOfVanishing L s' Z + X.ord f Z.genericPoint := by
  rw [hsf, orderOfVanishing_smul hL hf hs', add_comm]

omit [IsLocallyNoetherian X] in
/-- **Stacks 02SH, the ratio.** Two meromorphic sections of `L` with the second one nonzero have
a unique ratio in the function field, provided `L` is trivialized near the generic point. -/
theorem existsUnique_smul_eq (hL : IsTrivializedNear L (genericPoint X))
    {s s' : L.presheaf.stalk (genericPoint X)} (hs' : s' ≠ 0) :
    ∃! f : X.functionField, s = f • s' := by
  obtain ⟨W, hxW, t, ht⟩ := hL
  set b := L.presheaf.germ W (genericPoint X) hxW t
  have hbasis : IsStalkBasis L (genericPoint X) b := ht _ hxW
  obtain ⟨c, hc⟩ := hbasis.surjective s
  obtain ⟨c', hc'⟩ := hbasis.surjective s'
  replace hc : c • b = s := hc
  replace hc' : c' • b = s' := hc'
  have hc'0 : c' ≠ 0 := left_ne_zero_of_smul (hc' ▸ hs')
  refine ⟨c * c'⁻¹, ?_, ?_⟩
  · change s = (c * c'⁻¹) • s'
    rw [← hc, ← hc', smul_smul, inv_mul_cancel_right₀ hc'0]
  · intro g (hg : s = g • s')
    exact (eq_mul_inv_iff_mul_eq₀ hc'0).mpr
      (hbasis.injective (by rw [mul_smul, hc', ← hg, hc] : (g * c') • b = c • b))

end OrderOfVanishing

/-! ### Local finiteness and the Weil divisor -/

section WeilDivisor

/-- A coefficient family on the prime divisors of `X` is a Weil divisor as soon as every point
has an **open** neighbourhood containing only finitely many generic points of prime divisors
with nonzero coefficient. -/
theorem mem_weilDivisor_of_forall_exists_open {D : PrimeDivisor X → ℤ}
    (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      {Z : PrimeDivisor X | Z.genericPoint ∈ U ∧ D Z ≠ 0}.Finite) :
    D ∈ WeilDivisor X := by
  intro x
  obtain ⟨U, hUopen, hxU, hfin⟩ := h x
  refine ⟨U, hUopen.mem_nhds hxU, hfin.subset fun Z hZ ↦ ?_⟩
  simp only [Set.mem_ofPred_eq] at hZ
  have hD : D Z ≠ 0 := by
    by_contra hD
    rw [ite_eq_left hD] at hZ
    exact hZ.ne_empty (Set.empty_inter U)
  rw [ite_eq_right hD] at hZ
  obtain ⟨y, hyZ, hyU⟩ := hZ
  rw [Z.support_eq_closure] at hyZ
  exact ⟨(specializes_iff_mem_closure.mpr hyZ).mem_open hUopen hyU, hD⟩

/-
`AlgebraicGeometry.mem_weilDivisor_of_forall_exists_open`
(`StacksFrontier/AlgebraicGeometry/Divisors/WeilDivisorClass/GenericPoint.lean`) is identical to
the theorem above in docstring, statement and proof, and is NOT a duplicate of it.
`PrimeDivisor` and `WeilDivisor` are written unqualified in both files and resolve to different
constants. Asking the elaborator:

  Stacks.Divisors.mem_weilDivisor_of_forall_exists_open :
    ∀ {X} {D : Stacks.Divisors.PrimeDivisor X → ℤ},
      (∀ x, ∃ U, IsOpen U ∧ x ∈ U ∧ {Z | Z.genericPoint ∈ U ∧ D Z ≠ 0}.Finite) →
        D ∈ Stacks.Divisors.WeilDivisor X
  AlgebraicGeometry.mem_weilDivisor_of_forall_exists_open :
    ∀ {X} {D : AlgebraicGeometry.PrimeDivisor X → ℤ},
      (∀ x, ∃ U, IsOpen U ∧ x ∈ U ∧ {Z | Z.genericPoint ∈ U ∧ D Z ≠ 0}.Finite) →
        D ∈ AlgebraicGeometry.WeilDivisor X

Merging the two would leave one copy's consumers holding a lemma about the other's divisors.

THE FORK UNDERNEATH. The scheme-level prime-divisor development exists three times, under
three DISTINCT fully-qualified names — so there is no name collision between them, only
duplicated mathematics:

  Stacks.Divisors.PrimeDivisor
      StacksFrontier/AlgebraicGeometry/Chow/FirstChernClass/PrimeDivisor.lean
  AlgebraicGeometry.PrimeDivisor
      StacksFrontier/AlgebraicGeometry/Divisors/PrimeDivisor.lean
  StacksDraft.AlgebraicGeometry.Divisors.PrimeDivisorWeilGroup.PrimeDivisor
      StacksFrontier/AlgebraicGeometry/Divisors/PrimeDivisorWeilGroup.lean

The third's namespace carries a stray `StacksDraft.` prefix, which is itself worth fixing by
whoever owns that file. A fourth, `AlgebraicGeometry.Space.PrimeDivisor`
(`StacksFrontier/AlgebraicGeometry/Spaces/WeilDivisor.lean`), is the
algebraic-space notion over `B S hS X` and is not part of the fork.

Collapsing the three is Stacks tag 0BE2 and is the prerequisite for merging the lemma pair
above.
-/

variable [IsIntegral X] [IsLocallyNoetherian X] {L : X.Modules}

/-- **Stacks 02SG, second collection.** The prime divisors along which a meromorphic section of
`L` has nonzero order form a locally finite collection of closed subsets of `X`. -/
theorem locallyFinite_orderOfVanishing_ne_zero (hL : ∀ x : X, IsTrivializedNear L x)
    (s : L.presheaf.stalk (genericPoint X)) :
    (fun Z : PrimeDivisor X => orderOfVanishing L s Z) ∈ WeilDivisor X := by
  refine mem_weilDivisor_of_forall_exists_open fun x => ?_
  obtain ⟨W, hxW, t, ht⟩ := hL x
  have hηW : genericPoint X ∈ W := genericPoint_mem_of_mem hxW
  obtain ⟨f, hf⟩ := (ht _ hηW).surjective s
  replace hf : f • L.presheaf.germ W (genericPoint X) hηW t = s := hf
  obtain ⟨V, hV, hfin⟩ := Stacks.Chow.locallyFiniteSupport_ord X f x
  refine ⟨(W : Set X) ∩ interior V, W.isOpen.inter isOpen_interior,
    ⟨hxW, mem_interior_iff_mem_nhds.mpr hV⟩, ?_⟩
  have hmaps : ∀ Z : PrimeDivisor X, Z.genericPoint ∈ (W : Set X) ∩ interior V →
      orderOfVanishing L s Z ≠ 0 →
      Z.genericPoint ∈ V ∩ Function.support (X.ord f) := by
    intro Z hZ hne
    have hco : IsCoordinateAt L Z.genericPoint s f :=
      ⟨L.presheaf.germ W Z.genericPoint hZ.1 t, ht _ hZ.1, by
        rw [toGenericStalk_germ hZ.1 hηW, hf]⟩
    refine ⟨interior_subset hZ.2, ?_⟩
    rwa [Function.mem_support, ← orderOfVanishing_eq (hL _) hco]
  refine Set.Finite.of_finite_image (f := PrimeDivisor.genericPoint)
    (hfin.subset ?_) PrimeDivisor.genericPoint_injective.injOn
  rintro - ⟨Z, ⟨hZU, hZne⟩, rfl⟩
  exact hmaps Z hZU hZne

/-- **The Weil divisor of a nonzero meromorphic section, Stacks 0BE6 (1).**
`div_L(s) = ∑_Z ord_{Z, L}(s) [Z] ∈ Div(X)`, where the sum is over prime divisors and the
meromorphic section is given by its generic value `s ∈ L_η`. -/
def weilDivisorOfMeromorphicSection (hL : ∀ x : X, IsTrivializedNear L x)
    (s : L.presheaf.stalk (genericPoint X)) : WeilDivisor X :=
  ⟨fun Z => orderOfVanishing L s Z, locallyFinite_orderOfVanishing_ne_zero hL s⟩

/-- The coefficient of `div_L(s)` at a prime divisor is the order of vanishing of `s` there. -/
@[simp]
theorem weilDivisorOfMeromorphicSection_apply (hL : ∀ x : X, IsTrivializedNear L x)
    (s : L.presheaf.stalk (genericPoint X)) (Z : PrimeDivisor X) :
    (weilDivisorOfMeromorphicSection hL s).val Z = orderOfVanishing L s Z :=
  rfl

end WeilDivisor

end Stacks.Divisors

end
