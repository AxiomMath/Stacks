module

public import StacksFrontier.AlgebraicGeometry.Chow.SmoothChowCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SmoothCapFundamentalPieces
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SmoothCapFundamentalZeroDimensionalPart
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekindBivariantOneDimensional
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ModificationProduct
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0FCB over a base which may have field components

Let `(S, δ)` be a base as in Stacks section 42.63: `S` is locally Noetherian with an open covering
by spectra of Dedekind domains, `δ = 0` at closed points and `δ = 1` elsewhere. A field is a
Dedekind domain, so `S` may have components which are points. Let `X` be smooth over `S` and
equidimensional of dimension `d`: every irreducible component of `X` has δ-dimension `d`.

**Stacks 0FCB, first clause.** The map `A^p(X) ⟶ CH_{d-p}(X)`, `c ↦ c ∩ [X]_d`, is an isomorphism
(`IsDedekindChowBase.chowCohomologyCapFundamentalClass_bijective_of_smooth_of_equidimensional`). No
hypothesis on the components of `S` is made.

**Stacks 0FCB, second clause.** "Via this isomorphism composition of bivariant classes turns into
the intersection product defined above." The intersection product of section 42.64 is
`α · β = Δ^!(α × β)` with the exterior product of section 42.63, which lands in degree `n + m - 1`.
Over the part `X₁` this holds as stated
(`IsDedekindChowBase.chowGroupRestrict_chowCohomologyCapFundamentalClass_mulId`). Over a
zero-dimensional component of `S` it is false as stated: there the exterior product of
section 42.63 of an `n`-cycle and an `m`-cycle is the `(n + m - 1)`-cycle of a scheme of pure
dimension `n + m`, hence zero, so the intersection product vanishes identically, while composition
does not. For `S = X = Spec k` and `d = 0` the product of `Θ(1) = [X]₀` with itself lands in
`CH_{-1}(X) = 0`, whereas `Θ(1 · 1) = [X]₀ ≠ 0`
(`not_chowCohomologyCapFundamentalClass_mulId_fieldChowSituation`). The second clause is therefore
stated over the part `X₁` of `X` over the one-dimensional part of `S`, which is all of `X` when `S`
has no zero-dimensional component; that is the corrected form.

## Main results

* `IsDedekindChowBase.chowCohomologyCapFundamentalClass_bijective_of_smooth_of_equidimensional` —
  **Stacks 0FCB**, first clause.
* `IsDedekindChowBase.chowGroupRestrict_chowCohomologyCapFundamentalClass_mulId` —
  **Stacks 0FCB**, second clause, over the one-dimensional part of `S`.
* `not_chowCohomologyCapFundamentalClass_mulId_fieldChowSituation` — the second clause fails over
  a field.

## References

* [Stacks Project, Tag 0FCB](https://stacks.math.columbia.edu/tag/0FCB)
* [Stacks Project, Section 42.63 (Tag 0FC3)](https://stacks.math.columbia.edu/tag/0FC3)
* [Stacks Project, Section 42.64 (Tag 0FC9)](https://stacks.math.columbia.edu/tag/0FC9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Generic points of an open subscheme -/

/-- The generic point of an irreducible component of an open subscheme `U ⊆ X` is the generic point
of an irreducible component of `X`. -/
theorem Scheme.Opens.ι_mem_genericPoints {X : Scheme.{u}} (U : X.Opens) {η : (U : Scheme.{u})}
    (hη : η ∈ genericPoints (U : Scheme.{u})) : U.ι.base η ∈ genericPoints X := by
  rw [mem_genericPoints_iff_forall_specializes_eq] at hη ⊢
  intro y hy
  have hyU : y ∈ U := hy.mem_open U.isOpen η.2
  have h' : (⟨y, hyU⟩ : (U : Scheme.{u})) ⤳ η :=
    Topology.IsInducing.subtypeVal.specializes_iff.mp hy
  exact congrArg Subtype.val (hη _ h')

/-- On a scheme with no points, `c ↦ c ∩ [X]_d` is bijective. -/
theorem chowCohomologyCapFundamentalClass_bijective_of_isEmpty (C : ChowSituation.{u})
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [IsEmpty X] (d p : ℤ) :
    Function.Bijective
      (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX d p) := by
  refine ⟨fun c c' _ ↦ ?_, fun α ↦
    ⟨0, @Subsingleton.elim _ (subsingleton_chowGroup_of_isEmpty C sX (d - p)) _ _⟩⟩
  rw [← sub_eq_zero, BivariantClass.eq_zero_iff_capsIntegral_canonical]
  intro T g _ _ k
  have : IsEmpty (pullback (𝟙 X) g : Scheme.{u}) :=
    ⟨fun z ↦ isEmptyElim ((pullback.fst (𝟙 X) g).base z)⟩
  exact @Subsingleton.elim _ (subsingleton_chowGroup_of_isEmpty C _ _) _ 0

namespace IsDedekindChowBase

variable {C : ChowSituation.{u}} (hS : IsDedekindChowBase C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] [Smooth sX]

/-! ### Equidimensionality -/

omit [Smooth sX] in
/-- A scheme whose irreducible components all have δ-dimension `d` has relative dimension `d` at
the generic point of each of its components. -/
theorem relativeDimension_genericPoint_of_equidimensional (d : ℤ)
    (hd : ∀ V : irreducibleComponents X,
      deltaDimension C sX ⟨V, V.2.1, isClosed_of_mem_irreducibleComponents _ V.2⟩ = d)
    {η : X} (hη : η ∈ genericPoints X) :
    relativeDimension C.dimensionFunction sX η = d := by
  rw [← deltaDimension_closure_singleton]
  exact hd ⟨closure {η}, hη⟩

omit [Smooth sX] in
/-- A scheme whose irreducible components all have δ-dimension `d` has δ-dimension at most `d`. -/
theorem schemeDeltaDimension_le_of_equidimensional (d : ℤ)
    (hd : ∀ V : irreducibleComponents X,
      deltaDimension C sX ⟨V, V.2.1, isClosed_of_mem_irreducibleComponents _ V.2⟩ = d) :
    schemeDeltaDimension C sX ≤ (d : EInt) :=
  iSup_le fun V ↦ (congrArg (fun z : ℤ ↦ (z : EInt)) (hd V)).le

/-- The part `X₁ = sX⁻¹(S₁)` of `X` over the one-dimensional part of the base. -/
abbrev oneDimensionalPartPreimage : X.Opens :=
  sX ⁻¹ᵁ hS.oneDimensionalPart

/-- The part `X₀ = sX⁻¹(S₀)` of `X` over the zero-dimensional part of the base. -/
abbrev zeroDimensionalPartPreimage : X.Opens :=
  sX ⁻¹ᵁ hS.zeroDimensionalPart

/-- On an open subscheme of a scheme whose components all have δ-dimension `d`, the relative
dimension at each generic point is `d`. -/
private theorem relativeDimension_opensι_genericPoint_of_equidimensional {Y : Scheme.{u}}
    (tY : Y ⟶ C.S) [LocallyOfFiniteType tY] (d : ℤ)
    (hd : ∀ V : irreducibleComponents Y,
      deltaDimension C tY ⟨V, V.2.1, isClosed_of_mem_irreducibleComponents _ V.2⟩ = d)
    (W : Y.Opens) {η : (W : Scheme.{u})} (hη : η ∈ genericPoints (W : Scheme.{u})) :
    relativeDimension C.dimensionFunction (W.ι ≫ tY) η = d := by
  rw [relativeDimension_opensι_comp]
  exact relativeDimension_genericPoint_of_equidimensional tY d hd
    (Scheme.Opens.ι_mem_genericPoints W hη)

include hS in
/-- **The part over `S₁` of a smooth scheme equidimensional of dimension `e + 1` has relative
dimension `e`.** -/
theorem relativeDimension_oneDimensionalPartPreimage (e : ℕ)
    (hd : ∀ V : irreducibleComponents X,
      deltaDimension C sX ⟨V, V.2.1, isClosed_of_mem_irreducibleComponents _ V.2⟩ = e + 1) :
    AlgebraicGeometry.RelativeDimension ((hS.oneDimensionalPartPreimage sX).ι ≫ sX) e := by
  have h := hS.relativeDimension_of_forall_not_isZeroDimensionalBasePoint
    ((hS.oneDimensionalPartPreimage sX).ι ≫ sX) (e + 1) (fun η hη ↦ by
      exact_mod_cast relativeDimension_opensι_genericPoint_of_equidimensional sX _ hd _ hη)
    (fun x ↦ x.2)
  simpa using h

/-! ### Stacks 0FCB, first clause -/

include hS in
/-- **Stacks 0FCB, first clause.** Let `(S, δ)` be a base as in section 42.63 of the Stacks Project
(locally the spectrum of a Dedekind domain, fields allowed; `δ = 0` at closed points and `1`
elsewhere), and let `X` be smooth over `S`, equidimensional of dimension `d`: every irreducible
component of `X` has δ-dimension `d`. Then

  `A^p(X) ⟶ CH_{d-p}(X)`,   `c ↦ c ∩ [X]_d`,

is an isomorphism for every `p ∈ ℤ`. -/
@[stacks 0FCB "first clause, in full: S as in section 42.63 with field components allowed, X \
smooth over S and equidimensional of dimension d (every irreducible component of δ-dimension \
d); bivariant classes are those of the Gysin system of invertible modules, \
`Stacks.Chow.gysinSystemOfInvertible`"]
theorem chowCohomologyCapFundamentalClass_bijective_of_smooth_of_equidimensional (d : ℕ)
    (hd : ∀ V : irreducibleComponents X,
      deltaDimension C sX ⟨V, V.2.1, isClosed_of_mem_irreducibleComponents _ V.2⟩ = d)
    (p : ℤ) :
    Function.Bijective
      (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX d p) := by
  have hgen := fun (W : X.Opens) (η : (W : Scheme.{u})) (hη : η ∈ genericPoints (W : Scheme.{u})) ↦
    relativeDimension_opensι_genericPoint_of_equidimensional sX d hd W hη
  have hU : IsClopenDecomposition fun i ↦ sX ⁻¹ᵁ hS.dimensionPart i :=
    hS.isClopenDecomposition_dimensionPart.preimage sX
  refine chowCohomologyCapFundamentalClass_bijective_of_isClopenDecomposition hU p d
    (schemeDeltaDimension_le_of_equidimensional sX d hd) fun i ↦ ?_
  rcases i with ⟨_ | _⟩
  · set W := sX ⁻¹ᵁ hS.dimensionPart ⟨false⟩
    have hX0 : ∀ x : (W : Scheme.{u}),
        IsZeroDimensionalBasePoint C ((W.ι ≫ sX).base x) := fun x ↦ x.2
    have he := hS.relativeDimension_of_forall_isZeroDimensionalBasePoint (W.ι ≫ sX) d
      (fun η hη ↦ hgen W η hη) hX0
    exact hS.chowCohomologyCapFundamentalClass_bijective_of_forall_mem_zeroDimensional
      hS.zeroDimensionalPart (fun _ hs ↦ hs) (W.ι ≫ sX) (fun x ↦ x.2) d he p
      (compStructureFlatPullbackClass_bijective C (W.ι ≫ sX) d he p)
  · set W := sX ⁻¹ᵁ hS.dimensionPart ⟨true⟩
    have hX1 : ∀ x : (W : Scheme.{u}),
        ¬ IsZeroDimensionalBasePoint C ((W.ι ≫ sX).base x) := fun x ↦ x.2
    by_cases hd0 : d = 0
    · have : IsEmpty (W : Scheme.{u}) := by
        refine ⟨fun x ↦ ?_⟩
        set Z : irreducibleComponents (W : Scheme.{u}) := ⟨irreducibleComponent x,
          irreducibleComponent_mem_irreducibleComponents x⟩
        set η := genericPoints.ofComponent Z
        have hη := hgen W η.1 η.2
        have hgS : ((W.ι ≫ sX).base η.1) ∈ genericPoints C.S :=
          mem_genericPoints_of_flat (W.ι ≫ sX) η.2
        have hδ1 : C.dimensionFunction ((W.ι ≫ sX).base η.1) = 1 :=
          hS.2.2 _ fun hcl ↦ hX1 η.1 ⟨hcl, hgS⟩
        have hge : C.dimensionFunction ((W.ι ≫ sX).base η.1) ≤
            relativeDimension C.dimensionFunction (W.ι ≫ sX) η.1 := by
          change _ ≤ C.dimensionFunction ((W.ι ≫ sX).base η.1) +
            (Cardinal.toNat (residueTrdeg (W.ι ≫ sX) η.1) : ℤ)
          omega
        rw [hη, hδ1, hd0] at hge
        omega
      exact chowCohomologyCapFundamentalClass_bijective_of_isEmpty C _ _ _
    · obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 1 := ⟨d - 1, by omega⟩
      have he := hS.relativeDimension_of_forall_not_isZeroDimensionalBasePoint (W.ι ≫ sX) (e + 1)
        (fun η hη ↦ hgen W η hη) hX1
      simp only [add_tsub_cancel_right] at he
      have h := chowCohomologyCapFundamentalClass_bijective_of_bivariantCapBaseFundamentalClass C
        (W.ι ≫ sX) e he p (hS.schemeDeltaDimension_le_one _)
        (compStructureFlatPullbackClass_bijective C (W.ι ≫ sX) e he p)
        (bivariantCapBaseFundamentalClass_bijective_of_forall_not_isZeroDimensionalBasePoint C
          (W.ι ≫ sX) _ hS hX1)
      have hcast : ((e + 1 : ℕ) : ℤ) = (e : ℤ) + 1 := by push_cast; ring
      rwa [hcast]

/-! ### Stacks 0FCB, second clause -/

include hS in
/-- **Stacks 0FCB, second clause**, corrected form: over the one-dimensional part of the base. Let
`(S, δ)` be a base as in section 42.63 (field components allowed), and let `X` be smooth over `S`
and equidimensional of dimension `e + 1`. Write `X₁ ⊆ X` for the open and closed part over the
one-dimensional part `S₁` of `S`; it is smooth of relative dimension `e` over `S`. Then via
`Θ : c ↦ c ∩ [X]_{e+1}` composition of bivariant classes turns into the intersection product of
section 42.64 on `X₁`, formed with the Gysin class `Δ^!` of the diagonal of `X₁` (Stacks 0FBR):

  `Θ(a · b)|_{X₁} = Θ(a)|_{X₁} · Θ(b)|_{X₁}`.

When `S` has no zero-dimensional component, `X₁ = X`. Over the zero-dimensional part the clause is
false as stated, the exterior product of section 42.63 vanishing there identically
(`Stacks.Chow.not_chowCohomologyCapFundamentalClass_mulId_fieldChowSituation`); for `X`
equidimensional of dimension `0` the part `X₁` is empty. -/
@[stacks 0FCB "second clause, corrected form: Θ(a · b) = Θ(a) · Θ(b) on the part X₁ of X over the \
one-dimensional part of S (all of X when S has no zero-dimensional component), with the \
intersection product of section 42.64 formed with the Gysin class Δ^! of the diagonal; over a \
zero-dimensional component the clause is false as stated, see \
`Stacks.Chow.not_chowCohomologyCapFundamentalClass_mulId_fieldChowSituation`; S as in section \
42.63 with field components allowed, X smooth and equidimensional of dimension e + 1"]
theorem chowGroupRestrict_chowCohomologyCapFundamentalClass_mulId (e : ℕ)
    (hd : ∀ V : irreducibleComponents X,
      deltaDimension C sX ⟨V, V.2.1, isClosed_of_mem_irreducibleComponents _ V.2⟩ = e + 1)
    (p q : ℤ) (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
    (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sX q) :
    chowGroupRestrict C sX ((hS.oneDimensionalPartPreimage sX).ι ≫ sX)
        (hS.oneDimensionalPartPreimage sX).ι rfl ((e : ℤ) + 1 - (p + q))
        (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX (e + 1) (p + q)
          (a.mulId C sX b)) =
      chowGroupDegreeEquiv C ((hS.oneDimensionalPartPreimage sX).ι ≫ sX)
        (by ring : ((e : ℤ) + 1 - p) + ((e : ℤ) + 1 - q) - 1 - e = (e + 1) - (p + q))
        (chowGroupSelfProductUnitCollapse C ((hS.oneDimensionalPartPreimage sX).ι ≫ sX)
          (((e : ℤ) + 1 - p) + ((e : ℤ) + 1 - q) - 1 - e)
          (hS.intersectionProduct (gysinSystemOfInvertible C)
            ((hS.oneDimensionalPartPreimage sX).ι ≫ sX) (𝟙 _) (𝟙 _) e
            (bivariantClassCongrBase C (gysinSystemOfInvertible C)
              (pullback.diagonal ((hS.oneDimensionalPartPreimage sX).ι ≫ sX))
              (diagonal_comp_selfProductStructure C ((hS.oneDimensionalPartPreimage sX).ι ≫ sX))
              rfl e (diagonalGysinClass C ((hS.oneDimensionalPartPreimage sX).ι ≫ sX)
                ((hS.oneDimensionalPartPreimage sX).ι ≫ sX)
                (hS.relativeDimension_oneDimensionalPartPreimage sX e hd)))
            ((e : ℤ) + 1 - p) ((e : ℤ) + 1 - q)
            (chowGroupCongr C (Category.id_comp _).symm ((e : ℤ) + 1 - p)
              (chowGroupRestrict C sX ((hS.oneDimensionalPartPreimage sX).ι ≫ sX)
                (hS.oneDimensionalPartPreimage sX).ι rfl ((e : ℤ) + 1 - p)
                (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX (e + 1) p a))
              ⊗ₜ[ℤ] chowGroupCongr C (Category.id_comp _).symm ((e : ℤ) + 1 - q)
                (chowGroupRestrict C sX ((hS.oneDimensionalPartPreimage sX).ι ≫ sX)
                  (hS.oneDimensionalPartPreimage sX).ι rfl ((e : ℤ) + 1 - q)
                  (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX (e + 1) q
                    b))))) := by
  set W := hS.oneDimensionalPartPreimage sX
  have hdim := schemeDeltaDimension_le_of_equidimensional sX ((e : ℤ) + 1) hd
  have he := hS.relativeDimension_oneDimensionalPartPreimage sX e hd
  have hX1 : ∀ x : (W : Scheme.{u}), ¬ IsZeroDimensionalBasePoint C ((W.ι ≫ sX).base x) :=
    fun x ↦ x.2
  rw [chowGroupRestrict_chowCohomologyCapFundamentalClass C sX W (p + q) _ hdim,
    chowGroupRestrict_chowCohomologyCapFundamentalClass C sX W p _ hdim,
    chowGroupRestrict_chowCohomologyCapFundamentalClass C sX W q _ hdim]
  change chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) (W.ι ≫ sX) (e + 1)
      (p + q) (chowCohomologyRestriction C (gysinSystemOfInvertible C) sX W.ι (p + q)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) (a.mulId C sX b)) = _
  rw [chowCohomologyRestriction_mulId]
  exact hS.chowCohomologyCapFundamentalClass_mulId (W.ι ≫ sX) e he _
    (diagonalGysinClass_bivariantCommute C (W.ι ≫ sX) (W.ι ≫ sX) he)
    (diagonalGysinClass_compFlatPullbackEqOne_snd C (W.ι ≫ sX) (W.ι ≫ sX) he (𝟙 C.S)
      (Category.comp_id _)) p q
    (fun c' ↦
      isExteriorProductOverBase_bivariantCapBaseFundamentalClass_of_forall_not_isZeroDimBasePoint
        (W.ι ≫ sX) _ hS hX1 c') _ _

end IsDedekindChowBase

/-! ### The second clause fails over a field -/

section Counterexample

variable (k : Type u) [Field k]

/-- **The second clause of Stacks 0FCB is false as stated over a field.** For `S = X = Spec k` with
`δ ≡ 0` (a base as in section 42.63, `Stacks.Chow.isDedekindChowBase_fieldChowSituation`), `X` is
smooth over `S` and equidimensional of dimension `d = 0`, of relative dimension `0`. The
intersection product of section 42.64 is formed with the exterior product of section 42.63, which
lands in degree `n + m - 1`; so the product of `Θ(1) ∈ CH_0(X)` with itself lies in
`CH_{-1}(X ×_X X)`, which is zero, for every class of the diagonal. But `Θ(1 · 1) = [X]_0 ≠ 0` in
`CH_0(X)`, so `Θ(1 · 1)` is not the intersection product `Θ(1) · Θ(1)` under any identification of
the degrees. -/
theorem not_chowCohomologyCapFundamentalClass_mulId_fieldChowSituation :
    chowCohomologyCapFundamentalClass (fieldChowSituation k)
        (gysinSystemOfInvertible (fieldChowSituation k)) (𝟙 (fieldChowSituation k).S) 0 (0 + 0)
        ((bivariantIdentityClassOfInvertible (fieldChowSituation k)
          (𝟙 (fieldChowSituation k).S)).mulId (fieldChowSituation k)
          (𝟙 (fieldChowSituation k).S)
          (bivariantIdentityClassOfInvertible (fieldChowSituation k)
            (𝟙 (fieldChowSituation k).S))) ≠ 0 ∧
      ∀ (c : BivariantClass (fieldChowSituation k)
          (gysinSystemOfInvertible (fieldChowSituation k)) (𝟙 (fieldChowSituation k).S)
          (selfProductStructure (fieldChowSituation k) (𝟙 (fieldChowSituation k).S))
          (pullback.diagonal (𝟙 (fieldChowSituation k).S))
          (diagonal_comp_selfProductStructure (fieldChowSituation k)
            (𝟙 (fieldChowSituation k).S)) 0)
        (t : TensorProduct ℤ
          (chowGroup (fieldChowSituation k)
            (𝟙 (fieldChowSituation k).S ≫ 𝟙 (fieldChowSituation k).S) 0)
          (chowGroup (fieldChowSituation k)
            (𝟙 (fieldChowSituation k).S ≫ 𝟙 (fieldChowSituation k).S) 0)),
        (isDedekindChowBase_fieldChowSituation k).intersectionProduct
          (gysinSystemOfInvertible (fieldChowSituation k)) (𝟙 (fieldChowSituation k).S)
          (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S) 0 c 0 0 t = 0 := by
  set C := fieldChowSituation k
  constructor
  · intro h0
    set one := bivariantIdentityClassOfInvertible C (𝟙 C.S)
    have hΘ : chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) (𝟙 C.S) 0 (0 + 0)
        (one.mulId C (𝟙 C.S) one) ≍ fundamentalChowClass C (𝟙 C.S) 0 := by
      rw [← chowCohomologyCap_fundamentalChowClass]
      refine (chowCohomologyCap_heq_idRule_ofGysinSystem C _ (𝟙 C.S) (0 + 0) _ 0 _).trans ?_
      refine (BivariantClass.idRule_mulId C (𝟙 C.S) one one (𝟙 C.S) 0 _).trans ?_
      refine (idRule_bivariantIdentityClassOfInvertible_heq C (𝟙 C.S) (𝟙 C.S) (0 - 0) _).trans ?_
      refine (idRule_bivariantIdentityClassOfInvertible_heq C (𝟙 C.S) (𝟙 C.S) 0 _).trans ?_
      exact chowGroupCongr_heq C _ 0 _
    have hfund : fundamentalChowClass C (𝟙 C.S) 0 = 0 :=
      eq_of_heq (hΘ.symm.trans ((heq_of_eq h0).trans (heq_zero_chowGroup_of_degree_eq C _
        (by ring))))
    have hrel : relativeDimension C.dimensionFunction (𝟙 C.S) (genericPoint C.S) = 0 :=
      relativeDimension_id_fieldChowSituation_eq_zero k _
    have hmem : fundamentalCycle C (𝟙 C.S) 0 ∈ rationalEquivalences C (𝟙 C.S) 0 :=
      (QuotientAddGroup.eq_zero_iff _).mp hfund
    have hzero := eq_zero_of_isRationallyEquivalentToZero_fieldChowSituation k _ hmem
    have hval : (fundamentalCycle C (𝟙 C.S) 0).1 (genericPoint C.S) =
        (0 : CycleGroup C (𝟙 C.S) 0).1 (genericPoint C.S) := by rw [hzero]
    rw [fundamentalCycle_eq_single C (𝟙 C.S) genericPoints_eq_singleton hrel
      (Field.toIsField _)] at hval
    simp [Function.locallyFinsuppWithin.single_apply] at hval
  · intro c t
    have : Subsingleton (CycleGroup C (pullback.fst (𝟙 C.S) (𝟙 C.S) ≫ (𝟙 C.S ≫ 𝟙 C.S))
        (0 + 0 - 1 - 0)) := by
      refine ⟨fun x y ↦ Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)⟩
      have hnn : 0 ≤ relativeDimension C.dimensionFunction
          (pullback.fst (𝟙 C.S) (𝟙 C.S) ≫ (𝟙 C.S ≫ 𝟙 C.S)) z := by
        change 0 ≤ C.dimensionFunction _ + (Cardinal.toNat (residueTrdeg _ z) : ℤ)
        have h0 : C.dimensionFunction ((pullback.fst (𝟙 C.S) (𝟙 C.S) ≫ (𝟙 C.S ≫ 𝟙 C.S)).base z)
            = 0 := rfl
        omega
      have h₀ : ∀ w : CycleGroup C (pullback.fst (𝟙 C.S) (𝟙 C.S) ≫ (𝟙 C.S ≫ 𝟙 C.S))
          (0 + 0 - 1 - 0), w.1 z = 0 := fun w ↦ by
        by_contra h
        have := (mem_cyclesOfDimension_iff_forall_point C _ _ w.1).1 w.2 z h
        omega
      rw [h₀ x, h₀ y]
    have := Quotient.instSubsingletonQuotient (QuotientAddGroup.leftRel
      (rationalEquivalences C (pullback.fst (𝟙 C.S) (𝟙 C.S) ≫ (𝟙 C.S ≫ 𝟙 C.S)) (0 + 0 - 1 - 0)))
    exact Subsingleton.elim _ _

end Counterexample

end Stacks.Chow

end
