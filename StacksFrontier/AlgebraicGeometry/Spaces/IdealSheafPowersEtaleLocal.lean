module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IdealSheafPowers
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompSlice
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp

/-!
# Powers of a sheaf of ideals commute with étale localization

Let `φ : U ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, let `𝓘 ⊆ 𝒪_Y` be a sheaf of ideals on the small étale site of `Y` and let
`𝓙 ⊆ 𝒪_U` be a sheaf of ideals on the small étale site of `U` whose ideal of sections over every
étale chart `W` of `U` is the ideal of sections of `𝓘` over the composite chart `W ⟶ U ⟶ Y`.
Then the same holds for all the powers:

`𝓙ⁿ = 𝓘ⁿ|_U`.

## Main definitions

* `AlgebraicGeometry.Space.etaleRestrictionSection`: a section of `𝒪_U` over an étale chart of
  `U`, read as a section of `𝒪_Y` over the postcomposed chart.
* `AlgebraicGeometry.Space.etaleRestrictionIdealSheafZPow` and
  `AlgebraicGeometry.Space.etaleRestrictionIdealSheafZPowSheaf`: the étale restriction of the
  integer-indexed family of powers of `𝓘`, taken inside the submodules of `𝒪_U`, first as a
  family of ideals indexed by the étale charts of `U` and then as a sheaf submodule of `𝒪_U`.

## Main results

* `AlgebraicGeometry.Space.powSieve_etaleRestriction`: the membership sieve of a power of `𝓙` is
  the pullback along postcomposition of the membership sieve of the same power of `𝓘`.
* `AlgebraicGeometry.Space.idealAt_idealSheafPow_etaleRestriction` and
  `AlgebraicGeometry.Space.idealAt_idealSheafZPow_etaleRestriction`: the chartwise equality of
  the powers, for natural and for integer exponents.
* `AlgebraicGeometry.Space.etaleModulePullback_idealSheafZPow_eq`: the étale restriction of `𝓘ⁿ`
  is equal to `𝓙ⁿ` as an `𝒪_U`-module.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U Y : AlgebraicSpaces B S hS} (φ : U ⟶ Y) (hφ : IsEtale B S hS φ.hom)

/-- A section of the structure sheaf of `U` over an étale chart `V`, read as a section of the
structure sheaf of `Y` over the postcomposed chart `V ⟶ U ⟶ Y`; the two rings of regular
functions are the same, and this is the identity function. -/
def etaleRestrictionSection (V : SmallEtale B S hS U.1)
    (x : ToType ((structureRingSheaf B S hS U).obj.obj (op V))) :
    ToType ((structureRingSheaf B S hS Y).obj.obj
      (op ((smallEtalePostcomp B S hS φ hφ).obj V))) :=
  x

/-! ### The membership sieves of the powers -/

section Sieves

variable (𝓘 : (SheafOfModules.unit (structureRingSheaf B S hS Y)).Submodule)
    (𝓙 : (SheafOfModules.unit (structureRingSheaf B S hS U)).Submodule)
    (h : ∀ W : SmallEtale B S hS U.1,
      SheafOfModules.idealAt 𝓙 (op W) =
        SheafOfModules.idealAt 𝓘 (op ((smallEtalePostcomp B S hS φ hφ).obj W)))

include h

/-- A section of `𝒪_U` over an étale chart `V` of `U` restricts into the `n`-th power of the ideal
of sections of `𝓙` over a chart `W ⟶ V` exactly when it restricts into the `n`-th power of the
ideal of sections of `𝓘` over the postcomposed chart. -/
theorem mem_powSieve_etaleRestriction_iff (n : ℕ) {V W : SmallEtale B S hS U.1} (g : W ⟶ V)
    (x : ToType ((structureRingSheaf B S hS U).obj.obj (op V))) :
    SheafOfModules.powSieve 𝓙 n x g ↔
      SheafOfModules.powSieve 𝓘 n (etaleRestrictionSection B S hS φ hφ V x)
        ((smallEtalePostcomp B S hS φ hφ).map g) := by
  rw [SheafOfModules.mem_powSieve_iff, SheafOfModules.mem_powSieve_iff, h W]
  exact Iff.rfl

/-- The membership sieve of a power of `𝓙` is the pullback of the membership sieve of the same
power of `𝓘` along postcomposition with `φ`. -/
theorem powSieve_etaleRestriction (n : ℕ) (V : SmallEtale B S hS U.1)
    (x : ToType ((structureRingSheaf B S hS U).obj.obj (op V))) :
    SheafOfModules.powSieve 𝓙 n x =
      (SheafOfModules.powSieve 𝓘 n
        (etaleRestrictionSection B S hS φ hφ V x)).functorPullback
          (smallEtalePostcomp B S hS φ hφ) :=
  Sieve.ext fun _W g ↦ mem_powSieve_etaleRestriction_iff B S hS φ hφ 𝓘 𝓙 h n g x

/-- Membership in a power of `𝓙` over an étale chart of `U` is membership in the same power of
`𝓘` over the postcomposed chart of `Y`. -/
theorem mem_idealSheafPow_etaleRestriction_iff (n : ℕ) (V : SmallEtale B S hS U.1)
    (x : ToType ((structureRingSheaf B S hS U).obj.obj (op V))) :
    x ∈ SheafOfModules.idealAt (SheafOfModules.idealSheafPow 𝓙 n) (op V) ↔
      etaleRestrictionSection B S hS φ hφ V x ∈
        SheafOfModules.idealAt (SheafOfModules.idealSheafPow 𝓘 n)
          (op ((smallEtalePostcomp B S hS φ hφ).obj V)) := by
  rw [SheafOfModules.mem_idealSheafPow_iff, SheafOfModules.mem_idealSheafPow_iff]
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · refine (SmallEtale.topology B S hS Y.1).superset_covering ?_
      ((SmallEtale.coverPreserving_smallEtalePostcomp B S hS φ hφ).cover_preserve hx)
    rintro A f ⟨W, g, k, hg, rfl⟩
    exact (SheafOfModules.powSieve 𝓘 n
      (etaleRestrictionSection B S hS φ hφ V x)).downward_closed
      ((mem_powSieve_etaleRestriction_iff B S hS φ hφ 𝓘 𝓙 h n g x).1 hg) k
  · refine (SmallEtale.topology B S hS U.1).superset_covering ?_
      (SmallEtale.smallEtalePostcomp_cover_lift B S hS φ hφ V _ hx)
    intro W g hg
    exact (mem_powSieve_etaleRestriction_iff B S hS φ hφ 𝓘 𝓙 h n g x).2 hg

/-- The ideal of sections of `𝓙ⁿ` over an étale chart `V` of `U` is the ideal of sections of `𝓘ⁿ`
over the composite chart `V ⟶ U ⟶ Y`. -/
theorem idealAt_idealSheafPow_etaleRestriction (n : ℕ) (V : SmallEtale B S hS U.1) :
    SheafOfModules.idealAt (SheafOfModules.idealSheafPow 𝓙 n) (op V) =
      SheafOfModules.idealAt (SheafOfModules.idealSheafPow 𝓘 n)
        (op ((smallEtalePostcomp B S hS φ hφ).obj V)) :=
  Ideal.ext fun x ↦ mem_idealSheafPow_etaleRestriction_iff B S hS φ hφ 𝓘 𝓙 h n V x

/-- For an integer `n`, the ideal of sections of `𝓙ⁿ` over an étale chart `V` of `U` is the ideal
of sections of `𝓘ⁿ` over the composite chart `V ⟶ U ⟶ Y`. -/
theorem idealAt_idealSheafZPow_etaleRestriction (n : ℤ) (V : SmallEtale B S hS U.1) :
    SheafOfModules.idealAt (SheafOfModules.idealSheafZPow 𝓙 n) (op V) =
      SheafOfModules.idealAt (SheafOfModules.idealSheafZPow 𝓘 n)
        (op ((smallEtalePostcomp B S hS φ hφ).obj V)) := by
  rcases lt_or_ge n 0 with hn | hn
  · rw [SheafOfModules.idealSheafZPow_of_neg 𝓙 hn, SheafOfModules.idealSheafZPow_of_neg 𝓘 hn,
      SheafOfModules.idealAt_zeroIdealSheaf, SheafOfModules.idealAt_zeroIdealSheaf]
    exact rfl
  · rw [SheafOfModules.idealSheafZPow_of_nonneg 𝓙 hn,
      SheafOfModules.idealSheafZPow_of_nonneg 𝓘 hn]
    exact idealAt_idealSheafPow_etaleRestriction B S hS φ hφ 𝓘 𝓙 h n.toNat V

end Sieves

/-! ### The étale restriction of the family of powers -/

section Restriction

variable (𝓘 : (SheafOfModules.unit (structureRingSheaf B S hS Y)).Submodule)

/-- The étale restriction along `φ : U ⟶ Y` of the `n`-th power of a sheaf of ideals `𝓘 ⊆ 𝒪_Y`,
as a family of submodules of `𝒪_U` indexed by the étale charts of `U`: its sections over a chart
`V` are the sections of `𝓘ⁿ` over the postcomposed chart `V ⟶ U ⟶ Y`. -/
noncomputable def etaleRestrictionIdealSheafZPow (n : ℤ) :
    (SheafOfModules.unit (structureRingSheaf B S hS U)).val.Submodule where
  obj V := SheafOfModules.idealAt (SheafOfModules.idealSheafZPow 𝓘 n)
    (op ((smallEtalePostcomp B S hS φ hφ).obj V.unop))
  map f := (SheafOfModules.idealSheafZPow 𝓘 n).map
    ((smallEtalePostcomp B S hS φ hφ).op.map f)

variable (𝓙 : (SheafOfModules.unit (structureRingSheaf B S hS U)).Submodule)
    (h : ∀ W : SmallEtale B S hS U.1,
      SheafOfModules.idealAt 𝓙 (op W) =
        SheafOfModules.idealAt 𝓘 (op ((smallEtalePostcomp B S hS φ hφ).obj W)))

include h

/-- The étale restriction of the `n`-th power of `𝓘` is, chartwise, the `n`-th power of `𝓙`. -/
theorem etaleRestrictionIdealSheafZPow_eq (n : ℤ) :
    etaleRestrictionIdealSheafZPow B S hS φ hφ 𝓘 n =
      (SheafOfModules.idealSheafZPow 𝓙 n).toSubmodule :=
  PresheafOfModules.Submodule.ext fun V ↦
    (idealAt_idealSheafZPow_etaleRestriction B S hS φ hφ 𝓘 𝓙 h n V.unop).symm

/-- The étale restriction of the `n`-th power of `𝓘`, as a sheaf submodule of `𝒪_U`. -/
noncomputable def etaleRestrictionIdealSheafZPowSheaf (n : ℤ) :
    (SheafOfModules.unit (structureRingSheaf B S hS U)).Submodule where
  toSubmodule := etaleRestrictionIdealSheafZPow B S hS φ hφ 𝓘 n
  isSheaf := by
    rw [etaleRestrictionIdealSheafZPow_eq B S hS φ hφ 𝓘 𝓙 h n]
    exact (SheafOfModules.idealSheafZPow 𝓙 n).isSheaf

/-- The étale restriction of the `n`-th power of `𝓘` is the `n`-th power of `𝓙`, as sheaf
submodules of `𝒪_U`. -/
theorem etaleRestrictionIdealSheafZPowSheaf_eq (n : ℤ) :
    etaleRestrictionIdealSheafZPowSheaf B S hS φ hφ 𝓘 𝓙 h n =
      SheafOfModules.idealSheafZPow 𝓙 n :=
  SheafOfModules.Submodule.ext (etaleRestrictionIdealSheafZPow_eq B S hS φ hφ 𝓘 𝓙 h n)

/-- The étale restriction of the `n`-th power of `𝓘` is equal to the `n`-th power of `𝓙`, as
`𝒪_U`-modules. -/
theorem etaleModulePullback_idealSheafZPow_eq (n : ℤ) :
    (etaleModulePullback.{u, u} B S hS φ hφ).obj
        (SheafOfModules.idealSheafZPow 𝓘 n).toSheafOfModules =
      (SheafOfModules.idealSheafZPow 𝓙 n).toSheafOfModules := by
  rw [← etaleRestrictionIdealSheafZPowSheaf_eq B S hS φ hφ 𝓘 𝓙 h n]
  rfl

end Restriction

end AlgebraicGeometry.Space

end
