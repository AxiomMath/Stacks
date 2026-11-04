module

public import StacksFrontier.LinearAlgebra.ExteriorPower.DerivedSquareBaseChange
public import StacksFrontier.LinearAlgebra.ExteriorPower.DerivedSquareCrossEffect
public import StacksFrontier.RingTheory.RegularLocalRing.GlobalDimension
public import StacksFrontier.RingTheory.Support.FiniteDimensional
public import StacksFrontier.RingTheory.Tor.ProjectiveDimension

/-!
# Vanishing of the derived exterior square above twice the projective dimension

Let `A` be a commutative ring and `M` an `A`-module. The derived exterior squares `LᵢΛ²(M)` of
Dold and Puppe (`Stacks.DerivedSquare.homology`) vanish in high degrees when `M` has finite
projective dimension: if `pd M ≤ d` then `LᵢΛ²(M) = 0` for `i > 2d`, and even for `i ≥ 2d` when
`d ≥ 1`. This is the bound expected from `Λ²` being a functor of degree `2`.

**Projective modules.** For a projective object `X` of an abelian category the constant
simplicial object on `X` is a simplicial projective resolution of `X`, whose Moore complex is
homotopy equivalent to `X` in degree `0` by its extra degeneracy. Applying a functor `F` termwise
keeps it constant, so `LᵢF(X) = 0` for every `i > 0` and every functor `F`; in particular
`LᵢΛ²(P) = 0` for `i > 0` and `P` projective.

**Dimension shifting.** Let `0 → Ω → P → M → 0` be exact with `P` projective. The cross-effect
long exact sequences of a simplicial horseshoe over it
(`Stacks.DerivedSquare.exact_filtration_middle`, `Stacks.DerivedSquare.exact_exteriorSquare_right`)
give exact sequences

  `LⱼΛ²(Ω) → Hⱼ(Fil) → Torⱼ(Ω, M)` and `Lⱼ₊₁Λ²(P) → Lⱼ₊₁Λ²(M) → Hⱼ(Fil)`,

so `Lⱼ₊₁Λ²(M) = 0` as soon as `LⱼΛ²(Ω) = 0` and `Torⱼ(Ω, M) = 0`. If `pd M ≤ d + 1` then
`pd Ω ≤ d`, so `Torⱼ(Ω, M) = 0` for `j > d`, and by induction on `d` the vanishing of
`LⱼΛ²(Ω)` for `j > 2d` gives that of `LᵢΛ²(M)` for `i > 2d + 1`.

**Consequences.** A module of finite projective dimension has only finitely many nonzero derived
exterior squares. Over a Noetherian ring they are finitely generated when `M` is
(`Stacks.DerivedSquare.finite_homology`), and their supports lie in that of `M`
(`Stacks.DerivedSquare.support_homology_subset`), so they have finite length when `M` has. Over a
regular local ring of dimension `≤ c` every module has projective dimension `≤ c` (Stacks 00O7),
so `LᵢΛ²(M) = 0` for `i > 2c`.

## Main definitions

* `Stacks.SimplicialProjectiveResolution.const`: the constant simplicial projective resolution of
  a projective object.

## Main results

* `Stacks.SimplicialProjectiveResolution.isZero_derivedHomology_of_projective`: `LᵢF(X) = 0` for
  `i > 0` and `X` projective, for any functor `F`.
* `Stacks.DerivedSquare.isZero_homology_succ_of_shortExact`: dimension shifting along
  `0 → Ω → P → M → 0` with `P` projective.
* `Stacks.DerivedSquare.isZero_homology_of_hasProjectiveDimensionLE`: `pd M ≤ d` implies
  `LᵢΛ²(M) = 0` for `i > 2d`, and
  `Stacks.DerivedSquare.isZero_homology_of_hasProjectiveDimensionLE_succ`: `pd M ≤ d + 1`
  implies `LᵢΛ²(M) = 0` for `i > 2d + 1`.
* `Stacks.DerivedSquare.isZero_homology_of_projectiveResolution`: the same bound from a projective
  resolution of `M` of length `≤ d`.
* `Stacks.DerivedSquare.finite_setOf_not_isZero_homology`: finite projective dimension implies
  that only finitely many `LᵢΛ²(M)` are nonzero.
* `Stacks.DerivedSquare.isFiniteLength_homology`: over a Noetherian ring, the derived exterior
  squares of a module of finite length have finite length.
* `Stacks.DerivedSquare.isZero_homology_of_isRegularLocalRing`: over a regular local ring of
  dimension `≤ c`, `LᵢΛ²(M) = 0` for `i > 2c`.

## Implementation notes

The projective dimension is Mathlib's `CategoryTheory.HasProjectiveDimensionLE`, measured by
vanishing of `Ext`; the bridge to resolutions is
`CategoryTheory.hasProjectiveDimensionLE_tfae_leftResolution` (Stacks 0CXC). The bound is proved
by dimension shifting through the cross-effect sequences, rather than by showing that the
normalized Moore complex of `Λ²(Γ(K))` vanishes above degree `2d` for a resolution `K` of
length `d`: the former needs only the long exact sequences and the identification of the cross
term with `Tor`, and it gives the sharper bound `2d - 1` for `d ≥ 1` at no extra cost.

## References

* A. Dold, D. Puppe, *Homologie nicht-additiver Funktoren. Anwendungen*, Ann. Inst. Fourier 11
  (1961), 201–312.
* L. Illusie, *Complexe cotangent et déformations I*, Lecture Notes in Math. 239 (1971),
  chapitre I, §4.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite Simplicial

universe v u v' u'

namespace Stacks

namespace SimplicialProjectiveResolution

/-! ### The constant resolution of a projective object -/

section Const

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The constant simplicial object on a projective object `X` is a simplicial projective
resolution of `X`: its Moore complex is homotopy equivalent to `X` in degree `0`. -/
def const (X : C) [Projective X] : SimplicialProjectiveResolution X where
  obj := (SimplicialObject.const C).obj X
  projective _ := ‹Projective X›
  π := (constHomotopyEquiv X).hom

variable {D : Type u'} [Category.{v'} D] [Abelian D] (F : C ⥤ D)

/-- The complex `s(F(X))` of the constant resolution of a projective object `X` is homotopy
equivalent to `F(X)` in degree `0`: applying `F` termwise to a constant simplicial object gives
the constant simplicial object on `F(X)`. -/
def derivedComplexConstHomotopyEquiv (X : C) [Projective X] :
    HomotopyEquiv ((const X).derivedComplex F) ((ChainComplex.single₀ D).obj (F.obj X)) :=
  (HomotopyEquiv.ofIso ((alternatingFaceMapComplex D).mapIso
    (Functor.constComp SimplexCategoryᵒᵖ X F))).trans (constHomotopyEquiv (F.obj X))

/-- **Simplicial derived functors vanish on projectives in positive degrees.** For a projective
object `X`, `LᵢF(X) = 0` for every `i ≠ 0`, computed from any simplicial projective resolution of
`X`. -/
theorem isZero_derivedHomology_of_projective {X : C} [Projective X]
    (P : SimplicialProjectiveResolution X) {i : ℕ} (hi : i ≠ 0) :
    IsZero (P.derivedHomology F i) :=
  ((HomologicalComplex.isZero_single_obj_homology _ _ _ _ hi).of_iso
    ((derivedComplexConstHomotopyEquiv F X).toHomologyIso i)).of_iso (derivedIso F P (const X) i)

end Const

end SimplicialProjectiveResolution

namespace DerivedSquare

open SimplicialProjectiveResolution

variable {A : Type u} [CommRing A]

/-! ### Projective modules and dimension shifting -/

/-- **`LᵢΛ²` of a projective module vanishes in positive degrees.** -/
theorem isZero_homology_of_projective {M : ModuleCat.{u} A} [Projective M]
    (P : SimplicialProjectiveResolution M) {i : ℕ} (hi : i ≠ 0) : IsZero (homology P i) :=
  isZero_derivedHomology_of_projective _ P hi

/-- **Dimension shifting for the derived exterior square.** Let `0 → Ω → P → M → 0` be a short
exact sequence of modules with `P` projective. If `LⱼΛ²(Ω) = 0` and `Torⱼ(Ω, M) = 0`, then
`Lⱼ₊₁Λ²(M) = 0`. -/
theorem isZero_homology_succ_of_shortExact {S : ShortComplex (ModuleCat.{u} A)}
    (hS : S.ShortExact) [Projective S.X₂] (P₁ : SimplicialProjectiveResolution S.X₁)
    (P₃ : SimplicialProjectiveResolution S.X₃) {j : ℕ} (h₁ : IsZero (homology P₁ j))
    (hT : IsZero (((Tor' (ModuleCat.{u} A) j).obj S.X₁).obj S.X₃)) :
    IsZero (homology P₃ (j + 1)) := by
  let H := SimplicialHorseshoe.ofResolutions P₁ P₃ hS
  have hFil : IsZero ((filtrationComplex H).homology j) :=
    (exact_filtration_middle H j).isZero_X₂ (h₁.eq_of_src _ _)
      ((hT.of_iso (crossHomologyIsoTor H j)).eq_of_tgt _ _)
  exact (exact_exteriorSquare_right H j).isZero_X₂
    ((isZero_homology_of_projective H.P₂ (Nat.succ_ne_zero j)).eq_of_src _ _)
    (hFil.eq_of_tgt _ _)

/-- The inductive step: the bound `2d` for modules of projective dimension `≤ d` gives the bound
`2d + 1` for modules of projective dimension `≤ d + 1`, by dimension shifting along a projective
cover. -/
private lemma isZero_homology_of_hasProjectiveDimensionLE_succ_aux {d : ℕ}
    (ih : ∀ (N : ModuleCat.{u} A), HasProjectiveDimensionLE N d →
      ∀ (Q : SimplicialProjectiveResolution N) (j : ℕ), 2 * d < j → IsZero (homology Q j))
    {M : ModuleCat.{u} A} (hM : HasProjectiveDimensionLE M (d + 1))
    (P : SimplicialProjectiveResolution M) {i : ℕ} (hi : 2 * d + 1 < i) :
    IsZero (homology P i) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  let p : Projective.over M ⟶ M := Projective.π M
  let S : ShortComplex (ModuleCat.{u} A) := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel p }
  have : Projective S.X₂ := Projective.projective_over M
  have hΩ : HasProjectiveDimensionLE S.X₁ d := (hS.hasProjectiveDimensionLT_X₃_iff d this).1 hM
  exact isZero_homology_succ_of_shortExact hS (Classical.arbitrary _) P
    (ih _ hΩ _ _ (by omega))
    (StacksDraft.ProjectiveDimension.isZero_Tor'_of_hasProjectiveDimensionLE _ _ d j hΩ
      (by omega))

/-! ### The Dold–Puppe bound -/

/-- **Dold–Puppe bound.** If `M` has projective dimension at most `d`, then `LᵢΛ²(M) = 0` for
every `i > 2d`. -/
theorem isZero_homology_of_hasProjectiveDimensionLE {M : ModuleCat.{u} A} {d : ℕ}
    (hM : HasProjectiveDimensionLE M d) (P : SimplicialProjectiveResolution M) {i : ℕ}
    (hi : 2 * d < i) : IsZero (homology P i) := by
  induction d generalizing M i with
  | zero =>
    have : Projective M := (projective_iff_hasProjectiveDimensionLE_zero M).2 hM
    exact isZero_homology_of_projective P (by omega)
  | succ d ih =>
    exact isZero_homology_of_hasProjectiveDimensionLE_succ_aux (fun _ hN Q _ hj => ih hN Q hj)
      hM P (by omega)

/-- **Dold–Puppe bound, sharp form.** If `M` has projective dimension at most `d + 1`, then
`LᵢΛ²(M) = 0` for every `i > 2d + 1`, that is, for `i ≥ 2(d + 1)`. -/
theorem isZero_homology_of_hasProjectiveDimensionLE_succ {M : ModuleCat.{u} A} {d : ℕ}
    (hM : HasProjectiveDimensionLE M (d + 1)) (P : SimplicialProjectiveResolution M) {i : ℕ}
    (hi : 2 * d + 1 < i) : IsZero (homology P i) :=
  isZero_homology_of_hasProjectiveDimensionLE_succ_aux
    (fun _ hN Q _ hj => isZero_homology_of_hasProjectiveDimensionLE hN Q hj) hM P hi

/-- **Dold–Puppe bound, from a resolution.** If `M` has a projective resolution `K` whose terms
vanish in degrees `> d`, then `LᵢΛ²(M) = 0` for every `i > 2d`. -/
theorem isZero_homology_of_projectiveResolution {M : ModuleCat.{u} A} {d : ℕ}
    (K : ProjectiveResolution M) (hK : ∀ n, d < n → IsZero (K.complex.X n))
    (P : SimplicialProjectiveResolution M) {i : ℕ} (hi : 2 * d < i) : IsZero (homology P i) :=
  have hM : HasProjectiveDimensionLE M d :=
    ((hasProjectiveDimensionLE_tfae_leftResolution M d).out 2 1).1
      (Exists.intro (leftResolutionOfProjectiveResolution K K.projective) hK)
  isZero_homology_of_hasProjectiveDimensionLE hM P hi

/-! ### Consequences -/

/-- A module of finite projective dimension has vanishing derived exterior squares above some
degree. -/
theorem exists_isZero_homology_of_projectiveDimension_ne_top {M : ModuleCat.{u} A}
    (hM : projectiveDimension M ≠ ⊤) (P : SimplicialProjectiveResolution M) :
    ∃ b : ℕ, ∀ i, b < i → IsZero (homology P i) := by
  obtain ⟨d, hd⟩ := (projectiveDimension_ne_top_iff M).1 hM
  exact ⟨2 * d, fun i hi => isZero_homology_of_hasProjectiveDimensionLE hd P hi⟩

/-- **Only finitely many derived exterior squares are nonzero.** If `M` has finite projective
dimension, then `LᵢΛ²(M) ≠ 0` for only finitely many `i`. -/
theorem finite_setOf_not_isZero_homology {M : ModuleCat.{u} A}
    (hM : projectiveDimension M ≠ ⊤) (P : SimplicialProjectiveResolution M) :
    {i : ℕ | ¬ IsZero (homology P i)}.Finite := by
  obtain ⟨b, hb⟩ := exists_isZero_homology_of_projectiveDimension_ne_top hM P
  exact (Set.finite_Iic b).subset fun i hi => not_lt.1 fun h => hi (hb i h)

/-- **Finite length.** Over a Noetherian ring, the derived exterior squares of a module of finite
length have finite length: they are finitely generated, and their support lies in the support of
the module, a finite set of closed points. -/
theorem isFiniteLength_homology [IsNoetherianRing A] {M : ModuleCat.{u} A}
    (hM : IsFiniteLength A M) (P : SimplicialProjectiveResolution M) (i : ℕ) :
    IsFiniteLength A (homology P i) := by
  have : IsNoetherian A M := (isFiniteLength_iff_isNoetherian_isArtinian.1 hM).1
  have := finite_homology P i
  obtain ⟨hfin, hclosed⟩ := (Module.isFiniteLength_iff_support_finite_subset_closedPoints A M).1 hM
  have hsub := support_homology_subset P i
  exact (Module.isFiniteLength_iff_support_finite_subset_closedPoints A (homology P i)).2
    ⟨hfin.subset hsub, hsub.trans hclosed⟩

/-! ### Regular local rings -/

/-- **Regular local rings.** Over a regular local ring `R` of Krull dimension at most `c`, every
`R`-module `M` has `LᵢΛ²(M) = 0` for `i > 2c`: it has projective dimension at most `c`
(Stacks 00O7). -/
theorem isZero_homology_of_isRegularLocalRing {R : Type u} [CommRing R] [IsRegularLocalRing R]
    {c : ℕ} (hc : ringKrullDim R ≤ (c : WithBot ℕ∞)) {M : ModuleCat.{u} R}
    (P : SimplicialProjectiveResolution M) {i : ℕ} (hi : 2 * c < i) : IsZero (homology P i) :=
  isZero_homology_of_hasProjectiveDimensionLE
    ((IsRegularLocalRing.exists_leftResolution_free_finite_and_hasProjectiveDimensionLE hc).2 M)
    P hi

end DerivedSquare

end Stacks
