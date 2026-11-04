module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.Depth
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplex
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDuality
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.Duality
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.DualizingComplex
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverFieldDuality
public import StacksFrontier.RingTheory.Depth.Defs.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# The dualizing complex `f^×𝒪_{Spec k}` of a proper scheme of dimension at most one

Let `X` be a proper scheme of dimension at most one over a field `k`, with structure morphism
`f : X ⟶ Spec k`, and let

  `ω_X^• = f^×(𝒪_{Spec k}) = a(𝒪_{Spec k})`

be the value at `𝒪_{Spec k}` of the right adjoint `a` of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_{Spec k})`
([Stacks, Tag 0A9E]), which is `Stacks.Duality.dualizingComplexOverField f`, and let
`ω_X = H^{-1}(ω_X^•)`, which is `Stacks.Duality.dualizingSheafOverField f`. This file proves, for
this complex, that it is a dualizing complex and clauses (1)–(4) of [Stacks, Tag 0BS2].

## Main results

* `Stacks.Duality.isDualizingComplex_dualizingComplexOverField` — `ω_X^•` is a dualizing complex.
* `Stacks.Duality.isZero_homology_dualizingComplexOverField_of_ne` — clause (1): `H^i(ω_X^•)` is
  nonzero only for `i = -1, 0`.
* `Stacks.Duality.isCoherent_dualizingSheafOverField_of_isProper`,
  `Stacks.Duality.sheafIsCohenMacaulay_dualizingSheafOverField` and
  `Stacks.Duality.supp_dualizingSheafOverField` — clause (2): `ω_X` is a coherent
  Cohen--Macaulay module whose support is the union of the irreducible components of dimension `1`.
* `Stacks.Duality.nontrivial_stalk_homology_zero_dualizingComplexOverField_iff` — clause (3): at
  a closed point `x`, `H^0(ω_{X,x}^•)` is nonzero exactly when `dim 𝒪_{X,x} = 0`, or
  `dim 𝒪_{X,x} = 1` and `𝒪_{X,x}` is not Cohen--Macaulay.
* `Stacks.Duality.bijective_dualityLinearMap_dualizingComplexOverField` — clause (4): for `K` in
  `D_QCoh(𝒪_X)` the duality map `Ext^i_X(K, ω_X^•) ⟶ Hom_k(H^{-i}(X, K), k)` is bijective; its
  functoriality and compatibility with shifts and distinguished triangles are
  `Stacks.Duality.dualityEquiv_comp`, `Stacks.Duality.dualityLinearMap_shift` and
  `Stacks.Duality.dualityLinearMap_triangle`.

## Implementation notes

The proofs follow the source: `ω_X^•` is the complex of [Stacks, Tag 0FVV], which is a dualizing
complex whose cohomology lives in degrees `[-dim X, 0]`, whose module `H^{-dim X}(ω_X^•)` is
coherent with property `(S₂)` and supported on the components of dimension `dim X`, and whose
stalks at closed points have depth-controlled cohomology. With `dim X ≤ 1` these read as clauses
(1)–(3):

* when `dim X = 1`, `ω_X = H^{-1}(ω_X^•)` is the module of [Stacks, Tag 0FVV], and on a scheme
  of dimension at most one, property `(S₂)` is Cohen--Macaulayness, since the support of every
  stalk has dimension at most one;
* when `dim X ≤ 0` (this includes `X = ∅`), `ω_X = 0` by the degree bound, and `X` has no
  irreducible component of dimension `1`.

The stalk `H^0(ω_{X,x}^•)` of clause (3) is written as the stalk at `x` of the cohomology sheaf
`H^0(ω_X^•)`, as in part (4) of [Stacks, Tag 0FVV]; the stalk functor is exact, so the two agree.

## References

* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0FVV](https://stacks.math.columbia.edu/tag/0FVV)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- A space of dimension at most one has dimension one or dimension at most zero. -/
private theorem topologicalKrullDim_eq_one_or_le_zero (hdim : topologicalKrullDim X ≤ 1) :
    topologicalKrullDim X = 1 ∨ topologicalKrullDim X ≤ 0 := by
  rcases eq_or_lt_of_le hdim with h | h
  · exact Or.inl h
  · right
    cases hd : topologicalKrullDim X with
    | bot => exact bot_le
    | coe d =>
      rw [hd] at h
      have hd1 : d < 1 := by exact_mod_cast h
      have hd0 : d ≤ 0 := (Order.lt_one_iff.mp hd1).le
      exact_mod_cast hd0

/-- The Krull dimension of a local ring of a scheme is bounded by the dimension of the scheme. -/
private theorem ringKrullDim_stalk_le_topologicalKrullDim' (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk X]
  exact le_iSup (fun z : X => ringKrullDim (X.presheaf.stalk z)) x

/-- **`ω_X^• = f^×(𝒪_{Spec k})` is a dualizing complex** on a proper scheme over a field
([Stacks, Tag 0FVV]). -/
@[stacks 0BS2 "the existence assertion: ω_X^• = f^× O_{Spec k} is a dualizing complex"]
theorem isDualizingComplex_dualizingComplexOverField :
    letI := LocallyOfFiniteType.isLocallyNoetherian f
    IsDualizingComplex (dualizingComplexOverField f).obj :=
  isDualizingComplex_relativeDualizingComplex_of_isProper f

/-- If `dim X ≤ n`, a nonzero cohomology sheaf `H^i(ω_X^•)` has `i ≤ 0` and `-i ≤ n`. -/
private theorem le_zero_and_toNat_neg_le_of_not_isZero (n : ℕ) (hdim : topologicalKrullDim X ≤ n)
    (i : ℤ) (hi : ¬ IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj
      (dualizingComplexOverField f).obj)) :
    i ≤ 0 ∧ (-i).toNat ≤ n := by
  obtain ⟨h₁, h₂⟩ := le_zero_and_le_dim_of_not_isZero_homology_of_isProper f i hi
  exact ⟨h₁, by exact_mod_cast h₂.trans hdim⟩

/-- **[Stacks, Tag 0BS2], clause (1).** On a proper scheme of dimension at most one over a field,
`H^i(ω_X^•)` is nonzero only for `i = -1, 0`. -/
@[stacks 0BS2 "clause (1), at the constructed ω_X^• = f^× O_{Spec k}"]
theorem isZero_homology_dualizingComplexOverField_of_ne (hdim : topologicalKrullDim X ≤ 1)
    {i : ℤ} (hi : i ≠ -1) (hi0 : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj
      (dualizingComplexOverField f).obj) := by
  by_contra h
  have := le_zero_and_toNat_neg_le_of_not_isZero f 1 (by exact_mod_cast hdim) i h
  omega

/-- When `dim X ≤ 0`, the sheaf `ω_X = H^{-1}(ω_X^•)` is zero. -/
private theorem isZero_dualizingSheafOverField_of_le_zero (hdim : topologicalKrullDim X ≤ 0) :
    IsZero (dualizingSheafOverField f) := by
  by_contra h
  have := le_zero_and_toNat_neg_le_of_not_isZero f 0 (by exact_mod_cast hdim) (-1) h
  omega

/-- The stalks of a zero module are trivial. -/
private theorem subsingleton_stalk_of_isZero (F : X.Modules) (hF : IsZero F) (x : X) :
    Subsingleton (↑(TopCat.Presheaf.stalk F.val.presheaf x)) :=
  AddCommGrpCat.isZero_iff_subsingleton.mp
    ((Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x).map_isZero hF)

/-- **[Stacks, Tag 0BS2], clause (2), coherence.** `ω_X = H^{-1}(ω_X^•)` is a coherent
`𝒪_X`-module. -/
theorem isCoherent_dualizingSheafOverField_of_isProper :
    _root_.SheafOfModules.IsCoherent (dualizingSheafOverField f) :=
  let := LocallyOfFiniteType.isLocallyNoetherian f
  isCoherent_homology_of_isDualizingComplex (isDualizingComplex_dualizingComplexOverField f) (-1)

/-- On a scheme of dimension at most one, a module with property `(S₂)` is Cohen--Macaulay: the
support of each of its stalks has dimension at most one. -/
private theorem sheafIsCohenMacaulay_of_sheafHasPropertySk_two (hdim : topologicalKrullDim X ≤ 1)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hF : SheafHasPropertySk X F 2) : SheafIsCohenMacaulay X F := by
  intro n x
  have hs : Module.supportDim (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk F.val.presheaf x)) ≤ 2 :=
    (((Module.supportDim_le_ringKrullDim _ _).trans
      (ringKrullDim_stalk_le_topologicalKrullDim' x)).trans hdim).trans (by norm_num)
  refine le_trans ?_ (hF x)
  rcases le_total n 2 with hn | hn
  · exact min_le_min_right _ (by exact_mod_cast hn)
  · exact (min_le_right _ _).trans (le_min hs le_rfl)

/-- **[Stacks, Tag 0BS2], clause (2), the Cohen--Macaulay property.** On a proper scheme of
dimension at most one over a field, `ω_X = H^{-1}(ω_X^•)` is a Cohen--Macaulay `𝒪_X`-module. -/
theorem sheafIsCohenMacaulay_dualizingSheafOverField (hdim : topologicalKrullDim X ≤ 1) :
    SheafIsCohenMacaulay X (dualizingSheafOverField f) := by
  rcases topologicalKrullDim_eq_one_or_le_zero hdim with h | h
  · rw [dualizingSheafOverField_eq_relativeDualizingModule f h]
    exact sheafIsCohenMacaulay_of_sheafHasPropertySk_two hdim _
      (relativeDualizingModule_of_isProper f).2.1
  · intro n x
    have : Subsingleton (↑(TopCat.Presheaf.stalk
        (show SheafOfModules.{u} (structureSheafRing X.toRingedSpace) from
          dualizingSheafOverField f).val.presheaf x)) :=
      subsingleton_stalk_of_isZero _ (isZero_dualizingSheafOverField_of_le_zero f h) x
    rw [Module.depth_eq_top_of_subsingleton]
    exact le_top

/-- **[Stacks, Tag 0BS2], clause (2), the support.** On a proper scheme of dimension at most one
over a field, the support of `ω_X = H^{-1}(ω_X^•)` is the union of the irreducible components of
`X` of dimension `1`. -/
theorem supp_dualizingSheafOverField (hdim : topologicalKrullDim X ≤ 1) :
    _root_.SheafOfModules.supp (dualizingSheafOverField f) =
      ⋃₀ {C ∈ irreducibleComponents X | topologicalKrullDim C = 1} := by
  rcases topologicalKrullDim_eq_one_or_le_zero hdim with h | h
  · rw [dualizingSheafOverField_eq_relativeDualizingModule f h,
      (relativeDualizingModule_of_isProper f).2.2, h]
  · have hz := isZero_dualizingSheafOverField_of_le_zero f h
    have hl : _root_.SheafOfModules.supp (dualizingSheafOverField f) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun x ⟨a, ha⟩ => ?_
      exact ha (@Subsingleton.elim _ (subsingleton_stalk_of_isZero _ hz x) a 0)
    rw [hl, eq_comm, Set.sUnion_eq_empty]
    rintro C ⟨-, hC⟩
    have hle : topologicalKrullDim C ≤ 0 :=
      Topology.IsInducing.subtypeVal.topologicalKrullDim_le.trans h
    rw [hC] at hle
    exact absurd hle (by norm_num)

/-- **[Stacks, Tag 0BS2], clause (2).** On a proper scheme of dimension at most one over a field,
`ω_X = H^{-1}(ω_X^•)` is a coherent Cohen--Macaulay module whose support is the union of the
irreducible components of dimension `1`. -/
@[stacks 0BS2 "clause (2), at the constructed ω_X = H^{-1}(f^× O_{Spec k})"]
theorem dualizingSheafOverField_clauseTwo (hdim : topologicalKrullDim X ≤ 1) :
    _root_.SheafOfModules.IsCoherent (dualizingSheafOverField f) ∧
      SheafIsCohenMacaulay X (dualizingSheafOverField f) ∧
      _root_.SheafOfModules.supp (dualizingSheafOverField f) =
        ⋃₀ {C ∈ irreducibleComponents X | topologicalKrullDim C = 1} :=
  ⟨isCoherent_dualizingSheafOverField_of_isProper f,
    sheafIsCohenMacaulay_dualizingSheafOverField f hdim, supp_dualizingSheafOverField f hdim⟩

/-- **[Stacks, Tag 0BS2], clause (3).** On a proper scheme of dimension at most one over a
field, for `x ∈ X` closed the module `H^0(ω_{X,x}^•)` is nonzero if and only if either
`dim 𝒪_{X,x} = 0`, or `dim 𝒪_{X,x} = 1` and `𝒪_{X,x}` is not Cohen--Macaulay. -/
@[stacks 0BS2 "clause (3), at the constructed ω_X^• = f^× O_{Spec k}"]
theorem nontrivial_stalk_homology_zero_dualizingComplexOverField_iff
    (hdim : topologicalKrullDim X ≤ 1) {x : X} (hx : IsClosed ({x} : Set X)) :
    letI := LocallyOfFiniteType.isLocallyNoetherian f
    Nontrivial (moduleStalkAtPoint ((DerivedCategory.homologyFunctor X.Modules 0).obj
        (dualizingComplexOverField f).obj) x) ↔
      ringKrullDim (X.presheaf.stalk x) = 0 ∨
        ringKrullDim (X.presheaf.stalk x) = 1 ∧
          ¬ IsCohenMacaulayLocalRing (X.presheaf.stalk x) := by
  let := LocallyOfFiniteType.isLocallyNoetherian f
  have h := exists_nontrivial_stalk_homology_iff_depth_le_of_isProper f hx 0
  rw [← _root_.Dualizing.depth_eq_zero_iff_of_ringKrullDim_le_one
    ((ringKrullDim_stalk_le_topologicalKrullDim' x).trans hdim)]
  refine ⟨fun hn => by simpa using (h.1 ⟨0, le_rfl, le_rfl, hn⟩).2, fun hd => ?_⟩
  obtain ⟨j, hj, hj', hn⟩ := h.2 ⟨le_rfl, by simp [hd]⟩
  obtain rfl : j = 0 := by omega
  exact hn

/-- **[Stacks, Tag 0BS2], clause (4), the isomorphisms.** For `K` in `D_QCoh(𝒪_X)` and every `i`,
the duality map `Ext^i_X(K, ω_X^•) ⟶ Hom_k(H^{-i}(X, K), k)`, `α ↦ t ∘ H^{-i}(X, α)` with `t` the
trace, is a bijection. -/
theorem bijective_dualityLinearMap_dualizingComplexOverField
    (K : quasiCoherentDerivedCategory X) (i : ℤ) :
    Function.Bijective (dualityLinearMap f K.obj i) :=
  (dualityEquiv f K i).bijective

end Stacks.Duality

end
