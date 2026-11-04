module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.Extension
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.DominateRationalMap
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChainDominating
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupDescent
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Dominating a rational map from a Noetherian regular surface by quadratic transformations

Let `S` be a scheme, `X` a Noetherian scheme over `S` all of whose local rings are regular of
dimension at most two, and `Y` a scheme proper over `S`. An `S`-rational map from `X` to `Y`,
displayed on a dense open `U ⊆ X`, extends to an open `V ⊇ U` whose complement is a finite set
`T` of closed points with two-dimensional local rings, and a finite sequence of blowups at
closed points lying over `T` carries an `S`-morphism to `Y` agreeing with the rational map.

This is the argument of [Stacks, Tag 0C5H] with every input discharged. The library's form of
that tag, `Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_resolving_partialMap`, takes three
inputs as hypotheses; here they are supplied:

* `descent` is `Stacks.ResolutionOfSurfaces.pointBlowupDescent`;
* `domination` is `Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_factorization`, its own
  `U`-admissible blowup being supplied by
  `Stacks.ResolutionOfSurfaces.exists_isAdmissibleBlowup_dominating_of_isNoetherian`;
* `reduction`, the enlargement of the domain, is
  `Stacks.ResolutionOfSurfaces.exists_cofinite_extension_of_isNoetherian` below: the source's
  appeal to [Stacks, Tag 0BX7] at the points of codimension at most one, made at every such
  point at once by taking a maximal open of definition, which exists because `X` is Noetherian.

## Main results

* `Stacks.ResolutionOfSurfaces.exists_cofinite_extension_of_isNoetherian` — a rational map from a
  Noetherian scheme with regular local rings of dimension at most two to a proper scheme is
  defined away from a finite set of closed points with two-dimensional local rings.
* `Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_resolving_partialMap_of_isNoetherian` —
  the rational map is resolved by a sequence of blowups at those points.

## Implementation notes

The Noetherian hypothesis is needed and is not a convenience: a sequence of blowups is finite, and
a disjoint union of infinitely many copies of the affine plane over a field, with the rational map
to the projective line given by `(x : y)` on every copy, is a regular scheme of dimension two whose
rational map is not resolved by any finite sequence of blowups at closed points. No `@[stacks]`
attribute is attached, for that reason: the source states Tag 0C5H without quasi-compactness.

## References

* [Stacks Project, Tag 0C5H](https://stacks.math.columbia.edu/tag/0C5H)
* [Stacks Project, Tag 0BX7](https://stacks.math.columbia.edu/tag/0BX7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

/-- **A regular local ring of dimension at most one is a valuation ring.** Its cotangent space
has dimension at most one, so its maximal ideal is principal. -/
theorem valuationRing_of_isRegularLocalRing_of_ringKrullDim_le_one (A : Type u) [CommRing A]
    [IsRegularLocalRing A] [IsDomain A] (h : ringKrullDim A ≤ 1) : ValuationRing A := by
  refine ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain A).out 2 6).mpr ?_
  have h2 := (IsRegularLocalRing.iff_finrank_cotangentSpace A).mp inferInstance
  rw [← h2] at h
  exact_mod_cast h

/-- **Specialization raises the dimension of the local ring.** If `x` specializes to `y ≠ x` and
the local ring at `y` has finite dimension, then `dim 𝒪_{X,x} + 1 ≤ dim 𝒪_{X,y}`. -/
theorem ringKrullDim_stalk_add_one_le_of_specializes {X : Scheme.{u}} {x y : X} (h : x ⤳ y)
    (hne : x ≠ y) :
    ringKrullDim (X.presheaf.stalk x) + 1 ≤ ringKrullDim (X.presheaf.stalk y) := by
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight]
  have hlt : y < x := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr h)
    fun h' => hne (h.antisymm (Scheme.le_iff_specializes.mp h')).eq
  exact_mod_cast Order.coheight_add_one_le hlt

/-- **A rational map into a proper scheme extends over every point whose local ring is a
valuation ring.** On a Noetherian scheme a morphism from a dense open to a scheme proper over the
base extends, compatibly with the base, to an open containing every point whose local ring is a
valuation ring: take a maximal open of definition, which exists because the opens of a Noetherian
space satisfy the ascending chain condition, and apply [Stacks, Tag 0BX7] at any such point
outside it. -/
@[ega "II 7.3.3" "partial, special case"]
theorem exists_extension_of_valuationRing_stalks {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    [IsNoetherian X] [IsProper pY] (U : X.Opens) (hU : Dense (U : Set X))
    (f : (U : Scheme.{u}) ⟶ Y) (hf : f ≫ pY = U.ι ≫ pX) :
    ∃ (V : X.Opens) (hUV : U ≤ V) (g : (V : Scheme.{u}) ⟶ Y),
      g ≫ pY = V.ι ≫ pX ∧ X.homOfLE hUV ≫ g = f ∧
      ∀ (x : X) [IsDomain (X.presheaf.stalk x)], ValuationRing (X.presheaf.stalk x) → x ∈ V := by
  classical
  let P : Set X.Opens := {V | ∃ (hUV : U ≤ V) (g : (V : Scheme.{u}) ⟶ Y),
    g ≫ pY = V.ι ≫ pX ∧ X.homOfLE hUV ≫ g = f}
  have hP : U ∈ P := ⟨le_rfl, f, hf, by simp⟩
  have hwf : WellFounded ((· > ·) : X.Opens → X.Opens → Prop) := wellFounded_gt
  obtain ⟨V, ⟨hUV, g, hg, hgf⟩, hmax⟩ := hwf.has_min P ⟨U, hP⟩
  refine ⟨V, hUV, g, hg, hgf, fun x _ h2 => ?_⟩
  have := h2
  by_contra hx
  have hxV : x ∈ closure (V : Set X) := by
    rw [(hU.mono hUV).closure_eq]
    trivial
  obtain ⟨V', hVV', hxV', g', hg', hgg'⟩ :=
    exists_open_extension_of_valuationRing_stalk pX pY x V g hg hxV (Or.inr inferInstance)
  refine hmax V' ⟨hUV.trans hVV', g', hg', ?_⟩ (lt_of_le_of_ne hVV' ?_)
  · rw [← hgf, ← hgg', ← Category.assoc, Scheme.homOfLE_homOfLE]
  · rintro rfl
    exact hx hxV'

/-- **A closed subset of a Noetherian space all of whose points are closed is finite.** It is a
finite union of irreducible closed subsets, and each of these is the closure of its generic
point, a closed point. -/
theorem Set.Finite.of_isClosed_of_forall_isClosed_singleton {X : Scheme.{u}} [IsNoetherian X]
    {T : Set X} (hT : IsClosed T) (hpt : ∀ x ∈ T, IsClosed ({x} : Set X)) : T.Finite := by
  obtain ⟨S, hSf, hSc, hSi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hT
  refine Set.Finite.sUnion hSf fun t ht => ?_
  have hgen := (hSi t ht).isGenericPoint_genericPoint_closure
  rw [(hSc t ht).closure_eq] at hgen
  have hmem : (hSi t ht).genericPoint ∈ ⋃₀ S := ⟨t, ht, hgen.mem⟩
  have heq : t = {(hSi t ht).genericPoint} := by
    have h1 : closure ({(hSi t ht).genericPoint} : Set X) = t := hgen
    rw [(hpt _ hmem).closure_eq] at h1
    exact h1.symm
  exact heq ▸ Set.finite_singleton _

/-- A value of `WithBot ℕ∞` below two is at most one. -/
alias withBot_enat_le_one_of_lt_two :=
  Stacks.AlgebraicGeometry.ReflexiveModules.withBot_lt_two_le_one

/-- **A rational map from a Noetherian scheme with regular local rings of dimension at most two
into a proper scheme is defined away from finitely many closed points with two-dimensional local
rings.** This is the reduction step of the proof of [Stacks, Tag 0C5H]: by [Stacks, Tag 0BX7] the
map extends over every point of codimension at most one, whose local ring is a field or a discrete
valuation ring; the remaining points have two-dimensional local rings, hence are closed, and they
form a closed set, hence a finite one. -/
@[ega "I 3.7.3" "partial", ega "II 7.3.5" "special case", ega "II 7.3.6" "special case"]
theorem exists_cofinite_extension_of_isNoetherian {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    [IsNoetherian X] [IsProper pY]
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 2)
    (U : X.Opens) (hU : Dense (U : Set X)) (f : (U : Scheme.{u}) ⟶ Y)
    (hf : f ≫ pY = U.ι ≫ pX) :
    ∃ (T : Finset X) (V : X.Opens) (hUV : U ≤ V) (g : (V : Scheme.{u}) ⟶ Y),
      (V : Set X) = (T : Set X)ᶜ ∧ (∀ x ∈ T, IsClosed ({x} : Set X)) ∧
      (∀ x ∈ T, ringKrullDim (X.presheaf.stalk x) = 2) ∧
      g ≫ pY = V.ι ≫ pX ∧ X.homOfLE hUV ≫ g = f := by
  classical
  obtain ⟨V, hUV, g, hg, hgf, hval⟩ := exists_extension_of_valuationRing_stalks pX pY U hU f hf
  -- the points outside `V` have two-dimensional local rings
  have htwo : ∀ x : X, x ∉ V → ringKrullDim (X.presheaf.stalk x) = 2 := by
    intro x hx
    refine le_antisymm (hdim x) ?_
    by_contra hlt
    have hle : ringKrullDim (X.presheaf.stalk x) ≤ 1 :=
      withBot_enat_le_one_of_lt_two (not_le.mp hlt)
    have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
    exact hx (hval x (valuationRing_of_isRegularLocalRing_of_ringKrullDim_le_one _ hle))
  -- such points are closed
  have hclosed : ∀ x : X, x ∉ V → IsClosed ({x} : Set X) := by
    intro x hx
    refine closure_subset_iff_isClosed.mp fun y hy => ?_
    by_contra hne
    have hspec : x ⤳ y := specializes_iff_mem_closure.mpr hy
    have h1 := ringKrullDim_stalk_add_one_le_of_specializes hspec (Ne.symm hne)
    rw [htwo x hx] at h1
    have h2 := hdim y
    have h3 : (((2 : ℕ) : ℕ∞) : WithBot ℕ∞) + 1 ≤ (((2 : ℕ) : ℕ∞) : WithBot ℕ∞) := h1.trans h2
    norm_cast at h3
  have hfin : ((V : Set X)ᶜ).Finite :=
    Set.Finite.of_isClosed_of_forall_isClosed_singleton V.isOpen.isClosed_compl
      fun x hx => hclosed x hx
  refine ⟨hfin.toFinset, V, hUV, g, by simp, fun x hx => hclosed x (by simpa using hx),
    fun x hx => htwo x (by simpa using hx), hg, hgf⟩

/-- **[Stacks, Tag 0C5H] for a Noetherian scheme, unconditionally.** Let `S` be a scheme, `X` a
Noetherian scheme over `S` whose local rings are regular of dimension at most two, and `Y` a
scheme proper over `S`. Given an `S`-rational map from `X` to `Y` displayed on `f.domain`, there is
a finite set `T` of closed points of `X` outside `f.domain` with two-dimensional local rings, a
sequence of blowups at closed points lying over `T`, with composite `p : Z ⟶ X`, and an
`S`-morphism `h : Z ⟶ Y` agreeing with the rational map over `f.domain`. -/
theorem exists_pointBlowupChain_resolving_partialMap_of_isNoetherian
    {S X Y : Scheme.{u}} [X.Over S] [Y.Over S] [IsNoetherian X] [IsProper (Y ↘ S)]
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 2)
    (f : X.PartialMap Y) [f.IsOver S] :
    ∃ (T : Finset X) (Z : Scheme.{u}) (p : Z ⟶ X) (h : Z ⟶ Y),
      (∀ x ∈ T, IsClosed ({x} : Set X)) ∧ (∀ x ∈ T, ringKrullDim (X.presheaf.stalk x) = 2) ∧
      (∀ x ∈ T, x ∉ f.domain) ∧ PointBlowupChain X (T : Set X) Z p ∧
      h ≫ (Y ↘ S) = p ≫ (X ↘ S) ∧
      pullback.fst p f.domain.ι ≫ h = pullback.snd p f.domain.ι ≫ f.hom := by
  have hf : f.hom ≫ (Y ↘ S) = f.domain.ι ≫ (X ↘ S) := Scheme.PartialMap.isOver_iff.mp inferInstance
  obtain ⟨T, V, hUV, g, hVT, hTclosed, hTdim, hg, hgf⟩ :=
    exists_cofinite_extension_of_isNoetherian (X ↘ S) (Y ↘ S) hreg hdim f.domain f.dense_domain
      f.hom hf
  let f' : X.PartialMap Y := ⟨V, f.dense_domain.mono hUV, g⟩
  have : f'.IsOver S := Scheme.PartialMap.isOver_iff.mpr hg
  obtain ⟨Z, p, h, hchain, hS, hagree⟩ :=
    exists_pointBlowupChain_resolving_partialMap pointBlowupDescent
      (fun d _ _ _ T V hV hc hr hd q _ _ hdom =>
        exists_pointBlowupChain_factorization d T V hV hc hr hd q hdom)
      hreg f'
      ⟨T, V, le_rfl, g, hVT, hTclosed, hTdim, hg, by simp [f'],
        fun q _ _ => exists_isAdmissibleBlowup_dominating_of_isNoetherian q V⟩
  have hTV : ((f'.domain : Set X))ᶜ = (T : Set X) := by
    show ((V : Set X))ᶜ = _
    rw [hVT, compl_compl]
  refine ⟨T, Z, p, h, hTclosed, hTdim, fun x hx hxU => ?_, hTV ▸ hchain, hS, ?_⟩
  · have : x ∈ (V : Set X) := hUV hxU
    rw [hVT] at this
    exact this hx
  · -- compare through `Z ×_X V`
    have hcond : pullback.fst p f.domain.ι ≫ p =
        (pullback.snd p f.domain.ι ≫ X.homOfLE hUV) ≫ V.ι := by
      rw [pullback.condition, Category.assoc, Scheme.homOfLE_ι]
    let m : pullback p f.domain.ι ⟶ pullback p V.ι :=
      pullback.lift (pullback.fst p f.domain.ι) (pullback.snd p f.domain.ι ≫ X.homOfLE hUV) hcond
    have hagree' : pullback.fst p V.ι ≫ h = pullback.snd p V.ι ≫ g := hagree
    calc pullback.fst p f.domain.ι ≫ h
        = m ≫ pullback.fst p V.ι ≫ h := by rw [← Category.assoc, pullback.lift_fst]
      _ = m ≫ pullback.snd p V.ι ≫ g := by rw [hagree']
      _ = pullback.snd p f.domain.ι ≫ f.hom := by
            rw [← Category.assoc, pullback.lift_snd, Category.assoc, hgf]

end Stacks.ResolutionOfSurfaces

end
