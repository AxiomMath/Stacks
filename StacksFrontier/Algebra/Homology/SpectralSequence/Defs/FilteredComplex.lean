module

public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Defs
public import StacksFrontier.Algebra.Homology.SpectralSequence.Defs.DoubleComplex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Convergence of the spectral sequence of a filtered complex

Let `𝒜` be an abelian category and let `(K^•, F)` be a filtered complex of `𝒜`. Writing
`n = p + q`, the spectral sequence of `(K^•, F)` ([Stacks, Tag 012M]) has cycles and boundaries
```
Z_r^{p, q} = (F^p K^n ∩ (d^n)⁻¹(F^{p + r} K^{n + 1}) + F^{p + 1} K^n)/F^{p + 1} K^n,
B_r^{p, q} = (F^p K^n ∩ d^{n - 1}(F^{p - r + 1} K^{n - 1}) + F^{p + 1} K^n)/F^{p + 1} K^n,
```
and, when `Z_∞^{p, q} = ⋂_r Z_r^{p, q}` and `B_∞^{p, q} = ⋃_r B_r^{p, q}` exist, a limit
`E_∞^{p, q} = Z_∞^{p, q}/B_∞^{p, q}`. By [Stacks, Tag 012Q] the graded piece
`gr^p H^n(K^•)` of the induced filtration `F^p H^n(K^•) = Im(H^n(F^p K^•) → H^n(K^•))` is a
subquotient of `E_∞^{p, n - p}`: the object `Ker(d^n) ∩ F^p K^n` maps to both, and the image
of it in `E_∞^{p, n - p}` maps onto `gr^p H^n(K^•)`.

Following [Stacks, Tag 012U], the spectral sequence

1. *weakly converges* to `H^*(K^•)` if `gr^p H^n(K^•) = E_∞^{p, n - p}` via this comparison,
   for all `p, n`;
2. *abuts* to `H^*(K^•)` if moreover the induced filtration on each `H^n(K^•)` is separated,
   `⋂_p F^p H^n(K^•) = 0`, and exhaustive, `⋃_p F^p H^n(K^•) = H^n(K^•)`;
3. *converges* to `H^*(K^•)` if it is regular, abuts to `H^*(K^•)`, and
   `H^n(K^•) = lim_p H^n(K^•)/F^p H^n(K^•)` for all `n`.

By [Stacks, Tag 012V], weak convergence is the equality of the two inclusions
```
Ker(d^n) ∩ F^p K^n + F^{p + 1} K^n ⊆ Z_∞^{p, q},
B_∞^{p, q} ⊆ Im(d^{n - 1}) ∩ F^p K^n + F^{p + 1} K^n
```
for all `p, n` (both sides existing), and the two further conditions of abutment are
conditions on the subobjects `Ker(d^n) ∩ F^p K^n + Im(d^{n - 1})` of `K^n`; these are recorded
as characterisations of the predicates.

## Main definitions

* `CochainComplex.Filtered.WeaklyConverges`, `CochainComplex.Filtered.Abuts`,
  `CochainComplex.Filtered.Converges`: the three notions of [Stacks, Tag 012U]. They are phrased
  with the completeness `CategoryTheory.Filtration.IsComplete` of a filtration and the regularity
  `CochainComplex.Filtered.HasRegularSpectralSequence` of the spectral sequence of a filtered
  complex.
* `HomologicalComplex₂.WeaklyConvergesToTotalHomology₁`, `...₂`,
  `HomologicalComplex₂.AbutsToTotalHomology₁`, `...₂`,
  `HomologicalComplex₂.ConvergesToTotalHomology₁`, `...₂`: the same three notions for the
  spectral sequences `('E_r, 'd_r)` and `(''E_r, ''d_r)` of a double complex, that is, for
  `Tot(K^{•,•})` filtered by the first or by the second coordinate ([Stacks, Tag 0131]).

## Main results

* `CategoryTheory.Filtration.IsComplete.isSeparated`: a complete filtration is separated.
* `CochainComplex.Filtered.HasRegularSpectralSequence.isGLB_pageCycles`: for a regular spectral
  sequence the stable cycles `Z_∞^{p, q}` exist.
* `CochainComplex.Filtered.weaklyConverges_iff`: weak convergence is equality in the two
  inclusions displayed above; equivalently `WeaklyConverges ↔ WeaklyConvergesToHomology`.
* `CochainComplex.Filtered.abuts_iff`: abutment in terms of subobjects of the terms `K^n`;
  equivalently `Abuts ↔ AbutsToHomology`.
* `CochainComplex.Filtered.converges_iff_convergesToHomology`: `Converges ↔ ConvergesToHomology`.

## Implementation notes

*Filtered complexes and their pages.* A filtered complex is `CochainComplex.Filtered 𝒜`, a
cochain complex filtered by subcomplexes, and its degreewise steps are the subobjects
`F^p K^n` of `K^n`. The source's `Z_r^{p, q}` and `B_r^{p, q}` are subobjects of
`gr^p K^n = K^n/F^{p + 1}K^n`; they are presented by their numerators in `K^n`, the subobjects
containing `F^{p + 1}K^n` displayed above, indexed by `r : ℕ` (cofinal among the source's
indices). As in [Stacks, Tag 012Q], `Z_∞^{p, q}` and `B_∞^{p, q}` exist when the corresponding
greatest lower bound and least upper bound exist; no completeness of the subobject lattices of
`𝒜` is assumed. Weak convergence includes the existence of `E_∞^{p, q}`, without which the
equality `gr^p H^n(K^•) = E_∞^{p, n - p}` has no meaning.

*The comparison.* There is in general no morphism between `gr^p H^n(K^•)` and
`E_∞^{p, n - p}`; both receive canonical maps from `Ker(d^n) ∩ F^p K^n`, and
"`gr^p H^n(K^•) = E_∞^{p, n - p}` via [Stacks, Tag 012Q]" is the existence of an isomorphism
`E_∞^{p, n - p} ≅ gr^p H^n(K^•)` compatible with these two maps. Here `gr^p H^n(K^•)` is the
cokernel of `F^{p + 1} H^n(K^•) → F^p H^n(K^•)`, the images of `H^n(F^{p + 1}K^•)` and
`H^n(F^p K^•)` in `H^n(K^•)`.

*Regularity.* Regularity of a spectral sequence ([Stacks, Tag 0BDU]) asks that
`d_r^{p, q} = 0` for `r ≫ 0`. Since `Z_{r + 1}^{p, q}/B_r^{p, q} = Ker(d_r^{p, q})`, this is the
same as `Z_{r + 1}^{p, q} = Z_r^{p, q}` for `r ≫ 0` ([Stacks, Tag 0BDV]), and that is how it is
stated here: as eventual stationarity of the numerators of the cycles, a condition on the
filtered complex itself, the spectral sequence of [Stacks, Tag 012M] being given by an existence
statement rather than by a chosen object.

*Completeness.* `H^n(K^•) = lim_p H^n(K^•)/F^p H^n(K^•)` is the statement that the cone with
vertex `H^n(K^•)` and the projections onto the quotients is a limit cone; the limit is not assumed
to exist beforehand.

## References

* [Stacks Project, Tag 012U](https://stacks.math.columbia.edu/tag/012U)
* [Stacks Project, Tag 0131](https://stacks.math.columbia.edu/tag/0131)
* [Stacks Project, Tag 012Q](https://stacks.math.columbia.edu/tag/012Q)
* [Stacks Project, Tag 012V](https://stacks.math.columbia.edu/tag/012V)
* [Stacks Project, Tag 012M](https://stacks.math.columbia.edu/tag/012M)
* [Stacks Project, Tag 0BDU](https://stacks.math.columbia.edu/tag/0BDU)
* [Stacks Project, Tag 0BDV](https://stacks.math.columbia.edu/tag/0BDV)
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Filtration

variable {C : Type*} [Category* C] {I : Type*} [Category* I] {X : C}

section Quotients

variable [HasZeroMorphisms C] [HasCokernels C]

/-- A complete filtration is separated: a subobject contained in every `F^iX` dies in every
quotient `X/F^iX`, hence is zero. -/
theorem IsComplete.isSeparated [HasZeroObject C] {F : Filtration X I} (hF : F.IsComplete) :
    F.IsSeparated := by
  obtain ⟨hl⟩ := hF
  refine ⟨fun _ _ => bot_le, fun S hS => ?_⟩
  have h0 : S.arrow = 0 := by
    refine hl.hom_ext fun i => ?_
    have hf : (F.subobject i).Factors S.arrow :=
      Subobject.factors_of_le _ (hS ⟨i, rfl⟩) (by simpa using Subobject.factors_comp_arrow (𝟙 _))
    obtain ⟨t, ht⟩ := (Subobject.mk_factors_iff _ _).mp hf
    have hc : F.ι.app i ≫ F.quotientCone.π.app i = 0 := cokernel.condition _
    rw [← ht]
    exact (Category.assoc _ _ _).trans
      ((congrArg (t ≫ ·) hc).trans (comp_zero.trans zero_comp.symm))
  rw [← Subobject.mk_arrow S]
  exact (Subobject.mk_eq_bot_iff_zero.mpr h0).le

end Quotients

end CategoryTheory.Filtration

namespace CochainComplex.Filtered

variable {C : Type u} [Category.{v} C] [Abelian C] (K : Filtered C)

section Pages

/-- The steps `F^p K^n` of the filtration of `K^n` decrease as `p` increases. -/
lemma step_antitone (n : ℤ) : Antitone fun p : ℤ => K.step p n :=
  fun p p' hp => Subobject.mk_le_mk_of_comm ((K.filtration.diagram.map (homOfLE hp).op).f n)
    (by rw [← HomologicalComplex.comp_f, K.filtration.diagram_map_comp_ι_app])

/-- The numerator `F^p K^n ∩ (d^n)⁻¹(F^{p + r} K^{n + 1}) + F^{p + 1} K^n` in `K^n` of the cycles
`Z_r^{p, n - p}` of the spectral sequence of `K`. -/
noncomputable abbrev pageCycles (p n : ℤ) (r : ℕ) : Subobject (K.X.X n) :=
  K.step p n ⊓
      (Subobject.pullback (K.X.d n (n + 1))).obj (K.step (p + r) (n + 1)) ⊔
    K.step (p + 1) n

/-- The numerator `F^p K^n ∩ d^{n - 1}(F^{p - r} K^{n - 1}) + F^{p + 1} K^n` in `K^n` of the
boundaries `B_{r + 1}^{p, n - p}` of the spectral sequence of `K`. -/
noncomputable abbrev pageBoundaries (p n : ℤ) (r : ℕ) : Subobject (K.X.X n) :=
  K.step p n ⊓
      (Subobject.«exists» (K.X.d (n - 1) n)).obj (K.step (p - r) (n - 1)) ⊔
    K.step (p + 1) n

/-- The numerators of the cycles `Z_r^{p, n - p}` decrease as `r` increases. -/
lemma pageCycles_antitone (p n : ℤ) : Antitone (K.pageCycles p n) := fun r s hrs =>
  sup_le_sup_right (inf_le_inf_left _ ((Subobject.pullback _).monotone
    (K.step_antitone (n + 1) (by omega)))) _

/-- The numerators of the boundaries `B_{r + 1}^{p, n - p}` increase as `r` increases. -/
lemma pageBoundaries_monotone (p n : ℤ) : Monotone (K.pageBoundaries p n) := fun r s hrs =>
  sup_le_sup_right (inf_le_inf_left _ ((Subobject.exists _).monotone
    (K.step_antitone (n - 1) (by omega)))) _

/-- The cycles of `K^•` lying in `F^p K^n`, that is `Ker(d^n) ∩ F^p K^n`, as a subobject of the
cycles `Z^n(K^•)`. -/
noncomputable abbrev cyclesInStep (p n : ℤ) : Subobject (K.X.cycles n) :=
  (Subobject.pullback (K.X.iCycles n)).obj (K.step p n)

/-- The graded piece `gr^p H^n(K^•) = F^p H^n(K^•)/F^{p + 1} H^n(K^•)` of the induced filtration,
as the cokernel of the inclusion of the image of `H^n(F^{p + 1} K^•)` into that of
`H^n(F^p K^•)`. -/
noncomputable abbrev gradedHomology (p n : ℤ) : C :=
  cokernel (image.preComp
    (HomologicalComplex.homologyMap (K.filtration.diagram.map
      (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
    (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))

end Pages

/-- For a regular spectral sequence the stable cycles `Z_∞^{p, q}` exist: they are the eventual
value of `Z_r^{p, q}`. -/
theorem HasRegularSpectralSequence.isGLB_pageCycles {K : Filtered C}
    (hK : K.HasRegularSpectralSequence) (p n : ℤ) :
    ∃ Z, IsGLB (Set.range (K.pageCycles p n)) Z := by
  obtain ⟨b, hb⟩ := hK p n
  refine ⟨K.pageCycles p n b, IsLeast.isGLB ⟨⟨b, rfl⟩, ?_⟩⟩
  rintro _ ⟨r, rfl⟩
  rcases le_total r b with h | h
  · exact K.pageCycles_antitone p n h
  · exact (hb r h).ge

/-- **Stacks 012U (1).** The spectral sequence of a filtered complex `K` *weakly converges* to
`H^*(K^•)` if for all `p, n` the stable cycles `Z_∞^{p, n - p}` and boundaries
`B_∞^{p, n - p}` exist and `gr^p H^n(K^•) = E_∞^{p, n - p}` via [Stacks, Tag 012Q]: there is an
isomorphism `E_∞^{p, n - p} = Z_∞^{p, n - p}/B_∞^{p, n - p} ≅ gr^p H^n(K^•)` compatible with the
canonical maps to both from `Ker(d^n) ∩ F^p K^n`. -/
@[stacks 012U "(1)", ega "0 11.1.3" "special case"]
def WeaklyConverges : Prop :=
  ∀ p n : ℤ, ∃ Z B : Subobject (K.X.X n),
    IsGLB (Set.range (K.pageCycles p n)) Z ∧ IsLUB (Set.range (K.pageBoundaries p n)) B ∧
    ∃ (a : (K.cyclesInStep p n : C) ⟶ (Z : C))
      (b : (K.cyclesInStep p n : C) ⟶
        image (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))
      (e : cokernel (Subobject.ofLE (B ⊓ Z) Z inf_le_right) ≅ K.gradedHomology p n),
      a ≫ Z.arrow = (K.cyclesInStep p n).arrow ≫ K.X.iCycles n ∧
      b ≫ image.ι (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) =
        (K.cyclesInStep p n).arrow ≫ K.X.homologyπ n ∧
      a ≫ cokernel.π (Subobject.ofLE (B ⊓ Z) Z inf_le_right) ≫ e.hom =
        b ≫ cokernel.π (image.preComp
          (HomologicalComplex.homologyMap (K.filtration.diagram.map
            (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
          (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))

/-- **Stacks 012U (2).** The spectral sequence of a filtered complex `K` *abuts* to `H^*(K^•)` if
it weakly converges to `H^*(K^•)` and for all `n` the induced filtration on `H^n(K^•)` is
separated, `⋂_p F^p H^n(K^•) = 0`, and exhaustive, `⋃_p F^p H^n(K^•) = H^n(K^•)`. -/
@[stacks 012U "(2)"]
def Abuts : Prop :=
  K.WeaklyConverges ∧
    ∀ n : ℤ, (K.inducedFiltration n).IsSeparated ∧ (K.inducedFiltration n).IsExhaustive

/-- **Stacks 012U (3).** The spectral sequence of a filtered complex `K` *converges* to
`H^*(K^•)` if it is regular, abuts to `H^*(K^•)`, and
`H^n(K^•) = lim_p H^n(K^•)/F^p H^n(K^•)` for all `n`. -/
@[stacks 012U "(3)"]
def Converges : Prop :=
  K.HasRegularSpectralSequence ∧ K.Abuts ∧ ∀ n : ℤ, (K.inducedFiltration n).IsComplete

variable {K}

/-- If the spectral sequence of `K` abuts to `H^*(K^•)`, it weakly converges to `H^*(K^•)`. -/
theorem Abuts.weaklyConverges (h : K.Abuts) : K.WeaklyConverges := h.1

/-- If the spectral sequence of `K` converges to `H^*(K^•)`, it is regular. -/
theorem Converges.hasRegularSpectralSequence (h : K.Converges) : K.HasRegularSpectralSequence :=
  h.1

/-- If the spectral sequence of `K` converges to `H^*(K^•)`, it abuts to `H^*(K^•)`. -/
theorem Converges.abuts (h : K.Converges) : K.Abuts := h.2.1

/-- If the spectral sequence of `K` converges to `H^*(K^•)`, it weakly converges to
`H^*(K^•)`. -/
theorem Converges.weaklyConverges (h : K.Converges) : K.WeaklyConverges := h.2.1.1

variable (K)

/-- **Weak convergence through (012S) and (012T)** ([Stacks, Tag 012V]). The spectral sequence of
`K` weakly converges to `H^*(K^•)` if and only if, for all `p, n`, the stable cycles and
boundaries exist and are `Ker(d^n) ∩ F^p K^n + F^{p + 1} K^n` and
`Im(d^{n - 1}) ∩ F^p K^n + F^{p + 1} K^n`. -/
theorem weaklyConverges_iff : K.WeaklyConverges ↔ ∀ p n : ℤ,
    IsGLB (Set.range (K.pageCycles p n))
        (kernelSubobject (K.X.d n (n + 1)) ⊓ K.step p n ⊔ K.step (p + 1) n) ∧
      IsLUB (Set.range (K.pageBoundaries p n))
        (imageSubobject (K.X.d (n - 1) n) ⊓ K.step p n ⊔ K.step (p + 1) n) := by
  have key := fun p n => (exists_iso_stablePage_iff_and_isGLB_isLUB_inducedFiltration_iff K p n
    (fun p m => K.step p m) (fun _ _ => rfl) _ rfl _ _ rfl rfl
    (fun p' => K.inducedFiltrationStep n p') (fun _ => rfl)).1
  constructor
  · intro h p n
    obtain ⟨Z, B, hZ, hB, a, b, e, ha, hb, he⟩ := h p n
    obtain ⟨rfl, rfl⟩ := (key p n Z B hZ hB a ha b hb).mp ⟨e, he⟩
    exact ⟨hZ, hB⟩
  · intro h p n
    obtain ⟨hZ, hB⟩ := h p n
    obtain ⟨-, a, b, -, -, -, ha, hb, -, -, -, -⟩ :=
      exists_epi_gradedPiece_homology_of_isGLB_isLUB K p n (fun p m => K.step p m)
        (fun _ _ => rfl) _ rfl _ _ hZ hB
    obtain ⟨e, he⟩ := (key p n _ _ hZ hB a ha.symm b hb.symm).mpr ⟨rfl, rfl⟩
    exact ⟨_, _, hZ, hB, a, b, e, ha.symm, hb.symm, he⟩

/-- The steps of the induced filtration of `H^n(K^•)` are the images
`Im(H^n(F^p K^•) → H^n(K^•))`, `p ∈ ℤ`. -/
lemma range_inducedFiltration_subobject (n : ℤ) :
    Set.range (K.inducedFiltration n).subobject = Set.range (K.inducedFiltrationStep n) := by
  ext S
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.unop, (K.inducedFiltration_subobject n i.unop).symm⟩
  · rintro ⟨p, rfl⟩
    exact ⟨op p, K.inducedFiltration_subobject n p⟩

/-- **Abutment in terms of the terms of `K`** ([Stacks, Tag 012V]). The spectral sequence of `K`
abuts to `H^*(K^•)` if and only if it satisfies the condition of `weaklyConverges_iff` and, for
all `n`, `⋂_p (Ker(d^n) ∩ F^p K^n + Im(d^{n - 1})) = Im(d^{n - 1})` and
`⋃_p (Ker(d^n) ∩ F^p K^n + Im(d^{n - 1})) = Ker(d^n)`. -/
theorem abuts_iff : K.Abuts ↔
    (∀ p n : ℤ,
      IsGLB (Set.range (K.pageCycles p n))
          (kernelSubobject (K.X.d n (n + 1)) ⊓ K.step p n ⊔ K.step (p + 1) n) ∧
        IsLUB (Set.range (K.pageBoundaries p n))
          (imageSubobject (K.X.d (n - 1) n) ⊓ K.step p n ⊔
            K.step (p + 1) n)) ∧
    ∀ n : ℤ,
      IsGLB (Set.range fun p : ℤ => kernelSubobject (K.X.d n (n + 1)) ⊓ K.step p n ⊔
          imageSubobject (K.X.d (n - 1) n)) (imageSubobject (K.X.d (n - 1) n)) ∧
        IsLUB (Set.range fun p : ℤ => kernelSubobject (K.X.d n (n + 1)) ⊓ K.step p n ⊔
          imageSubobject (K.X.d (n - 1) n)) (kernelSubobject (K.X.d n (n + 1))) := by
  have key := fun n => (exists_iso_stablePage_iff_and_isGLB_isLUB_inducedFiltration_iff K 0 n
    (fun p m => K.step p m) (fun _ _ => rfl) _ rfl _ _ rfl rfl
    (fun p' => K.inducedFiltrationStep n p') (fun _ => rfl)).2
  rw [Abuts, weaklyConverges_iff]
  refine and_congr Iff.rfl (forall_congr' fun n => ?_)
  rw [Filtration.IsSeparated, Filtration.IsExhaustive, range_inducedFiltration_subobject]
  exact and_congr (key n).1 (key n).2

/-- `WeaklyConverges` agrees with `WeaklyConvergesToHomology`. -/
theorem weaklyConverges_iff_weaklyConvergesToHomology :
    K.WeaklyConverges ↔ K.WeaklyConvergesToHomology :=
  K.weaklyConverges_iff

/-- `Abuts` agrees with `AbutsToHomology`. -/
theorem abuts_iff_abutsToHomology : K.Abuts ↔ K.AbutsToHomology := by
  rw [Abuts, AbutsToHomology, weaklyConverges_iff_weaklyConvergesToHomology]

/-- `Converges` agrees with `ConvergesToHomology`. -/
theorem converges_iff_convergesToHomology : K.Converges ↔ K.ConvergesToHomology := by
  rw [Converges, ConvergesToHomology, abuts_iff_abutsToHomology]

end CochainComplex.Filtered

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [K.HasTotal (ComplexShape.up ℤ)]

/-- **Stacks 0131, the first spectral sequence, weak convergence.** The spectral sequence
`('E_r, 'd_r)` of `Tot(K^{•,•})` filtered by the first coordinate weakly converges to
`H^n(Tot(K^{•,•}))`. -/
@[stacks 0131 "`('E_r, 'd_r)` weakly converges"]
abbrev WeaklyConvergesToTotalHomology₁ : Prop :=
  CochainComplex.Filtered.WeaklyConverges K.totalFiltration₁

/-- **Stacks 0131, the first spectral sequence, abutment.** The spectral sequence
`('E_r, 'd_r)` of `Tot(K^{•,•})` filtered by the first coordinate abuts to
`H^n(Tot(K^{•,•}))`. -/
@[stacks 0131 "`('E_r, 'd_r)` abuts"]
abbrev AbutsToTotalHomology₁ : Prop :=
  CochainComplex.Filtered.Abuts K.totalFiltration₁

/-- **Stacks 0131, the first spectral sequence, convergence.** The spectral sequence
`('E_r, 'd_r)` of `Tot(K^{•,•})` filtered by the first coordinate converges to
`H^n(Tot(K^{•,•}))`. -/
@[stacks 0131 "`('E_r, 'd_r)` converges"]
abbrev ConvergesToTotalHomology₁ : Prop :=
  CochainComplex.Filtered.Converges K.totalFiltration₁

/-- **Stacks 0131, the second spectral sequence, weak convergence.** The spectral sequence
`(''E_r, ''d_r)` of `Tot(K^{•,•})` filtered by the second coordinate weakly converges to
`H^n(Tot(K^{•,•}))`. -/
@[stacks 0131 "`(''E_r, ''d_r)` weakly converges"]
abbrev WeaklyConvergesToTotalHomology₂ : Prop :=
  CochainComplex.Filtered.WeaklyConverges K.totalFiltration₂

/-- **Stacks 0131, the second spectral sequence, abutment.** The spectral sequence
`(''E_r, ''d_r)` of `Tot(K^{•,•})` filtered by the second coordinate abuts to
`H^n(Tot(K^{•,•}))`. -/
@[stacks 0131 "`(''E_r, ''d_r)` abuts"]
abbrev AbutsToTotalHomology₂ : Prop :=
  CochainComplex.Filtered.Abuts K.totalFiltration₂

/-- **Stacks 0131, the second spectral sequence, convergence.** The spectral sequence
`(''E_r, ''d_r)` of `Tot(K^{•,•})` filtered by the second coordinate converges to
`H^n(Tot(K^{•,•}))`. -/
@[stacks 0131 "`(''E_r, ''d_r)` converges"]
abbrev ConvergesToTotalHomology₂ : Prop :=
  CochainComplex.Filtered.Converges K.totalFiltration₂

end HomologicalComplex₂
