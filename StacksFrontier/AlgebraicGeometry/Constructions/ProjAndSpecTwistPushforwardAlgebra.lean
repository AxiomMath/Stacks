module

public import StacksFrontier.RingTheory.GradedAlgebra.TruncationLocalizationShift
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.TwistSections
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjLocalizedRingMap

/-!
# The degree-`i` part of `B[1/ψ f]` as a direct sum of homogeneous parts of `A[1/f]`

Let `A = ⨁_{d ≥ 0} A_d` be a graded ring, `B = ⨁_{d ≥ 0} A_{≥ d}` its truncation algebra,
`f ∈ A_d` with `d > 0` and `g = ψ(f) ∈ B_d`. Stacks, Section 0EKF, displays the equality of
homogeneous parts `(B[1/g])_{i} = ⨁_{m ≥ i} (A[1/f])_m`; it is
`Stacks.Truncation.map_locPiece_eq_iSup_awayPieceInt`, through the ring map
`Stacks.Truncation.locToLocalization : B[1/g] → A[1/f]`. This file rewrites it in the form the
twisting sheaves need, with the homogeneous parts written as
`Stacks.ProjectiveCohomology.awayGrading`, the description of the sections of `𝒪(i)` over a
standard open:

* `Stacks.Truncation.twistPieceToLocalization`: the map `(B[1/g])_i → A[1/f]`, injective;
* `Stacks.Truncation.twistPieceIncl`: for `m ≥ i`, the inclusion `(A[1/f])_m → (B[1/g])_i`,
  the unique lift along that map;
* `Stacks.Truncation.twistPieceSumEquiv`: `⨁_{m ≥ i} (A[1/f])_m ≃+ (B[1/g])_i`.

It also proves that `locToLocalization` intertwines the restriction maps of localizations,
`Stacks.Truncation.locToLocalization_localizedRingMap`.

## References

* [Stacks Project, Tag 0EKF](https://stacks.math.columbia.edu/tag/0EKF)
-/

@[expose] public noncomputable section

open Stacks.AlgebraicGeometry.ProjAndSpecTruncation AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.Truncation

universe u

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {d : ℕ} {f : A}

/-- An element of `(B[1/ψ f])_i`, in the form `Stacks.ProjectiveCohomology.awayGrading`, lies in
`Stacks.Truncation.locPiece`. -/
theorem mem_locPiece_of_mem_awayGrading (hf : f ∈ 𝒜 d) (hd : 0 < d) (i : ℤ)
    {z : LocalizedModule.Away (psi 𝒜 f) (TruncationRing 𝒜)}
    (hz : z ∈ Stacks.ProjectiveCohomology.awayGrading (grading 𝒜) ((psi 𝒜).map_mem hf) i) :
    (z : Localization.Away (psi 𝒜 f)) ∈ locPiece 𝒜 d hf hd i := by
  obtain ⟨k, b, hb, rfl⟩ := hz
  by_cases h : 0 ≤ ((k * d : ℕ) : ℤ) + i
  · have hb' : b ∈ grading 𝒜 (((k * d : ℕ) : ℤ) + i).toNat := by
      simp only [integerGrading, h, ↓reduceIte] at hb
      exact hb
    exact ⟨k, (((k * d : ℕ) : ℤ) + i).toNat, b, by push_cast at h ⊢; omega, hb', rfl⟩
  · have hb0 : b = 0 := by
      simpa only [integerGrading, h, ↓reduceIte, Submodule.mem_bot] using hb
    subst hb0
    convert zero_mem (locPiece 𝒜 d hf hd i)
    exact LocalizedModule.zero_mk _

/-- An element of `Stacks.Truncation.locPiece` lies in `(B[1/ψ f])_i`, in the form
`Stacks.ProjectiveCohomology.awayGrading`. -/
theorem mem_awayGrading_of_mem_locPiece (hf : f ∈ 𝒜 d) (hd : 0 < d) (i : ℤ)
    {z : Localization.Away (psi 𝒜 f)} (hz : z ∈ locPiece 𝒜 d hf hd i) :
    (z : LocalizedModule.Away (psi 𝒜 f) (TruncationRing 𝒜)) ∈
      Stacks.ProjectiveCohomology.awayGrading (grading 𝒜) ((psi 𝒜).map_mem hf) i := by
  obtain ⟨k, n, b, hn, hb, rfl⟩ := hz
  refine ⟨k, b, ?_, rfl⟩
  have hn' : ((k * d : ℕ) : ℤ) + i = (n : ℤ) := by push_cast; omega
  rw [hn', integerGrading_natCast]
  exact hb

/-- An element of `Stacks.Truncation.awayPieceInt` lies in the degree-`m` part of `A[1/f]`, in
the form `Stacks.ProjectiveCohomology.awayGrading`. -/
theorem mem_awayGrading_of_mem_awayPieceInt (hf : f ∈ 𝒜 d) (hd : 0 < d) (m : ℤ)
    {z : Localization.Away f} (hz : z ∈ awayPieceInt 𝒜 d hf hd m) :
    (z : LocalizedModule.Away f A) ∈ Stacks.ProjectiveCohomology.awayGrading 𝒜 hf m := by
  obtain ⟨k, n, a, hn, ha, rfl⟩ := hz
  refine ⟨k, a, ?_, rfl⟩
  have hn' : ((k * d : ℕ) : ℤ) + m = (n : ℤ) := by push_cast; omega
  rw [hn', integerGrading_natCast]
  exact ha

/-- An element of the degree-`m` part of `A[1/f]`, in the form
`Stacks.ProjectiveCohomology.awayGrading`, lies in `Stacks.Truncation.awayPieceInt`. -/
theorem mem_awayPieceInt_of_mem_awayGrading (hf : f ∈ 𝒜 d) (hd : 0 < d) (m : ℤ)
    {z : LocalizedModule.Away f A} (hz : z ∈ Stacks.ProjectiveCohomology.awayGrading 𝒜 hf m) :
    (z : Localization.Away f) ∈ awayPieceInt 𝒜 d hf hd m := by
  obtain ⟨k, a, ha, rfl⟩ := hz
  by_cases h : 0 ≤ ((k * d : ℕ) : ℤ) + m
  · have ha' : a ∈ 𝒜 (((k * d : ℕ) : ℤ) + m).toNat := by
      simp only [integerGrading, h, ↓reduceIte] at ha
      exact ha
    exact ⟨k, (((k * d : ℕ) : ℤ) + m).toNat, a, by push_cast at h ⊢; omega, ha', rfl⟩
  · have ha0 : a = 0 := by
      simpa only [integerGrading, h, ↓reduceIte, Submodule.mem_bot] using ha
    subst ha0
    convert zero_mem (awayPieceInt 𝒜 d hf hd m)
    exact LocalizedModule.zero_mk _

/-- The map `(B[1/ψ f])_i → A[1/f]`, `b / (ψ f)ᵏ ↦ b / fᵏ`, on the degree-`i` part in the form
`Stacks.ProjectiveCohomology.awayGrading`. -/
def twistPieceToLocalization (hf : f ∈ 𝒜 d) (i : ℤ) :
    Stacks.ProjectiveCohomology.awayGrading (grading 𝒜) ((psi 𝒜).map_mem hf) i →+
      Localization.Away f :=
  (locToLocalization 𝒜).toAddMonoidHom.comp
    (Stacks.ProjectiveCohomology.awayGrading (grading 𝒜) ((psi 𝒜).map_mem hf)
      i).subtype.toAddMonoidHom

/-- `twistPieceToLocalization` is `locToLocalization` on the underlying fraction. -/
@[simp] theorem twistPieceToLocalization_apply (hf : f ∈ 𝒜 d) (i : ℤ)
    (z : Stacks.ProjectiveCohomology.awayGrading (grading 𝒜) ((psi 𝒜).map_mem hf) i) :
    twistPieceToLocalization 𝒜 hf i z =
      locToLocalization 𝒜 (z : LocalizedModule.Away (psi 𝒜 f) (TruncationRing 𝒜)) :=
  rfl

/-- **The map `(B[1/ψ f])_i → A[1/f]` is injective.** -/
theorem twistPieceToLocalization_injective (hf : f ∈ 𝒜 d) (hd : 0 < d) (i : ℤ) :
    Function.Injective (twistPieceToLocalization 𝒜 hf i) := by
  refine (injective_iff_map_eq_zero _).mpr fun z hz => Subtype.ext ?_
  exact locToLocalization_injOn_locPiece hf hd i (mem_locPiece_of_mem_awayGrading 𝒜 hf hd i z.2)
    (show locToLocalization 𝒜 (z : Localization.Away (psi 𝒜 f)) = 0 from hz)

/-- **For `m ≥ i`, every element of `(A[1/f])_m` comes from `(B[1/ψ f])_i`**, by the equality
of homogeneous parts `(B[1/g])_i = ⨁_{m ≥ i} (A[1/f])_m`. -/
theorem mem_range_twistPieceToLocalization (hf : f ∈ 𝒜 d) (hd : 0 < d) {i m : ℤ} (him : i ≤ m)
    {z : LocalizedModule.Away f A} (hz : z ∈ Stacks.ProjectiveCohomology.awayGrading 𝒜 hf m) :
    (z : Localization.Away f) ∈ (twistPieceToLocalization 𝒜 hf i).range := by
  have hz' : (z : Localization.Away f) ∈
      (locPiece 𝒜 d hf hd i).map (locToLocalization 𝒜).toAddMonoidHom := by
    rw [map_locPiece_eq_iSup_awayPieceInt]
    exact AddSubgroup.mem_iSup_of_mem m (AddSubgroup.mem_iSup_of_mem him
      (mem_awayPieceInt_of_mem_awayGrading 𝒜 hf hd m hz))
  obtain ⟨w, hw, hwz⟩ := hz'
  exact ⟨⟨w, mem_awayGrading_of_mem_locPiece 𝒜 hf hd i hw⟩, hwz⟩

/-- **The image of `(B[1/ψ f])_i` in `A[1/f]` lies in the sum of the `(A[1/f])_m`, `m ≥ i`.** -/
theorem twistPieceToLocalization_mem_iSup (hf : f ∈ 𝒜 d) (hd : 0 < d) (i : ℤ)
    (z : Stacks.ProjectiveCohomology.awayGrading (grading 𝒜) ((psi 𝒜).map_mem hf) i) :
    twistPieceToLocalization 𝒜 hf i z ∈ ⨆ (m : ℤ) (_ : i ≤ m), awayPieceInt 𝒜 d hf hd m := by
  rw [← map_locPiece_eq_iSup_awayPieceInt]
  exact ⟨_, mem_locPiece_of_mem_awayGrading 𝒜 hf hd i z.2, rfl⟩

/-- For `m ≥ i`, the inclusion `(A[1/f])_m → (B[1/ψ f])_i`: the unique lift along the injective
map `twistPieceToLocalization`. -/
def twistPieceIncl (hf : f ∈ 𝒜 d) (hd : 0 < d) {i m : ℤ} (him : i ≤ m) :
    Stacks.ProjectiveCohomology.awayGrading 𝒜 hf m →+
      Stacks.ProjectiveCohomology.awayGrading (grading 𝒜) ((psi 𝒜).map_mem hf) i where
  toFun z := (AddMonoidHom.ofInjective (twistPieceToLocalization_injective 𝒜 hf hd i)).symm
    ⟨(z : LocalizedModule.Away f A), mem_range_twistPieceToLocalization 𝒜 hf hd him z.2⟩
  map_zero' := by
    rw [← map_zero (AddMonoidHom.ofInjective (twistPieceToLocalization_injective 𝒜 hf hd i)).symm]
    rfl
  map_add' z w := by
    rw [← map_add (AddMonoidHom.ofInjective (twistPieceToLocalization_injective 𝒜 hf hd i)).symm]
    rfl

/-- **The inclusion `(A[1/f])_m → (B[1/ψ f])_i` is a section of `twistPieceToLocalization`.** -/
@[simp] theorem twistPieceToLocalization_twistPieceIncl (hf : f ∈ 𝒜 d) (hd : 0 < d) {i m : ℤ}
    (him : i ≤ m) (z : Stacks.ProjectiveCohomology.awayGrading 𝒜 hf m) :
    twistPieceToLocalization 𝒜 hf i (twistPieceIncl 𝒜 hf hd him z) =
      (z : LocalizedModule.Away f A) :=
  congrArg Subtype.val ((AddMonoidHom.ofInjective
    (twistPieceToLocalization_injective 𝒜 hf hd i)).apply_symm_apply
      ⟨(z : LocalizedModule.Away f A), mem_range_twistPieceToLocalization 𝒜 hf hd him z.2⟩)

/-- The inclusions `(A[1/f])_m → (B[1/ψ f])_i`, `m ≥ i`, summed over `m`. -/
def twistPieceSum (hf : f ∈ 𝒜 d) (hd : 0 < d) (i : ℤ) :
    (DirectSum {m : ℤ // i ≤ m} fun m => Stacks.ProjectiveCohomology.awayGrading 𝒜 hf m.1) →+
      Stacks.ProjectiveCohomology.awayGrading (grading 𝒜) ((psi 𝒜).map_mem hf) i :=
  DirectSum.toAddMonoid fun m => twistPieceIncl 𝒜 hf hd m.2

/-- `twistPieceSum` on the `m`-th summand is the inclusion `twistPieceIncl`. -/
@[simp] theorem twistPieceSum_of (hf : f ∈ 𝒜 d) (hd : 0 < d) (i : ℤ) (m : {m : ℤ // i ≤ m})
    (z : Stacks.ProjectiveCohomology.awayGrading 𝒜 hf m.1) :
    twistPieceSum 𝒜 hf hd i (DirectSum.of _ m z) = twistPieceIncl 𝒜 hf hd m.2 z :=
  DirectSum.toAddMonoid_of _ _ _

/-- Read in `A[1/f]`, `twistPieceSum` is the sum of the homogeneous components. -/
theorem twistPieceToLocalization_twistPieceSum (hf : f ∈ 𝒜 d) (hd : 0 < d) (i : ℤ)
    (x : DirectSum {m : ℤ // i ≤ m} fun m => Stacks.ProjectiveCohomology.awayGrading 𝒜 hf m.1) :
    twistPieceToLocalization 𝒜 hf i (twistPieceSum 𝒜 hf hd i x) =
      DirectSum.coeAddMonoidHom (fun m : {m : ℤ // i ≤ m} =>
        Stacks.ProjectiveCohomology.awayGrading 𝒜 hf m.1) x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of m z => rw [twistPieceSum_of, twistPieceToLocalization_twistPieceIncl,
      DirectSum.coeAddMonoidHom_of]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- The homogeneous parts `(A[1/f])_m`, `m ≥ i`, are independent. -/
theorem iSupIndep_awayGrading_ge (hf : f ∈ 𝒜 d) (i : ℤ) :
    iSupIndep (fun m : {m : ℤ // i ≤ m} => Stacks.ProjectiveCohomology.awayGrading 𝒜 hf m.1) :=
  (Stacks.ProjectiveCohomology.iSupIndep_awayGrading 𝒜 hf).comp Subtype.val_injective

/-- The sum of the homogeneous parts `(A[1/f])_m`, `m ≥ i`, is injective. -/
theorem coeAddMonoidHom_awayGrading_ge_injective (hf : f ∈ 𝒜 d) (i : ℤ) :
    Function.Injective (DirectSum.coeAddMonoidHom (fun m : {m : ℤ // i ≤ m} =>
      Stacks.ProjectiveCohomology.awayGrading 𝒜 hf m.1)) := by
  have h := (iSupIndep_awayGrading_ge 𝒜 hf i).dfinsupp_lsum_injective
  refine fun x y hxy => h ?_
  have hc : ∀ z, DFinsupp.lsum ℕ (fun m : {m : ℤ // i ≤ m} =>
      (Stacks.ProjectiveCohomology.awayGrading 𝒜 hf m.1).subtype) z =
      DirectSum.coeAddMonoidHom (fun m : {m : ℤ // i ≤ m} =>
        Stacks.ProjectiveCohomology.awayGrading 𝒜 hf m.1) z := by
    intro z
    induction z using DirectSum.induction_on with
    | zero => simp
    | of m w =>
      rw [DirectSum.coeAddMonoidHom_of, DirectSum.of, DFinsupp.singleAddHom_apply,
        DFinsupp.lsum_single]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [hc, hc]
  exact hxy

/-- **`⨁_{m ≥ i} (A[1/f])_m ≃+ (B[1/ψ f])_i`** (Stacks, Section 0EKF), with the homogeneous parts
written as `Stacks.ProjectiveCohomology.awayGrading`. -/
@[stacks 0EKF "the equality of homogeneous parts (B[1/g])_{i} = ⨁_{m ≥ i} (A[1/f])_m, g = ψ(f), \
as an additive equivalence onto the degree-i part"]
def twistPieceSumEquiv (hf : f ∈ 𝒜 d) (hd : 0 < d) (i : ℤ) :
    (DirectSum {m : ℤ // i ≤ m} fun m => Stacks.ProjectiveCohomology.awayGrading 𝒜 hf m.1) ≃+
      Stacks.ProjectiveCohomology.awayGrading (grading 𝒜) ((psi 𝒜).map_mem hf) i :=
  AddEquiv.ofBijective (twistPieceSum 𝒜 hf hd i) <| by
    refine ⟨fun x y hxy => coeAddMonoidHom_awayGrading_ge_injective 𝒜 hf i ?_, fun w => ?_⟩
    · rw [← twistPieceToLocalization_twistPieceSum 𝒜 hf hd,
        ← twistPieceToLocalization_twistPieceSum 𝒜 hf hd, hxy]
    · have hw := twistPieceToLocalization_mem_iSup 𝒜 hf hd i w
      have hle : (⨆ (m : ℤ) (_ : i ≤ m), awayPieceInt 𝒜 d hf hd m) ≤
          (DirectSum.coeAddMonoidHom (fun m : {m : ℤ // i ≤ m} =>
            Stacks.ProjectiveCohomology.awayGrading 𝒜 hf m.1)).range := by
        refine iSup₂_le fun m him z hz => ?_
        exact ⟨DirectSum.of (fun m : {m : ℤ // i ≤ m} =>
            Stacks.ProjectiveCohomology.awayGrading 𝒜 hf m.1) ⟨m, him⟩
            ⟨(z : LocalizedModule.Away f A), mem_awayGrading_of_mem_awayPieceInt 𝒜 hf hd m hz⟩,
          DirectSum.coeAddMonoidHom_of _ _ _⟩
      obtain ⟨x, hx⟩ := hle hw
      refine ⟨x, twistPieceToLocalization_injective 𝒜 hf hd i ?_⟩
      rw [twistPieceToLocalization_twistPieceSum]
      exact hx

/-- `twistPieceSumEquiv` is `twistPieceSum`. -/
@[simp] theorem twistPieceSumEquiv_apply (hf : f ∈ 𝒜 d) (hd : 0 < d) (i : ℤ)
    (x : DirectSum {m : ℤ // i ≤ m} fun m => Stacks.ProjectiveCohomology.awayGrading 𝒜 hf m.1) :
    twistPieceSumEquiv 𝒜 hf hd i x = twistPieceSum 𝒜 hf hd i x :=
  rfl

/-! ### Compatibility with restriction -/

/-- **`locToLocalization` intertwines the restriction maps of localizations**: the one of `B`
attached to `D₊(ψ g) ⊆ D₊(ψ f)` on the source, the one of `A` attached to `D₊(g) ⊆ D₊(f)` on
the target. -/
theorem locToLocalization_localizedRingMap {g : A}
    (hf : ∃ d : ℕ, 0 < d ∧ f ∈ 𝒜 d) (hg : ∃ e : ℕ, 0 < e ∧ g ∈ 𝒜 e)
    (hψf : ∃ d : ℕ, 0 < d ∧ psi 𝒜 f ∈ grading 𝒜 d)
    (hψg : ∃ e : ℕ, 0 < e ∧ psi 𝒜 g ∈ grading 𝒜 e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (hψfg : ProjectiveSpectrum.basicOpen (grading 𝒜) (psi 𝒜 g) ≤
      ProjectiveSpectrum.basicOpen (grading 𝒜) (psi 𝒜 f))
    (z : Localization.Away (psi 𝒜 f)) :
    locToLocalization 𝒜
        (ProjectiveSpectrum.localizedRingMap (grading 𝒜) (psi 𝒜 f) (psi 𝒜 g) hψf hψg hψfg z) =
      ProjectiveSpectrum.localizedRingMap 𝒜 f g hf hg hfg (locToLocalization 𝒜 z) := by
  have hkey : (locToLocalization 𝒜 (f := g)).comp
        (ProjectiveSpectrum.localizedRingMap (grading 𝒜) (psi 𝒜 f) (psi 𝒜 g)
          hψf hψg hψfg).toRingHom =
      (ProjectiveSpectrum.localizedRingMap 𝒜 f g hf hg hfg).toRingHom.comp
        (locToLocalization 𝒜 (f := f)) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (psi 𝒜 f)) ?_
    refine RingHom.ext fun b => ?_
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [AlgHom.commutes, locToLocalization, locToLocalization, IsLocalization.Away.lift_eq,
      IsLocalization.Away.lift_eq, RingHom.comp_apply, RingHom.comp_apply, AlgHom.commutes]
  exact congrArg (fun φ : Localization.Away (psi 𝒜 f) →+* Localization.Away g => φ z) hkey

/-- `awayToLocalization` is `locToLocalization` on the underlying fraction. -/
theorem awayToLocalization_eq_locToLocalization
    (z : HomogeneousLocalization.Away (grading 𝒜) (psi 𝒜 f)) :
    awayToLocalization 𝒜 z = locToLocalization 𝒜 z.val :=
  rfl

end Stacks.Truncation

end
