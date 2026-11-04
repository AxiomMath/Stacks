module

public import Mathlib.RingTheory.FiniteLength
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.TwoPeriodic
public import StacksFrontier.AlgebraicGeometry.Chow.OrderFractionArithmetic
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesHerbrand.Defs
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicLengthDeterminantOrder
public import StacksFrontier.RingTheory.HilbertSamuel.Function
public import StacksFrontier.RingTheory.Lattice.Distance

/-!
# The multiplicity of a two-periodic complex through colengths of chosen submodules

Let `(M, φ, ψ)` be a `(2, 1)`-periodic complex of modules. Choosing submodules `S ≤ X` of
`ker φ` with `S` inside `im ψ`, and `Y ≤ T` of `ker ψ` with `Y` inside `im φ`, the multiplicity
of the complex is the colength of `S` in `X` minus the colength of `Y` in `T`, corrected by the
four colengths of `X`, `T`, `Y`, `S` in `ker φ`, `ker ψ`, `im φ`, `im ψ`. Those four combine into
the colengths of two submodules `V_φ`, `V_ψ` of `M` built from them, and measuring the latter
through a submodule `Z` common to both turns the multiplicity into a difference of four
colengths, which is the shape in which the determinant formula for a module of one-dimensional
support is proved.

## Main results

* `Module.FiniteLength.length_quotient_eq_ker_add_range_of_isFiniteLength_map_mkQ`: the colength
  of `V` in `M` is the colength of `W` in `ker φ` plus the colength of `φ V` in `im φ`.
* `AlgebraicGeometry.periodicLength_eq_of_le_ker`: the multiplicity through the six colengths.
* `AlgebraicGeometry.periodicLength_eq_sub_add_sub_of_le_ker`: the multiplicity as the
  difference of the four colengths of `S` in `X`, of `Y` in `T`, and of `Z` in `V_ψ` and `V_φ`.
* `AlgebraicGeometry.periodicLength_eq_toAdd_unzero_ordFrac_of_le_ker`: when those four
  colengths are the orders of four nonzero residues `g`, `h`, `f_φ`, `f_ψ` at a prime `q` with
  `R / q` of dimension at most one, the multiplicity is the order of `f_ψ g / (f_φ h)`.

## Implementation notes

A `(2, 1)`-periodic complex is `AlgebraicGeometry.twoPeriodicComplex` and its multiplicity is
`AlgebraicGeometry.periodicLength`; its two cohomology modules are `ker φ / im ψ` and
`ker ψ / im φ`. A colength is the length of a `Submodule.submoduleOf` quotient and takes values in
`ℕ∞`, whereas the multiplicity is an integer: the finiteness needed to pass between the two is
stated as the three lengths of `ker φ / S`, of `ker ψ / Y` and of `M / Z` being finite, each of
which bounds a whole group of the colengths involved.

## References

* [Stacks Project, Tag 02QD](https://stacks.math.columbia.edu/tag/02QD)
-/

@[expose] public section

universe u v

namespace Module.FiniteLength

/-- A submodule viewed inside a larger one is the preimage of the inclusion. -/
private theorem submoduleOf_eq_comap_subtype {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (p q : Submodule R M) :
    p.submoduleOf q = p.comap q.subtype :=
  rfl

/-- Two decompositions of the colength of a common submodule `Z` agree: the colength of `Z` in
`V` plus the colength of `V` in `M` is the colength of `Z` in `M`, however `V` is chosen. -/
theorem length_quotient_submoduleOf_add_length_quotient_eq {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] {Z V W : Submodule R M}
    (hZV : Z ≤ V) (hZW : Z ≤ W) :
    Module.length R (↥V ⧸ Z.submoduleOf V) + Module.length R (M ⧸ V) =
      Module.length R (↥W ⧸ Z.submoduleOf W) + Module.length R (M ⧸ W) := by
  rw [submoduleOf_eq_comap_subtype, submoduleOf_eq_comap_subtype,
    ← length_quotient_add_of_le hZV, ← length_quotient_add_of_le hZW]

/-- Replacing a submodule by an equal one does not change the colength of a fixed submodule
in it. -/
private theorem length_quotient_submoduleOf_congr {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (W : Submodule R M) {A B : Submodule R M} (h : A = B) :
    Module.length R (↥A ⧸ W.submoduleOf A) = Module.length R (↥B ⧸ W.submoduleOf B) := by
  subst h
  rfl

/-- The image of a submodule under the corestriction of a linear map to its range is the copy
of its image inside that range. -/
private theorem map_rangeRestrict_eq_submoduleOf {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (φ : M →ₗ[R] M) (V : Submodule R M) :
    V.map φ.rangeRestrict = (V.map φ).submoduleOf (LinearMap.range φ) := by
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact Submodule.mem_map_of_mem hv
  · rintro ⟨v, hv, hvz⟩
    exact ⟨v, hv, Subtype.ext hvz⟩

/-- Over a Noetherian local ring, let `φ` be an endomorphism of a module `M`, let `W ≤ ker φ` be a
submodule and let `V ⊇ W` be a submodule with `V / W` spanned by a sequence whose successive
quotients are copies of `R / q` for a prime `q` other than the maximal ideal. If `(ker φ ⊓ V) / W`
has finite length, then the colength of `V` in `M` is the colength of `W` in `ker φ` plus the
colength of `φ V` in `im φ`.

The sequence `0 → ker φ → M → im φ → 0` by itself only gives the colength of `V` in `M` as the
colength of `ker φ ⊓ V` in `ker φ` plus the colength of `φ V` in `im φ`; the finite-length
hypothesis on `(ker φ ⊓ V) / W` is what identifies `ker φ ⊓ V` with `W`. -/
theorem length_quotient_eq_ker_add_range_of_isFiniteLength_map_mkQ {R : Type u} {M : Type v}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    {l : ℕ} (q : Ideal R) [q.IsPrime] (hq : q ≠ IsLocalRing.maximalIdeal R) (φ : M →ₗ[R] M)
    {W V : Submodule R M} (hWV : W ≤ V) (hWK : W ≤ LinearMap.ker φ) (x : Fin l → (M ⧸ W))
    (hxf : ∀ i : Fin l,
      Nonempty
        (((spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R (M ⧸ W)) ⧸
            (spanBefore (R := R) x i).comap
              (spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R (M ⧸ W)).subtype) ≃ₗ[R]
          R ⧸ q))
    (hV : V.map W.mkQ = Submodule.span R (Set.range x))
    (hfin : IsFiniteLength R ((LinearMap.ker φ ⊓ V).map W.mkQ)) :
    Module.length R (M ⧸ V) =
      Module.length R (↥(LinearMap.ker φ) ⧸ W.submoduleOf (LinearMap.ker φ)) +
        Module.length R
          (↥(LinearMap.range φ) ⧸ (V.map φ).submoduleOf (LinearMap.range φ)) := by
  have hker : LinearMap.ker φ.rangeRestrict = LinearMap.ker φ := LinearMap.ker_rangeRestrict φ
  rw [length_quotient_eq_add_of_isFiniteLength_map_mkQ q hq φ.rangeRestrict
      φ.surjective_rangeRestrict hWV (by rwa [hker]) x hxf hV (by rwa [hker]),
    length_quotient_submoduleOf_congr W hker, map_rangeRestrict_eq_submoduleOf]

/-- If the colength of `A` in `C` is finite, so are the colengths of `A` in `B` and of `B` in `C`
for any `B` between them. -/
private theorem length_quotient_submoduleOf_ne_top {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] {A B C : Submodule R M} (hAB : A ≤ B) (hBC : B ≤ C)
    (h : Module.length R (↥C ⧸ A.submoduleOf C) ≠ ⊤) :
    Module.length R (↥B ⧸ A.submoduleOf B) ≠ ⊤ ∧ Module.length R (↥C ⧸ B.submoduleOf C) ≠ ⊤ := by
  rw [Module.length_quotient_submoduleOf_eq_add hAB hBC] at h
  exact WithTop.add_ne_top.mp h

/-- For `A ≤ B ≤ C` with finite colength of `A` in `C`, the colengths of `A` in `B` and of `B` in
`C` add up to that of `A` in `C`, as natural numbers. -/
private theorem toNat_length_quotient_submoduleOf_eq_add {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] {A B C : Submodule R M} (hAB : A ≤ B) (hBC : B ≤ C)
    (h : Module.length R (↥C ⧸ A.submoduleOf C) ≠ ⊤) :
    (Module.length R (↥C ⧸ A.submoduleOf C)).toNat =
      (Module.length R (↥B ⧸ A.submoduleOf B)).toNat +
        (Module.length R (↥C ⧸ B.submoduleOf C)).toNat := by
  obtain ⟨h₁, h₂⟩ := length_quotient_submoduleOf_ne_top hAB hBC h
  rw [Module.length_quotient_submoduleOf_eq_add hAB hBC]
  exact ENat.toNat_add h₁ h₂

end Module.FiniteLength

namespace AlgebraicGeometry

open Module.FiniteLength

/-- For a `(2, 1)`-periodic complex `(M, φ, ψ)`, the multiplicity computed from submodules
`S ≤ X ≤ ker φ` with `S ≤ im ψ` and `Y ≤ T ≤ ker ψ` with `Y ≤ im φ`: it is the colength of `S`
in `X` plus the colength of `X` in `ker φ` minus the colength of `S` in `im ψ`, minus the three
corresponding terms for `ψ`. -/
theorem periodicLength_eq_of_le_ker {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] (φ ψ : Module.End R M) (hφψ : φ * ψ = 0) (hψφ : ψ * φ = 0)
    {X S T Y : Submodule R M}
    (hSX : S ≤ X) (hXK : X ≤ LinearMap.ker φ) (hSI : S ≤ LinearMap.range ψ)
    (hYT : Y ≤ T) (hTK : T ≤ LinearMap.ker ψ) (hYI : Y ≤ LinearMap.range φ)
    (hfinφ : Module.length R (↥(LinearMap.ker φ) ⧸ S.submoduleOf (LinearMap.ker φ)) ≠ ⊤)
    (hfinψ : Module.length R (↥(LinearMap.ker ψ) ⧸ Y.submoduleOf (LinearMap.ker ψ)) ≠ ⊤) :
    periodicLength (twoPeriodicComplex φ ψ hφψ hψφ) =
      ((Module.length R (↥X ⧸ S.submoduleOf X)).toNat : ℤ) +
          ((Module.length R
            (↥(LinearMap.ker φ) ⧸ X.submoduleOf (LinearMap.ker φ))).toNat : ℤ) -
          ((Module.length R
            (↥(LinearMap.range ψ) ⧸ S.submoduleOf (LinearMap.range ψ))).toNat : ℤ) -
        (((Module.length R (↥T ⧸ Y.submoduleOf T)).toNat : ℤ) +
          ((Module.length R
            (↥(LinearMap.ker ψ) ⧸ T.submoduleOf (LinearMap.ker ψ))).toNat : ℤ) -
          ((Module.length R
            (↥(LinearMap.range φ) ⧸ Y.submoduleOf (LinearMap.range φ))).toNat : ℤ)) := by
  have hψK : LinearMap.range ψ ≤ LinearMap.ker φ := LinearMap.range_le_ker_iff.mpr hφψ
  have hφK : LinearMap.range φ ≤ LinearMap.ker ψ := LinearMap.range_le_ker_iff.mpr hψφ
  have hhom₀ := homology_length_eq_ker_quotient φ ψ hφψ hψφ (0 : ZMod 2) (Or.inl rfl)
  have hhom₁ := homology_length_eq_ker_quotient φ ψ hφψ hψφ (1 : ZMod 2) (Or.inr rfl)
  rw [ite_eq_left rfl, ← submoduleOf_eq_comap_subtype] at hhom₀
  rw [ite_eq_right (by decide : ¬((1 : ZMod 2) = 0)), ← submoduleOf_eq_comap_subtype] at hhom₁
  have := toNat_length_quotient_submoduleOf_eq_add hSX hXK hfinφ
  have := toNat_length_quotient_submoduleOf_eq_add hSI hψK hfinφ
  have := toNat_length_quotient_submoduleOf_eq_add hYT hTK hfinψ
  have := toNat_length_quotient_submoduleOf_eq_add hYI hφK hfinψ
  show ((Module.length R
      ((twoPeriodicComplex φ ψ hφψ hψφ).homology (0 : ZMod 2))).toNat : ℤ) -
    ((Module.length R
      ((twoPeriodicComplex φ ψ hφψ hψφ).homology (1 : ZMod 2))).toNat : ℤ) = _
  rw [hhom₀, hhom₁]
  omega

/-- For a `(2, 1)`-periodic complex `(M, φ, ψ)` with the submodules of
`AlgebraicGeometry.periodicLength_eq_of_le_ker`, submodules `V_φ`, `V_ψ` whose colengths in `M`
split as `k_φ + i_φ` and `k_ψ + i_ψ`, and a submodule `Z` below both, the multiplicity is the
colength of `S` in `X` minus the colength of `Y` in `T` plus the colength of `Z` in `V_ψ` minus
the colength of `Z` in `V_φ`. -/
theorem periodicLength_eq_sub_add_sub_of_le_ker {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] (φ ψ : Module.End R M) (hφψ : φ * ψ = 0) (hψφ : ψ * φ = 0)
    {X S T Y Vφ Vψ Z : Submodule R M}
    (hSX : S ≤ X) (hXK : X ≤ LinearMap.ker φ) (hSI : S ≤ LinearMap.range ψ)
    (hYT : Y ≤ T) (hTK : T ≤ LinearMap.ker ψ) (hYI : Y ≤ LinearMap.range φ)
    (hZφ : Z ≤ Vφ) (hZψ : Z ≤ Vψ)
    (hmφ : Module.length R (M ⧸ Vφ) =
      Module.length R (↥(LinearMap.ker φ) ⧸ X.submoduleOf (LinearMap.ker φ)) +
        Module.length R (↥(LinearMap.range φ) ⧸ Y.submoduleOf (LinearMap.range φ)))
    (hmψ : Module.length R (M ⧸ Vψ) =
      Module.length R (↥(LinearMap.ker ψ) ⧸ T.submoduleOf (LinearMap.ker ψ)) +
        Module.length R (↥(LinearMap.range ψ) ⧸ S.submoduleOf (LinearMap.range ψ)))
    (hfinφ : Module.length R (↥(LinearMap.ker φ) ⧸ S.submoduleOf (LinearMap.ker φ)) ≠ ⊤)
    (hfinψ : Module.length R (↥(LinearMap.ker ψ) ⧸ Y.submoduleOf (LinearMap.ker ψ)) ≠ ⊤)
    (hfinZ : Module.length R (M ⧸ Z) ≠ ⊤) :
    periodicLength (twoPeriodicComplex φ ψ hφψ hψφ) =
      ((Module.length R (↥X ⧸ S.submoduleOf X)).toNat : ℤ) -
        ((Module.length R (↥T ⧸ Y.submoduleOf T)).toNat : ℤ) +
        ((Module.length R (↥Vψ ⧸ Z.submoduleOf Vψ)).toNat : ℤ) -
        ((Module.length R (↥Vφ ⧸ Z.submoduleOf Vφ)).toNat : ℤ) := by
  have hψK : LinearMap.range ψ ≤ LinearMap.ker φ := LinearMap.range_le_ker_iff.mpr hφψ
  have hφK : LinearMap.range φ ≤ LinearMap.ker ψ := LinearMap.range_le_ker_iff.mpr hψφ
  have hZφne : Module.length R (↥Vφ ⧸ Z.submoduleOf Vφ) +
      Module.length R (M ⧸ Vφ) ≠ ⊤ := by
    rwa [submoduleOf_eq_comap_subtype, ← length_quotient_add_of_le hZφ]
  have hZψne : Module.length R (↥Vψ ⧸ Z.submoduleOf Vψ) +
      Module.length R (M ⧸ Vψ) ≠ ⊤ := by
    rwa [submoduleOf_eq_comap_subtype, ← length_quotient_add_of_le hZψ]
  obtain ⟨hE₁, hE₂⟩ := WithTop.add_ne_top.mp hZφne
  obtain ⟨hF₁, hF₂⟩ := WithTop.add_ne_top.mp hZψne
  have emφ := congrArg ENat.toNat hmφ
  have emψ := congrArg ENat.toNat hmψ
  rw [ENat.toNat_add (length_quotient_submoduleOf_ne_top hSX hXK hfinφ).2
    (length_quotient_submoduleOf_ne_top hYI hφK hfinψ).1] at emφ
  rw [ENat.toNat_add (length_quotient_submoduleOf_ne_top hYT hTK hfinψ).2
    (length_quotient_submoduleOf_ne_top hSI hψK hfinφ).1] at emψ
  have eZ := congrArg ENat.toNat
    (length_quotient_submoduleOf_add_length_quotient_eq hZφ hZψ)
  rw [ENat.toNat_add hE₁ hE₂, ENat.toNat_add hF₁ hF₂] at eZ
  rw [periodicLength_eq_of_le_ker φ ψ hφψ hψφ hSX hXK hSI hYT hTK hYI hfinφ hfinψ]
  omega

/-- For a `(2, 1)`-periodic complex `(M, φ, ψ)` over a Noetherian ring and a prime `q` with
`R / q` of dimension at most one, suppose each of the four colengths of
`AlgebraicGeometry.periodicLength_eq_sub_add_sub_of_le_ker` is the order of a nonzero element
`g`, `h`, `f_φ`, `f_ψ` of the residue field at `q`. Then the multiplicity of the complex is the
order of `f_ψ g / (f_φ h)`. -/
theorem periodicLength_eq_toAdd_unzero_ordFrac_of_le_ker {R : Type u} [CommRing R]
    [IsNoetherianRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (φ ψ : Module.End R M) (hφψ : φ * ψ = 0) (hψφ : ψ * φ = 0)
    (q : Ideal R) [q.IsPrime] [Ring.KrullDimLE 1 (R ⧸ q)]
    {X S T Y Vφ Vψ Z : Submodule R M}
    (hSX : S ≤ X) (hXK : X ≤ LinearMap.ker φ) (hSI : S ≤ LinearMap.range ψ)
    (hYT : Y ≤ T) (hTK : T ≤ LinearMap.ker ψ) (hYI : Y ≤ LinearMap.range φ)
    (hZφ : Z ≤ Vφ) (hZψ : Z ≤ Vψ)
    (hmφ : Module.length R (M ⧸ Vφ) =
      Module.length R (↥(LinearMap.ker φ) ⧸ X.submoduleOf (LinearMap.ker φ)) +
        Module.length R (↥(LinearMap.range φ) ⧸ Y.submoduleOf (LinearMap.range φ)))
    (hmψ : Module.length R (M ⧸ Vψ) =
      Module.length R (↥(LinearMap.ker ψ) ⧸ T.submoduleOf (LinearMap.ker ψ)) +
        Module.length R (↥(LinearMap.range ψ) ⧸ S.submoduleOf (LinearMap.range ψ)))
    (hfinφ : Module.length R (↥(LinearMap.ker φ) ⧸ S.submoduleOf (LinearMap.ker φ)) ≠ ⊤)
    (hfinψ : Module.length R (↥(LinearMap.ker ψ) ⧸ Y.submoduleOf (LinearMap.ker ψ)) ≠ ⊤)
    (hfinZ : Module.length R (M ⧸ Z) ≠ ⊤)
    (g h fφ fψ : q.ResidueField) (hg : g ≠ 0) (hh : h ≠ 0) (hfφ : fφ ≠ 0) (hfψ : fψ ≠ 0)
    (hgX : ((Module.length R (↥X ⧸ S.submoduleOf X)).toNat : ℤ) =
      Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac (R ⧸ q) g)
        ((hg.isUnit.map (Ring.ordFrac (R ⧸ q))).ne_zero)))
    (hhT : ((Module.length R (↥T ⧸ Y.submoduleOf T)).toNat : ℤ) =
      Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac (R ⧸ q) h)
        ((hh.isUnit.map (Ring.ordFrac (R ⧸ q))).ne_zero)))
    (hδφ : ((Module.length R (↥Vφ ⧸ Z.submoduleOf Vφ)).toNat : ℤ) =
      Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac (R ⧸ q) fφ)
        ((hfφ.isUnit.map (Ring.ordFrac (R ⧸ q))).ne_zero)))
    (hδψ : ((Module.length R (↥Vψ ⧸ Z.submoduleOf Vψ)).toNat : ℤ) =
      Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac (R ⧸ q) fψ)
        ((hfψ.isUnit.map (Ring.ordFrac (R ⧸ q))).ne_zero))) :
    periodicLength (twoPeriodicComplex φ ψ hφψ hψφ) =
      Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac (R ⧸ q) (fψ * g / (fφ * h)))
        (((div_ne_zero (mul_ne_zero hfψ hg) (mul_ne_zero hfφ hh)).isUnit.map
          (Ring.ordFrac (R ⧸ q))).ne_zero)) := by
  rw [periodicLength_eq_sub_add_sub_of_le_ker φ ψ hφψ hψφ hSX hXK hSI hYT hTK hYI hZφ hZψ
    hmφ hmψ hfinφ hfinψ hfinZ, hgX, hhT, hδφ, hδψ,
    toAdd_unzero_ordFrac_mul_div_mul g h fψ fφ hg hh hfψ hfφ]

end AlgebraicGeometry

end
