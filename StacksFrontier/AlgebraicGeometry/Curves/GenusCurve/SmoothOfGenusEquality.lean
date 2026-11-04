module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BirationalGenus
public import StacksFrontier.AlgebraicGeometry.Curves.NormalRegular
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusAlgClosure
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.SeparableDegreeFibreSum
public import StacksFrontier.AlgebraicGeometry.InvertibleFunctions.ProperVariety
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.FieldDescent
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RegularCompactification
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationOverField
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.SmoothRationalPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.RationalPointHyperplane

/-!
# A curve whose geometric genus is its genus is smooth

Let `C` be a proper curve over a field `F` which stays integral over an algebraically closed
field `L ⊇ F`. Its geometric genus over `L` is the genus of the normalization of `C_L`, which is at
most the genus of `C_L`; when the two agree, the normalization morphism is an isomorphism by the
equality case of [Stacks, Tag 0CE4], so `C_L` is normal of dimension one, hence regular, hence
smooth over the perfect field `L`, and `C` is smooth over `F` by descent. Applied over the field
of constants `κ = H⁰(C, 𝒪_C)` of a proper curve over `k` with a smooth `κ`-rational point, this is
the last step of the proof of [Stacks, Tag 0CEE].

## Main results

* `AlgebraicGeometry.smooth_of_geometricGenus_pullback_eq_genus`: a proper curve whose base change
  to an algebraically closed field is integral with geometric genus equal to its genus is smooth.
* `AlgebraicGeometry.smooth_toSpecΓ_and_isSeparable_of_geometricGenus_eq`: a proper curve over `k`
  with a smooth rational point over `κ = Γ(C, 𝒪_C)` and `g_geom(C/k) = [κ : k] · g_κ` is smooth
  over `κ`, and `κ/k` is separable when `g_κ ≠ 0`.

## References

* [Stacks Project, Tag 0CE4](https://stacks.math.columbia.edu/tag/0CE4)
* [Stacks Project, Tag 0CE5](https://stacks.math.columbia.edu/tag/0CE5)
* [Stacks Project, Tag 0CDW](https://stacks.math.columbia.edu/tag/0CDW)
* [Stacks Project, Tag 0CEE](https://stacks.math.columbia.edu/tag/0CEE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Order

universe u

namespace AlgebraicGeometry

variable (F L : Type u) [Field F] [Field L] [IsAlgClosed L] (φ : F →+* L) {C : Scheme.{u}}
  (f : C ⟶ Spec (.of F))

/-- **A proper curve which becomes normal over an algebraically closed field is smooth.** If the
normalization of the base change `C_L` of a proper scheme `C` of dimension one over `F` to an
algebraically closed field `L` is an isomorphism, then `C` is smooth over `F`: `C_L` is normal of
dimension one, hence regular, hence smooth over the perfect field `L`, and smoothness descends
along `F → L`. -/
theorem smooth_of_isIso_normalizationOverField_pullback [IsProper f]
    (hdim : topologicalKrullDim (C : Type u) ≤ 1)
    [IsReduced (pullback f (Spec.map (CommRingCat.ofHom φ)))]
    [IsIso (normalizationOverField L (pullback.snd f (Spec.map (CommRingCat.ofHom φ))))] :
    Smooth f := by
  set Z := pullback f (Spec.map (CommRingCat.ofHom φ))
  set c : Z ⟶ Spec (.of L) := pullback.snd f (Spec.map (CommRingCat.ofHom φ))
  have : LocallyOfFiniteType c := inferInstance
  have hZdim : topologicalKrullDim (Z : Type u) ≤ 1 :=
    (topologicalKrullDim_pullback_snd_eq F L φ f).trans_le hdim
  have hfin := finite_irreducibleComponents_of_locallyOfFiniteType L c
  have : IsNormal (Z.normalizationScheme hfin) :=
    Scheme.isNormal_normalizationScheme_of_isReduced Z hfin
  have : IsNormal Z := isNormal_of_iso (asIso (normalizationOverField L c)).symm
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian c
  have hreg := isRegular_of_isNormal_of_topologicalKrullDim_le_one Z hZdim
  have hc : Smooth c := smooth_of_isRegular_of_perfectField L c hreg
  let : Algebra F L := φ.toAlgebra
  exact smooth_of_smooth_pullback_snd_spec_algebraMap F L f hc

/-- **A proper curve whose geometric genus over an algebraically closed field is its genus is
smooth.** Let `C` be a proper scheme of dimension one over `F` and `φ : F → L` an embedding into
an algebraically closed field with `C_L` integral. If `g_geom(C_L/L) = g(C_L)`, then `C` is
smooth over `F`: the geometric genus of `C_L` is the genus of its normalization `C_L^ν`, the map
`H⁰(C_L) → H⁰(C_L^ν)` is onto because both are `L`, so [Stacks, Tag 0CE4] makes the normalization
an isomorphism. -/
theorem smooth_of_geometricGenus_pullback_eq_genus [IsProper f]
    (hdim : topologicalKrullDim (C : Type u) = 1)
    [IsIntegral (pullback f (Spec.map (CommRingCat.ofHom φ)))]
    (heq : geometricGenus L (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) =
      genus (pullback.snd f (Spec.map (CommRingCat.ofHom φ)))) :
    Smooth f := by
  set Z := pullback f (Spec.map (CommRingCat.ofHom φ))
  set c : Z ⟶ Spec (.of L) := pullback.snd f (Spec.map (CommRingCat.ofHom φ))
  have : LocallyOfFiniteType c := inferInstance
  have hZdim : topologicalKrullDim (Z : Type u) = 1 :=
    (topologicalKrullDim_pullback_snd_eq F L φ f).trans hdim
  rw [geometricGenus_eq_ite_genus_normalizationOverField L c hZdim.le, if_pos hZdim] at heq
  have hfin := finite_irreducibleComponents_of_locallyOfFiniteType L c
  have : IsFinite (normalizationOverField L c) := isFinite_normalizationOverField L c
  have hbir : IsBirational (normalizationOverField L c) := Scheme.isBirational_normalization Z hfin
  have : IsProper (normalizationOverField L c ≫ c) := isProper_normalizationOverField_comp L c
  have hsurj : Function.Surjective (normalizationOverField L c).appTop.hom := by
    have : IsProperVariety L (normalizationOverField L c ≫ c) := { }
    have h := surjective_appTop_of_isAlgClosed L (normalizationOverField L c ≫ c)
    rw [Scheme.Hom.comp_appTop] at h
    intro b
    obtain ⟨a, rfl⟩ := h b
    exact ⟨_, rfl⟩
  have : IsIso (normalizationOverField L c) :=
    isIso_of_isProper_of_isBirational_of_genus_eq L c _ hbir hZdim.le hsurj heq
  exact smooth_of_isIso_normalizationOverField_pullback F L φ f hdim.le

/-- **A proper curve with a smooth rational point whose geometric genus is `[κ : k] · g` is smooth
over its field of constants.** Let `C` be a proper curve over `k`, `κ = Γ(C, 𝒪_C)` and
`g = dim_κ H¹(C, 𝒪_C)`. Suppose `C ⟶ Spec κ` has a `κ`-rational point at which it is smooth, and
`g_geom(C/k) = [κ : k] · g`. Then `C` is smooth over `κ`, and `κ/k` is separable if `g ≠ 0`.

By [Stacks, Tag 0CDW] the smooth rational point makes `C` geometrically integral over `κ`. The
geometric genus is the sum over the `[κ : k]_s` embeddings `t : κ → k̄` of the geometric genera of
the fibres `C_t`, each at most `g` ([Stacks, Tag 0CE5]); equality with `[κ : k] · g` forces
`[κ : k]_s g = [κ : k] g` and `g_geom(C_t/k̄) = g = g(C_t)` for every `t`. So each `C_t` is smooth
over `k̄` by `AlgebraicGeometry.smooth_of_geometricGenus_pullback_eq_genus`, and smoothness
descends to `C ⟶ Spec κ`. -/
theorem smooth_toSpecΓ_and_isSeparable_of_geometricGenus_eq (k : Type u) [Field k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve k f] [IsProper f] :
    letI : Field Γ(C, ⊤) := (isField_of_universallyClosed k f).toField
    letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    ∀ c : C, IsRationalPoint C.toSpecΓ c → InfinitesimalLifting.SmoothAt C.toSpecΓ c →
      geometricGenus k f = Module.finrank k Γ(C, ⊤) * genus C.toSpecΓ →
      Smooth C.toSpecΓ ∧ (genus C.toSpecΓ ≠ 0 → Algebra.IsSeparable k Γ(C, ⊤)) := by
  let : Field Γ(C, ⊤) := (isField_of_universallyClosed k f).toField
  let : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  intro c hc hsm heq
  have : IsProper C.toSpecΓ := Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ f
  have : Module.Finite k Γ(C, ⊤) := by
    rw [← RingHom.finite_algebraMap]
    exact (finite_appTop_of_universallyClosed k f).comp
      (RingHom.Finite.of_surjective ((Scheme.ΓSpecIso (.of k)).inv.hom) fun x ↦
        ⟨(Scheme.ΓSpecIso (.of k)).hom.hom x, by simp⟩)
  have : IsVariety Γ(C, ⊤) C.toSpecΓ := { }
  have hgi : GeometricallyIntegral C.toSpecΓ :=
    geometricallyIntegral_of_isVariety_of_smoothAt_rationalPoint C.toSpecΓ
      (ptOfIsRationalPoint _ c hc) (ptOfIsRationalPoint_comp _ c hc)
      (by rwa [ptOfIsRationalPoint_apply])
  have hdim : topologicalKrullDim (C : Type u) = 1 := IsCurve.topologicalKrullDim_eq_one (f := f)
  have hsum := geometricGenus_eq_finsum_geometricGenus_pullback_snd_toSpecΓ k f
  have hgen := genus_pullback_snd_toSpecΓ_eq k f
  set g := genus C.toSpecΓ
  let G : (Γ(C, ⊤) →ₐ[k] AlgebraicClosure k) → ℕ := fun t =>
    geometricGenus (AlgebraicClosure k)
      (pullback.snd C.toSpecΓ (Spec.map (CommRingCat.ofHom t.toRingHom)))
  have hle : ∀ t, G t ≤ g := fun t => hgen t ▸ geometricGenus_le_genus_of_dim_le_one _ _
    ((topologicalKrullDim_pullback_snd_eq Γ(C, ⊤) (AlgebraicClosure k) t.toRingHom
      C.toSpecΓ).trans hdim).le
  let : Fintype (Γ(C, ⊤) →ₐ[k] AlgebraicClosure k) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype] at hsum
  have hcard : Fintype.card (Γ(C, ⊤) →ₐ[k] AlgebraicClosure k) =
      Field.finSepDegree k Γ(C, ⊤) := by
    rw [Field.finSepDegree_eq_of_isAlgClosed k Γ(C, ⊤) (AlgebraicClosure k),
      Nat.card_eq_fintype_card]
  have hconst : ∑ _t : Γ(C, ⊤) →ₐ[k] AlgebraicClosure k, g =
      Field.finSepDegree k Γ(C, ⊤) * g := by
    rw [Finset.sum_const, Finset.card_univ, hcard, smul_eq_mul]
  have h3 : ∑ t, G t = Module.finrank k Γ(C, ⊤) * g := by rw [← hsum, heq]
  have hmul : Field.finSepDegree k Γ(C, ⊤) * g = Module.finrank k Γ(C, ⊤) * g :=
    le_antisymm (Nat.mul_le_mul_right g (Field.finSepDegree_le_finrank k Γ(C, ⊤)))
      (h3 ▸ hconst ▸ Finset.sum_le_sum fun t _ => hle t)
  have hG : ∀ t, G t = g := fun t =>
    (Finset.sum_eq_sum_iff_of_le (g := fun _ => g) fun t _ => hle t).mp
      (by rw [h3, ← hmul, hconst]) t (Finset.mem_univ t)
  refine ⟨?_, fun hg => ?_⟩
  · obtain ⟨t₀⟩ : Nonempty (Γ(C, ⊤) →ₐ[k] AlgebraicClosure k) :=
      ⟨IsAlgClosed.lift (M := AlgebraicClosure k)⟩
    have : IsIntegral (pullback C.toSpecΓ
        (Spec.map (CommRingCat.ofHom t₀.toRingHom))) :=
      pullback_of_geometrically hgi.geometrically_isIntegral (AlgebraicClosure k) _
    exact smooth_of_geometricGenus_pullback_eq_genus Γ(C, ⊤) (AlgebraicClosure k) t₀.toRingHom
      C.toSpecΓ hdim ((hG t₀).trans (hgen t₀).symm)
  · exact (Field.finSepDegree_eq_finrank_iff k Γ(C, ⊤)).mp
      (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hg) hmul)

end AlgebraicGeometry

end
