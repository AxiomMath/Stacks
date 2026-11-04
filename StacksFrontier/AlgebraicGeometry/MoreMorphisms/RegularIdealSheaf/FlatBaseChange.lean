module

public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.BaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.AffineRegular
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.RegularOpenIndependence
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat base change of a regular immersion

Let `i : Z ⟶ X` be a regular immersion and `g : X' ⟶ X` a flat morphism. Then the base change
`X' ×_X Z ⟶ X'` of `i` along `g` is again a regular immersion, and likewise for Koszul-regular,
`H₁`-regular and quasi-regular immersions. This is Stacks tag 067P.

## Main results

* `Stacks.AlgebraicGeometry.isRegularIdealSheaf_definingIdealOfHom_of_isPullback_of_flat`: the
  statement for a closed immersion and a cartesian square whose vertical legs are flat.
* `Stacks.AlgebraicGeometry.isRegularImmersion_of_isPullback_of_flat`: the same for an arbitrary
  immersion and an arbitrary cartesian square.
* `Stacks.AlgebraicGeometry.isRegularImmersion_pullback_snd_of_flat`: the same for the base
  change `pullback.snd i g`.
* `Stacks.AlgebraicGeometry.isKoszulRegularIdealSheaf_definingIdealOfHom_of_isPullback_of_flat`,
  `Stacks.AlgebraicGeometry.isKoszulRegularImmersion_of_isPullback_of_flat` and
  `Stacks.AlgebraicGeometry.isKoszulRegularImmersion_pullback_snd_of_flat`: the same three
  statements for Koszul-regularity.
* `Stacks.AlgebraicGeometry.isH1RegularIdealSheaf_definingIdealOfHom_of_isPullback_of_flat`,
  `Stacks.AlgebraicGeometry.isH1RegularImmersion_of_isPullback_of_flat` and
  `Stacks.AlgebraicGeometry.isH1RegularImmersion_pullback_snd_of_flat`: the same three
  statements for `H₁`-regularity.
* `Stacks.AlgebraicGeometry.isQuasiRegularIdealSheaf_definingIdealOfHom_of_isPullback_of_flat`,
  `Stacks.AlgebraicGeometry.isQuasiRegularImmersion_of_isPullback_of_flat` and
  `Stacks.AlgebraicGeometry.isQuasiRegularImmersion_pullback_snd_of_flat`: the same three
  statements for quasi-regularity.

## References

* [Stacks Project, Lemma 31.21.4 (Tag 067P)](https://stacks.math.columbia.edu/tag/067P)
* [Stacks Project, Lemma 31.20.3 (Tag 063G)](https://stacks.math.columbia.edu/tag/063G)
* [Stacks Project, Lemma 31.21.2 (Tag 063J)](https://stacks.math.columbia.edu/tag/063J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry RingTheory.Sequence
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.AlgebraicGeometry

universe u

section ClosedImmersion

/-- For a cartesian square with `i : Z ⟶ X` a closed immersion, an affine open `U` of `X` and an
affine open `V` of `X'` inside `g⁻¹U`, the kernel of the base change `j` on `V` is the extension
along `g.appLE U V` of the kernel of `i` on `U`. -/
private theorem ker_appLE_of_isPullback {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} {j : Z' ⟶ X'}
    {k : Z' ⟶ Z} {g : X' ⟶ X} [IsClosedImmersion i] (H : IsPullback j k g i)
    {U : X.Opens} (hU : IsAffineOpen U) {V : X'.Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ g ⁻¹ᵁ U) :
    RingHom.ker (j.app V).hom =
      (RingHom.ker (i.app U).hom).map (g.appLE U V hVU).hom := by
  have hsurj : Function.Surjective (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom := by
    rw [Scheme.Hom.appLE_eq_app]
    exact i.app_surjective U hU
  have hk := Stacks.Flatness.ker_inl_of_isPushout
    (Stacks.Flatness.isPushout_appLE_of_isPullback H hU hV hVU) hsurj
  rwa [Scheme.Hom.appLE_eq_app (f := j) (U := V), Scheme.Hom.appLE_eq_app (f := i) (U := U)] at hk

/-- In a cartesian square with `i` a closed immersion, the image in `X` of a point of `Z'` lies in
the support of the quotient by the defining ideal of `i`. -/
private theorem apply_mem_idealQuotientSupport {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} {j : Z' ⟶ X'}
    {k : Z' ⟶ Z} {g : X' ⟶ X} [IsClosedImmersion i] (H : IsPullback j k g i) (z : Z') :
    g (j z) ∈ idealQuotientSupport X.toRingedSpace (definingIdealOfHom i) := by
  rw [definingIdealQuotient_support_eq_range]
  exact ⟨k z, congrArg (fun F : Z' ⟶ X => F.base z) H.w.symm⟩

/-- In a cartesian square of closed immersions, a family generating the defining ideal of `i` over
an affine open `U` is sent by `g.appLE U V` to a family generating the defining ideal of `j` over
an affine open `V ≤ g⁻¹U`. -/
private theorem isGeneratedByOn_definingIdealOfHom_appLE_of_isPullback
    {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} {j : Z' ⟶ X'} {k : Z' ⟶ Z} {g : X' ⟶ X}
    [IsClosedImmersion i] [IsClosedImmersion j] (H : IsPullback j k g i)
    {U : X.Opens} (hU : IsAffineOpen U) {V : X'.Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ g ⁻¹ᵁ U) {r : ℕ} (f : Fin r → Γ(X, U))
    (hgen : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) U f) :
    IsGeneratedByOn X'.toRingedSpace (definingIdealOfHom j) V
      (fun a => (g.appLE U V hVU).hom (f a)) := by
  refine isGeneratedByOn_definingIdealOfHom_of_ker_app_eq_span j hV _ ?_
  rw [ker_appLE_of_isPullback H hU hV hVU, ker_app_eq_span_range i hU _ hgen,
    Ideal.map_span, ← Set.range_comp]
  rfl

/-- Let `i : Z ⟶ X` be a closed immersion whose defining ideal is regular, let `g : X' ⟶ X` be
flat and let `H` exhibit the closed immersion `j : Z' ⟶ X'` as the base change of `i` along `g`.
Then the defining ideal of `j` is regular. -/
theorem isRegularIdealSheaf_definingIdealOfHom_of_isPullback_of_flat
    {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} {j : Z' ⟶ X'} {k : Z' ⟶ Z} {g : X' ⟶ X}
    [IsClosedImmersion i] [IsClosedImmersion j] [Flat g] (H : IsPullback j k g i)
    (hi : IsRegularIdealSheaf X.toRingedSpace (definingIdealOfHom i)) :
    IsRegularIdealSheaf X'.toRingedSpace (definingIdealOfHom j) := by
  rw [isRegularIdealSheaf_iff_exists_affine_generators]
  intro x hx
  rw [definingIdealQuotient_support_eq_range] at hx
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨U, hxU, r, f, hgen, hwr⟩ :=
    (isRegularIdealSheaf_iff_exists_affine_generators X _).mp hi (g (j z))
      (apply_mem_idealQuotientSupport H z)
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens
    (show j z ∈ g ⁻¹ᵁ U.1 from hxU)
  refine ⟨⟨V, hV⟩, hxV, r, fun a => (g.appLE U.1 V hVU).hom (f a), ?_, ?_⟩
  · exact isGeneratedByOn_definingIdealOfHom_appLE_of_isPullback H U.2 hV hVU f hgen
  · exact isWeaklyRegular_ofFn_map_of_flat _ (g.flat_appLE U.2 hV hVU) f hwr

end ClosedImmersion

section Immersion

/-- For a cartesian square with `i` an immersion, the base change `j` factors as a closed immersion
`l` into the preimage of the coborder range of `i`, and `l` is the base change of
`i.liftCoborder`. -/
private theorem exists_isClosedImmersion_isPullback_coborderRange
    {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} [IsImmersion i] {j : Z' ⟶ X'} {k : Z' ⟶ Z} {g : X' ⟶ X}
    (H : IsPullback j k g i) :
    ∃ l : Z' ⟶ (g ⁻¹ᵁ i.coborderRange).toScheme, l ≫ (g ⁻¹ᵁ i.coborderRange).ι = j ∧
      IsClosedImmersion l ∧ IsPullback l k (g ∣_ i.coborderRange) i.liftCoborder := by
  have hjD : ∀ z, j z ∈ g ⁻¹ᵁ i.coborderRange := by
    intro z
    change g (j z) ∈ i.coborderRange
    rw [← Scheme.Hom.comp_apply, H.w]
    exact subset_coborder ⟨k z, rfl⟩
  let l : Z' ⟶ (g ⁻¹ᵁ i.coborderRange).toScheme :=
    IsOpenImmersion.lift (g ⁻¹ᵁ i.coborderRange).ι j (by
      rintro _ ⟨z, rfl⟩
      exact ⟨⟨j z, hjD z⟩, rfl⟩)
  have hlD : l ≫ (g ⁻¹ᵁ i.coborderRange).ι = j := IsOpenImmersion.lift_fac _ _ _
  have hcomm : k ≫ i.liftCoborder = l ≫ g ∣_ i.coborderRange := by
    apply (cancel_mono i.coborderRange.ι).mp
    rw [Category.assoc, i.liftCoborder_ι, Category.assoc, morphismRestrict_ι,
      ← Category.assoc, hlD]
    exact H.w.symm
  have houter : IsPullback k (l ≫ (g ⁻¹ᵁ i.coborderRange).ι)
      (i.liftCoborder ≫ i.coborderRange.ι) g := by
    rw [hlD, i.liftCoborder_ι]
    exact H.flip
  have hsq := (houter.of_bot hcomm (isPullback_morphismRestrict g i.coborderRange)).flip
  exact ⟨l, hlD, MorphismProperty.of_isPullback hsq.flip inferInstance, hsq⟩

/-- Let `i : Z ⟶ X` be a regular immersion, let `g : X' ⟶ X` be flat and let `H` exhibit the
immersion `j : Z' ⟶ X'` as the base change of `i` along `g`. Then `j` is a regular immersion. -/
theorem isRegularImmersion_of_isPullback_of_flat {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X}
    [IsImmersion i] {j : Z' ⟶ X'} [IsImmersion j] {k : Z' ⟶ Z} {g : X' ⟶ X} [Flat g]
    (H : IsPullback j k g i) (hi : IsRegularImmersion i) : IsRegularImmersion j := by
  obtain ⟨l, hlD, _, hsq⟩ := exists_isClosedImmersion_isPullback_coborderRange H
  refine (isRegularImmersion_iff_of_open j (g ⁻¹ᵁ i.coborderRange) l hlD).mpr ?_
  exact isRegularIdealSheaf_definingIdealOfHom_of_isPullback_of_flat hsq
    ((isRegularImmersion_iff_of_open i i.coborderRange i.liftCoborder i.liftCoborder_ι).mp hi)

/-- A regular immersion remains a regular immersion after base change along a flat morphism. -/
@[stacks 067P "regular"]
theorem isRegularImmersion_pullback_snd_of_flat {Z X X' : Scheme.{u}} (i : Z ⟶ X) (g : X' ⟶ X)
    [IsImmersion i] [Flat g] (hi : IsRegularImmersion i) :
    IsRegularImmersion (pullback.snd i g) :=
  isRegularImmersion_of_isPullback_of_flat (IsPullback.of_hasPullback i g).flip hi

end Immersion

section KoszulRegular

/-- Let `i : Z ⟶ X` be a closed immersion whose defining ideal is Koszul-regular, let `g : X' ⟶ X`
be flat and let `H` exhibit the closed immersion `j : Z' ⟶ X'` as the base change of `i` along `g`.
Then the defining ideal of `j` is Koszul-regular. -/
theorem isKoszulRegularIdealSheaf_definingIdealOfHom_of_isPullback_of_flat
    {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} {j : Z' ⟶ X'} {k : Z' ⟶ Z} {g : X' ⟶ X}
    [IsClosedImmersion i] [IsClosedImmersion j] [Flat g] (H : IsPullback j k g i)
    (hi : IsKoszulRegularIdealSheaf X.toRingedSpace (definingIdealOfHom i)) :
    IsKoszulRegularIdealSheaf X'.toRingedSpace (definingIdealOfHom j) := by
  intro x hx
  rw [definingIdealQuotient_support_eq_range] at hx
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨U₀, hxU₀, r, f₀, hK₀, hgen₀⟩ := hi (g (j z)) (apply_mem_idealQuotientSupport H z)
  obtain ⟨U, hU, hxU, hUU₀⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxU₀
  have hgen : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) U
      (fun a => X.presheaf.map (homOfLE hUU₀).op (f₀ a)) :=
    isGeneratedByOn_of_le U₀ f₀ hgen₀ U hUU₀
  have hK : IsKoszulSequenceExactOn X.toRingedSpace U
      (fun a => X.presheaf.map (homOfLE hUU₀).op (f₀ a)) (fun n => 0 < n) :=
    hK₀.of_le U hUU₀
  obtain ⟨V, hV, hxV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens
    (show j z ∈ g ⁻¹ᵁ U from hxU)
  refine ⟨V, hxV, r,
    fun a => (g.appLE U V hVU).hom (X.presheaf.map (homOfLE hUU₀).op (f₀ a)), ?_, ?_⟩
  · have hpull := isKoszulSequenceExactOn_pullbackSections g.toLRSHom (hasFlatStalks_of_flat g) U
      (fun a => X.presheaf.map (homOfLE hUU₀).op (f₀ a)) (fun n => 0 < n) hK
    have hfam : (fun a => X'.presheaf.map (homOfLE hVU).op
          (pullbackSections g.toLRSHom U
            (fun a => X.presheaf.map (homOfLE hUU₀).op (f₀ a)) a))
        = fun a => (g.appLE U V hVU).hom (X.presheaf.map (homOfLE hUU₀).op (f₀ a)) := rfl
    exact hfam ▸ hpull.of_le V hVU
  · exact isGeneratedByOn_definingIdealOfHom_appLE_of_isPullback H hU hV hVU _ hgen

/-- Let `i : Z ⟶ X` be a Koszul-regular immersion, let `g : X' ⟶ X` be flat and let `H` exhibit the
immersion `j : Z' ⟶ X'` as the base change of `i` along `g`. Then `j` is a Koszul-regular
immersion. -/
theorem isKoszulRegularImmersion_of_isPullback_of_flat {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X}
    [IsImmersion i] {j : Z' ⟶ X'} [IsImmersion j] {k : Z' ⟶ Z} {g : X' ⟶ X} [Flat g]
    (H : IsPullback j k g i) (hi : IsKoszulRegularImmersion i) :
    IsKoszulRegularImmersion j := by
  obtain ⟨l, hlD, _, hsq⟩ := exists_isClosedImmersion_isPullback_coborderRange H
  refine (isKoszulRegularImmersion_iff_of_open j (g ⁻¹ᵁ i.coborderRange) l hlD).mpr ?_
  exact isKoszulRegularIdealSheaf_definingIdealOfHom_of_isPullback_of_flat hsq
    ((isKoszulRegularImmersion_iff_of_open i i.coborderRange i.liftCoborder
      i.liftCoborder_ι).mp hi)

/-- A Koszul-regular immersion remains a Koszul-regular immersion after base change along a flat
morphism. -/
@[stacks 067P "koszul"]
theorem isKoszulRegularImmersion_pullback_snd_of_flat {Z X X' : Scheme.{u}} (i : Z ⟶ X)
    (g : X' ⟶ X) [IsImmersion i] [Flat g] (hi : IsKoszulRegularImmersion i) :
    IsKoszulRegularImmersion (pullback.snd i g) :=
  isKoszulRegularImmersion_of_isPullback_of_flat (IsPullback.of_hasPullback i g).flip hi

/-- Let `i : Z ⟶ X` be a closed immersion whose defining ideal is `H₁`-regular, let `g : X' ⟶ X` be
flat and let `H` exhibit the closed immersion `j : Z' ⟶ X'` as the base change of `i` along `g`.
Then the defining ideal of `j` is `H₁`-regular. -/
theorem isH1RegularIdealSheaf_definingIdealOfHom_of_isPullback_of_flat
    {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} {j : Z' ⟶ X'} {k : Z' ⟶ Z} {g : X' ⟶ X}
    [IsClosedImmersion i] [IsClosedImmersion j] [Flat g] (H : IsPullback j k g i)
    (hi : IsH1RegularIdealSheaf X.toRingedSpace (definingIdealOfHom i)) :
    IsH1RegularIdealSheaf X'.toRingedSpace (definingIdealOfHom j) := by
  intro x hx
  rw [definingIdealQuotient_support_eq_range] at hx
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨U₀, hxU₀, r, f₀, hK₀, hgen₀⟩ := hi (g (j z)) (apply_mem_idealQuotientSupport H z)
  obtain ⟨U, hU, hxU, hUU₀⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxU₀
  have hgen : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) U
      (fun a => X.presheaf.map (homOfLE hUU₀).op (f₀ a)) :=
    isGeneratedByOn_of_le U₀ f₀ hgen₀ U hUU₀
  have hK : IsKoszulSequenceExactOn X.toRingedSpace U
      (fun a => X.presheaf.map (homOfLE hUU₀).op (f₀ a)) (fun n => n = 1) :=
    hK₀.of_le U hUU₀
  obtain ⟨V, hV, hxV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens
    (show j z ∈ g ⁻¹ᵁ U from hxU)
  refine ⟨V, hxV, r,
    fun a => (g.appLE U V hVU).hom (X.presheaf.map (homOfLE hUU₀).op (f₀ a)), ?_, ?_⟩
  · have hpull := isKoszulSequenceExactOn_pullbackSections g.toLRSHom (hasFlatStalks_of_flat g) U
      (fun a => X.presheaf.map (homOfLE hUU₀).op (f₀ a)) (fun n => n = 1) hK
    have hfam : (fun a => X'.presheaf.map (homOfLE hVU).op
          (pullbackSections g.toLRSHom U
            (fun a => X.presheaf.map (homOfLE hUU₀).op (f₀ a)) a))
        = fun a => (g.appLE U V hVU).hom (X.presheaf.map (homOfLE hUU₀).op (f₀ a)) := rfl
    exact hfam ▸ hpull.of_le V hVU
  · exact isGeneratedByOn_definingIdealOfHom_appLE_of_isPullback H hU hV hVU _ hgen

/-- Let `i : Z ⟶ X` be a `H₁`-regular immersion, let `g : X' ⟶ X` be flat and let `H` exhibit the
immersion `j : Z' ⟶ X'` as the base change of `i` along `g`. Then `j` is a `H₁`-regular
immersion. -/
theorem isH1RegularImmersion_of_isPullback_of_flat {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X}
    [IsImmersion i] {j : Z' ⟶ X'} [IsImmersion j] {k : Z' ⟶ Z} {g : X' ⟶ X} [Flat g]
    (H : IsPullback j k g i) (hi : IsH1RegularImmersion i) :
    IsH1RegularImmersion j := by
  obtain ⟨l, hlD, _, hsq⟩ := exists_isClosedImmersion_isPullback_coborderRange H
  refine (isH1RegularImmersion_iff_of_open j (g ⁻¹ᵁ i.coborderRange) l hlD).mpr ?_
  exact isH1RegularIdealSheaf_definingIdealOfHom_of_isPullback_of_flat hsq
    ((isH1RegularImmersion_iff_of_open i i.coborderRange i.liftCoborder
      i.liftCoborder_ι).mp hi)

/-- A `H₁`-regular immersion remains a `H₁`-regular immersion after base change along a flat
morphism. -/
@[stacks 067P "h1"]
theorem isH1RegularImmersion_pullback_snd_of_flat {Z X X' : Scheme.{u}} (i : Z ⟶ X)
    (g : X' ⟶ X) [IsImmersion i] [Flat g] (hi : IsH1RegularImmersion i) :
    IsH1RegularImmersion (pullback.snd i g) :=
  isH1RegularImmersion_of_isPullback_of_flat (IsPullback.of_hasPullback i g).flip hi

/-- Let `i : Z ⟶ X` be a closed immersion whose defining ideal is quasi-regular, let `g : X' ⟶ X`
be flat and let `H` exhibit the closed immersion `j : Z' ⟶ X'` as the base change of `i` along `g`.
Then the defining ideal of `j` is quasi-regular. -/
@[ega "IV 19.1.5" "(ii), special case"]
theorem isQuasiRegularIdealSheaf_definingIdealOfHom_of_isPullback_of_flat
    {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} {j : Z' ⟶ X'} {k : Z' ⟶ Z} {g : X' ⟶ X}
    [IsClosedImmersion i] [IsClosedImmersion j] [Flat g] (H : IsPullback j k g i)
    (hi : IsQuasiRegularIdealSheaf X.toRingedSpace (definingIdealOfHom i)) :
    IsQuasiRegularIdealSheaf X'.toRingedSpace (definingIdealOfHom j) := by
  intro x hx
  rw [definingIdealQuotient_support_eq_range] at hx
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨U₀, hxU₀, r, f₀, hiso₀, hgen₀⟩ := hi (g (j z)) (apply_mem_idealQuotientSupport H z)
  obtain ⟨U, hU, hxU, hUU₀⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxU₀
  have hgen : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) U
      (fun a => X.presheaf.map (homOfLE hUU₀).op (f₀ a)) :=
    isGeneratedByOn_of_le U₀ f₀ hgen₀ U hUU₀
  have hiso := isQuasiRegularMap_isIso_of_le hiso₀ U hUU₀
  obtain ⟨V, hV, hxV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens
    (show j z ∈ g ⁻¹ᵁ U from hxU)
  refine ⟨V, hxV, r,
    fun a => (g.appLE U V hVU).hom (X.presheaf.map (homOfLE hUU₀).op (f₀ a)), ?_, ?_⟩
  · have hpullGerm := forall_isQuasiRegularRel_germFamily_pullbackSections g.toLRSHom
      (hasFlatStalks_of_flat g) U (fun a => X.presheaf.map (homOfLE hUU₀).op (f₀ a))
      ((isQuasiRegularMapIso_iff_forall_germ X.toRingedSpace U _).mp hiso)
    have hpull := (isQuasiRegularMapIso_iff_forall_germ X'.toRingedSpace (g ⁻¹ᵁ U)
      (pullbackSections g.toLRSHom U
        (fun a => X.presheaf.map (homOfLE hUU₀).op (f₀ a)))).mpr hpullGerm
    have hfam : (fun a => X'.presheaf.map (homOfLE hVU).op
          (pullbackSections g.toLRSHom U
            (fun a => X.presheaf.map (homOfLE hUU₀).op (f₀ a)) a))
        = fun a => (g.appLE U V hVU).hom (X.presheaf.map (homOfLE hUU₀).op (f₀ a)) := rfl
    exact hfam ▸ isQuasiRegularMap_isIso_of_le hpull V hVU
  · exact isGeneratedByOn_definingIdealOfHom_appLE_of_isPullback H hU hV hVU _ hgen

/-- Let `i : Z ⟶ X` be a quasi-regular immersion, let `g : X' ⟶ X` be flat and let `H` exhibit the
immersion `j : Z' ⟶ X'` as the base change of `i` along `g`. Then `j` is a quasi-regular
immersion. -/
@[ega "IV 19.1.5" "(ii)"]
theorem isQuasiRegularImmersion_of_isPullback_of_flat {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X}
    [IsImmersion i] {j : Z' ⟶ X'} [IsImmersion j] {k : Z' ⟶ Z} {g : X' ⟶ X} [Flat g]
    (H : IsPullback j k g i) (hi : IsQuasiRegularImmersion i) :
    IsQuasiRegularImmersion j := by
  obtain ⟨l, hlD, _, hsq⟩ := exists_isClosedImmersion_isPullback_coborderRange H
  refine (isQuasiRegularImmersion_iff_of_open j (g ⁻¹ᵁ i.coborderRange) l hlD).mpr ?_
  exact isQuasiRegularIdealSheaf_definingIdealOfHom_of_isPullback_of_flat hsq
    ((isQuasiRegularImmersion_iff_of_open i i.coborderRange i.liftCoborder
      i.liftCoborder_ι).mp hi)

/-- A quasi-regular immersion remains a quasi-regular immersion after base change along a flat
morphism. -/
@[stacks 067P "quasi", ega "IV 19.1.5" "(ii)"]
theorem isQuasiRegularImmersion_pullback_snd_of_flat {Z X X' : Scheme.{u}} (i : Z ⟶ X)
    (g : X' ⟶ X) [IsImmersion i] [Flat g] (hi : IsQuasiRegularImmersion i) :
    IsQuasiRegularImmersion (pullback.snd i g) :=
  isQuasiRegularImmersion_of_isPullback_of_flat (IsPullback.of_hasPullback i g).flip hi

end KoszulRegular

end Stacks.AlgebraicGeometry

end
