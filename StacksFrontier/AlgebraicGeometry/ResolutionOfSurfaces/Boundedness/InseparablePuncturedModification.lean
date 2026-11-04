module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.InseparableFirstCohomologyAnnihilator
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpFiniteCase
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.PuncturedSpectrumModification
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PuncturedSpectrumSectionsDepthTwo
public import StacksFrontier.AlgebraicGeometry.Properties.NormalDepthTwo
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PuncturedSpectrum

/-!
# A modification of a normal surface singularity over the punctured spectrum

Let `A` be a Noetherian local normal domain of dimension two, `f : X ⟶ Spec A` a modification and
`U = f⁻¹(Spec A ∖ {𝔪})` the inverse image of the punctured spectrum. Then:

* `U` is nonempty, and `U ⟶ Spec A` is an open immersion onto the punctured spectrum;
* every function on `U` extends to `X` (Hartogs: `A` has depth two, so the punctured spectrum
  has the same functions as `Spec A`, [Stacks, Tag 0EY9]);
* the local ring of `X` at a point of `U` is a localization of `A`: every element is `a / s`
  with `a, s ∈ A` and `s` a unit there;
* consequently, an additive `θ_K : K ⟶ K` of the shape `θ_K(z / s) = θ(z sᵖ⁻¹) / s` preserves
  the local rings of `X` at the points of `U`.

## Main results

* `AlgebraicGeometry.SeparableGoUp.puncturedPreimage`: the open `U`.
* `AlgebraicGeometry.SeparableGoUp.surjective_restrict_puncturedPreimage`: the Hartogs extension.
* `AlgebraicGeometry.SeparableGoUp.exists_mul_eq_of_mem_puncturedPreimage`: the stalks over `U`
  are localizations of `A`.
* `AlgebraicGeometry.SeparableGoUp.exists_algebraMap_eq_thetaK`: `θ_K` preserves those stalks.

## References

* [Stacks Project, Tag 0B4U](https://stacks.math.columbia.edu/tag/0B4U)
* [Stacks Project, Tag 0EY9](https://stacks.math.columbia.edu/tag/0EY9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.LocalCohomology (puncturedSpectrum)

universe u

namespace AlgebraicGeometry.SeparableGoUp

variable {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- The inverse image of the punctured spectrum `Spec A ∖ {𝔪}` under `f : X ⟶ Spec A`. -/
abbrev puncturedPreimage : X.Opens := f ⁻¹ᵁ puncturedSpectrum (.of A)

variable [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] (hdim : ringKrullDim A = 2)
  (hf : IsModification f)

include hdim hf in
/-- The restriction of `f` over the punctured spectrum, `U ⟶ Spec A ∖ {𝔪}`, is an isomorphism. -/
theorem isIso_morphismRestrict_puncturedSpectrum :
    IsIso (f ∣_ (puncturedSpectrum (.of A))) :=
  isIso_morphismRestrict_of_isModification (CommRingCat.of A) hdim.le f hf _
    (fun h => h rfl)

include hdim hf in
/-- `U ⟶ Spec A` is an open immersion. -/
theorem isOpenImmersion_puncturedPreimage_ι_comp :
    IsOpenImmersion ((puncturedPreimage f).ι ≫ f) := by
  have := isIso_morphismRestrict_puncturedSpectrum f hdim hf
  rw [← morphismRestrict_ι]
  infer_instance

include hdim hf in
/-- `U ⟶ Spec A` has the punctured spectrum as its image. -/
theorem range_puncturedPreimage_ι_comp :
    Set.range ((puncturedPreimage f).ι ≫ f).base = {IsLocalRing.closedPoint A}ᶜ := by
  have := isIso_morphismRestrict_puncturedSpectrum f hdim hf
  rw [← morphismRestrict_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (f ∣_ (puncturedSpectrum (.of A))).surjective,
    Set.image_univ,
    Scheme.Opens.range_ι]
  rfl

include hdim hf in
/-- `U` is nonempty: its image is the punctured spectrum, which contains the generic point. -/
theorem nonempty_puncturedPreimage : Nonempty (puncturedPreimage f) := by
  have := isIso_morphismRestrict_puncturedSpectrum f hdim hf
  have hne : (⊥ : PrimeSpectrum A) ≠ IsLocalRing.closedPoint A := by
    intro h
    have := ringKrullDim_eq_zero_of_isField
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr (congrArg PrimeSpectrum.asIdeal h).symm)
    rw [hdim] at this
    exact absurd this (by decide)
  obtain ⟨y, -⟩ := (f ∣_ (puncturedSpectrum (.of A))).surjective ⟨(⊥ : PrimeSpectrum A), hne⟩
  exact ⟨y⟩

include hdim hf in
/-- **Hartogs for a modification of a normal surface singularity.** Every function on the inverse
image of the punctured spectrum extends to `X`. -/
theorem surjective_restrict_puncturedPreimage :
    Function.Surjective (X.presheaf.map (homOfLE (le_top : puncturedPreimage f ≤ ⊤)).op) := by
  have := isOpenImmersion_puncturedPreimage_ι_comp f hdim hf
  have hdepth : (2 : ℕ∞) ≤ Module.depth A (IsLocalRing.maximalIdeal A) A :=
    Stacks.NormalDepth.two_le_depth_of_isIntegrallyClosed A (by rw [hdim])
  have hb := Stacks.LocalCohomology.bijective_appTop_of_punctured_of_depth_ge_two A
    ((puncturedPreimage f).ι ≫ f) (range_puncturedPreimage_ι_comp f hdim hf) hdepth
  have hmor : X.presheaf.map (homOfLE (le_top : puncturedPreimage f ≤ ⊤)).op =
      (puncturedPreimage f).ι.appTop ≫ (Scheme.Opens.topIso (puncturedPreimage f)).hom := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
    exact Eq.trans (by rfl) (X.presheaf.map_comp _ _)
  have hι : Function.Surjective (puncturedPreimage f).ι.appTop := by
    intro t
    obtain ⟨a, ha⟩ := hb.2 t
    exact ⟨_, ha⟩
  intro t
  obtain ⟨t', ht'⟩ :=
    (ConcreteCategory.bijective_of_isIso (Scheme.Opens.topIso (puncturedPreimage f)).hom).2 t
  obtain ⟨s, hs⟩ := hι t'
  exact ⟨s, by rw [hmor, ConcreteCategory.comp_apply, hs, ht']⟩

include hdim hf in
/-- At a point of `U` the stalk map of `f` is an isomorphism. -/
theorem isIso_stalkMap_of_mem_puncturedPreimage (x : X) (hx : x ∈ puncturedPreimage f) :
    IsIso (f.stalkMap x) := by
  have := isOpenImmersion_puncturedPreimage_ι_comp f hdim hf
  have h1 : IsIso (((puncturedPreimage f).ι ≫ f).stalkMap ⟨x, hx⟩) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp ‹_›).2 _
  have h2 : IsIso ((puncturedPreimage f).ι.stalkMap ⟨x, hx⟩) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 _
  rw [Scheme.Hom.stalkMap_comp (puncturedPreimage f).ι f ⟨x, hx⟩] at h1
  exact @IsIso.of_isIso_comp_right _ _ _ _ _
    (f.stalkMap ((puncturedPreimage f).ι ⟨x, hx⟩)) ((puncturedPreimage f).ι.stalkMap ⟨x, hx⟩) h2 h1

include hdim hf in
/-- **The local rings of `X` over the punctured spectrum are localizations of `A`.** At a point
`x` of `U` every element of `𝒪_{X,x}` is `a / s` with `a, s ∈ A` and `s` a unit in `𝒪_{X,x}`. -/
theorem exists_mul_eq_of_mem_puncturedPreimage (x : X) (hx : x ∈ puncturedPreimage f)
    (w : X.presheaf.stalk x) :
    ∃ a s : A, IsUnit (X.presheaf.germ ⊤ x trivial (baseSection X f s)) ∧
      w * X.presheaf.germ ⊤ x trivial (baseSection X f s) =
        X.presheaf.germ ⊤ x trivial (baseSection X f a) := by
  have := isIso_stalkMap_of_mem_puncturedPreimage f hdim hf x hx
  obtain ⟨v, rfl⟩ := (ConcreteCategory.bijective_of_isIso (f.stalkMap x)).2 w
  let q : PrimeSpectrum A := f x
  let : Algebra A ((Spec (.of A)).presheaf.stalk (f x)) := StructureSheaf.stalkAlgebra A q
  have : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk (f x)) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A q
  have key : ∀ r : A, f.stalkMap x (algebraMap A ((Spec (.of A)).presheaf.stalk (f x)) r) =
      X.presheaf.germ ⊤ x trivial (baseSection X f r) := fun r => by
    show f.stalkMap x ((Spec (.of A)).presheaf.germ ⊤ (f x) trivial
      ((Scheme.ΓSpecIso (.of A)).inv r)) = _
    rw [Scheme.Hom.germ_stalkMap_apply f ⊤ x trivial]
    rfl
  obtain ⟨⟨a, s⟩, hv⟩ := IsLocalization.surj q.asIdeal.primeCompl v
  refine ⟨a, s, ?_, ?_⟩
  · rw [← key]
    exact (IsLocalization.map_units _ s).map (f.stalkMap x).hom
  · rw [← key, ← key, ← map_mul]
    exact congrArg _ hv

end AlgebraicGeometry.SeparableGoUp

namespace AlgebraicGeometry.SeparableGoUp

variable {A : Type u} [CommRing A] [IsDomain A] {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (.of A)) (U : X.Opens) {p : ℕ}

omit [IsDomain A] in
/-- **A Frobenius splitting extended to the function field preserves the local rings of `X` at
points where they are localizations of `A`.** If every element of `𝒪_{X,x}` is `a / s` with
`a, s ∈ A`, `s` a unit, then `θ_K(z / s) = θ(z sᵖ⁻¹) / s` lies in `𝒪_{X,x}` for
`z / s ∈ 𝒪_{X,x}`. -/
theorem exists_algebraMap_eq_thetaK (θ : A →+ A) (θK : X.functionField →+ X.functionField)
    (hθK : ∀ z s : A, s ≠ 0 →
      θK (X.presheaf.germ ⊤ (genericPoint X) trivial (baseSection X f z) /
          X.presheaf.germ ⊤ (genericPoint X) trivial (baseSection X f s)) =
        X.presheaf.germ ⊤ (genericPoint X) trivial (baseSection X f (θ (z * s ^ (p - 1)))) /
          X.presheaf.germ ⊤ (genericPoint X) trivial (baseSection X f s))
    (hloc : ∀ x : X, x ∈ U → ∀ w : X.presheaf.stalk x,
      ∃ a s : A, IsUnit (X.presheaf.germ ⊤ x trivial (baseSection X f s)) ∧
        w * X.presheaf.germ ⊤ x trivial (baseSection X f s) =
          X.presheaf.germ ⊤ x trivial (baseSection X f a))
    (x : X) (hx : x ∈ U) (w : X.presheaf.stalk x) :
    ∃ b : X.presheaf.stalk x,
      algebraMap _ X.functionField b = θK (algebraMap _ X.functionField w) := by
  obtain ⟨a, s, hu, hw⟩ := hloc x hx w
  have : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  have hg : ∀ r : A, algebraMap _ X.functionField (X.presheaf.germ ⊤ x trivial (baseSection X f r))
      = X.presheaf.germ ⊤ (genericPoint X) trivial (baseSection X f r) := fun r =>
    X.algebraMap_germ_eq_germToFunctionField (U := ⊤) trivial _
  have hs0 : X.presheaf.germ ⊤ (genericPoint X) trivial (baseSection X f s) ≠ 0 := by
    rw [← hg]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)).mpr
      hu.ne_zero
  have hsA : s ≠ 0 := by
    rintro rfl
    exact hs0 (by simp [baseSection])
  have hz : algebraMap _ X.functionField w =
      X.presheaf.germ ⊤ (genericPoint X) trivial (baseSection X f a) /
        X.presheaf.germ ⊤ (genericPoint X) trivial (baseSection X f s) := by
    rw [eq_div_iff hs0, ← hg, ← hg, ← map_mul, hw]
  refine ⟨X.presheaf.germ ⊤ x trivial (baseSection X f (θ (a * s ^ (p - 1)))) * ↑hu.unit⁻¹, ?_⟩
  rw [hz, hθK a s hsA, map_mul, hg, div_eq_mul_inv, ← hg s]
  congr 1
  exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, hu.val_inv_mul, map_one])

end AlgebraicGeometry.SeparableGoUp

end
