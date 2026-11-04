module

public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.DerivedDirectImage

/-!
# The derived direct image of a bounded below coherent complex with proper support

Let `S` be a Noetherian scheme, let `f : X ⟶ S` be a morphism locally of finite type and let `E`
be an object of `D^+_Coh(𝒪_X)` such that the support of every `H^i(E)` is proper over `S`. Then
`Rf_*E` is an object of `D^+_Coh(𝒪_S)`. This is [Stacks, Tag 0D0B].

Everything below lives in the namespace `Stacks.AlgebraicGeometry.ProperSupportCoherent`.

## Main results

* `isGE_derivedPushforward`: the unbounded derived direct image is left `t`-exact — it carries
  `D^{≥a}(𝒪_X)` into `D^{≥a}(𝒪_S)`.
* `derivedCategoryBPlus_derivedPushforward_of_isGE`: the bounded below statement with the lower
  bound of `E` given explicitly.
* `derivedCategoryBPlus_derivedPushforward_of_isProperOver_supp`: the statement of
  [Stacks, Tag 0D0B], with [Stacks, Tag 02O5] as its only hypothesis, in the named form
  `AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase`. That
  hypothesis is a theorem, and it is supplied in
  `StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/BoundedBelowUnconditional.lean`, where
  the tag's label sits on
  `derivedCategoryBPlus_derivedPushforward_of_properSupp`.

## Implementation notes

This is the second of the two routes the source offers: deduce the statement from
[Stacks, Tag 08E2] by applying the exact functor `Rf_*` to the canonical truncation triangles
`τ_{≤a}E → E → τ_{≥a+1}E → τ_{≤a}E[1]`. At a fixed degree `n` the triangle is taken at `a = n`.
Its third vertex `Rf_*τ_{≥n+1}E` lies in degrees `≥ n + 1`, because `Rf_*` is left `t`-exact, so
the long exact homology sequence makes `H^n(Rf_*E) ≅ H^n(Rf_*τ_{≤n}E)`; and `τ_{≤n}E` is bounded,
with coherent cohomology sheaves whose supports are proper over `S`, so that group is coherent by
[Stacks, Tag 08E2]. Boundedness below of `Rf_*E` is again left `t`-exactness.

Left `t`-exactness is read off the bounded below derived functor: on an object of `D^+(𝒪_X)` the
unbounded derived direct image agrees with `Rf_*` computed on `D^+` by
`Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus`, and there it is
`CategoryTheory.Functor.isGE_rightDerivedFunctorPlus_obj`, i.e. [Stacks, Tag 05TC] part (1).

The dévissage of [Stacks, Tag 08E2] is entered at
`derivedCategoryBBounded_derivedPushforward_of_bounded` rather than at that tag's own statement,
so that the hypotheses only have to be supplied for the cohomology sheaves of `τ_{≤n}E`: in
degrees `≤ n` these are those of `E`, and in degrees `> n` they vanish, and for a zero module the
higher direct images are zero, hence coherent and eventually vanishing. No statement about the
support of the zero module is needed.

The hypothesis on the support is on **every** `H^i(E)`, not on `f`: `f` is only locally of finite
type, and no properness of `f` itself is assumed anywhere.

## References

* [Stacks Project, Tag 0D0B](https://stacks.math.columbia.edu/tag/0D0B)
* [Stacks Project, Tag 08E2](https://stacks.math.columbia.edu/tag/08E2)
* [Stacks Project, Tag 05TC](https://stacks.math.columbia.edu/tag/05TC)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe u

namespace Stacks.AlgebraicGeometry.ProperSupportCoherent

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section DerivedPushforward

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### Left `t`-exactness of the derived direct image -/

/-- **`Rf_*` moves cohomology to the right**: if `E` lies in degrees `≥ a`, so does `Rf_*E`.

On a bounded below object the unbounded derived direct image agrees with the derived direct image
computed on `D^+(𝒪_X)`, where this is [Stacks, Tag 05TC] part (1). -/
theorem isGE_derivedPushforward (E : DerivedCategory X.Modules) (a : ℤ) (hE : E.IsGE a) :
    ((derivedPushforwardModules f).obj E).IsGE a := by
  let E' : DerivedCategory.Plus X.Modules := ⟨E, ⟨a, hE⟩⟩
  have hE' : E'.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff E' a).mp hE
  obtain ⟨e⟩ := Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus
    (Scheme.Modules.pushforward f) (derivedPushforwardModules f)
    (derivedPushforwardModulesUnit f)
    (fun I hI => RingedSpace.isIso_derivedPushforwardUnit_app_of_isKInjective _ I hI) E' a hE
  have hRP : ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj E').IsGE a :=
    CategoryTheory.Functor.isGE_rightDerivedFunctorPlus_obj _ E' a
  have hR : DerivedCategory.TStructure.t.IsGE
      ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj E').obj a :=
    (DerivedCategory.Plus.isGE_ι_obj_iff _ a).mpr hRP
  exact DerivedCategory.TStructure.t.isGE_of_iso e.symm a

/-! ### The dévissage hypothesis after truncating from above -/

/-- **The higher direct images of a zero module vanish.** A zero module is injective, so its
higher direct images vanish outside degree zero, and in degree zero they are its direct image. -/
theorem isZero_rightDerivedPlus_of_isZero {M : X.Modules} (hM : IsZero M) (p : ℤ) :
    IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj M) := by
  have : Injective M := Injective.of_iso hM.isoZero.symm (Injective.zero_injective (C := X.Modules))
  rcases eq_or_ne p 0 with rfl | hp
  · exact IsZero.of_iso ((Scheme.Modules.pushforward f).map_isZero hM)
      (Stacks.AlgebraicGeometry.HigherDirectImage.higherDirectImageZeroIso f M)
  · exact CategoryTheory.Functor.isZero_rightDerivedPlus_obj_injective
      (Scheme.Modules.pushforward f) p hp M

/-- The higher direct images of a zero module are coherent and vanish in large degrees. -/
theorem HasCoherentBoundedDirectImages.of_isZero {M : X.Modules} (hM : IsZero M) :
    HasCoherentBoundedDirectImages f M :=
  ⟨fun p => Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero
    (R := S.ringCatSheaf) (isZero_rightDerivedPlus_of_isZero f hM p), 0,
    fun p _ => isZero_rightDerivedPlus_of_isZero f hM p⟩

/-- **The dévissage hypothesis of [Stacks, Tag 08E2] at the cohomology sheaves of `τ_{≤n}E`.** In
degrees `≤ n` these are the cohomology sheaves of `E`, where it is
`hasCoherentBoundedDirectImages_of_isProperOver_supp`; in degrees `> n` they vanish. -/
theorem hasCoherentBoundedDirectImages_homology_truncLE [IsNoetherian S] [LocallyOfFiniteType f]
    (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsCoherent)
    (hsupp : ∀ j : ℤ, IsProperOver f
      ⟨SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules j).obj E),
        @SheafOfModules.isClosed_supp _ _ _ (hcoh j).isFiniteType⟩)
    (haff : AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase.{u})
    (n j : ℤ) :
    HasCoherentBoundedDirectImages f ((DerivedCategory.homologyFunctor X.Modules j).obj
      ((DerivedCategory.TStructure.t.truncLE n).obj E)) := by
  by_cases hj : j ≤ n
  · have := AlgebraicGeometry.isIso_homology_truncLE E n j hj
    exact HasCoherentBoundedDirectImages.of_iso f
      (asIso ((DerivedCategory.homologyFunctor X.Modules j).map
        ((DerivedCategory.TStructure.t.truncLEι n).app E))).symm
      (hasCoherentBoundedDirectImages_of_isProperOver_supp f _ (hcoh j) (hsupp j) haff)
  · exact HasCoherentBoundedDirectImages.of_isZero f
      (DerivedCategory.isZero_of_isLE _ n j (by omega))

/-! ### Stacks 0D0B -/

/-- **[Stacks, Tag 0D0B] with the lower bound of `E` named, and with [Stacks, Tag 02O5] as its
only hypothesis.** For `S` Noetherian, `f` locally of finite type and `E` an object of `D(𝒪_X)`
lying in degrees `≥ b` whose cohomology sheaves are coherent with support proper over `S`, the
object `Rf_*E` of `D(𝒪_S)` is bounded below with coherent cohomology sheaves.

Fix a degree `n` and apply `Rf_*` to the truncation triangle at `n`. Its third vertex lies in
degrees `≥ n + 1` by `isGE_derivedPushforward`, so the long exact homology sequence identifies
`H^n(Rf_*E)` with `H^n(Rf_*τ_{≤n}E)`, and `τ_{≤n}E` is bounded, so the dévissage of
[Stacks, Tag 08E2] applies to it. Boundedness below is `isGE_derivedPushforward` at `b`. -/
theorem derivedCategoryBPlus_derivedPushforward_of_isGE [IsNoetherian S] [LocallyOfFiniteType f]
    (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsCoherent)
    (hsupp : ∀ j : ℤ, IsProperOver f
      ⟨SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules j).obj E),
        @SheafOfModules.isClosed_supp _ _ _ (hcoh j).isFiniteType⟩)
    (haff : AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase.{u})
    (b : ℤ) (hGE : E.IsGE b) :
    DerivedCategoryB.derivedCategoryBPlus (fun N : S.Modules => N.IsCoherent)
      ((derivedPushforwardModules f).obj E) := by
  have hb := isGE_derivedPushforward f E b hGE
  refine ⟨⟨b, fun n hn =>
    ((derivedPushforwardModules f).obj E).isZero_of_isGE b n hn⟩, fun n => ?_⟩
  have hLE' : ((DerivedCategory.TStructure.t.truncLE n).obj E).IsLE
      (b + (((n - b).toNat : ℕ) : ℤ)) :=
    DerivedCategory.TStructure.t.isLE_of_le _ n (b + (((n - b).toNat : ℕ) : ℤ)) (by omega)
  have h₁ := derivedCategoryBBounded_derivedPushforward_of_bounded f (n - b).toNat b
    ((DerivedCategory.TStructure.t.truncLE n).obj E)
    (fun j _ => hasCoherentBoundedDirectImages_homology_truncLE f E hcoh hsupp haff n j)
    inferInstance hLE'
  let T := (derivedPushforwardModules f).mapTriangle.obj
    ((DerivedCategory.TStructure.t.triangleLEGE n (n + 1) rfl).obj E)
  have hdist : T ∈ distTriang (DerivedCategory S.Modules) :=
    (derivedPushforwardModules f).map_distinguished _
      (DerivedCategory.TStructure.t.triangleLEGE_distinguished n (n + 1) rfl E)
  have h₃ : T.obj₃.IsGE (n + 1) := isGE_derivedPushforward f
    ((DerivedCategory.TStructure.t.truncGE (n + 1)).obj E) (n + 1) inferInstance
  have hz := T.obj₃.isZero_of_isGE (n + 1) n (by omega)
  have hz' := T.obj₃.isZero_of_isGE (n + 1) (n - 1) (by omega)
  have : Epi ((DerivedCategory.homologyFunctor S.Modules n).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor S.Modules 0).homologySequence_epi_shift_map_mor₁_iff
      T hdist n).2 (hz.eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor S.Modules n).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor S.Modules 0).homologySequence_mono_shift_map_mor₁_iff
      T hdist (n - 1) n (by omega)).2 (hz'.eq_of_src _ _)
  have hiso : IsIso ((DerivedCategory.homologyFunctor S.Modules n).map T.mor₁) :=
    isIso_of_mono_of_epi _
  have hc : ((DerivedCategory.homologyFunctor S.Modules n).obj T.obj₁).IsCoherent := h₁.2 n
  exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso (R := S.ringCatSheaf)
    (@asIso _ _ _ _ _ hiso).symm

/-- **The statement of [Stacks, Tag 0D0B], with [Stacks, Tag 02O5] as its only hypothesis.** Let
`S` be a Noetherian scheme, let `f : X ⟶ S` be a morphism of schemes which is locally of finite
type and let `E` be an object of `D^+_Coh(𝒪_X)` such that the support of `H^i(E)` is proper over
`S` for all `i`. Then `Rf_*E` is an object of `D^+_Coh(𝒪_S)`.

The hypothesis `haff` is
`AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase`, the named
`Prop` this library carries for [Stacks, Tag 02O5]: the affine-base case of that tag's first
assertion, equivalent to the assertion itself. It is the hypothesis that [Stacks, Tag 08E2]
carries here, and no more is used. It is supplied by
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase` in
`StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/BoundedBelowUnconditional.lean`, which is
where the tag's label sits. -/
theorem derivedCategoryBPlus_derivedPushforward_of_isProperOver_supp [IsNoetherian S]
    [LocallyOfFiniteType f] (E : DerivedCategory X.Modules)
    (hE : DerivedCategoryB.derivedCategoryBPlus (fun M : X.Modules => M.IsCoherent) E)
    (hsupp : ∀ j : ℤ, IsProperOver f
      ⟨SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules j).obj E),
        @SheafOfModules.isClosed_supp _ _ _ (hE.2 j).isFiniteType⟩)
    (haff : AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase.{u}) :
    DerivedCategoryB.derivedCategoryBPlus (fun N : S.Modules => N.IsCoherent)
      ((derivedPushforwardModules f).obj E) := by
  obtain ⟨N, hN⟩ := hE.1
  obtain ⟨b, hb⟩ := (DerivedCategory.plus_iff E).2 ⟨N - 1, fun n hn => hN n (by omega)⟩
  exact derivedCategoryBPlus_derivedPushforward_of_isGE f E (fun j => hE.2 j) hsupp haff b hb

end DerivedPushforward

end Stacks.AlgebraicGeometry.ProperSupportCoherent

end
