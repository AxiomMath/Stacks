module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Module
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.PullbackStalk
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.RingTheory.Flat.FlatAtPointCriteria

/-!
# Relative flatness passes to a generalization inside a fibre

Let `f : X → S` be a morphism of schemes, let `F` be a quasi-coherent `𝒪_X`-module and let
`x' ⤳ x` be points of `X` with the same image in `S`. Then flatness of `F` over `S` at `x`
implies flatness of `F` over `S` at `x'`: the stalk `F_{x'}` is a localization of `F_x` over
`𝒪_{X, x}` while the base ring `𝒪_{S, f(x)}` is unchanged.

This is the implication (1) ⟹ (2) of Stacks 05UA. The converse, and the theorem itself, are
in `StacksFrontier/AlgebraicGeometry/Flatness/FlatAtAssociatedPoints.lean`.

## Main results

* `AlgebraicGeometry.exists_isLocalizedModule_stalkSpecializes`: for a quasi-coherent
  `𝒪_X`-module `F` and `x' ⤳ x`, the stalk `F_{x'}`, viewed as an `𝒪_{X, x}`-module through
  the specialization map of local rings, is a localization of `F_x` at a multiplicative subset
  of `𝒪_{X, x}`.
* `AlgebraicGeometry.isFlatOverAt_of_specializes`: relative flatness at `x` implies relative
  flatness at a generalization `x'` of `x` lying in the same fibre.
* `Stacks.Divisors.isAssociatedPoint_pullback_fiberι_iff_of_eq`: the associated-point dictionary
  for a fibre inclusion at an *arbitrary* point of an arbitrary fibre — a point `x'` of the fibre
  of `f` over `y` is associated to the restriction of `F` to that fibre exactly when the maximal
  ideal of `𝒪_{X, z}` is an associated prime of `F_z ⧸ 𝔪_{S, f z} · F_z`, where `z` is the image
  of `x'` in `X`.
* `AlgebraicGeometry.forall_isAssociatedPoint_specializes_iff`: consequently condition (2) of
  Stacks 05UA is the purely ring-theoretic condition obtained by replacing each
  associated-point clause by that associated-prime clause.
* `AlgebraicGeometry.isFlatOverAt_of_isAssociatedPoint_asFiber`: condition (2) of Stacks 05UA
  implies condition (1) directly whenever `x` is itself an associated point of its own
  fibre, because `x` is one of the points `x'` that (2) quantifies over.
* `AlgebraicGeometry.isFlatOverAt_of_subsingleton_stalk`: condition (1) holds trivially
  when the stalk `F_x` vanishes.
* `Module.Flat.of_bijective_algebraMap`: flatness transfers along an isomorphism of base rings.

## Implementation notes

The module structure on the stalk of an `𝒪_X`-module over the stalk of the structure sheaf is
`AlgebraicGeometry.Scheme.Modules.moduleStalk`, which typeclass resolution does not find for
the spelling `F.presheaf.stalk x` used by the affine-localization API; it is therefore supplied
by hand, as it is throughout the associated-points files.

`exists_isLocalizedModule_stalkSpecializes` produces *some* localization map, not the
specialization map of the sheaf of modules itself: for the flatness application the identity of
the map is irrelevant, and the construction avoids having to know that the specialization map of
an `𝒪_X`-module is semilinear over the specialization map of local rings. The map is obtained on
an affine open `U` containing `x` (hence containing `x'`) as `IsLocalizedModule.liftOfLE` between
the two localizations `Γ(F, U) → F_x` and `Γ(F, U) → F_{x'}` of
`AlgebraicGeometry.affineGerm_isLocalized`, upgraded from `Γ(X, U)`-linear to `𝒪_{X, x}`-linear
by `LinearMap.extendScalarsOfIsLocalization` and then to a localization at a submonoid of
`𝒪_{X, x}` by `IsLocalizedModule.of_restrictScalars`.

Since `x'` and `x` have the same image in `S` only up to a propositional equality, the two base
stalks `𝒪_{S, f(x')}` and `𝒪_{S, f(x)}` are different rings, isomorphic through
`TopCat.Presheaf.stalkCongr`. Flatness is moved across that isomorphism by
`Module.Flat.of_bijective_algebraMap`, the identification of the two actions on `F_{x'}` being
the naturality `AlgebraicGeometry.Scheme.Hom.stalkSpecializes_stalkMap`.

`Stacks.Divisors.isAssociatedPoint_pullback_fiberι_iff_of_eq` moves the fibre dictionary
`Stacks.Divisors.isAssociatedPoint_pullback_fiberι_iff'`, which is stated at the point
`f.asFiber x` of the fibre over `f x`, to an arbitrary point `x'` of the fibre over an arbitrary
`y`. No transport is needed: `f.fiberι y x'` lies over `y`, so substituting `y := f z` for
`z` the image of `x'` turns `x'` into `f.asFiber z` by injectivity of the fibre inclusion. The
image point is kept as a hypothesis `f.fiberι y x' = z` rather than substituted, so that the
statement applies at whichever presentation of the image the caller has.

## References

* [Stacks Project, Tag 05UA](https://stacks.math.columbia.edu/tag/05UA)
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace

universe u

/-- Flatness over a base ring is inherited by a base ring isomorphic to it: if the structure
map `R → R'` is bijective and `M` carries compatible actions of both, then `M` is flat over `R'`
as soon as it is flat over `R`. A bijective algebra map is a localization at the trivial
submonoid. -/
theorem Module.Flat.of_bijective_algebraMap {R R' M : Type*} [CommRing R] [CommRing R']
    [Algebra R R'] [AddCommGroup M] [Module R M] [Module R' M] [IsScalarTower R R' M]
    (hb : Function.Bijective (algebraMap R R')) [Module.Flat R M] : Module.Flat R' M := by
  have : IsLocalization (⊥ : Submonoid R) R' :=
    IsLocalization.of_le_isUnit_of_bijective (by
      rw [Algebra.algebraMapSubmonoid, Submonoid.map_bot]
      exact bot_le) hb
  exact (Module.flat_iff_of_isLocalization R' (⊥ : Submonoid R) M).mpr ‹_›

namespace Stacks.Divisors

open AlgebraicGeometry

/-- **The fibre dictionary at an arbitrary point of an arbitrary fibre.** A point `x'` of the
scheme-theoretic fibre of `f : X ⟶ S` over `y` is associated to the restriction of an
`𝒪_X`-module `F` to that fibre exactly when the maximal ideal of `𝒪_{X, z}` is an associated
prime of `F_z ⧸ 𝔪_{S, f z} · F_z`, where `z` is the image of `x'` in `X`.

This is `isAssociatedPoint_pullback_fiberι_iff'` with the restriction to points of the form
`f.asFiber x` removed: the fibre inclusion lands in `f ⁻¹' {y}`, so `f z = y`, and substituting
that equality identifies `x'` with `f.asFiber z` by injectivity of the fibre inclusion. -/
theorem isAssociatedPoint_pullback_fiberι_iff_of_eq {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) {y : S} (x' : f.fiber y) {z : X} (hz : f.fiberι y x' = z) :
    IsAssociatedPoint ((Scheme.Modules.pullback (f.fiberι y)).obj F) x' ↔
      IsAssociatedPrimeStacks (X.presheaf.stalk z)
        ((TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf z) ⧸
          (Ideal.map (f.stalkMap z).hom (IsLocalRing.maximalIdeal (S.presheaf.stalk (f z))) •
            (⊤ : Submodule (X.presheaf.stalk z)
              (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf z))))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk z)) := by
  have hy : f z = y := by
    have hmem : f.fiberι y x' ∈ f.base ⁻¹' {y} := by
      rw [← Scheme.Hom.range_fiberι]
      exact Set.mem_range_self x'
    rw [← hz]
    simpa using hmem
  subst hy
  have hx' : x' = f.asFiber z :=
    (f.fiberι (f z)).isEmbedding.injective (hz.trans (f.fiberι_asFiber z).symm)
  subst hx'
  exact isAssociatedPoint_pullback_fiberι_iff' f F z hz

end Stacks.Divisors

namespace AlgebraicGeometry

/-- For a quasi-coherent `𝒪_X`-module `F` and a point `x'` generalizing `x`, the stalk
`F_{x'}` — regarded as an `𝒪_{X, x}`-module through the specialization map
`𝒪_{X, x} → 𝒪_{X, x'}` — is the localization of `F_x` at a multiplicative subset of
`𝒪_{X, x}`. -/
theorem exists_isLocalizedModule_stalkSpecializes {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] {x w : X} (h : w ⤳ x) :
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      Scheme.Modules.moduleStalk F x
    letI : Module (X.presheaf.stalk w) (F.presheaf.stalk w) :=
      Scheme.Modules.moduleStalk F w
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk w) :=
      Module.compHom _ (X.presheaf.stalkSpecializes h).hom
    ∃ (T : Submonoid (X.presheaf.stalk x))
      (g : F.presheaf.stalk x →ₗ[X.presheaf.stalk x] F.presheaf.stalk w),
      IsLocalizedModule T g := by
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) := Scheme.Modules.moduleStalk F x
  let : Module (X.presheaf.stalk w) (F.presheaf.stalk w) := Scheme.Modules.moduleStalk F w
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk w) :=
    Module.compHom _ (X.presheaf.stalkSpecializes h).hom
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hwU : w ∈ U := h.mem_open U.2 hxU
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let : Algebra Γ(X, U) (X.presheaf.stalk w) := X.presheaf.algebra_section_stalk ⟨w, hwU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := hU.isLocalization_stalk ⟨x, hxU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk w)
      (hU.primeIdealOf ⟨w, hwU⟩).asIdeal := hU.isLocalization_stalk ⟨w, hwU⟩
  let : Module Γ(X, U) (F.presheaf.stalk x) := affineStalkModule F U x hxU
  let : Module Γ(X, U) (F.presheaf.stalk w) := affineStalkModule F U w hwU
  have : IsLocalizedModule (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      (affineGerm F U x hxU) := affineGerm_isLocalized F U hU x hxU
  have : IsLocalizedModule (hU.primeIdealOf ⟨w, hwU⟩).asIdeal.primeCompl
      (affineGerm F U w hwU) := affineGerm_isLocalized F U hU w hwU
  have hqp : (hU.primeIdealOf ⟨w, hwU⟩).asIdeal ≤ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    (PrimeSpectrum.le_iff_specializes _ _).mpr (by
      change (Scheme.homeoOfIso hU.isoSpec) (⟨w, hwU⟩ : U) ⤳
        (Scheme.homeoOfIso hU.isoSpec) (⟨x, hxU⟩ : U)
      exact ((subtype_specializes_iff (⟨w, hwU⟩ : U) ⟨x, hxU⟩).mpr h).map
        (Scheme.homeoOfIso hU.isoSpec).continuous)
  have hpq : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl ≤
      (hU.primeIdealOf ⟨w, hwU⟩).asIdeal.primeCompl := fun a ha hqa => ha (hqp hqa)
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk x) (F.presheaf.stalk w) := by
    refine IsScalarTower.of_algebraMap_smul fun r m => ?_
    change (X.presheaf.stalkSpecializes h).hom ((X.presheaf.germ U x hxU).hom r) • m = _
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
    rfl
  set g₀ := IsLocalizedModule.liftOfLE
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      (hU.primeIdealOf ⟨w, hwU⟩).asIdeal.primeCompl hpq
      (affineGerm F U x hxU) (affineGerm F U w hwU)
  have : IsLocalizedModule (hU.primeIdealOf ⟨w, hwU⟩).asIdeal.primeCompl
      ((g₀.extendScalarsOfIsLocalization
        (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
        (X.presheaf.stalk x)).restrictScalars Γ(X, U)) :=
    inferInstanceAs (IsLocalizedModule _ g₀)
  exact ⟨Algebra.algebraMapSubmonoid (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨w, hwU⟩).asIdeal.primeCompl,
    g₀.extendScalarsOfIsLocalization
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (X.presheaf.stalk x),
    IsLocalizedModule.of_restrictScalars _ _⟩

/-- **Stacks 05UA, the implication (1) ⟹ (2).** If a quasi-coherent `𝒪_X`-module is flat over
`S` at `x`, then it is flat over `S` at every point `w` generalizing `x` with the same image in
`S`, because `F_w` is a localization of `F_x` over `𝒪_{X, x}` and the base stalk does not
change. -/
theorem isFlatOverAt_of_specializes {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    [F.IsQuasicoherent] {x w : X} (h : w ⤳ x) (hfx : f.base w = f.base x)
    (hflat : IsFlatOverAt f.toLRSHom.toShHom F x) :
    IsFlatOverAt f.toLRSHom.toShHom F w := by
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) := Scheme.Modules.moduleStalk F x
  let : Module (X.presheaf.stalk w) (F.presheaf.stalk w) := Scheme.Modules.moduleStalk F w
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk w) :=
    Module.compHom _ (X.presheaf.stalkSpecializes h).hom
  let : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Module (S.presheaf.stalk (f.base x)) (F.presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  let : Module (S.presheaf.stalk (f.base x)) (F.presheaf.stalk w) :=
    Module.compHom _ ((X.presheaf.stalkSpecializes h).hom.comp (f.stalkMap x).hom)
  let : Module (S.presheaf.stalk (f.base w)) (F.presheaf.stalk w) :=
    Module.compHom _ (f.stalkMap w).hom
  have : IsScalarTower (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x)
      (F.presheaf.stalk x) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x)
      (F.presheaf.stalk w) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat (S.presheaf.stalk (f.base x)) (F.presheaf.stalk x) := hflat
  obtain ⟨T, g, hg⟩ := exists_isLocalizedModule_stalkSpecializes F h
  have : Module.Flat (S.presheaf.stalk (f.base x)) (F.presheaf.stalk w) :=
    Module.Flat.of_isLocalizedModule_of_tower T g
  let : Algebra (S.presheaf.stalk (f.base x)) (S.presheaf.stalk (f.base w)) :=
    (S.presheaf.stalkSpecializes (f.base.hom.map_specializes h)).hom.toAlgebra
  have hnat := Scheme.Hom.stalkSpecializes_stalkMap f w x h
  have : IsScalarTower (S.presheaf.stalk (f.base x)) (S.presheaf.stalk (f.base w))
      (F.presheaf.stalk w) := by
    refine IsScalarTower.of_algebraMap_smul fun r m => ?_
    change (f.stalkMap w).hom
        ((S.presheaf.stalkSpecializes (f.base.hom.map_specializes h)).hom r) • m =
      (X.presheaf.stalkSpecializes h).hom ((f.stalkMap x).hom r) • m
    congr 1
    exact congrArg (fun φ : S.presheaf.stalk (f.base x) ⟶ X.presheaf.stalk w => φ.hom r) hnat
  have hbij : Function.Bijective
      (algebraMap (S.presheaf.stalk (f.base x)) (S.presheaf.stalk (f.base w))) := by
    have e : Inseparable (f.base x) (f.base w) := Inseparable.of_eq hfx.symm
    have h1 := (S.presheaf.stalkCongr e).hom_inv_id
    have h2 := (S.presheaf.stalkCongr e).inv_hom_id
    simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkCongr_inv] at h1 h2
    refine Function.bijective_iff_has_inverse.mpr
      ⟨(S.presheaf.stalkSpecializes e.le).hom, fun a => ?_, fun a => ?_⟩
    · exact congrArg (fun φ : S.presheaf.stalk (f.base x) ⟶ S.presheaf.stalk (f.base x) =>
        φ.hom a) h1
    · exact congrArg (fun φ : S.presheaf.stalk (f.base w) ⟶ S.presheaf.stalk (f.base w) =>
        φ.hom a) h2
  change Module.Flat (S.presheaf.stalk (f.base w)) (F.presheaf.stalk w)
  exact Module.Flat.of_bijective_algebraMap hbij

/-- A module with vanishing stalk at `x` is flat over the base at `x`: the zero module is free,
hence flat, over any ring. -/
theorem isFlatOverAt_of_subsingleton_stalk {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (x : X) (hF : Subsingleton (F.presheaf.stalk x)) :
    IsFlatOverAt f.toLRSHom.toShHom F x := by
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) := Scheme.Modules.moduleStalk F x
  let : Module (S.presheaf.stalk (f.base x)) (F.presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  change Module.Flat (S.presheaf.stalk (f.base x)) (F.presheaf.stalk x)
  have : Subsingleton (F.presheaf.stalk x) := hF
  have : Module.Free (S.presheaf.stalk (f.base x)) (F.presheaf.stalk x) :=
    Module.Free.of_subsingleton _ _
  infer_instance

/-- **The implication (2) ⟹ (1) of Stacks 05UA at a point associated to its own fibre.** The
point `x` itself belongs to the fibre of `f` over `f x`, as `f.asFiber x`, and specializes to
itself; so if it is an associated point of the restriction of `F` to that fibre, then condition
(2) of Stacks 05UA contains condition (1) as the instance `x' = f.asFiber x`.

Consequently the converse implication of Stacks 05UA carries content only at a point which is
*not* associated to its own fibre, equivalently (by
`Stacks.Divisors.isAssociatedPoint_pullback_fiberι_iff`) at a point whose maximal ideal is not
an associated prime of `F_x ⧸ 𝔪_{S, f x} · F_x`. -/
theorem isFlatOverAt_of_isAssociatedPoint_asFiber {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (x : X)
    (hx : Stacks.Divisors.IsAssociatedPoint
      ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) (f.asFiber x))
    (h : ∀ x' : f.fiber (f x),
        x' ∈ Stacks.Divisors.associatedPoints
            ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) →
          Specializes (f.fiberι (f x) x') x →
            IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι (f x) x')) :
    IsFlatOverAt f.toLRSHom.toShHom F x := by
  have hsp : Specializes (f.fiberι (f x) (f.asFiber x)) x := by
    rw [Scheme.Hom.fiberι_asFiber]
  exact Scheme.Hom.fiberι_asFiber f x ▸ h (f.asFiber x) hx hsp

/-- **Condition (2) of Stacks 05UA, read as commutative algebra.** Quantifying over the
associated points of the restriction of `F` to the fibre over `f x` is the same as quantifying
over the points `x'` of that fibre for which the maximal ideal of `𝒪_{X, z}` is an associated
prime of `F_z ⧸ 𝔪_{S, f z} · F_z`, where `z` is the image of `x'` in `X`.

This is the fibre dictionary `Stacks.Divisors.isAssociatedPoint_pullback_fiberι_iff_of_eq`
applied under the quantifier; it eliminates the associated points of a pullback of modules from
condition (2) in favour of associated primes of stalks. -/
theorem forall_isAssociatedPoint_specializes_iff {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (x : X) :
    (∀ x' : f.fiber (f x),
        x' ∈ Stacks.Divisors.associatedPoints
            ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) →
          Specializes (f.fiberι (f x) x') x →
            IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι (f x) x')) ↔
      ∀ x' : f.fiber (f x),
        IsAssociatedPrimeStacks (X.presheaf.stalk (f.fiberι (f x) x'))
            ((TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf (f.fiberι (f x) x')) ⧸
              (Ideal.map (f.stalkMap (f.fiberι (f x) x')).hom
                  (IsLocalRing.maximalIdeal
                    (S.presheaf.stalk (f (f.fiberι (f x) x')))) •
                (⊤ : Submodule (X.presheaf.stalk (f.fiberι (f x) x'))
                  (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf
                    (f.fiberι (f x) x')))))
            (IsLocalRing.maximalIdeal (X.presheaf.stalk (f.fiberι (f x) x'))) →
          Specializes (f.fiberι (f x) x') x →
            IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι (f x) x') :=
  forall_congr' fun x' =>
    imp_congr_left (Stacks.Divisors.isAssociatedPoint_pullback_fiberι_iff_of_eq f F x' rfl)

end AlgebraicGeometry

end

end
