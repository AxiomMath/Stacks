module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.NagataPushforward
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.FiberMaximalSpectrum
public import StacksFrontier.RingTheory.Depth.Localization
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Depth of the stalk of a finite direct image

Let `f : Y ⟶ X` be a finite morphism onto a locally Noetherian scheme. The stalk of `f_* 𝒪_Y` at
a point `x` of `X` is a finite algebra over the local ring `𝒪_{X,x}` whose maximal ideals are the
points of the fibre of `f` over `x`, and its localization at such a maximal ideal is the local
ring of `Y` there. Consequently the depth of that stalk over `𝒪_{X,x}` is the infimum of the
depths of the local rings `𝒪_{Y,y}` for `y` above `x`. This is the scheme-level form of
[Stacks, Tag 0AUK], and it is the step in the proof of [Stacks, Tag 0AWA] that passes from a
depth bound upstairs to one for the direct image.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.stalkPushforwardOfEq`: the canonical map
  `(f_* 𝒪_Y)_x ⟶ 𝒪_{Y,y}` at a point `y` presented together with a proof that `f y = x`.
* `AlgebraicGeometry.Scheme.Hom.pushforwardUnitModule`: the `𝒪_X`-module `f_* 𝒪_Y`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isLocalization_stalk_of_fiber`: for an affine morphism, the local
  ring of `Y` at a point of the fibre over `x` is the localization of `(f_* 𝒪_Y)_x` at the prime
  that point cuts out.
* `AlgebraicGeometry.Scheme.Hom.moduleFinite_pushforwardStalk`: for a finite morphism the stalk
  `(f_* 𝒪_Y)_x` is a finite `𝒪_{X,x}`-module.
* `AlgebraicGeometry.Scheme.Hom.depth_pushforwardStalk_eq_iInf`: **[Stacks, Tag 0AUK] at the
  stalk of a finite direct image** — the depth of `(f_* 𝒪_Y)_x` over `𝒪_{X,x}` is the infimum of
  the depths of the `𝒪_{Y,y}` for `y` above `x`.
* `AlgebraicGeometry.Scheme.Hom.depth_stalk_pushforwardUnitModule_eq`: the stalk of the *module*
  `f_* 𝒪_Y` has the same depth as the stalk of the *ring* `f_* 𝒪_Y`.
* `AlgebraicGeometry.Scheme.Hom.hasDepthTwoOutside_pushforwardUnitModule` and
  `AlgebraicGeometry.Scheme.Hom.hasDepthTwoOutside_pushforwardUnitModule_of_isNormal`: the
  resulting depth-two hypothesis of
  `AlgebraicGeometry.isCoherent_pushforward_of_mono_of_depth_ge_two`, the second one reading the
  depth bound upstairs off normality and a dimension bound, which is the last paragraph of the
  proof of [Stacks, Tag 0AWA].

## Implementation notes

No Stacks tag is placed here. The ring-theoretic content is
`Module.depth_eq_iInf_depth_isLocalized_maximal`, which already carries the bare tag 0AUK at its
own site, and the depth bound from normality is
`AlgebraicGeometry.two_le_depth_stalk_of_isNormal_of_two_le_ringKrullDim`, which rests on the
tagged Serre criterion; what is added here is the geometric plumbing between them.

The localization comparison is read off a single affine open `V ∋ x`: the stalk `(f_* 𝒪_Y)_x` is
the localization of `Γ(Y, f⁻¹V)` away from the prime of `x`
(`AlgebraicGeometry.Scheme.Hom.isLocalization_pushforwardStalk`) and `𝒪_{Y,y}` is its
localization at the prime of `y` (`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`), the
second submonoid containing the first because `y` lies over `x`; the two are compared by
`IsLocalization.isLocalization_of_submonoid_le` and `IsLocalization.of_le`. The prime of
`(f_* 𝒪_Y)_x` cut out by `y` is identified with the contraction of the maximal ideal of
`𝒪_{Y,y}` through `AlgebraicGeometry.Scheme.Hom.ker_fiberResidue`, which is what makes both
comparisons membership statements about germs.

The stalk of `f_* 𝒪_Y` as an `𝒪_X`-module is *not* definitionally the stalk of `f_* 𝒪_Y` as a
ring: the former is a colimit in `Ab` and the latter one in `CommRingCat`. They are not compared
categorically here; instead both are exhibited as localizations at `x` of the same module
`Γ(Y, f⁻¹V)` — the sections of the module `f_* 𝒪_Y` over `V` *are* `Γ(Y, f⁻¹V)`, with the same
`Γ(X, V)`-action, by `rfl` — and `IsLocalizedModule.linearEquiv` then supplies a linear
equivalence, which is all the depth needs. Instance search does not cross between the two
spellings of that action, so the localization hypothesis is passed positionally.

## References

* [Stacks Project, Tag 0AUK](https://stacks.math.columbia.edu/tag/0AUK)
* [Stacks Project, Tag 0AWA](https://stacks.math.columbia.edu/tag/0AWA)
* [Stacks Project, Tag 0345](https://stacks.math.columbia.edu/tag/0345)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry

/-- A section over an affine open lies in the prime of a point exactly when its germ there lies in
the maximal ideal of the local ring. -/
private lemma IsAffineOpen.mem_primeIdealOf_iff_germ_mem_maximalIdeal {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (x : U) (t : Γ(X, U)) :
    t ∈ (hU.primeIdealOf x).asIdeal ↔
      X.presheaf.germ U x x.2 t ∈ maximalIdeal (X.presheaf.stalk x) := by
  rw [← hU.comap_maximalIdeal_germ x]
  exact Iff.rfl

namespace Scheme.Hom

variable {X Y : Scheme.{u}}

/-- The canonical map `(f_* 𝒪_Y)_x ⟶ 𝒪_{Y,y}` at a point `y` of the fibre of `f` over `x`. -/
def stalkPushforwardOfEq (f : Y ⟶ X) {x : X} (y : Y) (hy : f y = x) :
    f.pushforwardStalk x ⟶ Y.presheaf.stalk y :=
  hy ▸ f.stalkPushforward y

/-- For the proof `rfl : f y = f y`, the map `f.stalkPushforwardOfEq y rfl` is
`f.stalkPushforward y`. -/
@[simp]
lemma stalkPushforwardOfEq_rfl (f : Y ⟶ X) (y : Y) :
    f.stalkPushforwardOfEq y rfl = f.stalkPushforward y := rfl

/-- The kernel of the map from the stalk of `f_* 𝒪_Y` at `x` to the residue field of a point `y`
of the fibre over `x` is a prime ideal. -/
instance isPrime_ker_fiberResidueOfEq (f : Y ⟶ X) {x : X} (y : Y) (hy : f y = x) :
    (RingHom.ker (f.fiberResidueOfEq y hy).hom).IsPrime := by
  subst hy
  rw [fiberResidueOfEq_rfl]
  infer_instance

/-- The kernel of the map from the stalk of `f_* 𝒪_Y` at `x` to the residue field of a point `y`
of the fibre over `x` is the preimage of the maximal ideal of `𝒪_{Y,y}` under
`f.stalkPushforwardOfEq y hy`. -/
lemma ker_fiberResidueOfEq (f : Y ⟶ X) {x : X} (y : Y) (hy : f y = x) :
    RingHom.ker (f.fiberResidueOfEq y hy).hom =
      (maximalIdeal (Y.presheaf.stalk y)).comap (f.stalkPushforwardOfEq y hy).hom := by
  subst hy
  rw [fiberResidueOfEq_rfl, stalkPushforwardOfEq_rfl, ker_fiberResidue]

/-- Along `f`, the image of the complement of the prime of `f y` in `Γ(X, V)` avoids the prime of
`y` in `Γ(Y, f⁻¹V)`. -/
private lemma map_primeCompl_primeIdealOf_le (f : Y ⟶ X) {V : X.Opens} (hV : IsAffineOpen V)
    (hU : IsAffineOpen (f ⁻¹ᵁ V)) (y : Y) (hy : f y ∈ V) :
    (hV.primeIdealOf ⟨f y, hy⟩).asIdeal.primeCompl.map (f.app V).hom ≤
      (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl := by
  rintro - ⟨s, hs, rfl⟩
  refine fun hmem ↦ hs ((hV.mem_primeIdealOf_iff_germ_mem_maximalIdeal ⟨f y, hy⟩ s).mpr ?_)
  replace hmem := (hU.mem_primeIdealOf_iff_germ_mem_maximalIdeal ⟨y, hy⟩ _).mp hmem
  have hsq : (f.stalkMap y).hom ((X.presheaf.germ V (f y) hy) s) =
      (Y.presheaf.germ (f ⁻¹ᵁ V) y hy) ((f.app V).hom s) :=
    congrArg (fun g : Γ(X, V) ⟶ Y.presheaf.stalk y => (ConcreteCategory.hom g) s)
      (f.germ_stalkMap V y hy)
  rw [← IsLocalRing.maximalIdeal_comap (f.stalkMap y).hom]
  exact Ideal.mem_comap.mpr (hsq ▸ hmem)

/-- The stalk of `𝒪_Y` at a point of the fibre of an affine morphism is the localization of the
stalk of `f_* 𝒪_Y` at the prime that point cuts out. -/
theorem isLocalization_stalk_of_fiber (f : Y ⟶ X) [IsAffineHom f] {x : X} (y : Y)
    (hy : f y = x) :
    letI : Algebra (f.pushforwardStalk x) (Y.presheaf.stalk y) :=
      (f.stalkPushforwardOfEq y hy).hom.toAlgebra
    IsLocalization (RingHom.ker (f.fiberResidueOfEq y hy).hom).primeCompl
      (Y.presheaf.stalk y) := by
  subst hy
  let _ : Algebra (f.pushforwardStalk (f y)) (Y.presheaf.stalk y) :=
    (f.stalkPushforward y).hom.toAlgebra
  have halg : ∀ s : f.pushforwardStalk (f y),
      algebraMap (f.pushforwardStalk (f y)) (Y.presheaf.stalk y) s =
        f.stalkPushforward y s := fun _ ↦ rfl
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := f y) (U := ⊤) trivial
  have hU : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  have hyU : y ∈ f ⁻¹ᵁ V := hxV
  let _ : Algebra Γ(Y, f ⁻¹ᵁ V) (f.pushforwardStalk (f y)) :=
    (f.pushforwardGerm V (f y) hxV).hom.toAlgebra
  let _ : Algebra Γ(Y, f ⁻¹ᵁ V) (Y.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, hyU⟩ : f ⁻¹ᵁ V)
  have hgerm : ∀ t : Γ(Y, f ⁻¹ᵁ V),
      algebraMap Γ(Y, f ⁻¹ᵁ V) (Y.presheaf.stalk y) t =
        Y.presheaf.germ (f ⁻¹ᵁ V) y hyU t := fun t ↦ by
    rw [TopCat.Presheaf.stalk_open_algebraMap Y.presheaf (⟨y, hyU⟩ : f ⁻¹ᵁ V)]
  have _ : IsScalarTower Γ(Y, f ⁻¹ᵁ V) (f.pushforwardStalk (f y)) (Y.presheaf.stalk y) := by
    refine IsScalarTower.of_algebraMap_eq fun t ↦ ?_
    rw [hgerm, halg]
    exact (congrArg (fun g : Γ(Y, f ⁻¹ᵁ V) ⟶ Y.presheaf.stalk y => (ConcreteCategory.hom g) t)
      (TopCat.Presheaf.stalkPushforward_germ CommRingCat f.base Y.presheaf V y hxV)).symm
  have _ : IsLocalization
      ((hV.primeIdealOf ⟨f y, hxV⟩).asIdeal.primeCompl.map (f.app V).hom)
      (f.pushforwardStalk (f y)) := f.isLocalization_pushforwardStalk hV hxV
  have hqloc : IsLocalization (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl
      (Y.presheaf.stalk y) := hU.isLocalization_stalk ⟨y, hyU⟩
  have hstep : IsLocalization ((hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl.map
      (algebraMap Γ(Y, f ⁻¹ᵁ V) (f.pushforwardStalk (f y)))) (Y.presheaf.stalk y) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ _ _
      (f.map_primeCompl_primeIdealOf_le hV hU y hxV)
  have hker : ∀ a : f.pushforwardStalk (f y),
      a ∈ RingHom.ker (f.fiberResidueOfEq y rfl).hom ↔
        f.stalkPushforward y a ∈ maximalIdeal (Y.presheaf.stalk y) := by
    intro a
    rw [f.ker_fiberResidueOfEq y rfl, stalkPushforwardOfEq_rfl]
    exact Iff.rfl
  refine @IsLocalization.of_le _ _ _ _ _ _ hstep _ ?_ ?_
  · rintro - ⟨t, ht, rfl⟩
    refine fun hmem ↦ ht ((hU.mem_primeIdealOf_iff_germ_mem_maximalIdeal ⟨y, hyU⟩ t).mpr ?_)
    have h := (hker _).mp hmem
    rwa [← halg, ← IsScalarTower.algebraMap_apply, hgerm] at h
  · intro s hs
    rw [halg]
    exact notMem_maximalIdeal.mp fun hmem ↦ hs ((hker s).mpr hmem)

/-- The stalk of `f_* 𝒪_Y` at `x` is a finite module over the local ring of `X` at `x`, for `f`
a finite morphism onto a locally Noetherian scheme. -/
theorem moduleFinite_pushforwardStalk [IsLocallyNoetherian X] (f : Y ⟶ X) [IsFinite f] (x : X) :
    Module.Finite (X.presheaf.stalk x) (f.pushforwardStalk x) := by
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  let _ : Algebra Γ(X, V) Γ(Y, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  have _ : Module.Finite Γ(X, V) Γ(Y, f ⁻¹ᵁ V) := f.finite_app V hV
  let _ : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxV⟩ : V)
  let _ : Algebra Γ(Y, f ⁻¹ᵁ V) (f.pushforwardStalk x) :=
    (f.pushforwardGerm V x hxV).hom.toAlgebra
  let _ : Algebra Γ(X, V) (f.pushforwardStalk x) :=
    (f.app V ≫ f.pushforwardGerm V x hxV).hom.toAlgebra
  have _ : IsScalarTower Γ(X, V) Γ(Y, f ⁻¹ᵁ V) (f.pushforwardStalk x) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have _ : IsScalarTower Γ(X, V) (X.presheaf.stalk x) (f.pushforwardStalk x) := by
    refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
    change (f.app V ≫ f.pushforwardGerm V x hxV).hom r =
      (f.pushforwardStalkMap x).hom ((X.presheaf.germ V x hxV).hom r)
    exact (ConcreteCategory.congr_hom (TopCat.Presheaf.stalkFunctor_map_germ V x hxV f.c) r).symm
  have _ : IsLocalization (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl (X.presheaf.stalk x) :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  have _ : IsLocalization (Algebra.algebraMapSubmonoid Γ(Y, f ⁻¹ᵁ V)
      (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl) (f.pushforwardStalk x) :=
    f.isLocalization_pushforwardStalk hV hxV
  exact Module.Finite.of_isLocalizedModule (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
    (IsScalarTower.toAlgHom Γ(X, V) Γ(Y, f ⁻¹ᵁ V) (f.pushforwardStalk x)).toLinearMap

/-- Localizing at a prime does not depend on the presentation of that prime. -/
private theorem isLocalization_primeCompl_of_eq {R : Type u} [CommRing R] {p q : Ideal R}
    [p.IsPrime] [q.IsPrime] (h : p = q) (S : Type u) [CommRing S] [Algebra R S]
    [IsLocalization p.primeCompl S] : IsLocalization q.primeCompl S := by
  subst h
  assumption

/-- **[Stacks, Tag 0AUK] for the stalk of a finite direct image.** For `f : Y ⟶ X` finite with
`X` locally Noetherian, the depth of the stalk of `f_* 𝒪_Y` at `x`, as a module over the local
ring of `X` at `x`, is the infimum of the depths of the local rings of `Y` at the points above
`x`. -/
theorem depth_pushforwardStalk_eq_iInf [IsLocallyNoetherian X] (f : Y ⟶ X) [IsFinite f] (x : X) :
    Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
        (f.pushforwardStalk x) =
      ⨅ y : {y : Y // f y = x},
        Module.depth (Y.presheaf.stalk y.1) (maximalIdeal (Y.presheaf.stalk y.1))
          (Y.presheaf.stalk y.1) := by
  have _ : Module.Finite (X.presheaf.stalk x) (f.pushforwardStalk x) :=
    f.moduleFinite_pushforwardStalk x
  let e := f.fiberEquivMaximalSpectrum x
  let Sm : MaximalSpectrum (f.pushforwardStalk x) → Type u :=
    fun P ↦ Y.presheaf.stalk (e.symm P).1
  let _ : ∀ P, Algebra (f.pushforwardStalk x) (Sm P) := fun P ↦
    (f.stalkPushforwardOfEq (e.symm P).1 (e.symm P).2).hom.toAlgebra
  have hP : ∀ P : MaximalSpectrum (f.pushforwardStalk x),
      RingHom.ker (f.fiberResidueOfEq (e.symm P).1 (e.symm P).2).hom = P.asIdeal :=
    fun P ↦ congrArg MaximalSpectrum.asIdeal (e.apply_symm_apply P)
  have _ : ∀ P, IsLocalization.AtPrime (Sm P) P.asIdeal := fun P ↦
    have := f.isLocalization_stalk_of_fiber (e.symm P).1 (e.symm P).2
    isLocalization_primeCompl_of_eq (hP P) (Sm P)
  exact (Module.depth_eq_iInf_depth_isLocalized_maximal
    (R := X.presheaf.stalk x) (S := f.pushforwardStalk x) (N := f.pushforwardStalk x)
    Sm Sm (fun P ↦ Algebra.linearMap (f.pushforwardStalk x) (Sm P))).trans
    (Equiv.iInf_congr e.symm fun _ ↦ rfl)

/-- For `f : Y ⟶ X` finite with `X` locally Noetherian, if the local rings of `Y` at the points
above `x` all have depth at least two, then so does the stalk of `f_* 𝒪_Y` at `x` over the local
ring of `X` at `x`. -/
theorem two_le_depth_pushforwardStalk [IsLocallyNoetherian X] (f : Y ⟶ X) [IsFinite f] (x : X)
    (h : ∀ y : Y, f y = x → (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y)
      (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)) :
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
      (f.pushforwardStalk x) := by
  rw [f.depth_pushforwardStalk_eq_iInf x]
  exact le_iInf fun y ↦ h y.1 y.2

/-! ### The direct image of the structure sheaf as a module -/

/-- The `𝒪_X`-module underlying `f_* 𝒪_Y`, that is, the direct image of the unit module. -/
abbrev pushforwardUnitModule (f : Y ⟶ X) : X.Modules :=
  (Scheme.Modules.pushforward f).obj (SheafOfModules.unit.{u} Y.ringCatSheaf)

/-- For an affine morphism `f`, the `𝒪_X`-module `f_* 𝒪_Y` is quasi-coherent. -/
instance isQuasicoherent_pushforwardUnitModule (f : Y ⟶ X) [IsAffineHom f] :
    (f.pushforwardUnitModule).IsQuasicoherent :=
  haveI := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit Y
  Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom f _

/-- **The stalk of the module `f_* 𝒪_Y` is the stalk of `f_* 𝒪_Y` as a ring.** For an affine
morphism `f`, the two have the same depth over the local ring of `X` at `x`. -/
theorem depth_stalk_pushforwardUnitModule_eq (f : Y ⟶ X) [IsAffineHom f] (x : X) :
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) (f.pushforwardUnitModule).val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (f.pushforwardUnitModule).val x
    Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) (f.pushforwardUnitModule).val.presheaf x) =
      Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
        (f.pushforwardStalk x) := by
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  let _ : Algebra Γ(X, V) Γ(Y, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  let _ : Algebra Γ(Y, f ⁻¹ᵁ V) (f.pushforwardStalk x) :=
    (f.pushforwardGerm V x hxV).hom.toAlgebra
  let _ : Algebra Γ(X, V) (f.pushforwardStalk x) :=
    (f.app V ≫ f.pushforwardGerm V x hxV).hom.toAlgebra
  have _ : IsScalarTower Γ(X, V) Γ(Y, f ⁻¹ᵁ V) (f.pushforwardStalk x) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let _ : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxV⟩ : V)
  have _ : IsScalarTower Γ(X, V) (X.presheaf.stalk x) (f.pushforwardStalk x) := by
    refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
    change (f.app V ≫ f.pushforwardGerm V x hxV).hom r =
      (f.pushforwardStalkMap x).hom ((X.presheaf.germ V x hxV).hom r)
    exact (ConcreteCategory.congr_hom (TopCat.Presheaf.stalkFunctor_map_germ V x hxV f.c) r).symm
  have _ : IsLocalization (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl (X.presheaf.stalk x) :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  let _ : Module (X.presheaf.stalk x) ((f.pushforwardUnitModule).presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (f.pushforwardUnitModule).val x
  let _ := affineStalkModule (f.pushforwardUnitModule) V x hxV
  have _ : IsScalarTower Γ(X, V) (X.presheaf.stalk x)
      ((f.pushforwardUnitModule).presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have h₁ : IsLocalizedModule (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
      (affineGerm (f.pushforwardUnitModule) V x hxV) :=
    affineGerm_isLocalized (f.pushforwardUnitModule) V hV x hxV
  have h₂ : IsLocalizedModule (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
      (IsScalarTower.toAlgHom Γ(X, V) Γ(Y, f ⁻¹ᵁ V) (f.pushforwardStalk x)).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr (f.isLocalization_pushforwardStalk hV hxV)
  have e := @IsLocalizedModule.linearEquiv _ _ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
    _ _ _ _ _ _ _ _ _ (affineGerm (f.pushforwardUnitModule) V x hxV)
    (IsScalarTower.toAlgHom Γ(X, V) Γ(Y, f ⁻¹ᵁ V) (f.pushforwardStalk x)).toLinearMap h₁ h₂
  exact Module.depth_eq_depth_of_linearEquiv _
    (e.extendScalarsOfIsLocalization (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
      (X.presheaf.stalk x))

/-- **The scheme-level form of [Stacks, Tag 0AUK] needed by [Stacks, Tag 0AWA].** Let
`f : Y ⟶ X` be a finite morphism onto a locally Noetherian scheme and `V` an open subscheme of
`X`. If the local rings of `Y` above the complement of `V` all have depth at least two, then so
do the stalks of the `𝒪_X`-module `f_* 𝒪_Y` there. -/
theorem hasDepthTwoOutside_pushforwardUnitModule [IsLocallyNoetherian X] (f : Y ⟶ X) [IsFinite f]
    (V : X.Opens)
    (h : ∀ y : Y, f y ∉ (V : Set X) → (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y)
      (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)) :
    HasDepthTwoOutside X (f.pushforwardUnitModule) V := by
  intro z hz
  rw [f.depth_stalk_pushforwardUnitModule_eq z]
  exact f.two_le_depth_pushforwardStalk z fun y hy ↦ h y (hy ▸ hz)

/-- **The last paragraph of the proof of [Stacks, Tag 0AWA].** Let `f : Y ⟶ X` be finite with
`X` locally Noetherian and `Y` normal, and let `V` be an open subscheme of `X`. If every point of
`Y` lying over the complement of `V` has local ring of dimension at least two, then the stalks of
`f_* 𝒪_Y` along that complement have depth at least two. -/
theorem hasDepthTwoOutside_pushforwardUnitModule_of_isNormal [IsLocallyNoetherian X] (f : Y ⟶ X)
    [IsFinite f] (hY : IsNormal Y) (V : X.Opens)
    (hdim : ∀ y : Y, f y ∉ (V : Set X) →
      (2 : WithBot ℕ∞) ≤ ringKrullDim (Y.presheaf.stalk y)) :
    HasDepthTwoOutside X (f.pushforwardUnitModule) V := by
  have _ : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  exact f.hasDepthTwoOutside_pushforwardUnitModule V fun y hy ↦
    two_le_depth_stalk_of_isNormal_of_two_le_ringKrullDim Y hY y (hdim y hy)

end Scheme.Hom

end AlgebraicGeometry

end
