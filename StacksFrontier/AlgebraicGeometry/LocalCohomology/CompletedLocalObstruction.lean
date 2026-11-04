module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.FiniteTilde
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Affine
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Sections
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.DenseOpenGenericPoint
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PuncturedSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A completed local ring obstruction to coherence, over the punctured spectrum

Let `R` be a Noetherian local ring with an associated prime `𝔭` in the Stacks sense such that
`dim(R ⧸ 𝔭) = 1`, and let `V` be the punctured spectrum of `R`. Then the direct image of the
structure sheaf of `V` along the open immersion `V ⟶ Spec R` is *not* coherent: its global
sections contain `Frac(R ⧸ 𝔭)`, which is not a finite `R`-module.

This is the local case of [Stacks, Tag 0AWC]. For `R` a *complete* Noetherian local ring it is
exactly the case `X = Spec R`, `U = V`, `z` the closed point of that tag, since there
`𝒪^∧_{X,z} = R`. The tag itself is deduced from it below.

## Main results

* `Stacks.LocalCohomology.ι_appTop_topIso_hom`: for an open `V` of a scheme `X`, the global
  sections map of `V ⟶ X` followed by `AlgebraicGeometry.Scheme.Opens.topIso` is restriction
  `Γ(X, ⊤) ⟶ Γ(X, V)`.
* `Stacks.LocalCohomology.smul_sections_pushforward_structureSheaf`: scalars act on the sections
  of `f_*𝒪_X` over an open `U` of `Spec R` through `f.app U`.
* `Stacks.LocalCohomology.sectionsTopPushforwardOpensLinearEquiv`: hence
  `Γ((V ⟶ Spec R)_*𝒪_V, ⊤) ≅ Γ(Spec R, V)` as `R`-modules.
* `Stacks.LocalCohomology.module_finite_sections_of_isCoherent`: if `(V ⟶ Spec R)_*𝒪_V` is
  coherent, then `Γ(Spec R, V)` is a finite `R`-module.
* `Stacks.LocalCohomology.not_isCoherent_pushforward_structureSheaf_puncturedSpectrum`: the
  obstruction itself.
* `Stacks.LocalCohomology.module_finite_sections_affineOpen` and
  `Stacks.LocalCohomology.module_finite_sections_pushforward_affineOpen`: step (1) of the
  reduction below — the sections of a coherent module over an affine open are a finite module, so
  `X` may be replaced by an affine open around `z`.
* `Stacks.LocalCohomology.not_isCoherent_pushforward_structureSheaf_of_baseChange`: the whole of
  [Stacks, Tag 0AWC] granted the two degree-zero flat base changes of [Stacks, Tag 02KH].
* `Stacks.LocalCohomology.module_finite_sections_fromSpec_preimage_opensRange` and
  `Stacks.LocalCohomology.module_finite_sections_preimage_fromSpecStalk`: the first of those two
  base changes — the one along `Spec 𝒪_{X,z} ⟶ W` for an affine open `W ∋ z`.
* `Stacks.LocalCohomology.module_finite_sections_of_fromSpec_preimage_opensRange`: the converse
  of the previous statement.
* `Stacks.LocalCohomology.module_finite_sections_puncturedSpectrum_of_flat`: the second — the one
  along the completion map.
* `Stacks.LocalCohomology.not_isCoherent_pushforward_structureSheaf`: **[Stacks, Tag 0AWC]**, the
  `completed_local_ring_obstruction` clause.

## The reduction of [Stacks, Tag 0AWC]

The tag is stated for an open immersion `j : U ⟶ X` of integral locally Noetherian schemes and a
point `z ∈ X ∖ U` whose completed local ring `𝒪^∧_{X,z}` has an associated prime with
one-dimensional quotient. It reduces to the punctured-spectrum case in three steps
("localize, shrink to the punctured spectrum, complete"):

1. replace `X` by an affine open neighbourhood `W = Spec A` of `z`: if `j_*𝒪_U` is coherent, then
   `Γ(j_*𝒪_U, W)` is a finite `Γ(X, W)`-module (`module_finite_sections_pushforward_affineOpen`);
2. base change along the flat `Spec 𝒪_{X,z} ⟶ Spec A`
   (`module_finite_sections_preimage_fromSpecStalk`) and along the flat
   `Spec 𝒪^∧_{X,z} ⟶ Spec 𝒪_{X,z}` (`module_finite_sections_puncturedSpectrum_of_flat`), both the
   degree-zero flat base change of [Stacks, Tag 02KH];
3. enlarge the preimage of `U` in `Spec 𝒪_{X,z}`, which is nonempty because `U` is dense in the
   integral `X`, to the punctured spectrum of the Noetherian domain `𝒪_{X,z}`
   (`Stacks.LocalCohomology.module_finite_sections_puncturedSpectrum_of_preimage`).

`not_isCoherent_pushforward_structureSheaf_of_baseChange` is (1) + (3) + the obstruction with the
two base-change conclusions of (2) as hypotheses; `not_isCoherent_pushforward_structureSheaf`
discharges them. [Stacks, Tag 0AWC] is a remark with two paragraphs; only the second, the
`completed_local_ring_obstruction` clause, is proved here.

## References

* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 05AZ](https://stacks.math.columbia.edu/tag/05AZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.LocalCohomology

/-- **Global sections along an open immersion are restriction.** For an open `V` of a scheme `X`,
the map on global sections induced by `V ⟶ X`, followed by the identification of `Γ(V, ⊤)` with
`Γ(X, V)`, is the restriction map `Γ(X, ⊤) ⟶ Γ(X, V)`. -/
theorem ι_appTop_topIso_hom {X : Scheme.{u}} (V : X.Opens) :
    V.ι.appTop ≫ V.topIso.hom = X.presheaf.map V.leTop.op :=
  (X.presheaf.map_comp _ _).symm

/-- Restricting from `⊤` to `⊤` and then to `V` is restricting to `V`. -/
theorem map_leTop_top_map_leTop {X : Scheme.{u}} (V : X.Opens) :
    X.presheaf.map (⊤ : X.Opens).leTop.op ≫ X.presheaf.map V.leTop.op =
      X.presheaf.map V.leTop.op :=
  (X.presheaf.map_comp _ _).symm

/-- **Scalars act on the sections of `f_*𝒪_X` through `f`.** For a morphism `f : X ⟶ Spec R` and
an open `U` of `Spec R`, the sections of the direct image of the structure sheaf of `X` over `U`
are, by definition (`AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj`), the sections of
`𝒪_X` over `f ⁻¹ᵁ U`, and `r` acts there as multiplication by the image of
`algebraMap R Γ(Spec R, U) r` under `f.app U`. -/
theorem smul_sections_pushforward_structureSheaf {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) (U : (Spec R).Opens) (r : R)
    (x : Γ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit.{u} X.ringCatSheaf), U)) :
    (r • x : Γ((Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit.{u} X.ringCatSheaf), U)) =
      @Mul.mul (ToType Γ(X, f ⁻¹ᵁ U)) _
        (f.app U ((Spec R).presheaf.map U.leTop.op ((Scheme.ΓSpecIso R).inv r))) x := rfl

/-- **`Γ(j_*𝒪_V, ⊤) ≅ Γ(Spec R, V)` as `R`-modules**, for `j : V ⟶ Spec R` the immersion of an
open, given on carriers by `AlgebraicGeometry.Scheme.Opens.topIso`. -/
def sectionsTopPushforwardOpensLinearEquiv (R : CommRingCat.{u}) (V : (Spec R).Opens) :
    Γ((Scheme.Modules.pushforward V.ι).obj
        (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf), (⊤ : (Spec R).Opens)) ≃ₗ[R]
      Γ(Spec R, V) :=
  have hkey : ∀ r : R, V.topIso.hom
      (V.ι.appTop ((Spec R).presheaf.map (⊤ : (Spec R).Opens).leTop.op
        ((Scheme.ΓSpecIso R).inv r))) = algebraMap R Γ(Spec R, V) r := fun r => by
    have h1 := ConcreteCategory.congr_hom (ι_appTop_topIso_hom (X := Spec R) V)
      ((Spec R).presheaf.map (⊤ : (Spec R).Opens).leTop.op ((Scheme.ΓSpecIso R).inv r))
    have h2 := ConcreteCategory.congr_hom (map_leTop_top_map_leTop (X := Spec R) V)
      ((Scheme.ΓSpecIso R).inv r)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h1 h2
    rw [h1, h2]
    rfl
  { toFun x := V.topIso.hom (x : Γ(V.toScheme, ⊤))
    invFun y := ((V.topIso.inv y : Γ(V.toScheme, ⊤)) :
      Γ((Scheme.Modules.pushforward V.ι).obj
        (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf), (⊤ : (Spec R).Opens)))
    map_add' _ _ := map_add _ _ _
    map_smul' r x :=
      ((map_mul V.topIso.hom.hom
          (V.ι.appTop ((Spec R).presheaf.map (⊤ : (Spec R).Opens).leTop.op
            ((Scheme.ΓSpecIso R).inv r))) x).trans
        (by rw [hkey])).trans (Algebra.smul_def r _).symm
    left_inv x := ConcreteCategory.congr_hom V.topIso.hom_inv_id x
    right_inv y := ConcreteCategory.congr_hom V.topIso.inv_hom_id y }

/-- **A coherent direct image has finite global sections.** If the direct image of the structure
sheaf of an open `V` of `Spec R` is coherent, then `Γ(Spec R, V)` is a finite `R`-module. -/
theorem module_finite_sections_of_isCoherent (R : CommRingCat.{u}) [IsNoetherianRing R]
    (V : (Spec R).Opens)
    (h : ((Scheme.Modules.pushforward V.ι).obj
      (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf)).IsCoherent) :
    Module.Finite (ToType R) Γ(Spec R, V) := by
  have hqc := Stacks.AlgebraicGeometry.FlatBaseChange.isQuasicoherent_pushforward_of_qcqs V.ι
    (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf)
  have hft := h.isFiniteType
  have hfin := AlgebraicGeometry.moduleFinite_of_isFiniteType_qc R
    ((Scheme.Modules.pushforward V.ι).obj (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf))
  exact Module.Finite.equiv (sectionsTopPushforwardOpensLinearEquiv R V)

/-- **The completed-local-ring obstruction to coherence, over the punctured spectrum.**

Let `R` be a Noetherian local ring with an associated prime `𝔭` in the Stacks sense such that
`dim(R ⧸ 𝔭) = 1`, and let `V` be the punctured spectrum of `R`. Then the direct image of `𝒪_V`
along `V ⟶ Spec R` is not coherent.

This is the case `X = Spec R`, `U = V` of [Stacks, Tag 0AWC]. -/
theorem not_isCoherent_pushforward_structureSheaf_puncturedSpectrum (R : CommRingCat.{u})
    [IsNoetherianRing R] [IsLocalRing R] {p : Ideal (ToType R)} [p.IsPrime]
    (hp : IsAssociatedPrimeStacks (ToType R) (ToType R) p)
    (hdim : ringKrullDim (ToType R ⧸ p) = 1) :
    ¬ ((Scheme.Modules.pushforward (puncturedSpectrum R).ι).obj
      (SheafOfModules.unit.{u} (puncturedSpectrum R).toScheme.ringCatSheaf)).IsCoherent :=
  fun h => not_module_finite_sections_puncturedSpectrum R hp hdim
    (module_finite_sections_of_isCoherent R (puncturedSpectrum R) h)

/-! ### Step (1): restricting to an affine open

Coherence is local on the base, and what the argument of [Stacks, Tag 0AWC] needs out of it is
the finiteness of the sections over one affine open containing `z`.
-/

/-- **The sections of a coherent module over an affine open are a finite module.** On a locally
Noetherian scheme, if `F` is coherent and `W` is an affine open, then `Γ(F, W)` is a finite
`Γ(X, W)`-module. -/
@[ega "I 10.10.1" "partial"]
theorem module_finite_sections_affineOpen {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) (hF : F.IsCoherent) {W : X.Opens} (hW : IsAffineOpen W) :
    Module.Finite Γ(X, W) Γ(F, W) := by
  have : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec
  obtain ⟨hqc, hft⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  have : (F.restrict hW.fromSpec).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor hW.fromSpec F
  have : (F.restrict hW.fromSpec).IsFiniteType :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_restrict hW.fromSpec F
  have : Module.Finite Γ(X, W) Γ(F.restrict hW.fromSpec, ⊤) :=
    AlgebraicGeometry.moduleFinite_of_isFiniteType_qc (CommRingCat.of Γ(X, W))
      (F.restrict hW.fromSpec)
  exact Module.Finite.equiv (AlgebraicGeometry.affineSectionsLinearEquiv F hW)

/-- **Step (1) of [Stacks, Tag 0AWC].** If the direct image of the structure sheaf of `U` along an
open immersion `j : U ⟶ X` into a locally Noetherian scheme is coherent, then for every affine
open `W` of `X` the sections of `j_*𝒪_U` over `W` — which are, by definition
(`AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj`), the sections of `𝒪_U` over
`j ⁻¹ᵁ W` — are a finite `Γ(X, W)`-module. -/
theorem module_finite_sections_pushforward_affineOpen {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (j : Y ⟶ X)
    (h : ((Scheme.Modules.pushforward j).obj (SheafOfModules.unit.{u} Y.ringCatSheaf)).IsCoherent)
    {W : X.Opens} (hW : IsAffineOpen W) :
    Module.Finite Γ(X, W)
      Γ((Scheme.Modules.pushforward j).obj (SheafOfModules.unit.{u} Y.ringCatSheaf), W) :=
  module_finite_sections_affineOpen _ h hW

/-! ### The assembly, granted the two flat base changes

What remains of [Stacks, Tag 0AWC] after steps (1) and (3) is the two applications of the
degree-zero flat base change of [Stacks, Tag 02KH]. The next theorem takes their conclusions as
hypotheses.
-/

/-- **[Stacks, Tag 0AWC], granted the two degree-zero flat base changes.**

Let `X` be an integral locally Noetherian scheme, `j : Y ⟶ X` a nonempty open immersion, `z` a
point outside the image, and `R` a Noetherian local ring with an associated prime `𝔭` in the
Stacks sense such that `dim(R ⧸ 𝔭) = 1` — in the tag, `R = 𝒪^∧_{X,z}`. Suppose

* `hbc₁`: coherence of `j_*𝒪_Y` makes the sections of `𝒪_{Spec 𝒪_{X,z}}` over the preimage of
  the image of `j` a finite `𝒪_{X,z}`-module;
* `hbc₂`: finiteness of the sections over the punctured spectrum of `𝒪_{X,z}` is inherited by the
  sections over the punctured spectrum of `R`.

Then `j_*𝒪_Y` is not coherent. -/
theorem not_isCoherent_pushforward_structureSheaf_of_baseChange {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (j : Y ⟶ X) [IsOpenImmersion j] (z : X)
    (hz : z ∉ j.opensRange) (hne : (j.opensRange : Set X).Nonempty)
    (R : CommRingCat.{u}) [IsNoetherianRing R] [IsLocalRing R] {p : Ideal (ToType R)} [p.IsPrime]
    (hp : IsAssociatedPrimeStacks (ToType R) (ToType R) p)
    (hdim : ringKrullDim (ToType R ⧸ p) = 1)
    (hbc₁ : ((Scheme.Modules.pushforward j).obj
          (SheafOfModules.unit.{u} Y.ringCatSheaf)).IsCoherent →
      Module.Finite (ToType (X.presheaf.stalk z))
        Γ(Spec (X.presheaf.stalk z), X.fromSpecStalk z ⁻¹ᵁ j.opensRange))
    (hbc₂ : Module.Finite (ToType (X.presheaf.stalk z))
          Γ(Spec (X.presheaf.stalk z), puncturedSpectrum (X.presheaf.stalk z)) →
      Module.Finite (ToType R) Γ(Spec R, puncturedSpectrum R)) :
    ¬ ((Scheme.Modules.pushforward j).obj
      (SheafOfModules.unit.{u} Y.ringCatSheaf)).IsCoherent :=
  fun h => not_module_finite_sections_puncturedSpectrum R hp hdim
    (hbc₂ (module_finite_sections_puncturedSpectrum_of_preimage z j.opensRange hne hz (hbc₁ h)))

/-! ### Discharging `hbc₂`: base change along the completion map -/

/-- **The second flat base change of [Stacks, Tag 0AWC].** Let `φ : R ⟶ S` be a flat homomorphism
of local rings with `R` Noetherian, carrying the maximal ideal of `R` onto a generating set of the
maximal ideal of `S` — the completion map of a Noetherian local ring is such a map. Then
finiteness of the sections over the punctured spectrum of `R` is inherited by the sections over
the punctured spectrum of `S`. -/
theorem module_finite_sections_puncturedSpectrum_of_flat {R S : CommRingCat.{u}}
    [IsNoetherianRing R] [IsLocalRing R] [IsLocalRing S] (φ : R ⟶ S) (hφ : φ.hom.Flat)
    (hmap : Ideal.map φ.hom (IsLocalRing.maximalIdeal (ToType R)) =
      IsLocalRing.maximalIdeal (ToType S))
    (h : Module.Finite (ToType R) Γ(Spec R, puncturedSpectrum R)) :
    Module.Finite (ToType S) Γ(Spec S, puncturedSpectrum S) := by
  let := Stacks.AlgebraicGeometry.FlatBaseChange.noetherianSpace_opens (puncturedSpectrum R)
  have key := Stacks.AlgebraicGeometry.FlatBaseChange.module_finite_sections_preimage_of_flat
    φ hφ (puncturedSpectrum R) h
  rwa [preimage_puncturedSpectrum_of_map_maximalIdeal φ hmap] at key

/-! ### Discharging `hbc₁`: base change to the local ring at `z` -/

/-- **The sections of `j_*𝒪_Y` over an affine open `W` and the sections of `𝒪` over the preimage
of the image of `j` in `Spec Γ(X, W)` are one and the same `Γ(X, W)`-module**: there is an
additive equivalence between them commuting with the action of `Γ(X, W)`. -/
private theorem exists_addEquiv_sections_fromSpec_preimage_opensRange {X Y : Scheme.{u}}
    (j : Y ⟶ X) [IsOpenImmersion j] {W : X.Opens} (hW : IsAffineOpen W) :
    ∃ e : Γ((Scheme.Modules.pushforward j).obj (SheafOfModules.unit.{u} Y.ringCatSheaf), W) ≃+
        Γ(Spec Γ(X, W), hW.fromSpec ⁻¹ᵁ j.opensRange),
      ∀ (a : ToType Γ(X, W))
        (x : Γ((Scheme.Modules.pushforward j).obj (SheafOfModules.unit.{u} Y.ringCatSheaf), W)),
        e (a • x) = a • e x := by
  obtain ⟨T, hTj, hTW, hjT, hfT⟩ :
      ∃ T : X.Opens, T ≤ j.opensRange ∧ T ≤ W ∧ j ⁻¹ᵁ T = j ⁻¹ᵁ W ∧
        hW.fromSpec ⁻¹ᵁ T = hW.fromSpec ⁻¹ᵁ j.opensRange :=
    ⟨j.opensRange ⊓ W, inf_le_left, inf_le_right,
      by rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_opensRange, top_inf_eq],
      by rw [Scheme.Hom.preimage_inf, hW.fromSpec_preimage_self, inf_top_eq]⟩
  have : IsIso (j.app T) := j.isIso_app T hTj
  have : IsIso (hW.fromSpec.app T) :=
    hW.fromSpec.isIso_app T (hW.opensRange_fromSpec.symm ▸ hTW)
  have : IsIso (Y.presheaf.map (eqToHom hjT).op) := inferInstance
  have : IsIso ((Spec Γ(X, W)).presheaf.map (eqToHom hfT.symm).op) := inferInstance
  have h1 : j.app W ≫ Y.presheaf.map (eqToHom hjT).op =
      X.presheaf.map (homOfLE hTW).op ≫ j.app T := by
    rw [show (eqToHom hjT).op = (homOfLE (le_of_eq hjT)).op from Subsingleton.elim _ _,
      show j.app W ≫ Y.presheaf.map (homOfLE (le_of_eq hjT)).op =
        j.appLE W (j ⁻¹ᵁ T) (le_of_eq hjT) from rfl,
      show j.app T = j.appLE T (j ⁻¹ᵁ T) le_rfl from (Scheme.Hom.appLE_eq_app j).symm,
      Scheme.Hom.map_appLE]
  have h2 : X.presheaf.map (homOfLE hTW).op ≫ hW.fromSpec.app T ≫
      (Spec Γ(X, W)).presheaf.map (eqToHom hfT.symm).op =
      CommRingCat.ofHom (algebraMap (ToType Γ(X, W))
        Γ(Spec Γ(X, W), hW.fromSpec ⁻¹ᵁ j.opensRange)) := by
    rw [show hW.fromSpec.app T = hW.fromSpec.appLE T (hW.fromSpec ⁻¹ᵁ T) le_rfl from
        (Scheme.Hom.appLE_eq_app _).symm,
      ← Category.assoc, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE,
      hW.fromSpec_app_self, Category.assoc, ← Functor.map_comp,
      show CommRingCat.ofHom (algebraMap (ToType Γ(X, W))
            Γ(Spec Γ(X, W), hW.fromSpec ⁻¹ᵁ j.opensRange)) =
          (Scheme.ΓSpecIso Γ(X, W)).inv ≫
            (Spec Γ(X, W)).presheaf.map (homOfLE le_top).op from by
        rw [IsAffineOpen.algebraMap_Spec_obj]; rfl]
    exact congrArg (fun m : op (⊤ : (Spec Γ(X, W)).Opens) ⟶
        op (hW.fromSpec ⁻¹ᵁ j.opensRange) =>
      (Scheme.ΓSpecIso Γ(X, W)).inv ≫ (Spec Γ(X, W)).presheaf.map m)
      (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
  let C : Γ(Y, j ⁻¹ᵁ W) ⟶ Γ(Spec Γ(X, W), hW.fromSpec ⁻¹ᵁ j.opensRange) :=
    Y.presheaf.map (eqToHom hjT).op ≫ inv (j.app T) ≫ hW.fromSpec.app T ≫
      (Spec Γ(X, W)).presheaf.map (eqToHom hfT.symm).op
  have hkey : ∀ a : ToType Γ(X, W), C.hom ((j.app W).hom a) =
      algebraMap (ToType Γ(X, W)) Γ(Spec Γ(X, W), hW.fromSpec ⁻¹ᵁ j.opensRange) a := fun a => by
    have : j.app W ≫ C = CommRingCat.ofHom (algebraMap (ToType Γ(X, W))
        Γ(Spec Γ(X, W), hW.fromSpec ⁻¹ᵁ j.opensRange)) := by
      rw [← Category.assoc, h1, Category.assoc, IsIso.hom_inv_id_assoc, h2]
    simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom] using ConcreteCategory.congr_hom this a
  refine ⟨(asIso C).commRingCatIsoToRingEquiv.toAddEquiv, fun a x => ?_⟩
  rw [Algebra.smul_def]
  show C.hom (@HMul.hMul (ToType Γ(Y, j ⁻¹ᵁ W)) _ _ _ ((j.app W).hom a)
      (show ToType Γ(Y, j ⁻¹ᵁ W) from x)) = _
  rw [map_mul, hkey]
  rfl

/-- **The sections of `j_*𝒪_Y` over an affine open are the sections of `𝒪` over an open of its
spectrum.** Let `j : Y ⟶ X` be an open immersion and `W` an affine open of `X`. If `Γ(j_*𝒪_Y, W)`
is a finite `Γ(X, W)`-module, then so is `Γ(Spec Γ(X, W), hW.fromSpec ⁻¹ᵁ j.opensRange)`. -/
theorem module_finite_sections_fromSpec_preimage_opensRange {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] {W : X.Opens} (hW : IsAffineOpen W)
    (hfin : Module.Finite Γ(X, W)
      Γ((Scheme.Modules.pushforward j).obj (SheafOfModules.unit.{u} Y.ringCatSheaf), W)) :
    Module.Finite (ToType Γ(X, W)) Γ(Spec Γ(X, W), hW.fromSpec ⁻¹ᵁ j.opensRange) := by
  obtain ⟨e, he⟩ := exists_addEquiv_sections_fromSpec_preimage_opensRange j hW
  exact Stacks.AlgebraicGeometry.FlatBaseChange.module_finite_of_ringEquiv _ _
    (RingEquiv.refl (ToType Γ(X, W))) e he hfin

/-- Let `j : Y ⟶ X` be an open immersion and `W` an affine open of `X`. If
`Γ(Spec Γ(X, W), hW.fromSpec ⁻¹ᵁ j.opensRange)` is a finite `Γ(X, W)`-module, then so is
`Γ(j_*𝒪_Y, W)`. This is the converse of `module_finite_sections_fromSpec_preimage_opensRange`. -/
theorem module_finite_sections_of_fromSpec_preimage_opensRange {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] {W : X.Opens} (hW : IsAffineOpen W)
    (hfin : Module.Finite (ToType Γ(X, W))
      Γ(Spec Γ(X, W), hW.fromSpec ⁻¹ᵁ j.opensRange)) :
    Module.Finite Γ(X, W)
      Γ((Scheme.Modules.pushforward j).obj (SheafOfModules.unit.{u} Y.ringCatSheaf), W) := by
  obtain ⟨e, he⟩ := exists_addEquiv_sections_fromSpec_preimage_opensRange j hW
  refine Stacks.AlgebraicGeometry.FlatBaseChange.module_finite_of_ringEquiv _ _
    (RingEquiv.refl (ToType Γ(X, W))) e.symm (fun a y => ?_) hfin
  refine e.injective ?_
  rw [e.apply_symm_apply, he, e.apply_symm_apply]
  rfl

/-- **The first flat base change of [Stacks, Tag 0AWC].** If the direct image of the structure
sheaf of `Y` along an open immersion `j : Y ⟶ X` into a locally Noetherian scheme is coherent,
then the sections of `𝒪` over the preimage of the image of `j` in `Spec 𝒪_{X,z}` are a finite
`𝒪_{X,z}`-module, for every point `z` of `X`. -/
theorem module_finite_sections_preimage_fromSpecStalk {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (j : Y ⟶ X) [IsOpenImmersion j] (z : X)
    (h : ((Scheme.Modules.pushforward j).obj
      (SheafOfModules.unit.{u} Y.ringCatSheaf)).IsCoherent) :
    Module.Finite (ToType (X.presheaf.stalk z))
      Γ(Spec (X.presheaf.stalk z), X.fromSpecStalk z ⁻¹ᵁ j.opensRange) := by
  obtain ⟨W, hW, hzW, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := z) (U := ⊤) (TopologicalSpace.Opens.mem_top z)
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hfinA := module_finite_sections_fromSpec_preimage_opensRange j hW
    (module_finite_sections_pushforward_affineOpen j h hW)
  let : Algebra (ToType Γ(X, W)) (ToType (X.presheaf.stalk z)) :=
    X.presheaf.algebra_section_stalk (U := W) ⟨z, hzW⟩
  have : IsLocalization.AtPrime (ToType (X.presheaf.stalk z))
      (hW.primeIdealOf ⟨z, hzW⟩).asIdeal := hW.isLocalization_stalk ⟨z, hzW⟩
  have hflat : (X.presheaf.germ W z hzW).hom.Flat :=
    RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (ToType (X.presheaf.stalk z))
        (hW.primeIdealOf ⟨z, hzW⟩).asIdeal.primeCompl)
  let := Stacks.AlgebraicGeometry.FlatBaseChange.noetherianSpace_opens
    (hW.fromSpec ⁻¹ᵁ j.opensRange)
  have key := Stacks.AlgebraicGeometry.FlatBaseChange.module_finite_sections_preimage_of_flat
    (X.presheaf.germ W z hzW) hflat (hW.fromSpec ⁻¹ᵁ j.opensRange) hfinA
  rwa [show Spec.map (X.presheaf.germ W z hzW) ⁻¹ᵁ (hW.fromSpec ⁻¹ᵁ j.opensRange) =
      X.fromSpecStalk z ⁻¹ᵁ j.opensRange from by
    rw [← hW.fromSpecStalk_eq_fromSpecStalk hzW, IsAffineOpen.fromSpecStalk]; rfl] at key

/-! ### [Stacks, Tag 0AWC] -/

/-- **[Stacks, Tag 0AWC], the completed-local-ring obstruction to coherence.** Let `j : U ⟶ X` be
an open immersion of integral locally Noetherian schemes and suppose some point `z` outside the
image of `j` has an associated prime `𝔭` of the completed local ring `𝒪^∧_{X,z}` with
`dim(𝒪^∧_{X,z} ⧸ 𝔭) = 1`. Then `j_*𝒪_U` is not coherent.

This is the second paragraph of the remark, its `completed_local_ring_obstruction` clause, the
converse to [Stacks, Tag 0E9I]. -/
@[stacks 0AWC "completed_local_ring_obstruction", ega "IV 7.2.4" "(e) ⇒ (f)"]
theorem not_isCoherent_pushforward_structureSheaf {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsIntegral U] [IsIntegral X] [IsLocallyNoetherian X]
    (h : ∃ (z : X) (p : Ideal (AdicCompletion
        (IsLocalRing.maximalIdeal (ToType (X.presheaf.stalk z)))
        (ToType (X.presheaf.stalk z)))),
      z ∉ Set.range j.base ∧
      IsAssociatedPrimeStacks
        (AdicCompletion (IsLocalRing.maximalIdeal (ToType (X.presheaf.stalk z)))
          (ToType (X.presheaf.stalk z)))
        (AdicCompletion (IsLocalRing.maximalIdeal (ToType (X.presheaf.stalk z)))
          (ToType (X.presheaf.stalk z))) p ∧
      ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal (ToType (X.presheaf.stalk z)))
        (ToType (X.presheaf.stalk z)) ⧸ p) = 1) :
    ¬ ((Scheme.Modules.pushforward j).obj
      (SheafOfModules.unit.{u} U.ringCatSheaf)).IsCoherent := by
  obtain ⟨z, p, hz, hp, hdim⟩ := h
  have : p.IsPrime := hp.1
  have hne : (j.opensRange : Set X).Nonempty :=
    ⟨j.base (Nonempty.some inferInstance), _, rfl⟩
  exact not_isCoherent_pushforward_structureSheaf_of_baseChange j z hz hne
    (CommRingCat.of (AdicCompletion (IsLocalRing.maximalIdeal (ToType (X.presheaf.stalk z)))
      (ToType (X.presheaf.stalk z)))) hp hdim
    (fun hc => module_finite_sections_preimage_fromSpecStalk j z hc)
    (fun hfin => module_finite_sections_puncturedSpectrum_of_flat
      (CommRingCat.ofHom (algebraMap (ToType (X.presheaf.stalk z))
        (AdicCompletion (IsLocalRing.maximalIdeal (ToType (X.presheaf.stalk z)))
          (ToType (X.presheaf.stalk z)))))
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
      (AdicCompletion.maximalIdeal_eq_map_of_fg
        (IsNoetherian.noetherian (IsLocalRing.maximalIdeal (ToType (X.presheaf.stalk z))))).symm
      hfin)

end Stacks.LocalCohomology

end

