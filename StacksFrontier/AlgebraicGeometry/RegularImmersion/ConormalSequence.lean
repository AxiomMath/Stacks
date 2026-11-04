module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksFrontier.AlgebraicGeometry.Conormal.ConormalSequenceExact
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.LocalLiftingOverASlice
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.Implications
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.TwoImmersionsConormalMono
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.ConormalLocallyFree
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.FinitePresentation
public import StacksFrontier.RingTheory.Koszul.Descent
public import StacksFrontier.RingTheory.Regular.Ideal
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The conormal sequence of an H1-regular immersion

Let `Z --i--→ Y --j--→ X` be immersions of schemes.  The canonical sequence of
[Stacks Project, Tag 062S] is `i^* C_{Y/X} ⟶ C_{Z/X} ⟶ C_{Z/Y} ⟶ 0`, with both maps those of
[Stacks Project, Tag 01R4].  When `i` is `H1`-regular the sequence is exact also at its left-hand
term, so that `0 ⟶ i^* C_{Y/X} ⟶ C_{Z/X} ⟶ C_{Z/Y} ⟶ 0` is short exact, and it is split on a
neighbourhood of every point of `Z`.  That is [Stacks Project, Tag 063N].

Injectivity of the left-hand map is a local, and then affine, question.  Over an affine open
`V` of `X` on which the three immersions `j`, `i ≫ j` and `i|_{j^{-1}V}` have affine models in
the sense of [Stacks Project, Tag 01R3] part (2) — a chart of the chain, in the sense of
`Stacks.Immersion.ConormalChart` — the sequence reads, on conormal sections, as
`K/K^2 ⊗ A/J ⟶ J/J^2` for the kernel ideals `K ⊆ J` of `j` and of `i ≫ j`, and injectivity of
the left-hand map becomes the assertion that a function of `K` whose class in `J/J^2` vanishes
already lies in `K · J`.  That is `K ∩ J^2 = K · J`, which is
[Stacks Project, Tag 0666] for the ideal `J/K`, `H1`-regular because `i` is.

Local splitness comes from the right-hand term: an `H1`-regular immersion is quasi-regular, so
`C_{Z/Y}` is finite locally free by [Stacks Project, Tag 063M] condition (2), and on a
trivialising open it is a retract of a finite free sheaf.  The local lifting lemma of
[Stacks Project, Tag 08C6] then lifts the identity of `C_{Z/Y}` through the surjection
`C_{Z/X} ⟶ C_{Z/Y}` after passing to a smaller open, and a section of the right-hand map of a
short exact sequence is a splitting.

## Main results

* `Stacks.AlgebraicGeometry.RegularIdealSheaf.isH1Regular_ker_app_of_isH1RegularImmersion`: over
  an affine open of the coborder of the range of an `H1`-regular immersion the kernel ideal is
  `H1`-regular in the sense of [Stacks Project, Tag 07CV] part (3).
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.mono_conormalLeftMap`: **the conormal
  sequence of an `H1`-regular immersion is exact at its left-hand term**, that is, the canonical
  map `i^* C_{Y/X} ⟶ C_{Z/X}` is a monomorphism.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSequence_shortExact`: **the conormal
  sequence of an `H1`-regular immersion is short exact.**
* `Stacks.AlgebraicGeometry.RegularIdealSheaf`
  `.isFiniteLocallyFree_conormalSheaf_of_isH1RegularImmersion`: the conormal sheaf of an
  `H1`-regular immersion is finite locally free.
* `Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSequence_locallySplit`: **the conormal
  sequence of an `H1`-regular immersion is split on a neighbourhood of every point.**

## Implementation notes

The affine intersection identity is consumed in the form
`Ideal.inf_sq_eq_mul_of_quotient_isH1RegularIdeal`, whose hypothesis is `H1`-regularity of the
image of `J` in `A/K`.  That image is carried to the kernel ideal of `i` over `j^{-1}V` by the
isomorphism `A/K ≅ Γ(Y, j^{-1}V)` coming from surjectivity of `j` on sections over the chart, and
`H1`-regularity of an ideal is preserved by a ring isomorphism because such a map is flat.

`H1`-regularity of an immersion is a condition on the defining ideal *sheaf* of its canonical
closed factor, stated stalkwise; what the affine computation needs is `Ideal.IsH1Regular` for the
kernel ideal on an affine open.  `AlgebraicGeometry.isH1RegularIdealSheaf_iff_kerGeneratedBy`
turns the sheaf condition into `H1`-regular generators of the kernel on *some* affine open around
each point of the closure of the range, and the passage from there to an arbitrary affine open is
a principal localization, carried out prime by prime.

Injectivity is tested on stalks.  Every element of the stalk of `i^* C_{Y/X}` is the germ of the
image under the unit of `i^* ⊣ i_*` of a section of `C_{Y/X}`, because `i` is surjective on
stalks; this is the stalk formula of [Stacks Project, Tag 0098].  The section may then be
restricted to a chart, where it is the class of a function of `K` by [Stacks Project, Tag 01R3]
part (2).

Local splitness is stated for the slice restriction `SheafOfModules.over`, which is the
restriction the local lifting lemma of [Stacks Project, Tag 08C6] produces and is the one the
free-sheaf API of `SheafOfModules.GeneratingSections` is written for.  It agrees with the
open-subscheme restriction `AlgebraicGeometry.Scheme.Modules.restrictFunctor` by
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`.

## References

* [Stacks Project, Tag 063N](https://stacks.math.columbia.edu/tag/063N)
* [Stacks Project, Tag 062S](https://stacks.math.columbia.edu/tag/062S)
* [Stacks Project, Tag 063M](https://stacks.math.columbia.edu/tag/063M)
* [Stacks Project, Tag 063K](https://stacks.math.columbia.edu/tag/063K)
* [Stacks Project, Tag 0666](https://stacks.math.columbia.edu/tag/0666)
* [Stacks Project, Tag 07CV](https://stacks.math.columbia.edu/tag/07CV)
* [Stacks Project, Tag 07CX](https://stacks.math.columbia.edu/tag/07CX)
* [Stacks Project, Tag 08C6](https://stacks.math.columbia.edu/tag/08C6)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction 
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Stacks.ClosedImmersion Stacks.ClosedImmersion.AffineConormal
open Stacks.ClosedImmersion.IdealSheafAffine
open Stacks.Immersion
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

variable {Z Y X : Scheme.{u}}

/-! ### `H1`-regularity of the kernel ideal on an affine open -/

/-- The sections of `(i ≫ j)^♯` factor through those of `j^♯`. -/
private theorem comp_app_apply (i : Z ⟶ Y) (j : Y ⟶ X) (U : X.Opens) (s : Γ(X, U)) :
    ((i ≫ j).app U).hom s = (i.app (j ⁻¹ᵁ U)).hom ((j.app U).hom s) :=
  congrArg (fun φ : Γ(X, U) ⟶ Γ(Z, (i ≫ j) ⁻¹ᵁ U) => φ.hom s) (Scheme.Hom.comp_app i j U)

/-- The kernel of `(i ≫ j)^♯` is the preimage under `j^♯` of the kernel of `i^♯`. -/
private theorem ker_comp_app_eq_comap (i : Z ⟶ Y) (j : Y ⟶ X) (U : X.Opens) :
    RingHom.ker ((i ≫ j).app U).hom =
      Ideal.comap (j.app U).hom (RingHom.ker (i.app (j ⁻¹ᵁ U)).hom) :=
  Ideal.ext fun s => by
    rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker, comp_app_apply]
    exact Iff.rfl

/-- Post-composing with an isomorphism does not change the kernel. -/
private theorem ker_comp_isIso_right {R S T : CommRingCat.{u}} (a : R ⟶ S) (b : S ⟶ T)
    [IsIso b] : RingHom.ker (a ≫ b).hom = RingHom.ker a.hom := by
  rw [CommRingCat.hom_comp, ← RingHom.comap_ker,
    (RingHom.injective_iff_ker_eq_bot _).mp (ConcreteCategory.bijective_of_isIso b).1]
  rfl

/-- `H₁`-regularity of an ideal is carried along a ring isomorphism. -/
private theorem isH1Regular_comap_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    (δ : R ≃+* S) (K : Ideal S) (hK : Ideal.IsH1Regular K) :
    Ideal.IsH1Regular (Ideal.comap (δ : R →+* S) K) := by
  have h : Ideal.comap (δ : R →+* S) K = Ideal.map (δ.symm : S →+* R) K := by
    refine le_antisymm (fun x hx => ?_) (Ideal.map_le_iff_le_comap.mpr fun x hx => ?_)
    · simpa using Ideal.mem_map_of_mem (δ.symm : S →+* R) (show δ x ∈ K from hx)
    · refine Ideal.mem_comap.mpr (Ideal.mem_comap.mpr ?_)
      simp only [RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
      exact hx
  rw [h]
  exact (Koszul.regularIdeals_map_flat (δ.symm : S →+* R)
    (RingHom.Flat.of_bijective δ.symm.bijective) K).2.1 hK

/-- **The kernel ideal of a closed immersion over an affine open is `H₁`-regular**, when the
immersion is one whose kernel is generated by an `H₁`-regular sequence near every point of the
closure of its range. -/
private theorem isH1Regular_ker_app_of_kerGeneratedBy {W₀ C₀ : Scheme.{u}} (p : W₀ ⟶ C₀)
    [IsClosedImmersion p]
    (hp : _root_.AlgebraicGeometry.KerGeneratedBy (fun f => Koszul.IsH1Regular f) p)
    (U : C₀.affineOpens) : Ideal.IsH1Regular (RingHom.ker (p.app U.1).hom) := by
  intro q hq
  have hxU : U.2.fromSpec q ∈ U.1 := U.2.range_fromSpec.le ⟨q, rfl⟩
  have hxzero : U.2.fromSpec q ∈
      C₀.zeroLocus (RingHom.ker (p.app U.1).hom : Set Γ(C₀, U.1)) := by
    have hq' : q ∈ PrimeSpectrum.zeroLocus
        (RingHom.ker (p.app U.1).hom : Set Γ(C₀, U.1)) := hq
    rw [← U.2.fromSpec_preimage_zeroLocus] at hq'
    exact hq'
  have hxp : U.2.fromSpec q ∈ closure (Set.range p.base) := by
    rw [← Scheme.Hom.support_ker]
    exact (p.ker.mem_support_iff_of_mem hxU).mpr (by simpa [p.ker_apply] using hxzero)
  obtain ⟨V, hxV, r, f, hker, hf⟩ := hp _ hxp
  obtain ⟨g, k, hgk, hxg⟩ := exists_basicOpen_le_affine_inter U.2 V.2 _ ⟨hxU, hxV⟩
  have hWV : C₀.basicOpen g ≤ V.1 := hgk.le.trans (C₀.basicOpen_le k)
  let ρ : Γ(C₀, V.1) →+* Γ(C₀, C₀.basicOpen g) := (C₀.presheaf.map (homOfLE hWV).op).hom
  let _ : Algebra Γ(C₀, V.1) Γ(C₀, C₀.basicOpen g) := ρ.toAlgebra
  have : IsLocalization.Away k Γ(C₀, C₀.basicOpen g) :=
    V.2.isLocalization_of_eq_basicOpen k (homOfLE hWV) hgk
  have : Module.Flat Γ(C₀, V.1) Γ(C₀, C₀.basicOpen g) :=
    IsLocalization.flat _ (Submonoid.powers k)
  have hρflat : ρ.Flat := inferInstanceAs (Module.Flat Γ(C₀, V.1) Γ(C₀, C₀.basicOpen g))
  have hfW : Koszul.IsH1Regular fun n => ρ (f n) :=
    _root_.AlgebraicGeometry.isH1Regular_of_ringHomFlat ρ hρflat f hf
  have hkerW : p.ker.ideal ⟨C₀.basicOpen g, U.2.basicOpen g⟩ =
      Ideal.span (Set.range fun n => ρ (f n)) := by
    rw [← p.ker.map_ideal (U := ⟨C₀.basicOpen g, U.2.basicOpen g⟩) (V := V) hWV,
      p.ker_apply V, hker, Ideal.map_span, ← Set.range_comp]
    rfl
  have : IsLocalization.Away g Γ(C₀, C₀.basicOpen g) := U.2.isLocalization_basicOpen g
  let e : Γ(C₀, C₀.basicOpen g) ≃ₐ[Γ(C₀, U.1)] Localization.Away g :=
    (IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g)
      Γ(C₀, C₀.basicOpen g)).symm
  have hg : g ∉ q.asIdeal := by
    show q ∈ PrimeSpectrum.basicOpen g
    rw [← U.2.fromSpec_preimage_basicOpen]
    exact hxg
  refine ⟨g, hg, r, fun n => e (ρ (f n)),
    _root_.AlgebraicGeometry.isH1Regular_of_ringHomFlat e.toRingEquiv.toRingHom
      (RingHom.Flat.of_bijective e.toRingEquiv.bijective) _ hfW, ?_⟩
  have hmap : e.toRingHom.comp (C₀.presheaf.map (homOfLE (C₀.basicOpen_le g)).op).hom =
      algebraMap Γ(C₀, U.1) (Localization.Away g) := by
    ext b
    exact e.commutes b
  rw [← p.ker_apply U, ← hmap, ← Ideal.map_map, p.ker.map_ideal_basicOpen U g]
  show Ideal.map e.toRingHom (p.ker.ideal ⟨C₀.basicOpen g, U.2.basicOpen g⟩) = _
  rw [hkerW, Ideal.map_span, ← Set.range_comp]
  rfl

/-- **The kernel ideal of an `H₁`-regular immersion over an affine open of the coborder of its
range is `H₁`-regular.** -/
theorem isH1Regular_ker_app_of_isH1RegularImmersion (i : Z ⟶ Y) [IsImmersion i]
    (hi : IsH1RegularImmersion i) (V : Y.Opens) (hV : IsAffineOpen V)
    (hVc : V ≤ i.coborderRange) :
    Ideal.IsH1Regular (RingHom.ker (i.app V).hom) := by
  have hVr : V ≤ i.coborderRange.ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι]
    exact hVc
  have hV0 : IsAffineOpen (i.coborderRange.ι ⁻¹ᵁ V) :=
    hV.preimage_of_isOpenImmersion i.coborderRange.ι hVr
  have : IsIso (i.coborderRange.ι.app V) := Scheme.Hom.isIso_app i.coborderRange.ι V hVr
  set δ : Γ(Y, V) ≃+* Γ(i.coborderRange.toScheme, i.coborderRange.ι ⁻¹ᵁ V) :=
    (asIso (i.coborderRange.ι.app V)).commRingCatIsoToRingEquiv
  have h1 : RingHom.ker (i.app V).hom =
      RingHom.ker ((i.liftCoborder ≫ i.coborderRange.ι).app V).hom := by
    rw [Scheme.Hom.congr_app i.liftCoborder_ι.symm V]
    exact ker_comp_isIso_right _ _
  have h2 := ker_comp_app_eq_comap i.liftCoborder i.coborderRange.ι V
  rw [h1, h2]
  refine isH1Regular_comap_ringEquiv δ _
    (isH1Regular_ker_app_of_kerGeneratedBy i.liftCoborder ?_ ⟨i.coborderRange.ι ⁻¹ᵁ V, hV0⟩)
  exact (_root_.AlgebraicGeometry.isH1RegularIdealSheaf_iff_kerGeneratedBy i.liftCoborder).mp hi

/-- **Every germ of a pullback sheaf of modules is the germ of the image of a section.** For a
morphism surjective on stalks, the stalk of `f^* M` at `z` is `𝒪_{Z,z} ⊗_{𝒪_{Y,f z}} M_{f z}`
with the first factor a quotient of the second, so every element is a pure tensor `1 ⊗ m`; and
`m` is the germ of a section of `M`, whose image under the unit of `f^* ⊣ f_*` has the given
germ.

This is [Stacks Project, Tag 0098] in the form
`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`. -/
private theorem exists_germ_unit (f : Z ⟶ Y) [SurjectiveOnStalks f]
    (M : SheafOfModules.{u} (structureSheafRing Y.toLocallyRingedSpace.toRingedSpace)) (z : Z)
    (t : TopCat.Presheaf.stalk (C := Ab.{u})
      ((modulePullback f.toLRSHom.toShHom).obj M).val.presheaf z) :
    ∃ (V : Y.Opens) (hz : f z ∈ V) (s : M.val.obj (op V)),
      TopCat.Presheaf.germ ((modulePullback f.toLRSHom.toShHom).obj M).val.presheaf
          (f ⁻¹ᵁ V) z hz
          (((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).unit.app M).val.app
            (op V) s) = t := by
  let _ : Algebra (Y.presheaf.stalk (f.toLRSHom.toShHom.hom.base z)) (Z.presheaf.stalk z) :=
    (f.toLRSHom.toShHom.hom.stalkMap z).hom.toAlgebra
  obtain ⟨e, he⟩ :=
    RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv f.toLRSHom.toShHom M z
  obtain ⟨m, hm⟩ := @TensorProduct.mk_surjective _ _ _ _ _
    (PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.presheaf) M.val (f.toLRSHom.toShHom.hom.base z)) _ _
    (SurjectiveOnStalks.stalkMap_surjective f z) (e t)
  obtain ⟨V, hz, s, hs⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
  refine ⟨V, hz, s, e.injective ?_⟩
  rw [← hs] at hm
  exact (he V hz s).trans hm


/-! ### The affine intersection identity -/

/-- **The intersection identity of [Stacks Project, Tag 0666] over a chart of the chain.** For a
chart of `Z --i--→ Y --j--→ X` with `K` cutting out `Y` and `J` cutting out `Z`, if `i` is
`H1`-regular then `K ∩ J^2 = K · J`. -/
private theorem chart_inf_sq (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j]
    (hi : IsH1RegularImmersion i) (C : ConormalChart i j) :
    C.idealY ⊓ C.idealZ ^ 2 = C.idealY * C.idealZ := by
  have hWc : j ⁻¹ᵁ C.V ≤ i.coborderRange :=
    Stacks.Conormal.le_coborderRange_of_affineModel i (j ⁻¹ᵁ C.V) C.hW C.idealZY C.eI C.heI
  have hreg : Ideal.IsH1Regular C.idealZY :=
    isH1Regular_ker_app_of_isH1RegularImmersion i hi (j ⁻¹ᵁ C.V) C.hW hWc
  refine Ideal.inf_sq_eq_mul_of_quotient_isH1RegularIdeal _ _ C.idealY_le_idealZ ?_
  set ε : (Γ(X, C.V) ⧸ C.idealY) ≃+* Γ(Y, j ⁻¹ᵁ C.V) :=
    (j.app C.V).hom.quotientKerEquivOfSurjective C.hq
  have hεmk (x : Γ(X, C.V)) :
      (ε : (Γ(X, C.V) ⧸ C.idealY) →+* Γ(Y, j ⁻¹ᵁ C.V)) (Ideal.Quotient.mk C.idealY x) =
        (j.app C.V).hom x :=
    RingHom.quotientKerEquivOfSurjective_apply_mk C.hq x
  have hZ := ker_comp_app_eq_comap i j C.V
  have hmap : Ideal.map (Ideal.Quotient.mk C.idealY) C.idealZ =
      Ideal.comap (ε : (Γ(X, C.V) ⧸ C.idealY) →+* Γ(Y, j ⁻¹ᵁ C.V)) C.idealZY := by
    have hcomap : C.idealZ = Ideal.comap (Ideal.Quotient.mk C.idealY)
        (Ideal.comap (ε : (Γ(X, C.V) ⧸ C.idealY) →+* Γ(Y, j ⁻¹ᵁ C.V)) C.idealZY) :=
      hZ.trans (Ideal.ext fun x => by
        rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap, hεmk x])
    rw [hcomap, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  rw [hmap]
  exact isH1Regular_comap_ringEquiv ε _ hreg

/-! ### The chart generator of the left-hand map -/

/-- **The scalar action on the sections of a twice-iterated pushforward sheaf of modules.** Over
an open `U` of the base the sections are those over `i^{-1}j^{-1}U`, with a function on `U`
acting through `j^♯` and then `i^♯`.  True by `rfl`; the scalar and the section have to be
re-ascribed to the spellings over which the two module structures are declared. -/
private theorem smul_pushforward_section₂ (i : Z ⟶ Y) (j : Y ⟶ X)
    (A : SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace)) (U : X.Opens)
    (r : (structureSheafRing X.toLocallyRingedSpace.toRingedSpace).obj.obj (op U))
    (y : ((modulePushforward j.toLRSHom.toShHom).obj
      ((modulePushforward i.toLRSHom.toShHom).obj A)).val.obj (op U)) :
    r • y =
      (show ((modulePushforward j.toLRSHom.toShHom).obj
          ((modulePushforward i.toLRSHom.toShHom).obj A)).val.obj (op U) from
        (show (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace).obj.obj
              (op (i ⁻¹ᵁ (j ⁻¹ᵁ U))) from
            (i.app (j ⁻¹ᵁ U)).hom ((j.app U).hom (show Γ(X, U) from r))) •
          (show A.val.obj (op (i ⁻¹ᵁ (j ⁻¹ᵁ U))) from y)) := rfl

/-- A function killed by `(i ≫ j)^♯` annihilates the sections of a twice-iterated pushforward. -/
private theorem smul_eq_zero_of_mem_ker (i : Z ⟶ Y) (j : Y ⟶ X)
    (A : SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace)) (U : X.Opens)
    (b : Γ(X, U)) (hb : ((i ≫ j).app U).hom b = 0)
    (y : ((modulePushforward j.toLRSHom.toShHom).obj
      ((modulePushforward i.toLRSHom.toShHom).obj A)).val.obj (op U)) :
    (show (structureSheafRing X.toLocallyRingedSpace.toRingedSpace).obj.obj (op U) from
      b) • y = 0 := by
  rw [smul_pushforward_section₂ i j A U b, ← comp_app_apply i j U b, hb]
  exact zero_smul _ (show A.val.obj (op (i ⁻¹ᵁ (j ⁻¹ᵁ U))) from y)

/-- **A linear map out of an ideal annihilated by a second ideal vanishes on the product.** If
`q : I →ₗ[R] M` satisfies `b • q x = 0` for every `b ∈ J`, then `q` vanishes on every element of
`I` lying in `I · J`. -/
private theorem hom_eq_zero_of_mem_mul {R : Type u} [CommRing R] (I J : Ideal R)
    (M : ModuleCat.{u} R) (q : ModuleCat.of R I.Cotangent ⟶ M)
    (hq : ∀ b ∈ J, ∀ x : I.Cotangent, b • q.hom x = 0) (a : I) (ha : (a : R) ∈ I * J) :
    q.hom (I.toCotangent a) = 0 := by
  rw [Ideal.mul_comm] at ha
  refine Submodule.smul_induction_on'
    (p := fun b (hb : b ∈ J * I) ↦
      q.hom (I.toCotangent ⟨b, Ideal.mul_le_right hb⟩) = 0) (hx := ha) ?_ ?_
  · intro b hb c hc
    have h : q.hom (I.toCotangent (b • (⟨c, hc⟩ : I))) = 0 := by
      rw [map_smul, map_smul]
      exact hq b hb _
    exact h
  · intro b hb c hc hb' hc'
    have h : q.hom
        (I.toCotangent ((⟨b, Ideal.mul_le_right hb⟩ : I) + ⟨c, Ideal.mul_le_right hc⟩)) = 0 := by
      rw [map_add, map_add, hb', hc', add_zero]
    exact h

/-- **The chart generator of the left-hand map.** Over a chart of the chain it carries a function
of `K` to the section of `i^* C_{Y/X}` obtained from its class in `K/K^2` by the affine
computation of [Stacks Project, Tag 01R3] part (2) followed by the unit of `i^* ⊣ i_*`.

Those sections generate, which is why injectivity of the left-hand map may be tested on them. -/
private noncomputable def chartGen {i : Z ⟶ Y} {j : Y ⟶ X} [IsImmersion i] [IsImmersion j]
    (C : ConormalChart i j) :=
  C.isoY.inv ≫
    ((modulePushforward j.toLRSHom.toShHom).map
      ((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
        (ClosedImmersion.conormalSheaf j.liftCoborder.toLRSHom.toShHom))).val.app (op C.V)

/-- **The chart generator written out.** It is the unit of `i^* ⊣ i_*` applied to the conormal
section of `C_{Y/X}` attached to the class of `k` in `K/K^2`. -/
private theorem chartGen_apply {i : Z ⟶ Y} {j : Y ⟶ X} [IsImmersion i] [IsImmersion j]
    (C : ConormalChart i j) (w : C.idealY.Cotangent) :
    (chartGen C).hom w =
      ((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
          (ClosedImmersion.conormalSheaf j.liftCoborder.toLRSHom.toShHom)).val.app (op (j ⁻¹ᵁ C.V))
        (C.isoY.inv.hom w) := rfl

/-- **The chart generator vanishes on `K · J`.** A function of `K` lying in `K · J` has a factor
killed by `(i ≫ j)^♯`, and that factor acts on the sections of the pushforward through
`(i ≫ j)^♯`. -/
private theorem chartGen_eq_zero_of_mem_mul {i : Z ⟶ Y} {j : Y ⟶ X} [IsImmersion i]
    [IsImmersion j] (C : ConormalChart i j) (k : C.idealY)
    (hk : (k : Γ(X, C.V)) ∈ C.idealY * C.idealZ) :
    (chartGen C).hom (C.idealY.toCotangent k) = 0 :=
  hom_eq_zero_of_mem_mul C.idealY C.idealZ _ (chartGen C)
    (fun b hb _x => smul_eq_zero_of_mem_ker i j _ C.V b hb _) k hk

/-- A section killed by the inverse of an isomorphism of modules is zero.  Stated generically so
that the two large module-category terms it is used at are never unfolded. -/
private theorem eq_zero_of_iso_inv_eq_zero {R : Type u} [Ring R] {M N : ModuleCat.{u} R}
    (A : M ≅ N) {y : N} (h : A.inv.hom y = 0) : y = 0 :=
  (LinearMap.map_eq_zero_iff A.inv.hom
    (Stacks.ConormalSequenceTwoImmersions.injective_iso_inv A)).mp h

/-- A germ of the zero section is zero.  Stated generically for the same reason as
`Stacks.AlgebraicGeometry.RegularIdealSheaf.eq_zero_of_iso_inv_eq_zero`. -/
private theorem germ_zero {T : TopCat.{u}} (F : TopCat.Presheaf AddCommGrpCat.{u} T)
    (U : Opens T) (x : T) (hx : x ∈ U) : F.germ U x hx (0 : F.obj (op U)) = 0 := map_zero _

/-- Equal sections have equal images under a morphism of sheaves of modules. -/
private theorem val_app_congr {Zr : RingedSpace.{u, u}}
    {M N : SheafOfModules.{u} (structureSheafRing Zr)} (f : M ⟶ N) (A : (Opens Zr.carrier)ᵒᵖ)
    {x y : M.val.obj A} (h : x = y) : f.val.app A x = f.val.app A y := congrArg _ h

/-! ### Exactness at the left-hand term -/

/-- **[Stacks Project, Tag 063N]: the conormal sequence of an `H1`-regular immersion is exact at
its left-hand term.** For immersions `Z --i--→ Y --j--→ X` with `i` an `H1`-regular immersion,
the canonical map `i^* C_{Y/X} ⟶ C_{Z/X}` of [Stacks Project, Tag 01R4] is a monomorphism. -/
@[stacks 063N "exactness at the left term: for an H₁-regular immersion `i` the canonical map \
`i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X}` is a monomorphism"]
theorem mono_conormalLeftMap (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j]
    (hi : IsH1RegularImmersion i) : Mono (conormalLeftMap i j) := by
  rw [_root_.AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap]
  intro z
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨V₁, hzV₁, s, hs⟩ :=
    exists_germ_unit i (ClosedImmersion.conormalSheaf j.liftCoborder.toLRSHom.toShHom) z t
  obtain ⟨V, rfl⟩ := exists_preimage_eq j V₁
  have hzU : z ∈ i ⁻¹ᵁ (j ⁻¹ᵁ V) := hzV₁
  have hzX : (i ≫ j) z ∈ V := hzV₁
  have ht' : TopCat.Presheaf.germ
      (ClosedImmersion.conormalSheaf (i ≫ j).liftCoborder.toLRSHom.toShHom).val.presheaf
      (i ⁻¹ᵁ (j ⁻¹ᵁ V)) z hzU
      ((conormalLeftMap i j).val.app (op (i ⁻¹ᵁ (j ⁻¹ᵁ V)))
        (((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
          (ClosedImmersion.conormalSheaf j.liftCoborder.toLRSHom.toShHom)).val.app
          (op (j ⁻¹ᵁ V)) s)) = 0 :=
    (_root_.AlgebraicGeometry.SheafOfModules.stalkMap_germ _ z
        (conormalLeftMap i j) (i ⁻¹ᵁ (j ⁻¹ᵁ V)) hzU _).symm.trans
      ((congrArg (fun y => (_root_.AlgebraicGeometry.SheafOfModules.stalkMap _ z
        (conormalLeftMap i j)).hom y) hs).trans ht)
  obtain ⟨T, hzT, iU, iV, hTeq⟩ := TopCat.Presheaf.germ_eq
    (ClosedImmersion.conormalSheaf (i ≫ j).liftCoborder.toLRSHom.toShHom).val.presheaf z hzU hzU
    ((conormalLeftMap i j).val.app (op (i ⁻¹ᵁ (j ⁻¹ᵁ V)))
      (((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
        (ClosedImmersion.conormalSheaf j.liftCoborder.toLRSHom.toShHom)).val.app
        (op (j ⁻¹ᵁ V)) s)) 0
    (by rw [ht', map_zero])
  obtain ⟨V', hV'⟩ := exists_preimage_eq (i ≫ j) T
  have hzV' : (i ≫ j) z ∈ V' := by
    have h : z ∈ (i ≫ j) ⁻¹ᵁ V' := by rw [hV']; exact hzT
    exact h
  obtain ⟨C, hCV, hCz⟩ := exists_conormalChart i j z (V ⊓ V') ⟨hzX, hzV'⟩
  have hpre : j ⁻¹ᵁ C.V ≤ j ⁻¹ᵁ V := j.preimage_mono (hCV.trans inf_le_left)
  have hprei : i ⁻¹ᵁ (j ⁻¹ᵁ C.V) ≤ i ⁻¹ᵁ (j ⁻¹ᵁ V) := i.preimage_mono hpre
  have hCT : (i ≫ j) ⁻¹ᵁ C.V ≤ T := by
    rw [← hV']
    exact (i ≫ j).preimage_mono (hCV.trans inf_le_right)
  obtain ⟨k, hk⟩ := C.idealY.toCotangent_surjective (C.isoY.hom.hom
    ((ClosedImmersion.conormalSheaf j.liftCoborder.toLRSHom.toShHom).val.map (homOfLE hpre).op s))
  have hk' : C.isoY.inv.hom (C.idealY.toCotangent k) =
      (ClosedImmersion.conormalSheaf j.liftCoborder.toLRSHom.toShHom).val.map
        (homOfLE hpre).op s := by
    rw [hk]
    exact iso_inv_hom_apply C.isoY _
  have hnat := (val_app_naturality
      ((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
        (ClosedImmersion.conormalSheaf j.liftCoborder.toLRSHom.toShHom)) (homOfLE hpre) s).trans
    (val_map_eq_of_subsingleton _
      ((Opens.map i.toLRSHom.toShHom.hom.base).map (homOfLE hpre)) (homOfLE hprei) _)
  have hgen : (chartGen C).hom (C.idealY.toCotangent k) =
      ((modulePullback i.toLRSHom.toShHom).obj
        (ClosedImmersion.conormalSheaf j.liftCoborder.toLRSHom.toShHom)).val.map (homOfLE hprei).op
        (((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
          (ClosedImmersion.conormalSheaf j.liftCoborder.toLRSHom.toShHom)).val.app
          (op (j ⁻¹ᵁ V)) s) :=
    (chartGen_apply C (C.idealY.toCotangent k)).trans
      ((val_app_congr _ (op (j ⁻¹ᵁ C.V)) hk').trans hnat)
  have hx0 : (ClosedImmersion.conormalSheaf (i ≫ j).liftCoborder.toLRSHom.toShHom).val.map iU.op
      ((conormalLeftMap i j).val.app (op (i ⁻¹ᵁ (j ⁻¹ᵁ V)))
        (((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
          (ClosedImmersion.conormalSheaf j.liftCoborder.toLRSHom.toShHom)).val.app
          (op (j ⁻¹ᵁ V)) s)) = 0 :=
    hTeq.trans (map_zero _)
  have hzero : (conormalLeftMap i j).val.app (op ((i ≫ j) ⁻¹ᵁ C.V))
      ((chartGen C).hom (C.idealY.toCotangent k)) = 0 := by
    rw [hgen]
    refine (val_app_naturality (conormalLeftMap i j) (homOfLE hprei) _).trans ?_
    refine (val_map_unique (ClosedImmersion.conormalSheaf (i ≫ j).liftCoborder.toLRSHom.toShHom) iU
      (homOfLE hCT) (homOfLE hprei) _).symm.trans ?_
    exact (val_map_congr (homOfLE hCT) hx0).trans (map_zero _)
  have hzero' : C.isoZ.inv.hom
      (C.idealZ.toCotangent ⟨(k : Γ(X, C.V)), C.idealY_le_idealZ k.2⟩) = 0 :=
    (C.leftMap_unit_toCotangent k).symm.trans
      ((val_app_congr (conormalLeftMap i j) (op ((i ≫ j) ⁻¹ᵁ C.V))
        (chartGen_apply C (C.idealY.toCotangent k)).symm).trans hzero)
  have hsq : (k : Γ(X, C.V)) ∈ C.idealZ ^ 2 :=
    (C.idealZ.toCotangent_eq_zero _).mp (eq_zero_of_iso_inv_eq_zero C.isoZ hzero')
  have hmem : (k : Γ(X, C.V)) ∈ C.idealY * C.idealZ := by
    rw [← chart_inf_sq i j hi C]
    exact ⟨k.2, hsq⟩
  refine hs.symm.trans ((TopCat.Presheaf.germ_res_apply'
    ((modulePullback i.toLRSHom.toShHom).obj
      (ClosedImmersion.conormalSheaf j.liftCoborder.toLRSHom.toShHom)).val.presheaf
      (homOfLE hprei).op z hCz
    _).symm.trans ?_)
  exact (congrArg (fun y => TopCat.Presheaf.germ
      ((modulePullback i.toLRSHom.toShHom).obj
        (ClosedImmersion.conormalSheaf j.liftCoborder.toLRSHom.toShHom)).val.presheaf
      (i ⁻¹ᵁ (j ⁻¹ᵁ C.V)) z hCz y)
    (hgen.symm.trans (chartGen_eq_zero_of_mem_mul C k hmem))).trans
    (germ_zero _ (i ⁻¹ᵁ (j ⁻¹ᵁ C.V)) z hCz)

/-! ### Finite local freeness of the conormal sheaf -/

/-- **The conormal sheaf of an `H1`-regular immersion is finite locally free.** An `H1`-regular
immersion is quasi-regular by [Stacks Project, Tag 063K], and the conormal sheaf of a
quasi-regular immersion is finite locally free by [Stacks Project, Tag 063M] condition (2). -/
theorem isFiniteLocallyFree_conormalSheaf_of_isH1RegularImmersion (i : Z ⟶ Y) [IsImmersion i]
    (hi : IsH1RegularImmersion i) :
    _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (ClosedImmersion.conormalSheaf i.liftCoborder.toLRSHom.toShHom) :=
  isFiniteLocallyFree_conormalSheaf_of_isQuasiRegularImmersion i
    (isQuasiRegularImmersion_of_isH1RegularImmersion i hi)

/-! ### Local splitting -/

/-- **A short exact sequence of sheaves of modules on a space whose right-hand term is finite
locally free admits, near every point, a section of its right-hand map after restriction to a
slice.** On a trivialising open the right-hand term is a retract of a finite free sheaf, so
[Stacks Project, Tag 08C6] lifts the identity through the right-hand map along a covering sieve
of that open. -/
private theorem exists_over_section_of_isFiniteLocallyFree {T : TopCat.{u}}
    {Rt : Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    (S : ShortComplex (_root_.SheafOfModules.{u} Rt)) [Epi S.g]
    [hflf : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₃] (z : T) :
    ∃ V : Opens T, z ∈ V ∧ ∃ σ : S.X₃.over V ⟶ S.X₂.over V, σ ≫ S.g.over V = 𝟙 _ := by
  obtain ⟨q, hq, hqfin⟩ := hflf.exists_isFiniteLocallyFreeData
  obtain ⟨k, hk⟩ := ((Opens.coversTop_iff T q.X).mp q.coversTop).exists_mem z
  have hiso : IsIso (q.generators k).π := hq.isIso k
  have hfin : Finite (q.generators k).I := (hqfin.isFiniteType k).finite
  have hepi : Epi (S.g.over (q.X k)) :=
    Stacks.SheafOfModules.LocalKernel.over_epi S.g (q.X k)
  let ρ : Retract (S.X₃.over (q.X k)) (_root_.SheafOfModules.free (q.generators k).I) :=
    { i := (asIso (q.generators k).π).inv
      r := (q.generators k).π
      retract := (asIso (q.generators k).π).inv_hom_id }
  obtain ⟨Sv, hSv, hlift⟩ :=
    Stacks.StrictlyPerfect.LocalLiftingOverSlice.exists_local_lift
      (𝟙 (S.X₃.over (q.X k))) (S.g.over (q.X k)) ρ
  obtain ⟨V, g, hgS, hzV⟩ := hSv z hk
  obtain ⟨l, hl⟩ := hlift g hgS
  refine ⟨V, hzV, ((_root_.SheafOfModules.overFunctorMap Rt g).app S.X₃).inv ≫ l ≫
    ((_root_.SheafOfModules.overFunctorMap Rt g).app S.X₂).hom, ?_⟩
  have hnat : ((_root_.SheafOfModules.overMap Rt g).map (S.g.over (q.X k))) ≫
      ((_root_.SheafOfModules.overFunctorMap Rt g).app S.X₃).hom =
      ((_root_.SheafOfModules.overFunctorMap Rt g).app S.X₂).hom ≫ S.g.over V :=
    (_root_.SheafOfModules.overFunctorMap Rt g).hom.naturality S.g
  rw [Category.assoc, Category.assoc, ← hnat, ← Category.assoc l, hl,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]

/-! ### Short exactness -/

/-- **[Stacks Project, Tag 063N]: the conormal sequence of an `H1`-regular immersion is short
exact.** For immersions `Z --i--→ Y --j--→ X` with `i` an `H1`-regular immersion, the canonical
sequence `0 ⟶ i^* C_{Y/X} ⟶ C_{Z/X} ⟶ C_{Z/Y} ⟶ 0` of [Stacks Project, Tag 062S] is a short
exact sequence of `O_Z`-modules.

Exactness in the middle and surjectivity on the right are [Stacks Project, Tag 062S]; what
`H1`-regularity of `i` adds is injectivity on the left,
`Stacks.AlgebraicGeometry.RegularIdealSheaf.mono_conormalLeftMap`. -/
@[stacks 063N "exactness: the canonical sequence `0 ⟶ i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0` of \
an H₁-regular immersion is short exact"]
theorem conormalSequence_shortExact (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j]
    (hi : IsH1RegularImmersion i) : (conormalSequenceShortComplex i j).ShortExact where
  exact := conormalSequence_exact i j
  mono_f := mono_conormalLeftMap i j hi
  epi_g := epi_conormalSequenceRightMap i j

/-- **[Stacks Project, Tag 063N]: the conormal sequence of an `H1`-regular immersion is locally
split.** Every point of `Z` has an open neighbourhood over which the short exact sequence
`0 ⟶ i^* C_{Y/X} ⟶ C_{Z/X} ⟶ C_{Z/Y} ⟶ 0` splits, the restriction to an open being the slice
restriction `SheafOfModules.over`. -/
@[stacks 063N "local splitness: on a neighbourhood of every point of `Z` the canonical sequence \
of an H₁-regular immersion splits", ega "IV 16.9.13" "more general", ega "IV 19.1.5" "more general"]
theorem conormalSequence_locallySplit (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j]
    (hi : IsH1RegularImmersion i) (z : Z) :
    ∃ V : Z.Opens, z ∈ V ∧ Nonempty (((conormalSequenceShortComplex i j).map
      (_root_.SheafOfModules.overFunctor
        (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace) V)).Splitting) := by
  have hepi : Epi (conormalSequenceShortComplex i j).g := epi_conormalSequenceRightMap i j
  have hflf : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (conormalSequenceShortComplex i j).X₃ :=
    isFiniteLocallyFree_conormalSheaf_of_isH1RegularImmersion i hi
  obtain ⟨V, hzV, σ, hσ⟩ :=
    exists_over_section_of_isFiniteLocallyFree (conormalSequenceShortComplex i j) z
  have hmap := (conormalSequence_shortExact i j hi).map_of_exact
    (_root_.SheafOfModules.overFunctor (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace) V)
  exact ⟨V, hzV, ⟨ShortComplex.Splitting.ofExactOfSection _ hmap.exact σ hσ hmap.mono_f⟩⟩


end Stacks.AlgebraicGeometry.RegularIdealSheaf

end
