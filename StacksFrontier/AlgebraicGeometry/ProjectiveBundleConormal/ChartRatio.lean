module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartFactor
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartLinearForm
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.ChartHom

/-!
# The pulled-back degree-one section of the chart, carried to the invertible quotient

Clause 3 of [Stacks, Tag 0B3V] has two computations of the same section and this file joins them.

`Stacks.ProjectiveBundleConormal.chartTwistIso_hom_pullbackSection` computes the tautological
section attached to `m : Γ(ℰ, W)` on the **absolute** chart `Proj(Sym_A M)` over an affine open
`W`: it is `SymmetricAlgebra.toTwistSections Γ(X, W) Γ(E, W) m`.
`Stacks.ProjectiveBundleConormal.hom_pullbackSection_tautologicalMap` computes the same section
after pulling back along the **section** `σ` of `π : 𝐏(ℰ) ⟶ X`: it is `q(m)`. The two are
connected by the defining factorization
`Stacks.ProjectiveBundleConormal.chartSection_comp_chartMap`, which says the chart section
`σ|_W : W ⟶ Proj(Sym_A M)` composed with the chart is `σ` on `W`.

**This file transports along that factorization**, so that the pullback along `σ|_W` of
`SymmetricAlgebra.toTwistSections Γ(X, W) Γ(E, W) m` becomes the pullback along `W.ι` of `q(m)`.

## Main results

* `Stacks.ProjectiveBundleConormal.pullback_map_inv_hom_app`: the inverse of an isomorphism of
  modules cancels its forward map after an inverse image, read on a local section.
* `Stacks.ProjectiveBundleConormal.transport_pullbackSection_chartSection`: **the transport.**
* `Stacks.ProjectiveBundleConormal.appLE_eq_awayToSection_of_res_eq_smul`: **a ratio of two
  degree-one sections is the fraction `p/q`**, for an arbitrary morphism into an absolute `Proj`
  and an arbitrary open of its target. Nothing of the chart layer occurs in it.
* `Stacks.ProjectiveBundleConormal.appLE_chartMap_eq_awayToSection_of_res_eq_smul`: **the
  tautological ratio of the chart is `ι m / ι s`**, read across the open immersion
  `Stacks.ProjectiveBundleConormal.chartMap` — the previous result instantiated at the chart.
  This identifies the ratio whose mere existence is
  `Stacks.ProjectiveBundleConormal.exists_tautologicalSectionOver_res_eq_smul`; the identification
  pushed on into `Sym_A(ker p)` is
  `StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartRatioSplit`.

## Implementation notes

**Every comparison is cancelled forwards**, the discipline of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.PullbackTautologicalSection`: the proof is
an `Eq.trans` of `congrArg`s and no `rw` occurs, each structural comparison being turned around by
`Stacks.AlgebraicGeometry.PullbackUnit.natIso_inv_hom_app` or by
`Stacks.ProjectiveBundleConormal.pullback_map_inv_hom_app` rather than by injectivity.

**The slack open of `AlgebraicGeometry.Scheme.Modules.pullbackSection` removes every cast.** The
composite `σ|_W ≫ chartMap` and `W.ι ≫ σ` have the same preimage of `π⁻¹W`, namely `⊤`, and the
inner leg along `σ` is read over `W` itself rather than over `σ⁻¹(π⁻¹W)`; so the five structural
steps are chained with no transport of opens, and the inequalities they ask for are
`AlgebraicGeometry.Scheme.Hom.preimage_top`, `AlgebraicGeometry.Scheme.Opens.ι_preimage_self` and
`Stacks.ProjectiveBundleConormal.preimage_toBase_preimage`.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjDegreeOne (unitSection)
open Stacks.ProjectiveBundleSplitting
open Stacks.SymGraded

universe u

namespace Stacks.ProjectiveBundleConormal

/-- **An isomorphism of modules is cancelled against its inverse after an inverse image**, read
on a local section. This is `Stacks.AlgebraicGeometry.PullbackUnit.natIso_inv_hom_app` for the
image of an isomorphism under `AlgebraicGeometry.Scheme.Modules.pullback`, which is not a natural
isomorphism of functors and so is not covered by that lemma. -/
theorem pullback_map_inv_hom_app {Y Z : Scheme.{u}} (f : Y ⟶ Z) {F G : Z.Modules} (ε : F ≅ G)
    (V : Y.Opens) (x : ((Scheme.Modules.pullback f).obj F).val.obj (op V)) :
    ((Scheme.Modules.pullback f).map ε.inv).val.app (op V)
        (((Scheme.Modules.pullback f).map ε.hom).val.app (op V) x) = x :=
  congrArg
    (fun ρ : (Scheme.Modules.pullback f).obj F ⟶ (Scheme.Modules.pullback f).obj F =>
      ρ.val.app (op V) x)
    (((Scheme.Modules.pullback f).map_comp ε.hom ε.inv).symm.trans
      ((congrArg (Scheme.Modules.pullback f).map ε.hom_inv_id).trans
        ((Scheme.Modules.pullback f).map_id F)))

/-- **Scalar multiplication passes through a morphism of modules**, read on sections over an
open. This is `AlgebraicGeometry.Scheme.Modules.Hom.app_smul` in the `.val.app` spelling that
`AlgebraicGeometry.Scheme.Modules.pullbackSection` produces, where the `Module` instance is not
found by instance search because the type is written `.val.obj (op V)` rather than `Γ(M, V)`. -/
theorem val_app_smul {Y : Scheme.{u}} {M N : Y.Modules} (φ : M ⟶ N) (V : Y.Opens)
    (r : Γ(Y, V)) (x : Γ(M, V)) :
    φ.val.app (op V) ((M.smul r).asHom.hom x) = (N.smul r).asHom.hom (φ.val.app (op V) x) :=
  (φ.val.app (op V)).hom.map_smul r x

/-- **Restricting a section from `W` to the image of the inclusion of `W` is injective**, the two
opens being equal by `AlgebraicGeometry.Scheme.Opens.ι_image_top`: the restriction the other way
round undoes it, both composites being the identity arrow of a single open. -/
theorem val_map_ι_image_top_injective {X : Scheme.{u}} (L : X.Modules) (W : X.Opens) :
    Function.Injective fun a : Γ(L, W) =>
      L.presheaf.map (homOfLE W.ι_image_top.le).op a := by
  have hmap : L.presheaf.map (homOfLE W.ι_image_top.le).op ≫
      L.presheaf.map (homOfLE W.ι_image_top.ge).op = 𝟙 _ := by
    rw [← Functor.map_comp,
      show (homOfLE W.ι_image_top.le).op ≫ (homOfLE W.ι_image_top.ge).op = 𝟙 (op W) from
        Subsingleton.elim _ _, L.presheaf.map_id]
  have hround : ∀ a : Γ(L, W),
      L.presheaf.map (homOfLE W.ι_image_top.ge).op
          (L.presheaf.map (homOfLE W.ι_image_top.le).op a) = a := fun a =>
    ((ConcreteCategory.comp_apply (L.presheaf.map (homOfLE W.ι_image_top.le).op)
          (L.presheaf.map (homOfLE W.ι_image_top.ge).op) a).symm.trans
        (congrArg (fun φ : L.presheaf.obj (op W) ⟶ L.presheaf.obj (op W) =>
          ConcreteCategory.hom φ a) hmap)).trans rfl
  exact fun a₁ a₂ h => ((hround a₁).symm.trans
    (congrArg (fun z => L.presheaf.map (homOfLE W.ι_image_top.ge).op z) h)).trans (hround a₂)

/-- **Pulling a section back along the inclusion of an open is injective.** The comparison of the
inverse image with the restriction carries it to the restriction of the section along
`AlgebraicGeometry.Scheme.Opens.ι_image_top`, which is injective. -/
theorem pullbackSection_ι_injective {X : Scheme.{u}} (L : X.Modules) (W : X.Opens) :
    Function.Injective
      (Scheme.Modules.pullbackSection W.ι L W ⊤ W.ι_preimage_self.ge) := by
  intro a₁ a₂ h
  have key : ∀ a : Γ(L, W),
      ((Scheme.Modules.restrictFunctorIsoPullback W.ι).inv.app L).val.app (op ⊤)
          (Scheme.Modules.pullbackSection W.ι L W ⊤ W.ι_preimage_self.ge a) =
        L.presheaf.map (homOfLE W.ι_image_top.le).op a := fun a =>
    Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection W.ι L W ⊤
      W.ι_preimage_self.ge W.ι_image_top.le a
  exact val_map_ι_image_top_injective L W
    (((key a₁).symm.trans (congrArg
      (((Scheme.Modules.restrictFunctorIsoPullback W.ι).inv.app L).val.app (op ⊤)) h)).trans
      (key a₂))

/-- **A frame cancels a scalar off a pulled-back generator.** If a linear equivalence
`Γ(𝓛, W) ≃ₗ Γ(X, W)` carries `t` to `1` then two functions on `W` acting equally on the pullback
of `t` along the inclusion of `W` are equal.

This is the cancellation that turns the ratio identity of the chart into a value of the chart's
linear form: `AlgebraicGeometry.Scheme.Modules.pullbackSection_smul` moves each scalar back
across the pullback, `Stacks.ProjectiveBundleConormal.pullbackSection_ι_injective` strips the
pullback, and the frame strips `t`. -/
theorem eq_of_smul_pullbackSection_eq {X : Scheme.{u}} {L : X.Modules} {W : X.Opens}
    (frame : Γ(L, W) ≃ₗ[Γ(X, W)] Γ(X, W)) {t : Γ(L, W)} (ht : frame t = 1)
    {r₁ r₂ : Γ((↑W : Scheme.{u}), ⊤)}
    (h : (((Scheme.Modules.pullback W.ι).obj L).smul r₁).asHom.hom
          (Scheme.Modules.pullbackSection W.ι L W ⊤ W.ι_preimage_self.ge t) =
        (((Scheme.Modules.pullback W.ι).obj L).smul r₂).asHom.hom
          (Scheme.Modules.pullbackSection W.ι L W ⊤ W.ι_preimage_self.ge t)) :
    r₁ = r₂ := by
  have hsurj := (ConcreteCategory.bijective_of_isIso
    (W.ι.appLE W ⊤ W.ι_preimage_self.ge)).surjective
  obtain ⟨c₁, rfl⟩ := hsurj r₁
  obtain ⟨c₂, rfl⟩ := hsurj r₂
  rw [← Scheme.Modules.pullbackSection_smul, ← Scheme.Modules.pullbackSection_smul] at h
  have hsm := congrArg frame (pullbackSection_ι_injective L W h)
  rw [map_smul, map_smul, ht, smul_eq_mul, smul_eq_mul, mul_one, mul_one] at hsm
  rw [hsm]

/-! ### The ratio of two degree-one sections, transported across a morphism into `Proj` -/

section DegreeOneRatio

variable {S : Type u} [CommRing S] {τ : Type u} [SetLike τ S] [AddSubgroupClass τ S]
  (𝒮 : ℕ → τ) [GradedRing 𝒮]

/-- **A ratio of two degree-one sections is the fraction `p/q`, read across an open immersion.**

Let `f : Proj 𝒮 ⟶ Y` be a morphism of schemes carrying an invertible module `F` on `Y` whose
pullback is `𝒪(1)`, the comparison `ε` taking the pulled-back sections `tp`, `tq` of `F` over an
open `T` to the degree-one sections of two degree-one elements `p`, `q`. Suppose that over some
open `U ≤ T` the restriction of `tp` is a function `g` times the restriction of `tq`. Then
`f` carries `g` to the degree-zero fraction `p/q`, read on `D₊(q)` through
`AlgebraicGeometry.Proj.awayToSection`.

**This is the identification of a ratio that is only known to exist.** A consumer holding an
invertible `F` knows that one of its sections is a function times another on the locus where the
latter generates, with nothing said about the function; this says the function is `p/q` once the
two sections are the degree-one sections of `p` and `q`. The ratio identity
`Stacks.TwistPullbackRatio.degreeSection_res_eq` on the absolute `Proj` is what supplies the
right-hand side, and the uniqueness half of [Stacks, Tag 01MS]
(`Stacks.AlgebraicGeometry.ProjDegreeOneTriv.bijective_smul_degreeOneSection`) is what cancels
`degreeSection 𝒮 1 q` off both.

**Everything is a variable.** No chart datum appears: `f`, `F`, `ε`, the two sections and the
three inclusions of opens are parameters, and the only opens mentioned are `⊤` and `D₊(q)`. That
is what makes the statement affordable — a consumer instantiates it and the elaborator never has
to compare an explicit composite against this proof term's type
(`Stacks.ProjectiveBundleConormal.appLE_chartMap_eq_awayToSection_of_res_eq_smul` is that
instantiation, and costs nothing). -/
theorem appLE_eq_awayToSection_of_res_eq_smul {Y : Scheme.{u}} {p q : S} (hp : p ∈ 𝒮 1)
    (hq : q ∈ 𝒮 1) (f : AlgebraicGeometry.Proj 𝒮 ⟶ Y) (F : Y.Modules)
    (ε : (Scheme.Modules.pullback f).obj F ≅ Stacks.TwistPullbackRatio.O1 𝒮)
    {T : Y.Opens} (hT : (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens) ≤ f ⁻¹ᵁ T)
    (tp tq : Γ(F, T))
    (hεp : ε.hom.val.app (op ⊤) (Scheme.Modules.pullbackSection f F T ⊤ hT tp) =
      degreeSection 𝒮 1 ⟨p, hp⟩)
    (hεq : ε.hom.val.app (op ⊤) (Scheme.Modules.pullbackSection f F T ⊤ hT tq) =
      degreeSection 𝒮 1 ⟨q, hq⟩)
    {U : Y.Opens} (hUT : U ≤ T)
    (hDU : AlgebraicGeometry.Proj.basicOpen 𝒮 q ≤ f ⁻¹ᵁ U) (g : Γ(Y, U))
    (hg : F.presheaf.map (homOfLE hUT).op tp =
      (F.smul g).asHom.hom (F.presheaf.map (homOfLE hUT).op tq)) :
    f.appLE U (AlgebraicGeometry.Proj.basicOpen 𝒮 q) hDU g =
      (AlgebraicGeometry.Proj.awayToSection 𝒮 q).hom
        (HomogeneousLocalization.Away.mk 𝒮 hq 1 p (by simpa using hp)) := by
  have hpull : ∀ t : Γ(F, T),
      Scheme.Modules.pullbackSection f F U (AlgebraicGeometry.Proj.basicOpen 𝒮 q) hDU
          (F.presheaf.map (homOfLE hUT).op t) =
        ((Scheme.Modules.pullback f).obj F).presheaf.map
            (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen 𝒮 q))).op
          (Scheme.Modules.pullbackSection f F T ⊤ hT t) := fun t =>
    (Scheme.Modules.pullbackSection_res f F hUT (AlgebraicGeometry.Proj.basicOpen 𝒮 q) hDU
        t).trans
      (pullbackSection_res_target f F
        (le_top (a := AlgebraicGeometry.Proj.basicOpen 𝒮 q)) hT _ t).symm
  have key := (hpull tp).symm.trans
    ((congrArg
        (Scheme.Modules.pullbackSection f F U (AlgebraicGeometry.Proj.basicOpen 𝒮 q) hDU)
        hg).trans
      ((Scheme.Modules.pullbackSection_smul f F U (AlgebraicGeometry.Proj.basicOpen 𝒮 q) hDU g
            (F.presheaf.map (homOfLE hUT).op tq)).trans
        (congrArg
          (fun z => (((Scheme.Modules.pullback f).obj F).smul
              (f.appLE U (AlgebraicGeometry.Proj.basicOpen 𝒮 q) hDU g)).asHom.hom z)
          (hpull tq))))
  have hnat : ∀ t : Γ(F, T),
      ε.hom.val.app (op (AlgebraicGeometry.Proj.basicOpen 𝒮 q))
          (((Scheme.Modules.pullback f).obj F).presheaf.map
            (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen 𝒮 q))).op
            (Scheme.Modules.pullbackSection f F T ⊤ hT t)) =
        (Stacks.TwistPullbackRatio.O1 𝒮).presheaf.map
          (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen 𝒮 q))).op
          (ε.hom.val.app (op ⊤) (Scheme.Modules.pullbackSection f F T ⊤ hT t)) := fun t =>
    PresheafOfModules.naturality_apply ε.hom.val
      (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen 𝒮 q))).op _
  have step : (Stacks.TwistPullbackRatio.O1 𝒮).presheaf.map
          (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen 𝒮 q))).op
          (degreeSection 𝒮 1 ⟨p, hp⟩) =
      ((Stacks.TwistPullbackRatio.O1 𝒮).smul
            (f.appLE U (AlgebraicGeometry.Proj.basicOpen 𝒮 q) hDU g)).asHom.hom
        ((Stacks.TwistPullbackRatio.O1 𝒮).presheaf.map
          (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen 𝒮 q))).op
          (degreeSection 𝒮 1 ⟨q, hq⟩)) :=
    (congrArg
          ((Stacks.TwistPullbackRatio.O1 𝒮).presheaf.map
            (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen 𝒮 q))).op)
          hεp).symm.trans
      (((hnat tp).symm.trans
          ((congrArg (ε.hom.val.app (op (AlgebraicGeometry.Proj.basicOpen 𝒮 q))) key).trans
            ((val_app_smul ε.hom (AlgebraicGeometry.Proj.basicOpen 𝒮 q)
                  (f.appLE U (AlgebraicGeometry.Proj.basicOpen 𝒮 q) hDU g) _).trans
              (congrArg
                (fun z => ((Stacks.TwistPullbackRatio.O1 𝒮).smul
                    (f.appLE U (AlgebraicGeometry.Proj.basicOpen 𝒮 q) hDU g)).asHom.hom z)
                (hnat tq))))).trans
        (congrArg
          (fun z => ((Stacks.TwistPullbackRatio.O1 𝒮).smul
              (f.appLE U (AlgebraicGeometry.Proj.basicOpen 𝒮 q) hDU g)).asHom.hom
            ((Stacks.TwistPullbackRatio.O1 𝒮).presheaf.map
              (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen 𝒮 q))).op z))
          hεq))
  exact (Stacks.AlgebraicGeometry.ProjDegreeOneTriv.bijective_smul_degreeOneSection 𝒮 hq
      (W := AlgebraicGeometry.Proj.basicOpen 𝒮 q) le_rfl).injective
    (step.symm.trans (Stacks.TwistPullbackRatio.degreeSection_res_eq 𝒮 hp hq))

end DegreeOneRatio

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  (Q : Stacks.Divisors.InvertibleQuotient X E)
  {σ : X ⟶ (bundle E).scheme} (hσ : σ ≫ (bundle E).toBase = 𝟙 X)
  (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
  (hqe : (Scheme.Modules.pullbackId X).inv.app E ≫
    (Scheme.Modules.pullbackCongr hσ).inv.app E ≫
      (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app E ≫
        (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom = Q.q)
  {W : X.Opens} (hW : IsAffineOpen W)

include hσ in
/-- **The chart section carries everything into the chart.** This is
`AlgebraicGeometry.Scheme.Hom.preimage_top` at
`Stacks.ProjectiveBundleConormal.chartSection`, named so that the transport below can quote it. -/
theorem top_le_chartSection_preimage_top :
    (⊤ : (↑W : Scheme.{u}).Opens) ≤ chartSection E hW hσ ⁻¹ᵁ
      (⊤ : (AlgebraicGeometry.Proj (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))).Opens) :=
  (Scheme.Hom.preimage_top (chartSection E hW hσ)).ge

include hσ in
/-- **The chart section, composed with the chart, meets `π⁻¹W` on all of `W`.** The chart does so
by `Stacks.ProjectiveBundleConormal.top_le_chartMap_preimage`, and a preimage only grows. -/
theorem top_le_chartSection_comp_chartMap_preimage :
    (⊤ : (↑W : Scheme.{u}).Opens) ≤
      (chartSection E hW hσ ≫ chartMap E (symPieces E) hW) ⁻¹ᵁ ((bundle E).toBase ⁻¹ᵁ W) :=
  fun x _ =>
    top_le_chartMap_preimage E (symPieces E) hW (x := (chartSection E hW hσ).base x) trivial

include hσ in
/-- **`σ` on `W`, composed into the bundle, meets `π⁻¹W` on all of `W`.** This is the same
inequality as `Stacks.ProjectiveBundleConormal.top_le_chartSection_comp_chartMap_preimage`, the
two morphisms being equal by
`Stacks.ProjectiveBundleConormal.chartSection_comp_chartMap`; it is stated separately because
`AlgebraicGeometry.Scheme.Modules.pullbackSection_congr` asks for one inequality for each side. -/
theorem top_le_ι_comp_section_preimage :
    (⊤ : (↑W : Scheme.{u}).Opens) ≤ (W.ι ≫ σ) ⁻¹ᵁ ((bundle E).toBase ⁻¹ᵁ W) :=
  fun x _ => le_preimage_toBase_preimage E hσ x.2

include hσ e hqe in
/-- **The transport of the tautological section from the chart to the section.** The pullback
along the chart section `σ|_W` of the canonical degree-one section
`SymmetricAlgebra.toTwistSections Γ(X, W) Γ(E, W) m`, read back through the twist comparison
`Stacks.ProjectiveBundleConormal.chartTwistIso` and the three structural comparisons supplied by
`Stacks.ProjectiveBundleConormal.chartSection_comp_chartMap`, is the pullback along the inclusion
of `W` of `q(m)`.

This is the join of the two halves of clause 3 of [Stacks, Tag 0B3V]: the left-hand side is what
`Stacks.ProjectiveBundleConormal.chartTwistIso_hom_pullbackSection` computes on the absolute chart
and the right-hand side is what
`Stacks.ProjectiveBundleConormal.hom_pullbackSection_tautologicalMap` computes from the
classifying hypothesis, so with it the ratio identity
`Stacks.TwistPullbackRatio.pullbackSection_degreeSection_eq_smul` of the chart becomes an identity
about `q`. -/
theorem transport_pullbackSection_chartSection (m : Γ(E, W)) :
    ((Scheme.Modules.pullback W.ι).map e.hom).val.app (op ⊤)
        (((Scheme.Modules.pullbackComp W.ι σ).inv.app
              (tautologicalTwist E (symPieces E))).val.app (op ⊤)
          (((Scheme.Modules.pullbackCongr
                (chartSection_comp_chartMap E hW hσ)).hom.app
                (tautologicalTwist E (symPieces E))).val.app (op ⊤)
            (((Scheme.Modules.pullbackComp (chartSection E hW hσ)
                  (chartMap E (symPieces E) hW)).hom.app
                  (tautologicalTwist E (symPieces E))).val.app (op ⊤)
              (((Scheme.Modules.pullback (chartSection E hW hσ)).map
                    (chartTwistIso E (symPieces E) hW).inv).val.app (op ⊤)
                (Scheme.Modules.pullbackSection (chartSection E hW hσ)
                  (twistingSheaf (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)) (1 : ℤ)) ⊤ ⊤
                  (top_le_chartSection_preimage_top E hσ hW)
                  (SymmetricAlgebra.toTwistSections Γ(X, W) Γ(E, W) m)))))) =
      Scheme.Modules.pullbackSection W.ι Q.L W ⊤ W.ι_preimage_self.ge (Q.q.app W m) := by
  have hT := chartTwistIso_hom_pullbackSection E (symPieces E) hW m
  have h₁ :
      ((Scheme.Modules.pullback (chartSection E hW hσ)).map
            (chartTwistIso E (symPieces E) hW).inv).val.app (op ⊤)
          (Scheme.Modules.pullbackSection (chartSection E hW hσ)
            (twistingSheaf (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)) (1 : ℤ)) ⊤ ⊤
            (top_le_chartSection_preimage_top E hσ hW)
            (SymmetricAlgebra.toTwistSections Γ(X, W) Γ(E, W) m)) =
        Scheme.Modules.pullbackSection (chartSection E hW hσ)
          ((Scheme.Modules.pullback (chartMap E (symPieces E) hW)).obj
            (tautologicalTwist E (symPieces E))) ⊤ ⊤
          (top_le_chartSection_preimage_top E hσ hW)
          (Scheme.Modules.pullbackSection (chartMap E (symPieces E) hW)
            (tautologicalTwist E (symPieces E)) ((bundle E).toBase ⁻¹ᵁ W) ⊤
            (top_le_chartMap_preimage E (symPieces E) hW)
            (tautologicalSectionOver E W m)) :=
    (congrArg
        (fun z => ((Scheme.Modules.pullback (chartSection E hW hσ)).map
              (chartTwistIso E (symPieces E) hW).inv).val.app (op ⊤)
            (Scheme.Modules.pullbackSection (chartSection E hW hσ)
              (twistingSheaf (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)) (1 : ℤ)) ⊤ ⊤
              (top_le_chartSection_preimage_top E hσ hW) z))
        hT.symm).trans
      ((congrArg
          (((Scheme.Modules.pullback (chartSection E hW hσ)).map
            (chartTwistIso E (symPieces E) hW).inv).val.app (op ⊤))
          (Scheme.Modules.pullbackSection_naturality (chartSection E hW hσ)
            (chartTwistIso E (symPieces E) hW).hom ⊤ ⊤
            (top_le_chartSection_preimage_top E hσ hW) _).symm).trans
        (pullback_map_inv_hom_app (chartSection E hW hσ)
          (chartTwistIso E (symPieces E) hW) ⊤ _))
  have h₂ := Scheme.Modules.pullbackSection_comp (chartSection E hW hσ)
    (chartMap E (symPieces E) hW) (tautologicalTwist E (symPieces E))
    ((bundle E).toBase ⁻¹ᵁ W) ⊤ ⊤
    (top_le_chartMap_preimage E (symPieces E) hW)
    (top_le_chartSection_preimage_top E hσ hW)
    (top_le_chartSection_comp_chartMap_preimage E hσ hW)
    (tautologicalSectionOver E W m)
  have h₃ := Scheme.Modules.pullbackSection_congr (chartSection_comp_chartMap E hW hσ)
    (tautologicalTwist E (symPieces E)) ((bundle E).toBase ⁻¹ᵁ W) ⊤
    (top_le_chartSection_comp_chartMap_preimage E hσ hW)
    (top_le_ι_comp_section_preimage E hσ)
    (tautologicalSectionOver E W m)
  have h₄ :
      ((Scheme.Modules.pullbackComp W.ι σ).inv.app
            (tautologicalTwist E (symPieces E))).val.app (op ⊤)
          (Scheme.Modules.pullbackSection (W.ι ≫ σ) (tautologicalTwist E (symPieces E))
            ((bundle E).toBase ⁻¹ᵁ W) ⊤ (top_le_ι_comp_section_preimage E hσ)
            (tautologicalSectionOver E W m)) =
        Scheme.Modules.pullbackSection W.ι
          ((Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E))) W ⊤
          W.ι_preimage_self.ge
          (Scheme.Modules.pullbackSection σ (tautologicalTwist E (symPieces E))
            ((bundle E).toBase ⁻¹ᵁ W) W (preimage_toBase_preimage E hσ W).ge
            (tautologicalSectionOver E W m)) :=
    (congrArg
        (((Scheme.Modules.pullbackComp W.ι σ).inv.app
          (tautologicalTwist E (symPieces E))).val.app (op ⊤))
        (Scheme.Modules.pullbackSection_comp W.ι σ (tautologicalTwist E (symPieces E))
          ((bundle E).toBase ⁻¹ᵁ W) W ⊤ (preimage_toBase_preimage E hσ W).ge
          W.ι_preimage_self.ge (top_le_ι_comp_section_preimage E hσ)
          (tautologicalSectionOver E W m)).symm).trans
      (Stacks.AlgebraicGeometry.PullbackUnit.natIso_inv_hom_app
        (Scheme.Modules.pullbackComp W.ι σ) (tautologicalTwist E (symPieces E)) ⊤ _)
  have h₅ := Scheme.Modules.pullbackSection_naturality W.ι e.hom W ⊤ W.ι_preimage_self.ge
    (Scheme.Modules.pullbackSection σ (tautologicalTwist E (symPieces E))
      ((bundle E).toBase ⁻¹ᵁ W) W (preimage_toBase_preimage E hσ W).ge
      (tautologicalSectionOver E W m))
  have h₆ := hom_pullbackSection_tautologicalMap E Q hσ e hqe W m
  exact (congrArg
      (fun z => ((Scheme.Modules.pullback W.ι).map e.hom).val.app (op ⊤)
        (((Scheme.Modules.pullbackComp W.ι σ).inv.app
              (tautologicalTwist E (symPieces E))).val.app (op ⊤)
          (((Scheme.Modules.pullbackCongr
                (chartSection_comp_chartMap E hW hσ)).hom.app
                (tautologicalTwist E (symPieces E))).val.app (op ⊤)
            (((Scheme.Modules.pullbackComp (chartSection E hW hσ)
                  (chartMap E (symPieces E) hW)).hom.app
                  (tautologicalTwist E (symPieces E))).val.app (op ⊤) z))))
      h₁).trans
    ((congrArg
        (fun z => ((Scheme.Modules.pullback W.ι).map e.hom).val.app (op ⊤)
          (((Scheme.Modules.pullbackComp W.ι σ).inv.app
                (tautologicalTwist E (symPieces E))).val.app (op ⊤)
            (((Scheme.Modules.pullbackCongr
                  (chartSection_comp_chartMap E hW hσ)).hom.app
                  (tautologicalTwist E (symPieces E))).val.app (op ⊤) z)))
        h₂).trans
      ((congrArg
          (fun z => ((Scheme.Modules.pullback W.ι).map e.hom).val.app (op ⊤)
            (((Scheme.Modules.pullbackComp W.ι σ).inv.app
              (tautologicalTwist E (symPieces E))).val.app (op ⊤) z))
          h₃).trans
        ((congrArg
            (fun z => ((Scheme.Modules.pullback W.ι).map e.hom).val.app (op ⊤) z)
            h₄).trans
          (h₅.trans
            (congrArg
              (Scheme.Modules.pullbackSection W.ι Q.L W ⊤ W.ι_preimage_self.ge) h₆)))))

/-! ### The transport as a single morphism -/

/-- **The transport of `Stacks.ProjectiveBundleConormal.transport_pullbackSection_chartSection`,
packaged as one morphism of modules on `W`**: the twist comparison of the chart, the three
structural comparisons supplied by
`Stacks.ProjectiveBundleConormal.chartSection_comp_chartMap`, and the classifying isomorphism `e`.

Packaging the five factors is what lets a scalar pass through the whole transport by a single
application of `Stacks.ProjectiveBundleConormal.val_app_smul`, rather than five. -/
def chartTwistTransport :
    (Scheme.Modules.pullback (chartSection E hW hσ)).obj
        (twistingSheaf (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)) (1 : ℤ)) ⟶
      (Scheme.Modules.pullback W.ι).obj Q.L :=
  (Scheme.Modules.pullback (chartSection E hW hσ)).map
      (chartTwistIso E (symPieces E) hW).inv ≫
    (Scheme.Modules.pullbackComp (chartSection E hW hσ)
        (chartMap E (symPieces E) hW)).hom.app (tautologicalTwist E (symPieces E)) ≫
      (Scheme.Modules.pullbackCongr (chartSection_comp_chartMap E hW hσ)).hom.app
          (tautologicalTwist E (symPieces E)) ≫
        (Scheme.Modules.pullbackComp W.ι σ).inv.app (tautologicalTwist E (symPieces E)) ≫
          (Scheme.Modules.pullback W.ι).map e.hom

include hσ e hqe in
/-- **The transport, read through the packaged morphism.** This is
`Stacks.ProjectiveBundleConormal.transport_pullbackSection_chartSection` restated at
`Stacks.ProjectiveBundleConormal.chartTwistTransport`; the composite of morphisms of modules acts
on a section as the composite of the actions, so the two statements are definitionally the
same. -/
theorem chartTwistTransport_pullbackSection (m : Γ(E, W)) :
    (chartTwistTransport E Q hσ e hW).val.app (op ⊤)
        (Scheme.Modules.pullbackSection (chartSection E hW hσ)
          (twistingSheaf (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)) (1 : ℤ)) ⊤ ⊤
          (top_le_chartSection_preimage_top E hσ hW)
          (SymmetricAlgebra.toTwistSections Γ(X, W) Γ(E, W) m)) =
      Scheme.Modules.pullbackSection W.ι Q.L W ⊤ W.ι_preimage_self.ge (Q.q.app W m) :=
  transport_pullbackSection_chartSection E Q hσ e hqe hW m

/-! ### The ratio identity in the vocabulary of the chart's linear form -/

/-- **The canonical degree-one section of `m` is the degree-one section of `ι m`.** The two are
the same term: `SymmetricAlgebra.toTwistSections` is
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection` at `SymmetricAlgebra.toGradingOne`,
whose underlying element is `ι m` by `SymmetricAlgebra.coe_toGradingOne`.

It is recorded as an equation because the ratio identity
`Stacks.TwistPullbackRatio.pullbackSection_degreeSection_eq_smul` is phrased with
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection` while the transport above is phrased
with `SymmetricAlgebra.toTwistSections`; joining the two inside a rewrite, by letting the
elaborator discover the identity definitionally, makes it unfold the sheaf of modules. -/
theorem toTwistSections_eq_degreeSection {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M]
    [Module A M] (m : M) :
    SymmetricAlgebra.toTwistSections A M m =
      degreeSection (SymmetricAlgebra.grading A M) 1
        ⟨SymmetricAlgebra.ι A M m, SymmetricAlgebra.ι_mem_grading_one m⟩ :=
  congrArg (degreeSection (SymmetricAlgebra.grading A M) 1)
    (Subtype.ext (SymmetricAlgebra.coe_toGradingOne A M m))

omit [SheafOfModules.IsQuasicoherent E] in
/-- **A section of `ℰ` is its linear form times the frame section, after `q`.** If the chart's
linear form takes the value `1` at `s` then `q(m) = p(m)·q(s)` for every `m`: the frame is
injective and carries both sides to `p(m)`. -/
theorem app_eq_chartLinearForm_smul (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W)) (s m : Γ(E, W))
    (hs : chartLinearForm Q W eL s = 1) :
    Q.q.app W m = chartLinearForm Q W eL m • Q.q.app W s := by
  apply eL.injective
  have hs' : eL (Q.q.app W s) = 1 := hs
  rw [map_smul, hs', smul_eq_mul, mul_one]
  rfl

/-- **The ratio identity on the chart section, in the vocabulary of the transport.** For a
chart section landing in the standard open `D₊(ι s)`, the pullback of the canonical degree-one
section of `m` is the chart homomorphism's value at `ι m / ι s` times the pullback of the
canonical degree-one section of `s`.

This is `Stacks.TwistPullbackRatio.pullbackSection_degreeSection_eq_smul` read over `⊤` by
`AlgebraicGeometry.Scheme.Modules.pullbackSection_res` and spelled with
`SymmetricAlgebra.toTwistSections` by
`Stacks.ProjectiveBundleConormal.toTwistSections_eq_degreeSection`, which is the vocabulary
`Stacks.ProjectiveBundleConormal.chartTwistTransport_pullbackSection` consumes. -/
theorem pullbackSection_chartSection_ratio (s m : Γ(E, W))
    (hg : chartSection E hW hσ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
      (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
      (SymmetricAlgebra.ι Γ(X, W) Γ(E, W) s) = ⊤) :
    Scheme.Modules.pullbackSection (chartSection E hW hσ)
        (twistingSheaf (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)) (1 : ℤ)) ⊤ ⊤
        (top_le_chartSection_preimage_top E hσ hW)
        (SymmetricAlgebra.toTwistSections Γ(X, W) Γ(E, W) m) =
      (((Scheme.Modules.pullback (chartSection E hW hσ)).obj
            (twistingSheaf (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)) (1 : ℤ))).smul
          ((Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.chartHomEquiv
                (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
                (SymmetricAlgebra.ι_mem_grading_one s) Nat.one_pos (↑W : Scheme.{u})
                ⟨chartSection E hW hσ, hg⟩).hom
            (HomogeneousLocalization.Away.mk (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
              (SymmetricAlgebra.ι_mem_grading_one s) 1
              (SymmetricAlgebra.ι Γ(X, W) Γ(E, W) m)
              (SymmetricAlgebra.ι_mem_grading_smul m)))).asHom.hom
        (Scheme.Modules.pullbackSection (chartSection E hW hσ)
          (twistingSheaf (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)) (1 : ℤ)) ⊤ ⊤
          (top_le_chartSection_preimage_top E hσ hW)
          (SymmetricAlgebra.toTwistSections Γ(X, W) Γ(E, W) s)) := by
  have hbr : ∀ k : Γ(E, W),
      Scheme.Modules.pullbackSection (chartSection E hW hσ)
          (twistingSheaf (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)) (1 : ℤ)) ⊤ ⊤
          (top_le_chartSection_preimage_top E hσ hW)
          (SymmetricAlgebra.toTwistSections Γ(X, W) Γ(E, W) k) =
        Scheme.Modules.pullbackSection (chartSection E hW hσ)
          (Stacks.TwistPullbackRatio.O1 (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)))
          (AlgebraicGeometry.Proj.basicOpen (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
            (SymmetricAlgebra.ι Γ(X, W) Γ(E, W) s)) ⊤ hg.ge
          ((Stacks.TwistPullbackRatio.O1
              (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))).presheaf.map
            (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen
              (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
              (SymmetricAlgebra.ι Γ(X, W) Γ(E, W) s)))).op
            (degreeSection (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)) 1
              ⟨SymmetricAlgebra.ι Γ(X, W) Γ(E, W) k,
                SymmetricAlgebra.ι_mem_grading_one k⟩)) := fun k =>
    (congrArg
        (Scheme.Modules.pullbackSection (chartSection E hW hσ)
          (twistingSheaf (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)) (1 : ℤ)) ⊤ ⊤
          (top_le_chartSection_preimage_top E hσ hW))
        (toTwistSections_eq_degreeSection k)).trans
      (Scheme.Modules.pullbackSection_res (chartSection E hW hσ)
        (Stacks.TwistPullbackRatio.O1 (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)))
        (le_top (a := AlgebraicGeometry.Proj.basicOpen
          (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
          (SymmetricAlgebra.ι Γ(X, W) Γ(E, W) s))) ⊤ hg.ge
        (degreeSection (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)) 1
          ⟨SymmetricAlgebra.ι Γ(X, W) Γ(E, W) k,
            SymmetricAlgebra.ι_mem_grading_one k⟩)).symm
  exact (hbr m).trans
    ((Stacks.TwistPullbackRatio.pullbackSection_degreeSection_eq_smul
          (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)) (SymmetricAlgebra.ι_mem_grading_one m)
          (SymmetricAlgebra.ι_mem_grading_one s) (chartSection E hW hσ) hg).trans
      (congrArg
        (fun z => (((Scheme.Modules.pullback (chartSection E hW hσ)).obj
              (twistingSheaf (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)) (1 : ℤ))).smul
            ((Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.chartHomEquiv
                  (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
                  (SymmetricAlgebra.ι_mem_grading_one s) Nat.one_pos (↑W : Scheme.{u})
                  ⟨chartSection E hW hσ, hg⟩).hom
              (HomogeneousLocalization.Away.mk (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
                (SymmetricAlgebra.ι_mem_grading_one s) 1
                (SymmetricAlgebra.ι Γ(X, W) Γ(E, W) m)
                (SymmetricAlgebra.ι_mem_grading_smul m)))).asHom.hom z)
        (hbr s).symm))

include hσ e hqe in
/-- **The ratio identity carried to the invertible quotient.** The pullback along the inclusion
of `W` of `q(m)` is the chart homomorphism's value at `ι m / ι s` times the pullback of `q(s)`.

This is `Stacks.ProjectiveBundleConormal.pullbackSection_chartSection_ratio` pushed through the
packaged transport `Stacks.ProjectiveBundleConormal.chartTwistTransport`, whose action on the
two canonical degree-one sections
`Stacks.ProjectiveBundleConormal.chartTwistTransport_pullbackSection` computes and through which
the scalar passes by `Stacks.ProjectiveBundleConormal.val_app_smul`. -/
theorem pullbackSection_app_eq_smul (s m : Γ(E, W))
    (hg : chartSection E hW hσ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
      (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
      (SymmetricAlgebra.ι Γ(X, W) Γ(E, W) s) = ⊤) :
    Scheme.Modules.pullbackSection W.ι Q.L W ⊤ W.ι_preimage_self.ge (Q.q.app W m) =
      (((Scheme.Modules.pullback W.ι).obj Q.L).smul
          ((Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.chartHomEquiv
                (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
                (SymmetricAlgebra.ι_mem_grading_one s) Nat.one_pos (↑W : Scheme.{u})
                ⟨chartSection E hW hσ, hg⟩).hom
            (HomogeneousLocalization.Away.mk (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
              (SymmetricAlgebra.ι_mem_grading_one s) 1
              (SymmetricAlgebra.ι Γ(X, W) Γ(E, W) m)
              (SymmetricAlgebra.ι_mem_grading_smul m)))).asHom.hom
        (Scheme.Modules.pullbackSection W.ι Q.L W ⊤ W.ι_preimage_self.ge (Q.q.app W s)) :=
  (chartTwistTransport_pullbackSection E Q hσ e hqe hW m).symm.trans
    ((congrArg ((chartTwistTransport E Q hσ e hW).val.app (op ⊤))
          (pullbackSection_chartSection_ratio E hσ hW s m hg)).trans
      ((val_app_smul (chartTwistTransport E Q hσ e hW) ⊤
            ((Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.chartHomEquiv
                  (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
                  (SymmetricAlgebra.ι_mem_grading_one s) Nat.one_pos (↑W : Scheme.{u})
                  ⟨chartSection E hW hσ, hg⟩).hom
              (HomogeneousLocalization.Away.mk (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
                (SymmetricAlgebra.ι_mem_grading_one s) 1
                (SymmetricAlgebra.ι Γ(X, W) Γ(E, W) m)
                (SymmetricAlgebra.ι_mem_grading_smul m)))
            (Scheme.Modules.pullbackSection (chartSection E hW hσ)
              (twistingSheaf (SymmetricAlgebra.grading Γ(X, W) Γ(E, W)) (1 : ℤ)) ⊤ ⊤
              (top_le_chartSection_preimage_top E hσ hW)
              (SymmetricAlgebra.toTwistSections Γ(X, W) Γ(E, W) s))).trans
        (congrArg
          (fun z => (((Scheme.Modules.pullback W.ι).obj Q.L).smul
              ((Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.chartHomEquiv
                    (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
                    (SymmetricAlgebra.ι_mem_grading_one s) Nat.one_pos (↑W : Scheme.{u})
                    ⟨chartSection E hW hσ, hg⟩).hom
                (HomogeneousLocalization.Away.mk (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
                  (SymmetricAlgebra.ι_mem_grading_one s) 1
                  (SymmetricAlgebra.ι Γ(X, W) Γ(E, W) m)
                  (SymmetricAlgebra.ι_mem_grading_smul m)))).asHom.hom z)
          (chartTwistTransport_pullbackSection E Q hσ e hqe hW s))))

include hσ e hqe in
/-- **The degree-one ratio of the chart section is the chart's linear form.** Let `W` be an
affine open carrying a frame `eL` for `𝓛` and a section `s` of `ℰ` at which the chart's linear
form `p = eL ∘ q` takes the value `1`, so that the chart section `σ|_W` factors through the
standard open `D₊(ι s)`. Then the chart homomorphism of `σ|_W` carries the degree-one ratio
`ι m / ι s` to `p(m)`.

This is the computation clause 3 of [Stacks, Tag 0B3V] turns on: it says the point of the affine
bundle `𝐀(ker p)` named by `σ|_W` has every affine coordinate `ι k / ι s`, `k ∈ ker p`, equal to
zero — i.e. that it is the zero section, which is what
`Stacks.ProjectiveBundleConormal.splitChartOrigin_mk_ι` says on the other side.

The proof is the ratio identity
`Stacks.ProjectiveBundleConormal.pullbackSection_app_eq_smul`, cancelled against the frame by
`Stacks.ProjectiveBundleConormal.eq_of_smul_pullbackSection_eq`. -/
theorem chartHomEquiv_chartSection_mk_ι (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W)) (s m : Γ(E, W))
    (hs : chartLinearForm Q W eL s = 1) :
    (Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.chartHomEquiv
          (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
          (SymmetricAlgebra.ι_mem_grading_one s) Nat.one_pos (↑W : Scheme.{u})
          ⟨chartSection E hW hσ,
            chartSection_preimage_basicOpen_eq_top E Q hσ e hqe hW s
              (span_singleton_app_eq_top_of_chartLinearForm_eq_one Q W eL hs)⟩).hom
        (HomogeneousLocalization.Away.mk (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
          (SymmetricAlgebra.ι_mem_grading_one s) 1
          (SymmetricAlgebra.ι Γ(X, W) Γ(E, W) m)
          (SymmetricAlgebra.ι_mem_grading_smul m)) =
      W.ι.appLE W ⊤ W.ι_preimage_self.ge (chartLinearForm Q W eL m) :=
  eq_of_smul_pullbackSection_eq eL (t := Q.q.app W s) hs
    ((pullbackSection_app_eq_smul E Q hσ e hqe hW s m
          (chartSection_preimage_basicOpen_eq_top E Q hσ e hqe hW s
            (span_singleton_app_eq_top_of_chartLinearForm_eq_one Q W eL hs))).symm.trans
      ((congrArg (Scheme.Modules.pullbackSection W.ι Q.L W ⊤ W.ι_preimage_self.ge)
            (app_eq_chartLinearForm_smul E Q eL s m hs)).trans
        (Scheme.Modules.pullbackSection_smul W.ι Q.L W ⊤ W.ι_preimage_self.ge
          (chartLinearForm Q W eL m) (Q.q.app W s))))

/-- **The tautological ratio of the chart is `ι m / ι s`.** Let `W` be an affine open, `s` and `m`
sections of `ℰ` over `W`, and `U` an open of `π⁻¹W` over which the degree-one section attached to
`m` is a function `g` times the one attached to `s`. Then the chart
`Stacks.ProjectiveBundleConormal.chartMap` carries `g` to the degree-zero fraction
`ι m / ι s` on the standard open `D₊(ι s)` of the absolute `Proj(Sym_A M)`. -/
theorem appLE_chartMap_eq_awayToSection_of_res_eq_smul (s m : Γ(E, W))
    {U : (bundle E).scheme.Opens} (hU : U ≤ (bundle E).toBase ⁻¹ᵁ W)
    (hDU : AlgebraicGeometry.Proj.basicOpen (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
      (SymmetricAlgebra.ι Γ(X, W) Γ(E, W) s) ≤ chartMap E (symPieces E) hW ⁻¹ᵁ U)
    (g : Γ((bundle E).scheme, U))
    (hg : (tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hU).op
            (tautologicalSectionOver E W m) =
          ((tautologicalTwist E (symPieces E)).smul g).asHom.hom
            ((tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hU).op
              (tautologicalSectionOver E W s))) :
    (chartMap E (symPieces E) hW).appLE U
        (AlgebraicGeometry.Proj.basicOpen (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
          (SymmetricAlgebra.ι Γ(X, W) Γ(E, W) s)) hDU g =
      (AlgebraicGeometry.Proj.awayToSection (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
            (SymmetricAlgebra.ι Γ(X, W) Γ(E, W) s)).hom
        (HomogeneousLocalization.Away.mk (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
          (SymmetricAlgebra.ι_mem_grading_one s) 1 (SymmetricAlgebra.ι Γ(X, W) Γ(E, W) m)
          (SymmetricAlgebra.ι_mem_grading_smul m)) :=
  appLE_eq_awayToSection_of_res_eq_smul (SymmetricAlgebra.grading Γ(X, W) Γ(E, W))
    (SymmetricAlgebra.ι_mem_grading_one m) (SymmetricAlgebra.ι_mem_grading_one s)
    (chartMap E (symPieces E) hW) (tautologicalTwist E (symPieces E))
    (chartTwistIso E (symPieces E) hW) (top_le_chartMap_preimage E (symPieces E) hW)
    (tautologicalSectionOver E W m) (tautologicalSectionOver E W s)
    ((chartTwistIso_hom_pullbackSection E (symPieces E) hW m).trans
      (toTwistSections_eq_degreeSection m))
    ((chartTwistIso_hom_pullbackSection E (symPieces E) hW s).trans
      (toTwistSections_eq_degreeSection s))
    hU hDU g hg

end Stacks.ProjectiveBundleConormal

end
