module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartDelta
public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermSectionCalculus
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictPullbackCoherence
public import StacksFrontier.AlgebraicGeometry.RestrictPushforwardCoherence

/-!
# The canonical element of the determinant, read as a section on an affine chart

Let `X` be a scheme and `L` a perfect object of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]` of rank
zero. On every affine open `V` of `X` the determinant of `L` carries the canonical element
`AlgebraicGeometry.DeterminantTwoTerm.chartDelta` of More on Algebra, Section 0FJI, a global
section of the determinant on `Spec Γ(X, V)`. This file reads that element as a section of the
determinant on the chart of `V` in the shape the glueing datum of
`StacksFrontier/AlgebraicGeometry/AffineOpensDirectedGlue.lean` consumes, and proves that **the
family of these sections is matched by the comparison isomorphisms of that glueing datum**. Those
two facts are what make the canonical global section of the determinant on `X` well defined.

## Main definitions

* `AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecRestrictIso`: the determinant of `L` on an
  affine open is the *restriction* of the determinant on its spectrum along
  `AlgebraicGeometry.IsAffineOpen.isoSpec`.
* `AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecRestrict`: the chart comparison on the
  spectra, read in the restriction world.
* `AlgebraicGeometry.DeterminantTwoTerm.chartDeltaTop`: the canonical element as a *global*
  section of the determinant on an affine open.
* `AlgebraicGeometry.DeterminantTwoTerm.chartDeltaSection`: **the canonical element, read as a
  section on the chart of an affine open.**

## Main results

* `AlgebraicGeometry.DeterminantTwoTerm.chartDeltaSection_eq`: the chart section is the
  restriction of the global section `chartDeltaTop`.
* `AlgebraicGeometry.DeterminantTwoTerm.specMap_affineRestriction_eq` and
  `AlgebraicGeometry.DeterminantTwoTerm.isOpenImmersion_specMap_affineRestriction`: the morphism of
  spectra attached to an inclusion of affine opens is the inclusion of open subschemes conjugated
  by the two `isoSpec`, hence an open immersion.
* `AlgebraicGeometry.DeterminantTwoTerm.localAppFun_chartDetComp_chartDeltaSection`: **the family
  of canonical sections is matched by the comparisons of the glueing datum** — the comparison
  `AlgebraicGeometry.DeterminantTwoTerm.chartDetComp` carries the chart section at `V` to the
  restriction to `V` of the chart section at `W`.

## Implementation notes

*The identification used for the chart section.* `AlgebraicGeometry.IsAffineOpen.isoSpec` is an
isomorphism of schemes, hence an open immersion, so
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` turns the pullback that defines
`AlgebraicGeometry.DeterminantTwoTerm.chartDet` into a restriction; the sections of a restriction
over an open are the sections of the module over its image, so `chartDeltaTop` is the component of
that comparison at the top open applied to the canonical element, restricted from `⊤` to the image
`isoSpec ''ᵁ ⊤`, and `chartDeltaSection` is `chartDeltaTop` restricted from `⊤` to
`V.ι ⁻¹ᵁ V` — the two opens are equal, and the restriction map between equal opens is the
identification. Surjectivity of `isoSpec` is never needed: a restriction map along an inclusion of
opens serves, and the inclusion is all that the statement asks for.

*The comparison, in the restriction world.* `AlgebraicGeometry.DeterminantTwoTerm.chartDetComp` is
built from `chartDetRestrictIso`, a five-fold composite of components of the structure
isomorphisms of `AlgebraicGeometry.Scheme.Modules.pullback`, on which nothing can be computed.
`chartDetChase` rewrites it as the corresponding composite of the structure isomorphisms of
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`, whose components are *restriction maps of a
presheaf*; the input is the coherence of
`StacksFrontier/AlgebraicGeometry/ModuleLimits/RestrictPullbackCoherence.lean`. After that every
factor of the comparison acts on sections either as a restriction map — and all of those collapse,
the homs of a poset being unique — or as the one genuinely mathematical step,
`chartDetSpecRestrict_hom_app_unit`.

*The spelling obstruction.* `AlgebraicGeometry.Scheme.Modules.pullbackCongr` is
`CategoryTheory.eqToIso` of a transported `rfl`, and `chartDetRestrictIso` uses it in the form
`(pullbackCongr h).app M`, whose `hom` is definitionally but not syntactically
`CategoryTheory.NatTrans.app (pullbackCongr h).hom M`. Normalising that at the concrete terms —
`simp only [Iso.app_hom]`, or any `rfl` that expands the five factors into their `hom`s — makes the
kernel attempt the reconciliation and fail with `(kernel) deterministic timeout`. The fix is that
`chartDetRestrictIso_eq` is an equality of *isomorphisms*, that `pullbackRestrictSquare` and
`restrictPullbackChase` state the coherence on variables and in the `Iso.app` spelling
`chartDetRestrictIso` itself uses, and that the only step taken at the concrete terms is
`rw [fiveIsoHom …]`, whose justification is a closed lemma on variables.

*Sections, not morphisms.* The sections of a restriction, of a pushforward and of a module are
three spellings of one type, definitionally equal but not equal at the transparency `rw` checks its
results at, so a goal that mixes two of them is refused with "did not find an occurrence of the
pattern". Every step below is therefore an `Eq.trans` or a `congrArg` of a lemma stated on
variables and applied to explicit arguments, where the reconciliation is a single definitional
check at elaboration; `resSec` and `globalRes` name the restriction maps so that the collapses are
`resSec_resSec`, and `restrict_resSec` and `pushforward_resSec` move between the spellings.

*One definitional check at a time.* Each such reconciliation is affordable once and not twice: a
single term that chains three of them — for instance the left-adjoint comparison
`restrictFunctorIsoPullback_app_unit` written as one `Eq.trans` of three steps — dies with
`(deterministic) timeout at whnf`, while the same three steps as separate lemmas, each stating its
own endpoints, and a `have` whose type is *not* ascribed (so that nothing has to be reconciled with
a written type) all go through. The same applies to the kernel: `localAppFun_chartDeltaSection_aux`
had to be split off from the theorem it feeds, and the two collapses `resSec_chartDeltaSection` and
`resSec_chartDeltaTop` off from it, before the kernel would accept them.

## References

* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
* [Stacks Project, Section 15.124 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
* [Stacks Project, Lemma 26.7.3 (Tag 01I9)](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open CategoryTheory TwoTermDeterminant Opposite
open Stacks.SheafOfModules

universe u

namespace AlgebraicGeometry.DeterminantTwoTerm

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-! ### The components of the structural isomorphisms, on sections -/

/-- The first peeling isomorphism is a restriction map on sections. -/
private theorem restrictPushforwardIso_hom_apply {Y : Scheme.{u}} {U : Y.Opens}
    (N : (U : Scheme.{u}).Modules) (P : (U : Scheme.{u}).Opens)
    (s : ToType (N.val.obj (op (U.ι ⁻¹ᵁ U.ι ''ᵁ P)))) :
    Scheme.Modules.Hom.app (AffineOpensGlue.restrictPushforwardIso N).hom P s =
      resSec N (le_of_eq (U.ι.preimage_image_eq P).symm) s :=
  resSec_eq N (eqToHom (U.ι.preimage_image_eq P).symm).op _ s

/-- The component of the restriction of a morphism along an open immersion is its component at
the image open. -/
private theorem restrictFunctor_map_apply {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f]
    {M N : Z.Modules} (φ : M ⟶ N) (U : Y.Opens) (s : ToType (M.val.obj (op (f ''ᵁ U)))) :
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctor f).map φ) U s =
      Scheme.Modules.Hom.app φ (f ''ᵁ U) s := rfl

/-- The unit of the restriction adjunction at the top open is a restriction map. -/
private theorem restrictAdjunction_unit_app_top {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsOpenImmersion f] (M : Z.Modules) (s : ToType (M.val.obj (op (⊤ : Z.Opens)))) :
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictAdjunction f).unit.app M) ⊤ s =
      globalRes M (f ''ᵁ ⊤) s :=
  resSec_eq M (homOfLE (f.image_preimage_le ⊤)).op le_top s

/-- The comparison of a restriction along a composite with the iterated restriction is a
restriction map on sections. -/
private theorem restrictFunctorComp_hom_apply {Y Z T : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ T)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : T.Modules) (U : Y.Opens)
    (hle : g ''ᵁ (f ''ᵁ U) ≤ (f ≫ g) ''ᵁ U)
    (s : ToType (M.val.obj (op ((f ≫ g) ''ᵁ U)))) :
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorComp f g).hom.app M) U s =
      resSec M hle s :=
  resSec_eq M (eqToHom (show g ''ᵁ (f ''ᵁ U) = (f ≫ g) ''ᵁ U by simp)).op hle s

/-- The inverse comparison of a restriction along a composite is a restriction map on
sections. -/
private theorem restrictFunctorComp_inv_apply {Y Z T : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ T)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : T.Modules) (U : Y.Opens)
    (hle : (f ≫ g) ''ᵁ U ≤ g ''ᵁ (f ''ᵁ U))
    (s : ToType (M.val.obj (op (g ''ᵁ (f ''ᵁ U))))) :
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorComp f g).inv.app M) U s =
      resSec M hle s :=
  resSec_eq M (eqToHom (show (f ≫ g) ''ᵁ U = g ''ᵁ (f ''ᵁ U) by simp)).op hle s

/-- The reindexing of a restriction along an equality of open immersions is a restriction map on
sections. -/
private theorem restrictFunctorCongr_hom_apply {Y Z : Scheme.{u}} {f g : Y ⟶ Z}
    [IsOpenImmersion f] [IsOpenImmersion g] (hfg : f = g) (M : Z.Modules) (U : Y.Opens)
    (hle : g ''ᵁ U ≤ f ''ᵁ U) (s : ToType (M.val.obj (op (f ''ᵁ U)))) :
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorCongr hfg).hom.app M) U s =
      resSec M hle s :=
  resSec_eq M (eqToHom (show g ''ᵁ U = f ''ᵁ U by simp [hfg])).op hle s

/-- The inverse reindexing of a restriction along an equality of open immersions is a restriction
map on sections. -/
private theorem restrictFunctorCongr_inv_apply {Y Z : Scheme.{u}} {f g : Y ⟶ Z}
    [IsOpenImmersion f] [IsOpenImmersion g] (hfg : f = g) (M : Z.Modules) (U : Y.Opens)
    (hle : f ''ᵁ U ≤ g ''ᵁ U) (s : ToType (M.val.obj (op (g ''ᵁ U)))) :
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorCongr hfg).inv.app M) U s =
      resSec M hle s :=
  resSec_eq M (eqToHom (show f ''ᵁ U = g ''ᵁ U by simp [hfg])).op hle s

/-- Restricting a restricted global section of a restriction along an open immersion gives a
restricted global section of the module. -/
private theorem restrict_resSec_globalRes {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f]
    (M : Z.Modules) {P Q : Y.Opens} (hPQ : P ≤ Q) (hI : f ''ᵁ P ≤ f ''ᵁ Q)
    (s : ToType (M.val.obj (op (⊤ : Z.Opens)))) :
    resSec (Scheme.Modules.restrict M f) hPQ (globalRes M (f ''ᵁ Q) s) = globalRes M (f ''ᵁ P) s :=
  (restrict_resSec f M hPQ hI _).trans (resSec_globalRes M hI s)

/-- A morphism out of a restriction carries a restricted global section over `U` to the restriction
of its value on the restricted global section over `⊤`. -/
private theorem app_restrict_globalRes {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f]
    (M : Z.Modules) {N : Y.Modules} (φ : Scheme.Modules.restrict M f ⟶ N) (U : Y.Opens)
    (s : ToType (M.val.obj (op (⊤ : Z.Opens)))) :
    Scheme.Modules.Hom.app φ U (globalRes M (f ''ᵁ U) s) =
      resSec N (le_top : U ≤ ⊤) (Scheme.Modules.Hom.app φ ⊤ (globalRes M (f ''ᵁ ⊤) s)) :=
  ((congrArg (Scheme.Modules.Hom.app φ U)
    (restrict_resSec_globalRes f M (le_top : U ≤ ⊤) (f.image_mono le_top) s)).symm).trans
    (app_resSec φ (le_top : U ≤ ⊤) _)

/-- Restricting a restricted global section of a pushforward gives a restricted global section of
the module. -/
private theorem pushforward_resSec_globalRes {Y Z : Scheme.{u}} (f : Y ⟶ Z) (M : Y.Modules)
    {P Q : Z.Opens} (hPQ : P ≤ Q) (s : ToType (M.val.obj (op (⊤ : Y.Opens)))) :
    resSec ((Scheme.Modules.pushforward f).obj M) hPQ (globalRes M (f ⁻¹ᵁ Q) s) =
      globalRes M (f ⁻¹ᵁ P) s :=
  (pushforward_resSec f M hPQ (Scheme.Hom.preimage_mono _ hPQ) _).trans
    (resSec_globalRes M _ s)

/-! ### The chart comparison in the restriction world -/

/-- The forward map of a five-fold composite of isomorphisms. Isolated on variables so that no
component has to be reduced when it is instantiated. -/
private theorem fiveIsoHom {D : Type*} [Category D] {a₀ a₁ a₂ a₃ a₄ a₅ : D} (i₁ : a₀ ≅ a₁)
    (i₂ : a₁ ≅ a₂) (i₃ : a₂ ≅ a₃) (i₄ : a₃ ≅ a₄) (i₅ : a₄ ≅ a₅) :
    (i₁ ≪≫ i₂ ≪≫ i₃ ≪≫ i₄ ≪≫ i₅).hom =
      i₁.hom ≫ i₂.hom ≫ i₃.hom ≫ i₄.hom ≫ i₅.hom := by
  simp only [Iso.trans_hom]

/-- The composition coherence of `restrictFunctorIsoPullback` around a commuting square of open
immersions. -/
private theorem pullbackRestrictSquare {Z₁ Z₂ Z₃ Z₄ : Scheme.{u}} (p : Z₁ ⟶ Z₂) (q : Z₂ ⟶ Z₃)
    (r : Z₁ ⟶ Z₄) (t : Z₄ ⟶ Z₃) [IsOpenImmersion p] [IsOpenImmersion q] [IsOpenImmersion r]
    [IsOpenImmersion t] (sq : p ≫ q = r ≫ t) (N : Z₃.Modules) :
    (Scheme.Modules.restrictFunctorIsoPullback p).hom.app ((Scheme.Modules.pullback q).obj N) ≫
        (Scheme.Modules.pullbackComp p q).hom.app N ≫
        (Scheme.Modules.pullbackCongr sq).hom.app N ≫
        (Scheme.Modules.pullbackComp r t).inv.app N ≫
        (Scheme.Modules.restrictFunctorIsoPullback r).inv.app
          ((Scheme.Modules.pullback t).obj N) =
      (Scheme.Modules.restrictFunctor p).map
          ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app N) ≫
        (Scheme.Modules.restrictFunctorComp p q).inv.app N ≫
        (Scheme.Modules.restrictFunctorCongr sq).hom.app N ≫
        (Scheme.Modules.restrictFunctorComp r t).hom.app N ≫
        (Scheme.Modules.restrictFunctor r).map
          ((Scheme.Modules.restrictFunctorIsoPullback t).hom.app N) := by
  have c1 := Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctorIsoPullback_hom_app_comp p q N
  have c2 := Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctorIsoPullback_hom_app_comp r t N
  have c3 := NatTrans.congr_app
    (Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctorCongr_hom_restrictFunctorIsoPullback_hom
      sq) N
  simp only [NatTrans.comp_app] at c3
  have h1 : (Scheme.Modules.restrictFunctor p).map
          ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app N) ≫
        (Scheme.Modules.restrictFunctorComp p q).inv.app N ≫
        (Scheme.Modules.restrictFunctorIsoPullback (p ≫ q)).hom.app N =
      (Scheme.Modules.restrictFunctorIsoPullback p).hom.app
          ((Scheme.Modules.pullback q).obj N) ≫
        (Scheme.Modules.pullbackComp p q).hom.app N := by
    rw [c1]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.inv_hom_id_app_assoc]
  have h2 : (Scheme.Modules.restrictFunctorIsoPullback (r ≫ t)).hom.app N ≫
        (Scheme.Modules.pullbackComp r t).inv.app N ≫
        (Scheme.Modules.restrictFunctorIsoPullback r).inv.app
          ((Scheme.Modules.pullback t).obj N) =
      (Scheme.Modules.restrictFunctorComp r t).hom.app N ≫
        (Scheme.Modules.restrictFunctor r).map
          ((Scheme.Modules.restrictFunctorIsoPullback t).hom.app N) := by
    rw [c2]
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id, Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% h1, ← reassoc_of% c3, h2]

/-- **The chart comparison, in the restriction world, on variables.** For a commuting square of
open immersions `p ≫ q = r ≫ t`, a module `N` downstairs and an identification `χ` of the pullback
of `N` along `q`, the composite of the pullback structure isomorphisms that
`AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso` is made of agrees with the composite of
the corresponding restriction structure isomorphisms.

Every factor is written as `CategoryTheory.Iso.app`, as `chartDetRestrictIso` writes it, and every
datum is a variable, so an instance of this lemma needs no reduction. -/
private theorem restrictPullbackChase {Z₁ Z₂ Z₃ Z₄ : Scheme.{u}} (p : Z₁ ⟶ Z₂) (q : Z₂ ⟶ Z₃)
    (r : Z₁ ⟶ Z₄) (t : Z₄ ⟶ Z₃) [IsOpenImmersion p] [IsOpenImmersion q] [IsOpenImmersion r]
    [IsOpenImmersion t] (sq : p ≫ q = r ≫ t) (N : Z₃.Modules) (M : Z₂.Modules)
    (χ : (Scheme.Modules.pullback q).obj N ≅ M) :
    ((Scheme.Modules.restrictFunctorIsoPullback p).app M).hom ≫
        ((Scheme.Modules.pullback p).mapIso χ.symm).hom ≫
        ((Scheme.Modules.pullbackComp p q).app N).hom ≫
        ((Scheme.Modules.pullbackCongr sq).app N).hom ≫
        (((Scheme.Modules.pullbackComp r t).app N).symm).hom ≫
        (((Scheme.Modules.restrictFunctorIsoPullback r).app
          ((Scheme.Modules.pullback t).obj N)).symm).hom =
      (Scheme.Modules.restrictFunctor p).map
          (((Scheme.Modules.restrictFunctorIsoPullback q).app N ≪≫ χ).inv) ≫
        (Scheme.Modules.restrictFunctorComp p q).inv.app N ≫
        (Scheme.Modules.restrictFunctorCongr sq).hom.app N ≫
        (Scheme.Modules.restrictFunctorComp r t).hom.app N ≫
        (Scheme.Modules.restrictFunctor r).map
          ((Scheme.Modules.restrictFunctorIsoPullback t).hom.app N) := by
  simp only [Iso.app_hom, Iso.app_inv, Iso.symm_hom, Functor.mapIso_hom, Iso.trans_inv]
  have hnat := (Scheme.Modules.restrictFunctorIsoPullback p).hom.naturality χ.inv
  rw [← reassoc_of% hnat, pullbackRestrictSquare p q r t sq N, ← Functor.map_comp_assoc]

/-! ### The chart of an affine open as an open immersion of spectra -/

/-- The morphism of spectra attached to an inclusion of affine opens, read through the two
identifications `AlgebraicGeometry.IsAffineOpen.isoSpec`. -/
theorem specMap_affineRestriction_eq {V W : X.affineOpens} (h : V ≤ W) :
    Spec.map (affineRestriction X h) =
      V.2.isoSpec.inv ≫ X.homOfLE (AffineOpensGlue.coe_le_coe h) ≫ W.2.isoSpec.hom := by
  rw [← isoSpec_hom_specMap_chartRestriction h, Iso.inv_hom_id_assoc]

/-- The morphism of spectra attached to an inclusion of affine opens is an open immersion: it is
the inclusion of open subschemes conjugated by two isomorphisms. -/
instance isOpenImmersion_specMap_affineRestriction {V W : X.affineOpens} (h : V ≤ W) :
    IsOpenImmersion (Spec.map (affineRestriction X h)) := by
  rw [specMap_affineRestriction_eq h]
  infer_instance

/-- **The determinant of `L` on an affine open is the restriction of the determinant on its
spectrum.** The identification `AlgebraicGeometry.IsAffineOpen.isoSpec` is an isomorphism of
schemes, hence an open immersion, so
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` turns the pullback that defines
`AlgebraicGeometry.DeterminantTwoTerm.chartDet` into a restriction, whose sections over an open are
the sections of `AlgebraicGeometry.DeterminantTwoTerm.chartDetSpec` over its image. -/
def chartDetSpecRestrictIso (L : PerfectTwoTermAmplitude X) (V : X.affineOpens) :
    Scheme.Modules.restrict (chartDetSpec L V) V.2.isoSpec.hom ≅ chartDet L V :=
  (Scheme.Modules.restrictFunctorIsoPullback V.2.isoSpec.hom).app (chartDetSpec L V)

/-- The chart comparison of determinants on the spectra, read in the restriction world: the
determinant on the spectrum of `V` is the restriction along `Spec ρ` of the determinant on the
spectrum of `W`. -/
def chartDetSpecRestrict (L : PerfectTwoTermAmplitude X) {V W : X.affineOpens} (h : V ≤ W) :
    Scheme.Modules.restrict (chartDetSpec L W) (Spec.map (affineRestriction X h)) ≅
      chartDetSpec L V :=
  (Scheme.Modules.restrictFunctorIsoPullback (Spec.map (affineRestriction X h))).app
      (chartDetSpec L W) ≪≫ chartDetSpecPullbackIso L h

/-- The five factors of `AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso`, named. This
holds by unfolding the definition; it is recorded as an equality of *isomorphisms* rather than of
their `hom`s, because expanding the `hom` of the composite forces the kernel to reconcile the two
spellings of the component of `AlgebraicGeometry.Scheme.Modules.pullbackCongr`, which it does not
finish. -/
private theorem chartDetRestrictIso_eq (L : PerfectTwoTermAmplitude X) {V W : X.affineOpens}
    (h : V ≤ W) :
    chartDetRestrictIso L h =
      (Scheme.Modules.pullback V.2.isoSpec.hom).mapIso (chartDetSpecPullbackIso L h).symm ≪≫
        (Scheme.Modules.pullbackComp V.2.isoSpec.hom
            (Spec.map (affineRestriction X h))).app (chartDetSpec L W) ≪≫
          (Scheme.Modules.pullbackCongr
              (isoSpec_hom_specMap_chartRestriction h)).app (chartDetSpec L W) ≪≫
            ((Scheme.Modules.pullbackComp (X.homOfLE (AffineOpensGlue.coe_le_coe h))
                W.2.isoSpec.hom).app (chartDetSpec L W)).symm ≪≫
              ((Scheme.Modules.restrictFunctorIsoPullback
                  (X.homOfLE (AffineOpensGlue.coe_le_coe h))).app
                ((Scheme.Modules.pullback W.2.isoSpec.hom).obj (chartDetSpec L W))).symm :=
  rfl

/-- **The chart comparison of determinants, in the restriction world.** For affine opens `V ≤ W`
of `X`, the identification of the determinant on `V` with the restriction of the determinant on the
spectrum of `V`, followed by the chart comparison
`AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso`, is the restriction along `isoSpec` of
`AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecRestrict`, the bookkeeping of the commuting
square of the four open immersions, and the identification of the determinant on `W` with the
restriction of the determinant on the spectrum of `W`. -/
private theorem chartDetChase (L : PerfectTwoTermAmplitude X) {V W : X.affineOpens} (h : V ≤ W) :
    (chartDetSpecRestrictIso L V).hom ≫ (chartDetRestrictIso L h).hom =
      (Scheme.Modules.restrictFunctor V.2.isoSpec.hom).map (chartDetSpecRestrict L h).inv ≫
        (Scheme.Modules.restrictFunctorComp V.2.isoSpec.hom
            (Spec.map (affineRestriction X h))).inv.app (chartDetSpec L W) ≫
        (Scheme.Modules.restrictFunctorCongr
            (isoSpec_hom_specMap_chartRestriction h)).hom.app (chartDetSpec L W) ≫
        (Scheme.Modules.restrictFunctorComp (X.homOfLE (AffineOpensGlue.coe_le_coe h))
            W.2.isoSpec.hom).hom.app (chartDetSpec L W) ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE (AffineOpensGlue.coe_le_coe h))).map
          ((Scheme.Modules.restrictFunctorIsoPullback W.2.isoSpec.hom).hom.app
            (chartDetSpec L W)) := by
  rw [chartDetRestrictIso_eq, fiveIsoHom]
  exact restrictPullbackChase V.2.isoSpec.hom (Spec.map (affineRestriction X h))
    (X.homOfLE (AffineOpensGlue.coe_le_coe h)) W.2.isoSpec.hom
    (isoSpec_hom_specMap_chartRestriction h)
    (chartDetSpec L W) (chartDetSpec L V) (chartDetSpecPullbackIso L h)

/-! ### The canonical element of the determinant on an affine open -/

/-- The component of the pushforward of a component of a natural isomorphism: it is the component
of that natural isomorphism at the preimage open. -/
private theorem pushforward_map_isoApp {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    {F G : Z.Modules ⥤ Y.Modules} (α : F ≅ G) (M : Z.Modules) (U : Z.Opens)
    (s : ToType ((F.obj M).val.obj (op (f ⁻¹ᵁ U)))) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pushforward f).map (α.hom.app M)) U s =
      Scheme.Modules.Hom.app (α.app M).hom (f ⁻¹ᵁ U) s := rfl

/-- **`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` is the left-adjoint
comparison**: the unit of the restriction adjunction followed by its pushforward is the unit of the
pullback–pushforward adjunction. This is the defining property of
`CategoryTheory.Adjunction.leftAdjointUniq`. -/
private theorem unit_comp_restrictFunctorIsoPullback {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsOpenImmersion f] (M : Z.Modules) :
    (Scheme.Modules.restrictAdjunction f).unit.app M ≫
        (Scheme.Modules.pushforward f).map
          ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M) =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M :=
  Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f) M

/-- The component of `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` on a section in
the image of the unit of the restriction adjunction is the pushforward of that component on the
same section. -/
private theorem isoApp_app_eq_pushforward_map_app {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsOpenImmersion f] (M : Z.Modules) (U : Z.Opens) (s : ToType (M.val.obj (op U))) :
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback f).app M).hom (f ⁻¹ᵁ U)
        (Scheme.Modules.Hom.app ((Scheme.Modules.restrictAdjunction f).unit.app M) U s) =
      Scheme.Modules.Hom.app ((Scheme.Modules.pushforward f).map
          ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M)) U
        (Scheme.Modules.Hom.app ((Scheme.Modules.restrictAdjunction f).unit.app M) U s) :=
  (pushforward_map_isoApp f (Scheme.Modules.restrictFunctorIsoPullback f) M U
    (Scheme.Modules.Hom.app ((Scheme.Modules.restrictAdjunction f).unit.app M) U s)).symm

/-- The two factors of the left-adjoint comparison, applied one after the other, are the composite
applied once. -/
private theorem pushforward_map_app_eq_comp_app {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsOpenImmersion f] (M : Z.Modules) (U : Z.Opens) (s : ToType (M.val.obj (op U))) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pushforward f).map
          ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M)) U
        (Scheme.Modules.Hom.app ((Scheme.Modules.restrictAdjunction f).unit.app M) U s) =
      Scheme.Modules.Hom.app ((Scheme.Modules.restrictAdjunction f).unit.app M ≫
        (Scheme.Modules.pushforward f).map
          ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M)) U s :=
  (comp_app_apply ((Scheme.Modules.restrictAdjunction f).unit.app M)
    ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M)) U s).symm

/-- **The left-adjoint comparison on the unit of the restriction adjunction, over an arbitrary
open.** The component of `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` at the
preimage of `U` carries the image of a section under the unit of the restriction adjunction to its
image under the unit of the pullback–pushforward adjunction. -/
private theorem restrictFunctorIsoPullback_app_unit_of {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsOpenImmersion f] (M : Z.Modules) (U : Z.Opens) (s : ToType (M.val.obj (op U))) :
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback f).app M).hom (f ⁻¹ᵁ U)
        (Scheme.Modules.Hom.app ((Scheme.Modules.restrictAdjunction f).unit.app M) U s) =
      Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) U s := by
  have hu := ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ U)
    (unit_comp_restrictFunctorIsoPullback f M)) s
  refine Eq.trans ?_ hu
  exact (isoApp_app_eq_pushforward_map_app f M U s).trans
    (pushforward_map_app_eq_comp_app f M U s)

/-- **The left-adjoint comparison on the unit of the restriction adjunction**, at the top open. -/
private theorem restrictFunctorIsoPullback_app_unit {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsOpenImmersion f] (M : Z.Modules) (s : ToType (M.val.obj (op (⊤ : Z.Opens)))) :
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback f).app M).hom ⊤
        (Scheme.Modules.Hom.app ((Scheme.Modules.restrictAdjunction f).unit.app M) ⊤ s) =
      Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ⊤ s :=
  restrictFunctorIsoPullback_app_unit_of f M ⊤ s

/-- **The chart comparison on the spectra carries the canonical element to the canonical
element.** For affine opens `V ≤ W` of `X` and a rank-zero `L`, the identification
`AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecRestrict` of the determinant on the spectrum of
`V` with the restriction of the determinant on the spectrum of `W` carries the canonical global
section on the spectrum of `W` — restricted along the unit of the restriction adjunction — to the
canonical global section on the spectrum of `V`.

The comparison is the left-adjoint comparison of the restriction and pullback adjunctions followed
by Tag 01I9 and the image of the comparison over the rings. The first factor turns the restricted
global section into the image of the unit of the pullback–pushforward adjunction; Tag 01I9 then
carries that to `1 ⊗ δ` of the determinant module of the chart complex of `W`, by
`AlgebraicGeometry.pullbackTildeIso_hom_app_unit_toOpen`; and the last factor carries `1 ⊗ δ` to
`δ`, because a map of modules acts on the canonical global sections through the map itself and
`AlgebraicGeometry.DeterminantTwoTerm.chartDetModuleIso_one_tmul_delta` is exactly that map on
`1 ⊗ δ`. -/
private theorem chartDetSpecRestrict_hom_app_unit {L : PerfectTwoTermAmplitude X}
    (hL : IsRankZeroOn L) {V W : X.affineOpens} (h : V ≤ W) :
    Scheme.Modules.Hom.app (chartDetSpecRestrict L h).hom ⊤
        (Scheme.Modules.Hom.app ((Scheme.Modules.restrictAdjunction
          (Spec.map (affineRestriction X h))).unit.app (chartDetSpec L W)) ⊤
          (chartDelta hL W)) =
      chartDelta hL V := by
  have hkey := pullbackTildeIso_hom_app_unit_toOpen Γ(X, (W.1 : X.Opens))
    Γ(X, (V.1 : X.Opens)) (affineRestriction X h)
    ((det Γ(X, (W.1 : X.Opens))).obj ⟨chartComplex L W⟩).of.obj
    (delta (chartComplex L W) (hL W))
  have e1 := twoIsoHom_app ((Scheme.Modules.restrictFunctorIsoPullback
      (Spec.map (affineRestriction X h))).app (chartDetSpec L W))
    (chartDetSpecPullbackIso L h) (⊤ : (Spec Γ(X, (V.1 : X.Opens))).Opens)
    (Scheme.Modules.Hom.app ((Scheme.Modules.restrictAdjunction
      (Spec.map (affineRestriction X h))).unit.app (chartDetSpec L W)) ⊤ (chartDelta hL W))
  have e2 := congrArg (fun z => Scheme.Modules.Hom.app (chartDetSpecPullbackIso L h).hom
      (⊤ : (Spec Γ(X, (V.1 : X.Opens))).Opens) z)
    (restrictFunctorIsoPullback_app_unit (Spec.map (affineRestriction X h))
      (chartDetSpec L W) (chartDelta hL W))
  have e3 := twoIsoHom_app ((pullbackTildeIso Γ(X, (W.1 : X.Opens)) Γ(X, (V.1 : X.Opens))
      (affineRestriction X h)).app
        ((det Γ(X, (W.1 : X.Opens))).obj ⟨chartComplex L W⟩).of.obj)
    ((tilde.functor Γ(X, (V.1 : X.Opens))).mapIso (chartDetModuleIso L h).toModuleIso)
    (⊤ : (Spec Γ(X, (V.1 : X.Opens))).Opens)
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction
      (Spec.map (affineRestriction X h))).unit.app (chartDetSpec L W)) ⊤ (chartDelta hL W))
  have e4 := congrArg (fun z => Scheme.Modules.Hom.app
      ((tilde.functor Γ(X, (V.1 : X.Opens))).mapIso (chartDetModuleIso L h).toModuleIso).hom
      (⊤ : (Spec Γ(X, (V.1 : X.Opens))).Opens) z) hkey
  exact e1.trans (e2.trans (e3.trans (e4.trans
    ((app_tilde_toOpen Γ(X, (V.1 : X.Opens)) (chartDetModuleIso L h).toModuleIso.hom _).trans
      (congrArg (fun z =>
          (tilde.toOpen ((det Γ(X, (V.1 : X.Opens))).obj ⟨chartComplex L V⟩).of.obj ⊤).hom z)
        (chartDetModuleIso_one_tmul_delta hL h))))))

/-- **The canonical global section of the determinant of `L` on an affine open.** The canonical
element `AlgebraicGeometry.DeterminantTwoTerm.chartDelta` of the determinant on the spectrum of
`V`, read through the identification
`AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecRestrictIso` of the determinant on `V` with the
restriction of the determinant on the spectrum of `V`. -/
def chartDeltaTop {L : PerfectTwoTermAmplitude X} (hL : IsRankZeroOn L) (V : X.affineOpens) :
    Γ(chartDet L V, ⊤) :=
  Scheme.Modules.Hom.app (chartDetSpecRestrictIso L V).hom ⊤
    ((chartDetSpec L V).val.map (homOfLE le_top).op (chartDelta hL V))

/-- **The canonical element of the determinant of `L`, read as a section on the chart of an
affine open.** This is the member at `V` of the family of sections of the glueing datum of
`AlgebraicGeometry.AffineOpensGlue` that
`AlgebraicGeometry.DeterminantTwoTerm.chartDetComp` matches. -/
def chartDeltaSection {L : PerfectTwoTermAmplitude X} (hL : IsRankZeroOn L)
    (V : X.affineOpens) :
    ToType (openSections (AffineOpensGlue.chart X V) (chartDet L V) (V.1 : X.Opens)) :=
  (chartDet L V).val.map (homOfLE le_top).op (chartDeltaTop hL V)

/-- `AlgebraicGeometry.DeterminantTwoTerm.chartDeltaSection` is the restriction to the preimage of
`V` in `V` — which is all of `V` — of the canonical global section
`AlgebraicGeometry.DeterminantTwoTerm.chartDeltaTop`. -/
theorem chartDeltaSection_eq {L : PerfectTwoTermAmplitude X} (hL : IsRankZeroOn L)
    (V : X.affineOpens) :
    chartDeltaSection hL V =
      (chartDet L V).val.map
        (homOfLE (le_top :
          (V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens) ≤ (⊤ : ((V.1 : X.Opens) : Scheme.{u}).Opens))).op
        (chartDeltaTop hL V) := rfl

/-! ### The comparison of the glueing datum on the canonical sections -/

/-- The sections map of a three-fold composite of isomorphisms. Isolated on variables. -/
private theorem threeIsoHom_app {Y : Scheme.{u}} {A B C D : Y.Modules} (i : A ≅ B) (j : B ≅ C)
    (k : C ≅ D) (U : Y.Opens) (s : ToType (A.val.obj (op U))) :
    Scheme.Modules.Hom.app (i ≪≫ j ≪≫ k).hom U s =
      Scheme.Modules.Hom.app k.hom U (Scheme.Modules.Hom.app j.hom U
        (Scheme.Modules.Hom.app i.hom U s)) := rfl

/-- The sections map of a five-fold composite of morphisms. Isolated on variables. -/
private theorem fiveCompApp {Y : Scheme.{u}} {A₀ A₁ A₂ A₃ A₄ A₅ : Y.Modules} (f₁ : A₀ ⟶ A₁)
    (f₂ : A₁ ⟶ A₂) (f₃ : A₂ ⟶ A₃) (f₄ : A₃ ⟶ A₄) (f₅ : A₄ ⟶ A₅) (U : Y.Opens)
    (s : ToType (A₀.val.obj (op U))) :
    Scheme.Modules.Hom.app (f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅) U s =
      Scheme.Modules.Hom.app f₅ U (Scheme.Modules.Hom.app f₄ U
        (Scheme.Modules.Hom.app f₃ U (Scheme.Modules.Hom.app f₂ U
          (Scheme.Modules.Hom.app f₁ U s)))) := rfl

/-- **Peeling the pushforward off the determinant on `V`** carries the canonical section to the
canonical section: the first peeling isomorphism is a restriction map, and a restriction of a
restricted global section is a restricted global section. -/
private theorem step_peelV {L : PerfectTwoTermAmplitude X} (hL : IsRankZeroOn L)
    (V : X.affineOpens) (U : ((V.1 : X.Opens) : Scheme.{u}).Opens) :
    Scheme.Modules.Hom.app (AffineOpensGlue.restrictPushforwardIso (chartDet L V)).hom U
        (globalRes (chartDet L V)
          ((V.1 : X.Opens).ι ⁻¹ᵁ ((V.1 : X.Opens).ι ''ᵁ U)) (chartDeltaTop hL V)) =
      globalRes (chartDet L V) U (chartDeltaTop hL V) :=
  (restrictPushforwardIso_hom_apply (chartDet L V) U _).trans
    (resSec_globalRes (chartDet L V)
      (le_of_eq ((V.1 : X.Opens).ι.preimage_image_eq U).symm) (chartDeltaTop hL V))

/-- **The chart comparison on the open subschemes carries the canonical section to the canonical
section.** For affine opens `V ≤ W` of `X` and a rank-zero `L`, the comparison
`AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso` carries the restriction to an open `U`
of `V` of the canonical global section on `V` to the restriction to the image of `U` in `W` of the
canonical global section on `W`.

Through `AlgebraicGeometry.DeterminantTwoTerm.chartDetChase` the comparison becomes the restriction
along `isoSpec` of `AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecRestrict` followed by three
restriction maps of the determinant on the spectrum of `W` and the identification on `W`; the
first factor is `chartDetSpecRestrict_hom_app_unit`, read on the inverse and transported to `U` by
naturality, and the restriction maps collapse, the homs of a poset being unique. -/
private theorem step_restrict {L : PerfectTwoTermAmplitude X} (hL : IsRankZeroOn L)
    {V W : X.affineOpens} (h : V ≤ W) (U : ((V.1 : X.Opens) : Scheme.{u}).Opens) :
    Scheme.Modules.Hom.app (chartDetRestrictIso L h).hom U
        (globalRes (chartDet L V) U (chartDeltaTop hL V)) =
      globalRes (chartDet L W) (X.homOfLE (AffineOpensGlue.coe_le_coe h) ''ᵁ U)
        (chartDeltaTop hL W) := by
  have hIs : Spec.map (affineRestriction X h) ''ᵁ (V.2.isoSpec.hom ''ᵁ U) ≤
      Spec.map (affineRestriction X h) ''ᵁ ⊤ :=
    (Spec.map (affineRestriction X h)).image_mono le_top
  have h3 : (V.2.isoSpec.hom ≫ Spec.map (affineRestriction X h)) ''ᵁ U ≤
      Spec.map (affineRestriction X h) ''ᵁ (V.2.isoSpec.hom ''ᵁ U) := le_of_eq (by simp)
  have h4 : (X.homOfLE (AffineOpensGlue.coe_le_coe h) ≫ W.2.isoSpec.hom) ''ᵁ U ≤
      (V.2.isoSpec.hom ≫ Spec.map (affineRestriction X h)) ''ᵁ U :=
    le_of_eq (by simp [isoSpec_hom_specMap_chartRestriction h])
  have h5 : W.2.isoSpec.hom ''ᵁ (X.homOfLE (AffineOpensGlue.coe_le_coe h) ''ᵁ U) ≤
      (X.homOfLE (AffineOpensGlue.coe_le_coe h) ≫ W.2.isoSpec.hom) ''ᵁ U := le_of_eq (by simp)
  have hB1 := app_restrict_globalRes V.2.isoSpec.hom (chartDetSpec L V)
    (chartDetSpecRestrictIso L V).hom U (chartDelta hL V)
  have hinv := (inv_app_apply_eq (chartDetSpecRestrict L h) ⊤
    (Scheme.Modules.Hom.app ((Scheme.Modules.restrictAdjunction
      (Spec.map (affineRestriction X h))).unit.app (chartDetSpec L W)) ⊤ (chartDelta hL W))
    (chartDelta hL V) (chartDetSpecRestrict_hom_app_unit hL h)).trans
    (restrictAdjunction_unit_app_top (Spec.map (affineRestriction X h)) (chartDetSpec L W)
      (chartDelta hL W))
  have hf1 := (restrictFunctor_map_apply V.2.isoSpec.hom (chartDetSpecRestrict L h).inv U
      (globalRes (chartDetSpec L V) (V.2.isoSpec.hom ''ᵁ U) (chartDelta hL V))).trans
    ((app_resSec (chartDetSpecRestrict L h).inv
        (le_top : V.2.isoSpec.hom ''ᵁ U ≤ ⊤) (chartDelta hL V)).trans
      ((congrArg (fun z => resSec (Scheme.Modules.restrict (chartDetSpec L W)
            (Spec.map (affineRestriction X h)))
            (le_top : V.2.isoSpec.hom ''ᵁ U ≤ ⊤) z) hinv).trans
        (restrict_resSec_globalRes (Spec.map (affineRestriction X h)) (chartDetSpec L W)
          (le_top : V.2.isoSpec.hom ''ᵁ U ≤ ⊤) hIs (chartDelta hL W))))
  have hf2 := (restrictFunctorComp_inv_apply V.2.isoSpec.hom
      (Spec.map (affineRestriction X h)) (chartDetSpec L W) U h3 _).trans
    (resSec_globalRes (chartDetSpec L W) h3 (chartDelta hL W))
  have hf3 := (restrictFunctorCongr_hom_apply (isoSpec_hom_specMap_chartRestriction h)
      (chartDetSpec L W) U h4 _).trans
    (resSec_globalRes (chartDetSpec L W) h4 (chartDelta hL W))
  have hf4 := (restrictFunctorComp_hom_apply (X.homOfLE (AffineOpensGlue.coe_le_coe h))
      W.2.isoSpec.hom
      (chartDetSpec L W) U h5 _).trans
    (resSec_globalRes (chartDetSpec L W) h5 (chartDelta hL W))
  have hf5 := (restrictFunctor_map_apply (X.homOfLE (AffineOpensGlue.coe_le_coe h))
      ((Scheme.Modules.restrictFunctorIsoPullback W.2.isoSpec.hom).hom.app
        (chartDetSpec L W)) U _).trans
    (app_restrict_globalRes W.2.isoSpec.hom (chartDetSpec L W)
      ((Scheme.Modules.restrictFunctorIsoPullback W.2.isoSpec.hom).hom.app (chartDetSpec L W))
      (X.homOfLE (AffineOpensGlue.coe_le_coe h) ''ᵁ U) (chartDelta hL W))
  refine Eq.trans (congrArg (fun z => Scheme.Modules.Hom.app (chartDetRestrictIso L h).hom U z)
    hB1.symm) ?_
  refine Eq.trans (comp_app_apply (chartDetSpecRestrictIso L V).hom
    (chartDetRestrictIso L h).hom U _).symm ?_
  refine Eq.trans (ConcreteCategory.congr_hom
    (congrArg (fun φ => Scheme.Modules.Hom.app φ U) (chartDetChase L h)) _) ?_
  refine Eq.trans (fiveCompApp _ _ _ _ _ U _) ?_
  rw [hf1, hf2, hf3, hf4]
  exact hf5

/-- **Peeling the pushforward off the determinant on `W`** carries the canonical section to the
canonical section. The second peeling isomorphism is three restriction maps of the determinant on
`W`, and they collapse to one. -/
private theorem step_peelLe {L : PerfectTwoTermAmplitude X} (hL : IsRankZeroOn L)
    {V W : X.affineOpens} (h : V ≤ W) (U : ((V.1 : X.Opens) : Scheme.{u}).Opens) :
    Scheme.Modules.Hom.app
        (AffineOpensGlue.restrictPushforwardLeIso (AffineOpensGlue.coe_le_coe h)
          (chartDet L W)).hom U
        (globalRes (chartDet L W)
          ((W.1 : X.Opens).ι ⁻¹ᵁ ((V.1 : X.Opens).ι ''ᵁ U)) (chartDeltaTop hL W)) =
      globalRes (chartDet L W) (X.homOfLE (AffineOpensGlue.coe_le_coe h) ''ᵁ U)
        (chartDeltaTop hL W) := by
  have hA : (X.homOfLE (AffineOpensGlue.coe_le_coe h) ≫ (W.1 : X.Opens).ι) ''ᵁ U ≤
      (V.1 : X.Opens).ι ''ᵁ U := le_of_eq (by simp only [Scheme.homOfLE_ι])
  have hB : (W.1 : X.Opens).ι ''ᵁ (X.homOfLE (AffineOpensGlue.coe_le_coe h) ''ᵁ U) ≤
      (X.homOfLE (AffineOpensGlue.coe_le_coe h) ≫ (W.1 : X.Opens).ι) ''ᵁ U :=
    le_of_eq (by rw [← Scheme.Hom.comp_image])
  have hg1 := (restrictFunctorCongr_inv_apply (X.homOfLE_ι (AffineOpensGlue.coe_le_coe h))
      ((Scheme.Modules.pushforward (W.1 : X.Opens).ι).obj (chartDet L W)) U hA _).trans
    (pushforward_resSec_globalRes (W.1 : X.Opens).ι (chartDet L W) hA (chartDeltaTop hL W))
  have hg2 := (restrictFunctorComp_hom_apply (X.homOfLE (AffineOpensGlue.coe_le_coe h))
      (W.1 : X.Opens).ι ((Scheme.Modules.pushforward (W.1 : X.Opens).ι).obj (chartDet L W))
      U hB _).trans
    (pushforward_resSec_globalRes (W.1 : X.Opens).ι (chartDet L W) hB (chartDeltaTop hL W))
  have hg3 := (restrictFunctor_mapIso_apply (X.homOfLE (AffineOpensGlue.coe_le_coe h))
      (AffineOpensGlue.restrictPushforwardIso (chartDet L W)) U _).trans
    ((restrictPushforwardIso_hom_apply (chartDet L W)
        (X.homOfLE (AffineOpensGlue.coe_le_coe h) ''ᵁ U) _).trans
      (resSec_globalRes (chartDet L W)
        (le_of_eq ((W.1 : X.Opens).ι.preimage_image_eq
          (X.homOfLE (AffineOpensGlue.coe_le_coe h) ''ᵁ U)).symm) (chartDeltaTop hL W)))
  refine Eq.trans (threeIsoHom_app
    ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι (AffineOpensGlue.coe_le_coe h))).symm.app
      ((Scheme.Modules.pushforward (W.1 : X.Opens).ι).obj (chartDet L W)))
    ((Scheme.Modules.restrictFunctorComp (X.homOfLE (AffineOpensGlue.coe_le_coe h))
      (W.1 : X.Opens).ι).app
      ((Scheme.Modules.pushforward (W.1 : X.Opens).ι).obj (chartDet L W)))
    ((Scheme.Modules.restrictFunctor (X.homOfLE (AffineOpensGlue.coe_le_coe h))).mapIso
      (AffineOpensGlue.restrictPushforwardIso (chartDet L W))) U _) ?_
  refine Eq.trans (congrArg (fun z => Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctor (X.homOfLE (AffineOpensGlue.coe_le_coe h))).mapIso
        (AffineOpensGlue.restrictPushforwardIso (chartDet L W))).hom U
      (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorComp
        (X.homOfLE (AffineOpensGlue.coe_le_coe h)) (W.1 : X.Opens).ι).hom.app
          ((Scheme.Modules.pushforward (W.1 : X.Opens).ι).obj (chartDet L W))) U z)) hg1) ?_
  refine Eq.trans (congrArg (fun z => Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctor (X.homOfLE (AffineOpensGlue.coe_le_coe h))).mapIso
        (AffineOpensGlue.restrictPushforwardIso (chartDet L W))).hom U z) hg2) ?_
  exact hg3

/-- The three factors of `AlgebraicGeometry.DeterminantTwoTerm.chartDetComp`, named. This is its
definition, recorded as an equality of isomorphisms. -/
private theorem chartDetComp_eq (L : PerfectTwoTermAmplitude X) {V W : X.affineOpens}
    (h : V ≤ W) :
    chartDetComp L h =
      AffineOpensGlue.restrictPushforwardIso (chartDet L V) ≪≫ chartDetRestrictIso L h ≪≫
        (AffineOpensGlue.restrictPushforwardLeIso (AffineOpensGlue.coe_le_coe h)
          (chartDet L W)).symm := rfl

/-- **The comparison of the glueing datum carries the canonical section to the canonical
section**, over an arbitrary open of the smaller chart. This is the three peeling steps
composed. -/
private theorem chartDetComp_hom_app {L : PerfectTwoTermAmplitude X} (hL : IsRankZeroOn L)
    {V W : X.affineOpens} (h : V ≤ W) (U : ((V.1 : X.Opens) : Scheme.{u}).Opens) :
    Scheme.Modules.Hom.app (chartDetComp L h).hom U
        (globalRes (chartDet L V)
          ((V.1 : X.Opens).ι ⁻¹ᵁ ((V.1 : X.Opens).ι ''ᵁ U)) (chartDeltaTop hL V)) =
      globalRes (chartDet L W)
        ((W.1 : X.Opens).ι ⁻¹ᵁ ((V.1 : X.Opens).ι ''ᵁ U)) (chartDeltaTop hL W) := by
  have hmid := (congrArg (fun z => Scheme.Modules.Hom.app (chartDetRestrictIso L h).hom U z)
    (step_peelV hL V U)).trans (step_restrict hL h U)
  have hlast := symm_hom_app_apply_eq
    (AffineOpensGlue.restrictPushforwardLeIso (AffineOpensGlue.coe_le_coe h) (chartDet L W)) U
    (globalRes (chartDet L W)
      ((W.1 : X.Opens).ι ⁻¹ᵁ ((V.1 : X.Opens).ι ''ᵁ U)) (chartDeltaTop hL W))
    (globalRes (chartDet L W) (X.homOfLE (AffineOpensGlue.coe_le_coe h) ''ᵁ U) (chartDeltaTop hL W))
    (step_peelLe hL h U)
  rw [chartDetComp_eq]
  refine Eq.trans (threeIsoHom_app (AffineOpensGlue.restrictPushforwardIso (chartDet L V))
    (chartDetRestrictIso L h)
    (AffineOpensGlue.restrictPushforwardLeIso (AffineOpensGlue.coe_le_coe h) (chartDet L W)).symm U
    (globalRes (chartDet L V)
      ((V.1 : X.Opens).ι ⁻¹ᵁ ((V.1 : X.Opens).ι ''ᵁ U)) (chartDeltaTop hL V))) ?_
  exact (congrArg (fun z => Scheme.Modules.Hom.app
    (AffineOpensGlue.restrictPushforwardLeIso (AffineOpensGlue.coe_le_coe h)
      (chartDet L W)).symm.hom U z) hmid).trans hlast

/-- The sections map over an open `P` of a morphism of the restrictions to `P`, on a section.
This is `AlgebraicGeometry.localApp` unwound: the two comparison isomorphisms
`AlgebraicGeometry.Scheme.Modules.restrictAppIso` are identities, so only the two restriction maps
between `P` and the image of its preimage remain. -/
private theorem localAppFun_eq {A B : X.Modules} {P : X.Opens}
    (φ : Scheme.Modules.restrict A P.ι ⟶ Scheme.Modules.restrict B P.ι)
    (s : ToType (A.val.obj (op P)))
    (h₁ : P.ι ''ᵁ (P.ι ⁻¹ᵁ P) ≤ P) (h₂ : P ≤ P.ι ''ᵁ (P.ι ⁻¹ᵁ P)) :
    localAppFun φ P le_rfl s =
      resSec B h₂ (Scheme.Modules.Hom.app φ (P.ι ⁻¹ᵁ P) (resSec A h₁ s)) := rfl

/-- The restriction from `W` to `V` of the canonical section on the chart of `W` is the
restriction to the preimage of `V` in `W` of the canonical global section there. -/
private theorem chartDeltaSection_restrict {L : PerfectTwoTermAmplitude X}
    (hL : IsRankZeroOn L) {V W : X.affineOpens} (h : V ≤ W) :
    ((Scheme.Modules.pushforward (AffineOpensGlue.chart X W)).obj (chartDet L W)).val.map
        (homOfLE (show (V.1 : X.Opens) ≤ (W.1 : X.Opens) from h)).op
        (chartDeltaSection hL W) =
      globalRes (chartDet L W) ((W.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)) (chartDeltaTop hL W) :=
  (resSec_eq ((Scheme.Modules.pushforward (W.1 : X.Opens).ι).obj (chartDet L W))
      (homOfLE (show (V.1 : X.Opens) ≤ (W.1 : X.Opens) from h)).op
      (show (V.1 : X.Opens) ≤ (W.1 : X.Opens) from h) (chartDeltaSection hL W)).trans
    (pushforward_resSec_globalRes (W.1 : X.Opens).ι (chartDet L W)
      (show (V.1 : X.Opens) ≤ (W.1 : X.Opens) from h) (chartDeltaTop hL W))

/-- The chart section on `V`, restricted along the image of the preimage of `V`, is the canonical
global section restricted to that preimage. -/
private theorem resSec_chartDeltaSection {L : PerfectTwoTermAmplitude X} (hL : IsRankZeroOn L)
    (V : X.affineOpens)
    (h₁ : (V.1 : X.Opens).ι ''ᵁ ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)) ≤ (V.1 : X.Opens)) :
    resSec ((Scheme.Modules.pushforward (V.1 : X.Opens).ι).obj (chartDet L V)) h₁
        (chartDeltaSection hL V) =
      globalRes (chartDet L V)
        ((V.1 : X.Opens).ι ⁻¹ᵁ ((V.1 : X.Opens).ι ''ᵁ ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens))))
        (chartDeltaTop hL V) :=
  pushforward_resSec_globalRes (V.1 : X.Opens).ι (chartDet L V) h₁ (chartDeltaTop hL V)

/-- The canonical global section on `W`, restricted to the preimage of the image of the preimage of
`V` and then back to the preimage of `V`, is its restriction to the preimage of `V`. -/
private theorem resSec_chartDeltaTop {L : PerfectTwoTermAmplitude X} (hL : IsRankZeroOn L)
    {V W : X.affineOpens} (_h : V ≤ W)
    (h₂ : (V.1 : X.Opens) ≤ (V.1 : X.Opens).ι ''ᵁ ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens))) :
    resSec ((Scheme.Modules.pushforward (W.1 : X.Opens).ι).obj (chartDet L W)) h₂
        (globalRes (chartDet L W)
          ((W.1 : X.Opens).ι ⁻¹ᵁ
            ((V.1 : X.Opens).ι ''ᵁ ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens))))
          (chartDeltaTop hL W)) =
      globalRes (chartDet L W) ((W.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)) (chartDeltaTop hL W) :=
  pushforward_resSec_globalRes (W.1 : X.Opens).ι (chartDet L W) h₂ (chartDeltaTop hL W)

/-- **The comparison of the glueing datum carries the canonical section on the chart of `V` to the
canonical global section on the chart of `W`, restricted to the preimage of `V`.** This is
`AlgebraicGeometry.DeterminantTwoTerm.chartDetComp_hom_app` at the open `W.ι ⁻¹ᵁ V`, with the two
restriction maps of `AlgebraicGeometry.localApp` collapsed. -/
private theorem localAppFun_chartDeltaSection_aux {L : PerfectTwoTermAmplitude X}
    (hL : IsRankZeroOn L) {V W : X.affineOpens} (h : V ≤ W) :
    localAppFun (chartDetComp L h).hom (V.1 : X.Opens) le_rfl (chartDeltaSection hL V) =
      globalRes (chartDet L W) ((W.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)) (chartDeltaTop hL W) := by
  have h₁ : (V.1 : X.Opens).ι ''ᵁ ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)) ≤ (V.1 : X.Opens) :=
    Scheme.Hom.image_preimage_le _ _
  have h₂ : (V.1 : X.Opens) ≤ (V.1 : X.Opens).ι ''ᵁ ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)) :=
    le_of_eq (Stacks.AlgebraicGeometry.ModuleLimits.image_preimage_of_le
      (le_refl (V.1 : X.Opens))).symm
  refine Eq.trans (localAppFun_eq (chartDetComp L h).hom (chartDeltaSection hL V) h₁ h₂) ?_
  refine Eq.trans (congrArg (fun z => resSec
      ((Scheme.Modules.pushforward (W.1 : X.Opens).ι).obj (chartDet L W)) h₂
      (Scheme.Modules.Hom.app (chartDetComp L h).hom ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)) z))
    (resSec_chartDeltaSection hL V h₁)) ?_
  refine Eq.trans (congrArg (fun z => resSec
      ((Scheme.Modules.pushforward (W.1 : X.Opens).ι).obj (chartDet L W)) h₂ z)
    (chartDetComp_hom_app hL h ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)))) ?_
  exact resSec_chartDeltaTop hL h h₂

/-- **The family of canonical sections is matched by the comparisons of the glueing datum.** Let
`X` be a scheme, `L` a perfect object of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]` of rank zero and
`V ≤ W` affine opens of `X`. The comparison
`AlgebraicGeometry.DeterminantTwoTerm.chartDetComp` carries the canonical section
`AlgebraicGeometry.DeterminantTwoTerm.chartDeltaSection` on the chart of `V` to the restriction to
`V` of the canonical section on the chart of `W`.

This is the compatibility that a family of sections of a glueing datum has to satisfy, so the
canonical sections on the affine charts define a canonical global section of the glued
determinant. -/
theorem localAppFun_chartDetComp_chartDeltaSection {L : PerfectTwoTermAmplitude X}
    (hL : IsRankZeroOn L) {V W : X.affineOpens} (h : V ≤ W) :
    localAppFun (chartDetComp L h).hom (V.1 : X.Opens) le_rfl (chartDeltaSection hL V) =
      ((Scheme.Modules.pushforward (AffineOpensGlue.chart X W)).obj (chartDet L W)).val.map
        (homOfLE (show (V.1 : X.Opens) ≤ (W.1 : X.Opens) from h)).op
        (chartDeltaSection hL W) :=
  (localAppFun_chartDeltaSection_aux hL h).trans (chartDeltaSection_restrict hL h).symm

end AlgebraicGeometry.DeterminantTwoTerm

end
