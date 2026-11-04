module

public import StacksFrontier.AlgebraicGeometry.AmpleFibreNeighbourhood.FibreSectionToolkit
public import StacksFrontier.AlgebraicGeometry.AmpleFibreNeighbourhood.FibreSectionsSurjective
public import StacksFrontier.AlgebraicGeometry.AmpleFibreNeighbourhood.StalkSectionDescent
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeFactorization
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.ModulesOverOpen
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine

/-!
# Every section of a large twist on the fibre extends to a neighbourhood of the point

Let `f : X ⟶ S` be proper with `S` locally Noetherian, let `ℒ` be an invertible `𝒪_X`-module and
let `y` be a point of `S` at which `ℒ_y` is ample on the fibre `X_y`.  This file proves that for
every large `d` **every** section of `ℒ ^⊗ d` on the fibre `X_y` is the restriction of a section
of `ℒ ^⊗ d` over `f ⁻¹ᵁ U` for some open neighbourhood `U` of `y`:

`Γ(ℒ ^⊗ d, f ⁻¹ᵁ U) ⟶ Γ(X_y, (ℒ ^⊗ d)|_{X_y})` is jointly surjective over `U ∋ y`.

This is the lift half of the proof of [Stacks, Tag 0D2N] — the last step of the hard half of that
tag, where the surjectivity supplied by assertion (B) of [Stacks, Tag 0D2M] over the local base
`𝒪_{S, y}` is spread back out to a genuine open of `S`.

## Main results

* `Stacks.AmpleFibreNeighbourhood.exists_mem_pullbackSection_fiberι_eq`: **the theorem.**  There
  is a `d₀` such that for every `d ≥ d₀` and every `t : Γ(X_y, (ℒ ^⊗ d)|_{X_y})` there are an
  open `U ∋ y` and an `a : Γ(ℒ ^⊗ d, f ⁻¹ᵁ U)` whose restriction to the fibre,
  `AlgebraicGeometry.Scheme.Modules.pullbackSection` along `AlgebraicGeometry.Scheme.Hom.fiberι`,
  is `t`.

## The route

Write `c = S.fromSpecStalk y : Spec 𝒪_{S, y} ⟶ S`, `X' = X ×_S Spec 𝒪_{S, y}`,
`g' = pullback.fst f c : X' ⟶ X`, `f' = pullback.snd f c : X' ⟶ Spec 𝒪_{S, y}`,
`M = ℒ ^⊗ d` and let `V ⊂ X'` be the closed subscheme cut out by `𝔪 𝒪_{X'}`
(`Stacks.AmpleFibreNeighbourhood.stalkBaseChangeFibreIdeal`), with closed immersion
`v = V ⟶ X'`.  Nothing here is new mathematics; all three steps are in the library and the content is
their composition.

* **Surjectivity on `V`.**
  `Stacks.AmpleFibreNeighbourhood.exists_surjective_pullbackGlobalSections_stalkFibre` is
  assertion (B) of [Stacks, Tag 0D2M] over the local base: it produces the `d₀` such that for
  `d ≥ d₀` restriction of sections `Γ(X', (g')^* M) ⟶ Γ(V, v^* (g')^* M)` is surjective.  That
  `d₀` is the one this file returns.

* **Descent from `Spec 𝒪_{S, y}` to a neighbourhood**, in
  `Stacks.AmpleFibreNeighbourhood.exists_mem_pullbackSection_pullbackFst_eq` below.  Degree-zero
  flat base change identifies `Γ(X', (g')^* M)` with `Γ(Spec 𝒪_{S, y}, c^* f_* M)`: the
  comparison is `Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans`, an isomorphism
  by `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat` —
  [Stacks, Tag 02KH] part (1) at `i = 0` — since `c` is flat
  (`AlgebraicGeometry.flat_fromSpecStalk`), `f` is quasi-compact and quasi-separated and `f_* M`
  is quasi-coherent
  (`Stacks.AlgebraicGeometry.FlatBaseChange.isQuasicoherent_pushforward_of_qcqs`).  A section of
  `c^* f_* M` comes from a section of `f_* M` over an open `U ∋ y` by
  `Stacks.AmpleFibreNeighbourhood.exists_mem_pullbackSection_eq`, and
  `Γ(f_* M, U) = Γ(M, f ⁻¹ᵁ U)`.  The step that makes this possible is that the normalisation
  `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.baseChangeNatTrans_app_pullbackSection` is
  available **at an arbitrary open of the base** and not only over the whole space;  it is used
  here at the open `⊤` of `Spec 𝒪_{S, y}` but at a general `U` upstairs.  This is the same
  assembly as `Stacks.AlgebraicGeometry.FlatBaseChange.exists_linearEquiv_pushforwardStalk_`
  `stalkBaseChange`, with the germ replaced by the section it is the germ of.

* **Moving `V` onto `X_y`.**  `Stacks.AmpleFibreNeighbourhood.stalkFibreIso` identifies `V` with
  the fibre `X_y`, compatibly with the two morphisms to `X`:
  `Stacks.AmpleFibreNeighbourhood.stalkFibreIso_hom_fiberι` says `ε.hom ≫ f.fiberι y = v ≫ g'`.
  Restriction of a section along either composite is therefore the same, by
  `AlgebraicGeometry.Scheme.Modules.pullbackSection_comp` (functoriality in the morphism, at
  general opens) and `AlgebraicGeometry.Scheme.Modules.pullbackSection_congr` (transport along
  the equality of morphisms), and the restriction along the isomorphism `ε.hom` may then be
  cancelled because it is injective
  (`Stacks.AmpleFibreNeighbourhood.injective_pullbackGlobalSections_of_isIso`).  The two
  comparison isomorphisms of modules that appear are cancelled the same way, through
  `CategoryTheory.ConcreteCategory.bijective_of_isIso` and
  `AlgebraicGeometry.Scheme.Modules.Hom.isIso_iff_isIso_app`.

## Implementation notes

Every map in the proof is restriction of sections at the pair of opens it is naturally defined
at, `AlgebraicGeometry.Scheme.Modules.pullbackSection`, rather than
`AlgebraicGeometry.pullbackGlobalSections`;  the two agree over the whole space by
`AlgebraicGeometry.pullbackGlobalSections_eq_pullbackSection`, which is `rfl`, so the statements
quoted from the surjectivity step — which are phrased with `pullbackGlobalSections` — are used
verbatim.  The opens `f' ⁻¹ᵁ ⊤` and `⊤` of `X'`, which the normalisation of the base-change
comparison and the surjectivity statement respectively produce, are likewise equal by `rfl`
(`AlgebraicGeometry.Scheme.Hom.preimage_top`), as in
`../FlatBaseChange/Stalk.lean`.

The local ring `𝒪_{S, y}` is never named through `CommRingCat.of`: everything quoted below is
already stated at `AlgebraicGeometry.Scheme.fromSpecStalk` itself, so the two syntactically
different `CommRing` instances on `↥(S.presheaf.stalk y)` — which block `rw` and `simp` inside
terms mentioning the stalk, and which force the one `show` in
`../AmpleFibreNeighbourhood/FibreSectionsSurjective.lean` — never come into contact.

## No attribute

No `@[stacks]` attribute is attached.  This is the lift half of the proof of [Stacks, Tag 0D2N]
and not a numbered result of the Stacks project in its own right: the tag's statement is the
existence of the relatively ample neighbourhood, which this file does not yet assert.  The
attribute of [Stacks, Tag 0D2M], whose assertion (B) is the input used here, sits on
`Stacks.FormalFunctions.exists_isZero_stalk_rightDerived_and_surjective_fiberTwist`, and the
specialisations of [Stacks, Tag 02KH] used through the base-change comparison carry none either,
for the reason recorded in `../FlatBaseChange/Stalk.lean`.

## References

* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.AffinePushforward (baseChangeNatTrans)
open Stacks.AlgebraicGeometry.FlatBaseChange (isQuasicoherent_pushforward_of_qcqs)
open Stacks.AlgebraicGeometry.FlatBaseChangeCohomology
  (baseChangeNatTrans_app_pullbackSection isIso_baseChangeNatTrans_of_flat)

universe u

namespace Stacks.AmpleFibreNeighbourhood

/-- **The comparison that carries a section on the fibre to a section on the subscheme cut out by
`𝔪 𝒪`.**  For an isomorphism `ε : P ≅ Q`, morphisms `i : Q ⟶ Z`, `v : P ⟶ R`, `g : R ⟶ Z` with
`ε.hom ≫ i = v ≫ g`, and a module `M` on `Z`, a global section of `i^* M` is restricted along
`ε.hom` and then reassociated along the square: first through
`AlgebraicGeometry.Scheme.Modules.pullbackComp` into `(ε.hom ≫ i)^* M`, then through
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` into `(v ≫ g)^* M`, then back through
`AlgebraicGeometry.Scheme.Modules.pullbackComp` into `v^* g^* M`.

It is a private definition because it is bookkeeping: it exists only to name the element the
surjectivity of restriction along `v` is applied to, in
`Stacks.AmpleFibreNeighbourhood.exists_mem_pullbackSection_fiberι_eq`.  Its one property is
`Stacks.AmpleFibreNeighbourhood.pullbackSection_eq_of_pullbackGlobalSections_eq`. -/
private def fibreComparison {P Q R Z : Scheme.{u}} (ε : P ≅ Q) (i : Q ⟶ Z) (v : P ⟶ R)
    (g : R ⟶ Z) (hcomp : ε.hom ≫ i = v ≫ g) (M : Z.Modules)
    (t : Γ((Scheme.Modules.pullback i).obj M, ⊤)) :
    Γ((Scheme.Modules.pullback v).obj ((Scheme.Modules.pullback g).obj M), ⊤) :=
  Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp v g).inv.app M) ⊤
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hcomp).hom.app M) ⊤
      (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp ε.hom i).hom.app M) ⊤
        (pullbackGlobalSections ε.hom ((Scheme.Modules.pullback i).obj M) t)))

/-- Sections over any open of an isomorphism of modules are in bijection. -/
private theorem bijective_app_of_isIso {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) [IsIso φ]
    (U : X.Opens) : Function.Bijective (Scheme.Modules.Hom.app φ U) :=
  have : IsIso (Scheme.Modules.Hom.app φ U) := Scheme.Modules.Hom.isIso_iff_isIso_app.mp ‹_› U
  ConcreteCategory.bijective_of_isIso _

/-- If all of `R` lies over `U` along `g`, then all of `P` lies over `U` along `v ≫ g`. -/
private theorem top_le_comp_preimage {P R Z : Scheme.{u}} (v : P ⟶ R) (g : R ⟶ Z) (U : Z.Opens)
    (hg : (⊤ : R.Opens) ≤ g ⁻¹ᵁ U) : (⊤ : P.Opens) ≤ (v ≫ g) ⁻¹ᵁ U := by
  intro z _
  show (v ≫ g).base z ∈ U
  rw [Scheme.Hom.comp_apply]
  exact hg (show v.base z ∈ (⊤ : R.Opens) from trivial)

/-- **A section on `X ×_S Spec 𝒪_{S, y}` is the restriction of a section over `f ⁻¹ᵁ U` for some
open `U ∋ y`.**  For `f : X ⟶ S` quasi-compact and quasi-separated, `M` a quasi-coherent
`𝒪_X`-module and `y` a point of `S`, every global section of the pullback of `M` along the first
projection `X ×_S Spec 𝒪_{S, y} ⟶ X` is the pullback of a section of `M` over `f ⁻¹ᵁ U` for some
open neighbourhood `U` of `y`.

This is the step that undoes the replacement of `S` by `Spec 𝒪_{S, y}`.  Degree-zero flat base
change along `c = S.fromSpecStalk y`, which is flat by
`AlgebraicGeometry.flat_fromSpecStalk`, identifies the global sections upstairs with
`Γ(Spec 𝒪_{S, y}, c^* f_* M)`: the comparison is
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans`, invertible by
`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat`
([Stacks, Tag 02KH] part (1) at `i = 0`) because `f_* M` is quasi-coherent
(`Stacks.AlgebraicGeometry.FlatBaseChange.isQuasicoherent_pushforward_of_qcqs`), read over the
open `⊤` of `Spec 𝒪_{S, y}` through
`AlgebraicGeometry.Scheme.Modules.Hom.isIso_iff_isIso_app`.  A section of `c^* f_* M` comes from
an (affine) open neighbourhood of `y` by
`Stacks.AmpleFibreNeighbourhood.exists_mem_pullbackSection_eq`, and the two descriptions are
matched by the normalisation
`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.baseChangeNatTrans_app_pullbackSection`, whose
availability at an arbitrary open of the base is what makes the step possible.  The affineness of
`U` is dropped: it is not used downstream.

The section over `U` of the direct image `f_* M` *is* the section of `M` over `f ⁻¹ᵁ U` — the two
groups are equal, not merely isomorphic — so no transport appears. -/
private theorem exists_mem_pullbackSection_pullbackFst_eq {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] (M : X.Modules) [M.IsQuasicoherent] (y : S)
    (s : Γ((Scheme.Modules.pullback (pullback.fst f (S.fromSpecStalk y))).obj M, ⊤)) :
    ∃ (U : S.Opens) (hy : y ∈ U) (a : Γ(M, f ⁻¹ᵁ U)),
      Scheme.Modules.pullbackSection (pullback.fst f (S.fromSpecStalk y)) M (f ⁻¹ᵁ U) ⊤
        (Stacks.FormalFunctions.top_le_preimage_pullbackFst f y U hy) a = s := by
  have : ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_qcqs f M
  have : Flat (S.fromSpecStalk y) := flat_fromSpecStalk S y
  have H : IsPullback (pullback.fst f (S.fromSpecStalk y))
      (pullback.snd f (S.fromSpecStalk y)) f (S.fromSpecStalk y) :=
    IsPullback.of_hasPullback f (S.fromSpecStalk y)
  have : IsIso ((baseChangeNatTrans H.w).app M) := isIso_baseChangeNatTrans_of_flat H M
  obtain ⟨n, hn⟩ := (bijective_app_of_isIso ((baseChangeNatTrans H.w).app M)
    (⊤ : (Spec (S.presheaf.stalk y)).Opens)).surjective s
  obtain ⟨U, -, hy, a, ha⟩ :=
    exists_mem_pullbackSection_eq ((Scheme.Modules.pushforward f).obj M) y n
  -- The fibre product lies over `U` along both projections, by the cartesian square.
  have hpre : pullback.snd f (S.fromSpecStalk y) ⁻¹ᵁ (S.fromSpecStalk y ⁻¹ᵁ U) ≤
      pullback.fst f (S.fromSpecStalk y) ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    intro z hz
    have hz' : ((pullback.snd f (S.fromSpecStalk y) ≫ S.fromSpecStalk y).base z) ∈ U := hz
    rw [← Limits.pullback.condition] at hz'
    exact hz'
  refine ⟨U, hy, a, ?_⟩
  exact (baseChangeNatTrans_app_pullbackSection H.w M U ⊤
    (le_preimage_fromSpecStalk_of_mem y U hy) hpre
    (Stacks.FormalFunctions.top_le_preimage_pullbackFst f y U hy) a).symm.trans
      ((congrArg (fun z => Scheme.Modules.Hom.app ((baseChangeNatTrans H.w).app M)
        (⊤ : (Spec (S.presheaf.stalk y)).Opens) z) ha).trans hn)

/-- **Cancelling the identification of the two models of the fibre.**  Let `ε : P ≅ Q` be an
isomorphism of schemes sitting in a commuting square `ε.hom ≫ i = v ≫ g` with `i : Q ⟶ Z`,
`v : P ⟶ R` and `g : R ⟶ Z`, let `M` be a module on `Z`, let `U` be an open of `Z` lain over by
all of `Q` and all of `R`, and let `x : Γ(M, U)`.  If a global section `s` of `g^* M` is the
restriction of `x` and is carried to the comparison
`Stacks.AmpleFibreNeighbourhood.fibreComparison` of a global section `t` of `i^* M` by
restriction along `v`, then `t` is the restriction of `x` along `i`.

Both sides are compared inside `Γ((v ≫ g)^* M, ⊤)`.  Restriction along a composite is
restriction twice, `AlgebraicGeometry.Scheme.Modules.pullbackSection_comp`, applied once to
`ε.hom` and `i` and once to `v` and `g`;  the two are matched by
`AlgebraicGeometry.Scheme.Modules.pullbackSection_congr`, the transport along the equality of the
composites.  The three maps that have been applied are then cancelled: the two applications of a
comparison isomorphism of modules by `CategoryTheory.ConcreteCategory.bijective_of_isIso` and
`AlgebraicGeometry.Scheme.Modules.Hom.isIso_iff_isIso_app`, and the restriction along `ε.hom` by
`Stacks.AmpleFibreNeighbourhood.injective_pullbackGlobalSections_of_isIso`.

The inverse of the second comparison, which `fibreComparison` ends with, is undone by
`AlgebraicGeometry.SectionsEqualizer.moduleIso_hom_inv_app`.  Restriction of sections over the
whole space is `AlgebraicGeometry.pullbackGlobalSections` by
`AlgebraicGeometry.pullbackGlobalSections_eq_pullbackSection`. -/
private theorem pullbackSection_eq_of_pullbackGlobalSections_eq {P Q R Z : Scheme.{u}}
    (ε : P ≅ Q) (i : Q ⟶ Z) (v : P ⟶ R) (g : R ⟶ Z) (hcomp : ε.hom ≫ i = v ≫ g)
    (M : Z.Modules) (U : Z.Opens) (hi : (⊤ : Q.Opens) ≤ i ⁻¹ᵁ U)
    (hg : (⊤ : R.Opens) ≤ g ⁻¹ᵁ U) (x : Γ(M, U))
    (t : Γ((Scheme.Modules.pullback i).obj M, ⊤))
    (s : Γ((Scheme.Modules.pullback g).obj M, ⊤))
    (hs : Scheme.Modules.pullbackSection g M U ⊤ hg x = s)
    (hA : pullbackGlobalSections v ((Scheme.Modules.pullback g).obj M) s =
      fibreComparison ε i v g hcomp M t) :
    Scheme.Modules.pullbackSection i M U ⊤ hi x = t := by
  have hε : (⊤ : P.Opens) ≤ ε.hom ⁻¹ᵁ (⊤ : Q.Opens) := ε.hom.preimage_top.ge
  have hv : (⊤ : P.Opens) ≤ v ⁻¹ᵁ (⊤ : R.Opens) := v.preimage_top.ge
  have hεi := top_le_comp_preimage ε.hom i U hi
  have hvg := top_le_comp_preimage v g U hg
  -- The restriction of `x` to `P`, computed along `ε.hom ≫ i`.
  have hL : Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hcomp).hom.app M) ⊤
        (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp ε.hom i).hom.app M) ⊤
          (pullbackGlobalSections ε.hom ((Scheme.Modules.pullback i).obj M)
            (Scheme.Modules.pullbackSection i M U ⊤ hi x))) =
      Scheme.Modules.pullbackSection (v ≫ g) M U ⊤ hvg x :=
    (congrArg (fun z => Scheme.Modules.Hom.app
          ((Scheme.Modules.pullbackCongr hcomp).hom.app M) (⊤ : P.Opens) z)
        (Scheme.Modules.pullbackSection_comp ε.hom i M U ⊤ ⊤ hi hε hεi x)).trans
      (Scheme.Modules.pullbackSection_congr hcomp M U ⊤ hεi hvg x)
  -- The comparison of `t`, with `Stacks.AmpleFibreNeighbourhood.fibreComparison` unfolded, is the
  -- restriction along `v` of the restriction of `x` along `g`.
  have hx : Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp v g).inv.app M) ⊤
        (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hcomp).hom.app M) ⊤
          (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp ε.hom i).hom.app M) ⊤
            (pullbackGlobalSections ε.hom ((Scheme.Modules.pullback i).obj M) t))) =
      pullbackGlobalSections v ((Scheme.Modules.pullback g).obj M)
        (Scheme.Modules.pullbackSection g M U ⊤ hg x) :=
    hA.symm.trans (congrArg
      (fun z => pullbackGlobalSections v ((Scheme.Modules.pullback g).obj M) z) hs.symm)
  -- The same element, computed along `v ≫ g` from the section `s` that came from `U`.
  have hcv : Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp v g).hom.app M) ⊤
        (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp v g).inv.app M) ⊤
          (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hcomp).hom.app M) ⊤
            (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp ε.hom i).hom.app M) ⊤
              (pullbackGlobalSections ε.hom ((Scheme.Modules.pullback i).obj M) t)))) =
      Scheme.Modules.pullbackSection (v ≫ g) M U ⊤ hvg x :=
    (congrArg (fun z => Scheme.Modules.Hom.app
          ((Scheme.Modules.pullbackComp v g).hom.app M) (⊤ : P.Opens) z) hx).trans
      (Scheme.Modules.pullbackSection_comp v g M U ⊤ ⊤ hg hv hvg x)
  have hR : Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hcomp).hom.app M) ⊤
        (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp ε.hom i).hom.app M) ⊤
          (pullbackGlobalSections ε.hom ((Scheme.Modules.pullback i).obj M) t)) =
      Scheme.Modules.pullbackSection (v ≫ g) M U ⊤ hvg x :=
    (SectionsEqualizer.moduleIso_hom_inv_app ((Scheme.Modules.pullbackComp v g).app M)
      (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hcomp).hom.app M) ⊤
        (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp ε.hom i).hom.app M) ⊤
          (pullbackGlobalSections ε.hom
            ((Scheme.Modules.pullback i).obj M) t)))).symm.trans hcv
  exact injective_pullbackGlobalSections_of_isIso ε.hom ((Scheme.Modules.pullback i).obj M)
    ((bijective_app_of_isIso ((Scheme.Modules.pullbackComp ε.hom i).hom.app M) ⊤).injective
      ((bijective_app_of_isIso ((Scheme.Modules.pullbackCongr hcomp).hom.app M) ⊤).injective
        (hL.trans hR.symm)))

/-- **Every section of a large twist on the fibre `X_y` is the restriction of a section over
`f ⁻¹ᵁ U` for some open `U ∋ y`.**  Let `f : X ⟶ S` be proper with `S` locally Noetherian, let
`ℒ` be an invertible `𝒪_X`-module and let `y` be a point of `S` at which the restriction `ℒ_y`
is ample on the fibre `X_y`.  Then there is a `d₀` such that for every `d ≥ d₀` and every section
`t` of `(ℒ ^⊗ d)|_{X_y}` on the whole fibre there are an open neighbourhood `U` of `y` in `S` and
a section `a` of `ℒ ^⊗ d` over `f ⁻¹ᵁ U` restricting to `t`.

This is the lift half of the proof of [Stacks, Tag 0D2N], and it is the composition of three
facts from the library, laid out in the module docstring: assertion (B) of [Stacks, Tag 0D2M] over the
local base `𝒪_{S, y}`
(`Stacks.AmpleFibreNeighbourhood.exists_surjective_pullbackGlobalSections_stalkFibre`), the
descent of a section from `Spec 𝒪_{S, y}` to a neighbourhood of `y`
(`Stacks.AmpleFibreNeighbourhood.exists_mem_pullbackSection_pullbackFst_eq`, which is
degree-zero flat base change along `AlgebraicGeometry.Scheme.fromSpecStalk` followed by
`Stacks.AmpleFibreNeighbourhood.exists_mem_pullbackSection_eq`), and the identification
`Stacks.AmpleFibreNeighbourhood.stalkFibreIso` of the subscheme of `X ×_S Spec 𝒪_{S, y}` cut out
by `𝔪 𝒪` with the fibre `X_y`, which
`Stacks.AmpleFibreNeighbourhood.pullbackSection_eq_of_pullbackGlobalSections_eq` cancels.

No `@[stacks]` attribute is attached: this is one half of the proof of [Stacks, Tag 0D2N] rather
than a numbered result, and the attribute of [Stacks, Tag 0D2M], whose assertion (B) is used
here, sits on
`Stacks.FormalFunctions.exists_isZero_stalk_rightDerived_and_surjective_fiberTwist`. -/
theorem exists_mem_pullbackSection_fiberι_eq {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    [IsLocallyNoetherian S] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (y : S)
    (hL : Stacks.Ample.IsAmple (f.fiber y)
      (Stacks.AmpleLocallyClosed.pullbackModule (f.fiberι y) L)) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      ∀ t : Γ((AlgebraicGeometry.Scheme.Modules.pullback (f.fiberι y)).obj
          (Stacks.Ample.tensorPowModule X L d), ⊤),
        ∃ (U : S.Opens) (hy : y ∈ U) (a : Γ(Stacks.Ample.tensorPowModule X L d, f ⁻¹ᵁ U)),
          AlgebraicGeometry.Scheme.Modules.pullbackSection (f.fiberι y)
              (Stacks.Ample.tensorPowModule X L d) (f ⁻¹ᵁ U) ⊤
              (Stacks.FormalFunctions.top_le_preimage_fiberι f y U hy) a = t := by
  obtain ⟨d₀, hd₀⟩ := exists_surjective_pullbackGlobalSections_stalkFibre f L y hL
  refine ⟨d₀, fun d hd t => ?_⟩
  obtain ⟨s, hs⟩ := hd₀ d hd (fibreComparison (stalkFibreIso f y) (f.fiberι y)
    (stalkBaseChangeFibreIdeal f y).subschemeι (pullback.fst f (S.fromSpecStalk y))
    (stalkFibreIso_hom_fiberι f y) (Stacks.Ample.tensorPowModule X L d) t)
  obtain ⟨U, hy, a, ha⟩ :=
    exists_mem_pullbackSection_pullbackFst_eq f (Stacks.Ample.tensorPowModule X L d) y s
  exact ⟨U, hy, a, pullbackSection_eq_of_pullbackGlobalSections_eq (stalkFibreIso f y)
    (f.fiberι y) (stalkBaseChangeFibreIdeal f y).subschemeι
    (pullback.fst f (S.fromSpecStalk y)) (stalkFibreIso_hom_fiberι f y)
    (Stacks.Ample.tensorPowModule X L d) (f ⁻¹ᵁ U)
    (Stacks.FormalFunctions.top_le_preimage_fiberι f y U hy)
    (Stacks.FormalFunctions.top_le_preimage_pullbackFst f y U hy) a t s ha hs⟩

end Stacks.AmpleFibreNeighbourhood

end
