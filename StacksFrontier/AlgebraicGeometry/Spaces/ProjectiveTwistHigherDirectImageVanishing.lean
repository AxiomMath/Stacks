module

public import StacksFrontier.AlgebraicGeometry.AmpleProjectiveImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of the higher direct images of a large twist along a projective immersion

Let `i : X ⟶ P^n_Y` be a closed immersion of algebraic spaces over a scheme `S`, with `Y`
Noetherian, let `f : X ⟶ Y` be the composite with the projection, and put
`L = i^* O_{P^n_Y}(1)`.  Stacks 08AQ asserts that for a coherent `𝒪_X`-module `F` there is a
`d₀` with `R^p f_*(F ⊗ L^{⊗ d}) = 0` for all `d ≥ d₀` and all `p > 0`.

`P^n_Y` is the base change `Y ×_S P^n_S` of projective `n`-space over the base scheme, so the
diagram of the source is recorded as `AlgebraicGeometry.Space.ProjectiveSpaceImmersion`, a
cartesian square together with a closed immersion into its corner, and the twist is a
*definition*: the inverse image of the hyperplane sheaf of `P^n_S` along `X ⟶ P^n_Y ⟶ P^n_S`.

## Main definitions

* `AlgebraicGeometry.Space.ProjectiveSpaceImmersion`: the diagram of the source — relative
  projective `n`-space over an algebraic space `Y`, realised as `Y ×_S P^n_S`, together with a
  closed immersion of `X` into it.
* `AlgebraicGeometry.Space.ProjectiveSpaceImmersion.twist`: the twist
  `L = i^* O_{P^n_Y}(1)`.
* `AlgebraicGeometry.Space.tensorPow`: the tensor powers `L^{⊗ d}` of an `𝒪_Z`-module.
* `AlgebraicGeometry.Space.ChartwiseEventualTwistVanishing`: the hypothesis `h02O1`, the same
  eventual vanishing after base change to an étale scheme chart of the target.

## Main results

* `AlgebraicGeometry.Space.ProjectiveSpaceImmersion.relativelyRepresentable_proj` and
  `…relativelyRepresentable_hom`: the projection `P^n_Y ⟶ Y` and the composite `f : X ⟶ Y` are
  representable.
* `AlgebraicGeometry.Space.exists_isZero_rightDerived_modulePushforward_tensor_twist`:
  **Stacks 08AQ, with the scheme case carried as `h02O1`.**

## Implementation notes

*The reduction that is proved.*  The source's proof is one sentence: the assertion is étale
local on `Y`, so one reduces to `Y` the spectrum of a Noetherian ring, where `X` is a scheme and
Cohomology of Schemes, Lemma 30.16.2 (Stacks 02O1) applies.  The étale-local reduction is what
is proved here, by the two inputs the source names.  Equation 69.3.0.1 (Stacks 071Z),
`AlgebraicGeometry.Space.moduleHigherPushforwardChartBaseChangeIso`, identifies the restriction
of `R^p f_*` to an étale scheme chart `V` of `Y` with `R^p f'_*` of the restriction along the
base change `f' : V ×_Y X ⟶ V`, and a module on the small étale site of `Y` is zero as soon as
all those restrictions are, by
`AlgebraicGeometry.Space.isZero_iff_forall_isZero_etaleModulePullback_chartToSpace`.  The two
are combined by `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_chartwise`,
which is the same reduction already used for Stacks 073H in
`StacksFrontier/AlgebraicGeometry/Spaces/AffineHigherPushforwardVanishing.lean`.  Because a single
`d₀` has to serve every chart, the bound is quantified outside the chart in
`ChartwiseEventualTwistVanishing`; no quasi-compactness is then needed to combine bounds, and
none is used.

*Representability is proved, not assumed.*  Stacks 071Z applies to a representable morphism, and
the source does not pause over this.  Here it is discharged: `i` is representable because a
closed immersion of algebraic spaces is by definition
(`CategoryTheory.MorphismProperty.relative.rep`), the projection `P^n_Y ⟶ Y` is representable as
the base change of the morphism of schemes `P^n_S ⟶ S` along `Y ⟶ S`
(`CategoryTheory.Functor.relativelyRepresentable.map` and the base-change stability of
representability), and representable morphisms compose.

*What `h02O1` is.*  It is the conclusion after base change to an étale scheme chart of `Y`:
there the base is a scheme, which is the situation Stacks 02O1 is about.  It is therefore the
source's own reduction target rather than the conclusion itself; it is not, however, a small
piece of side-work, for two reasons.  Stacks 02O1 is proved only conditionally, in
`StacksFrontier/AlgebraicGeometry/RelativeAmpleTwistVanishing/Basic.lean`, under the hypothesis
`Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.VanishingOverAffineBase`, which is
absolute Serre vanishing over an affine base; and that statement is about
`AlgebraicGeometry.Scheme.Modules`, on the Zariski site,
whereas the higher direct images here live on the small étale sites.  Crossing between them is
Stacks 03DW, the keystone recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/AffineHigherPushforwardVanishing.lean` and carried as
`h03DW` there, and it is not available in this repository.  Discharging `h02O1` therefore needs
both of those, and the hypothesis is carried rather than proved.

*Where `Y` Noetherian and `F` coherent are used.*  Nowhere in the reduction; they are the
source's hypotheses and are what would discharge `h02O1`, so they are stated.  The source states
the conclusion for a coherent `F`, and coherence of a twist is available
(`AlgebraicGeometry.Space.isCoherent_tensorModule`, Stacks 07UE) but is not needed here.

*The twist.*  `O_{P^n_Y}(1)` is the inverse image of `O_{P^n_S}(1)` along the coordinate
projection, so `L = i^* O_{P^n_Y}(1)` is the inverse image of
`Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S` along `X ⟶ P^n_Y ⟶ P^n_S`,
and no twist on `P^n_Y` itself has to be constructed.  The hyperplane sheaf is a module on the
*scheme* `P^n_S`; `AlgebraicGeometry.Space.representedAssociatedModule` puts it on the small
étale site of the algebraic space `P^n_S` represents, and
`AlgebraicGeometry.Space.modulePullback` of Stacks 03LU moves it from there.  So the statement
below is not about an arbitrary invertible module, which would make it false.

*The tensor product and its powers.*  The tensor product is the symmetric monoidal structure
`AlgebraicGeometry.Space.modulesMonoidalCategory`, whose tensor product is the tensor sheaf of
Stacks 01CA and whose unit is `𝒪_Z` on the nose; it exists only at module universe `u`, which is
also the only module universe at which `AlgebraicGeometry.Space.modulePushforward` is declared,
so the whole file sits there.  `tensorPow L 0` is `𝒪_Z` and `tensorPow L 1` is `L`, with no
unitor in the way.

*Two local priority raises* are the ones
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleHigherPushforwardEtaleBaseChange.lean` documents:
with the module-universe-`max u v r w` instances of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Modules/CohomologyOfModules.lean` in the import
closure, search for
`Abelian` and `EnoughInjectives` on the modules at module universe `u` commits to them and then
fails on the universe constraint.  Both attributes are `local`.

*The degree* runs over `ℕ` in the injective-resolution convention
`CategoryTheory.Functor.rightDerived`, as in Stacks 071Z and Stacks 073H.

## References

* [Stacks Project, Tag 08AQ](https://stacks.math.columbia.edu/tag/08AQ)
* [Stacks Project, Tag 02O1](https://stacks.math.columbia.edu/tag/02O1)
* [Stacks Project, Tag 071Z](https://stacks.math.columbia.edu/tag/071Z)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

attribute [local instance] modulesMonoidalCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Projective space over the base scheme, as an object of the site -/

/-- The base scheme `S`, as an object of its own big fppf site. -/
def baseSiteObj : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))

/-- Projective `n`-space over the base scheme, as an object of the big fppf site over `S`,
carrying its canonical structure morphism. -/
noncomputable def projectiveSpaceSiteObj (n : ℕ)
    (hP : B.Contains (projectiveSpaceOver n S)) : BigFppfOver B S hS :=
  Over.mk (⟨projectiveSpaceOver n S ↘ S⟩ : B.obj hP ⟶ B.obj hS)

/-- The structure morphism `P^n_S ⟶ S` of projective `n`-space over the base scheme, read in
the big fppf site over `S`. -/
noncomputable def projectiveSpaceSiteObjToBase (n : ℕ)
    (hP : B.Contains (projectiveSpaceOver n S)) :
    projectiveSpaceSiteObj B S hS n hP ⟶ baseSiteObj B S hS :=
  Over.homMk (projectiveSpaceSiteObj B S hS n hP).hom

/-! ### The diagram of the source -/

/-- **The diagram of Stacks 08AQ.** Relative projective `n`-space over an algebraic space `Y`
over `S`, realised as the base change `P^n_Y = Y ×_S P^n_S` of projective `n`-space over the
base scheme, together with a closed immersion `i : X ⟶ P^n_Y`. -/
structure ProjectiveSpaceImmersion (n : ℕ) (hP : B.Contains (projectiveSpaceOver n S))
    (X Y : AlgebraicSpaces B S hS) where
  /-- The algebraic space `P^n_Y`. -/
  projSpace : AlgebraicSpaces B S hS
  /-- The projection `P^n_Y ⟶ Y`. -/
  proj : projSpace ⟶ Y
  /-- The homogeneous coordinates `P^n_Y ⟶ P^n_S`. -/
  coord : projSpace ⟶ schemeSpace (projectiveSpaceSiteObj B S hS n hP)
  /-- The structure morphism of `Y` over the base scheme. -/
  base : Y ⟶ schemeSpace (baseSiteObj B S hS)
  /-- `P^n_Y` is the base change `Y ×_S P^n_S`. -/
  isPullback : IsPullback proj.hom coord.hom base.hom
    (schemeSpaceMap (projectiveSpaceSiteObjToBase B S hS n hP)).hom
  /-- The closed immersion `i : X ⟶ P^n_Y`. -/
  imm : X ⟶ projSpace
  /-- `i` is a closed immersion. -/
  imm_isClosedImmersion : IsClosedImmersion B S hS imm.hom

namespace ProjectiveSpaceImmersion

variable {B S hS} {n : ℕ} {hP : B.Contains (projectiveSpaceOver n S)}
  {X Y : AlgebraicSpaces B S hS}

/-- The morphism `f : X ⟶ Y` of the diagram: the closed immersion followed by the projection
of `P^n_Y`. -/
abbrev hom (D : ProjectiveSpaceImmersion B S hS n hP X Y) : X ⟶ Y := D.imm ≫ D.proj

/-- The projection `P^n_Y ⟶ Y` is representable, being the base change of the morphism of
schemes `P^n_S ⟶ S` along the structure morphism of `Y`. -/
theorem relativelyRepresentable_proj (D : ProjectiveSpaceImmersion B S hS n hP X Y) :
    yoneda.relativelyRepresentable D.proj.hom :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback D.isPullback.flip
    (Functor.relativelyRepresentable.map _ (projectiveSpaceSiteObjToBase B S hS n hP))

/-- The morphism `f : X ⟶ Y` of the diagram is representable: a closed immersion of algebraic
spaces is representable by definition, the projection is by
`AlgebraicGeometry.Space.ProjectiveSpaceImmersion.relativelyRepresentable_proj`, and
representable morphisms compose. -/
theorem relativelyRepresentable_hom (D : ProjectiveSpaceImmersion B S hS n hP X Y) :
    yoneda.relativelyRepresentable D.hom.hom :=
  MorphismProperty.comp_mem _ _ _ D.imm_isClosedImmersion.rep D.relativelyRepresentable_proj

/-- The hyperplane sheaf `O_{P^n_Y}(1)`: the inverse image of the hyperplane sheaf of `P^n_S`
along the homogeneous coordinates. -/
noncomputable def twistOne (D : ProjectiveSpaceImmersion B S hS n hP X Y) :
    Modules.{u, u} B S hS D.projSpace.1 D.projSpace.2 :=
  (modulePullback B S hS D.coord).obj
    ((representedAssociatedModule B S hS (projectiveSpaceSiteObj B S hS n hP)
        (schemeSpace (projectiveSpaceSiteObj B S hS n hP)).2).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S))

/-- **The twist `L = i^* O_{P^n_Y}(1)` of Stacks 08AQ**: the inverse image of the hyperplane
sheaf of `P^n_S` along `X ⟶ P^n_Y ⟶ P^n_S`. -/
@[stacks 08AQ "the twist L = i^* O_{P^n_Y}(1) of the statement"]
noncomputable def twist (D : ProjectiveSpaceImmersion B S hS n hP X Y) :
    Modules.{u, u} B S hS X.1 X.2 :=
  (modulePullback B S hS D.imm).obj D.twistOne

end ProjectiveSpaceImmersion

/-! ### Tensor powers -/

/-- The tensor powers `L^{⊗ d}` of an `𝒪_Z`-module on an algebraic space, for the tensor
product of Stacks 01CA.  The zeroth power is `𝒪_Z`, the tensor unit, and the first is `L`. -/
noncomputable def tensorPow {Z : AlgebraicSpaces B S hS}
    (L : Modules.{u, u} B S hS Z.1 Z.2) : ℕ → Modules.{u, u} B S hS Z.1 Z.2
  | 0 => 𝟙_ (Modules.{u, u} B S hS Z.1 Z.2)
  | 1 => L
  | (d + 2) => tensorPow L (d + 1) ⊗ L

/-! ### Stacks 08AQ, reduced to the scheme case along étale scheme charts -/

/-- The hypothesis `h02O1` of
`AlgebraicGeometry.Space.exists_isZero_rightDerived_modulePushforward_tensor_twist`: a single
`d₀` such that for every `d ≥ d₀`, every `p > 0` and every étale scheme chart `V` of `Y`, the
base change `f' : V ×_Y X ⟶ V` has vanishing degree-`p` higher direct image on the restriction
of `F ⊗ L^{⊗ d}`.

Over the chart the base is a scheme, so this is the situation of Stacks 02O1; see the
implementation notes of this file for what discharging it would take. -/
def ChartwiseEventualTwistVanishing {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (F L : Modules.{u, u} B S hS X.1 X.2) : Prop :=
  ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ p : ℕ, 0 < p →
    ChartwiseIsZeroHigherDirectImage B S hS f hf (F ⊗ tensorPow B S hS L d) p

/-- **Stacks 08AQ, with the scheme case carried as `h02O1`.**

Let `i : X ⟶ P^n_Y` be a closed immersion of algebraic spaces over `S` with `Y` Noetherian, let
`f : X ⟶ Y` be the composite with the projection and let `L = i^* O_{P^n_Y}(1)`.  For a coherent
`𝒪_X`-module `F` there is a `d₀` such that

`R^p f_*(F ⊗ L^{⊗ d}) = 0` for all `d ≥ d₀` and all `p > 0`.

The source's proof is the étale-local reduction on `Y`, and that is what is proved: Equation
69.3.0.1 (Stacks 071Z) identifies the restriction of `R^p f_*` to an étale scheme chart of `Y`
with the corresponding higher direct image of the base change, and a module on the small étale
site of `Y` vanishes as soon as all those restrictions do.  Representability of `f`, which
Stacks 071Z needs, is supplied by
`AlgebraicGeometry.Space.ProjectiveSpaceImmersion.relativelyRepresentable_hom`.  What remains is
the conclusion over a scheme chart, which is where the source cites Stacks 02O1; it is carried
as `h02O1` and is not proved.  Noetherianity of `Y` and coherence of `F` are the source's
hypotheses and are what would discharge `h02O1`; the reduction itself uses neither. -/
@[stacks 08AQ "the étale-local reduction of the source's proof, by Stacks 071Z, with \
representability of the composite proved; the scheme case, where the source cites Stacks 02O1, \
is carried as the hypothesis h02O1 and is not proved — note that h02O1 is this same eventual \
vanishing after base change to an étale scheme chart of Y, so it is the source's reduction \
target rather than side-work, and discharging it needs both the conditional repository form of \
Stacks 02O1 and the étale-versus-Zariski comparison Stacks 03DW"]
theorem exists_isZero_rightDerived_modulePushforward_tensor_twist
    (hZ : B.Contains (⊤_ Scheme.{u})) (n : ℕ)
    (hP : B.Contains (projectiveSpaceOver n S)) {X Y : AlgebraicSpaces B S hS}
    (D : ProjectiveSpaceImmersion B S hS n hP X Y)
    (hY : IsNoetherian B S hS hZ Y.1) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : IsCoherent B S hS X.1 X.2 F)
    (h02O1 : ChartwiseEventualTwistVanishing B S hS D.hom D.relativelyRepresentable_hom F
      D.twist) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ p : ℕ, 0 < p →
      IsZero (((modulePushforward B S hS D.hom).rightDerived p).obj
        (F ⊗ tensorPow B S hS D.twist d)) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := hY
  have := hF
  obtain ⟨d₀, h⟩ := h02O1
  exact ⟨d₀, fun d hd p hp =>
    isZero_rightDerived_modulePushforward_of_chartwise B S hS D.hom
      D.relativelyRepresentable_hom _ p (h d hd p hp)⟩

end AlgebraicGeometry.Space

end
