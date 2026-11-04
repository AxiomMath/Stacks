module

public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsPullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveTwistHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.ToposModuleDerivedBaseChangeHigher
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# The situation of a proper algebraic space with an ample scheme fibre

Let `Y` be a Noetherian scheme of the big fppf site over `S`, `f : X ⟶ Y` a proper morphism from
an algebraic space, `ℒ` an invertible and `ℱ` a coherent `𝒪_X`-module, and `y ∈ Y` a point whose
fibre `X_y` is a scheme on which the restriction of `ℒ` is ample.  Stacks 0D39 produces a `d₀`
such that for all `d ≥ d₀`, with `𝒢_d = ℱ ⊗ ℒ^{⊗ d}`,

* `(R^p f_* 𝒢_d)_y = 0` for `p > 0`, and
* `f_*(𝒢_d)_y ⟶ H^0(X_y, 𝒢_d|_{X_y})` is surjective.

This file fixes the vocabulary in which that conclusion is stated, and states it as the
proposition `AlgebraicGeometry.Space.AmpleSchemeFibreTwistConclusion`; the theorem asserting it is
proved elsewhere.

## Main definitions

* `AlgebraicGeometry.Space.residuePointObject`: the spectrum of the residue field `κ(y)` of a
  point of the scheme underlying an object `Y` of the site, as an object of the site, and
  `AlgebraicGeometry.Space.residuePointHom` its canonical morphism to `Y`.
* `AlgebraicGeometry.Space.zariskiModule`: the restriction of a module on the algebraic space
  represented by `Y` to the Zariski site of the scheme underlying `Y`; stalks at points of `Y`
  are taken there.
* `AlgebraicGeometry.Space.spaceModuleSections`: the global sections `Γ(Z, 𝓜)` of a module on an
  algebraic space.
* `AlgebraicGeometry.Space.restrictSectionAlong`: the restriction of a global section of
  `p_V^* 𝒢` on `X_V` to a global section of `p^* 𝒢` on a scheme `U` lying over `X_V`.
* `AlgebraicGeometry.Space.AmpleSchemeFibreTwistConclusion`: the conclusion of Stacks 0D39.

## Implementation notes

*The fibre.*  "`X_y` is a scheme" is recorded as data: an object `U` of the site together with a
cartesian square `h_U ⟶ X` over `Spec κ(y) ⟶ Y`.  The hypothesis that `ℒ_y` is ample is
ampleness of `AlgebraicGeometry.Space.baseChangeModule ℒ U p` on the scheme underlying `U`,
together with its invertibility, exactly as in Stacks 0D31
(`AlgebraicGeometry.Space.IsRelativelyAmple`).

*The stalk.*  `Y` is a scheme, and the stalk at `y` of the higher direct image is the stalk of its
restriction to the Zariski site of `Y` (`AlgebraicGeometry.Space.zariskiModule`), which is the
restriction to the identity chart of `Y` used by `AlgebraicGeometry.Space.baseChangeModule`.

*The surjectivity.*  The stalk `f_*(𝒢)_y` is the colimit of the sections of `f_* 𝒢` over open
neighbourhoods `V` of `y`, and a section of `f_* 𝒢` over `V` is a section of `𝒢` over the
preimage `X_V = f⁻¹(V)`.  So surjectivity of `f_*(𝒢)_y ⟶ H^0(X_y, 𝒢|_{X_y})` says exactly that
every section of `𝒢` over `X_y` is the restriction of a section of `𝒢` over `X_V` for some open
`V ∋ y`, and then over `X_W` for every open `y ∈ W ⊆ V` by restriction.  That is the form
recorded here: there is an open `V ∋ y` such that for every open `y ∈ W ⊆ V`, every cartesian
square `X_W ⟶ X` over the open immersion `h_W ⟶ h_Y` and every factorization
`j_W : h_U ⟶ X_W` of the fibre inclusion, every global section of `p^* 𝒢` on `X_y` is the
pullback along `j_W` of a global section of `p_W^* 𝒢`.  Quantifying over all squares and all
factorizations makes the statement independent of a choice of `X_W`; quantifying over all
`W ⊆ V` lets finitely many sections be lifted over one neighbourhood.

*Universes.*  All modules live at `AlgebraicGeometry.Space.Modules.{u, u}`, the universe of the
higher direct images `(modulePushforward f).rightDerived p`, of Stacks 08EX and of Stacks 073K in
this development.  The twist `𝒢_d = ℱ ⊗ ℒ^{⊗ d}` is the tensor product of
`AlgebraicGeometry.Space.modulesMonoidalCategory` with the tensor power
`AlgebraicGeometry.Space.tensorPow`, and invertibility of `ℒ` is
`Stacks.SheafOfModules.IsInvertible` for the structure sheaf that tensor product is taken over.

## References

* [Stacks Project, Tag 0D39](https://stacks.math.columbia.edu/tag/0D39)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] modulesMonoidalCategory
attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

/-- Injective resolutions of the `𝒪`-modules of an algebraic space, at the universe of the
structure rings: `AlgebraicGeometry.Space.hasInjectiveResolutions_modules`, restated so that
instance search finds it with the universes fixed. -/
local instance ampleSchemeFibreHasInjectiveResolutions (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    HasInjectiveResolutions (Modules.{u, u} B S hS F hF) :=
  hasInjectiveResolutions_modules B S hS F hF

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The residue field of a point, as an object of the site -/

/-- The spectrum of the residue field `κ(y)` of a point `y` of the scheme underlying an object `Y`
of the big fppf site over `S`, as an object of that site.  It is contained in the site because
`Spec κ(y) ⟶ Y` is a quasi-compact monomorphism. -/
def residuePointObject (Y : BigFppfOver B S hS) (y : (BigFppfOver.toScheme B S hS).obj Y) :
    BigFppfOver B S hS :=
  siteObject B S hS (BigFppfSite.residueField_spec_contains B Y.left.2 y)
    (((BigFppfOver.toScheme B S hS).obj Y).fromSpecResidueField y ≫ Y.hom.hom)

/-- The canonical morphism `Spec κ(y) ⟶ Y` in the site. -/
def residuePointHom (Y : BigFppfOver B S hS) (y : (BigFppfOver.toScheme B S hS).obj Y) :
    residuePointObject Y y ⟶ Y :=
  Over.homMk (ObjectProperty.homMk
    (((BigFppfOver.toScheme B S hS).obj Y).fromSpecResidueField y)) rfl

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.residuePointHom` is
`Spec κ(y) ⟶ Y`. -/
theorem map_residuePointHom (Y : BigFppfOver B S hS) (y : (BigFppfOver.toScheme B S hS).obj Y) :
    (BigFppfOver.toScheme B S hS).map (residuePointHom Y y) =
      ((BigFppfOver.toScheme B S hS).obj Y).fromSpecResidueField y :=
  rfl

/-! ### Zariski restriction, global sections, and restriction of sections -/

/-- The restriction of a module on the algebraic space represented by `Y` to the Zariski site of
the scheme underlying `Y`, through the identity chart; this is the restriction used by
`AlgebraicGeometry.Space.baseChangeModule`. -/
abbrev zariskiModule (Y : BigFppfOver B S hS)
    (M : Modules.{u, u} B S hS (yoneda.obj Y) (isAlgebraicSpace_yoneda B S hS Y)) :
    ((BigFppfOver.toScheme B S hS).obj Y).Modules :=
  restrictToChartScheme B S hS (yoneda.obj Y) (isAlgebraicSpace_yoneda B S hS Y) M
    (idEtaleChart B S hS Y)

/-- The global sections `Γ(Z, 𝓜)` of a module on an algebraic space. -/
abbrev spaceModuleSections (Z : AlgebraicSpaces B S hS) (M : Modules.{u, u} B S hS Z.1 Z.2) :
    ModuleCat (RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O).obj) :=
  (globalSectionsFunctor.{u + 1, u, u, u} (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).obj
    M

/-- Pulling a module back along two equal morphisms gives isomorphic global sections. -/
def spaceModuleSectionsPullbackCongr {Z Z' : AlgebraicSpaces B S hS} {g g' : Z' ⟶ Z} (h : g = g')
    (G : Modules.{u, u} B S hS Z.1 Z.2) :
    spaceModuleSections Z' ((modulePullback B S hS g).obj G) ≅
      spaceModuleSections Z' ((modulePullback B S hS g').obj G) :=
  (globalSectionsFunctor.{u + 1, u, u, u}
    (ringSheaf (smallEtaleRingedSite B S hS Z'.1 Z'.2).O)).mapIso
      (eqToIso (congrArg (fun k => (modulePullback B S hS k).obj G) h))

/-- A morphism `h_U ⟶ X` from the algebraic space represented by an object of the site, as a
morphism of `AlgebraicGeometry.Space.AlgebraicSpaces`. -/
abbrev representedPointHom (U : BigFppfOver B S hS) {X : AlgebraicSpaces B S hS}
    (j : yoneda.obj U ⟶ X.1) : representedAlgebraicSpace B S hS U ⟶ X :=
  ObjectProperty.homMk j

/-- **The restriction of a section to a scheme lying over `X_V`.**  Let `p_V : X_V ⟶ X` be a
morphism of algebraic spaces, `U` an object of the site and `j_V : h_U ⟶ X_V` a morphism with
`j_V ≫ p_V = p`.  A global section `s` of `p_V^* 𝒢` restricts to the global section of `p^* 𝒢` on
`h_U` obtained by pulling `s` back along `j_V`
(`AlgebraicGeometry.Space.globalSectionsPullbackMap`, the unit of Stacks 03LU on global sections)
and identifying `j_V^* p_V^* 𝒢` with `p^* 𝒢` (`AlgebraicGeometry.Space.modulePullbackCompIso`). -/
def restrictSectionAlong {X XV : AlgebraicSpaces B S hS} (pV : XV ⟶ X) (U : BigFppfOver B S hS)
    (jV : yoneda.obj U ⟶ XV.1) (p : yoneda.obj U ⟶ X.1) (h : jV ≫ pV.hom = p)
    (G : Modules.{u, u} B S hS X.1 X.2)
    (s : spaceModuleSections XV ((modulePullback B S hS pV).obj G)) :
    spaceModuleSections (representedAlgebraicSpace B S hS U)
      ((modulePullback B S hS (ObjectProperty.homMk p :
        representedAlgebraicSpace B S hS U ⟶ X)).obj G) :=
  (spaceModuleSectionsPullbackCongr (ObjectProperty.hom_ext _ h :
      (representedPointHom U jV) ≫ pV =
        ObjectProperty.homMk p) G).hom
    ((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U)).O)).map
      ((modulePullbackCompIso B S hS (representedPointHom U jV) pV).hom.app G)
      ((globalSectionsPullbackMap B S hS (representedPointHom U jV)
        ((modulePullback B S hS pV).obj G)).hom s))

/-! ### The conclusion of Stacks 0D39 -/

section Conclusion

variable {Y : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}

/-- **The conclusion of Stacks 0D39** for a module `𝒢` on `X`, at the point `y` of `Y` and the
scheme fibre `p : h_U ⟶ X`:

1. for every `p > 0` the stalk at `y` of the higher direct image `R^p f_* 𝒢`, restricted to the
   Zariski site of `Y`, is zero;
2. every global section of `p^* 𝒢` on the fibre `X_y = U` is the restriction of a global section
   of `𝒢` over the preimage `X_W` of every sufficiently small open neighbourhood `W` of `y`: there
   is an open `V ∋ y` such that for every open `W ∋ y` inside `V`, every cartesian square
   `X_W ⟶ X` over `h_W ⟶ h_Y` and every factorization `j_W : h_U ⟶ X_W` of the fibre inclusion,
   there is a section over `X_W` restricting to it.

The second clause is surjectivity of `f_*(𝒢)_y ⟶ H^0(X_y, 𝒢|_{X_y})`; see the module
documentation. -/
def AmpleSchemeFibreTwistConclusion (f : X ⟶ representedAlgebraicSpace B S hS Y)
    (y : (BigFppfOver.toScheme B S hS).obj Y) (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X.1)
    (G : Modules.{u, u} B S hS X.1 X.2) : Prop :=
  letI := modulePushforward_additive B S hS f
  (∀ i : ℕ, 0 < i →
    IsZero ((zariskiModule Y (((modulePushforward B S hS f).rightDerived i).obj G)).presheaf.stalk
      y)) ∧
  ∀ t : spaceModuleSections (representedAlgebraicSpace B S hS U)
      ((modulePullback B S hS (ObjectProperty.homMk p :
        representedAlgebraicSpace B S hS U ⟶ X)).obj G),
    ∃ V : ((BigFppfOver.toScheme B S hS).obj Y).Opens, y ∈ V ∧
      ∀ W : ((BigFppfOver.toScheme B S hS).obj Y).Opens, W ≤ V → y ∈ W →
      ∀ ⦃XW : AlgebraicSpaces B S hS⦄ (pW : XW ⟶ X)
        (fW : XW ⟶ representedAlgebraicSpace B S hS (openSiteObject B S hS Y W)),
        IsPullback pW fW f
          (ObjectProperty.homMk (yoneda.map (openSiteObjectHom B S hS Y W))) →
        ∀ (jW : yoneda.obj U ⟶ XW.1) (h : jW ≫ pW.hom = p),
          ∃ s : spaceModuleSections XW ((modulePullback B S hS pW).obj G),
            restrictSectionAlong pW U jW p h G s = t

end Conclusion

/-- **The statement of Stacks 0D39**, as a proposition about the big fppf site `B` over `S`.

Let `Y` be a Noetherian scheme of the site, `f : X ⟶ Y` a proper morphism from an algebraic
space, `ℒ` an invertible and `ℱ` a coherent `𝒪_X`-module, and `y ∈ Y` a point such that the
fibre `X_y` is a scheme — a cartesian square `h_U ⟶ X` over `Spec κ(y) ⟶ Y` — on which the
restriction of `ℒ` is invertible and ample.  Then there is a `d₀` such that for every `d ≥ d₀`
the twist `ℱ ⊗ ℒ^{⊗ d}` (`AlgebraicGeometry.Space.tensorPow`) satisfies
`AlgebraicGeometry.Space.AmpleSchemeFibreTwistConclusion`. -/
def AmpleSchemeFibreTwistStatement (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Prop :=
  ∀ (Y : BigFppfOver B S hS)
    [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y)]
    (X : AlgebraicSpaces B S hS) (f : X ⟶ representedAlgebraicSpace B S hS Y),
    IsProper B S hS f.hom →
    ∀ (L : Modules.{u, u} B S hS X.1 X.2)
      [Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
        (structureRingPresheaf_isSheaf B S hS X.1 X.2) L]
      (F : Modules.{u, u} B S hS X.1 X.2), IsCoherent B S hS X.1 X.2 F →
    ∀ (y : (BigFppfOver.toScheme B S hS).obj Y) (U : BigFppfOver B S hS)
      (p : yoneda.obj U ⟶ X.1) (q : U ⟶ residuePointObject Y y),
      IsPullback p (yoneda.map q) f.hom (yoneda.map (residuePointHom Y y)) →
      (∃ hL : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
          (baseChangeModule B S hS L U p),
        @Stacks.Ample.IsAmple _ _ hL) →
      ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
        AmpleSchemeFibreTwistConclusion f y U p (F ⊗ tensorPow B S hS L d)

end AlgebraicGeometry.Space

end
