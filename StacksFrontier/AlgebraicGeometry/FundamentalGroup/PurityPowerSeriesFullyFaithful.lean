module

public import StacksFrontier.AlgebraicGeometry.AmpleLimit.Unconditional
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeBaseChange.PullbackSections
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSection
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeFactorization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PowerSeriesConstantCoeffQuotients
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PuncturedSpectrumSectionsDepthTwo
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionToClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanHomCompat
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.MulIsomorphism
public import StacksCore.Tactic.StacksAttribute

/-!
# Purity over a power series ring: restriction to the punctured closed fibre

Let `(A, 𝔪)` be a Noetherian local ring of depth at least two, let `B = A[[x_1, …, x_d]]` with
`d ≥ 1`, set `Y = Spec B` and let `Y_0 = V(x_1, …, x_d) ≅ Spec A` be the closed fibre. For an
open `V ⊆ Y` whose intersection with `Y_0` is the punctured spectrum of `A`, the restriction
functor `FÉt_V ⟶ FÉt_{V ∩ Y_0}` is fully faithful. This is [Stacks, Tag 0EY9], stated and proved
as `Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_restrict_mvPowerSeries` in
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/PurityPowerSeriesRestriction.lean`, which builds
on the material here.

The source's proof is the chain

* `Γ(V, 𝒪_V) = lim_n Γ(V_0, 𝒪_Y / I^n 𝒪_Y) = B`, because `depth(A) ≥ 2` makes the punctured
  spectrum of `A`, and of each `B / I^n`, have the same functions as the whole spectrum;
* [Stacks, Tag 0EKP], which turns that equality into full faithfulness of the completion functor
  on finite locally free coherent modules;
* [Stacks, Tag 0EL8], which turns that into full faithfulness of `FÉt_V ⟶ FÉt_{V_0}`.

The first step is prepared here; the second and third, and the assembly of the three, are in
`Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_restrict_mvPowerSeries`.

## Main results

* `Stacks.FundamentalGroup.isInfinitesimalSectionsComplete_unit_of_ringSections` — infinitesimal
  section completeness of the structure sheaf is a statement about rings of global functions: the
  structure-sheaf case of `Stacks.Algebraization.IsInfinitesimalSectionsComplete` is the
  assertion that `Γ(X, 𝒪_X)` is the inverse limit of the `Γ(Y_n, 𝒪_{Y_n})`.
* `Stacks.FundamentalGroup.bijective_appTop_of_retraction` — on an affine scheme a quasi-compact
  open whose functions retract onto the global functions has exactly the global functions.
* `Stacks.FundamentalGroup.isInfinitesimalSectionsComplete_of_quotientEquivs` — the structure
  sheaf of an open `V` of `Spec R`, with `R` adically complete for `I`, is infinitesimal section
  complete along a closed immersion into `V` whose infinitesimal neighbourhoods have the
  functions `R / I^(n+1)`.

[Stacks, Tag 0EY9] itself is
`Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_restrict_mvPowerSeries`, which
assumes nothing beyond the source's hypotheses.

## Implementation notes

`Stacks.Algebraization.IsInfinitesimalSectionsComplete` is phrased for an arbitrary module,
through `AlgebraicGeometry.pullbackGlobalSections` and `AlgebraicGeometry.pullbackSectionsMap`.
At the structure sheaf both of those are the maps on rings of functions, by
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`; the two compatibilities needed are
`Stacks.AlgebraicGeometry.PicardBaseChange.pullbackUnitIso_hom_pullbackUnitSections` for the
first map and, for the second,
`Stacks.AlgebraicGeometry.ModuleLimits.pullbackUnitIso_inv_canHom` read forwards — which is what
`canHom_comp_pullbackUnitIso` below does, by inverting an identity of isomorphisms rather than by
redoing the adjunction bookkeeping.

The geometry is the `n`-th order version of a single cartesian square. The closed subscheme
`Spec(B/I^{n+1}) ⊆ Y` has the same ideal sheaf as the `n`-th infinitesimal neighbourhood of the
closed fibre, so pulling it back along the open immersion `V ⊆ Y` gives the `n`-th infinitesimal
neighbourhood of `V ∩ Y_0` in `V`; that is `exists_isPullback_nthInfinitesimalNeighbourhood`. Its
functions are therefore the functions of the punctured spectrum of `B/I^{n+1}`, which by
`Stacks.LocalCohomology.bijective_appTop_of_punctured_of_depth_ge_two` and
`Stacks.MvPowerSeries.le_depth_quotient_pow_ker_constantCoeff` are `B/I^{n+1}` itself.

No compiler option is relaxed anywhere below. A step that needs a lowered
definitional-equality transparency is isolated into a named lemma stated at the spelling its
consumer needs; an identity that would need a raised heartbeat limit is instead derived from the
library's form of the same statement.

## References

* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP)
* [Stacks Project, Tag 0EL8](https://stacks.math.columbia.edu/tag/0EL8)
* [Stacks Project, Tag 0EY9](https://stacks.math.columbia.edu/tag/0EY9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.RelativeSpec
open Stacks.Algebraization (IsInfinitesimalSectionsComplete nthInfinitesimalNeighbourhood
  nthInfinitesimalNeighbourhoodι nthInfinitesimalNeighbourhoodOver
  nthInfinitesimalNeighbourhoodTransition CompletionFullyFaithfulOnFiniteLocallyFree)

universe u

namespace Stacks.FundamentalGroup

/-! ### The structure sheaf among the modules -/

/-- Sections over a fixed open of an isomorphism of modules are invertible. -/
private theorem isIso_app_of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    IsIso (Scheme.Modules.Hom.app e.hom U) :=
  ⟨Scheme.Modules.Hom.app e.inv U, by
      rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app], by
      rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]⟩

/-- **The pullback map on global sections of the structure sheaf is the map on functions.** Read
through the identification `f^* 𝒪_Y ≅ 𝒪_X`, the canonical map
`Γ(Y, 𝒪_Y) ⟶ Γ(X, f^* 𝒪_Y)` is `f.appTop`.

This is `Stacks.AlgebraicGeometry.PicardBaseChange.pullbackUnitIso_hom_pullbackUnitSections`,
after `AlgebraicGeometry.pullbackGlobalSections_eq_unit` removes the transport along
`f ⁻¹ᵁ ⊤ = ⊤` from the definition of the canonical map. -/
private theorem pullbackUnitIso_pullbackGlobalSections {X Y : Scheme.{u}} (f : X ⟶ Y)
    (t : Γ(Y, ⊤)) :
    Scheme.Modules.Hom.app (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom ⊤
        (pullbackGlobalSections f (SheafOfModules.unit Y.ringCatSheaf) t) = f.appTop t := by
  have h1 := congrArg
    (fun φ : Γ(SheafOfModules.unit Y.ringCatSheaf, ⊤) ⟶
        Γ((Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf), ⊤) => φ t)
    (pullbackGlobalSections_eq_unit f (SheafOfModules.unit Y.ringCatSheaf))
  exact (congrArg (fun z => Scheme.Modules.Hom.app
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom ⊤ z) h1).trans
    (Stacks.AlgebraicGeometry.PicardBaseChange.pullbackUnitIso_hom_pullbackUnitSections f t)

/-- **Inverting an identity of isomorphisms.** If `(a⁻¹ ≫ b⁻¹) ≫ c = d⁻¹` then
`c ≫ d = b ≫ a`. -/
private theorem comp_hom_of_inv_comp_inv_comp {C : Type*} [Category C] {P Q R U : C}
    (a : P ≅ U) (b : Q ≅ P) (d : R ≅ U) (c : Q ⟶ R)
    (h : (a.inv ≫ b.inv) ≫ c = d.inv) : c ≫ d.hom = b.hom ≫ a.hom := by
  have hc : c = b.hom ≫ a.hom ≫ d.inv := by
    rw [← h]
    simp
  rw [hc]
  simp

/-- **The canonical identification of iterated pullbacks is compatible with `𝒪 ≅ f^* 𝒪`.** For
`q ≫ g = pi` the composite `q^* g^* 𝒪_X ⟶ pi^* 𝒪_X ≅ 𝒪_W` is `q^* g^* 𝒪_X ⟶ q^* 𝒪_Z ≅ 𝒪_W`.

This is `Stacks.AlgebraicGeometry.ModuleLimits.pullbackUnitIso_inv_canHom`, which states the same
identity between the inverses, read forwards: all four morphisms are invertible, so the identity
`(A⁻¹ ≫ B⁻¹) ≫ C = D⁻¹` is equivalent to `C ≫ D = B ≫ A`. -/
private theorem canHom_comp_pullbackUnitIso {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X)
    (pi : W ⟶ X) (hpi : q ≫ g = pi) :
    Stacks.AlgebraicGeometry.ModuleLimits.canHom q g pi hpi
          (SheafOfModules.unit X.ringCatSheaf) ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso pi).hom =
      (Scheme.Modules.pullback q).map
          (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).hom ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso q).hom :=
  comp_hom_of_inv_comp_inv_comp (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso q)
    ((Scheme.Modules.pullback q).mapIso
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g))
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso pi) _
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackUnitIso_inv_canHom q g pi hpi)

/-- **The restriction maps of the presheaf of [Stacks, Tag 03DS] at the structure sheaf are the
maps on functions.** For a morphism `g` of schemes over `S`, the map
`Γ(B, B.hom^* 𝒪_S) ⟶ Γ(A, A.hom^* 𝒪_S)` is `g.left.appTop` once both sides are identified with
rings of functions.

`AlgebraicGeometry.pullbackSectionsMap_eq_comp` writes the restriction map as the canonical
identification of iterated pullbacks applied to a pullback of a section;
`canHom_comp_pullbackUnitIso` moves the identification past `𝒪 ≅ f^* 𝒪`,
`AlgebraicGeometry.pullbackGlobalSections_natural` moves the pullback map past it, and
`pullbackUnitIso_pullbackGlobalSections` finishes. -/
private theorem pullbackUnitIso_pullbackSectionsMap {S : Scheme.{u}} {A B : Over S} (g : A ⟶ B)
    (s : Γ((Scheme.Modules.pullback B.hom).obj (SheafOfModules.unit S.ringCatSheaf), ⊤)) :
    Scheme.Modules.Hom.app
          (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso A.hom).hom ⊤
          (pullbackSectionsMap (SheafOfModules.unit S.ringCatSheaf) g s) =
      g.left.appTop (Scheme.Modules.Hom.app
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso B.hom).hom ⊤ s) := by
  have h' : (⊤ : A.left.Opens) ≤ g.left ⁻¹ᵁ (⊤ : B.left.Opens) := by simp
  have hcan : pullbackSectionsMap (SheafOfModules.unit S.ringCatSheaf) g s =
      Scheme.Modules.Hom.app
        (Stacks.AlgebraicGeometry.ModuleLimits.canHom g.left B.hom A.hom (Over.w g)
          (SheafOfModules.unit S.ringCatSheaf)) ⊤
        (pullbackGlobalSections g.left
          ((Scheme.Modules.pullback B.hom).obj (SheafOfModules.unit S.ringCatSheaf)) s) := by
    rw [pullbackSectionsMap_eq_comp (SheafOfModules.unit S.ringCatSheaf) g h' s,
      pullbackGlobalSections_eq_pullbackSection g.left _ h' s]
    rfl
  rw [hcan]
  have hcc := congrArg
    (fun χ : (Scheme.Modules.pullback g.left).obj
        ((Scheme.Modules.pullback B.hom).obj (SheafOfModules.unit S.ringCatSheaf)) ⟶
        SheafOfModules.unit A.left.ringCatSheaf =>
      Scheme.Modules.Hom.app χ ⊤ (pullbackGlobalSections g.left
        ((Scheme.Modules.pullback B.hom).obj (SheafOfModules.unit S.ringCatSheaf)) s))
    (canHom_comp_pullbackUnitIso g.left B.hom A.hom (Over.w g))
  refine hcc.trans (Eq.trans (congrArg (fun z => Scheme.Modules.Hom.app
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g.left).hom ⊤ z)
    (pullbackGlobalSections_natural g.left
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso B.hom).hom s).symm) ?_)
  exact pullbackUnitIso_pullbackGlobalSections g.left _

/-- **Infinitesimal section completeness of the structure sheaf is a statement about functions.**
If every compatible system of functions on the infinitesimal neighbourhoods of a closed immersion
`i : Z ⟶ X` comes from a unique global function on `X`, then the structure sheaf of `X` is
infinitesimal section complete along `i`.

The two identifications of the maps occurring in
`Stacks.Algebraization.IsInfinitesimalSectionsComplete` with maps on functions are
`pullbackUnitIso_pullbackGlobalSections` and `pullbackUnitIso_pullbackSectionsMap`. -/
public theorem isInfinitesimalSectionsComplete_unit_of_ringSections {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (h : ∀ s : ∀ n : ℕ, Γ(nthInfinitesimalNeighbourhood i n, ⊤),
      (∀ (n m : ℕ) (hnm : n ≤ m),
        (nthInfinitesimalNeighbourhoodTransition i hnm).left.appTop (s m) = s n) →
      ∃! t : Γ(X, ⊤), ∀ n : ℕ, (nthInfinitesimalNeighbourhoodι i n).appTop t = s n) :
    IsInfinitesimalSectionsComplete i (SheafOfModules.unit X.ringCatSheaf) := by
  intro s hs
  let e (n : ℕ) := Scheme.Modules.Hom.app
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
      (nthInfinitesimalNeighbourhoodι i n)).hom ⊤
  have hei (n : ℕ) : Function.Injective (e n) := by
    have := isIso_app_of_iso
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
        (nthInfinitesimalNeighbourhoodι i n)) (⊤ : (nthInfinitesimalNeighbourhood i n).Opens)
    exact (ConcreteCategory.bijective_of_isIso (e n)).injective
  obtain ⟨t, ht, huniq⟩ := h (fun n => e n (s n)) (by
    intro n m hnm
    exact (pullbackUnitIso_pullbackSectionsMap
      (nthInfinitesimalNeighbourhoodTransition i hnm) (s m)).symm.trans
        (congrArg (e n) (hs n m hnm)))
  refine ⟨t, fun n => hei n ?_, fun t' ht' => huniq t' fun n => ?_⟩
  · exact (pullbackUnitIso_pullbackGlobalSections (nthInfinitesimalNeighbourhoodι i n) t).trans
      (ht n)
  · exact (pullbackUnitIso_pullbackGlobalSections
      (nthInfinitesimalNeighbourhoodι i n) t').symm.trans (congrArg (e n) (ht' n))

/-! ### Functions on a quasi-compact open of an affine scheme that retract -/

/-- **A quasi-compact open of an affine scheme whose functions retract onto the global functions
has exactly the global functions.** If the restriction `Γ(X, 𝒪_X) ⟶ Γ(X, V)` has a left inverse
as a ring map and `V` is quasi-compact, it is bijective.

Injectivity is the left inverse. For surjectivity it is enough that the left inverse be
injective, which is the kernel computation: a section of `𝒪_X` over `V` killed by the retraction
vanishes, because near each point of `V` it is supported on a basic open `D(f) ⊆ V`, where
`Mathlib.AlgebraicGeometry.exists_eq_pow_mul_of_isAffineOpen` writes it as `y / f^n` with `y`
global; quasi-compactness of `V` makes `f^k y = 0` for some `k`, and applying the retraction
kills `y`. -/
public theorem bijective_restriction_of_retraction (X : Scheme.{u}) [IsAffine X] (V : X.Opens)
    (hV : IsCompact (V : Set X)) (g : Γ(X, V) →+* Γ(X, ⊤))
    (hg : Function.LeftInverse g (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op)) :
    Function.Bijective (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op) := by
  let r : Γ(X, ⊤) →+* Γ(X, V) :=
    (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op).hom
  have hgr (a : Γ(X, ⊤)) : g (r a) = a := hg a
  have hker (s : Γ(X, V)) (hs : g s = 0) : s = 0 := by
    refine TopCat.Presheaf.section_ext X.sheaf V s 0 ?_
    intro x hx
    obtain ⟨f, hfV, hxf⟩ := (isAffineOpen_top X).exists_basicOpen_le ⟨x, hx⟩ (by trivial)
    let q : Γ(X, V) →+* Γ(X, X.basicOpen f) :=
      (X.presheaf.map (homOfLE hfV).op).hom
    let p : Γ(X, ⊤) →+* Γ(X, X.basicOpen f) :=
      (X.presheaf.map (homOfLE le_top).op).hom
    have hpr (a : Γ(X, ⊤)) : q (r a) = p a := by
      change (X.presheaf.map _ ≫ X.presheaf.map _) a = _
      rw [← X.presheaf.map_comp]
      rfl
    obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen X ⊤ (isAffineOpen_top X) f (q s)
    change p y = p f ^ n * q s at hy
    have hbasic : X.basicOpen (r f) = X.basicOpen f := by
      change X.basicOpen ((X.presheaf.map (homOfLE le_top).op) f) = _
      rw [Scheme.basicOpen_res, inf_eq_right.mpr hfV]
    have hz : TopCat.Presheaf.restrictOpen (r y - r f ^ n * s) (X.basicOpen (r f))
        (X.basicOpen_le (r f)) = 0 := by
      have hz' : q (r y - r f ^ n * s) = 0 := by
        simp only [map_sub, map_mul, map_pow, hpr, hy, sub_self]
      have htransport (W : X.Opens) (hWV : W ≤ V) (he : W = X.basicOpen f) :
          (X.presheaf.map (homOfLE hWV).op) (r y - r f ^ n * s) = 0 := by
        subst W
        exact hz'
      exact htransport _ _ hbasic
    obtain ⟨k, hk⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
      X hV (r y - r f ^ n * s) (r f) hz
    have hy0 : f ^ k * y = 0 := by
      have hh := congrArg g hk
      simpa only [map_mul, map_sub, map_pow, hgr, hs, mul_zero, sub_zero, map_zero] using hh
    have hu : IsUnit (p f) := X.toRingedSpace.isUnit_res_basicOpen f
    have hpy : p y = 0 := by
      have hh := congrArg p hy0
      have he : p f ^ k * p y = p f ^ k * 0 := by simpa using hh
      exact (hu.pow k).mul_left_cancel he
    have hqs : q s = 0 := by
      apply (hu.pow n).mul_left_cancel
      simpa [hpy] using hy.symm
    apply X.presheaf.germ_ext (X.basicOpen f) hxf (homOfLE hfV) (homOfLE hfV)
    change q s = q 0
    simpa using hqs
  have hgInj : Function.Injective g := by
    intro s t hst
    apply sub_eq_zero.mp
    apply hker
    simp [map_sub, hst]
  exact ⟨hg.injective, fun s => ⟨g s, hgInj (hg (g s))⟩⟩

/-- **The functions of a quasi-compact open immersion into an affine scheme that retracts.** If
`f : X ⟶ Y` is a quasi-compact open immersion into an affine scheme and `f.appTop` has a left
inverse as a ring map, then `f.appTop` is bijective.

`f` and the inclusion of the open `f ''ᵁ ⊤` have the same range, so they differ by an isomorphism
of the sources, whose functions are invertible; on the open subscheme the map on functions is a
restriction map of `𝒪_Y`, by `AlgebraicGeometry.Scheme.Opens.ι_appTop`, and that case is
`bijective_restriction_of_retraction`. -/
public theorem bijective_appTop_of_retraction {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y)
    [IsOpenImmersion f] (hc : IsCompact (Set.range f.base)) (g : Γ(X, ⊤) →+* Γ(Y, ⊤))
    (hg : Function.LeftInverse g f.appTop) : Function.Bijective f.appTop := by
  set W := f ''ᵁ (⊤ : X.Opens) with hW
  have hrange : Set.range f.base = Set.range W.ι.base := by
    rw [Scheme.Opens.range_ι, hW, Scheme.Hom.image_top_eq_opensRange]
    rfl
  let e : X ≅ W.toScheme := IsOpenImmersion.isoOfRangeEq f W.ι hrange
  have hfac : e.hom ≫ W.ι = f := IsOpenImmersion.isoOfRangeEq_hom_fac f W.ι hrange
  have hcomp : W.ι.appTop ≫ e.hom.appTop = f.appTop :=
    (Scheme.Hom.comp_appTop e.hom W.ι).symm.trans
      (congrArg (fun m : X ⟶ Y => m.appTop) hfac)
  have hcompelt (t : Γ(Y, ⊤)) : e.hom.appTop (W.ι.appTop t) = f.appTop t :=
    (ConcreteCategory.comp_apply W.ι.appTop e.hom.appTop t).symm.trans
      (congrArg (fun φ : Γ(Y, ⊤) ⟶ Γ(X, ⊤) => φ t) hcomp)
  have hiso : IsIso e.hom.appTop := ⟨(inv e.hom).appTop, by
      rw [← Scheme.Hom.comp_appTop]
      simp, by
      rw [← Scheme.Hom.comp_appTop]
      simp⟩
  have hcompact : IsCompact ((W.ι ''ᵁ (⊤ : W.toScheme.Opens)) : Set Y) := by
    rw [Scheme.Opens.ι_image_top, hW, Scheme.Hom.image_top_eq_opensRange]
    exact hc
  have hres : Function.Bijective W.ι.appTop :=
    bijective_restriction_of_retraction Y (W.ι ''ᵁ (⊤ : W.toScheme.Opens)) hcompact
      (g.comp (e.hom.appTop).hom) fun t => (congrArg g (hcompelt t)).trans (hg t)
  have hb : Function.Bijective (W.ι.appTop ≫ e.hom.appTop) :=
    (ConcreteCategory.bijective_of_isIso e.hom.appTop).comp hres
  exact (congrArg (fun φ : Γ(Y, ⊤) ⟶ Γ(X, ⊤) => Function.Bijective φ) hcomp).mp hb

/-! ### The functions of the infinitesimal neighbourhoods -/

/-- The ideal sheaf of a morphism of affine spectra is the kernel of the ring map, transported
along `Scheme.ΓSpecIso`. -/
private theorem ker_specMap (R S : CommRingCat.{u}) (φ : R ⟶ S) :
    (Spec.map φ).ker = Scheme.IdealSheafData.ofIdealTop
      ((RingHom.ker φ.hom).comap (Scheme.ΓSpecIso R).hom.hom) := by
  rw [Scheme.ker_of_isAffine]
  congr 1
  have he : (Spec.map φ).appTop =
      (Scheme.ΓSpecIso R).hom ≫ φ ≫ (Scheme.ΓSpecIso S).inv := by simp
  rw [he, CommRingCat.hom_comp, CommRingCat.hom_comp,
    ← RingHom.comap_ker, RingHom.ker_comp_of_injective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).inv).injective]

/-- A ring map whose kernel is the `n`-th power of the kernel of another one induces a morphism of
spectra whose ideal sheaf is the `n`-th power of the other's. -/
private theorem ker_specMap_pow {R S T : CommRingCat.{u}} (φ : R ⟶ S) (ψ : R ⟶ T) (n : ℕ)
    (h : RingHom.ker ψ.hom = RingHom.ker φ.hom ^ n) :
    (Spec.map ψ).ker = (Spec.map φ).ker ^ n := by
  rw [ker_specMap, ker_specMap, h]
  let e := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  change Scheme.IdealSheafData.ofIdealTop ((RingHom.ker φ.hom ^ n).comap e.symm) = _
  simp only [← Ideal.map_comap_of_equiv, Ideal.map_pow]
  apply Scheme.IdealSheafData.ext_of_isAffine
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal, homOfLE_refl, op_id,
    CategoryTheory.Functor.map_id, CommRingCat.hom_id, Ideal.map_id,
    Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
  exact congrArg (fun J => J ^ n) (Ideal.map_comap_of_equiv e)

/-- The inverse image of ideal sheaves along an open immersion commutes with powers. -/
private theorem ideal_comap_pow_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (I : Y.IdealSheafData) (n : ℕ) :
    (I ^ n).comap f = I.comap f ^ n := by
  ext U : 2
  simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
  let e := (f.appIso U).commRingCatIsoToRingEquiv
  let J := I.ideal ⟨f ''ᵁ U, U.2.image_of_isOpenImmersion f⟩
  change (J ^ n).comap e.symm.toRingHom = J.comap e.symm.toRingHom ^ n
  calc
    (J ^ n).comap e.symm.toRingHom = (J ^ n).map e.toRingHom :=
      (Ideal.map_comap_of_equiv e).symm
    _ = J.map e.toRingHom ^ n := Ideal.map_pow _ _ _
    _ = _ := congrArg (fun K => K ^ n) (Ideal.map_comap_of_equiv e)

/-- In a cartesian square whose horizontal maps are open immersions and whose right-hand vertical
map is a quasi-compact closed immersion, the inverse image of the ideal sheaf is the ideal sheaf
of the base change. -/
private theorem ker_comap_of_isPullback_of_isOpenImmersion {X Y S T : Scheme.{u}} (f : X ⟶ Y)
    (i : S ⟶ Y) (j : T ⟶ X) (g : T ⟶ S) [IsOpenImmersion f] [QuasiCompact i]
    (H : IsPullback j g f i) : i.ker.comap f = j.ker := by
  ext U : 2
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact (Scheme.ker_ideal_of_isPullback_of_isOpenImmersion i j g f H U).symm

/-- **The infinitesimal neighbourhoods of a closed fibre restricted to an open are base changes.**
Let `s : S ⟶ Y` be a closed immersion, `V ⊆ Y` an open, and `q : Z ⟶ Y` a closed immersion whose
ideal sheaf is the `(n+1)`-st power of that of `s`. Then the `n`-th infinitesimal neighbourhood of
`s ∣_ V` in `V` is the base change of `q` along `V ⊆ Y`.

The ideal sheaf of `s ∣_ V` pulled back to the canonical open through which it factors is the
inverse image of `s.ker`, so the inverse image of `q.ker` is the `(n+1)`-st power of it, which is
the ideal sheaf cutting out the `n`-th infinitesimal neighbourhood. A closed immersion is
determined by its ideal sheaf, so the comparison morphism exists and the square is cartesian. -/
private theorem exists_isPullback_nthInfinitesimalNeighbourhood {Y S Z : Scheme.{u}} (s : S ⟶ Y)
    [IsClosedImmersion s] (V : Y.Opens) (q : Z ⟶ Y) [IsClosedImmersion q] (n : ℕ)
    (hq : q.ker = s.ker ^ (n + 1)) :
    ∃ j : nthInfinitesimalNeighbourhood (s ∣_ V) n ⟶ Z,
      IsPullback ((s ∣_ V).liftCoborder.ker ^ (n + 1)).subschemeι j
        ((s ∣_ V).coborderRange.ι ≫ V.ι) q := by
  let i := s ∣_ V
  let f := i.coborderRange.ι ≫ V.ι
  have H₀ : IsPullback i.liftCoborder (𝟙 _) i.coborderRange.ι i :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have H := H₀.paste_vert (isPullback_morphismRestrict s V)
  have hk : s.ker.comap f = i.liftCoborder.ker :=
    ker_comap_of_isPullback_of_isOpenImmersion f s _ _ H
  have hpow : q.ker.comap f = i.liftCoborder.ker ^ (n + 1) := by
    rw [hq, ideal_comap_pow_of_isOpenImmersion, hk]
  let K := i.liftCoborder.ker ^ (n + 1)
  have hle : q.ker ≤ (K.subschemeι ≫ f).ker := by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι]
    exact Scheme.IdealSheafData.le_map_iff_comap_le.mpr hpow.le
  let j := IsClosedImmersion.lift q (K.subschemeι ≫ f) hle
  refine ⟨j, isPullback_of_isClosedImmersion K.subschemeι q j f ?_ ?_⟩
  · exact (IsClosedImmersion.lift_fac _ _ _).symm
  · simpa [K] using hpow

/-- Two closed immersions one of whose ideal sheaves is a positive power of the other's have the
same image: taking a positive power does not change the support of an ideal sheaf. -/
private theorem range_eq_of_ker_pow {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsClosedImmersion f] [IsClosedImmersion g] (n : ℕ) (hn : n ≠ 0)
    (h : f.ker = g.ker ^ n) : Set.range f.base = Set.range g.base := by
  have hf := f.support_ker
  have hg := g.support_ker
  rw [f.isClosedEmbedding.isClosed_range.closure_eq] at hf
  rw [g.isClosedEmbedding.isClosed_range.closure_eq] at hg
  rw [← hf, ← hg, h, Scheme.IdealSheafData.support_pow _ n hn]

/-- **The open stays the punctured spectrum along the infinitesimal neighbourhoods.** If the
inverse image of `V` under a closed immersion `s : Spec A ⟶ Y` is the punctured spectrum of `A`,
and `q : Spec R ⟶ Y` is a closed immersion with the same image whose ideal sheaf is a positive
power of that of `s`, with `R ⟶ A` a surjective local homomorphism inducing `q ↦ s`, then the
inverse image of `V` under `q` is the punctured spectrum of `R`.

The two immersions have the same image by `range_eq_of_ker_pow`, so a point of `Spec R` and the
point of `Spec A` above it have the same image in `Y`; and the closed point corresponds to the
closed point, because the comparison is a surjective local homomorphism. -/
private theorem preimage_eq_punctured_of_ker_pow (R A : Type u) [CommRing R] [IsLocalRing R]
    [CommRing A] [IsLocalRing A] {Y : Scheme.{u}} (s : Spec (.of A) ⟶ Y) (q : Spec (.of R) ⟶ Y)
    [IsClosedImmersion s] [IsClosedImmersion q] (c : R →+* A) [IsLocalHom c]
    (hc : Function.Surjective c) (hcomp : Spec.map (CommRingCat.ofHom c) ≫ q = s) (n : ℕ)
    (hn : n ≠ 0) (hk : q.ker = s.ker ^ n) (V : Y.Opens)
    (hV : (s ⁻¹ᵁ V : Set (Spec (.of A))) = {IsLocalRing.closedPoint A}ᶜ) :
    (q ⁻¹ᵁ V : Set (Spec (.of R))) = {IsLocalRing.closedPoint R}ᶜ := by
  have hr := range_eq_of_ker_pow q s n hn hk
  ext x
  have hxrange : q.base x ∈ Set.range s.base := by
    rw [← hr]
    exact Set.mem_range_self x
  obtain ⟨a, ha⟩ := hxrange
  have hx : PrimeSpectrum.comap c a = x := by
    apply q.isClosedEmbedding.injective
    exact (congrArg (fun f : Spec (.of A) ⟶ Y => f.base a) hcomp).trans ha
  have hinj := PrimeSpectrum.comap_injective_of_surjective c hc
  have haV : q.base x ∈ V ↔ a ≠ IsLocalRing.closedPoint A := by
    rw [← ha]
    exact Set.ext_iff.mp hV a
  change q.base x ∈ V ↔ x ≠ IsLocalRing.closedPoint R
  rw [haV, ← hx, ← IsLocalRing.comap_closedPoint c]
  exact not_congr hinj.eq_iff.symm

/-- The functions of an open immersion into the spectrum of a Noetherian local ring of depth at
least two whose range is the punctured spectrum are the functions of the whole spectrum. -/
private theorem bijective_appTop_punctured (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsOpenImmersion f]
    (h : Set.range f.base = {IsLocalRing.closedPoint R}ᶜ)
    (hdepth : (2 : ℕ∞) ≤ Module.depth R (IsLocalRing.maximalIdeal R) R) :
    Function.Bijective ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop) :=
  Stacks.LocalCohomology.bijective_appTop_of_punctured_of_depth_ge_two R f h hdepth

/-- **The functions of the infinitesimal neighbourhoods of the punctured closed fibre.** In the
situation of `exists_isPullback_nthInfinitesimalNeighbourhood`, if the inverse image of `V` under
`q : Spec R ⟶ Y` is the punctured spectrum of a Noetherian local ring `R` of depth at least two,
then the `n`-th infinitesimal neighbourhood of `s ∣_ V` in `V` has exactly the functions `R`, and
the identification is compatible with the two maps out of `Γ(Y, 𝒪_Y)`.

The neighbourhood is an open of `Spec R` with the punctured spectrum as its range, by
`exists_isPullback_nthInfinitesimalNeighbourhood`, so its functions are `R` by
`bijective_appTop_punctured`; the compatibility is the factorization of the comparison morphism
through the cartesian square. -/
private theorem exists_ringEquiv_nthInfinitesimalNeighbourhood {Y S : Scheme.{u}} (s : S ⟶ Y)
    [IsClosedImmersion s] (V : Y.Opens) (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (q : Spec (.of R) ⟶ Y) [IsClosedImmersion q] (n : ℕ)
    (hq : q.ker = s.ker ^ (n + 1))
    (hpunct : (q ⁻¹ᵁ V : Set (Spec (.of R))) = {IsLocalRing.closedPoint R}ᶜ)
    (hdepth : (2 : ℕ∞) ≤ Module.depth R (IsLocalRing.maximalIdeal R) R) :
    ∃ ε : R ≃+* Γ(nthInfinitesimalNeighbourhood (s ∣_ V) n, ⊤), ∀ a : Γ(Y, ⊤),
      ε ((Scheme.ΓSpecIso (.of R)).hom (q.appTop a)) =
        (nthInfinitesimalNeighbourhoodι (s ∣_ V) n).appTop (V.ι.appTop a) := by
  have hiV : IsClosedImmersion (s ∣_ V) := IsZariskiLocalAtTarget.restrict ‹_› V
  obtain ⟨j, hjpb⟩ := exists_isPullback_nthInfinitesimalNeighbourhood s V q n hq
  have hoi : IsOpenImmersion j := MorphismProperty.of_isPullback hjpb inferInstance
  have hco : (s ∣_ V).coborderRange = ⊤ :=
    TopologicalSpace.Opens.ext (s ∣_ V).isClosedEmbedding.isClosed_range.coborder_eq
  have hcoiso : IsIso (s ∣_ V).coborderRange.ι := by
    rw [hco]
    exact inferInstanceAs (IsIso V.toScheme.topIso.hom)
  have hrange : Set.range j.base = {IsLocalRing.closedPoint R}ᶜ := by
    have hh : j ''ᵁ (⊤ : (nthInfinitesimalNeighbourhood (s ∣_ V) n).Opens) =
        q ⁻¹ᵁ ((s ∣_ V).coborderRange.ι ≫ V.ι) ''ᵁ
          (⊤ : ((s ∣_ V).coborderRange.toScheme).Opens) :=
      @IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
        _ _ _ _ _ _ _ _ _ hoi hjpb ⊤
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.image_top_eq_opensRange,
      Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι] at hh
    exact (congrArg (fun W : (Spec (.of R)).Opens => (W : Set (Spec (.of R)))) hh).trans hpunct
  have hfac : j ≫ q = nthInfinitesimalNeighbourhoodι (s ∣_ V) n ≫ V.ι :=
    hjpb.w.symm.trans (Category.assoc _ _ _).symm
  refine ⟨RingEquiv.ofBijective ((Scheme.ΓSpecIso (.of R)).inv ≫ j.appTop).hom
    (bijective_appTop_punctured R j hrange hdepth), fun a => ?_⟩
  have e1 : (Scheme.ΓSpecIso (.of R)).hom ≫ ((Scheme.ΓSpecIso (.of R)).inv ≫ j.appTop) =
      j.appTop := by
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have e2 : q.appTop ≫ j.appTop =
      V.ι.appTop ≫ (nthInfinitesimalNeighbourhoodι (s ∣_ V) n).appTop := by
    rw [← Scheme.Hom.comp_appTop, hfac, Scheme.Hom.comp_appTop]
  calc ((Scheme.ΓSpecIso (.of R)).inv ≫ j.appTop) ((Scheme.ΓSpecIso (.of R)).hom (q.appTop a))
      = ((Scheme.ΓSpecIso (.of R)).hom ≫ ((Scheme.ΓSpecIso (.of R)).inv ≫ j.appTop))
          (q.appTop a) := (ConcreteCategory.comp_apply _ _ _).symm
    _ = j.appTop (q.appTop a) :=
        congrArg (fun φ : Γ(Spec (.of R), ⊤) ⟶
          Γ(nthInfinitesimalNeighbourhood (s ∣_ V) n, ⊤) => φ (q.appTop a)) e1
    _ = (q.appTop ≫ j.appTop) a := (ConcreteCategory.comp_apply _ _ _).symm
    _ = (V.ι.appTop ≫ (nthInfinitesimalNeighbourhoodι (s ∣_ V) n).appTop) a :=
        congrArg (fun φ : Γ(Y, ⊤) ⟶
          Γ(nthInfinitesimalNeighbourhood (s ∣_ V) n, ⊤) => φ a) e2
    _ = _ := ConcreteCategory.comp_apply _ _ _

/-! ### Section completeness from the functions of the neighbourhoods -/

/-- **Section completeness from the functions of the infinitesimal neighbourhoods.** Let `R` be
adically complete for `I`, let `V ⊆ Spec R` be a quasi-compact open and `i : Z ⟶ V` a closed
immersion whose `n`-th infinitesimal neighbourhood has functions `R / I^{n+1}`, compatibly with
the structure maps. Then the structure sheaf of `V` is infinitesimal section complete along `i`.

The isomorphisms `e` turn the inverse system of the neighbourhoods into the inverse system of the
quotients `R / I^{n+1}`, whose limit is `R` by
`Stacks.MvPowerSeries.existsUnique_adicLift_succ`; the resulting ring map
`Γ(V, 𝒪_V) ⟶ R` is a left inverse of `R ⟶ Γ(V, 𝒪_V)`, so the latter is bijective by
`bijective_appTop_of_retraction`, and the unique antecedent in `R` of a compatible family is
transported to `Γ(V, 𝒪_V)` along it. -/
public theorem isInfinitesimalSectionsComplete_of_quotientEquivs (R : Type u) [CommRing R]
    (I : Ideal R) [IsAdicComplete I R] (V : (Spec (.of R)).Opens)
    (hc : IsCompact (V : Set (Spec (.of R)))) {Z : Scheme.{u}} (i : Z ⟶ V.toScheme)
    [IsClosedImmersion i]
    (e : ∀ n : ℕ, (R ⧸ I ^ (n + 1)) ≃+* Γ(nthInfinitesimalNeighbourhood i n, ⊤))
    (he : ∀ (n : ℕ) (a : R), e n (Ideal.Quotient.mk _ a) =
      (nthInfinitesimalNeighbourhoodι i n).appTop
        (V.ι.appTop ((Scheme.ΓSpecIso (.of R)).inv a))) :
    IsInfinitesimalSectionsComplete i (SheafOfModules.unit V.toScheme.ringCatSheaf) := by
  let r : R →+* Γ(V.toScheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of R)).inv ≫ V.ι.appTop).hom
  let p (n : ℕ) := nthInfinitesimalNeighbourhoodι i n
  let q (n : ℕ) : Γ(V.toScheme, ⊤) →+* R ⧸ I ^ (n + 1) :=
    (e n).symm.toRingHom.comp (p n).appTop.hom
  have hp {n m : ℕ} (h : n ≤ m) (x : Γ(V.toScheme, ⊤)) :
      (nthInfinitesimalNeighbourhoodTransition i h).left.appTop ((p m).appTop x) =
        (p n).appTop x := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop]
    exact congrArg (fun f : _ ⟶ V.toScheme => f.appTop x) (Over.w _)
  have htrans {n m : ℕ} (h : n ≤ m) (a : R ⧸ I ^ (m + 1)) :
      (nthInfinitesimalNeighbourhoodTransition i h).left.appTop (e m a) =
        e n (Ideal.Quotient.factorPow I (Nat.succ_le_succ h) a) := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.factor_mk, he, he]
    exact hp h _
  have hq {m n : ℕ} (h : m ≤ n) :
      (Ideal.Quotient.factorPow I (Nat.succ_le_succ h)).comp (q n) = q m := by
    ext t
    apply (e m).injective
    rw [RingHom.comp_apply, ← htrans h]
    simpa [q] using hp h t
  have hsucc : StrictMono Nat.succ := fun _ _ h => Nat.succ_lt_succ h
  let g := IsAdicComplete.StrictMono.liftRingHom I hsucc q (fun {m} => hq (Nat.le_succ m))
  have hqr (n : ℕ) (a : R) : q n (r a) = Ideal.Quotient.mk _ a := by
    apply (e n).injective
    simpa [q, r, p] using (he n a).symm
  have hgr : Function.LeftInverse g r := by
    have hh := IsHausdorff.StrictMono.funext' I hsucc
      (f := fun a : R => g (r a)) (g := id) (fun n a => by
        rw [IsAdicComplete.StrictMono.mk_liftRingHom]
        exact hqr n a)
    exact congrFun hh
  have hr : Function.Bijective r := by
    have hv := bijective_appTop_of_retraction V.ι (by simpa using hc)
      ((Scheme.ΓSpecIso (.of R)).inv.hom.comp g) (by
        intro a
        have hh := hgr ((Scheme.ΓSpecIso (.of R)).hom a)
        simpa [r] using congrArg (Scheme.ΓSpecIso (.of R)).inv hh)
    exact hv.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv)
  apply isInfinitesimalSectionsComplete_unit_of_ringSections i
  intro s hs
  obtain ⟨a, ha, hu⟩ := Stacks.MvPowerSeries.existsUnique_adicLift_succ R I
    (fun n => (e n).symm (s n)) (by
      intro m n h
      apply (e m).injective
      rw [← htrans h]
      simpa using hs m n h)
  refine ⟨r a, fun n => ?_, fun t ht => ?_⟩
  · exact (he n a).symm.trans ((congrArg (e n) (ha n)).trans ((e n).apply_symm_apply _))
  · obtain ⟨b, rfl⟩ := hr.surjective t
    apply congrArg r
    apply hu b
    intro n
    apply (e n).injective
    exact ((he n b).trans (ht n)).trans ((e n).apply_symm_apply _).symm

/-! ### Tag 0EY9 -/

end Stacks.FundamentalGroup

end
