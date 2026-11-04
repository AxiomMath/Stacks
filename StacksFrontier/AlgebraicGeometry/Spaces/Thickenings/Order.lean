module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdeals
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings
public import StacksFrontier.AlgebraicGeometry.Thickenings

/-!
# The order of a thickening of algebraic spaces

A closed subspace `Z` of an algebraic space `X` over a scheme `S` has a canonical defining
ideal on every object of the small étale site of `X`, namely
`AlgebraicGeometry.Space.definingIdealAt`. Measuring the vanishing of its powers gives the
remaining three parts of Stacks 05ZK: `Z ⊂ X` is an *`n`th-order* thickening when the
`(n+1)`st power of that ideal vanishes on every étale chart, a *first-order* thickening when
`n = 1` works, and a *finite-order* thickening when some `n` works.

The point of the definitions is that they descend to scheme charts: along any étale scheme
chart `q : U ⟶ X` the closed subspace pulls back to a closed subscheme of `U` whose kernel
ideal sheaf satisfies the same power equation, so an `n`th-order thickening of algebraic
spaces becomes an `n`th-order thickening of schemes on every étale chart. This is what makes
the scheme-level deformation theory of Stacks 06AG available to algebraic spaces.

## Main definitions

* `AlgebraicGeometry.Space.IsNthOrderThickening`: **Stacks 05ZK**, part (4).
* `AlgebraicGeometry.Space.IsFirstOrderThickening`: **Stacks 05ZK**, part (2).
* `AlgebraicGeometry.Space.IsFiniteOrderThickening`: **Stacks 05ZK**, part (3).

## Main results

* `AlgebraicGeometry.Space.exists_nthOrderThickening_chart_pullback`: an `n`th-order
  thickening of algebraic spaces pulls back along an étale scheme chart of the ambient space
  to an `n`th-order thickening of schemes.
* `AlgebraicGeometry.Space.exists_finiteOrderThickening_chart_pullback`: the same for
  finite-order thickenings.

## Implementation notes

The source measures the order by powers of the quasi-coherent sheaf of ideals defining the
closed subspace. That sheaf is `AlgebraicGeometry.Space.definingIdealSheaf`, whose sections
over an étale chart are `AlgebraicGeometry.Space.definingIdealAt`; the power equation is
therefore stated chartwise, with the exponent chosen before the chart, so that "finite order"
means a single global exponent as in the source. No quasi-coherence of
`AlgebraicGeometry.Space.definingIdealSheaf` is used.

As in the source, the order conditions do not separately require the topological condition of
part (1): they ask only that `Z` be a closed subspace of `X`.

The chart descent is affine-local on the chart. The kernel ideal sheaf of a morphism of
schemes is determined by its values on affine opens, and an affine open `V` of the scheme
underlying a chart `U` is itself an object of the big fppf category over `S`, so
`V ⟶ U ⟶ X` is again an étale chart. On it,
`AlgebraicGeometry.Space.definingIdealAt_eq_ker` identifies the defining ideal with the
kernel of pullback of regular functions along a closed immersion of affine schemes, which is
exactly the value on `V` of the kernel ideal sheaf of the chart-level closed immersion, by
`AlgebraicGeometry.Scheme.ker_ideal_of_isPullback_of_isOpenImmersion`.

## References

* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Thickenings

namespace AlgebraicGeometry

universe u

/-! ### Nilpotence of a kernel ideal sheaf, read on open charts -/

/-- **Nilpotence of a kernel ideal sheaf is affine-local on the target.** If every affine open
`V` of the target carries a cartesian square exhibiting a morphism `f₀` over `V` as the base
change of `f`, and the kernel of `f₀` on global sections has vanishing `(n+1)`st power, then
the kernel ideal sheaf of `f` has vanishing `(n+1)`st power. -/
theorem Scheme.ker_pow_eq_bot_of_forall_affineOpens {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] {n : ℕ}
    (h : ∀ V : Y.affineOpens, ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ V.1.toScheme) (g : X₀ ⟶ X),
      IsPullback f₀ g V.1.ι f ∧ RingHom.ker (f₀.appTop).hom ^ (n + 1) = ⊥) :
    f.ker ^ (n + 1) = ⊥ := by
  have himg : ∀ V : Y.affineOpens, IsAffineOpen (V.1.ι ''ᵁ (⊤ : V.1.toScheme.Opens)) := by
    intro V
    have : IsAffine V.1.toScheme := V.2
    exact (isAffineOpen_top V.1.toScheme).image_of_isOpenImmersion _
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun V : Y.affineOpens ↦ ⟨V.1.ι ''ᵁ (⊤ : V.1.toScheme.Opens), himg V⟩) ?_ ?_
  · refine le_antisymm le_top fun x _ ↦ ?_
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hW⟩, ?_⟩
    show x ∈ ((⟨W, hW⟩ : Y.affineOpens).1.ι ''ᵁ
      (⊤ : (⟨W, hW⟩ : Y.affineOpens).1.toScheme.Opens) : Y.Opens)
    rwa [Scheme.Opens.ι_image_top]
  · intro V
    show f.ker.ideal _ ^ (n + 1) = ⊥
    obtain ⟨X₀, f₀, g, hsq, hker⟩ := h V
    have hV : IsAffine V.1.toScheme := V.2
    have hqc : QuasiCompact f₀ := MorphismProperty.of_isPullback hsq.flip inferInstance
    have hlocal := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f f₀ g V.1.ι hsq
      ⟨⊤, isAffineOpen_top V.1.toScheme⟩
    have hzero : f₀.ker.ideal ⟨⊤, isAffineOpen_top V.1.toScheme⟩ ^ (n + 1) = ⊥ := by
      rwa [Scheme.Hom.ker_apply]
    rw [hlocal] at hzero
    have hzero' : ((f.ker.ideal ⟨V.1.ι ''ᵁ (⊤ : V.1.toScheme.Opens), himg V⟩).comap
        (V.1.ι.appIso (⊤ : V.1.toScheme.Opens)).inv.hom) ^ (n + 1) = ⊥ := hzero
    have hsurj := (ConcreteCategory.bijective_of_isIso
      (V.1.ι.appIso (⊤ : V.1.toScheme.Opens)).inv).2
    have hmap := congrArg
      (Ideal.map (V.1.ι.appIso (⊤ : V.1.toScheme.Opens)).inv.hom) hzero'
    rwa [Ideal.map_pow, Ideal.map_comap_of_surjective _ hsurj, Ideal.map_bot] at hmap

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The order of a thickening -/

/-- **Stacks 05ZK, part (4).** A closed subspace `G` of an algebraic space `X` over `S` is an
*`n`th-order thickening* when the `(n+1)`st power of its defining ideal vanishes on every
object of the small étale site of `X`. -/
@[stacks 05ZK "part (4): nth-order thickening"]
abbrev IsNthOrderThickening (n : ℕ) (X : AlgebraicSpaces B S hS) (G : Subfunctor X.1) : Prop :=
  ∃ hG : IsThickening B S hS X G,
    ∀ U : SmallEtale B S hS X.1, definingIdealAt B S hS X ⟨G, hG.1⟩ (op U) ^ (n + 1) = ⊥

/-- **Stacks 05ZK, part (2).** A closed subspace `G` of an algebraic space `X` over `S` is a
*first-order thickening* when its defining ideal has square zero on every object of the small
étale site of `X`. -/
@[stacks 05ZK "part (2): first-order thickening"]
abbrev IsFirstOrderThickening (X : AlgebraicSpaces B S hS) (G : Subfunctor X.1) : Prop :=
  IsNthOrderThickening B S hS 1 X G

/-- **Stacks 05ZK, part (3).** A closed subspace `G` of an algebraic space `X` over `S` is a
*finite-order thickening* when its defining ideal is nilpotent, with one exponent valid on
every object of the small étale site of `X`. -/
@[stacks 05ZK "part (3): finite-order thickening"]
abbrev IsFiniteOrderThickening (X : AlgebraicSpaces B S hS) (G : Subfunctor X.1) : Prop :=
  ∃ n : ℕ, IsNthOrderThickening B S hS n X G

/-- A first-order thickening is of finite order. -/
theorem IsFirstOrderThickening.isFiniteOrderThickening {X : AlgebraicSpaces B S hS}
    {G : Subfunctor X.1} (h : IsFirstOrderThickening B S hS X G) :
    IsFiniteOrderThickening B S hS X G :=
  ⟨1, h⟩

/-- An `n`th-order thickening is a thickening. -/
theorem IsNthOrderThickening.isThickening {n : ℕ} {X : AlgebraicSpaces B S hS}
    {G : Subfunctor X.1} (h : IsNthOrderThickening B S hS n X G) :
    IsThickening B S hS X G :=
  h.1

/-- A first-order thickening is a thickening of order one. -/
theorem IsFirstOrderThickening.isNthOrderThickening {X : AlgebraicSpaces B S hS}
    {G : Subfunctor X.1} (h : IsFirstOrderThickening B S hS X G) :
    IsNthOrderThickening B S hS 1 X G :=
  h

/-- A thickening of some finite order is a finite-order thickening. -/
theorem IsNthOrderThickening.isFiniteOrderThickening {n : ℕ} {X : AlgebraicSpaces B S hS}
    {G : Subfunctor X.1} (h : IsNthOrderThickening B S hS n X G) :
    IsFiniteOrderThickening B S hS X G :=
  ⟨n, h⟩

/-! ### Objects of the site cut out by an open subscheme -/

section OpensObject

variable {B S hS}

/-- An open subscheme of the scheme underlying an object `U` of the big fppf category over
`S`, regarded as an object of that category through the structure morphism of `U`.

This is the same object as `AlgebraicGeometry.Space.openSiteObject`, with the ambient object
implicit and marked `@[reducible]`, which is what the étale-chart descent below and its
consumers unfold through. It is distinct from `AlgebraicGeometry.Space.opensObject`, which
builds the structure morphism out of `ObjectProperty.homMk` instead of out of the inclusion's
`preimage` and takes the site data explicitly. -/
@[reducible] noncomputable def openSiteObject' (U : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) : BigFppfOver B S hS :=
  Over.mk (B.inclusion.preimage (X := B.obj (contains_coe_opens B S hS U V)) (Y := U.left)
    (V.ι : B.inclusion.obj (B.obj (contains_coe_opens B S hS U V)) ⟶ B.inclusion.obj U.left) ≫
      U.hom)

/-- The open immersion of an open subscheme of a chart into that chart, as a morphism of the
big fppf category over `S`. -/
theorem exists_openSiteObject'_hom (U : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    ∃ ι : openSiteObject' U V ⟶ U, (BigFppfOver.toScheme B S hS).map ι = V.ι :=
  BigFppfOver.exists_hom_of_comp_eq B S hS (X := openSiteObject' U V) (Y := U) V.ι
    (((B.inclusion.map_comp _ U.hom).trans
      (congrArg (fun k ↦ k ≫ B.inclusion.map U.hom) (B.inclusion.map_preimage _))).symm)

end OpensObject

/-! ### Descent of the order to étale scheme charts -/

/-- **The order of a thickening is read on étale charts.** An `n`th-order thickening of
algebraic spaces pulls back along any étale scheme chart of the ambient space to an
`n`th-order thickening of schemes. -/
theorem exists_nthOrderThickening_chart_pullback {n : ℕ} {X : AlgebraicSpaces B S hS}
    {G : Subfunctor X.1} (hG : IsNthOrderThickening B S hS n X G)
    (U : BigFppfOver B S hS) (q : yoneda.obj U ⟶ X.1)
    (hq : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q) :
    ∃ (U₀ : BigFppfOver B S hS) (j : U₀ ⟶ U) (p : yoneda.obj U₀ ⟶ G.toFunctor),
      IsPullback p (yoneda.map j) G.ι q ∧
        Stacks.Thickenings.IsNthOrderThickening n
          ((BigFppfOver.toScheme B S hS).map j) := by
  classical
  obtain ⟨⟨hGc, _hsurj⟩, hpow⟩ := hG
  have hci : ∀ q' : yoneda.obj U ⟶ X.1, _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hGc.2.rep.snd q')) :=
    fun q' ↦ hGc.2.property q' _ _ (hGc.2.rep.isPullback q')
  refine ⟨hGc.2.rep.pullback q, hGc.2.rep.snd q, hGc.2.rep.fst q, hGc.2.rep.isPullback q,
    hci q, ?_⟩
  have := hci q
  refine Scheme.ker_pow_eq_bot_of_forall_affineOpens _ fun V ↦ ?_
  -- The affine open `V` of the chart, composed with the chart, is again an étale chart.
  obtain ⟨ιV, hιV⟩ := exists_openSiteObject'_hom U V.1
  have hetaleV : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map ιV ≫ q) := by
    have := (isMultiplicative_presheaf_etale B S hS).toIsStableUnderComposition
    refine MorphismProperty.comp_mem _ _ _ ?_ hq
    refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ ιV).2 ?_
    rw [hιV]
    exact inferInstanceAs (Etale V.1.ι)
  -- The two chart-level closed immersions form a cartesian square over `V ⟶ U`.
  have hsqPre := IsPullback.of_right' (hGc.2.rep.isPullback (yoneda.map ιV ≫ q))
    (hGc.2.rep.isPullback q)
  have hsqSite : IsPullback (yoneda.preimage
      ((hGc.2.rep.isPullback q).lift (hGc.2.rep.fst (yoneda.map ιV ≫ q))
        (yoneda.map (hGc.2.rep.snd (yoneda.map ιV ≫ q)) ≫ yoneda.map ιV)
        (by rw [(hGc.2.rep.isPullback (yoneda.map ιV ≫ q)).w, Category.assoc])))
      (hGc.2.rep.snd (yoneda.map ιV ≫ q)) (hGc.2.rep.snd q) ιV := by
    refine IsPullback.of_map_of_faithful yoneda ?_
    rwa [yoneda.map_preimage]
  have hsqScheme := (hsqSite.map (BigFppfOver.toScheme B S hS)).flip
  rw [hιV] at hsqScheme
  refine ⟨_, (BigFppfOver.toScheme B S hS).map (hGc.2.rep.snd (yoneda.map ιV ≫ q)),
    _, hsqScheme, ?_⟩
  -- On that chart the defining ideal is the kernel the chart-level immersion induces.
  have h := hpow ⟨CostructuredArrow.mk (yoneda.map ιV ≫ q), hetaleV⟩
  rwa [definingIdealAt_eq_ker B S hS X ⟨G, hGc⟩
    ⟨CostructuredArrow.mk (yoneda.map ιV ≫ q), hetaleV⟩, Scheme.Γ_map_op] at h

/-- **The finite order of a thickening is read on étale charts.** A finite-order thickening of
algebraic spaces pulls back along any étale scheme chart of the ambient space to a
finite-order thickening of schemes. -/
theorem exists_finiteOrderThickening_chart_pullback {X : AlgebraicSpaces B S hS}
    {G : Subfunctor X.1} (hG : IsFiniteOrderThickening B S hS X G)
    (U : BigFppfOver B S hS) (q : yoneda.obj U ⟶ X.1)
    (hq : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q) :
    ∃ (U₀ : BigFppfOver B S hS) (j : U₀ ⟶ U) (p : yoneda.obj U₀ ⟶ G.toFunctor),
      IsPullback p (yoneda.map j) G.ι q ∧
        Stacks.Thickenings.IsFiniteOrderThickening
          ((BigFppfOver.toScheme B S hS).map j) := by
  obtain ⟨n, hn⟩ := hG
  obtain ⟨U₀, j, p, hpb, hclosed, hker⟩ :=
    exists_nthOrderThickening_chart_pullback B S hS hn U q hq
  exact ⟨U₀, j, p, hpb, hclosed, n, hker⟩

end Space

end AlgebraicGeometry

end
