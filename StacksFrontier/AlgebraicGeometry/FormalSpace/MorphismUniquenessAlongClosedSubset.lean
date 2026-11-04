module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Completion
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.PointwiseEtale
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SmoothnessOverNoetherianBase
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DiagonalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability

/-!
# Two morphisms agreeing away from a closed subset and on its formal completion

Let `S` be a scheme contained in a big fppf site `B`, let `X` and `Y` be locally Noetherian
algebraic spaces over `S`, let `T ⊆ |X|` and `T' ⊆ |Y|` be closed subsets, and let
`a, b : X ⟶ Y` be morphisms with `|a| (T) ⊆ T'` and `|b| (T) ⊆ T'`. If `a` and `b` agree on the
open subspace `X ∖ T` and the induced morphisms of completions
`a_{/T}, b_{/T} : X_{/T} ⟶ Y_{/T'}` agree, then `a = b`.

The two conditions do *not* cover `X`: a section of `X` over an object of the site need lie
neither over `T` nor over its complement. What makes the statement true is that the locus where
`a` and `b` agree is an *étale* subspace of `X`: it is cut out by the diagonal of `Y`, hence is
a monomorphism locally of finite type over `X`, and the completion hypothesis makes its base
change to every infinitesimal neighbourhood of `T` an isomorphism, which forces étaleness over
`T` by the infinitesimal lifting criterion.

## Main definitions

* `AlgebraicGeometry.Space.completionSubfunctorMap` is the morphism of completions
  `X_{/T} ⟶ Y_{/T'}` induced by a morphism `X ⟶ Y` carrying `T` into `T'`.

## Main results

* `AlgebraicGeometry.Space.eq_of_eq_on_compl_of_completionSubfunctorMap_eq`: **Stacks 0AR7**.

## Implementation notes

*The completion.* `X_{/T}` is the completion of Stacks 0AIZ, the subfunctor
`AlgebraicGeometry.Space.completionSubfunctor` of sections whose point-set image lies in `T`;
`AlgebraicGeometry.Space.completionSheaf` is its fppf sheafification, to which it is
canonically isomorphic because the condition on a section is already fppf-local. The hypothesis
is therefore stated for the induced morphism of subfunctors. Likewise `X ∖ T` is
`AlgebraicGeometry.Space.openSubspaceOfPoints` applied to `Tᶜ`, the open subspace of Stacks
03BZ with point set `Tᶜ`, and the hypothesis is the equality of the two restrictions along its
inclusion.

*The argument.* Equality of morphisms out of `X` may be tested on a surjective étale atlas
`p : V ⟶ X` (`AlgebraicGeometry.Space.hom_ext_of_etale_atlas`), and the atlas may be chosen
with `V` locally Noetherian since `X` is. Write `W ⊆ |V|` for the inverse image of `T`, a closed
subset, and let `E = V ×_{(p a, p b), Y × Y} Y` be the locus in `V` where the two composites
agree. The diagonal of `Y` is representable, a monomorphism and locally of finite type — Stacks
02X4 — so `E` is an object of the site and `E ⟶ V` is a monomorphism of schemes locally of
finite type. A morphism `Z ⟶ V` factors through `E` exactly when the two composites to `Y` agree
on it, so:

* the open complement of `W` factors through `E`, because its image in `|X|` misses `T`, by the
  hypothesis on `X ∖ T`;
* every infinitesimal neighbourhood of the reduced closed subscheme supported on `W` factors
  through `E`, because such a neighbourhood has underlying space `W` and so its image in `|X|`
  lies in `T`, by the hypothesis on the completions.

A monomorphism with a section is an isomorphism, so the base change of `E ⟶ V` to each of those
is an isomorphism, hence étale; **Stacks 0A43** then makes `E ⟶ V` étale at every point over
`W`, and over the open complement it is an isomorphism. An étale monomorphism is an open
immersion, and the same two factorizations make it surjective, so `E ⟶ V` is an isomorphism and
the two composites agree.

*What the Noetherian hypothesis is for.* Only local Noetherianness of `X` is used, through
Stacks 0A43. The source assumes it of `Y` as well; that hypothesis is recorded and unused.

## References

* [Stacks Project, Tag 0AR7](https://stacks.math.columbia.edu/tag/0AR7)
* [Stacks Project, Tag 0GI1](https://stacks.math.columbia.edu/tag/0GI1)
* [Stacks Project, Tag 0A43](https://stacks.math.columbia.edu/tag/0A43)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry

/-! ### Monomorphisms of schemes with sections along a closed subset -/

/-- A base change of a monomorphism which admits a section over the base is an isomorphism. -/
theorem isIso_pullback_snd_of_section {V E A : Scheme.{u}} (f : E ⟶ V) [Mono f]
    (q : A ⟶ V) (τ : A ⟶ E) (hτ : τ ≫ f = q) : IsIso (pullback.snd f q) := by
  have h : τ ≫ f = 𝟙 A ≫ q := by rwa [Category.id_comp]
  have : IsSplitEpi (pullback.snd f q) :=
    ⟨⟨pullback.lift τ (𝟙 A) h, pullback.lift_snd τ (𝟙 A) h⟩⟩
  exact isIso_of_mono_of_isSplitEpi _

/-- An infinitesimal neighbourhood of a closed immersion has the same image as the closed
immersion itself. -/
theorem range_nthOrderToBase {V Z : Scheme.{u}} (i : Z ⟶ V) [IsClosedImmersion i]
    (n : ℕ) :
    Set.range (Stacks.Thickenings.nthOrderToBase i n).base = Set.range i.base := by
  have hth := Stacks.Thickenings.nthOrderInclusion_isNthOrderThickening i n
  have hsurj := (isThickening_of_ker_pow_eq_bot _ hth.1 hth.2).2
  have hfac : ∀ z : Z, Stacks.Thickenings.nthOrderToBase i n
      (Stacks.Thickenings.nthOrderInclusion i n z) = i z := by
    intro z
    conv_rhs => rw [← Stacks.Thickenings.nthOrderInclusion_toBase i n]
    rfl
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := hsurj x
    exact ⟨z, (hfac z).symm⟩
  · rintro _ ⟨z, rfl⟩
    exact ⟨Stacks.Thickenings.nthOrderInclusion i n z, hfac z⟩

/-- **The scheme-theoretic heart of Stacks 0AR7.** A monomorphism locally of finite type onto a
locally Noetherian scheme which has a section over the open complement of a closed subscheme and
over every infinitesimal neighbourhood of that subscheme is an isomorphism. -/
theorem isIso_of_mono_of_sections_along_closed {V E Z : Scheme.{u}}
    [IsLocallyNoetherian V] (f : E ⟶ V) [Mono f] [LocallyOfFiniteType f]
    (i : Z ⟶ V) [IsClosedImmersion i] (U : V.Opens)
    (hU : (U : Set V) = (Set.range i.base)ᶜ)
    (σ : U.toScheme ⟶ E) (hσ : σ ≫ f = U.ι)
    (τ : ∀ n : ℕ, Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood i n ⟶ E)
    (hτ : ∀ n : ℕ, τ n ≫ f = Stacks.Thickenings.nthOrderToBase i n) :
    IsIso f := by
  have hopenIso := isIso_pullback_snd_of_section f U.ι σ hσ
  have hetale : Etale f := by
    rw [etale_iff_forall_etaleAt]
    intro x
    by_cases hx : f x ∈ Set.range i.base
    · refine etaleAt_of_etale_infinitesimalNeighbourhoods f i (fun n => ?_) x hx
      have := isIso_pullback_snd_of_section f (Stacks.Thickenings.nthOrderToBase i n) (τ n) (hτ n)
      infer_instance
    · have hmem : f x ∈ Set.range U.ι.base :=
        (Scheme.Opens.range_ι U).symm.subset (by rwa [hU])
      obtain ⟨x', hx'⟩ : x ∈ Set.range (pullback.fst f U.ι).base := by
        rwa [Scheme.Pullback.range_fst]
      have hEt : Etale (pullback.fst f U.ι ≫ f) := by
        rw [pullback.condition]
        infer_instance
      have hat := (etale_iff_forall_etaleAt _).mp hEt x'
      exact hx' ▸ Stacks.FundamentalGroup.ExtendedEtaleFold.etaleAt_of_etaleAt_isOpenImmersion_comp
        (pullback.fst f U.ι) f x' hat
  have hsurj : Function.Surjective f.base := by
    intro v
    by_cases hv : v ∈ Set.range i.base
    · obtain ⟨z, hz⟩ := hv
      refine ⟨τ 0 (Stacks.Thickenings.nthOrderInclusion i 0 z), ?_⟩
      have h0 : f (τ 0 (Stacks.Thickenings.nthOrderInclusion i 0 z)) =
          Stacks.Thickenings.nthOrderToBase i 0 (Stacks.Thickenings.nthOrderInclusion i 0 z) := by
        conv_rhs => rw [← hτ 0]
        rfl
      rw [h0, ← hz]
      conv_rhs => rw [← Stacks.Thickenings.nthOrderInclusion_toBase i 0]
      rfl
    · have hvU : v ∈ (U : Set V) := by rwa [hU]
      refine ⟨σ ⟨v, hvU⟩, ?_⟩
      have h1 : f (σ ⟨v, hvU⟩) = U.ι ⟨v, hvU⟩ := by
        conv_rhs => rw [← hσ]
        rfl
      rw [h1]
      rfl
  rw [isIso_iff_isOpenImmersion_and_surjective]
  exact ⟨IsOpenImmersion.of_flat_of_mono f, ⟨hsurj⟩⟩

namespace Space

/-! ### The completion of a morphism along a closed subset -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- A section of a presheaf has point-set image in a set of points exactly when the morphism it
determines has. -/
theorem hasImageIn_iff_range_subset {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (points B S hS X)) (W : BigFppfOver B S hS) (x : X.obj (op W)) :
    HasImageIn B S hS X T W x ↔
      Set.range (pointsMap B S hS (yoneda.obj W) (yonedaEquiv.symm x)) ⊆ T := by
  constructor
  · rintro h _ ⟨w, rfl⟩
    obtain ⟨p, rfl⟩ := Quot.exists_rep w
    exact h p
  · intro h p
    exact h ⟨p.class B S hS (yoneda.obj W), rfl⟩

/-- The morphism determined by the image of a section under a morphism of presheaves. -/
private theorem yonedaEquiv_symm_app {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : X ⟶ Y)
    (W : BigFppfOver B S hS) (x : X.obj (op W)) :
    yonedaEquiv.symm (a.app (op W) x) = yonedaEquiv.symm x ≫ a := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- The morphism of completions `X_{/T} ⟶ Y_{/T'}` induced by a morphism `a : X ⟶ Y` of
presheaves whose map on points carries `T` into `T'`. -/
def completionSubfunctorMap {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : X ⟶ Y)
    (T : Set (points B S hS X)) (T' : Set (points B S hS Y))
    (ha : pointsMap B S hS X a '' T ⊆ T') :
    (completionSubfunctor B S hS X T).toFunctor ⟶
      (completionSubfunctor B S hS Y T').toFunctor where
  app W := ↾fun x => ⟨ULift.up (a.app W x.1.down), by
    change HasImageIn B S hS Y T' W.unop (a.app W x.1.down)
    rw [hasImageIn_iff_range_subset, yonedaEquiv_symm_app, pointsMap_comp]
    rintro _ ⟨w, rfl⟩
    exact ha ⟨_, (hasImageIn_iff_range_subset B S hS T W.unop x.1.down).mp x.2 ⟨w, rfl⟩, rfl⟩⟩
  naturality W W' k := by
    ext x
    exact Subtype.ext (congrArg ULift.up (NatTrans.naturality_apply a k x.1.down))

/-- Two morphisms whose completions along `T` agree agree on every morphism from a representable
presheaf whose point-set image lies in `T`. -/
private theorem comp_eq_of_range_subset
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a b : X ⟶ Y)
    {T : Set (points B S hS X)} {T' : Set (points B S hS Y)}
    (ha : pointsMap B S hS X a '' T ⊆ T') (hb : pointsMap B S hS X b '' T ⊆ T')
    (h : completionSubfunctorMap B S hS a T T' ha = completionSubfunctorMap B S hS b T T' hb)
    {W : BigFppfOver B S hS} (q : yoneda.obj W ⟶ X)
    (hq : Set.range (pointsMap B S hS (yoneda.obj W) q) ⊆ T) :
    q ≫ a = q ≫ b := by
  have hx : HasImageIn B S hS X T W (yonedaEquiv q) := by
    rwa [hasImageIn_iff_range_subset, Equiv.symm_apply_apply]
  have happ := congrFun (congrArg (fun α => α.app (op W)) h)
    (⟨ULift.up (yonedaEquiv q), hx⟩ :
      (completionSubfunctor B S hS X T).toFunctor.obj (op W))
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_comp]
  exact congrArg ULift.down (congrArg Subtype.val happ)

/-- Two morphisms agreeing on the open subspace with point set `Tᶜ` agree on every morphism from
a representable presheaf whose point-set image misses `T`. -/
theorem comp_eq_of_range_subset_compl
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a b : X ⟶ Y)
    {T : Set (points B S hS X)}
    (h : (openSubspaceOfPoints B S hS X Tᶜ).ι ≫ a = (openSubspaceOfPoints B S hS X Tᶜ).ι ≫ b)
    {W : BigFppfOver B S hS} (q : yoneda.obj W ⟶ X)
    (hq : Set.range (pointsMap B S hS (yoneda.obj W) q) ⊆ Tᶜ) :
    q ≫ a = q ≫ b := by
  have hx : yonedaEquiv q ∈ (openSubspaceOfPoints B S hS X Tᶜ).obj (op W) := by
    rwa [mem_openSubspaceOfPoints_iff, Equiv.symm_apply_apply]
  have happ := congrFun (congrArg (fun α => α.app (op W)) h)
    (⟨yonedaEquiv q, hx⟩ : (openSubspaceOfPoints B S hS X Tᶜ).toFunctor.obj (op W))
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_comp]
  exact happ

/-! ### The equalizer of two morphisms out of a representable presheaf -/

/-- The site object representing the source of a monomorphism of schemes into a site object. -/
private def monoSiteObj {V : BigFppfOver B S hS} {A : Scheme.{u}}
    (h : A ⟶ (BigFppfOver.toScheme B S hS).obj V) [Mono h] : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (B.contains_of_mono h V.left.2) (h ≫ B.inclusion.map V.hom)

/-- The morphism of site objects underlying a monomorphism of schemes into a site object. -/
private def monoSiteHom {V : BigFppfOver B S hS} {A : Scheme.{u}}
    (h : A ⟶ (BigFppfOver.toScheme B S hS).obj V) [Mono h] : monoSiteObj B S hS h ⟶ V :=
  Over.homMk (ObjectProperty.homMk h) (by apply ObjectProperty.hom_ext; rfl)

private theorem toScheme_map_monoSiteHom {V : BigFppfOver B S hS} {A : Scheme.{u}}
    (h : A ⟶ (BigFppfOver.toScheme B S hS).obj V) [Mono h] :
    (BigFppfOver.toScheme B S hS).map (monoSiteHom B S hS h) = h := rfl

/-- **Two morphisms out of a locally Noetherian atlas agreeing over a closed subset and over its
complement.** This is Stacks 0AR7 after reduction to an atlas: `Ws` is the inverse image of the
closed subset and the two hypotheses say that the morphisms agree on every site object mapping
into `Ws`, respectively into its complement. -/
theorem comp_eq_of_sections {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (V : BigFppfOver B S hS)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    (c d : yoneda.obj V ⟶ Y)
    (Ws : Set ((BigFppfOver.toScheme B S hS).obj V)) (hWs : IsClosed Ws)
    (hin : ∀ (Zo : BigFppfOver B S hS) (z : Zo ⟶ V),
      Set.range ((BigFppfOver.toScheme B S hS).map z).base ⊆ Ws →
      yoneda.map z ≫ c = yoneda.map z ≫ d)
    (hout : ∀ (Zo : BigFppfOver B S hS) (z : Zo ⟶ V),
      Set.range ((BigFppfOver.toScheme B S hS).map z).base ⊆ Wsᶜ →
      yoneda.map z ≫ c = yoneda.map z ≫ d) :
    c = d := by
  obtain ⟨E, e, hmono, hlft, hdict, hfinish⟩ :
      ∃ (E : BigFppfOver B S hS) (e : E ⟶ V),
        Mono ((BigFppfOver.toScheme B S hS).map e) ∧
        LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map e) ∧
        (∀ (Zo : BigFppfOver B S hS) (z : Zo ⟶ V),
          yoneda.map z ≫ c = yoneda.map z ≫ d → ∃ w : Zo ⟶ E, w ≫ e = z) ∧
        (IsIso ((BigFppfOver.toScheme B S hS).map e) → c = d) := by
    have hmonoP := presheaf_monomorphisms_diag B S hS Y hY
    have hlftP := presheaf_locallyOfFiniteType_diag B S hS Y hY
    have hrep : yoneda.relativelyRepresentable (diag Y) := hY.diagonal_representable
    refine ⟨hrep.pullback (prod.lift c d), hrep.snd (prod.lift c d),
      hmonoP.property_snd _, hlftP.property_snd _, ?_, ?_⟩
    · intro Zo z hz
      have hi : (yoneda.map z ≫ c) ≫ diag Y = yoneda.map z ≫ prod.lift c d := by
        simp only [diag, prod.comp_lift, Category.comp_id, hz]
      exact ⟨hrep.lift (yoneda.map z ≫ c) z hi, hrep.lift_snd _ _ _⟩
    · intro hiso
      have h1 : IsIso (B.inclusion.map
          ((Over.forget (B.obj hS)).map (hrep.snd (prod.lift c d)))) := hiso
      have h2 : IsIso ((Over.forget (B.obj hS)).map (hrep.snd (prod.lift c d))) :=
        isIso_of_reflects_iso _ B.inclusion
      have h3 : IsIso (hrep.snd (prod.lift c d)) :=
        isIso_of_reflects_iso _ (Over.forget (B.obj hS))
      have hG : prod.lift c d =
          (inv (yoneda.map (hrep.snd (prod.lift c d))) ≫ hrep.fst (prod.lift c d)) ≫ diag Y := by
        rw [Category.assoc, hrep.w, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
      have h4 := congrArg (fun α : yoneda.obj V ⟶ Y ⨯ Y => α ≫ prod.fst) hG
      have h5 := congrArg (fun α : yoneda.obj V ⟶ Y ⨯ Y => α ≫ prod.snd) hG
      simp only [diag, Category.assoc, prod.lift_fst, prod.lift_snd, Category.comp_id] at h4 h5
      exact h4.trans h5.symm
  have := hmono
  have := hlft
  obtain ⟨Zs, i, hiCI, hirange⟩ :
      ∃ (Zs : Scheme.{u}) (i : Zs ⟶ (BigFppfOver.toScheme B S hS).obj V),
        AlgebraicGeometry.IsClosedImmersion i ∧ Set.range i.base = Ws :=
    ⟨_, (Scheme.IdealSheafData.vanishingIdeal (⟨Ws, hWs⟩ :
      TopologicalSpace.Closeds ((BigFppfOver.toScheme B S hS).obj V))).subschemeι,
      inferInstance, by
        rw [Scheme.IdealSheafData.range_subschemeι,
          Scheme.IdealSheafData.coe_support_vanishingIdeal]
        rfl⟩
  have := hiCI
  obtain ⟨U, hU⟩ : ∃ U : ((BigFppfOver.toScheme B S hS).obj V).Opens,
      (U : Set ((BigFppfOver.toScheme B S hS).obj V)) = (Set.range i.base)ᶜ :=
    ⟨⟨(Set.range i.base)ᶜ, by rw [hirange]; exact hWs.isOpen_compl⟩, rfl⟩
  obtain ⟨wU, hwU⟩ := hdict (monoSiteObj B S hS U.ι) (monoSiteHom B S hS U.ι)
    (hout _ _ ((Scheme.Opens.range_ι U).trans_subset (by rw [hU, hirange])))
  have hthick : ∀ n : ℕ, ∃ τ : Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood i n ⟶
      (BigFppfOver.toScheme B S hS).obj E,
      τ ≫ (BigFppfOver.toScheme B S hS).map e = Stacks.Thickenings.nthOrderToBase i n := by
    intro n
    have hmn : Mono (Stacks.Thickenings.nthOrderToBase i n) := by
      have heq : Stacks.Thickenings.nthOrderToBase i n =
          (Scheme.Hom.ker (Scheme.Hom.liftCoborder i) ^ (n + 1)).subschemeι ≫
            (Scheme.Hom.coborderRange i).ι := rfl
      rw [heq]
      infer_instance
    obtain ⟨w, hw⟩ := hdict (monoSiteObj B S hS (Stacks.Thickenings.nthOrderToBase i n))
      (monoSiteHom B S hS (Stacks.Thickenings.nthOrderToBase i n))
      (hin _ _ ((range_nthOrderToBase i n).trans_subset hirange.subset))
    exact ⟨(BigFppfOver.toScheme B S hS).map w,
      ((BigFppfOver.toScheme B S hS).map_comp w e).symm.trans
        ((congrArg (BigFppfOver.toScheme B S hS).map hw).trans
          (toScheme_map_monoSiteHom B S hS _))⟩
  choose τ hτ using hthick
  exact hfinish (isIso_of_mono_of_sections_along_closed
    ((BigFppfOver.toScheme B S hS).map e) i U hU
    ((BigFppfOver.toScheme B S hS).map wU)
    (((BigFppfOver.toScheme B S hS).map_comp wU e).symm.trans
      ((congrArg (BigFppfOver.toScheme B S hS).map hwU).trans
        (toScheme_map_monoSiteHom B S hS _))) τ hτ)

/-! ### Stacks 0AR7 -/

/-- **Stacks 0AR7.** Let `X` and `Y` be locally Noetherian algebraic spaces over `S`, let
`T ⊆ |X|` and `T' ⊆ |Y|` be closed subsets and let `a, b : X ⟶ Y` be morphisms with
`|a| (T) ⊆ T'` and `|b| (T) ⊆ T'`. If `a` and `b` agree on the open subspace `X ∖ T` and the
induced morphisms of completions `a_{/T}, b_{/T} : X_{/T} ⟶ Y_{/T'}` agree, then `a = b`. -/
@[stacks 0AR7]
theorem eq_of_eq_on_compl_of_completionSubfunctorMap_eq
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXnoeth : HasEtaleLocalProperty B S hS X (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (_hYnoeth : HasEtaleLocalProperty B S hS Y (fun V : Scheme.{u} => IsLocallyNoetherian V))
    {T : Set (points B S hS X)} (hT : IsClosed T)
    {T' : Set (points B S hS Y)} (_hT' : IsClosed T')
    (a b : X ⟶ Y)
    (ha : pointsMap B S hS X a '' T ⊆ T') (hb : pointsMap B S hS X b '' T ⊆ T')
    (hcompl :
      (openSubspaceOfPoints B S hS X Tᶜ).ι ≫ a = (openSubspaceOfPoints B S hS X Tᶜ).ι ≫ b)
    (hcompletion : completionSubfunctorMap B S hS a T T' ha =
      completionSubfunctorMap B S hS b T T' hb) :
    a = b := by
  obtain ⟨V, p, hsurj, hetale, hVnoeth⟩ := hXnoeth
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) := hVnoeth
  refine hom_ext_of_etale_atlas B S hS hX.isSheaf hY.isSheaf p hsurj hetale ?_
  obtain ⟨Ws, hWsmem, hWsclosed⟩ :
      ∃ Ws : Set ((BigFppfOver.toScheme B S hS).obj V),
        (∀ w : points B S hS (yoneda.obj V),
          (pointsToScheme B S hS V w ∈ Ws ↔
            pointsMap B S hS (yoneda.obj V) p w ∈ T)) ∧ IsClosed Ws := by
    refine ⟨pointsToScheme B S hS V '' (pointsMap B S hS (yoneda.obj V) p ⁻¹' T), ?_, ?_⟩
    · intro w
      refine ⟨?_, fun hw => ⟨w, hw, rfl⟩⟩
      rintro ⟨v, hv, hveq⟩
      obtain rfl := injective_pointsToScheme B S hS V hveq
      exact hv
    · exact (isClosed_pointTopology_yoneda_iff_isClosed_image B S hS V _).mp
        (hT.preimage (continuous_pointsMap B S hS p))
  have hrange : ∀ (Zo : BigFppfOver B S hS) (z : Zo ⟶ V)
      (w : points B S hS (yoneda.obj Zo)),
      pointsToScheme B S hS V (pointsMap B S hS (yoneda.obj Zo) (yoneda.map z) w) ∈
        Set.range ((BigFppfOver.toScheme B S hS).map z).base :=
    fun Zo z w => ⟨pointsToScheme B S hS Zo w, (pointsToScheme_pointsMap_yoneda B S hS z w).symm⟩
  refine comp_eq_of_sections B S hS hY V (p ≫ a) (p ≫ b) Ws hWsclosed ?_ ?_
  · intro Zo z hz
    rw [← Category.assoc, ← Category.assoc]
    refine comp_eq_of_range_subset B S hS a b ha hb hcompletion _ ?_
    rintro _ ⟨w, rfl⟩
    rw [pointsMap_comp, Function.comp_apply]
    exact (hWsmem _).mp (hz (hrange Zo z w))
  · intro Zo z hz
    rw [← Category.assoc, ← Category.assoc]
    refine comp_eq_of_range_subset_compl B S hS a b hcompl _ ?_
    rintro _ ⟨w, rfl⟩
    rw [pointsMap_comp, Function.comp_apply]
    exact fun hmemT => hz (hrange Zo z w) ((hWsmem _).mpr hmemT)

end Space

end AlgebraicGeometry

end
