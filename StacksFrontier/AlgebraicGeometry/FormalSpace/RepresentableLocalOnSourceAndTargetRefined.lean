module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSchemeSourceRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableCancellation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SchemeAtlasRefined
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.CategoryTheory.Sites.LocallySurjectiveBaseChange

/-!
# Representability by algebraic spaces is local on the source and the target: the refined forms

Further results on when a morphism of fppf sheaves is representable by algebraic spaces,
complementing `StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget`.
Where a statement of that module is strengthened here, the stronger form carries the primed name.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AN4, condition (1) implies condition (3).** In a square as in condition (3) the
composite `U ⟶ X ⟶ Y` is representable by algebraic spaces by Stacks 0APY, and it factors
through `V`, so Stacks 0AQ0 applies to `U ⟶ V ⟶ Y`.

Stacks 0AQ0 is used in the form `isRepresentableByAlgebraicSpacesULift_of_comp`, whose
hypothesis on the relative diagonal of the morphism cancelled is **Stacks 0AN2** for the source
of that morphism, that is for `V`, which a square as in condition (3) asks to be a formal
algebraic space; it is discharged by
`…FormalSpace.relativelyRepresentable_pullback_diagonal_of_isFormalAlgebraicSpace`. -/
theorem isRepresentableOnEverySquare_of_isRepresentable' {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom) :
    IsRepresentableOnEverySquare B S hS f := by
  intro U V p q t _ hV hp hq hcomm
  have h1 : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (p ≫ f).hom :=
    Space.isRepresentableByAlgebraicSpacesULift_comp B S hS p.hom f.hom hp hf
  rw [hcomm] at h1
  exact isRepresentableByAlgebraicSpacesULift_of_comp B S hS t q
    (relativelyRepresentable_pullback_diagonal_of_isFormalAlgebraicSpace B S hS q hV) h1

/-! ### Locality on the target -/

/-! ### Locality on the source -/

/-- **Stacks 05VM for a surjective étale morphism, in the value universe of a formal algebraic
space.** A morphism of presheaves on the big fppf site of `S` which is representable by objects
of the site, surjective and étale is locally surjective: the base change along a section of the
target is one surjective étale morphism of the site, which generates a covering sieve, and the
section lifts over it. -/
theorem isLocallySurjective_of_relative_surjective_etale
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (a : F ⟶ G)
    (hs : (Space.surjectiveOnSite B S hS).relative (uliftYoneda.{u + 1}) a)
    (he : (Space.etaleOnSite B S hS).relative (uliftYoneda.{u + 1}) a) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) a := by
  constructor
  intro T y
  let ξ : (uliftYoneda.{u + 1}).obj T ⟶ G := uliftYonedaEquiv.symm y
  let q := hs.rep.snd ξ
  have hcover : Sieve.generate (Presieve.singleton q) ∈ BigFppfOver.topology B S hS T := by
    show Sieve.generate (Presieve.singleton q) ∈ B.topology.over (B.obj hS) T
    rw [B.topology.mem_over_iff, Sieve.overEquiv_generate,
      ← Sieve.arrows_generate_map_eq_functorPushforward, Sieve.generate_sieve,
      Presieve.map_singleton]
    exact Space.singleton_mem_bigFppf_topology B q.left
      (hs.property_snd ξ) (he.property ξ (hs.rep.fst ξ) q (hs.rep.isPullback ξ))
  apply (BigFppfOver.topology B S hS).superset_covering _ hcover
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨⟩
  refine ⟨uliftYonedaEquiv (hs.rep.fst ξ), ?_⟩
  have hw := congrArg uliftYonedaEquiv (hs.rep.isPullback ξ).w
  have hn := uliftYonedaEquiv_naturality ξ q.op
  exact (uliftYonedaEquiv_comp _ _).symm.trans (hw.trans
    (by simpa only [q, Quiver.Hom.unop_op, ξ, Equiv.apply_symm_apply] using hn.symm))

/-- A morphism of presheaves on the big fppf site of `S` representable by objects of the site is
representable by algebraic spaces, an object of the site being an algebraic space. -/
theorem isRepresentableByAlgebraicSpacesULift_of_relativelyRepresentable
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {a : F ⟶ G}
    (ha : (uliftYoneda.{u + 1}).relativelyRepresentable a) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS a := fun T ξ ↦
  Space.isAlgebraicSpaceULift_of_iso B S hS (ha.isPullback ξ).flip.isoPullback
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS (ha.pullback ξ))

/-- Every represented base change of a morphism of presheaves on the big fppf site of `S` which
is representable by objects of the site and étale is étale: that base change is the
universe-lifted Yoneda image of the morphism of the site representing it, up to the comparison
isomorphism of the two fibre products. -/
theorem isEtaleULift_pullback_fst_of_relative_etale
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {a : F ⟶ G}
    (ha : (Space.etaleOnSite B S hS).relative (uliftYoneda.{u + 1}) a)
    (T : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj T ⟶ G) :
    Space.IsEtaleULift.{u + 1} B S hS (pullback.fst ξ a) := by
  have h : Space.IsEtaleULift.{u + 1} B S hS
      ((ha.rep.isPullback ξ).flip.isoPullback.hom ≫ pullback.fst ξ a) := by
    rw [(ha.rep.isPullback ξ).flip.isoPullback_hom_fst]
    exact (Space.isEtaleULift_uliftYoneda_map_iff B S hS (ha.rep.snd ξ)).mpr (ha.property_snd ξ)
  have h2 := isEtaleULift_precomp_iso B S hS (ha.rep.isPullback ξ).flip.isoPullback.symm _ h
  rwa [Iso.symm_hom, Iso.inv_hom_id_assoc] at h2

/-- A morphism of presheaves on the big fppf site of `S` whose source is a universe-lifted
Yoneda presheaf and which is representable by algebraic spaces and étale is representable by
objects of the site and étale on each of them: representability by objects of the site is
**Stacks 0AHV**, and étaleness of the morphism of the site representing a base change is read
off by testing the étaleness of that base change on the comparison isomorphism between its two
fibre products. -/
theorem relative_etale_of_schemeSource {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (Z : BigFppfOver B S hS) (c : (uliftYoneda.{u + 1}).obj Z ⟶ F)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS c)
    (het : ∀ (T : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj T ⟶ F),
      Space.IsEtaleULift.{u + 1} B S hS (pullback.fst ξ c)) :
    (Space.etaleOnSite B S hS).relative (uliftYoneda.{u + 1}) c := by
  have hr : (uliftYoneda.{u + 1}).relativelyRepresentable c :=
    Space.relativelyRepresentableULift_of_isEtale_of_schemeSource B S hS c Z (Iso.refl _)
      hrep het
  apply MorphismProperty.relative_of_snd (P := Space.etaleOnSite B S hS) hr
  intro T ξ
  have hiso : (Space.etaleOnSite B S hS).relative (uliftYoneda.{u + 1})
      ((hr.isPullback ξ).flip.isoPullback.hom) := by
    have hid := Space.relative_id_etale.{u + 1} B S hS (hr.pullback ξ)
    simpa using MorphismProperty.RespectsIso.postcomp
      ((Space.etaleOnSite B S hS).relative (uliftYoneda.{u + 1}))
      (hr.isPullback ξ).flip.isoPullback.hom (𝟙 _) hid
  have hcomp := het T ξ (hr.pullback ξ) _ hiso
  rw [(hr.isPullback ξ).flip.isoPullback_hom_fst] at hcomp
  exact MorphismProperty.of_relative_map (P := Space.etaleOnSite B S hS)
    (F := uliftYoneda.{u + 1}) hcomp

/-- **A chart of the base change of a morphism along a scheme-valued point of its target, out of
an object of the site.** Let `p : U ⟶ X` be representable étale and let `p ≫ f` be
representable by algebraic spaces, where `f : X ⟶ Y`. Then every scheme-valued point
`ξ : T ⟶ Y` of the target admits an object `Z` of the site and an atlas
`β : Z ⟶ (T ×_Y X) ×_X U` of the base change of `p` which is representable by objects of the
site, surjective and étale, and whose composite with the projection to `T ×_Y X` is again
representable by objects of the site and étale.

The base change `(T ×_Y X) ×_X U` of `p` along `T ×_Y X ⟶ X` is a base change of `p ≫ f`, hence
an algebraic space over `S`, so it has such an atlas `β`. The projection to `T ×_Y X` is a base
change of `p`, hence representable by algebraic spaces and étale, so the composite
`β ≫ pr` is too; its source being an object of the site, **Stacks 0AHV** makes it
representable by objects of the site.

Nothing is asked of `p` beyond representable étaleness, so this is the chart contributed by one
member of a *family* of representable étale morphisms into `X` just as much as by a single
surjective one. It is the chart on which both Stacks 0BGR — for representability by algebraic
spaces — and Stacks 03MJ — for a property étale local on source and target — are tested, which
is why it is stated once here. -/
theorem exists_memberChart_pullback {X Y U : FppfSheaf B S hS}
    (f : X ⟶ Y) (p : U ⟶ X) (hp : IsRepresentableEtale B S hS p)
    (hpf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (p ≫ f).hom)
    (T : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj T ⟶ Y.obj) :
    ∃ (Z : BigFppfOver B S hS)
      (β : (uliftYoneda.{u + 1}).obj Z ⟶ pullback (pullback.snd ξ f.hom) p.hom),
      (Space.surjectiveOnSite B S hS).relative (uliftYoneda.{u + 1}) β ∧
      (Space.etaleOnSite B S hS).relative (uliftYoneda.{u + 1}) β ∧
      (Space.etaleOnSite B S hS).relative (uliftYoneda.{u + 1})
        (β ≫ pullback.fst (pullback.snd ξ f.hom) p.hom) := by
  obtain ⟨hprep, hpet⟩ := hp
  have hsq : IsPullback (pullback.snd (pullback.snd ξ f.hom) p.hom)
      (pullback.fst (pullback.snd ξ f.hom) p.hom) p.hom (pullback.snd ξ f.hom) :=
    (IsPullback.of_hasPullback (pullback.snd ξ f.hom) p.hom).flip
  have harep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (pullback.fst (pullback.snd ξ f.hom) p.hom) :=
    Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS _ _ _ _ hsq hprep
  have haet : ∀ (V : BigFppfOver B S hS)
      (η : (uliftYoneda.{u + 1}).obj V ⟶ pullback ξ f.hom),
      Space.IsEtaleULift.{u + 1} B S hS
        (pullback.fst η (pullback.fst (pullback.snd ξ f.hom) p.hom)) :=
    isEtaleULift_pullback_fst_of_isPullback B S hS hsq hpet
  obtain ⟨Z, β, hβS, hβE⟩ := (Space.isAlgebraicSpaceULift_of_iso B S hS
    (pullbackLeftPullbackSndIso ξ f.hom p.hom).symm (hpf T ξ)).exists_atlas
  have hβrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS β :=
    isRepresentableByAlgebraicSpacesULift_of_relativelyRepresentable B S hS hβE.rep
  have hcrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (β ≫ pullback.fst (pullback.snd ξ f.hom) p.hom) :=
    Space.isRepresentableByAlgebraicSpacesULift_comp B S hS β _ hβrep harep
  have hcet : ∀ (V : BigFppfOver B S hS)
      (η : (uliftYoneda.{u + 1}).obj V ⟶ pullback ξ f.hom),
      Space.IsEtaleULift.{u + 1} B S hS
        (pullback.fst η (β ≫ pullback.fst (pullback.snd ξ f.hom) p.hom)) :=
    isEtaleULift_pullback_fst_comp B S hS harep haet
      (isEtaleULift_pullback_fst_of_relative_etale B S hS hβE)
  exact ⟨Z, β, hβS, hβE, relative_etale_of_schemeSource B S hS Z _ hcrep hcet⟩

/-- **The chart of `…exists_memberChart_pullback` for a surjective `p`.** When `p : U ⟶ X` is in
addition a surjection of sheaves, the composite of the chart with the projection to `T ×_Y X` is
itself a surjection: the projection is a base change of `p`, and the chart is surjective and
étale, hence a surjection of sheaves by Stacks 05VM.

This is the form in which the chart is consumed, by Stacks 0BGR for representability by
algebraic spaces and by Stacks 03MJ for a property étale local on source and target. -/
theorem exists_schemeChart_pullback_of_locallySurjective {X Y U : FppfSheaf B S hS}
    (f : X ⟶ Y) (p : U ⟶ X) (hp : IsRepresentableEtale B S hS p)
    (hsurj : Sheaf.IsLocallySurjective p)
    (hpf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (p ≫ f).hom)
    (T : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj T ⟶ Y.obj) :
    ∃ (Z : BigFppfOver B S hS)
      (β : (uliftYoneda.{u + 1}).obj Z ⟶ pullback (pullback.snd ξ f.hom) p.hom),
      (Space.etaleOnSite B S hS).relative (uliftYoneda.{u + 1}) β ∧
      (Space.surjectiveOnSite B S hS).relative (uliftYoneda.{u + 1})
        (β ≫ pullback.fst (pullback.snd ξ f.hom) p.hom) ∧
      (Space.etaleOnSite B S hS).relative (uliftYoneda.{u + 1})
        (β ≫ pullback.fst (pullback.snd ξ f.hom) p.hom) := by
  obtain ⟨Z, β, hβS, hβE, hce⟩ := exists_memberChart_pullback B S hS f p hp hpf T ξ
  refine ⟨Z, β, hβE, ?_, hce⟩
  have hpls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) p.hom := hsurj
  have hβls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) β :=
    isLocallySurjective_of_relative_surjective_etale B S hS β hβS hβE
  have hals : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (pullback.fst (pullback.snd ξ f.hom) p.hom) :=
    Presheaf.isLocallySurjective_pullback_fst (BigFppfOver.topology B S hS)
      (pullback.snd ξ f.hom) p.hom
  exact relative_surjective_of_locallySurjective B S hS _ hce.rep
    (Presheaf.isLocallySurjective_comp _ _ _)

/-- **Representability by algebraic spaces is local on the source.** Let `f : X ⟶ Y` be a
morphism of fppf sheaves on the big fppf site of `S` and let `p : U ⟶ X` be representable étale
and surjective as a morphism of sheaves. If `p ≫ f` is representable by algebraic spaces then so
is `f`.

Nothing is asked of `X`, `Y` or `U` beyond the sheaf condition. At a scheme-valued point
`ξ : T ⟶ Y` the base change `T ×_Y X` is a sheaf receiving the chart of
`AlgebraicGeometry.FormalSpace.exists_schemeChart_pullback_of_locallySurjective`, a morphism out
of an object of the site which is representable by objects of the site, surjective and étale; so
**Stacks 0BGR** makes `T ×_Y X` an algebraic space over `S`.

This is the étale case of Stacks 0AMP for the hypothesis that `p` be representable by algebraic
spaces rather than by objects of the site: a base change of `p` along a scheme-valued point is
an algebraic space étale over a scheme and need not be a scheme, which is why Stacks 0BGR does
not apply to it directly, but it has a scheme atlas and that atlas is the chart Stacks 0BGR
asks for. -/
theorem isRepresentableByAlgebraicSpacesULift_of_comp_of_locallySurjective
    {X Y U : FppfSheaf B S hS} (f : X ⟶ Y) (p : U ⟶ X) (hp : IsRepresentableEtale B S hS p)
    (hsurj : Sheaf.IsLocallySurjective p)
    (hpf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (p ≫ f).hom) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom := by
  intro T ξ
  obtain ⟨Z, β, -, hcs, hce⟩ :=
    exists_schemeChart_pullback_of_locallySurjective B S hS f p hp hsurj hpf T ξ
  exact Space.isAlgebraicSpaceULift_of_relative_surjective_etale B S hS
    (Presheaf.isSheaf_pullback _ ξ f.hom
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS T).isSheaf X.cond Y.cond)
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS Z) _ hcs hce

/-- **Stacks 0AN4, condition (2) implies condition (1).** In a square as in condition (2) the
upper horizontal map `U ⟶ V` and the target column `V ⟶ Y` are representable by algebraic
spaces, so their composite is, by Stacks 0APY; it equals `U ⟶ X ⟶ Y`, and representability by
algebraic spaces is local on the source along the surjective representable étale map
`U ⟶ X`. -/
theorem isRepresentable_of_isRepresentableOnSomeSquare {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : IsRepresentableOnSomeSquare B S hS f) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom := by
  obtain ⟨U, V, p, q, t, -, -, hp, hpsurj, hq, ht, hcomm⟩ := hf
  have hpf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (p ≫ f).hom := by
    rw [hcomm]
    exact Space.isRepresentableByAlgebraicSpacesULift_comp B S hS t.hom q.hom ht hq
  exact isRepresentableByAlgebraicSpacesULift_of_comp_of_locallySurjective B S hS f p hp
    hpsurj hpf

/-- **Stacks 0AN4, the equivalence of conditions (1), (2) and (3).** For a morphism
`f : X ⟶ Y` of formal algebraic spaces over `S` the following are equivalent: `f` is
representable by algebraic spaces; there is one commutative square as in condition (2); every
commutative square as in condition (3) has its upper horizontal map representable by algebraic
spaces. -/
theorem isRepresentable_tfae_squares {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y) :
    List.TFAE [Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom,
      IsRepresentableOnSomeSquare B S hS f,
      IsRepresentableOnEverySquare B S hS f] := by
  tfae_have 1 → 2 := isRepresentableOnSomeSquare_of_isRepresentable B S hS f hX hY
  tfae_have 2 → 1 := isRepresentable_of_isRepresentableOnSomeSquare B S hS f
  tfae_have 1 → 3 := isRepresentableOnEverySquare_of_isRepresentable' B S hS f
  tfae_have 3 → 1 := isRepresentable_of_isRepresentableOnEverySquare B S hS f hX hY
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
