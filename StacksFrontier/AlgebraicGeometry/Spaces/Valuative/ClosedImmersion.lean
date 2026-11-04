module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.Criterion
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrict

/-!
# A closed immersion of algebraic spaces satisfies the valuative criterion

Let `p : F ⟶ G` be a closed immersion of algebraic spaces over a scheme `S` of a big fppf site,
that is, a representable morphism of presheaves all of whose pullbacks to representables are
closed immersions of schemes (`AlgebraicGeometry.Space.IsClosedImmersion`). This file proves
that every valuative square for `p` has a *unique* dotted arrow: at most one by
`AlgebraicGeometry.Space.valuativeCriterionUniqueness_of_isClosedImmersion`, and at least one by
`AlgebraicGeometry.Space.nonempty_valuativeSquareLift_of_isClosedImmersion` — with no field
extension and no passage to a dominating valuation ring, so the existence statement here is
stronger than `AlgebraicGeometry.Space.ValuativeCriterion.Existence`.

## Main results

* `AlgebraicGeometry.Space.valuativeCriterionUniqueness_of_mono`: a monomorphism of presheaves
  satisfies the uniqueness part of the valuative criterion.
* `AlgebraicGeometry.Space.valuativeCriterionUniqueness_of_isClosedImmersion`: a closed
  immersion of algebraic spaces satisfies the uniqueness part of the valuative criterion.
* `AlgebraicGeometry.Space.nonempty_valuativeSquareLift_of_isClosedImmersion`: every valuative
  square for a closed immersion of algebraic spaces has a dotted arrow.
* `AlgebraicGeometry.Space.valuativeCriterionExistence_of_isClosedImmersion` and
  `AlgebraicGeometry.Space.valuativeCriterion_of_isClosedImmersion`: the existence part, and both
  parts together.
* `AlgebraicGeometry.Space.exists_extension_of_isClosedImmersion_relocalizeToYoneda`: a section of
  a presheaf on the big fppf site of a scheme `U` of the site extends across the spectrum of a
  valuation ring lying over `U`, when the structural morphism of the relocalization of that
  presheaf is a closed immersion over `S`.
* `AlgebraicGeometry.Space.valuativeCriterionExistence_of_isClosedImmersion_relocalizeToYoneda`:
  the same hypothesis gives the existence part for any morphism from that presheaf to the terminal
  presheaf on the site of `U`.

## Implementation notes

The uniqueness half is formal, and uses nothing about `p` beyond that it is a monomorphism: a
dotted arrow of a valuative square is determined by its composite with `p`, which the square
fixes. It is therefore stated for a monomorphism of presheaves, with the closed immersion case a
corollary — a closed immersion of schemes is a monomorphism
(`AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono`) and the property of being a
monomorphism is inherited by the represented morphisms of presheaves
(`CategoryTheory.MorphismProperty.presheaf_monomorphisms_le_monomorphisms`).

The last two results change the site the condition is read on. Stacks 04YL imposes the closed
immersion condition on the structural morphism `Λ_U F' ⟶ h_U` of the lower-shriek extension of a
presheaf `F'` over an object `U` of the site, read over `S`; the valuative criterion for a base
change is a condition on a morphism out of `F'` over the site of `U`. A section of `Λ_U F'` is a
factorization through `U` together with a section of `F'` over it, and the structural morphism
reads off the factorization, so a lift for `Λ_U F' ⟶ h_U` over the spectrum of a valuation ring
whose bottom edge is a prescribed factorization *is* an extension of a section of `F'`. That is
`exists_extension_of_isClosedImmersion_relocalizeToYoneda`, and since the target of the base
change's structural morphism is the terminal presheaf on the site of `U` the bottom triangle of
the resulting lift is automatic.

The existence half is where the geometry enters, and it is a closed immersion of *schemes* that
supplies it. Pulling `p` back along the bottom edge of the square gives a closed immersion
`g : V ⟶ Spec R` of site objects; the generic point and the canonical map factor through the
pullback, producing a morphism `a` over `Spec K`. Now `g` is universally closed, hence satisfies
the existence part of the valuative criterion for schemes
(`AlgebraicGeometry.UniversallyClosed.eq_valuativeCriterion`), so the square `(a, 𝟙)` admits a
lift `l : Spec R ⟶ V` over `Spec R`. Because the big fppf site is a full subcategory of schemes,
`l` comes from a morphism of site objects, and that morphism, followed by the other pullback
projection, is the dotted arrow.

## References

* [Stacks Project, Tag 0CLP](https://stacks.math.columbia.edu/tag/0CLP)
* [Stacks Project, Tag 03IX](https://stacks.math.columbia.edu/tag/03IX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The uniqueness part of the valuative criterion for a monomorphism of presheaves.** A
valuative square prescribes the composite of a dotted arrow with the morphism, so if the morphism
is a monomorphism the dotted arrow is determined. -/
theorem valuativeCriterionUniqueness_of_mono (p : F ⟶ G) (hp : Mono p) :
    ValuativeCriterion.Uniqueness p := by
  refine fun q => ⟨fun a b => ?_⟩
  have hab : a.map = b.map :=
    (cancel_mono p).1 (by rw [a.special_comm, b.special_comm])
  cases a with
  | mk am ag aspec =>
    cases b with
    | mk bm bg bspec =>
      dsimp only at hab
      subst hab
      rfl

/-- **The uniqueness part of the valuative criterion for a closed immersion of algebraic
spaces.** A closed immersion is a monomorphism, so
`AlgebraicGeometry.Space.valuativeCriterionUniqueness_of_mono` applies. -/
theorem valuativeCriterionUniqueness_of_isClosedImmersion (p : F ⟶ G)
    (hp : IsClosedImmersion B S hS p) : ValuativeCriterion.Uniqueness p :=
  valuativeCriterionUniqueness_of_mono B S hS p (mono_of_isClosedImmersion B S hS p hp)

/-- A morphism of the big fppf site of `S` into the spectrum of a valuation ring whose underlying
morphism of schemes is universally closed has a section through every factorization of the
inclusion of the generic point. -/
private theorem exists_section_of_universallyClosed_map {R : Type u} [CommRing R] [IsDomain R]
    [ValuationRing R] {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    (hR : B.Contains (Spec (.of R))) (hK : B.Contains (Spec (.of K))) (b : Spec (.of R) ⟶ S)
    {X : BigFppfOver B S hS} (k : X ⟶ siteObject B S hS hR b)
    [AlgebraicGeometry.UniversallyClosed ((BigFppfOver.toScheme B S hS).map k)]
    (a : siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b) ⟶ X)
    (j : siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b) ⟶
      siteObject B S hS hR b)
    (hj : (BigFppfOver.toScheme B S hS).map j = Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (hak : a ≫ k = j) :
    ∃ l : siteObject B S hS hR b ⟶ X, l ≫ k = 𝟙 _ ∧ j ≫ l = a := by
  have hex : AlgebraicGeometry.ValuativeCriterion.Existence
      ((BigFppfOver.toScheme B S hS).map k) := by
    have huc : AlgebraicGeometry.UniversallyClosed
        ((BigFppfOver.toScheme B S hS).map k) := inferInstance
    rw [AlgebraicGeometry.UniversallyClosed.eq_valuativeCriterion] at huc
    exact huc.1
  have hscheme : (BigFppfOver.toScheme B S hS).map a ≫
      (BigFppfOver.toScheme B S hS).map k =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [← Functor.map_comp, hak, hj]
  obtain ⟨l, hl₁, hl₂⟩ := (hex
    { R := R
      K := K
      i₁ := (BigFppfOver.toScheme B S hS).map a
      i₂ := 𝟙 (Spec (.of R))
      commSq := ⟨by simpa using hscheme⟩ }).exists_lift
  -- the lift is a morphism of schemes between objects of the site, hence one of site objects
  let lSite : (siteObject B S hS hR b).left ⟶ X.left :=
    B.inclusion.preimage (show
      B.inclusion.obj (siteObject B S hS hR b).left ⟶ B.inclusion.obj X.left from l)
  have hlleft : lSite ≫ k.left = 𝟙 _ := by
    refine B.inclusion.map_injective ?_
    rw [B.inclusion.map_comp, B.inclusion.map_preimage, B.inclusion.map_id]
    exact (by simpa using hl₂ : l ≫ (BigFppfOver.toScheme B S hS).map k = 𝟙 _)
  refine ⟨Over.homMk lSite (by rw [← k.w, ← Category.assoc, hlleft]; simp),
    Over.OverMorphism.ext hlleft, ?_⟩
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  rw [Functor.map_comp, hj]
  refine Eq.trans (show Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ B.inclusion.map lSite =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ l by
    rw [B.inclusion.map_preimage]) ?_
  exact (by simpa using hl₁ :
    Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ l = (BigFppfOver.toScheme B S hS).map a)

/-- **The existence part of the valuative criterion for a closed immersion of algebraic
spaces**, in its strong form: a valuative square for a closed immersion has a dotted arrow
already over the given valuation ring, with no field extension and no dominating valuation
ring.

The dotted arrow is produced from the valuative criterion for the closed immersion of schemes
obtained by pulling `p` back along the bottom edge of the square, which is universally closed. -/
theorem nonempty_valuativeSquareLift_of_isClosedImmersion (p : F ⟶ G)
    (hp : IsClosedImmersion B S hS p) (q : ValuativeSquare p) : Nonempty q.Lift := by
  -- the canonical map of site objects between the two spectra
  let j : siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) ⟶
      siteObject B S hS q.ring_mem q.base :=
    Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K))) :
      B.obj q.field_mem ⟶ B.obj q.ring_mem)
  -- the pullback of `p` along the bottom edge, with its two projections
  let H := hp.1
  let i := H.fst q.special
  let k := H.snd q.special
  have hPB := H.isPullback q.special
  -- the generic point and the canonical map factor through the pullback
  let a := Yoneda.fullyFaithful.preimage (hPB.lift q.generic (yoneda.map j) q.comm)
  have ha : yoneda.map a = hPB.lift q.generic (yoneda.map j) q.comm :=
    Yoneda.fullyFaithful.map_preimage _
  have hcomp : a ≫ k = j :=
    Functor.map_injective yoneda (by rw [Functor.map_comp, ha, hPB.lift_snd])
  -- the pullback projection is a closed immersion of schemes, hence universally closed
  have : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map k) :=
    hp.2 q.special i k hPB
  obtain ⟨lOver, hlk, hjl⟩ := exists_section_of_universallyClosed_map B S hS q.ring_mem
    q.field_mem q.base k a j rfl hcomp
  refine ⟨{ map := yoneda.map lOver ≫ i, generic_comm := ?_, special_comm := ?_ }⟩
  · rw [← Category.assoc, ← Functor.map_comp, hjl, ha, hPB.lift_fst]
  · rw [Category.assoc, hPB.w, ← Category.assoc, ← Functor.map_comp, hlk,
      CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The existence part of the valuative criterion for a closed immersion of algebraic
spaces.** Every valuative square already has a lift, so the identity dominating extension
suffices. -/
theorem valuativeCriterionExistence_of_isClosedImmersion (p : F ⟶ G)
    (hp : IsClosedImmersion B S hS p) : ValuativeCriterion.Existence p :=
  valuativeCriterionExistence_of_forall_nonempty_lift p
    (nonempty_valuativeSquareLift_of_isClosedImmersion B S hS p hp)

/-- **A closed immersion of algebraic spaces satisfies the valuative criterion.** Both parts, by
`AlgebraicGeometry.Space.valuativeCriterionExistence_of_isClosedImmersion` and
`AlgebraicGeometry.Space.valuativeCriterionUniqueness_of_isClosedImmersion`. -/
theorem valuativeCriterion_of_isClosedImmersion (p : F ⟶ G)
    (hp : IsClosedImmersion B S hS p) : ValuativeCriterion p :=
  ⟨valuativeCriterionExistence_of_isClosedImmersion B S hS p hp,
    valuativeCriterionUniqueness_of_isClosedImmersion B S hS p hp⟩

/-! ### Sections of a presheaf over a scheme of the site, read over the base -/

section Relocalize

variable (U : BigFppfOver B S hS) (F' : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)

/-- The factorization through `U` carried by a scheme of the big fppf site lying over `U`, read as
a morphism of the big fppf site of `S`. -/
noncomputable abbrev overFactorization {T : Scheme.{u}} (hT : B.Contains T)
    (c : T ⟶ U.left.1) : B.obj hT ⟶ B.obj U.left.2 :=
  ObjectProperty.homMk c

/-- The inclusion of the generic point of the spectrum of a valuation ring, as a morphism of the
big fppf site of a scheme `U` of the big fppf site of `S`. -/
noncomputable abbrev genericInclusion {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    (hR : B.Contains (Spec (.of R))) (hK : B.Contains (Spec (.of K)))
    (b : Spec (.of R) ⟶ U.left.1) :
    siteObject B U.left.1 U.left.2 hK
        (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b) ⟶
      siteObject B U.left.1 U.left.2 hR b :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    B.obj hK ⟶ B.obj hR)

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
  {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  (hR : B.Contains (Spec (.of R))) (hK : B.Contains (Spec (.of K)))
  (b : Spec (.of R) ⟶ U.left.1)

/-- The valuative square over `S` for the structural morphism of the relocalization of `F'`
attached to a section of `F'` over the generic point of the spectrum of a valuation ring lying
over `U`: its generic point is that section, carrying the factorization through `U` it is defined
over, and its bottom edge is the factorization of the spectrum of the valuation ring. -/
private noncomputable def relocalizeSquare
    (s : F'.obj (Opposite.op (siteObject B U.left.1 U.left.2 hK
      (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b))))
    (hgen : overFactorization B S hS U hK
          (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b) ≫ U.hom =
        (siteObject B S hS hK
          (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b ≫ U.hom.hom)).hom)
    (hspec : overFactorization B S hS U hR b ≫ U.hom =
      (siteObject B S hS hR (b ≫ U.hom.hom)).hom) :
    ValuativeSquare (OverShriek.relocalizeToYoneda U.hom F') where
  R := R
  K := K
  ring_mem := hR
  field_mem := hK
  base := b ≫ U.hom.hom
  generic := yonedaEquiv.symm (OverShriek.relocalizeMk U.hom F'
    (overFactorization B S hS U hK (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b)) s hgen)
  special := yoneda.map (Over.homMk (overFactorization B S hS U hR b) hspec :
    siteObject B S hS hR (b ≫ U.hom.hom) ⟶ Over.mk U.hom)
  comm := by
    refine yonedaEquiv.injective ?_
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply, ← yoneda.map_comp, yonedaEquiv_yoneda_map]
    exact Over.OverMorphism.ext (ObjectProperty.hom_ext _ rfl)

/-- Restricting the relocalization of a section of `F'` over the spectrum of a valuation ring
along the inclusion of the generic point is the relocalization of its restriction. -/
private theorem relocalizeMk_map_genericInclusion
    (t : F'.obj (Opposite.op (siteObject B U.left.1 U.left.2 hR b)))
    (h₀ : overFactorization B S hS U hR b ≫ U.hom = (siteObject B S hS hR (b ≫ U.hom.hom)).hom)
    (hgen : overFactorization B S hS U hK
          (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b) ≫ U.hom =
        (siteObject B S hS hK
          (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b ≫ U.hom.hom)).hom) :
    ((OverShriek.relocalizePresheafFunctor U.hom).obj F').map
        (Opposite.op (Over.homMk (ObjectProperty.homMk
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) : B.obj hK ⟶ B.obj hR) :
          siteObject B S hS hK
              (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b ≫ U.hom.hom) ⟶
            siteObject B S hS hR (b ≫ U.hom.hom)))
        (OverShriek.relocalizeMk U.hom F' (overFactorization B S hS U hR b) t h₀) =
      OverShriek.relocalizeMk U.hom F'
        (overFactorization B S hS U hK
          (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b))
        (F'.map (genericInclusion B S hS U hR hK b).op t) hgen :=
  Subtype.ext (OverShriek.sigmaMk_eq F' t
    (Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) : B.obj hK ⟶ B.obj hR) rfl)
    (genericInclusion B S hS U hR hK b) rfl)

/-- **Sections extend across the spectrum of a valuation ring when the relocalization is a closed
immersion.** Let `F'` be a presheaf on the big fppf site of a scheme `U` of the big fppf site of
`S`, and suppose the structural morphism `Λ_U F' ⟶ h_U` of its relocalization is a closed
immersion of algebraic spaces over `S`. Then a section of `F'` over the generic point of the
spectrum of a valuation ring `R` lying over `U` extends to a section over the whole spectrum.

The extension comes from the strong existence half of the valuative criterion for the closed
immersion `Λ_U F' ⟶ h_U`, applied to the valuative square over `S` whose generic point is the
given section read as a section of `Λ_U F'` — the factorization through `U` being the structure
morphism of the generic point — and whose bottom edge is the factorization of the spectrum of `R`
through `U`. The lift is a section of `Λ_U F'` over the spectrum of `R`, and its bottom triangle
prescribes its factorization to be that very morphism, so the section of `F'` it carries lives
over the spectrum of `R` read over `U`; the top triangle is the extension property. -/
theorem exists_extension_of_isClosedImmersion_relocalizeToYoneda
    (hci : IsClosedImmersion B S hS (OverShriek.relocalizeToYoneda U.hom F'))
    (s : F'.obj (Opposite.op (siteObject B U.left.1 U.left.2 hK
      (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b)))) :
    ∃ t : F'.obj (Opposite.op (siteObject B U.left.1 U.left.2 hR b)),
      F'.map (genericInclusion B S hS U hR hK b).op t = s := by
  have hgen : overFactorization B S hS U hK
        (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b) ≫ U.hom =
      (siteObject B S hS hK
        (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b ≫ U.hom.hom)).hom :=
    ObjectProperty.hom_ext _ (Category.assoc _ _ _)
  have hspec : overFactorization B S hS U hR b ≫ U.hom =
      (siteObject B S hS hR (b ≫ U.hom.hom)).hom :=
    ObjectProperty.hom_ext _ rfl
  obtain ⟨L⟩ := nonempty_valuativeSquareLift_of_isClosedImmersion B S hS
    (OverShriek.relocalizeToYoneda U.hom F') hci
    (relocalizeSquare B S hS U F' hR hK b s hgen hspec)
  -- read off the factorization through `U` and the section of `F'` that the lift carries
  obtain ⟨ψ₀, t₀, h₀, hL⟩ :
      ∃ (ψ₀ : (siteObject B S hS hR (b ≫ U.hom.hom)).left ⟶ B.obj U.left.2)
        (t₀ : F'.obj (Opposite.op (Over.mk ψ₀)))
        (h₀ : ψ₀ ≫ U.hom = (siteObject B S hS hR (b ≫ U.hom.hom)).hom),
        yonedaEquiv L.map = OverShriek.relocalizeMk U.hom F' ψ₀ t₀ h₀ :=
    ⟨(yonedaEquiv L.map).1.1, (yonedaEquiv L.map).1.2, (yonedaEquiv L.map).2, rfl⟩
  -- the bottom triangle prescribes that factorization to be the one of the spectrum of `R`
  have hfac : ψ₀ = overFactorization B S hS U hR b := by
    have hsp := (yonedaEquiv_comp L.map (OverShriek.relocalizeToYoneda U.hom F')).symm.trans
      (congrArg yonedaEquiv L.special_comm)
    rw [hL] at hsp
    have hspecial : yonedaEquiv (relocalizeSquare B S hS U F' hR hK b s hgen hspec).special =
        (Over.homMk (overFactorization B S hS U hR b) hspec :
          siteObject B S hS hR (b ≫ U.hom.hom) ⟶ Over.mk U.hom) :=
      yonedaEquiv_yoneda_map _
    rw [hspecial] at hsp
    exact congrArg Over.Hom.left hsp
  subst hfac
  refine ⟨t₀, ?_⟩
  -- the top triangle is the extension property
  have h := (yonedaEquiv_naturality L.map _).trans (congrArg yonedaEquiv L.generic_comm)
  rw [hL] at h
  have hgeneric : yonedaEquiv (relocalizeSquare B S hS U F' hR hK b s hgen hspec).generic =
      OverShriek.relocalizeMk U.hom F'
        (overFactorization B S hS U hK
          (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b)) s hgen :=
    Equiv.apply_symm_apply yonedaEquiv _
  rw [hgeneric] at h
  exact eq_of_heq
    ((Sigma.mk.injEq _ _ _ _).mp (congrArg Subtype.val
      ((relocalizeMk_map_genericInclusion B S hS U F' hR hK b t₀ h₀ hgen).symm.trans h))).2

/-- **The existence part of the valuative criterion for a presheaf whose relocalization has closed
immersion structural morphism.** The target is the terminal presheaf on the big fppf site of `U`,
so the bottom triangle of a lift is automatic and a lift is exactly an extension of the generic
point, which
`AlgebraicGeometry.Space.exists_extension_of_isClosedImmersion_relocalizeToYoneda` supplies; the
dominating extension is then the identity one.

This is the shape in which the condition of Stacks 0CLN is verified for a closed immersion of
algebraic stacks: there the morphism tested is an arbitrary morphism from the presheaf
representing a base change to the terminal presheaf, while the closed immersion hypothesis of
Stacks 04YL is imposed on the structural morphism of the relocalization. -/
theorem valuativeCriterionExistence_of_isClosedImmersion_relocalizeToYoneda
    (hci : IsClosedImmersion B S hS (OverShriek.relocalizeToYoneda U.hom F'))
    (p : F' ⟶ yoneda.obj (Over.mk (𝟙 (B.obj U.left.2)))) :
    ValuativeCriterion.Existence p := by
  refine valuativeCriterionExistence_of_forall_nonempty_lift p fun q => ?_
  obtain ⟨t, ht⟩ := exists_extension_of_isClosedImmersion_relocalizeToYoneda B S hS U F'
    q.ring_mem q.field_mem q.base hci (yonedaEquiv q.generic)
  refine ⟨{ map := yonedaEquiv.symm t, generic_comm := ?_, special_comm := ?_ }⟩
  · exact yonedaEquiv.injective (by rwa [← yonedaEquiv_naturality, Equiv.apply_symm_apply])
  · exact yonedaEquiv.injective (Over.mkIdTerminal.hom_ext _ _)

end Relocalize

end AlgebraicGeometry.Space

end
