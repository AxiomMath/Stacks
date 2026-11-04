module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.EventualFiniteness.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLimitExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineStageSiteSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.CategoryTheory.Representable.RepresentedDiagram

/-!
# Eventual finiteness over the base in a directed limit of algebraic spaces

Stacks 0A0S reads, verbatim:

> Let `S` be a scheme. Let `Y` be an algebraic space over `S`. Let `X = lim X_i` be a directed
> limit of algebraic spaces over `Y` with affine transition morphisms. Assume (1) `Y`
> quasi-compact and quasi-separated, (2) `X_i` quasi-compact and quasi-separated, (3) the
> transition morphisms `X_{i'} → X_i` are finite, (4) `X_i → Y` locally of finite type, (5)
> `X → Y` integral. Then `X_i → Y` is finite for `i` large enough.

The source's proof chooses an affine scheme `W` with a surjective étale morphism `W → Y`,
observes that `X ×_Y W` is finite over `W` and that it therefore suffices to make
`X_i ×_Y W → W` finite for one `i` (Stacks 03ZQ), reduces to the case of schemes by Stacks 07SR
and concludes by Stacks 09ZN.

## Main results

* `AlgebraicGeometry.Space.eventually_isFinite_of_isLimit_of_isIntegral` — **Stacks 0A0S**,
  unconditionally. Its one appeal to a stage of the base-changed system being affine is Stacks
  07SQ, discharged by
  `AlgebraicGeometry.Space.DescentSituation.exists_isAffineSpace_system_obj_of_isSiteSmall`; see
  "The appeal to Stacks 07SQ" below.

## Implementation notes

*07SR is not needed; 07SQ is.* The source reduces to schemes by Stacks 07SR, which makes a
stage a scheme once the limit is one. That is more than this argument needs and less than it can
use. Because `X → Y` is integral and `W` is affine, the base change `X ×_Y W` is not merely a
scheme but an *affine* scheme — this is immediate from the definition of an integral morphism of
algebraic spaces, which produces an affine representing object over every affine test object.
So Stacks 07SQ applies to the base-changed system directly, and it gives more than 07SR would:
affineness of the stage `X_{i_0} ×_Y W`, hence — transition morphisms being affine — affineness
of *every* later stage, and with it `CompactSpace` and `QuasiSeparatedSpace` at every later
stage for free. Routing through 07SR instead would leave those two to be recovered from
quasi-compactness and quasi-separatedness of the stages as algebraic spaces.

*From the site to schemes.* Once every stage beyond `i_0` is affine, the system of representing
objects is a cofiltered system of affine objects of the site, and
`AlgebraicGeometry.BigFppfOver.preservesLimit_toScheme_of_isSiteSmallDiagram` carries its limit to
a limit of schemes. No part of Stacks 07SI — the identification `Γ(X, ℱ) = colim_i Γ(X_i, ℱ_i)`,
which is stated but unproved in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/SectionsColimitDescent.lean` — is consumed anywhere
below.

*The index set.* `I` is taken in the universe of the site and subject to
`#I < B.cutoff.ord.cof`. Both are forced rather than chosen. The size bound is the hypothesis of
Stacks 07SF, and is what keeps the limit of the affine stages inside the site; it is the same
bound that `AlgebraicGeometry.Space.LimitSituation.isAffineHom_π` and
`AlgebraicGeometry.Space.DescentSituation.isAffineHom_limitCone_π_of_isSiteSmall` carry. The
universe restriction is forced by Stacks 09ZN, whose formalization
`AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral` is stated for `I : Type u`; at
free index universe the corresponding scheme-level sections statement is false, refuted by
`Stacks.LimitSectionsIdentification.not_card_01Z0`.

*The limiting cone is given, not constructed.* As in the formalization of Stacks 09ZN the system
is unbundled — a functor out of `Iᵒᵖ`, a cone, and `IsLimit` — rather than carried by
`AlgebraicGeometry.Space.DescentSituation`, because the structure morphisms to `Y` are part of
the data of this tag and the structure does not carry them. The structure is built internally,
for the base-changed system, so that Stacks 07SQ can be applied to it.

### The appeal to Stacks 07SQ

The argument needs Stacks 07SQ exactly once, for the base-changed system: for a situation of
Stacks 084R whose limit is an affine algebraic space, some stage beyond the distinguished index
is an affine algebraic space. That is
`AlgebraicGeometry.Space.DescentSituation.exists_isAffineSpace_system_obj_of_isSiteSmall`, applied
below to the descent situation `EDescent` built from the system of base changes along the affine
étale chart `W → Y`. It carries the Stacks 07SF size hypothesis, and the bound `hI` this theorem
already needs for its own passage from the site to schemes is exactly the one that form wants, so
the appeal costs no extra hypothesis. Nothing else about 07SQ is used anywhere below.

This theorem therefore takes no hypothesis standing in for a tag; in particular there is no
`h07SQ`-shaped binder of the kind the two theorems
`AlgebraicGeometry.Space.MinimalNonSchematicSpace` and
`AlgebraicGeometry.Space.PurelyInseparableBaseChangeScheme` carry.

*A redundancy kept for fidelity.* `haffine` — the transition morphisms are affine — follows
from `hfinite` by `AlgebraicGeometry.Space.IsFinite.isAffineHom`, so it could be dropped. It is
kept because the source states it (`X = lim X_i` is introduced as a limit "with affine
transition morphisms", separately from assumption (3)), and because the formalization of
Stacks 09ZN this reduces to carries the same pair.

## References

* [Stacks Project, Tag 0A0S](https://stacks.math.columbia.edu/tag/0A0S)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 09ZN](https://stacks.math.columbia.edu/tag/09ZN)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Generalities reused below -/

section Generalities

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An object of the site representing an affine algebraic space has affine underlying scheme:
the representing object of the definition and this one are isomorphic in the site, the Yoneda
embedding being fully faithful. -/
private theorem isAffine_of_isAffineSpace_yoneda (V : BigFppfOver B S hS)
    (h : IsAffineSpace B S hS (yoneda.obj V)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj V) := by
  obtain ⟨T₀, hT₀, ⟨e⟩⟩ := h
  have : IsIso (yoneda.map (yoneda.preimage e.hom)) := by
    rw [yoneda.map_preimage]
    infer_instance
  have : IsIso (yoneda.preimage e.hom) := Yoneda.fullyFaithful.isIso_of_isIso_map _
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀) := hT₀
  exact isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map (yoneda.preimage e.hom))

/-- Along an isomorphism of arrows `yoneda.map f ≅ g`, a stable property holds for the presheaf
morphism `g` exactly when it holds for `f`. -/
private theorem presheaf_iff_of_arrow_iso (P : MorphismProperty (BigFppfOver B S hS))
    [P.IsStableUnderBaseChange] {V W : BigFppfOver B S hS}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : V ⟶ W) (g : X ⟶ Y)
    (e : Arrow.mk (yoneda.map f) ≅ Arrow.mk g) : P.presheaf g ↔ P f :=
  ((MorphismProperty.arrow_iso_iff P.presheaf e).symm).trans MorphismProperty.relative_map_iff

/-- A morphism `g` out of a representable presheaf, precomposed with a representing isomorphism,
is isomorphic as an arrow to the Yoneda image of the corresponding morphism of the site. -/
private noncomputable def arrowIsoYonedaPreimage {V W : BigFppfOver B S hS}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : yoneda.obj V ≅ X) (g : X ⟶ yoneda.obj W) :
    Arrow.mk (yoneda.map (yoneda.preimage (e.hom ≫ g))) ≅ Arrow.mk g :=
  Arrow.isoMk e (Iso.refl _) (by simp)

end Generalities

/-! ### Stacks 0A0S -/

section Main

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 0A0S.** Let `X = lim X_i` be a directed limit of algebraic spaces over an algebraic
space `Y`, with affine transition morphisms. If `Y` is quasi-compact and quasi-separated, every
`X_i` is quasi-compact and quasi-separated, the transition morphisms are finite, every
`X_i → Y` is locally of finite type and `X → Y` is integral, then `X_i → Y` is finite for all
sufficiently large `i`.

The limit `X` is an algebraic space by Stacks 07SF
(`AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_isSiteSmall`), so that is not assumed.
Every input of the source's proof is discharged: the affine étale chart of `Y` by Stacks 03H6,
the affine stage of the base-changed system by Stacks 07SQ, the finiteness of the base-changed
stages descending to finiteness over `Y` by Stacks 03ZQ, and the scheme case by Stacks 09ZN. The
index set is asked to be small compared to the cofinality of the site's size cutoff, the Stacks
07SF bound that both Stacks 07SQ and the passage from the site to schemes carry here. -/
@[stacks 0A0S]
theorem eventually_isFinite_of_isLimit_of_isIntegral
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (hI : #I < B.cutoff.ord.cof)
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (D : Iᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (p : D ⟶ (Functor.const Iᵒᵖ).obj Y)
    (c : Cone D) (hc : IsLimit c) (f : c.pt ⟶ Y)
    (hf : ∀ i : I, f = c.π.app (op i) ≫ p.app (op i))
    (hY : IsAlgebraicSpace B S hS Y)
    (hD : ∀ i : I, IsAlgebraicSpace B S hS (D.obj (op i)))
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (hDqc : ∀ i : I, IsQuasiCompactSpace B S hS (D.obj (op i)))
    (hDqs : ∀ i : I, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj (op i)))
    (haffine : ∀ {i j : I} (h : i ≤ j), IsAffineHom B S hS (D.map (homOfLE h).op))
    (hfinite : ∀ {i j : I} (h : i ≤ j), IsFinite B S hS (D.map (homOfLE h).op))
    (hfiniteType : ∀ i : I, IsLocallyOfFiniteType B S hS (p.app (op i)))
    (hintegral : IsIntegralHom B S hS f) :
    ∀ᶠ i : I in Filter.atTop, IsFinite B S hS (p.app (op i)) := by
  classical
  -- Stacks 07SF: the limit is an algebraic space.
  have hX : IsAlgebraicSpace B S hS c.pt :=
    (Space.isAlgebraicSpace_limit_of_isSiteSmall B S hS D (.of_lt_cof_op hI)
      (fun a => hD a.unop) (fun {a b} g => by
        have h := haffine (leOfHom g.unop)
        rwa [show (homOfLE (leOfHom g.unop)).op = g from Subsingleton.elim _ _] at h)).of_iso
      (hc.conePointUniqueUpToIso (limit.isLimit D)).symm
  let T := BigFppfOver.toScheme B S hS
  -- Stacks 03H6: an affine surjective étale chart of the quasi-compact algebraic space `Y`.
  obtain ⟨U, chart, hU, hchartSurjective, hchartEtale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Y hY).mp hYqc
  let QEtale := MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T
  have hpEtaleChart : QEtale.presheaf chart := presheaf_etale_of_isEtale B S hS hchartEtale
  have hUaff : IsAffine (T.obj U) := hU
  -- The system of base changes along the chart, with its limiting cone.
  have hcomm : c.π ≫ p = (Functor.const Iᵒᵖ).map f := by
    ext i A x
    exact congrArg (fun q => q.app A x) ((hf i.unop).symm)
  let DOver := Over.lift D p
  let cOver := Over.liftCone D p c f fun i => by simpa using congrArg (fun α => α.app i) hcomm
  have hcOver : IsLimit cOver :=
    Over.isLimitLiftCone D p c f (fun i => by simpa using congrArg (fun α => α.app i) hcomm) hc
  let pulled := Over.pullback chart
  let pulledCone := pulled.mapCone cOver
  have hpulledCone : IsLimit pulledCone := isLimitOfPreserves pulled hcOver
  let E := DOver ⋙ pulled ⋙ Over.forget (yoneda.obj U)
  let eCone := (Over.forget (yoneda.obj U)).mapCone pulledCone
  have heCone : IsLimit eCone := isLimitOfPreserves _ hpulledCone
  -- `X ×_Y W` is affine, directly from integrality of `X → Y` over the affine `W`.
  have hXUaff : IsAffineSpace B S hS eCone.pt := by
    obtain ⟨V, q, qX, hpull, hVaff, -⟩ := hintegral U hU chart
    exact ⟨V, hVaff, ⟨hpull.isoPullback.symm⟩⟩
  have hUalg : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hUqc : IsQuasiCompactSpace B S hS (yoneda.obj U) :=
    isQuasiCompact_yoneda_of_compact B S hS U inferInstance
  have hUqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj U) :=
    isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS hZ _
      (isAbsolutelySeparated_of_isAffineSpace B S hS hZ (isAffineSpace_yoneda B S hS U hU))
  -- The base-changed system is a system of quasi-compact and quasi-separated algebraic spaces.
  have hEalg (i : I) : IsAlgebraicSpace B S hS (E.obj (op i)) := by
    show IsAlgebraicSpace B S hS (pullback (p.app (op i)) chart)
    exact isAlgebraicSpace_pullback B S hS (p.app (op i)) chart (hD i) hUalg hY
  have hEqc (i : I) : IsQuasiCompactSpace B S hS (E.obj (op i)) := by
    show IsQuasiCompactSpace B S hS (pullback (p.app (op i)) chart)
    exact isQuasiCompactSpace_pullback B S hS hZ (p.app (op i)) chart (hD i) hY
      (hDqc i) hUqc hYqs
  have hEqs (i : I) : IsAbsolutelyQuasiSeparated B S hS hZ (E.obj (op i)) := by
    show IsAbsolutelyQuasiSeparated B S hS hZ (pullback (p.app (op i)) chart)
    exact isAbsolutelyQuasiSeparated_pullback B S hS hZ (p.app (op i)) chart (hD i) hUalg hY
      (hDqs i) hUqs
  -- Each transition morphism of the base-changed system is a base change of one of `D`.
  have hEtransitionPB {i j : Iᵒᵖ} (g : i ⟶ j) :
      IsPullback (pullback.fst (p.app i) chart) (E.map g)
        (D.map (homOfLE (leOfHom g.unop)).op) (pullback.fst (p.app j) chart) := by
    apply IsPullback.flip
    refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback _ _).flip
    · show IsPullback (pullback.lift _ _ _ ≫ pullback.snd _ _) (pullback.fst _ _) chart
        ((DOver.map g).left ≫ (DOver.obj j).hom)
      rw [pullback.lift_snd, (DOver.map g).w]
      exact (IsPullback.of_hasPullback (DOver.obj i).hom chart).flip
    · show pullback.lift _ _ _ ≫ pullback.fst _ _ = _
      exact pullback.lift_fst _ _ _
  have hEaff {i j : Iᵒᵖ} (g : i ⟶ j) : IsAffineHom B S hS (E.map g) :=
    isAffineHom_of_isPullback (hEtransitionPB g) (haffine (leOfHom g.unop))
  have hEfinite {i j : I} (hij : i ≤ j) : IsFinite B S hS (E.map (homOfLE hij).op) :=
    isFinite_of_isPullback B S hS (hEtransitionPB (homOfLE hij).op) (hfinite hij)
  -- Stacks 084R for the base-changed system, and Stacks 07SQ applied to it.
  let EDescent : DescentSituation B S hS hZ I :=
    { system := E
      algebraicSpace := hEalg
      transition_affine := hEaff
      quasiCompact := hEqc
      quasiSeparated := hEqs
      limitCone := eCone
      isLimit := heCone
      limitAlgebraicSpace := hXUaff.isAlgebraicSpace
      base := Classical.arbitrary I }
  obtain ⟨i₀, -, hi₀aff⟩ :=
    EDescent.exists_isAffineSpace_system_obj_of_isSiteSmall (.of_lt_cof_op hI) hXUaff
  -- Beyond `i₀` every stage is affine, the transition morphisms being affine.
  let Tail := {i : I // i₀ ≤ i}
  have : Nonempty Tail := ⟨⟨i₀, le_rfl⟩⟩
  have : IsDirected Tail (· ≤ ·) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨k, hak, hbk⟩ := IsDirected.directed (r := (· ≤ ·)) a.1 b.1
    exact ⟨⟨k, a.2.trans hak⟩, hak, hbk⟩
  let tailInclusion : Tail ⥤ I :=
    { obj i := i.1
      map g := homOfLE (leOfHom g)
      map_id := fun i => Subsingleton.elim _ _
      map_comp := fun g h => Subsingleton.elim _ _ }
  let tailOp := tailInclusion.op
  have htailInitial : Functor.Initial tailOp := by
    apply Functor.initial_of_exists_of_isCofiltered
    · intro d
      obtain ⟨k, hik, hdk⟩ := IsDirected.directed (r := (· ≤ ·)) i₀ d.unop
      exact ⟨op ⟨k, hik⟩, ⟨(homOfLE hdk).op⟩⟩
    · intro d a s s'
      exact ⟨a, 𝟙 a, by have : s = s' := Subsingleton.elim _ _; simp [this]⟩
  let ETail := tailOp ⋙ E
  let eConeTail := eCone.whisker tailOp
  have heConeTail : IsLimit eConeTail :=
    (Functor.Initial.isLimitWhiskerEquiv tailOp eCone).symm heCone
  have hETailAff (j : Tailᵒᵖ) : IsAffineSpace B S hS (ETail.obj j) := by
    show IsAffineSpace B S hS (E.obj (op j.unop.1))
    exact IsAffineHom.isAffineSpace_source (hEaff (homOfLE j.unop.2).op) hi₀aff
  have hETailRep (j : Tailᵒᵖ) : (ETail.obj j).IsRepresentable := by
    obtain ⟨V, -, ⟨e⟩⟩ := hETailAff j
    exact Functor.IsRepresentable.mk' e.symm
  -- The system of representing objects of the stages beyond `i₀`, all affine.
  let VTail := representedDiagram (C := BigFppfOver B S hS) ETail hETailRep
  let repETail := representedDiagramIso (C := BigFppfOver B S hS) ETail hETailRep
  have hVTailAff (j : Tailᵒᵖ) : IsAffine (T.obj (VTail.obj j)) :=
    isAffine_of_isAffineSpace_yoneda B S hS _ ((hETailAff j).of_iso (repETail.app j).symm)
  have hrepNat {j k : Tailᵒᵖ} (g : j ⟶ k) :
      yoneda.map (VTail.map g) ≫ (repETail.app k).hom =
        (repETail.app j).hom ≫ ETail.map g := by
    simpa [VTail] using repETail.hom.naturality g
  have hrepInv {j k : Tailᵒᵖ} (g : j ⟶ k) :
      (repETail.app j).inv ≫ yoneda.map (VTail.map g) =
        ETail.map g ≫ (repETail.app k).inv := by
    apply (cancel_mono (repETail.app k).hom).1
    rw [Category.assoc, hrepNat g, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact Iso.inv_hom_id_assoc _ _
  -- Transport the limiting cone to the system of representing objects.
  have hlimRep : eConeTail.pt.IsRepresentable := by
    obtain ⟨V, -, ⟨e⟩⟩ := hXUaff
    exact Functor.IsRepresentable.mk' e.symm
  have := hlimRep
  let limObj := eConeTail.pt.reprX
  let limRepr := eConeTail.pt.reprW
  let limLeg (j : Tailᵒᵖ) : limObj ⟶ VTail.obj j :=
    yoneda.preimage (limRepr.hom ≫ eConeTail.π.app j ≫ (repETail.app j).inv)
  let cVTail : Cone VTail :=
    { pt := limObj
      π :=
        { app := limLeg
          naturality := by
            intro j k g
            apply yoneda.map_injective
            dsimp [limLeg]
            simp only [Category.id_comp, Functor.map_comp, yoneda.map_preimage]
            have hpi : eConeTail.π.app j ≫ ETail.map g = eConeTail.π.app k := eConeTail.w g
            calc limRepr.hom ≫ eConeTail.π.app k ≫ (repETail.app k).inv
                _ = limRepr.hom ≫ (eConeTail.π.app j ≫ ETail.map g) ≫
                      (repETail.app k).inv :=
                    congrArg (fun q => limRepr.hom ≫ q ≫ (repETail.app k).inv) hpi.symm
                _ = limRepr.hom ≫ eConeTail.π.app j ≫ ETail.map g ≫
                      (repETail.app k).inv := by rw [Category.assoc]
                _ = limRepr.hom ≫ eConeTail.π.app j ≫ (repETail.app j).inv ≫
                      yoneda.map (VTail.map g) := by rw [hrepInv g] } }
  have hConeIso : (Cone.postcompose repETail.hom).obj (yoneda.mapCone cVTail) ≅ eConeTail :=
    Cone.ext limRepr (by
      intro j
      show yoneda.map (limLeg j) ≫ (repETail.app j).hom = limRepr.hom ≫ eConeTail.π.app j
      dsimp [limLeg]
      rw [yoneda.map_preimage]
      simp only [Category.assoc, repETail.inv_hom_id_app]
      show (limRepr.hom ≫ eConeTail.π.app j) ≫ 𝟙 _ = limRepr.hom ≫ eConeTail.π.app j
      exact Category.comp_id _)
  have hcVTailYon : IsLimit (yoneda.mapCone cVTail) :=
    (IsLimit.equivOfNatIsoOfIso repETail _ eConeTail hConeIso).symm heConeTail
  have hcVTail : IsLimit cVTail := isLimitOfReflects yoneda hcVTailYon
  -- The limit of the representing objects is a limit of schemes: Stacks 07SF's size bound makes
  -- `BigFppfOver.toScheme` preserve it.
  have hTailSize : #Tailᵒᵖ < B.cutoff.ord.cof :=
    ((mk_congr (Opposite.equivToOpposite (α := Tail)).symm).trans_le (mk_subtype_le _)).trans_lt hI
  have hpres := BigFppfOver.preservesLimit_toScheme_of_isSiteSmallDiagram VTail hVTailAff
      (.of_lt_cof hTailSize)
  let schemeTail := VTail ⋙ T
  let coneTail := T.mapCone cVTail
  have hcSchemeTail : IsLimit coneTail := isLimitOfPreserves T hcVTail
  -- The structure morphisms of the system of representing objects, down to `W`.
  let O := tailOp ⋙ (DOver ⋙ pulled)
  let stageToU (j : Tailᵒᵖ) : VTail.obj j ⟶ U :=
    yoneda.preimage ((repETail.app j).hom ≫ (O.obj j).hom)
  have hstageToU_O (j : Tailᵒᵖ) :
      yoneda.map (stageToU j) = (repETail.app j).hom ≫ (O.obj j).hom :=
    yoneda.map_preimage _
  have hstageToU_natural {j k : Tailᵒᵖ} (g : j ⟶ k) :
      VTail.map g ≫ stageToU k = stageToU j := by
    apply yoneda.map_injective
    rw [Functor.map_comp, hstageToU_O, hstageToU_O, ← Category.assoc, hrepNat g,
      Category.assoc]
    exact congrArg (fun q => (repETail.app j).hom ≫ q) (O.map g).w
  let mapTail : schemeTail ⟶ (Functor.const Tailᵒᵖ).obj (T.obj U) :=
    { app := fun j => T.map (stageToU j)
      naturality := by
        intro j k g
        show T.map (VTail.map g) ≫ T.map (stageToU k) = T.map (stageToU j)
        rw [← Functor.map_comp, hstageToU_natural g] }
  let limitToU : limObj ⟶ U := yoneda.preimage (limRepr.hom ≫ pulledCone.pt.hom)
  have hconeTail_comm :
      coneTail.π ≫ mapTail = (Functor.const Tailᵒᵖ).map (T.map limitToU) := by
    ext j
    show T.map (cVTail.π.app j) ≫ T.map (stageToU j) = T.map limitToU
    rw [← T.map_comp]
    apply congrArg T.map
    apply yoneda.map_injective
    show yoneda.map (limLeg j ≫ stageToU j) = yoneda.map limitToU
    simp only [Functor.map_comp, limLeg, stageToU, limitToU, yoneda.map_preimage,
      Category.assoc, Iso.inv_hom_id_assoc]
    exact congrArg (fun q => limRepr.hom ≫ q) (pulledCone.π.app (tailOp.obj j)).w
  -- Hypotheses of Stacks 09ZN for the system of schemes, at the affine base `W`.
  have hSchemeAff : ∀ j : Tail, IsAffine (schemeTail.obj (op j)) := fun j => hVTailAff (op j)
  have : ∀ j : Tail, CompactSpace (schemeTail.obj (op j)) := fun j =>
    have := hSchemeAff j; inferInstance
  have : ∀ j : Tail, QuasiSeparatedSpace (schemeTail.obj (op j)) := fun j =>
    have := hSchemeAff j; inferInstance
  have hstageLft (j : Tailᵒᵖ) : LocallyOfFiniteType (T.map (stageToU j)) := by
    let i := j.unop.1
    let fstPull := pullback.fst (p.app (op i)) chart
    let sndPull := pullback.snd (p.app (op i)) chart
    have hfstEtale : QEtale.presheaf fstPull :=
      (MorphismProperty.relative_isStableUnderBaseChange QEtale).of_isPullback
        (IsPullback.of_hasPullback (p.app (op i)) chart).flip hpEtaleChart
    let a : yoneda.obj (VTail.obj j) ⟶ D.obj (op i) := (repETail.app j).hom ≫ fstPull
    have harr : Arrow.mk a ≅ Arrow.mk fstPull :=
      Arrow.isoMk (repETail.app j) (Iso.refl _) (by rfl)
    have ha : QEtale.presheaf a :=
      (MorphismProperty.arrow_iso_iff QEtale.presheaf harr).mpr hfstEtale
    have hcommChart : yoneda.map (stageToU j) ≫ chart = a ≫ p.app (op i) := by
      have hsnd : yoneda.map (stageToU j) = (repETail.app j).hom ≫ sndPull :=
        yoneda.map_preimage _
      rw [hsnd]
      calc ((repETail.app j).hom ≫ sndPull) ≫ chart
          _ = (repETail.app j).hom ≫ (sndPull ≫ chart) := Category.assoc _ _ _
          _ = (repETail.app j).hom ≫ (fstPull ≫ p.app (op i)) :=
              congrArg (fun q => (repETail.app j).hom ≫ q)
                (IsPullback.of_hasPullback (p.app (op i)) chart).w.symm
          _ = a ≫ p.app (op i) := (Category.assoc _ _ _).symm
    exact hfiniteType i (VTail.obj j) U a chart (stageToU j) ha hpEtaleChart hcommChart
  have : ∀ j : Tail, LocallyOfFiniteType (mapTail.app (op j)) := fun j => hstageLft (op j)
  -- Affineness, finiteness and integrality for the system of schemes.
  let Paff := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u}) T
  have : Paff.IsStableUnderBaseChange := BigFppfOver.isStableUnderBaseChange_inverseImage B S hS _
  let Pfin := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) T
  have : Pfin.IsStableUnderBaseChange := BigFppfOver.isStableUnderBaseChange_inverseImage B S hS _
  have harrTail {j k : Tailᵒᵖ} (g : j ⟶ k) :
      Arrow.mk (yoneda.map (VTail.map g)) ≅ Arrow.mk (ETail.map g) :=
    Arrow.isoMk (repETail.app j) (repETail.app k) (hrepNat g).symm
  have hyonedaMapAffine {j k : Tailᵒᵖ} (g : j ⟶ k) :
      _root_.AlgebraicGeometry.IsAffineHom (schemeTail.map g) := by
    have hdata := ((isAffineHom_tfae_of_isAlgebraicSpace B S hS (ETail.map g)
      (hEalg j.unop.1) (hEalg k.unop.1)).out 2 1).mp (hEaff (tailOp.map g))
    exact (presheaf_iff_of_arrow_iso B S hS Paff _ _ (harrTail g)).mp hdata.2
  have hyonedaMapFinite {j k : Tailᵒᵖ} (g : j ⟶ k) :
      _root_.AlgebraicGeometry.IsFinite (schemeTail.map g) := by
    have hlocalE : Pfin.presheaf (ETail.map g) :=
      ((isFinite_iff_representable B S hS (ETail.map g) (hEalg j.unop.1)
        (hEalg k.unop.1)).mp (hEfinite (leOfHom (tailOp.map g).unop))).2
    exact (presheaf_iff_of_arrow_iso B S hS Pfin _ _ (harrTail g)).mp hlocalE
  let Pint := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u}) T
  have : Pint.IsStableUnderBaseChange := BigFppfOver.isStableUnderBaseChange_inverseImage B S hS _
  have : Pint.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange Pint
  have hintLocal : Pint.presheaf f :=
    ((isIntegralHom_iff_representable B S hS f hX hY).mp hintegral).2
  have hintPullback : Pint.presheaf (pullback.snd f chart) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f chart) hintLocal
  have : _root_.AlgebraicGeometry.IsIntegralHom (T.map limitToU) :=
    (presheaf_iff_of_arrow_iso B S hS Pint _ _
      (arrowIsoYonedaPreimage B S hS limRepr (pullback.snd f chart))).mp hintPullback
  -- Stacks 09ZN for the system of schemes over `W`.
  have hEventually := _root_.AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral
    schemeTail mapTail coneTail hcSchemeTail (T.map limitToU)
    (fun j => (congrArg (fun a => a.app (op j)) hconeTail_comm).symm)
    (fun _ => hyonedaMapAffine _) (fun _ => hyonedaMapFinite _)
  -- Descend finiteness over `W` to finiteness over `Y`: Stacks 03ZQ.
  obtain ⟨j₀, hj₀⟩ := Filter.eventually_atTop.1 hEventually
  refine Filter.eventually_atTop.2 ⟨j₀.1, fun i hi => ?_⟩
  let j : Tail := ⟨i, j₀.2.trans hi⟩
  have hPullbackFinite : Pfin.presheaf (pullback.snd (p.app (op i)) chart) :=
    (presheaf_iff_of_arrow_iso B S hS Pfin _ _
      (arrowIsoYonedaPreimage B S hS (repETail.app (op j)) (pullback.snd (p.app (op i)) chart))).mpr
      (hj₀ j hi)
  refine (isFinite_iff_etaleLocal B S hS (p.app (op i)) (hD i) hY).mpr
    ⟨U, chart, hchartSurjective, hpEtaleChart, ?_⟩
  exact (isFinite_iff_representable B S hS (pullback.snd (p.app (op i)) chart)
    (hEalg i) hUalg).mpr ⟨hPullbackFinite.1, hPullbackFinite⟩

end Main

end AlgebraicGeometry.Space

end
