module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessAndStrictTransformImage
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImmersionFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenComplementAffineHom
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformComparisonOffExceptional
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformSpaceEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedQuotientNoSupportedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalFirstOrderThickening
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal

/-!
# The image of a space in an admissible blowup, without side conditions

Let `S` be a scheme and let `X` be an algebraic space over `S`.  Stacks 0F49 concerns a morphism
`X ⟶ T` and a morphism `Y ⟶ T` of algebraic spaces over `S`, an open subspace `U ⊆ X`, and a
quasi-compact morphism `V ⟶ X ×_T Y` whose composite with the first projection factors through `U`.
Writing `Z ⊆ X ×_T Y` for the scheme-theoretic image of that morphism and `b : X' ⟶ X` for a
`U`-admissible blowup, the scheme-theoretic image of `V ⟶ X' ×_T Y` is the strict transform of `Z`
with respect to `b`.

The base algebraic space of the source is written `T` here, the name `B` being taken by the
ambient big fppf site; and `X' ×_T Y` is spelled `(X ×_T Y) ×_X X'`, which is the shape the
strict transform of `StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform` lives over and which
is canonically the same algebraic space.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompact_of_comp_fiberProductFirst_unconditional` is step (3)
  of the source's proof of Stacks 0F49: a morphism to `(X ×_T Y) ×_X X'` whose composite with
  the projection to `X ×_T Y` is quasi-compact is itself quasi-compact, because that projection
  is a base change of an admissible blowup, hence proper, hence separated, hence
  quasi-separated, so that Stacks 03KS applies.
* `AlgebraicGeometry.Space.exists_lift_strictTransformPullback` is step (2): the lift
  `w : V ⟶ Z ×_X X'` of the source, whose image lies over the complement of the centre.
* `AlgebraicGeometry.Space.range_le_strictTransformInAmbient` is the source's unnamed morphism
  `V ⟶ Z'`: the lift factors through the strict transform, because over the complement of the
  centre the strict transform cuts nothing away
  (`AlgebraicGeometry.Space.preimage_openComplement_le_strictTransform_of_isBlowupAlong`).
* `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_le_strictTransformInAmbient_of_lift`
  is the inclusion of the scheme-theoretic image of the lift in the strict transform, steps (1)
  and (2).
* `AlgebraicGeometry.Space.strictTransformInAmbient_le_schemeTheoreticImageSubfunctor` is the
  reverse inclusion, steps (4) and (5).
* `Space.schemeTheoreticImageSubfunctor_eq_strictTransformInAmbient_unconditional`
  is **Stacks 0F49**, the equality of the two, and carries the tag.
* The statements `AlgebraicGeometry.Space.isQuasiCompact_of_comp_fiberProductFirst`,
  `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_le_strictTransformInAmbient` and
  `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_eq_strictTransformInAmbient` of
  `StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessAndStrictTransformImage` are the shapes
  of the same results that take, as an explicit hypothesis, an input proved here.

## What is assumed

**Nothing.**
`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_eq_strictTransformInAmbient_unconditional`
asks for what Stacks 0F49 asks for and nothing more.  Neither half of the equality of Stacks 0F49
is assumed in proving it.

The one external input is the properness of an admissible blowup, Stacks 085Z, which is
`AlgebraicGeometry.Space.isProper_of_isBlowupAlong_of_isFinitePresentation`, read off for a
`U`-admissible blowup as `AlgebraicGeometry.Space.IsAdmissibleBlowup.isProper`; it is proved at
the source's hypotheses through a surjective étale chart of `X` and carries no side condition.

## Implementation notes

The finite-type condition on the ideal cutting out the centre is spelled, as in Stacks 086B and
in `AlgebraicGeometry.Space.IsAdmissibleBlowup`, as finite presentation of the closed immersion
of the centre.

For Stacks 0F49 the exceptional divisor is `Zc.1.preimage b.hom`, the inverse image of the
centre along the blowup, which is the subspace `E` of the source.  The strict transform is
`AlgebraicGeometry.Space.strictTransform` of Stacks 0862 applied to the scheme-theoretic image
`Z` viewed as an algebraic space over `X`, so it is a closed subspace of `Z ×_X X'`, and
`AlgebraicGeometry.Space.strictTransformInAmbient` is its image in `(X ×_T Y) ×_X X'` under the
morphism induced by the closed immersion of `Z` into `X ×_T Y`.

The source's step (5) says that the surjection `𝒪_{Z'} ⟶ 𝒪_{Z''}` is an isomorphism because
`𝒪_{Z'}` has no nonzero sections supported on the exceptional divisor.  That is used here in its
ideal-theoretic form, which needs no structure sheaf of `Z'` and no quotient: the defining ideal
of the scheme-theoretic image `Z''` consists, by part (2) of Stacks 082Z, of the local functions
killed by `V`, each of which is supported on the exceptional divisor by step (4); and the ideal
of sections supported on the exceptional divisor *is* the defining ideal of `Z'`, which for a
blowup is `AlgebraicGeometry.Space.definingIdealSheaf_strictTransform_of_isBlowupAlong`.  So the
defining ideal of `Z''` is contained in that of `Z'`, and the injectivity half of Stacks 03MB
turns that into `Z' ⊆ Z''`.  This is why the preamble of the section containing Stacks 0862 — the
local principality of the exceptional divisor and the affineness of the complement — is not
needed, and why Stacks 0863 part (3) is not quoted.

## References

* [Stacks Project, Tag 085Z](https://stacks.math.columbia.edu/tag/085Z)
* [Stacks Project, Tag 0F49](https://stacks.math.columbia.edu/tag/0F49)
* [Stacks Project, Tag 085R](https://stacks.math.columbia.edu/tag/085R)
* [Stacks Project, Tag 085T](https://stacks.math.columbia.edu/tag/085T)
* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 0863](https://stacks.math.columbia.edu/tag/0863)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 03KS](https://stacks.math.columbia.edu/tag/03KS)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Subfunctor

/-- **An inverse image along which a morphism becomes an isomorphism stays one after base
change.**  Let

```
P --ρ--> A'
|        |
π        b
v        v
Y --g--> A
```

be a cartesian square of type-valued functors and let `Ω ⊆ A` be a subfunctor such that the
comparison `Ω.fromPreimage b : b^{-1}Ω ⟶ Ω` is an isomorphism — that is, `b` is an isomorphism
over `Ω`.  Then `(g^{-1}Ω).fromPreimage π` is an isomorphism, i.e. `π` is an isomorphism over
`g^{-1}Ω`.

The inverse is built from the universal property of the square: over `g^{-1}Ω` the composite to
`A` factors through `Ω`, so inverting `Ω.fromPreimage b` produces a morphism to `b^{-1}Ω ⊆ A'`
which together with the inclusion of `g^{-1}Ω` into `Y` lifts to `P`.  That lift is a section of
the comparison, and it is also a retraction because a morphism into `P` is determined by its two
projections and the projection to `A'` is pinned down by `Ω.fromPreimage b` being a
monomorphism. -/
theorem isIso_fromPreimage_preimage_of_isPullback {C : Type*} [Category C]
    {P Y A' A : C ⥤ Type u} {π : P ⟶ Y} {ρ : P ⟶ A'} {g : Y ⟶ A} {b : A' ⟶ A}
    (hsq : IsPullback π ρ g b) (Ω : Subfunctor A) (hb : IsIso (Ω.fromPreimage b)) :
    IsIso ((Ω.preimage g).fromPreimage π) := by
  have hb' : (Ω.preimage b).ι ≫ b = Ω.fromPreimage b ≫ Ω.ι := (Ω.fromPreimage_ι b).symm
  -- The morphism `g^{-1}Ω ⟶ A'` obtained by inverting `Ω.fromPreimage b`.
  set k' : (Ω.preimage g).toFunctor ⟶ A' :=
    Ω.fromPreimage g ≫ inv (Ω.fromPreimage b) ≫ (Ω.preimage b).ι with hk'
  have hk'b : (Ω.preimage g).ι ≫ g = k' ≫ b := by
    rw [hk']
    simp only [Category.assoc, hb', IsIso.inv_hom_id_assoc]
    exact (Ω.fromPreimage_ι g).symm
  -- Its lift to `P`.
  set k : (Ω.preimage g).toFunctor ⟶ P := hsq.lift (Ω.preimage g).ι k' hk'b with hk
  have hkπ : k ≫ π = (Ω.preimage g).ι := hsq.lift_fst _ _ _
  have hkρ : k ≫ ρ = k' := hsq.lift_snd _ _ _
  have hle : range k ≤ (Ω.preimage g).preimage π := by
    rw [← image_le_iff, ← range_comp, hkπ, range_ι]
  set σ : (Ω.preimage g).toFunctor ⟶ ((Ω.preimage g).preimage π).toFunctor := lift k hle with hσ
  have hσι : σ ≫ ((Ω.preimage g).preimage π).ι = k := lift_ι _ _
  -- `σ` is a section.
  have hsec : σ ≫ (Ω.preimage g).fromPreimage π = 𝟙 _ := by
    refine (cancel_mono (Ω.preimage g).ι).1 ?_
    rw [Category.assoc, (Ω.preimage g).fromPreimage_ι π, ← Category.assoc, hσι, hkπ,
      Category.id_comp]
  -- `σ` is a retraction: both legs to `Y` and to `A'` agree.
  have hret : (Ω.preimage g).fromPreimage π ≫ σ = 𝟙 _ := by
    refine (cancel_mono ((Ω.preimage g).preimage π).ι).1 ?_
    rw [Category.assoc, hσι, Category.id_comp]
    refine hsq.hom_ext ?_ ?_
    · rw [Category.assoc, hkπ, (Ω.preimage g).fromPreimage_ι π]
    · have hw : (((Ω.preimage g).fromPreimage π) ≫ Ω.fromPreimage g) ≫ Ω.ι =
          (((Ω.preimage g).preimage π).ι ≫ ρ) ≫ b := by
        simp only [Category.assoc, Ω.fromPreimage_ι g, ← hsq.w]
        rw [(Ω.preimage g).fromPreimage_ι_assoc π]
      set lam : ((Ω.preimage g).preimage π).toFunctor ⟶ (Ω.preimage b).toFunctor :=
        (isPullback_preimage b Ω).lift (((Ω.preimage g).fromPreimage π) ≫ Ω.fromPreimage g)
          (((Ω.preimage g).preimage π).ι ≫ ρ) hw with hlam
      have hlam₁ : lam ≫ Ω.fromPreimage b =
          ((Ω.preimage g).fromPreimage π) ≫ Ω.fromPreimage g :=
        (isPullback_preimage b Ω).lift_fst _ _ _
      have hlam₂ : lam ≫ (Ω.preimage b).ι = ((Ω.preimage g).preimage π).ι ≫ ρ :=
        (isPullback_preimage b Ω).lift_snd _ _ _
      rw [Category.assoc, hkρ, hk']
      calc (Ω.preimage g).fromPreimage π ≫ Ω.fromPreimage g ≫
              inv (Ω.fromPreimage b) ≫ (Ω.preimage b).ι
          = ((Ω.preimage g).fromPreimage π ≫ Ω.fromPreimage g) ≫
              inv (Ω.fromPreimage b) ≫ (Ω.preimage b).ι := by rw [Category.assoc]
        _ = (lam ≫ Ω.fromPreimage b) ≫ inv (Ω.fromPreimage b) ≫ (Ω.preimage b).ι := by
              rw [hlam₁]
        _ = lam ≫ (Ω.preimage b).ι := by simp
        _ = ((Ω.preimage g).preimage π).ι ≫ ρ := hlam₂
  exact ⟨σ, hret, hsec⟩

/-- **The range of a factorization through a subfunctor is the inverse image of the range.**  If
the range of `f : G ⟶ F` lies in a subfunctor `W ⊆ F`, then the range of the induced
`G ⟶ W` is the inverse image along `W.ι` of the range of `f`. -/
theorem range_lift_eq_preimage_range {C : Type*} [Category C] {F G : C ⥤ Type u}
    (W : Subfunctor F) (f : G ⟶ F) (hf : range f ≤ W) :
    range (lift f hf) = (range f).preimage W.ι := by
  refine Subfunctor.ext (funext fun A => Set.ext fun x => ?_)
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext hy⟩

/-- **A monomorphism of type-valued functors reflects the inverse image of an image.**  For a
monomorphism `m` the inverse image along `m` of the image of a subfunctor is that
subfunctor. -/
theorem preimage_image_of_mono {C : Type*} [Category C] {F G : C ⥤ Type u} (R : Subfunctor F)
    (m : F ⟶ G) [Mono m] : (R.image m).preimage m = R := by
  have hinj : ∀ A, Function.Injective (m.app A) := fun A => by
    rw [← mono_iff_injective]
    exact (NatTrans.mono_iff_mono_app m).1 inferInstance A
  refine Subfunctor.ext (funext fun A => Set.ext fun x => ?_)
  constructor
  · rintro ⟨r, hr, hrx⟩
    exact hinj A hrx ▸ hr
  · exact fun hx => ⟨x, hx, rfl⟩

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance (priority := high) hasLimit_cospan_presheaf_BlowupPropernessUnconditional
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Two general facts about closed subspaces -/

section Generic

/- The sections of `𝒪_P` are indexed by the objects of `(smallEtaleRingedSite B S hS P.1 P.2).C`,
which is `SmallEtale B S hS P.1` only after unfolding
`AlgebraicGeometry.Space.smallEtaleRingedSite`; a chart presented as an object of the latter is
therefore not type-correct at `implicit` transparency without this. -/
attribute [local implicit_reducible] smallEtaleRingedSite

/-- **A closed subspace cut out by the sections supported on `T` contains every étale subspace
that misses `T`.**  Let `H ⊆ P` be a closed subspace of an algebraic space whose defining ideal
sheaf of Stacks 03MB is the ideal of sections of `𝒪_P` supported on a set of points `T`
(Stacks 0859), and let `can : Q ⟶ P` be an étale morphism no point of whose source lies over
`T`.  Then `can` factors through `H`.

On an étale chart `D` of `Q` the defining ideal of `can^{-1}H` is the defining ideal of `H` on
the postcomposed chart of `P` (Stacks 082Z, the étale-localization computation
`AlgebraicGeometry.Space.definingIdealAt_preimage_eq_definingIdealAt_smallEtalePostcomp`), which
by hypothesis is the ideal of sections supported on `T`, which is the ideal of sections of
`𝒪_Q` supported on `|can|^{-1}T = ∅`
(`AlgebraicGeometry.Space.supportedSectionsUnit_obj_postcomp`), and a section with empty support
is zero.  So `can^{-1}H` has zero defining ideal on every chart and is the whole of `Q` by the
injectivity half of Stacks 03MB. -/
theorem range_le_of_definingIdealSheaf_eq_supportedSections
    {Q P : AlgebraicSpaces B S hS} (can : Q ⟶ P) (hcan : IsEtale B S hS can.hom)
    (T : Set (points B S hS P.1)) (H : ClosedSubspaces B S hS P.1)
    (hH : definingIdealSheaf B S hS P H =
      supportedSectionsSubmodule B S hS P.1 P.2 T
        (SheafOfModules.unit (structureRingSheaf B S hS P)))
    (hT : pointsMap B S hS Q.1 can.hom ⁻¹' T = ∅) :
    Subfunctor.range can.hom ≤ H.1 := by
  set Hp : ClosedSubspaces B S hS Q.1 :=
    ⟨H.1.preimage can.hom, isClosedSubspace_preimage B S hS can.hom H.1 P.2 Q.2 H.2⟩ with hHp
  have key : ∀ D : SmallEtale B S hS Q.1, definingIdealAt B S hS Q Hp (op D) = ⊥ := by
    intro D
    have h1 : definingIdealAt B S hS Q Hp (op D) =
        definingIdealAt B S hS P H (op ((smallEtalePostcomp B S hS can hcan).obj D)) :=
      (definingIdealAt_preimage_eq_definingIdealAt_smallEtalePostcomp B S hS can hcan H D).symm
    have h2 := (supportedSectionsUnit_obj_postcomp B S hS can hcan T
      (pointsMap B S hS Q.1 can.hom ⁻¹' T) rfl D).symm
    rw [hT] at h2
    have h4 : (supportedSectionsSubmodule B S hS Q.1 Q.2 (∅ : Set (points B S hS Q.1))
        (SheafOfModules.unit (structureRingSheaf B S hS Q))).toSubmodule.obj (op D) = ⊥ := by
      refine le_antisymm (fun s hs => ?_) bot_le
      simp only [Submodule.mem_bot]
      refine eq_zero_of_supportOfSection_eq_empty
        (F := moduleAddSheaf B S hS Q.1 Q.2 (SheafOfModules.unit (structureRingSheaf B S hS Q)))
        D s ?_
      refine Set.eq_empty_iff_forall_notMem.2 fun y hy => ?_
      exact ((mem_supportedSectionsSubmodule_iff B S hS Q.1 Q.2 ∅ _ D s).1 hs) hy
    rw [h1, ← definingIdealSheaf_obj, hH]
    exact h2.trans h4
  rw [← Subfunctor.preimage_eq_top_iff]
  exact top_le_iff.1 (le_of_forall_definingIdealAt_le B S hS Q
    ⟨⊤, isClosedSubspace_top B S hS Q⟩ Hp fun D _ => (key D) ▸ bot_le)

/-- The defining ideal of the whole of an algebraic space, viewed as a closed subspace of
itself, vanishes: the inclusion of the subspace is split by the factorization of the identity
through it, so `AlgebraicGeometry.Space.definingIdealAt_eq_bot_of_retraction` applies. -/
theorem definingIdealAt_eq_bot_of_eq_top (P : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS P.1) (hZ : Z.1 = ⊤) (D : (SmallEtale B S hS P.1)ᵒᵖ) :
    definingIdealAt B S hS P Z D = ⊥ := by
  have hle : Subfunctor.range (𝟙 P.1) ≤ Z.1 := hZ ▸ le_top
  refine definingIdealAt_eq_bot_of_retraction B S hS P Z
    (ObjectProperty.homMk (Subfunctor.lift (𝟙 P.1) hle)) ?_ D
  apply ObjectProperty.hom_ext
  exact Subfunctor.lift_ι _ hle

/-- The base change of a factorization through a subfunctor has the range of the factorization. -/
private theorem range_pullback_snd_eq_range_lift {Vs P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (w : Vs ⟶ P) (O : Subfunctor P) (hrange : Subfunctor.range w ≤ O) :
    Subfunctor.range (pullback.snd w O.ι) = Subfunctor.range (Subfunctor.lift w hrange) :=
  (Subfunctor.range_eq_preimage_of_isPullback (IsPullback.of_hasPullback w O.ι).flip).trans
    (Subfunctor.range_lift_eq_preimage_range O w hrange).symm

/-- **A function killed on a scheme-theoretically dense open part is supported on the closed
complement.**  Let `P` be an algebraic space over `S`, let `T` be a closed set of its points and
let `Co ⊆ P` be an open subspace whose points are exactly those outside `T`.  Let `w : V ⟶ P`
be a morphism factoring through `Co` whose factorization `V ⟶ Co` is quasi-compact with
scheme-theoretic image the whole of `Co`.  Then every local section of `𝒪_P` killed by `w` —
that is, every section of the kernel ideal sheaf of Stacks 03G8 — is supported on `T` in the
sense of Stacks 0859.

A subchart of a chart of `P` all of whose points lie outside `T` lies over `Co`, hence factors
through it by Stacks 03IE and comes from a chart of `Co` by
`AlgebraicGeometry.Space.exists_factorisation_smallEtalePostcomp`.  Over such a chart the kernel
ideal of `w` is the kernel ideal of the base change `V ×_P Co ⟶ Co`
(`AlgebraicGeometry.Space.kernelIdealSheaf_fibreProduct_obj`), which by Stacks 082Z is the
defining ideal of the scheme-theoretic image of that base change; that image is the whole of
`Co` because the base change is, up to the canonical isomorphism, the given factorization.  So
the section dies on every subchart lying outside `T`, and is therefore supported on `T` by
the maximality of the open zero locus of Stacks 04KA. -/
theorem kernelIdealSheaf_le_supportedSectionsSubmodule {V P : AlgebraicSpaces B S hS}
    (T : Set (points B S hS P.1)) (hT : IsClosed T) (Co : Subfunctor P.1)
    (hCo : IsOpenSubspace B S hS Co)
    (hCoPts : subspacePointSet B S hS P.1 Co = Tᶜ) (w : V ⟶ P)
    (hrange : Subfunctor.range w.hom ≤ Co)
    (hqc : IsQuasiCompact B S hS (Subfunctor.lift w.hom hrange))
    (htop : schemeTheoreticImageSubfunctor B S hS (Subfunctor.lift w.hom hrange) = ⊤) :
    kernelIdealSheaf B S hS w ≤ supportedSectionsSubmodule B S hS P.1 P.2 T
      (SheafOfModules.unit (structureRingSheaf B S hS P)) := by
  set CoSp : AlgebraicSpaces B S hS := ⟨Co.toFunctor, hCo.1⟩ with hCoSp
  set can : CoSp ⟶ P := ObjectProperty.homMk Co.ι with hcanDef
  have hcan : IsEtale B S hS can.hom := isEtale_ι_of_isOpenSubspace hCo
  have hmono : Mono can.hom := inferInstanceAs (Mono Co.ι)
  set wC : V.1 ⟶ CoSp.1 := Subfunctor.lift w.hom hrange with hwCdef
  have hwCι : wC ≫ can.hom = w.hom := Subfunctor.lift_ι _ _
  -- The base change `V ×_P Co ⟶ Co` has the same range as `wC`, hence full image.
  set bc : AlgebraicSpaces.fiberProduct B S hS w can ⟶ CoSp :=
    ObjectProperty.homMk (pullback.snd w.hom can.hom) with hbcDef
  have hsq : IsPullback (pullback.fst w.hom can.hom) (pullback.snd w.hom can.hom) w.hom can.hom :=
    IsPullback.of_hasPullback _ _
  have hbcRange : Subfunctor.range bc.hom = Subfunctor.range wC :=
    range_pullback_snd_eq_range_lift B S hS w.hom Co hrange
  have hbcTop : schemeTheoreticImageSubfunctor B S hS bc.hom = ⊤ := by
    rw [schemeTheoreticImageSubfunctor_congr_range' B S hS bc.hom wC CoSp.2 hbcRange]
    exact htop
  -- and it is quasi-compact, being the factorization composed with an isomorphism.
  have hchi : (𝟙 V.1) ≫ w.hom = wC ≫ can.hom := by rw [Category.id_comp, hwCι]
  set chi : V.1 ⟶ (AlgebraicSpaces.fiberProduct B S hS w can).1 :=
    pullback.lift (𝟙 V.1) wC hchi with hchiDef
  have hchifst : chi ≫ pullback.fst w.hom can.hom = 𝟙 V.1 := pullback.lift_fst _ _ _
  have : Mono (pullback.fst w.hom can.hom) := hsq.mono_fst_of_mono
  have : IsSplitEpi (pullback.fst w.hom can.hom) := IsSplitEpi.mk' ⟨chi, hchifst⟩
  have hfstIso : IsIso (pullback.fst w.hom can.hom) :=
    isIso_of_mono_of_isSplitEpi (pullback.fst w.hom can.hom)
  have hfstwC : pullback.fst w.hom can.hom ≫ wC = pullback.snd w.hom can.hom := by
    refine (cancel_mono can.hom).1 ?_
    rw [Category.assoc, hwCι, pullback.condition]
  have hbcQc : IsQuasiCompact B S hS bc.hom := by
    rw [hbcDef]
    show IsQuasiCompact B S hS (pullback.snd w.hom can.hom)
    rw [← hfstwC]
    exact isQuasiCompact_isIso_comp B S hS (pullback.fst w.hom can.hom) hqc
  -- The kernel ideal of the base change vanishes on every chart of `Co`.
  have hker : ∀ D : SmallEtale B S hS CoSp.1,
      (kernelIdealSheaf B S hS bc).obj (op D) = ⊥ := by
    intro D
    rw [← definingIdealSheaf_schemeTheoreticImage_eq_kernelIdealSheaf B S hS bc hbcQc,
      definingIdealSheaf_obj]
    exact definingIdealAt_eq_bot_of_eq_top B S hS CoSp _ hbcTop _
  -- Now the chart computation.
  intro D s hs
  refine (mem_supportedSectionsSubmodule_iff B S hS P.1 P.2 T _ D.unop s).2 ?_
  refine sectionSupportedIn_of_restrict_eq_zero_of_imageInOpen B S hS P T hT _ D.unop s ?_
  intro U' i hi
  -- `U'` lies over `Co`, hence comes from a chart of `Co`.
  have hpts : Set.range (pointsMap B S hS _ U'.1.hom) ⊆
      Set.range (pointsMap B S hS Co.toFunctor Co.ι) := by
    rintro x ⟨y, rfl⟩
    rw [show Set.range (pointsMap B S hS Co.toFunctor Co.ι) =
      subspacePointSet B S hS P.1 Co from rfl, hCoPts]
    have h := hi y
    rw [← pointsMap_chart_hom B S hS P.1 i y]
    exact h
  obtain ⟨k, hk⟩ := (factorsThrough_openSubspace_iff_points B S hS P.2
    (isAlgebraicSpace_yoneda B S hS _) Co hCo U'.1.hom).2 hpts
  obtain ⟨U'', m, e, hem⟩ :=
    exists_factorisation_smallEtalePostcomp B S hS can hcan i k hk
  -- Over the chart coming from `Co` the section dies.
  have hm0 : (SheafOfModules.unit (structureRingSheaf B S hS P)).val.map m.op s = 0 := by
    have hvanish := (Submodule.eq_bot_iff _).1 (hker U'')
    have hmem := (kernelIdealSheaf B S hS w).toSubmodule.map_mem m.op hs
    rw [← kernelIdealSheaf_fibreProduct_obj B S hS w can hcan U'', ← hbcDef] at hmem
    exact hvanish _ hmem
  have hcomp : i.op = m.op ≫ e.op := by rw [← op_comp, hem]
  have hkey := (SheafOfModules.unit (structureRingSheaf B S hS P)).val.map_comp_apply m.op e.op s
  rw [hcomp, hkey, hm0]
  exact map_zero _

/-- **The scheme-theoretic image of a factorization through an open subspace is the restriction
of the scheme-theoretic image.**  Let `w : Vs ⟶ P` be a quasi-compact morphism of algebraic
spaces over `S` whose image lies in an open subspace `O ⊆ P`.  Then the scheme-theoretic image
of the factorization `Vs ⟶ O` is the inverse image along the inclusion of `O` of the
scheme-theoretic image of `w`.

This is part (3) of Stacks 082Z, compatibility of the scheme-theoretic image with étale base
change of the target, read at the inclusion of `O`: the factorization and the base change
`Vs ×_P O ⟶ O` have the same range — `AlgebraicGeometry.Space.range_lift_eq_preimage_range` and
`CategoryTheory.Subfunctor.range_eq_preimage_of_isPullback` both compute it as the inverse image
of the range of `w` — and the scheme-theoretic image depends only on the range. -/
theorem schemeTheoreticImageSubfunctor_lift {Vs P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hVs : IsAlgebraicSpace B S hS Vs) (hP : IsAlgebraicSpace B S hS P) (w : Vs ⟶ P)
    (hw : IsQuasiCompact B S hS w) (O : Subfunctor P) (hO : IsOpenSubspace B S hS O)
    (hrange : Subfunctor.range w ≤ O) :
    schemeTheoreticImageSubfunctor B S hS (Subfunctor.lift w hrange) =
      (schemeTheoreticImageSubfunctor B S hS w).preimage O.ι := by
  rw [← schemeTheoreticImageSubfunctor_congr_range' B S hS (pullback.snd w O.ι)
    (Subfunctor.lift w hrange) hO.1 (range_pullback_snd_eq_range_lift B S hS w O hrange)]
  exact schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact' B S hS
    w O.ι hVs hP hO.1 hw (isEtale_ι_of_isOpenSubspace hO)

/-- **A full scheme-theoretic image stays full after an isomorphism of the target.**  If the
scheme-theoretic image of `h ≫ e` is everything and `e` is an isomorphism, then so is the
scheme-theoretic image of `h`.

The square `(h ≫ e) ≫ e⁻¹ = 1 ≫ h` puts the scheme-theoretic image of `h ≫ e` inside the
inverse image along `e⁻¹` of that of `h`, so the latter inverse image is everything, which says
that the range of `e⁻¹` — all of the target, `e⁻¹` being an epimorphism — lies in the
scheme-theoretic image of `h`. -/
theorem schemeTheoreticImageSubfunctor_eq_top_of_comp_isIso
    {Vs C D : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hC : IsAlgebraicSpace B S hS C)
    (hD : IsAlgebraicSpace B S hS D) (h : Vs ⟶ C) (e : C ⟶ D) (he : IsIso e)
    (htop : schemeTheoreticImageSubfunctor B S hS (h ≫ e) = ⊤) :
    schemeTheoreticImageSubfunctor B S hS h = ⊤ := by
  have := he
  have hsq : (h ≫ e) ≫ inv e = 𝟙 Vs ≫ h := by
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
  have hle := schemeTheoreticImageSubfunctor_le_preimage B S hS hD hC hsq
  rw [htop] at hle
  refine le_antisymm le_top ?_
  have h2 : Subfunctor.range (inv e) ≤ schemeTheoreticImageSubfunctor B S hS h :=
    (Subfunctor.preimage_eq_top_iff _ _).1 (top_le_iff.1 hle)
  rwa [Subfunctor.range_eq_top] at h2

end Generic

/-! ### The ambient fibre products of Stacks 0F49 -/

section Ambient

variable {T X Y X' : AlgebraicSpaces B S hS}

/-- **The exceptional preimage, computed through the projection to the source.**  For the
exceptional divisor `b⁻¹Zc` of a morphism `b : A' ⟶ A` and an algebraic space `f : Xs ⟶ A` over
`A`, the exceptional preimage `pr_{A'}^{-1}(b⁻¹Zc)` of
`AlgebraicGeometry.Space.exceptionalPreimage` in `Xs ×_A A'` is the inverse image of `Zc` along
the composite `Xs ×_A A' ⟶ Xs ⟶ A`.  This is the cartesian square `pr_{Xs} ≫ f = pr_{A'} ≫ b`
read on subfunctors. -/
theorem exceptionalPreimage_preimage_eq {A Xs A' : AlgebraicSpaces B S hS} (f : Xs ⟶ A)
    (b : A' ⟶ A) (Zc : Subfunctor A.1) :
    exceptionalPreimage B S hS f b (Zc.preimage b.hom) =
      Zc.preimage ((strictTransformPullbackToSource B S hS f b).hom ≫ f.hom) := by
  show (Zc.preimage b.hom).preimage (pullback.snd f.hom b.hom) = _
  rw [← Subfunctor.preimage_comp, ← pullback.condition]
  rfl

/-- **The exceptional preimage on points.**  The set of points of
`pr_{A'}^{-1}(b⁻¹Zc) ⊆ Xs ×_A A'` is the inverse image of the point set of the centre `Zc` along
the composite `Xs ×_A A' ⟶ Xs ⟶ A`.

This is `AlgebraicGeometry.Space.exceptionalPreimage_preimage_eq` read on points, by Stacks 03H4
in the form `AlgebraicGeometry.Space.range_pointsMap_preimage_ι`. -/
theorem exceptionalPreimageSet_eq_preimage_centre {A Xs A' : AlgebraicSpaces B S hS} (f : Xs ⟶ A)
    (b : A' ⟶ A) (Zc : ClosedSubspaces B S hS A.1) :
    exceptionalPreimageSet B S hS f b (Zc.1.preimage b.hom) =
      pointsMap B S hS (strictTransformPullback B S hS f b).1
          ((strictTransformPullbackToSource B S hS f b).hom ≫ f.hom) ⁻¹'
        subspacePointSet B S hS A.1 Zc.1 := by
  rw [show exceptionalPreimageSet B S hS f b (Zc.1.preimage b.hom) =
    subspacePointSet B S hS (strictTransformPullback B S hS f b).1
      (exceptionalPreimage B S hS f b (Zc.1.preimage b.hom)) from rfl,
    exceptionalPreimage_preimage_eq B S hS f b Zc.1]
  exact range_pointsMap_preimage_ι B S hS _ Zc.1

/-- **The part of `Xs ×_A A'` lying over the complement of the centre is the complement of the
exceptional preimage, on points.**  The point set of the inverse image of `A ∖ Zc` along
`Xs ×_A A' ⟶ Xs ⟶ A` is the complement of the point set `|pr_{A'}^{-1}(b⁻¹Zc)|` of the
exceptional preimage.

Both sides are computed by Stacks 03H4 in the form
`AlgebraicGeometry.Space.range_pointsMap_preimage_ι` as inverse images along that composite, of
the complement of `|Zc|` on the left — Stacks 03BZ in the form
`AlgebraicGeometry.Space.subspacePointSet_openComplement` — and of `|Zc|` on the right. -/
theorem subspacePointSet_preimage_openComplement_eq_compl_exceptionalPreimageSet
    {A Xs A' : AlgebraicSpaces B S hS} (f : Xs ⟶ A) (b : A' ⟶ A)
    (Zc : ClosedSubspaces B S hS A.1) :
    subspacePointSet B S hS (strictTransformPullback B S hS f b).1
        (((openComplementOfClosedSubspace B S hS A Zc).1.preimage f.hom).preimage
          (strictTransformPullbackToSource B S hS f b).hom) =
      (exceptionalPreimageSet B S hS f b (Zc.1.preimage b.hom))ᶜ := by
  rw [show subspacePointSet B S hS (strictTransformPullback B S hS f b).1
      (((openComplementOfClosedSubspace B S hS A Zc).1.preimage f.hom).preimage
        (strictTransformPullbackToSource B S hS f b).hom) =
    Set.range (pointsMap B S hS
      ((((openComplementOfClosedSubspace B S hS A Zc).1.preimage f.hom).preimage
        (strictTransformPullbackToSource B S hS f b).hom)).toFunctor
      ((((openComplementOfClosedSubspace B S hS A Zc).1.preimage f.hom).preimage
        (strictTransformPullbackToSource B S hS f b).hom)).ι) from rfl,
    range_pointsMap_preimage_ι B S hS (strictTransformPullbackToSource B S hS f b).hom
      ((openComplementOfClosedSubspace B S hS A Zc).1.preimage f.hom),
    range_pointsMap_preimage_ι B S hS f.hom (openComplementOfClosedSubspace B S hS A Zc).1,
    show Set.range (pointsMap B S hS (openComplementOfClosedSubspace B S hS A Zc).1.toFunctor
        (openComplementOfClosedSubspace B S hS A Zc).1.ι) =
      subspacePointSet B S hS A.1 (openComplementOfClosedSubspace B S hS A Zc).1 from rfl,
    subspacePointSet_openComplement B S hS A Zc,
    exceptionalPreimageSet_eq_preimage_centre B S hS f b Zc, pointsMap_comp, Set.preimage_comp,
    Set.preimage_compl, Set.preimage_compl]

/-- The part of `Xs ×_A A'` lying over the complement of the centre is an open subspace. -/
private theorem isOpenSubspace_preimage_preimage_openComplement
    {A Xs A' : AlgebraicSpaces B S hS} (f : Xs ⟶ A) (b : A' ⟶ A)
    (Zc : ClosedSubspaces B S hS A.1) :
    IsOpenSubspace B S hS
      (((openComplementOfClosedSubspace B S hS A Zc).1.preimage f.hom).preimage
        (strictTransformPullbackToSource B S hS f b).hom) :=
  isOpenSubspace_preimage B S hS (strictTransformPullbackToSource B S hS f b).hom _ Xs.2
    (strictTransformPullback B S hS f b).2
    (isOpenSubspace_preimage B S hS f.hom _ A.2 Xs.2
      (openComplementOfClosedSubspace B S hS A Zc).2)

/-- **The part of `Xs ×_A A'` lying over the complement of the centre is contained in the strict
transform.**  For `b : A' ⟶ A` the blowup of `A` in `Zc` and `f : Xs ⟶ A` an algebraic space over
`A`, the inverse image of `A ∖ Zc` along `Xs ×_A A' ⟶ Xs ⟶ A` is contained in the strict
transform of `Xs` with respect to `b`.

For a blowup the strict transform is honestly cut out by the ideal of sections supported on the
exceptional preimage,
`AlgebraicGeometry.Space.definingIdealSheaf_strictTransform_of_isBlowupAlong`, and that part of
`Xs ×_A A'` is an open subspace — hence an étale algebraic space over `Xs ×_A A'` — no point of
which lies on the exceptional preimage, by
`AlgebraicGeometry.Space.subspacePointSet_preimage_openComplement_eq_compl_exceptionalPreimageSet`.
So `AlgebraicGeometry.Space.range_le_of_definingIdealSheaf_eq_supportedSections` applies.

This is the content of Stacks 085T part (1) that the strict transform sees: away from the centre
the blowup is an isomorphism, so nothing is cut away there. -/
theorem preimage_openComplement_le_strictTransform_of_isBlowupAlong
    {A Xs A' : AlgebraicSpaces B S hS} (f : Xs ⟶ A) (b : A' ⟶ A)
    (Zc : ClosedSubspaces B S hS A.1) (hbl : IsBlowupAlong B S hS Zc b) :
    ((openComplementOfClosedSubspace B S hS A Zc).1.preimage f.hom).preimage
        (strictTransformPullbackToSource B S hS f b).hom ≤
      (strictTransform B S hS f b (Zc.1.preimage b.hom)).1 := by
  set Co : Subfunctor (strictTransformPullback B S hS f b).1 :=
    ((openComplementOfClosedSubspace B S hS A Zc).1.preimage f.hom).preimage
      (strictTransformPullbackToSource B S hS f b).hom with hCo
  have hOpen : IsOpenSubspace B S hS Co :=
    isOpenSubspace_preimage_preimage_openComplement B S hS f b Zc
  have hT : pointsMap B S hS Co.toFunctor Co.ι ⁻¹'
      exceptionalPreimageSet B S hS f b (Zc.1.preimage b.hom) = ∅ := by
    have hcompl := subspacePointSet_preimage_openComplement_eq_compl_exceptionalPreimageSet
      B S hS f b Zc
    exact Set.eq_empty_iff_forall_notMem.2 fun x hx => hcompl.le ⟨x, rfl⟩ hx
  have h := range_le_of_definingIdealSheaf_eq_supportedSections B S hS
    (ObjectProperty.homMk Co.ι : (⟨Co.toFunctor, hOpen.1⟩ : AlgebraicSpaces B S hS) ⟶
      strictTransformPullback B S hS f b)
    (isEtale_ι_of_isOpenSubspace hOpen)
    (exceptionalPreimageSet B S hS f b (Zc.1.preimage b.hom))
    (strictTransform B S hS f b (Zc.1.preimage b.hom))
    (definingIdealSheaf_strictTransform_of_isBlowupAlong B S hS f b Zc hbl) hT
  rwa [show (ObjectProperty.homMk Co.ι : (⟨Co.toFunctor, hOpen.1⟩ : AlgebraicSpaces B S hS) ⟶
    strictTransformPullback B S hS f b).hom = Co.ι from rfl, Subfunctor.range_ι] at h

/-- **The morphism `Z ×_X X' ⟶ (X ×_T Y) ×_X X'` is a base change of the closed immersion of
`Z`.**  This is step (1) of the source's proof of Stacks 0F49: the two ambient fibre products sit
in a cartesian square over the closed immersion `Z ⟶ X ×_T Y` and the projection to `X ×_T Y`.

Pasting: the square for `Z ×_X X'` is the base change of `b` along `Z ⟶ X ×_T Y ⟶ X`, which is
the composite of the base change of `b` along `X ×_T Y ⟶ X` with the base change of
`Z ⟶ X ×_T Y`, so `CategoryTheory.IsPullback.of_right` splits off the left-hand square. -/
theorem isPullback_strictTransformToAmbient (p : X ⟶ T) (q : Y ⟶ T) (b : X' ⟶ X)
    (Z : ClosedSubspaces B S hS (AlgebraicSpaces.fiberProduct B S hS p q).1) :
    IsPullback (strictTransformToAmbient B S hS p q b Z)
      (pullback.fst (closedSubspaceFirst B S hS p q Z).hom b.hom)
      (pullback.fst (fiberProductFirst B S hS p q).hom b.hom) Z.1.ι := by
  have hsnd : strictTransformToAmbient B S hS p q b Z ≫
      pullback.snd (fiberProductFirst B S hS p q).hom b.hom =
      pullback.snd (closedSubspaceFirst B S hS p q Z).hom b.hom :=
    pullback.lift_snd _ _ _
  have hs : IsPullback (strictTransformToAmbient B S hS p q b Z ≫
        pullback.snd (fiberProductFirst B S hS p q).hom b.hom)
      (pullback.fst (closedSubspaceFirst B S hS p q Z).hom b.hom) b.hom
      (Z.1.ι ≫ (fiberProductFirst B S hS p q).hom) := by
    rw [hsnd]
    exact (IsPullback.of_hasPullback (closedSubspaceFirst B S hS p q Z).hom b.hom).flip
  exact IsPullback.of_right hs (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback (fiberProductFirst B S hS p q).hom b.hom).flip

/-- **The strict transform of `Z` is a closed subspace of `(X ×_T Y) ×_X X'`.**  This is the
`himm` input of the source's proof of Stacks 0F49, proved outright:
`AlgebraicGeometry.Space.strictTransformToAmbient` is a base change of the closed immersion of
`Z` by `AlgebraicGeometry.Space.isPullback_strictTransformToAmbient`, hence a closed immersion;
so is its composite with the closed immersion of the strict transform, and the range of a closed
immersion is a closed subspace. -/
theorem isClosedSubspace_strictTransformInAmbient (p : X ⟶ T) (q : Y ⟶ T) (b : X' ⟶ X)
    (Zc : ClosedSubspaces B S hS X.1)
    (Z : ClosedSubspaces B S hS (AlgebraicSpaces.fiberProduct B S hS p q).1) :
    IsClosedSubspace B S hS (strictTransformInAmbient B S hS p q b Zc Z) := by
  have := isClosedImmersion_isStableUnderBaseChange B S hS
  have hj : IsClosedImmersion B S hS (strictTransformToAmbient B S hS p q b Z) :=
    MorphismProperty.of_isPullback
      (isPullback_strictTransformToAmbient B S hS p q b Z).flip Z.2.2
  exact isClosedSubspace_range_of_isClosedImmersion B S hS _
    (strictTransform B S hS (closedSubspaceFirst B S hS p q Z) b (Zc.1.preimage b.hom)).2.1
    (isClosedImmersion_comp B S hS _ _
      (strictTransform B S hS (closedSubspaceFirst B S hS p q Z) b (Zc.1.preimage b.hom)).2.2 hj)

end Ambient

/-! ### The image of a space in an admissible blowup -/

section Image

variable {T X Y V X' : AlgebraicSpaces B S hS}

/-- **Step (3) of the source's proof of Stacks 0F49.**  Let `b : X' ⟶ X` be a `U`-admissible
blowup and let `v' : V ⟶ (X ×_T Y) ×_X X'` be a morphism whose composite with the projection to
`X ×_T Y` is quasi-compact.  Then `v'` is quasi-compact.

The projection `(X ×_T Y) ×_X X' ⟶ X ×_T Y` is a base change of `b`, so it is proper by
Stacks 04WP and `AlgebraicGeometry.Space.IsAdmissibleBlowup.isProper`, hence
separated, hence quasi-separated; and a morphism whose composite with a quasi-separated morphism
is quasi-compact is quasi-compact, which is Stacks 03KS.

Nothing is assumed: the properness of the admissible blowup is
`AlgebraicGeometry.Space.IsAdmissibleBlowup.isProper`, which carries no side condition. -/
theorem isQuasiCompact_of_comp_fiberProductFirst_unconditional
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)] (p : X ⟶ T) (q : Y ⟶ T)
    (U : OpenSubspaces B S hS X.1) (b : X' ⟶ X)
    (hb : IsAdmissibleBlowup B S hS U b)
    (v' : V.1 ⟶ (strictTransformPullback B S hS (fiberProductFirst B S hS p q) b).1)
    (hv' : IsQuasiCompact B S hS
      (v' ≫ pullback.fst (fiberProductFirst B S hS p q).hom b.hom)) :
    IsQuasiCompact B S hS v' := by
  have hbp : IsProper B S hS b.hom := hb.isProper
  have hproj : IsProper B S hS (pullback.fst (fiberProductFirst B S hS p q).hom b.hom) :=
    isProper_pullback_fst B S hS X'.property X.property
      (AlgebraicSpaces.fiberProduct B S hS p q).property b.hom
      (fiberProductFirst B S hS p q).hom hbp
  exact isQuasiCompact_of_comp_of_isQuasiSeparated B S hS v'
    (pullback.fst (fiberProductFirst B S hS p q).hom b.hom) V.property
    (AlgebraicSpaces.fiberProduct B S hS p q).property hv'
    (isQuasiSeparated_of_isSeparated B S hS hproj.1)

/-- **Step (2) of the source's proof of Stacks 0F49: the lift of `V` to `Z ×_X X'`.**  In the
setting of Stacks 0F49 — `v : V ⟶ X ×_T Y` with `v ≫ pr_X` factoring through `U`, a closed
subspace `Z ⊆ X ×_T Y` through which `v` factors, and a lift `v' : V ⟶ (X ×_T Y) ×_X X'` of `v`
— there is a morphism `w : V ⟶ Z ×_X X'` whose composite with
`AlgebraicGeometry.Space.strictTransformToAmbient` is `v'`, whose composite with the projection
to `Z` is the given factorization, and whose image lies in the part of `Z ×_X X'` over the
complement of the centre `Zc`.

The morphism is the one the fibre product `Z ×_X X'` supplies for the factorization of `v`
through `Z` and the composite `V ⟶ (X ×_T Y) ×_X X' ⟶ X'`; the two agree over `X` because `v'`
lifts `v`.  Its image avoids the centre because `v ≫ pr_X` factors through `U`, which is disjoint
from `Zc`, so no point of `V` maps into `|Zc|`, and the part of `Z ×_X X'` over the complement is
cut out by exactly that condition on points
(`AlgebraicGeometry.Space.subspacePointSet_preimage_openComplement_eq_compl_exceptionalPreimageSet`
together with Stacks 03IE in the form
`AlgebraicGeometry.Space.factorsThrough_openSubspace_iff_points`). -/
theorem exists_lift_strictTransformPullback (p : X ⟶ T) (q : Y ⟶ T)
    (U : OpenSubspaces B S hS X.1) (Zc : ClosedSubspaces B S hS X.1) (b : X' ⟶ X)
    (hdisj : Disjoint (subspacePointSet B S hS X.1 U.1)
      (subspacePointSet B S hS X.1 Zc.1))
    (Z : ClosedSubspaces B S hS (AlgebraicSpaces.fiberProduct B S hS p q).1)
    (v : V ⟶ AlgebraicSpaces.fiberProduct B S hS p q)
    (vZ : V.1 ⟶ Z.1.toFunctor) (hvZ : vZ ≫ Z.1.ι = v.hom)
    (v' : V.1 ⟶ (strictTransformPullback B S hS (fiberProductFirst B S hS p q) b).1)
    (hv' : v' ≫ pullback.fst (fiberProductFirst B S hS p q).hom b.hom = v.hom)
    (hvU : Subfunctor.range (v.hom ≫ (fiberProductFirst B S hS p q).hom) ≤ U.1) :
    ∃ w : V.1 ⟶ (strictTransformPullback B S hS (closedSubspaceFirst B S hS p q Z) b).1,
      w ≫ strictTransformToAmbient B S hS p q b Z = v' ∧
      w ≫ (strictTransformPullbackToSource B S hS
          (closedSubspaceFirst B S hS p q Z) b).hom = vZ ∧
      Subfunctor.range w ≤
        ((openComplementOfClosedSubspace B S hS X Zc).1.preimage
            (closedSubspaceFirst B S hS p q Z).hom).preimage
          (strictTransformPullbackToSource B S hS (closedSubspaceFirst B S hS p q Z) b).hom := by
  set w := (isPullback_strictTransformToAmbient B S hS p q b Z).lift v' vZ
    (hv'.trans hvZ.symm) with hwdef
  have hw1 : w ≫ strictTransformToAmbient B S hS p q b Z = v' :=
    (isPullback_strictTransformToAmbient B S hS p q b Z).lift_fst _ _ _
  have hw2 : w ≫ (strictTransformPullbackToSource B S hS
      (closedSubspaceFirst B S hS p q Z) b).hom = vZ :=
    (isPullback_strictTransformToAmbient B S hS p q b Z).lift_snd _ _ _
  refine ⟨w, hw1, hw2, ?_⟩
  -- The image of `w` avoids the centre.
  have hwfac : (w ≫ (strictTransformPullbackToSource B S hS
          (closedSubspaceFirst B S hS p q Z) b).hom) ≫
        (closedSubspaceFirst B S hS p q Z).hom =
      v.hom ≫ (fiberProductFirst B S hS p q).hom := by
    rw [hw2, show (closedSubspaceFirst B S hS p q Z).hom =
      Z.1.ι ≫ (fiberProductFirst B S hS p q).hom from rfl, ← Category.assoc, hvZ]
  have hCoOpen := isOpenSubspace_preimage_preimage_openComplement B S hS
    (closedSubspaceFirst B S hS p q Z) b Zc
  have hpts : Set.range (pointsMap B S hS V.1 w) ⊆
      subspacePointSet B S hS
        (strictTransformPullback B S hS (closedSubspaceFirst B S hS p q Z) b).1
        (((openComplementOfClosedSubspace B S hS X Zc).1.preimage
            (closedSubspaceFirst B S hS p q Z).hom).preimage
          (strictTransformPullbackToSource B S hS
            (closedSubspaceFirst B S hS p q Z) b).hom) := by
    rw [subspacePointSet_preimage_openComplement_eq_compl_exceptionalPreimageSet B S hS
        (closedSubspaceFirst B S hS p q Z) b Zc,
      exceptionalPreimageSet_eq_preimage_centre B S hS
        (closedSubspaceFirst B S hS p q Z) b Zc]
    rintro x ⟨y, rfl⟩
    intro hmem
    rw [Set.mem_preimage, ← pointsMap_comp_apply, ← Category.assoc, hwfac] at hmem
    exact Set.disjoint_left.1 hdisj
      ⟨pointsMap B S hS V.1
          (Subfunctor.lift (v.hom ≫ (fiberProductFirst B S hS p q).hom) hvU) y,
        by rw [← pointsMap_comp_apply, Subfunctor.lift_ι]⟩ hmem
  obtain ⟨k, hk⟩ := (factorsThrough_openSubspace_iff_points B S hS
    (strictTransformPullback B S hS (closedSubspaceFirst B S hS p q Z) b).2 V.2 _
    hCoOpen w).2 hpts
  rw [← hk]
  exact (Subfunctor.range_comp_le _ _).trans (Subfunctor.range_ι _).le

/-- **The lift of `V` factors through the strict transform.**  In the setting of Stacks 0F49, with
`b : X' ⟶ X` the blowup of `X` in a closed subspace `Zc` disjoint from `U`, the image of the lift
`v' : V ⟶ (X ×_T Y) ×_X X'` lies in the strict transform of the scheme-theoretic image `Z` of `v`.

This is the morphism `V ⟶ Z'` that the source uses without comment, and it is the content of
Stacks 085T part (1) that the argument needs: the lift of `V` to `Z ×_X X'`
(`AlgebraicGeometry.Space.exists_lift_strictTransformPullback`) lands over the complement of the
centre, and over that complement nothing is cut away by the strict transform
(`AlgebraicGeometry.Space.preimage_openComplement_le_strictTransform_of_isBlowupAlong`). -/
theorem range_le_strictTransformInAmbient (p : X ⟶ T) (q : Y ⟶ T)
    (U : OpenSubspaces B S hS X.1) (Zc : ClosedSubspaces B S hS X.1) (b : X' ⟶ X)
    (hdisj : Disjoint (subspacePointSet B S hS X.1 U.1)
      (subspacePointSet B S hS X.1 Zc.1))
    (hbl : IsBlowupAlong B S hS Zc b)
    (v : V ⟶ AlgebraicSpaces.fiberProduct B S hS p q)
    (v' : V.1 ⟶ (strictTransformPullback B S hS (fiberProductFirst B S hS p q) b).1)
    (hv' : v' ≫ pullback.fst (fiberProductFirst B S hS p q).hom b.hom = v.hom)
    (hvU : Subfunctor.range (v.hom ≫ (fiberProductFirst B S hS p q).hom) ≤ U.1) :
    Subfunctor.range v' ≤ strictTransformInAmbient B S hS p q b Zc
      (schemeTheoreticImage B S hS v.hom
        (AlgebraicSpaces.fiberProduct B S hS p q).property) := by
  obtain ⟨w, hw1, -, hw3⟩ := exists_lift_strictTransformPullback B S hS p q U Zc b hdisj
    (schemeTheoreticImage B S hS v.hom (AlgebraicSpaces.fiberProduct B S hS p q).property) v
    (toSchemeTheoreticImage B S hS v.hom) (toSchemeTheoreticImage_ι B S hS v.hom) v' hv' hvU
  have hle := hw3.trans (preimage_openComplement_le_strictTransform_of_isBlowupAlong B S hS
    (closedSubspaceFirst B S hS p q (schemeTheoreticImage B S hS v.hom
      (AlgebraicSpaces.fiberProduct B S hS p q).property)) b Zc hbl)
  rw [← hw1, Subfunctor.range_comp, strictTransformInAmbient, Subfunctor.range_comp,
    Subfunctor.range_ι]
  exact (Subfunctor.image_le_iff _ _ _).2 (hle.trans ((Subfunctor.image_le_iff _ _ _).1 le_rfl))

/-- **Steps (4) and (5) of the source's proof of Stacks 0F49: the reverse inclusion.**  In the
setting of Stacks 0F49, with `v` and its lift `v'` quasi-compact, the strict transform of the
scheme-theoretic image `Z` of `v` is **contained in** the scheme-theoretic image of `v'`.

Write `Z'` for the strict transform, a closed subspace of `Z ×_X X'`, and `w : V ⟶ Z ×_X X'` for
the lift of `AlgebraicGeometry.Space.exists_lift_strictTransformPullback`, which is quasi-compact
because `AlgebraicGeometry.Space.strictTransformToAmbient` is a monomorphism, hence separated,
hence quasi-separated, so that Stacks 03KS applies to `w ≫ j = v'`.

Step (4) is that `V` is scheme-theoretically dense in the part `Co` of `Z ×_X X'` lying over the
complement of the centre: that part is isomorphic, over `Z`, to the part of `Z` lying over the
complement of the centre — the blowup is an isomorphism there by Stacks 085T part (1), and
`CategoryTheory.Subfunctor.isIso_fromPreimage_preimage_of_isPullback` transports this through the
cartesian square — and in that part of `Z` the morphism `V ⟶ Z` has full scheme-theoretic image, by
part (3) of Stacks 082Z in the form `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_lift`
and the fullness of the image of `V` in `Z` itself.

Step (5) is the ideal computation.  Density in `Co` makes every local function killed by `w`
supported on the exceptional preimage,
`AlgebraicGeometry.Space.kernelIdealSheaf_le_supportedSectionsSubmodule`; for a quasi-compact
morphism that kernel is the defining ideal of the scheme-theoretic image of `w`, part (2) of
Stacks 082Z; and the ideal of sections supported on the exceptional preimage is the defining
ideal of `Z'`, which is the content of
`AlgebraicGeometry.Space.definingIdealSheaf_strictTransform_of_isBlowupAlong` — this is where
"there are no nonzero sections of `𝒪_{Z'}` supported on `E`" enters, in its ideal-theoretic form.
So the defining ideal of the scheme-theoretic image of `w` is inside that of `Z'`, and the
injectivity half of Stacks 03MB reverses the inclusion: `Z' ⊆` the scheme-theoretic image of `w`.
Pushing that forward along `j` gives the assertion, the scheme-theoretic image of `w` mapping into
that of `v' = w ≫ j`. -/
theorem strictTransformInAmbient_le_schemeTheoreticImageSubfunctor (p : X ⟶ T) (q : Y ⟶ T)
    (U : OpenSubspaces B S hS X.1) (Zc : ClosedSubspaces B S hS X.1) (b : X' ⟶ X)
    (hdisj : Disjoint (subspacePointSet B S hS X.1 U.1)
      (subspacePointSet B S hS X.1 Zc.1))
    (hbl : IsBlowupAlong B S hS Zc b)
    (v : V ⟶ AlgebraicSpaces.fiberProduct B S hS p q) (hv : IsQuasiCompact B S hS v.hom)
    (v' : V.1 ⟶ (strictTransformPullback B S hS (fiberProductFirst B S hS p q) b).1)
    (hv' : v' ≫ pullback.fst (fiberProductFirst B S hS p q).hom b.hom = v.hom)
    (hqc' : IsQuasiCompact B S hS v')
    (hvU : Subfunctor.range (v.hom ≫ (fiberProductFirst B S hS p q).hom) ≤ U.1) :
    strictTransformInAmbient B S hS p q b Zc
        (schemeTheoreticImage B S hS v.hom
          (AlgebraicSpaces.fiberProduct B S hS p q).property) ≤
      schemeTheoreticImageSubfunctor B S hS v' := by
  set Zs := schemeTheoreticImage B S hS v.hom
    (AlgebraicSpaces.fiberProduct B S hS p q).property with hZs
  -- The factorization of `v` through its scheme-theoretic image, with the three properties of it
  -- that the argument uses; naming it keeps every subfunctor below over one and the same space.
  obtain ⟨vZ, hvZι, hvZtop, hvZqc⟩ :
      ∃ vZ : V.1 ⟶ (closedSubspaceSpace B S hS
          (AlgebraicSpaces.fiberProduct B S hS p q) Zs).1,
        vZ ≫ Zs.1.ι = v.hom ∧ schemeTheoreticImageSubfunctor B S hS vZ = ⊤ ∧
          IsQuasiCompact B S hS vZ := by
    refine ⟨toSchemeTheoreticImage B S hS v.hom, toSchemeTheoreticImage_ι B S hS v.hom,
      schemeTheoreticImageSubfunctor_toSchemeTheoreticImage_eq_top B S hS v.hom
        (AlgebraicSpaces.fiberProduct B S hS p q).2,
      isQuasiCompact_of_comp_of_isQuasiSeparated B S hS _ Zs.1.ι V.2
        (AlgebraicSpaces.fiberProduct B S hS p q).2 hv
        (isQuasiSeparated_of_mono B S hS _ inferInstance)⟩
  obtain ⟨w, hw1, hw2, hw3⟩ := exists_lift_strictTransformPullback B S hS p q U Zc b hdisj Zs v
    vZ hvZι v' hv' hvU
  -- `w` is quasi-compact, by Stacks 03KS.
  have : Mono (strictTransformToAmbient B S hS p q b Zs) :=
    (isPullback_strictTransformToAmbient B S hS p q b Zs).mono_fst_of_mono
  have hwqc : IsQuasiCompact B S hS w :=
    isQuasiCompact_of_comp_of_isQuasiSeparated B S hS w
      (strictTransformToAmbient B S hS p q b Zs) V.2
      (strictTransformPullback B S hS (fiberProductFirst B S hS p q) b).2
      (by rw [hw1]; exact hqc')
      (isQuasiSeparated_of_mono B S hS _ inferInstance)
  have hliftqc : IsQuasiCompact B S hS (Subfunctor.lift w hw3) :=
    isQuasiCompact_of_comp_of_isQuasiSeparated B S hS (Subfunctor.lift w hw3)
      (((openComplementOfClosedSubspace B S hS X Zc).1.preimage
          (closedSubspaceFirst B S hS p q Zs).hom).preimage
        (strictTransformPullbackToSource B S hS
          (closedSubspaceFirst B S hS p q Zs) b).hom).ι V.2
      (strictTransformPullback B S hS (closedSubspaceFirst B S hS p q Zs) b).2 hwqc
      (isQuasiSeparated_of_mono B S hS _ inferInstance)
  have hCoOpen := isOpenSubspace_preimage_preimage_openComplement B S hS
    (closedSubspaceFirst B S hS p q Zs) b Zc
  have hΩzOpen : IsOpenSubspace B S hS
      ((openComplementOfClosedSubspace B S hS X Zc).1.preimage
        (closedSubspaceFirst B S hS p q Zs).hom) :=
    isOpenSubspace_preimage B S hS _ _ X.2
      (closedSubspaceSpace B S hS (AlgebraicSpaces.fiberProduct B S hS p q) Zs).2
      (openComplementOfClosedSubspace B S hS X Zc).2
  -- Step (4): `V` is scheme-theoretically dense over the complement of the centre.
  have hrangeΩ : Subfunctor.range vZ ≤
      (openComplementOfClosedSubspace B S hS X Zc).1.preimage
        (closedSubspaceFirst B S hS p q Zs).hom := by
    rw [← hw2, Subfunctor.range_comp]
    exact (Subfunctor.image_le_iff _ _ _).2 hw3
  have htopΩ : schemeTheoreticImageSubfunctor B S hS (Subfunctor.lift vZ hrangeΩ) = ⊤ := by
    rw [schemeTheoreticImageSubfunctor_lift B S hS V.2
        (closedSubspaceSpace B S hS (AlgebraicSpaces.fiberProduct B S hS p q) Zs).2
        vZ hvZqc _ hΩzOpen hrangeΩ, hvZtop]
    exact (Subfunctor.preimage_eq_top_iff _ _).2 le_top
  have hψ : Subfunctor.lift w hw3 ≫
      ((openComplementOfClosedSubspace B S hS X Zc).1.preimage
          (closedSubspaceFirst B S hS p q Zs).hom).fromPreimage
        (strictTransformPullbackToSource B S hS (closedSubspaceFirst B S hS p q Zs) b).hom =
      Subfunctor.lift vZ hrangeΩ := by
    refine (cancel_mono ((openComplementOfClosedSubspace B S hS X Zc).1.preimage
      (closedSubspaceFirst B S hS p q Zs).hom).ι).1 ?_
    rw [Subfunctor.lift_ι, Category.assoc, Subfunctor.fromPreimage_ι, ← Category.assoc,
      Subfunctor.lift_ι, hw2]
  have htop : schemeTheoreticImageSubfunctor B S hS (Subfunctor.lift w hw3) = ⊤ :=
    schemeTheoreticImageSubfunctor_eq_top_of_comp_isIso B S hS hCoOpen.1 hΩzOpen.1
      (Subfunctor.lift w hw3)
      (((openComplementOfClosedSubspace B S hS X Zc).1.preimage
          (closedSubspaceFirst B S hS p q Zs).hom).fromPreimage
        (strictTransformPullbackToSource B S hS (closedSubspaceFirst B S hS p q Zs) b).hom)
      (Subfunctor.isIso_fromPreimage_preimage_of_isPullback
        (IsPullback.of_hasPullback (closedSubspaceFirst B S hS p q Zs).hom b.hom)
        (openComplementOfClosedSubspace B S hS X Zc).1
        (isIso_fromPreimage_openComplement hbl))
      (by rw [hψ]; exact htopΩ)
  -- Step (5): the ideal computation.
  have hTclosed : IsClosed (exceptionalPreimageSet B S hS
      (closedSubspaceFirst B S hS p q Zs) b (Zc.1.preimage b.hom)) :=
    isClosed_range_pointsMap_of_isClosedImmersion B S hS
      (strictTransformPullback B S hS (closedSubspaceFirst B S hS p q Zs) b).2 _
      (exceptionalPreimage_isClosedSubspace B S hS (closedSubspaceFirst B S hS p q Zs) b
        (Zc.1.preimage b.hom)
        (isClosedSubspace_preimage B S hS b.hom Zc.1 X.2 X'.2 Zc.2)).2
  have hker := kernelIdealSheaf_le_supportedSectionsSubmodule B S hS
    (exceptionalPreimageSet B S hS (closedSubspaceFirst B S hS p q Zs) b
      (Zc.1.preimage b.hom)) hTclosed _ hCoOpen
    (subspacePointSet_preimage_openComplement_eq_compl_exceptionalPreimageSet B S hS
      (closedSubspaceFirst B S hS p q Zs) b Zc)
    (ObjectProperty.homMk w :
      V ⟶ strictTransformPullback B S hS (closedSubspaceFirst B S hS p q Zs) b)
    hw3 hliftqc htop
  have hid : definingIdealSheaf B S hS
      (strictTransformPullback B S hS (closedSubspaceFirst B S hS p q Zs) b)
      (strictTransform B S hS (closedSubspaceFirst B S hS p q Zs) b
        (Zc.1.preimage b.hom)) =
      strictTransformIdealSubmodule B S hS (closedSubspaceFirst B S hS p q Zs) b
        (Zc.1.preimage b.hom) :=
    definingIdealSheaf_strictTransform_of_isBlowupAlong B S hS
      (closedSubspaceFirst B S hS p q Zs) b Zc hbl
  have himg := definingIdealSheaf_schemeTheoreticImage_eq_kernelIdealSheaf B S hS
    (ObjectProperty.homMk w :
      V ⟶ strictTransformPullback B S hS (closedSubspaceFirst B S hS p q Zs) b) hwqc
  have hZple : (strictTransform B S hS (closedSubspaceFirst B S hS p q Zs) b
      (Zc.1.preimage b.hom)).1 ≤ schemeTheoreticImageSubfunctor B S hS w := by
    refine le_of_forall_definingIdealAt_le B S hS
      (strictTransformPullback B S hS (closedSubspaceFirst B S hS p q Zs) b)
      (strictTransform B S hS (closedSubspaceFirst B S hS p q Zs) b (Zc.1.preimage b.hom))
      (schemeTheoreticImage B S hS w
        (strictTransformPullback B S hS (closedSubspaceFirst B S hS p q Zs) b).2) fun Uc _ => ?_
    have h1 : definingIdealAt B S hS
          (strictTransformPullback B S hS (closedSubspaceFirst B S hS p q Zs) b)
          (schemeTheoreticImage B S hS w
            (strictTransformPullback B S hS (closedSubspaceFirst B S hS p q Zs) b).2)
          (op Uc) =
        (kernelIdealSheaf B S hS (ObjectProperty.homMk w :
          V ⟶ strictTransformPullback B S hS
            (closedSubspaceFirst B S hS p q Zs) b)).obj (op Uc) :=
      congrArg (fun N : (SheafOfModules.unit (structureRingSheaf B S hS
        (strictTransformPullback B S hS
          (closedSubspaceFirst B S hS p q Zs) b))).Submodule => N.obj (op Uc)) himg
    have h2 : definingIdealAt B S hS
          (strictTransformPullback B S hS (closedSubspaceFirst B S hS p q Zs) b)
          (strictTransform B S hS (closedSubspaceFirst B S hS p q Zs) b
            (Zc.1.preimage b.hom)) (op Uc) =
        (strictTransformIdealSubmodule B S hS (closedSubspaceFirst B S hS p q Zs) b
          (Zc.1.preimage b.hom)).obj (op Uc) :=
      congrArg (fun N : (SheafOfModules.unit (structureRingSheaf B S hS
        (strictTransformPullback B S hS
          (closedSubspaceFirst B S hS p q Zs) b))).Submodule => N.obj (op Uc)) hid
    exact h1.le.trans ((hker (op Uc)).trans h2.ge)
  show Subfunctor.range ((strictTransform B S hS (closedSubspaceFirst B S hS p q Zs) b
    (Zc.1.preimage b.hom)).1.ι ≫ strictTransformToAmbient B S hS p q b Zs) ≤ _
  rw [Subfunctor.range_comp, Subfunctor.range_ι, Subfunctor.image_le_iff]
  exact hZple.trans (schemeTheoreticImageSubfunctor_le_preimage B S hS
    (strictTransformPullback B S hS (closedSubspaceFirst B S hS p q Zs) b).2
    (strictTransformPullback B S hS (fiberProductFirst B S hS p q) b).2
    (by rw [Category.id_comp]; exact hw1))

/-- **One inclusion of Stacks 0F49.**  Let `X ⟶ T` and `Y ⟶ T` be morphisms of algebraic spaces
over `S`, let `U ⊆ X` be an open subspace, let `v : V ⟶ X ×_T Y` be a morphism whose composite
with the first projection factors through `U`, and let `Z` be the scheme-theoretic image of `v`.
Let `b : X' ⟶ X` be the blowup of `X` in a closed subspace `Zc` whose points are disjoint from
those of `U` — for a centre of finite presentation, a `U`-admissible blowup of Stacks 086B.  Then
the scheme-theoretic image of the lift `v' : V ⟶ X' ×_T Y` is **contained in** the strict
transform of `Z` with respect to `b`.

Here `X' ×_T Y` is spelled `(X ×_T Y) ×_X X'`, the strict transform of Stacks 0862 is taken of
`Z` viewed as an algebraic space over `X`, and its image in the ambient space is
`AlgebraicGeometry.Space.strictTransformInAmbient`.

This is the inclusion of the scheme-theoretic image in the strict transform, and only that; the
equality that Stacks 0F49 asserts, and which carries the tag, is
`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_eq_strictTransformInAmbient_unconditional`.

The inclusion is the minimality of the scheme-theoretic image, Stacks 082X in the form
`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_le`: the strict transform is a closed
subspace (`AlgebraicGeometry.Space.isClosedSubspace_strictTransformInAmbient`, which is step (1)
of the source's proof) through which the lift factors
(`AlgebraicGeometry.Space.range_le_strictTransformInAmbient`, which is the use the source makes of
Stacks 085T part (1)).  Quasi-compactness of `v` is not needed for this half and so is not
carried; the source uses it only in the reverse inclusion. -/
theorem schemeTheoreticImageSubfunctor_le_strictTransformInAmbient_of_lift (p : X ⟶ T) (q : Y ⟶ T)
    (U : OpenSubspaces B S hS X.1) (Zc : ClosedSubspaces B S hS X.1) (b : X' ⟶ X)
    (hdisj : Disjoint (subspacePointSet B S hS X.1 U.1)
      (subspacePointSet B S hS X.1 Zc.1))
    (hbl : IsBlowupAlong B S hS Zc b)
    (v : V ⟶ AlgebraicSpaces.fiberProduct B S hS p q)
    (v' : V.1 ⟶ (strictTransformPullback B S hS (fiberProductFirst B S hS p q) b).1)
    (hv' : v' ≫ pullback.fst (fiberProductFirst B S hS p q).hom b.hom = v.hom)
    (hvU : Subfunctor.range (v.hom ≫ (fiberProductFirst B S hS p q).hom) ≤ U.1) :
    schemeTheoreticImageSubfunctor B S hS v' ≤
      strictTransformInAmbient B S hS p q b Zc
        (schemeTheoreticImage B S hS v.hom
          (AlgebraicSpaces.fiberProduct B S hS p q).property) :=
  schemeTheoreticImageSubfunctor_le B S hS v'
    (isClosedSubspace_strictTransformInAmbient B S hS p q b Zc
      (schemeTheoreticImage B S hS v.hom (AlgebraicSpaces.fiberProduct B S hS p q).property))
    (range_le_strictTransformInAmbient B S hS p q U Zc b hdisj hbl v v' hv' hvU)

/-- **Stacks 0F49.**  Let
`X ⟶ T` and `Y ⟶ T` be
morphisms of algebraic spaces over `S`, let `U ⊆ X` be an open subspace, let `v : V ⟶ X ×_T Y` be
a *quasi-compact* morphism whose composite with the first projection factors through `U`, and let
`Z` be the scheme-theoretic image of `v`.  Let `b : X' ⟶ X` be a `U`-admissible blowup, that is,
the blowup of `X` in a closed subspace `Zc` of finite presentation whose points are disjoint from
those of `U`.  Then the scheme-theoretic image of the lift `v' : V ⟶ X' ×_T Y` **equals** the
strict transform of `Z` with respect to `b`.

This is the assertion of Stacks 0F49.  Both inclusions are proved:

* `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_le_strictTransformInAmbient_of_lift`
  is steps (1) and (2) of the source's proof — the strict transform is a closed subspace of
  `X' ×_T Y` through which the lift factors;
* `AlgebraicGeometry.Space.strictTransformInAmbient_le_schemeTheoreticImageSubfunctor` is steps
  (4) and (5) — `V` is scheme-theoretically dense in the part of `Z ×_X X'` lying over the
  complement of the centre, by part (3) of Stacks 082Z, and the strict transform is cut out by
  the ideal of sections supported on the exceptional divisor, which is the ideal-theoretic form
  of "there are no nonzero sections of `𝒪_{Z'}` supported on `E`".

Step (3) of the source's proof, the quasi-compactness of the lift, is supplied by
`AlgebraicGeometry.Space.isQuasiCompact_of_comp_fiberProductFirst_unconditional`, which needs
the properness of the admissible blowup, Stacks 085Z.  That is now *proved*, in
`AlgebraicGeometry.Space.isProper_of_isBlowupAlong_of_isFinitePresentation`, and carries no side
condition, so **nothing is assumed here beyond the source's own hypotheses**.  In particular the density
statement, part of the tag's own conclusion, is the theorem
`AlgebraicGeometry.Space.strictTransformInAmbient_le_schemeTheoreticImageSubfunctor`, and neither
the existence of a proper blowup nor a surjective étale chart of `X` with the size conditions of
Stacks 085Q is assumed. -/
@[stacks 0F49 "the equality of the scheme-theoretic image of the lift with the strict \
transform, at the source's hypotheses and with NO side condition and no part of the conclusion \
assumed. The properness of the admissible blowup, Stacks 085Z, is proved rather than assumed, by \
AlgebraicGeometry.Space.isProper_of_isBlowupAlong_of_isFinitePresentation, which itself carries \
no side condition"]
theorem schemeTheoreticImageSubfunctor_eq_strictTransformInAmbient_unconditional
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)] (p : X ⟶ T) (q : Y ⟶ T)
    (U : OpenSubspaces B S hS X.1) (Zc : ClosedSubspaces B S hS X.1) (b : X' ⟶ X)
    (hfp : IsFinitePresentation B S hS Zc.1.ι)
    (hdisj : Disjoint (subspacePointSet B S hS X.1 U.1)
      (subspacePointSet B S hS X.1 Zc.1))
    (hbl : IsBlowupAlong B S hS Zc b)
    (v : V ⟶ AlgebraicSpaces.fiberProduct B S hS p q)
    (hv : IsQuasiCompact B S hS v.hom)
    (v' : V.1 ⟶ (strictTransformPullback B S hS (fiberProductFirst B S hS p q) b).1)
    (hv' : v' ≫ pullback.fst (fiberProductFirst B S hS p q).hom b.hom = v.hom)
    (hvU : Subfunctor.range (v.hom ≫ (fiberProductFirst B S hS p q).hom) ≤ U.1) :
    schemeTheoreticImageSubfunctor B S hS v' =
      strictTransformInAmbient B S hS p q b Zc
        (schemeTheoreticImage B S hS v.hom
          (AlgebraicSpaces.fiberProduct B S hS p q).property) := by
  have hadm : IsAdmissibleBlowup B S hS U b :=
    isAdmissibleBlowup_of_isBlowupAlong hfp hdisj hbl
  have hqc : IsQuasiCompact B S hS v' :=
    isQuasiCompact_of_comp_fiberProductFirst_unconditional B S hS p q U b hadm v'
      (by rw [hv']; exact hv)
  exact le_antisymm
    (schemeTheoreticImageSubfunctor_le_strictTransformInAmbient_of_lift B S hS p q U Zc b hdisj hbl
      v v' hv' hvU)
    (strictTransformInAmbient_le_schemeTheoreticImageSubfunctor B S hS p q U Zc b hdisj hbl
      v hv v' hv' hqc hvU)

end Image

end AlgebraicGeometry.Space

end
