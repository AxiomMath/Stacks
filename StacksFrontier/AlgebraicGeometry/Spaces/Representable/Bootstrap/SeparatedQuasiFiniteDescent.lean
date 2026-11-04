module

public import StacksCore.CategoryTheory.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.SurjectiveFlatDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Descending separatedness and local quasi-finiteness along a flat cover of sheaves

Let `S` be a scheme contained in a big fppf site `B` and let

```
E --a--> F
|        |
f        g
↓        ↓
H --b--> G
```

be a cartesian square of presheaves on the big fppf site of `S`.  If the right-hand column
`g` is representable by algebraic spaces, surjective, flat and locally of finite
presentation, then the two scheme-valued base changes of `b` and of `a` differ by an fppf
covering: the base change of `g` along a scheme-valued point of `G` is an fppf covering
family of that point, and over it the base change of `b` becomes a base change of `a`.  Any
property of morphisms of algebraic spaces over `S` which is local on the base for the fppf
topology therefore passes from `a` to `b`.

Applied to separatedness and local quasi-finiteness this is the content of **Stacks 046J**,
whose conclusion is moreover that `b` is representable *by schemes*.  That half is effective
descent of schemes along the fppf covering the right-hand column provides: each base change of
`a` is a separated, locally quasi-finite algebraic space over a scheme, hence a scheme by
Stacks 03XX, and Stacks 02W8 descends the family to a scheme over the base.

## Main results

* `AlgebraicGeometry.Space.hasProperty_of_isPullback_of_fppfCover`: the descent of an
  fppf-local property from `a` to `b`, given that `b` is representable by algebraic spaces.
* `AlgebraicGeometry.Space.relativelyRepresentable_of_hasProperty_separated_locallyQuasiFinite`:
  a morphism of presheaves representable by algebraic spaces which is separated and locally
  quasi-finite is representable by objects of the site.  This is Stacks 03XX read on a
  morphism of presheaves.
* `AlgebraicGeometry.Space.relativelyRepresentable_of_isPullback_of_flat_surjective`: the
  bottom row `b` of the square is representable by objects of the site, unconditionally.
* `AlgebraicGeometry.Space.IsRepresentabilityDescentAlongFlatSurjection` is the statement of
  Stacks 0AMP, taken as an input by the declarations below that need it.
* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_of_isPullback_of_descent`
  deduces representability of `b` by algebraic spaces from it.
* `AlgebraicGeometry.Space.relativelyRepresentable_separated_locallyQuasiFinite_of_isPullback`
  is **Stacks 046J**.
* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_of_comp_of_flat_surjective` is
  **Stacks 0AMP**, deduced from the bootstrap theorem Stacks 04S6 part (3), which it takes as
  the input `AlgebraicGeometry.Space.IsBootstrapAlgebraicSpaceAlongFlatSurjection`.
* `AlgebraicGeometry.Space.isRepresentabilityDescentAlongFlatSurjection_of_bootstrap`
  discharges the Stacks 0AMP hypothesis above from that same bootstrap theorem.
* `AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection_iff`: the two
  statements are equivalent, so assuming Stacks 0AMP is assuming Stacks 04S6 part (3).

## Implementation notes

The hypotheses on `g` and on `a` are read through
`AlgebraicGeometry.Space.HasProperty`, which is the definition of Stacks 03YK: a morphism of
presheaves representable by algebraic spaces has a property of morphisms of algebraic spaces
when every base change of it along a scheme-valued point of its target has that property.
Surjectivity of `g` is therefore the surjectivity of each of those base changes, not
surjectivity of `g` as a map of presheaves; the two agree for a morphism representable by
algebraic spaces, but the former is what Stacks 03YK says and what the covering condition of
Stacks 03Y8 consumes verbatim.

Representability of `b` is obtained the way the source obtains it, by effective descent of
schemes along the one-member fppf covering `{F → G}`, and so needs no bootstrap theorem.  The
descent input is `isEffectiveDescentAlongSurjectiveFlat_isSeparated_inf_locallyQuasiFinite_inf_lft`
in this namespace, Stacks 02W8 at its own property along a single surjective flat chart of the
site, which this library proves unconditionally; the reduction to a single chart is the scheme
atlas of the algebraic space `h_{a₀} ×_G F`, exactly the source's `U → F`.

The two locality inputs are both available.  Separatedness is fppf local on the base by Stacks
0421, `AlgebraicGeometry.Space.separated_isLocalAtTarget_fpqc` read at the fppf precoverage
through `AlgebraicGeometry.fppfPrecoverage_le_fpqcPrecoverage`, and local quasi-finiteness by
Stacks 0427, `AlgebraicGeometry.Space.isLocallyQuasiFinite_isLocalAtTarget_fppf`.  So Stacks
046J is proved here with exactly the hypotheses of the source.

Stacks 0AMP is a different matter.  Its source proof is an appeal to the bootstrap theorem
Stacks 04S6 part (3), and it is equivalent to that condition rather than weaker than it: read
over the terminal object of the site, "`b` is representable by algebraic spaces" for the
structure morphism of a sheaf says that the sheaf is an algebraic space.  So
`AlgebraicGeometry.Space.IsRepresentabilityDescentAlongFlatSurjection` remains a hypothesis,
discharged only by `AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection_iff`.

Local quasi-finiteness needs no hypothesis at all: Stacks 0427 is available at the fppf
precoverage as `AlgebraicGeometry.Space.isLocallyQuasiFinite_isLocalAtTarget_fppf`, so
`AlgebraicGeometry.Space.hasProperty_of_isPullback_of_fppfCover` specialised to local
quasi-finiteness is unconditional.

The witness of representability of `b` appears in the type of
`AlgebraicGeometry.Space.HasProperty`, so the final statement quantifies over it
existentially rather than naming one; the objects of
`AlgebraicGeometry.Space.AlgebraicSpaces` carry their algebraicity in a `Prop` field, so the
proposition does not in fact depend on which witness is chosen.

## References

* [Stacks Project, Tag 046J](https://stacks.math.columbia.edu/tag/046J)
* [Stacks Project, Tag 03XX](https://stacks.math.columbia.edu/tag/03XX)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 0427](https://stacks.math.columbia.edu/tag/0427)
* [Stacks Project, Tag 0AMP](https://stacks.math.columbia.edu/tag/0AMP)
* [Stacks Project, Tag 0421](https://stacks.math.columbia.edu/tag/0421)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Flatness and local finite presentation as packaged properties -/

/-- Being flat (**Stacks 03ML**, part (1)), as a property of morphisms in the category of
algebraic spaces over `S`. -/
abbrev flatProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ φ => IsFlat B S hS φ.hom

/-- Being locally of finite presentation (**Stacks 03XR**), as a property of morphisms in the
category of algebraic spaces over `S`. -/
abbrev locallyOfFinitePresentationProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ φ => IsLocallyOfFinitePresentation B S hS φ.hom

/-- Flatness of a morphism of algebraic spaces over `S` is stable under base change,
registered at `AlgebraicGeometry.Space.flatProperty`.  This is
`AlgebraicGeometry.Space.isFlat_isStableUnderBaseChange`, **Stacks 03MO**. -/
instance flatProperty_isStableUnderBaseChange :
    (flatProperty B S hS).IsStableUnderBaseChange :=
  isFlat_isStableUnderBaseChange B S hS

/-- Local finite presentation of a morphism of algebraic spaces over `S` is stable under base
change, registered at `AlgebraicGeometry.Space.locallyOfFinitePresentationProperty`.  This is
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_isStableUnderBaseChange`, **Stacks
03XR**. -/
instance locallyOfFinitePresentationProperty_isStableUnderBaseChange :
    (locallyOfFinitePresentationProperty B S hS).IsStableUnderBaseChange :=
  isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS

/-! ### The fppf covering supplied by the right-hand column -/

/-- The base change of a morphism of presheaves which is representable by algebraic spaces,
surjective, flat and locally of finite presentation along a scheme-valued point `ξ` of its
target is a one-member fppf covering family of `yoneda.obj U` in the sense of Stacks 03Y8. -/
theorem isCovering_fppf_pullback_fst_of_isRepresentableByAlgebraicSpaces
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : F ⟶ G)
    (hgRep : IsRepresentableByAlgebraicSpaces B S hS g)
    (hgSurj : HasProperty B S hS (surjectiveMorphismProperty B S hS) g hgRep)
    (hgFlat : HasProperty B S hS (flatProperty B S hS) g hgRep)
    (hgLfp : HasProperty B S hS (locallyOfFinitePresentationProperty B S hS) g hgRep)
    (U : BigFppfOver B S hS) (ξ : yoneda.obj U ⟶ G) :
    Topology.IsCovering .fppf B S hS (I := PUnit.{v + 1})
      (Yi := fun _ => pullback ξ g) (g := fun _ => pullback.fst ξ g) := by
  refine ⟨isAlgebraicSpace_yoneda B S hS U, (fun _ => hgRep U ξ), ?_⟩
  refine { target_isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS U
           source_isAlgebraicSpace := fun _ => hgRep U ξ
           flat := fun _ => hgFlat U ξ
           locallyOfFinitePresentation := fun _ => hgLfp U ξ
           jointly_surjective := ?_ }
  rw [Set.eq_univ_iff_forall]
  intro x
  obtain ⟨y, hy⟩ := hgSurj U ξ x
  exact Set.mem_iUnion.mpr ⟨PUnit.unit, Set.mem_range.mpr ⟨y, hy⟩⟩

/-! ### Descending an fppf-local property across the square -/

/-- In a cartesian square of presheaves on the big fppf site of `S` whose right-hand column
`g` is representable by algebraic spaces, surjective, flat and locally of finite
presentation, a property `P` of morphisms of algebraic spaces over `S` which is local on the
base for the fppf topology passes from the top row `a` to the bottom row `b`, provided `b` is
representable by algebraic spaces.

At a scheme-valued point `ξ` of `G` the base change of `g` is a one-member fppf covering
family of `yoneda.obj U`, and the base change of `b` along `ξ`, pulled back along that
covering, is the base change of `a` along the induced algebraic-space-valued point of `F`.
Stacks 046F widens the test of `P` to algebraic-space-valued points, so `P` holds there, and
locality on the base carries it to the base change of `b` itself. -/
theorem hasProperty_of_isPullback_of_fppfCover
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Topology.fppf.precoverage.{u, v} B S hS)]
    {E F H G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : E ⟶ F) (f : E ⟶ H) (g : F ⟶ G) (b : H ⟶ G) (sq : IsPullback a f g b)
    (hgRep : IsRepresentableByAlgebraicSpaces B S hS g)
    (hgSurj : HasProperty B S hS (surjectiveMorphismProperty B S hS) g hgRep)
    (hgFlat : HasProperty B S hS (flatProperty B S hS) g hgRep)
    (hgLfp : HasProperty B S hS (locallyOfFinitePresentationProperty B S hS) g hgRep)
    (haRep : IsRepresentableByAlgebraicSpaces B S hS a)
    (hPa : HasProperty B S hS P a haRep)
    (hbRep : IsRepresentableByAlgebraicSpaces B S hS b) :
    HasProperty B S hS P b hbRep := by
  intro U ξ
  -- The two base changes of the square along `ξ`, as objects of the category of algebraic
  -- spaces over `S`.
  let UObj : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let XObj : AlgebraicSpaces B S hS := ⟨pullback ξ b, hbRep U ξ⟩
  let YObj : AlgebraicSpaces B S hS := ⟨pullback ξ g, hgRep U ξ⟩
  let q : XObj ⟶ UObj := ObjectProperty.homMk (pullback.fst ξ b)
  let cover : YObj ⟶ UObj := ObjectProperty.homMk (pullback.fst ξ g)
  let AObj : AlgebraicSpaces B S hS :=
    ⟨pullback (pullback.snd ξ g) a, isAlgebraicSpace_pullback_of_isRepresentableByAlgebraicSpaces
      B S hS a (pullback.snd ξ g) haRep (hgRep U ξ)⟩
  let s : AObj ⟶ YObj := ObjectProperty.homMk (pullback.fst (pullback.snd ξ g) a)
  -- `P` holds for the base change of `a` along the algebraic-space-valued point
  -- `pullback.snd ξ g` of `F`, by Stacks 046F.
  have hA : P s :=
    hasProperty_pullback_fst_of_isAlgebraicSpace B S hS P (hgRep U ξ) (pullback.snd ξ g) a
      haRep hPa
  -- That base change is the base change of `q` along the covering `cover`.
  have hbot : pullback.fst ξ g ≫ ξ = pullback.snd ξ g ≫ g := pullback.condition
  have hpaste : IsPullback (pullback.snd (pullback.snd ξ g) a ≫ f)
      (pullback.fst (pullback.snd ξ g) a) b (pullback.fst ξ g ≫ ξ) := by
    rw [hbot]
    exact IsPullback.paste_horiz
      (IsPullback.of_hasPullback (pullback.snd ξ g) a).flip sq.flip
  have hright : IsPullback (pullback.snd ξ b) (pullback.fst ξ b) b ξ :=
    (IsPullback.of_hasPullback ξ b).flip
  let kRaw : pullback (pullback.snd ξ g) a ⟶ pullback ξ b :=
    hright.lift (pullback.snd (pullback.snd ξ g) a ≫ f)
      (pullback.fst (pullback.snd ξ g) a ≫ pullback.fst ξ g)
      (by rw [hpaste.w, Category.assoc])
  let k : AObj ⟶ XObj := ObjectProperty.homMk kRaw
  have hSquare : IsPullback k s q cover := by
    apply IsPullback.of_map_of_faithful
      (ObjectProperty.ι (fun Z => IsAlgebraicSpace B S hS Z))
    exact IsPullback.of_right' hpaste hright
  -- Locality on the base finishes.
  have hcov : Topology.IsCovering .fppf B S hS (I := PUnit.{v + 1})
      (Yi := fun _ => pullback ξ g) (g := fun _ => pullback.fst ξ g) :=
    isCovering_fppf_pullback_fst_of_isRepresentableByAlgebraicSpaces B S hS g hgRep hgSurj
      hgFlat hgLfp U ξ
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd (P := P)
    (K := Topology.fppf.precoverage.{u, v} B S hS) (f := q)
    (R := Presieve.ofArrows (ι := PUnit.{v + 1}) (fun _ => YObj) (fun _ => cover))
    ⟨PUnit.{v + 1}, fun _ => YObj, fun _ => cover, rfl, hcov⟩
  intro Z w _ hw
  change Presieve.ofArrows (fun _ : PUnit.{v + 1} => YObj) (fun _ => cover) w at hw
  rcases hw with ⟨i⟩
  cases i
  exact (P.cancel_left_of_respectsIso hSquare.isoPullback.hom (pullback.snd q cover)).mp
    (by rw [hSquare.isoPullback_hom_snd]; exact hA)

/-! ### Representability by schemes -/

/-- **Stacks 03XX read on a morphism of presheaves.** A morphism of presheaves on the big
fppf site of `S` which is representable by algebraic spaces, separated and locally
quasi-finite is representable by objects of the site.

Each base change along a scheme-valued point of the target is a separated, locally
quasi-finite algebraic space over a representable algebraic space, hence representable. -/
theorem relativelyRepresentable_of_hasProperty_separated_locallyQuasiFinite
    {H G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (b : H ⟶ G)
    (hbRep : IsRepresentableByAlgebraicSpaces B S hS b)
    (hbSep : HasProperty B S hS (separatedProperty B S hS) b hbRep)
    (hbLqf : HasProperty B S hS (locallyQuasiFiniteProperty B S hS) b hbRep) :
    yoneda.relativelyRepresentable b := by
  refine (CategoryTheory.yoneda_relativelyRepresentable_iff_pullback_representable b).2
    fun U ξ => ?_
  exact isRepresentable_of_locallyQuasiFinite_separated B S hS
    (pullback (yonedaEquiv.symm ξ) b) (yoneda.obj U) (hbRep U (yonedaEquiv.symm ξ))
    (isAlgebraicSpace_yoneda B S hS U) (pullback.fst (yonedaEquiv.symm ξ) b) inferInstance
    (hbLqf U (yonedaEquiv.symm ξ)) (hbSep U (yonedaEquiv.symm ξ))

/-! ### Representability of the bottom row by fppf descent of schemes -/

/-- **Stacks 03XX in the form effective descent consumes it.** A separated, locally quasi-finite
morphism to a representable presheaf from an algebraic space over `S` is representable by objects
of the site, and the representing morphism of each represented base change is a separated,
locally quasi-finite morphism of schemes locally of finite type — the property of Stacks 02W8.

Representability is `relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated` in this
namespace; the three scheme-level properties are read off the base change by
`AlgebraicGeometry.Space.isSeparated_yoneda_map_iff` and
`AlgebraicGeometry.Space.isLocallyQuasiFinite_yoneda_map_iff`. -/
private theorem presheaf_sepLqfLft_of_isSeparated_of_isLocallyQuasiFinite
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {c : BigFppfOver B S hS}
    (hA : IsAlgebraicSpace B S hS A) (r : A ⟶ yoneda.obj c)
    (hsep : IsSeparated B S hS r) (hlqf : IsLocallyQuasiFinite B S hS r) :
    ((@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @AlgebraicGeometry.LocallyQuasiFinite.{u} ⊓
        @AlgebraicGeometry.LocallyOfFiniteType.{u} :
      MorphismProperty Scheme.{u}).inverseImage
      (BigFppfOver.toScheme B S hS)).presheaf r := by
  have hPbc : MorphismProperty.IsStableUnderBaseChange
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @AlgebraicGeometry.LocallyQuasiFinite.{u} ⊓
        @AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) :=
    isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_isStableUnderBaseChange.{u}
  have := isSeparated_respectsIso B S hS
  have hc : IsAlgebraicSpace B S hS (yoneda.obj c) := isAlgebraicSpace_yoneda B S hS c
  have hrep : yoneda.relativelyRepresentable r :=
    relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated B S hS r hA hc hlqf hsep
  refine MorphismProperty.relative.of_exists fun d ξ ↦ ?_
  have hq := (isLocallyQuasiFinite_yoneda_map_iff B S hS (hrep.snd ξ)).1
    (IsLocallyQuasiFinite.of_isPullback B S hS (hrep.isPullback ξ).flip hA hc hlqf)
  refine ⟨hrep.pullback ξ, hrep.fst ξ, hrep.snd ξ, hrep.isPullback ξ, ⟨⟨?_, hq.2⟩, hq.1⟩⟩
  refine (isSeparated_yoneda_map_iff B S hS (hrep.snd ξ)).1 ?_
  rw [← (hrep.isPullback ξ).isoPullback_hom_snd]
  exact MorphismProperty.RespectsIso.precomp (@Space.IsSeparated B S hS) _ _
    (isSeparated_pullback B S hS r ξ hsep)

/-- **In the cartesian square of Stacks 046J the bottom row `b` is representable by objects of
the site.**

This is the source's own argument, and it uses no bootstrap theorem.  Over a scheme-valued
point `η` of `G` the fibre product `h_{a₀} ×_G F` is an algebraic space, so it has a scheme
atlas `h_c`; the composite `q : c ⟶ a₀` of that atlas with the projection is surjective, flat
and locally of finite presentation, being the composite of an étale surjection with a base
change of `g` (**Stacks 046F**).  The base change of `b` along `yoneda.map q ≫ η` is the base
change of the top row `a` along `h_c ⟶ F`, hence — by **Stacks 03XX** — representable by
objects of the site, separated and locally quasi-finite over `h_c` and locally of finite type.
Effective fppf descent at that property along the single chart `q` — **Stacks 02W8**, as
`isEffectiveDescentAlongSurjectiveFlat_isSeparated_inf_locallyQuasiFinite_inf_lft` in this
namespace — therefore makes the base change of `b` along `η` representable, and
**Stacks 02YQ** assembles those into representability of `b`. -/
theorem relativelyRepresentable_of_isPullback_of_flat_surjective
    {E F H G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : E ⟶ F) (f : E ⟶ H) (g : F ⟶ G) (b : H ⟶ G) (sq : IsPullback a f g b)
    (hH : Presheaf.IsSheaf (BigFppfOver.topology B S hS) H)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (hgRep : IsRepresentableByAlgebraicSpaces B S hS g)
    (hgSurj : HasProperty B S hS (surjectiveMorphismProperty B S hS) g hgRep)
    (hgFlat : HasProperty B S hS (flatProperty B S hS) g hgRep)
    (hgLfp : HasProperty B S hS (locallyOfFinitePresentationProperty B S hS) g hgRep)
    (haRep : IsRepresentableByAlgebraicSpaces B S hS a)
    (haSep : HasProperty B S hS (separatedProperty B S hS) a haRep)
    (haLqf : HasProperty B S hS (locallyQuasiFiniteProperty B S hS) a haRep) :
    yoneda.relativelyRepresentable b := by
  have hPbc : MorphismProperty.IsStableUnderBaseChange
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @AlgebraicGeometry.LocallyQuasiFinite.{u} ⊓
        @AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) :=
    isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_isStableUnderBaseChange.{u}
  refine (MorphismProperty.presheaf_of_forall_presheaf_pullback_snd
    ((@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @AlgebraicGeometry.LocallyQuasiFinite.{u} ⊓
      @AlgebraicGeometry.LocallyOfFiniteType.{u} :
      MorphismProperty Scheme.{u}).inverseImage (BigFppfOver.toScheme B S hS))
    (f := b) ?_).rep
  intro a₀ η
  obtain ⟨c, u, hus, hue⟩ := (hgRep a₀ η).exists_atlas
  have hcS : IsAlgebraicSpace B S hS (yoneda.obj c) := isAlgebraicSpace_yoneda B S hS c
  have ha₀S : IsAlgebraicSpace B S hS (yoneda.obj a₀) := isAlgebraicSpace_yoneda B S hS a₀
  have hFg : IsAlgebraicSpace B S hS (pullback η g) := hgRep a₀ η
  have hueS : IsEtale B S hS u := (isEtale_iff_presheaf_of_yoneda B S hS u).2 hue
  have husS : IsSurjective B S hS u := isSurjective_of_presheafSurjective B S hS u hus
  have huf : IsFlat B S hS u :=
    holdsOnEveryEtaleChart_of_isEtale B S hS
      (@_root_.AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u})
      (fun _ h ↦ have := h; inferInstance) hFg hueS
  have hul : IsLocallyOfFinitePresentation B S hS u :=
    holdsOnEveryEtaleChart_of_isEtale B S hS
      (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      (fun _ h ↦ have := h; inferInstance) hFg hueS
  obtain ⟨q, hq⟩ : ∃ q : c ⟶ a₀, yoneda.map q = u ≫ pullback.fst η g :=
    ⟨yoneda.preimage (u ≫ pullback.fst η g), yoneda.map_preimage _⟩
  -- The chart `q` is surjective, flat and locally of finite presentation.
  have hqs : _root_.AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map q) := by
    refine ((surjective_yonedaMap_iff_surjective_pointsMap B S hS q).2 ?_).property
      (𝟙 (yoneda.obj a₀)) (𝟙 (yoneda.obj c)) q (IsPullback.of_horiz_isIso ⟨by simp⟩)
    change IsSurjective B S hS (yoneda.map q)
    rw [hq]
    exact isSurjective_comp B S hS husS (hgSurj a₀ η)
  have hqf : _root_.AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map q) := by
    refine (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      _root_.AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget q).1 ?_
    change IsFlat B S hS (yoneda.map q)
    rw [hq]
    exact isFlat_comp B S hS hcS hFg ha₀S u (pullback.fst η g) huf (hgFlat a₀ η)
  have hqp : _root_.AlgebraicGeometry.LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map q) := by
    refine (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      _root_.AlgebraicGeometry.LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget q).1 ?_
    change IsLocallyOfFinitePresentation B S hS (yoneda.map q)
    rw [hq]
    exact isLocallyOfFinitePresentation_comp B S hS hcS hFg ha₀S u (pullback.fst η g) hul
      (hgLfp a₀ η)
  -- The descent datum: the base change of the top row along the chart.
  have hwg : (u ≫ pullback.snd η g) ≫ g = yoneda.map q ≫ η := by
    rw [hq, Category.assoc, Category.assoc, pullback.condition]
  have hsqq : IsPullback (pullback.snd (u ≫ pullback.snd η g) a ≫ f)
      (pullback.fst (u ≫ pullback.snd η g) a) b (yoneda.map q ≫ η) := by
    rw [← hwg]
    exact IsPullback.paste_horiz
      (IsPullback.of_hasPullback (u ≫ pullback.snd η g) a).flip sq.flip
  exact isEffectiveDescentAlongSurjectiveFlat_isSeparated_inf_locallyQuasiFinite_inf_lft
    B S hS b hH hG η q hqs hqf hqp _ _ hsqq
    (presheaf_sepLqfLft_of_isSeparated_of_isLocallyQuasiFinite B S hS
      (haRep c (u ≫ pullback.snd η g)) (pullback.fst (u ≫ pullback.snd η g) a)
      (haSep c (u ≫ pullback.snd η g)) (haLqf c (u ≫ pullback.snd η g)))

/-! ### Stacks 046J -/

/-- The statement of **Stacks 0AMP**: representability by algebraic spaces descends along a
morphism of fppf sheaves which is representable by algebraic spaces, surjective, flat and
locally of finite presentation.

In the source this is a corollary of the bootstrap theorem Stacks 04S6, which this library
does not have, so it is taken as an input rather than proved.  The three properties of
the descending morphism are read through `AlgebraicGeometry.Space.HasProperty`, which is the
definition of Stacks 03YK. -/
abbrev IsRepresentabilityDescentAlongFlatSurjection : Prop :=
  ∀ {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H),
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) G →
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) H →
    ∀ ha : IsRepresentableByAlgebraicSpaces B S hS a,
      HasProperty B S hS (surjectiveMorphismProperty B S hS) a ha →
      HasProperty B S hS (flatProperty B S hS) a ha →
      HasProperty B S hS (locallyOfFinitePresentationProperty B S hS) a ha →
      IsRepresentableByAlgebraicSpaces B S hS (a ≫ b) →
      IsRepresentableByAlgebraicSpaces B S hS b

/-- In the cartesian square of Stacks 046J the bottom row `b` is representable by algebraic
spaces, from Stacks 0AMP as an input.

The left-hand column `f` is the base change of `g`, so it is representable by algebraic
spaces, surjective, flat and locally of finite presentation by Stacks 03Y0 and Stacks 046F,
and the composite `f ≫ b` is `a ≫ g`, representable by algebraic spaces by Stacks 03Y1.
Stacks 0AMP applied to `f` and `b` then gives the conclusion. -/
theorem isRepresentableByAlgebraicSpaces_of_isPullback_of_descent
    (hdescent : IsRepresentabilityDescentAlongFlatSurjection B S hS)
    {E F H G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : E ⟶ F) (f : E ⟶ H) (g : F ⟶ G) (b : H ⟶ G) (sq : IsPullback a f g b)
    (hH : Presheaf.IsSheaf (BigFppfOver.topology B S hS) H)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (hgRep : IsRepresentableByAlgebraicSpaces B S hS g)
    (hgSurj : HasProperty B S hS (surjectiveMorphismProperty B S hS) g hgRep)
    (hgFlat : HasProperty B S hS (flatProperty B S hS) g hgRep)
    (hgLfp : HasProperty B S hS (locallyOfFinitePresentationProperty B S hS) g hgRep)
    (haRep : IsRepresentableByAlgebraicSpaces B S hS a) :
    IsRepresentableByAlgebraicSpaces B S hS b := by
  have hfRep : IsRepresentableByAlgebraicSpaces B S hS f :=
    isRepresentableByAlgebraicSpaces_of_isPullback B S hS a f g b sq hgRep
  have hcomp : IsRepresentableByAlgebraicSpaces B S hS (f ≫ b) := by
    simpa only [sq.w] using isRepresentableByAlgebraicSpaces_comp B S hS a g haRep hgRep
  exact hdescent f b hH hG hfRep
    (hasProperty_of_isPullback B S hS (surjectiveMorphismProperty B S hS) a f g b sq hgRep hgSurj)
    (hasProperty_of_isPullback B S hS (flatProperty B S hS) a f g b sq hgRep hgFlat)
    (hasProperty_of_isPullback B S hS (locallyOfFinitePresentationProperty B S hS) a f g b sq
      hgRep hgLfp)
    hcomp

/-- **Stacks 046J**, conditional only on the fppf locality of separatedness.

In a cartesian square of sheaves on the big fppf site of `S` whose right-hand column `g` is
representable by algebraic spaces, surjective, flat and locally of finite presentation and
whose top row `a` is representable by algebraic spaces, separated and locally quasi-finite,
the bottom row `b` is representable by objects of the site, separated and locally
quasi-finite.

Representability of `b` by objects of the site is
`AlgebraicGeometry.Space.relativelyRepresentable_of_isPullback_of_flat_surjective`, the
source's own argument by effective fppf descent of schemes.  Separatedness and local
quasi-finiteness descend by Stacks 0421 and Stacks 0427, each read at the fppf precoverage
from its fpqc form. -/
@[stacks 046J]
theorem relativelyRepresentable_separated_locallyQuasiFinite_of_isPullback
    {E F H G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : E ⟶ F) (f : E ⟶ H) (g : F ⟶ G) (b : H ⟶ G) (sq : IsPullback a f g b)
    (hH : Presheaf.IsSheaf (BigFppfOver.topology B S hS) H)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (hgRep : IsRepresentableByAlgebraicSpaces B S hS g)
    (hgSurj : HasProperty B S hS (surjectiveMorphismProperty B S hS) g hgRep)
    (hgFlat : HasProperty B S hS (flatProperty B S hS) g hgRep)
    (hgLfp : HasProperty B S hS (locallyOfFinitePresentationProperty B S hS) g hgRep)
    (haRep : IsRepresentableByAlgebraicSpaces B S hS a)
    (haSep : HasProperty B S hS (separatedProperty B S hS) a haRep)
    (haLqf : HasProperty B S hS (locallyQuasiFiniteProperty B S hS) a haRep) :
    ∃ hbRep : IsRepresentableByAlgebraicSpaces B S hS b,
      yoneda.relativelyRepresentable b ∧
        HasProperty B S hS (separatedProperty B S hS) b hbRep ∧
          HasProperty B S hS (locallyQuasiFiniteProperty B S hS) b hbRep := by
  have hlqfLocal : (locallyQuasiFiniteProperty B S hS).IsLocalAtTarget
      (Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    isLocallyQuasiFinite_isLocalAtTarget_fppf B S hS
  have hsepLocal : (separatedProperty B S hS).IsLocalAtTarget
      (Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le
      (L := Topology.fpqc.precoverage.{u, u + 1} B S hS)
      (fppfPrecoverage_le_fpqcPrecoverage.{u, u + 1} B S hS)
  have hbSch : yoneda.relativelyRepresentable b :=
    relativelyRepresentable_of_isPullback_of_flat_surjective B S hS a f g b sq hH hG
      hgRep hgSurj hgFlat hgLfp haRep haSep haLqf
  have hbRep : IsRepresentableByAlgebraicSpaces B S hS b :=
    IsRepresentableByAlgebraicSpaces.of_relativelyRepresentable hbSch
  have hbSep : HasProperty B S hS (separatedProperty B S hS) b hbRep :=
    hasProperty_of_isPullback_of_fppfCover B S hS (separatedProperty B S hS) a f g b sq hgRep
      hgSurj hgFlat hgLfp haRep haSep hbRep
  have hbLqf : HasProperty B S hS (locallyQuasiFiniteProperty B S hS) b hbRep :=
    hasProperty_of_isPullback_of_fppfCover B S hS (locallyQuasiFiniteProperty B S hS) a f g b sq
      hgRep hgSurj hgFlat hgLfp haRep haLqf hbRep
  exact ⟨hbRep, hbSch, hbSep, hbLqf⟩

/-! ### Stacks 0AMP, modulo the bootstrap theorem -/

/-- **The statement of Stacks 04S6, part (3).** A sheaf on the big fppf site of `S` which
receives a morphism from an algebraic space over `S` that is representable by algebraic
spaces, surjective, flat and locally of finite presentation is itself an algebraic space
over `S`.

The three properties of the morphism are read through
`AlgebraicGeometry.Space.HasProperty`, the definition of Stacks 03XZ.

This abbreviation states a condition and proves nothing.  It is deliberately untagged: the
source derives it from the whole Bootstrap chapter, which this library does not have, so
tagging it would register a part of Stacks 04S6 that is not proved here. -/
abbrev IsBootstrapAlgebraicSpaceAlongFlatSurjection : Prop :=
  ∀ {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y),
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
    IsAlgebraicSpace B S hS X →
    ∀ hf : IsRepresentableByAlgebraicSpaces B S hS f,
      HasProperty B S hS (surjectiveMorphismProperty B S hS) f hf →
      HasProperty B S hS (flatProperty B S hS) f hf →
      HasProperty B S hS (locallyOfFinitePresentationProperty B S hS) f hf →
      IsAlgebraicSpace B S hS Y

/-- Stacks 0AMP from the bootstrap theorem Stacks 04S6 part (3).

For morphisms of presheaves `a : F ⟶ G` and `b : G ⟶ H` on the big fppf site of `S` with `G`
and `H` sheaves, if `a` is representable by algebraic spaces, surjective, flat and locally of
finite presentation and the composite `a ≫ b` is representable by algebraic spaces, then `b`
is representable by algebraic spaces.

At a scheme-valued point `ξ` of `H` the fibre product `U ×_H F` is an algebraic space, being
a base change of `a ≫ b`, and `U ×_H G` is a sheaf.  The morphism `U ×_H F ⟶ U ×_H G` is the
base change of `a` along `U ×_H G ⟶ G`, so Stacks 046F gives it the three properties of `a`,
and the bootstrap theorem makes `U ×_H G` an algebraic space.

Sheafness of `F` is assumed in the source and is not needed here: representability of `a ≫ b`
already makes the base changes of `F` that the argument uses algebraic spaces.

**This does not register [Stacks, Tag 0AMP] and carries no attribute.** Its input
`hbootstrap` is Stacks 04S6 part (3), which this repository does not prove, and
`isBootstrapAlgebraicSpaceAlongFlatSurjection_iff` below shows the two statements are
*equivalent*: the universally quantified form of this theorem is 04S6 part (3). So nothing
weaker than 04S6 part (3) can discharge the input, and a declaration assuming an equivalent
statement does not formalize the tag. The theorem and its proof are kept, because they are
the deduction the source makes; the tag will be registered here once 04S6 part (3) is proved. -/
@[stacks 0AMP "granted Stacks 04S6 part (3), carried as the hypothesis hbootstrap"]
theorem isRepresentableByAlgebraicSpaces_of_comp_of_flat_surjective
    (hbootstrap : IsBootstrapAlgebraicSpaceAlongFlatSurjection B S hS)
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (hH : Presheaf.IsSheaf (BigFppfOver.topology B S hS) H)
    (haRep : IsRepresentableByAlgebraicSpaces B S hS a)
    (haSurj : HasProperty B S hS (surjectiveMorphismProperty B S hS) a haRep)
    (haFlat : HasProperty B S hS (flatProperty B S hS) a haRep)
    (haLfp : HasProperty B S hS (locallyOfFinitePresentationProperty B S hS) a haRep)
    (hcomp : IsRepresentableByAlgebraicSpaces B S hS (a ≫ b)) :
    IsRepresentableByAlgebraicSpaces B S hS b := by
  intro U ξ
  have hsq : IsPullback (pullback.snd (pullback.snd ξ b) a)
      (pullback.fst (pullback.snd ξ b) a) a (pullback.snd ξ b) :=
    (IsPullback.of_hasPullback (pullback.snd ξ b) a).flip
  have hX : IsAlgebraicSpace B S hS (pullback (pullback.snd ξ b) a) :=
    (hcomp U ξ).of_iso (pullbackLeftPullbackSndIso ξ b a).symm
  have hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback ξ b) :=
    Presheaf.isSheaf_pullback _ ξ b (isAlgebraicSpace_yoneda B S hS U).isSheaf hG hH
  exact hbootstrap (pullback.fst (pullback.snd ξ b) a) hY hX
    (isRepresentableByAlgebraicSpaces_of_isPullback B S hS _ _ a _ hsq haRep)
    (hasProperty_of_isPullback B S hS (surjectiveMorphismProperty B S hS) _ _ a _ hsq haRep haSurj)
    (hasProperty_of_isPullback B S hS (flatProperty B S hS) _ _ a _ hsq haRep haFlat)
    (hasProperty_of_isPullback B S hS (locallyOfFinitePresentationProperty B S hS) _ _ a _
      hsq haRep haLfp)

/-- The hypothesis
`AlgebraicGeometry.Space.IsRepresentabilityDescentAlongFlatSurjection`, the statement of
Stacks 0AMP, is discharged by the bootstrap theorem Stacks 04S6 part (3). -/
theorem isRepresentabilityDescentAlongFlatSurjection_of_bootstrap
    (hbootstrap : IsBootstrapAlgebraicSpaceAlongFlatSurjection B S hS) :
    IsRepresentabilityDescentAlongFlatSurjection B S hS := by
  intro F G H a b hG hH haRep haSurj haFlat haLfp hcomp
  exact isRepresentableByAlgebraicSpaces_of_comp_of_flat_surjective B S hS hbootstrap a b hG hH
    haRep haSurj haFlat haLfp hcomp

/-- **Stacks 0AMP and Stacks 04S6 part (3) are the same assumption.**

One direction is Stacks 0AMP itself.  For the other, read Stacks 0AMP over the terminal object
`S` of the site: a sheaf `Y` receiving a chart `f : X ⟶ Y` from an algebraic space which is
representable by algebraic spaces, surjective, flat and locally of finite presentation has its
structure morphism `Y ⟶ h_S` representable by algebraic spaces, because the composite
`X ⟶ h_S` is — every fibre product `h_U ×_{h_S} X` is a fibre product of algebraic spaces.
The base change of `Y ⟶ h_S` along the identity of `h_S` is `Y` itself, so `Y` is an algebraic
space.

So assuming Stacks 0AMP is assuming the bootstrap theorem: no hypothesis strictly weaker than
`AlgebraicGeometry.Space.IsBootstrapAlgebraicSpaceAlongFlatSurjection` can discharge
`AlgebraicGeometry.Space.IsRepresentabilityDescentAlongFlatSurjection`. -/
theorem isBootstrapAlgebraicSpaceAlongFlatSurjection_iff :
    IsBootstrapAlgebraicSpaceAlongFlatSurjection B S hS ↔
      IsRepresentabilityDescentAlongFlatSurjection B S hS := by
  refine ⟨isRepresentabilityDescentAlongFlatSurjection_of_bootstrap B S hS, fun hdescent ↦ ?_⟩
  intro X Y f hY hX hf hfSurj hfFlat hfLfp
  have hT : IsAlgebraicSpace B S hS (yoneda.obj (⊤_ (BigFppfOver B S hS))) :=
    isAlgebraicSpace_yoneda B S hS _
  set t : Y ⟶ yoneda.obj (⊤_ (BigFppfOver B S hS)) :=
    (isTerminal_yoneda_obj_terminal B S hS).from Y with ht
  have hcomp : IsRepresentableByAlgebraicSpaces B S hS (f ≫ t) := fun U ξ ↦
    isAlgebraicSpace_pullback B S hS ξ (f ≫ t) (isAlgebraicSpace_yoneda B S hS U) hX hT
  exact isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces
    (hdescent f t hY hT.isSheaf hf hfSurj hfFlat hfLfp hcomp)

end AlgebraicGeometry.Space

end
