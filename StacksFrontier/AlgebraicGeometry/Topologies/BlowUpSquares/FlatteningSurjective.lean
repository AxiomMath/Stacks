module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Basic
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Iterated
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.Flattening
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.Shrinking

/-!
# Making the relative morphism of the flattening pair surjective

Let `f : X ⟶ Y` be a proper surjective morphism and let `V ⊆ Y` be an open for which the pair of
almost blowup squares of Stacks tag 0EVC exists. Its relative morphism `g : X' ⟶ Y'` is flat and
of finite presentation, but need not be surjective. Shrinking `Y'` to the image of `g` repairs
this without disturbing anything else, and is what the proof of Stacks tag 0EVF needs.

## Main results

* `AlgebraicGeometry.exists_surjective_of_hasFlatAlmostBlowUpSquarePair`: the pair of almost
  blowup squares of Stacks tag 0EVC can be chosen with its relative morphism proper and
  surjective as well as flat and of finite presentation.

## Implementation notes

The three steps of the Stacks proof are:

* `g` is proper. The modification `c : X' ⟶ X` of the right-hand square is proper and so is `f`,
  hence `g ≫ b = c ≫ f` is proper (tag 01W3); the modification `b : Y' ⟶ Y` is proper, hence
  separated, so properness descends to `g` by
  `AlgebraicGeometry.isProper_of_isProper_of_isSeparated` (tag 01W6).
* The image of `g` is open and closed. It is open because a flat morphism locally of finite
  presentation is universally open
  (`AlgebraicGeometry.universallyOpen_of_flat_of_locallyOfFinitePresentation`, tag 01UA), and
  closed because a proper morphism is universally closed, hence a closed map (tag 01W6).
* `Y'` is replaced by that clopen image. The replacement is the closed subscheme cut out by
  `W.ι.ker`, the kernel of the inclusion of the open subscheme `W` carried by the image. Because
  the image is also closed, `W.ι` is a closed immersion, so the closed subscheme cut out by
  `W.ι.ker` *is* `W`: the two closed immersions `W.ι` and `W.ι.ker.subschemeι` have the same
  kernel, which is `AlgebraicGeometry.isIso_clopenSubschemeComparison`. That is what makes the
  new centre finitely presented, and the open immersion `W.ι` is what `g` is factored through.

The shrinking itself is the forward direction of
`AlgebraicGeometry.le_supportedSectionsIdeal_iff_isAlmostBlowUpSquare` (tag 0EV8), whose
hypothesis `W.ι.ker ≤ supportedSectionsIdeal (Z.comap b).support` is, after
`AlgebraicGeometry.supportedSectionsIdeal_eq_complementKernel`, an inclusion of kernels
`W.ι.ker ≤ (Y' ∖ E).ι.ker`, for `E` the exceptional subset of `b`. Since `Y' ∖ E` is contained in
the image of `g`, its inclusion factors through `W.ι`, so the inclusion of kernels is
`AlgebraicGeometry.Scheme.Hom.le_ker_comp`.

The containment of `Y' ∖ E` in the image of `g` is
`AlgebraicGeometry.compl_support_comap_subset_range`, and it is where the surjectivity of `f` is
used. Over the complement of the centre the two
modifications are isomorphisms (tag 0EV6), so a point of `Y' ∖ E` is hit by `c ≫ f = g ≫ b` and
`b` is injective there; the point of `X'` produced that way is therefore carried to the given one
by `g` itself.

Properties of the factorisation `gW : X' ⟶ W` are read off from the fact that it is a base change
of `g` along `W.ι` (`AlgebraicGeometry.IsOpenImmersion.isPullback_lift_id`); properties of the
composition with the comparison isomorphism are then stability under composition.

## References

* [Stacks Project, Tag 0EVF](https://stacks.math.columbia.edu/tag/0EVF)
* [Stacks Project, Tag 0EVC](https://stacks.math.columbia.edu/tag/0EVC)
* [Stacks Project, Tag 0EV8](https://stacks.math.columbia.edu/tag/0EV8)
* [Stacks Project, Tag 0EV6](https://stacks.math.columbia.edu/tag/0EV6)
* [Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
* [Stacks Project, Tag 01W3](https://stacks.math.columbia.edu/tag/01W3)
* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The comparison morphism from an open subscheme whose inclusion is a closed immersion to the
closed subscheme cut out by the kernel of that inclusion. It is an isomorphism, by
`AlgebraicGeometry.isIso_clopenSubschemeComparison`. -/
public def clopenSubschemeComparison {Y : Scheme.{u}} (W : Y.Opens) [IsClosedImmersion W.ι] :
    W.toScheme ⟶ W.ι.ker.subscheme :=
  IsClosedImmersion.lift W.ι.ker.subschemeι W.ι (by simp)

/-- The comparison morphism of `AlgebraicGeometry.clopenSubschemeComparison` is a morphism over
the ambient scheme. -/
public theorem clopenSubschemeComparison_fac {Y : Scheme.{u}} (W : Y.Opens)
    [IsClosedImmersion W.ι] :
    clopenSubschemeComparison W ≫ W.ι.ker.subschemeι = W.ι :=
  IsClosedImmersion.lift_fac _ _ _

/-- An open subscheme whose inclusion is a closed immersion is the closed subscheme cut out by
the kernel of that inclusion: the two closed immersions have the same kernel. -/
public theorem isIso_clopenSubschemeComparison {Y : Scheme.{u}} (W : Y.Opens)
    [IsClosedImmersion W.ι] : IsIso (clopenSubschemeComparison W) :=
  IsClosedImmersion.isIso_of_ker_eq W.ι W.ι.ker.subschemeι (clopenSubschemeComparison W)
    (clopenSubschemeComparison_fac W) (by simp)

/-- The closed subscheme cut out by the kernel of the inclusion of an open subscheme which is
also closed is of finite presentation: it is that open subscheme, whose inclusion is locally of
finite presentation because it is an open immersion, and quasi-compact and quasi-separated
because it is a closed immersion. -/
public theorem finitePresentation_ker_subschemeι {Y : Scheme.{u}} (W : Y.Opens)
    [IsClosedImmersion W.ι] : FinitePresentation W.ι.ker.subschemeι := by
  have : IsIso (clopenSubschemeComparison W) := isIso_clopenSubschemeComparison W
  have hinv : inv (clopenSubschemeComparison W) ≫ W.ι = W.ι.ker.subschemeι :=
    (IsIso.inv_comp_eq _).2 (clopenSubschemeComparison_fac W).symm
  refine FinitePresentation.mk ?_ inferInstance inferInstance
  have hcomp : LocallyOfFinitePresentation (inv (clopenSubschemeComparison W) ≫ W.ι) :=
    MorphismProperty.comp_mem @LocallyOfFinitePresentation _ _ inferInstance inferInstance
  rwa [hinv] at hcomp

/-- **The complement of the exceptional subset lies in the image of the relative morphism.**
In the diagram of Stacks tag 0EVC over a surjective `f`, every point of `Y'` lying outside the
exceptional subset of `b` is in the image of `g`.

Over the complement of the centre both modifications are isomorphisms
(`AlgebraicGeometry.isIso_restrict_compl_support`), so the restriction of `c ≫ f` there is
surjective, `f` being surjective. A point `y` of `Y'` outside the exceptional subset therefore
has a preimage `x` under `c ≫ f`, and `b (g x) = (g ≫ b) x = (c ≫ f) x = b y`; as `b` is
injective over the complement of the centre, `g x = y`. -/
public theorem compl_support_comap_subset_range {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y)
    (hsurj : Surjective f) (Z : Y.IdealSheafData) {b : Y' ⟶ Y} {c : X' ⟶ X} {g : X' ⟶ Y'}
    (hleft : IsAlmostBlowUpSquare Z b) (hright : IsAlmostBlowUpSquare (Z.comap f) c)
    (hcomm : g ≫ b = c ≫ f) :
    ((Z.comap b).support : Set Y')ᶜ ⊆ Set.range g.base := by
  let UZ : Y.Opens := ⟨(Z.support : Set Y)ᶜ, Z.support.isClosed.isOpen_compl⟩
  have hb : IsIso (b ∣_ UZ) := isIso_restrict_compl_support Z b hleft
  have hUT : (⟨((Z.comap f).support : Set X)ᶜ,
      (Z.comap f).support.isClosed.isOpen_compl⟩ : X.Opens) = f ⁻¹ᵁ UZ := by
    refine TopologicalSpace.Opens.ext ?_
    ext x
    simp [UZ, Scheme.IdealSheafData.support_comap]
  have hc : Surjective (c ∣_ (f ⁻¹ᵁ UZ)) := by
    rw [← hUT]
    exact (have := isIso_restrict_compl_support (Z.comap f) c hright; inferInstance)
  have hfres : Surjective (f ∣_ UZ) := IsZariskiLocalAtTarget.restrict hsurj UZ
  have hcf : Surjective ((c ≫ f) ∣_ UZ) := by
    rw [morphismRestrict_comp]
    exact ⟨hfres.surj.comp hc.surj⟩
  intro y hy
  have hmem : b.base y ∈ (UZ : Set Y) := by
    simpa [UZ, Scheme.IdealSheafData.support_comap] using hy
  obtain ⟨q, hq⟩ := Scheme.Hom.surjective ((c ≫ f) ∣_ UZ) ⟨b.base y, hmem⟩
  have hq' : (c ≫ f).base q.1 = b.base y := by
    rw [← morphismRestrict_base_coe (c ≫ f) UZ q, hq]
  have hkey : b.base (g.base q.1) = b.base y := by
    rw [← Scheme.Hom.comp_apply, hcomm, hq']
  exact ⟨q.1, Stacks.StrictTransform.injOn_preimage_of_isIso_morphismRestrict b UZ
    (by simpa [hkey] using hmem) hmem hkey⟩

/-- **Stacks Project, Tag 0EVF, the shrinking step.** Let `f : X ⟶ Y` be proper and surjective
and let `V ⊆ Y` be an open admitting the pair of almost blowup squares of Stacks tag 0EVC. Then
the pair may be chosen with its relative morphism `g : X' ⟶ Y'` proper and surjective in addition
to flat and of finite presentation.

The given relative morphism is automatically proper, and its image is a clopen subset of `Y'`
containing the complement of the exceptional subset; replacing `Y'` by the corresponding closed
subscheme keeps an almost blowup square, by Stacks tag 0EV8, and makes the relative morphism
surjective. -/
public theorem exists_surjective_of_hasFlatAlmostBlowUpSquarePair {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hproper : IsProper f) (hsurj : Surjective f) (V : Y.Opens)
    (h : HasFlatAlmostBlowUpSquarePair f V) :
    ∃ (Z : Y.IdealSheafData) (Y' : Scheme.{u}) (b : Y' ⟶ Y) (X' : Scheme.{u}) (c : X' ⟶ X)
        (g : X' ⟶ Y'),
      IsAlmostBlowUpSquare Z b ∧ IsAlmostBlowUpSquare (Z.comap f) c ∧
        Disjoint (V : Set Y) (Z.support : Set Y) ∧
          g ≫ b = c ≫ f ∧ Flat g ∧ FinitePresentation g ∧ IsProper g ∧ Surjective g := by
  obtain ⟨Z, Y', b, X', c, g, hleft, hright, hdisj, hcomm, hflat, hfp⟩ := h
  have := hproper
  have := hflat
  have hbproper : IsProper b := hleft.proper
  have hcproper : IsProper c := hright.proper
  have hlfp : LocallyOfFinitePresentation g := hfp.locallyOfFinitePresentation
  have hqc : QuasiCompact g := hfp.quasiCompact
  have hqs : QuasiSeparated g := hfp.quasiSeparated
  -- `g` is proper, because `g ≫ b = c ≫ f` is proper and `b` is separated
  have hgproper : IsProper g := isProper_of_isProper_of_isSeparated g b (c ≫ f) hcomm
  -- the image of `g` is clopen, and carries an open subscheme `W` whose inclusion is also closed
  have huo : UniversallyOpen g := universallyOpen_of_flat_of_locallyOfFinitePresentation g
  have hWopen : IsOpen (Set.range g.base) := Set.image_univ ▸ g.isOpenMap _ isOpen_univ
  have hWclosed : IsClosed (Set.range g.base) := Set.image_univ ▸ g.isClosedMap _ isClosed_univ
  obtain ⟨W, hWcarrier⟩ : ∃ W : Y'.Opens, (W : Set Y') = Set.range g.base :=
    ⟨⟨Set.range g.base, hWopen⟩, rfl⟩
  have hWrange : Set.range W.ι.base = Set.range g.base := by
    rw [Scheme.Opens.range_ι, hWcarrier]
  have hWci : IsClosedImmersion W.ι :=
    IsClosedImmersion.of_isPreimmersion W.ι (by rw [hWrange]; exact hWclosed)
  have hm : IsIso (clopenSubschemeComparison W) := isIso_clopenSubschemeComparison W
  have hfpJ : FinitePresentation W.ι.ker.subschemeι := finitePresentation_ker_subschemeι W
  -- the new centre contains the complement of the exceptional subset, so the square survives
  have hsub : ((Z.comap b).support : Set Y')ᶜ ⊆ Set.range g.base :=
    compl_support_comap_subset_range f hsurj Z hleft hright hcomm
  have hJle : W.ι.ker ≤ supportedSectionsIdeal ((Z.comap b).support : Set Y') := by
    have hle : Set.range (Scheme.Opens.ι (X := Y') ⟨((Z.comap b).support : Set Y')ᶜ,
        (Z.comap b).support.isClosed.isOpen_compl⟩).base ⊆ Set.range W.ι.base := by
      rwa [Scheme.Opens.range_ι, hWrange]
    rw [supportedSectionsIdeal_eq_complementKernel ((Z.comap b).support : Set Y')
      (Z.comap b).support.isClosed, ← IsOpenImmersion.lift_fac W.ι _ hle]
    exact Scheme.Hom.le_ker_comp _ W.ι
  have hnew : IsAlmostBlowUpSquare Z (W.ι.ker.subschemeι ≫ b) :=
    (le_supportedSectionsIdeal_iff_isAlmostBlowUpSquare Z b hleft W.ι.ker hfpJ).mp hJle
  -- the factorisation of `g` through `W`, a base change of `g` along `W.ι`
  have hrange : Set.range g.base ⊆ Set.range W.ι.base := hWrange.ge
  have hsq : IsPullback (IsOpenImmersion.lift W.ι g hrange) (𝟙 X') W.ι g :=
    IsOpenImmersion.isPullback_lift_id g W.ι hrange
  have hgW : IsOpenImmersion.lift W.ι g hrange ≫ W.ι = g := IsOpenImmersion.lift_fac _ _ _
  set gW : X' ⟶ W.toScheme := IsOpenImmersion.lift W.ι g hrange with hgWdef
  have : Flat gW := MorphismProperty.of_isPullback hsq.flip hflat
  have : LocallyOfFinitePresentation gW := MorphismProperty.of_isPullback hsq.flip hlfp
  have : QuasiCompact gW := MorphismProperty.of_isPullback hsq.flip hqc
  have : QuasiSeparated gW := MorphismProperty.of_isPullback hsq.flip hqs
  have : IsProper gW := MorphismProperty.of_isPullback hsq.flip hgproper
  have : Surjective gW := by
    refine ⟨fun w ↦ ?_⟩
    obtain ⟨x, hx⟩ : W.ι.base w ∈ Set.range g.base := by
      rw [← hWrange]; exact Set.mem_range_self w
    refine ⟨x, W.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hgW, hx]
  refine ⟨Z, W.ι.ker.subscheme, W.ι.ker.subschemeι ≫ b, X', c,
    gW ≫ clopenSubschemeComparison W, hnew, hright, hdisj, ?_, inferInstance,
    ⟨inferInstance, inferInstance, inferInstance⟩, inferInstance, inferInstance⟩
  calc (gW ≫ clopenSubschemeComparison W) ≫ W.ι.ker.subschemeι ≫ b
      = (gW ≫ clopenSubschemeComparison W ≫ W.ι.ker.subschemeι) ≫ b := by
        simp only [Category.assoc]
    _ = (gW ≫ W.ι) ≫ b := by rw [clopenSubschemeComparison_fac]
    _ = c ≫ f := by rw [hgW, hcomm]

end AlgebraicGeometry

end
