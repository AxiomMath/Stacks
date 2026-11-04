module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Smallness
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctions

/-!
# Dominant morphisms and dominant rational maps of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is *dominant* when its map on points has
dense image. A rational map, that is a class of morphisms defined on dense open subspaces, is
*defined at a point* when one of its representatives has that point in its domain, and it is
*dominant* when every one of its representatives is a dominant morphism. Two algebraic spaces
with irreducible point spaces are *birational* when they are isomorphic by dominant rational
maps, and that happens exactly when they contain isomorphic nonempty open subspaces.

## Main definitions

* `AlgebraicGeometry.Space.IsDominant` is **Stacks 0ABL**: dominance of a morphism.
* `AlgebraicGeometry.Space.RationalMap.IsDefinedAt` and
  `AlgebraicGeometry.Space.RationalMap.domainOfDefinition` are **Stacks 0EMQ**.
* `AlgebraicGeometry.Space.RationalMap.IsDominant` is **Stacks 0EMS**: dominance of a
  rational map.
* `AlgebraicGeometry.Space.Birational` is **Stacks 0EMT**: birationality of two algebraic
  spaces with irreducible point spaces.

## Main results

* `AlgebraicGeometry.Space.isDenseOpenSubspace_of_nonempty`: in an algebraic space with
  irreducible point space, a nonempty open subspace is a dense open subspace.
* `AlgebraicGeometry.Space.RationalMap.isDominant_of_denseRange`: a rational map with one
  representative with dense image is dominant.
* `AlgebraicGeometry.Space.birational_iff_exists_isOpenSubspace_iso` is **Stacks 0EMU**: two
  algebraic spaces with irreducible point spaces are birational if and only if they have
  isomorphic nonempty open subspaces.

## Implementation notes

The point set is `AlgebraicGeometry.Space.points` of Stacks 03BU, the induced map is
`AlgebraicGeometry.Space.pointsMap`, and the topology is
`AlgebraicGeometry.Space.pointTopology` of Stacks 03BX, installed here as a local instance;
so dominance is literally `DenseRange` for the map on points and the usual topological API
applies to it without a conversion lemma. No algebraicity hypothesis enters the definition of a
dominant morphism, because the point topology needs none. The rational-map notions are indexed
by the algebraicity hypothesis on the source, since `AlgebraicGeometry.Space.RationalMap` is.

Birationality is phrased as the existence of two dominant rational maps whose two composites
agree with the respective identities on dense open subspaces, which is what an isomorphism in
the category of irreducible algebraic spaces and dominant rational maps amounts to; no
category structure on the quotient of partial maps is needed for that, and the irreducibility
hypotheses, which single out the objects of that category, are carried as unused parameters.

## References

* [Stacks Project, Tag 0ABL](https://stacks.math.columbia.edu/tag/0ABL)
* [Stacks Project, Tag 0EMQ](https://stacks.math.columbia.edu/tag/0EMQ)
* [Stacks Project, Tag 0EMS](https://stacks.math.columbia.edu/tag/0EMS)
* [Stacks Project, Tag 0EMT](https://stacks.math.columbia.edu/tag/0EMT)
* [Stacks Project, Tag 0EMU](https://stacks.math.columbia.edu/tag/0EMU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Dominant morphisms -/

section Dominant

variable {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism of algebraic spaces over `S` is *dominant* when the image of its map on points is
dense in the point space of the target. -/
@[stacks 0ABL, ega "I 2.2.6" "dominant"]
abbrev IsDominant (f : F ⟶ G) : Prop := DenseRange (pointsMap B S hS F f)

/-- A dense range stays dense after precomposition with an isomorphism. -/
private theorem denseRange_pointsMap_comp_of_iso {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : F ≅ V) (k : V ⟶ G) (hk : DenseRange (pointsMap B S hS V k)) :
    DenseRange (pointsMap B S hS F (e.hom ≫ k)) := by
  have hsurj : Function.Surjective (pointsMap B S hS F e.hom) := by
    intro y
    refine ⟨pointsMap B S hS V e.inv y, ?_⟩
    have hy : pointsMap B S hS V (e.inv ≫ e.hom) y = y := by
      rw [e.inv_hom_id, pointsMap_id, id_eq]
    rwa [pointsMap_comp] at hy
  have hrange : Set.range (pointsMap B S hS F (e.hom ≫ k)) =
      Set.range (pointsMap B S hS V k) := by
    rw [pointsMap_comp, Set.range_comp, hsurj.range_eq, Set.image_univ]
  change Dense (Set.range (pointsMap B S hS F (e.hom ≫ k)))
  rwa [hrange]

end Dominant

/-! ### Open subspaces of open subspaces -/

section OpenSubspace

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An open subspace of an open subspace of `X` is isomorphic to an open subspace of `X`,
namely the range of the composite inclusion. -/
private theorem exists_isOpenSubspace_iso {W : Subfunctor X} (hW : IsOpenSubspace B S hS W)
    {Q : Subfunctor W.toFunctor} (hQ : IsOpenSubspace B S hS Q) :
    ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧ Nonempty (Q.toFunctor ≅ U.toFunctor) := by
  have hc : IsOpenImmersion B S hS (Q.ι ≫ W.ι) :=
    isOpenImmersion_comp B S hS Q.ι W.ι hQ.2 hW.2
  refine ⟨Subfunctor.range (Q.ι ≫ W.ι), ⟨?_, ?_⟩,
    ⟨asIso (Subfunctor.toRange (Q.ι ≫ W.ι))⟩⟩
  · exact hQ.1.of_iso (asIso (Subfunctor.toRange (Q.ι ≫ W.ι)))
  · exact (MorphismProperty.cancel_left_of_respectsIso
      (P := MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)))
      (asIso (Subfunctor.toRange (Q.ι ≫ W.ι))).hom
      (Subfunctor.range (Q.ι ≫ W.ι)).ι).mp hc

/-- In an algebraic space over `S` whose point space is irreducible, an open subspace with a
point is a dense open subspace. -/
theorem isDenseOpenSubspace_of_nonempty (hX : IsAlgebraicSpace B S hS X)
    (hXirr : IrreducibleSpace (points B S hS X)) {U : Subfunctor X}
    (hU : IsOpenSubspace B S hS U) (hne : Nonempty (points B S hS U.toFunctor)) :
    IsDenseOpenSubspace B S hS hX U := by
  have := hXirr
  refine ⟨hU, (isOpen_range_pointsMap_of_isOpenImmersion B S hS U.ι hU.2).dense ?_⟩
  obtain ⟨p⟩ := hne
  exact ⟨pointsMap B S hS U.toFunctor U.ι p, p, rfl⟩

/-- The point set of a subspace contained in an open subspace `U` is dense in `|U|` as soon as
it is dense in the ambient point space. -/
private theorem denseRange_pointsMap_homOfLe {E U : Subfunctor X}
    (hU : IsOpenSubspace B S hS U) (hEU : E ≤ U)
    (hE : DenseRange (pointsMap B S hS E.toFunctor E.ι)) :
    DenseRange (pointsMap B S hS E.toFunctor (Subfunctor.homOfLe hEU)) := by
  have hopen : IsOpenMap (pointsMap B S hS U.toFunctor U.ι) :=
    isOpenMap_pointsMap_of_isOpenImmersion B S hS U.ι hU.2
  have hinj : Function.Injective (pointsMap B S hS U.toFunctor U.ι) :=
    pointsMap_injective_of_mono B S hS U.ι
  have hcomp : pointsMap B S hS U.toFunctor U.ι ∘
      pointsMap B S hS E.toFunctor (Subfunctor.homOfLe hEU) =
      pointsMap B S hS E.toFunctor E.ι := by
    rw [← pointsMap_comp, Subfunctor.homOfLe_ι]
  change Dense (Set.range (pointsMap B S hS E.toFunctor (Subfunctor.homOfLe hEU)))
  rw [dense_iff_inter_open]
  intro O hO hOne
  obtain ⟨pE, pU, hpU, hpUE⟩ := hE.exists_mem_open (hopen O hO) (hOne.image _)
  have heq : pointsMap B S hS E.toFunctor (Subfunctor.homOfLe hEU) pE = pU := by
    refine hinj ?_
    calc pointsMap B S hS U.toFunctor U.ι
            (pointsMap B S hS E.toFunctor (Subfunctor.homOfLe hEU) pE)
        = pointsMap B S hS E.toFunctor E.ι pE := congrFun hcomp pE
      _ = pointsMap B S hS U.toFunctor U.ι pU := hpUE.symm
  exact ⟨pointsMap B S hS E.toFunctor (Subfunctor.homOfLe hEU) pE, heq ▸ hpU, pE, rfl⟩

end OpenSubspace

/-! ### Inverse images of subspaces -/

section Preimage

variable {A T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The inverse image of a subspace `V ≤ D` along a morphism which factors through `D` sits
over `V` compatibly with that factorization. -/
private theorem fromPreimage_homOfLe {V D : Subfunctor T} (f : A ⟶ T) (g : A ⟶ D.toFunctor)
    (hV : V ≤ D) (hg : g ≫ D.ι = f) :
    V.fromPreimage f ≫ Subfunctor.homOfLe hV = (V.preimage f).ι ≫ g := by
  refine (cancel_mono D.ι).1 ?_
  rw [Category.assoc, Subfunctor.homOfLe_ι, Subfunctor.fromPreimage_ι, Category.assoc, hg]

/-- A morphism whose composite with `f` factors through a subspace `Z` of the target lands in
the inverse image of `Z` along `f`. -/
private theorem range_le_preimage {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : A ⟶ T)
    (Z : Subfunctor T) (R : Subfunctor P) (k : R.toFunctor ⟶ A) (w : R.toFunctor ⟶ Z.toFunctor)
    (h : k ≫ f = w ≫ Z.ι) : Subfunctor.range k ≤ Z.preimage f := by
  intro i y hy
  obtain ⟨a, rfl⟩ := hy
  change f.app i (k.app i a) ∈ Z.obj i
  have he : f.app i (k.app i a) = Z.ι.app i (w.app i a) := by
    simpa only [NatTrans.comp_app, types_comp_apply] using congrArg (fun q => q.app i a) h
  rw [he]
  exact (w.app i a).property

end Preimage

/-! ### Dominant rational maps -/

section RationalMaps

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

namespace RationalMap

variable {hX : IsAlgebraicSpace B S hS X}

/-- A rational map is *defined at a point* of its source when it has a representative whose
domain contains that point. -/
@[stacks 0EMQ "defined at a point",
  ega "I 7.2.1" "defined at a point",
  ega "IV 20.2.3" "defined at a point"]
abbrev IsDefinedAt (φ : RationalMap B S hS hX Y) (x : points B S hS X) : Prop :=
  ∃ f : PartialMap B S hS hX Y, f.toRationalMap B S hS = φ ∧
    x ∈ Set.range (pointsMap B S hS f.domain.toFunctor f.domain.ι)

/-- The *domain of definition* of a rational map is the set of points at which it is defined. -/
@[stacks 0EMQ "domain of definition",
  ega "I 7.2.1" "domain of definition",
  ega "IV 20.2.3" "dom(ω)"]
abbrev domainOfDefinition (φ : RationalMap B S hS hX Y) : Set (points B S hS X) :=
  {x | IsDefinedAt B S hS φ x}

/-- A rational map is *dominant* when every one of its dense-open representatives is a dominant
morphism. -/
@[stacks 0EMS]
abbrev IsDominant (φ : RationalMap B S hS hX Y) : Prop :=
  ∀ f : PartialMap B S hS hX Y, f.toRationalMap B S hS = φ →
    Space.IsDominant B S hS f.hom

end RationalMap

/-- The restriction of a morphism on an open subspace `U` to a subspace `E ≤ U` with dense
point set again has dense image. -/
private theorem denseRange_pointsMap_of_restrict {E U : Subfunctor X}
    (hU : IsOpenSubspace B S hS U) (hEU : E ≤ U)
    (hE : DenseRange (pointsMap B S hS E.toFunctor E.ι))
    {f : U.toFunctor ⟶ Y} {g : E.toFunctor ⟶ Y} (hfg : Subfunctor.homOfLe hEU ≫ f = g)
    (hf : DenseRange (pointsMap B S hS U.toFunctor f)) :
    DenseRange (pointsMap B S hS E.toFunctor g) := by
  have hd := hf.comp (denseRange_pointsMap_homOfLe B S hS hU hEU hE)
    (continuous_pointsMap B S hS f)
  rwa [← pointsMap_comp, hfg] at hd

/-- Of two morphisms on subspaces of `X` which agree on a subspace with dense point set, the
first having dense image forces the second to have dense image, provided the first is defined
on an open subspace. -/
private theorem denseRange_pointsMap_of_agree {U V E : Subfunctor X}
    (hU : IsOpenSubspace B S hS U) (hEU : E ≤ U) (hEV : E ≤ V)
    (hE : DenseRange (pointsMap B S hS E.toFunctor E.ι))
    {f : U.toFunctor ⟶ Y} {g : V.toFunctor ⟶ Y}
    (hagree : Subfunctor.homOfLe hEU ≫ f = Subfunctor.homOfLe hEV ≫ g)
    (hf : DenseRange (pointsMap B S hS U.toFunctor f)) :
    DenseRange (pointsMap B S hS V.toFunctor g) := by
  refine (denseRange_pointsMap_of_restrict B S hS hU hEU hE hagree hf).mono ?_
  rintro y ⟨p, rfl⟩
  rw [pointsMap_comp]
  exact ⟨pointsMap B S hS E.toFunctor (Subfunctor.homOfLe hEV) p, rfl⟩

/-- A rational map with one dense-image representative is dominant. -/
theorem RationalMap.isDominant_of_denseRange {hX : IsAlgebraicSpace B S hS X}
    (f : PartialMap B S hS hX Y)
    (hf : DenseRange (pointsMap B S hS f.domain.toFunctor f.hom)) :
    RationalMap.IsDominant B S hS (f.toRationalMap B S hS) := by
  intro f' hf'
  obtain ⟨E, hE, hEf', hEf, hagree⟩ := (PartialMap.toRationalMap_eq_iff B S hS).mp hf'
  exact denseRange_pointsMap_of_agree B S hS f.dense_open_domain.1 hEf hEf' hE.2 hagree.symm hf

/-! ### Birational algebraic spaces -/

/-- Two algebraic spaces over `S` with irreducible point spaces are *birational* when they have
mutually inverse dominant rational maps: two dominant rational maps whose composites agree with
the respective identities on dense open subspaces. -/
@[stacks 0EMT]
abbrev Birational (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (_hXirr : IrreducibleSpace (points B S hS X))
    (_hYirr : IrreducibleSpace (points B S hS Y)) : Prop :=
  ∃ (f : PartialMap B S hS hX Y) (g : PartialMap B S hS hY X),
    RationalMap.IsDominant B S hS (f.toRationalMap B S hS) ∧
    RationalMap.IsDominant B S hS (g.toRationalMap B S hS) ∧
    (∃ W : Subfunctor X, IsDenseOpenSubspace B S hS hX W ∧
      ∃ (hWf : W ≤ f.domain) (fWg : W.toFunctor ⟶ g.domain.toFunctor),
        Subfunctor.homOfLe hWf ≫ f.hom = fWg ≫ g.domain.ι ∧ fWg ≫ g.hom = W.ι) ∧
    (∃ V : Subfunctor Y, IsDenseOpenSubspace B S hS hY V ∧
      ∃ (hVg : V ≤ g.domain) (gVf : V.toFunctor ⟶ f.domain.toFunctor),
        Subfunctor.homOfLe hVg ≫ g.hom = gVf ≫ f.domain.ι ∧ gVf ≫ f.hom = V.ι)

/-- The two lifts through the inverse images of `V` and `W` compose to the identity, given the
compatibility of `V.fromPreimage fW` with `gV`. -/
private theorem lift_fromPreimage_comp_lift {W : Subfunctor X} {V : Subfunctor Y}
    {fW : W.toFunctor ⟶ Y} {gV : V.toFunctor ⟶ X}
    (hA : V.fromPreimage fW ≫ gV = (V.preimage fW).ι ≫ W.ι)
    (hRA : Subfunctor.range (V.fromPreimage fW) ≤ W.preimage gV)
    (hRP : Subfunctor.range (W.fromPreimage gV) ≤ V.preimage fW) :
    Subfunctor.lift (V.fromPreimage fW) hRA ≫ Subfunctor.lift (W.fromPreimage gV) hRP =
      𝟙 (V.preimage fW).toFunctor := by
  have hA' : Subfunctor.lift (W.fromPreimage gV) hRP ≫ (V.preimage fW).ι ≫ W.ι =
      (W.preimage gV).ι ≫ gV := by
    rw [← Category.assoc, Subfunctor.lift_ι, Subfunctor.fromPreimage_ι]
  refine (cancel_mono ((V.preimage fW).ι ≫ W.ι)).1 ?_
  rw [Category.id_comp, Category.assoc, hA', ← Category.assoc, Subfunctor.lift_ι, hA]

/-- Two morphisms `fW : W ⟶ Y` and `gV : V ⟶ X` out of subspaces of `X` and of `Y` whose two
composites are the two inclusions restrict to mutually inverse isomorphisms between the
inverse images `fW⁻¹V` and `gV⁻¹W`. -/
private theorem nonempty_iso_preimage {W : Subfunctor X} {V : Subfunctor Y}
    {fW : W.toFunctor ⟶ Y} {gV : V.toFunctor ⟶ X}
    (hA : V.fromPreimage fW ≫ gV = (V.preimage fW).ι ≫ W.ι)
    (hP : W.fromPreimage gV ≫ fW = (W.preimage gV).ι ≫ V.ι) :
    Nonempty ((V.preimage fW).toFunctor ≅ (W.preimage gV).toFunctor) := by
  have hRA : Subfunctor.range (V.fromPreimage fW) ≤ W.preimage gV :=
    range_le_preimage B S hS gV W (V.preimage fW) (V.fromPreimage fW) (V.preimage fW).ι hA
  have hRP : Subfunctor.range (W.fromPreimage gV) ≤ V.preimage fW :=
    range_le_preimage B S hS fW V (W.preimage gV) (W.fromPreimage gV) (W.preimage gV).ι hP
  exact ⟨⟨Subfunctor.lift (V.fromPreimage fW) hRA, Subfunctor.lift (W.fromPreimage gV) hRP,
    lift_fromPreimage_comp_lift B S hS hA hRA hRP, lift_fromPreimage_comp_lift B S hS hP hRP hRA⟩⟩

/-- Two algebraic spaces over `S` with irreducible point spaces are birational if and only if
they contain nonempty open subspaces which are isomorphic as algebraic spaces over `S`. -/
@[stacks 0EMU]
theorem birational_iff_exists_isOpenSubspace_iso (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXirr : IrreducibleSpace (points B S hS X))
    (hYirr : IrreducibleSpace (points B S hS Y)) :
    Birational B S hS hX hY hXirr hYirr ↔
      ∃ (U : Subfunctor X) (V : Subfunctor Y), IsOpenSubspace B S hS U ∧
        IsOpenSubspace B S hS V ∧ Nonempty (points B S hS U.toFunctor) ∧
        Nonempty (points B S hS V.toFunctor) ∧ Nonempty (U.toFunctor ≅ V.toFunctor) := by
  constructor
  · rintro ⟨f, g, hfDom, hgDom, ⟨W, hW, hWf, fWg, hWcomp₁, hWcomp₂⟩,
      ⟨V, hV, hVg, gVf, hVcomp₁, hVcomp₂⟩⟩
    obtain ⟨fW, hfW⟩ : ∃ k : W.toFunctor ⟶ Y, fWg ≫ g.domain.ι = k := ⟨_, rfl⟩
    obtain ⟨gV, hgV⟩ : ∃ k : V.toFunctor ⟶ X, gVf ≫ f.domain.ι = k := ⟨_, rfl⟩
    have hAopen : IsOpenSubspace B S hS (V.preimage fW) :=
      isOpenSubspace_preimage B S hS fW V hY hW.1.1 hV.1
    have hPopen : IsOpenSubspace B S hS (W.preimage gV) :=
      isOpenSubspace_preimage B S hS gV W hX hV.1.1 hW.1
    have hAcomp : V.fromPreimage fW ≫ gV = (V.preimage fW).ι ≫ W.ι := by
      rw [← hgV, ← hVcomp₁, ← Category.assoc, fromPreimage_homOfLe B S hS fW fWg hVg hfW,
        Category.assoc, hWcomp₂]
    have hPcomp : W.fromPreimage gV ≫ fW = (W.preimage gV).ι ≫ V.ι := by
      rw [← hfW, ← hWcomp₁, ← Category.assoc, fromPreimage_homOfLe B S hS gV gVf hWf hgV,
        Category.assoc, hVcomp₂]
    obtain ⟨eAP⟩ := nonempty_iso_preimage B S hS hAcomp hPcomp
    obtain ⟨U, hU, ⟨eAU⟩⟩ := exists_isOpenSubspace_iso B S hS hW.1 hAopen
    obtain ⟨V', hV', ⟨ePV⟩⟩ := exists_isOpenSubspace_iso B S hS hV.1 hPopen
    have := hYirr
    have hfWdense : DenseRange (pointsMap B S hS W.toFunctor fW) :=
      denseRange_pointsMap_of_restrict B S hS f.dense_open_domain.1 hWf hW.2
        (hWcomp₁.trans hfW) (hfDom f rfl)
    obtain ⟨pW, pV, hpV⟩ := hfWdense.exists_mem_open
      (isOpen_range_pointsMap_of_isOpenImmersion B S hS V.ι hV.1.2)
      (hV.2.nonempty_iff.mpr inferInstance)
    obtain ⟨pA, -, -⟩ := exists_point_of_isPullback B S hS
      (show IsPullback
          (ObjectProperty.homMk (V.fromPreimage fW) :
            (⟨(V.preimage fW).toFunctor, hAopen.1⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨V.toFunctor, hV.1.1⟩)
          (ObjectProperty.homMk (V.preimage fW).ι :
            _ ⟶ (⟨W.toFunctor, hW.1.1⟩ : AlgebraicSpaces B S hS))
          (ObjectProperty.homMk V.ι : _ ⟶ (⟨Y, hY⟩ : AlgebraicSpaces B S hS))
          (ObjectProperty.homMk fW) from
        IsPullback.of_map_of_faithful
          (F := ObjectProperty.ι (fun Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
            IsAlgebraicSpace B S hS Z))
          (Subfunctor.isPullback_preimage fW V)) pV pW hpV
    exact ⟨U, V', hU, hV', ⟨pointsMap B S hS (V.preimage fW).toFunctor eAU.hom pA⟩,
      ⟨pointsMap B S hS (W.preimage gV).toFunctor ePV.hom
        (pointsMap B S hS (V.preimage fW).toFunctor eAP.hom pA)⟩,
      ⟨eAU.symm ≪≫ eAP ≪≫ ePV⟩⟩
  · rintro ⟨U, V, hU, hV, hUne, hVne, ⟨e⟩⟩
    have hUdense : IsDenseOpenSubspace B S hS hX U :=
      isDenseOpenSubspace_of_nonempty B S hS hX hXirr hU hUne
    have hVdense : IsDenseOpenSubspace B S hS hY V :=
      isDenseOpenSubspace_of_nonempty B S hS hY hYirr hV hVne
    have hid : ∀ {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (R : Subfunctor Z),
        Subfunctor.homOfLe (le_rfl : R ≤ R) = 𝟙 R.toFunctor := fun _ ↦ rfl
    refine ⟨⟨U, hUdense, e.hom ≫ V.ι⟩, ⟨V, hVdense, e.inv ≫ U.ι⟩,
      RationalMap.isDominant_of_denseRange B S hS _
        (denseRange_pointsMap_comp_of_iso B S hS e V.ι hVdense.2),
      RationalMap.isDominant_of_denseRange B S hS _
        (denseRange_pointsMap_comp_of_iso B S hS e.symm U.ι hUdense.2),
      ⟨U, hUdense, le_rfl, e.hom, ?_, ?_⟩, ⟨V, hVdense, le_rfl, e.inv, ?_, ?_⟩⟩
    · rw [hid U, Category.id_comp]
    · rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
    · rw [hid V, Category.id_comp]
    · rw [← Category.assoc, e.inv_hom_id, Category.id_comp]

end RationalMaps

end AlgebraicGeometry.Space

end
