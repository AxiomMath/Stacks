module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableEtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibresComposition
public import StacksFrontier.CategoryTheory.Sites.Representable.CoproductYonedaRefinement

/-!
# Reasonableness of the source of a reasonable morphism

Reasonableness of an algebraic space over a scheme `S` is tested on étale charts, and
Stacks 03JT lets one test it on a single jointly surjective family of them. A reasonable
morphism supplies such a family over each member of a family for its target, and the
composite charts are again étale with universally bounded fibres. This gives the case
"reasonable" of Stacks 0ABY, and with the base-change statement of Stacks 03L0 it gives the
case "reasonable" of Stacks 03L1.

## Main results

* `AlgebraicGeometry.Space.isReasonableSpace_of_isReasonable`: **Stacks 0ABY** for
  reasonableness — if a morphism of algebraic spaces and its target are reasonable, so is its
  source.
* `AlgebraicGeometry.Space.isReasonable_comp`: **Stacks 03L1** for reasonableness — a
  composition of reasonable morphisms is reasonable.

## Implementation notes

The degree bound of a chart must not depend on the field-valued point at which it is tested,
whereas `AlgebraicGeometry.Space.HasUniversallyBoundedFibers` hides the bound behind an
existential quantifier. The bound is therefore carried explicitly through the two steps where
it is needed, base change along a representable morphism and composition through a scheme, by
the private predicate `HasFieldBound` below; the two statements about it are
Stacks 03JN and Stacks 03JM with their bounds exposed, and their proofs are those of
`AlgebraicGeometry.Space.hasUniversallyBoundedFibers_baseChange` and
`AlgebraicGeometry.Space.hasUniversallyBoundedFibers_comp`.

Both charts of a composite are produced by base change: a field-valued point of the source
`X` is pushed to the target `Y`, the chart of `Y` is base changed to its fibre there, and the
chart of the fibre product is base changed to the fibre of *that*. The two fibres are schemes
finite over the field, so their degrees multiply, which is Stacks 03J6 at the level of
schemes.

## References

* [Stacks Project, Tag 03J6](https://stacks.math.columbia.edu/tag/03J6)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 03JM](https://stacks.math.columbia.edu/tag/03JM)
* [Stacks Project, Tag 03JN](https://stacks.math.columbia.edu/tag/03JN)
* [Stacks Project, Tag 03JT](https://stacks.math.columbia.edu/tag/03JT)
* [Stacks Project, Tag 03KZ](https://stacks.math.columbia.edu/tag/03KZ)
* [Stacks Project, Tag 03L0](https://stacks.math.columbia.edu/tag/03L0)
* [Stacks Project, Tag 03L1](https://stacks.math.columbia.edu/tag/03L1)
* [Stacks Project, Tag 0ABY](https://stacks.math.columbia.edu/tag/0ABY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Fibre bounds with the bound exposed -/

section Bounds

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- `AlgebraicGeometry.Space.HasUniversallyBoundedFibers` with its bound exposed: every
field-valued base change of `f` is represented by a scheme finite locally free of rank at
most `n` over the field. -/
private abbrev HasFieldBound (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ X) (n : ℤ) : Prop :=
  ∀ (k : Type u) [Field k] (T : BigFppfOver B S hS),
    ((BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of k)) →
      ∀ ξ : yoneda.obj T ⟶ X,
        ∃ (V : BigFppfOver B S hS) (p : V ⟶ T) (i : yoneda.obj V ⟶ yoneda.obj U) (r : ℕ),
          (r : ℤ) ≤ n ∧
            Stacks.Morphisms.IsFiniteLocallyFreeOfRank
              ((BigFppfOver.toScheme B S hS).map p) r ∧
            IsPullback i (yoneda.map p) f ξ

/-- **Stacks 03JL compared with Stacks 03J4, with the bound.** A bound on the degrees of the
field-valued fibres of a morphism of representable presheaves bounds the degrees of the
scheme-theoretic fibres of the underlying morphism of schemes. -/
private theorem boundsFiberDegrees_toScheme_map_of_hasFieldBound
    {V U : BigFppfOver B S hS} (f : V ⟶ U) (n : ℤ)
    (hn : HasFieldBound B S hS V (yoneda.map f) n) :
    BoundsFiberDegrees ((BigFppfOver.toScheme B S hS).map f) n := by
  intro y
  obtain ⟨W, q, i, r, hr, hrank, hpb⟩ :=
    hn (((BigFppfOver.toScheme B S hS).obj U).residueField y) (residueFieldSiteObj B S hS U y)
      (Iso.refl _) (yoneda.map (residueFieldSiteHom B S hS U y))
  obtain ⟨q', rfl⟩ := yoneda.map_surjective i
  have hsiteSq : IsPullback q' q f (residueFieldSiteHom B S hS U y) :=
    IsPullback.of_map_of_faithful yoneda hpb
  have hschemeSq := hsiteSq.map (BigFppfOver.toScheme B S hS)
  rw [show (BigFppfOver.toScheme B S hS).map (residueFieldSiteHom B S hS U y) =
    ((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField y from rfl] at hschemeSq
  have hfib := MorphismProperty.RespectsIso.precomp
    (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property r)
    hschemeSq.isoPullback.inv ((BigFppfOver.toScheme B S hS).map q) hrank
  rw [hschemeSq.isoPullback_inv_snd] at hfib
  exact ⟨r, hr, hfib⟩

/-- **Stacks 03JN, with the bound.** A representable base change of a morphism whose
field-valued fibres have degrees bounded by `n` is represented by a scheme whose fibres have
degrees bounded by the same `n`. -/
private theorem hasFieldBound_baseChange (g : Y ⟶ X) (hg : yoneda.relativelyRepresentable g)
    (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ X) (n : ℤ)
    (hf : HasFieldBound B S hS U f n) :
    ∃ (V : BigFppfOver B S hS) (i : yoneda.obj V ⟶ yoneda.obj U) (p : yoneda.obj V ⟶ Y),
      IsPullback i p f g ∧ HasFieldBound B S hS V p n := by
  obtain ⟨V, i, p, hp⟩ := hg f
  refine ⟨V, yoneda.map i, p, hp.flip, ?_⟩
  intro k _ T hT ξ
  obtain ⟨W, q, j, r, hbound, hrank, hq⟩ := hf k T hT (ξ ≫ g)
  refine ⟨W, q, hp.flip.lift j (yoneda.map q ≫ ξ) (by
    simpa [Category.assoc] using hq.w), r, hbound, hrank, ?_⟩
  simpa using hq.of_right' hp.flip

/-- **Stacks 03JM, with the bounds.** The degrees of the field-valued fibres of a composite
through a scheme are bounded by the product of bounds for the two factors. -/
private theorem hasFieldBound_comp {V U : BigFppfOver B S hS} (f : V ⟶ U)
    (g : yoneda.obj U ⟶ X) (n m : ℤ)
    (hf : HasFieldBound B S hS V (yoneda.map f) n) (hg : HasFieldBound B S hS U g m) :
    HasFieldBound B S hS V (yoneda.map f ≫ g) (max n 0 * max m 0) := by
  have hN : BoundsFiberDegrees ((BigFppfOver.toScheme B S hS).map f) (max n 0) :=
    boundsFiberDegrees_toScheme_map_of_hasFieldBound B S hS f (max n 0) fun k _ T hT ξ ↦ by
      obtain ⟨P, p, i, r, hr, hrank, hpb⟩ := hf k T hT ξ
      exact ⟨P, p, i, r, hr.trans (le_max_left n 0), hrank, hpb⟩
  intro k _ A hA ξ
  obtain ⟨P, pA, i₀, r₀, hr₀, hrank₀, hP⟩ := hg k A hA ξ
  obtain ⟨pU, rfl⟩ := yoneda.map_surjective i₀
  have hsite : IsPullback (pullback.fst f pU) (pullback.snd f pU) f pU :=
    IsPullback.of_hasPullback f pU
  have hbase : BoundsFiberDegrees
      ((BigFppfOver.toScheme B S hS).map (pullback.snd f pU)) (max n 0) :=
    boundsFiberDegrees_of_isPullback (hsite.map (BigFppfOver.toScheme B S hS)) hN
  have hrank₀' : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map pA ≫ hA.hom) r₀ :=
    ((Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property r₀).cancel_right_of_respectsIso
      _ hA.hom).mpr hrank₀
  have hcomp : BoundsFiberDegrees
      ((BigFppfOver.toScheme B S hS).map (pullback.snd f pU) ≫
        ((BigFppfOver.toScheme B S hS).map pA ≫ hA.hom)) (max n 0 * r₀) :=
    boundsFiberDegrees_comp _ _ _ _ (le_max_right n 0) hbase
      (boundsFiberDegrees_of_isFiniteLocallyFreeOfRank _ r₀)
  obtain ⟨r, hr, hrank⟩ := exists_rank_le_of_boundsFiberDegrees_of_specTarget _ hcomp
  refine ⟨pullback f pU, pullback.snd f pU ≫ pA, yoneda.map (pullback.fst f pU), r,
    hr.trans (mul_le_mul_of_nonneg_left (hr₀.trans (le_max_left m 0)) (le_max_right n 0)),
    ?_, ?_⟩
  · rw [Functor.map_comp]
    refine ((Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property r).cancel_right_of_respectsIso
      _ hA.hom).mp ?_
    rwa [Category.assoc]
  · rw [Functor.map_comp]
    exact IsPullback.paste_vert (hsite.map yoneda) hP

/-- A chart of a fibre product `V ×_Y X` composed with the projection to `X` has universally
bounded fibres, when the chart `V ⟶ Y` and the chart of the fibre product both do.

A field-valued point of `X` is pushed to `Y`, where the chart `V ⟶ Y` has a finite fibre; the
chart of the fibre product is base changed to that fibre, and the degrees of the two finite
schemes multiply. -/
private theorem hasUniversallyBoundedFibers_comp_pullback_snd {V U : BigFppfOver B S hS}
    (hY : IsAlgebraicSpace B S hS Y) (φ : yoneda.obj V ⟶ Y) (f : X ⟶ Y)
    (hA : IsAlgebraicSpace B S hS (pullback φ f)) (ψ : yoneda.obj U ⟶ pullback φ f)
    (hφ : HasUniversallyBoundedFibers B S hS V φ)
    (hψ : HasUniversallyBoundedFibers B S hS U ψ) :
    HasUniversallyBoundedFibers B S hS U (ψ ≫ pullback.snd φ f) := by
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  obtain ⟨n, hn⟩ := hφ
  obtain ⟨m, hm⟩ := hψ
  refine ⟨max m 0 * max n 0, ?_⟩
  intro k _ T hT ξ
  have hξrep : yoneda.relativelyRepresentable (ξ ≫ f) :=
    (Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := Y)).mp
      hY.diagonal_representable (ξ ≫ f)
  obtain ⟨W, iW, pW, hpbW, hboundW⟩ :=
    hasFieldBound_baseChange B S hS (ξ ≫ f) hξrep V φ n hn
  obtain ⟨q, hq⟩ := yoneda.map_surjective pW
  have hpbW' : IsPullback iW (yoneda.map q) φ (ξ ≫ f) := by simpa [hq] using hpbW
  have hApb := IsPullback.of_hasPullback φ f
  have hcompat : iW ≫ φ = (yoneda.map q ≫ ξ) ≫ f := by
    rw [hpbW'.w, Category.assoc]
  let w : yoneda.obj W ⟶ pullback φ f := hApb.lift iW (yoneda.map q ≫ ξ) hcompat
  have hwfst : w ≫ pullback.fst φ f = iW := hApb.lift_fst iW (yoneda.map q ≫ ξ) hcompat
  have hwsnd : w ≫ pullback.snd φ f = yoneda.map q ≫ ξ :=
    hApb.lift_snd iW (yoneda.map q ≫ ξ) hcompat
  have hbig : IsPullback (w ≫ pullback.fst φ f) (yoneda.map q) φ (ξ ≫ f) := by
    simpa [hwfst] using hpbW'
  have hpbWA : IsPullback w (yoneda.map q) (pullback.snd φ f) ξ :=
    (hApb.paste_horiz_iff hwsnd).1 hbig
  have hwrep : yoneda.relativelyRepresentable w :=
    (Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := pullback φ f)).mp
      hA.diagonal_representable w
  obtain ⟨Z, inc, pZ, hpbZ, hboundZ⟩ := hasFieldBound_baseChange B S hS w hwrep U ψ m hm
  obtain ⟨qZ, hqZ⟩ := yoneda.map_surjective pZ
  have hboundZT := hasFieldBound_comp B S hS qZ (yoneda.map q) m n
    (by simpa [hqZ] using hboundZ) (by simpa [hq] using hboundW)
  have hpbZT : IsPullback inc (yoneda.map qZ ≫ yoneda.map q)
      (ψ ≫ pullback.snd φ f) ξ := by
    simpa [hqZ, Category.assoc] using hpbZ.paste_vert hpbWA
  obtain ⟨D, d, j, r, hr, hrank, hpbD⟩ := hboundZT k T hT (𝟙 _)
  refine ⟨D, d, j ≫ inc, r, hr, hrank, ?_⟩
  have hpbD' : IsPullback j (yoneda.map d)
      (yoneda.map qZ ≫ yoneda.map q) (𝟙 (yoneda.obj T)) := by simpa using hpbD
  simpa [Category.assoc] using hpbD'.paste_horiz hpbZT

end Bounds

/-! ### Reasonableness of the source -/

section Source

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0ABY, reasonable.** If a morphism of algebraic spaces over `S` is reasonable and
its target is reasonable, then its source is reasonable.

A jointly surjective family of étale charts with universally bounded fibres for the target,
Stacks 03JT, pulls back to a family of fibre products over the source, each of which is a
reasonable algebraic space because the morphism is reasonable; a family of charts for each of
those, composed with the projections to the source, is again jointly surjective and étale,
and the fibres of the composites remain universally bounded. -/
@[stacks 0ABY "reasonable"]
theorem isReasonableSpace_of_isReasonable (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hYr : IsReasonableSpace B S hS Y)
    (hf : IsReasonable B S hS f) :
    IsReasonableSpace B S hS X := by
  classical
  set J := BigFppfOver.topology B S hS
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  obtain ⟨I, V, φ, hcoverY, hpropsY⟩ :=
    (isReasonableSpace_iff_exists_boundedEtaleCover B S hS Y hY).1 hYr
  let A (i : I) := pullback (φ i) f
  have hA (i : I) : IsAlgebraicSpace B S hS (A i) :=
    isAlgebraicSpace_pullback B S hS (φ i) f (isAlgebraicSpace_yoneda B S hS (V i)) hX hY
  have hcoverA (i : I) :=
    (isReasonableSpace_iff_exists_boundedEtaleCover B S hS (A i) (hA i)).1 (hf (V i) (φ i))
  choose K U ψ hcA hpA using hcoverA
  let I' := Σ i, K i
  let U' (z : I') := U z.1 z.2
  let p' (z : I') : yoneda.obj (U' z) ⟶ X := ψ z.1 z.2 ≫ pullback.snd (φ z.1) f
  have hcoverX : Presheaf.IsLocallySurjective J (Sigma.desc p') := by
    refine ⟨?_⟩
    intro Q x
    apply J.transitive (hcoverY.imageSieve_mem (f.app (op Q) x))
    intro Q₁ g₁ hg₁
    obtain ⟨s, hs⟩ := hg₁
    obtain ⟨i, v, hσ⟩ := Presheaf.exists_sigmaι_app_eq (fun i ↦ yoneda.obj (V i)) (op Q₁) s
    have hv : (φ i).app (op Q₁) v = Y.map g₁.op (f.app (op Q) x) := by
      rw [← hσ] at hs
      change ((Sigma.ι (fun i ↦ yoneda.obj (V i)) i ≫ Sigma.desc φ).app (op Q₁)) v = _ at hs
      simpa only [Sigma.ι_desc, NatTrans.comp_app] using hs
    have hpbV := IsPullback.of_hasPullback (φ i) f
    have hcomm : yonedaEquiv.symm v ≫ φ i = yonedaEquiv.symm (X.map g₁.op x) ≫ f := by
      apply yonedaEquiv.injective
      simpa [yonedaEquiv_comp] using hv
    let q := hpbV.lift (yonedaEquiv.symm v) (yonedaEquiv.symm (X.map g₁.op x)) hcomm
    have hqX : q ≫ pullback.snd (φ i) f = yonedaEquiv.symm (X.map g₁.op x) :=
      hpbV.lift_snd (yonedaEquiv.symm v) (yonedaEquiv.symm (X.map g₁.op x)) hcomm
    let a : (A i).obj (op Q₁) := yonedaEquiv q
    have _ : Presheaf.IsLocallySurjective J (Sigma.desc (ψ i)) := hcA i
    have hcoverAt : Presheaf.imageSieve (Sigma.desc (ψ i)) a ∈ J Q₁ :=
      Presheaf.imageSieve_mem J (Sigma.desc (ψ i)) a
    apply J.superset_covering ?_ hcoverAt
    intro Q₂ g₂ hg₂
    obtain ⟨s₂, hs₂⟩ := hg₂
    obtain ⟨j, w, hσ₂⟩ := Presheaf.exists_sigmaι_app_eq (fun j ↦ yoneda.obj (U i j)) (op Q₂) s₂
    have hw : (ψ i j).app (op Q₂) w = (A i).map g₂.op a := by
      rw [← hσ₂] at hs₂
      change ((Sigma.ι (fun j ↦ yoneda.obj (U i j)) j ≫ Sigma.desc (ψ i)).app (op Q₂)) w = _
        at hs₂
      simpa only [Sigma.ι_desc, NatTrans.comp_app] using hs₂
    have hwX : (p' ⟨i, j⟩).app (op Q₂) w = X.map g₂.op (X.map g₁.op x) := by
      show (pullback.snd (φ i) f).app (op Q₂) ((ψ i j).app (op Q₂) w) = _
      rw [hw]
      have hqpoint : (pullback.snd (φ i) f).app (op Q₁) a = X.map g₁.op x := by
        rw [← yonedaEquiv_comp, hqX]
        simp
      calc
        _ = X.map g₂.op ((pullback.snd (φ i) f).app (op Q₁) a) :=
          NatTrans.naturality_apply (pullback.snd (φ i) f) g₂.op a
        _ = _ := by rw [hqpoint]
    refine ⟨(Sigma.ι (fun z : I' ↦ yoneda.obj (U' z)) ⟨i, j⟩).app (op Q₂) w, ?_⟩
    show ((Sigma.ι (fun z : I' ↦ yoneda.obj (U' z)) ⟨i, j⟩ ≫ Sigma.desc p').app (op Q₂)) w = _
    rw [Sigma.ι_desc]
    simpa [Functor.map_comp] using hwX
  refine (isReasonableSpace_iff_exists_boundedEtaleCover B S hS X hX).2
    ⟨I', U', p', hcoverX, fun z ↦ ⟨?_, ?_⟩⟩
  · let Pe := MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
    have _ : MorphismProperty.IsStableUnderComposition
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
      (inferInstance : MorphismProperty.IsMultiplicative
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})).toIsStableUnderComposition
    have _ : Pe.IsStableUnderComposition :=
      MorphismProperty.IsStableUnderComposition.inverseImage _
    have _ : Pe.presheaf.IsStableUnderComposition :=
      MorphismProperty.relative_isStableUnderComposition _
    have hπ : Pe.presheaf (pullback.snd (φ z.1) f) :=
      (MorphismProperty.relative_isStableUnderBaseChange Pe).of_isPullback
        (IsPullback.of_hasPullback (φ z.1) f) (hpropsY z.1).1
    exact MorphismProperty.comp_mem Pe.presheaf (ψ z.1 z.2) (pullback.snd (φ z.1) f)
      (hpA z.1 z.2).1 hπ
  · exact hasUniversallyBoundedFibers_comp_pullback_snd B S hS hY (φ z.1) f (hA z.1)
      (ψ z.1 z.2) (hpropsY z.1).2 (hpA z.1 z.2).2

end Source

/-! ### Composition -/

section Composition

variable {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03L1, reasonable.** Reasonableness of a morphism of algebraic spaces over `S` is
preserved by composition.

The base change of `f ≫ g` along `k : T ⟶ Z` is the base change of `f` along the projection
`T ×_Z Y ⟶ Y`, viewed over `T ×_Z Y`; that projection is reasonable by Stacks 03L0 and
`T ×_Z Y` is reasonable because `g` is, so Stacks 0ABY applies. -/
@[stacks 03L1 "reasonable"]
theorem isReasonable_comp (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsReasonable B S hS f) (hg : IsReasonable B S hS g) :
    IsReasonable B S hS (f ≫ g) := by
  intro T k
  have hP : IsAlgebraicSpace B S hS (pullback k g) :=
    isAlgebraicSpace_pullback B S hS k g (isAlgebraicSpace_yoneda B S hS T) hY hZ
  exact isReasonableSpace_of_iso B S hS (pullbackLeftPullbackSndIso k g f)
    (isReasonableSpace_of_isReasonable B S hS
      (isAlgebraicSpace_pullback B S hS (pullback.snd k g) f hP hX hY) hP
      (pullback.fst (pullback.snd k g) f) (hg T k)
      (isReasonable_baseChange B S hS f (pullback.snd k g) hf))

end Composition

end AlgebraicGeometry.Space

end
