module

public import Mathlib.AlgebraicGeometry.Properties
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.FieldValued
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FiniteSchemeFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.Reduced
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleEnlargementOfOpen.PointsAndDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleEnlargementOfOpen.SquareAndCoproductCovers

/-!
# Enlarging a dense open subspace by an affine etale chart

Let `U` be a dense open subspace of a Noetherian algebraic space `X` which is not all of
`X`. This file produces an affine scheme `V` and an etale morphism `V` to `X` whose image
enlarges `U`: the open subspace `W` spanned by `U` and the image of `V` strictly contains
`U`, the pair `(U, V)` is an elementary distinguished square on `W`, and the overlap
`U` times over `W` with `V` still has dense image in `U`.

The construction follows the proof of Stacks 0F4C. A finite filtration of `X` by open
subspaces whose reduced strata carry separated etale neighbourhoods, isomorphic above the
stratum, is supplied by Stacks 07ST. The first stratum not contained in `U` provides a point
outside `U`; an affine open of the corresponding etale neighbourhood containing a
representative of that point is the chart `V`, and the stratum isomorphism turns the chart
into an elementary distinguished square. Density of the overlap is restored by adjoining a
dense open affine of the part of `U` missed by the overlap, which exists because `U` is
Noetherian and so has a dense open subscheme by Stacks 06NH.

## Main results

* `AlgebraicGeometry.Space.exists_dense_affine_openImmersion_self`: a Noetherian algebraic
  space has a dense affine open subspace.
* `AlgebraicGeometry.Space.exists_affine_etale_isElementaryDistinguishedSquare` is
  Stacks 0F4C: the affine etale chart enlarging a proper dense open subspace of a Noetherian
  algebraic space in an elementary distinguished square with dense overlap.

## Implementation notes

Open subspaces are subfunctors, so the open subspace `W` is described by its point set: the
range of its inclusion on points is the union of the range of the inclusion of `U` and the
range of the chart. The copy of `U` sitting inside `W` is the range of the morphism
`CategoryTheory.Subfunctor.homOfLe` induced by `U` at most `W`, and it is that subfunctor of
`W` which enters the elementary distinguished square. The overlap of `U` and the chart is
taken as a pullback over `X` rather than over `W`; the two pullbacks are canonically the
same, since the inclusion of `W` is a monomorphism.

"Proper" in the statement of Stacks 0F4C means proper as a subset: the hypothesis is that
`U` is not equal to the whole of `X`, which is exactly what the proof of the tag uses and
what the Nagata compactification theorem Stacks 0F4D feeds it.

## References

* [Stacks Project, Tag 0F4C](https://stacks.math.columbia.edu/tag/0F4C)
* [Stacks Project, Tag 07ST](https://stacks.math.columbia.edu/tag/07ST)
* [Stacks Project, Tag 08GM](https://stacks.math.columbia.edu/tag/08GM)
* [Stacks Project, Tag 06NH](https://stacks.math.columbia.edu/tag/06NH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space


/-- In a descending family `A` of elements of a poset with top, with `A 0 = ⊤` and `A n ≤ U`,
if `U ≠ ⊤` then some index `p < n` has `A p ⊄ U` while `A (p + 1) ≤ U`. This is the choice of
stratum in the proof of Stacks 0F4C. -/
private theorem exists_layer_not_le_then_le
    {X : Type*} [PartialOrder X] [OrderTop X] (A : ℕ → X) (n : ℕ) (U : X)
    (hzero : A 0 = ⊤) (hfinish : A n ≤ U)
    (hproper : U ≠ ⊤) :
    ∃ p < n, ¬ A p ≤ U ∧ A (p + 1) ≤ U := by
  classical
  have hex : ∃ k, k ≤ n ∧ A k ≤ U := ⟨n, le_rfl, hfinish⟩
  let k := Nat.find hex
  have hk := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra hn
    have hle : A 0 ≤ U := by simpa [k, Nat.eq_zero_of_not_pos hn] using hk.2
    exact hproper (top_unique (by simpa [hzero] using hle))
  refine ⟨k - 1, by omega, ?_, by convert hk.2 using 1; congr 1; omega⟩
  intro hp
  have hmin := Nat.find_min' hex ⟨by omega, hp⟩
  omega

/-- A field-valued point of a represented presheaf whose underlying scheme point lies in
the image of an open immersion of schemes is the image of a field-valued point of the
smaller representable. -/
private theorem fieldPoint_factors_through_open
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : AlgebraicGeometry.BigFppfOver B S hS} (j : V ⟶ U)
    [AlgebraicGeometry.IsOpenImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j)]
    (p : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj U))
    (hp : AlgebraicGeometry.Space.schemePoint B S hS U p ∈
      Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j)) :
    ∃ q : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj V),
      AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj V) (yoneda.map j)
        (q.class B S hS (yoneda.obj V)) = p.class B S hS (yoneda.obj U) := by
  classical
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let A := AlgebraicGeometry.Space.FieldValuedPoint.siteObject B S hS (yoneda.obj U) p
  let : Field p.carrier := p.field
  have hrange : Set.range (G.map p.value) ⊆ Set.range (G.map j) := by
    intro x hx
    obtain ⟨z, rfl⟩ := hx
    have hz : z = IsLocalRing.closedPoint p.carrier :=
      (inferInstance : Subsingleton (PrimeSpectrum p.carrier)).elim _ _
    subst z
    simpa [AlgebraicGeometry.Space.schemePoint, G] using hp
  let ψ : Spec (.of p.carrier) ⟶ G.obj V :=
    IsOpenImmersion.lift (G.map j) (G.map p.value) hrange
  have hψ : ψ ≫ G.map j = G.map p.value :=
    IsOpenImmersion.lift_fac _ _ _
  let k : A.left ⟶ V.left :=
    B.inclusion.preimage
      (show B.inclusion.obj A.left ⟶ B.inclusion.obj V.left from ψ)
  have hk : B.inclusion.map k = ψ := by
    show B.inclusion.map
      (B.inclusion.preimage
        (show B.inclusion.obj A.left ⟶ B.inclusion.obj V.left from ψ)) = ψ
    rw [B.inclusion.map_preimage]
  let g : A ⟶ V := Over.homMk k (by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp]
    have hj : G.map j ≫ B.inclusion.map U.hom = B.inclusion.map V.hom := by
      show B.inclusion.map j.left ≫ B.inclusion.map U.hom = B.inclusion.map V.hom
      rw [← B.inclusion.map_comp, j.w]
    have hpv : G.map p.value ≫ B.inclusion.map U.hom = B.inclusion.map A.hom := by
      show B.inclusion.map p.value.left ≫ B.inclusion.map U.hom = B.inclusion.map A.hom
      rw [← B.inclusion.map_comp, p.value.w]
      rfl
    rw [hk, ← hj, ← Category.assoc, hψ]
    exact hpv)
  have hg : g ≫ j = p.value := by
    apply Over.OverMorphism.ext
    show k ≫ j.left = p.value.left
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, hk]
    exact hψ
  let q : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj V) :=
    ⟨p.carrier, p.contained, p.toBase, g⟩
  refine ⟨q, ?_⟩
  rw [AlgebraicGeometry.Space.pointsMap_class]
  have hmap : AlgebraicGeometry.Space.FieldValuedPoint.map B S hS (yoneda.obj V)
      (yoneda.map j) q = p := by
    cases p
    simp [q, AlgebraicGeometry.Space.FieldValuedPoint.map, hg]
  exact congrArg (AlgebraicGeometry.Space.FieldValuedPoint.class B S hS (yoneda.obj U)) hmap

/-- Open subspaces whose point sets are included one in the other are included one in the
other. -/
private theorem le_of_range_pointsMap_subset
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X) {V U : Subfunctor X}
    (hV : AlgebraicGeometry.Space.IsOpenSubspace B S hS V)
    (hU : AlgebraicGeometry.Space.IsOpenSubspace B S hS U)
    (h : Set.range (AlgebraicGeometry.Space.pointsMap B S hS V.toFunctor V.ι) ⊆
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS U.toFunctor U.ι)) : V ≤ U := by
  let := AlgebraicGeometry.Space.pointTopology B S hS X
  let e := AlgebraicGeometry.Space.openSubspacesOrderIso B S hS X hX
  have : (⟨V, hV⟩ : {G : Subfunctor X // AlgebraicGeometry.Space.IsOpenSubspace B S hS G}) ≤
      ⟨U, hU⟩ := by
    apply e.map_rel_iff.mp
    change (e ⟨V, hV⟩).1 ⊆ (e ⟨U, hU⟩).1
    rwa [AlgebraicGeometry.Space.openSubspacesOrderIso_apply,
      AlgebraicGeometry.Space.openSubspacesOrderIso_apply]
  exact this

/-- An étale morphism into an algebraic space `X` and an open subspace `U` of `X` span an
open subspace `W` of `X`: its point set is the union of the point set of `U` and the image
of the étale morphism, and the étale morphism factors through it. -/
private theorem exists_openSubspace_union_range
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (U : Subfunctor X) (hU : AlgebraicGeometry.Space.IsOpenSubspace B S hS U)
    (f : Y ⟶ X) (hf : AlgebraicGeometry.Space.IsEtale B S hS f) :
    ∃ (W : Subfunctor X) (_hW : AlgebraicGeometry.Space.IsOpenSubspace B S hS W)
      (_hUW : U ≤ W) (g : Y ⟶ W.toFunctor),
      g ≫ W.ι = f ∧
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS W.toFunctor W.ι) =
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS U.toFunctor U.ι) ∪
          Set.range (AlgebraicGeometry.Space.pointsMap B S hS Y f) := by
  let := AlgebraicGeometry.Space.pointTopology B S hS X
  let := AlgebraicGeometry.Space.pointTopology B S hS Y
  let e := AlgebraicGeometry.Space.openSubspacesOrderIso B S hS X hX
  let uo := e ⟨U, hU⟩
  have hu : uo.1 = Set.range (AlgebraicGeometry.Space.pointsMap B S hS U.toFunctor U.ι) :=
    AlgebraicGeometry.Space.openSubspacesOrderIso_apply B S hS X hX ⟨U, hU⟩
  let w : TopologicalSpace.Opens (AlgebraicGeometry.Space.points B S hS X) :=
    ⟨uo.1 ∪ Set.range (AlgebraicGeometry.Space.pointsMap B S hS Y f),
      uo.2.union
        (AlgebraicGeometry.Space.isOpenMap_pointsMap_of_isEtale
          B S hS f hY hX hf).isOpen_range⟩
  let W := e.symm w
  have hwrange : Set.range (AlgebraicGeometry.Space.pointsMap B S hS W.1.toFunctor W.1.ι) =
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS U.toFunctor U.ι) ∪
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS Y f) := by
    rw [← AlgebraicGeometry.Space.openSubspacesOrderIso_apply B S hS X hX W]
    show (e (e.symm w)).1 = _
    rw [e.apply_symm_apply]
    exact congrArg (fun t => t ∪ Set.range (AlgebraicGeometry.Space.pointsMap B S hS Y f)) hu
  have hUW : U ≤ W.1 :=
    le_of_range_pointsMap_subset B S hS hX hU W.2 (by rw [hwrange]; exact Set.subset_union_left)
  obtain ⟨g, hg⟩ := (AlgebraicGeometry.Space.factorsThrough_openSubspace_iff_points
    B S hS hX hY W.1 W.2 f).2 (by rw [hwrange]; exact Set.subset_union_right)
  exact ⟨W.1, W.2, hUW, g, hg, hwrange⟩

/-- The first projection of a pullback has dense image as soon as some morphism with dense
image into the first factor lifts to the pullback. -/
private theorem denseRange_pullback_fst_of_lift
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A D V X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hA : AlgebraicGeometry.IsAlgebraicSpace B S hS A)
    (i : A ⟶ X) (f : V ⟶ X) (d : D ⟶ A) (g : D ⟶ V)
    (h : d ≫ i = g ≫ f)
    (hd : letI := AlgebraicGeometry.Space.pointTopology B S hS A
      DenseRange (AlgebraicGeometry.Space.pointsMap B S hS D d)) :
    letI := AlgebraicGeometry.Space.pointTopology B S hS A
    DenseRange (AlgebraicGeometry.Space.pointsMap B S hS (pullback i f) (pullback.fst i f)) := by
  let := AlgebraicGeometry.Space.pointTopology B S hS A
  apply hd.mono
  rintro _ ⟨x, rfl⟩
  refine ⟨AlgebraicGeometry.Space.pointsMap B S hS D (pullback.lift d g h) x, ?_⟩
  rw [← pointsMap_comp_apply, pullback.lift_fst]

/-- Two affine objects of the big fppf site have a coproduct in the site which is again
affine and realizes the coproduct of the underlying schemes. -/
private theorem exists_affine_coproduct
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A D : AlgebraicGeometry.BigFppfOver B S hS)
    (hA : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj A))
    (hD : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj D)) :
    ∃ (E : AlgebraicGeometry.BigFppfOver B S hS) (i : A ⟶ E) (j : D ⟶ E),
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj E) ∧
      ∃ e : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj A ⨿
          (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj D) ≅
          (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj E,
        coprod.inl ≫ e.hom = (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i ∧
        coprod.inr ≫ e.hom = (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j := by
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have hsum : B.Contains (T.obj A ⨿ T.obj D) := by
    show (T.obj A ⨿ T.obj D).size < B.cutoff
    rw [Scheme.size_congr (AlgebraicGeometry.coprodIsoSigma (T.obj A) (T.obj D))]
    apply Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof
    · simp
    · intro i
      cases i.down
      · exact A.left.2
      · exact D.left.2
  let E₀ := B.obj hsum
  let e₀ : E₀ ⟶ B.obj hS := B.inclusion.preimage
    (coprod.desc (B.inclusion.map A.hom) (B.inclusion.map D.hom))
  let E : AlgebraicGeometry.BigFppfOver B S hS := Over.mk e₀
  let i₀ : A.left ⟶ E₀ := B.inclusion.preimage coprod.inl
  let j₀ : D.left ⟶ E₀ := B.inclusion.preimage coprod.inr
  let i : A ⟶ E := Over.homMk i₀ (by
    show i₀ ≫ e₀ = A.hom
    apply B.inclusion.map_injective
    simp only [i₀, e₀, Functor.map_comp, Functor.map_preimage, coprod.inl_desc])
  let j : D ⟶ E := Over.homMk j₀ (by
    show j₀ ≫ e₀ = D.hom
    apply B.inclusion.map_injective
    simp only [j₀, e₀, Functor.map_comp, Functor.map_preimage, coprod.inr_desc])
  have hi : T.map i = (coprod.inl : T.obj A ⟶ T.obj A ⨿ T.obj D) :=
    B.inclusion.map_preimage _
  have hj : T.map j = (coprod.inr : T.obj D ⟶ T.obj A ⨿ T.obj D) :=
    B.inclusion.map_preimage _
  let : IsAffine (T.obj A) := hA
  let : IsAffine (T.obj D) := hD
  refine ⟨E, i, j, (inferInstance : IsAffine (T.obj A ⨿ T.obj D)),
    Iso.refl _, ?_, ?_⟩
  · show (coprod.inl : T.obj A ⟶ T.obj A ⨿ T.obj D) ≫ 𝟙 _ = T.map i
    exact (Category.comp_id _).trans hi.symm
  · show (coprod.inr : T.obj D ⟶ T.obj A ⨿ T.obj D) ≫ 𝟙 _ = T.map j
    exact (Category.comp_id _).trans hj.symm


/-- A sheaf admits a descent of a family of morphisms out of the members of a pairwise
disjoint covering family of monomorphisms. -/
private theorem exists_yoneda_desc_of_disjoint_cover
    {C : Type*} [Category.{u} C] (J : GrothendieckTopology C)
    {I : Type*} (A : I → C) (E : C) (j : ∀ i, A i ⟶ E)
    (hm : ∀ i, Mono (j i)) (hj : Sieve.ofArrows A j ∈ J E)
    (hd : ∀ {i k}, i ≠ k → ∀ {Y : C} (a : Y ⟶ A i) (b : Y ⟶ A k),
      a ≫ j i = b ≫ j k → ⊥ ∈ J Y)
    (F : Cᵒᵖ ⥤ Type u) (hF : Presheaf.IsSheaf J F)
    (f : ∀ i, yoneda.obj (A i) ⟶ F) :
    ∃ g : yoneda.obj E ⟶ F, ∀ i, yoneda.map (j i) ≫ g = f i := by
  let x (i : I) : PUnit ⟶ F.obj (Opposite.op (A i)) := ↾fun _ => yonedaEquiv (f i)
  have hx : ∀ ⦃Y : C⦄ ⦃i k : I⦄ (a : Y ⟶ A i) (b : Y ⟶ A k),
      a ≫ j i = b ≫ j k → x i ≫ F.map a.op = x k ≫ F.map b.op := by
    intro Y i k a b hab
    by_cases hik : i = k
    · subst k
      let := hm i
      have : a = b := (cancel_mono (j i)).mp hab
      subst b
      rfl
    · apply hF.hom_ext_ofArrows (X := fun e : PEmpty.{1} => e.elim) (fun e => e.elim)
        (by simpa [Sieve.ofArrows, Presieve.ofArrows_of_isEmpty] using hd hik a b hab)
      intro e
      exact e.elim
  obtain ⟨g, hg, -⟩ := hF.existsUnique_amalgamation_ofArrows j hj x hx
  refine ⟨yonedaEquiv.symm (g PUnit.unit), ?_⟩
  intro i
  apply yonedaEquiv.injective
  rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply]
  exact ConcreteCategory.congr_hom (hg i) PUnit.unit

/-- Transfer of the isomorphism over a closed subspace along an open immersion: if `f`
factors as an open immersion `i` followed by `g`, the preimage of the closed subspace along
`g` lands in the image of `i` on points, and `f` is an isomorphism over the closed subspace,
then so is `g`. -/
private theorem isIso_fromPreimage_of_factorsThrough_open
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A E X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hE : AlgebraicGeometry.IsAlgebraicSpace B S hS E)
    (Z : Subfunctor X) (hZ : AlgebraicGeometry.Space.IsClosedSubspace B S hS Z)
    (i : A ⟶ E) (hi : AlgebraicGeometry.Space.IsOpenImmersion B S hS i)
    (f : A ⟶ X) (g : E ⟶ X) (hfg : i ≫ g = f)
    (hpoints : Set.range (AlgebraicGeometry.Space.pointsMap B S hS (Z.preimage g).toFunctor
      (Z.preimage g).ι) ⊆ Set.range (AlgebraicGeometry.Space.pointsMap B S hS A i))
    [IsIso (Z.fromPreimage f)] : IsIso (Z.fromPreimage g) := by
  let N := Z.preimage g
  let M := Z.preimage f
  let n := Z.fromPreimage g
  let m := Z.fromPreimage f
  have hsN := CategoryTheory.Subfunctor.isPullback_preimage g Z
  have hsM := CategoryTheory.Subfunctor.isPullback_preimage f Z
  have hN : AlgebraicGeometry.IsAlgebraicSpace B S hS N.toFunctor := by
    apply AlgebraicGeometry.isAlgebraicSpace_of_relativelyRepresentable B S hS N.ι _ hE
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := yoneda.relativelyRepresentable) hsN hZ.2.1
  obtain ⟨a, ha⟩ := factorsThrough_isOpenImmersion B S hS hE hN i hi N.ι hpoints
  have hn : n ≫ Z.ι = a ≫ f := by
    rw [← hfg, ← Category.assoc, ha]
    exact hsN.w
  let k : N.toFunctor ⟶ M.toFunctor := hsM.lift n a hn
  have hkn : k ≫ m = n := hsM.lift_fst _ _ _
  have hka : k ≫ M.ι = a := hsM.lift_snd _ _ _
  let l : M.toFunctor ⟶ N.toFunctor := hsN.lift m (M.ι ≫ i) (by
    rw [Category.assoc, hfg]
    exact hsM.w)
  have hln : l ≫ n = m := hsN.lift_fst _ _ _
  have hli : l ≫ N.ι = M.ι ≫ i := hsN.lift_snd _ _ _
  have hkl : k ≫ l = 𝟙 _ := by
    apply hsN.hom_ext
    · show (k ≫ l) ≫ n = (𝟙 _) ≫ n
      simp only [Category.assoc, hln, hkn, Category.id_comp]
    · show (k ≫ l) ≫ N.ι = (𝟙 _) ≫ N.ι
      simp only [Category.assoc, hli, ← Category.assoc k M.ι, hka, ha, Category.id_comp]
  have hlk : l ≫ k = 𝟙 _ := by
    apply hsM.hom_ext
    · show (l ≫ k) ≫ m = (𝟙 _) ≫ m
      simp only [Category.assoc, hkn, hln, Category.id_comp]
    · show (l ≫ k) ≫ M.ι = (𝟙 _) ≫ M.ι
      rw [Category.assoc, hka, Category.id_comp]
      let := mono_of_isOpenImmersion B S hS i hi
      apply (cancel_mono i).mp
      rw [Category.assoc, ha, hli]
  let : IsIso k := ⟨⟨l, hkl, hlk⟩⟩
  show IsIso n
  rw [← hkn]
  infer_instance

attribute [local instance] AlgebraicGeometry.Space.pointTopology in
/-- **A Noetherian algebraic space has a dense affine open subspace.**  Its schematic locus is
a dense open subspace which is a scheme by Stacks 06NH, and a Noetherian scheme has a dense
affine open; this is the case `U = X` of
`AlgebraicGeometry.Space.exists_dense_affine_openImmersion`, transported along the
isomorphism between the top open subspace and the space itself. -/
theorem exists_dense_affine_openImmersion_self
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hN : AlgebraicGeometry.Space.IsNoetherian B S hS hZ X) :
    ∃ (D : AlgebraicGeometry.BigFppfOver B S hS) (u : yoneda.obj D ⟶ X),
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj D) ∧
      AlgebraicGeometry.Space.IsOpenImmersion B S hS u ∧
      DenseRange (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj D) u) := by
  classical
  have hUtop : AlgebraicGeometry.Space.IsOpenSubspace B S hS (⊤ : Subfunctor X) :=
    AlgebraicGeometry.Space.isOpenSubspace_top (B := B) (S := S) (hS := hS) (F := X) hX
  obtain ⟨D, j, hDaff, hjopen, hjdense⟩ :=
    exists_dense_affine_openImmersion B S hS hZ X hX hN ⊤ hUtop
  refine ⟨D, j ≫ (⊤ : Subfunctor X).ι, hDaff, ?_, ?_⟩
  · exact AlgebraicGeometry.Space.isOpenImmersion_comp B S hS _ _ hjopen
      (AlgebraicGeometry.Space.isOpenImmersion_of_isIso B S hS _)
  · rw [AlgebraicGeometry.Space.pointsMap_comp]
    exact DenseRange.comp
      (pointsMap_surjective_of_isIso B S hS (⊤ : Subfunctor X).ι).denseRange hjdense
      (AlgebraicGeometry.Space.continuous_pointsMap B S hS _)

/-- If an open subspace `V` of an algebraic space is not contained in an open subspace `U`,
then some point of `V` is not a point of `U`. -/
theorem exists_point_of_not_le
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X) {V U : Subfunctor X}
    (hV : AlgebraicGeometry.Space.IsOpenSubspace B S hS V)
    (hU : AlgebraicGeometry.Space.IsOpenSubspace B S hS U) (hVU : ¬ V ≤ U) :
    ∃ x : AlgebraicGeometry.Space.points B S hS X,
      x ∈ Set.range (AlgebraicGeometry.Space.pointsMap B S hS V.toFunctor V.ι) ∧
      x ∉ Set.range (AlgebraicGeometry.Space.pointsMap B S hS U.toFunctor U.ι) := by
  exact Set.not_subset.mp fun h => hVU (le_of_range_pointsMap_subset B S hS hX hV hU h)

/-- **Stacks 0F4C.** Let `U` be a dense open subspace of a Noetherian algebraic space `X`
over `S` with `U ≠ X`. There is an affine scheme `V` and an étale morphism `V ⟶ X` such that
the open subspace `W` whose points are those of `U` together with the image of `V` strictly
contains `U`, the pair `(U ⊆ W, V ⟶ W)` is an elementary distinguished square, and
`U ×_X V ⟶ U` has dense image. -/
@[stacks 0F4C]
theorem exists_affine_etale_isElementaryDistinguishedSquare
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hXnoeth : AlgebraicGeometry.Space.IsNoetherian B S hS hZ X)
    (U : Subfunctor X) (hU : AlgebraicGeometry.Space.IsOpenSubspace B S hS U)
    (hUproper : U ≠ ⊤)
    (_hUdense : letI : TopologicalSpace (AlgebraicGeometry.Space.points B S hS X) :=
        AlgebraicGeometry.Space.pointTopology B S hS X
      DenseRange (AlgebraicGeometry.Space.pointsMap B S hS U.toFunctor U.ι)) :
    ∃ (V : AlgebraicGeometry.BigFppfOver B S hS)
      (W : Subfunctor X)
      (hW : AlgebraicGeometry.Space.IsOpenSubspace B S hS W)
      (hUW : U < W)
      (f : yoneda.obj V ⟶ W.toFunctor),
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V) ∧
      AlgebraicGeometry.Space.IsEtale B S hS (f ≫ W.ι) ∧
      (Set.range (AlgebraicGeometry.Space.pointsMap B S hS W.toFunctor W.ι) =
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS U.toFunctor U.ι) ∪
          Set.range (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj V) (f ≫ W.ι))) ∧
      AlgebraicGeometry.Space.IsElementaryDistinguishedSquare B S hS hW.1
        (Subfunctor.range (Subfunctor.homOfLe hUW.le)) f ∧
      (letI : TopologicalSpace (AlgebraicGeometry.Space.points B S hS U.toFunctor) :=
        AlgebraicGeometry.Space.pointTopology B S hS U.toFunctor
       DenseRange (AlgebraicGeometry.Space.pointsMap B S hS (pullback U.ι (f ≫ W.ι))
         (pullback.fst U.ι (f ≫ W.ι)))) := by
  classical
  obtain ⟨n, Useq, hn, hUzero, hUend, hUopen, hUdesc, hstrata⟩ :=
    AlgebraicGeometry.Space.exists_finiteFiltration_of_isQuasiCompactSpace
      B S hS hZ X hX hXnoeth.1 hXnoeth.2.1
  obtain ⟨T, Vp, fp, hstrata_data⟩ := hstrata
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  have hxSheaf : Presieve.IsSheaf J X :=
    (isSheaf_iff_isSheaf_of_type J X).mp hX.isSheaf
  have huSheaf : Presieve.IsSheaf J U.toFunctor :=
    (isSheaf_iff_isSheaf_of_type J U.toFunctor).mp hU.1.isSheaf
  have hbottom : (⊥ : Subfunctor X).sheafify J ≤ U :=
    Subfunctor.sheafify_le (J := J) (G := ⊥) (G' := U)
      (fun _ _ hx => hx.elim) hxSheaf huSheaf
  have hfinish : Useq n ≤ U := by rwa [hUend]
  obtain ⟨p, hp, hpnot, hple⟩ := exists_layer_not_le_then_le Useq n U
    hUzero hfinish hUproper
  let q : Fin n := ⟨p, hp⟩
  obtain ⟨hTclosed, hTrange, hTred, hVpcompact, hVpsep, hfSurj, hfetale, hiso⟩ := hstrata_data q
  let hUp : AlgebraicGeometry.Space.IsOpenSubspace B S hS (Useq p) := hUopen p (le_of_lt hp)
  let hUp1 : AlgebraicGeometry.Space.IsOpenSubspace B S hS (Useq (p + 1)) :=
    hUopen (p + 1) (by omega)
  obtain ⟨x, hxUp, hxnotU⟩ := exists_point_of_not_le B S hS hX hUp hU hpnot
  have hstratum :
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS (Useq p).toFunctor (Useq p).ι) \
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS U.toFunctor U.ι) ⊆
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS (T q).toFunctor
        ((T q).ι ≫ (Useq p).ι)) := by
    rw [hTrange]
    rintro z ⟨hz, hzU⟩
    refine ⟨hz, ?_⟩
    rintro ⟨z', hz'⟩
    apply hzU
    refine ⟨AlgebraicGeometry.Space.pointsMap B S hS (Useq (p + 1)).toFunctor
      (Subfunctor.homOfLe hple) z', ?_⟩
    rw [← pointsMap_comp_apply, Subfunctor.homOfLe_ι]
    exact hz'
  have hxT : x ∈ Set.range
      (AlgebraicGeometry.Space.pointsMap B S hS (T q).toFunctor ((T q).ι ≫ (Useq p).ι)) :=
    hstratum ⟨hxUp, hxnotU⟩
  obtain ⟨t, ht⟩ := Set.mem_range.mp hxT
  let P := pullback (T q).ι (fp q)
  let fst := pullback.fst (T q).ι (fp q)
  let lift : (T q).toFunctor ⟶ P := inv fst
  have hlift : lift ≫ fst = 𝟙 _ := by
    simp [lift, fst]
  let g : (T q).toFunctor ⟶ yoneda.obj (Vp q) :=
    lift ≫ pullback.snd (T q).ι (fp q)
  have hg : g ≫ fp q = (T q).ι := by
    dsimp [g]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hlift, Category.id_comp]
  obtain ⟨tp, rfl⟩ := Quot.exists_rep t
  let r := AlgebraicGeometry.Space.FieldValuedPoint.map B S hS (T q).toFunctor g tp
  have hrX : AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj (Vp q))
        (fp q ≫ (Useq p).ι) r.class = x := by
    calc
      AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj (Vp q))
          (fp q ≫ (Useq p).ι) r.class =
      AlgebraicGeometry.Space.pointsMap B S hS (T q).toFunctor
            (g ≫ fp q ≫ (Useq p).ι) tp.class := by
              dsimp only [r]
              rw [← AlgebraicGeometry.Space.pointsMap_class]
              exact (pointsMap_comp_apply _ _ _ g (fp q ≫ (Useq p).ι) tp.class).symm
      _ = AlgebraicGeometry.Space.pointsMap B S hS (T q).toFunctor
            ((g ≫ fp q) ≫ (Useq p).ι) tp.class := by rw [← Category.assoc]
      _ = AlgebraicGeometry.Space.pointsMap B S hS (T q).toFunctor
            ((T q).ι ≫ (Useq p).ι) tp.class := by rw [hg]
      _ = x := ht
  let Xp := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (Vp q)
  let y := AlgebraicGeometry.Space.schemePoint B S hS (Vp q) r
  obtain ⟨A, hAbasis, hyA, -⟩ :=
    Xp.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  obtain ⟨Vop, hVop⟩ := hAbasis
  have hyVop : y ∈ Vop := by
    show y ∈ (Vop : Set Xp)
    rw [hVop.2]
    exact hyA
  let Vsite : B.Schemes :=
    ⟨AlgebraicGeometry.Scheme.Opens.toScheme Vop,
      (Scheme.size_coe_opens_le _ Vop).trans_lt (Vp q).left.2⟩
  let jleft : Vsite ⟶ (Vp q).left :=
    ObjectProperty.homMk (AlgebraicGeometry.Scheme.Opens.ι Vop)
  let V : AlgebraicGeometry.BigFppfOver B S hS := Over.mk (jleft ≫ (Vp q).hom)
  let j : V ⟶ Vp q := Over.homMk jleft
  have hVaff : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V) := by
    show IsAffine (AlgebraicGeometry.Scheme.Opens.toScheme Vop)
    exact hVop.1
  have hjOpen : AlgebraicGeometry.IsOpenImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j) := by
    show AlgebraicGeometry.IsOpenImmersion (Scheme.Opens.ι Vop)
    infer_instance
  have hjEtale : AlgebraicGeometry.Space.IsEtale B S hS (yoneda.map j) :=
    isEtale_of_isOpenImmersion_aux (isOpenImmersion_yoneda_map_aux B S hS j hjOpen)
  let fUp : yoneda.obj V ⟶ (Useq p).toFunctor := yoneda.map j ≫ fp q
  have hfUp : AlgebraicGeometry.Space.IsEtale B S hS fUp :=
    isEtale_comp_aux (yoneda.map j) (fp q) hjEtale hfetale
  let fX : yoneda.obj V ⟶ X := fUp ≫ (Useq p).ι
  have hfX : AlgebraicGeometry.Space.IsEtale B S hS fX :=
    isEtale_comp_aux fUp (Useq p).ι hfUp (isEtale_of_isOpenImmersion_aux hUp.2)
  let := hjOpen
  have hyrange : y ∈ Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j) := by
    show y ∈ Set.range (Scheme.Opens.ι Vop)
    simpa using hyVop
  obtain ⟨rv, hrv⟩ := fieldPoint_factors_through_open B S hS j r hyrange
  have hxV : x ∈ Set.range (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj V) fX) := by
    refine ⟨rv.class, ?_⟩
    show AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj V)
      ((yoneda.map j ≫ fp q) ≫ (Useq p).ι) rv.class = x
    rw [Category.assoc, pointsMap_comp_apply _ _ _, hrv]
    exact hrX
  obtain ⟨W, hW, hUW, f, hf, hrange⟩ := exists_openSubspace_union_range
    B S hS hX (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V) U hU fX hfX
  have hUWlt : U < W := lt_of_le_of_ne hUW (by
    intro heq
    have hxW : x ∈ Set.range (AlgebraicGeometry.Space.pointsMap B S hS W.toFunctor W.ι) := by
      rw [hrange]
      exact Or.inr hxV
    exact hxnotU (heq.symm ▸ hxW))
  have hsquare : AlgebraicGeometry.Space.IsElementaryDistinguishedSquare B S hS hW.1
      (Subfunctor.range (Subfunctor.homOfLe hUW)) f :=
    elementaryDistinguishedSquare_of_etale_neighborhood B S hS hX
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (Vp q))
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V)
      U (Useq p) W hU hUp hW hUW (T q) hTclosed (fp q) hfetale
      (yoneda.map j) (isOpenImmersion_yoneda_map_aux B S hS j hjOpen) f
      (by simpa only [fX, fUp, Category.assoc] using hf)
      (by simpa only [hf] using hrange) hstratum
  obtain ⟨D, d, hDaff, hdOpen, hdDense⟩ :=
    exists_dense_affine_openImmersion B S hS hZ X hX hXnoeth U hU
  obtain ⟨E, iE, jE, hEaff, eE, hiE, hjE⟩ :=
    exists_affine_coproduct B S hS V D hVaff hDaff
  let K : Bool → AlgebraicGeometry.BigFppfOver B S hS := fun b => cond b V D
  let k : ∀ b, K b ⟶ E := fun b => Bool.rec jE iE b
  obtain ⟨hkm, hkcover, hkdisjoint⟩ := binary_coproduct_cover B S hS iE jE eE hiE hjE
  let uW := Subfunctor.homOfLe hUW
  let φ : ∀ b, yoneda.obj (K b) ⟶ W.toFunctor := fun b => Bool.rec (d ≫ uW) f b
  obtain ⟨fE, hfacE⟩ := exists_yoneda_desc_of_disjoint_cover
    (AlgebraicGeometry.BigFppfOver.topology B S hS) K E k hkm hkcover hkdisjoint
    W.toFunctor hW.1.isSheaf φ
  have hfi : yoneda.map iE ≫ fE = f := hfacE true
  have hfj : yoneda.map jE ≫ fE = d ≫ uW := hfacE false
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have hkOpen : ∀ b, AlgebraicGeometry.IsOpenImmersion (G.map (k b)) := by
    intro b
    cases b
    · show AlgebraicGeometry.IsOpenImmersion (G.map jE)
      rw [← hjE]
      infer_instance
    · show AlgebraicGeometry.IsOpenImmersion (G.map iE)
      rw [← hiE]
      infer_instance
  have hfD : AlgebraicGeometry.Space.IsEtale B S hS (d ≫ uW) := by
    apply AlgebraicGeometry.Space.isEtale_of_isEtale_over B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS D) hW.1 hX
      (d ≫ uW) (d ≫ U.ι) W.ι
      (isEtale_comp_aux d U.ι (isEtale_of_isOpenImmersion_aux hdOpen)
        (isEtale_of_isOpenImmersion_aux hU.2)) (isEtale_of_isOpenImmersion_aux hW.2)
    simp only [Category.assoc, uW, Subfunctor.homOfLe_ι]
  have hfE : AlgebraicGeometry.Space.IsEtale B S hS fE := by
    apply isEtale_of_scheme_openCover B S hS hW.1 fE K k hkOpen
    · intro z
      obtain ⟨z, rfl⟩ := eE.hom.homeomorph.surjective z
      obtain ⟨z, rfl⟩ := (coprodMk (G.obj V) (G.obj D)).surjective z
      cases z with
      | inl v =>
        refine ⟨true, v, ?_⟩
        show G.map iE v = _
        rw [← hiE]
        simp only [coprodMk_inl, Scheme.Hom.comp_apply]
        rfl
      | inr d =>
        refine ⟨false, d, ?_⟩
        show G.map jE d = _
        rw [← hjE]
        simp only [coprodMk_inr, Scheme.Hom.comp_apply]
        rfl
    · intro b
      cases b
      · show AlgebraicGeometry.Space.IsEtale B S hS (yoneda.map jE ≫ fE)
        rw [hfj]
        exact hfD
      · show AlgebraicGeometry.Space.IsEtale B S hS (yoneda.map iE ≫ fE)
        rw [hfi]
        exact hsquare.isEtale
  have hrangeE :
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS W.toFunctor W.ι) =
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS U.toFunctor U.ι) ∪
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj E) (fE ≫ W.ι)) := by
    apply Set.Subset.antisymm
    · rw [hrange]
      rintro z (hz | ⟨v, rfl⟩)
      · exact Or.inl hz
      · right
        refine ⟨AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj V) (yoneda.map iE) v, ?_⟩
        rw [← pointsMap_comp_apply, ← Category.assoc, hfi, hf]
    · rintro z (⟨v, rfl⟩ | ⟨v, rfl⟩)
      · refine ⟨AlgebraicGeometry.Space.pointsMap B S hS U.toFunctor uW v, ?_⟩
        rw [← pointsMap_comp_apply, Subfunctor.homOfLe_ι]
      · exact ⟨AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj E) fE v,
          (pointsMap_comp_apply _ _ _ fE W.ι v).symm⟩
  let C := Subfunctor.range uW
  let Z := AlgebraicGeometry.Space.reducedClosedSubspace B S hS W.toFunctor hW.1
    (Set.range (AlgebraicGeometry.Space.pointsMap B S hS C.toFunctor C.ι))ᶜ
      hsquare.isClosedComplement
  have hZclosed := AlgebraicGeometry.Space.isClosedSubspace_reducedClosedSubspace
    B S hS W.toFunctor hW.1
    (Set.range (AlgebraicGeometry.Space.pointsMap B S hS C.toFunctor C.ι))ᶜ
      hsquare.isClosedComplement
  have hZrangeEq := AlgebraicGeometry.Space.range_pointsMap_ι_reducedClosedSubspace
    B S hS W.toFunctor hW.1
    (Set.range (AlgebraicGeometry.Space.pointsMap B S hS C.toFunctor C.ι))ᶜ
      hsquare.isClosedComplement
  have hisoE : IsIso (Z.fromPreimage fE) := by
    let : IsIso (Z.fromPreimage f) := hsquare.isIsoOverComplement
    apply isIso_fromPreimage_of_factorsThrough_open B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS E) Z hZclosed
      (yoneda.map iE) (isOpenImmersion_yoneda_map_aux B S hS iE (hkOpen true)) f fE hfi
    rintro z ⟨v, rfl⟩
    rcases binary_coproduct_points_cover B S hS iE jE eE hiE hjE
      (AlgebraicGeometry.Space.pointsMap B S hS (Z.preimage fE).toFunctor (Z.preimage fE).ι v)
      with hv | ⟨d', hd'⟩
    · exact hv
    · exfalso
      have hzin : AlgebraicGeometry.Space.pointsMap B S hS (Z.preimage fE).toFunctor
          ((Z.preimage fE).ι ≫ fE) v ∈
          Set.range (AlgebraicGeometry.Space.pointsMap B S hS C.toFunctor C.ι) := by
        refine ⟨AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj D)
          (d ≫ Subfunctor.toRange uW) d', ?_⟩
        rw [← pointsMap_comp_apply, Category.assoc, Subfunctor.toRange_ι]
        rw [← hfj, pointsMap_comp_apply _ _ _, pointsMap_comp_apply _ _ _, hd']
      have hzn : AlgebraicGeometry.Space.pointsMap B S hS (Z.preimage fE).toFunctor
          ((Z.preimage fE).ι ≫ fE) v ∉
          Set.range (AlgebraicGeometry.Space.pointsMap B S hS C.toFunctor C.ι) := by
        rw [← (CategoryTheory.Subfunctor.isPullback_preimage fE Z).w, pointsMap_comp_apply _ _ _]
        have hz : AlgebraicGeometry.Space.pointsMap B S hS Z.toFunctor Z.ι
            (AlgebraicGeometry.Space.pointsMap B S hS (Z.preimage fE).toFunctor
              (Z.fromPreimage fE) v) ∈
            Set.range (AlgebraicGeometry.Space.pointsMap B S hS Z.toFunctor Z.ι) :=
          Set.mem_range_self _
        rw [hZrangeEq] at hz
        exact hz
      exact hzn hzin
  have hsquareE : AlgebraicGeometry.Space.IsElementaryDistinguishedSquare B S hS hW.1 C fE :=
    ⟨AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS E,
      hsquare.isOpenSubspace, hfE, hsquare.isClosedComplement, hisoE⟩
  refine ⟨E, W, hW, hUWlt, fE, hEaff,
    isEtale_comp_aux fE W.ι hfE (isEtale_of_isOpenImmersion_aux hW.2), hrangeE, hsquareE, ?_⟩
  apply denseRange_pullback_fst_of_lift B S hS hU.1 U.ι (fE ≫ W.ι)
    d (yoneda.map jE) _ hdDense
  rw [← Category.assoc, hfj, Category.assoc, Subfunctor.homOfLe_ι]

end AlgebraicGeometry.Space

end
