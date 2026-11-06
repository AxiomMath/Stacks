module

public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafGivesSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValued
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleJointlyEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleModificationSites

/-!
# Sheaves glued along a spaces-étale modification square are representable

Let `j ≫ f = g ≫ i` be a commutative square of algebraic spaces over `S` whose sheaf-level
restriction functor `F ↦ (f⁻¹ F, i⁻¹ F)` on the spaces-étale topoi is an equivalence. A
spaces-étale sheaf `𝓕` on `X` whose restriction is isomorphic to `(h_{V'}, h_W, h_α)`, for
algebraic spaces `V'` étale over `Y` and `W` étale over `Z`, is represented by an algebraic space
étale over `X`; consequently the site-level restriction functor `V ↦ (V ×_X Y, V ×_X Z)` is an
equivalence.

Fixing a surjective étale chart `X₀` of `X`, the affine schemes étale over `X₀` cover every
algebraic space étale over `X` through each of its points, and a family of them of bounded size
has a disjoint union in the site along which sections of spaces-étale sheaves glue.

## Main definitions

* `AlgebraicGeometry.Space.IsCompactChartOver`: an étale chart of `X` whose scheme is
  quasi-compact and étale over a fixed chart `X₀`.

## Main results

* `CategoryTheory.Limits.CategoricalPullback.epi_of_epi_fst_of_epi_snd`: a morphism of a
  categorical pullback with epimorphic components is an epimorphism.
* `AlgebraicGeometry.Space.exists_isCompactChartOver_hom`: such charts cover every algebraic space
  étale over `X` through each of its points.
* `AlgebraicGeometry.Space.exists_glued_isCompactChartOver`: a uniformly bounded family of such
  charts has a disjoint union in the site, along which sections of spaces-étale sheaves glue.
* `AlgebraicGeometry.Space.exists_iso_yoneda_of_spacesModificationRestriction`: a sheaf whose
  restriction is representable is representable, when the sheaf-level restriction functor is an
  equivalence.
* `AlgebraicGeometry.Space.isEquivalence_spacesEtaleModificationRestriction_of_isEquivalence`:
  the site-level restriction functor is an equivalence as soon as the sheaf-level one is.

## References

* [Stacks Project, Tag 0GG1](https://stacks.math.columbia.edu/tag/0GG1)
* [Stacks Project, Tag 0GF6](https://stacks.math.columbia.edu/tag/0GF6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace CategoryTheory.Limits.CategoricalPullback

variable {A B C : Type*} [Category* A] [Category* B] [Category* C] {F : A ⥤ B} {G : C ⥤ B}

/-- A morphism of a categorical pullback whose two components are epimorphisms is an
epimorphism. -/
theorem epi_of_epi_fst_of_epi_snd {x y : CategoricalPullback F G} (a : x ⟶ y) [Epi a.fst]
    [Epi a.snd] : Epi a :=
  ⟨fun {z} b c h => CategoricalPullback.hom_ext
    ((cancel_epi a.fst).1 (by simpa using congrArg Hom.fst h))
    ((cancel_epi a.snd).1 (by simpa using congrArg Hom.snd h))⟩

end CategoryTheory.Limits.CategoricalPullback

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Bounded charts -/

section Charts

attribute [local instance] pointTopology

variable {X : AlgebraicSpaces B S hS}

/-- An étale chart `T` of `X` *over* a chart `X₀` of `X`: the scheme of `T` is quasi-compact and
the chart factors as an étale morphism of schemes `T ⟶ X₀` followed by the chart `X₀`. -/
def IsCompactChartOver (X₀ T : SmallEtale B S hS X.1) : Prop :=
  CompactSpace ((BigFppfOver.toScheme B S hS).obj T.1.left) ∧
    ∃ d : T.1.left ⟶ X₀.1.left, Etale ((BigFppfOver.toScheme B S hS).map d) ∧
      T.1.hom = yoneda.map d ≫ X₀.1.hom

/-- A chart over `X₀` is at most as large as `X₀`. -/
theorem IsCompactChartOver.size_le {X₀ T : SmallEtale B S hS X.1}
    (h : IsCompactChartOver B S hS X₀ T) :
    ((BigFppfOver.toScheme B S hS).obj T.1.left).size ≤
      ((BigFppfOver.toScheme B S hS).obj X₀.1.left).size := by
  obtain ⟨hc, d, hd, -⟩ := h
  exact Scheme.size_le_of_locallyOfFiniteType ((BigFppfOver.toScheme B S hS).map d)

/-- **Charts over a surjective chart cover.** Let `X₀` be an étale chart of `X` surjective on
points. Through every point of an algebraic space `U` étale over `X` passes a morphism to `U`
from (the algebraic space of) an affine scheme étale over `X₀`. -/
theorem exists_isCompactChartOver_hom (X₀ : SmallEtale B S hS X.1)
    (hX₀ : IsSurjective B S hS X₀.1.hom) (U : SpacesEtale B S hS X)
    (u : points B S hS ((SpacesEtale.toSpaces B S hS X).obj U).1) :
    ∃ (T : SmallEtale B S hS X.1) (_ : IsCompactChartOver B S hS X₀ T)
      (t : (comparisonFunctor B S hS X).obj T ⟶ U)
      (τ : points B S hS ((SpacesEtale.toSpaces B S hS X).obj
        ((comparisonFunctor B S hS X).obj T)).1),
      pointsMap B S hS _ ((SpacesEtale.toSpaces B S hS X).map t).hom τ = u := by
  let U' := (SpacesEtale.toSpaces B S hS X).obj U
  obtain ⟨U₀, hU₀⟩ := exists_surjective_smallEtale_chart B S hS U'.1 U'.2
  let U₁ := (smallEtalePostcomp B S hS U.1.hom U.2).obj U₀
  let φU : yoneda.obj U₁.1.left ⟶ U'.1 := U₀.1.hom
  have hφU : φU ≫ U.1.hom.hom = U₁.1.hom := rfl
  obtain ⟨hrep, hP⟩ := U₁.2
  let g := X₀.1.hom
  let Q := hrep.pullback g
  have hsq : IsPullback (hrep.fst g) (yoneda.map (hrep.snd g)) U₁.1.hom g :=
    hrep.isPullback g
  have hQ : Etale ((BigFppfOver.toScheme B S hS).map (hrep.snd g)) :=
    hP g (hrep.fst g) (hrep.snd g) hsq
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : points B S hS (yoneda.obj U₁.1.left),
      pointsMap B S hS _ φU u₀ = u := hU₀ u
  obtain ⟨v, hv⟩ := hX₀ (pointsMap B S hS _ U₁.1.hom u₀)
  obtain ⟨q, hq₁, hq₂⟩ := exists_points_of_isPullback B S hS hsq u₀ v hv.symm
  set q' := schemePointsHomeomorph B S hS Q q with hq'
  obtain ⟨O, hO, hqO, -⟩ : ∃ O ∈ ((BigFppfOver.toScheme B S hS).obj Q).affineOpens,
      q' ∈ O ∧ O ≤ ⊤ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens _)
      (show q' ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj Q).Opens) from trivial)
  let ι₀ := openSubHom Q O
  let d := ι₀ ≫ hrep.snd g
  have hd : Etale ((BigFppfOver.toScheme B S hS).map d) := by
    have := etale_toScheme_map_openSubHom B S hS Q O
    rw [Functor.map_comp]
    infer_instance
  let T : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk (yoneda.map d ≫ X₀.1.hom),
      etale_comp_of_scheme B S hS d X₀.1.hom hd X₀.2⟩
  have hT : IsCompactChartOver B S hS X₀ T := by
    refine ⟨?_, d, hd, rfl⟩
    have : IsAffine (O : Scheme.{u}) := hO
    show CompactSpace (O : Scheme.{u})
    infer_instance
  have hw : (yoneda.map ι₀ ≫ hrep.fst g ≫ φU) ≫ U.1.hom.hom = yoneda.map d ≫ X₀.1.hom := by
    rw [Category.assoc, Category.assoc, hφU, hsq.w, Functor.map_comp, Category.assoc]
  let t : (comparisonFunctor B S hS X).obj T ⟶ U :=
    ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk
      (yoneda.map ι₀ ≫ hrep.fst g ≫ φU)) (ObjectProperty.hom_ext _ hw))
  let τ₀ : (BigFppfOver.toScheme B S hS).obj (openSub Q O) := ⟨q', hqO⟩
  refine ⟨T, hT, t, (schemePointsHomeomorph B S hS (openSub Q O)).symm τ₀, ?_⟩
  show pointsMap B S hS _ (yoneda.map ι₀ ≫ hrep.fst g ≫ φU)
    ((schemePointsHomeomorph B S hS (openSub Q O)).symm τ₀) = u
  have hι : ((BigFppfOver.toScheme B S hS).map ι₀) τ₀ = q' := by
    rw [toScheme_map_openSubHom]
    rfl
  rw [pointsMap_comp_apply, pointsMap_comp_apply, schemePointsHomeomorph_symm_naturality, hι,
    hq', Homeomorph.symm_apply_apply, hq₁, hu₀]

/-- **Sections over charts over `X₀` are jointly epimorphic.** Two morphisms out of a
spaces-étale sheaf `G` on `X` which agree after composing with every section of `G` over an
affine scheme étale over a surjective chart `X₀` are equal. -/
theorem eq_of_isCompactChartOver_comp_eq (X₀ : SmallEtale B S hS X.1)
    (hX₀ : IsSurjective B S hS X₀.1.hom)
    {G H : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1))}
    (α β : G ⟶ H)
    (h : ∀ (T : SmallEtale B S hS X.1), IsCompactChartOver B S hS X₀ T →
      ∀ e : (SpacesEtale.topology B S hS X).yoneda.obj ((comparisonFunctor B S hS X).obj T) ⟶ G,
        e ≫ α = e ≫ β) :
    α = β := by
  let J := SpacesEtale.topology B S hS X
  have key : ∀ (T : SmallEtale B S hS X.1), IsCompactChartOver B S hS X₀ T →
      ∀ {U : SpacesEtale B S hS X} (t : (comparisonFunctor B S hS X).obj T ⟶ U)
        (x : G.obj.obj (op U)),
        α.hom.app _ (G.obj.map t.op x) = β.hom.app _ (G.obj.map t.op x) := by
    intro T hT U t x
    have h' := congrArg J.yonedaEquiv (h T hT (J.yonedaEquiv.symm (G.obj.map t.op x)))
    rwa [GrothendieckTopology.yonedaEquiv_comp, GrothendieckTopology.yonedaEquiv_comp,
      Equiv.apply_symm_apply] at h'
  ext U x
  let I : Type (u + 1) := Σ T : {T : SmallEtale B S hS X.1 // IsCompactChartOver B S hS X₀ T},
    ((comparisonFunctor B S hS X).obj T.1 ⟶ U.unop)
  let E : PreZeroHypercover.{u + 1} U.unop :=
    ⟨I, fun i => (comparisonFunctor B S hS X).obj i.1.1, fun i => i.2⟩
  have hE : SpacesEtale.IsCovering B S hS X ⟨U.unop, E⟩ := fun y => by
    obtain ⟨T, hT, t, τ, hτ⟩ := exists_isCompactChartOver_hom B S hS X₀ hX₀ U.unop y
    exact ⟨⟨⟨T, hT⟩, t⟩, τ, hτ⟩
  have hmem : Sieve.generate E.presieve₀ ∈ J U.unop :=
    Precoverage.generate_mem_toGrothendieck ⟨E, rfl, hE⟩
  have hsep := ((isSheaf_iff_isSheaf_of_type _ _).1 H.property).isSeparated _ hmem
  refine hsep.ext fun V f hf => ?_
  obtain ⟨W, k, t, ⟨i⟩, rfl⟩ := hf
  show H.obj.map (k ≫ E.f i).op (α.hom.app U x) = H.obj.map (k ≫ E.f i).op (β.hom.app U x)
  rw [← NatTrans.naturality_apply α.hom (k ≫ E.f i).op x,
    ← NatTrans.naturality_apply β.hom (k ≫ E.f i).op x, op_comp, Functor.map_comp_apply,
    NatTrans.naturality_apply α.hom k.op, NatTrans.naturality_apply β.hom k.op,
    key i.1.1 i.1.2 i.2 x]

end Charts

/-! ### Inverse images of sections into a representable sheaf -/

section Restriction

variable {X Y : AlgebraicSpaces B S hS} (k : Y ⟶ X)
  {G : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1))} {V' : SpacesEtale B S hS Y}
  (ε : (spacesEtaleInverseImage B S hS k).obj G ≅ (SpacesEtale.topology B S hS Y).yoneda.obj V')

/-- The morphism `U ×_X Y ⟶ V'` of the spaces-étale site of `Y` which represents, through
`h_{U ×_X Y} ≅ k⁻¹ h_U` and an identification `k⁻¹ G ≅ h_{V'}`, the inverse image along
`k : Y ⟶ X` of a section `e : h_U ⟶ G` over an object `U` of the spaces-étale site of `X`. -/
def restrictArrow {U : SpacesEtale B S hS X}
    (e : (SpacesEtale.topology B S hS X).yoneda.obj U ⟶ G) :
    (spacesBaseChange B S hS k).functor.obj U ⟶ V' :=
  (SpacesEtale.topology B S hS Y).yonedaFullyFaithful.preimage
    ((baseChangeYonedaIso B S hS k U).inv ≫ (spacesEtaleInverseImage B S hS k).map e ≫ ε.hom)

/-- The Yoneda image of `AlgebraicGeometry.Space.restrictArrow` is the composite of the inverse
image of the section with the identifications `h_{U ×_X Y} ≅ k⁻¹ h_U` and `k⁻¹ G ≅ h_{V'}`. -/
theorem yoneda_map_restrictArrow {U : SpacesEtale B S hS X}
    (e : (SpacesEtale.topology B S hS X).yoneda.obj U ⟶ G) :
    (SpacesEtale.topology B S hS Y).yoneda.map (restrictArrow B S hS k ε e) =
      (baseChangeYonedaIso B S hS k U).inv ≫ (spacesEtaleInverseImage B S hS k).map e ≫
        ε.hom :=
  (SpacesEtale.topology B S hS Y).yonedaFullyFaithful.map_preimage _

/-- `AlgebraicGeometry.Space.restrictArrow` is natural in the object carrying the section. -/
theorem restrictArrow_comp {U U' : SpacesEtale B S hS X} (t : U ⟶ U')
    (e : (SpacesEtale.topology B S hS X).yoneda.obj U' ⟶ G) :
    restrictArrow B S hS k ε ((SpacesEtale.topology B S hS X).yoneda.map t ≫ e) =
      (spacesBaseChange B S hS k).functor.map t ≫ restrictArrow B S hS k ε e := by
  apply (SpacesEtale.topology B S hS Y).yonedaFullyFaithful.map_injective
  have hn := (baseChangeYonedaNatIso B S hS k).inv.naturality t
  dsimp only [baseChangeYonedaNatIso, Functor.comp_map, NatIso.ofComponents_inv_app] at hn
  rw [yoneda_map_restrictArrow, Functor.map_comp (spacesEtaleInverseImage B S hS k),
    Functor.map_comp (SpacesEtale.topology B S hS Y).yoneda, yoneda_map_restrictArrow,
    reassoc_of% hn]
  simp only [Category.assoc]

/-- **The inverse images along `k` of sections over charts over `X₀` cover `V'`.** If
`k⁻¹ G ≅ h_{V'}`, then through every point of `V'` passes the morphism representing the inverse
image along `k` of some section of `G` over an affine scheme étale over a surjective chart `X₀`
of `X`. -/
theorem exists_isCompactChartOver_restrictArrow (X₀ : SmallEtale B S hS X.1)
    (hX₀ : IsSurjective B S hS X₀.1.hom)
    (x : points B S hS ((SpacesEtale.toSpaces B S hS Y).obj V').1) :
    ∃ (T : SmallEtale B S hS X.1) (_ : IsCompactChartOver B S hS X₀ T)
      (e : (SpacesEtale.topology B S hS X).yoneda.obj ((comparisonFunctor B S hS X).obj T) ⟶ G)
      (q : points B S hS ((SpacesEtale.toSpaces B S hS Y).obj
        ((spacesBaseChange B S hS k).functor.obj ((comparisonFunctor B S hS X).obj T))).1),
      pointsMap B S hS _ ((SpacesEtale.toSpaces B S hS Y).map (restrictArrow B S hS k ε e)).hom q =
        x := by
  have hjoint : ∀ (H : Sheaf (SpacesEtale.topology B S hS Y) (Type (u + 1)))
      (α β : (SpacesEtale.topology B S hS Y).yoneda.obj V' ⟶ H),
      (∀ κ : Σ T : {T : SmallEtale B S hS X.1 // IsCompactChartOver B S hS X₀ T},
          (SpacesEtale.topology B S hS X).yoneda.obj ((comparisonFunctor B S hS X).obj T.1) ⟶ G,
        (SpacesEtale.topology B S hS Y).yoneda.map (restrictArrow B S hS k ε κ.2) ≫ α =
          (SpacesEtale.topology B S hS Y).yoneda.map (restrictArrow B S hS k ε κ.2) ≫ β) →
      α = β := by
    intro H α β hαβ
    suffices h : ε.hom ≫ α = ε.hom ≫ β by
      simpa using congrArg (ε.inv ≫ ·) h
    apply ((spacesEtaleAdjunction B S hS k).homEquiv _ _).injective
    apply eq_of_isCompactChartOver_comp_eq B S hS X₀ hX₀
    intro T hT e
    rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_left]
    congr 1
    have h₁ := hαβ ⟨⟨T, hT⟩, e⟩
    simp only [yoneda_map_restrictArrow, Category.assoc] at h₁
    simpa only [Category.assoc] using (cancel_epi _).1 h₁
  obtain ⟨⟨⟨T, hT⟩, e⟩, q, hq⟩ := SpacesEtale.exists_points_of_jointlyEpi B S hS
    (fun κ : Σ T : {T : SmallEtale B S hS X.1 // IsCompactChartOver B S hS X₀ T},
      (SpacesEtale.topology B S hS X).yoneda.obj ((comparisonFunctor B S hS X).obj T.1) ⟶ G =>
        restrictArrow B S hS k ε κ.2) hjoint x
  exact ⟨T, hT, e, q, hq⟩

end Restriction

/-! ### Glueing charts over `X₀` -/

section Glue

attribute [local instance] pointTopology

variable {X : AlgebraicSpaces B S hS}

/-- **A bounded family of charts over `X₀` has a disjoint union in the site, along which
sections of spaces-étale sheaves glue.** Let `T i` be charts of `X` over a chart `X₀`, indexed by
a set of cardinality at most `μ`, with `X₀` of size at most `μ < B.cutoff`. Then there is a
chart `V` of `X` with morphisms `T i ⟶ V` such that every family of sections `h_{T i} ⟶ G` of a
spaces-étale sheaf `G` is the restriction of a section `h_V ⟶ G`. -/
theorem exists_glued_isCompactChartOver (X₀ : SmallEtale B S hS X.1) {ι : Type u}
    (T : ι → SmallEtale B S hS X.1) (hT : ∀ i, IsCompactChartOver B S hS X₀ (T i))
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff) (hι : #ι ≤ μ)
    (hX₀ : ((BigFppfOver.toScheme B S hS).obj X₀.1.left).size ≤ μ) :
    ∃ (V : SmallEtale B S hS X.1) (c : ∀ i, T i ⟶ V),
      ∀ (G : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)))
        (e : ∀ i, (SpacesEtale.topology B S hS X).yoneda.obj
          ((comparisonFunctor B S hS X).obj (T i)) ⟶ G),
        ∃ e' : (SpacesEtale.topology B S hS X).yoneda.obj
            ((comparisonFunctor B S hS X).obj V) ⟶ G,
          ∀ i, (SpacesEtale.topology B S hS X).yoneda.map
            ((comparisonFunctor B S hS X).map (c i)) ≫ e' = e i := by
  classical
  have hsize : ∀ i, ((BigFppfOver.toScheme B S hS).obj (T i).1.left).size ≤ μ :=
    fun i => (hT i).size_le.trans hX₀
  have hℵ : ℵ₀ ≤ μ := (Scheme.aleph0_le_size _).trans hX₀
  obtain ⟨Z, j, hjopen, hjdisj, hjcov⟩ :=
    BigFppfOver.exists_coproduct_of_size_le B S hS (fun i => (T i).1.left) hℵ hμ hι hsize
  have hT' : ∀ i, ∃ d : (T i).1.left ⟶ X₀.1.left, Etale ((BigFppfOver.toScheme B S hS).map d) ∧
      (T i).1.hom = yoneda.map d ≫ X₀.1.hom := fun i => (hT i).2
  choose d hd hTd using hT'
  have hH : Presieve.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj X₀.1.left) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj X₀.1.left)
  obtain ⟨dd, hdd⟩ := BigFppfOver.exists_section_of_disjoint_openCover hH j hjopen hjdisj
    hjcov (H := yoneda.obj X₀.1.left) d
  have hdd' : ∀ i, j i ≫ dd = d i := hdd
  have hdde : Etale ((BigFppfOver.toScheme B S hS).map dd) := by
    let 𝒰 : ((BigFppfOver.toScheme B S hS).obj Z).OpenCover.{u} :=
      { I₀ := ι
        X := fun i => (BigFppfOver.toScheme B S hS).obj (T i).1.left
        f := fun i => (BigFppfOver.toScheme B S hS).map (j i)
        mem₀ := by
          rw [Scheme.presieve₀_mem_precoverage_iff]
          exact ⟨hjcov, hjopen⟩ }
    have : IsZariskiLocalAtSource (@Etale.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u}) (Q := RingHom.Etale)
    refine IsZariskiLocalAtSource.of_openCover 𝒰 fun i => ?_
    have hfac : 𝒰.f i ≫ (BigFppfOver.toScheme B S hS).map dd =
        (BigFppfOver.toScheme B S hS).map (d i) := by
      show (BigFppfOver.toScheme B S hS).map (j i) ≫ _ = _
      rw [← Functor.map_comp, hdd' i]
    rw [hfac]
    exact hd i
  let V : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk (yoneda.map dd ≫ X₀.1.hom),
      etale_comp_of_scheme B S hS dd X₀.1.hom hdde X₀.2⟩
  let c : ∀ i, T i ⟶ V := fun i => ObjectProperty.homMk (CostructuredArrow.homMk (j i) (by
    show yoneda.map (j i) ≫ yoneda.map dd ≫ X₀.1.hom = (T i).1.hom
    rw [hTd i, ← Category.assoc, ← Functor.map_comp, hdd' i]))
  refine ⟨V, c, fun G e => ?_⟩
  let J := SpacesEtale.topology B S hS X
  let C := comparisonFunctor B S hS X
  let p : ∀ k : ULift.{u + 1} ι, C.obj (T k.down) ⟶ C.obj V := fun k => C.map (c k.down)
  have hpmono : ∀ i, Mono (j i) := fun i =>
    have := hjopen i
    (BigFppfOver.toScheme B S hS).mono_of_mono_map (IsOpenImmersion.mono _)
  have hcov : SpacesEtale.IsCovering B S hS X
      ⟨C.obj V, ⟨ULift.{u + 1} ι, fun k => C.obj (T k.down), p⟩⟩ := by
    intro y
    obtain ⟨i, w, hw⟩ := hjcov (schemePointsHomeomorph B S hS Z y)
    refine ⟨⟨i⟩, (schemePointsHomeomorph B S hS (T i).1.left).symm w, ?_⟩
    show pointsMap B S hS _ (yoneda.map (j i))
      ((schemePointsHomeomorph B S hS (T i).1.left).symm w) = y
    rw [schemePointsHomeomorph_symm_naturality, hw]
    exact (schemePointsHomeomorph B S hS Z).symm_apply_apply y
  have hmem : Sieve.generate (Presieve.ofArrows (fun k : ULift.{u + 1} ι => C.obj (T k.down)) p) ∈
      J (C.obj V) :=
    Precoverage.generate_mem_toGrothendieck ⟨_, rfl, hcov⟩
  have hGsheaf := (isSheaf_iff_isSheaf_of_type _ _).1 G.property
  have hsf : Presieve.IsSheafFor G.obj
      (Presieve.ofArrows (fun k : ULift.{u + 1} ι => C.obj (T k.down)) p) :=
    (Presieve.isSheafFor_iff_generate _).2 (hGsheaf _ hmem)
  rw [Presieve.isSheafFor_arrows_iff] at hsf
  obtain ⟨t, ht, -⟩ := hsf (fun k => J.yonedaEquiv (e k.down)) (by
    intro k k' W gi gj hij
    by_cases hkk : k = k'
    · subst hkk
      have hpm : gi = gj := by
        refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_))
        exact (cancel_mono (yoneda.map (j k.down))).1 (congrArg (fun m => m.hom.left.hom) hij)
      rw [hpm]
    · have hempty : IsEmpty (points B S hS ((SpacesEtale.toSpaces B S hS X).obj W).1) := by
        refine ⟨fun y => ?_⟩
        let a : points B S hS (yoneda.obj (T k.down).1.left) :=
          pointsMap B S hS _ gi.hom.left.hom y
        let b : points B S hS (yoneda.obj (T k'.down).1.left) :=
          pointsMap B S hS _ gj.hom.left.hom y
        have h₁ : pointsMap B S hS (yoneda.obj (T k.down).1.left) (yoneda.map (j k.down)) a =
            pointsMap B S hS (yoneda.obj (T k'.down).1.left) (yoneda.map (j k'.down)) b := by
          have e₁ := pointsMap_comp_apply B S hS gi.hom.left.hom (p k).hom.left.hom y
          have e₂ := pointsMap_comp_apply B S hS gj.hom.left.hom (p k').hom.left.hom y
          have e₃ : pointsMap B S hS _ (gi.hom.left.hom ≫ (p k).hom.left.hom) y =
              pointsMap B S hS _ (gj.hom.left.hom ≫ (p k').hom.left.hom) y :=
            congrArg (fun m : W ⟶ C.obj V =>
              pointsMap B S hS ((SpacesEtale.toSpaces B S hS X).obj W).1 m.hom.left.hom y) hij
          exact e₁.symm.trans (e₃.trans e₂)
        have h₂ := congrArg (schemePointsHomeomorph B S hS Z) h₁
        rw [← (schemePointsHomeomorph B S hS (T k.down).1.left).symm_apply_apply a,
          ← (schemePointsHomeomorph B S hS (T k'.down).1.left).symm_apply_apply b,
          schemePointsHomeomorph_symm_naturality, schemePointsHomeomorph_symm_naturality,
          Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply] at h₂
        exact hjdisj k.down k'.down (fun h => hkk (ULift.ext h)) _ _ h₂
      let E₀ : PreZeroHypercover.{u + 1} W := ⟨PEmpty, PEmpty.elim, fun i => i.elim⟩
      have hE₀ : SpacesEtale.IsCovering B S hS X ⟨W, E₀⟩ := fun y => (hempty.false y).elim
      have hsep := hGsheaf.isSeparated _ (Precoverage.generate_mem_toGrothendieck
        (J := SpacesEtale.precoverage B S hS X) ⟨E₀, rfl, hE₀⟩)
      refine hsep.ext fun Y f hf => ?_
      obtain ⟨_, _, _, ⟨i⟩, _⟩ := hf
      exact i.elim)
  refine ⟨J.yonedaEquiv.symm t, fun i => ?_⟩
  apply J.yonedaEquiv.injective
  rw [← GrothendieckTopology.yonedaEquiv_naturality, Equiv.apply_symm_apply]
  exact ht ⟨i⟩

end Glue

/-! ### The glued sheaf is representable -/

section Representable

attribute [local instance] pointTopology

variable {X Y Z E : AlgebraicSpaces B S hS} (f : Y ⟶ X) (i : Z ⟶ X) (j : E ⟶ Y) (g : E ⟶ Z)
  (w : j ≫ f = g ≫ i)

/-- If the inverse images along `k` of sections `e₁ v` over charts `T v` are represented by
morphisms hitting the points `C₁ ⟶ V'` of a surjective chart, and these sections are the
restrictions of a section `e'`, then the morphism representing `k⁻¹ e'` is surjective on points. -/
private theorem surjective_pointsMap_restrictArrow {X Y : AlgebraicSpaces B S hS} (k : Y ⟶ X)
    {G : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1))} {V' : SpacesEtale B S hS Y}
    (ε : (spacesEtaleInverseImage B S hS k).obj G ≅ (SpacesEtale.topology B S hS Y).yoneda.obj V')
    (C₁ : SmallEtale B S hS ((SpacesEtale.toSpaces B S hS Y).obj V').1)
    (hC₁ : IsSurjective B S hS C₁.1.hom)
    {T : (BigFppfOver.toScheme B S hS).obj C₁.1.left → SmallEtale B S hS X.1}
    (e₁ : ∀ v, (SpacesEtale.topology B S hS X).yoneda.obj
      ((comparisonFunctor B S hS X).obj (T v)) ⟶ G)
    (q₁ : ∀ v, points B S hS ((SpacesEtale.toSpaces B S hS Y).obj
      ((spacesBaseChange B S hS k).functor.obj ((comparisonFunctor B S hS X).obj (T v)))).1)
    (hq₁ : ∀ v, pointsMap B S hS _
      ((SpacesEtale.toSpaces B S hS Y).map (restrictArrow B S hS k ε (e₁ v))).hom (q₁ v) =
        pointsMap B S hS _ C₁.1.hom ((schemePointsHomeomorph B S hS C₁.1.left).symm v))
    {V : SmallEtale B S hS X.1} (c : ∀ v, T v ⟶ V)
    (e' : (SpacesEtale.topology B S hS X).yoneda.obj ((comparisonFunctor B S hS X).obj V) ⟶ G)
    (he' : ∀ v, (SpacesEtale.topology B S hS X).yoneda.map
      ((comparisonFunctor B S hS X).map (c v)) ≫ e' = e₁ v) :
    Function.Surjective (pointsMap B S hS _
      ((SpacesEtale.toSpaces B S hS Y).map (restrictArrow B S hS k ε e')).hom) := by
  intro x
  obtain ⟨p, hp⟩ := hC₁ x
  let v := schemePointsHomeomorph B S hS C₁.1.left p
  have key := hq₁ v
  rw [(schemePointsHomeomorph B S hS C₁.1.left).symm_apply_apply, hp,
    ← he' v, restrictArrow_comp] at key
  exact ⟨_, (pointsMap_comp_apply B S hS _ _ _).symm.trans key⟩

/-- A section of a spaces-étale sheaf whose inverse image along `k` is represented by a
morphism surjective on points has an epimorphic inverse image along `k`. -/
theorem epi_map_of_surjective_restrictArrow {X Y : AlgebraicSpaces B S hS} (k : Y ⟶ X)
    {G : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1))} {V' : SpacesEtale B S hS Y}
    (ε : (spacesEtaleInverseImage B S hS k).obj G ≅ (SpacesEtale.topology B S hS Y).yoneda.obj V')
    {U : SpacesEtale B S hS X} (e : (SpacesEtale.topology B S hS X).yoneda.obj U ⟶ G)
    (he : Function.Surjective (pointsMap B S hS _
      ((SpacesEtale.toSpaces B S hS Y).map (restrictArrow B S hS k ε e)).hom)) :
    Epi ((spacesEtaleInverseImage B S hS k).map e) := by
  have h₁ := SpacesEtale.epi_yoneda_map_of_surjective B S hS _ he
  rw [yoneda_map_restrictArrow] at h₁
  have h₂ : (spacesEtaleInverseImage B S hS k).map e = (baseChangeYonedaIso B S hS k U).hom ≫
      ((baseChangeYonedaIso B S hS k U).inv ≫ (spacesEtaleInverseImage B S hS k).map e ≫
        ε.hom) ≫ ε.inv := by
    simp
  rw [h₂]
  infer_instance

/-- **A sheaf with representable restriction is representable.** Suppose the sheaf-level
restriction functor `F ↦ (f⁻¹ F, i⁻¹ F)` of a commutative square `j ≫ f = g ≫ i` of algebraic
spaces is an equivalence. If the restriction of a spaces-étale sheaf `G` on `X` is isomorphic to
`(h_{V'}, h_W, h_α)` for an object `(V', W, α)` of the categorical pullback of the spaces-étale
sites, then `G` is represented by an algebraic space étale over `X`. -/
theorem exists_iso_yoneda_of_spacesModificationRestriction
    [(spacesModificationRestriction B S hS f i j g w).IsEquivalence]
    (G : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)))
    (A : CategoricalPullback (spacesBaseChange B S hS j).functor
      (spacesBaseChange B S hS g).functor)
    (φ : (spacesModificationRestriction B S hS f i j g w).obj G ≅
      (spacesEtaleModificationYoneda B S hS j g).obj A) :
    ∃ V : SpacesEtale B S hS X, Nonempty (G ≅ (SpacesEtale.topology B S hS X).yoneda.obj V) := by
  classical
  let J := SpacesEtale.topology B S hS X
  let C := comparisonFunctor B S hS X
  let εf : (spacesEtaleInverseImage B S hS f).obj G ≅
      (SpacesEtale.topology B S hS Y).yoneda.obj A.fst :=
    (CategoricalPullback.π₁ _ _).mapIso φ
  let εi : (spacesEtaleInverseImage B S hS i).obj G ≅
      (SpacesEtale.topology B S hS Z).yoneda.obj A.snd :=
    (CategoricalPullback.π₂ _ _).mapIso φ
  obtain ⟨X₀, hX₀⟩ := exists_surjective_smallEtale_chart B S hS X.1 X.2
  let A₁ := (SpacesEtale.toSpaces B S hS Y).obj A.fst
  let A₂ := (SpacesEtale.toSpaces B S hS Z).obj A.snd
  obtain ⟨C₁, hC₁⟩ := exists_surjective_smallEtale_chart B S hS A₁.1 A₁.2
  obtain ⟨C₂, hC₂⟩ := exists_surjective_smallEtale_chart B S hS A₂.1 A₂.2
  let P₁ := (BigFppfOver.toScheme B S hS).obj C₁.1.left
  let P₂ := (BigFppfOver.toScheme B S hS).obj C₂.1.left
  have hpt₁ := fun v : P₁ => exists_isCompactChartOver_restrictArrow B S hS f εf X₀ hX₀
    (pointsMap B S hS _ C₁.1.hom ((schemePointsHomeomorph B S hS C₁.1.left).symm v))
  have hpt₂ := fun v : P₂ => exists_isCompactChartOver_restrictArrow B S hS i εi X₀ hX₀
    (pointsMap B S hS _ C₂.1.hom ((schemePointsHomeomorph B S hS C₂.1.left).symm v))
  choose T₁ hT₁ e₁ q₁ hq₁ using hpt₁
  choose T₂ hT₂ e₂ q₂ hq₂ using hpt₂
  let T : P₁ ⊕ P₂ → SmallEtale B S hS X.1 := Sum.elim T₁ T₂
  have hT : ∀ k, IsCompactChartOver B S hS X₀ (T k)
    | .inl v => hT₁ v
    | .inr v => hT₂ v
  let e : ∀ k, J.yoneda.obj (C.obj (T k)) ⟶ G := fun k => match k with
    | .inl v => e₁ v
    | .inr v => e₂ v
  let μ : Cardinal.{u} := max ((BigFppfOver.toScheme B S hS).obj X₀.1.left).size
    (max (2 ^ P₁.size) (2 ^ P₂.size))
  have hμ : μ < B.cutoff := max_lt X₀.1.left.left.property
    (max_lt (B.cutoff_isStrongPrelimit C₁.1.left.left.property)
      (B.cutoff_isStrongPrelimit C₂.1.left.left.property))
  have hι : #(P₁ ⊕ P₂) ≤ μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    refine ((add_le_add (Scheme.mk_le_two_pow_size P₁) (Scheme.mk_le_two_pow_size P₂)).trans
      (Cardinal.add_le_max _ _)).trans (max_le (le_max_right _ _) ?_)
    exact (Scheme.aleph0_le_size _).trans (le_max_left _ _)
  obtain ⟨Vsm, c, hglue⟩ := exists_glued_isCompactChartOver B S hS X₀ T hT hμ hι (le_max_left _ _)
  obtain ⟨e', he'⟩ := hglue G e
  have hsf := surjective_pointsMap_restrictArrow B S hS f εf C₁ hC₁ e₁ q₁ hq₁
    (fun v => c (.inl v)) e' fun v => he' (.inl v)
  have hsi := surjective_pointsMap_restrictArrow B S hS i εi C₂ hC₂ e₂ q₂ hq₂
    (fun v => c (.inr v)) e' fun v => he' (.inr v)
  let R := spacesModificationRestriction B S hS f i j g w
  have : Epi (R.map e').fst := epi_map_of_surjective_restrictArrow B S hS f εf e' hsf
  have : Epi (R.map e').snd := epi_map_of_surjective_restrictArrow B S hS i εi e' hsi
  have : R.ReflectsEpimorphisms := Functor.reflectsEpimorphisms_of_faithful R
  have : Epi e' := R.epi_of_epi_map (CategoricalPullback.epi_of_epi_fst_of_epi_snd _)
  obtain ⟨W, ⟨α⟩⟩ := exists_iso_yoneda_of_epi B S hS G Vsm
    ((sheafificationIso (J.yoneda.obj (C.obj Vsm))).inv ≫ e')
  exact ⟨W, ⟨α ≪≫ (sheafificationIso (J.yoneda.obj W)).symm⟩⟩

/-- For a commutative square `j ≫ f = g ≫ i` of algebraic spaces whose sheaf-level restriction
functor `F ↦ (f⁻¹ F, i⁻¹ F)` on the spaces-étale topoi is an equivalence, the site-level
restriction functor `V ↦ (V ×_X Y, V ×_X Z)` from the spaces-étale site of `X` to the categorical
pullback of the spaces-étale sites of `Y` and `Z` over that of `E` is an equivalence. -/
theorem isEquivalence_spacesEtaleModificationRestriction_of_isEquivalence
    [(spacesModificationRestriction B S hS f i j g w).IsEquivalence] :
    (spacesEtaleModificationRestriction B S hS f i j g w).IsEquivalence :=
  isEquivalence_spacesEtaleModificationRestriction_of_representable B S hS f i j g w
    fun G A ⟨φ⟩ => exists_iso_yoneda_of_spacesModificationRestriction B S hS f i j g w G A φ

end Representable

end AlgebraicGeometry.Space
