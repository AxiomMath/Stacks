module

public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.IntersectionLocalStructure
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.Reduced
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusIrreducible
public import StacksFrontier.AlgebraicGeometry.Curves.NodalGorensteinReduced
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.AutomaticProperties
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.GoingDownNormal
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ConnectedLocal
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced

/-!
# Rational bridges after extension of the ground field

Let `X` be a proper one-dimensional scheme over a field `k` with `H⁰(X, 𝒪_X) = k` and
at-worst-nodal singularities, and let `C ⊆ X` be a rational bridge which is moreover
geometrically integral over its field of global functions. For every field extension `K/k` the
inverse image of `C` in the base change `X_K` is a finite disjoint union of rational bridges of
`X_K`.

[Stacks, Tag 0E65] asserts this without the geometric integrality, and in that form the tag is
false: see the implementation notes below. The unconditional statement at the tag's own
hypotheses, with the disjointness dropped from the conclusion, is
`AlgebraicGeometry.exists_finset_isRationalBridge_baseChange` of
`ContractingRationalBridges/BaseChangeUnion.lean`. **Both registrations of the tag in this file
are therefore CONDITIONAL**, carrying the binder `hgeom` which the tag does not have; each
attribute string says so, and neither should be read as a proof of the tag.

The field `k'` of global functions on `C` is a finite separable extension of `k`, so `K ⊗_k k'`
is a finite product of finite separable extensions `K'_i/K`; the corresponding decomposition of
`C_K` has components `C_i = C_{K'_i}`. Each `C_i` is an irreducible component of `X_K` of
dimension one, its genus over `K'_i` equals the genus of `C` over `k'` by flat base change, and
its scheme-theoretic intersection with the closure of its complement is the base change of
`C ∩ X'`, hence again of degree two.

## Main results

* `AlgebraicGeometry.exists_iso_sigma_isRationalBridge_baseChange` gives the finite coproduct
  decomposition, compatibly with the closed immersions into the base-changed curve.
* `AlgebraicGeometry.exists_iso_sigma_isRationalBridge_baseChange_of_perfectField` specialises it
  to a perfect ground field.
* `AlgebraicGeometry.finrank_globalSections_baseChange`: for a quasi-compact quasi-separated
  scheme over `k`, extension of the ground field does not change the dimension of the ring of
  global sections. Taken at the intersection of a closed subscheme of a curve with the closure of
  its complement, this is invariance of the degree of that intersection, the quantity clause (4)
  of `AlgebraicGeometry.IsRationalBridge` constrains to be two.
* `AlgebraicGeometry.finrank_globalSections_eq_of_isIso_base` reads that absolute degree as the
  relative degree over the global sections of the ambient scheme, which is the form clause (4)
  of `AlgebraicGeometry.IsRationalBridge` is stated in.

## Implementation notes

The inverse image of the closed subscheme is taken as `Scheme.IdealSheafData.comap` along the
projection. The isomorphism with the finite coproduct commutes with its closed immersion into
the base-changed curve, so the components are disjoint as closed subschemes and not merely
abstractly isomorphic to a disjoint union.

Separability of the field of global functions is expressed for the algebra structure induced by
the structure morphism of the bridge, and geometric integrality is expressed over that field via
`Scheme.toSpecΓ` rather than over the ground field.

Both facts that the source reads off its standing hypotheses are derived here from nodality:

* geometric reducedness of `X` over `k` is the geometric half of Tag 0E37,
  `Stacks.Curves.geometricallyReduced_of_hasAtWorstNodalSingularities`, applied to `X` itself
  (`X` is equidimensional because its global functions are `k` and it has dimension one);
* separability over `k` of the field `Γ(C, 𝒪_C)` of global functions of the bridge goes through
  the same tag applied to the bridge: a rational bridge is a reduced closed subcurve of `X`,
  equidimensional of dimension one, so it is itself nodal by Tag 0E38 (1)
  (`Stacks.Curves.hasAtWorstNodalSingularities_subscheme`) and therefore geometrically reduced
  over `k`; and the field of global functions of a connected geometrically reduced proper scheme
  over `k` is separable over `k` by Tag 0BUG
  (`ProperSectionsGeom.isSeparable_globalSections_of_connectedSpace_of_geometricallyReduced`).

Geometric integrality of the bridge over its field of global functions remains a hypothesis: the
source uses it when asserting that the base change of `C` decomposes into the integral pieces
`C_{K'_i}`, and does not prove it. It is not a consequence of the remaining assumptions, because
the decomposition itself fails without it. Over `k = ℝ` take the plane curves

`X = V(T₂(T₀² + T₁²)) ⊂ P²_ℝ` and its irreducible component `C = V(T₀² + T₁²)`.

Both have `ℝ` as their global functions and `C` has genus zero (Tag 0BYD); `C` is integral
because `T₀² + T₁²` is irreducible over `ℝ` (Tag 0BYC); the base change of `X` to `ℂ` is the
triangle of lines `T₂`, `T₀ + iT₁`, `T₀ - iT₁`, whose three pairwise intersections are ordinary
double points, so the singularities of `X` are at-worst-nodal (Tag 0C47 tests nodality after base
change to an algebraic closure, so a node whose two branches are conjugate is a node); and the
closure of the complement of `C` is the line `V(T₂)`, meeting `C` in `Spec ℝ[t]/(t² + 1)`, of
degree two over `ℝ`. Thus `C` is a rational bridge, while its base change
`C_ℂ = V(T₀ + iT₁) ∪ V(T₀ - iT₁)` is connected and reducible, hence not isomorphic to a coproduct
of integral closed subschemes.

The degree of the intersection is what separates a bridge from a tail here. A rational tail meets
the closure of its complement in one point rational over its global functions, so it carries an
invertible module of degree one and is a projective line over that field (Tag 0C6U) and in
particular geometrically integral; that is the step the tail form of this lemma takes
(Tag 0E3I). A bridge meets it in degree two, and a genus-zero curve whose global functions are
its base field is then only an irreducible plane conic (Tag 0C6N), as in the curve `C` above.

It is also not a consequence of the clauses of Tag 0E3M, so no proof can discharge it from `hC`.
The route suggested by Tag 0E3K — a genus-zero bridge, viewed over its field of global
functions, is a plane conic — reaches an *irreducible* conic and stops there, and an irreducible
conic may be the norm form of a separable quadratic extension, which splits into two conjugate
lines over that extension. `Stacks.Curves.DegenerateConic.not_geometricallyIntegral_conic`
exhibits this: over a field `k` in which `-1` is not a square, the plane curve `T₀² + T₁² = 0` is
integral by Tag 0BYC, has genus zero and global functions exactly `k` by Tag 0BYD — so it is a
genus-zero curve over its own field of global functions — and is not `GeometricallyIntegral` over
`k`. `Stacks.Curves.DegenerateConic.isCurve_genus_zero_and_not_isCurve_baseChange` collects the
assertions. So `hgeom` records an independent property of the bridge.

Dropping the disjointness from the conclusion repairs the statement at the source's own
hypotheses, and that weaker form is true: in the curve `C` above the two lines of `C_ℂ` are each a
rational bridge of `X_ℂ` and together they cover `C_ℂ`, failing only to be disjoint. That is the
form in which the tag holds unconditionally, and it is proved in
`ContractingRationalBridges/BaseChangeUnion.lean` as
`AlgebraicGeometry.exists_finset_isRationalBridge_baseChange`, with the pieces taken to be the
reduced structures on the irreducible components of `C_K`. The two inputs that proof needs beyond
what is here are the genus inequality `AlgebraicGeometry.genus_add_le_genus_union`
(`GenusCurve/GenusUnion.lean`), which gives clause (3) for every closed subcurve of a genus-zero
piece, and the conjugacy of the components of `C_Ω` over a separably closed extension
(`Stacks.Curves.finrank_sup_complementaryCurveIdeal_eq_of_image_eq`), which is what forces the
complementary degree of each component to be exactly two rather than merely two on average: the
bookkeeping identity alone is also satisfied by a chain of three components of degrees
`(1, 4, 1)`.

## References

* [Stacks Project, Tag 0E65](https://stacks.math.columbia.edu/tag/0E65)
* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
* [Stacks Project, Tag 0E3I](https://stacks.math.columbia.edu/tag/0E3I)
* [Stacks Project, Tag 0E38](https://stacks.math.columbia.edu/tag/0E38)
* [Stacks Project, Tag 0E37](https://stacks.math.columbia.edu/tag/0E37)
* [Stacks Project, Tag 0C6U](https://stacks.math.columbia.edu/tag/0C6U)
* [Stacks Project, Tag 0C6N](https://stacks.math.columbia.edu/tag/0C6N)
* [Stacks Project, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J)
* [Stacks Project, Tag 0C47](https://stacks.math.columbia.edu/tag/0C47)
* [Stacks Project, Tag 0BYD](https://stacks.math.columbia.edu/tag/0BYD)
* [Stacks Project, Tag 0BYC](https://stacks.math.columbia.edu/tag/0BYC)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
* [Stacks Project, Tag 0BY5](https://stacks.math.columbia.edu/tag/0BY5)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 081I](https://stacks.math.columbia.edu/tag/081I)
* [Stacks Project, Tag 04KP](https://stacks.math.columbia.edu/tag/04KP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

private theorem nonempty_sigmaSpec_iso_pullback
    (k K A : Type u) [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A]
    {ι : Type u} [Finite ι] (L : ι → Type u)
    [∀ i, CommRing (L i)] [∀ i, Algebra K (L i)]
    (e : K ⊗[k] A ≃ₐ[K] (∀ i, L i)) :
    Nonempty ((∐ fun i ↦ Spec (.of (L i))) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  classical
  let := Fintype.ofFinite ι
  exact ⟨asIso (sigmaSpec (fun i ↦ .of (L i))) ≪≫
    (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.symm.op).symm ≪≫
    (pullbackSpecIso k K A).symm ≪≫ pullbackSymmetry _ _⟩

private theorem exists_idealSheafData_of_coproduct_iso
    {ι : Type u} {Y : Scheme.{u}} (C : Y.IdealSheafData) (Z : ι → Scheme.{u})
    (e : (∐ Z) ≅ C.subscheme) :
    ∃ (D : ι → Y.IdealSheafData) (a : ∀ i, Z i ≅ (D i).subscheme)
      (b : (∐ fun i ↦ (D i).subscheme) ≅ C.subscheme),
      (∀ i, (a i).hom ≫ (D i).subschemeι = Sigma.ι Z i ≫ e.hom ≫ C.subschemeι) ∧
      b.hom ≫ C.subschemeι = Sigma.desc (fun i ↦ (D i).subschemeι) := by
  have (i : ι) : IsClosedImmersion (Sigma.ι Z i) := isClosedImmersion_sigma_ι Z i
  let d (i : ι) : Z i ⟶ Y := Sigma.ι Z i ≫ e.hom ≫ C.subschemeι
  let D (i : ι) := (d i).ker
  let a (i : ι) : Z i ≅ (D i).subscheme := asIso (d i).toImage
  let b := (Sigma.mapIso a).symm ≪≫ e
  have ha (i : ι) : (a i).hom ≫ (D i).subschemeι = d i :=
    (d i).toImage_imageι
  refine ⟨D, a, b, ha, ?_⟩
  apply Sigma.hom_ext
  intro i
  dsimp [b]
  simp only [Category.assoc, Sigma.ι_mapIso_inv_assoc, Sigma.ι_desc]
  exact (Iso.inv_comp_eq (a i)).mpr (ha i).symm

private theorem isIso_sigmaDesc_pullback_fst
    {ι : Type u} [Finite ι] {Z Y : Scheme.{u}} (S : ι → Scheme.{u})
    (π : ∀ i, S i ⟶ Z) (f : Y ⟶ Z) [hπ : IsIso (Sigma.desc π)] :
    IsIso (Sigma.desc (fun i ↦ pullback.fst f (π i))) := by
  let c := Cofan.mk Y (fun i ↦ pullback.fst f (π i))
  apply c.nonempty_isColimit_iff_isIso_sigmaDesc.mp
  have hau : IsUniversalColimit (Cofan.mk Z π) :=
    FinitaryPreExtensive.isUniversal_finiteCoproducts
      ((Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mpr hπ).some
  refine hau.nonempty_isColimit_of_pullbackCone_left _ (𝟙 _) _ _ (fun i ↦ ?_)
    (PullbackCone.mk (𝟙 _) f (by simp)) (IsPullback.id_horiz f).isLimit _ (Iso.refl _)
    (by simp)
    (by intro i; change pullback.fst f (π i) ≫ 𝟙 Y ≫ 𝟙 Y = pullback.fst f (π i); simp)
    (by intro i; change pullback.fst f (π i) ≫ 𝟙 Y ≫ f =
          pullback.snd f (π i) ≫ π i
        simp [pullback.condition])
  exact pullback.isLimit _ _

private theorem component_dim_one
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (hEq : TopologicalSpace.Equidimensional X)
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) :
    topologicalKrullDim Z = topologicalKrullDim X := by
  let d := topologicalKrullDim Z
  have hl (x : X) : topologicalKrullDimAt X x ≤ d := by
    rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k X f x]
    exact iSup₂_le fun W hW ↦ (hEq W hW.1 Z hZ).le
  have he : d ≤ topologicalKrullDim X := by
    obtain ⟨x, hx⟩ := hZ.1.nonempty
    rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
    apply le_iSup_of_le x
    rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim,
      topologicalKrullDimAt_eq_iSup_irreducibleComponents k X f x]
    exact le_iSup₂_of_le Z
      (show Z ∈ {W ∈ irreducibleComponents X | x ∈ W} from ⟨hZ, hx⟩) le_rfl
  have hle : topologicalKrullDim X ≤ d := by
    rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
    refine iSup_le fun x ↦ ?_
    rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim]
    exact hl x
  exact le_antisymm he hle

private theorem support_mem_irreducibleComponents_of_dimension_one
    {Y : Scheme.{u}} (D : Y.IdealSheafData) [IsIntegral D.subscheme]
    (hY : topologicalKrullDim Y ≤ 1)
    (hD : topologicalKrullDim D.subscheme = 1) :
    (D.support : Set Y) ∈ irreducibleComponents Y := by
  let F := TopologicalSpace.IrreducibleCloseds.map D.subschemeι D.subschemeι.continuous
  have hF : StrictMono F :=
    TopologicalSpace.IrreducibleCloseds.map_strictMono_of_isInducing
      D.subschemeι.isClosedEmbedding.isEmbedding.isInducing
  have hirr : IsIrreducible (D.support : Set Y) := by
    rw [← D.range_subschemeι]
    simpa only [Set.image_univ] using
      (show IsIrreducible (Set.univ : Set D.subscheme) from
        IrreducibleSpace.isIrreducible_univ _).image
        D.subschemeι D.subschemeι.continuous.continuousOn
  let T : TopologicalSpace.IrreducibleCloseds Y := ⟨D.support, hirr, D.support.isClosed⟩
  have hle (W : TopologicalSpace.IrreducibleCloseds D.subscheme) : F W ≤ T := by
    show closure (D.subschemeι '' (W : Set D.subscheme)) ⊆ D.support
    exact D.support.isClosed.closure_subset_iff.mpr
      ((Set.image_subset_range _ _).trans D.range_subschemeι.le)
  obtain ⟨A, B, hAB⟩ := Order.krullDim_pos_iff.mp
    (show 0 < topologicalKrullDim D.subscheme by rw [hD]; exact zero_lt_one)
  have hAT : F A < T := (hF hAB).trans_le (hle B)
  have hmax : IsMax T :=
    (Order.krullDim_le_one_iff.mp hY T).resolve_left fun hmin ↦ hAT.not_ge (hmin hAT.le)
  refine ⟨hirr, fun Z hZ hDZ ↦ ?_⟩
  let W : TopologicalSpace.IrreducibleCloseds Y :=
    ⟨closure Z, hZ.closure, isClosed_closure⟩
  exact subset_closure.trans (hmax (show T ≤ W from hDZ.trans subset_closure))

/-- **The scheme-theoretic closure of the complement of a closed subscheme commutes with flat
pullback.** The complementary curve ideal is the kernel of the open immersion of the complement
of the support, and flatness is what makes the inverse image of that open immersion again the
open immersion of the complement of the inverse image of the support. -/
public theorem complementaryCurveIdeal_comap
    {X Y : Scheme.{u}} (C : X.IdealSheafData) (f : Y ⟶ X)
    [Flat f] [QuasiCompact (Scheme.Opens.ι C.support.compl)] :
    complementaryCurveIdeal (C.comap f) =
      (complementaryCurveIdeal C).comap f := by
  have hU : (C.comap f).support.compl = f ⁻¹ᵁ C.support.compl := by
    ext x
    simp [Scheme.IdealSheafData.support_comap]
  show ((Scheme.Opens.ι (C.comap f).support.compl)).ker =
    ((Scheme.Opens.ι C.support.compl)).ker.comap f
  rw [hU]
  let e := (pullbackRestrictIsoRestrict f C.support.compl).symm ≪≫
    pullbackSymmetry f (Scheme.Opens.ι C.support.compl)
  have he : e.hom ≫ pullback.snd (Scheme.Opens.ι C.support.compl) f =
      (f ⁻¹ᵁ C.support.compl).ι := by simp [e]
  rw [← he, Scheme.Hom.ker_comp_of_isIso]
  exact ker_pullback_snd_eq_comap f (Scheme.Opens.ι C.support.compl)

/-- **The intersection of a closed subscheme with the closure of its complement commutes with
flat pullback.** -/
public theorem intersectionWithComplementaryCurveIdeal_comap
    {X Y : Scheme.{u}} (C : X.IdealSheafData) (f : Y ⟶ X)
    [Flat f] [QuasiCompact (Scheme.Opens.ι C.support.compl)] :
    intersectionWithComplementaryCurveIdeal (C.comap f) =
      (intersectionWithComplementaryCurveIdeal C).comap f := by
  show C.comap f ⊔ _ = (C ⊔ _).comap f
  rw [Scheme.IdealSheafData.comap_sup, complementaryCurveIdeal_comap]

private theorem complementaryCurveIdeal_eq_vanishingIdeal
    {Y : Scheme.{u}} [IsReduced Y] (C : Y.IdealSheafData)
    [QuasiCompact (Scheme.Opens.ι C.support.compl)] :
    complementaryCurveIdeal C =
      Scheme.IdealSheafData.vanishingIdeal
      ⟨closure ((C.support : Set Y)ᶜ), isClosed_closure⟩ := by
  rw [complementaryCurveIdeal,
    Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
  congr 1
  ext1
  rw [Scheme.Opens.range_ι]
  rfl

private theorem sup_inf_eq_of_sup_eq_top
    {Y : Scheme.{u}} (I J E : Y.IdealSheafData) (h : I ⊔ E = ⊤) :
    I ⊔ (J ⊓ E) = I ⊔ J := by
  apply le_antisymm (sup_le_sup_left inf_le_left _)
  intro U
  have hU : I.ideal U ⊔ E.ideal U = ⊤ := congrArg (fun A => A.ideal U) h
  show I.ideal U ⊔ J.ideal U ≤ I.ideal U ⊔ (J.ideal U ⊓ E.ideal U)
  rw [← Ideal.sup_mul_eq_of_coprime_right hU]
  exact sup_le_sup_left Ideal.mul_le_inf _

/-- **A piece of a closed subscheme that is disjoint from the rest of it meets the closure of the
complement of the whole in the same scheme as the closure of its own complement.** For `D` a
closed subscheme of `C` whose support is a union `supp D ∪ E` with `supp D` and `E` disjoint, the
intersection of `D` with the closure of the complement of `D` is its intersection with the
closure of the complement of `C`: the part of `C` outside `D` contributes nothing, being disjoint
from `D`. -/
public theorem intersectionWithComplementaryCurveIdeal_of_disjoint_union
    {Y : Scheme.{u}} [IsReduced Y] (C D : Y.IdealSheafData)
    [QuasiCompact (Scheme.Opens.ι C.support.compl)]
    [QuasiCompact (Scheme.Opens.ι D.support.compl)]
    (E : TopologicalSpace.Closeds Y)
    (hC : (C.support : Set Y) = (D.support : Set Y) ∪ E)
    (hDE : Disjoint (D.support : Set Y) (E : Set Y)) :
    intersectionWithComplementaryCurveIdeal D =
      D ⊔ complementaryCurveIdeal C := by
  have hsets : (D.support : Set Y)ᶜ = (C.support : Set Y)ᶜ ∪ E := by
    rw [hC]
    have hdisj := Set.disjoint_left.mp hDE
    ext x
    simp only [Set.mem_compl_iff, Set.mem_union]
    tauto
  have hclosure :
      (⟨closure ((D.support : Set Y)ᶜ), isClosed_closure⟩ : TopologicalSpace.Closeds Y) =
      ⟨closure ((C.support : Set Y)ᶜ), isClosed_closure⟩ ⊔ E := by
    ext1
    simp only [hsets, closure_union, E.isClosed.closure_eq,
      TopologicalSpace.Closeds.coe_sup, TopologicalSpace.Closeds.coe_mk]
  have hcoprime : D ⊔ Scheme.IdealSheafData.vanishingIdeal E = ⊤ := by
    apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
    rw [Scheme.IdealSheafData.support_sup]
    apply SetLike.coe_injective
    simpa only [TopologicalSpace.Closeds.coe_inf,
      Scheme.IdealSheafData.coe_support_vanishingIdeal,
      TopologicalSpace.Closeds.coe_bot] using Set.disjoint_iff_inter_eq_empty.mp hDE
  show D ⊔ complementaryCurveIdeal D = _
  rw [complementaryCurveIdeal_eq_vanishingIdeal D, hclosure,
    Scheme.IdealSheafData.vanishingIdeal_sup,
    sup_inf_eq_of_sup_eq_top _ _ _ hcoprime,
    complementaryCurveIdeal_eq_vanishingIdeal C]

private theorem intersectionWithComplementaryCurveIdeal_of_openImmersion
    {Y : Scheme.{u}} [IsReduced Y] (C D : Y.IdealSheafData)
    [QuasiCompact (Scheme.Opens.ι C.support.compl)]
    [QuasiCompact (Scheme.Opens.ι D.support.compl)]
    (j : D.subscheme ⟶ C.subscheme) [IsOpenImmersion j]
    (hj : j ≫ C.subschemeι = D.subschemeι) :
    intersectionWithComplementaryCurveIdeal D =
      D ⊔ complementaryCurveIdeal C := by
  let E : TopologicalSpace.Closeds Y :=
    ⟨C.subschemeι '' (Set.range j)ᶜ,
      C.subschemeι.isClosedEmbedding.isClosedMap _
        (j.isOpenEmbedding.isOpen_range.isClosed_compl)⟩
  have hD : (D.support : Set Y) = C.subschemeι '' Set.range j := by
    rw [← D.range_subschemeι, ← hj]
    show Set.range (C.subschemeι ∘ j) = _
    exact Set.range_comp _ _
  have hC : (C.support : Set Y) = (D.support : Set Y) ∪ E := by
    rw [hD, ← C.range_subschemeι]
    show Set.range C.subschemeι =
      C.subschemeι '' Set.range j ∪ C.subschemeι '' (Set.range j)ᶜ
    rw [← Set.image_union, Set.union_compl_self, Set.image_univ]
  have hDE : Disjoint (D.support : Set Y) (E : Set Y) := by
    rw [hD, Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    exact hy (C.subschemeι.isClosedEmbedding.injective hyx ▸ hx)
  exact intersectionWithComplementaryCurveIdeal_of_disjoint_union C D E hC hDE

/-- The global sections of a base change along a field extension: for a quasi-compact
quasi-separated scheme `X` over `k` and a Cartesian square over `Spec k ← Spec K`, the global
sections of the base change are `Γ(X, 𝒪_X) ⊗_k K` as a `K`-algebra.

This is `AlgebraicGeometry.isPushout_appTop_of_flat`, flat base change for the structure sheaf in
degree zero over an affine base, read through the identification of the pushout of
`k → Γ(X, 𝒪_X)` along `k → K` with the tensor product. -/
private noncomputable def globalSectionsTensorProductEquiv
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (p : Y ⟶ X) (q : Y ⟶ Spec (.of K))
    (h : IsPullback p q f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    letI : Algebra k Γ(X, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    letI : Algebra K Γ(Y, ⊤) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop).hom.toAlgebra
    letI : Algebra K (Γ(X, ⊤) ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
    Γ(X, ⊤) ⊗[k] K ≃ₐ[K] Γ(Y, ⊤) := by
  classical
  letI : Algebra k Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  letI : Algebra K Γ(Y, ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop).hom.toAlgebra
  letI : Algebra K (Γ(X, ⊤) ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) := inferInstance
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have hs := isPushout_appTop_of_flat h
  let f₀ : CommRingCat.of k ⟶ Γ(X, ⊤) :=
    (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop
  let g₀ := CommRingCat.ofHom (algebraMap k K)
  let β : CommRingCat.of K ⟶ Γ(Y, ⊤) :=
    (Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop
  have hs₀ : IsPushout f₀ g₀ p.appTop β := by
    refine hs.of_iso (Scheme.ΓSpecIso (.of k)) (Iso.refl _)
      (Scheme.ΓSpecIso (.of K)) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [f₀]
    · exact Scheme.ΓSpecIso_naturality g₀
    · simp
    · simp [β]
  let c := CommRingCat.pushoutCocone k Γ(X, ⊤) K
  have ht : IsPushout f₀ g₀ c.inl c.inr :=
    IsPushout.of_isColimit (CommRingCat.pushoutCoconeIsColimit k Γ(X, ⊤) K)
  let e := IsPushout.isoIsPushout _ _ ht hs₀
  refine AlgEquiv.ofRingEquiv (f := e.commRingCatIsoToRingEquiv) fun x ↦ ?_
  have hβ : c.inr ≫ e.hom = β := IsPushout.inr_isoIsPushout_hom _ _ ht hs₀
  rw [show c.inr = CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : K →ₐ[k] Γ(X, ⊤) ⊗[k] K).toRingHom from
    CommRingCat.pushoutCocone_inr k Γ(X, ⊤) K] at hβ
  change e.hom.hom (1 ⊗ₜ[k] x) = β.hom x
  exact congrArg (fun t : CommRingCat.of K ⟶ Γ(Y, ⊤) => t.hom x) hβ

/-- **Extension of the ground field does not change the dimension of the global sections.** Let
`X` be a quasi-compact quasi-separated scheme over a field `k` and let `K/k` be a field extension.
Then the base change `X_K` satisfies

`dim_K Γ(X_K, 𝒪_{X_K}) = dim_k Γ(X, 𝒪_X)`.

Flatness of `K/k` is what makes this work: it turns the square of global sections into a pushout
of rings, `Γ(X_K, 𝒪_{X_K}) = Γ(X, 𝒪_X) ⊗_k K`, and extension of scalars of a vector space along
a field extension preserves its dimension. Neither properness nor any finiteness or dimension
hypothesis enters; when `Γ(X, 𝒪_X)` is infinite-dimensional over `k` both sides are `0` by the
convention of `Module.finrank`.

Taken at a closed subscheme of a curve, this is invariance under extension of the ground field of
the degree of an intersection. To read it as invariance of the *relative* degree that clause (4)
of `AlgebraicGeometry.IsRationalBridge` constrains to be two, compose it on both sides with
`AlgebraicGeometry.finrank_globalSections_eq_of_isIso_base`. -/
public theorem finrank_globalSections_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (p : Y ⟶ X) (q : Y ⟶ Spec (.of K))
    (h : IsPullback p q f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    letI : Algebra k Γ(X, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    letI : Algebra K Γ(Y, ⊤) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop).hom.toAlgebra
    Module.finrank K Γ(Y, ⊤) = Module.finrank k Γ(X, ⊤) := by
  let : Algebra k Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  let : Algebra K Γ(Y, ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop).hom.toAlgebra
  let : Algebra K (Γ(X, ⊤) ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  let eSections := globalSectionsTensorProductEquiv k K f p q h
  have he : (algebraMap K Γ(Y, ⊤)).comp (RingEquiv.refl K).toRingHom =
      eSections.toRingEquiv.toRingHom.comp
        (algebraMap K (Γ(X, ⊤) ⊗[k] K)) := by
    ext x
    exact (eSections.commutes x).symm
  have hcomm : Module.finrank K (Γ(X, ⊤) ⊗[k] K) =
      Module.finrank K (K ⊗[k] Γ(X, ⊤)) := by
    apply Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl K)
      (Algebra.TensorProduct.comm k Γ(X, ⊤) K).toRingEquiv
    ext x
    simp [Algebra.TensorProduct.right_algebraMap_apply,
      Algebra.TensorProduct.comm_tmul]
  exact (Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl K)
      eSections.toRingEquiv he).symm.trans
    (hcomm.trans Module.finrank_baseChange)

/-- **The relative degree of a scheme over a scheme with no nonconstant global functions is its
degree over the base ring.** If `f : X ⟶ Spec R` makes the canonical map `R ⟶ Γ(X, 𝒪_X)` an
isomorphism, then for any morphism `i : Z ⟶ X` the dimension of `Γ(Z, 𝒪_Z)` over `Γ(X, 𝒪_X)`,
with the algebra structure given by `i`, is its dimension over `R`.

This is what turns the absolute statement
`AlgebraicGeometry.finrank_globalSections_baseChange` into a statement about the relative degree
`Module.finrank Γ(X, ⊤) Γ(Z, ⊤)` that clause (4) of `AlgebraicGeometry.IsRationalBridge` speaks
about. -/
public theorem finrank_globalSections_eq_of_isIso_base
    (R : Type u) [CommRing R] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of R))
    [IsIso ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop)] (i : Z ⟶ X) :
    letI : Algebra Γ(X, ⊤) Γ(Z, ⊤) := i.appTop.hom.toAlgebra
    letI : Algebra R Γ(Z, ⊤) :=
      ((Scheme.ΓSpecIso (.of R)).inv ≫ (i ≫ f).appTop).hom.toAlgebra
    Module.finrank Γ(X, ⊤) Γ(Z, ⊤) = Module.finrank R Γ(Z, ⊤) := by
  let : Algebra Γ(X, ⊤) Γ(Z, ⊤) := i.appTop.hom.toAlgebra
  let : Algebra R Γ(Z, ⊤) :=
    ((Scheme.ΓSpecIso (.of R)).inv ≫ (i ≫ f).appTop).hom.toAlgebra
  let β := (Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop
  let eBase : Γ(X, ⊤) ≃+* R := (asIso β).commRingCatIsoToRingEquiv.symm
  have hβ : (asIso β).inv ≫
      ((Scheme.ΓSpecIso (.of R)).inv ≫ (i ≫ f).appTop) = i.appTop := by
    rw [Scheme.Hom.comp_appTop]
    show (asIso β).inv ≫ β ≫ i.appTop = _
    simp
  apply Algebra.finrank_eq_of_equiv_equiv eBase (RingEquiv.refl Γ(Z, ⊤))
  ext x
  exact congrArg (fun t : Γ(X, ⊤) ⟶ Γ(Z, ⊤) => t.hom x) hβ

private theorem ker_inclusion_eq_comap
    {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I ≤ J) :
    (Scheme.IdealSheafData.inclusion h).ker = J.comap I.subschemeι := by
  let i := Scheme.IdealSheafData.inclusion h
  have hsq : IsPullback i (𝟙 J.subscheme) I.subschemeι J.subschemeι :=
    IsPullback.of_vert_isIso_mono ⟨by
      simpa only [Category.id_comp] using Scheme.IdealSheafData.inclusion_subschemeι h⟩
  show i.ker = _
  rw [← hsq.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
  rfl

private theorem intersectionWithComplementaryCurve_isPullback
    {X Y : Scheme.{u}} [IsReduced Y]
    (C : X.IdealSheafData) (D : Y.IdealSheafData)
    (p : Y ⟶ X) [Flat p]
    [QuasiCompact (Scheme.Opens.ι C.support.compl)]
    [QuasiCompact (Scheme.Opens.ι (C.comap p).support.compl)]
    [QuasiCompact (Scheme.Opens.ι D.support.compl)]
    (j : D.subscheme ⟶ (C.comap p).subscheme) [IsOpenImmersion j]
    (hj : j ≫ (C.comap p).subschemeι = D.subschemeι)
    (c : D.subscheme ⟶ C.subscheme)
    (hc : c ≫ C.subschemeι = D.subschemeι ≫ p) :
    let I := intersectionWithComplementaryCurveIdeal D
    let J := intersectionWithComplementaryCurveIdeal C
    ∃ r : I.subscheme ⟶ J.subscheme,
      IsPullback (Scheme.IdealSheafData.inclusion (le_sup_left : D ≤ I)) r c
        (Scheme.IdealSheafData.inclusion (le_sup_left : C ≤ J)) := by
  let I := intersectionWithComplementaryCurveIdeal D
  let J := intersectionWithComplementaryCurveIdeal C
  let iD := Scheme.IdealSheafData.inclusion (le_sup_left : D ≤ I)
  let iC := Scheme.IdealSheafData.inclusion (le_sup_left : C ≤ J)
  have hle : C.comap p ≤ D := by
    rw [← (C.comap p).ker_subschemeι, ← D.ker_subschemeι, ← hj]
    exact Scheme.Hom.le_ker_comp j (C.comap p).subschemeι
  have hJ : (C.comap p) ⊔
      complementaryCurveIdeal (C.comap p) = J.comap p :=
    intersectionWithComplementaryCurveIdeal_comap C p
  have hI : I = D ⊔ J.comap p := by
    show intersectionWithComplementaryCurveIdeal D = _
    rw [intersectionWithComplementaryCurveIdeal_of_openImmersion (C.comap p) D j hj, ← hJ,
      ← sup_assoc, sup_eq_left.mpr hle]
  have hmap : J ≤ I.map p :=
    Scheme.IdealSheafData.le_map_iff_comap_le.mpr (by rw [hI]; exact le_sup_right)
  let r := I.subschemeMap J p hmap
  refine ⟨r, isPullback_of_isClosedImmersion iD iC r c ?_ ?_⟩
  · apply (cancel_mono C.subschemeι).1
    calc
      (iD ≫ c) ≫ C.subschemeι = (iD ≫ D.subschemeι) ≫ p := by
        rw [Category.assoc, hc, Category.assoc]
      _ = I.subschemeι ≫ p := by rw [Scheme.IdealSheafData.inclusion_subschemeι]
      _ = r ≫ J.subschemeι := (Scheme.IdealSheafData.subschemeMap_subschemeι I J p hmap).symm
      _ = (r ≫ iC) ≫ C.subschemeι := by
        rw [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  · rw [ker_inclusion_eq_comap, ker_inclusion_eq_comap]
    have hzero : D.comap D.subschemeι = ⊥ := by
      show (pullback.fst D.subschemeι D.subschemeι).ker = ⊥
      exact Scheme.Hom.ker_eq_bot_of_isIso _
    show (J.comap C.subschemeι).comap c = I.comap D.subschemeι
    calc
      (J.comap C.subschemeι).comap c = J.comap (c ≫ C.subschemeι) :=
        (Scheme.IdealSheafData.comap_comp J c C.subschemeι).symm
      _ = J.comap (D.subschemeι ≫ p) := by rw [hc]
      _ = (J.comap p).comap D.subschemeι :=
        Scheme.IdealSheafData.comap_comp J D.subschemeι p
      _ = D.comap D.subschemeι ⊔ (J.comap p).comap D.subschemeι := by
        rw [hzero, bot_sup_eq]
      _ = (D ⊔ J.comap p).comap D.subschemeι :=
        (Scheme.IdealSheafData.comap_sup D (J.comap p) D.subschemeι).symm
      _ = I.comap D.subschemeι := congrArg (fun E => E.comap D.subschemeι) hI.symm

/-- **The disjoint decomposition of a geometrically integral rational bridge.** Let `X` be a
proper one-dimensional scheme over a field `k` with `H⁰(X, 𝒪_X) = k` and at-worst-nodal
singularities, and let `C ⊆ X` be a rational bridge that is geometrically integral over its field
of global functions. For every field extension `K/k` the inverse image of `C` in `X_K` is a finite
disjoint union of rational bridges of `X_K`, compatibly with their closed immersions into `X_K`.

Geometric integrality of the bridge is an extra assumption beyond those of [Stacks, Tag 0E65],
and the disjointness of the decomposition is false without it: the module docstring above exhibits
the plane curve `X = V(T₂(T₀² + T₁²)) ⊂ P²_ℝ` whose component `C = V(T₀² + T₁²)` is a rational
bridge with `C_ℂ` connected and reducible, and
`Stacks.Curves.DegenerateConic.not_exists_iso_sigma_isRationalBridge_degenerateConic` proves that
the conclusion below fails for it. So the tag itself is registered on
`AlgebraicGeometry.exists_finset_isRationalBridge_baseChange`, which reaches the
scheme-theoretic-union form of the conclusion from the tag's own hypotheses. -/
@[stacks 0E65 "CONDITIONALLY -- this is not an unconditional proof of 0E65: the binder `hgeom`,
geometric integrality of the bridge over its field of global functions, is not a hypothesis of the
tag. It cannot be discharged, because the tag's conclusion as stated -- a DISJOINT union -- is
false without it, refuted by
`Stacks.Curves.DegenerateConic.not_exists_iso_sigma_isRationalBridge_degenerateConic` for the
rational bridge `V(T₀² + T₁²)` of `V(T₂(T₀² + T₁²)) ⊂ P²_ℝ`. The tag at its own hypotheses, with
the disjointness dropped from the conclusion, is proved unconditionally as
`AlgebraicGeometry.exists_finset_isRationalBridge_baseChange` in
`ContractingRationalBridges/BaseChangeUnion.lean`"]
public theorem exists_iso_sigma_isRationalBridge_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData)
    (hC : IsRationalBridge k X C)
    (hgeom :
      letI : IsIntegral C.subscheme := hC.isIntegral
      letI : Field Γ(C.subscheme, ⊤) :=
        (isField_of_universallyClosed k
          (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
      GeometricallyIntegral C.subscheme.toSpecΓ) :
    let g : Spec (.of K) ⟶ Spec (.of k) :=
      Spec.map (CommRingCat.ofHom (algebraMap k K))
    let Y := (pullback (X ↘ Spec (.of k)) g : Scheme.{u})
    let p : Y ⟶ X := pullback.fst (X ↘ Spec (.of k)) g
    letI : Y.Over (Spec (.of K)) := ⟨pullback.snd (X ↘ Spec (.of k)) g⟩
    letI : IsProper (Y ↘ Spec (.of K)) :=
      inferInstanceAs (IsProper (pullback.snd (X ↘ Spec (.of k)) g))
    ∃ (ι : Type u) (_ : Finite ι) (D : ι → Y.IdealSheafData)
        (_ : ∀ i, IsRationalBridge K Y (D i))
        (e : (∐ fun i ↦ (D i).subscheme) ≅ (C.comap p).subscheme),
      e.hom ≫ (C.comap p).subschemeι =
        Sigma.desc (fun i ↦ (D i).subschemeι) := by
  classical
  let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := pullback (X ↘ Spec (.of k)) g
  let p : Y ⟶ X := pullback.fst (X ↘ Spec (.of k)) g
  let : Y.Over (Spec (.of K)) := ⟨pullback.snd (X ↘ Spec (.of k)) g⟩
  have hpb := IsPullback.of_hasPullback (X ↘ Spec (.of k)) g
  let A := Γ(C.subscheme, ⊤)
  have : IsIntegral C.subscheme := hC.isIntegral
  let : Field A := (isField_of_universallyClosed k
    (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
  let : Algebra k A :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      (C.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
  have : Module.Finite k A :=
    RingHom.Finite.comp
      (finite_appTop_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k))))
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.finite
  have hXeq : TopologicalSpace.Equidimensional X :=
    equidimensional_of_isIso_globalSections_of_dimension_one k (X ↘ Spec (.of k)) hdim
  have hCdim : topologicalKrullDim C.subscheme = 1 := by
    have : LocallyOfFiniteType (X ↘ Spec (.of k)) := inferInstance
    have hcompdim : topologicalKrullDim (C.support : Set X) = 1 :=
      (component_dim_one k X (X ↘ Spec (.of k)) hXeq
        hC.support_mem_irreducibleComponents).trans hdim
    let eI : C.subscheme ≃ₜ C.support :=
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso C.subschemeIso)).trans C.gluedHomeo
    exact (IsHomeomorph.topologicalKrullDim_eq _ eI.isHomeomorph).trans hcompdim
  -- Separability of the field of global functions of the bridge: the bridge is a reduced closed
  -- subcurve of `X`, hence nodal (Tag 0E38 (1)) and so geometrically reduced (Tag 0E37), and the
  -- field of global functions of a connected geometrically reduced proper scheme over `k` is
  -- separable over `k` (Tag 0BUG).
  have : Algebra.IsSeparable k A := by
    let : C.subscheme.Over (Spec (.of k)) := ⟨C.subschemeι ≫ (X ↘ Spec (.of k))⟩
    have : IsProper (C.subschemeι ≫ (X ↘ Spec (.of k))) := inferInstance
    have : LocallyOfFiniteType (C.subscheme ↘ Spec (.of k)) :=
      inferInstanceAs (LocallyOfFiniteType (C.subschemeι ≫ (X ↘ Spec (.of k))))
    have hCeq : TopologicalSpace.Equidimensional C.subscheme :=
      TopologicalSpace.Equidimensional.of_preirreducibleSpace C.subscheme
    have hCnodal : Stacks.Curves.HasAtWorstNodalSingularities k C.subscheme :=
      Stacks.Curves.hasAtWorstNodalSingularities_subscheme hXeq hdim hnodal C hCeq hCdim
    have : GeometricallyReduced (C.subschemeι ≫ (X ↘ Spec (.of k))) :=
      Stacks.Curves.geometricallyReduced_of_hasAtWorstNodalSingularities k C.subscheme
        hCeq hCdim hCnodal
    open Stacks.AlgebraicGeometry.ProperSectionsGeom in
    exact isSeparable_globalSections_of_connectedSpace_of_geometricallyReduced k
      (C.subschemeι ≫ (X ↘ Spec (.of k)))
  have : Algebra.FormallyEtale k A := Algebra.FormallyEtale.of_isSeparable k A
  have : Algebra.FiniteType k A := inferInstance
  have : Algebra.FinitePresentation k A :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale k A := ⟨inferInstance, inferInstance⟩
  obtain ⟨ι, hι, L, hL, hKL, eA, hLfin⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K (K ⊗[k] A)).mp inferInstance
  have : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  let (i : ι) : Field (L i) := hL i
  let (i : ι) : Algebra K (L i) := hKL i
  let f := C.subschemeι ≫ (X ↘ Spec (.of k))
  let α := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop
  let a : Spec (.of A) ⟶ Spec (.of k) := Spec.map α
  have hfa : C.subscheme.toSpecΓ ≫ a = f := by
    dsimp [a, α]
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp
  let T := pullback a g
  let q : T ⟶ Spec (.of A) := pullback.fst a g
  let r : T ⟶ Spec (.of K) := pullback.snd a g
  obtain ⟨eT⟩ := nonempty_sigmaSpec_iso_pullback k K A L eA
  let π (i : ι) : Spec (.of (L i)) ⟶ T :=
    Sigma.ι (fun i ↦ Spec (.of (L i))) i ≫ eT.hom
  have hπ : Sigma.desc π = eT.hom := Sigma.hom_ext _ _ fun i ↦ Sigma.ι_desc π i
  have : IsIso (Sigma.desc π) := hπ ▸ inferInstance
  let φ (i : ι) : CommRingCat.of A ⟶ CommRingCat.of (L i) :=
    Classical.choose (Spec.map_surjective (π i ≫ q))
  have hφ (i : ι) : Spec.map (φ i) = π i ≫ q :=
    Classical.choose_spec (Spec.map_surjective (π i ≫ q))
  let (i : ι) : Algebra A (L i) := (φ i).hom.toAlgebra
  let Z := pullback C.subscheme.toSpecΓ q
  let v : Z ⟶ C.subscheme := pullback.fst C.subscheme.toSpecΓ q
  let z : Z ⟶ T := pullback.snd C.subscheme.toSpecΓ q
  have htot : IsPullback (z ≫ r) v g f := by
    rw [← hfa]
    exact (IsPullback.of_hasPullback C.subscheme.toSpecΓ q).flip.paste_horiz
      (IsPullback.of_hasPullback a g).flip
  let hY := hpb.flip
  let j : Z ⟶ Y := hY.lift (z ≫ r) (v ≫ C.subschemeι)
    (by rw [htot.w, Category.assoc])
  have hj : IsPullback j v p C.subschemeι := htot.of_right' hY
  let eZ : Z ≅ (C.comap p).subscheme := hj.isoPullback ≪≫ (C.comapIso p).symm
  have heZ : eZ.hom ≫ (C.comap p).subschemeι = j := by simp [eZ]
  have : IsClosedImmersion j := by
    rw [← hj.isoPullback_hom_fst]
    infer_instance
  have : IsProper (Y ↘ Spec (.of K)) := by
    show IsProper (pullback.snd (X ↘ Spec (.of k)) g)
    infer_instance
  let W (i : ι) := pullback z (π i)
  let w (i : ι) : W i ⟶ Z := pullback.fst z (π i)
  let bL (i : ι) : W i ⟶ Spec (.of (L i)) := pullback.snd z (π i)
  have (i : ι) : IsOpenImmersion (π i) := by dsimp [π]; infer_instance
  have (i : ι) : IsOpenImmersion (w i) := by dsimp [w]; infer_instance
  have : IsIso (Sigma.desc w) := isIso_sigmaDesc_pullback_fst _ π z
  let e := asIso (Sigma.desc w) ≪≫ eZ
  obtain ⟨D, eD, b, heD, hb⟩ := exists_idealSheafData_of_coproduct_iso (C.comap p) W e
  have hd (i : ι) : (eD i).hom ≫ (D i).subschemeι = w i ≫ j := by
    rw [heD]
    simp [e, Category.assoc, heZ]
  have hYdim : topologicalKrullDim Y = 1 :=
    (topologicalKrullDim_baseChange k K p
      (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
      hpb).trans hdim
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of K))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of K))
  have : IsNoetherian Y := ⟨⟩
  have : GeometricallyIntegral C.subscheme.toSpecΓ := hgeom
  have hWi (i : ι) : IsPullback (w i ≫ v) (bL i) C.subscheme.toSpecΓ
      (Spec.map (φ i)) := by
    rw [hφ i]
    exact (IsPullback.of_hasPullback z (π i)).paste_horiz
      (IsPullback.of_hasPullback C.subscheme.toSpecΓ q)
  have hWi_integral (i : ι) : IsIntegral (W i) := by
    have : IsIntegral (pullback C.subscheme.toSpecΓ (Spec.map (φ i))) :=
      GeometricallyIntegral.isIntegral_of_subsingleton
        (pullback.snd C.subscheme.toSpecΓ (Spec.map (φ i)))
    exact IsIntegral.of_isIso (hWi i).isoPullback.inv
  have : IsProper C.subscheme.toSpecΓ := by
    have : IsProper (C.subscheme.toSpecΓ ≫ a) := hfa ▸ inferInstance
    exact IsProper.of_comp (f := C.subscheme.toSpecΓ) (g := a)
  have : IsIso ((Scheme.ΓSpecIso (.of A)).inv ≫ C.subscheme.toSpecΓ.appTop) := by
    dsimp [A]
    rw [Scheme.toSpecΓ_appTop]
    infer_instance
  have hWi_dim (i : ι) : topologicalKrullDim (W i) = 1 :=
    (topologicalKrullDim_baseChange A (L i) (w i ≫ v)
      (bL i) C.subscheme.toSpecΓ (hWi i)).trans hCdim
  have hD_integral (i : ι) : IsIntegral (D i).subscheme :=
    IsIntegral.of_isIso (eD i).hom
  have hD_dim (i : ι) : topologicalKrullDim (D i).subscheme = 1 := by
    rw [← IsHomeomorph.topologicalKrullDim_eq (eD i).hom
      (eD i).hom.homeomorph.isHomeomorph]
    exact hWi_dim i
  have hSupport (i : ι) : ((D i).support : Set Y) ∈ irreducibleComponents Y := by
    have : IsIntegral (D i).subscheme := hD_integral i
    exact support_mem_irreducibleComponents_of_dimension_one
      (D i) hYdim.le (hD_dim i)
  have hDmap (i : ι) : (D i).subschemeι = (eD i).inv ≫ w i ≫ j :=
    (Iso.eq_inv_comp (eD i)).mpr (hd i)
  have hDsubset (i : ι) :
      ((D i).support : Set Y) ⊆ ((C.comap p).support : Set Y) := by
    rw [← (D i).range_subschemeι, ← (C.comap p).range_subschemeι]
    rintro y ⟨z, rfl⟩
    refine ⟨eZ.hom (w i ((eD i).inv z)), ?_⟩
    rw [hDmap i]
    exact congrArg (fun f : Z ⟶ Y => f (w i ((eD i).inv z))) heZ
  have hsurj : Surjective p := by
    have hg : Surjective g := ⟨fun _ ↦ ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
    exact MorphismProperty.of_isPullback
      hpb.flip hg
  have hXcomp : ((C.support : Set X)ᶜ).Nonempty := by
    let U : X.Opens := C.support.compl
    let u : U.toScheme ⟶ X := U.ι
    by_contra hU
    have : IsEmpty U.toScheme := ⟨fun x => hU ⟨x.1, x.2⟩⟩
    have hdense : Dense (Set.range u.toImage.base) :=
      (IsDominant.denseRange : DenseRange u.toImage.base)
    have hrange : Set.range u.toImage.base = ∅ := by
      ext y
      simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false]
      rintro ⟨x, _⟩
      exact isEmptyElim x
    have hnonempty : Nonempty u.image := by
      simpa [u, U, complementaryCurve] using
        hC.complementaryCurve_nonempty
    obtain ⟨z⟩ := hnonempty
    have hz : z ∈ closure (Set.range u.toImage.base) := hdense z
    simp [hrange] at hz
  have hYcomp : (((C.comap p).support : Set Y)ᶜ).Nonempty := by
    obtain ⟨x, hx⟩ := hXcomp
    obtain ⟨y, hy⟩ := hsurj.surj x
    refine ⟨y, ?_⟩
    show y ∉ (C.comap p).support
    rw [Scheme.IdealSheafData.support_comap]
    show p y ∉ (C.support : Set X)
    rw [hy]
    exact hx
  have hDcomp (i : ι) : (((D i).support : Set Y)ᶜ).Nonempty := by
    obtain ⟨y, hy⟩ := hYcomp
    exact ⟨y, fun hmem => hy (hDsubset i hmem)⟩
  have hD_complementaryCurve_nonempty (i : ι) :
      Nonempty (complementaryCurve (D i)) := by
    obtain ⟨y, hy⟩ := hDcomp i
    exact ⟨(Scheme.Opens.ι (D i).support.compl).toImage ⟨y, hy⟩⟩
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  -- Geometric reducedness of `X` is Tag 0E37, from the nodality hypothesis.
  have : GeometricallyReduced (X ↘ Spec (.of k)) :=
    Stacks.Curves.geometricallyReduced_of_hasAtWorstNodalSingularities k X hXeq hdim hnodal
  have : IsReduced Y :=
    GeometricallyReduced.geometrically_isReduced g p
      (Y ↘ Spec (.of K)) hpb
  have : Flat p := MorphismProperty.of_isPullback hpb.flip (inferInstanceAs (Flat g))
  let cD (i : ι) : (D i).subscheme ⟶ C.subscheme :=
    (eD i).inv ≫ w i ≫ v
  have hcD (i : ι) : cD i ≫ C.subschemeι = (D i).subschemeι ≫ p := by
    calc
      cD i ≫ C.subschemeι = (eD i).inv ≫ w i ≫ (v ≫ C.subschemeι) := by
        simp [cD, Category.assoc]
      _ = (eD i).inv ≫ w i ≫ (j ≫ p) := by rw [← hj.w]
      _ = (D i).subschemeι ≫ p := by simp [Category.assoc, hDmap i]
  let fDbase (i : ι) : (D i).subscheme ⟶ Spec (.of (L i)) :=
    (eD i).inv ≫ bL i
  have hDbase (i : ι) : IsPullback (cD i) (fDbase i) C.subscheme.toSpecΓ
      (Spec.map (φ i)) :=
    (hWi i).of_iso (eD i) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [cD]) (by simp [fDbase])
      (by simp) (by simp)
  have hDbase_iso (i : ι) :
      IsIso ((Scheme.ΓSpecIso (.of (L i))).inv ≫ (fDbase i).appTop) :=
    isIso_globalSections_baseChange A (L i) (cD i)
      (fDbase i) C.subscheme.toSpecΓ (hDbase i)
  have hD_genus (i : ι) :
      letI : IsIntegral (D i).subscheme := hD_integral i
      letI : Field Γ((D i).subscheme, ⊤) :=
        (isField_of_universallyClosed K
          ((D i).subschemeι ≫ (Y ↘ Spec (.of K)))).toField
      genus (D i).subscheme.toSpecΓ = 0 := by
    let : IsIntegral (D i).subscheme := hD_integral i
    let : Field Γ((D i).subscheme, ⊤) :=
      (isField_of_universallyClosed K
        ((D i).subschemeι ≫ (Y ↘ Spec (.of K)))).toField
    have : IsProper (fDbase i) := by
      dsimp [fDbase]
      infer_instance
    have : IsIso ((Scheme.ΓSpecIso (.of (L i))).inv ≫
        (fDbase i).appTop) := hDbase_iso i
    calc
      genus (D i).subscheme.toSpecΓ =
          genus (fDbase i) :=
        genus_toSpecΓ_eq_genus (L i) (fDbase i)
      _ = genus C.subscheme.toSpecΓ :=
        genus_baseChange A (L i) (cD i) (fDbase i)
          C.subscheme.toSpecΓ (hDbase i)
      _ = 0 := hC.genus_eq_zero
  have hD_rank (i : ι) :
      let ID := intersectionWithComplementaryCurveIdeal (D i)
      let iD : ID.subscheme ⟶ (D i).subscheme :=
        Scheme.IdealSheafData.inclusion (le_sup_left : D i ≤ ID)
      letI : Algebra Γ((D i).subscheme, ⊤) Γ(ID.subscheme, ⊤) :=
        iD.appTop.hom.toAlgebra
      Module.finrank Γ((D i).subscheme, ⊤) Γ(ID.subscheme, ⊤) = 2 := by
    let ID := intersectionWithComplementaryCurveIdeal (D i)
    let J := intersectionWithComplementaryCurveIdeal C
    let iD := Scheme.IdealSheafData.inclusion (le_sup_left : D i ≤ ID)
    let iC := Scheme.IdealSheafData.inclusion (le_sup_left : C ≤ J)
    let : Algebra Γ((D i).subscheme, ⊤) Γ(ID.subscheme, ⊤) :=
      iD.appTop.hom.toAlgebra
    let : Algebra (L i) Γ(ID.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of (L i))).inv ≫ (iD ≫ fDbase i).appTop).hom.toAlgebra
    let fI := iC ≫ C.subscheme.toSpecΓ
    let : Algebra A Γ(J.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of A)).inv ≫ fI.appTop).hom.toAlgebra
    have : IsProper fI := by dsimp [fI]; infer_instance
    have : IsIso ((Scheme.ΓSpecIso (.of (L i))).inv ≫ (fDbase i).appTop) :=
      hDbase_iso i
    let jd := (eD i).inv ≫ w i ≫ eZ.hom
    have hjd : jd ≫ (C.comap p).subschemeι = (D i).subschemeι := by
      simp [jd, Category.assoc, heZ, ← hd i]
    obtain ⟨r, hr⟩ := intersectionWithComplementaryCurve_isPullback
      C (D i) p jd hjd (cD i) (hcD i)
    have hsq : IsPullback r (iD ≫ fDbase i) fI (Spec.map (φ i)) :=
      hr.flip.paste_vert (hDbase i)
    have hfI : (Scheme.ΓSpecIso (.of A)).inv ≫ fI.appTop = iC.appTop := by
      show (Scheme.ΓSpecIso (.of A)).inv ≫
        (iC ≫ C.subscheme.toSpecΓ).appTop = iC.appTop
      rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
      show (Scheme.ΓSpecIso Γ(C.subscheme, ⊤)).inv ≫
        (Scheme.ΓSpecIso Γ(C.subscheme, ⊤)).hom ≫ iC.appTop = iC.appTop
      simp
    calc
      Module.finrank Γ((D i).subscheme, ⊤) Γ(ID.subscheme, ⊤) =
          Module.finrank (L i) Γ(ID.subscheme, ⊤) :=
        finrank_globalSections_eq_of_isIso_base (L i) (fDbase i) iD
      _ = Module.finrank A Γ(J.subscheme, ⊤) :=
        finrank_globalSections_baseChange A (L i) fI r (iD ≫ fDbase i) hsq
      _ = 2 := by
        show @Module.finrank A Γ(J.subscheme, ⊤) _ _
          (((Scheme.ΓSpecIso (.of A)).inv ≫ fI.appTop).hom.toAlgebra.toModule) = 2
        rw [hfI]
        exact hC.intersection_finrank_eq_two
  exact ⟨ι, hι, D, fun i ↦ ⟨hD_integral i, hSupport i, hD_complementaryCurve_nonempty i,
    hD_rank i, hD_genus i⟩, b, hb⟩

/-- **The disjoint decomposition over a perfect ground field.** Specialisation of
`AlgebraicGeometry.exists_iso_sigma_isRationalBridge_baseChange` to a perfect `k`.

The general statement no longer carries the two hypotheses this specialisation was introduced to
discharge — geometric reducedness of `X` over `k` and separability over `k` of the field of global
functions of the bridge are now derived from nodality for an arbitrary ground field, see the
implementation notes above — so nothing beyond perfectness of `k` separates the two, and the
proof is an application. It is kept because it is the form in which the perfect-field case is
cited elsewhere. -/
@[stacks 0E65 "CONDITIONALLY -- this is not an unconditional proof of 0E65: the binder `hgeom`,
geometric integrality of the bridge over its field of global functions, is not a hypothesis of the
tag, and `[PerfectField k]` is not either. Both are inherited from
`AlgebraicGeometry.exists_iso_sigma_isRationalBridge_baseChange`, which this specialises; see the
disclosure there. The tag at its own hypotheses, with the disjointness dropped from the
conclusion, is proved unconditionally as
`AlgebraicGeometry.exists_finset_isRationalBridge_baseChange` in
`ContractingRationalBridges/BaseChangeUnion.lean`"]
public theorem exists_iso_sigma_isRationalBridge_baseChange_of_perfectField
    (k K : Type u) [Field k] [PerfectField k] [Field K] [Algebra k K]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData)
    (hC : IsRationalBridge k X C)
    (hgeom :
      letI : IsIntegral C.subscheme := hC.isIntegral
      letI : Field Γ(C.subscheme, ⊤) :=
        (isField_of_universallyClosed k
          (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
      GeometricallyIntegral C.subscheme.toSpecΓ) :
    let g : Spec (.of K) ⟶ Spec (.of k) :=
      Spec.map (CommRingCat.ofHom (algebraMap k K))
    let Y := (pullback (X ↘ Spec (.of k)) g : Scheme.{u})
    let p : Y ⟶ X := pullback.fst (X ↘ Spec (.of k)) g
    letI : Y.Over (Spec (.of K)) := ⟨pullback.snd (X ↘ Spec (.of k)) g⟩
    letI : IsProper (Y ↘ Spec (.of K)) :=
      inferInstanceAs (IsProper (pullback.snd (X ↘ Spec (.of k)) g))
    ∃ (ι : Type u) (_ : Finite ι) (D : ι → Y.IdealSheafData)
        (_ : ∀ i, IsRationalBridge K Y (D i))
        (e : (∐ fun i ↦ (D i).subscheme) ≅ (C.comap p).subscheme),
      e.hom ≫ (C.comap p).subschemeι =
        Sigma.desc (fun i ↦ (D i).subschemeι) :=
  exists_iso_sigma_isRationalBridge_baseChange k K X hdim hnodal C hC hgeom

end AlgebraicGeometry

end
