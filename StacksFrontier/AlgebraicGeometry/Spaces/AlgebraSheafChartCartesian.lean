module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafChartCocycle
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts

/-!
# The chart transition of an algebra sheaf is cartesian on affine opens

`StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafChartTransition` builds the transition
comparison `𝒜|_V ⟶ (chartSchemeMap g)_* 𝒜|_W` of the chart restrictions of a sheaf of
`𝒪_X`-algebras along a morphism `g : W ⟶ V` of étale scheme charts of an algebraic space `X`,
and `StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafChartCocycle` the two cocycle laws of
that family.  Both record what is still missing before a glueing datum can be assembled: the
comparison is only a *morphism*, and nothing says it is cartesian.

This file supplies the cartesianness **on sections, over an affine Zariski open with affine
preimage**: there the sections of `𝒜|_W` over the preimage of the open are the base change of
the sections of `𝒜|_V` over it, along the restriction map of regular functions.  What is
supplied is the local content of the missing statement, not the global one; see the
implementation notes for exactly what remains.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.bijective_sectionsBaseChange_of_isQuasicoherent`: **a
  quasi-coherent sheaf of `𝒪_F`-algebras is cartesian on affine charts** — for a morphism of
  affine étale charts of `F` the base change comparison
  `𝒪_F(V) ⊗_{𝒪_F(U)} 𝒜(U) ⟶ 𝒜(V)` of
  `AlgebraicGeometry.Space.sectionsBaseChange` on the algebra's own sections is bijective.
* `AlgebraicGeometry.Space.AlgebraSheaf.sectionsBaseChange_tmul_eq`: on a pure tensor the
  comparison is `b ⊗ x ↦ 𝒜(b) · x|_V`, written with the structure-algebra map and the
  multiplication of the algebra rather than with a scalar action.
* `AlgebraicGeometry.Space.AlgebraSheaf.sectionsBaseChange_tmul_mul_tmul`: the comparison is
  **multiplicative on pure tensors**, so the bijection of the preceding result identifies
  `𝒜(V)` with the base change of `𝒜(U)` *as an algebra* and not merely as a module.
* `AlgebraicGeometry.Space.AlgebraSheaf.isQuasicoherent_iff_isCartesianOnAffineCharts`:
  Descent, Proposition 03DX (2) for a sheaf of algebras — it is quasi-coherent exactly when it
  is cartesian on affine charts.
* `AlgebraicGeometry.Space.AlgebraSheaf.bijective_sectionsBaseChange_chartOpensRestrict`:
  **the transition comparison of the chart restrictions is cartesian over an affine Zariski
  open with affine preimage.**  The comparison whose bijectivity this asserts is the base
  change of the section map of
  `AlgebraicGeometry.Space.AlgebraSheaf.restrictToChartSchemeTransition` over that open, by
  `AlgebraicGeometry.Space.AlgebraSheaf.restrictToChartSchemeTransition_app` together with
  `AlgebraicGeometry.Space.AlgebraSheaf.sectionsBaseChange_tmul_eq`.
* `AlgebraicGeometry.Space.chartOpensRestrictLE` and
  `AlgebraicGeometry.Space.exists_isAffine_le_preimage`: the chart morphism from a Zariski open
  of the smaller chart inside the preimage of one of the larger, and the statement that the
  affine such pairs **cover the smaller chart** — which the preimages of affine opens on their
  own do not, since the preimage of an affine open need not be affine.
* `AlgebraicGeometry.Space.AlgebraSheaf.bijective_sectionsBaseChange_chartOpensRestrictLE`:
  **the transition comparison is therefore cartesian over a family of affine opens covering
  the smaller chart**, which is the local statement at its full strength.

## Implementation notes

**The bridge is the underlying module, and it is the identity on sections.**  Quasi-coherence of
an algebra sheaf is by definition quasi-coherence of
`AlgebraicGeometry.Space.AlgebraSheaf.underlyingModule`, whose sections over a chart *are* the
algebra's sections and whose scalar action is multiplication by the image of the
structure-algebra map.  So the cartesianness statement for the algebra is the module statement
`AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_isQuasicoherentOnSite_anyUniverse` at
that module, with no transport; and the identification of the comparison with the algebra-level
base change map is an equality of terms.  This is the same bridge that
`AlgebraicGeometry.Space.AlgebraSheaf.underlyingModule_restrictToChartScheme` provides for
quasi-coherence of the chart restriction, used here one level down, on sections rather than on
sheaves.

**Why the transition appears only through its section maps.**  By
`AlgebraicGeometry.Space.AlgebraSheaf.restrictToChartSchemeTransition_app` the section map of
the transition over a Zariski open `O` of the larger chart is the restriction map of `𝒜` along
the morphism of étale charts `AlgebraicGeometry.Space.chartOpensRestrict`, on the nose, so the
base change comparison at that chart morphism is literally the base change of the transition's
section map.  That is what makes this file short.

**What is *not* proved here, and what it would take.**  The statement a descent datum for
Stacks 081V consumes is that the *inverse-image transpose* of the transition is an isomorphism
of sheaves of algebras on `chartScheme W`, which is strictly more than the family of section
bijections proved here.  Three separate inputs are missing, and none of them is formal.

* **The affine-local criterion.**  The opens of `chartScheme W` over which a bijection is
  available here are those of the form `O' ⊆ (chartSchemeMap g)⁻¹ O` with `O` affine in
  `chartScheme V` and `O'` affine, and they cover `chartScheme W`
  (`AlgebraicGeometry.Space.exists_isAffine_le_preimage`).  What is missing is the passage from
  bijectivity on such a family to invertibility of a morphism of sheaves whose source is a
  sheafification, which is the next item.
* **The sections of the algebra pullback.**  `Stacks.AffineAlgebraEquivalence.algebraPullback`
  is the pushout of sheaves of rings along `g⁻¹𝒪_V ⟶ 𝒪_W`, i.e. a *sheafification* of the
  objectwise tensor product; its sections over an open are therefore not the tensor product of
  sections, and identifying them needs exactly the step recorded as open in the implementation
  notes of
  `StacksFrontier/AlgebraicGeometry/FlatBaseChangeCohomology/AffineDegreeZero/AlgebraPushout.lean`.
  Its `Stacks.SheafOfModules.AlgebraPushout.extendScalarsComparison` now carries a
  `CategoryTheory.IsIso`, `Stacks.SheafOfModules.AlgebraPushout.isIso_extendScalarsComparison`;
  what the identification of sections still needs from that file is recorded there.
* **The module-level comparison.**  One level down the mate computation this called for is
  done.  `AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison` is still a bare
  morphism and `AlgebraicGeometry.Space.nonempty_pullback_restrictToChartScheme` still produces
  *some* isomorphism between its source and target without saying it is that morphism, but the
  canonical comparison is no longer opaque: the transposes through the Zariski sheafification
  adjunction and through
  `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` are computed on sections in
  `StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestrictionComparisonSections.lean`, whose
  `AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison_app_pullbackSection_toSheafify`
  identifies the comparison, on a pulled-back section, with the restriction map of the module
  along the induced morphism of étale charts.  What is left of this point is therefore only the
  first one: carrying the bijectivity of
  `AlgebraicGeometry.Space.sectionsBaseChange` over to the rings of regular functions on the two
  affine opens, which are isomorphic to the chart rings it is stated over but not equal to them.

**Invertibility of the chart restriction comparison is not Stacks 03M0.**  Stacks 03M0 is the
lemma characterizing quasi-coherence of a module on an algebraic space by its restrictions to
étale charts, registered as such on
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_over_of_isSurjective`,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_forall_affine_over` and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_etaleModulePullback_iff`; its affine clause (4)
in the chart-scheme reading, for *algebras*, is proved unconditionally as
`AlgebraicGeometry.Space.AlgebraSheaf.isQuasicoherent_restrictToChartScheme`.  The invertibility
of the comparison is the cartesianness of Descent, Proposition 03DX together with the
identification of the chart restriction with an inverse image, Stacks 03LY.
Nothing here is registered as 03M0, 03DX or 03LY.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u m

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-! ### A morphism of charts restricted to an open inside a preimage -/

/-- **The morphism of étale charts of `F` from a Zariski open of the smaller chart lying inside
the preimage of an open of the larger one.**  It is
`AlgebraicGeometry.Space.chartOpensRestrict` preceded by the inclusion of opens, and it is the
chart morphism over which the transition comparison of the chart restrictions is cartesian on a
family of opens covering the smaller chart — `chartOpensRestrict` alone only reaches the
preimages themselves, which need not be affine. -/
noncomputable def chartOpensRestrictLE {U V : SmallEtale B S hS F} (g : V ⟶ U)
    {O : (chartScheme U).Opens} {O' : (chartScheme V).Opens}
    (hle : O' ≤ chartSchemeMap g ⁻¹ᵁ O) :
    (chartOpens B S hS V).obj O' ⟶ (chartOpens B S hS U).obj O :=
  (chartOpens B S hS V).map (homOfLE hle) ≫ chartOpensRestrict B S hS g O

/-- **The affine Zariski opens of the smaller chart lying inside the preimage of an affine
Zariski open of the larger one cover the smaller chart.**  So the chart morphisms
`AlgebraicGeometry.Space.chartOpensRestrictLE` between affine charts reach every point of the
chart scheme of `V`, which the chart morphisms
`AlgebraicGeometry.Space.chartOpensRestrict` do not: the preimage of an affine open need not be
affine. -/
theorem exists_isAffine_le_preimage {U V : SmallEtale B S hS F} (g : V ⟶ U)
    (x : chartScheme V) :
    ∃ (O : (chartScheme U).Opens) (O' : (chartScheme V).Opens)
      (_ : O' ≤ chartSchemeMap g ⁻¹ᵁ O), x ∈ O' ∧
        IsAffine (chartScheme ((chartOpens B S hS U).obj O)) ∧
        IsAffine (chartScheme ((chartOpens B S hS V).obj O')) := by
  obtain ⟨O, hOaff, hxO, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := chartScheme U) (x := (chartSchemeMap g).base x) (U := ⊤) trivial
  obtain ⟨O', hO'aff, hxO', hsub⟩ := exists_isAffineOpen_mem_and_subset
    (X := chartScheme V) (x := x) (U := chartSchemeMap g ⁻¹ᵁ O) hxO
  exact ⟨O, O', hsub, hxO', hOaff, hO'aff⟩

namespace AlgebraSheaf

/-! ### The base change comparison on the sections of an algebra sheaf -/

/-- **The base change comparison of an algebra sheaf, on a pure tensor.**  Over a morphism
`f : V ⟶ U` of étale charts of `F` the comparison
`AlgebraicGeometry.Space.sectionsBaseChange` of the underlying module carries `b ⊗ x` to the
product, in the algebra of sections over `V`, of the image of `b` under the structure-algebra
map and the restriction of `x`.

This is an equality of terms: the scalar action on the sections of the underlying module *is*
multiplication by the image of the structure-algebra map.  The product is on the left so that
it is the product of the algebra of sections, rather than one the sections of the underlying
module would have to be given. -/
theorem sectionsBaseChange_tmul_eq (A : AlgebraSheaf.{u, m} B S hS F hF)
    {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (b : (structureSheaf B S hS F hF).obj.obj (op V)) (x : A.right.obj.obj (op U)) :
    letI := chartAlgebra (hF := hF) f
    A.algebraMap (op V) b * A.right.obj.map f.op x =
      sectionsBaseChange A.underlyingModule f (TensorProduct.tmul _ b x) :=
  rfl

/-- **The base change comparison of an algebra sheaf is multiplicative on pure tensors.**  So
where the comparison is bijective it identifies the sections over the smaller chart with the
base change of the sections over the larger one *as an algebra*, and not only as a module: the
ring structure of a base change is determined by its values on pure tensors.

Both sides are written through
`AlgebraicGeometry.Space.AlgebraSheaf.sectionsBaseChange_tmul_eq`, so that the multiplications
are those of the algebras of sections. -/
theorem sectionsBaseChange_tmul_mul_tmul (A : AlgebraSheaf.{u, m} B S hS F hF)
    {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (b b' : (structureSheaf B S hS F hF).obj.obj (op V))
    (x x' : A.right.obj.obj (op U)) :
    letI := chartAlgebra (hF := hF) f
    A.algebraMap (op V) b * A.right.obj.map f.op x *
        (A.algebraMap (op V) b' * A.right.obj.map f.op x') =
      sectionsBaseChange A.underlyingModule f (TensorProduct.tmul _ (b * b') (x * x')) := by
  let := chartAlgebra (hF := hF) f
  rw [← sectionsBaseChange_tmul_eq A f (b * b') (x * x'), map_mul, map_mul]
  ring

/-- **A quasi-coherent sheaf of `𝒪_F`-algebras is cartesian on affine charts.**  For a morphism
`f : V ⟶ U` of affine étale charts of `F` the base change comparison
`𝒪_F(V) ⊗_{𝒪_F(U)} 𝒜(U) ⟶ 𝒜(V)` on the algebra's own sections is bijective.

Quasi-coherence of an algebra sheaf is quasi-coherence of its underlying module, whose sections
are the algebra's sections, so this is the forward implication of Descent, Proposition 03DX for
the small étale site of `F` —
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite_anyUniverse` — read
at that module, with no transport in the way.  By
`AlgebraicGeometry.Space.AlgebraSheaf.sectionsBaseChange_tmul_mul_tmul` the bijection is
multiplicative, so it is an identification of algebras. -/
theorem bijective_sectionsBaseChange_of_isQuasicoherent
    (A : AlgebraSheaf.{u, m} B S hS F hF) (hA : A.IsQuasicoherent)
    {U V : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V))
    (f : V ⟶ U) :
    Function.Bijective (sectionsBaseChange A.underlyingModule f) :=
  bijective_sectionsBaseChange_of_isQuasicoherentOnSite_anyUniverse B S hS F hF
    A.underlyingModule hA hU hV f

/-- **Descent, Proposition 03DX (2) for a sheaf of algebras on the small étale site of an
algebraic space**: it is quasi-coherent exactly when it is cartesian on affine charts, that is,
when its sections over the smaller of two affine étale charts are the base change of its
sections over the larger one.

Quasi-coherence of an algebra sheaf *is* quasi-coherence of its underlying module and the
sections of the two agree, so this is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts_anyUniverse` at
that module. -/
theorem isQuasicoherent_iff_isCartesianOnAffineCharts
    (A : AlgebraSheaf.{u, m} B S hS F hF) :
    A.IsQuasicoherent ↔ IsCartesianOnAffineCharts A.underlyingModule :=
  isQuasicoherentOnSite_iff_isCartesianOnAffineCharts_anyUniverse B S hS F hF
    A.underlyingModule

/-! ### Cartesianness of the transition comparison of the chart restrictions -/

variable {X : AlgebraicSpaces B S hS}

/-- **The transition comparison of the chart restrictions of a quasi-coherent algebra sheaf is
cartesian over an affine Zariski open with affine preimage.**  Let `g : W ⟶ V` be a morphism of
étale scheme charts of `X` and let `O` be a Zariski open of the chart scheme of `V` such that
`O` and its preimage in the chart scheme of `W`, read as étale charts of `X`, are both affine.
Then the sections of `𝒜|_W` over the preimage of `O` are the base change of the sections of
`𝒜|_V` over `O`, along the restriction map of regular functions.

The comparison this asserts to be bijective is the one built from the section map of the
transition: by `AlgebraicGeometry.Space.AlgebraSheaf.restrictToChartSchemeTransition_app` the
transition over `O` *is* restriction of `𝒜` along the chart morphism
`AlgebraicGeometry.Space.chartOpensRestrict`, and by
`AlgebraicGeometry.Space.AlgebraSheaf.sectionsBaseChange_tmul_eq` the comparison at that chart
morphism carries `b ⊗ x` to the product of the image of `b` with the transition of `x`.  The
statement itself is
`AlgebraicGeometry.Space.AlgebraSheaf.bijective_sectionsBaseChange_of_isQuasicoherent` at that
chart morphism. -/
theorem bijective_sectionsBaseChange_chartOpensRestrict
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (hA : A.IsQuasicoherent)
    {V W : SmallEtale B S hS X.1} (g : W ⟶ V) (O : (chartScheme V).Opens)
    (hO : IsAffine (chartScheme ((chartOpens B S hS V).obj O)))
    (hO' : IsAffine
      (chartScheme ((chartOpens B S hS W).obj (chartSchemeMap g ⁻¹ᵁ O)))) :
    Function.Bijective
      (sectionsBaseChange A.underlyingModule (chartOpensRestrict B S hS g O)) :=
  bijective_sectionsBaseChange_of_isQuasicoherent A hA
    (U := (chartOpens B S hS V).obj O)
    (V := (chartOpens B S hS W).obj (chartSchemeMap g ⁻¹ᵁ O)) hO hO'
    (chartOpensRestrict B S hS g O)

/-- **The transition comparison of the chart restrictions of a quasi-coherent algebra sheaf is
cartesian over a family of affine opens covering the smaller chart.**  Let `g : V ⟶ U` be a
morphism of étale scheme charts of `F`, let `O` be a Zariski open of the chart scheme of `U`
and let `O'` be a Zariski open of the chart scheme of `V` contained in the preimage of `O`,
both affine as étale charts of `F`.  Then the sections of the algebra over `O'` are the base
change of its sections over `O`, along the restriction of regular functions.

Those pairs `(O, O')` cover the chart scheme of `V`, by
`AlgebraicGeometry.Space.exists_isAffine_le_preimage`; the restriction map over which the base
change is taken is the section map of
`AlgebraicGeometry.Space.AlgebraSheaf.restrictToChartSchemeTransition` over `O` followed by
restriction from the preimage of `O` to `O'`, since
`AlgebraicGeometry.Space.chartOpensRestrictLE` is the inclusion of opens followed by
`AlgebraicGeometry.Space.chartOpensRestrict`. -/
theorem bijective_sectionsBaseChange_chartOpensRestrictLE
    (A : AlgebraSheaf.{u, m} B S hS F hF) (hA : A.IsQuasicoherent)
    {U V : SmallEtale B S hS F} (g : V ⟶ U)
    {O : (chartScheme U).Opens} {O' : (chartScheme V).Opens}
    (hle : O' ≤ chartSchemeMap g ⁻¹ᵁ O)
    (hO : IsAffine (chartScheme ((chartOpens B S hS U).obj O)))
    (hO' : IsAffine (chartScheme ((chartOpens B S hS V).obj O'))) :
    Function.Bijective
      (sectionsBaseChange A.underlyingModule (chartOpensRestrictLE g hle)) :=
  bijective_sectionsBaseChange_of_isQuasicoherent A hA
    (U := (chartOpens B S hS U).obj O) (V := (chartOpens B S hS V).obj O') hO hO'
    (chartOpensRestrictLE g hle)

end AlgebraSheaf

end AlgebraicGeometry.Space

end
