module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Trace.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsEssentialImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverField
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldPointGaloisDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageSectionsOverChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos

/-!
# Global sections on the small étale site of the spectrum of a field are exact

Let `k` be a field and let `Y` be the algebraic space represented by `Spec k`.  Every module
over the structure sheaf of the small étale site of `Y` has vanishing higher cohomology:
the functor of global sections, which is the functor of sections over the identity chart
`Spec k ⟶ Spec k`, is exact.  This is additive Galois descent, the étale-site form of the
vanishing of `H^i(Gal(k^{sep}/k), V)` for a semilinear representation `V`.

The proof is the one by a trace-one element.  Let `𝓜 ⟶ 𝓝` be an epimorphism of
`𝒪_Y`-modules and `s` a global section of `𝓝`.  The section `s` lifts locally, and a covering
of `Spec k` in the small étale site contains a chart `Spec L ⟶ Spec k` with `L / k` a finite
Galois extension: an étale `k`-scheme is a disjoint union of spectra of finite separable
extensions (Stacks 03PC), and a finite separable extension embeds in a finite Galois one.  So
`s|_{Spec L}` is the image of a section `t` of `𝓜` over `Spec L`.  Choose `λ ∈ L` with
`Tr_{L/k}(λ) = 1`; then

`t' = ∑_{σ ∈ Gal(L/k)} σ^*(λ t)`

is invariant under the Galois group, and its image is `Tr_{L/k}(λ) · s|_{Spec L} = s|_{Spec L}`.
A Galois-invariant section over `Spec L` descends to `Spec k`: two morphisms `Z ⟶ Spec L` of
étale `k`-schemes differ, on each spectrum of a field in the decomposition of `Z`, by an element
of the Galois group, because two `k`-embeddings of a normal extension differ by an automorphism.
The descended section maps to `s`.

## Main definitions

* `AlgebraicGeometry.Space.separableChart`: the chart `Spec L ⟶ Spec k` of the small étale site
  of the spectrum of a field, for a finite separable extension `L / k`, with the action
  `AlgebraicGeometry.Space.separableChartAut` of the automorphisms of `L / k`.
* `AlgebraicGeometry.Space.separableChartHomOfScheme`: a morphism from a separable chart to an
  étale chart, from a morphism of schemes over `Spec k`.

## Main results

* `AlgebraicGeometry.Space.exists_separableChart_hom_mem_range`: the separable charts cover
  every étale chart of `Spec k` (Stacks 03PC).
* `AlgebraicGeometry.Space.exists_separableChartAut_of_isGalois`: two morphisms into a Galois
  chart differ by the Galois group.
* `AlgebraicGeometry.Space.exists_map_separableChartToId_eq`: Galois descent of sections of a
  sheaf of sets.
* `AlgebraicGeometry.Space.surjective_app_idEtaleChart_of_epi`: sections over `Spec k` take
  epimorphisms of sheaves of modules to surjections, for a sheaf of rings with trace-one
  elements on the Galois charts.
* `AlgebraicGeometry.Space.surjective_globalSectionsFunctor_map_of_epi`: global sections of
  `𝒪_{Spec k}`-modules on the small étale site take epimorphisms to surjections.
* `AlgebraicGeometry.Space.isZero_rightDerived_globalSectionsFunctor_of_field`: the higher
  cohomology of every `𝒪_{Spec k}`-module on the small étale site vanishes.
* `AlgebraicGeometry.Space.acyclicHigherDirectImages_of_field`: for every morphism of
  algebraic spaces `f : X ⟶ Spec k` and every `𝒪_X`-module, the higher direct images are
  acyclic for global sections, the hypothesis `AlgebraicGeometry.Space.AcyclicHigherDirectImages`.

## Implementation notes

The spectrum of the field is an object `V` of the big fppf site over `S` together with an
isomorphism of its underlying scheme with `Spec k`; nothing else about `V` is used.

The statement is for every `𝒪_{Spec k}`-module on the small étale site, not only for the
quasi-coherent ones.  In the source the two agree: every `𝒪`-module on the small étale site of
the spectrum of a field is quasi-coherent (Stacks 0D1W), and quasi-coherent modules on an affine
scheme have no higher étale cohomology (Stacks 03P2).  The proof here goes through neither: the
trace-one argument applies to an arbitrary module directly.

The covering of an étale `k`-scheme by spectra of finite separable extensions is taken from
`AlgebraicGeometry.etale_iff_iso_coproduct_spectra_finite_separable`.  Each such spectrum is
itself an étale chart of `Spec k`, with structure morphism `Spec L ⟶ Spec k`, so the morphisms
of charts needed in the argument are just morphisms of schemes over `Spec k`.

## References

* [Stacks Project, Tag 03PC](https://stacks.math.columbia.edu/tag/03PC)
* [Stacks Project, Tag 0D1W](https://stacks.math.columbia.edu/tag/0D1W)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 03QV](https://stacks.math.columbia.edu/tag/03QV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-! ### An element of trace one -/

/-- **A finite Galois extension has an element whose conjugates sum to one**: an element of
trace one, the trace being nonzero for a separable extension. -/
theorem IsGalois.exists_sum_algEquiv_apply_eq_one (K L : Type*) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    ∃ x : L, ∑ σ : L ≃ₐ[K] L, σ x = 1 := by
  obtain ⟨y, hy⟩ : ∃ y : L, Algebra.trace K L y ≠ 0 := by
    by_contra! h
    exact Algebra.trace_ne_zero K L (LinearMap.ext h)
  refine ⟨(Algebra.trace K L y)⁻¹ • y, ?_⟩
  rw [← trace_eq_sum_automorphisms, map_smul, smul_eq_mul, inv_mul_cancel₀ hy, map_one]

attribute [-instance] CategoryTheory.catToReflQuiver

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (K : Type u) [Field K] (V : BigFppfOver B S hS)
    (e : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of K))

/-! ### The separable charts of the spectrum of a field -/

section SeparableChart

variable (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- The morphism `Spec L ⟶ V` through the identification of `V` with `Spec k`. -/
abbrev separableSpecHom : Spec (.of L) ⟶ (BigFppfOver.toScheme B S hS).obj V :=
  Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ e.inv

/-- The morphism `Spec L ⟶ V` of a finite separable extension `L / k` is étale. -/
instance etale_separableSpecHom : Etale (separableSpecHom B S hS K V e L) := by
  have := etale_specMap_algebraMap K L
  infer_instance

include e in
/-- The spectrum of a finite separable extension lies in the big fppf site. -/
theorem contains_spec_of_isSeparable : B.Contains (Spec (.of L)) :=
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (separableSpecHom B S hS K V e L)
    V.left.property

/-- `Spec L` as an object of the big fppf site over `S`, through `Spec L ⟶ V ⟶ S`. -/
abbrev separableSpecObject : BigFppfOver B S hS :=
  siteObject B S hS (contains_spec_of_isSeparable B S hS K V e L)
    (separableSpecHom B S hS K V e L ≫ B.inclusion.map V.hom)

/-- The morphism `Spec L ⟶ V` of the big fppf site over `S`. -/
def separableSpecMap : separableSpecObject B S hS K V e L ⟶ V :=
  Over.homMk (ObjectProperty.homMk (separableSpecHom B S hS K V e L)) (by
    apply ObjectProperty.hom_ext
    rfl)

/-- The underlying morphism of schemes of `separableSpecMap` is `separableSpecHom`. -/
@[simp]
theorem toScheme_map_separableSpecMap :
    (BigFppfOver.toScheme B S hS).map (separableSpecMap B S hS K V e L) =
      separableSpecHom B S hS K V e L := rfl

/-- **The separable chart** `Spec L ⟶ Spec k` of the small étale site of the spectrum of a field,
for a finite separable extension `L / k`. -/
abbrev separableChart : SmallEtale B S hS (yoneda.obj V) :=
  ⟨CostructuredArrow.mk (yoneda.map (separableSpecMap B S hS K V e L)),
    (presheaf_yoneda_map_etale_iff B S hS _).2 (etale_separableSpecHom B S hS K V e L)⟩

/-- The scheme of the separable chart of `L` is `Spec L`. -/
theorem chartScheme_separableChart :
    chartScheme (separableChart B S hS K V e L) = Spec (.of L) := rfl

/-- The morphism from the separable chart to the identity chart. -/
def separableChartToId : separableChart B S hS K V e L ⟶ idEtaleChart B S hS V :=
  ObjectProperty.homMk (CostructuredArrow.homMk (separableSpecMap B S hS K V e L)
    (by change _ ≫ 𝟙 _ = _; exact Category.comp_id _))

/-- The action of an automorphism `σ` of `L / k` on the spectrum `Spec L`, over `V`. -/
def separableSpecAut (σ : L ≃ₐ[K] L) :
    separableSpecObject B S hS K V e L ⟶ separableSpecObject B S hS K V e L :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom σ.toRingHom))) (by
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ separableSpecHom B S hS K V e L ≫ _ =
      separableSpecHom B S hS K V e L ≫ _
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp]
    congr 3
    ext x
    exact σ.commutes x)

/-- The action of an automorphism of `L / k` on `Spec L` is a morphism over `V`. -/
theorem separableSpecAut_comp_separableSpecMap (σ : L ≃ₐ[K] L) :
    separableSpecAut B S hS K V e L σ ≫ separableSpecMap B S hS K V e L =
      separableSpecMap B S hS K V e L := by
  ext
  show Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ separableSpecHom B S hS K V e L =
    separableSpecHom B S hS K V e L
  rw [← Category.assoc, ← Spec.map_comp]
  congr 3
  ext x
  exact σ.commutes x

/-- **The action of the automorphisms of `L / k` on the separable chart**: the automorphism `σ`
of `L / k` acts on the chart
`Spec L ⟶ Spec k` through `Spec σ`. -/
def separableChartAut (σ : L ≃ₐ[K] L) :
    separableChart B S hS K V e L ⟶ separableChart B S hS K V e L :=
  ObjectProperty.homMk (CostructuredArrow.homMk (separableSpecAut B S hS K V e L σ) (by
    change yoneda.map _ ≫ yoneda.map _ = yoneda.map _
    rw [← Functor.map_comp, separableSpecAut_comp_separableSpecMap]))

/-- The underlying morphism of schemes of the action of `σ` on the separable chart is
`Spec σ`. -/
@[simp]
theorem toScheme_map_toOver_map_separableChartAut (σ : L ≃ₐ[K] L) :
    (BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS (yoneda.obj V)).map (separableChartAut B S hS K V e L σ)) =
      Spec.map (CommRingCat.ofHom σ.toRingHom) := rfl

/-- The action of `σ * τ` on the separable chart is the action of `σ` followed by that of
`τ`. -/
theorem separableChartAut_mul (σ τ : L ≃ₐ[K] L) :
    separableChartAut B S hS K V e L (σ * τ) =
      separableChartAut B S hS K V e L σ ≫ separableChartAut B S hS K V e L τ := by
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  ext
  show Spec.map (CommRingCat.ofHom (σ * τ).toRingHom) =
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.map (CommRingCat.ofHom τ.toRingHom)
  rw [← Spec.map_comp]
  rfl

end SeparableChart

/-! ### Morphisms into and between the separable charts -/

section Charts

/-- The structure morphism over `V` of an étale chart `W` of the algebraic space represented by
`V`, as a morphism of the big fppf site: the Yoneda preimage of the chart. -/
def representableChartOverHom (W : SmallEtale B S hS (yoneda.obj V)) :
    (SmallEtale.toOver B S hS (yoneda.obj V)).obj W ⟶ V :=
  Yoneda.fullyFaithful.preimage W.obj.hom

/-- The Yoneda image of `representableChartOverHom` is the structure morphism of the chart. -/
theorem yoneda_map_representableChartOverHom (W : SmallEtale B S hS (yoneda.obj V)) :
    yoneda.map (representableChartOverHom B S hS V W) = W.obj.hom :=
  Yoneda.fullyFaithful.map_preimage _

/-- The structure morphism of schemes over `V` of an étale chart of `V`. -/
abbrev representableChartHom (W : SmallEtale B S hS (yoneda.obj V)) :
    chartScheme W ⟶ (BigFppfOver.toScheme B S hS).obj V :=
  (BigFppfOver.toScheme B S hS).map (representableChartOverHom B S hS V W)

/-- The structure morphism over `V` of an étale chart of `V` is étale. -/
theorem etale_representableChartHom (W : SmallEtale B S hS (yoneda.obj V)) :
    Etale (representableChartHom B S hS V W) :=
  (presheaf_yoneda_map_etale_iff B S hS _).1
    ((yoneda_map_representableChartOverHom B S hS V W).symm ▸ W.property)

/-- A morphism of étale charts of `V` is a morphism over `V`. -/
theorem toOver_map_comp_representableChartOverHom {W W' : SmallEtale B S hS (yoneda.obj V)}
    (φ : W ⟶ W') :
    (SmallEtale.toOver B S hS (yoneda.obj V)).map φ ≫ representableChartOverHom B S hS V W' =
      representableChartOverHom B S hS V W := by
  apply yoneda.map_injective
  rw [Functor.map_comp, yoneda_map_representableChartOverHom, yoneda_map_representableChartOverHom]
  exact CostructuredArrow.w φ.hom

/-- A morphism of étale charts of `V` commutes with their structure morphisms of schemes
over `V`. -/
theorem representableChartHom_naturality {W W' : SmallEtale B S hS (yoneda.obj V)} (φ : W ⟶ W') :
    (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS (yoneda.obj V)).map φ) ≫
      representableChartHom B S hS V W' = representableChartHom B S hS V W := by
  rw [← Functor.map_comp, toOver_map_comp_representableChartOverHom]

/-- The structure morphism over `V` of the separable chart of `L` is `separableSpecMap`. -/
theorem representableChartOverHom_separableChart (L : Type u) [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    representableChartOverHom B S hS V (separableChart B S hS K V e L) =
      separableSpecMap B S hS K V e L :=
  yoneda.map_injective (yoneda_map_representableChartOverHom B S hS V _)

/-- The structure morphism of schemes over `V` of the separable chart of `L` is
`separableSpecHom`. -/
theorem representableChartHom_separableChart (L : Type u) [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    representableChartHom B S hS V (separableChart B S hS K V e L) =
      separableSpecHom B S hS K V e L := by
  rw [representableChartHom, representableChartOverHom_separableChart]
  rfl

variable {B S hS K V e}

/-- The morphism `Spec L ⟶ W` of the big fppf site over `S`, for a morphism of schemes over
`V` from `Spec L` to the scheme of an étale chart `W`. -/
def separableSpecOverHom (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] (W : SmallEtale B S hS (yoneda.obj V))
    (h : Spec (.of L) ⟶ chartScheme W)
    (hh : h ≫ representableChartHom B S hS V W = separableSpecHom B S hS K V e L) :
    separableSpecObject B S hS K V e L ⟶ (SmallEtale.toOver B S hS (yoneda.obj V)).obj W :=
  Over.homMk (ObjectProperty.homMk h) (by
    apply ObjectProperty.hom_ext
    have hw := Over.w (representableChartOverHom B S hS V W)
    change h ≫ ((SmallEtale.toOver B S hS (yoneda.obj V)).obj W).hom.hom =
      separableSpecHom B S hS K V e L ≫ V.hom.hom
    rw [← hw]
    change (h ≫ representableChartHom B S hS V W) ≫ V.hom.hom = _
    rw [hh])

/-- The morphism `separableSpecOverHom L W h hh` followed by the structure morphism of `W`
over `V` is `separableSpecMap`. -/
theorem separableSpecOverHom_comp (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] (W : SmallEtale B S hS (yoneda.obj V))
    (h : Spec (.of L) ⟶ chartScheme W)
    (hh : h ≫ representableChartHom B S hS V W = separableSpecHom B S hS K V e L) :
    separableSpecOverHom L W h hh ≫ representableChartOverHom B S hS V W =
      separableSpecMap B S hS K V e L := by
  ext
  exact hh

/-- A morphism of the separable chart of `L` into an étale chart `W`, from a morphism of schemes
`Spec L ⟶ W` over `V`. -/
def separableChartHomOfScheme (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] (W : SmallEtale B S hS (yoneda.obj V))
    (h : Spec (.of L) ⟶ chartScheme W)
    (hh : h ≫ representableChartHom B S hS V W = separableSpecHom B S hS K V e L) :
    separableChart B S hS K V e L ⟶ W :=
  ObjectProperty.homMk (CostructuredArrow.homMk (separableSpecOverHom L W h hh) (by
    change yoneda.map _ ≫ W.obj.hom = yoneda.map _
    rw [← yoneda_map_representableChartOverHom, ← Functor.map_comp, separableSpecOverHom_comp]))

/-- The underlying morphism of schemes of `separableChartHomOfScheme L W h hh` is `h`. -/
@[simp]
theorem toScheme_map_separableChartHomOfScheme (L : Type u) [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (W : SmallEtale B S hS (yoneda.obj V))
    (h : Spec (.of L) ⟶ chartScheme W)
    (hh : h ≫ representableChartHom B S hS V W = separableSpecHom B S hS K V e L) :
    (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS (yoneda.obj V)).map
      (separableChartHomOfScheme L W h hh)) = h := rfl

/-- Two morphisms of étale charts agree when their morphisms of schemes agree. -/
theorem SmallEtale.hom_ext_of_toScheme {W W' : SmallEtale B S hS (yoneda.obj V)}
    {f g : W ⟶ W'} (h : (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS _).map f) =
      (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS _).map g)) : f = g := by
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  ext
  exact h

/-- The morphism of schemes underlying a morphism from a separable chart to another is over
`V`. -/
theorem toScheme_map_comp_representableChartHom {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {W : SmallEtale B S hS (yoneda.obj V)}
    (φ : separableChart B S hS K V e L ⟶ W) :
    (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS _).map φ) ≫
      representableChartHom B S hS V W = separableSpecHom B S hS K V e L := by
  rw [representableChartHom_naturality, representableChartHom_separableChart]

/-- **Morphisms between separable charts are spectra of embeddings.**  Every morphism from the
separable chart of `L'` to that of `L` is `Spec ρ` for a `k`-algebra map `ρ : L ⟶ L'`. -/
theorem exists_algHom_of_separableChart_hom {L L' : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Field L'] [Algebra K L']
    [FiniteDimensional K L'] [Algebra.IsSeparable K L']
    (φ : separableChart B S hS K V e L' ⟶ separableChart B S hS K V e L) :
    ∃ ρ : L →ₐ[K] L', (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS _).map φ) =
      Spec.map (CommRingCat.ofHom ρ.toRingHom) := by
  set φs := (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS _).map φ)
  have h1 := toScheme_map_comp_representableChartHom φ
  rw [representableChartHom_separableChart, separableSpecHom, ← Category.assoc] at h1
  set ρ0 := Spec.preimage φs
  have hρ0 : Spec.map ρ0 = φs := Spec.map_preimage φs
  have hcomm : CommRingCat.ofHom (algebraMap K L) ≫ ρ0 = CommRingCat.ofHom (algebraMap K L') := by
    apply Spec.map_injective
    rw [Spec.map_comp, hρ0]
    exact (cancel_mono e.inv).1 h1
  exact ⟨{ ρ0.hom with commutes' := fun x => congrArg (fun f => f.hom x) hcomm }, hρ0.symm⟩

/-- The morphism of separable charts given by a `k`-algebra map `ι : L ⟶ L'`: the morphism
`Spec ι : Spec L' ⟶ Spec L`. -/
def separableChartHomOfAlgHom {L L' : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Field L'] [Algebra K L']
    [FiniteDimensional K L'] [Algebra.IsSeparable K L'] (ι : L →ₐ[K] L') :
    separableChart B S hS K V e L' ⟶ separableChart B S hS K V e L :=
  separableChartHomOfScheme L' (separableChart B S hS K V e L)
    (Spec.map (CommRingCat.ofHom ι.toRingHom)) (by
      rw [representableChartHom_separableChart, separableSpecHom, separableSpecHom,
        ← Category.assoc, ← Spec.map_comp]
      congr 3
      ext x
      exact ι.commutes x)

/-- **Two morphisms into a Galois chart differ by the Galois action.**  If `L / k` is finite
Galois, any two morphisms from a separable chart to the chart of `L` differ by an element of
`Gal(L/k)`. -/
theorem exists_separableChartAut_of_isGalois {L L' : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Field L'] [Algebra K L']
    [FiniteDimensional K L'] [Algebra.IsSeparable K L']
    (φ₁ φ₂ : separableChart B S hS K V e L' ⟶ separableChart B S hS K V e L) :
    ∃ σ : L ≃ₐ[K] L, φ₂ = φ₁ ≫ separableChartAut B S hS K V e L σ := by
  obtain ⟨ρ₁, h₁⟩ := exists_algHom_of_separableChart_hom φ₁
  obtain ⟨ρ₂, h₂⟩ := exists_algHom_of_separableChart_hom φ₂
  obtain ⟨σ, hσ⟩ := AlgHom.exists_algEquiv_comp_eq_of_normal K L L' ρ₂ ρ₁
  refine ⟨σ, SmallEtale.hom_ext_of_toScheme ?_⟩
  rw [Functor.map_comp, Functor.map_comp, h₂, h₁, toScheme_map_toOver_map_separableChartAut,
    ← Spec.map_comp, ← hσ]
  rfl

/-- **The scheme of an étale chart of `Spec k` is covered by separable charts**: every point
lies in the image of a morphism from the chart of a finite separable extension.  This is the
decomposition of an étale `k`-scheme into spectra of finite separable extensions (Stacks 03PC). -/
theorem exists_separableChart_hom_mem_range (W : SmallEtale B S hS (yoneda.obj V))
    (x : chartScheme W) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L) (m : separableChart B S hS K V e L ⟶ W),
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS (yoneda.obj V)).map m)) := by
  have := etale_representableChartHom B S hS V W
  obtain ⟨I, Kf, hK, hAlg, hFin, hSep, e', he'⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable K
      (representableChartHom B S hS V W ≫ e.hom)).1 inferInstance
  obtain ⟨⟨i, y⟩, hy⟩ := (sigmaMk fun i ↦ Spec (.of (Kf i))).surjective (e'.hom x)
  rw [sigmaMk_mk] at hy
  have hh : (Sigma.ι (fun i ↦ Spec (.of (Kf i))) i ≫ e'.inv) ≫ representableChartHom B S hS V W =
      separableSpecHom B S hS K V (L := Kf i) e := by
    rw [separableSpecHom, ← cancel_mono e.hom, Category.assoc, Category.assoc, Category.assoc,
      e.inv_hom_id, Category.comp_id, ← he', Iso.inv_hom_id_assoc, Sigma.ι_desc]
  refine ⟨Kf i, hK i, hAlg i, hFin i, hSep i,
    separableChartHomOfScheme (Kf i) W _ hh, y, ?_⟩
  rw [toScheme_map_separableChartHomOfScheme]
  show e'.inv (Sigma.ι (fun i ↦ Spec (.of (Kf i))) i y) = x
  rw [hy, ← Scheme.Hom.comp_apply, e'.hom_inv_id]
  rfl

end Charts

/-! ### Galois descent of sections -/

section Descent

variable {B S hS K V e}

/-- A sieve of an étale chart of `Spec k` is covering as soon as it contains every morphism from
a separable chart: the separable charts cover every étale chart. -/
theorem mem_topology_of_forall_separableChart {W : SmallEtale B S hS (yoneda.obj V)} (T : Sieve W)
    (hT : ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
      [Algebra.IsSeparable K L] (m : separableChart B S hS K V e L ⟶ W), T.arrows m) :
    T ∈ SmallEtale.topology B S hS (yoneda.obj V) W := by
  rw [SmallEtale.mem_topology_iff_exists_mem_range]
  intro x
  obtain ⟨L, _, _, _, _, m, hm⟩ := exists_separableChart_hom_mem_range (e := e) W x
  exact ⟨_, m, hT L m, hm⟩

/-- The separable chart of a nonzero extension covers the identity chart. -/
theorem generate_separableChartToId_mem_topology (L : Type u) [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Sieve.generate (Presieve.singleton (separableChartToId B S hS K V e L)) ∈
      SmallEtale.topology B S hS (yoneda.obj V) (idEtaleChart B S hS V) := by
  rw [SmallEtale.mem_topology_iff_exists_mem_range]
  intro x
  have key : ∀ y : (BigFppfOver.toScheme B S hS).obj V,
      (Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ e.inv)
        (Classical.arbitrary (Spec (.of L))) = y := by
    intro y
    rw [Scheme.Hom.comp_apply, Subsingleton.elim (Spec.map _ _) (e.hom y),
      ← Scheme.Hom.comp_apply, e.hom_inv_id]
    rfl
  exact ⟨_, separableChartToId B S hS K V e L,
    ⟨_, 𝟙 _, _, Presieve.singleton.mk, Category.id_comp _⟩, _, key x⟩

/-- **Galois descent of sections.**  Let `L / k` be a finite Galois extension.  A section of a
sheaf of sets on the small étale site of `Spec k` over the chart `Spec L` which is invariant
under `Gal(L/k)` is the restriction of a section over `Spec k`. -/
theorem exists_map_separableChartToId_eq {P : (SmallEtale B S hS (yoneda.obj V))ᵒᵖ ⥤ Type*}
    (hP : Presieve.IsSheaf (SmallEtale.topology B S hS (yoneda.obj V)) P)
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (t : P.obj (op (separableChart B S hS K V e L)))
    (ht : ∀ σ : L ≃ₐ[K] L, P.map (separableChartAut B S hS K V e L σ).op t = t) :
    ∃ t₀ : P.obj (op (idEtaleChart B S hS V)),
      P.map (separableChartToId B S hS K V e L).op t₀ = t := by
  have hfor := hP _ (generate_separableChartToId_mem_topology (e := e) L)
  rw [← Presieve.isSheafFor_iff_generate] at hfor
  obtain ⟨t₀, ht₀, -⟩ := Presieve.isSheafFor_singleton.1 hfor t (fun {Z} p₁ p₂ _ => by
    let T : Sieve Z :=
      { arrows := fun Y g => P.map g.op (P.map p₁.op t) = P.map g.op (P.map p₂.op t)
        downward_closed := fun {Y Y'} g hg f => by
          rw [op_comp, FunctorToTypes.map_comp_apply, FunctorToTypes.map_comp_apply]
          exact congrArg _ hg }
    refine (hP T (mem_topology_of_forall_separableChart (e := e) T fun L' _ _ _ _ m => ?_)
      ).isSeparatedFor.ext fun Y g hg => hg
    obtain ⟨σ, hσ⟩ := exists_separableChartAut_of_isGalois (m ≫ p₁) (m ≫ p₂)
    show P.map m.op (P.map p₁.op t) = P.map m.op (P.map p₂.op t)
    rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp,
      ← op_comp, hσ, show ((m ≫ p₁) ≫ separableChartAut B S hS K V e L σ).op =
        (separableChartAut B S hS K V e L σ).op ≫ (m ≫ p₁).op from rfl,
      FunctorToTypes.map_comp_apply, ht])
  exact ⟨t₀, ht₀⟩

end Descent

/-! ### Exactness of sections over `Spec k` -/

section Exact

variable {B S hS K V e}
variable (R : Sheaf (SmallEtale.topology B S hS (yoneda.obj V)) RingCat.{u})

open Stacks.SheafOfModules.ChangeOfRings in
/-- **Sections over `Spec k` take epimorphisms of sheaves of modules to surjections**, for a
sheaf of rings `R` on the small étale site of `Spec k` which has, over every finite Galois
chart `Spec L`, an element whose `Gal(L/k)`-conjugates sum to one. -/
theorem surjective_app_idEtaleChart_of_epi
    (hR : ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
      ∃ c : R.obj.obj (op (separableChart B S hS K V e L)),
        ∑ σ : L ≃ₐ[K] L, R.obj.map (separableChartAut B S hS K V e L σ).op c = 1)
    {M N : SheafOfModules.{u} R} (p : M ⟶ N) [Epi p] :
    Function.Surjective (p.val.app (op (idEtaleChart B S hS V))) := by
  have nat : ∀ {X : (SmallEtale B S hS (yoneda.obj V))ᵒᵖ} (m : M.val.obj X) {Y} (g : Y ⟶ X.unop),
      p.val.app (op Y) (sectionRestrict M m g) = sectionRestrict N (p.val.app X m) g :=
    fun m _ g => PresheafOfModules.naturality_apply p.val g.op m
  have rsum : ∀ {X : (SmallEtale B S hS (yoneda.obj V))ᵒᵖ} {ι : Type u} (A : Finset ι)
      (m : ι → M.val.obj X) {Y} (g : Y ⟶ X.unop),
      sectionRestrict M (∑ i ∈ A, m i) g = ∑ i ∈ A, sectionRestrict M (m i) g :=
    fun A m _ g => map_sum (M.val.map g.op).hom m A
  intro s
  have hls := Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi p
  have hmem := Presheaf.imageSieve_mem (SmallEtale.topology B S hS (yoneda.obj V))
    ((PresheafOfModules.toPresheaf R.obj).map p.val) s
  obtain ⟨W, g, ⟨t, ht⟩, x, -⟩ :=
    (SmallEtale.mem_topology_iff_exists_mem_range B S hS (yoneda.obj V) _).1 hmem
      (e.inv (Classical.arbitrary (Spec (.of K))))
  obtain ⟨t, ht'⟩ : ∃ t' : M.val.obj (op W), p.val.app (op W) t' = sectionRestrict N s g :=
    ⟨t, ht⟩
  obtain ⟨K', _, _, _, _, m, -⟩ := exists_separableChart_hom_mem_range (e := e) W x
  obtain ⟨L, _, _, _, _, ⟨ι⟩⟩ := exists_isGalois_of_finiteDimensional_of_isSeparable K K'
  set c := separableChartToId B S hS K V e L
  set n : separableChart B S hS K V e L ⟶ W := separableChartHomOfAlgHom ι ≫ m
  have hc : n ≫ g = c := (isTerminalIdEtaleChart B S hS V).hom_ext _ _
  have hcσ : ∀ σ : L ≃ₐ[K] L, separableChartAut B S hS K V e L σ ≫ c = c := fun σ =>
    (isTerminalIdEtaleChart B S hS V).hom_ext _ _
  set aut := separableChartAut B S hS K V e L
  have ht₁ : p.val.app _ (sectionRestrict M t n) = sectionRestrict N s c := by
    rw [nat, ht', sectionRestrict_sectionRestrict, hc]
  obtain ⟨l, hl⟩ := hR L
  obtain ⟨t₂, ht₂⟩ : ∃ t₂ : M.val.obj (op (separableChart B S hS K V e L)),
      t₂ = ∑ σ : L ≃ₐ[K] L, sectionRestrict M (l • sectionRestrict M t n) (aut σ) := ⟨_, rfl⟩
  have hinv : ∀ τ : L ≃ₐ[K] L, sectionRestrict M t₂ (aut τ) = t₂ := fun τ => by
    rw [ht₂, rsum]
    refine Fintype.sum_bijective (τ * ·) (Group.mulLeft_bijective τ) _ _ fun σ => ?_
    rw [sectionRestrict_sectionRestrict]
    exact congrArg _ (separableChartAut_mul B S hS K V e L τ σ).symm
  obtain ⟨t₀, ht₀'⟩ : ∃ t₀ : M.val.obj (op (idEtaleChart B S hS V)),
      sectionRestrict M t₀ c = t₂ := exists_map_separableChartToId_eq (e := e)
        (isSheafOfTypes_of_isSheaf M.val.presheaf M.isSheaf) L t₂ hinv
  have hterm : ∀ σ : L ≃ₐ[K] L,
      p.val.app _ (sectionRestrict M (l • sectionRestrict M t n) (aut σ)) =
        R.obj.map (aut σ).op l • sectionRestrict N s c := fun σ => by
    rw [nat, map_smul, sectionRestrict_smul, ht₁, sectionRestrict_sectionRestrict, hcσ]
  have key : sectionRestrict N (p.val.app _ t₀) c = sectionRestrict N s c := by
    rw [← nat, ht₀', ht₂, map_sum, Finset.sum_congr rfl fun σ _ => hterm σ, ← Finset.sum_smul,
      hl, one_smul]
  refine ⟨t₀, sections_ext N (generate_separableChartToId_mem_topology (e := e) L) ?_⟩
  rintro Y _ ⟨_, h, _, ⟨⟩, rfl⟩
  have := congrArg (fun z => sectionRestrict N z h) key
  rwa [sectionRestrict_sectionRestrict, sectionRestrict_sectionRestrict] at this

variable (hV : IsAlgebraicSpace B S hS (yoneda.obj V))

/-- The structure sheaf of the small étale site of `Spec k` has, over the chart of a finite
Galois extension `L / k`, an element whose Galois conjugates sum to one: an element of `L` of
trace one, read as a regular function on `Spec L`. -/
theorem exists_sum_structureSheaf_map_separableChartAut_eq_one (L : Type u) [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    ∃ c : (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (yoneda.obj V) hV).O).obj.obj
          (op (separableChart B S hS K V e L)),
      ∑ σ : L ≃ₐ[K] L, (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (yoneda.obj V) hV).O).obj.map
          (separableChartAut B S hS K V e L σ).op c = 1 := by
  obtain ⟨x, hx⟩ := IsGalois.exists_sum_algEquiv_apply_eq_one K L
  refine ⟨(Scheme.ΓSpecIso (.of L)).inv.hom x, ?_⟩
  have hσ : ∀ σ : L ≃ₐ[K] L, (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (yoneda.obj V) hV).O).obj.map
        (separableChartAut B S hS K V e L σ).op ((Scheme.ΓSpecIso (.of L)).inv.hom x) =
      (Scheme.ΓSpecIso (.of L)).inv.hom (σ x) := fun σ =>
    (congrArg (fun f => f.hom x)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ.toRingHom))).symm
  refine (Finset.sum_congr rfl fun σ _ => hσ σ).trans ?_
  exact (map_sum (Scheme.ΓSpecIso (.of L)).inv.hom (fun σ : L ≃ₐ[K] L => σ x)
    Finset.univ).symm.trans (by rw [hx, map_one]; rfl)

include e in
/-- **Sections over `Spec k` of `𝒪_{Spec k}`-modules on the small étale site take
epimorphisms to surjections.** -/
theorem surjective_app_idEtaleChart_of_epi_structureSheaf
    {M N : Modules.{u, u} B S hS (yoneda.obj V) hV} (p : M ⟶ N) [Epi p] :
    Function.Surjective (p.val.app (op (idEtaleChart B S hS V))) :=
  @surjective_app_idEtaleChart_of_epi B S hS K _ V e _
    (fun L _ _ _ _ => exists_sum_structureSheaf_map_separableChartAut_eq_one (e := e) hV L) M N p
    ‹_›

include e in
/-- **Global sections of `𝒪_{Spec k}`-modules on the small étale site take epimorphisms to
surjections**: the global sections are the sections over the identity chart, a terminal
object. -/
theorem surjective_globalSectionsFunctor_map_of_epi
    {M N : Modules.{u, u} B S hS (yoneda.obj V) hV} (p : M ⟶ N) [Epi p] :
    Function.Surjective ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (yoneda.obj V) hV).O)).map p) := by
  let eM := Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal M
    (isTerminalIdEtaleChart B S hS V)
  let eN := Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal N
    (isTerminalIdEtaleChart B S hS V)
  intro s
  obtain ⟨t₀, ht₀⟩ := surjective_app_idEtaleChart_of_epi_structureSheaf (e := e) hV p (eN s)
  exact ⟨eM.symm t₀, eN.injective ((congrArg (p.val.app _) (eM.apply_symm_apply t₀)).trans ht₀)⟩

end Exact

/-! ### Vanishing of the higher cohomology -/

section Vanishing

attribute [local instance 5000] SheafOfModules.instAbelian

variable {B S hS K V}
variable (hV : IsAlgebraicSpace B S hS (yoneda.obj V))

include e in
/-- **Global sections of `𝒪_{Spec k}`-modules on the small étale site are exact.** -/
theorem preservesFiniteColimits_globalSectionsFunctor_of_field :
    PreservesFiniteColimits (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (yoneda.obj V) hV).O)) := by
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS (yoneda.obj V) hV
  have : (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (yoneda.obj V) hV).O)).PreservesEpimorphisms :=
    ⟨fun p _ => (ModuleCat.epi_iff_surjective _).2
      (surjective_globalSectionsFunctor_map_of_epi (e := e) hV p)⟩
  have := Functor.preservesHomology_of_preservesEpis_and_kernels
    (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (yoneda.obj V) hV).O))
  have : Abelian (Modules.{u, u} B S hS (yoneda.obj V) hV) := inferInstance
  have : HasZeroObject (Modules.{u, u} B S hS (yoneda.obj V) hV) := inferInstance
  have : HasFiniteCoproducts (Modules.{u, u} B S hS (yoneda.obj V) hV) := inferInstance
  have : HasCokernels (Modules.{u, u} B S hS (yoneda.obj V) hV) := inferInstance
  exact Functor.preservesFiniteColimits_of_preservesHomology _

include e in
/-- **The higher cohomology of every `𝒪_{Spec k}`-module on the small étale site vanishes**:
`H^n(Spec k, 𝓝) = 0` for `n > 0`. -/
theorem isZero_rightDerived_globalSectionsFunctor_of_field
    (N : Modules.{u, u} B S hS (yoneda.obj V) hV) (n : ℕ) (hn : 0 < n) :
    have := hasInjectiveResolutions_modules B S hS (yoneda.obj V) hV
    IsZero (((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (yoneda.obj V) hV).O)).rightDerived n).obj N) := by
  have := hasInjectiveResolutions_modules B S hS (yoneda.obj V) hV
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS (yoneda.obj V) hV
  have := preservesFiniteColimits_globalSectionsFunctor_of_field e hV
  exact Functor.isZero_rightDerived_of_exact _ N n hn

include e in
/-- **The higher direct images along a morphism to `Spec k` are acyclic for global sections.**
For every morphism of algebraic spaces `f : X ⟶ Spec k` and every `𝒪_X`-module `𝓕`, the
hypothesis `AlgebraicGeometry.Space.AcyclicHigherDirectImages` holds: every `𝒪_{Spec k}`-module
has vanishing higher cohomology. -/
theorem acyclicHigherDirectImages_of_field {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V)
    (F : Modules.{u, u} B S hS X.1 X.2) : AcyclicHigherDirectImages B S hS f F :=
  fun _ n hn => isZero_rightDerived_globalSectionsFunctor_of_field e (schemeSpace V).2 _ n hn

end Vanishing

end AlgebraicGeometry.Space
