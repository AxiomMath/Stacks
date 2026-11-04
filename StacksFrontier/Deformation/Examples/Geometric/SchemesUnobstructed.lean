module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleAffineAvoidance.AmpleFiniteSet
public import StacksFrontier.AlgebraicGeometry.HQuasiProjectiveDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.LocalCompleteIntersection
public import StacksFrontier.Deformation.Examples.Geometric.SchemesTwoOpenCoverSmooth

/-!
# Stacks Tag 0DZQ: deformations of a curve with isolated singularities are unobstructed

In Example 0DY7 let `X` be a scheme over a field `k`. Assume

1. `X` is separated and of finite type over `k` and `dim(X) ≤ 1`,
2. `X` is a local complete intersection over `k`, and
3. `X → Spec(k)` is smooth except at finitely many points.

Then `Def_X` is unobstructed, that is, the structure morphism of `Def_X` over `𝒞_Λ` is smooth.

The source's proof is a two-chart reduction. Choose an affine open `U₂ ⊆ X` containing every
non-smooth point of `X` and the generic point of every irreducible component; then `X ∖ U₂` is
finite, so a second affine open `U₁` avoiding the non-smooth points covers it, and `X = U₁ ∪ U₂`.
Both `U₁` and `U₁₂ = U₁ ∩ U₂` lie in the smooth locus, so Tag 0DZN applies and
`Def_X ⟶ Def_{U₂}` is smooth; `Def_{U₂} = Def_{P₂}` by Tag 0DYX and `Def_{P₂} ⟶ 𝒞_Λ` is smooth
by Tag 0DZH, `P₂` being a local complete intersection over `k`.

## Main definitions

* `Deformation.Examples.sectionsAlgebra`: the `k`-algebra structure on the sections of a scheme
  over `Spec k` on an open subset — the coordinate ring of a chart.
* `Deformation.Examples.gluingSituationOfAffineCover`: Situation 0DYY built from a cover of a
  scheme over `k` by two affine opens with affine intersection.
* `Deformation.Examples.GluingComparisonSmooth`: **Tag 0DYZ as a carried hypothesis**, see below.
* `Deformation.Examples.SmoothSectionsOfSmoothAffineOpen`: **the affine-local reading of
  smoothness over a field as a carried hypothesis**, see below.

## Main results

* `Deformation.Examples.finite_of_isClosed_disjoint_genericPoints`: a closed subset of a
  Noetherian scheme of dimension at most one containing no generic point of an irreducible
  component is finite. This is the step of the source's proof that makes `X ∖ U₂` finite.
* `Deformation.Examples.exists_affineOpen_cover_avoiding_of_topologicalKrullDim_le_one`:
  **the geometric heart of Tag 0DZQ**, the two-chart affine cover. A separated scheme of finite
  type over `k` of dimension at most one is covered by two affine opens, the second containing a
  prescribed finite closed set and the first avoiding it.
* `Deformation.Examples.isLocalCompleteIntersection_sections_of_syntomic`: the sections of a
  local complete intersection over `k` on an affine open form a local complete intersection
  `k`-algebra. This is the affine-local reading of hypothesis (2).
* `Deformation.Examples.isSmooth_baseProjection_schemeDeformationCategoryProjection`:
  **Stacks Tag 0DZQ**, given the carried hypotheses listed below.

## Implementation notes

### The two-chart cover

`exists_affineOpen_cover_avoiding_of_topologicalKrullDim_le_one` is the first paragraph of the
source's proof and is proved here outright, modulo the single hypothesis `h09NZ` that Tag 0A25
already carries in this repository. The ample invertible module comes from `h09NZ` through
`Stacks.HQuasiProjectiveDimensionOne`'s two reductions (`X` is Noetherian and separated as a
scheme), part (3) of Tag 01ZY puts a finite set inside an affine open — and, in its confined
form, inside an affine open contained in a prescribed open containing the set — and the passage
from "`U₂` contains every generic point" to "`X ∖ U₂` is finite" is
`Deformation.Examples.finite_of_isClosed_disjoint_genericPoints`, which is where the dimension
bound is used.

The prescribed finite set is assumed **closed**, which is how Tag 0DZQ uses it: there the set is
the complement of the open smooth locus. Closedness is what makes the complement an open to
confine `U₁` to, and the conclusion `Disjoint E U₁` would otherwise be false in general, a point
of `X ∖ U₂` being allowed to lie in the closure of `E`.

### The hypotheses that are carried rather than discharged

Tag 0DZQ is assembled from Tags 0DZN, 0DYX, 0DZH and 0A25, three of which are themselves
conditional in this repository. The scheme-level hypotheses (1), (2) and (3) of the source are
all present in the statement; the carried hypotheses are, in full:

* `h09NZ : Stacks.HQuasiProjectiveDimensionOne.AmpleOfNoetherianSeparatedDimLEOne` — Tag 09NZ,
  the existence of an ample invertible sheaf on a Noetherian separated scheme of dimension at
  most one. This is what Tag 0A25 carries, and it is used only through the two-chart cover.
* `hΛ : Deformation.IsDeformationCategory (𝟭 _)` — the Rim–Schlessinger condition for `𝒞_Λ` over
  itself, carried by Tag 0DZN and by `Deformation.isDeformationCategory_cofiberedProduct`.
* `h0DYZ : Deformation.Examples.GluingComparisonSmooth Λ k` — **Tag 0DYZ**, in the form Tag 0DZN
  consumes it: for every gluing situation there are restriction morphisms
  `Def_{P_i} ⟶ Def_{P₁₂}` and a *smooth* comparison morphism from `Def_X` into the `2`-fibre
  product `Def_{P₁} ×_{Def_{P₁₂}} Def_{P₂}`. Tag 0DYZ asserts that the comparison is an
  equivalence and is not available here; Tag 0DZN carries the same data, pointwise in one gluing
  situation, as its `p₁`, `p₂`, `comparison` and `hcomparison` arguments. The quantified form is
  needed because the gluing situation of Tag 0DZQ is produced inside the proof, by the two-chart
  cover, so its coordinate rings cannot be named in the statement. Tag 0DYX — the identification
  `Def_{U_i} = Def_{P_i}`, which is unconditional in this repository — is already absorbed into
  this hypothesis, exactly as in Tag 0DZN, which is why no affineness of thickenings appears
  below.
* `hsmooth : Deformation.Examples.SmoothSectionsOfSmoothAffineOpen k` — the affine-local reading
  of smoothness over a field: on an affine open on which the structure morphism is smooth, the
  sections form a smooth `k`-algebra. Tag 0DZN asks for `Algebra.Smooth k S.P₁₂` and the
  two-chart cover delivers smoothness of `U₁₂ ⟶ Spec k`; no affine-local characterization of
  `AlgebraicGeometry.Smooth` is available in this repository, so the translation between the two
  is carried. The corresponding reading of hypothesis (2) is **not** carried: it is
  `Deformation.Examples.isLocalCompleteIntersection_sections_of_syntomic`, proved below from the
  affine-pair characterization `AlgebraicGeometry.syntomic_tfae` of Tag 01UD.

### The coordinate rings

They are the sections themselves, `Γ(X, U_i)`, with the `k`-algebra structure
`Deformation.Examples.sectionsAlgebra` given by the structure morphism; the presentations
`affine_i` of Situation 0DYY are then `AlgebraicGeometry.IsAffineOpen.isoSpec` read in
`Over (Spec k)`, which is `Deformation.Examples.gluingSituationOfAffineCover`. No separate choice
of presentation is made, and the `k`-algebra structure on `Γ(X, U)` is the same one that
`AlgebraicGeometry.localCompleteIntersection_tfae` uses.

## References

* [Stacks Project, Tag 0DZQ](https://stacks.math.columbia.edu/tag/0DZQ)
* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 0DYY](https://stacks.math.columbia.edu/tag/0DYY)
* [Stacks Project, Tag 0DYZ](https://stacks.math.columbia.edu/tag/0DYZ)
* [Stacks Project, Tag 0DYX](https://stacks.math.columbia.edu/tag/0DYX)
* [Stacks Project, Tag 0DZN](https://stacks.math.columbia.edu/tag/0DZN)
* [Stacks Project, Tag 0DZH](https://stacks.math.columbia.edu/tag/0DZH)
* [Stacks Project, Tag 0A25](https://stacks.math.columbia.edu/tag/0A25)
* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)
* [Stacks Project, Tag 01UD](https://stacks.math.columbia.edu/tag/01UD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Deformation.Examples

/-! ### A closed subset meeting no component generically is finite -/

/-- In a `T0` space of topological Krull dimension at most one there is no chain of two strict
specializations: the middle term of such a chain is neither minimal nor maximal among the
irreducible closed subsets. -/
private theorem not_specializes_chain_of_topologicalKrullDim_le_one {Y : Type*}
    [TopologicalSpace Y] [T0Space Y] (hdim : topologicalKrullDim Y ≤ 1) {x y z : Y}
    (hxy : x ⤳ y) (hyz : y ⤳ z) (hxy' : x ≠ y) (hyz' : y ≠ z) : False := by
  let cl (a : Y) : IrreducibleCloseds Y :=
    ⟨closure ({a} : Set Y), isIrreducible_singleton.closure, isClosed_closure⟩
  have key : ∀ {a b : Y}, a ⤳ b → a ≠ b → cl b < cl a := fun hab hne =>
    lt_of_le_of_ne (specializes_iff_closure_subset.mp hab) fun heq =>
      hne (hab.antisymm (specializes_iff_closure_subset.mpr heq.ge)).eq
  have hdim' : Order.krullDim (IrreducibleCloseds Y) ≤ 1 := hdim
  rcases Order.krullDim_le_one_iff.mp hdim' (cl y) with hmin | hmax
  · exact hmin.not_lt (key hyz hyz')
  · exact hmax.not_lt (key hxy hxy')

/-- **A closed subset of a Noetherian scheme of dimension at most one containing no generic point
of an irreducible component is finite.**

Write the closed set as a finite union of irreducible closed subsets. Each piece `t` has a generic
point `η`, which is not a generic point of a component of the ambient scheme, so the generic point
`ξ` of some component containing `η` specializes strictly to `η`; a further strict specialization
`η ⤳ x` with `x ∈ t` would then be a chain of length two, which the dimension bound forbids.
Hence `t = {η}`, and a finite union of singletons is finite. -/
theorem finite_of_isClosed_disjoint_genericPoints {Y : Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian Y] (hdim : topologicalKrullDim (Y : Type u) ≤ 1) {C : Set Y}
    (hC : IsClosed C) (havoid : Disjoint C (genericPoints (Y : Type u))) : C.Finite := by
  classical
  obtain ⟨S, hSfin, hSclosed, hSirr, hS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hC
  have hEach : ∀ t ∈ S, t.Finite := by
    intro t ht
    obtain ⟨η, hηt⟩ : ∃ η, IsGenericPoint η t :=
      ⟨_, (hSirr t ht).isGenericPoint_genericPoint (hSclosed t ht)⟩
    have hηC : η ∈ C := hS ▸ Set.mem_sUnion.mpr ⟨t, ht, hηt.mem⟩
    have hηNotGen : η ∉ genericPoints (Y : Type u) := fun h =>
      Set.disjoint_left.mp havoid hηC h
    obtain ⟨Z, hZ, hηZ⟩ := Set.mem_sUnion.mp
      (show η ∈ ⋃₀ irreducibleComponents (Y : Type u) by
        rw [sUnion_irreducibleComponents]; exact Set.mem_univ η)
    have hξη : (genericPoints.ofComponent (α := (Y : Type u)) ⟨Z, hZ⟩).1 ⤳ η :=
      (genericPoints.isGenericPoint_ofComponent (α := (Y : Type u)) ⟨Z, hZ⟩).specializes hηZ
    have hξηne : (genericPoints.ofComponent (α := (Y : Type u)) ⟨Z, hZ⟩).1 ≠ η := fun heq =>
      hηNotGen (heq ▸ (genericPoints.ofComponent (α := (Y : Type u)) ⟨Z, hZ⟩).2)
    have htEq : t = {η} :=
      Set.Subset.antisymm
        (fun x hx => Set.mem_singleton_iff.mpr (by
          by_contra hne
          exact not_specializes_chain_of_topologicalKrullDim_le_one hdim hξη
            (hηt.specializes hx) hξηne (Ne.symm hne)))
        (Set.singleton_subset_iff.mpr hηt.mem)
    rw [htEq]
    exact Set.finite_singleton η
  rw [hS]
  simpa only [← Set.sUnion_eq_biUnion] using hSfin.biUnion hEach

/-! ### The two-chart affine cover -/

/-- **The geometric heart of [Stacks, Tag 0DZQ]: the two-chart affine cover.**

Let `X` be a separated scheme of finite type over a field `k` with `dim(X) ≤ 1`, and let `E` be a
finite closed subset of `X` — in the application, the non-smooth locus of `X ⟶ Spec k`. Then `X`
is covered by two affine opens `U₁`, `U₂` with `E ⊆ U₂` and `U₁` disjoint from `E`.

By [Stacks, Tag 0A25] — whose only missing input, [Stacks, Tag 09NZ], is the hypothesis
`h09NZ` — the scheme `X` carries an ample invertible module, so part (3) of [Stacks, Tag 01ZY]
puts any finite set of points inside an affine open contained in a prescribed open containing the
set. Applying it to `E` together with the finitely many generic points of the irreducible
components of `X` gives `U₂`; the complement of `U₂` is then a closed set containing no component
generic point, hence finite by
`Deformation.Examples.finite_of_isClosed_disjoint_genericPoints`, and a second application inside
the open `Eᶜ` gives `U₁`.

See the module documentation for why `E` is assumed closed. -/
theorem exists_affineOpen_cover_avoiding_of_topologicalKrullDim_le_one
    (h09NZ : Stacks.HQuasiProjectiveDimensionOne.AmpleOfNoetherianSeparatedDimLEOne.{u})
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (hdim : topologicalKrullDim (X : Type u) ≤ 1)
    {E : Set X} (hEfin : E.Finite) (hEclosed : IsClosed E) :
    ∃ U₁ U₂ : X.Opens, IsAffineOpen U₁ ∧ IsAffineOpen U₂ ∧ U₁ ⊔ U₂ = ⊤ ∧
      E ⊆ (U₂ : Set X) ∧ Disjoint E (U₁ : Set X) := by
  classical
  have : AlgebraicGeometry.IsNoetherian X :=
    Stacks.HQuasiProjectiveDimensionOne.isNoetherian_of_finiteType_over_field f
  have : X.IsSeparated :=
    Stacks.HQuasiProjectiveDimensionOne.isSeparated_of_isSeparated_over_field f
  obtain ⟨L, hLinv, hLamp⟩ := h09NZ X hdim
  have := hLinv
  have hL : Stacks.Ample.IsAmple X L :=
    (Stacks.AmpleBridge.isAmple_iff_isAmple X L).mpr hLamp
  have hgen : (genericPoints (X : Type u)).Finite :=
    genericPoints.finite TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  obtain ⟨U₂, hU₂, hEU₂⟩ :=
    Stacks.AmpleAffineAvoidance.exists_affineOpen_containing_finite_of_ample L hL
      (hEfin.union hgen)
  have hEU₂' : E ⊆ (U₂ : Set X) := fun x hx => hEU₂ (Set.mem_union_left _ hx)
  have hCfin : ((U₂ : Set X)ᶜ).Finite :=
    finite_of_isClosed_disjoint_genericPoints hdim U₂.2.isClosed_compl
      (Set.disjoint_left.mpr fun x hx hgx => hx (hEU₂ (Set.mem_union_right _ hgx)))
  obtain ⟨U₁, hU₁, hCU₁, hU₁E⟩ :=
    Stacks.AmpleAffineAvoidance.exists_affineOpen_containing_finite_le_of_ample L hL hCfin
      ⟨Eᶜ, hEclosed.isOpen_compl⟩ fun x hx hxE => hx (hEU₂' hxE)
  refine ⟨U₁, U₂, hU₁, hU₂, le_antisymm le_top fun x _ => ?_, hEU₂',
    Set.disjoint_right.mpr fun x hx => hU₁E hx⟩
  by_cases hx₂ : x ∈ U₂
  · exact Or.inr hx₂
  · exact Or.inl (hCU₁ hx₂)

/-! ### The coordinate ring of a chart -/

/-- The `k`-algebra structure on the sections of a scheme `X` over `Spec k` on an open `U`: the
canonical identification of `k` with `Γ(Spec k, ⊤)` followed by the restriction of the structure
morphism. This is the `k`-algebra structure used by
`AlgebraicGeometry.localCompleteIntersection_tfae`. -/
@[instance_reducible]
def sectionsAlgebra {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) : Algebra k Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom.toAlgebra

/-- The presentation of an affine open of a scheme over `Spec k` as the spectrum of its
coordinate ring, *over* `Spec k`: the isomorphism `U ≅ Spec Γ(X, U)` of
`AlgebraicGeometry.IsAffineOpen.isoSpec` commutes with the structure morphisms. -/
theorem isoSpec_hom_comp_specMap_algebraMap {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) {U : X.Opens} (hU : IsAffineOpen U) :
    letI := sectionsAlgebra f U
    hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U))) = U.ι ≫ f := by
  let : Algebra k Γ(X, U) := sectionsAlgebra f U
  rw [hU.isoSpec_hom]
  have hmap : CommRingCat.ofHom (algebraMap k Γ(X, U)) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ U (by simp) := rfl
  rw [hmap, Spec.map_comp]
  show U.toSpecΓ ≫ Spec.map (f.appLE ⊤ U (by simp)) ≫
    Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv = U.ι ≫ f
  rw [← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_appLE f ⊤ U (by simp)]
  simp only [Category.assoc, Scheme.Opens.toSpecΓ_top, toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]
  exact Scheme.Hom.resLE_comp_ι (f := f) (U := ⊤) (V := U) (e := by simp)

/-! ### Situation 0DYY from a two-element affine cover -/

/-- **Situation 0DYY from a cover by two affine opens.** A scheme `X` over `k` covered by two
affine opens with affine intersection is a gluing situation, with the sections `Γ(X, U_i)` as the
coordinate rings and `AlgebraicGeometry.IsAffineOpen.isoSpec` as the presentations. -/
def gluingSituationOfAffineCover {k : Type u} [Field k] (Λ : Type u) [CommRing Λ] [Algebra Λ k]
    (X : Over (Spec (CommRingCat.of k))) {U₁ U₂ : X.left.Opens} (hU₁ : IsAffineOpen U₁)
    (hU₂ : IsAffineOpen U₂) (hU₁₂ : IsAffineOpen (U₁ ⊓ U₂)) (hcover : U₁ ⊔ U₂ = ⊤) :
    GluingSituation Λ k :=
  letI := sectionsAlgebra X.hom U₁
  letI := sectionsAlgebra X.hom U₂
  letI := sectionsAlgebra X.hom (U₁ ⊓ U₂)
  { X := X
    U₁ := U₁
    U₂ := U₂
    cover := hcover
    P₁ := Γ(X.left, U₁)
    P₂ := Γ(X.left, U₂)
    P₁₂ := Γ(X.left, U₁ ⊓ U₂)
    affine₁ := Over.isoMk hU₁.isoSpec (isoSpec_hom_comp_specMap_algebraMap X.hom hU₁)
    affine₂ := Over.isoMk hU₂.isoSpec (isoSpec_hom_comp_specMap_algebraMap X.hom hU₂)
    affine₁₂ := Over.isoMk hU₁₂.isoSpec (isoSpec_hom_comp_specMap_algebraMap X.hom hU₁₂) }

/-! ### The affine-local readings of the hypotheses on `X` -/

/-- **Hypothesis (2) of Tag 0DZQ read on a chart.** For a scheme which is a local complete
intersection over `k`, the sections on an affine open form a local complete intersection
`k`-algebra.

This is the affine-pair characterization of syntomicity, [Stacks, Tag 01UD]
(`AlgebraicGeometry.syntomic_tfae`), applied to the affine open `U` of the source and `⊤` of
`Spec k`, followed by the comparison of `k` with `Γ(Spec k, ⊤)`: being syntomic over a field and
being a local complete intersection over it agree, and the two base fields are identified by the
bijective map `k ⟶ Γ(Spec k, ⊤)`. -/
theorem isLocalCompleteIntersection_sections_of_syntomic {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (hf : IsLocalCompleteIntersectionOverField f)
    {U : X.Opens} (hU : IsAffineOpen U) :
    letI := sectionsAlgebra f U
    IsLocalCompleteIntersection k Γ(X, U) := by
  let K : Type u := Γ(Spec (CommRingCat.of k), ⊤)
  let A : Type u := Γ(X, U)
  let : Algebra K A := (f.appLE ⊤ U (by simp)).hom.toAlgebra
  let : Algebra k A := sectionsAlgebra f U
  have hpairs := ((syntomic_tfae f).out 1 2).mp hf
  have hsyn : Algebra.Syntomic K A := hpairs U hU ⊤ (isAffineOpen_top _) (by simp)
  -- Compare `k` with the global sections of `Spec k`.
  have hKfield : IsField K :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)
  let : Field K := hKfield.toField
  let : Algebra k K := (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toAlgebra
  have : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hbij : Function.Bijective (algebraMap k K) :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv
  have : Module.FaithfullyFlat k K :=
    (RingHom.faithfullyFlat_algebraMap_iff (R := k) (S := K)).mp
      (RingHom.FaithfullyFlat.of_bijective hbij)
  have : Algebra.IsPushout k K A A :=
    (Algebra.IsPushout.of_bijective_left (T := A) (A := K) hbij).symm
  have hsyn' : Algebra.Syntomic k A := (Algebra.IsPushout.syntomic_iff k K A A).mp hsyn
  -- Over a field, being syntomic and being a local complete intersection agree.
  have hfib := hsyn'.isLocalCompleteIntersection_fiber (⊥ : Ideal k)
  let : Algebra A ((⊥ : Ideal k).Fiber A) := Algebra.TensorProduct.rightAlgebra
  have : Algebra.IsPushout k (⊥ : Ideal k).ResidueField A ((⊥ : Ideal k).Fiber A) := inferInstance
  exact (Algebra.IsPushout.isLocalCompleteIntersection_iff k (⊥ : Ideal k).ResidueField A
    ((⊥ : Ideal k).Fiber A)).mp hfib

/-- **The affine-local reading of smoothness over a field, carried as a hypothesis.** On an
affine open `U` of a scheme `X` over `k` on which the structure morphism is smooth, the sections
`Γ(X, U)` form a smooth `k`-algebra.

This is the translation Tag 0DZN needs for its hypothesis on `P₁₂`. The repository has no
affine-local characterization of `AlgebraicGeometry.Smooth` over a field — the corresponding
statement for syntomicity is [Stacks, Tag 01UD], `AlgebraicGeometry.syntomic_tfae`, which is what
`Deformation.Examples.isLocalCompleteIntersection_sections_of_syntomic` uses — so this
translation is assumed. -/
def SmoothSectionsOfSmoothAffineOpen (k : Type u) [Field k] : Prop :=
  ∀ {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) {U : X.Opens}, IsAffineOpen U →
    Smooth (U.ι ≫ f) →
      letI := sectionsAlgebra f U
      Algebra.Smooth k Γ(X, U)

/-- **[Stacks, Tag 0DYZ] as a hypothesis, in the form Tag 0DZN consumes it.** For every gluing
situation of Tag 0DYY there are restriction morphisms `Def_{P_i} ⟶ Def_{P₁₂}` over `𝒞_Λ` and a
*smooth* comparison morphism from `Def_X` into the `2`-fibre product
`Def_{P₁} ×_{Def_{P₁₂}} Def_{P₂}`.

Tag 0DYZ asserts that the comparison morphism is an equivalence; smoothness is the only
consequence of it that the proof of Tag 0DZN uses, and neither is available in this repository.
Tag 0DZN carries exactly this data for a single gluing situation, as its arguments `p₁`, `p₂`,
`comparison` and `hcomparison`; the quantified form is what Tag 0DZQ needs, the gluing situation
there being produced inside the proof by the two-chart cover. The identification
`Def_{U_i} = Def_{P_i}` of Tag 0DYX is absorbed into the statement, as it is in Tag 0DZN. -/
def GluingComparisonSmooth (Λ k : Type u) [CommRing Λ] [Field k] [Algebra Λ k] : Prop :=
  ∀ S : GluingSituation Λ k,
    ∃ (p₁ : BasedFunctor (ringDeformationCategoryOver Λ k S.P₁)
        (ringDeformationCategoryOver Λ k S.P₁₂))
      (p₂ : BasedFunctor (ringDeformationCategoryOver Λ k S.P₂)
        (ringDeformationCategoryOver Λ k S.P₁₂))
      (comparison : BasedFunctor (schemeDeformationCategoryOver Λ k S.X)
        (twoFibreProductBasedCategory p₁ p₂)), IsSmooth comparison

/-! ### Tag 0DZQ -/

/-- An open subscheme of the smooth locus is smooth over the base. -/
private theorem smooth_ι_comp_of_le_smoothLocus {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] {U : X.Opens} (hU : U ≤ f.smoothLocus) :
    Smooth (U.ι ≫ f) := by
  refine Scheme.Hom.smoothLocus_eq_top_iff.mp ?_
  rw [← Scheme.Hom.preimage_smoothLocus_eq U.ι f]
  exact eq_top_iff.mpr fun x _ => hU x.2

/-- **[Stacks, Tag 0DZQ].** Let `X` be a scheme over a field `k` which is separated and of finite
type over `k`, of dimension at most one, a local complete intersection over `k`, and smooth over
`k` outside a finite set of points. Then the deformation category `Def_X` of Example 0DY7 is
unobstructed: its structure morphism over `𝒞_Λ` is smooth.

The proof is the source's. The two-chart cover is
`Deformation.Examples.exists_affineOpen_cover_avoiding_of_topologicalKrullDim_le_one`, applied to
the complement of the smooth locus; it produces affine opens `U₁`, `U₂` covering `X` with `U₁`
inside the smooth locus, hence with `U₁` and `U₁₂` smooth over `k`. Tag 0DZN, clause 2, then
makes `Def_X ⟶ Def_{P₂}` smooth, and Tag 0DZH makes `Def_{P₂} ⟶ 𝒞_Λ` smooth, `P₂ = Γ(X, U₂)`
being a local complete intersection over `k` by hypothesis (2); the composite is the structure
morphism of `Def_X` by `Deformation.comp_baseProjection`.

See the module documentation for a full account of the four carried hypotheses. -/
@[stacks 0DZQ "carrying four hypotheses this repository cannot discharge, and no others: \
h09NZ, the existence of an ample invertible sheaf on a Noetherian separated scheme of dimension \
at most one (Tag 09NZ), which is what Tag 0A25 carries; hΛ, the Rim–Schlessinger condition for \
𝒞_Λ over itself, which is what Tag 0DZN carries; h0DYZ, Tag 0DYZ in the form Tag 0DZN consumes \
it, namely the existence of restriction morphisms Def_{P_i} ⟶ Def_{P_12} and of a smooth \
comparison morphism Def_X ⟶ Def_{P_1} ×_{Def_{P_12}} Def_{P_2} for every gluing situation — \
this absorbs the identification Def_{U_i} = Def_{P_i} of Tag 0DYX, as Tag 0DZN does; and \
hsmooth, the affine-local reading of smoothness over a field, which translates smoothness of \
U_12 ⟶ Spec k into Algebra.Smooth k Γ(X, U_12) as Tag 0DZN asks. The three hypotheses (1), \
(2), (3) of the source are present in full, scheme-level form; the affine-local reading of (2) \
is proved here from Tag 01UD and is not carried"]
theorem isSmooth_baseProjection_schemeDeformationCategoryProjection {Λ k : Type u} [CommRing Λ]
    [Field k] [Algebra Λ k]
    (h09NZ : Stacks.HQuasiProjectiveDimensionOne.AmpleOfNoetherianSeparatedDimLEOne.{u})
    (hΛ : IsDeformationCategory.{u, u, u} (𝟭 (ArtinianLocalAlgCat.{u, u, u} Λ k)))
    (h0DYZ : GluingComparisonSmooth Λ k) (hsmooth : SmoothSectionsOfSmoothAffineOpen.{u} k)
    (X : Over (Spec (CommRingCat.of k))) [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (hdim : topologicalKrullDim (X.left : Type u) ≤ 1)
    (hlci : IsLocalCompleteIntersectionOverField X.hom)
    (hfinite : ((X.hom.smoothLocus : Set X.left)ᶜ).Finite) :
    IsSmooth (baseProjection (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X)) := by
  classical
  -- The two-chart cover, around the non-smooth locus.
  obtain ⟨U₁, U₂, hU₁, hU₂, hcover, -, hdisj⟩ :=
    exists_affineOpen_cover_avoiding_of_topologicalKrullDim_le_one h09NZ X.hom hdim hfinite
      X.hom.smoothLocus.2.isClosed_compl
  have hU₁sm : U₁ ≤ X.hom.smoothLocus := fun x hx =>
    not_not.mp (Set.disjoint_right.mp hdisj hx)
  -- The intersection of two affine opens of a separated scheme is affine.
  have : X.left.IsSeparated :=
    Stacks.HQuasiProjectiveDimensionOne.isSeparated_of_isSeparated_over_field X.hom
  have : IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X.left)) := inferInstance
  have hU₁₂ : IsAffineOpen (U₁ ⊓ U₂) := hU₁.inf hU₂
  -- The gluing situation of Situation 0DYY.
  let S := gluingSituationOfAffineCover Λ X hU₁ hU₂ hU₁₂ hcover
  obtain ⟨p₁, p₂, comparison, hcomparison⟩ := h0DYZ S
  have hP₁₂ : Algebra.Smooth k S.P₁₂ :=
    hsmooth X.hom hU₁₂ (smooth_ι_comp_of_le_smoothLocus X.hom (inf_le_left.trans hU₁sm))
  have hP₁ : IsLocalCompleteIntersection k S.P₁ :=
    isLocalCompleteIntersection_sections_of_syntomic X.hom hlci hU₁
  have hP₂ : IsLocalCompleteIntersection k S.P₂ :=
    isLocalCompleteIntersection_sections_of_syntomic X.hom hlci hU₂
  -- Tag 0DZN, clause 2, followed by Tag 0DZH.
  have hcomp := isSmooth_comp
    (BasedFunctor.comp (GluingSituation.toChartProduct S p₁ p₂ comparison)
      (cofiberedProductSnd (ringDeformationCategoryOver Λ k S.P₁)
        (ringDeformationCategoryOver Λ k S.P₂)))
    (baseProjection (ringDeformationCategoryOver Λ k S.P₂).p)
    (GluingSituation.isSmooth_toChartProduct_comp_snd S p₁ p₂ comparison hΛ hP₁₂ hcomparison hP₁)
    (ringDeformationCategory_isSmooth_of_isLocalCompleteIntersection hP₂)
  rw [Deformation.comp_baseProjection] at hcomp
  exact hcomp

end Deformation.Examples

end
