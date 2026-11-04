module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.RingTheory.Nagata.Japanese
public import StacksFrontier.RingTheory.Length.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# The one-dimensional components of a scheme of dimension at most one

Let `X` be a scheme whose topological Krull dimension is at most one. Stacks Tag 0AYW expresses
the degree of a finite locally free sheaf on `X` as the multiplicity-weighted sum of its degrees
on the one-dimensional irreducible components of `X`, taken with their reduced induced scheme
structure. This file builds the geometry that statement rests on: the components themselves,
their multiplicities, and the facts that make each component a proper curve over the base.

Components are indexed by their generic points, i.e. by the set `genericPointsOne X` of points
whose closure is an irreducible component of dimension exactly one.

## Main definitions

* `Stacks.AlgebraicGeometry.ComponentDegrees.genericPointsOne`: the generic points of the
  one-dimensional irreducible components of a scheme.
* `Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponent` and `reducedComponentι`: the
  reduced induced closed subscheme on the closure of such a generic point, and its closed
  immersion into `X`.
* `Stacks.AlgebraicGeometry.ComponentDegrees.componentMultiplicity`: the multiplicity of a
  component, namely the length of the local ring of `X` at its generic point.

## Main results

* `isIntegral_reducedComponent`, `reducedComponentι_genericPoint` and
  `topologicalKrullDim_reducedComponent`: a reduced component is an integral scheme of
  dimension exactly one whose generic point maps to the chosen generic point of `X`.
* `isProper_reducedComponentι_comp` and `topologicalKrullDim_reducedComponent_le`: for a proper
  morphism `f : X ⟶ Spec k`, the composite `reducedComponentι X ξ ≫ f` is proper, and the
  component still has dimension at most one. These are exactly the first two data obligations
  carried by the conclusion of Tag 0AYW.
* `isNoetherian_of_isProper_over_field` and `finite_genericPointsOne`: a scheme proper over a
  field is Noetherian, hence has only finitely many one-dimensional components, which is what
  makes the sum of Tag 0AYW finite.
* `length_stalk_ne_top` and `componentMultiplicity_cast`: the local ring at a generic point of a
  scheme proper over a field is Artinian, so the multiplicity is a genuine natural number and
  its cast back to `ℕ∞` is the length.
* `exists_isIso_hom_to_reducedComponent`: an integral closed subscheme of `X` whose generic
  point is `ξ` is canonically isomorphic, over `X`, to `reducedComponent X ξ`. This is how the
  layers produced by dévissage are recognized as the components of `X`.
* `genericPoint_mem_genericPointsOne`, `genericPoint_eq_of_mem_range` and
  `topologicalKrullDim_le_zero_or_eq_one`: the dichotomy used to split the layers of a
  filtration into those supported on a one-dimensional component and those of dimension zero.

## Implementation notes

`genericPointsOne`, `reducedComponent`, `reducedComponentι` and `componentMultiplicity` restate,
in library vocabulary, definitions introduced with the statements of Tags 0AYU and 0AYW; those
modules cannot be imported here, so the definitions are reproduced. They carry no Stacks attribute:
nothing of either tag's tagged content is proved in this file. The uniqueness half of Tag 01J3 is
`AlgebraicGeometry.Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme`, which this
file uses rather than restating.

`reducedComponent` and `reducedComponentι` are `abbrev`s, not `def`s, so that
`Scheme.IdealSheafData.subscheme` lemmas and the properness instance apply to them without a
bridging lemma.

The component formula of Tag 0AYW itself is **not** proved, here or in the companion files
`Rank` and `Degree`; no Stacks attribute for Tag 0AYW is attached anywhere. The formula reduces
to the Euler-characteristic theory of coherent sheaves on a proper scheme over a field, and the
library has that theory's vocabulary (`AlgebraicGeometry.cohomologyOverField`,
`AlgebraicGeometry.eulerCharacteristic`, `AlgebraicGeometry.curveDegree`) but none of its
theorems. Specifically, the argument of Tag 0AYW needs, and the library does not have: the
dévissage of a coherent sheaf on a Noetherian scheme into pushforwards of ideal sheaves on
integral closed subschemes (Tag 01YF); coherence of a finite locally free sheaf and of the
structure sheaf (Tag 01XZ); additivity of the Euler characteristic along a short exact sequence
(Tag 08AA); the Euler characteristic of a tensor product on a proper curve and on a
zero-dimensional support (Tags 0AYV and 0AYT); cohomology of a pushforward along a finite
morphism (Tag 089W); and the projection formula (Tags 01E8 and 0FZE). It also needs Tag 0AYU,
the invariance of the degree under a morphism inducing isomorphisms on the local rings at the
generic points of the one-dimensional components, which is the first reduction step of the
source proof.

## References

* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 0AYU](https://stacks.math.columbia.edu/tag/0AYU)
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.AlgebraicGeometry.ComponentDegrees

universe u

/-- Generic points of the one-dimensional irreducible components of a scheme. -/
def genericPointsOne (X : Scheme.{u}) : Set X :=
  {x | x ∈ genericPoints X ∧ topologicalKrullDim (closure ({x} : Set X)) = 1}

/-- Membership of `genericPointsOne`, spelled out. The body of `genericPointsOne` is not
exposed, so this is the only way a later module can use its defining property. -/
theorem mem_genericPointsOne_iff {X : Scheme.{u}} {x : X} :
    x ∈ genericPointsOne X ↔
      x ∈ genericPoints X ∧ topologicalKrullDim (closure ({x} : Set X)) = 1 :=
  Iff.rfl

/-- A one-dimensional irreducible component with its reduced induced scheme structure. -/
noncomputable abbrev reducedComponent (X : Scheme.{u}) (ξ : genericPointsOne X) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal
    ⟨closure ({ξ.1} : Set X), isClosed_closure⟩).subscheme

/-- The canonical closed immersion of a reduced one-dimensional component. -/
noncomputable abbrev reducedComponentι (X : Scheme.{u}) (ξ : genericPointsOne X) :
    reducedComponent X ξ ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal
    ⟨closure ({ξ.1} : Set X), isClosed_closure⟩).subschemeι

/-- The multiplicity of an irreducible component is the length of the local ring at its
generic point. -/
@[sga "4 XVIII 1.1.3"]
noncomputable abbrev componentMultiplicity (X : Scheme.{u}) (ξ : genericPointsOne X) : ℕ :=
  (Module.length (X.presheaf.stalk ξ.1) (X.presheaf.stalk ξ.1)).toNat

/-- A one-dimensional component with its reduced induced structure is an integral scheme. -/
theorem isIntegral_reducedComponent (X : Scheme.{u}) (ξ : genericPointsOne X) :
    IsIntegral (reducedComponent X ξ) := by
  let Z : Closeds X := ⟨closure ({ξ.1} : Set X), isClosed_closure⟩
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal Z
  have hsupport : (I.support : Set X) = closure ({ξ.1} : Set X) := rfl
  have : IsReduced I.subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal Z
  have : IrreducibleSpace I.subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme X I (by
      rw [I.range_subschemeι, hsupport]
      exact (genericPoints.component ⟨ξ.1, ξ.2.1⟩).2.1)
  exact isIntegral_of_irreducibleSpace_of_isReduced I.subscheme

/-- The generic point of a reduced component maps to the generic point indexing it. -/
theorem reducedComponentι_genericPoint (X : Scheme.{u}) (ξ : genericPointsOne X) :
    (letI : IsIntegral (reducedComponent X ξ) := isIntegral_reducedComponent X ξ
     reducedComponentι X ξ (genericPoint (reducedComponent X ξ)) = ξ.1) := by
  let Z : Closeds X := ⟨closure ({ξ.1} : Set X), isClosed_closure⟩
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal Z
  have : IsIntegral I.subscheme := isIntegral_reducedComponent X ξ
  have hsupport : (I.support : Set X) = closure ({ξ.1} : Set X) := rfl
  have hclosure : closure ({I.subschemeι (genericPoint I.subscheme)} : Set X) =
      closure ({ξ.1} : Set X) := by
    rw [← Set.image_singleton, I.subschemeι.isClosedEmbedding.closure_image_eq,
      genericPoint_closure, Set.image_univ, I.range_subschemeι, hsupport]
  show I.subschemeι (genericPoint I.subscheme) = ξ.1
  exact isGenericPoint_closure.eq (hclosure ▸ isGenericPoint_closure)

/-- A reduced one-dimensional component has dimension exactly one. -/
theorem topologicalKrullDim_reducedComponent (X : Scheme.{u}) (ξ : genericPointsOne X) :
    topologicalKrullDim (reducedComponent X ξ) = 1 := by
  let Z : Closeds X := ⟨closure ({ξ.1} : Set X), isClosed_closure⟩
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal Z
  have hsupport : (I.support : Set X) = closure ({ξ.1} : Set X) := rfl
  calc
    topologicalKrullDim I.subscheme = topologicalKrullDim (Set.range I.subschemeι.base) :=
      IsHomeomorph.topologicalKrullDim_eq _
        (IsPreimmersion.isEmbedding I.subschemeι).toHomeomorph.isHomeomorph
    _ = topologicalKrullDim (closure ({ξ.1} : Set X)) :=
      IsHomeomorph.topologicalKrullDim_eq _
        (Homeomorph.setCongr (by rw [I.range_subschemeι, hsupport])).isHomeomorph
    _ = 1 := ξ.2.2

/-- A reduced component of a scheme of dimension at most one again has dimension at most one.
This is the second data obligation carried by the conclusion of Stacks Tag 0AYW. -/
theorem topologicalKrullDim_reducedComponent_le (X : Scheme.{u})
    (hX : topologicalKrullDim X ≤ 1) (ξ : genericPointsOne X) :
    topologicalKrullDim (reducedComponent X ξ) ≤ 1 :=
  (reducedComponentι X ξ).isClosedEmbedding.isEmbedding.isInducing.topologicalKrullDim_le.trans hX

/-- A reduced component of a scheme proper over a field is itself proper over that field.
This is the first data obligation carried by the conclusion of Stacks Tag 0AYW. -/
theorem isProper_reducedComponentι_comp (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (ξ : genericPointsOne X) :
    IsProper (reducedComponentι X ξ ≫ f) := by
  dsimp [reducedComponentι]
  infer_instance

/-- The support of the kernel ideal sheaf of a closed immersion with integral source is the
closure of the image of the generic point. -/
theorem support_ker_eq_closure_genericPoint {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] :
    i.ker.support = closure ({i (genericPoint Z)} : Set X) := by
  rw [Scheme.Hom.support_ker]
  calc
    closure (Set.range i.base) = Set.range i.base :=
      i.isClosedEmbedding.isClosed_range.closure_eq
    _ = i.base '' Set.univ := Set.image_univ.symm
    _ = i.base '' closure ({genericPoint Z} : Set Z) := by
      rw [genericPoint_closure, Set.image_univ]
    _ = closure (i.base '' ({genericPoint Z} : Set Z)) :=
      (i.isClosedEmbedding.closure_image_eq _).symm
    _ = closure ({i (genericPoint Z)} : Set X) := by
      congr 1
      ext x
      simp

/-- The image of a closed immersion with integral source is the closure of the image of the
generic point. -/
theorem range_eq_closure_genericPoint {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] :
    Set.range i.base = closure ({i (genericPoint Z)} : Set X) := by
  rw [← support_ker_eq_closure_genericPoint i, Scheme.Hom.support_ker]
  exact i.isClosedEmbedding.isClosed_range.closure_eq.symm

/-- A scheme proper over a field is Noetherian. -/
theorem isNoetherian_of_isProper_over_field (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] : IsNoetherian X := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact (isNoetherian_iff X).2 ⟨inferInstance, inferInstance⟩

/-- A Noetherian scheme has only finitely many one-dimensional components. -/
theorem finite_genericPointsOne (X : Scheme.{u}) [IsNoetherian X] :
    (genericPointsOne X).Finite :=
  (genericPoints.finite finite_irreducibleComponents_of_isNoetherian).subset fun _ hx => hx.1

/-- A generic point of a scheme is maximal for the specialization order. -/
theorem isMax_of_mem_genericPoints {X : Scheme.{u}} (x : X) (hx : x ∈ genericPoints X) :
    IsMax x := by
  change closure ({x} : Set X) ∈ irreducibleComponents X at hx
  intro y hxy
  have hxY : x ∈ closure ({y} : Set X) :=
    specializes_iff_mem_closure.mp (Scheme.le_iff_specializes.mp hxy)
  have hsubset : closure ({x} : Set X) ⊆ closure ({y} : Set X) :=
    (closure_mono (Set.singleton_subset_iff.mpr hxY)).trans_eq closure_closure
  have hEqClosure : closure ({x} : Set X) = closure ({y} : Set X) :=
    hsubset.antisymm (hx.2 isIrreducible_singleton.closure hsubset)
  rw [Scheme.le_iff_specializes, specializes_iff_mem_closure, hEqClosure]
  exact subset_closure (Set.mem_singleton y)

/-- On a scheme proper over a field, the local ring at a generic point has finite length: it is
Noetherian of Krull dimension zero, hence Artinian. -/
theorem length_stalk_ne_top (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (ξ : genericPointsOne X) :
    Module.length (X.presheaf.stalk ξ.1) (X.presheaf.stalk ξ.1) ≠ ⊤ := by
  have : IsNoetherian X := isNoetherian_of_isProper_over_field k f
  let R := X.presheaf.stalk ξ.1
  have hdim : ringKrullDim R = 0 := by
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight]
    have hcoheight : Order.coheight ξ.1 = 0 :=
      Order.coheight_eq_zero.mpr (isMax_of_mem_genericPoints ξ.1 ξ.2.1)
    simpa only [WithBot.coe_zero] using congrArg (fun d : ℕ∞ => (d : WithBot ℕ∞)) hcoheight
  have : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr (by rw [hdim]; exact le_rfl)
  have : IsArtinianRing R := isArtinianRing_iff_krullDimLE_zero.mpr inferInstance
  exact Module.length_ne_top_iff.mpr ((isArtinianRing_iff_isFiniteLength R).mp inferInstance)

/-- The multiplicity of a component, cast back to `ℕ∞`, is the length of the local ring at its
generic point. -/
theorem componentMultiplicity_cast (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (ξ : genericPointsOne X) :
    (componentMultiplicity X ξ : ℕ∞) =
      Module.length (X.presheaf.stalk ξ.1) (X.presheaf.stalk ξ.1) :=
  ENat.natCast_toNat (length_stalk_ne_top k f ξ)

/-- An integral closed subscheme of `X` whose generic point is `ξ` is isomorphic over `X` to the
reduced component indexed by `ξ`. -/
theorem exists_isIso_hom_to_reducedComponent {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] (ξ : genericPointsOne X)
    (hξ : i (genericPoint Z) = ξ.1) :
    ∃ ψ : Z ⟶ reducedComponent X ξ, IsIso ψ ∧ ψ ≫ reducedComponentι X ξ = i := by
  let ι := reducedComponentι X ξ
  let V : Closeds X := ⟨closure ({ξ.1} : Set X), isClosed_closure⟩
  let J : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal V
  have hsupport : i.ker.support = V := by
    apply SetLike.coe_injective
    show (i.ker.support : Set X) = closure ({ξ.1} : Set X)
    rw [support_ker_eq_closure_genericPoint, hξ]
  have : IsReduced i.ker.subscheme :=
    ObjectProperty.IsClosedUnderIsomorphisms.of_iso (asIso i.toImage)
      (inferInstance : IsReduced Z)
  have hker : i.ker = J :=
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme i.ker V hsupport
  have hkerJ : ι.ker = J := by
    show (Scheme.IdealSheafData.vanishingIdeal V).subschemeι.ker = J
    rw [Scheme.IdealSheafData.ker_subschemeι]
  let ψ : Z ⟶ reducedComponent X ξ := IsClosedImmersion.lift ι i (by rw [hkerJ, hker])
  have hfac : ψ ≫ ι = i := IsClosedImmersion.lift_fac _ _ _
  exact ⟨ψ, IsClosedImmersion.isIso_of_ker_eq i ι ψ hfac (hker.trans hkerJ.symm), hfac⟩

/-- In a space of dimension at most one, the closure of a point that has dimension one is an
irreducible component. -/
private theorem closure_singleton_mem_irreducibleComponents_of_topologicalKrullDim {X : Type*}
    [TopologicalSpace X] (hX : topologicalKrullDim X ≤ 1) (x : X)
    (hx : topologicalKrullDim (closure ({x} : Set X)) = 1) :
    closure ({x} : Set X) ∈ irreducibleComponents X := by
  let C : IrreducibleCloseds X :=
    ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩
  have hX' : Order.krullDim (IrreducibleCloseds X) ≤ 1 := hX
  have hnotMin : ¬ IsMin C := by
    intro hmin
    have hchain : 1 ≤ Order.krullDim (IrreducibleCloseds (closure ({x} : Set X))) := hx.ge
    obtain ⟨A, B, hAB⟩ := Order.one_le_krullDim_iff.mp hchain
    let m := IrreducibleCloseds.map (Subtype.val : closure ({x} : Set X) → X)
      continuous_subtype_val
    have hm : StrictMono m :=
      IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal
    have hB : m B ≤ C := by
      apply SetLike.coe_subset_coe.mp
      show closure ((Subtype.val : closure ({x} : Set X) → X) '' B) ⊆ closure {x}
      exact (closure_mono (by
        rintro y ⟨z, hz, rfl⟩
        exact z.2)).trans_eq closure_closure
    exact hmin.not_lt ((hm hAB).trans_le hB)
  have hmax : IsMax C := ((Order.krullDim_le_one_iff.mp hX') C).resolve_left hnotMin
  rw [irreducibleComponents_eq_maximals_closed]
  refine ⟨⟨isClosed_closure, isIrreducible_singleton.closure⟩, ?_⟩
  intro Y hY hCY
  let D : IrreducibleCloseds X := ⟨Y, hY.2, hY.1⟩
  have hDC : D ≤ C := hmax hCY
  have heq : Y = closure ({x} : Set X) := by
    simpa [D, C] using
      congrArg (fun W : IrreducibleCloseds X => (W : Set X)) (le_antisymm hDC hCY)
  rw [heq]

/-- If `Z` is an integral closed subscheme of dimension one of a scheme of dimension at most
one, then the image of its generic point indexes a one-dimensional component. -/
theorem genericPoint_mem_genericPointsOne {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] (hX : topologicalKrullDim X ≤ 1)
    (hZ : topologicalKrullDim Z = 1) : i (genericPoint Z) ∈ genericPointsOne X := by
  have hdimClosure : topologicalKrullDim (closure ({i (genericPoint Z)} : Set X)) = 1 :=
    calc
      _ = topologicalKrullDim (Set.range i.base) := IsHomeomorph.topologicalKrullDim_eq _
          (Homeomorph.setCongr (range_eq_closure_genericPoint i).symm).isHomeomorph
      _ = topologicalKrullDim Z := (IsHomeomorph.topologicalKrullDim_eq _
          i.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm
      _ = 1 := hZ
  exact mem_genericPointsOne_iff.mpr
    ⟨closure_singleton_mem_irreducibleComponents_of_topologicalKrullDim hX _ hdimClosure,
      hdimClosure⟩

/-- A generic point of `X` lying in the image of a closed immersion with integral source is the
image of the generic point of that source. -/
theorem genericPoint_eq_of_mem_range {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegral Z] (x : X) (hx : x ∈ genericPoints X) (hxi : x ∈ Set.range i.base) :
    i (genericPoint Z) = x := by
  have hr := range_eq_closure_genericPoint i
  change closure ({x} : Set X) ∈ irreducibleComponents X at hx
  have hsub : closure ({x} : Set X) ⊆ closure ({i (genericPoint Z)} : Set X) :=
    closure_minimal (Set.singleton_subset_iff.mpr (hr ▸ hxi)) isClosed_closure
  have he : closure ({i (genericPoint Z)} : Set X) = closure ({x} : Set X) :=
    Set.Subset.antisymm (hx.2 isIrreducible_singleton.closure hsub) hsub
  exact isGenericPoint_closure.eq (he ▸ isGenericPoint_closure)

/-- A closed subscheme of a scheme of dimension at most one has dimension either at most zero or
exactly one. -/
theorem topologicalKrullDim_le_zero_or_eq_one {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (hX : topologicalKrullDim X ≤ 1) :
    topologicalKrullDim Z ≤ 0 ∨ topologicalKrullDim Z = 1 := by
  have h := i.isClosedEmbedding.isEmbedding.isInducing.topologicalKrullDim_le.trans hX
  rcases h.lt_or_eq with h | h
  · left
    cases hZ : topologicalKrullDim Z with
    | bot => exact bot_le
    | coe d =>
      have hd : d < (1 : ℕ∞) := by simpa [hZ] using h
      exact_mod_cast (Order.le_of_lt_add_one (by simpa using hd) : d ≤ 0)
  · exact Or.inr h

end Stacks.AlgebraicGeometry.ComponentDegrees
