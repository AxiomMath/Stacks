module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Components
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.UniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import StacksFrontier.Topology.Irreducible.GenericPoints

/-!
# The normalization morphism is integral, surjective and bijective on irreducible components

Let `X` be a scheme such that every quasi-compact open of `X` has finitely many irreducible
components, and let `ν : X^ν ⟶ X` be its normalization morphism. Then `ν` is integral, it is
surjective, and sending an irreducible component to the closure of its image under `ν` is a
bijection from the irreducible components of `X^ν` onto those of `X`.

## Main results

* `AlgebraicGeometry.Scheme.bijOn_genericPoints_normalization`: the normalization morphism
  restricts to a bijection from the generic points of `X^ν` onto the generic points of `X`.
* `AlgebraicGeometry.Scheme.bijOn_irreducibleComponents_normalization`: the normalization
  morphism induces a bijection on irreducible components.
* `AlgebraicGeometry.Scheme.isIntegralHom_surjective_bijOn_irreducibleComponents_normalization`
  is part (2) of Tag 035Q: `ν` is integral, surjective, and a bijection on irreducible
  components.

## Implementation notes

The three assertions are assembled from results already in the library. Integrality is
`AlgebraicGeometry.Scheme.isIntegralHom_normalization`, the structural morphism of a relative
normalization (Tag 035I). Surjectivity is
`AlgebraicGeometry.Scheme.surjective_normalization`: `ν` is dominant because the morphism from
the generic-point residue fields it normalizes is (Tag 035M), and an integral morphism is
closed, so a dense image is everything.

The bijection on irreducible components is read off from the bijection on generic points.
Schemes are sober and `T0`, so taking the closure of a singleton is a bijection from the generic
points of a scheme onto its irreducible components, and `ν` is a bijection on generic points:
by Tag 035O the normalization of `X` is the normalization of the reduction of `X`, whose
inclusion is a homeomorphism on points, and the normalization of a reduced scheme is birational,
hence bijective on generic points by Tag 0BXC. Transporting along the two bijections of generic
points turns `ν` into the map `D ↦ closure (ν '' D)`, because `closure (ν '' closure {z})` is
`closure {ν z}`.

## References

* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-- The closure of a singleton is a bijection from the generic points of a sober `T0` space onto
its irreducible components. -/
private theorem bijOn_closure_singleton_genericPoints (α : Type*) [TopologicalSpace α]
    [T0Space α] [QuasiSober α] :
    Set.BijOn (fun x ↦ closure ({x} : Set α)) (genericPoints α) (irreducibleComponents α) := by
  refine ⟨fun _ hx ↦ hx, fun x hx y hy h ↦ ?_, fun C hC ↦ ?_⟩
  · exact congrArg Subtype.val (genericPoints.component_injective
      (Subtype.ext h : genericPoints.component ⟨x, hx⟩ = genericPoints.component ⟨y, hy⟩))
  · exact ⟨_, (genericPoints.ofComponent ⟨C, hC⟩).2,
      genericPoints.isGenericPoint_ofComponent ⟨C, hC⟩⟩

/-- Cancelling a bijection on the right: if `g` is a bijection from `s` onto `t` and `f ∘ g` is
a bijection from `s` onto `u`, then `f` is a bijection from `t` onto `u`. -/
private theorem bijOn_of_bijOn_comp {α β γ : Type*} {g : α → β} {f : β → γ} {s : Set α}
    {t : Set β} {u : Set γ} (hg : Set.BijOn g s t) (hfg : Set.BijOn (f ∘ g) s u) :
    Set.BijOn f t u := by
  refine ⟨fun b hb ↦ ?_, fun b hb b' hb' h ↦ ?_, fun c hc ↦ ?_⟩
  · obtain ⟨a, ha, rfl⟩ := hg.surjOn hb
    exact hfg.mapsTo ha
  · obtain ⟨a, ha, rfl⟩ := hg.surjOn hb
    obtain ⟨a', ha', rfl⟩ := hg.surjOn hb'
    exact congrArg g (hfg.injOn ha ha' h)
  · obtain ⟨a, ha, hac⟩ := hfg.surjOn hc
    exact ⟨g a, hg.mapsTo ha, hac⟩

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The normalization morphism of a scheme whose quasi-compact opens have finitely many
irreducible components restricts to a bijection from the generic points of the normalization
onto the generic points of the scheme.

By Tag 035O the normalization factors through the reduction, whose inclusion is a homeomorphism
on points, and the normalization of a reduced scheme is birational, hence bijective on generic
points by Tag 0BXC. -/
theorem bijOn_genericPoints_normalization
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    Set.BijOn (X.normalization hX) (genericPoints (X.normalizationScheme hX))
      (genericPoints X) := by
  obtain ⟨e, he⟩ := X.exists_normalizationScheme_iso_reduction hX
  have hred : IsReduced X.nilradical.subscheme := by
    simpa only [Scheme.IdealSheafData.vanishingIdeal_top] using
      Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal (X := X) ⊤
  have hsurj : Function.Surjective X.nilradical.subschemeι := fun x ↦
    Set.mem_range.mp (by rw [X.nilradical.range_subschemeι, Scheme.support_nilradical]; trivial)
  refine (((Homeomorph.bijOn_genericPoints
      (X.nilradical.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective
        hsurj)).comp
    (X.nilradical.subscheme.isBirational_normalization
      (X.finite_irreducibleComponents_reduction hX)).bijOn).comp
    (Homeomorph.bijOn_genericPoints (Scheme.Hom.homeomorph e.hom))).congr
    fun x _ => ?_
  rw [← he]
  rfl

/-- The normalization morphism of a scheme whose quasi-compact opens have finitely many
irreducible components induces a bijection on irreducible components: an irreducible component
of the normalization is carried to the closure of its image.

The closure of a singleton is a bijection from the generic points of a scheme onto its
irreducible components, and `AlgebraicGeometry.Scheme.bijOn_genericPoints_normalization` is the
corresponding statement for generic points. -/
theorem bijOn_irreducibleComponents_normalization
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    Set.BijOn (fun D ↦ closure ((X.normalization hX).base '' D))
      (irreducibleComponents (X.normalizationScheme hX)) (irreducibleComponents X) := by
  refine bijOn_of_bijOn_comp
    (bijOn_closure_singleton_genericPoints (X.normalizationScheme hX))
    (((bijOn_closure_singleton_genericPoints X).comp
      (X.bijOn_genericPoints_normalization hX)).congr fun z _ ↦ ?_)
  show closure {(X.normalization hX).base z} =
    closure ((X.normalization hX).base '' closure {z})
  rw [closure_image_closure (X.normalization hX).continuous, Set.image_singleton]

/-- **Stacks Project, Tag 035Q.** Part (2). Let `X` be a scheme such that every quasi-compact
open of `X` has finitely many irreducible components. Then the normalization morphism
`ν : X^ν ⟶ X` is integral, it is surjective, and it induces a bijection on irreducible
components: sending an irreducible component of `X^ν` to the closure of its image under `ν` is a
bijection onto the set of irreducible components of `X`.

Integrality is `AlgebraicGeometry.Scheme.isIntegralHom_normalization` (Tag 035I), surjectivity
is `AlgebraicGeometry.Scheme.surjective_normalization`, and the bijection on components is
`AlgebraicGeometry.Scheme.bijOn_irreducibleComponents_normalization`, which rests on Tags 035O
and 0BXC. -/
@[stacks 035Q "normalization_integral_surjective_bijection_on_components"]
theorem isIntegralHom_surjective_bijOn_irreducibleComponents_normalization
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    IsIntegralHom (X.normalization hX) ∧ Surjective (X.normalization hX) ∧
      Set.BijOn (fun D ↦ closure ((X.normalization hX).base '' D))
        (irreducibleComponents (X.normalizationScheme hX)) (irreducibleComponents X) :=
  ⟨X.isIntegralHom_normalization hX, X.surjective_normalization hX,
    X.bijOn_irreducibleComponents_normalization hX⟩

end AlgebraicGeometry.Scheme

end
