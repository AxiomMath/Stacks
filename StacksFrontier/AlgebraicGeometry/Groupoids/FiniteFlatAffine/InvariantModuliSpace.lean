module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.FlatInvariants
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.IntegralInvariants
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.UniversallyClosedCriterion

/-!
# The invariant spectrum as a moduli space in affine schemes

Let `G = (U, R, s, t, c)` be a groupoid scheme and let `C = invariantRing G` be the ring of
`R`-invariant global functions on the object scheme. The canonical morphism
`φ : U ⟶ M = Spec C` is `AlgebraicGeometry.GroupoidScheme.objectsToInvariantSpectrum`. This file
proves that `φ` is a categorical quotient in the category of affine schemes, that it stays one
after every flat base change of `C`, and that it is universally closed.

## Main results

* `AlgebraicGeometry.GroupoidScheme.existsUnique_comp_objectsToInvariantSpectrum`: every morphism
  from the object scheme to an affine scheme which coequalizes the target and the source factors
  uniquely through `φ`. This holds with no hypothesis on the groupoid.
* `AlgebraicGeometry.GroupoidScheme.target_comp_objectsToInvariantSpectrum`: `φ` coequalizes the
  target and the source maps, again with no hypothesis on the groupoid.
* `AlgebraicGeometry.GroupoidScheme.existsUnique_comp_objects_hom_of_flat`: after a flat base
  change `C ⟶ C'`, the structure morphism of the object scheme of the base-changed groupoid has
  the same universal property, with target the base change `Spec C'` itself.
* `AlgebraicGeometry.GroupoidScheme.universallyClosed_objectsToInvariantSpectrum`: `φ` is
  universally closed, for a groupoid with affine object and arrow schemes and finite locally free
  source and target.

## Implementation notes

The test objects are the absolute affine schemes `Spec C'`, not the affine schemes over the base
scheme `S` of the groupoid. This gives more test objects, hence a stronger universal property.

The universal property and the invariance of `φ` follow from the definition of
`AlgebraicGeometry.invariantRing` as the equalizer subring of `AlgebraicGeometry.sourceMap` and
`AlgebraicGeometry.targetMap`, together with the `Γ`-`Spec` adjunction; the object scheme need not
be affine, because the adjunction unit `AlgebraicGeometry.Scheme.toSpecΓ` is available for every
scheme.

The flat base change is the package `AlgebraicGeometry.GroupoidScheme.AffineInvariantBaseChange`,
which carries the base-changed groupoid as data.

## References

* [Stacks Project, Tag 0DUP](https://stacks.math.columbia.edu/tag/0DUP)
* [Stacks Project, Tag 01I1](https://stacks.math.columbia.edu/tag/01I1)
* [Stacks Project, Tag 01WM](https://stacks.math.columbia.edu/tag/01WM)
* [Stacks Project, Tag 03BJ](https://stacks.math.columbia.edu/tag/03BJ)
* [Stacks Project, Tag 03BK](https://stacks.math.columbia.edu/tag/03BK)
* [Stacks Project, Tag 03BE](https://stacks.math.columbia.edu/tag/03BE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-! ### Morphisms into an affine scheme -/

/-- The ring map induced by the morphism `X ⟶ Spec R` attached to a ring map `R ⟶ Γ(X, ⊤)` is
that ring map again. -/
private theorem induced_toSpecΓ_comp_specMap (X : Scheme.{u}) {R : CommRingCat.{u}}
    (φ : R ⟶ Γ(X, ⊤)) :
    (Scheme.ΓSpecIso R).inv ≫ Scheme.Γ.map (X.toSpecΓ ≫ Spec.map φ).op = φ := by
  rw [Scheme.Γ_map_op, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
    Scheme.ΓSpecIso_naturality]
  simp

/-- The ring map induced by `φ` followed by a morphism `Spec C ⟶ Spec C'` of affine schemes is the
corresponding ring map followed by the inclusion of the invariant ring. -/
private theorem induced_objectsToInvariantSpectrum_comp (C' : Type u) [CommRing C']
    (p : CommRingCat.of C' ⟶ CommRingCat.of (invariantRing G)) :
    (Scheme.ΓSpecIso (.of C')).inv ≫
        Scheme.Γ.map (objectsToInvariantSpectrum G ≫ Spec.map p).op =
      p ≫ CommRingCat.ofHom (invariantRing G).subtype := by
  rw [objectsToInvariantSpectrum, Category.assoc, ← Spec.map_comp]
  exact induced_toSpecΓ_comp_specMap _ _

/-- A morphism from the object scheme to an affine scheme which coequalizes the target and the
source maps induces a ring map landing in the invariant ring. -/
theorem induced_mem_invariantRing (C' : Type u) [CommRing C']
    (ψ : G.objects.left ⟶ Spec (.of C'))
    (hψ : G.target.left ≫ ψ = G.source.left ≫ ψ) (c : C') :
    ((Scheme.ΓSpecIso (.of C')).inv ≫ Scheme.Γ.map ψ.op).hom c ∈ invariantRing G := by
  have h := congrArg (fun k => (Scheme.ΓSpecIso (CommRingCat.of C')).inv ≫ Scheme.Γ.map k.op) hψ
  simp only [Scheme.Γ_map_op, Scheme.Hom.comp_appTop] at h
  replace h := congrArg (fun k => CommRingCat.Hom.hom k c) h
  simp only [Scheme.Γ_map_op]
  exact_mod_cast h.symm

/-! ### The universal property in the category of affine schemes -/

/-- A morphism from the arrow scheme to the object scheme followed by the invariant quotient map,
written through the unit of the `Γ`-`Spec` adjunction at the arrow scheme. -/
private theorem comp_objectsToInvariantSpectrum (m : G.arrows.left ⟶ G.objects.left) :
    m ≫ objectsToInvariantSpectrum G =
      G.arrows.left.toSpecΓ ≫ Spec.map
        (CommRingCat.ofHom (invariantRing G).subtype ≫ m.appTop) := by
  rw [objectsToInvariantSpectrum, Spec.map_comp, ← Category.assoc,
    Scheme.toSpecΓ_naturality, Category.assoc]

/-- The invariant quotient coequalizes the target and the source maps. -/
theorem target_comp_objectsToInvariantSpectrum :
    G.target.left ≫ objectsToInvariantSpectrum G =
      G.source.left ≫ objectsToInvariantSpectrum G := by
  rw [comp_objectsToInvariantSpectrum, comp_objectsToInvariantSpectrum]
  refine congrArg (fun p => G.arrows.left.toSpecΓ ≫ Spec.map p)
    (CommRingCat.hom_ext (RingHom.ext fun c => ?_))
  exact (c.property : sourceMap G c.val = targetMap G c.val).symm

/-- Let `G = (U, R, s, t, c)` be a groupoid scheme and let `C` be the ring of `R`-invariant
global functions on `U`. Every morphism `ψ : U ⟶ Spec C'` to an affine scheme which coequalizes
the target and the source maps factors uniquely through `φ : U ⟶ Spec C`. Together with
`AlgebraicGeometry.GroupoidScheme.target_comp_objectsToInvariantSpectrum` this says that `φ` is a
categorical quotient of `(t, s)` in the category of affine schemes. -/
@[stacks 0DUP "the construction of the moduli space and its universal property, at the groupoid \
presentation and for the quotient map of the object scheme: the invariant-ring quotient \
U -> M = Spec C is a categorical quotient in the category of affine schemes. The 1-morphism \
f : X -> M out of the quotient stack is NOT constructed, and none of the four assertions about f \
is proved: the passage from U -> M to f along Stacks 0DUH and Stacks 0DUI, and the implication \
(1) => (2) of Stacks 0DUM, are not available in the library", sga "1 V 1.1" "(iv), special case"]
theorem existsUnique_comp_objectsToInvariantSpectrum (C' : Type u) [CommRing C']
    (ψ : G.objects.left ⟶ Spec (.of C'))
    (hψ : G.target.left ≫ ψ = G.source.left ≫ ψ) :
    ∃! χ : Spec (.of (invariantRing G)) ⟶ Spec (.of C'),
      objectsToInvariantSpectrum G ≫ χ = ψ := by
  refine ⟨Spec.map (CommRingCat.ofHom (RingHom.codRestrict
      ((Scheme.ΓSpecIso (.of C')).inv ≫ Scheme.Γ.map ψ.op).hom (invariantRing G)
      (induced_mem_invariantRing G C' ψ hψ))), ext_to_Spec ?_, ?_⟩
  · rw [induced_objectsToInvariantSpectrum_comp G C']
    exact CommRingCat.hom_ext (RingHom.ext fun c => rfl)
  · intro χ' hχ'
    obtain ⟨p, rfl⟩ : ∃ p, Spec.map p = χ' := ⟨Spec.preimage χ', Spec.map_preimage χ'⟩
    have h1 : p ≫ CommRingCat.ofHom (invariantRing G).subtype =
        (Scheme.ΓSpecIso (.of C')).inv ≫ Scheme.Γ.map ψ.op := by
      rw [← induced_objectsToInvariantSpectrum_comp G C' p, hχ']
    rw [Spec.map_inj]
    exact CommRingCat.hom_ext (RingHom.ext fun c => Subtype.ext
      (congrArg (fun k => CommRingCat.Hom.hom k c) h1))

/-! ### Uniformity under flat base change -/

section BaseChange

variable {C' : Type u} [CommRing C'] [Algebra (invariantRing G) C']
  (G' : AffineInvariantBaseChange G C')

/-- The structure morphism of the object scheme of the base-changed groupoid factors through its
own invariant quotient, followed by the morphism of affine schemes attached to the canonical map
from the new base ring to the invariant ring of the base-changed groupoid. -/
private theorem objects_hom_eq_objectsToInvariantSpectrum_comp :
    objectsToInvariantSpectrum G'.groupoid ≫
        Spec.map (CommRingCat.ofHom G'.canonicalMapToInvariantFunctions) =
      G'.groupoid.objects.hom := by
  refine ext_to_Spec ?_
  rw [induced_objectsToInvariantSpectrum_comp G'.groupoid C']
  exact CommRingCat.hom_ext (RingHom.ext fun c => rfl)

/-- For a flat ring map `C ⟶ C'`, the canonical map from `C'` to the invariant ring of the
base-changed groupoid induces an isomorphism of affine schemes. -/
theorem isIso_specMap_canonicalMap [Module.Flat (invariantRing G) C'] :
    IsIso (Spec.map (CommRingCat.ofHom G'.canonicalMapToInvariantFunctions)) := by
  have : IsIso (CommRingCat.ofHom G'.canonicalMapToInvariantFunctions) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (canonicalMapToInvariantFunctions_bijective_of_flat G')
  infer_instance

/-- Let `C ⟶ C'` be a flat ring map and let `G'` be the base change of the groupoid along it.
Then the structure morphism `U' ⟶ Spec C'` of the object scheme of `G'` has the universal property
of `AlgebraicGeometry.GroupoidScheme.existsUnique_comp_objectsToInvariantSpectrum`: every morphism
from `U'` to an affine scheme which coequalizes the target and the source maps of `G'` factors
uniquely through it. -/
@[stacks 0DUP "the word *uniform*, at the groupoid presentation and for the quotient map of the \
object scheme: after a flat base change C -> C' the structure morphism U' -> Spec C' of the \
base-changed groupoid is again a categorical quotient in the category of affine schemes, so the \
flat base change of M is again the moduli space. Stated for U' -> Spec C' and NOT for the base \
change of a 1-morphism f : X -> M, which is not constructed here",
  sga "1 V 1.9" "affine case with Z = Y"]
theorem existsUnique_comp_objects_hom_of_flat [Module.Flat (invariantRing G) C']
    (C'' : Type u) [CommRing C''] (ψ : G'.groupoid.objects.left ⟶ Spec (.of C''))
    (hψ : G'.groupoid.target.left ≫ ψ = G'.groupoid.source.left ≫ ψ) :
    ∃! χ : Spec (.of C') ⟶ Spec (.of C''), G'.groupoid.objects.hom ≫ χ = ψ := by
  have := isIso_specMap_canonicalMap G G'
  set e := Spec.map (CommRingCat.ofHom G'.canonicalMapToInvariantFunctions)
  have hfac : objectsToInvariantSpectrum G'.groupoid ≫ e = G'.groupoid.objects.hom :=
    objects_hom_eq_objectsToInvariantSpectrum_comp G G'
  obtain ⟨χ₀, hχ₀, huniq⟩ :=
    existsUnique_comp_objectsToInvariantSpectrum G'.groupoid C'' ψ hψ
  refine ⟨inv e ≫ χ₀, ?_, fun χ hχ => ?_⟩
  · show G'.groupoid.objects.hom ≫ inv e ≫ χ₀ = ψ
    rw [← hfac, Category.assoc, IsIso.hom_inv_id_assoc, hχ₀]
  · have hx : e ≫ χ = χ₀ := by
      refine huniq _ ?_
      show objectsToInvariantSpectrum G'.groupoid ≫ e ≫ χ = ψ
      rwa [← Category.assoc, hfac]
    rw [← hx, IsIso.inv_hom_id_assoc]

end BaseChange

/-! ### The quotient map is universally closed -/

section UniversallyClosed

variable [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]

/-- The invariant quotient map is integral. -/
@[sga "1 V 1.1" "more general", sga "1 V 1.3" "(i), special case"]
theorem isIntegralHom_objectsToInvariantSpectrum :
    IsIntegralHom (objectsToInvariantSpectrum G) := by
  have h : IsIntegralHom (Spec.map (CommRingCat.ofHom (invariantRing G).subtype)) :=
    IsIntegralHom.SpecMap_iff.2 (isIntegral_invariantRing G)
  rw [objectsToInvariantSpectrum]
  infer_instance

/-- The invariant quotient map `U ⟶ M = Spec C` is universally closed. -/
@[stacks 0DUP "part of assertion (d), at the groupoid presentation and for the quotient map of \
the object scheme: U -> M = Spec C is integral (Stacks 03BJ) and therefore universally closed \
(Stacks 01WM). That f : X -> M is a universal homeomorphism is NOT proved: neither the transport \
of universal closedness along the surjection U -> X (Stacks 0CQK), nor universal injectivity of f \
(Stacks 0DTN), nor surjectivity of |f| is covered here", sga "3 V 6.1" "special case"]
theorem universallyClosed_objectsToInvariantSpectrum :
    UniversallyClosed (objectsToInvariantSpectrum G) :=
  (IsIntegralHom.iff_universallyClosed_and_isAffineHom.1
    (isIntegralHom_objectsToInvariantSpectrum G)).1

end UniversallyClosed

end AlgebraicGeometry.GroupoidScheme

end
