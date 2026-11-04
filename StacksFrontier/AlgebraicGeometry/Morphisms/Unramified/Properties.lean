module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.Unramified.LocalStructure
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Local
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Properties of unramified morphisms

An unramified morphism of schemes is equivalently a locally finite type, formally unramified
morphism, and a G-unramified morphism is equivalently a locally finitely presented, formally
unramified one. Both classes are stable under composition and under arbitrary base change, and
both descend from a composite to its first factor, G-unramifiedness under the additional
assumption that the second factor is locally of finite type. A morphism unramified at a point is
quasi-finite there; an unramified morphism is locally of finite type and locally quasi-finite, and
its residue field extensions are finite separable.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.unramified_iff_locallyOfFiniteType_and_formallyUnramified` and
  `AlgebraicGeometry.gUnramified_iff_locallyOfFinitePresentation_and_formallyUnramified`
  characterize the two classes by a finiteness condition together with formal unramifiedness.
* `AlgebraicGeometry.unramified_isStableUnderComposition` and
  `AlgebraicGeometry.gUnramified_isStableUnderComposition` give stability under composition.
* `AlgebraicGeometry.unramified_isStableUnderBaseChange` and
  `AlgebraicGeometry.gUnramified_isStableUnderBaseChange` give stability under base change.
* `AlgebraicGeometry.unramified_of_comp` descends unramifiedness to the first factor, and
  `AlgebraicGeometry.gUnramified_of_comp` does the same for G-unramifiedness when the second
  factor is locally of finite type.
* `AlgebraicGeometry.quasiFiniteAt_of_unramifiedAt` is the pointwise finiteness consequence, and
  `AlgebraicGeometry.locallyOfFiniteType_of_unramified` and
  `AlgebraicGeometry.locallyQuasiFinite_of_unramified` are the two global ones.
* `AlgebraicGeometry.finite_residueField_of_unramified` and
  `AlgebraicGeometry.isSeparable_residueField_of_unramified` describe the residue field
  extensions.

## Implementation notes

Stability under composition and under base change are transported from the corresponding
properties of ring homomorphisms along the `AlgebraicGeometry.HasRingHomProperty` instances
established with the locality of the two classes, so the conjunctive form of each class is set up
once rather than at each use. The two descent statements along a composite are proved through
that conjunctive form as well: the formal half is Mathlib's
`AlgebraicGeometry.FormallyUnramified.of_comp` in both cases, while the finiteness half is
`AlgebraicGeometry.locallyOfFiniteType_of_comp` for the unramified case and
`AlgebraicGeometry.locallyOfFinitePresentation_of_comp` for the G-unramified one, the latter
being exactly where the finite-type hypothesis on the second factor is consumed.

Local quasi-finiteness of an unramified morphism uses that an unramified algebra is quasi-finite:
`Algebra.Unramified.finiteType` gives essential finite type and
`Algebra.Unramified.formallyUnramified` the formal condition, and Mathlib's quasi-finiteness
instance concludes.

The pointwise statement concludes `AlgebraicGeometry.quasiFiniteAt`, which is finite type at the
point together with quasi-finiteness of the stalk map, Mathlib's
`AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt` omitting the finite-type condition. Both halves come
from the single affine chart that witnesses unramifiedness at the point, so that no global
finiteness hypothesis is required: the chart's map of sections is of finite type, which is the
first half directly, and `AlgebraicGeometry.IsAffineOpen.arrowStalkMapIso` identifies the stalk
map with the local homomorphism that map of sections induces, along which
`RingHom.HoldsForLocalization.localRingHom` transports essential finite type and formal
unramifiedness.

The residue field statements record the finite and the separable half of "finite separable"
separately, with the algebra structure on `κ(x)` induced by the canonical residue field map
`κ(f(x)) → κ(x)`.

## References

* [Stacks Project, Tag 02HE](https://stacks.math.columbia.edu/tag/02HE)
* [Stacks Project, Tag 02G9](https://stacks.math.columbia.edu/tag/02G9)
* [Stacks Project, Tag 02GA](https://stacks.math.columbia.edu/tag/02GA)
* [Stacks Project, Tag 02GG](https://stacks.math.columbia.edu/tag/02GG)
* [Stacks Project, Tag 02G8](https://stacks.math.columbia.edu/tag/02G8)
* [Stacks Project, Tag 02V5](https://stacks.math.columbia.edu/tag/02V5)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- An unramified morphism of schemes is locally of finite type. -/
@[stacks 02V5 "local finite-type part of the global consequence"]
public instance locallyOfFiniteType_of_unramified (f : X ⟶ S) [Unramified f] :
    LocallyOfFiniteType f := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFiniteType)
    (RingHom.finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finiteType_holdsForLocalizationAway).left]
  intro x
  obtain ⟨U, hU, hx, V, hV, e, h⟩ := Unramified.unramifiedAt (f := f) x
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  exact ⟨⟨V, hV⟩, ⟨U, hU⟩, hx, e, Algebra.Unramified.finiteType⟩

/-- An unramified morphism of schemes is formally unramified. -/
public lemma formallyUnramified_of_unramified (f : X ⟶ S) [Unramified f] :
    FormallyUnramified f := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @FormallyUnramified)
    (RingHom.FormallyUnramified.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.FormallyUnramified.holdsForLocalizationAway).left]
  intro x
  obtain ⟨U, hU, hx, V, hV, e, h⟩ := Unramified.unramifiedAt (f := f) x
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  exact ⟨⟨V, hV⟩, ⟨U, hU⟩, hx, e, Algebra.Unramified.formallyUnramified⟩

/-- **Stacks Project, Tag 02V5, the pointwise claim.** A morphism of schemes unramified at `x` is
quasi-finite at `x`. No hypothesis beyond unramifiedness at the point: the affine chart witnessing
it carries an unramified, hence finite-type, map of sections, which is finite type at the point
and makes the stalk map both essentially of finite type and formally unramified, and such an
algebra is quasi-finite. -/
@[stacks 02V5 "the pointwise claim: unramified at `x` implies quasi-finite at `x`"]
public theorem quasiFiniteAt_of_unramifiedAt (f : X ⟶ S) {x : X} (h : UnramifiedAt f x) :
    quasiFiniteAt f x := by
  obtain ⟨U, hU, hxU, V, hV, e, halg⟩ := h
  let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  have halg' : Algebra.Unramified Γ(S, V) Γ(X, U) := halg
  have hft : (f.appLE V U e).hom.FiniteType :=
    RingHom.finiteType_algebraMap.mpr halg'.finiteType
  refine ⟨⟨⟨V, hV⟩, ⟨U, hU⟩, hxU, e, hft⟩, ?_⟩
  have hcomap : (hV.primeIdealOf ⟨f x, e hxU⟩).asIdeal =
      Ideal.comap (f.appLE V U e).hom (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    congr($(IsAffineOpen.comap_primeIdealOf_appLE V hV U hU e hxU).1).symm
  have hiso := IsAffineOpen.arrowStalkMapIso f V hV U hU e hxU
  have hess : (f.stalkMap x).hom.EssFiniteType :=
    (RingHom.EssFiniteType.respectsIso.arrow_mk_iso_iff hiso).mpr <|
      RingHom.EssFiniteType.holdsForLocalization.localRingHom
        RingHom.EssFiniteType.stableUnderComposition
        RingHom.EssFiniteType.isStableUnderBaseChange.localizationPreserves hcomap
        (RingHom.FiniteType.essFiniteType hft)
  have hfu : (f.stalkMap x).hom.FormallyUnramified :=
    (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff hiso).mpr <|
      RingHom.FormallyUnramified.holdsForLocalization.localRingHom
        RingHom.FormallyUnramified.stableUnderComposition
        RingHom.FormallyUnramified.isStableUnderBaseChange.localizationPreserves hcomap
        (RingHom.formallyUnramified_algebraMap.mpr halg'.formallyUnramified)
  algebraize [(f.stalkMap x).hom]
  have _ : Algebra.EssFiniteType (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    RingHom.essFiniteType_algebraMap.mpr hess
  have _ : Algebra.FormallyUnramified (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    RingHom.formallyUnramified_algebraMap.mpr hfu
  exact RingHom.quasiFinite_algebraMap.mpr inferInstance

/-- The fibers of an unramified morphism are locally discrete. -/
@[stacks 02V5 "fiber-isolation part of the global consequence", ega "IV 17.4.3"]
public instance locallyQuasiFinite_of_unramified (f : X ⟶ S) [Unramified f] :
    LocallyQuasiFinite f := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyQuasiFinite)
    (RingHom.QuasiFinite.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.QuasiFinite.holdsForLocalizationAway).left]
  intro x
  obtain ⟨U, hU, hx, V, hV, e, h⟩ := Unramified.unramifiedAt (f := f) x
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  let : Algebra.Unramified Γ(S, V) Γ(X, U) := h
  exact ⟨⟨V, hV⟩, ⟨U, hU⟩, hx, e,
    RingHom.quasiFinite_algebraMap.mpr (inferInstance : Algebra.QuasiFinite _ _)⟩

private lemma algebraUnramified_iff_ringHom {R T : Type u} [CommRing R] [CommRing T]
    (g : R →+* T) :
    letI : Algebra R T := g.toAlgebra
    Algebra.Unramified R T ↔ (g.FiniteType ∧ g.FormallyUnramified) := by
  let : Algebra R T := g.toAlgebra
  show Algebra.Unramified R T ↔
    (RingHom.FiniteType (algebraMap R T) ∧ RingHom.FormallyUnramified (algebraMap R T))
  rw [RingHom.finiteType_algebraMap, RingHom.formallyUnramified_algebraMap]
  exact ⟨fun h => ⟨h.finiteType, h.formallyUnramified⟩, fun h => ⟨h.2, h.1⟩⟩

private lemma algebraGUnramified_iff_ringHom {R T : Type u} [CommRing R] [CommRing T]
    (g : R →+* T) :
    letI : Algebra R T := g.toAlgebra
    Algebra.GUnramified R T ↔ (g.FinitePresentation ∧ g.FormallyUnramified) := by
  let : Algebra R T := g.toAlgebra
  show Algebra.GUnramified R T ↔
    (RingHom.FinitePresentation (algebraMap R T) ∧ RingHom.FormallyUnramified (algebraMap R T))
  rw [RingHom.finitePresentation_algebraMap, RingHom.formallyUnramified_algebraMap]
  exact ⟨fun h => ⟨h.finitePresentation, h.formallyUnramified⟩, fun h => ⟨h.2, h.1⟩⟩

/-- A property of ring homomorphisms that splits as a conjunction with formal unramifiedness holds
on all `appLE` maps of a morphism if and only if each conjunct does, as in `locallyOfFiniteType_iff`
and `formallyUnramified_iff`. -/
private lemma forall_appLE_iff_and
    {A B : ∀ {R T : Type u} [CommRing R] [CommRing T], (R →+* T) → Prop}
    (h : ∀ {R T : Type u} [CommRing R] [CommRing T] (g : R →+* T),
      A g ↔ (B g ∧ g.FormallyUnramified))
    (f : X ⟶ S) :
    (∀ (U : X.Opens), IsAffineOpen U → ∀ (V : S.Opens), IsAffineOpen V → ∀ (e : U ≤ f ⁻¹ᵁ V),
      A (f.appLE V U e).hom) ↔
    ((∀ {V : S.Opens}, IsAffineOpen V → ∀ {U : X.Opens}, IsAffineOpen U → ∀ (e : U ≤ f ⁻¹ᵁ V),
      B (f.appLE V U e).hom) ∧
    (∀ {V : S.Opens}, IsAffineOpen V → ∀ {U : X.Opens}, IsAffineOpen U → ∀ (e : U ≤ f ⁻¹ᵁ V),
      (f.appLE V U e).hom.FormallyUnramified)) := by
  refine ⟨fun H => ⟨fun {V} hV {U} hU e => ((h _).mp (H U hU V hV e)).1,
    fun {V} hV {U} hU e => ((h _).mp (H U hU V hV e)).2⟩, ?_⟩
  rintro ⟨hB, hform⟩ U hU V hV e
  exact (h _).mpr ⟨hB hV hU e, hform hV hU e⟩

/-- A morphism of schemes is unramified if and only if it is locally of finite type and formally
unramified. -/
@[stacks 02HE "unramified case",
  ega "IV 17.4.1.2" "a) formally unramified",
  ega "IV 17.4.2" "a) ⇔ e)", ega "IV 17.4.1" "a) <=> e)"]
public theorem unramified_iff_locallyOfFiniteType_and_formallyUnramified (f : X ⟶ S) :
    Unramified f ↔ (LocallyOfFiniteType f ∧ FormallyUnramified f) := by
  refine ((unramified_tfae f).out 1 2).trans ?_
  rw [locallyOfFiniteType_iff, formallyUnramified_iff]
  exact forall_appLE_iff_and algebraUnramified_iff_ringHom f

/-- A morphism of schemes is G-unramified if and only if it is locally of finite presentation and
formally unramified. -/
@[stacks 02HE "G-unramified case",
  ega "IV 17.3.2" "(ii) unramified",
  ega "IV 17.4.2" "a) ⇔ e)",
  ega "IV 17.4.1" "a) <=> e)", ega "IV 17.3.1" "unramified (net)"]
public theorem gUnramified_iff_locallyOfFinitePresentation_and_formallyUnramified (f : X ⟶ S) :
    GUnramified f ↔ (LocallyOfFinitePresentation f ∧ FormallyUnramified f) := by
  refine ((gUnramified_tfae f).out 1 2).trans ?_
  rw [locallyOfFinitePresentation_iff, formallyUnramified_iff]
  exact forall_appLE_iff_and algebraGUnramified_iff_ringHom f

/-- Unramified morphisms of schemes are stable under composition. -/
@[stacks 02G9 "unramified", ega "IV 17.3.3" "(ii), special case", sga "1 I 3.5" "more general"]
public instance unramified_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition (@Unramified.{u}) :=
  HasRingHomProperty.stableUnderComposition
    (RingHom.FormallyUnramified.stableUnderComposition.and
      RingHom.finiteType_stableUnderComposition)

/-- G-unramified morphisms of schemes are stable under composition. -/
@[stacks 02G9 "G-unramified", ega "IV 17.3.3" "(ii)", sga "1 I 3.5" "more general"]
public instance gUnramified_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition (@GUnramified.{u}) :=
  HasRingHomProperty.stableUnderComposition
    (RingHom.FormallyUnramified.stableUnderComposition.and
      RingHom.finitePresentation_stableUnderComposition)

/-- Unramified morphisms of schemes are stable under arbitrary base change. -/
@[stacks 02GA "unramified", sga "1 I 3.5" "(iii)"]
public instance unramified_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (fun {X S : Scheme.{u}} (f : X ⟶ S) ↦ Unramified f) :=
  HasRingHomProperty.isStableUnderBaseChange
    (RingHom.FormallyUnramified.isStableUnderBaseChange.and
      RingHom.finiteType_isStableUnderBaseChange)

/-- G-unramified morphisms of schemes are stable under arbitrary base change. -/
@[stacks 02GA "G-unramified", sga "1 I 3.5" "(iii)"]
public instance gUnramified_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (fun {X S : Scheme.{u}} (f : X ⟶ S) ↦ GUnramified f) :=
  HasRingHomProperty.isStableUnderBaseChange
    (RingHom.FormallyUnramified.isStableUnderBaseChange.and
      RingHom.finitePresentation_isStableUnderBaseChange)

/-- If the composite `X ⟶ Y ⟶ S` is unramified, then `X ⟶ Y` is unramified. -/
@[stacks 02GG "part (1)", sga "1 I 3.6" "(v)"]
public theorem unramified_of_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [Unramified (f ≫ g)] : Unramified f := by
  apply (unramified_iff_locallyOfFiniteType_and_formallyUnramified f).mpr
  have h := (unramified_iff_locallyOfFiniteType_and_formallyUnramified
    (f ≫ g)).mp (inferInstance : Unramified (f ≫ g))
  let := h.1
  let := h.2
  exact ⟨locallyOfFiniteType_of_comp f g, FormallyUnramified.of_comp f g⟩

/-- If the composite `X ⟶ Y ⟶ S` is G-unramified and `Y ⟶ S` is locally of finite type, then
`X ⟶ Y` is G-unramified. -/
@[stacks 02GG "part (2): carries the hypothesis that `g` is locally of finite type"]
public theorem gUnramified_of_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [GUnramified (f ≫ g)] [LocallyOfFiniteType g] : GUnramified f := by
  apply (gUnramified_iff_locallyOfFinitePresentation_and_formallyUnramified f).mpr
  have h := (gUnramified_iff_locallyOfFinitePresentation_and_formallyUnramified
    (f ≫ g)).mp (inferInstance : GUnramified (f ≫ g))
  let := h.1
  let := h.2
  exact ⟨locallyOfFinitePresentation_of_comp f g, FormallyUnramified.of_comp f g⟩

/-- The residue field extension at a point of an unramified morphism is finite. -/
@[stacks 02G8 "finite_separable_residue",
  ega "IV 17.4.1" "a) => d'' finiteness",
  sga "3 XI 1.3" "(ii) k(B)/k(A) finite", sga "1 I 3.1" "(ii)=>(i) finiteness"]
public instance finite_residueField_of_unramified (f : X ⟶ S) [Unramified f] (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Module.Finite (S.residueField (f x)) (X.residueField x) := by
  let : FormallyUnramified f := formallyUnramified_of_unramified f
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (S.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  suffices h : Module.Finite
      (IsLocalRing.ResidueField <| S.presheaf.stalk (f x))
      (IsLocalRing.ResidueField <| X.presheaf.stalk x) by
    convert! h
    exact congrArg (fun A : Algebra (S.residueField (f x)) (X.residueField x) ↦
      @Algebra.toModule _ _ _ _ A) (Algebra.algebra_ext _ _ fun
        y : S.residueField (f x) ↦ by
      obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective y
      rfl)
  have : Algebra.EssFiniteType (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    RingHom.essFiniteType_algebraMap.mpr (LocallyOfFiniteType.stalkMap f x)
  have : Algebra.FormallyUnramified (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    RingHom.formallyUnramified_algebraMap.mpr (AlgebraicGeometry.FormallyUnramified.stalkMap f x)
  infer_instance

/-- The residue field extension at a point of an unramified morphism is separable. -/
@[stacks 02G8 "finite_separable_residue",
  ega "IV 17.4.1" "a) => d'' separability",
  sga "3 XI 1.3" "(ii) k(B)/k(A) separable", sga "1 I 3.1" "(ii)=>(i) separability"]
public instance isSeparable_residueField_of_unramified (f : X ⟶ S) [Unramified f] (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Algebra.IsSeparable (S.residueField (f x)) (X.residueField x) := by
  let : FormallyUnramified f := formallyUnramified_of_unramified f
  infer_instance

end AlgebraicGeometry
