module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Defs
public import StacksFrontier.RingTheory.Unramified.Properties
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Characterizations of unramified morphisms

Unramifiedness and G-unramifiedness of a morphism of schemes may be checked on every pair of
compatible affine opens, on arbitrary open coverings by unramified morphisms, or on affine open
coverings by unramified ring maps. Both properties are also preserved when the source and target
are restricted to compatible open subschemes.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.unramified_tfae` gives four equivalent characterizations of an unramified
  morphism.
* `AlgebraicGeometry.gUnramified_tfae` gives the corresponding characterizations for
  G-unramifiedness.
* `AlgebraicGeometry.unramified_resLE` and `AlgebraicGeometry.gUnramified_resLE` show that these
  properties are preserved by restriction to compatible open subschemes.

## Implementation notes

The four entries of each `List.TFAE` are, in order, global unramifiedness, the condition on every
compatible pair of affine opens, an open-covering criterion using restricted morphisms, and an
affine-open-covering criterion using maps on rings of sections. The two restriction lemmas state
the respective clauses following the list of equivalent conditions in the source.

`Algebra.Unramified` on a ring map is the conjunction of `RingHom.FormallyUnramified` and
`RingHom.FiniteType`, and `Algebra.GUnramified` replaces the latter by
`RingHom.FinitePresentation`. Both conjunctions are local on the source, so unramifiedness and
G-unramifiedness are `affineLocally` of a ring-homomorphism property. That identification is
recorded here as `AlgebraicGeometry.unramified_iff_affineLocally` and
`AlgebraicGeometry.gUnramified_iff_affineLocally`, together with the
`AlgebraicGeometry.HasRingHomProperty` instances in conjunctive form, so that every later
consequence of locality is derived from one copy rather than reconstructed.

## References

* [Stacks Project, Tag 02G6](https://stacks.math.columbia.edu/tag/02G6)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Unramifiedness of a ring homomorphism, as a property of the induced algebra, is local. -/
public theorem unramified_ringHom_propertyIsLocal : RingHom.PropertyIsLocal
    (fun {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) =>
      letI := g.toAlgebra; Algebra.Unramified R S) := by
  let Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop := fun
      {R S} _ _ g => let := g.toAlgebra; Algebra.Unramified R S
  let Q' : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop :=
      fun g => RingHom.FormallyUnramified g ∧ RingHom.FiniteType g
  have e : @Q = @Q' := by
    funext R S iR iS g
    let := g.toAlgebra
    exact propext ⟨fun h => ⟨h.formallyUnramified, h.finiteType⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩
  change RingHom.PropertyIsLocal Q
  rw [e]
  exact RingHom.FormallyUnramified.propertyIsLocal.and RingHom.finiteType_isLocal

/-- Unramifiedness of a ring homomorphism is stable under precomposition with a localization
away from an element of the source. -/
public theorem unramified_ringHom_stableUnderCompositionWithLocalizationAwaySource :
    RingHom.StableUnderCompositionWithLocalizationAwaySource
      (fun {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) =>
        letI := g.toAlgebra; Algebra.Unramified R S) := by
  intro R S T iR iS iT a r hloc g hg
  let := g.toAlgebra
  let : Algebra R T := (g.comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.Unramified R S := Algebra.Unramified.of_isLocalization_Away r
  exact Algebra.Unramified.comp R S T

/-- An unramified morphism of schemes is exactly one that is affine-locally given by unramified
maps on rings of sections. -/
public lemma unramified_iff_affineLocally {X S : Scheme.{u}} (f : X ⟶ S) :
    Unramified f ↔
      affineLocally (fun {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) =>
        letI := g.toAlgebra; Algebra.Unramified R S) f := by
  let Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop := fun
      {R S} _ _ g => let := g.toAlgebra; Algebra.Unramified R S
  let : HasRingHomProperty (affineLocally Q) Q := ⟨unramified_ringHom_propertyIsLocal, rfl⟩
  rw [unramified_iff, HasRingHomProperty.iff_exists_appLE (P := affineLocally Q)
    unramified_ringHom_stableUnderCompositionWithLocalizationAwaySource]
  constructor
  · intro h x
    obtain ⟨U, hU, hx, V, hV, e, he⟩ := h x
    exact ⟨⟨V, hV⟩, ⟨U, hU⟩, hx, e, he⟩
  · intro h x
    obtain ⟨U, V, hx, e, he⟩ := h x
    exact ⟨V.1, V.2, hx, U.1, U.2, e, he⟩

/-- Unramifiedness of scheme morphisms is the affine-local property attached to the conjunction
of formal unramifiedness and local finite type of ring maps. -/
public instance hasRingHomProperty_unramified :
    HasRingHomProperty (fun {X S : Scheme.{u}} (f : X ⟶ S) ↦ Unramified f)
      (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) ↦
        f.FormallyUnramified ∧ f.FiniteType) := by
  refine ⟨RingHom.FormallyUnramified.propertyIsLocal.and RingHom.finiteType_isLocal, ?_⟩
  ext X S f
  rw [unramified_iff_affineLocally]
  simp only [affineLocally_iff_forall_isAffineOpen]
  constructor
  · intro h U hU V hV e
    let : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V e).hom.toAlgebra
    have hu := h hU hV e
    exact ⟨RingHom.formallyUnramified_algebraMap.mpr hu.formallyUnramified,
      RingHom.finiteType_algebraMap.mpr hu.finiteType⟩
  · intro h U hU V hV e
    let : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V e).hom.toAlgebra
    have hu := h hU hV e
    exact ⟨RingHom.formallyUnramified_algebraMap.mp hu.1,
      RingHom.finiteType_algebraMap.mp hu.2⟩

/-- A morphism property local at the source and the target holds for `f` once it holds for the
restrictions of `f` to an open cover of the target and open covers of the preimages. -/
private theorem IsZariskiLocalAtSource.of_isOpenCover_resLE {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtSource P] [IsZariskiLocalAtTarget P] [P.RespectsRight @IsOpenImmersion]
    {X S : Scheme.{u}} {f : X ⟶ S} {J : Type u} {V : J → S.Opens} (hV : IsOpenCover V)
    (hU : ∀ j, ∃ (I : Type u) (U : I → X.Opens) (hU : (⨆ i, U i) = f ⁻¹ᵁ V j),
      ∀ i, P (f.resLE (V j) (U i) ((le_iSup U i).trans hU.le))) :
    P f := by
  refine (IsZariskiLocalAtSource.iff_exists_resLE (P := P)).mpr fun x => ?_
  obtain ⟨j, hj⟩ : ∃ j, f x ∈ V j := by
    simpa using (show f x ∈ ⨆ j, V j from (by rw [hV]; trivial))
  obtain ⟨I, U, hUeq, hP⟩ := hU j
  obtain ⟨i, hi⟩ : ∃ i, x ∈ U i := by
    simpa using (show x ∈ ⨆ i, U i from (by rw [hUeq]; exact hj))
  exact ⟨V j, U i, hi, _, hP i⟩

/-- The four characterizations of an unramified morphism: the global condition, the condition on
every compatible pair of affine opens, an open-covering criterion, and an affine-open-covering
criterion on rings of sections. -/
@[stacks 02G6 "unramified characterization"]
public theorem unramified_tfae {X S : Scheme.{u}} (f : X ⟶ S) :
    List.TFAE [
      Unramified f,
      ∀ (U : X.Opens) (_ : IsAffineOpen U) (V : S.Opens) (_ : IsAffineOpen V)
        (hUV : U ≤ f ⁻¹ᵁ V),
        letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
        Algebra.Unramified Γ(S, V) Γ(X, U),
      ∃ (J : Type u) (V : J → S.Opens),
        IsOpenCover V ∧
          ∀ j, ∃ (I : Type u) (U : I → X.Opens)
            (hU : (⨆ i, U i) = f ⁻¹ᵁ V j),
            ∀ i, Unramified
              (f.resLE (V j) (U i) ((le_iSup U i).trans hU.le)),
      ∃ (J : Type u) (V : J → S.Opens),
        IsOpenCover V ∧
          (∀ j, IsAffineOpen (V j)) ∧
          ∀ j, ∃ (I : Type u) (U : I → X.Opens)
            (hU : (⨆ i, U i) = f ⁻¹ᵁ V j),
            (∀ i, IsAffineOpen (U i)) ∧
              ∀ i,
                let hUV : U i ≤ f ⁻¹ᵁ V j := (le_iSup U i).trans hU.le
                letI : Algebra Γ(S, V j) Γ(X, U i) := (f.appLE (V j) (U i) hUV).hom.toAlgebra
                Algebra.Unramified Γ(S, V j) Γ(X, U i)] := by
  let Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop := fun
      {R S} _ _ g => let := g.toAlgebra; Algebra.Unramified R S
  let P : MorphismProperty Scheme.{u} := affineLocally Q
  have h12 : Unramified f ↔ P f := unramified_iff_affineLocally f
  let : HasRingHomProperty P Q := ⟨unramified_ringHom_propertyIsLocal, rfl⟩
  have : P.Respects @IsOpenImmersion := HasRingHomProperty.respects_isOpenImmersion (P := P)
    unramified_ringHom_stableUnderCompositionWithLocalizationAwaySource
  tfae_have 1 ↔ 2 := by
    rw [h12]
    change affineLocally Q f ↔ _
    rw [affineLocally_iff_forall_isAffineOpen]
    constructor
    · intro h U hU V hV e
      exact h hV hU e
    · intro h V hV U hU e
      exact h U hU V hV e
  tfae_have 1 ↔ 3 := by
    constructor
    · intro hf
      refine ⟨ULift.{u} Unit, fun _ => ⊤, ?_, fun _ => ?_⟩
      · simp [IsOpenCover]
      · exact ⟨X.affineOpens, fun U => U.1, iSup_affineOpens_eq_top X, fun U =>
          (unramified_iff_affineLocally _).mpr
            (IsZariskiLocalAtSource.resLE (P := P) (by simp) (h12.mp hf))⟩
    · rintro ⟨J, V, hV, hU⟩
      refine h12.mpr (IsZariskiLocalAtSource.of_isOpenCover_resLE (P := P) hV fun j => ?_)
      obtain ⟨I, U, hUeq, hP⟩ := hU j
      exact ⟨I, U, hUeq, fun i => (unramified_iff_affineLocally _).mp (hP i)⟩
  tfae_have 1 ↔ 4 := by
    constructor
    · intro hf
      refine ⟨S.affineOpens, fun V => V.1, iSup_affineOpens_eq_top S,
        fun V => V.2, fun V => ?_⟩
      let U : { U : X.affineOpens // U.1 ≤ f ⁻¹ᵁ V.1 } → X.Opens := fun i => i.1.1
      have hU : (⨆ i, U i) = f ⁻¹ᵁ V.1 := by
        refine le_antisymm (iSup_le fun i => i.2) fun x hx => ?_
        obtain ⟨W, hW, hxW, hWle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
        exact (le_iSup U ⟨⟨W, hW⟩, hWle⟩) hxW
      exact ⟨_, U, hU, fun i => i.1.2, fun i => tfae_1_iff_2.mp hf (U i) i.1.2 V.1 V.2 _⟩
    · rintro ⟨J, V, hV, hVa, hU⟩
      refine h12.mpr (IsZariskiLocalAtSource.of_isOpenCover_resLE (P := P) hV fun j => ?_)
      obtain ⟨I, U, hUeq, hUa, hP⟩ := hU j
      refine ⟨I, U, hUeq, fun i => ?_⟩
      have : IsAffine (U i) := hUa i
      have : IsAffine (V j) := hVa j
      rw [HasRingHomProperty.iff_of_isAffine (P := P)]
      exact (unramified_ringHom_propertyIsLocal.respectsIso.arrow_mk_iso_iff
        (arrowResLEAppIso f (V j) (U i) _)).mpr (hP i)
  tfae_finish

/-- G-unramifiedness of a ring homomorphism, as a property of the induced algebra, is local. -/
public theorem gUnramified_ringHom_propertyIsLocal : RingHom.PropertyIsLocal
    (fun {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) =>
      letI := g.toAlgebra; Algebra.GUnramified R S) := by
  let Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop := fun
      {R S} _ _ g => let := g.toAlgebra; Algebra.GUnramified R S
  let Q' : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop :=
      fun g => RingHom.FormallyUnramified g ∧ RingHom.FinitePresentation g
  have e : @Q = @Q' := by
    funext R S iR iS g
    let := g.toAlgebra
    exact propext ⟨fun h => ⟨h.formallyUnramified, h.finitePresentation⟩,
      fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩
  change RingHom.PropertyIsLocal Q
  rw [e]
  exact RingHom.FormallyUnramified.propertyIsLocal.and RingHom.finitePresentation_isLocal

/-- G-unramifiedness of a ring homomorphism is stable under precomposition with a localization
away from an element of the source. -/
public theorem gUnramified_ringHom_stableUnderCompositionWithLocalizationAwaySource :
    RingHom.StableUnderCompositionWithLocalizationAwaySource
      (fun {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) =>
        letI := g.toAlgebra; Algebra.GUnramified R S) := by
  intro R S T iR iS iT a r hloc g hg
  let := g.toAlgebra
  let : Algebra R T := (g.comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.GUnramified R S := Algebra.GUnramified.of_isLocalization_Away r
  exact Algebra.GUnramified.comp R S T

/-- A G-unramified morphism of schemes is exactly one that is affine-locally given by
G-unramified maps on rings of sections. -/
public lemma gUnramified_iff_affineLocally {X S : Scheme.{u}} (f : X ⟶ S) :
    GUnramified f ↔
      affineLocally (fun {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) =>
        letI := g.toAlgebra; Algebra.GUnramified R S) f := by
  let Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop := fun
      {R S} _ _ g => let := g.toAlgebra; Algebra.GUnramified R S
  let : HasRingHomProperty (affineLocally Q) Q := ⟨gUnramified_ringHom_propertyIsLocal, rfl⟩
  rw [gUnramified_iff, HasRingHomProperty.iff_exists_appLE (P := affineLocally Q)
    gUnramified_ringHom_stableUnderCompositionWithLocalizationAwaySource]
  constructor
  · intro h x
    obtain ⟨U, hU, hx, V, hV, e, he⟩ := h x
    exact ⟨⟨V, hV⟩, ⟨U, hU⟩, hx, e, he⟩
  · intro h x
    obtain ⟨U, V, hx, e, he⟩ := h x
    exact ⟨V.1, V.2, hx, U.1, U.2, e, he⟩

/-- G-unramifiedness of scheme morphisms is the affine-local property attached to the conjunction
of formal unramifiedness and local finite presentation of ring maps. -/
@[ega "IV 17.3.1"]
public instance hasRingHomProperty_gUnramified :
    HasRingHomProperty (fun {X S : Scheme.{u}} (f : X ⟶ S) ↦ GUnramified f)
      (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) ↦
        f.FormallyUnramified ∧ f.FinitePresentation) := by
  refine ⟨RingHom.FormallyUnramified.propertyIsLocal.and
    RingHom.finitePresentation_isLocal, ?_⟩
  ext X S f
  rw [gUnramified_iff_affineLocally]
  simp only [affineLocally_iff_forall_isAffineOpen]
  constructor
  · intro h U hU V hV e
    let : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V e).hom.toAlgebra
    have hu := h hU hV e
    exact ⟨RingHom.formallyUnramified_algebraMap.mpr hu.formallyUnramified,
      RingHom.finitePresentation_algebraMap.mpr hu.finitePresentation⟩
  · intro h U hU V hV e
    let : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V e).hom.toAlgebra
    have hu := h hU hV e
    exact ⟨RingHom.formallyUnramified_algebraMap.mp hu.1,
      RingHom.finitePresentation_algebraMap.mp hu.2⟩

/-- The four characterizations of a G-unramified morphism: the global condition, the condition on
every compatible pair of affine opens, an open-covering criterion, and an affine-open-covering
criterion on rings of sections. -/
@[stacks 02G6 "G-unramified characterization"]
public theorem gUnramified_tfae {X S : Scheme.{u}} (f : X ⟶ S) :
    List.TFAE [
      GUnramified f,
      ∀ (U : X.Opens) (_ : IsAffineOpen U) (V : S.Opens) (_ : IsAffineOpen V)
        (hUV : U ≤ f ⁻¹ᵁ V),
        letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
        Algebra.GUnramified Γ(S, V) Γ(X, U),
      ∃ (J : Type u) (V : J → S.Opens),
        IsOpenCover V ∧
          ∀ j, ∃ (I : Type u) (U : I → X.Opens)
            (hU : (⨆ i, U i) = f ⁻¹ᵁ V j),
            ∀ i, GUnramified
              (f.resLE (V j) (U i) ((le_iSup U i).trans hU.le)),
      ∃ (J : Type u) (V : J → S.Opens),
        IsOpenCover V ∧
          (∀ j, IsAffineOpen (V j)) ∧
          ∀ j, ∃ (I : Type u) (U : I → X.Opens)
            (hU : (⨆ i, U i) = f ⁻¹ᵁ V j),
            (∀ i, IsAffineOpen (U i)) ∧
              ∀ i,
                let hUV : U i ≤ f ⁻¹ᵁ V j := (le_iSup U i).trans hU.le
                letI : Algebra Γ(S, V j) Γ(X, U i) := (f.appLE (V j) (U i) hUV).hom.toAlgebra
                Algebra.GUnramified Γ(S, V j) Γ(X, U i)] := by
  let Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop := fun
      {R S} _ _ g => let := g.toAlgebra; Algebra.GUnramified R S
  let P : MorphismProperty Scheme.{u} := affineLocally Q
  have h12 : GUnramified f ↔ P f := gUnramified_iff_affineLocally f
  let : HasRingHomProperty P Q := ⟨gUnramified_ringHom_propertyIsLocal, rfl⟩
  have : P.Respects @IsOpenImmersion := HasRingHomProperty.respects_isOpenImmersion (P := P)
    gUnramified_ringHom_stableUnderCompositionWithLocalizationAwaySource
  tfae_have 1 ↔ 2 := by
    rw [h12]
    change affineLocally Q f ↔ _
    rw [affineLocally_iff_forall_isAffineOpen]
    constructor
    · intro h U hU V hV e
      exact h hV hU e
    · intro h V hV U hU e
      exact h U hU V hV e
  tfae_have 1 ↔ 3 := by
    constructor
    · intro hf
      refine ⟨ULift.{u} Unit, fun _ => ⊤, ?_, fun _ => ?_⟩
      · simp [IsOpenCover]
      · exact ⟨X.affineOpens, fun U => U.1, iSup_affineOpens_eq_top X, fun U =>
          (gUnramified_iff_affineLocally _).mpr
            (IsZariskiLocalAtSource.resLE (P := P) (by simp) (h12.mp hf))⟩
    · rintro ⟨J, V, hV, hU⟩
      refine h12.mpr (IsZariskiLocalAtSource.of_isOpenCover_resLE (P := P) hV fun j => ?_)
      obtain ⟨I, U, hUeq, hP⟩ := hU j
      exact ⟨I, U, hUeq, fun i => (gUnramified_iff_affineLocally _).mp (hP i)⟩
  tfae_have 1 ↔ 4 := by
    constructor
    · intro hf
      refine ⟨S.affineOpens, fun V => V.1, iSup_affineOpens_eq_top S,
        fun V => V.2, fun V => ?_⟩
      let U : { U : X.affineOpens // U.1 ≤ f ⁻¹ᵁ V.1 } → X.Opens := fun i => i.1.1
      have hU : (⨆ i, U i) = f ⁻¹ᵁ V.1 := by
        refine le_antisymm (iSup_le fun i => i.2) fun x hx => ?_
        obtain ⟨W, hW, hxW, hWle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
        exact (le_iSup U ⟨⟨W, hW⟩, hWle⟩) hxW
      exact ⟨_, U, hU, fun i => i.1.2, fun i => tfae_1_iff_2.mp hf (U i) i.1.2 V.1 V.2 _⟩
    · rintro ⟨J, V, hV, hVa, hU⟩
      refine h12.mpr (IsZariskiLocalAtSource.of_isOpenCover_resLE (P := P) hV fun j => ?_)
      obtain ⟨I, U, hUeq, hUa, hP⟩ := hU j
      refine ⟨I, U, hUeq, fun i => ?_⟩
      have : IsAffine (U i) := hUa i
      have : IsAffine (V j) := hVa j
      rw [HasRingHomProperty.iff_of_isAffine (P := P)]
      exact (gUnramified_ringHom_propertyIsLocal.respectsIso.arrow_mk_iso_iff
        (arrowResLEAppIso f (V j) (U i) _)).mpr (hP i)
  tfae_finish

/-- Restricting an unramified morphism to compatible open subschemes of its source and target
is unramified. -/
@[stacks 02G6 "restriction of an unramified morphism"]
public theorem unramified_resLE {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : Unramified f) (U : X.Opens) (V : S.Opens) (hUV : U ≤ f ⁻¹ᵁ V) :
    Unramified (f.resLE V U hUV) := by
  let Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop := fun
      {R S} _ _ g => let := g.toAlgebra; Algebra.Unramified R S
  let P : MorphismProperty Scheme.{u} := affineLocally Q
  let : HasRingHomProperty P Q := ⟨unramified_ringHom_propertyIsLocal, rfl⟩
  exact (unramified_iff_affineLocally _).mpr
    (IsZariskiLocalAtSource.resLE (P := P) hUV ((unramified_iff_affineLocally f).mp hf))

/-- Restricting a G-unramified morphism to compatible open subschemes of its source and target
is G-unramified. -/
@[stacks 02G6 "restriction of a G-unramified morphism"]
public theorem gUnramified_resLE {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : GUnramified f) (U : X.Opens) (V : S.Opens) (hUV : U ≤ f ⁻¹ᵁ V) :
    GUnramified (f.resLE V U hUV) := by
  let Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop := fun
      {R S} _ _ g => let := g.toAlgebra; Algebra.GUnramified R S
  let P : MorphismProperty Scheme.{u} := affineLocally Q
  let : HasRingHomProperty P Q := ⟨gUnramified_ringHom_propertyIsLocal, rfl⟩
  exact (gUnramified_iff_affineLocally _).mpr
    (IsZariskiLocalAtSource.resLE (P := P) hUV ((gUnramified_iff_affineLocally f).mp hf))

end AlgebraicGeometry
