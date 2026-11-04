module

public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.EtaleSmoothProperties

/-!
# Criteria for an étale-smooth local property (Stacks 0CG1)

Let `S` be a scheme contained in a big fppf site `B`, let `P` be a property of morphisms of
algebraic spaces over `S` which is étale-smooth local on the source-and-target
(`AlgebraicGeometry.Space.IsEtaleSmoothLocalOnSourceAndTarget`, **Stacks 0CFZ**), and let
`f : X ⟶ Y` be a morphism of algebraic spaces over `S`. Seven conditions on `f` are then
equivalent: `P f` itself; a pointwise condition; two diagrammatic conditions, one existential
and one universal, over an étale neighbourhood of a smooth base change; and three conditions
phrased with covering families of the target, of the source, and of the base changes.

This is the étale-smooth analogue of **Stacks 06FA**, and it is the list of criteria the
Deligne–Mumford results of **Stacks 0CIF** and above select from.

## Main results

* `AlgebraicGeometry.Space.etaleSmoothLocalOnSourceAndTarget_tfae`: **Stacks 0CG1**.

## Implementation notes

The hub of the equivalence is `P f`, and every item is compared with it directly, via
`List.TFAE` and the `tfae_have`/`tfae_finish` tactics. The pointwise item is literally the third
clause of `IsEtaleSmoothLocalOnSourceAndTarget`, so item 1 ↔ item 2 is that clause; the two
locality statements of **Stacks 0CG0** supply the two covering items whose implications towards
`P f` are genuine descent, and the remaining implications produce a degenerate witness: the
identity of `Y` as the smooth target neighbourhood, the constant family at `X` or `Y` as the
covering family.

Taking the identity of `Y` as the target neighbourhood makes the first projection of the fibre
product an isomorphism, which is `AlgebraicGeometry.Space.pullbackIdIso` below; the two lemmas
after it record its composites with the two projections, and they are what turns the degenerate
witness into a statement about `f`.

The index types of the covering families in the last three items are in `Type (u + 1)`, which
is the universe of `AlgebraicGeometry.Space.points`, matching the instantiation of
`AlgebraicGeometry.Space.Topology.precoverage` used by the two locality statements of
Stacks 0CG0.

## References

* [Stacks Project, Tag 0CG1](https://stacks.math.columbia.edu/tag/0CG1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Base change of a morphism of algebraic spaces over `S` along the identity of its target
does nothing: the first projection of `X ×_Y Y` is an isomorphism, and this is its inverse. -/
noncomputable def pullbackIdIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    X ≅ AlgebraicSpaces.fiberProduct B S hS f (𝟙 Y) :=
  haveI : IsIso (ObjectProperty.homMk (pullback.fst f.hom ((𝟙 Y : Y ⟶ Y).hom)) :
      AlgebraicSpaces.fiberProduct B S hS f (𝟙 Y) ⟶ X) :=
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f (𝟙 Y)).isIso_fst_of_isIso
  (asIso (ObjectProperty.homMk (pullback.fst f.hom ((𝟙 Y : Y ⟶ Y).hom)) :
    AlgebraicSpaces.fiberProduct B S hS f (𝟙 Y) ⟶ X)).symm

/-- `AlgebraicGeometry.Space.pullbackIdIso` is a section of the first projection. -/
theorem pullbackIdIso_hom_fst {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (pullbackIdIso B S hS f).hom ≫
      (ObjectProperty.homMk (pullback.fst f.hom ((𝟙 Y : Y ⟶ Y).hom)) :
        AlgebraicSpaces.fiberProduct B S hS f (𝟙 Y) ⟶ X) = 𝟙 X := by
  simp [pullbackIdIso]

/-- Composing `AlgebraicGeometry.Space.pullbackIdIso` with the second projection returns the
morphism that was base changed. -/
theorem pullbackIdIso_hom_snd {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (pullbackIdIso B S hS f).hom ≫
      (ObjectProperty.homMk (pullback.snd f.hom ((𝟙 Y : Y ⟶ Y).hom)) :
        AlgebraicSpaces.fiberProduct B S hS f (𝟙 Y) ⟶ Y) = f := by
  have h : (ObjectProperty.homMk (pullback.fst f.hom ((𝟙 Y : Y ⟶ Y).hom)) :
        AlgebraicSpaces.fiberProduct B S hS f (𝟙 Y) ⟶ X) ≫ f =
      (ObjectProperty.homMk (pullback.snd f.hom ((𝟙 Y : Y ⟶ Y).hom)) :
        AlgebraicSpaces.fiberProduct B S hS f (𝟙 Y) ⟶ Y) := by
    simpa using (AlgebraicSpaces.isPullback_fiberProduct B S hS f (𝟙 Y)).w
  rw [← h, ← Category.assoc, pullbackIdIso_hom_fst, Category.id_comp]

/-- A property of morphisms of algebraic spaces over `S` which is local at the source for the
étale topology descends along an étale covering of the source. -/
private theorem of_etaleCovering
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtSource (Topology.precoverage.{u, u + 1} .etale B S hS)]
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {I : Type (u + 1)} (U : I → AlgebraicSpaces B S hS) (a : ∀ i, U i ⟶ X)
    (hcov : IsEtaleCovering B S hS (fun i => (U i).1) (fun i => (a i).hom))
    (hPi : ∀ i, P (a i ≫ f)) : P f := by
  have hR : Presieve.ofArrows U a ∈
      (Topology.precoverage.{u, u + 1} .etale B S hS).coverings X :=
    ⟨I, U, a, rfl, hcov.target_isAlgebraicSpace, hcov.source_isAlgebraicSpace, hcov⟩
  refine MorphismProperty.IsLocalAtSource.of_forall_comp (P := P) (f := f) hR ?_
  rintro Z g ⟨i⟩
  exact hPi i

/-- **Stacks 0CG1.** Seven equivalent criteria for a morphism `f : X ⟶ Y` of algebraic spaces
over `S` to have a property which is étale-smooth local on the source-and-target: the property
itself; an étale neighbourhood over a smooth target neighbourhood on which it holds above every
point of the source; one such neighbourhood surjective onto the source; every such
neighbourhood; a smooth covering of the target whose base changes have it; an étale covering of
the source whose composites have it; and a smooth covering of the target together with étale
coverings of the corresponding fibre products. -/
@[stacks 0CG1]
theorem etaleSmoothLocalOnSourceAndTarget_tfae
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : IsEtaleSmoothLocalOnSourceAndTarget B S hS P)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    List.TFAE [
      P f,
      (∀ x : points B S hS X.1,
        ∃ (V U : AlgebraicSpaces B S hS)
          (b : V ⟶ Y)
          (e : U ⟶ AlgebraicSpaces.fiberProduct B S hS f b)
          (v : points B S hS U.1),
          IsSmooth B S hS b.hom ∧
          IsEtale B S hS e.hom ∧
          pointsMap B S hS U.1
            (e ≫ (ObjectProperty.homMk (pullback.fst f.hom b.hom) :
              AlgebraicSpaces.fiberProduct B S hS f b ⟶ X)).hom v = x ∧
          P (e ≫ (ObjectProperty.homMk (pullback.snd f.hom b.hom) :
            AlgebraicSpaces.fiberProduct B S hS f b ⟶ V))),
      (∃ (V U : AlgebraicSpaces B S hS)
        (b : V ⟶ Y)
        (e : U ⟶ AlgebraicSpaces.fiberProduct B S hS f b),
        IsSmooth B S hS b.hom ∧
        IsEtale B S hS e.hom ∧
        IsSurjective B S hS
          (e ≫ (ObjectProperty.homMk (pullback.fst f.hom b.hom) :
            AlgebraicSpaces.fiberProduct B S hS f b ⟶ X)).hom ∧
        P (e ≫ (ObjectProperty.homMk (pullback.snd f.hom b.hom) :
          AlgebraicSpaces.fiberProduct B S hS f b ⟶ V))),
      (∀ (V U : AlgebraicSpaces B S hS)
        (b : V ⟶ Y)
        (e : U ⟶ AlgebraicSpaces.fiberProduct B S hS f b),
        IsSmooth B S hS b.hom →
        IsEtale B S hS e.hom →
        P (e ≫ (ObjectProperty.homMk (pullback.snd f.hom b.hom) :
          AlgebraicSpaces.fiberProduct B S hS f b ⟶ V))),
      (∃ (I : Type (u + 1))
        (V : I → AlgebraicSpaces B S hS)
        (b : ∀ i, V i ⟶ Y),
        IsSmoothCovering B S hS (fun i => (V i).1) (fun i => (b i).hom) ∧
        ∀ i, P (ObjectProperty.homMk (pullback.snd f.hom (b i).hom) :
          AlgebraicSpaces.fiberProduct B S hS f (b i) ⟶ V i)),
      (∃ (I : Type (u + 1))
        (U : I → AlgebraicSpaces B S hS)
        (a : ∀ i, U i ⟶ X),
        IsEtaleCovering B S hS (fun i => (U i).1) (fun i => (a i).hom) ∧
        ∀ i, P ((a i) ≫ f)),
      (∃ (I : Type (u + 1))
        (V : I → AlgebraicSpaces B S hS)
        (b : ∀ i, V i ⟶ Y)
        (J : I → Type (u + 1))
        (U : ∀ i, J i → AlgebraicSpaces B S hS)
        (e : ∀ i j, U i j ⟶ AlgebraicSpaces.fiberProduct B S hS f (b i)),
        IsSmoothCovering B S hS (fun i => (V i).1) (fun i => (b i).hom) ∧
        ∀ i, IsEtaleCovering B S hS (fun j => (U i j).1) (fun j => (e i j).hom) ∧
          ∀ j, P (e i j ≫
            (ObjectProperty.homMk (pullback.snd f.hom (b i).hom) :
              AlgebraicSpaces.fiberProduct B S hS f (b i) ⟶ V i)))] := by
  let : P.RespectsIso := hP.respectsIso
  let : P.IsLocalAtSource (Topology.precoverage.{u, u + 1} .etale B S hS) :=
    isLocalAtSource_etale B S hS P hP
  let : P.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .smooth B S hS) :=
    isLocalAtTarget_smooth B S hS P hP
  have hb : IsSmooth B S hS (𝟙 Y : Y ⟶ Y).hom := isSmooth_id_presheaf B S hS Y.1
  have he : IsEtale B S hS (pullbackIdIso B S hS f).hom.hom :=
    isEtale_of_isIso B S hS (pullbackIdIso B S hS f).hom.hom
  tfae_have 1 ↔ 2 := hP.iff_forall_exists_etale_smooth_neighborhood f
  tfae_have 3 → 1 := by
    rintro ⟨V, U, b, e, hb, he, hsurj, hlocal⟩
    refine (hP.iff_forall_exists_etale_smooth_neighborhood f).mpr fun x => ?_
    obtain ⟨u, hu⟩ := hsurj x
    exact ⟨V, U, b, e, u, hb, he, hu, hlocal⟩
  tfae_have 1 → 4 := fun hf V U b e hb he =>
    hP.precomp_of_etale e (ObjectProperty.homMk (pullback.snd f.hom b.hom)) he
      (hP.pullbackSnd_of_smooth f hf b hb)
  tfae_have 1 → 3 := by
    intro hf
    refine ⟨Y, X, 𝟙 Y, (pullbackIdIso B S hS f).hom, hb, he, ?_, ?_⟩
    · show Function.Surjective (pointsMap B S hS X.1 _)
      rw [pullbackIdIso_hom_fst B S hS f]
      exact (pointsMap_id ..).symm ▸ Function.surjective_id
    · rwa [pullbackIdIso_hom_snd]
  tfae_have 4 → 1 := by
    intro hd
    have h := hd Y X (𝟙 Y) (pullbackIdIso B S hS f).hom hb he
    rwa [pullbackIdIso_hom_snd] at h
  tfae_have 1 → 5 := fun hf =>
    ⟨ULift.{u + 1} Unit, fun _ => Y, fun _ => 𝟙 Y,
      isSmoothCovering_const_id B S hS Y.1 Y.property,
      fun _ => hP.pullbackSnd_of_smooth f hf (𝟙 Y) hb⟩
  tfae_have 1 → 6 := fun hf =>
    ⟨ULift.{u + 1} Unit, fun _ => X, fun _ => 𝟙 X,
      isEtaleCovering_const_id B S hS X.1 X.property, fun _ => by simpa using hf⟩
  tfae_have 5 → 7 := by
    rintro ⟨I, V, b, hcov, hPi⟩
    refine ⟨I, V, b, fun _ => ULift.{u + 1} Unit,
      fun i _ => AlgebraicSpaces.fiberProduct B S hS f (b i), fun _ _ => 𝟙 _, hcov, fun i => ?_⟩
    exact ⟨isEtaleCovering_const_id B S hS _ (AlgebraicSpaces.fiberProduct B S hS f (b i)).property,
      fun _ => by simpa using hPi i⟩
  tfae_have 5 → 1 := by
    rintro ⟨I, V, b, hcov, hPi⟩
    have hR : Presieve.ofArrows V b ∈
        (Topology.precoverage.{u, u + 1} .smooth B S hS).coverings Y :=
      ⟨I, V, b, rfl, hcov.target_isAlgebraicSpace, hcov.source_isAlgebraicSpace, hcov⟩
    refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd (P := P) (f := f) hR ?_
    rintro Z g _ ⟨i⟩
    exact (prop_pullbackSnd_iff_fibreProductSnd B S hS P f (b i)).mpr (hPi i)
  tfae_have 6 → 1 := by
    rintro ⟨I, U, a, hcov, hPi⟩
    exact of_etaleCovering B S hS P f U a hcov hPi
  tfae_have 7 → 5 := by
    rintro ⟨I, V, b, J, U, e, hVcov, hRest⟩
    exact ⟨I, V, b, hVcov, fun i =>
      of_etaleCovering B S hS P
        (ObjectProperty.homMk (pullback.snd f.hom (b i).hom) :
          AlgebraicSpaces.fiberProduct B S hS f (b i) ⟶ V i)
        (U i) (e i) (hRest i).1 (hRest i).2⟩
  tfae_finish

end AlgebraicGeometry.Space

end
