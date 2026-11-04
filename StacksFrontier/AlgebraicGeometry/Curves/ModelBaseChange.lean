module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.ModelGlobalSections
public import StacksFrontier.AlgebraicGeometry.Curves.ModelUniqueness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericStalkCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksCore.Tactic.StacksAttribute

/-!
# Nonsingular projective models under extension of the ground field

Let `k` be a field and let `X` be a geometrically irreducible curve over `k`. For a field
extension `K/k` write `Y_K` for a nonsingular projective model of the reduction `(X_K)_red` of
the base change of `X`. Given a commutative diagram of fields `Ω ← K'`, `K → Ω`, `k → K`,
`k → K'` in which `Y_K` and `Y_{K'}` are smooth, this file proves `Y_Ω = (Y_K)_Ω = (Y_{K'})_Ω`:
each base change is isomorphic to `Y_Ω` as a scheme over `Ω`.

The proof is the source's. A base change of a smooth morphism is smooth, so `(Y_K)_Ω` is a smooth
— hence regular — projective curve over `Ω`; it is birational to `(X_Ω)_red` over `Ω`; so it is a
nonsingular projective model of `(X_Ω)_red`, and such a model is unique up to isomorphism over
the base field.

## Main results

* `AlgebraicGeometry.isCurve_pullback_snd_of_smooth`: the base change of a smooth geometrically
  irreducible curve along an extension of the ground field is again a curve.
* `AlgebraicGeometry.birationalOver_iff_nonempty_functionFieldAlgEquiv`: two curves over a field
  are birational over it exactly when their function fields are isomorphic as algebras over it.
* `AlgebraicGeometry.exists_iso_pullback_of_smooth_model`: one leg of the source's statement —
  for a tower `Ω/K/k` and a smooth model `Y_K`, every nonsingular projective model of
  `(X_Ω)_red` is isomorphic to `(Y_K)_Ω` over `Ω`.
* `AlgebraicGeometry.exists_iso_pullback_of_smooth_models`: Tag 0BY4 part (4), both legs of the
  source's commutative diagram.

## Implementation notes

The commutative diagram of fields is the pair of scalar towers `k ⊆ K ⊆ Ω` and `k ⊆ K' ⊆ Ω`;
commutativity of the square is exactly the two `IsScalarTower` hypotheses. The source's equality
of schemes is a canonical isomorphism over `Ω`: compatibility with the structure morphisms is
part of the conclusion, and `AlgebraicGeometry.NonsingularProjectiveModel.hom_ext` says that the
isomorphism matching the birational identifications is unique, so no choice is hidden in the
statement.

That `(X_K)_red` is a curve over `K` is an instance argument rather than a derived fact, exactly
as in `AlgebraicGeometry.isIso_globalSections_of_smooth_model_reducedBaseChange`: it is
presupposed by the source's notation `Y_K` for a nonsingular projective model of `(X_K)_red`,
since a model is only defined for a curve.

Birationality is `AlgebraicGeometry.Scheme.BirationalOver`, and it is compared with isomorphism
of function fields through the generic-stalk criterion of [Stacks, Tag 0BAD]. The step that turns
compatibility with the structure morphisms into linearity over the base field is that the stalk
of the spectrum of a field at its unique point is a quotient of that field, so a map out of it is
determined by its restriction along the field.

The passage from `(X_K)_red ×_K Ω` to `(X_Ω)_red` is not an isomorphism — the base change of a
reduced scheme along an inseparable extension need not be reduced — but it is a surjective closed
immersion with reduced source, and that is enough: a reduced open subscheme of
`(X_K)_red ×_K Ω` factors through it, and an open immersion stays one after the factorization.

## References

* [Stacks Project, Tag 0BY4](https://stacks.math.columbia.edu/tag/0BY4)
* [Stacks Project, Tag 0BY2](https://stacks.math.columbia.edu/tag/0BY2), the model.
* [Stacks Project, Tag 0BY1](https://stacks.math.columbia.edu/tag/0BY1), its uniqueness.
* [Stacks Project, Tag 0BAD](https://stacks.math.columbia.edu/tag/0BAD), the criterion for
  birationality over a base.
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9), invariance of the
  dimension under extension of the ground field.
* [Stacks Project, Tag 0356](https://stacks.math.columbia.edu/tag/0356), factoring through the
  reduction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### The base change of a smooth curve along an extension of the ground field -/

/-- **The base change of a smooth geometrically irreducible curve along an extension of the
ground field is again a curve.** It is smooth over the larger field, hence regular, hence
reduced; it is irreducible because the curve is geometrically irreducible; and its dimension is
unchanged, which is the dimension clause of [Stacks, Tag 0BY9]. -/
public theorem isCurve_pullback_snd_of_smooth (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [GeometricallyIrreducible f]
    [Smooth f] :
    IsCurve K (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hreg : IsRegular (pullback f g : Scheme.{u}) :=
    isRegular_of_smooth_over_field (pullback.snd f g)
  have : IsNormal (pullback f g : Scheme.{u}) := isNormal_of_isRegular _ hreg
  have : IsReduced (pullback f g : Scheme.{u}) := isReduced_of_isReduced_stalk _
  have : IrreducibleSpace (pullback f g : Scheme.{u}) := inferInstance
  have : IsIntegral (pullback f g : Scheme.{u}) :=
    (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨inferInstance, inferInstance⟩
  have : IsVariety K (pullback.snd f g) := {}
  exact ⟨(topologicalKrullDim_baseChange k K (pullback.fst f g) (pullback.snd f g) f
    (IsPullback.of_hasPullback f g)).trans (IsCurve.topologicalKrullDim_eq_one f)⟩

/-! ### Birationality over a field and isomorphism of function fields -/

/-- The `k`-algebra structure map of the function field of a curve over `k`, read through
stalks: it is the map to the stalk of `Spec k` at the image of the generic point, followed by
the stalk map of the structure morphism. -/
private theorem algebraMap_functionField_eq_stalkMap (K : Type u) [Field K] {Z : Scheme.{u}}
    (sZ : Z ⟶ Spec (.of K)) [IsCurve K sZ] :
    @algebraMap K Z.functionField _ _ (functionFieldAlgebra K sZ) =
      (StructureSheaf.toStalk K (sZ (genericPoint Z)) ≫
        sZ.stalkMap (genericPoint Z)).hom := by
  rw [← varietyFunctionFieldAlgebra_eq_functionFieldAlgebra K sZ]
  rfl

/-- Over the spectrum of a field, two maps out of the stalk at a point agree exactly when they
agree after composing with the map from the field, since that map is surjective; stated with the
transport along an equality of points that the birationality criterion of [Stacks, Tag 0BAD]
carries. -/
private theorem transport_stalk_comp_iff (K : Type u) [Field K] {p q : Spec (.of K)} (h : p = q)
    {A B : CommRingCat.{u}} (f : (Spec (.of K)).presheaf.stalk p ⟶ A)
    (g : (Spec (.of K)).presheaf.stalk q ⟶ B) (φ : A ⟶ B) :
    (h ▸ (f ≫ φ) = g) ↔
      StructureSheaf.toStalk K p ≫ f ≫ φ = StructureSheaf.toStalk K q ≫ g := by
  subst h
  refine ⟨fun H => congrArg (fun t : (Spec (.of K)).presheaf.stalk p ⟶ B =>
    StructureSheaf.toStalk K p ≫ t) (show f ≫ φ = g from H), fun H => ?_⟩
  have hsurj : Function.Surjective (StructureSheaf.toStalk K p).hom :=
    fieldBaseStalkAlgebraMap_surjective (Subsingleton.elim _ _)
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  obtain ⟨a, rfl⟩ := hsurj r
  exact congrArg (fun t : CommRingCat.of K ⟶ B => t.hom a) H

/-- **Two curves over a field are birational over that field exactly when their function fields
are isomorphic as algebras over it.**

Birationality over the base is tested on the local rings at the generic points, which is
[Stacks, Tag 0BAD]; for a curve that local ring is the function field, and the structure map of
the base field into it factors through the stalk of the spectrum of the field at the image of the
generic point. That stalk is a quotient of the field — indeed the field itself — so a map out of
it is determined by its restriction along the field, which is what turns compatibility with the
structure maps of the base into `K`-linearity. -/
public theorem birationalOver_iff_nonempty_functionFieldAlgEquiv (K : Type u) [Field K]
    {Z Y : Scheme.{u}} (sZ : Z ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
    [IsCurve K sZ] [IsCurve K sY] :
    Scheme.BirationalOver sZ sY ↔
      Nonempty (letI : Algebra K Z.functionField := functionFieldAlgebra K sZ
        letI : Algebra K Y.functionField := functionFieldAlgebra K sY
        Z.functionField ≃ₐ[K] Y.functionField) := by
  let : Algebra K Z.functionField := functionFieldAlgebra K sZ
  let : Algebra K Y.functionField := functionFieldAlgebra K sY
  have : LocallyOfFinitePresentation sZ :=
    varietyStructureMap_locallyOfFinitePresentation (⟨Z, sZ⟩ : Variety K)
  have : LocallyOfFinitePresentation sY :=
    varietyStructureMap_locallyOfFinitePresentation (⟨Y, sY⟩ : Variety K)
  have hstalk := algebraMap_functionField_eq_stalkMap K sZ
  have hstalkY := algebraMap_functionField_eq_stalkMap K sY
  rw [birationalOver_iff_generic_stalk_iso sZ sY]
  constructor
  · rintro ⟨h, e, hcompat⟩
    have hring := (transport_stalk_comp_iff K h (sZ.stalkMap (genericPoint Z))
      (sY.stalkMap (genericPoint Y)) e.hom).mp hcompat
    refine ⟨AlgEquiv.ofRingEquiv (f := e.commRingCatIsoToRingEquiv) fun a => ?_⟩
    rw [hstalk, hstalkY]
    exact congrArg (fun t : CommRingCat.of K ⟶ Y.functionField => t.hom a) hring
  · rintro ⟨e⟩
    refine ⟨Subsingleton.elim _ _, e.toRingEquiv.toCommRingCatIso, ?_⟩
    refine (transport_stalk_comp_iff K (Subsingleton.elim _ _)
      (sZ.stalkMap (genericPoint Z)) (sY.stalkMap (genericPoint Y))
      e.toRingEquiv.toCommRingCatIso.hom).mpr ?_
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    have hc := e.commutes a
    rwa [hstalk, hstalkY] at hc

/-! ### Base change of morphisms over a base -/

/-- An open immersion with nonempty source into an irreducible scheme is dominant: its range is
a nonempty open subset of an irreducible space, hence dense. -/
private theorem isDominant_of_isOpenImmersion {U X : Scheme.{u}} (a : U ⟶ X)
    [IsOpenImmersion a] [Nonempty U] [IrreducibleSpace X] : IsDominant a :=
  ⟨a.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty a)⟩

/-- The base change along `g : T ⟶ S` of a morphism `a : U ⟶ Y` of schemes over `S`. -/
private noncomputable abbrev baseChangeHom {U Y S T : Scheme.{u}}
    (sU : U ⟶ S) (sY : Y ⟶ S) (g : T ⟶ S) (a : U ⟶ Y) (ha : a ≫ sY = sU) :
    pullback sU g ⟶ pullback sY g :=
  pullback.lift (pullback.fst sU g ≫ a) (pullback.snd sU g)
    (by simp only [Category.assoc, ha, pullback.condition])

/-- The base change of `a` along `g` is itself a base change of `a`. -/
private theorem isPullback_baseChangeHom {U Y S T : Scheme.{u}}
    (sU : U ⟶ S) (sY : Y ⟶ S) (g : T ⟶ S) (a : U ⟶ Y) (ha : a ≫ sY = sU) :
    IsPullback (baseChangeHom sU sY g a ha) (pullback.fst sU g) (pullback.fst sY g) a := by
  have h : IsPullback (baseChangeHom sU sY g a ha ≫ pullback.snd sY g)
      (pullback.fst sU g) g (a ≫ sY) := by
    simpa only [baseChangeHom, pullback.lift_snd, ha] using (IsPullback.of_hasPullback sU g).flip
  exact h.of_right (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback sY g).flip

/-- The base change of an open immersion is an open immersion. -/
private theorem isOpenImmersion_baseChangeHom {U Y S T : Scheme.{u}}
    (sU : U ⟶ S) (sY : Y ⟶ S) (g : T ⟶ S) (a : U ⟶ Y) (ha : a ≫ sY = sU)
    [IsOpenImmersion a] : IsOpenImmersion (baseChangeHom sU sY g a ha) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (isPullback_baseChangeHom sU sY g a ha).flip inferInstance

/-- The base change of a closed immersion is a closed immersion. -/
private theorem isClosedImmersion_baseChangeHom {U Y S T : Scheme.{u}}
    (sU : U ⟶ S) (sY : Y ⟶ S) (g : T ⟶ S) (a : U ⟶ Y) (ha : a ≫ sY = sU)
    [IsClosedImmersion a] : IsClosedImmersion (baseChangeHom sU sY g a ha) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_baseChangeHom sU sY g a ha).flip inferInstance

/-- In a tower of fields `k ⊆ K ⊆ Ω` the induced morphisms of spectra commute. -/
private theorem specMap_algebraMap_comp (k K Ω : Type u) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω] :
    Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k K)) =
      Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact (IsScalarTower.algebraMap_apply k K Ω a).symm

/-- A morphism out of a reduced scheme into a reduced base change factors through any surjective
closed immersion onto its target, and the factorization of an open immersion is again an open
immersion: the pullback of the closed immersion along it is a surjective closed immersion onto a
reduced scheme, hence an isomorphism. -/
@[sga "3 X 8.9" "partial"]
private theorem exists_isOpenImmersion_lift_of_isClosedImmersion_of_surjective
    {U R T : Scheme.{u}} (a : U ⟶ T) (q : R ⟶ T)
    [IsOpenImmersion a] [IsClosedImmersion q] [Surjective q] [IsReduced U] :
    ∃ b : U ⟶ R, IsOpenImmersion b ∧ b ≫ q = a := by
  have : IsIso (pullback.fst a q) := isIso_of_isClosedImmersion_of_surjective _
  refine ⟨inv (pullback.fst a q) ≫ pullback.snd a q, inferInstance, ?_⟩
  rw [Category.assoc, ← pullback.condition]
  simp

/-! ### Factoring through a reduction -/

/-- A morphism from a reduced scheme factors through the reduction of its target, which is
[Stacks, Tag 0356] phrased for `AlgebraicGeometry.Scheme.reduction`. -/
@[ega "I 5.1.5"]
private theorem exists_lift_reductionι {Y Z : Scheme.{u}} [IsReduced Y] (f : Y ⟶ Z) :
    ∃ b : Y ⟶ Z.reduction, b ≫ Z.reductionι = f := by
  obtain ⟨b, hb, -⟩ := Scheme.existsUnique_lift_nilradical_subschemeι f
  exact ⟨b, hb⟩

/-! ### The comparison of reduced base changes along a tower -/

/-- Along a commuting triangle `g ≫ gK = gΩ` of base changes, the reduction of the base change
of `Z` along `gΩ` maps canonically to the reduction of the base change along `gK`: the reduction
maps to the base change along `gK` by the universal property of the fibre product, and its source
is reduced, so that map factors through the reduction of the target. -/
private theorem exists_reductionBaseChangeProjection {S T T' Z : Scheme.{u}}
    (sZ : Z ⟶ S) (gK : T ⟶ S) (gΩ : T' ⟶ S) (g : T' ⟶ T) (hcomp : g ≫ gK = gΩ) :
    ∃ pZ : (pullback sZ gΩ).reduction ⟶ (pullback sZ gK).reduction,
      pZ ≫ (pullback sZ gK).reductionι ≫ pullback.fst sZ gK =
        (pullback sZ gΩ).reductionι ≫ pullback.fst sZ gΩ ∧
      pZ ≫ ((pullback sZ gK).reductionι ≫ pullback.snd sZ gK) =
        ((pullback sZ gΩ).reductionι ≫ pullback.snd sZ gΩ) ≫ g := by
  obtain ⟨pZ, hpZ⟩ := exists_lift_reductionι (Z := pullback sZ gK)
    ((pullback sZ gΩ).reductionι ≫
      pullback.lift (pullback.fst sZ gΩ) (pullback.snd sZ gΩ ≫ g)
        (by rw [Category.assoc, hcomp, pullback.condition]))
  refine ⟨pZ, ?_, ?_⟩
  · rw [← Category.assoc, hpZ, Category.assoc, pullback.lift_fst]
  · rw [← Category.assoc, hpZ, Category.assoc, pullback.lift_snd]
    exact (Category.assoc _ _ _).symm

/-- The comparison of the reduction of the base change along `gΩ` with the base change along `g`
of the reduction of the base change along `gK` is a **surjective closed immersion**: composed
with the closed immersion of that base change into the base change along `gΩ`, it is the closed
immersion of the reduction, which is surjective. -/
private theorem isClosedImmersion_and_surjective_reductionComparison {S T T' Z : Scheme.{u}}
    (sZ : Z ⟶ S) (gK : T ⟶ S) (gΩ : T' ⟶ S) (g : T' ⟶ T) (hcomp : g ≫ gK = gΩ)
    (pZ : (pullback sZ gΩ).reduction ⟶ (pullback sZ gK).reduction)
    (hp₁ : pZ ≫ (pullback sZ gK).reductionι ≫ pullback.fst sZ gK =
      (pullback sZ gΩ).reductionι ≫ pullback.fst sZ gΩ)
    (hp₂ : pZ ≫ ((pullback sZ gK).reductionι ≫ pullback.snd sZ gK) =
      ((pullback sZ gΩ).reductionι ≫ pullback.snd sZ gΩ) ≫ g) :
    IsClosedImmersion
        (pullback.lift pZ ((pullback sZ gΩ).reductionι ≫ pullback.snd sZ gΩ) hp₂) ∧
      Surjective
        (pullback.lift pZ ((pullback sZ gΩ).reductionι ≫ pullback.snd sZ gΩ) hp₂) := by
  subst hcomp
  have : IsClosedImmersion (baseChangeHom
      ((pullback sZ gK).reductionι ≫ pullback.snd sZ gK) (pullback.snd sZ gK) g
      (pullback sZ gK).reductionι rfl) :=
    isClosedImmersion_baseChangeHom _ _ _ _ _
  set t := baseChangeHom ((pullback sZ gK).reductionι ≫ pullback.snd sZ gK)
    (pullback.snd sZ gK) g (pullback sZ gK).reductionι rfl ≫
      (pullbackLeftPullbackSndIso sZ gK g).hom with ht
  have : IsClosedImmersion t := by
    rw [ht]
    infer_instance
  set q := pullback.lift pZ
    ((pullback sZ (g ≫ gK)).reductionι ≫ pullback.snd sZ (g ≫ gK)) hp₂ with hq
  have hqt : q ≫ t = (pullback sZ (g ≫ gK)).reductionι := by
    apply pullback.hom_ext
    · rw [Category.assoc, ht, Category.assoc, pullbackLeftPullbackSndIso_hom_fst]
      simpa only [hq, baseChangeHom, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc] using hp₁
    · rw [Category.assoc, ht, Category.assoc, pullbackLeftPullbackSndIso_hom_snd]
      simp only [hq, baseChangeHom, pullback.lift_snd]
  have hcq : IsClosedImmersion (q ≫ t) := by
    rw [hqt]
    infer_instance
  have : IsClosedImmersion q := IsClosedImmersion.of_comp_isClosedImmersion q t
  refine ⟨inferInstance, ⟨?_⟩⟩
  have hsurj : Function.Surjective (t.base ∘ q.base) := by
    show Function.Surjective (q ≫ t).base
    rw [hqt]
    exact Scheme.surjective_reductionι _
  exact hsurj.of_comp_left t.isEmbedding.injective

/-! ### Base change of a smooth nonsingular projective model -/

/-- The base change of a smooth nonsingular projective model of a geometrically irreducible curve
along an extension of the ground field is a curve. -/
private theorem isCurve_pullback_snd_model (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
    {Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of K)} [IsCurve K sZ] [GeometricallyIrreducible sZ]
    (M : NonsingularProjectiveModel K Z sZ) (hsm : Smooth M.structureMap) :
    IsCurve Ω (pullback.snd M.structureMap (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) :=
  let : IsCurve K M.structureMap := M.isCurve
  have : GeometricallyIrreducible M.structureMap := M.geometricallyIrreducible_structureMap K
  isCurve_pullback_snd_of_smooth K Ω M.structureMap

/-- **The base change to `Ω` of a smooth nonsingular projective model of `(X_K)_red` is
birational over `Ω` to `(X_Ω)_red`.**

The model and `(X_K)_red` have isomorphic nonempty open subschemes over `K`, since their function
fields agree over `K`. Base changing such a pair to `Ω` gives a nonempty open subscheme of
`(Y_K)_Ω` isomorphic over `Ω` to one of `(X_K)_red ×_K Ω`. The latter contains `(X_Ω)_red` as a
surjective closed subscheme, and the open subscheme is reduced — it is open in `(Y_K)_Ω`, which is
smooth over `Ω`, hence integral — so it factors through `(X_Ω)_red`. The resulting pair of
dominant open immersions out of one scheme exhibits the birationality. -/
private theorem birationalOver_reducedBaseChange_pullback_snd
    (k K Ω : Type u) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsCurve k sX] [GeometricallyIrreducible sX]
    [IsCurve K (reducedBaseChangeStructureMap k K sX)]
    [IsCurve Ω (reducedBaseChangeStructureMap k Ω sX)]
    (M : NonsingularProjectiveModel K (reducedBaseChange k K sX)
      (reducedBaseChangeStructureMap k K sX))
    (hsm : Smooth M.structureMap) :
    Scheme.BirationalOver (reducedBaseChangeStructureMap k Ω sX)
      (pullback.snd M.structureMap (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) := by
  let : IsCurve K M.structureMap := M.isCurve
  have := isCurve_pullback_snd_model K Ω M hsm
  have hgsurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :=
    ⟨fun _ => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
  -- the common nonempty open subscheme over `K`
  have hbir : Scheme.BirationalOver (reducedBaseChangeStructureMap k K sX) M.structureMap :=
    (birationalOver_iff_nonempty_functionFieldAlgEquiv K (reducedBaseChangeStructureMap k K sX)
      M.structureMap).mpr ⟨M.functionFieldEquiv⟩
  obtain ⟨U, V, hU, hV, e, he⟩ :=
    (birationalOver_iff_exists_nonempty_open_iso (reducedBaseChangeStructureMap k K sX)
      M.structureMap).mp hbir
  obtain ⟨u, hu⟩ := hU
  have : Nonempty U.toScheme := ⟨⟨u, hu⟩⟩
  have : IsOpenImmersion (e.hom ≫ V.ι) := inferInstance
  -- the two base changes of that open subscheme
  have : IsOpenImmersion (baseChangeHom (U.ι ≫ reducedBaseChangeStructureMap k K sX)
      M.structureMap (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (e.hom ≫ V.ι) he) :=
    isOpenImmersion_baseChangeHom _ _ _ _ _
  have : IsOpenImmersion (baseChangeHom (U.ι ≫ reducedBaseChangeStructureMap k K sX)
      (reducedBaseChangeStructureMap k K sX)
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) U.ι rfl) :=
    isOpenImmersion_baseChangeHom _ _ _ _ _
  have : Nonempty (pullback (U.ι ≫ reducedBaseChangeStructureMap k K sX)
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) : Scheme.{u}) := by
    obtain ⟨w, -⟩ := (pullback.fst (U.ι ≫ reducedBaseChangeStructureMap k K sX)
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).surjective ⟨u, hu⟩
    exact ⟨w⟩
  have : IsIntegral (pullback (U.ι ≫ reducedBaseChangeStructureMap k K sX)
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) : Scheme.{u}) :=
    isIntegral_of_isOpenImmersion (baseChangeHom
      (U.ι ≫ reducedBaseChangeStructureMap k K sX) M.structureMap
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (e.hom ≫ V.ι) he)
  -- the comparison of reduced base changes
  obtain ⟨pZ, hp₁, hp₂⟩ := exists_reductionBaseChangeProjection sX
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (specMap_algebraMap_comp k K Ω)
  obtain ⟨hqci, hqsurj⟩ := isClosedImmersion_and_surjective_reductionComparison sX
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (specMap_algebraMap_comp k K Ω) pZ hp₁ hp₂
  let := hqci
  let := hqsurj
  -- the open subscheme of `(X_Ω)_red` it cuts out
  obtain ⟨bΩ, hbΩopen, hbΩ⟩ := exists_isOpenImmersion_lift_of_isClosedImmersion_of_surjective
    (baseChangeHom (U.ι ≫ reducedBaseChangeStructureMap k K sX)
      (reducedBaseChangeStructureMap k K sX)
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) U.ι rfl)
    (pullback.lift pZ (reducedBaseChangeStructureMap k Ω sX) hp₂)
  let := hbΩopen
  have : IsDominant bΩ := isDominant_of_isOpenImmersion bΩ
  have : IsDominant (baseChangeHom (U.ι ≫ reducedBaseChangeStructureMap k K sX)
      M.structureMap (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (e.hom ≫ V.ι) he) :=
    isDominant_of_isOpenImmersion _
  -- both open immersions are over `Ω`, so the two targets are birational over `Ω`
  have hb₀ : bΩ ≫ (pullback.lift pZ (reducedBaseChangeStructureMap k Ω sX) hp₂ ≫
      pullback.snd (reducedBaseChangeStructureMap k K sX)
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) =
      pullback.snd (U.ι ≫ reducedBaseChangeStructureMap k K sX)
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    rw [hbΩ]
    exact pullback.lift_snd _ _ _
  have hb : bΩ ≫ reducedBaseChangeStructureMap k Ω sX =
      pullback.snd (U.ι ≫ reducedBaseChangeStructureMap k K sX)
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) := by
    rwa [pullback.lift_snd] at hb₀
  have ha : baseChangeHom (U.ι ≫ reducedBaseChangeStructureMap k K sX) M.structureMap
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (e.hom ≫ V.ι) he ≫
      pullback.snd M.structureMap (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) =
        pullback.snd (U.ι ≫ reducedBaseChangeStructureMap k K sX)
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :=
    pullback.lift_snd _ _ _
  exact (Scheme.Hom.birationalOver bΩ (reducedBaseChangeStructureMap k Ω sX) _ hb).symm.trans
    (Scheme.Hom.birationalOver _ (pullback.snd M.structureMap
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) _ ha)

/-- **The base change of a smooth nonsingular projective model is a nonsingular projective model
of the reduced base change, and so agrees with any model there.**

Let `X` be a geometrically irreducible curve over `k`, let `Ω/K/k` be a tower of fields, let
`Y_K` be a nonsingular projective model of `(X_K)_red` which is smooth over `K`, and let `Y_Ω` be
a nonsingular projective model of `(X_Ω)_red`. Then `Y_Ω` is isomorphic to `(Y_K)_Ω` over `Ω`.

The base change `(Y_K)_Ω` is smooth over `Ω` because smoothness is stable under base change, so
it is a regular projective curve over `Ω`; it is birational to `(X_Ω)_red` over `Ω` by
`AlgebraicGeometry.birationalOver_reducedBaseChange_pullback_snd`; so it is a nonsingular
projective model of `(X_Ω)_red`, and a nonsingular projective model is unique up to isomorphism
over the base field. -/
public theorem exists_iso_pullback_of_smooth_model
    (k K Ω : Type u) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsCurve k sX] [GeometricallyIrreducible sX]
    [IsCurve K (reducedBaseChangeStructureMap k K sX)]
    [IsCurve Ω (reducedBaseChangeStructureMap k Ω sX)]
    (M : NonsingularProjectiveModel K (reducedBaseChange k K sX)
      (reducedBaseChangeStructureMap k K sX))
    (N : NonsingularProjectiveModel Ω (reducedBaseChange k Ω sX)
      (reducedBaseChangeStructureMap k Ω sX))
    (hsm : Smooth M.structureMap) :
    ∃ e : N.Y ≅ pullback M.structureMap (Spec.map (CommRingCat.ofHom (algebraMap K Ω))),
      e.hom ≫ pullback.snd M.structureMap
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) = N.structureMap := by
  let : IsCurve K M.structureMap := M.isCurve
  have hc := isCurve_pullback_snd_model K Ω M hsm
  obtain ⟨E⟩ := (birationalOver_iff_nonempty_functionFieldAlgEquiv Ω
      (reducedBaseChangeStructureMap k Ω sX)
      (pullback.snd M.structureMap (Spec.map (CommRingCat.ofHom (algebraMap K Ω))))).mp
    (birationalOver_reducedBaseChange_pullback_snd k K Ω sX M hsm)
  obtain ⟨e, hcomm, -⟩ := N.exists_iso
    { Y := pullback M.structureMap (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
      structureMap := pullback.snd M.structureMap
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
      isCurve := hc
      isProjectiveVariety :=
        ⟨IsProjectiveMorphism.baseChange M.isProjectiveVariety.isProjective
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))⟩
      isRegular := isRegular_of_smooth_over_field (pullback.snd M.structureMap
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω))))
      functionFieldEquiv := E }
  exact ⟨e, hcomm⟩

/-- **Stacks Project, Tag 0BY4, part (4).** Let `k` be a field and let `X` be a geometrically
irreducible curve over `k`. For a field extension `K/k` write `Y_K` for a nonsingular projective
model of `(X_K)_red`. Given a commutative diagram of fields

```
Ω  ←  K'
↑     ↑
K  ←  k
```

such that `Y_K` and `Y_{K'}` are smooth, we have `Y_Ω = (Y_K)_Ω = (Y_{K'})_Ω`: both base changes
are isomorphic to `Y_Ω` as schemes over `Ω`, and hence to each other.

The commuting square of fields is the two scalar towers `k ⊆ K ⊆ Ω` and `k ⊆ K' ⊆ Ω`. The
equality of the source is a canonical isomorphism of schemes over `Ω`: the isomorphism is
compatible with the structure morphisms, which is part of the conclusion, and it is the only such
isomorphism matching the birational identifications, by
`AlgebraicGeometry.NonsingularProjectiveModel.hom_ext`.

The three instance binders `[IsCurve K (reducedBaseChangeStructureMap k K sX)]` and its analogues
for `K'` and `Ω` are not added hypotheses: each follows from `[IsCurve k sX]` and
`[GeometricallyIrreducible sX]` by the instance
`AlgebraicGeometry.isCurve_reducedBaseChangeStructureMap'`, which lives in
`StacksFrontier/AlgebraicGeometry/Curves/ModelNormalization.lean` and is not in this file's import
closure, so the facts are named instead. -/
@[stacks 0BY4 "part (4): for a commuting square of fields k to K to Omega and k to K' to Omega \
with the models Y_K and Y_K' smooth, the nonsingular projective model Y_Omega of (X_Omega)_red is \
isomorphic over Omega to the base change of Y_K and to the base change of Y_K'. The three \
binders `[IsCurve _ (reducedBaseChangeStructureMap k _ sX)]` add nothing: each follows from \
`[IsCurve k sX]` and `[GeometricallyIrreducible sX]` by the instance \
`AlgebraicGeometry.isCurve_reducedBaseChangeStructureMap'`, which is not in this file's import \
closure"]
public theorem exists_iso_pullback_of_smooth_models
    (k K K' Ω : Type u) [Field k] [Field K] [Field K'] [Field Ω]
    [Algebra k K] [Algebra k K'] [Algebra K Ω] [Algebra K' Ω] [Algebra k Ω]
    [IsScalarTower k K Ω] [IsScalarTower k K' Ω]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsCurve k sX] [GeometricallyIrreducible sX]
    [IsCurve K (reducedBaseChangeStructureMap k K sX)]
    [IsCurve K' (reducedBaseChangeStructureMap k K' sX)]
    [IsCurve Ω (reducedBaseChangeStructureMap k Ω sX)]
    (M_K : NonsingularProjectiveModel K (reducedBaseChange k K sX)
      (reducedBaseChangeStructureMap k K sX))
    (M_K' : NonsingularProjectiveModel K' (reducedBaseChange k K' sX)
      (reducedBaseChangeStructureMap k K' sX))
    (M_Ω : NonsingularProjectiveModel Ω (reducedBaseChange k Ω sX)
      (reducedBaseChangeStructureMap k Ω sX))
    (hK : Smooth M_K.structureMap) (hK' : Smooth M_K'.structureMap) :
    (∃ e : M_Ω.Y ≅ pullback M_K.structureMap
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω))),
      e.hom ≫ pullback.snd M_K.structureMap
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) = M_Ω.structureMap) ∧
    (∃ e : M_Ω.Y ≅ pullback M_K'.structureMap
        (Spec.map (CommRingCat.ofHom (algebraMap K' Ω))),
      e.hom ≫ pullback.snd M_K'.structureMap
        (Spec.map (CommRingCat.ofHom (algebraMap K' Ω))) = M_Ω.structureMap) :=
  ⟨exists_iso_pullback_of_smooth_model k K Ω sX M_K M_Ω hK,
    exists_iso_pullback_of_smooth_model k K' Ω sX M_K' M_Ω hK'⟩

end AlgebraicGeometry

end
