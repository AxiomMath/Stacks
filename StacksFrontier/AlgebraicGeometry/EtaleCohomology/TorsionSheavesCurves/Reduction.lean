module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.Statement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.RestrictionComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstructibleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.Reduction
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ReducedInvariance
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.SiteIsomorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsFiniteDirectImage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Reduction of the assertions of Stacks Tag 03SC to a reduced scheme

The first step of the proof of Stacks Tag 03SC replaces `X` by its reduction, which is permissible
by Stacks Tag 03SI: along the closed immersion `X_red ⟶ X`, a universal homeomorphism, étale
cohomology agrees in every degree. This file proves the reduction for any closed immersion
`r : Y ⟶ X` which is a universal homeomorphism: if the eight assertions of Tag 03SC hold for the
inverse image `r⁻¹ F` over `Y`, with structure morphism `r ≫ f`, they hold for `F` over `X`.

## Main results

* `Stacks.Torsion.LocallyKilledBy`: every local section is locally killed by an integer with a
  prescribed property; the three torsion conditions of Tag 03SC are instances.
* `Stacks.EtaleCohomology.locallyKilledBy_inverseImage_of_isDenseSubsite`: inverse image along a
  dense subsite inclusion of small étale sites preserves such a condition.
* `Stacks.EtaleCohomology.TorsionCurveAssertions.of_universalHomeomorphism`: the reduction.
* `Stacks.EtaleCohomology.TorsionCurveAssertions.of_reduction`: the case of `X_red ⟶ X`.

## Implementation notes

The comparison maps of assertions (6), (7) and (8) of the two sheaves are compared across the
squares formed by `r`, its base change to the scalar extension, and its restriction to an open,
through `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_of_comm` and
`Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_of_comm`; the base change and
the restriction of `r` are again universal homeomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w v u u₁ v₁ u₂ v₂

namespace Stacks.Torsion

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- An abelian sheaf is **locally killed by integers with property `P`** if every local section
is, locally on a covering sieve, annihilated by some `n` with `P n`. -/
@[sga "4 IX 1.1"]
def LocallyKilledBy (P : ℕ → Prop) (F : Sheaf J AddCommGrpCat.{w}) : Prop :=
  ∀ (U : C) (x : F.obj.obj (Opposite.op U)),
    ∃ R : Sieve U, R ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), R f → ∃ n : ℕ, P n ∧ n • (F.obj.map f.op x) = 0

/-- An abelian sheaf is `l`-power torsion if and only if it is locally killed by the positive
powers of `l`. -/
theorem isPrimePowerTorsion_iff_locallyKilledBy (l : ℕ) (F : Sheaf J AddCommGrpCat.{w}) :
    IsPrimePowerTorsion J l F ↔ LocallyKilledBy J (fun n => ∃ r : ℕ, 0 < r ∧ n = l ^ r) F := by
  refine forall₂_congr fun U x => exists_congr fun R => and_congr_right fun _ =>
    forall₃_congr fun V f _ => ⟨?_, ?_⟩
  · rintro ⟨r, hr, h⟩
    exact ⟨l ^ r, ⟨r, hr, rfl⟩, h⟩
  · rintro ⟨n, ⟨r, hr, rfl⟩, h⟩
    exact ⟨r, hr, h⟩

/-- An abelian sheaf is torsion prime to `p` if and only if it is locally killed by the positive
integers coprime to `p`. -/
theorem isPrimeToCharacteristicTorsion_iff_locallyKilledBy (p : ℕ)
    (F : Sheaf J AddCommGrpCat.{w}) :
    IsPrimeToCharacteristicTorsion J p F ↔
      LocallyKilledBy J (fun n => 0 < n ∧ Nat.Coprime n p) F := by
  refine forall₂_congr fun U x => exists_congr fun R => and_congr_right fun _ =>
    forall₃_congr fun V f _ => ⟨?_, ?_⟩
  · rintro ⟨n, hn, hc, h⟩
    exact ⟨n, ⟨hn, hc⟩, h⟩
  · rintro ⟨n, ⟨hn, hc⟩, h⟩
    exact ⟨n, hn, hc, h⟩

/-- Being locally killed by integers with property `P` is invariant under isomorphism. -/
theorem LocallyKilledBy.of_iso {P : ℕ → Prop} {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G)
    (hF : LocallyKilledBy J P F) : LocallyKilledBy J P G := by
  intro U x
  obtain ⟨R, hR, h⟩ := hF U ((e.inv.hom.app _) x)
  refine ⟨R, hR, fun V f hf => ?_⟩
  obtain ⟨n, hn, hx⟩ := h V f hf
  refine ⟨n, hn, ?_⟩
  have h1 := congrArg (e.hom.hom.app (Opposite.op V)) hx
  have h2 : e.hom.hom.app (Opposite.op V) (F.obj.map f.op (e.inv.hom.app _ x)) =
      G.obj.map f.op x := by
    rw [NatTrans.naturality_apply]
    congr 1
    exact (((sheafToPresheaf J _).mapIso e).app (Opposite.op U)).inv_hom_id_apply x
  rwa [map_nsmul, map_zero, h2] at h1

/-- A sheaf is locally killed by integers with property `P` if its direct image along a dense
subsite inclusion is. -/
theorem LocallyKilledBy.of_pushforward {D : Type u₂} [Category.{v₂} D]
    (K : GrothendieckTopology D) (G : C ⥤ D) [G.IsContinuous J K] [G.IsDenseSubsite J K]
    {P : ℕ → Prop} (F : Sheaf K AddCommGrpCat.{w})
    (hF : LocallyKilledBy J P ((G.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj F)) :
    LocallyKilledBy K P F := by
  have := Functor.IsDenseSubsite.isCoverDense J K G
  intro U x
  let S : Sieve U :=
    { arrows := fun V f => ∃ n : ℕ, P n ∧ n • F.obj.map f.op x = 0
      downward_closed := by
        rintro V W f ⟨n, hn, hx⟩ g
        refine ⟨n, hn, ?_⟩
        simpa using congrArg (F.obj.map g.op) hx }
  refine ⟨S, ?_, fun V f hf => hf⟩
  refine K.transitive (G.is_cover_of_isCoverDense K U) S ?_
  rintro V' g ⟨⟨W, l, m, rfl⟩⟩
  rw [Sieve.pullback_comp]
  refine K.pullback_stable l ?_
  obtain ⟨R, hR, hRx⟩ := hF W (F.obj.map m.op x)
  apply K.superset_covering (S := R.functorPushforward G) _
    ((G.functorPushforward_mem_iff J K).mpr hR)
  rintro V f ⟨W', g', h, hg', rfl⟩
  obtain ⟨n, hn, hx⟩ := hRx W' g' hg'
  refine ⟨n, hn, ?_⟩
  change n • (F.obj.map (G.map g').op).hom ((F.obj.map m.op).hom x) = 0 at hx
  simpa using congrArg (F.obj.map h.op).hom hx

end Stacks.Torsion

namespace Stacks.EtaleCohomology

open Stacks.Torsion

section Invariance

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(smallEtaleBaseChange f).IsDenseSubsite (smallEtaleTopology Y) (smallEtaleTopology X)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]

omit [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}] in
/-- Inverse image along a dense subsite inclusion of small étale sites preserves the condition of
being locally killed by integers with a given property. -/
@[sga "4 IX 1.2" "(iv)"]
theorem locallyKilledBy_inverseImage_of_isDenseSubsite {P : ℕ → Prop}
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : LocallyKilledBy Y.smallEtaleTopology P F) :
    LocallyKilledBy X.smallEtaleTopology P ((etaleAbelianInverseImage.{u, v} f).obj F) := by
  let G := smallEtaleBaseChange f
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G
    AddCommGrpCat.{max (u + 1) v} Y.smallEtaleTopology X.smallEtaleTopology
  exact LocallyKilledBy.of_pushforward Y.smallEtaleTopology X.smallEtaleTopology G
    ((etaleAbelianInverseImage.{u, v} f).obj F)
    (LocallyKilledBy.of_iso Y.smallEtaleTopology (asIso (adj.unit.app F)) hF)

omit [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}] in
/-- Inverse image along a dense subsite inclusion of small étale sites preserves `l`-power
torsion sheaves. -/
theorem isPrimePowerTorsion_inverseImage_of_isDenseSubsite (l : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : IsPrimePowerTorsion Y.smallEtaleTopology l F) :
    IsPrimePowerTorsion X.smallEtaleTopology l ((etaleAbelianInverseImage.{u, v} f).obj F) :=
  (isPrimePowerTorsion_iff_locallyKilledBy _ l _).mpr
    (locallyKilledBy_inverseImage_of_isDenseSubsite f F
      ((isPrimePowerTorsion_iff_locallyKilledBy _ l F).mp hF))

omit [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}] in
/-- Inverse image along a dense subsite inclusion of small étale sites preserves sheaves that are
torsion prime to `p`. -/
theorem isPrimeToCharacteristicTorsion_inverseImage_of_isDenseSubsite (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : IsPrimeToCharacteristicTorsion Y.smallEtaleTopology p F) :
    IsPrimeToCharacteristicTorsion X.smallEtaleTopology p
      ((etaleAbelianInverseImage.{u, v} f).obj F) :=
  (isPrimeToCharacteristicTorsion_iff_locallyKilledBy _ p _).mpr
    (locallyKilledBy_inverseImage_of_isDenseSubsite f F
      ((isPrimeToCharacteristicTorsion_iff_locallyKilledBy _ p F).mp hF))

end Invariance

namespace TorsionCurveAssertions

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (r : Y ⟶ X)
  [UniversalHomeomorphism r] [IsClosedImmersion r]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- The base change of `r` to the scalar extensions, from that of `Y` to that of `X`. -/
abbrev scalarExtensionMap (k' : Type u) [Field k'] [Algebra k k'] :
    scalarExtension k k' (r ≫ f) ⟶ scalarExtension k k' f :=
  pullback.map (r ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k k'))) f
    (Spec.map (CommRingCat.ofHom (algebraMap k k'))) r (𝟙 _) (𝟙 _) (by simp) (by simp)

omit [UniversalHomeomorphism r] [IsClosedImmersion r]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- The base change of `r` to the scalar extensions commutes with `r` and the projections of the
scalar extensions. -/
theorem scalarExtensionMap_fst (k' : Type u) [Field k'] [Algebra k k'] :
    scalarExtensionMap f r k' ≫ scalarExtensionFst k k' f =
      scalarExtensionFst k k' (r ≫ f) ≫ r :=
  (isPullback_scalarExtension k' r f).w.symm

omit [UniversalHomeomorphism r] [IsClosedImmersion r]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- The base change of `r` to the scalar extensions is a pullback of `r`. -/
theorem isPullback_scalarExtensionMap (k' : Type u) [Field k'] [Algebra k k'] :
    IsPullback (scalarExtensionMap f r k') (scalarExtensionFst k k' (r ≫ f))
      (scalarExtensionFst k k' f) r :=
  (isPullback_scalarExtension k' r f).flip

/-- The base change of `r` to the scalar extensions is a universal homeomorphism. -/
instance universalHomeomorphism_scalarExtensionMap (k' : Type u) [Field k'] [Algebra k k'] :
    UniversalHomeomorphism (scalarExtensionMap f r k') :=
  ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_scalarExtensionMap f r k').flip
    (UniversalHomeomorphism.universally_isHomeomorph (f := r))⟩

/-- The restriction `r ∣_ U` of `r` over an open `U` of `X` is a universal homeomorphism. -/
instance universalHomeomorphism_morphismRestrict (U : X.Opens) :
    UniversalHomeomorphism (r ∣_ U) :=
  ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_morphismRestrict r U).flip
    (UniversalHomeomorphism.universally_isHomeomorph (f := r))⟩

omit [IsClosedImmersion r] in
/-- Restriction along `r` is bijective in every degree, by Stacks Tag 03SI. -/
theorem bijective_restriction (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} r F q) :=
  etaleCohomologyRestrictionMap_bijective_of_universalHomeomorphism.{u, u + 1, u + 1} r F q

/-- Transfers bijectivity of restriction from `Y_{k'}` to `X_{k'}`, given that along `r`. -/
private theorem bijective_restriction_scalarExtension (r : Y ⟶ X) [UniversalHomeomorphism r]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (k' : Type u) [Field k'] [Algebra k k']
    [HasExt.{u + 1} (Sheaf (scalarExtension k k' f).smallEtaleTopology AddCommGrpCat.{u + 1})]
    (q : ℕ)
    (H : ∀ [HasExt.{u + 1}
        (Sheaf (scalarExtension k k' (r ≫ f)).smallEtaleTopology AddCommGrpCat.{u + 1})],
      Function.Bijective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
        (scalarExtensionFst k k' (r ≫ f)) ((etaleAbelianInverseImage.{u, u + 1} r).obj F) q)) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
      (scalarExtensionFst k k' f) F q) :=
  let _ : HasExt.{u + 1}
      (Sheaf (scalarExtension k k' (r ≫ f)).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    hasExt_of_enoughInjectives.{u + 1} _
  bijective_etaleCohomologyRestrictionMap_of_comm.{u, u + 1, u + 1}
    (scalarExtensionFst k k' f) r (scalarExtensionFst k k' (r ≫ f))
    (scalarExtensionMap f r k') (scalarExtensionMap_fst f r k') F q
    (bijective_restriction r F q) H (bijective_restriction (scalarExtensionMap f r k') _ q)

/-- **Reduction of Stacks Tag 03SC along a closed universal homeomorphism (Tag 03SI).** If the
eight assertions hold for `r⁻¹ F` over `Y`, with structure morphism `r ≫ f`, they hold for `F`
over `X`. -/
theorem of_universalHomeomorphism (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h : TorsionCurveAssertions (r ≫ f) ((etaleAbelianInverseImage.{u, u + 1} r).obj F)) :
    TorsionCurveAssertions f F := by
  have := isDenseSubsite_of_universalHomeomorphism r
  let e : ∀ q, Sheaf.H.{u + 1} F q ≃
      Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, u + 1} r).obj F) q :=
    fun q => Equiv.ofBijective _ (bijective_restriction r F q)
  have hc : IsConstructibleSmallEtaleSheaf F →
      IsConstructibleSmallEtaleSheaf ((etaleAbelianInverseImage.{u, u + 1} r).obj F) :=
    IsConstructibleSmallEtaleSheaf.inverseImage_of_mono r
  have ht : IsPrimeToCharacteristicTorsion X.smallEtaleTopology (ringExpChar k) F →
      IsPrimeToCharacteristicTorsion Y.smallEtaleTopology (ringExpChar k)
        ((etaleAbelianInverseImage.{u, u + 1} r).obj F) :=
    isPrimeToCharacteristicTorsion_inverseImage_of_isDenseSubsite.{u + 1, u} r _ F
  refine
    { vanishing := fun q hq => (e q).subsingleton_congr.mpr (h.vanishing q hq)
      vanishing_of_isAffine := fun hX q hq =>
        (e q).subsingleton_congr.mpr (h.vanishing_of_isAffine (isAffine_of_isAffineHom r) q hq)
      vanishing_of_isPrimePowerTorsion := fun p hp hp0 hF q hq =>
        (e q).subsingleton_congr.mpr (h.vanishing_of_isPrimePowerTorsion p hp hp0
          (isPrimePowerTorsion_inverseImage_of_isDenseSubsite.{u + 1, u} r p F hF) q hq)
      finite_of_isPrimeToCharacteristicTorsion := fun hcF htF q =>
        (Equiv.finite_iff (e q)).mpr
          (h.finite_of_isPrimeToCharacteristicTorsion (hc hcF) (ht htF) q)
      finite_of_isProper := fun hf hcF q =>
        (Equiv.finite_iff (e q)).mpr (h.finite_of_isProper inferInstance (hc hcF) q)
      bijective_of_isPrimeToCharacteristicTorsion := fun htF k' _ _ _ _ q =>
        bijective_restriction_scalarExtension f r F k' q
          (h.bijective_of_isPrimeToCharacteristicTorsion (ht htF) k' q)
      bijective_of_isProper := fun hf k' _ _ _ _ q =>
        bijective_restriction_scalarExtension f r F k' q
          (h.bijective_of_isProper inferInstance k' q)
      surjective_restriction := fun U _ => by
        let : HasExt.{u + 1}
            (Sheaf ((r ⁻¹ᵁ U : Y.Opens) : Scheme.{u}).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
          hasExt_of_enoughInjectives.{u + 1} _
        exact surjective_etaleCohomologyRestrictionMap_of_comm.{u, u + 1, u + 1}
          U.ι r (r ⁻¹ᵁ U).ι (r ∣_ U) (morphismRestrict_ι r U) F 2
          (bijective_restriction r F 2).2 (h.surjective_restriction (r ⁻¹ᵁ U))
          (bijective_restriction (r ∣_ U) _ 2) }

/-- **Reduction of Stacks Tag 03SC to the reduction of `X` (Tag 03SI).** -/
theorem of_reduction [HasExt.{u + 1} (Sheaf X.reduction.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h : TorsionCurveAssertions (X.reductionι ≫ f)
      ((etaleAbelianInverseImage.{u, u + 1} X.reductionι).obj F)) :
    TorsionCurveAssertions f F :=
  of_universalHomeomorphism f X.reductionι F h

end TorsionCurveAssertions

end Stacks.EtaleCohomology

end
