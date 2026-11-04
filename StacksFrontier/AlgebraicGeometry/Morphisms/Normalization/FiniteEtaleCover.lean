module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Normalization
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.GenericPointGluing.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.BirationalIsIso
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Varieties.FunctionFieldEquivalence.Basic
public import StacksFrontier.RingTheory.GeometricallyNormal.TFAE

/-!
# Connected finite étale covers of normal integral schemes

A connected finite étale cover of a normal integral scheme is itself integral and normal, and
it is canonically the normalization of the base in its own function field.

Normality ascends along an étale morphism because it is an affine-local condition on the rings
of sections and an étale algebra over a normal ring is normal. Flatness forces every generic
point of the cover to lie over the generic point of the base, and quasi-finiteness then makes
the set of those generic points finite; a normal scheme with locally finitely many irreducible
components is a coproduct of normal integral schemes, so connectedness leaves exactly one
summand. Finally the comparison morphism from the relative normalization in the function field
is integral and birational onto a normal target, hence an isomorphism.

## Main results

* `AlgebraicGeometry.isIntegral_of_finite_etale_connected`: a connected finite étale cover of a
  normal integral scheme is integral.
* `AlgebraicGeometry.normalizationDesc_isIso_of_finite_etale_connected`: that cover is the
  relative normalization of the base in its function field.

## Implementation notes

The normalization is Mathlib's relative normalization of the composite of the generic-point
morphism `Spec 𝒪_{Y, η} ⟶ Y` with the covering morphism `Y ⟶ X`. Its canonical comparison
morphism to `Y` is `AlgebraicGeometry.Scheme.Hom.normalizationDesc`; asserting that this
comparison is an isomorphism also records that the identification is the canonical one and is
compatible with the morphisms to `X`.

## References

* [Stacks Project, Tag 0BQL](https://stacks.math.columbia.edu/tag/0BQL)
-/

@[expose] public section

open CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry

/-- Along a flat morphism to an irreducible scheme every generic point of the source is carried
to the generic point of the target. -/
private theorem genericPoint_image_of_flat {X Y : Scheme.{u}} [IrreducibleSpace X]
    (f : Y ⟶ X) [Flat f] (η : genericPoints Y) : f η.1 = genericPoint X := by
  obtain ⟨z, hzy, hfz⟩ := Flat.generalizingMap f (genericPoint_specializes (f η.1))
  rwa [← Stacks.AlgebraicGeometry.GenericPointGluing.eq_of_specializes_genericPoint η.2 hzy]

/-- A flat, locally quasi-finite and quasi-compact morphism to an irreducible scheme has a
source with finitely many generic points: they all lie in the fibre over the generic point of
the target, which is finite. -/
private theorem finite_genericPoints_of_flat_quasiFinite {X Y : Scheme.{u}}
    [IrreducibleSpace X] (f : Y ⟶ X) [Flat f] [LocallyQuasiFinite f] [QuasiCompact f] :
    Finite (genericPoints Y) := by
  let η := genericPoint X
  let toFiber : genericPoints Y → f ⁻¹' ({η} : Set X) := fun y =>
    ⟨y.1, Set.mem_singleton_iff.mpr (genericPoint_image_of_flat f y)⟩
  have : Finite (f ⁻¹' ({η} : Set X)) := (f.finite_preimage_singleton η).to_subtype
  exact Finite.of_injective toFiber (fun a b hab =>
    Subtype.ext (congrArg (fun p : f ⁻¹' ({η} : Set X) => p.1) hab))

/-- An open subspace of a space with finitely many irreducible components again has finitely
many irreducible components: each one is the trace of the component of the closure of its
image, and that assignment is injective. -/
private theorem finite_irreducibleComponents_open_of_finite
    {X : Type u} [TopologicalSpace X] [Finite (irreducibleComponents X)]
    (U : Set X) (hU : IsOpen U) :
    Finite (irreducibleComponents (U : Set X)) := by
  classical
  let j : U → X := fun x => x.1
  let closureImage (C : irreducibleComponents (U : Set X)) := closure (j '' C.1)
  let spec (C : irreducibleComponents (U : Set X)) :
      ∃ D : Set X, D ∈ irreducibleComponents X ∧ closureImage C ⊆ D :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible (closureImage C)
      (C.2.1.image j continuous_subtype_val.continuousOn).closure
  let toX (C : irreducibleComponents (U : Set X)) : irreducibleComponents X :=
    ⟨Classical.choose (spec C), (Classical.choose_spec (spec C)).1⟩
  have hsub (C : irreducibleComponents (U : Set X)) : closureImage C ⊆ (toX C).1 :=
    (Classical.choose_spec (spec C)).2
  have hCsub (C : irreducibleComponents (U : Set X)) : C.1 ⊆ j ⁻¹' (toX C).1 :=
    fun x hx => hsub C (subset_closure ⟨x, hx, rfl⟩)
  have hmeet (C : irreducibleComponents (U : Set X)) :
      ((toX C).1 ∩ Set.range j).Nonempty := by
    obtain ⟨x, hx⟩ := C.2.1.nonempty
    exact ⟨j x, hCsub C hx, ⟨x, rfl⟩⟩
  have hpre_eq (C : irreducibleComponents (U : Set X)) : j ⁻¹' (toX C).1 = C.1 :=
    Set.Subset.antisymm (C.2.2
      (preimage_mem_irreducibleComponents (toX C).2 hU.isOpenEmbedding_subtypeVal
        (hmeet C)).1 (hCsub C)) (hCsub C)
  exact Finite.of_injective toX fun C D h =>
    Subtype.ext (by rw [← hpre_eq C, h, hpre_eq D])

/-- A dominant morphism of irreducible schemes carries the generic point to the generic
point. -/
private alias dominant_map_genericPoint := AlgebraicGeometry.map_genericPoint_of_isDominant

/-- A connected finite étale cover of a normal integral scheme is integral. -/
@[stacks 0BQL "integrality", sga "1 I 10.1" "integrality, finite case"]
theorem isIntegral_of_finite_etale_connected {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsNormal X] [IsFinite f] [Etale f]
    [ConnectedSpace Y] : IsIntegral Y := by
  have : IsNormal Y := isNormal_of_etale f
  obtain ⟨ι, Z, _, hZintegral, ⟨e⟩⟩ :=
    (isNormal_iff_exists_iso_coproduct
      (fun U _ => by
        have : Finite (genericPoints Y) := finite_genericPoints_of_flat_quasiFinite f
        have : Finite (irreducibleComponents Y) :=
          Finite.of_equiv (genericPoints Y) genericPoints.equiv
        exact finite_irreducibleComponents_open_of_finite (U : Set Y) U.isOpen)).mp
      (inferInstance : IsNormal Y)
  let C : Scheme.{u} := ∐ Z
  let htop : Y ≃ₜ C := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)
  let : ConnectedSpace C := htop.connectedSpace_iff.mp inferInstance
  let : ConnectedSpace (Σ i, Z i) :=
    (AlgebraicGeometry.sigmaMk Z).connectedSpace_iff.mpr inferInstance
  have hι : Nonempty ι :=
    ⟨((AlgebraicGeometry.sigmaMk Z).symm (e.hom (Classical.choice inferInstance))).1⟩
  have : Subsingleton ι := ⟨fun i j => by
    let : IsIntegral (Z i) := hZintegral i
    obtain ⟨xi⟩ := (inferInstance : Nonempty (Z i))
    let : IsIntegral (Z j) := hZintegral j
    obtain ⟨xj⟩ := (inferInstance : Nonempty (Z j))
    have hconn : IsConnected (Set.univ : Set (Σ k, Z k)) := isConnected_univ
    have hsub := hconn.isPreconnected.subset_isClopen isClopen_range_sigmaMk
      ⟨⟨i, xi⟩, Set.mem_univ _, xi, rfl⟩
    obtain ⟨x, hx⟩ := hsub (Set.mem_univ (⟨j, xj⟩ : Σ k, Z k))
    exact congrArg Sigma.fst hx⟩
  let : Unique ι := uniqueOfSubsingleton (Classical.choice hι)
  let : IsIntegral (Z default) := hZintegral default
  exact IsIntegral.of_isIso (e ≪≫ CategoryTheory.Limits.coproductUniqueIso Z).inv

/-- The generic-point morphism `Spec 𝒪_{Y, η} ⟶ Y` of an irreducible scheme is dominant. -/
private theorem isDominant_fromSpecStalk_genericPoint_of_irreducibleSpace
    (Y : Scheme.{u}) [IrreducibleSpace Y] :
    IsDominant (Y.fromSpecStalk (genericPoint Y)) := by
  have hηrange : genericPoint Y ∈ Set.range (Y.fromSpecStalk (genericPoint Y)).base :=
    ⟨closedPoint (Y.presheaf.stalk _), Scheme.fromSpecStalk_closedPoint (X := Y) (x := _)⟩
  refine ⟨?_⟩
  show Dense (Set.range (Y.fromSpecStalk (genericPoint Y)).base)
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_iff_forall.mpr
  intro y
  have hy : y ∈ closure {genericPoint Y} := by
    rw [(genericPoint_spec Y).def]
    exact Set.mem_univ y
  exact closure_mono (Set.singleton_subset_iff.mpr hηrange) hy

/-- The morphism `Spec 𝒪_{Y, y} ⟶ Y` induces an isomorphism on stalks at the closed point. -/
private theorem isIso_stalkMap_closedPoint_fromSpecStalk (Y : Scheme.{u}) (y : Y) :
    IsIso ((Y.fromSpecStalk y).stalkMap (closedPoint (Y.presheaf.stalk y))) := by
  have h : IsIso (Scheme.stalkClosedPointTo (Y.fromSpecStalk y)) := by
    rw [Scheme.stalkClosedPointTo_fromSpecStalk]
    infer_instance
  change IsIso ((Y.fromSpecStalk y).stalkMap (closedPoint (Y.presheaf.stalk y)) ≫
    (stalkClosedPointIso _).hom) at h
  exact IsIso.of_isIso_comp_right _ (stalkClosedPointIso _).hom

/-- If a composite of ring maps is an isomorphism and the middle ring is a field, then the
second map is an isomorphism. -/
private theorem isIso_of_isIso_comp_of_isField {A B C : CommRingCat.{u}} (a : A ⟶ B)
    (b : B ⟶ C) [IsIso (a ≫ b)] [Nontrivial C] (hB : IsField B) : IsIso b := by
  let := hB.toField
  have hs : Function.Surjective (b.hom.comp a.hom) := by
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using
      (ConcreteCategory.bijective_of_isIso (a ≫ b)).2
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨b.hom.injective, Function.Surjective.of_comp hs⟩

/-- Equal morphisms of schemes have isomorphic stalk maps. -/
private theorem isIso_stalkMap_of_hom_eq {X Y : Scheme.{u}} {φ ψ : X ⟶ Y} (h : φ = ψ) (x : X)
    [IsIso (ψ.stalkMap x)] : IsIso (φ.stalkMap x) := by
  subst h
  infer_instance

/-- An integral normal scheme is the relative normalization of its base in its function field
whenever the structural morphism is integral. -/
private theorem normalizationDesc_isIso_of_integral_normal_source
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIntegral Y] [IsNormal Y] [IsIntegralHom f] :
    IsIso ((Y.fromSpecStalk (genericPoint Y) ≫ f).normalizationDesc
      (Y.fromSpecStalk (genericPoint Y)) f rfl) := by
  let η := genericPoint Y
  let g := Y.fromSpecStalk η
  have : QuasiCompact g := by
    dsimp [g]
    infer_instance
  have : QuasiSeparated g := by
    dsimp [g]
    infer_instance
  let n := g ≫ f
  let k := n.normalizationDesc g f rfl
  show IsIso k
  have hfactor : n.toNormalization ≫ k = g := n.toNormalization_normalizationDesc g f rfl
  have : IsDominant g := isDominant_fromSpecStalk_genericPoint_of_irreducibleSpace Y
  have : IsDominant (n.toNormalization ≫ k) := by rwa [hfactor]
  have : IsDominant k := IsDominant.of_comp n.toNormalization k
  have hkpoint : k (genericPoint n.normalization) = η := by
    simpa [η] using map_genericPoint_of_isDominant k
  let S : Scheme.{u} := Spec (.of (Y.presheaf.stalk η))
  have hsource : genericPoint S = closedPoint (Y.presheaf.stalk η) := Subsingleton.elim _ _
  let z := n.toNormalization (genericPoint S)
  have hnormpoint : z = genericPoint n.normalization :=
    map_genericPoint_of_isDominant n.toNormalization
  have hfieldAtZ : IsField (n.normalization.presheaf.stalk z) := by
    rw [hnormpoint]
    exact isField_stalk_of_closure_mem_irreducibleComponents _ _ (by
      simp [irreducibleComponents_eq_singleton])
  have : IsIso (g.stalkMap (genericPoint S)) := by
    rw [hsource]
    exact isIso_stalkMap_closedPoint_fromSpecStalk Y η
  have hcompRaw : IsIso ((n.toNormalization ≫ k).stalkMap (genericPoint S)) :=
    isIso_stalkMap_of_hom_eq hfactor _
  have : IsIso (k.stalkMap z ≫ n.toNormalization.stalkMap (genericPoint S)) := by
    have hEq := Scheme.Hom.stalkMap_comp n.toNormalization k (genericPoint S)
    simpa [z] using hEq ▸ hcompRaw
  have : IsIso (n.toNormalization.stalkMap (genericPoint S)) :=
    isIso_of_isIso_comp_of_isField (k.stalkMap z) _ hfieldAtZ
  have hstalk : IsIso (k.stalkMap (genericPoint n.normalization)) := by
    rw [← hnormpoint]
    exact IsIso.of_isIso_comp_right (k.stalkMap z)
      (n.toNormalization.stalkMap (genericPoint S))
  have hbij : Set.BijOn k (genericPoints n.normalization) (genericPoints Y) := by
    rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
    simp [η, hkpoint]
  have hbir : IsBirational k :=
    isBirational_of_bijOn_of_isIso_stalkMap k hbij (by
      intro x hx
      obtain rfl : x = genericPoint n.normalization := by
        simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hx
      exact hstalk)
  exact isIso_of_isIntegralHom_of_isBirational_of_isNormal k hbir

/-- A connected finite étale cover of a normal integral scheme is canonically the
normalization of the base in the function field of the cover. -/
@[stacks 0BQL "normalization in the function field",
  sga "1 I 10.1" "finite étale case",
  sga "1 I 10.2" "finite => normalization"]
theorem normalizationDesc_isIso_of_finite_etale_connected
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsNormal X] [IsFinite f] [Etale f]
    [ConnectedSpace Y] :
    let : IsIntegral Y := isIntegral_of_finite_etale_connected f
    IsIso ((Y.fromSpecStalk (genericPoint Y) ≫ f).normalizationDesc
      (Y.fromSpecStalk (genericPoint Y)) f rfl) := by
  let : IsIntegral Y := isIntegral_of_finite_etale_connected f
  let : IsNormal Y := isNormal_of_etale f
  exact normalizationDesc_isIso_of_integral_normal_source f

end AlgebraicGeometry

end
