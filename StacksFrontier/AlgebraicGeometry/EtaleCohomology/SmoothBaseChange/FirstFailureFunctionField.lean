module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.FirstFailureDiagram
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SmoothLimitBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes

/-!
# A first failure of étale base change, over the function field of the base: the ingredients

Let `f : X ⟶ S` be a morphism of schemes and `n` an integer invertible on `S`, as in the
condition `BC(f, n, q₀)` of [Stacks, Tag 0F02]. [Stacks, Tag 0F1D] refines the diagram of
[Stacks, Tag 0F08], whose bottom right corner is `Spec K` for an algebraically closed extension
`K` of the function field `K(S')`, to one over `Spec K(S')` itself. This file collects the
ingredients of that descent; the descent itself is in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FirstFailureFunctionFieldDiagram`.

## Main definitions

* `Stacks.EtaleCohomology.FirstFailureFunctionField.smallEtalePullbackAbConstantIso` — inverse
  image carries the constant abelian sheaf to the constant abelian sheaf.
* `Stacks.EtaleCohomology.FirstFailureFunctionField.rightDerivedConstantZModIsoOfIsIsoUnit` — if
  the derived unit `ℤ/dℤ ⟶ Rπ_* π⁻¹(ℤ/dℤ)` is invertible then
  `R^r (π ≫ h₀)_*(ℤ/dℤ) ≅ R^r h₀_*(ℤ/dℤ)`, by relative Leray.

## Main results

* `Stacks.EtaleCohomology.FirstFailureFunctionField.exists_specMap_comp_fromSpecStalk_genericPoint`
  — a dominant morphism from the spectrum of a field to an integral scheme factors through the
  spectrum of its function field.
* `Stacks.EtaleCohomology.FirstFailureFunctionField.hasTorsionOrdersInvertibleOn_of_iso`,
  `hasTorsionOrdersInvertibleOn_of_isZero`, `hasTorsionOrdersInvertibleOn_constantZMod` and
  `hasTorsionOrdersInvertibleOn_homology_single` — the torsion hypothesis of
  [Stacks, Tag 0F0B] at `ℤ/dℤ[0]`.

## References

* [Stacks Project, Tag 0F1D](https://stacks.math.columbia.edu/tag/0F1D)
* [Stacks Project, Tag 0F0B](https://stacks.math.columbia.edu/tag/0F0B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.FirstFailureFunctionField

attribute [local instance] HasDerivedCategory.standard

open FirstFailureDiagram

/-- **Inverse image carries the constant abelian sheaf to the constant abelian sheaf.** Both
functors are left adjoint to evaluation at the final object of the small étale site of `X`,
because base change carries the final object of the small étale site of `Y` to it. -/
public def smallEtalePullbackAbConstantIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    constantSheaf (smallEtaleTopology Y) Ab.{u + 1} ⋙ smallEtalePullbackAb f ≅
      constantSheaf (smallEtaleTopology X) Ab.{u + 1} := by
  letI : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    (HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
      RingHom.Etale.containsIdentities :
        MorphismProperty.IsMultiplicative
          (@Etale : MorphismProperty Scheme.{u})).toContainsIdentities
  let T : Y.Etale := MorphismProperty.Over.mk ⊤ (𝟙 Y) (by infer_instance)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ _
  let hGT := hT.isTerminalObj (smallEtaleBaseChange f)
  exact ((constantSheafAdj _ _ hT).comp (smallEtaleAdjunctionAb f)).leftAdjointUniq
    (constantSheafAdj _ _ hGT)

/-- The torsion condition `HasTorsionOrdersInvertibleOn` is invariant under isomorphism of
abelian sheaves. -/
public theorem hasTorsionOrdersInvertibleOn_of_iso {S X : Scheme.{u}}
    {F G : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (e : F ≅ G)
    (hG : HasTorsionOrdersInvertibleOn S G) : HasTorsionOrdersInvertibleOn S F := by
  intro U x
  obtain ⟨R, hR, hx⟩ := hG U ((e.hom.hom.app (op U)).hom x)
  refine ⟨R, hR, fun V g hg => ?_⟩
  obtain ⟨n, hn, h0⟩ := hx V g hg
  refine ⟨n, hn, ?_⟩
  have hnat := congrArg (fun φ => φ.hom x) (e.hom.hom.naturality g.op)
  have hinv : ∀ y, (e.inv.hom.app (op V)).hom ((e.hom.hom.app (op V)).hom y) = y :=
    fun y => congrArg (fun φ => φ.hom y) (((sheafToPresheaf _ _).mapIso e).app (op V)).hom_inv_id
  rw [← hinv (n • F.obj.map g.op x), map_nsmul]
  dsimp at hnat
  rw [hnat, h0, map_zero]

/-- A zero abelian sheaf satisfies the torsion condition. -/
public theorem hasTorsionOrdersInvertibleOn_of_isZero {S X : Scheme.{u}}
    {F : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (hF : IsZero F) :
    HasTorsionOrdersInvertibleOn S F := by
  intro U x
  refine ⟨⊤, (smallEtaleTopology X).top_mem U, fun V g _ => ⟨1, ⟨one_pos, by simp⟩, ?_⟩⟩
  have hz : IsZero (F.obj.obj (op V)) :=
    ((sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op V)).map_isZero hF :)
  exact (AddCommGrpCat.isZero_iff_subsingleton.mp hz).elim _ _

/-- The constant sheaf `ℤ/dℤ` satisfies the torsion condition when `d` is positive and
invertible on `S`. -/
public theorem hasTorsionOrdersInvertibleOn_constantZMod {S X : Scheme.{u}} {d : ℕ}
    (hd : 0 < d) (hdS : IsUnit (d : Γ(S, ⊤))) :
    HasTorsionOrdersInvertibleOn S (constantZMod X d) := by
  intro U x
  refine ⟨⊤, (smallEtaleTopology X).top_mem U, fun V g _ => ⟨d, ⟨hd, hdS⟩, ?_⟩⟩
  simpa only [natCast_zsmul] using
    zsmul_constantZMod_eq_zero X d (n := (d : ℤ)) dvd_rfl V ((constantZMod X d).obj.map g.op x)

/-- Every cohomology sheaf of `F[0]` satisfies the torsion condition when `F` does. -/
public theorem hasTorsionOrdersInvertibleOn_homology_single {S X : Scheme.{u}}
    {F : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (hF : HasTorsionOrdersInvertibleOn S F)
    (q : ℤ) :
    HasTorsionOrdersInvertibleOn S
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  obtain rfl | hq := eq_or_ne q 0
  · exact hasTorsionOrdersInvertibleOn_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F) hF
  apply hasTorsionOrdersInvertibleOn_of_isZero
  change IsZero ((DerivedCategory.homologyFunctor _ q).obj
    ((DerivedCategory.singleFunctor _ 0).obj F))
  rcases hq.lt_or_gt with h | h
  · exact DerivedCategory.isZero_of_isGE _ 0 q h
  · exact DerivedCategory.isZero_of_isLE _ 0 q h

/-- A dominant morphism from the spectrum of a field to an integral scheme factors through
the spectrum of its function field, by the canonical morphism `Spec K(S') ⟶ S'`. -/
public theorem exists_specMap_comp_fromSpecStalk_genericPoint {S' : Scheme.{u}} [IsIntegral S']
    {K : Type u} [Field K] (g : Spec (.of K) ⟶ S') [IsDominant g] :
    ∃ φ : S'.functionField ⟶ CommRingCat.of K,
      Spec.map φ ≫ S'.fromSpecStalk (genericPoint S') = g := by
  have hgen : g (IsLocalRing.closedPoint (CommRingCat.of K)) = genericPoint S' := by
    have hg : g (genericPoint (Spec (.of K))) = genericPoint S' :=
      ((tfae_isDominant_of_isIntegral g).out 1 2).mp (inferInstance : IsDominant g)
    rwa [Subsingleton.elim (genericPoint (Spec (.of K)))
      (IsLocalRing.closedPoint (CommRingCat.of K))] at hg
  suffices H : ∀ x : S', g (IsLocalRing.closedPoint (CommRingCat.of K)) = x →
      ∃ φ : S'.presheaf.stalk x ⟶ CommRingCat.of K, Spec.map φ ≫ S'.fromSpecStalk x = g from
    H _ hgen
  rintro x rfl
  exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk g⟩

/-- **Leray along `π` with `Rπ_*(ℤ/dℤ) = ℤ/dℤ`.** If the derived unit
`ℤ/dℤ ⟶ Rπ_* π⁻¹ ℤ/dℤ` on `Y₀` is invertible, then for every `h₀ : Y₀ ⟶ X'` and every `h` with
`π ≫ h₀ = h` the higher direct images `R^r h_*(ℤ/dℤ)` and `R^r h₀_*(ℤ/dℤ)` are isomorphic. -/
public def rightDerivedConstantZModIsoOfIsIsoUnit {Y Y₀ X' : Scheme.{u}} (π : Y ⟶ Y₀)
    (h₀ : Y₀ ⟶ X') (h : Y ⟶ X') (w : π ≫ h₀ = h) (d : ℕ)
    (hUnit : IsIso ((Adjunction.rightDerivedFunctorPlus (smallEtaleAdjunctionAb π)).unit.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (constantZMod Y₀ d))))
    (r : ℕ) :
    ((smallEtalePushforwardAb h).rightDerived r).obj (constantZMod Y d) ≅
      ((smallEtalePushforwardAb h₀).rightDerived r).obj (constantZMod Y₀ d) := by
  let L := smallEtalePullbackAb π
  let P := smallEtalePushforwardAb π
  let E := (DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology Y₀) Ab.{u + 1}) 0).obj
    (constantZMod Y₀ d)
  let ePull : L.rightDerivedFunctorPlus.obj E ≅
      (DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) 0).obj
        (constantZMod Y d) :=
    ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso L 0).app
        (constantZMod Y₀ d)).symm ≪≫
      (DerivedCategory.Plus.singleFunctor _ 0).mapIso
        ((smallEtalePullbackAbConstantIso π).app _)
  let eπ : P.rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) 0).obj
        (constantZMod Y d)) ≅ E :=
    (P.rightDerivedFunctorPlus.mapIso ePull).symm ≪≫
      (asIso ((Adjunction.rightDerivedFunctorPlus (smallEtaleAdjunctionAb π)).unit.app E)).symm
  haveI : P.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (smallEtaleAdjunctionAb π)
  let eComp := rightDerivedFunctorPlusCompIsoOfIso P (smallEtalePushforwardAb h₀)
    (smallEtalePushforwardAb h)
    (smallEtalePushforwardAbCompIso π h₀ ≪≫ eqToIso (congrArg smallEtalePushforwardAb w))
  exact (Stacks.DerivedIndexing.rightDerivedIso _ r).app _ ≪≫
    (DerivedCategory.Plus.homologyFunctor _ (r : ℤ)).mapIso
      (eComp.app _ ≪≫ (smallEtalePushforwardAb h₀).rightDerivedFunctorPlus.mapIso eπ) ≪≫
    ((Stacks.DerivedIndexing.rightDerivedIso _ r).app _).symm

end Stacks.EtaleCohomology.FirstFailureFunctionField

end
