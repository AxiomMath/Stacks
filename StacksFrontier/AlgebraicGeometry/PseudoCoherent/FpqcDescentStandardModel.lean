module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FpqcDescent
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# `m`-pseudo-coherence descends along an fpqc covering, at the standard derived category

Let `{f_i : X_i ⟶ X}` be an fpqc covering of schemes and let `E ∈ D(𝒪_X)` have quasi-coherent
cohomology sheaves. If every derived pullback `Lf_i^*E` is `m`-pseudo-coherent, then so is `E`.
This is the converse of Stacks 09UE, stated here at `HasDerivedCategory.standard`, the model of
`D(𝒪_X)` at which derived pullback, perfectness and Tor amplitude are formalized.

The proof is the source's: over an affine open `U` the covering is refined by Stacks 03L7 to
finitely many flat morphisms of affine schemes `V_j ⟶ U` whose product of rings of sections is
faithfully flat, `E|_U` is the sheafification of a complex of modules (Stacks 06Z0), and Stacks
068R descends pseudo-coherence of complexes of modules along the faithfully flat product.

## Main results

* `isQuasicoherent_homology_derivedPullback_of_isFlat`: derived pullback along a flat morphism
  of schemes preserves quasi-coherence of the cohomology sheaves.
* `isPseudoCoherentFrom_of_forall_fpqc_of_isQuasicoherent`: the converse of Stacks 09UE for an
  object with quasi-coherent cohomology sheaves, at the locally small model.
* `isPseudoCoherentFrom_of_forall_fpqc`: the same at the standard model.

## Implementation notes

Stacks 06Z0 is available at the locally small model only, so the descent is run there and the
result is moved to the standard model through `Stacks.Injectives.grothendieckModelEquiv`, which
is the identity on objects and matches the two localization functors out of cochain complexes on
the nose: `m`-pseudo-coherence and the cohomology sheaves are read off a representing complex
identically on the two sides, and derived pullback is matched by
`StacksDraft.DerivedModel.derivedPullbackModelIso`.

## References

* [Stacks Project, Tag 09UE](https://stacks.math.columbia.edu/tag/09UE)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 068R](https://stacks.math.columbia.edu/tag/068R)
* [Stacks Project, Tag 03L7](https://stacks.math.columbia.edu/tag/03L7)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RingedSpace RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.HigherDirectImage

universe u v

namespace Stacks.Cohomology.PseudoCoherence.FpqcDescent

/-! ### Cohomology sheaves of a derived pullback along a flat morphism -/

/-- **Along a flat morphism the derived pullback preserves quasi-coherence of a cohomology
sheaf**: `H^i(Lf^*E) ≅ f^*H^i(E)`, and pullback preserves quasi-coherence (Stacks 01BG). -/
public theorem isQuasicoherent_homology_derivedPullback_of_isFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f]
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} Y.toRingedSpace)) (i : ℤ)
    (hE : ((DerivedCategory.homologyFunctor
      (StrictlyPerfect.OXMod.{u, u} Y.toRingedSpace) i).obj E).IsQuasicoherent) :
    ((DerivedCategory.homologyFunctor (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) i).obj
      ((derivedPullback f.toLRSHom.toShHom).obj E)).IsQuasicoherent :=
  let : PreservesFiniteLimits (modulePullback f.toLRSHom.toShHom) :=
    preservesFiniteLimits_modulePullback_of_isFlat f.toLRSHom.toShHom
      (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom f)
  let : PreservesFiniteColimits (modulePullback f.toLRSHom.toShHom) :=
    preservesFiniteColimits_modulePullback f.toLRSHom.toShHom
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (((DerivedCategory.homologyFunctor (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) i).mapIso
        ((AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso
          f.toLRSHom.toShHom).app E) ≪≫
      (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
        (modulePullback f.toLRSHom.toShHom) i).app E).symm)
    (Stacks.Modules.isQuasicoherent_pullback f _ hE)

/-! ### The converse of Stacks 09UE at the locally small model -/

/-- **The converse of Stacks 09UE for an object with quasi-coherent cohomology sheaves**, at the
locally small model of `D(𝒪_X)`. -/
public theorem isPseudoCoherentFrom_of_forall_fpqc_of_isQuasicoherent {X : Scheme.{u}}
    {I : Type v} (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
    (hf : Presieve.ofArrows Y f ∈ Scheme.fpqcPrecoverage X)
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) i).obj E).IsQuasicoherent) (m : ℤ)
    (hEi : ∀ i : I, IsPseudoCoherentFrom
      ((derivedPullback (f i).toLRSHom.toShHom).obj E) m) :
    IsPseudoCoherentFrom E m := by
  have hflat : ∀ i, Flat (f i) := fun i => flat_of_mem_fpqcPrecoverage Y f hf i
  refine isPseudoCoherentFrom_of_local_restrict E m fun x => ?_
  obtain ⟨U, hU, hxU, n, a, V, hV, hVcov⟩ := exists_affineOpen_affine_images_cover Y f hf x
  refine ⟨U, hxU, ?_⟩
  have hUaff : IsAffine U.toScheme := hU
  have hVaff : ∀ j, IsAffine (V j).toScheme := fun j => hV j
  have hVU : ∀ j, V j ≤ (f (a j)) ⁻¹ᵁ U := by
    intro j y hy
    rw [Scheme.Hom.mem_preimage, ← SetLike.mem_coe, ← hVcov]
    exact Set.mem_iUnion.mpr ⟨j, ⟨y, hy, rfl⟩⟩
  have hgflat : ∀ j, Flat ((f (a j)).resLE U (V j) (hVU j)) := fun _ => inferInstance
  have hgcover : ∀ y : U.toScheme, ∃ j, ∃ z : (V j).toScheme,
      (f (a j)).resLE U (V j) (hVU j) z = y := by
    intro y
    have hy : (y.1 : X) ∈ (⋃ j, (f (a j)) '' (V j : Set (Y (a j)))) := by
      rw [hVcov]
      exact y.2
    obtain ⟨j, z, hz, hzy⟩ := Set.mem_iUnion.mp hy
    refine ⟨j, ⟨z, hz⟩, Subtype.ext ?_⟩
    rw [Scheme.Hom.coe_resLE_apply]
    exact hzy
  have hEUqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StrictlyPerfect.OXMod.{u, u} (X.toRingedSpace.restrict U.isOpenEmbedding)) i).obj
        ((derivedRestrictModules X.toRingedSpace U).obj E)).IsQuasicoherent := by
    intro i
    have hM : ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent := hE i
    have hres : (((restrictModules.{u, u} X.toRingedSpace U).obj
        ((DerivedCategory.homologyFunctor
          (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) i).obj E))).IsQuasicoherent := by
      exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
        ((restrictModulesIsoRestrictFunctor X U).app _).symm
        (@Scheme.Modules.isQuasicoherent_restrictFunctor U.toScheme X U.ι inferInstance
          ((DerivedCategory.homologyFunctor X.Modules i).obj E) hM)
    exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
        (restrictModules.{u, u} X.toRingedSpace U) i).app E).symm hres
  have hgpc : ∀ j, IsPseudoCoherentFrom
      ((derivedPullback ((f (a j)).resLE U (V j) (hVU j)).toLRSHom.toShHom).obj
        ((derivedRestrictModules X.toRingedSpace U).obj E)) m := by
    intro j
    refine (isPseudoCoherentFrom_derivedRestrictModules
      ((derivedPullback (f (a j)).toLRSHom.toShHom).obj E) m (hEi (a j)) (V j)).ofIso ?_
    exact (derivedPullbackRestrictIsoFree (f (a j)).toLRSHom.toShHom
      (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom (f (a j))) U (V j)
      ((f (a j)).resLE U (V j) (hVU j)).toLRSHom.toShHom
      (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom _)
      (Stacks.Cohomology.PseudoCoherence.FlatDescent.resLE_square (f (a j)) U (V j)
        (hVU j)) E).symm
  refine isPseudoCoherentFrom_of_derivedPullback_iso U.toScheme.isoSpec.symm _ m ?_
  refine isPseudoCoherentFrom_of_faithfullyFlat_pi_spec
    (fun j => ((f (a j)).resLE U (V j) (hVU j)).appTop) ?_ (fun j => Scheme.Hom.flat_appTop _)
    _ ?_ m ?_
  · exact faithfullyFlat_pi_of_affine_cover (fun j => (V j).toScheme)
      (fun j => (f (a j)).resLE U (V j) (hVU j)) hgflat hgcover
  · exact fun i => isQuasicoherent_homology_derivedPullback_of_isFlat
      U.toScheme.isoSpec.inv _ i (hEUqc i)
  · intro j
    have hnat := Scheme.isoSpec_hom_naturality ((f (a j)).resLE U (V j) (hVU j))
    have key : Spec.map (((f (a j)).resLE U (V j) (hVU j)).appTop) ≫
          U.toScheme.isoSpec.inv =
        (V j).toScheme.isoSpec.inv ≫ (f (a j)).resLE U (V j) (hVU j) := by
      rw [← Iso.inv_hom_id_assoc (V j).toScheme.isoSpec
        (Spec.map (((f (a j)).resLE U (V j) (hVU j)).appTop) ≫ U.toScheme.isoSpec.inv)]
      rw [← Category.assoc ((V j).toScheme.isoSpec.hom), hnat]
      simp
    have hsq := congrArg
      (fun q : Spec Γ((V j).toScheme, ⊤) ⟶ U.toScheme => q.toLRSHom.toShHom) key
    exact (isPseudoCoherentFrom_derivedPullback_of_isFlat
      ((V j).toScheme.isoSpec.inv).toLRSHom.toShHom
      (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom _) _ m
      (hgpc j)).ofIso (derivedPullbackCommSquareIso _ _ _ _ hsq _).symm

/-! ### Transport to the standard model -/

section Standard

attribute [local instance 2000] _root_.HasDerivedCategory.standard

/-- The comparison of the two models of `D(𝒪_X)`, from the standard one to the locally small
one. -/
abbrev shrinkComparison (X : RingedSpace.{u, u}) :=
  (Stacks.Injectives.grothendieckModelEquiv.{u} (StrictlyPerfect.OXMod.{u, u} X)).functor

/-- The cohomology sheaves of an object of the standard derived category are those of its image
in the locally small one. -/
public def homologyShrinkComparisonIso (X : RingedSpace.{u, u})
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X)) (i : ℤ) :
    (@DerivedCategory.homologyFunctor (StrictlyPerfect.OXMod.{u, u} X) _ _
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) i).obj
        ((shrinkComparison X).obj E) ≅
      (DerivedCategory.homologyFunctor (StrictlyPerfect.OXMod.{u, u} X) i).obj E :=
  let K := DerivedCategory.Q.objPreimage E
  let e : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  ((@DerivedCategory.homologyFunctor (StrictlyPerfect.OXMod.{u, u} X) _ _
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) i).mapIso
      ((shrinkComparison X).mapIso e.symm) ≪≫
    (@DerivedCategory.homologyFunctorFactors (StrictlyPerfect.OXMod.{u, u} X) _ _
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) i).app K) ≪≫
  ((DerivedCategory.homologyFunctor (StrictlyPerfect.OXMod.{u, u} X) i).mapIso e.symm ≪≫
    (DerivedCategory.homologyFunctorFactors (StrictlyPerfect.OXMod.{u, u} X) i).app K).symm

/-- `m`-pseudo-coherence of an object of the standard derived category is `m`-pseudo-coherence of
its image in the locally small one. -/
public theorem isPseudoCoherentFrom_shrinkComparison_iff (X : RingedSpace.{u, u})
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X)) (m : ℤ) :
    @IsPseudoCoherentFrom X (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      ((shrinkComparison X).obj E) m ↔ IsPseudoCoherentFrom E m :=
  ⟨fun ⟨K, hK, ⟨e⟩⟩ => ⟨K, hK, ⟨(shrinkComparison X).preimageIso e⟩⟩,
    fun ⟨K, hK, ⟨e⟩⟩ => ⟨K, hK, ⟨(shrinkComparison X).mapIso e⟩⟩⟩

/-- **The converse of Stacks 09UE at the standard model.** Let `{f_i : Y_i ⟶ X}` be an fpqc
covering of schemes and let `E ∈ D(𝒪_X)` have quasi-coherent cohomology sheaves. If every derived
pullback `Lf_i^*E` is `m`-pseudo-coherent, then `E` is `m`-pseudo-coherent. -/
public theorem isPseudoCoherentFrom_of_forall_fpqc {X : Scheme.{u}} {I : Type v}
    (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
    (hf : Presieve.ofArrows Y f ∈ Scheme.fpqcPrecoverage X)
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace))
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) i).obj E).IsQuasicoherent) (m : ℤ)
    (hEi : ∀ i : I, IsPseudoCoherentFrom
      ((derivedPullback (f i).toLRSHom.toShHom).obj E) m) :
    IsPseudoCoherentFrom E m := by
  refine (isPseudoCoherentFrom_shrinkComparison_iff X.toRingedSpace E m).1
    (isPseudoCoherentFrom_of_forall_fpqc_of_isQuasicoherent Y f hf _ (fun i =>
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        (homologyShrinkComparisonIso X.toRingedSpace E i).symm (hE i)) m fun i => ?_)
  obtain ⟨K, hK, ⟨e⟩⟩ := hEi i
  exact ⟨K, hK, ⟨(shrinkComparison (Y i).toRingedSpace).mapIso e ≪≫
    (StacksDraft.DerivedModel.derivedPullbackModelIso (f i).toLRSHom.toShHom).app E⟩⟩

end Standard

end Stacks.Cohomology.PseudoCoherence.FpqcDescent

end
