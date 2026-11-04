module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismAssociatedPoints.Flat
public import StacksFrontier.AlgebraicGeometry.FiberRank.LocallyFree
public import StacksFrontier.AlgebraicGeometry.FiberRank.Semicontinuity
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.AffinePushforward
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineOpen
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StructureSheafDegreeZero
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.PushforwardAffine
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.FlatFinitePresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Schemes on which every finite flat module is finite locally free

Let `X` be a scheme. A quasi-coherent `𝒪_X`-module of finite type which is flat has free stalks,
but it need not be finite locally free: that fails exactly when some closed subset of `X` stable
under generalization is not open. This file proves the equivalence of the two conditions:

1. every quasi-coherent `𝒪_X`-module of finite type which is flat is finite locally free;
2. every closed subset of `X` stable under generalization is open.

For (2) `⇒` (1) the stalks of such a module are free, so its fibre rank is the rank of its
stalk; that function is upper semicontinuous and constant along specializations, so each locus
`{x | n ≤ fiberRank F x}` is closed and stable under generalization, hence open by (2), hence the
fibre rank is locally constant and Stacks Tag 05P2 applies.

For (1) `⇒` (2) a closed generalization-stable subset is the support of a unique flat closed
subscheme `i : Z ⟶ X` (Stacks Tag 04PW). The direct image `i_* 𝒪_Z` is then of finite type,
quasi-coherent and flat, so (1) makes it finite locally free; its support is therefore open, and
that support is the given subset.

## Main results

* `AlgebraicGeometry.isFlatOver_id_iff_isFlat`: flatness over the identity morphism, in the sense
  of Stacks Tag 08KT, is flatness.
* `AlgebraicGeometry.isFlat_pushforwardStructureSheaf`: the direct image of the structure sheaf
  along a flat affine morphism is a flat module on the target.
* `AlgebraicGeometry.Scheme.Modules.supp_pushforwardStructureSheaf_subschemeι`: the support of
  the direct image of the structure sheaf of a closed subscheme is that subscheme's support.
* `AlgebraicGeometry.Scheme.Modules.forall_isFiniteLocallyFree_iff_forall_isOpen` is Stacks
  Tag 053N: the two conditions above are equivalent.

## Implementation notes

The support of `i_* 𝒪_Z` is computed from its sections rather than from its stalks. Over an
affine open `U` the annihilator of `Γ(i_* 𝒪_Z, U)` is the kernel of `Γ(X, U) → Γ(Z, i⁻¹U)`,
because a function of the base acts on a section of the source by multiplication by its image;
that kernel is the ideal of the closed subscheme, so the support of the module of sections is the
vanishing locus of that ideal, and Stacks Tag 056I transfers this to the sheaf.

Flatness of `i_* 𝒪_Z` is obtained from flatness of `i` through flatness over a base (Stacks
Tag 08KT): the structure sheaf of the source of a flat morphism is flat over the target, and
along an affine morphism flatness over a base passes to the direct image (Stacks Tag 0FLM).
Taking the base to be `X` itself leaves flatness over the identity, which is flatness.

## References

* [Stacks Project, Tag 053N](https://stacks.math.columbia.edu/tag/053N)
* [Stacks Project, Tag 052U](https://stacks.math.columbia.edu/tag/052U)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
* [Stacks Project, Tag 04PW](https://stacks.math.columbia.edu/tag/04PW)
* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
* [Stacks Project, Tag 0FLM](https://stacks.math.columbia.edu/tag/0FLM)
* [Stacks Project, Tag 056I](https://stacks.math.columbia.edu/tag/056I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

section FlatOverIdentity

/-- **Flatness over the identity is flatness.** Stacks Tag 08KT applied to `𝟙 X` says that every
stalk of `F`, read as a module over the local ring of `X` through the stalk map of the identity,
is flat; that stalk map is the identity, so the condition is flatness of `F` itself. -/
theorem isFlatOver_id_iff_isFlat {X : Scheme.{u}} (F : X.Modules) :
    IsFlatOver (𝟙 X : X ⟶ X).toLRSHom.toShHom F ↔
      AlgebraicGeometry.SheafOfModules.IsFlat
        (C := TopologicalSpace.Opens X.toTopCat)
        (J := Opens.grothendieckTopology X.toTopCat) (O := X.sheaf) F := by
  have hmod : ∀ x : X, Module.compHom
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x)
        ((𝟙 X : X ⟶ X).toLRSHom.toShHom.hom.stalkMap x).hom =
      (inferInstance : Module (ToType (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x)) := by
    intro x
    have hid : ((𝟙 X : X ⟶ X).toLRSHom.toShHom.hom.stalkMap x :
        X.presheaf.stalk x ⟶ X.presheaf.stalk x) = 𝟙 (X.presheaf.stalk x) :=
      AlgebraicGeometry.PresheafedSpace.stalkMap.id _ x
    refine Module.ext' _ _ fun a m => ?_
    exact congrArg (fun r : ToType (X.presheaf.stalk x) => r • m)
      (congrArg (fun φ : X.presheaf.stalk x ⟶ X.presheaf.stalk x =>
        (CommRingCat.Hom.hom φ) a) hid)
  refine Iff.trans (forall_congr' fun x => ?_)
    (AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat X.sheaf F).symm
  exact Iff.of_eq (congrArg (fun inst : Module (ToType (X.presheaf.stalk x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x) =>
    @Module.Flat _ _ _ _ inst) (hmod x))

/-- **The direct image of the structure sheaf along a flat affine morphism is flat.** The
structure sheaf of the source of a flat morphism is flat over the target (Stacks Tag 08KT), and
along an affine morphism flatness over a base passes to the direct image (Stacks Tag 0FLM); over
the base `X` itself, flatness over the identity is flatness. -/
theorem isFlat_pushforwardStructureSheaf {Z X : Scheme.{u}} (i : Z ⟶ X) [IsAffineHom i]
    [Flat i] :
    AlgebraicGeometry.SheafOfModules.IsFlat
      (C := TopologicalSpace.Opens X.toTopCat)
      (J := Opens.grothendieckTopology X.toTopCat) (O := X.sheaf)
      (Stacks.Morphisms.pushforwardStructureSheaf i) :=
  (isFlatOver_id_iff_isFlat _).mp
    ((isFlatOver_pushforward_iff i (𝟙 X) (structureSheafModule Z)).mp
      (by simpa only [Category.comp_id] using isFlatOver_structureSheafModule i))

end FlatOverIdentity

namespace Scheme.Modules

section Support

/-- **The annihilator of the sections of a direct image of a structure sheaf.** A function of the
base acts on a section of `f_* 𝒪_Y` by multiplication by its image, so it annihilates all of them
exactly when that image vanishes. -/
theorem annihilator_sections_pushforwardStructureSheaf {Y X : Scheme.{u}} (f : Y ⟶ X)
    (U : X.Opens) :
    Module.annihilator Γ(X, U) Γ(Stacks.Morphisms.pushforwardStructureSheaf f, U) =
      RingHom.ker (f.app U).hom := by
  ext a
  rw [Module.mem_annihilator, RingHom.mem_ker]
  refine ⟨fun h => ?_, fun h m => ?_⟩
  · have h1 : (f.app U).hom a * (1 : Γ(Y, f ⁻¹ᵁ U)) = 0 :=
      h (show Γ(Stacks.Morphisms.pushforwardStructureSheaf f, U) from (1 : Γ(Y, f ⁻¹ᵁ U)))
    simpa using h1
  · change (f.app U).hom a * (show Γ(Y, f ⁻¹ᵁ U) from m) = 0
    rw [h, zero_mul]

/-- **The support of the direct image of the structure sheaf of a closed subscheme is the support
of that subscheme.** Over an affine open the sections of `i_* 𝒪_Z` are a quotient of the
functions on that open by the ideal of the subscheme, so the support of the module of sections is
the vanishing locus of that ideal. -/
@[ega "IV 19.1.7" "closed support of O_X/J"]
theorem supp_pushforwardStructureSheaf_subschemeι {X : Scheme.{u}} (I : X.IdealSheafData) :
    SheafOfModules.supp (Stacks.Morphisms.pushforwardStructureSheaf I.subschemeι)
      = (I.support : Set X) := by
  ext x
  obtain ⟨W, hW, hxW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := x) (by trivial)
  let U : X.affineOpens := ⟨W, hW⟩
  let F := Stacks.Morphisms.pushforwardStructureSheaf I.subschemeι
  have hxU : x ∈ U.1 := hxW
  have hfin : Module.Finite Γ(X, U.1) Γ(F, U.1) := by
    refine Module.Finite.of_surjective
      ({ toFun := fun a => (I.subschemeι.app U.1).hom a
         map_add' := map_add (I.subschemeι.app U.1).hom
         map_smul' := fun r a => map_mul (I.subschemeι.app U.1).hom r a } :
        Γ(X, U.1) →ₗ[Γ(X, U.1)] Γ(F, U.1)) (I.subschemeι_app_surjective U)
  have h2 : U.2.primeIdealOf ⟨x, hxU⟩ ∈ Module.support Γ(X, U.1) Γ(F, U.1) ↔
      x ∈ X.zeroLocus (U := U.1) (I.ideal U) := by
    rw [Module.support_eq_zeroLocus,
      (annihilator_sections_pushforwardStructureSheaf I.subschemeι U.1).trans
        (I.ker_subschemeι_app U), ← U.2.fromSpec_preimage_zeroLocus]
    exact Iff.of_eq (congrArg (fun z : X => z ∈ X.zeroLocus (U := U.1) (I.ideal U))
      (U.2.fromSpec_primeIdealOf ⟨x, hxU⟩))
  exact (mem_support_sections_iff_mem_supp F U x hxU).symm.trans
    (h2.trans (I.mem_support_iff_of_mem (U := U) hxU).symm)

/-- **The direct image of the structure sheaf of a closed subscheme is of finite type.** The
canonical map `𝒪_X ⟶ i_* 𝒪_Z` is an epimorphism and `𝒪_X` is of finite type over itself. -/
theorem isFiniteType_pushforwardStructureSheaf_of_isClosedImmersion {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    _root_.SheafOfModules.IsFiniteType.{u, u, u}
      (Stacks.Morphisms.pushforwardStructureSheaf i) := by
  have := epi_unitToPushforwardObjUnit i
  apply Stacks.SheafOfModules.isFiniteType_of_epi
    (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)
  exact structureSheaf_isFiniteType X

end Support

section Equivalence

/-- **Stacks Project, Tag 053N.** For a scheme `X` the following are equivalent: every
quasi-coherent `𝒪_X`-module of finite type which is flat is finite locally free; every closed
subset of `X` stable under generalization is open. -/
@[stacks 053N]
theorem forall_isFiniteLocallyFree_iff_forall_isOpen (X : Scheme.{u}) :
    (∀ F : X.Modules, _root_.SheafOfModules.IsFiniteType.{u, u, u} F → F.IsQuasicoherent →
        AlgebraicGeometry.SheafOfModules.IsFlat
            (C := TopologicalSpace.Opens X.toTopCat)
            (J := Opens.grothendieckTopology X.toTopCat) (O := X.sheaf) F →
          AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
            (R := X.ringCatSheaf) F) ↔
      ∀ Z : Set X, IsClosed Z → StableUnderGeneralization Z → IsOpen Z := by
  refine ⟨fun hyp Z hZc hZg => ?_, fun h F hft hqc hflat => ?_⟩
  · obtain ⟨I, hIflat, hIsupp⟩ :=
      (support_bijOn_flat_closedImmersions X).surjOn
        (show (⟨Z, hZc⟩ : Closeds X) ∈ {C : Closeds X | StableUnderGeneralization (C : Set X)}
          from hZg)
    have hflat : Flat I.subschemeι := hIflat
    have hopen := isOpen_supp_of_isFiniteLocallyFree _
      (hyp (Stacks.Morphisms.pushforwardStructureSheaf I.subschemeι)
        (isFiniteType_pushforwardStructureSheaf_of_isClosedImmersion I.subschemeι)
        inferInstance (isFlat_pushforwardStructureSheaf I.subschemeι))
    rwa [supp_pushforwardStructureSheaf_subschemeι I,
      congrArg (fun C : Closeds X => (C : Set X)) hIsupp] at hopen
  · have hfree : ∀ x : X,
        let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) F.val x
        Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x) := fun x =>
      Stacks.StalkFiniteType.free_stalk_of_flat F x
        ((AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat X.sheaf F).mp hflat x)
    exact isFiniteLocallyFree_of_free_stalk_of_isLocallyConstant F hft hfree
      (isLocallyConstant_fiberRank_of_forall_isOpen F hfree h)

end Equivalence

end Scheme.Modules

end AlgebraicGeometry

end
