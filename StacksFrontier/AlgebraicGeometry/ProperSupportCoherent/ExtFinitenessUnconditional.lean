module

public import StacksFrontier.Algebra.Homology.DerivedHomologyLinear
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeCoherentDerivedHom
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.BoundedBelowUnconditional
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessAffineBase
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessGlobalSectionsForget
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessLeray
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessLinear
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCategorySections
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorDualGlobalFunctoriality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finiteness of the Ext modules on a proper scheme over the base ring

Let `A` be a Noetherian ring, let `X` be a scheme proper over `A`, let `K` be an object of
`D^-_Coh(𝒪_X)` and let `L` be an object of `D^+_Coh(𝒪_X)`. [Stacks, Tag 0D0D] asserts that the
`A`-modules `Ext^n_{𝒪_X}(K, L)` are finite for every `n`. This file proves that.

The proof is the source's:

`Ext^n_{𝒪_X}(K, L) = Hom_{D(𝒪_X)}(K, L⟦n⟧) = H^0(X, R𝓗om(K, L⟦n⟧))`,

by [Stacks, Tag 08DK]; `R𝓗om(K, L⟦n⟧)` lies in `D^+_Coh(𝒪_X)` by [Stacks, Tag 0D0C]; derived
global sections over `A` factor through the derived direct image by [Stacks, Tag 0D5W], and
`Rf_* R𝓗om(K, L⟦n⟧)` lies in `D^+_Coh(𝒪_{Spec A})` by [Stacks, Tag 0D0B]; and on the affine
base the degree-zero cohomology of derived global sections is the global sections of the
degree-zero cohomology sheaf ([Stacks, Tag 06Z0]), which is a finite `A`-module because that
sheaf is coherent.

## Main results

* `Stacks.AlgebraicGeometry.ProperSupportCoherent.extAddEquiv` and
  `Stacks.AlgebraicGeometry.ProperSupportCoherent.extAddEquiv_map_smul`: **[Stacks, Tag 08DK]
  over the base ring** — `Hom_{D(𝒪_X)}(K, M)` is the degree-zero cohomology of
  `RΓ(X, R𝓗om(K, M))` as an `A`-module.
* `…ProperSupportCoherent.moduleFinite_homologyZero_derivedGlobalSections_of_proper`:
  for `H` in `D^+_Coh(𝒪_X)` with `X` proper over `A`, the `A`-module `H^0(X, H)` is finite.
* `Stacks.AlgebraicGeometry.ProperSupportCoherent.moduleFinite_ext_of_proper`:
  **[Stacks, Tag 0D0D]**.

## Implementation notes

**Where the `A`-module structure comes from.** `Ext^n_{𝒪_X}(K, L)` is
`DerivedCategory.Ext K L n`, that is `Hom_{D(𝒪_X)}(K, L⟦n⟧)`, and its `A`-module structure is the
one of the canonical `A`-linear structure `AlgebraicGeometry.modulesLinear` on `𝒪_X`-modules,
induced by the structure morphism `X ⟶ Spec A`. Making [Stacks, Tag 08DK] an isomorphism of
`A`-modules rather than merely of abelian groups is the content of
`StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/ExtFinitenessLinear.lean`: the derived
internal Hom and derived global sections both carry multiplication by a base scalar to
multiplication by that scalar, so the identification of Tag 08DK — which is natural in the
second variable — carries the scalar action on one side to the scalar action on the other. The
passage between the abelian-group-valued hypercohomology in which Tag 08DK is stated and the
`A`-module-valued derived global sections is
`StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/ExtFinitenessGlobalSectionsForget.lean`.

**Why the proper support hypothesis of [Stacks, Tag 0D0B] is free here.** That tag asks the
support of every cohomology sheaf of the complex to be proper over the base. For `X` proper over
`A` every closed subscheme of `X` is proper over `A`, since a closed immersion is proper and
properness is stable under composition, so the hypothesis is discharged by instance search.

**The derived-category model.** Everything runs at `CategoryTheory.HasDerivedCategory.standard`,
pinned at a priority high enough to displace the locally small model: the import cone of
[Stacks, Tag 0D0B] passes through Chow's lemma, which contributes a competing
`HasDerivedCategory` instance, and at the other model the statements of the inputs are about a
different category.

## References

* [Stacks Project, Tag 0D0D](https://stacks.math.columbia.edu/tag/0D0D)
* [Stacks Project, Tag 0D0C](https://stacks.math.columbia.edu/tag/0D0C)
* [Stacks Project, Tag 0D0B](https://stacks.math.columbia.edu/tag/0D0B)
* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.ModuleSections (derivedModuleGlobalSections)

universe u

namespace Stacks.AlgebraicGeometry.ProperSupportCoherent

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] (X : Over (Spec (CommRingCat.of A)))

/-! ### `D^+_Coh` is stable under the shift -/

/-- The shift of an object of `D^+_Coh(𝒪_X)` is an object of `D^+_Coh(𝒪_X)`. -/
theorem derivedCategoryBPlus_isCoherent_shift {Y : Scheme.{u}}
    (L : DerivedCategory Y.Modules)
    (hL : DerivedCategoryB.derivedCategoryBPlus (fun M : Y.Modules => M.IsCoherent) L) (n : ℤ) :
    DerivedCategoryB.derivedCategoryBPlus (fun M : Y.Modules => M.IsCoherent) (L⟦n⟧) := by
  refine ⟨DerivedCategoryB.isBoundedBelow_shift n hL.1, fun i => ?_⟩
  have e : (DerivedCategory.homologyFunctor Y.Modules i).obj (L⟦n⟧) ≅
      (DerivedCategory.homologyFunctor Y.Modules (n + i)).obj L :=
    ((DerivedCategory.homologyFunctor Y.Modules 0).shiftIso n i (n + i) rfl).app L
  exact _root_.AlgebraicGeometry.isCoherent_of_modulesIso e.symm (hL.2 (n + i))

/-! ### The `A`-module `H^0(X, R𝓗om(K, -))` -/

/-- `H^0(X, R𝓗om(K, -))` as a functor valued in `A`-modules: the derived internal Hom out of
`K`, followed by `A`-linear derived global sections and degree-zero cohomology.

It carries multiplication by a base scalar to multiplication by that scalar, each of its three
factors doing so; that is the `hsmul` step inside `extAddEquiv_map_smul`, the one place it is
needed, and `AlgebraicGeometry.derivedSheafHomFunctor_map_smul_id` of
`StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/ExtFinitenessLinear.lean` is the clause of
it that is not formal. -/
def extModuleFunctor (K : DerivedCategory X.left.Modules) :
    DerivedCategory X.left.Modules ⥤ ModuleCat.{u} A :=
  _root_.AlgebraicGeometry.derivedSheafHomFunctor X K ⋙
    derivedGlobalSectionsOver X.hom ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0

/-! ### Stacks 08DK over the base ring -/

/-- The identification of [Stacks, Tag 08DK] on a scheme, as an isomorphism of abelian groups
between the degree-zero cohomology of `RΓ(X, R𝓗om(K, M))` over `A`, with its scalars forgotten,
and `Hom_{D(𝒪_X)}(K, M)`. -/
def extAddEquiv (K M : DerivedCategory X.left.Modules) :
    ((extModuleFunctor X K).obj M : Type u) ≃+ (K ⟶ M) :=
  ((homologyZeroForgetIso X.hom
      ((_root_.AlgebraicGeometry.derivedSheafHomFunctor X K).obj
        M)).addCommGroupIsoToAddEquiv).trans
    (Stacks.SheafOfModules.derivedSheafHomGlobalSectionsEquiv X.left.sheaf K M)

/-- Transfer of module finiteness along an additive bijection compatible with the scalars. -/
private theorem moduleFinite_of_addEquiv {R : Type*} [Ring R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃+ N)
    (h : ∀ (r : R) (m : M), e (r • m) = r • e m) (hM : Module.Finite R M) :
    Module.Finite R N :=
  let := hM
  Module.Finite.equiv ({ __ := e, map_smul' := h } : M ≃ₗ[R] N)

/-- The comparison of `A`-linear with abelian-group-valued degree-zero hypercohomology is
natural: it carries the map induced by an endomorphism of the complex to the map induced by that
endomorphism. This is the naturality of `homologyZeroForgetNatIso`, read on elements. -/
private theorem homologyZeroForget_naturality_apply (H : DerivedCategory X.left.Modules)
    (φ : H ⟶ H) (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      ((derivedGlobalSectionsOver X.hom).obj H)) :
    (homologyZeroForgetIso X.hom H).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          ((derivedGlobalSectionsOver X.hom).map φ)) x) =
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections (Stacks.SheafOfModules.ringedSite X.left.sheaf)).map φ))
        ((homologyZeroForgetIso X.hom H).hom x) :=
  ((CategoryTheory.comp_apply
      ((derivedGlobalSectionsOver X.hom ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0 ⋙
        forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).map φ)
      ((homologyZeroForgetNatIso X.hom).hom.app H) x).symm.trans
    (ConcreteCategory.congr_hom ((homologyZeroForgetNatIso X.hom).hom.naturality φ) x)).trans
      (CategoryTheory.comp_apply ((homologyZeroForgetNatIso X.hom).hom.app H)
        ((derivedModuleGlobalSections (Stacks.SheafOfModules.ringedSite X.left.sheaf) ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map φ) x)

/-- **[Stacks, Tag 08DK] over the base ring.** The identification of `Hom_{D(𝒪_X)}(K, M)` with
the degree-zero cohomology of `RΓ(X, R𝓗om(K, M))` carries the action of a base scalar to the
action of that scalar.

The underlying identification of abelian groups is Tag 08DK. It is `A`-linear because the
identification is natural in the second variable, because `R𝓗om(K, -)` and `RΓ(X, -)` both carry
multiplication by a base scalar to multiplication by that scalar, and because the scalar action
on `Hom_{D(𝒪_X)}(K, M)` is postcomposition with multiplication by the scalar on `M`. -/
theorem extAddEquiv_map_smul (K M : DerivedCategory X.left.Modules) (a : A)
    (x : (extModuleFunctor X K).obj M) :
    letI : Linear A X.left.Modules := modulesLinear A X
    extAddEquiv X K M (a • x) = a • extAddEquiv X K M x := by
  let : Linear A X.left.Modules := modulesLinear A X
  have hsmul : ((extModuleFunctor X K).map (a • 𝟙 M)) x = a • x := by
    have hfun : (extModuleFunctor X K).map (a • 𝟙 M) =
        a • 𝟙 ((extModuleFunctor X K).obj M) := by
      change (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          ((derivedGlobalSectionsOver X.hom).map
            ((_root_.AlgebraicGeometry.derivedSheafHomFunctor X K).map (a • 𝟙 M))) = _
      rw [_root_.AlgebraicGeometry.derivedSheafHomFunctor_map_smul_id,
        _root_.AlgebraicGeometry.derivedGlobalSectionsOver_map_smul_id,
        Functor.Linear.map_smul, CategoryTheory.Functor.map_id]
      rfl
    rw [hfun]
    rfl
  have key := homologyZeroForget_naturality_apply X
    ((_root_.AlgebraicGeometry.derivedSheafHomFunctor X K).obj M)
    (((Stacks.SheafOfModules.derivedSheafHom X.left.sheaf).obj (op K)).map (a • 𝟙 M)) x
  have key2 : (homologyZeroForgetIso X.hom
        ((_root_.AlgebraicGeometry.derivedSheafHomFunctor X K).obj M)).hom (a • x) =
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections
          (Stacks.SheafOfModules.ringedSite X.left.sheaf)).map
            (((Stacks.SheafOfModules.derivedSheafHom X.left.sheaf).obj (op K)).map (a • 𝟙 M))))
        ((homologyZeroForgetIso X.hom
          ((_root_.AlgebraicGeometry.derivedSheafHomFunctor X K).obj M)).hom x) :=
    (congrArg (fun y => (homologyZeroForgetIso X.hom
      ((_root_.AlgebraicGeometry.derivedSheafHomFunctor X K).obj M)).hom y) hsmul).symm.trans key
  have h08DK := Stacks.SheafOfModules.derivedSheafHomGlobalSectionsEquiv_naturality_target
    X.left.sheaf K (a • 𝟙 M)
    ((homologyZeroForgetIso X.hom
      ((_root_.AlgebraicGeometry.derivedSheafHomFunctor X K).obj M)).hom x)
  have hlast : ∀ g : K ⟶ M, g ≫ (a • 𝟙 M) = a • g := fun g => by
    rw [Linear.comp_smul, Category.comp_id]
  exact (congrArg (fun y => Stacks.SheafOfModules.derivedSheafHomGlobalSectionsEquiv
    X.left.sheaf K M y) key2).trans (h08DK.trans (hlast _))

/-! ### Finiteness of the degree-zero hypercohomology of a bounded below coherent complex -/

/-- **The degree-zero hypercohomology of an object of `D^+_Coh(𝒪_X)` on a scheme proper over a
Noetherian ring is a finite module over that ring.** Derived global sections over `A` factor
through the derived direct image ([Stacks, Tag 0D5W]), which carries `D^+_Coh(𝒪_X)` into
`D^+_Coh(𝒪_{Spec A})` ([Stacks, Tag 0D0B]); on the affine base the degree-zero cohomology of
derived global sections is the global sections of the degree-zero cohomology sheaf
([Stacks, Tag 06Z0]), and a coherent module on the spectrum of a Noetherian ring has finite
global sections. -/
@[ega "III 3.2.3" "more general", ega "III 6.2.5" "special case"]
theorem moduleFinite_homologyZero_derivedGlobalSections_of_proper [IsNoetherianRing A]
    [IsProper X.hom] (H : DerivedCategory X.left.Modules)
    (hH : DerivedCategoryB.derivedCategoryBPlus (fun M : X.left.Modules => M.IsCoherent) H) :
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      ((derivedGlobalSectionsOver X.hom).obj H)) := by
  have : IsLocallyNoetherian (Spec (CommRingCat.of A)) := inferInstance
  have : IsNoetherian (Spec (CommRingCat.of A)) := inferInstance
  have : LocallyOfFiniteType X.hom := inferInstance
  have hsupp : ∀ j : ℤ, _root_.AlgebraicGeometry.IsProperOver X.hom
      ⟨SheafOfModules.supp ((DerivedCategory.homologyFunctor X.left.Modules j).obj H),
        @SheafOfModules.isClosed_supp _ _ _ (hH.2 j).isFiniteType⟩ := by
    intro j
    exact inferInstance
  have hpush := derivedCategoryBPlus_derivedPushforward_of_properSupp X.hom H hH hsupp
  have hfin := moduleFinite_homologyZero_derivedGlobalSections
    ((derivedPushforwardModules X.hom).obj H)
    (fun i => have := hpush.2 i
      (CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1) (hpush.2 0)
  have hfin' : Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      ((derivedPushforwardModules X.hom ⋙
        derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of A)))).obj H)) := hfin
  let := hfin'
  exact Module.Finite.equiv
    (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).mapIso
      ((_root_.AlgebraicGeometry.derivedGlobalSectionsOverPushforwardIso
        X.hom).app H)).toLinearEquiv).symm

/-! ### Stacks 0D0D -/

/-- **Stacks Project, Tag 0D0D.** Let `A` be a Noetherian ring, let `X` be a scheme proper over
`A`, let `K` be an object of `D^-_Coh(𝒪_X)` and let `L` be an object of `D^+_Coh(𝒪_X)`. Then the
`A`-module `Ext^n_{𝒪_X}(K, L)` is finite, for every `n`, the `A`-action being the canonical one
induced by the structure morphism `X ⟶ Spec A`.

`Ext^n_{𝒪_X}(K, L)` is `Hom_{D(𝒪_X)}(K, L⟦n⟧)`, which is the degree-zero cohomology of
`RΓ(X, R𝓗om(K, L⟦n⟧))` as an `A`-module by `extLinearEquiv`, that is by [Stacks, Tag 08DK];
`R𝓗om(K, L⟦n⟧)` is an object of `D^+_Coh(𝒪_X)` by [Stacks, Tag 0D0C], the shift of `L` being one
by `derivedCategoryBPlus_isCoherent_shift`; and
`moduleFinite_homologyZero_derivedGlobalSections_of_proper` makes the degree-zero
hypercohomology of such an object a finite `A`-module. -/
@[stacks 0D0D]
theorem moduleFinite_ext_of_proper {A : Type u} [CommRing A] [IsNoetherianRing A]
    (X : Over (Spec (CommRingCat.of A))) [IsProper X.hom]
    (K L : DerivedCategory X.left.Modules)
    (hK : DerivedCategoryB.derivedCategoryBMinus
      (fun M : X.left.Modules => M.IsCoherent) K)
    (hL : DerivedCategoryB.derivedCategoryBPlus
      (fun M : X.left.Modules => M.IsCoherent) L)
    (n : ℤ) :
    letI : Linear A X.left.Modules := modulesLinear A X
    Module.Finite A (DerivedCategory.Ext K L n) := by
  let : Linear A X.left.Modules := modulesLinear A X
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have hM := derivedCategoryBPlus_isCoherent_shift L hL n
  have hH : DerivedCategoryB.derivedCategoryBPlus
      (fun M : X.left.Modules => M.IsCoherent)
      ((_root_.AlgebraicGeometry.derivedSheafHomFunctor X K).obj (L⟦n⟧)) := by
    have e : (fun M : X.left.Modules => M.IsCoherent) =
        Stacks.SheafOfModules.coherentModules X.left.ringCatSheaf :=
      CoherentAbelian.coherentModules_eq
    rw [e] at hK hM ⊢
    exact _root_.AlgebraicGeometry.derivedCategoryBPlus_isCoherent_derivedSheafHom X.left
      K (L⟦n⟧) hK hM
  have hfin := moduleFinite_homologyZero_derivedGlobalSections_of_proper X
    ((_root_.AlgebraicGeometry.derivedSheafHomFunctor X K).obj (L⟦n⟧)) hH
  exact moduleFinite_of_addEquiv (extAddEquiv X K (L⟦n⟧))
    (fun a x => extAddEquiv_map_smul X K (L⟦n⟧) a x) hfin

end Stacks.AlgebraicGeometry.ProperSupportCoherent

end
