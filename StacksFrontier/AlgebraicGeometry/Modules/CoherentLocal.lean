module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherenceClosure
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic

/-!
# Coherence of a sheaf of modules on a scheme is local on the base

Let `X` be a scheme and `M` an `𝒪_X`-module. With restriction to an open subscheme written as
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` along its inclusion, the restriction of a
coherent module to an open subscheme is coherent, and a module whose restrictions to the members
of an open covering are all coherent is coherent.

## Main definitions

* `AlgebraicGeometry.Modules.restrictCompIso`: two iterated restrictions of `M` along equal
  composites of open immersions agree.
* `AlgebraicGeometry.Modules.resOpen`: an open immersion `f`, restricted to the preimage of an
  open `U` of the target, read as a morphism into the open subscheme `U`.
* `AlgebraicGeometry.Modules.KernelIsFiniteType`: the second condition of [Stacks, Tag 01BV] for
  a single sheaf of modules on a scheme — the kernel of every morphism into it from a finite free
  sheaf of modules is of finite type.

## Main results

* `AlgebraicGeometry.Modules.isCoherent_restrict`: **coherence passes to open subschemes.**
* `AlgebraicGeometry.Modules.isCoherent_of_restrict`: **coherence is local on the base.**
* `AlgebraicGeometry.Modules.isCoherent_iff`: [Stacks, Tag 01BV] read on open subschemes — a
  module is coherent exactly when it is of finite type and, over every open subscheme, the kernel
  of every morphism into its restriction from a finite free module is of finite type.
* `AlgebraicGeometry.Modules.isFiniteType_restrict` and
  `AlgebraicGeometry.Modules.isFiniteType_of_restrict`: finite type passes to open subschemes and
  is local on a scheme.
* `AlgebraicGeometry.Modules.isFiniteType_equivOver_functor`,
  `AlgebraicGeometry.Modules.isFiniteType_equivOver_inverse`,
  `AlgebraicGeometry.Modules.isFiniteType_overEquiv_functor` and
  `AlgebraicGeometry.Modules.isFiniteType_overEquiv_inverse`: being of finite type transports both
  ways across the equivalence between modules on the slice site over an open and modules on the
  open subscheme.
* `AlgebraicGeometry.Modules.preservesFiniteLimits_restrictFunctor`,
  `AlgebraicGeometry.Modules.preservesColimits_restrictFunctor` and
  `AlgebraicGeometry.Modules.preservesZeroMorphisms_restrictFunctor`: restriction along an open
  immersion is left exact, preserves colimits and preserves zero morphisms.

## Implementation notes

The namespace is `AlgebraicGeometry.Modules` rather than one under `Stacks`: inside `Stacks.*` the
name `SheafOfModules.IsCoherent` resolves to `Stacks.SheafOfModules.IsCoherent`, a different
constant from the root `SheafOfModules.IsCoherent` that every statement here is about.

`Stacks.SheafOfModules.isFiniteType_pushforward` is applied with its arguments positional, so that
the proof of `IsIso φ` on the ring-sheaf morphism is supplied rather than searched for: instance
search does not find it.

The instances `PreservesColimitsOfShape`, `PreservesFiniteLimits` and `PreservesZeroMorphisms`
for the `Scheme.Modules` restriction and `overEquiv` functors are not found by instance search, so
each is bound by a `have` and passed by name to
`Stacks.AlgebraicGeometry.CoherentKernel.mapFreeHom` and `kernelMapFreeIso`.

## References

* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 01BD](https://stacks.math.columbia.edu/tag/01BD)
-/

@[expose] public section

open CategoryTheory Limits SheafOfModules TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.CoherentTFAE (generatingSectionsRestrict restrictIsoSelf
  isFiniteType_of_restrict_generatingSections)
open AlgebraicGeometry.Scheme.Modules (restrictFunctor restrictFunctorComp restrictFunctorCongr
  restrictFunctorId overEquiv overFunctorEquiv restrictUnitIso)

universe u

namespace AlgebraicGeometry.Modules

variable {X : Scheme.{u}}

/-- Two iterated restrictions of `M` along equal composites agree. -/
noncomputable def restrictCompIso {Y Y' Z : Scheme.{u}} (M : X.Modules)
    (a : Y ⟶ X) [IsOpenImmersion a] (b : Z ⟶ Y) [IsOpenImmersion b]
    (a' : Y' ⟶ X) [IsOpenImmersion a'] (b' : Z ⟶ Y') [IsOpenImmersion b']
    (h : b ≫ a = b' ≫ a') :
    ((restrictFunctor b).obj ((restrictFunctor a).obj M)) ≅
      ((restrictFunctor b').obj ((restrictFunctor a').obj M)) :=
  ((restrictFunctorComp b a).app M).symm ≪≫ (restrictFunctorCongr h).app M ≪≫
    (restrictFunctorComp b' a').app M

/-- An open immersion `f`, restricted to the preimage of an open `U`, as a morphism into the
open subscheme `U`. -/
noncomputable def resOpen {Z : Scheme.{u}} (f : Z ⟶ X) [IsOpenImmersion f] (U : X.Opens) :
    (f ⁻¹ᵁ U).toScheme ⟶ U.toScheme :=
  (f.isoImage (f ⁻¹ᵁ U)).hom ≫ X.homOfLE (f.image_preimage_le U)

/-- `resOpen f U` is an open immersion. -/
instance isOpenImmersion_resOpen {Z : Scheme.{u}} (f : Z ⟶ X) [IsOpenImmersion f]
    (U : X.Opens) : IsOpenImmersion (resOpen f U) :=
  inferInstanceAs (IsOpenImmersion
    ((f.isoImage (f ⁻¹ᵁ U)).hom ≫ X.homOfLE (f.image_preimage_le U)))

/-- `resOpen f U` followed by the inclusion of `U` is the inclusion of `f ⁻¹ᵁ U` followed by
`f`. -/
@[reassoc]
theorem resOpen_comp_ι {Z : Scheme.{u}} (f : Z ⟶ X) [IsOpenImmersion f] (U : X.Opens) :
    resOpen f U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f := by
  rw [resOpen, Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoImage_hom_ι]

/-- The functor of `overEquiv V` is a left adjoint. -/
noncomputable instance isLeftAdjointOverEquivFunctor (V : X.Opens) :
    Functor.IsLeftAdjoint (overEquiv V).functor :=
  (overEquiv V).toAdjunction.isLeftAdjoint

/-- Generating sections of `M.over V` give generating sections of `M.restrict V.ι`. -/
noncomputable def generatingSectionsRestrictOfOver (V : X.Opens) (M : X.Modules)
    (σ : (M.over V).GeneratingSections) : ((restrictFunctor V.ι).obj M).GeneratingSections :=
  have hcolim : PreservesColimitsOfSize.{u, u} (overEquiv V).functor := inferInstance
  Stacks.AlgebraicGeometry.CoherentKernel.generatingSectionsOfMap
    (hcolimΨ := hcolim) (overEquiv V).functor (Iso.refl _) ((overFunctorEquiv V).app M) σ

/-- `generatingSectionsRestrictOfOver` keeps the index type of the generating sections. -/
@[simp]
theorem generatingSectionsRestrictOfOver_I (V : X.Opens) (M : X.Modules)
    (σ : (M.over V).GeneratingSections) : (generatingSectionsRestrictOfOver V M σ).I = σ.I :=
  rfl

section TopCatLevel

variable {T : TopCat.{u}} (U : Opens T) (R : T.Sheaf RingCat.{u})

/-- The functor of `Opens.sheafOfModulesEquivOver U R` sends a module of finite type to a module
of finite type. -/
theorem isFiniteType_equivOver_functor
    {N : SheafOfModules.{u} (R.over U)} (h : N.IsFiniteType) :
    ((Opens.sheafOfModulesEquivOver U R).functor.obj N).IsFiniteType :=
  @Stacks.SheafOfModules.isFiniteType_pushforward _ _ _ _ _ _ _ _ _ _ _ _ _ _
    U.overEquivalence.inverse _ _ _ _ (U.overPullbackSheafEquivOver.app R).inv
    (Iso.isIso_inv _) (Iso.refl _) _ h

/-- The inverse of `Opens.sheafOfModulesEquivOver U R` sends a module of finite type to a module
of finite type. -/
theorem isFiniteType_equivOver_inverse
    {N : SheafOfModules.{u} (U.sheafRestrict.obj R)} (h : N.IsFiniteType) :
    ((Opens.sheafOfModulesEquivOver U R).inverse.obj N).IsFiniteType :=
  @Stacks.SheafOfModules.isFiniteType_pushforward _ _ _ _ _ _ _ _ _ _ _ _ _ _
    U.overEquivalence.functor _ _ _ _ (U.sheafRestrictSheafEquivOver.app R).inv
    (Iso.isIso_inv _) (Opens.sheafOfModulesEquivOverInverseUnit U R) _ h

end TopCatLevel

/-! ### Finite type across `overEquiv`, and on open subschemes -/

/-- The functor of `overEquiv V` sends a module of finite type on the slice site over `V` to a
module of finite type on the open subscheme `V`. -/
theorem isFiniteType_overEquiv_functor {V : X.Opens}
    {N : SheafOfModules.{u} (X.ringCatSheaf.over V)} (h : N.IsFiniteType) :
    ((overEquiv V).functor.obj N).IsFiniteType :=
  isFiniteType_equivOver_functor V X.ringCatSheaf h

/-- The inverse of `overEquiv V` sends a module of finite type on the open subscheme `V` to a
module of finite type on the slice site over `V`. -/
theorem isFiniteType_overEquiv_inverse {V : X.Opens} {N : V.toScheme.Modules}
    (h : N.IsFiniteType) : ((overEquiv V).inverse.obj N).IsFiniteType :=
  isFiniteType_equivOver_inverse V X.ringCatSheaf h

/-- A module of finite type on a scheme is, on each member of some open covering, generated by
finitely many sections of its restriction. -/
theorem exists_isOpenCover_generatingSections (M : X.Modules) (h : M.IsFiniteType) :
    ∃ (I : Type u) (U : I → X.Opens) (_ : IsOpenCover U)
      (σ : ∀ i, ((restrictFunctor (U i).ι).obj M).GeneratingSections), ∀ i, Finite (σ i).I := by
  have := h
  obtain ⟨d, hd⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  exact ⟨d.I, d.X, (Opens.coversTop_iff _ d.X).mp d.coversTop,
    fun i => generatingSectionsRestrictOfOver (d.X i) M (d.generators i),
    fun i => (hd.isFiniteType i).finite⟩

/-- **Finite type is preserved by restriction along an open immersion.** -/
theorem isFiniteType_restrict {Z : Scheme.{u}} (f : Z ⟶ X) [IsOpenImmersion f] (M : X.Modules)
    (h : M.IsFiniteType) : ((restrictFunctor f).obj M).IsFiniteType := by
  obtain ⟨I, U, hU, σ, hσ⟩ := exists_isOpenCover_generatingSections M h
  refine isFiniteType_of_restrict_generatingSections _ (fun i => f ⁻¹ᵁ U i)
    (IsOpenCover.mk (f.iSup_preimage_eq_top hU)) (fun i => ?_) (fun i => ?_)
  · exact GeneratingSections.equivOfIso
      (restrictCompIso M (U i).ι (resOpen f (U i)) f (f ⁻¹ᵁ U i).ι (resOpen_comp_ι f (U i)))
      (generatingSectionsRestrict (resOpen f (U i)) (σ i))
  · exact hσ i

/-- Finite type is invariant under isomorphism. -/
theorem isFiniteType_of_iso {Z : Scheme.{u}} {N N' : SheafOfModules.{u} Z.ringCatSheaf}
    (e : N ≅ N') (h : N.IsFiniteType) : N'.IsFiniteType :=
  have := h
  Stacks.SheafOfModules.isFiniteType_of_iso.{u} e

/-- The same, for modules on the slice site over an open. -/
theorem isFiniteType_of_iso_over {V : X.Opens}
    {N N' : SheafOfModules.{u} (X.ringCatSheaf.over V)} (e : N ≅ N') (h : N.IsFiniteType) :
    N'.IsFiniteType :=
  have := h
  Stacks.SheafOfModules.isFiniteType_of_iso.{u} e

/-- **Finite type is local on a scheme.** -/
theorem isFiniteType_of_restrict (M : X.Modules) {I : Type u} (U : I → X.Opens)
    (hU : IsOpenCover U) (h : ∀ i, ((restrictFunctor (U i).ι).obj M).IsFiniteType) :
    M.IsFiniteType := by
  choose J W hW σ hσ using fun i =>
    exists_isOpenCover_generatingSections ((restrictFunctor (U i).ι).obj M) (h i)
  have key (i : I) : ⨆ k, (U i).ι ''ᵁ W i k = U i :=
    (Scheme.Hom.image_iSup (U i).ι (W i)).symm.trans <| by
      rw [show ⨆ k, W i k = ⊤ from hW i]; exact (U i).ι_image_top
  refine isFiniteType_of_restrict_generatingSections M (I := Σ i, J i)
    (fun j => (U j.1).ι ''ᵁ W j.1 j.2) (IsOpenCover.mk ?_)
    (fun j => GeneratingSections.equivOfIso
      (restrictIsoSelf ((U j.1).ι.isoImage (W j.1 j.2)).symm
        ((restrictFunctor ((U j.1).ι ''ᵁ W j.1 j.2).ι).obj M))
      (generatingSectionsRestrict ((U j.1).ι.isoImage (W j.1 j.2)).inv
        (GeneratingSections.equivOfIso
          (restrictCompIso M (U j.1).ι (W j.1 j.2).ι ((U j.1).ι ''ᵁ W j.1 j.2).ι
            ((U j.1).ι.isoImage (W j.1 j.2)).hom
            (Scheme.Hom.isoImage_hom_ι (U j.1).ι (W j.1 j.2)).symm)
          (σ j.1 j.2)))) (fun j => hσ j.1 j.2)
  rw [iSup_sigma, ← hU.iSup_eq_top]
  exact iSup_congr key

/-! ### The kernel condition of Tag 01BV, read on open subschemes -/

/-- The second condition of [Stacks, Tag 01BV] for a single sheaf of modules on a scheme: the
kernel of every morphism into it from a finite free sheaf of modules is of finite type. -/
def KernelIsFiniteType (Z : Scheme.{u}) (N : SheafOfModules.{u} Z.ringCatSheaf) : Prop :=
  ∀ (I : Type u), Finite I → ∀ φ : (free I : SheafOfModules.{u} Z.ringCatSheaf) ⟶ N,
    (kernel φ).IsFiniteType

/-- **Restriction along an open immersion is left exact.** -/
theorem preservesFiniteLimits_restrictFunctor {Y Z : Scheme.{u}} (f : Z ⟶ Y)
    [IsOpenImmersion f] : PreservesFiniteLimits (restrictFunctor f) :=
  Stacks.AlgebraicGeometry.RestrictionExact.preservesFiniteLimits_pushforward.{u} _

/-- The kernel condition is invariant under isomorphism. -/
theorem kernelIsFiniteType_of_iso {Z : Scheme.{u}} {N N' : SheafOfModules.{u} Z.ringCatSheaf}
    (e : N ≅ N') (h : KernelIsFiniteType Z N) : KernelIsFiniteType Z N' := fun I hI φ =>
  isFiniteType_of_iso (kernel.mapIso (φ ≫ e.inv) φ (Iso.refl _) e (by simp))
    (h I hI (φ ≫ e.inv))

/-- If `Φ` is left exact and preserves finite coproducts, and the kernels of all maps from a
finite free module to `N ≅ Φ.obj M` are of finite type, then so is `Φ.obj (kernel φ)`. -/
private theorem isFiniteType_obj_kernel {C D : Type u} [Category.{u} C] [Category.{u} D]
    [HasBinaryProducts C] [HasBinaryProducts D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ Y : D, HasSheafify (K.over Y) AddCommGrpCat.{u}]
    [∀ Y : D, (K.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (Φ : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S) {I : Type u}
    (hcol : PreservesColimitsOfShape (Discrete I) Φ) (hlim : PreservesFiniteLimits Φ)
    (η : unit S ≅ Φ.obj (unit R))
    {M : SheafOfModules.{u} R} (φ : free I ⟶ M) {N : SheafOfModules.{u} S} (α : Φ.obj M ≅ N)
    (h : ∀ ψ : (free I : SheafOfModules.{u} S) ⟶ N, (kernel ψ).IsFiniteType) :
    (Φ.obj (kernel φ)).IsFiniteType :=
  haveI := hcol
  haveI := hlim
  have := h (Stacks.AlgebraicGeometry.CoherentKernel.mapFreeHom Φ η φ α)
  Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    (Stacks.AlgebraicGeometry.CoherentKernel.kernelMapFreeIso Φ η φ α).symm

/-- The kernel condition transports along restriction by an isomorphism of schemes. -/
theorem kernelIsFiniteType_restrict_iso {Y Z : Scheme.{u}} (e : Z ≅ Y) (N : Y.Modules)
    (h : KernelIsFiniteType Y N) : KernelIsFiniteType Z ((restrictFunctor e.hom).obj N) := by
  intro I hI φ
  have := hI
  have hcol : PreservesColimitsOfShape (Discrete I) (restrictFunctor e.inv) := inferInstance
  have hlim := preservesFiniteLimits_restrictFunctor e.inv
  exact isFiniteType_of_iso (restrictIsoSelf e (kernel φ))
    (isFiniteType_restrict e.hom ((restrictFunctor e.inv).obj (kernel φ))
      (isFiniteType_obj_kernel (restrictFunctor e.inv) hcol hlim
        (restrictUnitIso e.inv).symm φ (restrictIsoSelf e.symm N) (h I hI)))

/-- The kernel condition over every open subscheme gives it over every open immersion. -/
theorem kernelIsFiniteType_restrict {Z : Scheme.{u}} (M : X.Modules)
    (h : ∀ V : X.Opens, KernelIsFiniteType V.toScheme ((restrictFunctor V.ι).obj M))
    (g : Z ⟶ X) [IsOpenImmersion g] :
    KernelIsFiniteType Z ((restrictFunctor g).obj M) := by
  refine kernelIsFiniteType_of_iso ?_
    (kernelIsFiniteType_restrict_iso g.isoOpensRange
      ((restrictFunctor g.opensRange.ι).obj M) (h g.opensRange))
  refine restrictCompIso M g.opensRange.ι g.isoOpensRange.hom g (𝟙 Z) ?_ ≪≫
    restrictFunctorId.app ((restrictFunctor g).obj M)
  rw [Scheme.Hom.isoOpensRange_hom_ι, Category.id_comp]

/-! ### Coherence on open subschemes -/

/-- **[Stacks, Tag 01BV] read on open subschemes.** A sheaf of modules on a scheme is coherent
exactly when it is of finite type and, over every open subscheme, the kernel of every morphism
into its restriction from a finite free sheaf of modules is of finite type. -/
theorem isCoherent_iff (M : X.Modules) :
    M.IsCoherent ↔ M.IsFiniteType ∧
      ∀ V : X.Opens, KernelIsFiniteType V.toScheme ((restrictFunctor V.ι).obj M) := by
  constructor
  · intro hM
    refine ⟨hM.isFiniteType, fun V I hI φ => ?_⟩
    have := hI
    have hcol : PreservesColimitsOfShape (Discrete I) (overEquiv V).inverse := inferInstance
    have hlim : PreservesFiniteLimits (overEquiv V).inverse := inferInstance
    exact isFiniteType_of_iso ((overEquiv V).counitIso.app (kernel φ))
      (isFiniteType_overEquiv_functor
        (isFiniteType_obj_kernel (overEquiv V).inverse hcol hlim
          (Stacks.AlgebraicGeometry.AffinePushforward.overInverseUnitIso V) φ
          (Stacks.AlgebraicGeometry.AffinePushforward.overInverseIso V M).symm
          (hM.kernel_isFiniteType V I hI)))
  · rintro ⟨hft, hker⟩
    refine ⟨hft, fun V I hI φ => ?_⟩
    have := hI
    have hcol : PreservesColimitsOfShape (Discrete I) (overEquiv V).functor := inferInstance
    have hlim : PreservesFiniteLimits (overEquiv V).functor := inferInstance
    exact isFiniteType_of_iso_over ((overEquiv V).unitIso.app (kernel φ)).symm
      (isFiniteType_overEquiv_inverse
        (isFiniteType_obj_kernel (overEquiv V).functor hcol hlim (Iso.refl _) φ
          ((overFunctorEquiv V).app M) (hker V I hI)))

/-- **Coherence passes to open subschemes.** -/
theorem isCoherent_restrict (M : X.Modules) [hM : M.IsCoherent] (U : X.Opens) :
    ((restrictFunctor U.ι).obj M).IsCoherent := by
  obtain ⟨hft, hker⟩ := (isCoherent_iff M).mp hM
  refine (isCoherent_iff _).mpr ⟨isFiniteType_restrict U.ι M hft, fun W => ?_⟩
  exact kernelIsFiniteType_of_iso ((restrictFunctorComp W.ι U.ι).app M)
    (kernelIsFiniteType_restrict M hker (W.ι ≫ U.ι))

/-- **Coherence is local on the base.** -/
theorem isCoherent_of_restrict (M : X.Modules) {I : Type u} (U : I → X.Opens)
    (hU : iSup U = ⊤)
    (h : ∀ i, ((restrictFunctor (U i).ι).obj M).IsCoherent) : M.IsCoherent := by
  have hd (i : I) := (isCoherent_iff ((restrictFunctor (U i).ι).obj M)).mp (h i)
  refine (isCoherent_iff M).mpr
    ⟨isFiniteType_of_restrict M U (IsOpenCover.mk hU) (fun i => (hd i).1), fun V K hK φ => ?_⟩
  have := hK
  refine isFiniteType_of_restrict (kernel φ) (fun i => V.ι ⁻¹ᵁ U i)
    (IsOpenCover.mk (V.ι.iSup_preimage_eq_top hU)) (fun i => ?_)
  have hi : KernelIsFiniteType (V.ι ⁻¹ᵁ U i).toScheme
      ((restrictFunctor (V.ι ⁻¹ᵁ U i).ι).obj ((restrictFunctor V.ι).obj M)) :=
    kernelIsFiniteType_of_iso
      (restrictCompIso M (U i).ι (resOpen V.ι (U i)) V.ι (V.ι ⁻¹ᵁ U i).ι
        (resOpen_comp_ι V.ι (U i)))
      (kernelIsFiniteType_restrict ((restrictFunctor (U i).ι).obj M) (hd i).2
        (resOpen V.ι (U i)))
  have hcol : PreservesColimitsOfShape (Discrete K) (restrictFunctor (V.ι ⁻¹ᵁ U i).ι) :=
    inferInstance
  have hlim := preservesFiniteLimits_restrictFunctor (V.ι ⁻¹ᵁ U i).ι
  exact isFiniteType_obj_kernel (restrictFunctor (V.ι ⁻¹ᵁ U i).ι) hcol hlim
    (restrictUnitIso (V.ι ⁻¹ᵁ U i).ι).symm φ (Iso.refl _) (hi K hK)

end AlgebraicGeometry.Modules

end

/-! ### Additional declarations -/

@[expose] public section
open CategoryTheory Limits SheafOfModules TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.CoherentTFAE (generatingSectionsRestrict restrictIsoSelf
  isFiniteType_of_restrict_generatingSections)
open AlgebraicGeometry.Scheme.Modules (restrictFunctor restrictFunctorComp restrictFunctorCongr
  restrictFunctorId overEquiv overFunctorEquiv restrictUnitIso)
universe u
namespace AlgebraicGeometry.Modules
variable {X : Scheme.{u}}

/-- **Restriction along an open immersion of schemes preserves colimits**: it is isomorphic to
the pullback functor, which is a left adjoint. -/
public theorem preservesColimits_restrictFunctor {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsOpenImmersion f] : PreservesColimitsOfSize.{u, u} (restrictFunctor f) :=
  preservesColimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback f).symm

/-- **Restriction along an open immersion of schemes preserves zero morphisms**, being
isomorphic to the pullback functor. -/
public theorem preservesZeroMorphisms_restrictFunctor {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsOpenImmersion f] : (restrictFunctor f).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_iso (Scheme.Modules.restrictFunctorIsoPullback f).symm

end AlgebraicGeometry.Modules
end
