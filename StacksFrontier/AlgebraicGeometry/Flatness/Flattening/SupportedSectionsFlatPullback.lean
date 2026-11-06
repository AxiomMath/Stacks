module

public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.FlatnessAtPoint
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward
public import StacksFrontier.AlgebraicGeometry.SupportedQuotient.Basic
public import StacksFrontier.Topology.Sheaves.Functors.Module.FlatPullback

/-!
# Supported sections commute with flat pullback

Let `j : Y ⟶ X` be a flat morphism of schemes, let `U ⊆ X` be an open whose inclusion is an
affine morphism, and let `F` be a quasi-coherent `𝒪_X`-module. The submodule of sections of `F`
supported in `X ∖ U` is the kernel of the unit `F ⟶ (ι_U)_* (ι_U)^* F` of the adjunction along
`ι_U`, and pullback along `j` is exact and commutes with that unit by affine base change. So the
submodule of sections of `j^* F` supported in `j⁻¹(X ∖ U)` is the pullback of the one downstairs,
and the same holds for the quotients: the strict-transform construction of
[Stacks, Tag 080D] commutes with flat pullback.

## Main definitions

* `Stacks.SupportedQuotient.submoduleIso`: an isomorphism of modules matching two submodules
  section by section is an isomorphism of those submodules.
* `Stacks.SupportedQuotient.supportedSectionsCokernelIso`: an isomorphism of modules induces one
  of their quotients by the sections supported in a fixed subset.
* `Stacks.SupportedQuotient.flatPullbackSupportedSectionsCokernelIso`: the comparison of the
  pullback of the quotient with the quotient of the pullback.

## Main results

* `Stacks.SupportedQuotient.exists_supportedSectionsPullbackKernelIso`: the sections supported in
  the complement of an open are the kernel of the unit of the pullback-pushforward adjunction
  along that open.
* `Stacks.SupportedQuotient.exists_pullbackSupportedSectionsIso_of_flat`: pullback along a flat
  morphism carries the supported-sections submodule to the supported-sections submodule,
  compatibly with the two inclusions.

## Implementation notes

The one geometric input is affine base change, [Stacks, Tag 02KG], in the form
`AlgebraicGeometry.ElementaryEtaleFlatness.affineBaseChangeIso`; it needs the inclusion of `U` to
be an affine morphism, which for the application — `U` the complement of an effective Cartier
divisor — is [Stacks, Tag 07ZT]. Exactness of the pullback functor is
`RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat`, crossed into the
scheme spelling of the functor in term position.

Everything is phrased with the complement of an *open*, which is the shape the library's
supported-quotient lemmas take; the subsets appearing in the strict transform are rewritten into
that shape by their consumers.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 084L](https://stacks.math.columbia.edu/tag/084L)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.SupportedQuotient

variable {X : Scheme.{u}}

/-! ### Transporting a submodule along an isomorphism -/

/-- A morphism of sheaves of modules carrying a submodule `N` into a submodule `P` section by
section restricts to a morphism from `N` to `P`. -/
def submoduleHom {F G : X.Modules} (f : F ⟶ G) (N : F.Submodule) (P : G.Submodule)
    (hf : ∀ (U : X.Opens) (s : Γ(F, U)),
      s ∈ N.toSubmodule.obj (op U) → f.app U s ∈ P.toSubmodule.obj (op U)) :
    N.toSheafOfModules ⟶ P.toSheafOfModules where
  val :=
    { app := fun U ↦ ModuleCat.ofHom <| LinearMap.codRestrict _
        ((f.val.app U).hom.domRestrict (N.toSubmodule.obj U)) fun s ↦ hf (unop U) s.1 s.2
      naturality := by
        intro U V i
        ext s
        refine Subtype.ext ?_
        change f.app (unop V) ((F.val.map i) s.1) = (G.val.map i) (f.app (unop U) s.1)
        exact congrArg (fun t ↦ t s.1) (f.val.naturality i) }

/-- An isomorphism `e : F ≅ G` of sheaves of modules which matches a submodule `N` of `F` with a
submodule `P` of `G` section by section induces an isomorphism of `N` and `P` as sheaves of
modules. -/
def submoduleIso {F G : X.Modules} (e : F ≅ G) (N : F.Submodule) (P : G.Submodule)
    (h : ∀ (U : X.Opens) (s : Γ(F, U)),
      s ∈ N.toSubmodule.obj (op U) ↔ e.hom.app U s ∈ P.toSubmodule.obj (op U)) :
    N.toSheafOfModules ≅ P.toSheafOfModules := by
  refine ⟨submoduleHom e.hom N P fun U s ↦ (h U s).mp, submoduleHom e.inv P N fun U s hs ↦ by
    have heq : e.hom.app U (e.inv.app U s) = s := congrArg (fun k : G ⟶ G ↦ k.app U s) e.inv_hom_id
    exact (h U _).mpr (by rwa [heq]), ?_, ?_⟩
  · refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
    ext s
    refine Subtype.ext ?_
    change e.inv.app U (e.hom.app U s.1) = s.1
    exact congrArg (fun k : F ⟶ F ↦ k.app U s.1) e.hom_inv_id
  · refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
    ext s
    refine Subtype.ext ?_
    change e.hom.app U (e.inv.app U s.1) = s.1
    exact congrArg (fun k : G ⟶ G ↦ k.app U s.1) e.inv_hom_id

/-- An isomorphism of sheaves of modules identifies their submodules of sections supported in a
fixed subset. -/
def supportedSectionsIso (Z : Set X) {F G : X.Modules} (e : F ≅ G) :
    supportedSectionsObj Z F ≅ supportedSectionsObj Z G := by
  refine submoduleIso e _ _ fun U s ↦ ⟨map_mem_supportedSectionsSubmodule Z e.hom U s, fun hs ↦ ?_⟩
  have hcancel : e.inv.app U (e.hom.app U s) = s :=
    congrArg (fun k : F ⟶ F ↦ k.app U s) e.hom_inv_id
  simpa only [hcancel] using map_mem_supportedSectionsSubmodule Z e.inv U (e.hom.app U s) hs

/-- An isomorphism of sheaves of modules identifies their quotients by the sections supported in
a fixed subset. -/
def supportedSectionsCokernelIso (Z : Set X) {F G : X.Modules} (e : F ≅ G) :
    cokernel (supportedSectionsι Z F) ≅ cokernel (supportedSectionsι Z G) :=
  cokernel.mapIso _ _ (supportedSectionsIso Z e) e
    (Scheme.Modules.hom_ext _ _ fun _ ↦ rfl)

/-! ### Two generalities -/

/-- Two morphisms out of a common source with the same vanishing criterion have isomorphic
kernels, compatibly with the two inclusions. -/
lemma exists_kernelIso_of_comp_eq_zero_iff {C : Type*} [Category* C] [HasZeroMorphisms C]
    [HasKernels C] {A B D : C} (f : A ⟶ B) (g : A ⟶ D)
    (h : ∀ (W : C) (k : W ⟶ A), k ≫ f = 0 ↔ k ≫ g = 0) :
    ∃ e : kernel f ≅ kernel g, e.hom ≫ kernel.ι g = kernel.ι f := by
  let a := kernel.lift g (kernel.ι f) ((h _ _).mp (kernel.condition f))
  let b := kernel.lift f (kernel.ι g) ((h _ _).mpr (kernel.condition g))
  refine ⟨⟨a, b, ?_, ?_⟩, ?_⟩
  · exact (cancel_mono (kernel.ι f)).mp (by simp [a, b])
  · exact (cancel_mono (kernel.ι g)).mp (by simp [a, b])
  · simp [a]

/-- For an adjunction `L ⊣ R` whose left part is a monomorphism on `f` and whose unit is a
monomorphism on the target of `f`, a morphism dies against `f` exactly when it dies against the
unit. -/
lemma comp_eq_zero_iff_comp_unit_eq_zero {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.PreservesZeroMorphisms] [R.PreservesZeroMorphisms] {A B : C} (f : A ⟶ B)
    [Mono (L.map f)] [Mono (adj.unit.app B)] (W : C) (k : W ⟶ A) :
    k ≫ f = 0 ↔ k ≫ adj.unit.app A = 0 := by
  refine ⟨fun hzero ↦ ?_, fun hzero ↦ ?_⟩
  · have hmap : L.map k = 0 := by
      refine (cancel_mono (L.map f)).mp ?_
      rw [← L.map_comp, hzero, Functor.map_zero, zero_comp]
    simpa only [Functor.id_map, Functor.comp_map, hmap, Functor.map_zero, comp_zero] using
      adj.unit.naturality k
  · have hnat : f ≫ adj.unit.app B = adj.unit.app A ≫ R.map (L.map f) := adj.unit.naturality f
    refine (cancel_mono (adj.unit.app B)).mp ?_
    rw [Category.assoc, hnat, ← Category.assoc, hzero, zero_comp, zero_comp]

/-- Invertibility of the image of a morphism transfers along an isomorphism of functors. -/
lemma isIso_map_of_natIso {C D : Type*} [Category* C] [Category* D] {L R : C ⥤ D} (e : L ≅ R)
    {A B : C} (f : A ⟶ B) [IsIso (L.map f)] : IsIso (R.map f) := by
  rw [show R.map f = (e.app A).inv ≫ L.map f ≫ (e.app B).hom by simp]
  infer_instance

/-! ### Supported sections as a kernel -/

/-- The sections of `F` supported in the complement of an open `U` are the kernel of the unit of
the pullback-pushforward adjunction along `U`, compatibly with the two inclusions. -/
lemma exists_supportedSectionsPullbackKernelIso (U : X.Opens) (F : X.Modules) :
    ∃ e : supportedSectionsObj (U : Set X)ᶜ F ≅
        kernel ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F),
      e.hom ≫ kernel.ι ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F) =
        supportedSectionsι (U : Set X)ᶜ F := by
  let η := (Scheme.Modules.restrictAdjunction U.ι).unit.app F
  let θ := (Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F
  let e₀ : supportedSectionsObj (U : Set X)ᶜ F ≅ kernel η :=
    (isLimit_kernelFork_supportedSectionsι_compl U F).conePointUniqueUpToIso (limit.isLimit _)
  have he₀ : e₀.hom ≫ kernel.ι η = supportedSectionsι (U : Set X)ᶜ F :=
    limit.conePointUniqueUpToIso_hom_comp _ WalkingParallelPair.zero
  let e := (Scheme.Modules.pushforward U.ι).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F)
  have h : η ≫ e.hom = θ := Adjunction.unit_leftAdjointUniq_hom_app _ _ F
  let ek := kernel.mapIso η θ (Iso.refl _) e (by simpa using h)
  refine ⟨e₀ ≪≫ ek, ?_⟩
  change e₀.hom ≫ ek.hom ≫ kernel.ι θ = _
  simpa only [ek, kernel.mapIso_hom, kernel.lift_ι, Iso.refl_hom, Category.comp_id] using he₀

/-! ### Flat pullback -/

/-- **Supported sections commute with flat pullback.** For `j : Y ⟶ X` flat, `U ⊆ X` an open
with affine inclusion and `F` quasi-coherent, the pullback along `j` of the submodule of sections
of `F` supported in `X ∖ U` is the submodule of sections of `j^* F` supported in `j⁻¹(X ∖ U)`,
compatibly with the two inclusions. -/
lemma exists_pullbackSupportedSectionsIso_of_flat {Y : Scheme.{u}} (j : Y ⟶ X) [Flat j]
    (U : X.Opens) [IsAffineHom U.ι] (F : X.Modules) [F.IsQuasicoherent] :
    ∃ e : (Scheme.Modules.pullback j).obj (supportedSectionsObj (U : Set X)ᶜ F) ≅
        supportedSectionsObj (j.base ⁻¹' (U : Set X)ᶜ) ((Scheme.Modules.pullback j).obj F),
      e.hom ≫ supportedSectionsι (j.base ⁻¹' (U : Set X)ᶜ)
          ((Scheme.Modules.pullback j).obj F) =
        (Scheme.Modules.pullback j).map (supportedSectionsι (U : Set X)ᶜ F) := by
  let P := Scheme.Modules.pullback j
  let V := j ⁻¹ᵁ U
  let L := Scheme.Modules.pullback V.ι
  let adj := Scheme.Modules.pullbackPushforwardAdjunction V.ι
  let η := (Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F
  let α := P.map η
  have : ((Scheme.Modules.pullback U.ι).obj F).IsQuasicoherent :=
    @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      U.ι.toLRSHom.toShHom F ‹F.IsQuasicoherent›
  let eBC := AlgebraicGeometry.ElementaryEtaleFlatness.affineBaseChangeIso
    (isPullback_morphismRestrict j U) ((Scheme.Modules.pullback U.ι).obj F)
  have : IsIso (adj.unit.app (P.obj ((Scheme.Modules.pullback U.ι ⋙
      Scheme.Modules.pushforward U.ι).obj F))) := adj.isIso_unit_app_of_iso eBC
  let ecomp : Scheme.Modules.pullback U.ι ⋙ Scheme.Modules.pullback (j ∣_ U) ≅ P ⋙ L :=
    Scheme.Modules.pullbackComp (j ∣_ U) U.ι ≪≫
      Scheme.Modules.pullbackCongr (morphismRestrict_ι j U) ≪≫
      (Scheme.Modules.pullbackComp V.ι j).symm
  have : IsIso ((Scheme.Modules.pullback U.ι).map η) := inferInstance
  have : IsIso ((Scheme.Modules.pullback U.ι ⋙ Scheme.Modules.pullback (j ∣_ U)).map η) := by
    change IsIso ((Scheme.Modules.pullback (j ∣_ U)).map ((Scheme.Modules.pullback U.ι).map η))
    infer_instance
  have : IsIso (L.map α) := isIso_map_of_natIso ecomp η
  have : PreservesFiniteLimits P :=
    AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat j
  obtain ⟨e₀, h₀⟩ := exists_supportedSectionsPullbackKernelIso U F
  have : L.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have : (Scheme.Modules.pushforward V.ι).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isRightAdjoint _
  have : Mono (L.map α) := IsIso.mono_of_iso _
  have : Mono (adj.unit.app (P.obj ((Scheme.Modules.pullback U.ι ⋙
      Scheme.Modules.pushforward U.ι).obj F))) := IsIso.mono_of_iso _
  obtain ⟨e₁, h₁⟩ := exists_kernelIso_of_comp_eq_zero_iff α (adj.unit.app (P.obj F))
    (comp_eq_zero_iff_comp_unit_eq_zero adj α)
  obtain ⟨e₂, h₂⟩ := exists_supportedSectionsPullbackKernelIso V (P.obj F)
  refine ⟨P.mapIso e₀ ≪≫ PreservesKernel.iso P η ≪≫ e₁ ≪≫ e₂.symm, ?_⟩
  change (P.mapIso e₀ ≪≫ PreservesKernel.iso P η ≪≫ e₁ ≪≫ e₂.symm).hom ≫
    supportedSectionsι (V : Set Y)ᶜ (P.obj F) = _
  rw [← h₂]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [h₁, PreservesKernel.iso_hom]
  change P.map e₀.hom ≫ kernelComparison η P ≫ kernel.ι (P.map η) = _
  rw [kernelComparison_comp_ι, ← P.map_comp, h₀]

/-- **The quotient by supported sections commutes with flat pullback.** For `j : Y ⟶ X` flat,
`U ⊆ X` an open with affine inclusion and `F` quasi-coherent, the pullback along `j` of the
quotient of `F` by the sections supported in `X ∖ U` is the quotient of `j^* F` by the sections
supported in `j⁻¹(X ∖ U)`. -/
def flatPullbackSupportedSectionsCokernelIso {Y : Scheme.{u}} (j : Y ⟶ X) [Flat j] (U : X.Opens)
    [IsAffineHom U.ι] (F : X.Modules) [F.IsQuasicoherent] :
    (Scheme.Modules.pullback j).obj (cokernel (supportedSectionsι (U : Set X)ᶜ F)) ≅
      cokernel (supportedSectionsι (j.base ⁻¹' (U : Set X)ᶜ)
        ((Scheme.Modules.pullback j).obj F)) :=
  PreservesCokernel.iso (Scheme.Modules.pullback j) _ ≪≫
    cokernel.mapIso _ _ (exists_pullbackSupportedSectionsIso_of_flat j U F).choose (Iso.refl _)
      (by simpa using (exists_pullbackSupportedSectionsIso_of_flat j U F).choose_spec.symm)

end Stacks.SupportedQuotient

end
