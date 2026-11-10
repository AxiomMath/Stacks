module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Sections
public import StacksFrontier.CategoryTheory.NatIsoOfEpiCone
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# Affine sections of the completion of a coherent module

Let `X` be a locally Noetherian scheme, `I` a quasi-coherent ideal sheaf and `F` a coherent
`𝒪_X`-module. The completion functor of Stacks 0880 sends `F` to the inverse system
`n ↦ F / I ^ (n+1) F`, and `Stacks.Algebraization.completionProjection` is the canonical map from
`F` onto its `n`-th term. This file computes that map on the sections over an affine open: it is
surjective with kernel `I(U) ^ (n+1) • F(U)`, so the sections of the `n`-th term of the completion
are the honest module quotient `F(U) / I(U) ^ (n+1) F(U)`, compatibly with the transition maps.
Assembling the projections into a cone exhibits the canonical map from `F` to the limit of its
completion.

## Main definitions

* `Stacks.Algebraization.completionCone` — the projections of `F` onto the terms of its completion,
  as a cone over the inverse system.
* `Stacks.Algebraization.completionToLimit` — the induced map from `F` to the limit of its
  completion.
* `Stacks.Algebraization.completionQuotientSectionsEquiv` — the sections of the `n`-th term of the
  completion over an affine open `U`, identified with `F(U) / I(U) ^ (n+1) F(U)`.
* `Stacks.Algebraization.completionIsoOfProjections` — a family of isomorphisms of the terms of a
  completion with the terms of an inverse system, carrying the projections of the completion to a
  compatible family of maps, is an isomorphism of inverse systems.

## Main results

* `Stacks.Algebraization.cokernel_π_app_eq_zero_iff` — a section of a sheaf of modules dies in the
  quotient by a subsheaf exactly when it is a section of that subsheaf.
* `Stacks.Algebraization.epi_completionProjection` — the projections are epimorphisms.
* `Stacks.Algebraization.completionProjection_naturality_le` and `completionProjection_map` — the
  projections are compatible with every transition map of the inverse system, in the form
  indexed by `m ≤ n` and in the form indexed by the arrows of `ℕᵒᵖ`.
* `Stacks.Algebraization.completionProjection_app_ker` and
  `completionProjection_app_surjective` — over an affine open the projection is surjective with
  kernel `I(U) ^ (n+1) • F(U)`.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`, and the two
presentations carry separately declared instances, so an instance found for one is not found for
the other. The devices of `Stacks.Algebraization.CompletionFunctor.Basic` are used again here:
every categorical construction is given its category explicitly as `(C := X.Modules)`, the
instances for the scalar action on sections are the `local instance`s of
`Completion.IdealPowerQuasicoherent` and `Completion.Quasicoherent.IdealPowerMultiple`
reactivated rather than restated, and `congrArg` against a stated equality of morphisms replaces
a `rw` whose motive would mix the two presentations.

`completionProjection` is by construction a quotient projection followed by an `eqToHom`, and
`Epi` of that composite is not found by instance search for the same reason: the quotient
projection is typed at `SheafOfModules X.ringCatSheaf` and the `eqToHom` at `X.Modules`. Both
factors are therefore produced separately and `epi_comp` applied by hand.

The kernel computation runs through `cokernel_π_app_eq_zero_iff`, which is proved by evaluating
the cokernel short complex at `U`: evaluation at an open preserves finite limits and zero
morphisms, so the exact sequence `P → F → F / P` stays exact in modules, where exactness is a
statement about elements. The `eqToHom` factor of the projection is substituted away, which turns
it into an identity and so makes it visibly injective on sections. The sections of `I ^ (n+1) F`
over an affine open are `Stacks.Algebraization.idealPowerMultiple_toSubmodule_obj_affine`, and
surjectivity is `Stacks.Algebraization.surjective_app_of_epi_of_isAffineOpen` applied to the
epimorphism.

The module structure on sections comes in several spellings: over `X.ringCatSheaf.obj.obj U` or
over `Γ(X, U)`, and on `M.val.obj U` or on `Γ(M, U)`, with `M` presented either as an
`𝒪_X`-module or as a sheaf of modules. Mathlib declares the instance for one combination, and
instance search does not cross the definitions relating them; the two `local instance`s below
supply the two further combinations this file meets, each with Mathlib's own body, so nothing new
is assumed. `completionQuotientSectionsEquiv` additionally names its linear map at the `Γ(X, U)`
spelling before composing the two isomorphisms, since `LinearEquiv.trans` across two spellings of
one ring asks for a `RingHomCompTriple` that does not exist.

## References

* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0EI8](https://stacks.math.columbia.edu/tag/0EI8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

/-! ### Bridging instances across the two presentations of the category of modules

The scalar action on sections is bridged by the `local instance`s of
`Completion.IdealPowerQuasicoherent` and `Completion.Quasicoherent.IdealPowerMultiple`,
reactivated rather than restated. -/

attribute [local instance] sectionsModuleΓ sectionsModuleΓSheaf sectionsSMulCommClassΓ
  monoSubmoduleι sectionsModuleΓPresheaf

/-- The module structure on `Γ(M, U)` for `M` presented as a sheaf of modules over
`X.ringCatSheaf` rather than as an `𝒪_X`-module.

Mathlib declares it with the `X.Modules` presentation as the binder, and instance search does not
cross the `AlgebraicGeometry.Scheme.Modules` definition; the body is the one Mathlib uses. -/
local instance sectionsModuleΓSheafPresheaf {X : Scheme.{u}}
    (M : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens) :
    Module Γ(X, U) Γ(M, U) :=
  (M.val.obj (op U)).isModule

/-- The module structure on `M.val.obj (op U)` over `Γ(X, U)`, for `M` presented as a sheaf of
modules over `X.ringCatSheaf`. The companion of the previous instance at the spelling of the
sections which a morphism of sheaves of modules produces. -/
local instance sectionsModuleΓSheafVal {X : Scheme.{u}}
    (M : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens) :
    Module Γ(X, U) (M.val.obj (op U)) :=
  (M.val.obj (op U)).isModule

/-! ### Sections of a sheaf quotient -/

/-- An `eqToHom` of `𝒪_X`-modules annihilates a section only if that section is zero. -/
private lemma eqToHom_val_app_eq_zero_iff {X : Scheme.{u}} {M N : X.Modules} (h : M = N)
    (U : X.Opens) (x : Γ(M, U)) :
    (eqToHom h).val.app (op U) x = 0 ↔ x = 0 := by
  subst h
  rw [eqToHom_refl]
  exact Iff.rfl

/-- A section of `F` over an open `U` dies in the quotient `F / P` exactly when it is a section of
the subsheaf `P` over `U`.

Evaluation at `U` preserves zero morphisms and finite limits, so it carries the exact sequence
`P → F → F / P` to an exact sequence of modules, where exactness is the statement that the kernel
of the second map is the image of the first. -/
public theorem cokernel_π_app_eq_zero_iff {X : Scheme.{u}} (F : X.Modules) (P : F.Submodule)
    (U : X.Opens) (s : Γ(F, U)) :
    (cokernel.π (C := X.Modules) P.ι).val.app (op U) s = 0 ↔ s ∈ P.toSubmodule.obj (op U) := by
  let T : X.Modules ⥤ ModuleCat Γ(X, U) :=
    SheafOfModules.evaluation X.ringCatSheaf (op U)
  let _ : T.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let _ : PreservesFiniteLimits T :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf (op U)
  have hex := (ShortComplex.exact_cokernel (C := X.Modules) P.ι).map_of_mono_of_preservesKernel T
    inferInstance inferInstance
  have hh := (ShortComplex.moduleCat_exact_iff _).mp hex
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · obtain ⟨t, ht⟩ := hh s hs
    exact ht ▸ t.property
  · exact congrArg (fun f : P.toSheafOfModules ⟶ cokernel (C := X.Modules) P.ι =>
      f.val.app (op U) ⟨s, hs⟩) (cokernel.condition (C := X.Modules) P.ι)

/-! ### The projections onto the terms of the completion -/

/-- **Stacks 0880.** The projection of a coherent module onto the `n`-th term of its completion is
an epimorphism.

Instance search does not see this through the composite defining the projection: the quotient
projection is typed at `SheafOfModules X.ringCatSheaf` and the `eqToHom` at `X.Modules`, so the
two factors are produced separately. -/
public theorem epi_completionProjection (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    Epi (C := X.Modules) (completionProjection X I F n) := by
  have h1 : Epi (cokernel.π (idealPowerMultiple I (n + 1) F.obj).ι) := coequalizer.π_epi
  have h2 : Epi (eqToHom (completionFunctor_obj X I F n).symm) := inferInstance
  exact @epi_comp _ _ _ _ _ _ h1 _ h2

/-- **Stacks 0880.** The projections of a coherent module onto the terms of its completion are
compatible with every transition map of the inverse system, indexed by `m ≤ n`.  The form
indexed by the arrows of `ℕᵒᵖ` is `Stacks.Algebraization.completionProjection_map`. -/
public theorem completionProjection_naturality_le (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) {m n : ℕ}
    (h : m ≤ n) :
    completionProjection X I F n ≫ ((completionFunctor X I).obj F).obj.map (homOfLE h).op =
      completionProjection X I F m := by
  induction n, h using Nat.le_induction with
  | base =>
    have h0 : ((completionFunctor X I).obj F).obj.map (homOfLE (le_refl m)).op = 𝟙 _ :=
      (congrArg ((completionFunctor X I).obj F).obj.map
        (Subsingleton.elim (homOfLE (le_refl m)).op (𝟙 (op m)))).trans
        (((completionFunctor X I).obj F).obj.map_id (op m))
    rw [h0]
    exact Category.comp_id _
  | succ n hn ih =>
    have heq : (homOfLE (Nat.le_succ_of_le hn)).op =
        (homOfLE (Nat.le_succ n)).op ≫ (homOfLE hn).op := Subsingleton.elim _ _
    rw [heq, Functor.map_comp]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ ((completionFunctor X I).obj F).obj.map (homOfLE hn).op)
          (completionProjection_transition X I F n)).trans ih)

/-- **Stacks 0880.** The projections are compatible with the transition maps, in the form indexed
by the arrows of `ℕᵒᵖ`. -/
public theorem completionProjection_map (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) {m n : ℕᵒᵖ}
    (f : m ⟶ n) :
    completionProjection X I F m.unop ≫ ((completionFunctor X I).obj F).obj.map f =
      completionProjection X I F n.unop := by
  simpa only [show (homOfLE (leOfHom f.unop)).op = f from Subsingleton.elim _ _] using
    completionProjection_naturality_le X I F (leOfHom f.unop)

/-- **A levelwise comparison compatible with the projections is an isomorphism of systems.**
Given maps `Φ n : F ⟶ D_n` into an inverse system which are compatible with its transition maps,
and isomorphisms of the terms of the completion of `F` with the terms of `D` carrying the
projections of the completion to the `Φ n`, the two inverse systems are isomorphic.

The projections out of a completion are epimorphisms and are compatible with every transition map,
which is what makes the levelwise isomorphisms natural. -/
public noncomputable def completionIsoOfProjections (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (D : ℕᵒᵖ ⥤ X.Modules) (Φ : ∀ n : ℕ, F.obj ⟶ D.obj (op n))
    (hΦ : ∀ {m n : ℕᵒᵖ} (f : m ⟶ n), Φ m.unop ≫ D.map f = Φ n.unop)
    (c : ∀ n : ℕ, ((completionFunctor X I).obj F).obj.obj (op n) ≅ D.obj (op n))
    (hc : ∀ n : ℕ, completionProjection X I F n ≫ (c n).hom = Φ n) :
    ((completionFunctor X I).obj F).obj ≅ D :=
  CategoryTheory.natIsoOfEpiNormalizedCone F.obj
    (fun n => completionProjection X I F n.unop) (fun n => Φ n.unop)
    (fun f => completionProjection_map X I F f) (fun f => hΦ f)
    (fun n => epi_completionProjection X I F n.unop) (fun n => c n.unop)
    (fun n => hc n.unop)

/-! ### Affine sections of the projections -/

/-- A coherent module is quasi-coherent. -/
private lemma isQuasicoherent_of_isCoherent {X : Scheme.{u}} (M : X.Modules) [M.IsCoherent] :
    M.IsQuasicoherent :=
  (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent M).1

/-- **Stacks 0880.** Over an affine open `U`, the kernel of the projection onto the `n`-th term of
the completion is `I(U) ^ (n+1) • F(U)`.

The `eqToHom` factor of the projection is injective on sections, so a section dies in the `n`-th
term exactly when it dies in the sheaf quotient by `I ^ (n+1) F`, which by
`cokernel_π_app_eq_zero_iff` means that it is a section of `I ^ (n+1) F`. -/
public theorem completionProjection_app_ker (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ)
    (U : X.affineOpens) :
    LinearMap.ker ((completionProjection X I F n).val.app (op U.1)).hom =
      I.ideal U ^ (n + 1) • (⊤ : Submodule Γ(X, U) Γ(F.obj, U)) := by
  have : F.obj.IsCoherent := F.property
  have := isQuasicoherent_of_isCoherent F.obj
  ext s
  change (completionProjection X I F n).val.app (op U.1) s = 0 ↔ _
  rw [completionProjection]
  change (eqToHom (completionFunctor_obj X I F n).symm).val.app (op U.1)
    ((cokernel.π (idealPowerMultiple I (n + 1) F.obj).ι).val.app (op U.1) s) = 0 ↔ _
  refine Iff.trans (eqToHom_val_app_eq_zero_iff (completionFunctor_obj X I F n).symm U.1 _) ?_
  refine Iff.trans (cokernel_π_app_eq_zero_iff F.obj (idealPowerMultiple I (n + 1) F.obj) U.1 s) ?_
  exact Iff.of_eq (congrArg (fun S => s ∈ S)
    (idealPowerMultiple_toSubmodule_obj_affine I (n + 1) F.obj U))

/-- **Stacks 0880.** Over an affine open the projection onto the `n`-th term of the completion is
surjective: it is an epimorphism of quasi-coherent modules. -/
public theorem completionProjection_app_surjective (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ)
    (U : X.affineOpens) :
    Function.Surjective ((completionProjection X I F n).val.app (op U.1)) := by
  have : F.obj.IsCoherent := F.property
  have := isQuasicoherent_of_isCoherent F.obj
  have : (((completionFunctor X I).obj F).obj.obj (op n)).IsCoherent :=
    ((completionFunctor X I).obj F).property.1 n
  have := isQuasicoherent_of_isCoherent (((completionFunctor X I).obj F).obj.obj (op n))
  have := epi_completionProjection X I F n
  exact surjective_app_of_epi_of_isAffineOpen (completionProjection X I F n) U

/-- **Stacks 0880.** The sections over an affine open `U` of the `n`-th term of the completion of
`F`, identified with the module quotient `F(U) / I(U) ^ (n+1) F(U)`. -/
public noncomputable def completionQuotientSectionsEquiv (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ)
    (U : X.affineOpens) :
    (Γ(F.obj, U) ⧸ I.ideal U ^ (n + 1) • (⊤ : Submodule Γ(X, U) Γ(F.obj, U))) ≃ₗ[Γ(X, U)]
      (((completionFunctor X I).obj F).obj.obj (op n)).val.obj (op U.1) :=
  let p : Γ(F.obj, U) →ₗ[Γ(X, U)] Γ(((completionFunctor X I).obj F).obj.obj (op n), U) :=
    ((completionProjection X I F n).val.app (op U.1)).hom
  have hker : I.ideal U ^ (n + 1) • (⊤ : Submodule Γ(X, U) Γ(F.obj, U)) = LinearMap.ker p :=
    (completionProjection_app_ker X I F n U).symm
  (Submodule.quotEquivOfEq _ _ hker).trans
    (p.quotKerEquivOfSurjective (completionProjection_app_surjective X I F n U))

/-- The identification of affine sections sends the class of a section to its image under the
projection. -/
public theorem completionQuotientSectionsEquiv_mk (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ)
    (U : X.affineOpens) (x : Γ(F.obj, U)) :
    completionQuotientSectionsEquiv X I F n U (Submodule.Quotient.mk x) =
      (completionProjection X I F n).val.app (op U.1) x := by
  simp only [completionQuotientSectionsEquiv]
  rfl

/-- The identification of affine sections carries the transition maps of the completion to the
canonical maps between the successive module quotients. -/
public theorem completionQuotientSectionsEquiv_naturality (X : Scheme.{u})
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (U : X.affineOpens)
    {m n : ℕ} (h : m ≤ n)
    (x : Γ(F.obj, U) ⧸ I.ideal U ^ (n + 1) • (⊤ : Submodule Γ(X, U) Γ(F.obj, U))) :
    (((completionFunctor X I).obj F).obj.map (homOfLE h).op).val.app (op U.1)
        (completionQuotientSectionsEquiv X I F n U x) =
      completionQuotientSectionsEquiv X I F m U
        (Submodule.factorPow (I.ideal U) Γ(F.obj, U) (Nat.add_le_add_right h 1) x) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change _ = completionQuotientSectionsEquiv X I F m U (Submodule.Quotient.mk x)
    rw [completionQuotientSectionsEquiv_mk, completionQuotientSectionsEquiv_mk]
    exact congrArg (fun f : F.obj ⟶ ((completionFunctor X I).obj F).obj.obj (op m) =>
      f.val.app (op U.1) x) (completionProjection_naturality_le X I F h)

/-! ### The map to the limit of the completion -/

/-- **Stacks 0880.** The projections of a coherent module onto the terms of its completion, as a
cone over the inverse system. -/
public noncomputable def completionCone (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    Cone ((completionFunctor X I).obj F).obj where
  pt := F.obj
  π :=
    { app := fun n => completionProjection X I F n.unop
      naturality := fun _ _ f => (Category.id_comp _).trans
        (completionProjection_map X I F f).symm }

/-- **Stacks 0880.** The canonical map from a coherent module to the limit of its completion. -/
public noncomputable def completionToLimit (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    F.obj ⟶ limit (C := X.Modules) ((completionFunctor X I).obj F).obj :=
  limit.lift _ (completionCone X I F)

/-- **Stacks 0880.** The map to the limit of the completion is compatible with the projections. -/
public theorem completionToLimit_projection (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕᵒᵖ) :
    completionToLimit X I F ≫ limit.π ((completionFunctor X I).obj F).obj n =
      completionProjection X I F n.unop :=
  limit.lift_π (completionCone X I F) n

end Stacks.Algebraization

end
