module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeAffineDual
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Algebraize

/-!
# Algebraizing a map out of a completion, locally on a scheme

Let `X` be a locally Noetherian scheme, `ℐ` a quasi-coherent sheaf of ideals on `X`, `G` a
coherent `𝒪_X`-module and `(F_n)` a coherent `ℐ`-adic system. This file carries the affine case of
Stacks 0889 part (2) — the statement with both arrows reversed — over to an arbitrary
quasi-coherent ideal sheaf on an affine scheme, and then to the restriction of the datum to an
affine open of an arbitrary locally Noetherian scheme.

The datum of part (2) is a morphism `α : G^∧ ⟶ (F_n)` out of the completion of `G`, and it
restricts to an open subscheme: restriction along an open immersion is exact, so it carries the
levelwise kernels and cokernels of `α` to those of the restricted morphism, and it preserves
annihilation by a power of the ideal sheaf. Over an affine open the restricted ideal sheaf is the
one attached to an ideal of the global sections, which is the form the affine theorem is stated
in.

## Main definitions

* `Stacks.Algebraization.restrictedSystemMapDual` — the datum of part (2) transported to an open
  subscheme.
* `Stacks.Algebraization.restrictedCompletionCompIso` and
  `Stacks.Algebraization.restrictedSystemCompIso` — the comparisons of the source and of the
  target of the datum restricted along a composite of two open immersions with those of the datum
  restricted in two steps.
* `Stacks.Algebraization.restrictCoherentModulesMap` — the restriction of a morphism of coherent
  modules along an open immersion.
* `Stacks.Algebraization.restrictedAlgebraizationIsoDual` — the isomorphism of an algebraization
  transported to an open subscheme.

## Main results

* `Stacks.Algebraization.affine_exists_algebraization_dual_of_idealSheafData` and
  `Stacks.Algebraization.affine_unique_algebraization_dual_of_idealSheafData` — the affine case of
  Stacks 0889 (2), existence and uniqueness, for an arbitrary quasi-coherent ideal sheaf on an
  affine scheme.
* `Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_restrictedSystemMapDual` — the
  hypothesis of Stacks 0888 (1) restricts along an open immersion in this direction too.
* `Stacks.Algebraization.exists_local_algebraization_dual` — over each affine open the restricted
  datum admits an algebraization out of `G|_U`, whose kernel and cokernel are annihilated by a
  power of `ℐ|_U`.
* `Stacks.Algebraization.unique_local_algebraization_dual` — that local algebraization is unique
  up to a unique isomorphism.
* `Stacks.Algebraization.completionSystemHom_ext` — a morphism of inverse systems out of a
  completion is determined by its composites with the canonical projections.
* `Stacks.Algebraization.completionProjection_comp_restrictedSystemMapDual` — the restricted datum
  read through those projections.
* `Stacks.Algebraization.restrictedSystemMapDual_comp` — **restriction-transitivity of the
  datum**: restricting along `f` and then along `g` agrees with restricting along `g ≫ f`, through
  the two comparison isomorphisms above.
* `Stacks.Algebraization.completionRestrictOpenIso_inv_naturality` — the comparison isomorphism of
  Stacks 0880 is natural in the module, so completing a morphism and restricting it agrees with
  restricting it and completing it.
* `Stacks.Algebraization.restrictedSystemMapDual_eq_of_algebraization`,
  `Stacks.Algebraization.isPowerAnnihilated_kernel_restrictCoherentModulesMap` and
  `Stacks.Algebraization.isPowerAnnihilated_cokernel_restrictCoherentModulesMap` — **a local
  algebraization restricts to a local algebraization**: the factorization of the datum and the
  annihilation of the kernel and the cokernel of `b` both survive restriction to an open
  subscheme.

## Implementation notes

The comparison isomorphism of Stacks 0880 between the restricted completion of `G` and the
completion of `G|_U` enters on the other side here than it does in part (1): the restricted datum
is the restriction of `α` *precomposed* with the inverse of that isomorphism. The levelwise kernel
is therefore unchanged because an isomorphism precomposed with a map does not change its kernel,
and the levelwise cokernel because an epimorphism precomposed with a map does not change its
cokernel; in part (1) the roles of these two facts are played by the corresponding statements for
postcomposition with a monomorphism and with an isomorphism.

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`, so every limit
and colimit below names its category explicitly as `(C := X.Modules)` or `(C := Y.Modules)`.

The two presentations are also why the transitivity proofs are term-mode. A projection onto a
term of a completion is typed at `SheafOfModules Y.ringCatSheaf` while the components of the
comparison isomorphism are typed at `Y.Modules`, so a composite of the two carries two defeq but
not syntactically equal category instances; neither `rw` nor `simp` can then match an
associativity or a hypothesis against it. The reassociations are therefore done by the three
private lemmas `comp_assoc_eq_of_eq₂`, `comp_assoc_eq_comp_of_eq₂` and `comp_assoc_eq_comp_of_eq₃`,
stated in an abstract category where no such mismatch arises and applied by `exact`, which checks
up to definitional equality. For the same reason the two goals that need the defining composite of
`Stacks.Algebraization.restrictedSystemMapDual` are put in that shape by `change` rather than by
unfolding.

## References

* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

/-! ### The affine case for an arbitrary ideal sheaf -/

/-- On an affine scheme every ideal sheaf is the one attached to an ideal of the global sections. -/
private theorem exists_eq_ofIdealTop {Y : Scheme.{u}} [IsAffine Y] (K : Y.IdealSheafData) :
    ∃ J : Ideal Γ(Y, ⊤), K = Scheme.IdealSheafData.ofIdealTop J :=
  ⟨_, (Scheme.IdealSheafData.equivOfIsAffine.symm_apply_apply K).symm⟩

/-- **The affine case of Stacks 0889 (2).** On an affine Noetherian scheme every quasi-coherent
ideal sheaf is the one attached to an ideal of the global sections, by
`AlgebraicGeometry.Scheme.IdealSheafData.equivOfIsAffine`, so the affine algebraization theorem in
the direction out of the completion holds for an arbitrary quasi-coherent ideal sheaf. -/
public theorem affine_exists_algebraization_dual_of_idealSheafData (Y : Scheme.{u}) [IsAffine Y]
    [IsLocallyNoetherian Y] [IsNoetherianRing Γ(Y, ⊤)] (K : Y.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems K)
    (α : ((completionFunctor Y K).obj G).obj ⟶ Fsys.obj)
    (hα : IsKernelCokernelAnnihilatedByPower K α) :
    ∃ (F : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf) (a : G ⟶ F)
      (β : ((completionFunctor Y K).obj F).obj ≅ Fsys.obj),
      α = ((completionFunctor Y K).map a).hom ≫ β.hom ∧
        IsPowerAnnihilated K (kernel (C := Y.Modules) a.hom) ∧
          IsPowerAnnihilated K (cokernel (C := Y.Modules) a.hom) := by
  obtain ⟨J, hJ⟩ := exists_eq_ofIdealTop K
  subst hJ
  exact affine_exists_algebraization_dual Y J G Fsys α hα

/-- **The uniqueness clause of the affine case of Stacks 0889 (2)** for an arbitrary
quasi-coherent ideal sheaf on an affine Noetherian scheme. -/
public theorem affine_unique_algebraization_dual_of_idealSheafData (Y : Scheme.{u}) [IsAffine Y]
    [IsLocallyNoetherian Y] [IsNoetherianRing Γ(Y, ⊤)] (K : Y.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems K)
    (α : ((completionFunctor Y K).obj G).obj ⟶ Fsys.obj)
    (F F' : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (a : G ⟶ F) (a' : G ⟶ F')
    (β : ((completionFunctor Y K).obj F).obj ≅ Fsys.obj)
    (β' : ((completionFunctor Y K).obj F').obj ≅ Fsys.obj)
    (hα : α = ((completionFunctor Y K).map a).hom ≫ β.hom)
    (hα' : α = ((completionFunctor Y K).map a').hom ≫ β'.hom)
    (hKa : IsPowerAnnihilated K (kernel (C := Y.Modules) a.hom))
    (hCa : IsPowerAnnihilated K (cokernel (C := Y.Modules) a.hom))
    (hKa' : IsPowerAnnihilated K (kernel (C := Y.Modules) a'.hom))
    (hCa' : IsPowerAnnihilated K (cokernel (C := Y.Modules) a'.hom)) :
    ∃! d : F ≅ F',
      a ≫ d.hom = a' ∧
        ((completionFunctor Y K).map d.hom).hom ≫ β'.hom = β.hom := by
  obtain ⟨J, hJ⟩ := exists_eq_ofIdealTop K
  subst hJ
  exact affine_unique_algebraization_dual Y J G Fsys α F F' a a' β β' hα hα' hKa hCa hKa' hCa'

/-! ### Restricting the datum to an open subscheme -/

/-- The datum `α : G^∧ ⟶ (F_n)` transported to an open subscheme: compare the completion of
`G|_Y` with the restricted completion of `G`, then restrict `α` term by term. -/
public noncomputable def restrictedSystemMapDual {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : ((completionFunctor X I).obj G).obj ⟶ Fsys.obj) :
    ((completionFunctor Y (I.comap f)).obj (restrictCoherentModules f G)).obj ⟶
      ((Stacks.Coherent.restrictFunctor I f).obj Fsys).obj :=
  (completionRestrictOpenIso f I G).inv ≫
    Functor.whiskerRight α (Scheme.Modules.restrictFunctor f)

/-- If the kernel of `φ` is killed by `ℐ ^ t`, so is the kernel of its restriction to an open. -/
private theorem idealPowerMultiple_kernel_restrict_eq_bot {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (I : X.IdealSheafData) (t : ℕ) {A B : X.Modules} (φ : A ⟶ B)
    (h : idealPowerMultiple I t (kernel φ) = ⊥) :
    idealPowerMultiple (I.comap f) t
      (kernel (C := Y.Modules) ((Scheme.Modules.restrictFunctor f).map φ)) = ⊥ := by
  have hfl : PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) :=
    AlgebraicGeometry.Modules.preservesFiniteLimits_restrictFunctor f
  have hpl : PreservesLimitsOfShape WalkingParallelPair (Scheme.Modules.restrictFunctor f) :=
    hfl.preservesFiniteLimits _
  exact idealPowerMultiple_eq_bot_of_iso (I.comap f)
    (PreservesKernel.iso (Scheme.Modules.restrictFunctor f) φ).symm t
    (idealPowerMultiple_restrict_eq_bot f I t _ h)

/-- If the cokernel of `φ` is killed by `ℐ ^ t`, so is the cokernel of its restriction to an
open. -/
private theorem idealPowerMultiple_cokernel_restrict_eq_bot {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (I : X.IdealSheafData) (t : ℕ) {A B : X.Modules} (φ : A ⟶ B)
    (h : idealPowerMultiple I t (cokernel φ) = ⊥) :
    idealPowerMultiple (I.comap f) t
      (cokernel (C := Y.Modules) ((Scheme.Modules.restrictFunctor f).map φ)) = ⊥ := by
  have hpc : PreservesColimitsOfShape WalkingParallelPair
    (Scheme.Modules.restrictFunctor f) := inferInstance
  exact idealPowerMultiple_eq_bot_of_iso (I.comap f)
    (PreservesCokernel.iso (Scheme.Modules.restrictFunctor f) φ).symm t
    (idealPowerMultiple_restrict_eq_bot f I t _ h)

/-- **The hypothesis of Stacks 0888 (1) restricts, in the direction out of the completion.** If
the levelwise kernels and cokernels of `α : G^∧ ⟶ (F_n)` are annihilated by a power of `ℐ`, then
so are those of the datum transported to an open subscheme.

Restriction along an open immersion is exact, so it carries the levelwise kernel and cokernel of
`α` to those of the restricted morphism — the comparison isomorphism of Stacks 0880 is
precomposed, and precomposing with an isomorphism changes neither the kernel nor the cokernel —
and it preserves annihilation by a power of the ideal sheaf. -/
public theorem isKernelCokernelAnnihilatedByPower_restrictedSystemMapDual {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : ((completionFunctor X I).obj G).obj ⟶ Fsys.obj)
    (hα : IsKernelCokernelAnnihilatedByPower I α) :
    IsKernelCokernelAnnihilatedByPower (I.comap f) (restrictedSystemMapDual f I G Fsys α) := by
  obtain ⟨t, ht, h⟩ := hα
  refine ⟨t, ht, fun k => ⟨?_, ?_⟩⟩
  · have hiso1 : IsIso ((completionRestrictOpenIso f I G).inv.app (op k)) :=
      NatIso.isIso_app_of_isIso _ _
    exact idealPowerMultiple_eq_bot_of_iso (I.comap f)
      (kernelIsIsoComp ((completionRestrictOpenIso f I G).inv.app (op k))
        ((Scheme.Modules.restrictFunctor f).map (α.app (op k)))) t
      (idealPowerMultiple_kernel_restrict_eq_bot f I t _ (h k).1)
  · have hiso1 : IsIso ((completionRestrictOpenIso f I G).inv.app (op k)) :=
      NatIso.isIso_app_of_isIso _ _
    exact idealPowerMultiple_eq_bot_of_iso (I.comap f)
      (cokernelEpiComp ((completionRestrictOpenIso f I G).inv.app (op k))
        ((Scheme.Modules.restrictFunctor f).map (α.app (op k)))) t
      (idealPowerMultiple_cokernel_restrict_eq_bot f I t _ (h k).2)

/-! ### Algebraization over an affine open -/

/-- The ring of global sections of an affine open of a locally Noetherian scheme is Noetherian. -/
private theorem isNoetherianRing_affineOpen {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U : X.affineOpens) : IsNoetherianRing Γ(U.1.toScheme, ⊤) :=
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  isNoetherianRing_of_ringEquiv _
    (Scheme.restrictFunctorΓ.app (op U.1)).symm.commRingCatIsoToRingEquiv

/-- **Algebraization over an affine open, in the direction out of the completion.** The datum
restricted to an affine open `U` admits an algebraization `G|_U ⟶ F` along `ℐ|_U`, whose kernel
and cokernel are annihilated by a power of `ℐ|_U`.

This is the affine theorem applied on `U`: the restricted system is a coherent `ℐ|_U`-adic
system, the restricted morphism still satisfies the hypothesis of Stacks 0888 (1), and the ring
`Γ(U, ⊤)` is Noetherian because `X` is locally Noetherian. -/
public theorem exists_local_algebraization_dual {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : ((completionFunctor X I).obj G).obj ⟶ Fsys.obj)
    (hα : IsKernelCokernelAnnihilatedByPower I α) (U : X.affineOpens) :
    ∃ (F : AlgebraicGeometry.SheafOfModules.CoherentModules U.1.toScheme.ringCatSheaf)
      (b : restrictCoherentModules U.1.ι G ⟶ F)
      (β : ((completionFunctor U.1.toScheme (I.comap U.1.ι)).obj F).obj ≅
        ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys).obj),
      restrictedSystemMapDual U.1.ι I G Fsys α =
          ((completionFunctor U.1.toScheme (I.comap U.1.ι)).map b).hom ≫ β.hom ∧
        IsPowerAnnihilated (I.comap U.1.ι)
            (kernel (C := U.1.toScheme.Modules) b.hom) ∧
          IsPowerAnnihilated (I.comap U.1.ι)
            (cokernel (C := U.1.toScheme.Modules) b.hom) := by
  have hAff : IsAffine U.1.toScheme := U.2
  have hNR := isNoetherianRing_affineOpen U
  exact affine_exists_algebraization_dual_of_idealSheafData U.1.toScheme (I.comap U.1.ι)
    (restrictCoherentModules U.1.ι G) ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys)
    (restrictedSystemMapDual U.1.ι I G Fsys α)
    (isKernelCokernelAnnihilatedByPower_restrictedSystemMapDual U.1.ι I G Fsys α hα)

/-- **The local algebraization out of `G|_U` is unique up to a unique isomorphism.** This is the
affine uniqueness clause applied on an affine open. -/
public theorem unique_local_algebraization_dual {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : ((completionFunctor X I).obj G).obj ⟶ Fsys.obj) (U : X.affineOpens)
    (F F' : AlgebraicGeometry.SheafOfModules.CoherentModules U.1.toScheme.ringCatSheaf)
    (b : restrictCoherentModules U.1.ι G ⟶ F) (b' : restrictCoherentModules U.1.ι G ⟶ F')
    (β : ((completionFunctor U.1.toScheme (I.comap U.1.ι)).obj F).obj ≅
      ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys).obj)
    (β' : ((completionFunctor U.1.toScheme (I.comap U.1.ι)).obj F').obj ≅
      ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys).obj)
    (hβ : restrictedSystemMapDual U.1.ι I G Fsys α =
      ((completionFunctor U.1.toScheme (I.comap U.1.ι)).map b).hom ≫ β.hom)
    (hβ' : restrictedSystemMapDual U.1.ι I G Fsys α =
      ((completionFunctor U.1.toScheme (I.comap U.1.ι)).map b').hom ≫ β'.hom)
    (hKb : IsPowerAnnihilated (I.comap U.1.ι) (kernel (C := U.1.toScheme.Modules) b.hom))
    (hCb : IsPowerAnnihilated (I.comap U.1.ι) (cokernel (C := U.1.toScheme.Modules) b.hom))
    (hKb' : IsPowerAnnihilated (I.comap U.1.ι) (kernel (C := U.1.toScheme.Modules) b'.hom))
    (hCb' : IsPowerAnnihilated (I.comap U.1.ι) (cokernel (C := U.1.toScheme.Modules) b'.hom)) :
    ∃! d : F ≅ F',
      b ≫ d.hom = b' ∧
        ((completionFunctor U.1.toScheme (I.comap U.1.ι)).map d.hom).hom ≫ β'.hom = β.hom := by
  have hAff : IsAffine U.1.toScheme := U.2
  have hNR := isNoetherianRing_affineOpen U
  exact affine_unique_algebraization_dual_of_idealSheafData U.1.toScheme (I.comap U.1.ι)
    (restrictCoherentModules U.1.ι G) ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys)
    (restrictedSystemMapDual U.1.ι I G Fsys α) F F' b b' β β' hβ hβ' hKb hCb hKb' hCb'

/-! ### Restriction-transitivity of the datum -/

section TransitivityHelpers

variable {C : Type*} [Category C]

/-- Reassociating a composite of three morphisms, given the first two composites. -/
theorem comp_assoc_eq_of_eq₂ {W X Y Z : C} {p : W ⟶ X} {a : X ⟶ Y} {m : Y ⟶ Z}
    {u : W ⟶ Y} {w : W ⟶ Z} (h₁ : p ≫ a = u) (h₂ : u ≫ m = w) : p ≫ a ≫ m = w := by
  rw [← Category.assoc, h₁, h₂]

/-- Reassociating a composite of three morphisms whose head splits off a common factor. -/
theorem comp_assoc_eq_comp_of_eq₂ {W X Y Z S : C} {p : W ⟶ X} {a : X ⟶ Y} {m : Y ⟶ Z}
    {e : W ⟶ S} {v : S ⟶ Y} {w : S ⟶ Z} (h₁ : p ≫ a = e ≫ v) (h₂ : v ≫ m = w) :
    p ≫ a ≫ m = e ≫ w := by
  rw [← Category.assoc, h₁, Category.assoc, h₂]

/-- Reassociating a composite of four morphisms whose middle step splits off a common factor. -/
private theorem comp_assoc_eq_comp_of_eq₃ {W X Y Z T S : C} {p : W ⟶ X} {a : X ⟶ Y} {b : Y ⟶ Z}
    {k : Z ⟶ T} {u : W ⟶ Y} {e : W ⟶ S} {v : S ⟶ Z} {w : S ⟶ T} (h₁ : p ≫ a = u)
    (h₂ : u ≫ b = e ≫ v) (h₃ : v ≫ k = w) : p ≫ a ≫ b ≫ k = e ≫ w := by
  rw [← Category.assoc, ← Category.assoc, h₁, h₂, Category.assoc, h₃]

end TransitivityHelpers

/-- **A morphism out of a completion is determined by its composites with the projections.** Two
morphisms of inverse systems out of the completion of a coherent module agree as soon as they
agree after precomposition with the canonical projection at each level, those projections being
epimorphisms by Stacks 0880. -/
public theorem completionSystemHom_ext (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    (J : Y.IdealSheafData)
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    {S : ℕᵒᵖ ⥤ Y.Modules} (u v : ((completionFunctor Y J).obj M).obj ⟶ S)
    (h : ∀ n : ℕ, completionProjection Y J M n ≫ u.app (op n) =
      completionProjection Y J M n ≫ v.app (op n)) : u = v := by
  refine NatTrans.ext (funext fun n => ?_)
  have hepi := epi_completionProjection Y J M n.unop
  exact (@cancel_epi _ _ _ _ _ (completionProjection Y J M n.unop) hepi _ _).mp (h n.unop)

/-- The projection onto a term of a restricted completion, read through the inverse of the
comparison isomorphism of Stacks 0880. -/
public theorem completionProjection_comp_completionRestrictOpenIso_inv {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    completionProjection Y (I.comap f) (restrictCoherentModules f G) n ≫
        (completionRestrictOpenIso f I G).inv.app (op n) =
      (Scheme.Modules.restrictFunctor f).map (completionProjection X I G n) :=
  (Iso.comp_inv_eq ((completionRestrictOpenIso f I G).app (op n))).2
    (completionProjection_comp_completionRestrictOpenIso f I G n).symm

/-- **The restricted datum, read through the projections.** Precomposing the datum of part (2)
transported to an open subscheme with the canonical projection at level `n` is the restriction of
the composite of the projection on `X` with the level-`n` component of `α`.

The comparison isomorphism of Stacks 0880 is precomposed in
`Stacks.Algebraization.restrictedSystemMapDual`, and
`Stacks.Algebraization.completionProjection_comp_completionRestrictOpenIso` says that it carries
the restriction of the projection to the projection of the restriction. -/
public theorem completionProjection_comp_restrictedSystemMapDual {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : ((completionFunctor X I).obj G).obj ⟶ Fsys.obj) (n : ℕ) :
    completionProjection Y (I.comap f) (restrictCoherentModules f G) n ≫
        (restrictedSystemMapDual f I G Fsys α).app (op n) =
      (Scheme.Modules.restrictFunctor f).map (completionProjection X I G n ≫ α.app (op n)) := by
  change completionProjection Y (I.comap f) (restrictCoherentModules f G) n ≫
      (completionRestrictOpenIso f I G).inv.app (op n) ≫
        (Scheme.Modules.restrictFunctor f).map (α.app (op n)) =
    (Scheme.Modules.restrictFunctor f).map (completionProjection X I G n ≫ α.app (op n))
  exact comp_assoc_eq_of_eq₂
    (completionProjection_comp_completionRestrictOpenIso_inv f I G n)
    ((Scheme.Modules.restrictFunctor f).map_comp _ _).symm

/-- The source of the datum restricted along a composite of two open immersions, compared with
the source of the datum restricted in two steps. Both are the completion of a restriction of `G`,
and the comparison is built out of the two comparison isomorphisms of Stacks 0880 and the
composition isomorphism of the restriction functors. -/
public noncomputable def restrictedCompletionCompIso {X Y V : Scheme.{u}} (g : V ⟶ Y) (f : Y ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian V] (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    ((completionFunctor V (I.comap (g ≫ f))).obj (restrictCoherentModules (g ≫ f) G)).obj ≅
      ((completionFunctor V ((I.comap f).comap g)).obj
        (restrictCoherentModules g (restrictCoherentModules f G))).obj :=
  (completionRestrictOpenIso (g ≫ f) I G).symm ≪≫
    Functor.isoWhiskerLeft ((completionFunctor X I).obj G).obj
        (Scheme.Modules.restrictFunctorComp g f) ≪≫
      Functor.isoWhiskerRight (completionRestrictOpenIso f I G)
          (Scheme.Modules.restrictFunctor g) ≪≫
        completionRestrictOpenIso g (I.comap f) (restrictCoherentModules f G)

/-- The target of the datum restricted along a composite of two open immersions, compared with
the target of the datum restricted in two steps: both are a termwise restriction of the system
`(F_n)`, and the comparison is the composition isomorphism of the restriction functors. -/
public noncomputable def restrictedSystemCompIso {X Y V : Scheme.{u}} (g : V ⟶ Y) (f : Y ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (I : X.IdealSheafData) (Fsys : Stacks.Coherent.CoherentAdicSystems I) :
    ((Stacks.Coherent.restrictFunctor I (g ≫ f)).obj Fsys).obj ≅
      ((Stacks.Coherent.restrictFunctor (I.comap f) g).obj
        ((Stacks.Coherent.restrictFunctor I f).obj Fsys)).obj :=
  Functor.isoWhiskerLeft Fsys.obj (Scheme.Modules.restrictFunctorComp g f)

/-- **The comparison of the two restricted completions, read through the projections.** The
isomorphism `Stacks.Algebraization.restrictedCompletionCompIso` carries the projection of the
completion restricted along `g ≫ f` to the projection of the completion restricted in two steps,
up to the composition isomorphism of the restriction functors. -/
public theorem completionProjection_comp_restrictedCompletionCompIso {X Y V : Scheme.{u}}
    (g : V ⟶ Y) (f : Y ⟶ X) [IsOpenImmersion g] [IsOpenImmersion f] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian V] (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    completionProjection V (I.comap (g ≫ f)) (restrictCoherentModules (g ≫ f) G) n ≫
        (restrictedCompletionCompIso g f I G).hom.app (op n) =
      (Scheme.Modules.restrictFunctorComp g f).hom.app G.obj ≫
        completionProjection V ((I.comap f).comap g)
          (restrictCoherentModules g (restrictCoherentModules f G)) n := by
  have hin : (Scheme.Modules.restrictFunctor g).map
        ((Scheme.Modules.restrictFunctor f).map (completionProjection X I G n)) ≫
      (Scheme.Modules.restrictFunctor g).map ((completionRestrictOpenIso f I G).hom.app (op n)) ≫
        (completionRestrictOpenIso g (I.comap f) (restrictCoherentModules f G)).hom.app (op n) =
      completionProjection V ((I.comap f).comap g)
        (restrictCoherentModules g (restrictCoherentModules f G)) n :=
    comp_assoc_eq_of_eq₂
      (((Scheme.Modules.restrictFunctor g).map_comp _ _).symm.trans
        (congrArg (Scheme.Modules.restrictFunctor g).map
          (completionProjection_comp_completionRestrictOpenIso f I G n)))
      (completionProjection_comp_completionRestrictOpenIso g (I.comap f)
        (restrictCoherentModules f G) n)
  change completionProjection V (I.comap (g ≫ f)) (restrictCoherentModules (g ≫ f) G) n ≫
      (completionRestrictOpenIso (g ≫ f) I G).inv.app (op n) ≫
        (Scheme.Modules.restrictFunctorComp g f).hom.app
            (((completionFunctor X I).obj G).obj.obj (op n)) ≫
          (Scheme.Modules.restrictFunctor g).map
              ((completionRestrictOpenIso f I G).hom.app (op n)) ≫
            (completionRestrictOpenIso g (I.comap f) (restrictCoherentModules f G)).hom.app
              (op n) =
    (Scheme.Modules.restrictFunctorComp g f).hom.app G.obj ≫
      completionProjection V ((I.comap f).comap g)
        (restrictCoherentModules g (restrictCoherentModules f G)) n
  exact comp_assoc_eq_comp_of_eq₃
    (completionProjection_comp_completionRestrictOpenIso_inv (g ≫ f) I G n)
    ((Scheme.Modules.restrictFunctorComp g f).hom.naturality (completionProjection X I G n)) hin

/-- **Restriction-transitivity of the datum of Stacks 0889 (2).** For open immersions
`g : V ⟶ Y` and `f : Y ⟶ X`, restricting the datum along `f` and then along `g` is the same as
restricting it along `g ≫ f`, through the comparison isomorphisms
`Stacks.Algebraization.restrictedCompletionCompIso` of the sources and
`Stacks.Algebraization.restrictedSystemCompIso` of the targets.

Both sides are morphisms out of the completion of a restriction of `G`, so by
`Stacks.Algebraization.completionSystemHom_ext` it suffices to compare them after the canonical
projections, where `Stacks.Algebraization.completionProjection_comp_restrictedSystemMapDual`
turns each into a restriction of the composite of a projection on `X` with a component of `α`. -/
public theorem restrictedSystemMapDual_comp {X Y V : Scheme.{u}} (g : V ⟶ Y) (f : Y ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian V] (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : ((completionFunctor X I).obj G).obj ⟶ Fsys.obj) :
    restrictedSystemMapDual (g ≫ f) I G Fsys α ≫ (restrictedSystemCompIso g f I Fsys).hom =
      (restrictedCompletionCompIso g f I G).hom ≫
        restrictedSystemMapDual g (I.comap f) (restrictCoherentModules f G)
          ((Stacks.Coherent.restrictFunctor I f).obj Fsys)
          (restrictedSystemMapDual f I G Fsys α) := by
  refine completionSystemHom_ext V (I.comap (g ≫ f)) (restrictCoherentModules (g ≫ f) G) _ _
    fun n => ?_
  have hleft : completionProjection V (I.comap (g ≫ f))
        (restrictCoherentModules (g ≫ f) G) n ≫
      (restrictedSystemMapDual (g ≫ f) I G Fsys α).app (op n) ≫
        (Scheme.Modules.restrictFunctorComp g f).hom.app (Fsys.obj.obj (op n)) =
      (Scheme.Modules.restrictFunctorComp g f).hom.app G.obj ≫
        (Scheme.Modules.restrictFunctor f ⋙ Scheme.Modules.restrictFunctor g).map
          (completionProjection X I G n ≫ α.app (op n)) :=
    comp_assoc_eq_of_eq₂
      (completionProjection_comp_restrictedSystemMapDual (g ≫ f) I G Fsys α n)
      ((Scheme.Modules.restrictFunctorComp g f).hom.naturality
        (completionProjection X I G n ≫ α.app (op n)))
  have hright : completionProjection V (I.comap (g ≫ f))
        (restrictCoherentModules (g ≫ f) G) n ≫
      (restrictedCompletionCompIso g f I G).hom.app (op n) ≫
        (restrictedSystemMapDual g (I.comap f) (restrictCoherentModules f G)
          ((Stacks.Coherent.restrictFunctor I f).obj Fsys)
          (restrictedSystemMapDual f I G Fsys α)).app (op n) =
      (Scheme.Modules.restrictFunctorComp g f).hom.app G.obj ≫
        (Scheme.Modules.restrictFunctor g).map
          ((Scheme.Modules.restrictFunctor f).map
            (completionProjection X I G n ≫ α.app (op n))) :=
    comp_assoc_eq_comp_of_eq₂
      (completionProjection_comp_restrictedCompletionCompIso g f I G n)
      (((completionProjection_comp_restrictedSystemMapDual g (I.comap f)
        (restrictCoherentModules f G) ((Stacks.Coherent.restrictFunctor I f).obj Fsys)
        (restrictedSystemMapDual f I G Fsys α) n)).trans
          (congrArg (Scheme.Modules.restrictFunctor g).map
            (completionProjection_comp_restrictedSystemMapDual f I G Fsys α n)))
  exact hleft.trans hright.symm

/-! ### Naturality of the comparison isomorphism in the module -/

/-- The restriction of a morphism of coherent modules along an open immersion, as a morphism of
the restricted coherent modules. -/
public noncomputable def restrictCoherentModulesMap {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] [IsLocallyNoetherian X]
    {G F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (b : G ⟶ F) :
    restrictCoherentModules f G ⟶ restrictCoherentModules f F :=
  ObjectProperty.homMk ((Scheme.Modules.restrictFunctor f).map b.hom)

/-- **The comparison isomorphism of Stacks 0880 is natural in the module.** Completing a morphism
`b : G ⟶ F` of coherent modules on `X` and restricting the result to an open subscheme `Y` is the
completion along `ℐ|_Y` of the restriction of `b`, read through the comparison isomorphisms of the
two modules.

Both sides are morphisms out of the completion of `G|_Y`, so by
`Stacks.Algebraization.completionSystemHom_ext` it is enough to compare them after the canonical
projections, where each becomes the restriction of `b` followed by a projection, by
`Stacks.Algebraization.completionFunctor_map_quotient` and
`Stacks.Algebraization.completionProjection_comp_completionRestrictOpenIso_inv`. -/
public theorem completionRestrictOpenIso_inv_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (I : X.IdealSheafData)
    {G F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (b : G ⟶ F) :
    (completionRestrictOpenIso f I G).inv ≫
        Functor.whiskerRight ((completionFunctor X I).map b).hom
          (Scheme.Modules.restrictFunctor f) =
      ((completionFunctor Y (I.comap f)).map (restrictCoherentModulesMap f b)).hom ≫
        (completionRestrictOpenIso f I F).inv := by
  refine completionSystemHom_ext Y (I.comap f) (restrictCoherentModules f G) _ _ fun n => ?_
  have hL : completionProjection Y (I.comap f) (restrictCoherentModules f G) n ≫
      (completionRestrictOpenIso f I G).inv.app (op n) ≫
        (Scheme.Modules.restrictFunctor f).map
          (((completionFunctor X I).map b).hom.app (op n)) =
      (Scheme.Modules.restrictFunctor f).map (b.hom ≫ completionProjection X I F n) :=
    (comp_assoc_eq_of_eq₂
        (completionProjection_comp_completionRestrictOpenIso_inv f I G n)
        ((Scheme.Modules.restrictFunctor f).map_comp _ _).symm).trans
      (congrArg (Scheme.Modules.restrictFunctor f).map
        (completionFunctor_map_quotient X I b n))
  have hR : completionProjection Y (I.comap f) (restrictCoherentModules f G) n ≫
      ((completionFunctor Y (I.comap f)).map (restrictCoherentModulesMap f b)).hom.app (op n) ≫
        (completionRestrictOpenIso f I F).inv.app (op n) =
      (restrictCoherentModulesMap f b).hom ≫
        (Scheme.Modules.restrictFunctor f).map (completionProjection X I F n) :=
    comp_assoc_eq_comp_of_eq₂
      (completionFunctor_map_quotient Y (I.comap f) (restrictCoherentModulesMap f b) n)
      (completionProjection_comp_completionRestrictOpenIso_inv f I F n)
  change completionProjection Y (I.comap f) (restrictCoherentModules f G) n ≫
      (completionRestrictOpenIso f I G).inv.app (op n) ≫
        (Scheme.Modules.restrictFunctor f).map
          (((completionFunctor X I).map b).hom.app (op n)) =
    completionProjection Y (I.comap f) (restrictCoherentModules f G) n ≫
      ((completionFunctor Y (I.comap f)).map (restrictCoherentModulesMap f b)).hom.app (op n) ≫
        (completionRestrictOpenIso f I F).inv.app (op n)
  exact hL.trans
    (((Scheme.Modules.restrictFunctor f).map_comp _ _).trans hR.symm)

/-! ### A local algebraization restricts to a local algebraization -/

/-- The isomorphism of an algebraization transported to an open subscheme: compare the completion
of `F|_V` with the restricted completion of `F`, then restrict `β` term by term. -/
public noncomputable def restrictedAlgebraizationIsoDual {Y V : Scheme.{u}} (g : V ⟶ Y)
    [IsOpenImmersion g] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] (K : Y.IdealSheafData)
    (Ssys : Stacks.Coherent.CoherentAdicSystems K)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (β : ((completionFunctor Y K).obj F).obj ≅ Ssys.obj) :
    ((completionFunctor V (K.comap g)).obj (restrictCoherentModules g F)).obj ≅
      ((Stacks.Coherent.restrictFunctor K g).obj Ssys).obj :=
  (completionRestrictOpenIso g K F).symm ≪≫
    Functor.isoWhiskerRight β (Scheme.Modules.restrictFunctor g)

/-- **The factorization of an algebraization restricts.** If `α : G^∧ ⟶ (F_n)` factors as the
completion of `b : G ⟶ F` followed by an isomorphism `β`, then the datum transported to an open
subscheme `V` factors as the completion of `b|_V` followed by
`Stacks.Algebraization.restrictedAlgebraizationIsoDual`.

The whole content is the naturality of the comparison isomorphism of Stacks 0880 in the module,
`Stacks.Algebraization.completionRestrictOpenIso_inv_naturality`: restriction is a functor, so it
carries the factorization of `α` to a factorization of its restriction, and that naturality moves
the comparison isomorphism of `G` past the completion of `b`. -/
public theorem restrictedSystemMapDual_eq_of_algebraization {Y V : Scheme.{u}} (g : V ⟶ Y)
    [IsOpenImmersion g] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] (K : Y.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (Ssys : Stacks.Coherent.CoherentAdicSystems K)
    (α : ((completionFunctor Y K).obj G).obj ⟶ Ssys.obj)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf) (b : G ⟶ F)
    (β : ((completionFunctor Y K).obj F).obj ≅ Ssys.obj)
    (hβ : α = ((completionFunctor Y K).map b).hom ≫ β.hom) :
    restrictedSystemMapDual g K G Ssys α =
      ((completionFunctor V (K.comap g)).map (restrictCoherentModulesMap g b)).hom ≫
        (restrictedAlgebraizationIsoDual g K Ssys F β).hom := by
  rw [hβ]
  change (completionRestrictOpenIso g K G).inv ≫
      Functor.whiskerRight (((completionFunctor Y K).map b).hom ≫ β.hom)
        (Scheme.Modules.restrictFunctor g) =
    ((completionFunctor V (K.comap g)).map (restrictCoherentModulesMap g b)).hom ≫
      (completionRestrictOpenIso g K F).inv ≫
        Functor.whiskerRight β.hom (Scheme.Modules.restrictFunctor g)
  exact (congrArg (fun k => (completionRestrictOpenIso g K G).inv ≫ k)
      (Functor.whiskerRight_comp _ _ _)).trans
    (comp_assoc_eq_comp_of_eq₂ (completionRestrictOpenIso_inv_naturality g K b) rfl)

/-- **The kernel of an algebraization stays power-annihilated after restriction.** Restriction
along an open immersion is exact, so it carries the kernel of `b` to the kernel of `b|_V`, and it
preserves annihilation by a power of the ideal sheaf. -/
public theorem isPowerAnnihilated_kernel_restrictCoherentModulesMap {Y V : Scheme.{u}}
    (g : V ⟶ Y) [IsOpenImmersion g] [IsLocallyNoetherian Y] [IsLocallyNoetherian V]
    (K : Y.IdealSheafData)
    {G F : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf} (b : G ⟶ F)
    (h : IsPowerAnnihilated K (kernel (C := Y.Modules) b.hom)) :
    IsPowerAnnihilated (K.comap g)
      (kernel (C := V.Modules) (restrictCoherentModulesMap g b).hom) := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, idealPowerMultiple_kernel_restrict_eq_bot g K t _ ht⟩

/-- **The cokernel of an algebraization stays power-annihilated after restriction.** -/
public theorem isPowerAnnihilated_cokernel_restrictCoherentModulesMap {Y V : Scheme.{u}}
    (g : V ⟶ Y) [IsOpenImmersion g] [IsLocallyNoetherian Y] [IsLocallyNoetherian V]
    (K : Y.IdealSheafData)
    {G F : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf} (b : G ⟶ F)
    (h : IsPowerAnnihilated K (cokernel (C := Y.Modules) b.hom)) :
    IsPowerAnnihilated (K.comap g)
      (cokernel (C := V.Modules) (restrictCoherentModulesMap g b).hom) := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, idealPowerMultiple_cokernel_restrict_eq_bot g K t _ ht⟩

end Stacks.Algebraization

end
