module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineBaseChangeKernel
public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineComparisonAbstract

/-!
# The affine base change of ambient sections along an arbitrary morphism, from the `f`-map alone

`StacksFrontier/AlgebraicGeometry/Crystalline/AffineComparisonAbstract.lean` produces, from a
morphism `g : (U', T', δ') ⟶ (U, T, δ)` of `CRIS(X/S)` and an `f`-map `N_T ⟶ g_* N_{T'}` between
two modules over the restrictions of `𝒪_{X/S}` to the two ambient schemes, the comparison map

`c_g : g^* N_T ⟶ N_{T'}`,

and shows it to be an isomorphism as soon as the comparison map over the restricted structure
sheaves is.  This module composes that comparison with
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` on the affine ambient schemes and obtains

`Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} Γ(T, N_T) ⟶ Γ(T', N_{T'})`,  `t ⊗ a ↦ t · (f-map of a)`,

bijective, and reads off its kernel on the pure tensors `1 ⊗ a`.

Nothing here mentions a coefficient sheaf, so the statements apply on **either** crystalline
site: at `N_T = F_T` for a sheaf of modules on `CRIS(X/S)` they are the computation of
`StacksFrontier/AlgebraicGeometry/Crystalline/AffineBaseChangeAlong.lean` read on ambient sections,
and at `N_T = ℱ_T` for a sheaf of modules on `Cris(X/S)` they are the same computation there.

The two scalar actions are carried on the synonym
`Crystalline.GlobalCrystallineSituation.ringAlong` for the reason recorded in the module
documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/AffineBaseChangeAlong.lean`: neither is determined by
the pair of objects, both being built from `g`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.fmapTopSection` — the `f`-map on global sections, with
  its value named in the sections of `N_{T'}` over the whole of `T'`.
* `Crystalline.GlobalCrystallineSituation.ambientCrossAbstract` — the bridge identifying the
  plain tensor product over the ambient sections with the carrier of Mathlib's
  `ModuleCat.extendScalars`.
* `Crystalline.GlobalCrystallineSituation.ambientBaseChangeTensorFun` — the base change of
  ambient sections.

## Main results

* `Crystalline.GlobalCrystallineSituation.ambientBaseChangeTensorFun_tmul` — the normalisation
  `t ⊗ a ↦ t · (f-map of a)`.
* `Crystalline.GlobalCrystallineSituation.bijective_ambientBaseChangeTensorFun` — **the base
  change of ambient sections is bijective** on affine objects with quasi-coherent `N_T`, as soon
  as the comparison map is an isomorphism.
* `Crystalline.GlobalCrystallineSituation.fmapTopSection_eq_zero_iff_exists_smul` — **the
  kernel of the `f`-map on global sections is the subgroup of `α`-multiples**, when the map on
  sections of the structure sheaves of the ambient schemes is surjective with kernel `(α)`.

## References

* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PresheafOfModules
open scoped AlgebraicGeometry TensorProduct ChangeOfRings

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}} {A A' : Thickening S} (g : A' ⟶ A)
  (NA : SheafOfModules.{u} A.ringRestrictionSheaf)
  (NA' : SheafOfModules.{u} A'.ringRestrictionSheaf)
  (fmap : NA ⟶ (SheafOfModules.pushforward.{u} (Thickening.ringRestrictionSheafFMap g)).obj NA')

/-! ### Two namings -/

/-- **The `f`-map of [Stacks, Tag 07IQ] on global sections**, with its value named in the
sections of `N_{T'}` over the whole of `T'`.  The pushforward has the sections of `N_{T'}` over
the preimage of the whole of `T` for its sections over the whole of `T`, and that preimage is the
whole of `T'`; the two are the same type in two spellings, and only the second carries the action
of `Γ(T', 𝒪_{T'})`. -/
def fmapTopSection (x : Γ(ambientSchemeOf A NA, ⊤)) : Γ(ambientSchemeOf A' NA', ⊤) :=
  fmap.val.app (op ⊤) x

/-- The normalisation of the comparison map,
`...GlobalCrystallineSituation.ambientComparisonAbstract_ambientPullbackSectionTopAbstract`,
with its right-hand side named. -/
theorem ambientComparisonAbstract_fmapTopSection (x : Γ(ambientSchemeOf A NA, ⊤)) :
    (ambientComparisonAbstract g NA NA' fmap).app ⊤
        (ambientPullbackSectionTopAbstract g NA x) = fmapTopSection g NA NA' fmap x :=
  ambientComparisonAbstract_ambientPullbackSectionTopAbstract g NA NA' fmap x

/-- **The plain tensor product of the ambient sections over
`Crystalline.GlobalCrystallineSituation.moduleAmbientRingAlong` is the carrier of Mathlib's
`ModuleCat.extendScalars`**, the two scalar actions being the same `Module.compHom` term.  The
single crossing of that boundary; it is the identity. -/
def ambientCrossAbstract
    (z : ringAlong g ⊗[Γ(A.thickening.target.scheme, ⊤)] Γ(ambientSchemeOf A NA, ⊤)) :
    ((ModuleCat.extendScalars (g.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient g)).hom).obj
      (ModuleCat.of Γ(A.thickening.target.scheme, ⊤) Γ(ambientSchemeOf A NA, ⊤)) : Type u) := z

/-- The bridge, on a pure tensor. -/
theorem ambientCrossAbstract_tmul (t : ringAlong g) (a : Γ(ambientSchemeOf A NA, ⊤)) :
    ambientCrossAbstract g NA (t ⊗ₜ[Γ(A.thickening.target.scheme, ⊤)] a) =
      ambientRingSection A' (siteRingAlong g t) ⊗ₜ[
        Γ(A.thickening.target.scheme, ⊤),
        (g.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient g)).hom] a := rfl

/-- The bridge carries zero to zero; it is the identity. -/
theorem ambientCrossAbstract_zero :
    ambientCrossAbstract g NA
      (0 : ringAlong g ⊗[Γ(A.thickening.target.scheme, ⊤)] Γ(ambientSchemeOf A NA, ⊤)) = 0 := rfl

/-- The bridge is injective; it is the identity. -/
theorem injective_ambientCrossAbstract : Function.Injective (ambientCrossAbstract g NA) :=
  fun _ _ h ↦ h

/-- The bridge is surjective; it is the identity. -/
theorem surjective_ambientCrossAbstract : Function.Surjective (ambientCrossAbstract g NA) :=
  fun y ↦ ⟨y, rfl⟩

section Affine

variable [IsAffine A.thickening.target.scheme] [IsAffine A'.thickening.target.scheme]
  [(ambientSchemeOf A NA).IsQuasicoherent]

/-- The affine base-change comparison of [Stacks, Tag 01I9] at the whole of the two ambient
schemes, which are affine. -/
abbrev affineBaseChangeTopIsoAbstract :=
  affinePullbackSectionsBaseChangeIso g.targetHom.hom (ambientSchemeOf A NA)
    (isAffineOpen_top _) (isAffineOpen_top _) (top_le_preimage_ambient g)

/-- The base-change comparison at `⊤, ⊤`, as an additive map. -/
def affineBaseChangeTopHomAbstract :
    ((ModuleCat.extendScalars (g.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient g)).hom).obj
      (ModuleCat.of Γ(A.thickening.target.scheme, ⊤) Γ(ambientSchemeOf A NA, ⊤)) : Type u) →+
      ((ModuleCat.of Γ(A'.thickening.target.scheme, ⊤)
        Γ((Scheme.Modules.pullback g.targetHom.hom).obj (ambientSchemeOf A NA), ⊤)) : Type u) :=
  (affineBaseChangeTopIsoAbstract g NA).hom.hom.toAddMonoidHom

/-- The base-change comparison, written out. -/
theorem affineBaseChangeTopHomAbstract_apply
    (w : ((ModuleCat.extendScalars
        (g.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient g)).hom).obj
      (ModuleCat.of Γ(A.thickening.target.scheme, ⊤) Γ(ambientSchemeOf A NA, ⊤)) : Type u)) :
    affineBaseChangeTopHomAbstract g NA w = (affineBaseChangeTopIsoAbstract g NA).hom w := rfl

/-- **The base-change comparison is bijective** under quasi-coherence and affineness, being an
isomorphism of `ModuleCat`. -/
theorem bijective_affineBaseChangeTopHomAbstract :
    Function.Bijective (affineBaseChangeTopHomAbstract g NA) := by
  have h : (affineBaseChangeTopHomAbstract g NA : _ → _) =
      fun w ↦ (affineBaseChangeTopIsoAbstract g NA).hom w :=
    funext fun w ↦ affineBaseChangeTopHomAbstract_apply g NA w
  rw [h]
  exact ConcreteCategory.bijective_of_isIso (affineBaseChangeTopIsoAbstract g NA).hom

/-- `Crystalline.GlobalCrystallineSituation.ambientPullbackSectionTopAbstract`, with its type
named at the codomain of the base-change comparison. -/
def ambientPullbackSectionTopModuleAbstract (x : Γ(ambientSchemeOf A NA, ⊤)) :
    ((ModuleCat.of Γ(A'.thickening.target.scheme, ⊤)
      Γ((Scheme.Modules.pullback g.targetHom.hom).obj (ambientSchemeOf A NA), ⊤)) : Type u) :=
  ambientPullbackSectionTopAbstract g NA x

omit [IsAffine A.thickening.target.scheme] [IsAffine A'.thickening.target.scheme]
  [SheafOfModules.IsQuasicoherent (ambientSchemeOf A NA)] in
/-- **The comparison map on a scalar multiple of a pullback of a section.**  The comparison map
is semilinear and its normalisation
`Crystalline.GlobalCrystallineSituation.ambientComparisonAbstract_fmapTopSection` applies to the
pullback. -/
theorem ambientComparisonAbstractTop_smul_ambientPullbackSectionTopModuleAbstract
    (r : Γ(A'.thickening.target.scheme, ⊤)) (x : Γ(ambientSchemeOf A NA, ⊤)) :
    ambientComparisonAbstractTop g NA NA' fmap
        (r • ambientPullbackSectionTopModuleAbstract g NA x) =
      r • fmapTopSection g NA NA' fmap x := by
  change (ambientComparisonAbstract g NA NA' fmap).app ⊤
    (r • ambientPullbackSectionTopAbstract g NA x) = _
  rw [Scheme.Modules.Hom.app_smul, ambientComparisonAbstract_fmapTopSection]

/-- The base-change comparison at `⊤, ⊤` carries `1 ⊗ a` to the pullback of `a`.  This is
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_one_tmul`, with its value named at the
`ModuleCat` object whose carrier it is. -/
theorem affineBaseChangeTopAbstract_one_tmul
    (a : Γ(ambientSchemeOf A NA, (⊤ : A.thickening.target.scheme.Opens))) :
    (affinePullbackSectionsBaseChangeIso g.targetHom.hom (ambientSchemeOf A NA)
        (isAffineOpen_top _) (isAffineOpen_top _) (top_le_preimage_ambient g)).hom
        ((1 : Γ(A'.thickening.target.scheme,
          (⊤ : A'.thickening.target.scheme.Opens))) ⊗ₜ[
        Γ(A.thickening.target.scheme, (⊤ : A.thickening.target.scheme.Opens)),
        (g.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient g)).hom] a) =
      ambientPullbackSectionTopModuleAbstract g NA a :=
  affinePullbackSectionsBaseChangeIso_one_tmul g.targetHom.hom (ambientSchemeOf A NA)
    (isAffineOpen_top _) (isAffineOpen_top _) (top_le_preimage_ambient g) a

/-- The base-change comparison at `⊤, ⊤` carries `t ⊗ a` to `t` times the pullback of `a`.  It is
a declaration of its own so that the two elaborations are paid for out of two budgets. -/
theorem affineBaseChangeTopAbstract_tmul
    (r : Γ(A'.thickening.target.scheme, (⊤ : A'.thickening.target.scheme.Opens)))
    (a : Γ(ambientSchemeOf A NA, (⊤ : A.thickening.target.scheme.Opens))) :
    (affinePullbackSectionsBaseChangeIso g.targetHom.hom (ambientSchemeOf A NA)
        (isAffineOpen_top _) (isAffineOpen_top _) (top_le_preimage_ambient g)).hom (r ⊗ₜ[
        Γ(A.thickening.target.scheme, (⊤ : A.thickening.target.scheme.Opens)),
        (g.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient g)).hom] a) =
      r • ambientPullbackSectionTopModuleAbstract g NA a :=
  (affinePullbackSectionsBaseChangeIso_tmul g.targetHom.hom (ambientSchemeOf A NA)
    (isAffineOpen_top _) (isAffineOpen_top _) (top_le_preimage_ambient g) r a).trans
      (congrArg (fun z ↦ r • z) (affineBaseChangeTopAbstract_one_tmul g NA a))

/-- **The abbreviation naming the affine base-change comparison is that comparison.**  Trivial,
and stated because it is the one step that has to be taken as a *rewrite*. -/
theorem affineBaseChangeTopIsoAbstract_eq :
    affineBaseChangeTopIsoAbstract g NA =
      affinePullbackSectionsBaseChangeIso g.targetHom.hom (ambientSchemeOf A NA)
        (isAffineOpen_top _) (isAffineOpen_top _) (top_le_preimage_ambient g) := rfl

/-- `Crystalline.GlobalCrystallineSituation.affineBaseChangeTopAbstract_tmul`, read through the
abbreviation the chain is written with. -/
theorem affineBaseChangeTopIsoAbstract_hom_tmul
    (r : Γ(A'.thickening.target.scheme, (⊤ : A'.thickening.target.scheme.Opens)))
    (a : Γ(ambientSchemeOf A NA, (⊤ : A.thickening.target.scheme.Opens))) :
    (affineBaseChangeTopIsoAbstract g NA).hom (r ⊗ₜ[
        Γ(A.thickening.target.scheme, (⊤ : A.thickening.target.scheme.Opens)),
        (g.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient g)).hom] a) =
      r • ambientPullbackSectionTopModuleAbstract g NA a := by
  rw [affineBaseChangeTopIsoAbstract_eq]
  exact affineBaseChangeTopAbstract_tmul g NA r a

/-! ### The base change of the ambient sections -/

/-- **The base change of the ambient sections along `g`, on the extension of scalars**: the
base-change comparison of [Stacks, Tag 01I9] followed by the comparison map of
[Stacks, Tag 07IQ] on sections over the whole of `T'`. -/
def ambientBaseChangeFunAbstract
    (w : ((ModuleCat.extendScalars
        (g.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient g)).hom).obj
      (ModuleCat.of Γ(A.thickening.target.scheme, ⊤) Γ(ambientSchemeOf A NA, ⊤)) : Type u)) :
    Γ(ambientSchemeOf A' NA', ⊤) :=
  ambientComparisonAbstractTop g NA NA' fmap ((affineBaseChangeTopIsoAbstract g NA).hom w)

/-- **It is bijective** as soon as the comparison map over the restricted structure sheaves is an
isomorphism: both of its factors are. -/
theorem bijective_ambientBaseChangeFunAbstract
    (hc : IsIso (comparisonAbstract g NA NA' fmap)) :
    Function.Bijective (ambientBaseChangeFunAbstract g NA NA' fmap) := by
  exact (bijective_ambientComparisonAbstractTop g NA NA' fmap hc).comp
    (bijective_affineBaseChangeTopHomAbstract g NA)

/-- **The base change of the ambient sections, on the plain tensor product.**  The bridge
followed by the map above. -/
def ambientBaseChangeTensorFun
    (z : ringAlong g ⊗[Γ(A.thickening.target.scheme, ⊤)] Γ(ambientSchemeOf A NA, ⊤)) :
    Γ(ambientSchemeOf A' NA', ⊤) :=
  ambientBaseChangeFunAbstract g NA NA' fmap (ambientCrossAbstract g NA z)

/-- **The base change of ambient sections is bijective** on affine objects with quasi-coherent
`N_T`, as soon as the comparison map over the restricted structure sheaves is an isomorphism. -/
theorem bijective_ambientBaseChangeTensorFun
    (hc : IsIso (comparisonAbstract g NA NA' fmap)) :
    Function.Bijective (ambientBaseChangeTensorFun g NA NA' fmap) := by
  exact (bijective_ambientBaseChangeFunAbstract g NA NA' fmap hc).comp
    ⟨injective_ambientCrossAbstract g NA, surjective_ambientCrossAbstract g NA⟩

/-- **The normalisation of the base change of ambient sections**: `t ⊗ a` goes to `t` times the
`f`-map of `a`. -/
theorem ambientBaseChangeTensorFun_tmul (t : ringAlong g)
    (a : Γ(ambientSchemeOf A NA, (⊤ : A.thickening.target.scheme.Opens))) :
    ambientBaseChangeTensorFun g NA NA' fmap
        (t ⊗ₜ[Γ(A.thickening.target.scheme, ⊤)] a) =
      ambientRingSection A' (siteRingAlong g t) • fmapTopSection g NA NA' fmap a := by
  have hcross : ambientBaseChangeTensorFun g NA NA' fmap
        (t ⊗ₜ[Γ(A.thickening.target.scheme, ⊤)] a) =
      ambientComparisonAbstractTop g NA NA' fmap
        ((affineBaseChangeTopIsoAbstract g NA).hom
          (ambientRingSection A' (siteRingAlong g t) ⊗ₜ[
            Γ(A.thickening.target.scheme, (⊤ : A.thickening.target.scheme.Opens)),
            (g.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient g)).hom] a)) :=
    congrArg (fun w ↦ ambientComparisonAbstractTop g NA NA' fmap
      ((affineBaseChangeTopIsoAbstract g NA).hom w)) (ambientCrossAbstract_tmul g NA t a)
  have hcomp := congrArg (fun y ↦ ambientComparisonAbstractTop g NA NA' fmap y)
    (affineBaseChangeTopIsoAbstract_hom_tmul g NA
      (ambientRingSection A' (siteRingAlong g t)) a)
  exact (hcross.trans hcomp).trans
    (ambientComparisonAbstractTop_smul_ambientPullbackSectionTopModuleAbstract g NA NA' fmap
      (ambientRingSection A' (siteRingAlong g t)) a)

/-- **The base change of ambient sections carries `1 ⊗ a` to the `f`-map of `a`.** -/
theorem ambientBaseChangeTensorFun_one_tmul
    (a : Γ(ambientSchemeOf A NA, (⊤ : A.thickening.target.scheme.Opens))) :
    ambientBaseChangeTensorFun g NA NA' fmap
        ((1 : ringAlong g) ⊗ₜ[Γ(A.thickening.target.scheme, ⊤)] a) =
      fmapTopSection g NA NA' fmap a := by
  rw [ambientBaseChangeTensorFun_tmul]
  change (1 : Γ(A'.thickening.target.scheme, ⊤)) • fmapTopSection g NA NA' fmap a = _
  exact one_smul _ _

/-- **It carries zero to zero.**  Read at the pure tensor `0 ⊗ 0`, which is zero: that way the
zero of the tensor product never has to be elaborated at the carrier of
`ModuleCat.extendScalars`, where it is not reachable within the recursion budget. -/
theorem ambientBaseChangeTensorFun_zero :
    ambientBaseChangeTensorFun g NA NA' fmap
      (0 : ringAlong g ⊗[Γ(A.thickening.target.scheme, ⊤)] Γ(ambientSchemeOf A NA, ⊤)) = 0 := by
  refine (congrArg (fun z ↦ ambientBaseChangeTensorFun g NA NA' fmap z)
    (TensorProduct.zero_tmul (ringAlong g)
      (0 : Γ(ambientSchemeOf A NA, (⊤ : A.thickening.target.scheme.Opens)))).symm).trans ?_
  rw [ambientBaseChangeTensorFun_tmul]
  change (0 : Γ(A'.thickening.target.scheme, ⊤)) •
    fmapTopSection g NA NA' fmap
      (0 : Γ(ambientSchemeOf A NA, (⊤ : A.thickening.target.scheme.Opens))) = 0
  exact zero_smul _ _

/-- **The `f`-map on global sections kills `a` exactly when the pure tensor `1 ⊗ a` vanishes**,
on affine objects with quasi-coherent `N_T` and an invertible comparison map: the base change of
ambient sections is injective and carries `1 ⊗ a` to the `f`-map of `a`. -/
theorem fmapTopSection_eq_zero_iff_one_tmul_eq_zero
    (hc : IsIso (comparisonAbstract g NA NA' fmap))
    (a : Γ(ambientSchemeOf A NA, (⊤ : A.thickening.target.scheme.Opens))) :
    fmapTopSection g NA NA' fmap a = 0 ↔
      (1 : ringAlong g) ⊗ₜ[Γ(A.thickening.target.scheme, ⊤)] a = 0 := by
  rw [← ambientBaseChangeTensorFun_one_tmul g NA NA' fmap a]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (bijective_ambientBaseChangeTensorFun g NA NA' fmap hc).1
      (h.trans (ambientBaseChangeTensorFun_zero g NA NA' fmap).symm)
  · rw [h]
    exact ambientBaseChangeTensorFun_zero g NA NA' fmap

/-- **The kernel of the `f`-map on global sections is the subgroup of `α`-multiples**, when the
map on sections of the structure sheaves of the ambient schemes is surjective with kernel the
principal ideal `(α)`, the two ambient schemes are affine, `N_T` is quasi-coherent and the
comparison map of [Stacks, Tag 07IQ] is an isomorphism.

This is the kernel clause of the crystal property of [Stacks, Proposition 60.21.3, Tag 07LG], on
ambient sections and at an arbitrary morphism of the site: the sections over `T'` are the base
change of the sections over `T`, and the kernel of `x ↦ 1 ⊗ x` into a base change along a
surjection with principal kernel is the multiples of the generator, by
`TensorProduct.one_tmul_eq_zero_iff_exists_smul`. -/
theorem fmapTopSection_eq_zero_iff_exists_smul (hc : IsIso (comparisonAbstract g NA NA' fmap))
    (hsurj : Function.Surjective
      (g.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient g)).hom)
    (α : Γ(A.thickening.target.scheme, ⊤))
    (hker : ∀ b : Γ(A.thickening.target.scheme, ⊤),
      (g.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient g)).hom b = 0 ↔ α ∣ b)
    (a : Γ(ambientSchemeOf A NA, (⊤ : A.thickening.target.scheme.Opens))) :
    fmapTopSection g NA NA' fmap a = 0 ↔ ∃ b, a = α • b := by
  rw [fmapTopSection_eq_zero_iff_one_tmul_eq_zero g NA NA' fmap hc a]
  exact TensorProduct.one_tmul_eq_zero_iff_exists_smul (R' := ringAlong g)
    (g.targetHom.hom.appLE ⊤ ⊤ (top_le_preimage_ambient g)).hom (fun r t ↦ rfl) hsurj α hker a

end Affine

end Crystalline.GlobalCrystallineSituation

end

end
