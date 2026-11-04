module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorDeterminantTopPower
public import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.SupportedCoherentPerfectKGroup
public import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.SupportedPerfectCohomologyHom
import StacksCore.Tactic.StacksAttribute

/-!
# `K'_0(Z) = K_0(D_{Z, perf}(𝒪_X))` for a closed subscheme of a Noetherian regular scheme

Let `X` be a Noetherian regular scheme and `i : Z ⟶ X` a closed immersion. The homomorphism
`K'_0(Z) = K_0(Coh(𝒪_Z)) → K_0(D_{Z, perf}(𝒪_X))`, `[ℱ] ↦ [(i_*ℱ)[0]]`, of [Stacks, Tag 0FEQ] and
the homomorphism `K_0(D_{Z, perf}(𝒪_X)) → K'_0(Z)`,
`[E] ↦ [⊕_n H^{2n}(E)] - [⊕_n H^{2n+1}(E)]`, of [Stacks, Tag 0FEP] are mutually inverse.

## Main definitions

* `AlgebraicGeometry.supportedCoherentToSupportedPerfectHom`: the homomorphism
  `K_0(Coh_Z(X)) → K_0(D_{Z, perf}(𝒪_X))` placing a coherent module supported on `Z` in
  degree `0`.
* `AlgebraicGeometry.coherentKZeroEquivSupportedPerfectKZero`: the isomorphism
  `K'_0(Z) ≃+ K_0(D_{Z, perf}(𝒪_X))`.

## Main results

* `AlgebraicGeometry.supportedPerfectCohomologyHomToCoherent_comp_coherentToSupportedPerfectHom`:
  the composite `K'_0(Z) → K_0(D_{Z, perf}(𝒪_X)) → K'_0(Z)` is the identity.
* `AlgebraicGeometry.surjective_coherentToSupportedPerfectHom`: the first map is surjective.
* `AlgebraicGeometry.coherentToSupportedPerfectHom_mutuallyInverse`: **[Stacks, Tag 0FER]**.

## Implementation notes

The composite is the identity because `(i_*ℱ)[0]` has `i_*ℱ` as its only nonzero cohomology sheaf,
in degree `0`: the even sum is `i_*ℱ` and the odd sum is zero, and `K'_0(Z) → K_0(Coh_Z(X))` is
inverted by [Stacks, Tag 0FDT].

Surjectivity is the source's argument: by the truncation triangles every class of
`K_0(D_{Z, perf}(𝒪_X))` is a combination of classes of coherent `𝒪_X`-modules supported on `Z`
placed in degree `0`, which is the surjectivity in [Stacks, Tag 0FCS] of
`AlgebraicGeometry.supportedCoherentToPerfectHom`, and each such module is filtered by
`𝒪_Z`-modules, which is the surjectivity in [Stacks, Tag 0FDT]. The first statement is about
`Coh_Z(X)` spelled as `𝒪_X`-modules that are coherent and supported on `Z`, the second about
coherent modules supported on `Z`; `AlgebraicGeometry.supportedCoherentToSupportedPerfectHom` is
defined on the second spelling and its surjectivity is read off from the first on generators, so
no homomorphism between the two Grothendieck groups is formed.

## References

* [Stacks Project, Tag 0FER](https://stacks.math.columbia.edu/tag/0FER)
* [Stacks Project, Tag 0FEP](https://stacks.math.columbia.edu/tag/0FEP)
* [Stacks Project, Tag 0FEQ](https://stacks.math.columbia.edu/tag/0FEQ)
* [Stacks Project, Tag 0FDT](https://stacks.math.columbia.edu/tag/0FDT)
* [Stacks Project, Tag 0FCS](https://stacks.math.columbia.edu/tag/0FCS)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated StrictlyPerfect

universe u

namespace AlgebraicGeometry

open SupportedPerfectCohomology

attribute [local instance] HasDerivedCategory.standard

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsNoetherian X] (hX : IsRegular X)

/-- A coherent module supported on `Z`, viewed as an `𝒪_X`-module that is coherent and supported
on `Z`. -/
def supportedCoherentToCoherentSupported (G : SupportedCoherentModules i) :
    (coherentSupportedProperty i).FullSubcategory :=
  ⟨G.obj.obj, CoherentAbelian.isCoherent_of_stacksIsCoherent G.obj.property, G.property⟩

/-- An `𝒪_X`-module that is coherent and supported on `Z`, viewed as a coherent module supported
on `Z`. -/
def coherentSupportedToSupportedCoherent (G : (coherentSupportedProperty i).FullSubcategory) :
    SupportedCoherentModules i :=
  ⟨⟨G.obj, CoherentAbelian.stacksIsCoherent_of_isCoherent G.property.1⟩, G.property.2⟩

/-- The class of a coherent module supported on `Z`, placed in degree `0`, is additive along short
exact sequences: the inclusions of coherent modules supported on `Z` into coherent modules and of
coherent modules into all `𝒪_X`-modules are exact, so a short exact sequence gives a distinguished
triangle of the three modules placed in degree `0`. -/
theorem cls_singleSupportedPerfect_supportedCoherentToCoherentSupported_add
    (S : ShortComplex (SupportedCoherentModules i)) (hS : S.ShortExact) :
    Pretriangulated.K0.cls
        (singleSupportedPerfect i hX (supportedCoherentToCoherentSupported i S.X₂)) =
      Pretriangulated.K0.cls
          (singleSupportedPerfect i hX (supportedCoherentToCoherentSupported i S.X₁)) +
        Pretriangulated.K0.cls
          (singleSupportedPerfect i hX (supportedCoherentToCoherentSupported i S.X₃)) := by
  have := (supportedCoherentProperty i).preservesFiniteLimits_ι_of_isWeakSerreClass
  have := (supportedCoherentProperty i).preservesFiniteColimits_ι_of_isWeakSerreClass
  have := (Stacks.SheafOfModules.coherentModules
    X.ringCatSheaf).preservesFiniteLimits_ι_of_isWeakSerreClass
  have := (Stacks.SheafOfModules.coherentModules
    X.ringCatSheaf).preservesFiniteColimits_ι_of_isWeakSerreClass
  have h₁ := hS.map_of_exact (ObjectProperty.ι (supportedCoherentProperty i))
  have h₂ := h₁.map_of_exact
    (ObjectProperty.ι (Stacks.SheafOfModules.coherentModules X.ringCatSheaf))
  exact Pretriangulated.K0.cls_add_of_shortExact (C := OXMod.{u, u} X.toRingedSpace) h₂
    (singleSupportedPerfect i hX (supportedCoherentToCoherentSupported i S.X₁))
    (singleSupportedPerfect i hX (supportedCoherentToCoherentSupported i S.X₂))
    (singleSupportedPerfect i hX (supportedCoherentToCoherentSupported i S.X₃)) rfl rfl rfl

/-- **The homomorphism `K_0(Coh_Z(X)) → K_0(D_{Z, perf}(𝒪_X))`** sending the class of a coherent
module supported on `Z` to the class of that module placed in degree `0`. -/
def supportedCoherentToSupportedPerfectHom :
    KZero (SupportedCoherentModules i) →+ Pretriangulated.K0 (supportedPerfectDerivedCategory i) :=
  KZero.lift (fun G => Pretriangulated.K0.cls
      (singleSupportedPerfect i hX (supportedCoherentToCoherentSupported i G)))
    (cls_singleSupportedPerfect_supportedCoherentToCoherentSupported_add i hX)

/-- The homomorphism `K_0(Coh_Z(X)) → K_0(D_{Z, perf}(𝒪_X))` sends the class of a coherent module
supported on `Z` to the class of that module placed in degree `0`. -/
@[simp]
theorem supportedCoherentToSupportedPerfectHom_mk (G : SupportedCoherentModules i) :
    supportedCoherentToSupportedPerfectHom i hX (KZero.mk _ G) =
      Pretriangulated.K0.cls
        (singleSupportedPerfect i hX (supportedCoherentToCoherentSupported i G)) :=
  KZero.lift_mk _ _ _

/-- **The homomorphism `K_0(Coh_Z(X)) → K_0(D_{Z, perf}(𝒪_X))` is surjective.** Every class is a
combination of classes of coherent modules supported on `Z` placed in degree `0`, by the
surjectivity of `supportedCoherentToPerfectHom` ([Stacks, Tag 0FCS]). -/
theorem surjective_supportedCoherentToSupportedPerfectHom :
    Function.Surjective (supportedCoherentToSupportedPerfectHom i hX) := fun x => by
  obtain ⟨y, rfl⟩ := (bijective_supportedCoherentToPerfectHom i hX).2 x
  have h : QuotientAddGroup.mk' ((supportedCoherentToSupportedPerfectHom i hX).range.comap
      (supportedCoherentToPerfectHom i hX)) = 0 :=
    KZero.hom_ext fun G => (QuotientAddGroup.eq_zero_iff _).2 <| AddSubgroup.mem_comap.2 <|
      AddMonoidHom.mem_range.2 ⟨KZero.mk _ (coherentSupportedToSupportedCoherent i G),
        (show supportedCoherentToSupportedPerfectHom i hX
            (KZero.mk _ (coherentSupportedToSupportedCoherent i G)) =
              Pretriangulated.K0.cls (singleSupportedPerfect i hX G) from
          supportedCoherentToSupportedPerfectHom_mk i hX _).trans
        (show supportedCoherentToPerfectHom i hX (KZero.mk _ G) =
            Pretriangulated.K0.cls (singleSupportedPerfect i hX G) from
          supportedCoherentToPerfectHom_mk i hX G).symm⟩
  exact AddMonoidHom.mem_range.1 (AddSubgroup.mem_comap.1
    ((QuotientAddGroup.eq_zero_iff _).1 (DFunLike.congr_fun h y)))

/-- The odd cohomology sum `⊕_n H^{2n+1}((i_*ℱ)[0])` is zero: a complex concentrated in degree `0`
has no cohomology in odd degrees. -/
theorem isZero_oddHomologySupported_singlePushforwardSupportedPerfect
    (F : Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf) :
    IsZero (oddHomologySupported i (singlePushforwardSupportedPerfect i hX F)) := by
  refine IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι (supportedCoherentProperty i)) _ ?_
  refine IsZero.of_full_of_faithful_of_isZero
    (ObjectProperty.ι (Stacks.SheafOfModules.coherentModules X.ringCatSheaf)) _ ?_
  refine (IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ fun n => ?_)
  exact (DerivedCategory.isZero_homology_singleFunctor_obj (C := OXMod.{u, u} X.toRingedSpace)
    ((Scheme.Modules.pushforward i).obj F.obj) (n := 2 * n + 1) (by omega)).eq_of_src _ _

/-- The even cohomology sum `⊕_n H^{2n}((i_*ℱ)[0])` is `i_*ℱ`: its only nonzero summand is the
cohomology sheaf in degree `0`, which is `i_*ℱ`. -/
def evenHomologySupportedSinglePushforwardIso
    (F : Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf) :
    evenHomologySupported i (singlePushforwardSupportedPerfect i hX F) ≅
      (coherentToSupportedCoherent i).obj F := by
  refine (ObjectProperty.fullyFaithfulι (supportedCoherentProperty i)).preimageIso ?_
  refine (ObjectProperty.fullyFaithfulι
    (Stacks.SheafOfModules.coherentModules X.ringCatSheaf)).preimageIso ?_
  refine (sigmaIsoOfIsZero (fun n : ℤ =>
      (DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) (2 * n)).obj
        ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj
          ((Scheme.Modules.pushforward i).obj F.obj))) 0 fun n hn =>
      DerivedCategory.isZero_homology_singleFunctor_obj (C := OXMod.{u, u} X.toRingedSpace)
        ((Scheme.Modules.pushforward i).obj F.obj) (n := 2 * n) (by omega)).symm ≪≫ ?_
  exact (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (OXMod.{u, u} X.toRingedSpace) 0).app ((Scheme.Modules.pushforward i).obj F.obj)

/-- The homomorphism of [Stacks, Tag 0FEP] sends `[(i_*ℱ)[0]]` to the class of `i_*ℱ`. -/
theorem supportedPerfectCohomologyHom_coherentToSupportedPerfectHom_mk
    (F : Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf) :
    supportedPerfectCohomologyHom i (coherentToSupportedPerfectHom i hX (KZero.mk _ F)) =
      KZero.mk _ ((coherentToSupportedCoherent i).obj F) := by
  rw [coherentToSupportedPerfectHom_mk, supportedPerfectCohomologyHom_cls,
    KZero.mk_eq_zero_of_isZero
      (isZero_oddHomologySupported_singlePushforwardSupportedPerfect i hX F), sub_zero]
  exact KZero.mk_eq_of_iso (evenHomologySupportedSinglePushforwardIso i hX F)

/-- The composite `K'_0(Z) → K_0(D_{Z, perf}(𝒪_X)) → K_0(Coh_Z(X))` of the homomorphisms of
[Stacks, Tag 0FEQ] and [Stacks, Tag 0FEP] is the homomorphism of [Stacks, Tag 0FDT]. -/
theorem supportedPerfectCohomologyHom_comp_coherentToSupportedPerfectHom :
    (supportedPerfectCohomologyHom i).comp (coherentToSupportedPerfectHom i hX) =
      coherentToSupportedCoherentKZeroHom i :=
  KZero.hom_ext fun F => by
    rw [AddMonoidHom.comp_apply, supportedPerfectCohomologyHom_coherentToSupportedPerfectHom_mk,
      coherentToSupportedCoherentKZeroHom_mk]

/-- **The composite `K'_0(Z) → K_0(D_{Z, perf}(𝒪_X)) → K'_0(Z)` is the identity.** -/
theorem supportedPerfectCohomologyHomToCoherent_comp_coherentToSupportedPerfectHom :
    (supportedPerfectCohomologyHomToCoherent i).comp (coherentToSupportedPerfectHom i hX) =
      AddMonoidHom.id _ :=
  KZero.hom_ext fun F => (coherentToSupportedCoherentKZeroEquiv i).injective <| by
    rw [AddMonoidHom.comp_apply,
      coherentToSupportedCoherentKZeroEquiv_supportedPerfectCohomologyHomToCoherent,
      supportedPerfectCohomologyHom_coherentToSupportedPerfectHom_mk, AddMonoidHom.id_apply,
      coherentToSupportedCoherentKZeroEquiv_apply, coherentToSupportedCoherentKZeroHom_mk]

/-- The homomorphism `K'_0(Z) → K_0(D_{Z, perf}(𝒪_X))` of [Stacks, Tag 0FEQ] factors through
`K_0(Coh_Z(X))`: it is the homomorphism of [Stacks, Tag 0FDT] followed by the placement of a
coherent module supported on `Z` in degree `0`. -/
theorem coherentToSupportedPerfectHom_eq_comp :
    coherentToSupportedPerfectHom i hX =
      (supportedCoherentToSupportedPerfectHom i hX).comp (coherentToSupportedCoherentKZeroHom i) :=
  KZero.hom_ext fun F =>
    ((coherentToSupportedPerfectHom_mk i hX F).trans
      (supportedCoherentToSupportedPerfectHom_mk i hX
        ((coherentToSupportedCoherent i).obj F)).symm).trans
      ((congrArg (supportedCoherentToSupportedPerfectHom i hX)
        (coherentToSupportedCoherentKZeroHom_mk i F).symm).trans
          (AddMonoidHom.comp_apply _ _ _).symm)

/-- **The homomorphism `K'_0(Z) → K_0(D_{Z, perf}(𝒪_X))` of [Stacks, Tag 0FEQ] is surjective.**
It is the composite of the surjection `K'_0(Z) → K_0(Coh_Z(X))` of [Stacks, Tag 0FDT] with the
surjection `supportedCoherentToSupportedPerfectHom`. -/
theorem surjective_coherentToSupportedPerfectHom :
    Function.Surjective (coherentToSupportedPerfectHom i hX) := by
  intro x
  obtain ⟨w, rfl⟩ := surjective_supportedCoherentToSupportedPerfectHom i hX x
  obtain ⟨z, rfl⟩ := (coherentToSupportedCoherentKZeroHom_bijective i).2 w
  exact ⟨z, DFunLike.congr_fun (coherentToSupportedPerfectHom_eq_comp i hX) z⟩

/-- **Stacks Project, Tag 0FER.** Let `X` be a Noetherian regular scheme and `i : Z ⟶ X` a closed
immersion. The homomorphism `K'_0(Z) = K_0(Coh(𝒪_Z)) → K_0(D_{Z, perf}(𝒪_X))`,
`[ℱ] ↦ [(i_*ℱ)[0]]`, of [Stacks, Tag 0FEQ] and the homomorphism
`K_0(D_{Z, perf}(𝒪_X)) → K'_0(Z)`, `[E] ↦ [⊕_n H^{2n}(E)] - [⊕_n H^{2n+1}(E)]`, of
[Stacks, Tag 0FEP] are mutually inverse. -/
@[stacks 0FER]
theorem coherentToSupportedPerfectHom_mutuallyInverse :
    (supportedPerfectCohomologyHomToCoherent i).comp (coherentToSupportedPerfectHom i hX) =
        AddMonoidHom.id _ ∧
      (coherentToSupportedPerfectHom i hX).comp (supportedPerfectCohomologyHomToCoherent i) =
        AddMonoidHom.id _ := by
  have hl : Function.LeftInverse (supportedPerfectCohomologyHomToCoherent i)
      (coherentToSupportedPerfectHom i hX) := fun y => DFunLike.congr_fun
    (supportedPerfectCohomologyHomToCoherent_comp_coherentToSupportedPerfectHom i hX) y
  exact ⟨supportedPerfectCohomologyHomToCoherent_comp_coherentToSupportedPerfectHom i hX,
    AddMonoidHom.ext
      (hl.rightInverse_of_surjective (surjective_coherentToSupportedPerfectHom i hX))⟩

/-- **Stacks Project, Tag 0FER**, as an isomorphism: `K'_0(Z) ≃+ K_0(D_{Z, perf}(𝒪_X))` for a
closed subscheme `Z` of a Noetherian regular scheme `X`, given by the mutually inverse
homomorphisms of [Stacks, Tag 0FEQ] and [Stacks, Tag 0FEP]. -/
@[stacks 0FER "the resulting identification K'_0(Z) = K_0(D_{Z, perf}(O_X))"]
def coherentKZeroEquivSupportedPerfectKZero :
    KZero (Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf) ≃+
      Pretriangulated.K0 (supportedPerfectDerivedCategory i) where
  toFun := coherentToSupportedPerfectHom i hX
  invFun := supportedPerfectCohomologyHomToCoherent i
  left_inv x := DFunLike.congr_fun
    (coherentToSupportedPerfectHom_mutuallyInverse i hX).1 x
  right_inv x := DFunLike.congr_fun
    (coherentToSupportedPerfectHom_mutuallyInverse i hX).2 x
  map_add' := map_add _

/-- The isomorphism `coherentKZeroEquivSupportedPerfectKZero` sends a class `x` in `K'_0(Z)` to
`coherentToSupportedPerfectHom i hX x`. -/
@[simp]
theorem coherentKZeroEquivSupportedPerfectKZero_apply
    (x : KZero (Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf)) :
    coherentKZeroEquivSupportedPerfectKZero i hX x = coherentToSupportedPerfectHom i hX x :=
  rfl

/-- The inverse of `coherentKZeroEquivSupportedPerfectKZero` sends a class `x` in
`K_0(D_{Z, perf}(𝒪_X))` to `supportedPerfectCohomologyHomToCoherent i x`. -/
@[simp]
theorem coherentKZeroEquivSupportedPerfectKZero_symm_apply
    (x : Pretriangulated.K0 (supportedPerfectDerivedCategory i)) :
    (coherentKZeroEquivSupportedPerfectKZero i hX).symm x =
      supportedPerfectCohomologyHomToCoherent i x :=
  rfl

end AlgebraicGeometry

end
