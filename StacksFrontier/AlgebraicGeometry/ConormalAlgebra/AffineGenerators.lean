module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AffineIdentification
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.GradedPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalSheaf

/-!
# The affine generators of the conormal sheaf of a closed subscheme

For an effective-Cartier-shaped closed subscheme `D ⊆ X` and an affine open `U ⊆ X` presenting
`D ∩ U` as `Spec (Γ(X, U) ⧸ I)`, Tag 0B3P asks for the *normalisation* of the two
identifications it asserts: the affine computation of the conormal sheaf
(`Stacks.Conormal.affineConormalIsoCotangent`, Tag 01R3 (2)) must send the pulled-back ideal
section determined by `s ∈ ℐ_D(U)` to the class of `s` modulo `I²`.

This file proves that, and the sectionwise lemmas about the module pullback that it needs.

## Main results

* `Stacks.Divisors.conormalSheafIsoNegativeTwist_apply`: **Tag 0B3P**, the canonical-ideal-quotient
  clause. On an affine open carrying an affine model of `D ∩ U`, the affine conormal
  identification sends the image of `s ∈ ℐ_D(U)` under the adjunction unit and
  `Stacks.Divisors.conormalSheafIsoNegativeTwist` to `I.toCotangent s`.
* `Stacks.Conormal.factoredAffineConormalIsoCotangent_pullbackIdealSheafIso_unit`: the same
  statement for an immersion presented with an arbitrary closed-immersion factorization through
  an open subscheme.
* `Stacks.Conormal.affineIdealPullbackIsoCotangent_hom_pullbackSection`: the affine computation of
  the sections of the pullback of an ideal sheaf sends the pullback of a section of the ideal
  sheaf to its class modulo the square of the ideal.
* `Stacks.Conormal.affineConormalIsoCotangent_hom_pullbackSection` and
  `Stacks.Conormal.factoredAffineConormalIsoCotangent_hom_pullbackSection`: **Tag 01R3 (2)** on
  generators, in the `Stacks.Conormal.pullbackSection` form — a section of the ideal sheaf of the
  closed factorization lying over an ideal generator `b ∈ I` is sent to the class of `b` modulo
  `I²`. The second does not need the open immersion of the factorization to be an isomorphism of
  ringed spaces.
* `Stacks.Conormal.exists_idealSection_of_ker`: a section of `𝒪_X` over `U` killed by the
  immersion gives a section of the ideal sheaf of `i.liftCoborder` over
  `i.coborderRange.ι ⁻¹ᵁ U`.
* `Stacks.Conormal.kernelι_val_app_injective`: a section of the ideal sheaf of a closed immersion
  is determined by its image in the structure sheaf, and
  `Stacks.Conormal.pullbackSection_restrict_target`,
  `Stacks.Conormal.pullbackSection_restrict_source` move a pulled-back section between opens.
* `Stacks.Conormal.cotangentComapIso_hom_toCotangent` and `cotangentComapIso_inv_toCotangent`: the
  transport of `Ideal.Cotangent` along a ring isomorphism sends generators to generators.
* `Stacks.ClosedImmersion.pullbackIdealSheafIsoComp_hom_unit`: `(a ≫ b)^* ℐ_{a ≫ b} ≅ a^* ℐ_a`
  for an isomorphism `b` carries the pullback of a section of `ℐ_{a ≫ b}` to the pullback of the
  corresponding section of `ℐ_a`, and
  `Stacks.ClosedImmersion.kernelι_idealSheafPushforwardIso_hom` identifies those two sections
  inside the structure sheaf.
* `Stacks.RingedSpace.unit_val_app_naturality`,
  `Stacks.RingedSpace.modulePullbackComp_inv_unit` and
  `Stacks.RingedSpace.pullbackPushforwardObjIso_hom_unit`: the three sectionwise facts about the
  unit of `f^* ⊣ f_*` for a morphism of ringed spaces — naturality, compatibility with
  pseudofunctoriality, and the triangle identity.

## Implementation notes

**Why the statement is proved at the factored form first.**
`Stacks.Conormal.affineConormalIsoCotangent` is built from
`Stacks.Conormal.factoredAffineConormalIsoCotangent` at the canonical factorization
`i.liftCoborder ≫ i.coborderRange.ι = i`, whose body substitutes that equation; and
`Stacks.Divisors.conormalSheafIsoNegativeTwist` is
`Stacks.ClosedImmersion.pullbackIdealSheafIso` at the same equation, whose body substitutes it
too. Neither substitution can be performed at `i = D.subschemeι`, because the factorization is
*constructed from* `i`, so `i` is not a variable. At the factored form the factorization and the
immersion are independent binders, the substitution is legal, and both definitions reduce to
their explicit composites. The two uses of the equation are then discharged by one `subst`, and
proof irrelevance identifies the two proofs of it.

**The transport inside the affine computation.**
`Stacks.Conormal.affineIdealPullbackIsoCotangent` is defined by rewriting
`Scheme.Hom.appLE_preimage_self` in the base-change isomorphism
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`, which leaves an `Eq.mp` transport on it.
That transport cannot be removed after the fact: the element `1 ⊗ₜ a` whose image the
normalisation lemma `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_one_tmul` computes has
a *type* mentioning the ring map, so rewriting the map in that lemma asks for a motive that is
not type correct. `eq_mp_iso_hom_one_tmul` is the transport stated with the two ring maps as
variables, where `subst` applies and the `Eq.mp` disappears by proof irrelevance; everything else
is read off it.

**Spelling.** The module sheaf argument of the base-change isomorphism is kept as a variable
`F : X.Modules` throughout, because the instance `Module Γ(X, U) Γ(F, U)` is not found when `F`
is written out as a kernel. For the same reason the sections of the affine computation are
reached through `AlgebraicGeometry.Scheme.Modules.pullbackSection` rather than through the unit
of the adjunction directly, the two being identified by
`Stacks.Conormal.pullbackSection_self`.

## References

* [Stacks Project, Tag 0B3P](https://stacks.math.columbia.edu/tag/0B3P)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction Opposite
open TopologicalSpace
open scoped TensorProduct ChangeOfRings

universe u

namespace Stacks.RingedSpace

variable {Z W X : RingedSpace.{u, u}} (a : Z ⟶ W) (b : W ⟶ X)

/-- **Naturality of the unit of `f^* ⊣ f_*` on sections.** -/
theorem unit_val_app_naturality {F G : SheafOfModules.{u} (structureSheafRing W)} (t : F ⟶ G)
    (U : Opens W.carrier) (s : F.val.obj (op U)) :
    ((modulePullback a).map t).val.app (op ((opensMap a).obj U))
        (((modulePullbackPushforwardAdjunction a).unit.app F).val.app (op U) s) =
      ((modulePullbackPushforwardAdjunction a).unit.app G).val.app (op U)
        (t.val.app (op U) s) :=
  (congrArg (fun q : F ⟶ (modulePushforward a).obj ((modulePullback a).obj G) =>
      q.val.app (op U) s)
    ((modulePullbackPushforwardAdjunction a).unit.naturality t)).symm

/-- **Pseudofunctoriality of the pullback, on a pulled-back section.** The comparison
`(a ≫ b)^* ⟶ a^* ∘ b^*` carries the unit of `a ≫ b` to the composite of the two units. -/
theorem modulePullbackComp_inv_unit (N : SheafOfModules.{u} (structureSheafRing X))
    (U : Opens X.carrier) (s : N.val.obj (op U)) :
    ((modulePullbackComp a b).inv.app N).val.app (op ((opensMap (a ≫ b)).obj U))
        (((modulePullbackPushforwardAdjunction (a ≫ b)).unit.app N).val.app (op U) s) =
      ((modulePullbackPushforwardAdjunction a).unit.app
        ((modulePullback b).obj N)).val.app (op ((opensMap b).obj U))
          (((modulePullbackPushforwardAdjunction b).unit.app N).val.app (op U) s) := by
  have _ha : (SheafOfModules.pushforward (structureSheafHom a)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint a
  have _hb : (SheafOfModules.pushforward (structureSheafHom b)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint b
  have key : CategoryTheory.conjugateEquiv
      ((modulePullbackPushforwardAdjunction b).comp (modulePullbackPushforwardAdjunction a))
      (modulePullbackPushforwardAdjunction (a ≫ b)) (modulePullbackComp a b).inv =
        (SheafOfModules.pushforwardComp (structureSheafHom b) (structureSheafHom a)).hom :=
    SheafOfModules.conjugateEquiv_pullbackComp_inv _ _
  have h := CategoryTheory.unit_conjugateEquiv
    ((modulePullbackPushforwardAdjunction b).comp (modulePullbackPushforwardAdjunction a))
    (modulePullbackPushforwardAdjunction (a ≫ b)) (modulePullbackComp a b).inv N
  rw [key] at h
  exact (congrArg (fun t => t.val.app (op U) s) h).symm

/-- **The triangle identity on sections**, for an isomorphism `b` of ringed spaces: the counit
`b^* (b_* N) ≅ N` undoes the unit of `b^* ⊣ b_*` at `b_* N`. -/
theorem pullbackPushforwardObjIso_hom_unit [IsIso b] (N : SheafOfModules.{u} (structureSheafRing W))
    (U : Opens X.carrier) (t : ((modulePushforward b).obj N).val.obj (op U)) :
    (pullbackPushforwardObjIso b N).hom.val.app (op ((opensMap b).obj U))
        (((modulePullbackPushforwardAdjunction b).unit.app
          ((modulePushforward b).obj N)).val.app (op U) t) = t :=
  congrArg (fun q => q.val.app (op U) t)
    ((modulePullbackPushforwardAdjunction b).right_triangle_components N)

end Stacks.RingedSpace

namespace Stacks.ClosedImmersion

open Stacks.RingedSpace

variable {Z W X : RingedSpace.{u, u}} (a : Z ⟶ W) (b : W ⟶ X)

/-- **The pushforward identification of ideal sheaves is compatible with their inclusions into
the structure sheaf.** For `b` an isomorphism, `ℐ_{a ≫ b} ≅ b_* ℐ_a` followed by the inclusion of
`ℐ_a` is the inclusion of `ℐ_{a ≫ b}` followed by `𝒪_X ⟶ b_* 𝒪_W`. -/
theorem kernelι_comp_idealSheafPushforwardIso_hom [IsIso b] :
    (idealSheafPushforwardIso a b).hom ≫
        (modulePushforward b).map (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom a))) =
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom (a ≫ b))) ≫
        SheafOfModules.unitToPushforwardObjUnit (structureSheafHom b) := by
  have _he : (modulePushforward b).IsEquivalence := isEquivalence_modulePushforward b
  change ((kernelIsIsoComp (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom b))
        ((modulePushforward b).map (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom a)))).hom ≫
      (PreservesKernel.iso (modulePushforward b)
        (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom a))).inv) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => (kernelIsIsoComp (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom b))
        ((modulePushforward b).map (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom a)))).hom ≫ q)
      (PreservesKernel.iso_inv_ι (modulePushforward b)
        (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom a)))).trans
      (kernel.lift_ι _ _ _))

/-- `kernelι_comp_idealSheafPushforwardIso_hom` read on sections over an open of the target. -/
theorem kernelι_idealSheafPushforwardIso_hom [IsIso b] (U : Opens X.carrier)
    (x : (idealSheaf (a ≫ b)).val.obj (op U)) :
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom a))).val.app (op ((opensMap b).obj U))
        ((idealSheafPushforwardIso a b).hom.val.app (op U) x) =
      (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom b)).val.app (op U)
        ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom (a ≫ b)))).val.app (op U) x) :=
  congrArg (fun q => q.val.app (op U) x) (kernelι_comp_idealSheafPushforwardIso_hom a b)

/-- **The comparison `(a ≫ b)^* ℐ_{a ≫ b} ≅ a^* ℐ_a` on a pulled-back section.** It carries the
image of `x ∈ ℐ_{a ≫ b}(U)` under the unit of `(a ≫ b)^* ⊣ (a ≫ b)_*` to the image of the
corresponding section of `ℐ_a` over `b⁻¹U` under the unit of `a^* ⊣ a_*`. -/
theorem pullbackIdealSheafIsoComp_hom_unit [IsIso b] (U : Opens X.carrier)
    (x : (idealSheaf (a ≫ b)).val.obj (op U)) :
    (pullbackIdealSheafIsoComp a b).hom.val.app (op ((opensMap (a ≫ b)).obj U))
        (((modulePullbackPushforwardAdjunction (a ≫ b)).unit.app
          (idealSheaf (a ≫ b))).val.app (op U) x) =
      ((modulePullbackPushforwardAdjunction a).unit.app (idealSheaf a)).val.app
        (op ((opensMap b).obj U))
        ((idealSheafPushforwardIso a b).hom.val.app (op U) x) := by
  change ((modulePullback a).map (pullbackPushforwardObjIso b (idealSheaf a)).hom).val.app
        (op ((opensMap (a ≫ b)).obj U))
      ((((modulePullbackComp a b).inv.app
          ((modulePushforward b).obj (idealSheaf a))).val.app
            (op ((opensMap (a ≫ b)).obj U)))
        (((modulePullback (a ≫ b)).map (idealSheafPushforwardIso a b).hom).val.app
            (op ((opensMap (a ≫ b)).obj U))
          (((modulePullbackPushforwardAdjunction (a ≫ b)).unit.app
            (idealSheaf (a ≫ b))).val.app (op U) x))) = _
  rw [unit_val_app_naturality (a ≫ b) (idealSheafPushforwardIso a b).hom U x,
    modulePullbackComp_inv_unit a b ((modulePushforward b).obj (idealSheaf a)) U
      ((idealSheafPushforwardIso a b).hom.val.app (op U) x)]
  refine (unit_val_app_naturality a (pullbackPushforwardObjIso b (idealSheaf a)).hom
    ((opensMap b).obj U) _).trans ?_
  rw [pullbackPushforwardObjIso_hom_unit b (idealSheaf a) U]

end Stacks.ClosedImmersion

namespace Stacks.Conormal

/-- The transport of an isomorphism out of an extension of scalars along an equality of the ring
map, read on `1 ⊗ₜ m`. -/
private theorem eq_mp_iso_hom_one_tmul {R S : CommRingCat.{u}} {φ ψ : R ⟶ S} (hφψ : φ = ψ)
    {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (pf : ((ModuleCat.extendScalars φ.hom).obj M ≅ N) =
          ((ModuleCat.extendScalars ψ.hom).obj M ≅ N))
    (e : (ModuleCat.extendScalars φ.hom).obj M ≅ N) (m : M) :
    (pf.mp e).hom.hom ((1 : S) ⊗ₜ[R, ψ.hom] m) = e.hom.hom ((1 : S) ⊗ₜ[R, φ.hom] m) := by
  subst hφψ; rfl

/-- The transported base-change isomorphism carries the pullback of a section back to `1 ⊗ₜ` that
section. -/
private theorem eq_mp_baseChangeIso_inv_pullbackSection {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen (f ⁻¹ᵁ U))
    (pf : ((ModuleCat.extendScalars (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom).obj
            (ModuleCat.of Γ(X, U) Γ(F, U)) ≅
          ModuleCat.of Γ(Y, f ⁻¹ᵁ U) Γ((Scheme.Modules.pullback f).obj F, f ⁻¹ᵁ U)) =
          ((ModuleCat.extendScalars (f.app U).hom).obj
            (ModuleCat.of Γ(X, U) Γ(F, U)) ≅
          ModuleCat.of Γ(Y, f ⁻¹ᵁ U) Γ((Scheme.Modules.pullback f).obj F, f ⁻¹ᵁ U)))
    (a : Γ(F, U)) :
    (pf.mp (AlgebraicGeometry.affinePullbackSectionsBaseChangeIso f F hU hV
          (le_refl (f ⁻¹ᵁ U)))).inv.hom
        (Scheme.Modules.pullbackSection f F U (f ⁻¹ᵁ U) le_rfl a)
      = (1 : Γ(Y, f ⁻¹ᵁ U)) ⊗ₜ[Γ(X, U), (f.app U).hom] a := by
  refine (congrArg _ (AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_one_tmul f F hU hV
    (le_refl (f ⁻¹ᵁ U)) a).symm).trans ?_
  rw [← eq_mp_iso_hom_one_tmul (Scheme.Hom.appLE_preimage_self f U) pf _ a]
  exact ConcreteCategory.congr_hom
    (pf.mp (AlgebraicGeometry.affinePullbackSectionsBaseChangeIso f F hU hV
      (le_refl (f ⁻¹ᵁ U)))).hom_inv_id _

/-- The composite defining `Stacks.Conormal.affineIdealPullbackIsoCotangent`, for an arbitrary
base-change isomorphism `bc`, sends a section `t` with `bc⁻¹ t = 1 ⊗ y` to the class of `y`. -/
private theorem affineIdealPullbackIsoCotangent_aux {Z C : Scheme.{u}} (a : Z ⟶ C)
    (W : C.Opens) (F : C.Modules)
    (hsurj : Function.Surjective (a.app W).hom)
    (bc : (ModuleCat.extendScalars (a.app W).hom).obj (ModuleCat.of Γ(C, W) Γ(F, W)) ≅
      ModuleCat.of Γ(Z, a ⁻¹ᵁ W) Γ((Scheme.Modules.pullback a).obj F, a ⁻¹ᵁ W))
    (sec : ModuleCat.of Γ(C, W) Γ(F, W) ≅
      ModuleCat.of Γ(C, W) (RingHom.ker (a.app W).hom))
    (t : Γ((Scheme.Modules.pullback a).obj F, a ⁻¹ᵁ W)) (y : Γ(F, W))
    (hbc : bc.inv.hom t = (1 : Γ(Z, a ⁻¹ᵁ W)) ⊗ₜ[Γ(C, W), (a.app W).hom] y) :
    letI : Algebra Γ(C, W) Γ(Z, a ⁻¹ᵁ W) := (a.app W).hom.toAlgebra
    ((ModuleCat.restrictScalars (a.app W).hom).mapIso
          (bc.symm ≪≫ (ModuleCat.extendScalars (a.app W).hom).mapIso sec) ≪≫
        (Stacks.Conormal.surjectiveTensorEquivQuotSMul hsurj
          (RingHom.ker (a.app W).hom)).toModuleIso).hom.hom t
      = (RingHom.ker (a.app W).hom).toCotangent (sec.hom.hom y) := by
  let : Algebra Γ(C, W) Γ(Z, a ⁻¹ᵁ W) := (a.app W).hom.toAlgebra
  change (Stacks.Conormal.surjectiveTensorEquivQuotSMul hsurj _)
      (((ModuleCat.extendScalars (a.app W).hom).map sec.hom).hom (bc.inv.hom t)) = _
  rw [hbc]
  exact Stacks.Conormal.surjectiveTensorEquivQuotSMul_one_tmul hsurj _

/-- **The affine computation of the sections of the pullback of an ideal sheaf, on generators.**
It sends the pullback of a section `y` of `ℐ_a` over an affine open `W` with affine preimage and
surjective map on functions to the class of `y` modulo the square of `ker (a.app W)`. -/
theorem affineIdealPullbackIsoCotangent_hom_pullbackSection {Z C : Scheme.{u}} (a : Z ⟶ C)
    (W : C.Opens) [IsClosedImmersion a]
    (hW : IsAffineOpen W) (hV : IsAffineOpen (a ⁻¹ᵁ W))
    (hsurj : Function.Surjective (a.app W).hom)
    (y : (Stacks.ClosedImmersion.idealSheaf a.toLRSHom.toShHom).val.obj (op W)) :
    (affineIdealPullbackIsoCotangent a W hW hV hsurj).hom.hom
        (Scheme.Modules.pullbackSection a
          (Stacks.ClosedImmersion.idealSheaf a.toLRSHom.toShHom) W (a ⁻¹ᵁ W) le_rfl y)
      = (RingHom.ker (a.app W).hom).toCotangent
          ((idealSheafSectionsIso a W).hom.hom y) := by
  simp only [affineIdealPullbackIsoCotangent]
  exact affineIdealPullbackIsoCotangent_aux a W
    (Stacks.ClosedImmersion.idealSheaf a.toLRSHom.toShHom) hsurj _
    (idealSheafSectionsIso a W) _ y
    (eq_mp_baseChangeIso_inv_pullbackSection a
      (Stacks.ClosedImmersion.idealSheaf a.toLRSHom.toShHom) hW hV _ y)

/-- The sections of the ideal sheaf sit inside the sections of the structure sheaf by the
inclusion of the kernel. -/
theorem idealSheafSectionsIso_hom_coe {Z C : Scheme.{u}} (a : Z ⟶ C) (W : C.Opens)
    (y : (Stacks.ClosedImmersion.idealSheaf a.toLRSHom.toShHom).val.obj (op W)) :
    (((idealSheafSectionsIso a W).hom.hom y : RingHom.ker (a.app W).hom) : Γ(C, W)) =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom a.toLRSHom.toShHom))).val.app (op W) y :=
  rfl

/-- **A section of the ideal sheaf of a closed immersion is determined by its image in the
structure sheaf.** -/
theorem kernelι_val_app_injective {Z C : Scheme.{u}} (a : Z ⟶ C) (W : C.Opens) :
    Function.Injective fun y : (Stacks.ClosedImmersion.idealSheaf a.toLRSHom.toShHom).val.obj
        (op W) =>
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom a.toLRSHom.toShHom))).val.app (op W) y := by
  intro y z hyz
  have h : (idealSheafSectionsIso a W).hom.hom y = (idealSheafSectionsIso a W).hom.hom z :=
    Subtype.ext (by rwa [idealSheafSectionsIso_hom_coe a W y, idealSheafSectionsIso_hom_coe a W z])
  exact ((idealSheafSectionsIso a W).hom_inv_id_apply y).symm.trans
    ((congrArg (fun t => (idealSheafSectionsIso a W).inv.hom t) h).trans
      ((idealSheafSectionsIso a W).hom_inv_id_apply z))

/-! ### Moving a pulled-back section between opens -/

/-- Restricting a pulled-back section to a smaller open of the source is pulling it back to that
open. -/
theorem pullbackSection_restrict_target {Z C : Scheme.{u}} (a : Z ⟶ C) (F : C.Modules)
    (U : C.Opens) (V V' : Z.Opens) (h : V ≤ a ⁻¹ᵁ U) (h' : V' ≤ V) (s : Γ(F, U)) :
    ((Scheme.Modules.pullback a).obj F).val.map (homOfLE h').op
        (Scheme.Modules.pullbackSection a F U V h s)
      = Scheme.Modules.pullbackSection a F U V' (h'.trans h) s :=
  (PresheafOfModules.map_comp_apply (((Scheme.Modules.pullback a).obj F).val)
    (homOfLE h).op (homOfLE h').op _).symm

/-- Pulling back a section is compatible with restricting it on the target first. -/
theorem pullbackSection_restrict_source {Z C : Scheme.{u}} (a : Z ⟶ C) (F : C.Modules)
    (U U' : C.Opens) (hU : U' ≤ U) (V : Z.Opens) (h : V ≤ a ⁻¹ᵁ U') (s : Γ(F, U)) :
    Scheme.Modules.pullbackSection a F U V (h.trans (a.preimage_mono hU)) s
      = Scheme.Modules.pullbackSection a F U' V h (F.val.map (homOfLE hU).op s) := by
  unfold Scheme.Modules.pullbackSection
  have hn := PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app F).val (homOfLE hU).op s
  dsimp only [Functor.id_obj] at hn
  rw [hn]
  exact PresheafOfModules.map_comp_apply (((Scheme.Modules.pullback a).obj F).val)
    ((Opens.map a.base).map (homOfLE hU)).op (homOfLE h).op _

/-- `Stacks.Conormal.cotangentComapIso` sends the class of a section to the class of its
image. -/
theorem cotangentComapIso_hom_toCotangent {R R' : CommRingCat.{u}} (α : R ≅ R') (K : Ideal R')
    (z : K.comap α.hom.hom) :
    (cotangentComapIso α K).hom.hom ((K.comap α.hom.hom).toCotangent z)
      = K.toCotangent ⟨α.hom.hom z, z.2⟩ := rfl

/-- The inverse of `Stacks.Conormal.cotangentComapIso` on generators: it sends the class of
`α z` to the class of `z`. -/
theorem cotangentComapIso_inv_toCotangent {R R' : CommRingCat.{u}} (α : R ≅ R') (K : Ideal R')
    (z : K.comap α.hom.hom) :
    (cotangentComapIso α K).inv.hom (K.toCotangent ⟨α.hom.hom z, z.2⟩)
      = (K.comap α.hom.hom).toCotangent z := by
  rw [← cotangentComapIso_hom_toCotangent]
  exact ConcreteCategory.congr_hom (cotangentComapIso α K).hom_inv_id _

/-- The image of a section of the structure sheaf of `X` in the structure sheaf of an open
subscheme, read through the unit comparison of the module pushforward. -/
theorem unitToPushforwardObjUnit_val_app {Z X : Scheme.{u}} (b : Z ⟶ X) (U : X.Opens)
    (z : Γ(X, U)) :
    (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom b.toLRSHom.toShHom)).val.app (op U) z = (b.app U).hom z :=
  rfl

/-- `Stacks.Conormal.factoredAffineConormalIsoCotangent_hom_pullbackSection` at the composite
factorization. -/
private theorem factoredAffineConormalIsoCotangent_hom_pullbackSection_comp
    {Z X : Scheme.{u}} (C : X.Opens) (a : Z ⟶ C.toScheme) [IsClosedImmersion a]
    (U : X.Opens) (hUC : U ≤ C) (hU : IsAffineOpen U)
    (I : Ideal Γ(X, U)) (hV : IsAffineOpen ((a ≫ C.ι) ⁻¹ᵁ U))
    (hker : RingHom.ker ((a ≫ C.ι).app U).hom = I)
    (hsurj : Function.Surjective ((a ≫ C.ι).app U).hom)
    (hle : (a ≫ C.ι) ⁻¹ᵁ U ≤ a ⁻¹ᵁ (C.ι ⁻¹ᵁ U))
    (b : I) (x : (Stacks.ClosedImmersion.idealSheaf a.toLRSHom.toShHom).val.obj (op (C.ι ⁻¹ᵁ U)))
    (hx : (C.ι.app U).hom (b : Γ(X, U)) =
      ((idealSheafSectionsIso a (C.ι ⁻¹ᵁ U)).hom.hom x : Γ(C.toScheme, C.ι ⁻¹ᵁ U))) :
    (factoredAffineConormalIsoCotangent C a (a ≫ C.ι) rfl U hUC hU I hV hker hsurj).hom.hom
        (Scheme.Modules.pullbackSection a
          (Stacks.ClosedImmersion.idealSheaf a.toLRSHom.toShHom)
          (C.ι ⁻¹ᵁ U) ((a ≫ C.ι) ⁻¹ᵁ U) hle x)
      = I.toCotangent b := by
  have hιiso : IsIso (C.ι.app U) := C.ι.isIso_app U (by simpa using hUC)
  have hW : IsAffineOpen (C.ι ⁻¹ᵁ U) := hU.preimage_of_isOpenImmersion _ (by simpa using hUC)
  have hsurj' : Function.Surjective (a.app (C.ι ⁻¹ᵁ U)).hom :=
    Function.Surjective.of_comp (g := (C.ι.app U).hom) hsurj
  have hkerI : Ideal.comap (C.ι.app U).hom (RingHom.ker (a.app (C.ι ⁻¹ᵁ U)).hom) = I := by
    rw [RingHom.comap_ker, ← hker]; rfl
  have hmem : ((C.ι.app U).hom (b : Γ(X, U))) ∈ RingHom.ker (a.app (C.ι ⁻¹ᵁ U)).hom := by
    rw [hx]; exact ((idealSheafSectionsIso a (C.ι ⁻¹ᵁ U)).hom.hom x).2
  have hbmem : (b : Γ(X, U)) ∈ Ideal.comap (C.ι.app U).hom
      (RingHom.ker (a.app (C.ι ⁻¹ᵁ U)).hom) := hmem
  rw [show factoredAffineConormalIsoCotangent C a (a ≫ C.ι) rfl U hUC hU I hV hker hsurj
      = (pushforwardCompSectionsIso C a (a ≫ C.ι) rfl U
            ((modulePullback a.toLRSHom.toShHom).obj
              (Stacks.ClosedImmersion.idealSheaf a.toLRSHom.toShHom)) ≪≫
          (ModuleCat.restrictScalars (C.ι.app U).hom).mapIso
            (affineIdealPullbackIsoCotangent a (C.ι ⁻¹ᵁ U) hW hV hsurj') ≪≫
          (cotangentComapIso (asIso (C.ι.app U))
            (RingHom.ker (a.app (C.ι ⁻¹ᵁ U)).hom)).symm ≪≫
          (Ideal.Cotangent.equivOfEq _ I hkerI).toModuleIso) from rfl]
  change (Ideal.Cotangent.equivOfEq _ I hkerI)
      ((cotangentComapIso (asIso (C.ι.app U))
          (RingHom.ker (a.app (C.ι ⁻¹ᵁ U)).hom)).inv.hom
        ((affineIdealPullbackIsoCotangent a (C.ι ⁻¹ᵁ U) hW hV hsurj').hom.hom
          (Scheme.Modules.pullbackSection a
            (Stacks.ClosedImmersion.idealSheaf a.toLRSHom.toShHom)
            (C.ι ⁻¹ᵁ U) (a ⁻¹ᵁ (C.ι ⁻¹ᵁ U)) le_rfl x))) = _
  rw [affineIdealPullbackIsoCotangent_hom_pullbackSection a (C.ι ⁻¹ᵁ U) hW hV hsurj' x,
    show ((idealSheafSectionsIso a (C.ι ⁻¹ᵁ U)).hom.hom x)
      = ⟨(asIso (C.ι.app U)).hom.hom (⟨(b : Γ(X, U)), hbmem⟩ :
          ↥(Ideal.comap (C.ι.app U).hom (RingHom.ker (a.app (C.ι ⁻¹ᵁ U)).hom))), hmem⟩
      from Subtype.ext hx.symm,
    cotangentComapIso_inv_toCotangent (asIso (C.ι.app U))
      (RingHom.ker (a.app (C.ι ⁻¹ᵁ U)).hom) ⟨(b : Γ(X, U)), hbmem⟩]
  change (Ideal.Cotangent.equivOfEq _ I hkerI)
      ((Ideal.comap (C.ι.app U).hom (RingHom.ker (a.app (C.ι ⁻¹ᵁ U)).hom)).toCotangent
        ⟨(b : Γ(X, U)), hbmem⟩) = _
  rw [Ideal.Cotangent.equivOfEq_toCotangent]
  rfl

/-- **Tag 0B3P's canonical-ideal-quotient clause at the factored form.**

Let `i : Z ⟶ X` be an immersion presented as a closed immersion `a` into an open subscheme `C`
whose open immersion is an isomorphism of ringed spaces, and let `U ⊆ C` be an affine open with
`ker (i.app U) = I` and `i.app U` surjective. Then the affine computation of the conormal sheaf
sends the image of `x ∈ ℐ_i(U)` under the unit of `i^* ⊣ i_*` and the comparison
`i^* ℐ_i ≅ a^* ℐ_a` to the class of `x` modulo `I²`. -/
theorem factoredAffineConormalIsoCotangent_pullbackIdealSheafIso_unit
    {Z X : Scheme.{u}} (C : X.Opens) (a : Z ⟶ C.toScheme) [IsClosedImmersion a]
    [IsIso C.ι.toLRSHom.toShHom]
    (i : Z ⟶ X) (hfac : a ≫ C.ι = i)
    (U : X.Opens) (hUC : U ≤ C) (hU : IsAffineOpen U) (I : Ideal Γ(X, U))
    (hV : IsAffineOpen (i ⁻¹ᵁ U))
    (hker : RingHom.ker (i.app U).hom = I)
    (hsurj : Function.Surjective (i.app U).hom)
    (hc : a.toLRSHom.toShHom ≫ C.ι.toLRSHom.toShHom = i.toLRSHom.toShHom)
    (x : (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).val.obj (op U))
    (hx : (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom i.toLRSHom.toShHom))).val.app (op U) x ∈ I) :
    (factoredAffineConormalIsoCotangent C a i hfac U hUC hU I hV hker hsurj).hom.hom
        ((Stacks.ClosedImmersion.pullbackIdealSheafIso a.toLRSHom.toShHom
            C.ι.toLRSHom.toShHom i.toLRSHom.toShHom hc).hom.val.app
              (op ((opensMap i.toLRSHom.toShHom).obj U))
          (((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
            (Stacks.ClosedImmersion.idealSheaf
              i.toLRSHom.toShHom)).val.app (op U) x))
      = I.toCotangent ⟨(kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom i.toLRSHom.toShHom))).val.app (op U) x, hx⟩ := by
  subst hfac
  refine Eq.trans (congrArg
    (fun z => (factoredAffineConormalIsoCotangent C a (a ≫ C.ι) rfl U hUC hU I hV hker
        hsurj).hom.hom z)
    (Stacks.ClosedImmersion.pullbackIdealSheafIsoComp_hom_unit
      a.toLRSHom.toShHom C.ι.toLRSHom.toShHom U x)) ?_
  have hval : (((idealSheafSectionsIso a (C.ι ⁻¹ᵁ U)).hom.hom
        ((Stacks.ClosedImmersion.idealSheafPushforwardIso a.toLRSHom.toShHom
          C.ι.toLRSHom.toShHom).hom.val.app (op U) x) :
      RingHom.ker (a.app (C.ι ⁻¹ᵁ U)).hom) : Γ(C.toScheme, C.ι ⁻¹ᵁ U)) =
      (C.ι.app U).hom ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom (a ≫ C.ι).toLRSHom.toShHom))).val.app (op U) x) :=
    (idealSheafSectionsIso_hom_coe a (C.ι ⁻¹ᵁ U) _).trans
      ((Stacks.ClosedImmersion.kernelι_idealSheafPushforwardIso_hom
        a.toLRSHom.toShHom C.ι.toLRSHom.toShHom U x).trans
        (unitToPushforwardObjUnit_val_app C.ι U _))
  exact (congrArg _ (pullbackSection_self a _ (C.ι ⁻¹ᵁ U) _).symm).trans
    (factoredAffineConormalIsoCotangent_hom_pullbackSection_comp C a U hUC hU I hV hker hsurj
      le_rfl ⟨_, hx⟩ _ hval.symm)

/-! ### Tag 01R3 (2), on generators -/

/-- **The affine computation for a factored immersion, on generators.** A section `x` of the
ideal sheaf of the closed factorization `a` lying over an ideal generator `b ∈ I`, pulled back
to the conormal sheaf, is sent by
`Stacks.Conormal.factoredAffineConormalIsoCotangent` to the class of `b` modulo `I²`.

This is the `Stacks.Conormal.pullbackSection` form of
`Stacks.Conormal.factoredAffineConormalIsoCotangent_pullbackIdealSheafIso_unit`, and unlike that
statement it does not need the open immersion of the factorization to be an isomorphism of
ringed spaces. -/
theorem factoredAffineConormalIsoCotangent_hom_pullbackSection
    {Z X : Scheme.{u}} (C : X.Opens) (a : Z ⟶ C.toScheme) [IsClosedImmersion a]
    (i : Z ⟶ X) (hfac : a ≫ C.ι = i) (U : X.Opens) (hUC : U ≤ C) (hU : IsAffineOpen U)
    (I : Ideal Γ(X, U)) (hV : IsAffineOpen (i ⁻¹ᵁ U))
    (hker : RingHom.ker (i.app U).hom = I) (hsurj : Function.Surjective (i.app U).hom)
    (hle : i ⁻¹ᵁ U ≤ a ⁻¹ᵁ (C.ι ⁻¹ᵁ U))
    (b : I) (x : (Stacks.ClosedImmersion.idealSheaf a.toLRSHom.toShHom).val.obj (op (C.ι ⁻¹ᵁ U)))
    (hx : (C.ι.app U).hom (b : Γ(X, U)) =
      ((idealSheafSectionsIso a (C.ι ⁻¹ᵁ U)).hom.hom x : Γ(C.toScheme, C.ι ⁻¹ᵁ U))) :
    (factoredAffineConormalIsoCotangent C a i hfac U hUC hU I hV hker hsurj).hom.hom
        (Scheme.Modules.pullbackSection a
          (Stacks.ClosedImmersion.idealSheaf a.toLRSHom.toShHom)
          (C.ι ⁻¹ᵁ U) (i ⁻¹ᵁ U) hle x)
      = I.toCotangent b := by
  subst hfac
  exact factoredAffineConormalIsoCotangent_hom_pullbackSection_comp C a U hUC hU I hV hker
    hsurj hle b x hx

/-- **Tag 01R3 (2), on generators**, over the canonical open of the defining factorization. A
section `x` of the ideal sheaf of `i.liftCoborder` over `i.coborderRange.ι ⁻¹ᵁ U` lying over an
ideal generator `b ∈ I`, pulled back to the conormal sheaf, is sent by
`Stacks.Conormal.affineConormalIsoCotangent` to the class of `b` modulo `I²`. -/
theorem affineConormalIsoCotangent_hom_pullbackSection
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (hU : IsAffineOpen U) (I : Ideal Γ(X, U))
    (e : Limits.pullback i U.ι ≅ Spec (.of (Γ(X, U) ⧸ I)))
    (he : Limits.pullback.snd i U.ι ≫ hU.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (hle : i ⁻¹ᵁ U ≤ i.liftCoborder ⁻¹ᵁ (i.coborderRange.ι ⁻¹ᵁ U))
    (b : I)
    (x : (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom).val.obj
      (op (i.coborderRange.ι ⁻¹ᵁ U)))
    (hx : (i.coborderRange.ι.app U).hom (b : Γ(X, U)) =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i.liftCoborder.toLRSHom.toShHom))).val.app
          (op (i.coborderRange.ι ⁻¹ᵁ U)) x) :
    (affineConormalIsoCotangent i U hU I e he).hom.hom
        (Scheme.Modules.pullbackSection i.liftCoborder
          (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom)
          (i.coborderRange.ι ⁻¹ᵁ U) (i ⁻¹ᵁ U) hle x)
      = I.toCotangent b :=
  factoredAffineConormalIsoCotangent_hom_pullbackSection i.coborderRange i.liftCoborder i
    (Scheme.Hom.liftCoborder_ι i) U _ hU I _ _ _ hle b x
    (by rwa [idealSheafSectionsIso_hom_coe])

/-- **A section of the structure sheaf killed by an immersion is a section of the ideal sheaf of
its closed factorization.** -/
theorem exists_idealSection_of_ker {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (r : Γ(X, U)) (hr : (i.app U).hom r = 0) :
    ∃ x₀ : (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom).val.obj
        (op (i.coborderRange.ι ⁻¹ᵁ U)),
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom i.liftCoborder.toLRSHom.toShHom))).val.app
            (op (i.coborderRange.ι ⁻¹ᵁ U)) x₀
        = (i.coborderRange.ι.app U).hom r := by
  have hmem : ((i.coborderRange.ι.app U).hom r) ∈
      RingHom.ker (i.liftCoborder.app (i.coborderRange.ι ⁻¹ᵁ U)).hom := by
    have key : ∀ (f : Z ⟶ X) (_hf : i.liftCoborder ≫ i.coborderRange.ι = f)
        (_hf' : (f.app U).hom r = 0),
        ((i.coborderRange.ι.app U).hom r) ∈
          RingHom.ker (i.liftCoborder.app (i.coborderRange.ι ⁻¹ᵁ U)).hom := by
      rintro f rfl hf'
      rw [Scheme.Hom.comp_app] at hf'
      exact RingHom.mem_ker.mpr hf'
    exact key i i.liftCoborder_ι hr
  refine ⟨(idealSheafSectionsIso i.liftCoborder (i.coborderRange.ι ⁻¹ᵁ U)).inv.hom
    (⟨(i.coborderRange.ι.app U).hom r, hmem⟩ :
      ↥(RingHom.ker (i.liftCoborder.app (i.coborderRange.ι ⁻¹ᵁ U)).hom)), ?_⟩
  rw [← idealSheafSectionsIso_hom_coe]
  exact congrArg
    (fun z : ↥(RingHom.ker (i.liftCoborder.app (i.coborderRange.ι ⁻¹ᵁ U)).hom) =>
      (z : Γ(i.coborderRange.toScheme, i.coborderRange.ι ⁻¹ᵁ U)))
    ((idealSheafSectionsIso i.liftCoborder (i.coborderRange.ι ⁻¹ᵁ U)).inv_hom_id_apply _)

end Stacks.Conormal

namespace Stacks.Divisors

/-- **Stacks Project, Tag 0B3P**, the canonical-ideal-quotient clause: on an affine open `U` of
`X` carrying an affine model `D ∩ U = Spec (Γ(X, U) ⧸ I)` of the closed subscheme `D`, the affine
computation of the conormal sheaf of `D` sends the image of a section `x` of `ℐ_D` over `U` —
pulled back to `D` by the unit of the adjunction and read on the conormal sheaf through
`Stacks.Divisors.conormalSheafIsoNegativeTwist` — to the class of `x` modulo `I²`.

The sheaf `𝒪_X(-D)` of Tag 01WX is the ideal sheaf `ℐ_D` itself, so this is the normalisation of
both of Tag 0B3P's descriptions of the conormal sheaf at once. -/
@[stacks 0B3P "canonical ideal quotient"]
theorem conormalSheafIsoNegativeTwist_apply {X : Scheme.{u}} (D : X.IdealSheafData)
    (U : X.Opens) (hU : IsAffineOpen U) (I : Ideal Γ(X, U))
    (e : Limits.pullback D.subschemeι U.ι ≅ Spec (.of (Γ(X, U) ⧸ I)))
    (he : Limits.pullback.snd D.subschemeι U.ι ≫ hU.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (x : (Stacks.ClosedImmersion.idealSheaf D.subschemeι.toLRSHom.toShHom).val.obj (op U))
    (hx : (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom D.subschemeι.toLRSHom.toShHom))).val.app (op U) x ∈ I) :
    (Stacks.Conormal.affineConormalIsoCotangent D.subschemeι U hU I e he).hom.hom
        ((conormalSheafIsoNegativeTwist D).inv.val.app
          (op ((opensMap D.subschemeι.toLRSHom.toShHom).obj U))
          (((modulePullbackPushforwardAdjunction D.subschemeι.toLRSHom.toShHom).unit.app
            (Stacks.ClosedImmersion.idealSheaf
              D.subschemeι.toLRSHom.toShHom)).val.app (op U) x))
      = I.toCotangent ⟨(kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom D.subschemeι.toLRSHom.toShHom))).val.app (op U) x, hx⟩ :=
  Stacks.Conormal.factoredAffineConormalIsoCotangent_pullbackIdealSheafIso_unit
    D.subschemeι.coborderRange D.subschemeι.liftCoborder D.subschemeι
    (Scheme.Hom.liftCoborder_ι D.subschemeι) U
    (Stacks.Conormal.le_coborderRange_of_affineModel D.subschemeι U hU I e he) hU I
    (Stacks.Conormal.isAffineOpen_preimage_of_affineModel D.subschemeι U I e)
    (by rw [← Scheme.Hom.appLE_preimage_self D.subschemeι U]
        exact Stacks.Conormal.ker_appLE_eq_of_affineModel D.subschemeι U hU I e he)
    (by rw [← Scheme.Hom.appLE_preimage_self D.subschemeι U]
        exact Stacks.Conormal.surjective_appLE_of_affineModel D.subschemeι U hU I e he)
    _ x hx

end Stacks.Divisors

end
