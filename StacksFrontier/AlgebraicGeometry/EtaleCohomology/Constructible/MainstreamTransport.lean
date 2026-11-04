module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparison

/-!
# Torsion étale sheaves on Mathlib's small étale site as colimits of constructible ones

Stacks 03SA part (3) is available in this library on the small étale site of Stacks 021B of a
scheme `X` of a big étale site `B`, for sheaves of modules over a Noetherian ring
(`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleModuleSheaf_of_qcqs`). Étale
cohomology, on the other hand, is computed on Mathlib's small étale site `X.smallEtaleTopology`
with abelian coefficients. This file carries the first statement to the second setting for
abelian sheaves annihilated by an integer `n > 0`.

The transport functor `AlgebraicGeometry.SmallEtale.moduleSheafToEtale` forgets the module
structure of a sheaf of `Λ`-modules on the site of Stacks 021B and then crosses to Mathlib's site
along the equivalence of sheaf categories `AlgebraicGeometry.SmallEtale.sheafEquiv`. It preserves
all colimits: forgetting the module structure is a left adjoint, and so is composition with it on
sheaves.

## Main definitions

* `AlgebraicGeometry.SmallEtale.moduleSheafToEtale` — the transport functor.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_isColimit_moduleSheafToEtale_isConstructible` — an abelian
  sheaf on Mathlib's small étale site of a quasi-compact quasi-separated scheme which is
  annihilated by `n > 0` is the colimit of a filtered diagram of transports of constructible
  sheaves of `ℤ/nℤ`-modules on the site of Stacks 021B.

## Implementation notes

The coefficient ring is `ULift (ZMod n)`, because Stacks 03SA (3) is stated for coefficient rings
in `Type (u + 1)`. The module structure on an abelian sheaf annihilated by `n` is the ring map
`ZMod n → End F` induced by the integers; it is carried to the site of Stacks 021B along the
inverse equivalence, which is additive, and the sheaf of modules is then
`Stacks.ModuleCatLift.sheafOfEndAction`, whose underlying abelian sheaf is the original one on
the nose.

No `@[stacks]` attribute appears: this is the transport of Stacks 03SA (3), not a new statement.

## References

* [Stacks Project, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

/-- Forgetting the module structure is a left adjoint, Mathlib having its right adjoint only for
`Λ = ℤ`: it preserves colimits and the category of modules has a separator. -/
public lemma forget₂_isLeftAdjoint (Λ : Type (u + 1)) [Ring Λ] :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).IsLeftAdjoint := by
  let : PreservesColimits (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} Λ
  exact isLeftAdjoint_of_preservesColimits_of_isSeparating.{u + 1}
    (ModuleCat.isSeparator.{u + 1, u + 1} Λ) _

/-- Composition with an adjunction is an adjunction between categories of sheaves. -/
public def sheafComposeAdjunction {C : Type*} [Category* C]
    (J : GrothendieckTopology C) {A B : Type*} [Category* A] [Category* B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    [J.HasSheafCompose L] [J.HasSheafCompose R] :
    sheafCompose J L ⊣ sheafCompose J R :=
  (adj.whiskerRight Cᵒᵖ).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf J A) (fullyFaithfulSheafToPresheaf J B)
    (Iso.refl _) (Iso.refl _)

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type (u + 1)) [Ring Λ]

/-- **The transport functor.** A sheaf of `Λ`-modules on the small étale site of Stacks 021B of
`X` goes to the abelian sheaf on Mathlib's small étale site of `X` obtained by forgetting the
module structure and crossing along `AlgebraicGeometry.SmallEtale.sheafEquiv`. -/
public def moduleSheafToEtale :
    Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ) ⥤
      Sheaf X.obj.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙
    (sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).functor

/-- The transport functor is a left adjoint. -/
public instance moduleSheafToEtale_isLeftAdjoint : (moduleSheafToEtale B X Λ).IsLeftAdjoint := by
  have := forget₂_isLeftAdjoint Λ
  have := (sheafComposeAdjunction (SmallEtale.topology B X.obj X.property)
    (Adjunction.ofIsLeftAdjoint
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))).isLeftAdjoint
  dsimp only [moduleSheafToEtale]
  infer_instance

/-- The transport functor preserves all colimits. -/
public instance moduleSheafToEtale_preservesColimits :
    PreservesColimitsOfSize.{u + 1, u + 1} (moduleSheafToEtale B X Λ) :=
  (Adjunction.ofIsLeftAdjoint (moduleSheafToEtale B X Λ)).leftAdjoint_preservesColimits

/-- The ring map `ZMod n → End F` on an object of a preadditive category annihilated by `n`. -/
private def zmodEndRingHom {C : Type*} [Category* C] [Preadditive C] (n : ℕ) (F : C)
    (hF : (n : ℤ) • 𝟙 F = 0) : ULift.{u + 1} (ZMod n) →+* End F :=
  have : CharP (End F) (ringChar (End F)) := ringChar.charP _
  (ZMod.castHom (ringChar.dvd (by rw [← nsmul_one, ← natCast_zsmul]; exact hF)) (End F)).comp
    ULift.ringEquiv.toRingHom

/-- `ULift (ZMod n)` is Noetherian for `n > 0`, being finite. -/
private instance isNoetherianRing_uliftZMod (n : ℕ) [NeZero n] :
    IsNoetherianRing (ULift.{u + 1} (ZMod n)) :=
  isNoetherianRing_of_ringEquiv (ZMod n) ULift.ringEquiv.symm

/-- **Stacks 03SA (3), transported to Mathlib's small étale site.** Let `X` be a quasi-compact and
quasi-separated scheme of a big étale site `B`, `n > 0`, and `F` an abelian sheaf on Mathlib's
small étale site of `X` annihilated by `n`. Then `F` is the colimit of a filtered diagram of
transports, along `AlgebraicGeometry.SmallEtale.moduleSheafToEtale`, of constructible sheaves of
`ℤ/nℤ`-modules on the small étale site of Stacks 021B. -/
public theorem exists_isColimit_moduleSheafToEtale_isConstructible
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] (n : ℕ) [NeZero n]
    (F : Sheaf X.obj.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : (n : ℤ) • 𝟙 F = 0) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))))
      (ι : D ⋙ moduleSheafToEtale B X (ULift.{u + 1} (ZMod n)) ⟶ (Functor.const I).obj F),
        Nonempty (IsColimit (Cocone.mk F ι)) ∧
          ∀ i, IsConstructibleModuleSheaf B X (ULift.{u + 1} (ZMod n)) (D.obj i) := by
  let E := sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}
  let G := E.inverse.obj F
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  let φ := (Stacks.ModuleCatLift.mapEndRingHom E.inverse F).comp (zmodEndRingHom n F hF)
  let Gm := Stacks.ModuleCatLift.sheafOfEndAction (ULift.{u + 1} (ZMod n))
    (SmallEtale.topology B X.obj X.property) G φ
  obtain ⟨I, hI, hfilt, D, ι, ⟨hc⟩, hD⟩ :=
    exists_isFilteredColimit_isConstructibleModuleSheaf_of_qcqs B X _ Gm
  have hc' := isColimitOfPreserves (moduleSheafToEtale B X (ULift.{u + 1} (ZMod n))) hc
  let e : (moduleSheafToEtale B X (ULift.{u + 1} (ZMod n))).obj Gm ≅ F := E.counitIso.app F
  refine ⟨I, hI, hfilt, D,
    ((moduleSheafToEtale B X _).mapCocone (Cocone.mk Gm ι)).ι ≫ (Functor.const I).map e.hom,
    ⟨IsColimit.ofIsoColimit hc' (Cocones.ext e (fun _ => rfl))⟩, hD⟩

/-- The right adjoint of forgetting the module structure. -/
public abbrev forget₂RightAdjoint : AddCommGrpCat.{u + 1} ⥤ ModuleCat.{u + 1} Λ :=
  have := forget₂_isLeftAdjoint Λ
  (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).rightAdjoint

/-- Forgetting the module structure is left adjoint to `forget₂RightAdjoint`. -/
public abbrev forget₂Adjunction :
    forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} ⊣ forget₂RightAdjoint Λ :=
  have := forget₂_isLeftAdjoint Λ
  Adjunction.ofIsLeftAdjoint _

/-- The right adjoint of the transport functor: restriction to the site of Stacks 021B followed by
composition with the right adjoint of forgetting the module structure. -/
public abbrev moduleSheafFromEtale :
    Sheaf X.obj.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ) :=
  (sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).inverse ⋙
    sheafCompose _ (forget₂RightAdjoint Λ)

/-- The adjunction between the transport functor and `moduleSheafFromEtale`. -/
public def moduleSheafToEtaleAdjunction : moduleSheafToEtale B X Λ ⊣ moduleSheafFromEtale B X Λ :=
  (sheafComposeAdjunction (SmallEtale.topology B X.obj X.property) (forget₂Adjunction Λ)).comp
    (sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).toAdjunction

/-- **The transport functor commutes with inverse image.** For a morphism `f : T ⟶ S` of a big
étale site, transporting and then taking the inverse image along `f` on Mathlib's small étale sites
is taking the inverse image on the sites of Stacks 021B and then transporting. Both composites are
left adjoints, and their right adjoints agree because the two presentations of the small étale
site have the same direct image along base change
(`AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso`) and composition with a
functor of coefficients commutes with direct image on the nose. -/
public def moduleSheafToEtalePullbackIso {S T : B.Scheme} (f : T ⟶ S) :
    moduleSheafToEtale B S Λ ⋙
        Stacks.EtaleCohomology.etaleAbelianInverseImage.{u, 0} (B.inclusion.map f) ≅
      (AlgebraicGeometry.smallEtaleBaseChange B f).sheafPullback (ModuleCat.{u + 1} Λ)
          (topology B S.obj S.property) (topology B T.obj T.property) ⋙
        moduleSheafToEtale B T Λ :=
  Adjunction.leftAdjointUniq
    (((moduleSheafToEtaleAdjunction B S Λ).comp
      (Stacks.EtaleCohomology.etaleAbelianInverseImageDirectImageAdj.{u, 0}
        (B.inclusion.map f))).ofNatIsoRight
      (Functor.isoWhiskerRight (toEtaleSitePushforwardBaseChangeIso B f AddCommGrpCat.{u + 1})
        (sheafCompose _ (forget₂RightAdjoint Λ))))
    (((AlgebraicGeometry.smallEtaleBaseChange B f).sheafAdjunctionContinuous
      (ModuleCat.{u + 1} Λ) _ _).comp (moduleSheafToEtaleAdjunction B T Λ))

/-- **The transport functor carries constant sheaves to constant sheaves.** Both composites are
left adjoint to taking sections over the final object, read through the right adjoint of forgetting
the module structure; the embedding of the site of Stacks 021B carries its final object to a final
object of Mathlib's site (`AlgebraicGeometry.SmallEtale.isTerminalToEtaleSiteFinal`). -/
public def moduleSheafToEtaleConstantIso :
    constantSheaf (topology B X.obj X.property) (ModuleCat.{u + 1} Λ) ⋙
        moduleSheafToEtale B X Λ ≅
      forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} ⋙
        constantSheaf X.obj.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Adjunction.leftAdjointUniq
    ((constantSheafAdj (topology B X.obj X.property) (ModuleCat.{u + 1} Λ)
      (SmallEtale.finalIsTerminal B X.obj X.property)).comp
        (moduleSheafToEtaleAdjunction B X Λ))
    (((forget₂Adjunction Λ).comp (constantSheafAdj X.obj.smallEtaleTopology AddCommGrpCat.{u + 1}
      (isTerminalToEtaleSiteFinal B X.obj X.property))).ofNatIsoRight (Iso.refl _))

end AlgebraicGeometry.SmallEtale

end
