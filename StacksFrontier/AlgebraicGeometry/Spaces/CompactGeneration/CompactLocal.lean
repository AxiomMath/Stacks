module

public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.EtaleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.QcqsUnitCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforwardDirectSums
public import StacksFrontier.CategoryTheory.Triangulated.CompactGenerationAdjunction
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory

/-!
# Compactness in `D_QCoh` is local for an elementary distinguished square

A compact object of `D_QCoh(𝒪_Z)` is compact relative to `D_QCoh(𝒪_Z)` inside `D(𝒪_Z)`, and
conversely (`AlgebraicGeometry.Space.IsQcohCompact`). Restriction along an étale, quasi-compact
and quasi-separated morphism preserves compact objects of `D_QCoh`, its right adjoint commuting
with direct sums ([Stacks, Tag 08FB]).

For an elementary distinguished square `(U ⊆ W, j : V ⟶ W)` with intersection `P`, an object of
`D_QCoh(𝒪_W)` whose restrictions to `U`, `V` and `P` are compact is compact: the Mayer–Vietoris
triangle of [Stacks, Tag 08GV] places it after `j_{P!}E|_P ⟶ j_{U!}E|_U ⊕ j_{V!}E|_V`, and
extension by zero preserves relative compactness.

## Main results

* `AlgebraicGeometry.Space.isQcohCompact_of_isCompactObject`,
  `AlgebraicGeometry.Space.isCompactObject_of_isQcohCompact`: the two notions agree on `D_QCoh`.
* `AlgebraicGeometry.Space.isCompactObject_quasicoherentDerivedEtalePullback_obj`: restriction
  preserves compact objects.
* `AlgebraicGeometry.Space.isCompactObject_of_isCompactObject_restrict_eds`: compactness is local
  for an elementary distinguished square.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Pretriangulated

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

attribute [local instance] isGrothendieckAbelian_modules_ringUniverse
  Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A compact object of `D_QCoh(𝒪_Z)` is compact relative to `D_QCoh(𝒪_Z)` in `D(𝒪_Z)`. -/
theorem isQcohCompact_of_isCompactObject (Z : AlgebraicSpaces B S hS)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Z.1 Z.2) (hK : IsCompactObject.{u} K) :
    IsQcohCompact B S hS Z K.obj := by
  intro I _ E hE T ι hι
  have := isClosedUnderColimitsOfShape_qcohDerived B S hS Z I
  have hT : QcohDerived B S hS Z T :=
    (QcohDerived B S hS Z).prop_of_isColimit hι fun i => hE i.as
  let E' : I → QuasicoherentDerivedCategory.{u, u} B S hS Z.1 Z.2 := fun i => ⟨E i, hE i⟩
  let T' : QuasicoherentDerivedCategory.{u, u} B S hS Z.1 Z.2 := ⟨T, hT⟩
  let ι' : ∀ i, E' i ⟶ T' := fun i => ObjectProperty.homMk (ι i)
  have hι' : IsColimit (Cofan.mk T' ι') :=
    isColimitOfReflects (ObjectProperty.ι _)
      ((isColimitMapCoconeCofanMkEquiv (ObjectProperty.ι _) E' ι').symm hι)
  exact (bijective_cofanMap_map_iff_of_fullyFaithful (ObjectProperty.ι _) _ ι').2
    (bijective_cofanMap _ hK ι' hι')

/-- An object of `D_QCoh(𝒪_Z)` compact relative to `D_QCoh(𝒪_Z)` in `D(𝒪_Z)` is compact. -/
theorem isCompactObject_of_isQcohCompact (Z : AlgebraicSpaces B S hS)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Z.1 Z.2) (h : IsQcohCompact B S hS Z K.obj) :
    IsCompactObject.{u} K := by
  constructor
  intro I _ E _
  have := isClosedUnderColimitsOfShape_qcohDerived B S hS Z I
  have hc : IsColimit (Cofan.mk ((ObjectProperty.ι _).obj (∐ E))
      fun i => (ObjectProperty.ι _).map (Sigma.ι E i)) :=
    (isColimitMapCoconeCofanMkEquiv (ObjectProperty.ι _) E (Sigma.ι E))
      (isColimitOfPreserves (ObjectProperty.ι _) (coproductIsCoproduct E))
  exact (bijective_cofanMap_map_iff_of_fullyFaithful (ObjectProperty.ι _) _ (Sigma.ι E)).1
    (h (fun i => (E i).obj) (fun i => (E i).property) _ hc)

/-- **Restriction along an étale, quasi-compact and quasi-separated morphism preserves compact
objects of `D_QCoh`**: its right adjoint `Rf_*` commutes with direct sums ([Stacks, Tag 08FB]). -/
theorem isCompactObject_quasicoherentDerivedEtalePullback_obj {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom)
    {K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2} (hK : IsCompactObject.{u} K) :
    IsCompactObject.{u} ((quasicoherentDerivedEtalePullback B S hS f hf).obj K) :=
  have := fun J : Type u =>
    preservesCoproducts_quasicoherentDerivedPushforward B S hS f hfqc hfqs J
  isCompactObject_map_of_adjunction (quasicoherentDerivedEtaleAdjunction B S hS f hf hfqc hfqs) hK

section Square

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable {B S hS} {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}

/-- Relative compactness of `j_!(E|_Z)` from that of `E|_Z`, for `j : Z ⟶ W` étale. -/
theorem isQcohCompact_restrict_lowerShriek {Z : AlgebraicSpaces B S hS} (j : Z ⟶ W)
    (hj : IsEtale B S hS j.hom) (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (h : IsQcohCompact B S hS Z
      ((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.obj E)) :
    IsQcohCompact B S hS W ((etaleModulePullback.{u, u} B S hS j hj ⋙
      etaleModuleLowerShriek B S hS j hj).mapDerivedCategory.obj E) :=
  (isQcohCompact_lowerShriek j hj h).of_iso
    ((Dualizing.mapDerivedCategoryComp _ _).app E).symm

/-- **Compactness in `D_QCoh` is local for an elementary distinguished square**: an object of
`D_QCoh(𝒪_W)` whose restrictions to `U`, `V` and `P = U ×_W V` are compact relative to `D_QCoh`
is compact. -/
theorem isCompactObject_of_isQcohCompact_restrict_eds
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS W.1 W.2)
    (hU : IsQcohCompact B S hS (edsOpen B S hS hsq) ((etaleModulePullback.{u, u} B S hS
      (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj E.obj))
    (hV : IsQcohCompact B S hS (edsEtale B S hS hsq) ((etaleModulePullback.{u, u} B S hS
      (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj E.obj))
    (hP : IsQcohCompact B S hS (edsInter B S hS hsq) ((etaleModulePullback.{u, u} B S hS
      (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E.obj)) :
    IsCompactObject.{u} E := by
  refine isCompactObject_of_isQcohCompact B S hS W E ?_
  obtain ⟨_, hT⟩ := (mayerVietoris_shortExact_and_mem_distTriang B S hS hsq).2 E.obj
  exact IsQcohCompact.obj₃ _ hT
    (isQcohCompact_restrict_lowerShriek _ (isEtale_edsInterHom B S hS hsq) E.obj hP)
    ((isQcohCompact_restrict_lowerShriek _ (isEtale_edsOpenHom B S hS hsq) E.obj hU).biprod
      (isQcohCompact_restrict_lowerShriek _ (isEtale_edsEtaleHom B S hS hsq) E.obj hV))

end Square

end AlgebraicGeometry.Space

end
