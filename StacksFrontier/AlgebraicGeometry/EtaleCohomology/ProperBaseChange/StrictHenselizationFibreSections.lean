module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.FiniteSurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreEtaleSectionsProper
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SeparablyClosedBaseFieldSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkOfDerivedPushforward

/-!
# Sections over the geometric fibre extend to the base change to the strict henselization

Let `f : X ⟶ S` be proper and `s` a geometric point of `S`, and let
`X^{sh} = X ×_S Spec(𝒪^{sh}_{S,s})` be the base change of `f` to the strict henselization. For
every sheaf of sets `H` on the small étale site of `X`, every global section of `H` restricted
to the geometric fibre `X_s` extends to `X^{sh}`: the restriction map
`Γ(X^{sh}, H|_{X^{sh}}) ⟶ Γ(X_s, H|_{X_s})` is surjective (in fact bijective). This is the
geometric input of the proof of Stacks 0A3T.

The route is the source's. The morphism `X_s ⟶ X^{sh}` factors through the closed fibre
`X^{sh}_0 = X^{sh} ×_{Spec R} Spec κ(R)`, `R = 𝒪^{sh}_{S,s}`, as a base change of
`Spec κ(s) ⟶ Spec κ(R)`. Restriction to the closed fibre is bijective by Stacks 0A3S, since `R` is
strictly henselian and `X^{sh} ⟶ Spec R` is proper; restriction along the base change of the
separably closed field extension `κ(R) ⊆ κ(s)` is bijective by Stacks 0A3I. The two comparisons
of global sections used here — the one of
`Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImageComparison` and the one of
`Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImage` — agree, and agree with
composites, because a natural transformation `Γ(S, -) ⟶ Γ(T, f⁻¹ -)` of global-sections functors
of sheaves of sets is unique: global sections are corepresented by the sheaf of singletons, whose
inverse image is again a sheaf of singletons. The remaining isomorphism of schemes over `X^{sh}`
is bijective on sections by Stacks 0EZK.

## Main results

* `Stacks.EtaleCohomology.globalSectionsNatTrans_ext` — uniqueness of natural transformations
  between global-sections functors along an inverse image.
* `Stacks.EtaleCohomology.surjective_relativeGlobalSectionsMap_geometricFibre_of_isProper` — the
  surjectivity of restriction from `X^{sh}` to the geometric fibre.

## References

* [Stacks Project, Tag 0A3T](https://stacks.math.columbia.edu/tag/0A3T)
* [Stacks Project, Tag 0A3S](https://stacks.math.columbia.edu/tag/0A3S)
* [Stacks Project, Tag 0A3I](https://stacks.math.columbia.edu/tag/0A3I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

section Singletons

variable (X : Scheme.{u})

/-- The sheaf of singletons on the small étale site of a scheme. -/
public def etalePUnitSheaf : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v)) :=
  ⟨(Functor.const _).obj PUnit.{max (u + 1) v + 1}, by
    rw [isSheaf_iff_isSheaf_of_type]
    intro U S hS x hx
    refine ⟨PUnit.unit, ?_, ?_⟩
    · intro V g hg; exact Subsingleton.elim (α := PUnit.{max (u + 1) v + 1}) _ _
    · intro y hy; exact Subsingleton.elim (α := PUnit.{max (u + 1) v + 1}) _ _⟩

/-- The sheaf of singletons is a final object of the topos of sheaves of sets. -/
public def isTerminal_etalePUnitSheaf : IsTerminal (etalePUnitSheaf.{u, v} X) :=
  IsTerminal.ofUniqueHom (fun _ => ⟨{ app := fun _ => ↾fun _ => PUnit.unit }⟩)
    (fun _ _ => by ext U z; exact Subsingleton.elim (α := PUnit.{max (u + 1) v + 1}) _ _)

/-- A final sheaf of sets has at most one section over any object. -/
public theorem subsingleton_obj_of_isTerminal
    {F : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v))} (hF : IsTerminal F) (U : X.Etale) :
    Subsingleton (F.obj.obj (op U)) := by
  let e := hF.uniqueUpToIso (isTerminal_etalePUnitSheaf.{u, v} X)
  refine ⟨fun a b => ?_⟩
  have h : e.hom.hom.app (op U) a = e.hom.hom.app (op U) b :=
    Subsingleton.elim (α := PUnit.{max (u + 1) v + 1}) _ _
  have hid : ∀ z, e.inv.hom.app (op U) (e.hom.hom.app (op U) z) = z := fun z =>
    congrArg (fun φ : F ⟶ F => φ.hom.app (op U) z) e.hom_inv_id
  rw [← hid a, ← hid b, h]

variable {X} {T : Scheme.{u}} (f : T ⟶ X)

/-- The inverse image of a final sheaf of sets is final: its stalks are the stalks of a final
sheaf. -/
public def isTerminal_smallEtaleInverseImage
    {E : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v))} (hE : IsTerminal E) :
    IsTerminal ((smallEtaleInverseImage.{u, v} f).obj E) := by
  have hAB : AB5OfSize.{u, u} (Type (max (u + 1) v)) :=
    AB5OfSize_of_univLE.{u, u, max (u + 1) v, max (u + 1) v} _
  let φ := (isTerminal_etalePUnitSheaf.{u, v} T).from ((smallEtaleInverseImage.{u, v} f).obj E)
  have hiso : IsIso φ := by
    refine isIso_of_forall_geometricStalk φ fun Ω _ _ s => ?_
    have h1 : IsTerminal ((pointSmallEtale s).sheafFiber.obj
        ((smallEtaleInverseImage.{u, v} f).obj E)) :=
      (IsTerminal.isTerminalObj (pointSmallEtale (s ≫ f)).sheafFiber _ hE).ofIso
        ((smallEtaleInverseImageStalkIso.{v, u} f s).app E).symm
    exact isIso_of_isTerminal h1
      (IsTerminal.isTerminalObj (pointSmallEtale s).sheafFiber _
        (isTerminal_etalePUnitSheaf.{u, v} T)) _
  exact (isTerminal_etalePUnitSheaf.{u, v} T).ofIso (asIso φ).symm

end Singletons

section Unique

variable {T S : Scheme.{u}} (f : T ⟶ S)

/-- The isomorphism of global sections with sections over the final object of the small étale
site. -/
abbrev etaleΓIso (X : Scheme.{u}) :=
  Sheaf.ΓNatIsoSheafSections (smallEtaleTopology X) (Type (max (u + 1) v))
    (terminalIsTerminal (C := X.Etale))

/-- A final sheaf of sets has at most one global section. -/
public theorem subsingleton_Γ_of_isTerminal {X : Scheme.{u}}
    {F : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v))} (hF : IsTerminal F) :
    Subsingleton ((Sheaf.Γ (smallEtaleTopology X) (Type (max (u + 1) v))).obj F) := by
  have hs := subsingleton_obj_of_isTerminal.{u, v} X hF (terminal X.Etale)
  refine ⟨fun a b => ?_⟩
  have hinj := (ConcreteCategory.bijective_of_isIso ((etaleΓIso.{u, v} X).hom.app F)).1
  exact hinj (hs.elim _ _)

/-- The morphism from the sheaf of singletons corresponding to a global section. -/
def globalSectionHom {X : Scheme.{u}} (F : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v)))
    (s : (Sheaf.Γ (smallEtaleTopology X) (Type (max (u + 1) v))).obj F) :
    etalePUnitSheaf.{u, v} X ⟶ F :=
  ⟨{ app := fun U => ↾fun _ =>
       F.obj.map (terminal.from U.unop).op ((etaleΓIso.{u, v} X).hom.app F s)
     naturality := fun U V g => by
       ext z
       change F.obj.map (terminal.from V.unop).op _ =
         F.obj.map g (F.obj.map (terminal.from U.unop).op _)
       rw [← types_comp_apply (F.obj.map _) (F.obj.map g), ← F.obj.map_comp]
       have ht : (terminal.from U.unop).op ≫ g = (terminal.from V.unop).op :=
         Quiver.Hom.unop_inj (terminal.hom_ext _ _)
       rw [ht] }⟩

/-- The global section of the sheaf of singletons. -/
def etalePUnitSection (X : Scheme.{u}) :
    (Sheaf.Γ (smallEtaleTopology X) (Type (max (u + 1) v))).obj (etalePUnitSheaf.{u, v} X) :=
  (etaleΓIso.{u, v} X).inv.app (etalePUnitSheaf.{u, v} X) (PUnit.unit : PUnit.{max (u + 1) v + 1})

/-- The morphism attached to a global section carries the unique global section of the sheaf of
singletons to that section. -/
theorem globalSectionHom_map {X : Scheme.{u}}
    (F : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v)))
    (s : (Sheaf.Γ (smallEtaleTopology X) (Type (max (u + 1) v))).obj F) :
    (Sheaf.Γ (smallEtaleTopology X) (Type (max (u + 1) v))).map (globalSectionHom F s)
        (etalePUnitSection.{u, v} X) = s := by
  apply (ConcreteCategory.bijective_of_isIso ((etaleΓIso.{u, v} X).hom.app F)).1
  have hn := congrArg (fun φ => φ (etalePUnitSection.{u, v} X))
    ((etaleΓIso.{u, v} X).hom.naturality (globalSectionHom F s))
  simp only [types_comp_apply] at hn
  refine hn.trans ?_
  show F.obj.map (terminal.from (terminal X.Etale)).op _ = _
  rw [show terminal.from (terminal X.Etale) = 𝟙 _ from terminal.hom_ext _ _, op_id,
    F.obj.map_id, types_id_apply]

/-- **Uniqueness of the comparison of global sections.** Any two natural transformations
`Γ(S, -) ⟶ Γ(T, f⁻¹ -)` between the global-sections functors of sheaves of sets on the small
étale sites are equal: global sections are corepresented by the sheaf of singletons, and the
inverse image of the sheaf of singletons is final, so it has only one global section. -/
public theorem globalSectionsNatTrans_ext
    (α β : Sheaf.Γ (smallEtaleTopology S) (Type (max (u + 1) v)) ⟶
      smallEtaleInverseImage.{u, v} f ⋙ Sheaf.Γ (smallEtaleTopology T) (Type (max (u + 1) v))) :
    α = β := by
  ext F s
  rw [← globalSectionHom_map F s]
  have hα := congrArg (fun φ => φ (etalePUnitSection.{u, v} S))
    (α.naturality (globalSectionHom F s))
  have hβ := congrArg (fun φ => φ (etalePUnitSection.{u, v} S))
    (β.naturality (globalSectionHom F s))
  simp only [types_comp_apply] at hα hβ
  refine hα.trans (Eq.trans ?_ hβ.symm)
  have := subsingleton_Γ_of_isTerminal.{u, v}
    (isTerminal_smallEtaleInverseImage.{u, v} f (isTerminal_etalePUnitSheaf.{u, v} S))
  exact congrArg _ (Subsingleton.elim _ _)

end Unique

section Pullback

/-- **Pullback of global sections is transitive.** For `p = g ≫ f`, pulling a global section
back along `f` and then along `g` is pulling it back along `p`: both are natural
transformations `Γ(X, -) ⟶ Γ(Z, p⁻¹ -)`, hence equal. -/
public theorem relativeGlobalSectionsMap_etaleGlobalPullback {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (p : Z ⟶ X) (hp : p = g ≫ f)
    (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v)))
    (s : (etaleGlobalSections X).obj F) :
    relativeGlobalSectionsMap.{u, v} f g p hp F (etaleGlobalPullback.{u, v} f F s) =
      etaleGlobalPullback.{u, v} p F s := by
  have h := globalSectionsNatTrans_ext.{u, v} p
    ((globalSectionsSmallEtaleInverseImageComparison.{u, v} f).val ≫
      Functor.whiskerLeft (smallEtaleInverseImage.{u, v} f)
        (globalSectionsSmallEtaleInverseImageComparison.{u, v} g).val ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (etalePullbackCompIso.{u, v} f g p hp).hom
        (Sheaf.Γ (smallEtaleTopology Z) (Type (max (u + 1) v))))
    (globalSectionsSmallEtaleInverseImageComparison.{u, v} p).val
  exact congrArg (fun η => η.app F s) h

/-- Pullback of global sections along `f` is bijective as soon as global sections are carried
isomorphically to the global sections of the inverse image by some natural isomorphism. -/
public theorem bijective_etaleGlobalPullback_of_iso {T S : Scheme.{u}} (f : T ⟶ S)
    (φ : Sheaf.Γ (smallEtaleTopology S) (Type (max (u + 1) v)) ≅
      smallEtaleInverseImage.{u, v} f ⋙ Sheaf.Γ (smallEtaleTopology T) (Type (max (u + 1) v)))
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) :
    Function.Bijective (etaleGlobalPullback.{u, v} f F) := by
  have h : (globalSectionsSmallEtaleInverseImageComparison.{u, v} f).val = φ.hom :=
    globalSectionsNatTrans_ext.{u, v} f _ _
  show Function.Bijective ((globalSectionsSmallEtaleInverseImageComparison.{u, v} f).val.app F)
  rw [h]
  exact ConcreteCategory.bijective_of_isIso (φ.hom.app F)

/-- The relative map of global sections is surjective as soon as pullback along `g` is. -/
private theorem surjective_relativeGlobalSectionsMap_of_surjective {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (p : Z ⟶ X) (hp : p = g ≫ f)
    (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v)))
    (hg : Function.Surjective
      (etaleGlobalPullback.{u, v} g ((smallEtaleInverseImage.{u, v} f).obj F))) :
    Function.Surjective (relativeGlobalSectionsMap.{u, v} f g p hp F) :=
  (ConcreteCategory.bijective_of_isIso
    ((etaleGlobalSections Z).map ((etalePullbackCompIso.{u, v} f g p hp).hom.app F))).2.comp hg

/-- Surjectivity of pullback of global sections is stable under composition. -/
public theorem surjective_etaleGlobalPullback_comp {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (p : Z ⟶ X) (hp : p = g ≫ f)
    (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v)))
    (hf : Function.Surjective (etaleGlobalPullback.{u, v} f F))
    (hg : Function.Surjective
      (etaleGlobalPullback.{u, v} g ((smallEtaleInverseImage.{u, v} f).obj F))) :
    Function.Surjective (etaleGlobalPullback.{u, v} p F) := by
  intro t
  obtain ⟨w, rfl⟩ := surjective_relativeGlobalSectionsMap_of_surjective.{u, v} f g p hp F hg t
  obtain ⟨s, rfl⟩ := hf w
  exact ⟨s, (relativeGlobalSectionsMap_etaleGlobalPullback.{u, v} f g p hp F s).symm⟩

/-- An isomorphism of schemes is geometrically connected: each of its base changes to the
spectrum of a field is again an isomorphism. -/
public theorem geometricallyConnected_of_isIso {T S : Scheme.{u}} (e : T ⟶ S) [IsIso e] :
    GeometricallyConnected e := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  have := h.isIso_snd_of_isIso
  exact (Scheme.homeoOfIso (asIso snd)).symm.connectedSpace_iff.1 inferInstance

/-- Pullback of global sections along an isomorphism of schemes is bijective, by Stacks 0EZK. -/
public theorem bijective_etaleGlobalPullback_of_isIso {T S : Scheme.{u}} (e : T ⟶ S) [IsIso e]
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) :
    Function.Bijective (etaleGlobalPullback.{u, v} e F) :=
  have := geometricallyConnected_of_isIso e
  bijective_etaleGlobalPullback_of_iso.{u, v} e
    (globalSectionsSmallEtaleInverseImageIso.{u, v} e
      (universally_isQuotientMap_of_flat_quasiCompact e)) F

end Pullback

section StrictHenselization

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)

variable (s : GeometricPoint S) in
/-- The residue field of the étale local ring at a geometric point embeds in the residue field
of the geometric point, through the evaluation of étale germs. -/
abbrev strictHenselizationResidueAlgebra :
    Algebra (IsLocalRing.ResidueField ↥(etaleLocalRing B S hS s)) s.residueField :=
  haveI := structureSheafStalkToGeometricField_isLocalHom B S hS s
  (IsLocalRing.ResidueField.lift (structureSheafStalkToGeometricField B S hS s)).toAlgebra

attribute [local instance] strictHenselizationResidueAlgebra

variable (s : GeometricPoint S) in
/-- The canonical point of the strict henselization is the residue field extension followed by
the closed point. -/
theorem specMap_algebraMap_comp_residueFieldPoint :
    Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField ↥(etaleLocalRing B S hS s))
        s.residueField)) ≫ residueFieldPoint ↥(etaleLocalRing B S hS s) =
      geometricPointToStrictHenselization B S hS s := by
  have := structureSheafStalkToGeometricField_isLocalHom B S hS s
  show Spec.map (CommRingCat.ofHom (algebraMap _ s.residueField)) ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥(etaleLocalRing B S hS s))) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ))
    (IsLocalRing.ResidueField.lift_comp_residue _)

variable (s : GeometricPoint S) in
/-- **The geometric fibre is a base change of the closed fibre of `X^{sh}`.** The morphism
`X_s ⟶ X^{sh}` is, up to an isomorphism of schemes over `X^{sh}`, the projection from the base
change of the closed fibre along `Spec κ(s) ⟶ Spec κ(R)` followed by the closed fibre
inclusion. -/
theorem exists_iso_geometricFibreToStrictHenselizationBaseChange :
    ∃ e : geometricFibre f s ≅ pullback (closedFibreProjection ↥(etaleLocalRing B S hS s)
        (strictHenselizationBaseChangeToStrictHenselization B hS f s))
        (Spec.map (CommRingCat.ofHom (algebraMap
          (IsLocalRing.ResidueField ↥(etaleLocalRing B S hS s)) s.residueField))),
      geometricFibreToStrictHenselizationBaseChange B hS f s =
        e.hom ≫ pullback.fst _ _ ≫ closedFibreInclusion _ _ := by
  have hc := specMap_algebraMap_comp_residueFieldPoint B hS s
  have h₁ : IsPullback (geometricFibreToStrictHenselizationBaseChange B hS f s)
      (geometricFibreToPoint f s) (strictHenselizationBaseChangeToStrictHenselization B hS f s)
      (Spec.map (CommRingCat.ofHom (algebraMap
        (IsLocalRing.ResidueField ↥(etaleLocalRing B S hS s)) s.residueField)) ≫
        residueFieldPoint ↥(etaleLocalRing B S hS s)) := by
    refine IsPullback.of_right ?_ ?_
      (IsPullback.of_hasPullback f (strictHenselizationToBase B S hS s))
    · rw [geometricFibreToStrictHenselizationBaseChange_comp_toSource, hc,
        geometricPointToStrictHenselization_comp]
      exact IsPullback.of_hasPullback f s.hom
    · rw [hc]
      exact pullback.lift_snd _ _ _
  have h₂ := (IsPullback.of_hasPullback (closedFibreProjection ↥(etaleLocalRing B S hS s)
      (strictHenselizationBaseChangeToStrictHenselization B hS f s))
      (Spec.map (CommRingCat.ofHom (algebraMap
        (IsLocalRing.ResidueField ↥(etaleLocalRing B S hS s)) s.residueField)))).paste_horiz
    (IsPullback.of_hasPullback (strictHenselizationBaseChangeToStrictHenselization B hS f s)
      (residueFieldPoint ↥(etaleLocalRing B S hS s)))
  exact ⟨h₁.isoIsPullback _ _ h₂, (h₁.isoIsPullback_hom_fst _ _ h₂).symm⟩

/-- **Sections over the geometric fibre extend to the base change to the strict
henselization.** For `f : X ⟶ S` proper, `s` a geometric point of `S` and `H` a sheaf of sets
on `X_étale`, every global section of `H` restricted to the geometric fibre `X_s` extends to
`X ×_S Spec(𝒪^{sh}_{S,s})`.

The morphism `X_s ⟶ X ×_S Spec(𝒪^{sh}_{S,s})` is, up to an isomorphism, the closed fibre
inclusion after the base change of `Spec κ(s) ⟶ Spec κ(R)`, `R = 𝒪^{sh}_{S,s}`; restriction to
the closed fibre is bijective by Stacks 0A3S, the base change of the separably closed residue
field `κ(R)` is bijective on sections by Stacks 0A3I, and an isomorphism of schemes is bijective
on sections. -/
public theorem surjective_relativeGlobalSectionsMap_geometricFibre_of_isProper
    [IsProper f] (s : GeometricPoint S)
    (H : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v))) :
    Function.Surjective (relativeGlobalSectionsMap.{u, v}
      (strictHenselizationBaseChangeToSource B hS f s)
      (geometricFibreToStrictHenselizationBaseChange B hS f s)
      (geometricFibreToSource f s)
      (geometricFibreToStrictHenselizationBaseChange_comp_toSource B hS f s).symm H) := by
  obtain ⟨e, he⟩ := exists_iso_geometricFibreToStrictHenselizationBaseChange B hS f s
  let A := ↥(etaleLocalRing B S hS s)
  let h := strictHenselizationBaseChangeToStrictHenselization B hS f s
  let G := (smallEtaleInverseImage.{u, v} (strictHenselizationBaseChangeToSource B hS f s)).obj H
  let a := pullback.fst (closedFibreProjection A h)
    (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField A) s.residueField)))
  have hb : Function.Surjective (etaleGlobalPullback.{u, v} (closedFibreInclusion A h) G) :=
    have := isIso_globalSectionsComparison_closedFibre_of_isProper.{u, v} A h
    (bijective_etaleGlobalPullback_of_iso.{u, v} _ (asIso
      (globalSectionsSmallEtaleInverseImageComparison.{u, v} (closedFibreInclusion A h)).val) G).2
  have ha : Function.Surjective (etaleGlobalPullback.{u, v} a
      ((smallEtaleInverseImage.{u, v} (closedFibreInclusion A h)).obj G)) :=
    (bijective_etaleGlobalPullback_of_iso.{u, v} a
      (globalSectionsSmallEtaleInverseImageIso_of_isSepClosed.{u, v}
        (IsLocalRing.ResidueField A) s.residueField (closedFibreProjection A h)) _).2
  have hq := surjective_etaleGlobalPullback_comp.{u, v} _ a _ rfl G hb ha
  have hg := surjective_etaleGlobalPullback_comp.{u, v} _ e.hom _ he G hq
    (bijective_etaleGlobalPullback_of_isIso.{u, v} e.hom _).2
  exact surjective_relativeGlobalSectionsMap_of_surjective.{u, v} _ _ _ _ H hg

end StrictHenselization

end Stacks.EtaleCohomology

end
