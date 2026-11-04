module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CanonicalExtension
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Pullback
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.BaseAdicCompletion
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.EquationsBaseChange
public import StacksFrontier.CategoryTheory.Limits.ProObject.Functoriality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat base change for canonical extensions of coherent formal modules

Fix an algebraization situation `S`: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, giving
`X = Spec(A)` and the open complement `U = X ∖ V(𝔞)`. Let `A → A'` be a flat ring map with `A'`
Noetherian. Extending both ideals along it gives the base-changed situation `S'`, with
`X' = Spec(A')`; its open complement `U'` is the inverse image of `U` along `f : X' ⟶ X`, and the
induced `g : U' ⟶ U` sits in a cartesian square over `f`. A coherent `I`-adic system `(F_n)` on
`U` pulls back to the coherent `I A'`-adic system `(F'_n) = (g^*F_n)` on `U'`. If `(F_n)`
canonically extends to `X`, then `(F'_n)` canonically extends to `X'`, and its extension is the
pullback along `f` of the extension of `(F_n)`.

## Main definitions

* `Stacks.Coherent.quasicoherentModulesPullback` — pullback of quasi-coherent modules,
  `QCoh(X) ⥤ QCoh(X')`.
* `Stacks.Algebraization.AlgebraizationSituation.baseChange` — the situation `(A', I A', 𝔞 A')`.
* `Stacks.Algebraization.baseChangeAdicSystem` — the pulled back system `(g^*F_n)` on `U'`.
* `Stacks.Algebraization.baseChangeCanonicalExtension` — the pulled back system `(f^*G_n)` on
  `X'`.

## Main results

* `Stacks.Coherent.nonempty_diagramToPro_comp_iso` — a functor on quasi-coherent modules carries
  a pro-isomorphism of inverse systems to a pro-isomorphism of the composed systems.
* `Stacks.Coherent.coherentAdicPullback_quasicoherentDiagram` — the diagram of the pullback of a
  coherent adic system is the pullback of its diagram.
* `Stacks.Algebraization.nonempty_tildeGlobalSectionsSystem_baseChange_iso` — the system of
  quasi-coherent sheaves attached to the global sections of `(F'_n)` is the pullback along `f` of
  the one attached to `(F_n)`.
* `Stacks.Algebraization.nonempty_pullback_extension_iso` — the pullback along `f` of an
  extension of `(F_n)` to `X` is an extension of `(F'_n)` to `X'`.
* `Stacks.Algebraization.canonicallyExtends_base_change` — if `(F_n)` canonically extends to `X`,
  then `(F'_n)` canonically extends to `X'`.

## References

* [Stacks Project, Tag 0EIS](https://stacks.math.columbia.edu/tag/0EIS)
* [Stacks Project, Tag 0887](https://stacks.math.columbia.edu/tag/0887)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Coherent

/-- The pullback functor `QCoh(Y) ⥤ QCoh(X)` along `f : X ⟶ Y`, the restriction of the pullback
of `𝒪`-modules to quasi-coherent modules. -/
public def quasicoherentModulesPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.QuasicoherentModules Y ⥤ Scheme.QuasicoherentModules X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Scheme.Modules.pullback f) (fun M => by
    have _ : (M.1).IsQuasicoherent := M.2
    exact Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback f M.1)

/-- An isomorphism of diagrams landing in a full subcategory, read in that subcategory. -/
private def liftObjectPropertyIso {J : Type*} [Category J] {D : Type*} [Category D]
    {P : ObjectProperty D} {A B : J ⥤ D} (hA : ∀ j, P (A.obj j)) (hB : ∀ j, P (B.obj j))
    (e : A ≅ B) : ObjectProperty.lift P A hA ≅ ObjectProperty.lift P B hB :=
  NatIso.ofComponents (fun j => ObjectProperty.isoMk _ (e.app j))
    (fun f => (ObjectProperty.ι _).map_injective (e.hom.naturality f))

/-! ### The bridge to colimits of representables -/

section Bridge

variable {X Y : Scheme.{u}}

/-- An isomorphism of inverse diagrams of quasi-coherent modules induces one of the pro-objects
they present. -/
public def diagramToProMapIso {F G : ℕᵒᵖ ⥤ Scheme.QuasicoherentModules X} (i : F ≅ G) :
    diagramToPro F ≅ diagramToPro G := by
  letI : IsFiltered (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ))) :=
    IsFiltered.of_equivalence adicIndexEquivalence.{u}
  exact ((Ind.lim (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))).mapIso
    (Functor.isoWhiskerLeft adicIndexEquivalence.{u}.inverse (NatIso.op i))).op

/-- The pro-object presented by a diagram of quasi-coherent modules, seen inside presheaves, is
the colimit of the representables on its stages. -/
public def indInclusionColimitIso (F : ℕᵒᵖ ⥤ Scheme.QuasicoherentModules X)
    [IsFiltered (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))] :
    (Ind.inclusion (Scheme.QuasicoherentModules X)ᵒᵖ).obj
        ((Ind.lim (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))).obj
          (adicIndexEquivalence.{u}.inverse ⋙ F.op)) ≅
      colimit (F.op ⋙ yoneda) :=
  (Ind.limCompInclusion.app (adicIndexEquivalence.{u}.inverse ⋙ F.op)) ≪≫
    Functor.Final.colimitIso adicIndexEquivalence.{u}.inverse (F.op ⋙ yoneda)

/-- Two inverse diagrams of quasi-coherent modules present isomorphic pro-objects exactly when
the colimits of the representables on their stages are isomorphic. -/
public theorem nonempty_colimitYonedaIso_iff
    (F G : ℕᵒᵖ ⥤ Scheme.QuasicoherentModules X) :
    Nonempty (diagramToPro F ≅ diagramToPro G) ↔
      Nonempty (colimit (F.op ⋙ yoneda) ≅ colimit (G.op ⋙ yoneda)) := by
  let _ : IsFiltered (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ))) :=
    IsFiltered.of_equivalence adicIndexEquivalence.{u}
  exact ⟨Nonempty.map fun h => (indInclusionColimitIso F).symm ≪≫
      (Ind.inclusion (Scheme.QuasicoherentModules X)ᵒᵖ).mapIso h.unop.symm ≪≫
      indInclusionColimitIso G,
    Nonempty.map fun h => ((Ind.inclusion (Scheme.QuasicoherentModules X)ᵒᵖ).preimageIso
      (indInclusionColimitIso F ≪≫ h ≪≫ (indInclusionColimitIso G).symm)).symm.op⟩

/-- A functor on quasi-coherent modules carries a pro-isomorphism of inverse diagrams to a
pro-isomorphism of the composed diagrams. -/
public theorem nonempty_diagramToPro_comp_iso
    (L : Scheme.QuasicoherentModules X ⥤ Scheme.QuasicoherentModules Y)
    (F G : ℕᵒᵖ ⥤ Scheme.QuasicoherentModules X)
    (h : diagramToPro F ≅ diagramToPro G) :
    Nonempty (diagramToPro (F ⋙ L) ≅ diagramToPro (G ⋙ L)) :=
  (nonempty_colimitYonedaIso_iff (F ⋙ L) (G ⋙ L)).2
    (((nonempty_colimitYonedaIso_iff F G).1 ⟨h⟩).map (Stacks.ProObject.transportIso L.op F.op G.op))

end Bridge

/-- The pro-object attached to a coherent adic system is the one presented by its diagram of
quasi-coherent modules. -/
public theorem coherentAdicToPro_obj_eq {X : Scheme.{u}} (I : X.IdealSheafData)
    (G : CoherentAdicSystems I) :
    (coherentAdicToPro X I).obj G = diagramToPro (quasicoherentDiagram G) :=
  rfl

/-- The diagram of quasi-coherent modules of the pullback of a coherent adic system is the
pullback of its diagram. -/
public theorem coherentAdicPullback_quasicoherentDiagram {X Y : Scheme.{u}} [IsNoetherian X]
    [IsNoetherian Y] (f : X ⟶ Y) (J : Y.IdealSheafData) (G : CoherentAdicSystems J) :
    quasicoherentDiagram ((coherentAdicPullback f J).obj G) =
      quasicoherentDiagram G ⋙ quasicoherentModulesPullback f :=
  rfl

end Stacks.Coherent

namespace Stacks.Algebraization

/-- A coherent adic system presenting a pro-object along one ideal sheaf presents it along any
ideal sheaf equal to it. -/
public theorem exists_coherentAdicSystem_of_eq {X : Scheme.{u}} {I J : X.IdealSheafData}
    (hIJ : I = J) (P : (Ind (Scheme.QuasicoherentModules X)ᵒᵖ)ᵒᵖ)
    (G : Stacks.Coherent.CoherentAdicSystems I)
    (e : P ≅ (Stacks.Coherent.coherentAdicToPro X I).obj G) :
    ∃ G' : Stacks.Coherent.CoherentAdicSystems J,
      Nonempty (P ≅ (Stacks.Coherent.coherentAdicToPro X J).obj G') := by
  subst hIJ
  exact ⟨G, ⟨e⟩⟩

/-! ### The base-changed situation -/

variable (S : AlgebraizationSituation.{u}) (A' : Type u) [CommRing A'] [IsNoetherianRing A']
  [Algebra S.A A']

/-- The base change of an algebraization situation along a ring map `A → A'`: the ring is `A'` and
the two ideals are the extensions `I A'` and `𝔞 A'`, so that `X' = Spec(A')`. -/
public def AlgebraizationSituation.baseChange : AlgebraizationSituation.{u} where
  A := A'
  I := S.I.map (algebraMap S.A A')
  a := S.a.map (algebraMap S.A A')
  I_le_a := Ideal.map_mono S.I_le_a

/-- The morphism `f : X' = Spec(A') ⟶ X = Spec(A)` induced by the ring map. -/
public def AlgebraizationSituation.baseChangeMap : (S.baseChange A').X ⟶ S.X :=
  Spec.map (CommRingCat.ofHom (algebraMap S.A A'))

/-- The morphism `X' ⟶ X` induced by a flat ring map `A → A'` is flat. -/
public instance [Module.Flat S.A A'] : Flat (S.baseChangeMap A') :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr ‹_› : RingHom.Flat (algebraMap S.A A'))

/-- The open complement `U'` of the base-changed situation is the inverse image of `U` along
`f : X' ⟶ X`. -/
public theorem AlgebraizationSituation.baseChange_U_eq_preimage :
    (S.baseChange A').U = S.baseChangeMap A' ⁻¹ᵁ S.U := by
  ext x
  show ¬(S.a.map (algebraMap S.A A') ≤ (x : PrimeSpectrum A').asIdeal) ↔
    ¬(S.a ≤ (x : PrimeSpectrum A').asIdeal.comap (algebraMap S.A A'))
  exact not_congr Ideal.map_le_iff_le_comap

/-- The inverse image of `I 𝒪_X` along `f : X' ⟶ X` is `(I A') 𝒪_{X'}`. -/
public theorem comap_idealOnX_baseChange :
    (idealOnX S).comap (S.baseChangeMap A') = idealOnX (S.baseChange A') := by
  have h : (idealOnX S).comap (S.baseChangeMap A') =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A')).inv.hom
          (Ideal.map (algebraMap S.A A') S.I)) := by
    rw [idealOnX, Stacks.IdealSheaf.comap_ofIdealTop, Ideal.map_map, Ideal.map_map]
    exact congrArg (fun ψ : S.A →+* Γ(Spec (CommRingCat.of A'), ⊤) =>
      Scheme.IdealSheafData.ofIdealTop (Ideal.map ψ S.I)) (congrArg CommRingCat.Hom.hom
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap S.A A')))).symm
  exact h

/-- The induced morphism `g : U' ⟶ U` on the open complements. -/
public def AlgebraizationSituation.baseChangeOpenMap :
    (S.baseChange A').U.toScheme ⟶ S.U.toScheme :=
  ((S.baseChange A').X.isoOfEq (S.baseChange_U_eq_preimage A')).hom ≫ (S.baseChangeMap A' ∣_ S.U)

/-- `U'` is the fibre product of `U` and `X'` over `X`. -/
public theorem AlgebraizationSituation.isPullback_baseChangeOpenMap :
    IsPullback (S.baseChangeOpenMap A') (S.baseChange A').U.ι S.U.ι (S.baseChangeMap A') :=
  (isPullback_morphismRestrict (S.baseChangeMap A') S.U).of_iso
    ((S.baseChange A').X.isoOfEq (S.baseChange_U_eq_preimage A')).symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (by simp [AlgebraizationSituation.baseChangeOpenMap]) (by simp) (by simp)
    (by simp)

/-- The inverse image of `I 𝒪_U` along `g` is `(I A') 𝒪_{U'}`. -/
public theorem comap_idealOnOpen_baseChange :
    (idealOnOpen S).comap (S.baseChangeOpenMap A') = idealOnOpen (S.baseChange A') := by
  rw [idealOnOpen_eq_comap_idealOnX, ← Scheme.IdealSheafData.comap_comp,
    (S.isPullback_baseChangeOpenMap A').w, Scheme.IdealSheafData.comap_comp,
    comap_idealOnX_baseChange, idealOnOpen_eq_comap_idealOnX]

/-- The pulled back coherent adic system `(F'_n) = (g^*F_n)` on `U'`. -/
public def baseChangeAdicSystem (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) :
    Stacks.Coherent.CoherentAdicSystems (idealOnOpen (S.baseChange A')) :=
  ⟨F.obj ⋙ Scheme.Modules.pullback (S.baseChangeOpenMap A'),
    comap_idealOnOpen_baseChange S A' ▸
      Stacks.Coherent.isCoherentAdicSystem_pullback (S.baseChangeOpenMap A') (idealOnOpen S) F⟩

/-- The pulled back coherent adic system `(f^*G_n)` on `X'`. -/
public def baseChangeCanonicalExtension (G : Stacks.Coherent.CoherentAdicSystems (idealOnX S)) :
    Stacks.Coherent.CoherentAdicSystems (idealOnX (S.baseChange A')) :=
  ⟨G.obj ⋙ Scheme.Modules.pullback (S.baseChangeMap A'),
    comap_idealOnX_baseChange S A' ▸
      Stacks.Coherent.isCoherentAdicSystem_pullback (S.baseChangeMap A') (idealOnX S) G⟩

/-! ### The global sections as a direct image -/

/-- The stages of a coherent adic system are quasi-coherent. -/
private theorem isQuasicoherent_coherentAdicSystem_obj (T : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen T)) (n : ℕᵒᵖ) :
    (F.obj.obj n).IsQuasicoherent := by
  have _ : (F.obj.obj n).IsCoherent := F.property.1 n.unop
  exact isQuasicoherent_of_isCoherent _

/-- The direct images `j_*F_n` along the open immersion `j : U ⟶ X` are quasi-coherent. -/
@[sga "6 0 2.5" "special case"]
private theorem isQuasicoherent_pushforwardQCohSystem (T : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen T)) (n : ℕᵒᵖ) :
    ((F.obj ⋙ Scheme.Modules.pushforward T.U.ι).obj n).IsQuasicoherent := by
  have _ := isQuasicoherent_coherentAdicSystem_obj T F n
  exact AlgebraicGeometry.pushforward_isQuasicoherent T.U.ι (F.obj.obj n)

/-- The system of direct images `(j_*F_n)` on `X`, as quasi-coherent modules. -/
private def pushforwardQCohSystem (T : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen T)) :
    ℕᵒᵖ ⥤ Scheme.QuasicoherentModules T.X :=
  ObjectProperty.lift _ (F.obj ⋙ Scheme.Modules.pushforward T.U.ι)
    (isQuasicoherent_pushforwardQCohSystem T F)

/-- Global sections on `X` of the direct image are global sections on `U`, as `A`-modules. -/
private theorem pushforwardQCohSystem_comp_inverse (T : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen T)) :
    pushforwardQCohSystem T F ⋙ (tildeEquiv (R := .of T.A)).inverse =
      globalSectionsSystem T F := rfl

/-- The system `(H⁰(U, F_n)^~)` is isomorphic to the system of direct images `(j_*F_n)`. -/
private def tildeGlobalSectionsSystem_iso_pushforward (T : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen T)) :
    tildeGlobalSectionsSystem T F ≅ pushforwardQCohSystem T F :=
  eqToIso (congrArg (fun G => G ⋙ (tildeEquiv (R := .of T.A)).functor)
      (pushforwardQCohSystem_comp_inverse T F).symm) ≪≫
    Functor.associator (pushforwardQCohSystem T F) (tildeEquiv (R := .of T.A)).inverse
      (tildeEquiv (R := .of T.A)).functor ≪≫
    Functor.isoWhiskerLeft (pushforwardQCohSystem T F) (tildeEquiv (R := .of T.A)).counitIso ≪≫
    (pushforwardQCohSystem T F).rightUnitor

/-! ### Flat base change for the global sections -/

section FlatBaseChange

open Stacks.AlgebraicGeometry.AffinePushforward
open Stacks.AlgebraicGeometry.FlatBaseChangeCohomology

variable (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

private theorem isQuasicoherent_pullback_pushforwardQCohSystem (n : ℕᵒᵖ) :
    (((F.obj ⋙ Scheme.Modules.pushforward S.U.ι) ⋙
      Scheme.Modules.pullback (S.baseChangeMap A')).obj n).IsQuasicoherent := by
  have _ : ((Scheme.Modules.pushforward S.U.ι).obj (F.obj.obj n)).IsQuasicoherent :=
    isQuasicoherent_pushforwardQCohSystem S F n
  exact Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback
    (S.baseChangeMap A') ((Scheme.Modules.pushforward S.U.ι).obj (F.obj.obj n))

private theorem pushforwardQCohSystem_comp_pullback_eq :
    pushforwardQCohSystem S F ⋙ Stacks.Coherent.quasicoherentModulesPullback (S.baseChangeMap A') =
      ObjectProperty.lift _ ((F.obj ⋙ Scheme.Modules.pushforward S.U.ι) ⋙
        Scheme.Modules.pullback (S.baseChangeMap A'))
        (isQuasicoherent_pullback_pushforwardQCohSystem S A' F) := rfl

private theorem pushforwardQCohSystem_baseChangeAdicSystem_eq :
    pushforwardQCohSystem (S.baseChange A') (baseChangeAdicSystem S A' F) =
      ObjectProperty.lift _ ((F.obj ⋙ Scheme.Modules.pullback (S.baseChangeOpenMap A')) ⋙
        Scheme.Modules.pushforward (S.baseChange A').U.ι)
        (isQuasicoherent_pushforwardQCohSystem (S.baseChange A')
          (baseChangeAdicSystem S A' F)) := rfl

variable [Module.Flat S.A A']

/-- For `A → A'` flat, the base-change isomorphisms `f^*j_*F_n ≅ j'_*g^*F_n` of the cartesian
square of `U'` over `U`. -/
private def pullbackPushforwardBaseChangeIso :
    (F.obj ⋙ Scheme.Modules.pushforward S.U.ι) ⋙
        Scheme.Modules.pullback (S.baseChangeMap A') ≅
      (F.obj ⋙ Scheme.Modules.pullback (S.baseChangeOpenMap A')) ⋙
        Scheme.Modules.pushforward (S.baseChange A').U.ι :=
  have hq : ∀ n : ℕᵒᵖ, IsIso ((baseChangeNatTrans
      (S.isPullback_baseChangeOpenMap A').w).app (F.obj.obj n)) := by
    intro n
    have _ := isQuasicoherent_coherentAdicSystem_obj S F n
    exact isIso_baseChangeNatTrans_of_flat (S.isPullback_baseChangeOpenMap A') (F.obj.obj n)
  NatIso.ofComponents (fun n => @asIso _ _ _ _ _ (hq n))
    (fun φ => (baseChangeNatTrans (S.isPullback_baseChangeOpenMap A').w).naturality (F.obj.map φ))

/-- For `A → A'` flat, the system of quasi-coherent sheaves attached to the global sections of
`(F'_n)` on `X'` is the pullback along `f` of the one attached to `(F_n)` on `X`. -/
public theorem nonempty_tildeGlobalSectionsSystem_baseChange_iso :
    Nonempty (tildeGlobalSectionsSystem (S.baseChange A') (baseChangeAdicSystem S A' F) ≅
      tildeGlobalSectionsSystem S F ⋙
        Stacks.Coherent.quasicoherentModulesPullback (S.baseChangeMap A')) :=
  ⟨tildeGlobalSectionsSystem_iso_pushforward (S.baseChange A') (baseChangeAdicSystem S A' F) ≪≫
    eqToIso (pushforwardQCohSystem_baseChangeAdicSystem_eq S A' F) ≪≫
    (Stacks.Coherent.liftObjectPropertyIso
      (isQuasicoherent_pullback_pushforwardQCohSystem S A' F)
      (isQuasicoherent_pushforwardQCohSystem (S.baseChange A') (baseChangeAdicSystem S A' F))
      (pullbackPushforwardBaseChangeIso S A' F)).symm ≪≫
    eqToIso (pushforwardQCohSystem_comp_pullback_eq S A' F).symm ≪≫
    (Functor.isoWhiskerRight (tildeGlobalSectionsSystem_iso_pushforward S F)
      (Stacks.Coherent.quasicoherentModulesPullback (S.baseChangeMap A'))).symm⟩

/-- For `A → A'` flat, if `(G_n)` in `Coh(X, I 𝒪_X)` is pro-isomorphic to `(H⁰(U, F_n)^~)`, then
`(f^*G_n)` is pro-isomorphic to `(H⁰(U', F'_n)^~)`. -/
@[stacks 0EIS "the extension pulls back"]
public theorem nonempty_pullback_extension_iso
    (G : Stacks.Coherent.CoherentAdicSystems (idealOnX S))
    (e : Stacks.Coherent.diagramToPro (tildeGlobalSectionsSystem S F) ≅
      (Stacks.Coherent.coherentAdicToPro S.X (idealOnX S)).obj G) :
    Nonempty (Stacks.Coherent.diagramToPro
        (tildeGlobalSectionsSystem (S.baseChange A') (baseChangeAdicSystem S A' F)) ≅
      (Stacks.Coherent.coherentAdicToPro (S.baseChange A').X (idealOnX (S.baseChange A'))).obj
        (baseChangeCanonicalExtension S A' G)) := by
  obtain ⟨hbase⟩ := nonempty_tildeGlobalSectionsSystem_baseChange_iso S A' F
  exact (Stacks.Coherent.nonempty_diagramToPro_comp_iso
    (Stacks.Coherent.quasicoherentModulesPullback (S.baseChangeMap A'))
    (tildeGlobalSectionsSystem S F) (Stacks.Coherent.quasicoherentDiagram G) e).map
      (Stacks.Coherent.diagramToProMapIso hbase ≪≫ ·)

/-- Let `S` be an algebraization situation: a Noetherian ring `A`
with ideals `I ⊆ 𝔞`, the affine scheme `X = Spec(A)` and the open complement `U = X ∖ V(𝔞)`. Let
`(F_n)` be a coherent `I`-adic system on `U` and let `A → A'` be a flat ring map with `A'`
Noetherian. Put `X' = Spec(A')`, let `U' ⊆ X'` be the inverse image of `U`, let `g : U' ⟶ U` be
the induced morphism and set `(F'_n) = (g^*F_n)`. If `(F_n)` canonically extends to `X`, then
`(F'_n)` canonically extends to `X'`. -/
@[stacks 0EIS "flat base change of the canonical extension"]
public theorem canonicallyExtends_base_change (h : CanonicallyExtends S F) :
    CanonicallyExtends (S.baseChange A') (baseChangeAdicSystem S A' F) := by
  obtain ⟨G, ⟨e⟩⟩ := h
  exact ⟨baseChangeCanonicalExtension S A' G, nonempty_pullback_extension_iso S A' F G e⟩

end FlatBaseChange

end Stacks.Algebraization

end
