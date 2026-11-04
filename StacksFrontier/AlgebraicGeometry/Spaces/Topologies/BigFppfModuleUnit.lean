module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientRestrictionConservative
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.LocalizedPullbackMateUnit
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfModuleHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleAffineSchemesOver

/-!
# The unit of `a_X^* ⊣ a_{X,*}` on quasi-coherent modules

Let `f : X ⟶ Y` be a morphism of ringed sites and `G` a sheaf of modules on `Y`. Invertibility of
the unit `G ⟶ f_*f^*G` is local: it may be checked on the localized units over a family covering
the final object, or on components at the objects of a cover-dense family. A component at an
object `t` over `V` is invertible when `G|_V` is `L_s M` for a fully faithful left adjoint `L_s`
of sections over `t` and the sections over `u(t)` have a fully faithful left adjoint as well.

For the morphism `a_X : ((Spaces/X)_fppf, 𝒪) ⟶ (X_{spaces,étale}, 𝒪_X)` of Stacks 0DGM these
inputs are the sheaves `M^a` attached to modules over the ring of an affine object, on the big
fppf slice and on the affine schemes étale over an object of the spaces-étale site. Hence the
unit `𝓕 ⟶ a_{X,*}a_X^*𝓕` is an isomorphism for every quasi-coherent `𝒪_X`-module `𝓕`: the
`a_X` half of Stacks 0DGN (6).

## Main results

* `AlgebraicGeometry.RingedSite.Hom.isIso_unit_app_of_coversTop`: the unit is invertible as soon
  as the localized units are, over a family covering the final object.
* `AlgebraicGeometry.RingedSite.Hom.isIso_unit_val_app_of_fullyFaithful`: a component of the unit
  is invertible when both slices have fully faithful left adjoints of sections.
* `AlgebraicGeometry.BigFppfSpaceSite.isIso_unit_app_of_isQuasicoherentOnSite`: **the unit
  `𝓕 ⟶ a_{X,*}a_X^*𝓕` is an isomorphism** for a quasi-coherent `𝒪_X`-module `𝓕`.

## References

* [Stacks Project, Tag 0DGN](https://stacks.math.columbia.edu/tag/0DGN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.AlgebraicGeometry.QcohRestrictEquiv

universe v₁ v₂ u₁ u₂ v w

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  [Functor.IsContinuous F J K] {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}}

/-- A component of `φ` is invertible as soon as the corresponding component of its pushforward
along a site functor is. -/
theorem isIso_val_app_of_isIso_pushforward_val_app
    (ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
    {M N : SheafOfModules.{v} R} (φ : M ⟶ N) (W : Cᵒᵖ)
    (h : IsIso (((SheafOfModules.pushforward.{v} ψ).map φ).val.app W)) :
    IsIso (φ.val.app (op (F.obj W.unop))) := by
  have h2 : IsIso ((forget₂ (ModuleCat.{v} (S.obj.obj W)) AddCommGrpCat.{v}).map
      (((SheafOfModules.pushforward.{v} ψ).map φ).val.app W)) :=
    @Functor.map_isIso _ _ _ _ _ _ (forget₂ (ModuleCat.{v} (S.obj.obj W)) AddCommGrpCat.{v}) _ h
  have h3 : IsIso ((forget₂ (ModuleCat.{v} (R.obj.obj (op (F.obj W.unop))))
      AddCommGrpCat.{v}).map (φ.val.app (op (F.obj W.unop)))) := h2
  exact @isIso_of_reflects_iso _ _ _ _ _ _ (φ.val.app (op (F.obj W.unop)))
    (forget₂ (ModuleCat.{v} (R.obj.obj (op (F.obj W.unop)))) AddCommGrpCat.{v}) h3 inferInstance

/-- **A morphism of sheaves of modules is invertible as soon as its components at the objects
of a cover-dense family are.** -/
theorem isIso_of_isIso_val_app_of_isCoverDense {E : Type*} [Category E] (G : E ⥤ D)
    [G.IsCoverDense K] [G.IsLocallyFull K] {M N : SheafOfModules.{v} R} (φ : M ⟶ N)
    (h : ∀ U : E, IsIso (φ.val.app (op (G.obj U)))) : IsIso φ := by
  have hs : IsIso ((SheafOfModules.toSheaf R).map φ) := by
    refine Functor.IsCoverDense.iso_of_restrict_iso (G := G) _ ?_
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun U ↦ isIso_toSheaf_map_hom_app φ _ (h U.unop)
  exact @isIso_of_reflects_iso _ _ _ _ _ _ φ (SheafOfModules.toSheaf R) hs inferInstance

end Stacks.AlgebraicGeometry.QcohRestrictEquiv

namespace AlgebraicGeometry.RingedSite

/-- If `a ≫ b = c ≫ d`, `b` is invertible and `c`, `d` are invertible under `F`, so is
`F.map a`. -/
private theorem isIso_map_of_comp_eq {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {P Q R T : A} {a : P ⟶ Q} {b : Q ⟶ T} {c : P ⟶ R} {d : R ⟶ T} (h : a ≫ b = c ≫ d)
    (hb : IsIso b)
    (hc : IsIso (F.map c)) (hd : IsIso (F.map d)) : IsIso (F.map a) :=
  IsIso.of_isIso_fac_right (g := F.map a) (f := F.map b) (h := F.map c ≫ F.map d)
    (by rw [← F.map_comp, ← F.map_comp, h])

universe u

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The unit of `f^* ⊣ f_*` is invertible as soon as the localized units are**, over a family
covering the final object. -/
theorem Hom.isIso_unit_app_of_coversTop {ι : Type*} {V : ι → Y.C} (hV : Y.J.CoversTop V)
    [∀ i, HasWeakSheafify (X.J.over (f.u.obj (V i))) AddCommGrpCat.{u}]
    [∀ i, (X.J.over (f.u.obj (V i))).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))
    (h : ∀ i, IsIso ((RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
        (f.localized (V i)).ringedToposHom).unit.app (G.over (V i)))) :
    IsIso (f.toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.unit.app G) := by
  rw [← f.isIso_pullbackPushforwardAdjunctionTopos_unit_app_iff]
  exact Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over hV _
    (fun i ↦ (f.isIso_overRestrictionModules_map_unit_iff (V i) G).2 (h i))

variable (V : Y.C) [HasWeakSheafify (X.J.over (f.u.obj V)) AddCommGrpCat.{u}]
  [(X.J.over (f.u.obj V)).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A component of the unit of `f^* ⊣ f_*` at an object over `V` is invertible as soon as the
component of the localized unit is**. -/
theorem Hom.isIso_unit_val_app_of_isIso_localized
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))
    (t : Over V)
    (h : IsIso ((SheafOfModules.evaluation.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over V)
        (Opposite.op t)).map
      ((RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
        (f.localized V).ringedToposHom).unit.app ((Y.overRestrictionModules V).obj G)))) :
    IsIso (((RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
      f.ringedToposHom).unit.app G).val.app (Opposite.op t.left)) := by
  let ev := SheafOfModules.evaluation.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over V)
    (Opposite.op t)
  have := f.isIso_localizedPullbackMate V
  let m := asIso ((f.localizedPullbackMate V).natTrans.app G)
  exact Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_isIso_pushforward_val_app
    (𝟙 (((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)).over V)) _ (Opposite.op t)
    (isIso_map_of_comp_eq ev (f.overRestrictionModules_map_unit_comp V G)
      (f.isIso_localizedPushforwardSquare_app V _) h
      (ev.mapIso ((f.localized V).ringedToposHom.pushforwardModules.mapIso m)).isIso_hom)

/-- **A component of the unit of `f^* ⊣ f_*` at an object `t` over `V` is invertible** when
`G|_V` is of the form `L_s M` for a fully faithful left adjoint `L_s` of sections over `t`, and
sections over `u(t)` on the source slice have a fully faithful left adjoint `L_b`, compatibly
with the direct image. -/
theorem Hom.isIso_unit_val_app_of_fullyFaithful
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (t : Over V)
    {Ls : ModuleCat.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over V).obj.obj
        (Opposite.op t)) ⥤
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over V)}
    (adjS : Ls ⊣ SheafOfModules.evaluation.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over V)
      (Opposite.op t))
    (hLs : Ls.FullyFaithful)
    {Lb : ModuleCat.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (f.u.obj V)).obj.obj
        (Opposite.op ((Over.post f.u).obj t))) ⥤
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (f.u.obj V))}
    (adjB : Lb ⊣ SheafOfModules.evaluation.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (f.u.obj V))
      (Opposite.op ((Over.post f.u).obj t)))
    (hLb : Lb.FullyFaithful)
    (E : ModuleCat.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (f.u.obj V)).obj.obj
        (Opposite.op ((Over.post f.u).obj t))) ≌
      ModuleCat.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over V).obj.obj (Opposite.op t)))
    (e : (f.localized V).toRingedToposSiteHom.pushforwardTopos ⋙
        SheafOfModules.evaluation.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over V)
          (Opposite.op t) ≅
      SheafOfModules.evaluation.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (f.u.obj V))
        (Opposite.op ((Over.post f.u).obj t)) ⋙ E.functor)
    (M : ModuleCat.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over V).obj.obj
      (Opposite.op t)))
    (i : G.over V ≅ Ls.obj M) {W : Y.C} (j : t.left ≅ W) :
    IsIso (((RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
      f.ringedToposHom).unit.app G).val.app (Opposite.op W)) := by
  let ev := SheafOfModules.evaluation.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over V)
    (Opposite.op t)
  let g := (f.localized V).ringedToposHom
  let adj := RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u} g
  have h := Adjunction.isIso_map_unit_app_of_fullyFaithful adj adjS hLs adjB hLb E
    (Functor.isoWhiskerRight (f.localized V).pushforwardToposIso ev ≪≫ e) M
  exact Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_iso _ j
    (f.isIso_unit_val_app_of_isIso_localized V G t
      (isIso_map_of_comp_eq ev (adj.unit.naturality i.hom).symm
        ((g.toModulesHom.pullbackModules ⋙ g.pushforwardModules).mapIso i).isIso_hom
        (ev.mapIso i).isIso_hom h))

omit [HasWeakSheafify (X.J.over (f.u.obj V)) AddCommGrpCat.{u}]
  [(X.J.over (f.u.obj V)).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The unit of `f^* ⊣ f_*` at `G` is invertible as soon as its components at the objects of a
cover-dense family are.** -/
theorem Hom.isIso_pullbackPushforwardAdjunctionTopos_unit_app_of_isCoverDense
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) {E : Type*} [Category E]
    (ι : E ⥤ Y.C)
    [ι.IsCoverDense Y.J] [ι.IsLocallyFull Y.J]
    (h : ∀ U : E, IsIso (((RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
      f.ringedToposHom).unit.app G).val.app (Opposite.op (ι.obj U)))) :
    IsIso (f.toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.unit.app G) := by
  rw [← f.isIso_pullbackPushforwardAdjunctionTopos_unit_app_iff]
  exact Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_val_app_of_isCoverDense ι _ h

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.BigFppfSpaceSite

universe u

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {X : T.Spaces}
  {W : Space.SpacesEtale T.schemeSite S T.scheme_mem X}

open EtaleAffineSchemesOver in
/-- **The unit `𝓕 ⟶ a_{X,*}a_X^*𝓕` is invertible on sections over an affine object over which
`𝓕` has a global presentation.** -/
theorem isIso_unit_val_app_of_hasGlobalPresentation
    (F : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O))
    (hW : Space.SpacesEtale.IsAffineScheme T.schemeSite S T.scheme_mem X W)
    (hF : (F.over W).HasGlobalPresentation) :
    IsIso (((RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
        (fppfToSpacesEtaleRingedSiteHom T X).ringedToposHom).unit.app F).val.app (op W)) := by
  obtain ⟨V₀, hV₀, ⟨e⟩⟩ := hW
  obtain ⟨p⟩ := SheafOfModules.HasGlobalPresentation.nonempty_presentation.{u + 1, u + 1, u + 1} hF
  let hs := baseChangeIsSheaf V₀ hV₀ e
  let hb := AffineSchemesOver.baseChangeIsSheaf V₀ hV₀ e
  obtain ⟨M, ⟨i⟩⟩ := Stacks.DenseSubsiteBaseChange.exists_iso_associatedSheaf_of_presentation
    hs (isTerminal_toSmallSlice_ofIso V₀ hV₀ e) p
  let f := fppfToSpacesEtaleRingedSiteHom T X
  let t := (toSmallSlice W).obj (ofIso V₀ hV₀ e)
  let ψ : (ringPresheaf (W := W)).obj (op (ofIso V₀ hV₀ e)) ≃+*
      (AffineSchemesOver.ringPresheaf (T := T) (V := W.obj)).obj
        (op (AffineSchemesOver.ofIso V₀ hV₀ e)) := RingEquiv.refl _
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv ψ
  let e₂ : (f.localized W).toRingedToposSiteHom.pushforwardTopos ⋙
      SheafOfModules.evaluation _ (op t) ≅
      SheafOfModules.evaluation _ (op ((AffineSchemesOver.toSlice T W.obj).obj
        (AffineSchemesOver.ofIso V₀ hV₀ e))) ⋙ E.functor :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)
  exact f.isIso_unit_val_app_of_fullyFaithful W F t
    (Stacks.DenseSubsiteBaseChange.associatedSheafAdj hs)
    (Stacks.DenseSubsiteBaseChange.associatedSheafFullyFaithful hs)
    (Stacks.DenseSubsiteBaseChange.associatedSheafAdj hb)
    (Stacks.DenseSubsiteBaseChange.associatedSheafFullyFaithful hb) E e₂ M i
    (ObjectProperty.isoMk _ (Over.isoMk (f := Over.mk (e.hom ≫ W.obj.hom)) (g := W.obj) e rfl))

/-- The objects of the spaces-étale site of `X` represented by an affine scheme over which a
module has a global presentation. -/
def IsPresentedAffine
    (F : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O)) :
    ObjectProperty (Space.SpacesEtale T.schemeSite S T.scheme_mem X) :=
  fun W ↦ presentedAffinePresieve F W (𝟙 W)

/-- For a quasi-coherent module, the affine objects over which it has a global presentation are
cover-dense in the spaces-étale site of `X`. -/
instance isCoverDense_isPresentedAffine
    (F : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O))
    [F.IsQuasicoherentOnSite] :
    (IsPresentedAffine F).ι.IsCoverDense
      (Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X) where
  is_cover U := by
    refine GrothendieckTopology.superset_covering _ ?_ (generate_presentedAffinePresieve_mem F U)
    rw [Sieve.generate_le_iff]
    rintro Z g hg
    exact ⟨⟨⟨Z, hg⟩, 𝟙 _, g, Category.id_comp _⟩⟩

/-- **Stacks 0DGN (6), the `a_X` half: the unit `𝓕 ⟶ a_{X,*}a_X^*𝓕` is an isomorphism** for a
quasi-coherent `𝒪_X`-module `𝓕` on the spaces-étale site of `X`. -/
theorem isIso_unit_app_of_isQuasicoherentOnSite
    (F : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O))
    [F.IsQuasicoherentOnSite] :
    IsIso ((fppfToSpacesEtaleRingedSiteHom T
      X).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.unit.app F) :=
  RingedSite.Hom.isIso_pullbackPushforwardAdjunctionTopos_unit_app_of_isCoverDense
    (fppfToSpacesEtaleRingedSiteHom T X) F (IsPresentedAffine F).ι
    (fun W ↦ isIso_unit_val_app_of_hasGlobalPresentation F W.property.1 W.property.2)

end AlgebraicGeometry.BigFppfSpaceSite
