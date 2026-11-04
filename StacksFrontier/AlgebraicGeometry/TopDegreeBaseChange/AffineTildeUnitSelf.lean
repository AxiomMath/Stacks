module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineTildeCounit

/-!
# The two identifications of the structure sheaf with the tilde of its global sections

On an affine scheme `Z` there are two ways to see the structure sheaf as the module associated
to the ring `Γ(Z, ⊤)` of its own global sections. One is the general identification
`Stacks.Coherent.affineTildeObjSectionsIso` of a quasi-coherent module with the tilde of its
sections, specialised at `𝒪_Z`. The other is a concrete chain of Mathlib isomorphisms:
`AlgebraicGeometry.tildeSelf` identifies `R~` with `𝒪_{Spec R}`, and restriction along
`Z.isoSpec.hom` carries `𝒪_{Spec R}` back to `𝒪_Z`.

This file proves that the two agree.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.affineTildeUnitIso` — the concrete chain.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.affineTildeObjSectionsIso_unitModule` — the two
  identifications agree.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-- The module structure on the sections of a module over a scheme, at the instantiation
`CategoryTheory.SheafOfModules.evaluation` produces.  Instance search does not cross the
`TopCat.Sheaf` definition on its own. -/
private instance moduleEvaluation {X : Scheme.{u}} (M : X.Modules) (U : X.Opensᵒᵖ) :
    Module (X.presheaf.obj U) ((SheafOfModules.evaluation X.ringCatSheaf U).obj M) :=
  inferInstanceAs (Module (X.ringCatSheaf.obj.obj U) (M.val.obj U))

/-- The structure sheaf of an affine scheme `Z` is the module associated to `Γ(Z, ⊤)`, through
Mathlib's `AlgebraicGeometry.tildeSelf` and restriction along `Z.isoSpec.hom`. -/
def affineTildeUnitIso (Z : Scheme.{u}) [IsAffine Z] :
    (Stacks.Coherent.affineTilde Z).obj (ModuleCat.of Γ(Z, ⊤) Γ(Z, ⊤)) ≅ Scheme.unitModule Z :=
  (Scheme.Modules.restrictFunctor Z.isoSpec.hom).mapIso
      (AlgebraicGeometry.tildeSelf (R := CommRingCat.of Γ(Z, ⊤))) ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback Z.isoSpec.hom).app _ ≪≫
    Scheme.Modules.pullbackUnitIso Z.isoSpec.hom

/-! ### Two lemmas about adjunctions

Both are statements about arbitrary adjunctions, where no transparency question arises; this is
why they are stated separately rather than unfolded in place. -/

/-- A morphism is the transpose of its own transpose, in the form the computation below needs: a
morphism `χ` whose image under the left adjoint, followed by the counit, is `φ` is the transpose
of `φ`. -/
private lemma homEquiv_eq {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {X : C} {Y : D} {φ : F.obj X ⟶ Y} {χ : X ⟶ G.obj Y}
    (h : F.map χ ≫ adj.counit.app Y = φ) : adj.homEquiv X Y φ = χ := by
  subst h
  exact (adj.homEquiv X Y).apply_symm_apply χ

/-- **The unit of a composite adjunction, transported along an isomorphism of the right adjoints,
composed with a morphism out of the left adjoint.**  It is the unit of the first adjunction
followed by the transpose, under the second adjunction, of that morphism. -/
private lemma unit_comp_map {C D E : Type*} [Category C] [Category D] [Category E]
    {F₁ : C ⥤ D} {G₁ : D ⥤ C} {F₂ : D ⥤ E} {G₂ : E ⥤ D} {H : E ⥤ C}
    (adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂) (e : G₂ ⋙ G₁ ≅ H) (X : C) (Y : E)
    (φ : (F₁ ⋙ F₂).obj X ⟶ Y) :
    ((adj₁.comp adj₂).ofNatIsoRight e).unit.app X ≫ H.map φ =
      adj₁.unit.app X ≫ G₁.map (adj₂.homEquiv _ _ φ) ≫ e.hom.app Y := by
  have hnat : e.hom.app (F₂.obj (F₁.obj X)) ≫ H.map φ =
      G₁.map (G₂.map φ) ≫ e.hom.app Y := (e.hom.naturality φ).symm
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Adjunction.comp_unit_app, Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc,
    Functor.comp_obj]
  rw [hnat]

/-! ### Restriction maps of sections

Morphisms between two fixed opens are unique, so a restriction map depends only on its source and
its target, and restriction maps compose. -/

/-- A restriction map of sections depends only on its source and its target. -/
private lemma pmap {X : Scheme.{u}} {U V : X.Opensᵒᵖ} (i j : U ⟶ V) (y : Γ(X, U.unop)) :
    X.presheaf.map i y = X.presheaf.map j y :=
  congrArg (fun k => X.presheaf.map k y) (Subsingleton.elim i j)

/-- Restriction maps of sections compose. -/
private lemma pcomp {X : Scheme.{u}} {U V W : X.Opensᵒᵖ} (i : U ⟶ V) (j : V ⟶ W)
    (y : Γ(X, U.unop)) :
    X.presheaf.map j (X.presheaf.map i y) = X.presheaf.map (i ≫ j) y :=
  (ConcreteCategory.congr_hom (X.presheaf.map_comp i j) y).symm

/-- The unit section of the structure sheaf restricts to the unit section. -/
private lemma pone {X : Scheme.{u}} {U V : X.Opensᵒᵖ} (i : U ⟶ V) :
    (Scheme.unitModule X).presheaf.map i (1 : Γ(X, U.unop)) = (1 : Γ(X, V.unop)) :=
  map_one (ConcreteCategory.hom (X.presheaf.map i))

/-! ### The restriction of the structure sheaf along an open immersion -/

/-- `AlgebraicGeometry.Scheme.Modules.restrictUnitIso` acts on sections as
`AlgebraicGeometry.Scheme.Hom.appIso`. -/
private lemma restrictUnitIso_hom_app {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : X.Opens) (x : Γ(Y, f ''ᵁ U)) :
    (Scheme.Modules.restrictUnitIso f).hom.app U x = (f.appIso U).hom x := rfl

/-- The inverse of `AlgebraicGeometry.Scheme.Modules.restrictUnitIso` acts on sections as the
inverse of `AlgebraicGeometry.Scheme.Hom.appIso`. -/
private lemma restrictUnitIso_inv_app {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : X.Opens) (x : Γ(X, U)) :
    (Scheme.Modules.restrictUnitIso f).inv.app U x = (f.appIso U).inv x := rfl

/-- The inverse of `AlgebraicGeometry.Scheme.Hom.appIso` carries `1` to `1`. -/
private lemma appIso_inv_one {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Opens) :
    (f.appIso U).inv (1 : Γ(X, U)) = (1 : Γ(Y, f ''ᵁ U)) :=
  map_one (ConcreteCategory.hom (f.appIso U).inv)

/-- Restricting to the image of a preimage and then transporting along
`AlgebraicGeometry.Scheme.Hom.appIso` is the map on sections of an open immersion. -/
private lemma map_comp_appIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : Y.Opens) :
    Y.presheaf.map (homOfLE (f.image_preimage_le U)).op ≫ (f.appIso (f ⁻¹ᵁ U)).hom =
      f.app U := by
  simp [Scheme.Hom.appIso_hom', ← Scheme.Hom.app_eq_appLE]

/-- `AlgebraicGeometry.Scheme.Modules.unitToPushforwardUnit` acts on sections as the map on
sections of the morphism of schemes. -/
private lemma unitToPushforwardUnit_app {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (x : Γ(Y, U)) :
    (Scheme.Modules.unitToPushforwardUnit f).app U x = f.app U x := rfl

/-- **The comparison of restriction with pullback carries the structure sheaf to the structure
sheaf.**  At the structure sheaf, `Scheme.Modules.restrictFunctorIsoPullback` followed by
`Scheme.Modules.pullbackUnitIso` is `Scheme.Modules.restrictUnitIso`: both sides transpose, along
the restriction--pushforward adjunction, to the canonical map `𝒪_Y ⟶ f_* 𝒪_X`. -/
private lemma restrictFunctorIsoPullback_hom_app_unit_comp_pullbackUnitIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctorIsoPullback f).hom.app (Scheme.unitModule Y) ≫
        (Scheme.Modules.pullbackUnitIso f).hom =
      (Scheme.Modules.restrictUnitIso f).hom := by
  have hunit : (Scheme.Modules.restrictAdjunction f).unit.app (Scheme.unitModule Y) ≫
      (Scheme.Modules.pushforward f).map (Scheme.Modules.restrictUnitIso f).hom =
      Scheme.Modules.unitToPushforwardUnit f := by
    ext U x
    show (Scheme.Modules.restrictUnitIso f).hom.app (f ⁻¹ᵁ U)
        (Y.presheaf.map (homOfLE (f.image_preimage_le U)).op x) =
      (Scheme.Modules.unitToPushforwardUnit f).app U x
    exact ((restrictUnitIso_hom_app f (f ⁻¹ᵁ U) _).trans
      (congr($(map_comp_appIso_hom f U) x))).trans (unitToPushforwardUnit_app f U x).symm
  apply ((Scheme.Modules.restrictAdjunction f).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    Scheme.Modules.restrictFunctorIsoPullback, Adjunction.unit_leftAdjointUniq_hom_app]
  exact (Scheme.Modules.pullbackUnitIso_homEquiv f).trans hunit.symm

/-- `affineTildeUnitIso` is the restriction of the structure sheaf of `Spec Γ(Z, ⊤)` along
`Z.isoSpec.hom`: Mathlib's `AlgebraicGeometry.tildeSelf` is the identity. -/
private lemma affineTildeUnitIso_hom (Z : Scheme.{u}) [IsAffine Z] :
    (affineTildeUnitIso Z).hom = (Scheme.Modules.restrictUnitIso Z.isoSpec.hom).hom := by
  simp only [affineTildeUnitIso, AlgebraicGeometry.tildeSelf]
  exact restrictFunctorIsoPullback_hom_app_unit_comp_pullbackUnitIso Z.isoSpec.hom

/-! ### The two morphisms between an affine scheme and the spectrum of its functions -/

/-- `Z.isoSpec.hom` followed by `(isAffineOpen_top Z).fromSpec` is the identity. -/
private lemma isoSpec_hom_comp_fromSpec (Z : Scheme.{u}) [IsAffine Z] :
    Z.isoSpec.hom ≫ (isAffineOpen_top Z).fromSpec = 𝟙 Z := by
  simpa only [IsAffineOpen.fromSpec_top] using Z.isoSpec.hom_inv_id

/-- An open of an affine scheme is the image of its image in the spectrum of the functions. -/
private lemma eq_image_image (Z : Scheme.{u}) [IsAffine Z] (U : Z.Opens) :
    U = (isAffineOpen_top Z).fromSpec ''ᵁ (Z.isoSpec.hom ''ᵁ U) := by
  simp [IsAffineOpen.fromSpec_top]

/-- The whole of an affine scheme is the image of the whole of the spectrum of its functions. -/
private lemma top_eq_image_top (Z : Scheme.{u}) [IsAffine Z] :
    (⊤ : Z.Opens) = (isAffineOpen_top Z).fromSpec ''ᵁ ⊤ := by
  rw [Scheme.Hom.image_top_eq_opensRange, (isAffineOpen_top Z).opensRange_fromSpec]

/-- **Transporting a section back and forth between an affine scheme and the spectrum of its
functions is the identity.**  Going along `(isAffineOpen_top Z).fromSpec` and restricting is the
map on sections of `Z.isoSpec.hom`. -/
private lemma appIso_inv_restrict (Z : Scheme.{u}) [IsAffine Z] (U : Z.Opens) {V : Z.Opensᵒᵖ}
    (a : op ((isAffineOpen_top Z).fromSpec ''ᵁ (Z.isoSpec.hom ''ᵁ U)) ⟶ V) (b : V ⟶ op U)
    (x : Γ(Spec Γ(Z, ⊤), Z.isoSpec.hom ''ᵁ U)) :
    Z.presheaf.map b (Z.presheaf.map a
        (((isAffineOpen_top Z).fromSpec.appIso (Z.isoSpec.hom ''ᵁ U)).inv x)) =
      (Z.isoSpec.hom.appIso U).hom x := by
  rw [Scheme.Hom.appIso_hom,
    AlgebraicGeometry.IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq Z.isoSpec.hom
      (isAffineOpen_top Z).fromSpec (𝟙 Z) (isoSpec_hom_comp_fromSpec Z).symm
      (Z.isoSpec.hom ''ᵁ U)]
  exact (pcomp a b _).trans ((pmap _ _ _).trans (pcomp _ _ _).symm)

/-- **The counit of `Stacks.Coherent.affineRestrictionEquivalence` at the structure sheaf.**
Precomposed with the restriction of the structure sheaf along `(isAffineOpen_top Z).fromSpec`, it
is the restriction of the structure sheaf along `Z.isoSpec.hom`. -/
private lemma restrictUnitIso_inv_comp_counit (Z : Scheme.{u}) [IsAffine Z] :
    (Scheme.Modules.restrictFunctor Z.isoSpec.hom).map
          (Scheme.Modules.restrictUnitIso (isAffineOpen_top Z).fromSpec).inv ≫
        (Stacks.Coherent.affineRestrictionEquivalence Z).counit.app (Scheme.unitModule Z) =
      (Scheme.Modules.restrictUnitIso Z.isoSpec.hom).hom := by
  ext U x
  show (Scheme.unitModule Z).presheaf.map (eqToHom (show U = (𝟙 Z) ''ᵁ U by simp)).op
      ((Scheme.unitModule Z).presheaf.map (eqToHom (show (𝟙 Z) ''ᵁ U =
            (Z.isoSpec.hom ≫ (isAffineOpen_top Z).fromSpec) ''ᵁ U by
              simpa using eq_image_image Z U)).op
        ((Scheme.unitModule Z).presheaf.map (eqToHom (show
              (Z.isoSpec.hom ≫ (isAffineOpen_top Z).fromSpec) ''ᵁ U =
              (isAffineOpen_top Z).fromSpec ''ᵁ (Z.isoSpec.hom ''ᵁ U) by simp)).op
          (((isAffineOpen_top Z).fromSpec.appIso (Z.isoSpec.hom ''ᵁ U)).inv x))) =
    (Z.isoSpec.hom.appIso U).hom x
  exact (pcomp _ _ _).trans (appIso_inv_restrict Z U _ _ x)

/-! ### The unit isomorphism of the tilde adjunction on an affine scheme -/

/-- `Stacks.Coherent.affineRestrictionSectionsIso` is natural in the module. -/
private lemma affineRestrictionSectionsIso_naturality (Z : Scheme.{u}) [IsAffine Z]
    {M N : Z.Modules} (φ : M ⟶ N) :
    AlgebraicGeometry.moduleSpecΓFunctor.map
          ((Scheme.Modules.restrictFunctor (isAffineOpen_top Z).fromSpec).map φ) ≫
        (Stacks.Coherent.affineRestrictionSectionsIso Z N).hom =
      (Stacks.Coherent.affineRestrictionSectionsIso Z M).hom ≫
        (SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).map φ :=
  ModuleCat.hom_ext (LinearMap.ext fun x =>
    congrArg (fun g => g.hom x) (φ.val.naturality (eqToHom (top_eq_image_top Z)).op).symm)

/-- Global sections over `⊤` of a module on an affine scheme, as an isomorphism of functors with
the global sections of its restriction to the spectrum of the functions.  This is the isomorphism
`Stacks.Coherent.affineTildeAdjunction` transports its right adjoint along. -/
private def sectionsNatIso (Z : Scheme.{u}) [IsAffine Z] :
    Scheme.Modules.restrictFunctor (isAffineOpen_top Z).fromSpec ⋙
        AlgebraicGeometry.moduleSpecΓFunctor ≅
      SheafOfModules.evaluation Z.ringCatSheaf (op ⊤) :=
  NatIso.ofComponents (fun M => Stacks.Coherent.affineRestrictionSectionsIso Z M)
    (fun φ => affineRestrictionSectionsIso_naturality Z φ)

/-- `Stacks.Coherent.affineRestrictionSectionsIso` acts on sections as a restriction map. -/
private lemma affineRestrictionSectionsIso_hom_apply (Z : Scheme.{u}) [IsAffine Z]
    (N : Z.Modules) (x : Γ(N, (isAffineOpen_top Z).fromSpec ''ᵁ ⊤)) :
    (Stacks.Coherent.affineRestrictionSectionsIso Z N).hom.hom x =
      N.presheaf.map (eqToHom (top_eq_image_top Z)).op x := rfl

/-- `AlgebraicGeometry.tilde.toOpen` carries `1` to `1`. -/
private lemma toOpen_one (R : CommRingCat.{u}) :
    AlgebraicGeometry.tilde.toOpen (ModuleCat.of R R) ⊤ (1 : R) =
      (1 : Γ(Spec R, (⊤ : (Spec R).Opens))) :=
  StructureSheaf.const_one ⊤

/-- **The unit of `Stacks.Coherent.affineTildeAdjunction` at `Γ(Z, ⊤)`, followed by the global
sections of the structure-sheaf identification, computed.** -/
private lemma affineTildeSectionsIso_hom_comp (Z : Scheme.{u}) [IsAffine Z] :
    (Stacks.Coherent.affineTildeSectionsIso Z (ModuleCat.of Γ(Z, ⊤) Γ(Z, ⊤))).hom ≫
        (SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).map
          (Scheme.Modules.restrictUnitIso Z.isoSpec.hom).hom =
      AlgebraicGeometry.tilde.adjunction.unit.app (ModuleCat.of Γ(Z, ⊤) Γ(Z, ⊤)) ≫
        AlgebraicGeometry.moduleSpecΓFunctor.map
            (Scheme.Modules.restrictUnitIso (isAffineOpen_top Z).fromSpec).inv ≫
          (sectionsNatIso Z).hom.app (Scheme.unitModule Z) := by
  refine Eq.trans (unit_comp_map AlgebraicGeometry.tilde.adjunction
    (Stacks.Coherent.affineRestrictionEquivalence Z).toAdjunction (sectionsNatIso Z)
    (ModuleCat.of Γ(Z, ⊤) Γ(Z, ⊤)) (Scheme.unitModule Z)
    (Scheme.Modules.restrictUnitIso Z.isoSpec.hom).hom) ?_
  exact congrArg (fun k =>
      AlgebraicGeometry.tilde.adjunction.unit.app (ModuleCat.of Γ(Z, ⊤) Γ(Z, ⊤)) ≫
        AlgebraicGeometry.moduleSpecΓFunctor.map k ≫
          (sectionsNatIso Z).hom.app (Scheme.unitModule Z))
    (homEquiv_eq (Stacks.Coherent.affineRestrictionEquivalence Z).toAdjunction
      (restrictUnitIso_inv_comp_counit Z))

/-- **The global sections of the structure-sheaf identification invert the unit.** -/
private lemma affineTildeSectionsIso_hom_comp_eq_id (Z : Scheme.{u}) [IsAffine Z] :
    (Stacks.Coherent.affineTildeSectionsIso Z (ModuleCat.of Γ(Z, ⊤) Γ(Z, ⊤))).hom ≫
        (SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).map
          (Scheme.Modules.restrictUnitIso Z.isoSpec.hom).hom =
      𝟙 (ModuleCat.of Γ(Z, ⊤) Γ(Z, ⊤)) := by
  have h1 : AlgebraicGeometry.moduleSpecΓFunctor.map
        (Scheme.Modules.restrictUnitIso (isAffineOpen_top Z).fromSpec).inv
        (1 : Γ(Spec Γ(Z, ⊤), (⊤ : (Spec Γ(Z, ⊤)).Opens))) =
      (1 : Γ(Z, (isAffineOpen_top Z).fromSpec ''ᵁ ⊤)) :=
    (restrictUnitIso_inv_app (isAffineOpen_top Z).fromSpec ⊤ 1).trans
      (appIso_inv_one (isAffineOpen_top Z).fromSpec ⊤)
  have h2 : (Stacks.Coherent.affineRestrictionSectionsIso Z (Scheme.unitModule Z)).hom.hom
        (1 : Γ(Z, (isAffineOpen_top Z).fromSpec ''ᵁ ⊤)) = (1 : Γ(Z, ⊤)) :=
    (affineRestrictionSectionsIso_hom_apply Z (Scheme.unitModule Z)
      (1 : Γ(Z, (isAffineOpen_top Z).fromSpec ''ᵁ ⊤))).trans (pone _)
  refine (affineTildeSectionsIso_hom_comp Z).trans (ModuleCat.hom_ext (LinearMap.ext_ring ?_))
  exact (congrArg
      (fun y => (Stacks.Coherent.affineRestrictionSectionsIso Z (Scheme.unitModule Z)).hom.hom y)
      ((congrArg (fun y => AlgebraicGeometry.moduleSpecΓFunctor.map
          (Scheme.Modules.restrictUnitIso (isAffineOpen_top Z).fromSpec).inv y)
        (toOpen_one Γ(Z, ⊤))).trans h1)).trans h2

/-- **The two identifications of the structure sheaf of an affine scheme with the module
associated to its ring of global sections agree.** -/
theorem affineTildeObjSectionsIso_unitModule (Z : Scheme.{u}) [IsAffine Z] :
    Stacks.Coherent.affineTildeObjSectionsIso Z (Scheme.unitModule Z) inferInstance =
      affineTildeUnitIso Z := by
  have hqc : ((Stacks.Coherent.affineTilde Z).obj
      ((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).obj
        (Scheme.unitModule Z))).IsQuasicoherent :=
    Stacks.Coherent.affineTilde_quasicoherent Z _
  refine Iso.ext (Stacks.Coherent.affineQuasicoherentHom_ext ?_)
  refine Eq.trans
    (Stacks.Coherent.evaluation_map_affineTildeObjSectionsIso_hom Z _ inferInstance) ?_
  refine Eq.trans ?_ ((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤)).congr_map
    (affineTildeUnitIso_hom Z).symm)
  exact ((Stacks.Coherent.affineTildeSectionsIso Z
    (ModuleCat.of Γ(Z, ⊤) Γ(Z, ⊤))).hom_comp_eq_id.mp
      (affineTildeSectionsIso_hom_comp_eq_id Z)).symm

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
