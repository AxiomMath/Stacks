module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesCompConjugate
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMateComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardIsoSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleEtaleBaseChangeHFace
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.ExtensionByZeroBaseChangeComparison
public import StacksFrontier.CategoryTheory.Adjunction.MateTransportedAdjunctions
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesCompare

/-!
# The underived base change map for extension by zero

Let

```
T' --u'--> T
|t'        |t
v          v
U  --u-->  Z
```

be a cartesian square of algebraic spaces with `u` étale.  The base change map
`u'_!(t'^*F) ⟶ t^*(u_!F)` of sheaves of modules — the inverse mate, under the adjunctions of
extension by zero, of the identification `u^* ⋙ t'^* ≅ t^* ⋙ u'^*` built from the compositors of
the inverse images of the small étale ringed topoi — is an isomorphism.

## Main definitions

* `AlgebraicGeometry.Space.extensionByZeroBaseChangeModules`: the base change map
  `u'_!(t'^*F) ⟶ t^*(u_!F)` for extension by zero.

## Main results

* `AlgebraicGeometry.Space.isIso_extensionByZeroBaseChangeModules`: for a cartesian square with
  `u` étale, the base change map for extension by zero is an isomorphism.
* `AlgebraicGeometry.Space.modulePullbackAdjunction_eq_transport`: the adjunction of Stacks 03D7 of
  the modules development is that of the morphism of small étale ringed topoi, transported along
  the identifications of the two spellings of the inverse and direct images.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

open _root_.CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {F : Type u₄} [Category.{v₄} F]

/-- Two base change squares of direct images that are built from the same composition
comparisons `ca`, `cb` and comparisons `τa = Ta`, `τb = Tb`, and that differ only by renamings of
their functors along equalities, are related by those renamings. -/
theorem baseChangeSquare_eq_of_eqToIso {Fu' Mu' : D ⥤ C} {Ft Mt : C ⥤ E} {Ft' Mt' : D ⥤ F}
    {Fu Mu : F ⥤ E} {Fa Ma Fb Mb Fca Fcb : D ⥤ E}
    (κu' : Fu' ≅ Mu') (κt : Ft ≅ Mt) (κt' : Ft' ≅ Mt') (κu : Fu ≅ Mu)
    (eu' : Fu' = Mu') (et : Ft = Mt) (et' : Ft' = Mt') (eu : Fu = Mu)
    (hu' : κu' = eqToIso eu') (ht : κt = eqToIso et) (ht' : κt' = eqToIso et')
    (hu : κu = eqToIso eu) (ea : Fa = Ma) (eb : Fb = Mb)
    (τa Ta : Fca ≅ Fa) (τb Tb : Fcb ≅ Fb) (hτa : τa = Ta) (hτb : τb = Tb)
    (ca : Fca ≅ Fu' ⋙ Ft) (cb : Fcb ≅ Ft' ⋙ Fu) (ma : Mu' ⋙ Mt = Fu' ⋙ Ft)
    (mb : Mt' ⋙ Mu = Ft' ⋙ Fu) (eF : Fa = Fb) (eM : Ma = Mb) :
    (τa.symm ≪≫ ca).inv ≫ eqToHom eF ≫ (τb.symm ≪≫ cb).hom =
      whiskerLeft Fu' κt.hom ≫ whiskerRight κu'.hom Mt ≫
        ((eqToIso ma ≪≫ ca.symm ≪≫ Ta ≪≫ eqToIso ea).hom ≫ eqToHom eM ≫
          (eqToIso mb ≪≫ cb.symm ≪≫ Tb ≪≫ eqToIso eb).inv) ≫
        whiskerLeft Mt' κu.inv ≫ whiskerRight κt'.inv Fu := by
  subst hu' ht ht' hu hτa hτb eu' et et' eu ea eb eF
  ext X
  simp

section Conjugates

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {L₁ L₂ L₃ L₄ : A ⥤ B} {R₁ R₂ R₃ R₄ : B ⥤ A}

/-- The conjugate of a composite of three transformations of left adjoints, from the conjugates
of the factors. -/
theorem conjugateEquiv_comp_comp_eq (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
    (adj₄ : L₄ ⊣ R₄) (a : L₄ ⟶ L₃) (b : L₃ ⟶ L₂) (c : L₂ ⟶ L₁) {x : R₁ ⟶ R₂} {y : R₂ ⟶ R₃}
    {z : R₃ ⟶ R₄} (hc : conjugateEquiv adj₁ adj₂ c = x) (hb : conjugateEquiv adj₂ adj₃ b = y)
    (ha : conjugateEquiv adj₃ adj₄ a = z) :
    conjugateEquiv adj₁ adj₄ (a ≫ b ≫ c) = x ≫ y ≫ z := by
  rw [← hc, ← hb, ← ha, conjugateEquiv_comp, conjugateEquiv_comp, Category.assoc]

end Conjugates

section IteratedMates

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {C : Type u₃} [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]
  {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}

/-- **A mate is invertible when its own mate is the inverse mate of an invertible 2-cell.** For a
square of four left adjoints, the mate of `α` across `L₁ ⊣ R₁`, `L₂ ⊣ R₂` is invertible as soon as
the conjugate of `α` is a 2-cell `π` whose inverse mate across `F₂ ⊣ U₂`, `F₁ ⊣ U₁` is
invertible. -/
theorem isIso_mateEquiv_natTrans_of_conjugateEquiv_eq (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₃ : F₁ ⊣ U₁) (adj₄ : F₂ ⊣ U₂) (α : TwoSquare F₁ L₁ L₂ F₂) (π : U₂ ⋙ R₁ ⟶ R₂ ⋙ U₁)
    (h : conjugateEquiv (adj₁.comp adj₄) (adj₃.comp adj₂) α = π)
    (hπ : IsIso ((mateEquiv adj₄ adj₃).symm (TwoSquare.mk _ _ _ _ π)).natTrans) :
    IsIso (mateEquiv adj₁ adj₂ α).natTrans := by
  have key : mateEquiv adj₁ adj₂ α = (mateEquiv adj₄ adj₃).symm (TwoSquare.mk _ _ _ _ π) := by
    rw [Equiv.eq_symm_apply]
    ext X
    rw [← h, ← iterated_mateEquiv_conjugateEquiv]
  rw [key]
  exact hπ

end IteratedMates

end CategoryTheory

namespace AlgebraicGeometry.RingedToposHom

open Stacks.Sheaves.RingedToposModules

universe v₁ u₁ w₁ v₂ u₂ w₂

variable {X : RingedTopos.{v₁, u₁, w₁}} {Y : RingedTopos.{v₂, u₂, w₂}}
  [X.J.HasSheafCompose (forget RingCat.{w₁})]
  [Y.J.HasSheafCompose (forget RingCat.{w₂})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w₂})]

/-- The transport of the direct image of sheaves of modules along an equality of four-field
morphisms of ringed topoi is, on underlying sheaves of sets, the transport along the equality of
their underlying morphisms of topoi. -/
theorem _root_.Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_eqToIso_pushforwardModules_hom_app
    {ψ ψ' : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y} (h : ψ = ψ')
    (ht : ψ.toToposHom = ψ'.toToposHom)
    (N : SheafOfModules.{w₁} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((eqToIso (congrArg (fun φ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y ↦
          Stacks.Sheaves.RingedToposModules.pushforwardModules φ) h)).hom.app N) =
      eqToHom (congrArg (fun T : MorphismOfTopoi X.Topos Y.Topos ↦
        T.pushforward.obj (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N))
          ht) := by
  subst h
  exact (moduleSheafFunctor_map_eqToIso_hom_app rfl N).trans (eqToHom_refl _ _)

/-- The transport of the direct image of sheaves of modules along the equality of the two
four-field readings of a morphism of ringed topoi is the identity on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_eqToIso_toModulesHom_eq_hom_app (f : RingedToposHom X Y)
    (N : SheafOfModules.{w₁} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((eqToIso (congrArg (fun φ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y ↦
          Stacks.Sheaves.RingedToposModules.pushforwardModules φ)
            f.toModulesHom_eq_toRingedToposModulesHom)).hom.app N) =
      𝟙 (f.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) :=
  (moduleSheafFunctor_map_eqToIso_pushforwardModules_hom_app
    f.toModulesHom_eq_toRingedToposModulesHom rfl N).trans (eqToHom_refl _ _)

/-- The direct images of sheaves of modules attached to the two four-field readings of a morphism
of ringed topoi are identified with that of the morphism itself in two ways — through the equality
of the two readings, and directly — and the two agree. -/
theorem eqToIso_trans_pushforwardModulesIso (f : RingedToposHom X Y) :
    eqToIso (congrArg (fun ψ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y ↦
          Stacks.Sheaves.RingedToposModules.pushforwardModules ψ)
          f.toModulesHom_eq_toRingedToposModulesHom) ≪≫ f.pushforwardModulesIso =
      f.toModulesPushforwardIso := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply hom_ext_moduleSheafFunctor
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp,
    moduleSheafFunctor_map_pushforwardModulesIso,
    moduleSheafFunctor_map_eqToIso_toModulesHom_eq_hom_app,
    moduleSheafFunctor_map_toModulesPushforwardIso_hom_app_eq_id]
  show 𝟙 (f.toToposHom.pushforward.obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) ≫
    𝟙 (f.toToposHom.pushforward.obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) = 𝟙 _
  exact Category.id_comp _

/-- A 2-isomorphism of morphisms of ringed topoi and the transport of the direct image of sheaves
of modules along its underlying isomorphism of direct images give the same comparison of direct
images of sheaves of modules. -/
theorem TwoIso.pushforwardModulesIso_eq_pushforwardModulesIsoOfNatIso {φ ψ : RingedToposHom X Y}
    (t : TwoIso φ ψ)
    (he : φ.fSharpRing ≫ Stacks.Sheaves.ToposPullback.pullbackRingSheafMapOfNatTrans Y.J
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) t.e.hom = ψ.fSharpRing) :
    t.pushforwardModulesIso = pushforwardModulesIsoOfNatIso φ ψ t.e he :=
  Iso.ext (NatTrans.ext (funext fun _ ↦ hom_ext_moduleSheafFunctor rfl))

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Spelling

variable {X Y : AlgebraicSpaces B S hS}

/-- The four-field morphism of ringed topoi underlying the derived pullback is that of the modules
development. -/
theorem smallEtaleRingedToposHom_toModulesHom_eq (f : X ⟶ Y) :
    (smallEtaleRingedToposHom B S hS f).toModulesHom = smallEtaleRingedToposModulesHom B S hS f :=
  RingedToposHom.toModulesHom_eq_toRingedToposModulesHom.{u, u + 1, u, u, u + 1, u} _

/-- The adjunction of Stacks 03D7 of a four-field morphism of small étale ringed topoi, with its
right adjoint renamed along `β`, transported along an equality of four-field morphisms. -/
theorem pullbackAdjPushforwardModules_ofNatIsoRight_eq
    {φ φ' : Stacks.Sheaves.RingedToposModules.RingedToposHom (smallEtaleRingedTopos B S hS X)
      (smallEtaleRingedTopos B S hS Y)} (h : φ = φ')
    {R₀ R : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X) ⥤
      SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)}
    (α : Stacks.Sheaves.RingedToposModules.pushforwardModules.{u, u, u, u + 1, u, u + 1} φ ≅ R₀)
    (β : Stacks.Sheaves.RingedToposModules.pushforwardModules.{u, u, u, u + 1, u, u + 1} φ' ≅ R) :
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules φ').ofNatIsoRight β =
      (((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules φ).ofNatIsoRight
          α).ofNatIsoLeft (eqToIso (congrArg
            (fun ψ : Stacks.Sheaves.RingedToposModules.RingedToposHom
            (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y) ↦ ψ.pullbackModules)
              h))).ofNatIsoRight
        (α.symm ≪≫ eqToIso (congrArg (fun ψ : Stacks.Sheaves.RingedToposModules.RingedToposHom
            (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y) ↦
              Stacks.Sheaves.RingedToposModules.pushforwardModules.{u, u, u, u + 1, u, u + 1} ψ)
                h) ≪≫ β) := by
  subst h
  apply Adjunction.ext
  ext M
  simp

/-- The two spellings of the inverse image of modules along a morphism of algebraic spaces. -/
def smallEtaleToposPullbackSpellingIso (f : X ⟶ Y) :
    (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules ≅ modulePullback B S hS f :=
  eqToIso (congrArg (fun ψ : Stacks.Sheaves.RingedToposModules.RingedToposHom
    (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y) ↦ ψ.pullbackModules)
      (smallEtaleRingedToposHom_toModulesHom_eq f))

/-- The two spellings of the direct image of modules along a morphism of algebraic spaces. -/
def smallEtaleToposPushforwardSpellingIso (f : X ⟶ Y) :=
  (smallEtaleRingedToposHom B S hS f).toModulesPushforwardIso.symm ≪≫
    eqToIso (congrArg (fun ψ : Stacks.Sheaves.RingedToposModules.RingedToposHom
      (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y) ↦
        Stacks.Sheaves.RingedToposModules.pushforwardModules.{u, u, u, u + 1, u, u + 1} ψ)
      (smallEtaleRingedToposHom_toModulesHom_eq f)) ≪≫ modulePushforwardIso B S hS f

/-- The identification of the two spellings of the direct image of modules, unfolded. -/
theorem smallEtaleToposPushforwardSpellingIso_eq_trans (f : X ⟶ Y) :
    smallEtaleToposPushforwardSpellingIso f =
      (smallEtaleRingedToposHom B S hS f).toModulesPushforwardIso.symm ≪≫
        ((eqToIso (congrArg (fun ψ : Stacks.Sheaves.RingedToposModules.RingedToposHom
            (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y) ↦
              Stacks.Sheaves.RingedToposModules.pushforwardModules.{u, u, u, u + 1, u, u + 1} ψ)
            (smallEtaleRingedToposHom B S hS f).toModulesHom_eq_toRingedToposModulesHom)) ≪≫
          ((smallEtaleRingedToposHom B S hS f).pushforwardModulesIso ≪≫
            pushforwardModulesIsoModulePushforward B S hS f)) := rfl

private theorem smallEtaleToposPushforwardSpellingIso_eq_aux₁ (f : X ⟶ Y) :
      (smallEtaleRingedToposHom B S hS f).toModulesPushforwardIso.symm ≪≫
        ((eqToIso (congrArg (fun ψ : Stacks.Sheaves.RingedToposModules.RingedToposHom
            (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y) ↦
              Stacks.Sheaves.RingedToposModules.pushforwardModules.{u, u, u, u + 1, u, u + 1} ψ)
            (smallEtaleRingedToposHom B S hS f).toModulesHom_eq_toRingedToposModulesHom)) ≪≫
          ((smallEtaleRingedToposHom B S hS f).pushforwardModulesIso ≪≫
            pushforwardModulesIsoModulePushforward B S hS f)) =
      (smallEtaleRingedToposHom B S hS f).toModulesPushforwardIso.symm ≪≫
        (((eqToIso (congrArg (fun ψ : Stacks.Sheaves.RingedToposModules.RingedToposHom
            (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y) ↦
              Stacks.Sheaves.RingedToposModules.pushforwardModules.{u, u, u, u + 1, u, u + 1} ψ)
            (smallEtaleRingedToposHom B S hS f).toModulesHom_eq_toRingedToposModulesHom)) ≪≫
          (smallEtaleRingedToposHom B S hS f).pushforwardModulesIso) ≪≫
          pushforwardModulesIsoModulePushforward B S hS f) :=
  congrArg ((smallEtaleRingedToposHom B S hS f).toModulesPushforwardIso.symm ≪≫ ·)
    (Iso.trans_assoc _ _ _).symm

private theorem smallEtaleToposPushforwardSpellingIso_eq_aux₂ (f : X ⟶ Y) :
      (smallEtaleRingedToposHom B S hS f).toModulesPushforwardIso.symm ≪≫
        (((eqToIso (congrArg (fun ψ : Stacks.Sheaves.RingedToposModules.RingedToposHom
            (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y) ↦
              Stacks.Sheaves.RingedToposModules.pushforwardModules.{u, u, u, u + 1, u, u + 1} ψ)
            (smallEtaleRingedToposHom B S hS f).toModulesHom_eq_toRingedToposModulesHom)) ≪≫
          (smallEtaleRingedToposHom B S hS f).pushforwardModulesIso) ≪≫
          pushforwardModulesIsoModulePushforward B S hS f) =
      (smallEtaleRingedToposHom B S hS f).toModulesPushforwardIso.symm ≪≫
        ((smallEtaleRingedToposHom B S hS f).toModulesPushforwardIso ≪≫
          pushforwardModulesIsoModulePushforward B S hS f) := by
  have h := RingedToposHom.eqToIso_trans_pushforwardModulesIso (smallEtaleRingedToposHom B S hS f)
  exact congrArg (fun e ↦ (smallEtaleRingedToposHom B S hS f).toModulesPushforwardIso.symm ≪≫
    (e ≪≫ pushforwardModulesIsoModulePushforward B S hS f)) h

private theorem smallEtaleToposPushforwardSpellingIso_eq_aux₃ (f : X ⟶ Y) :
      (smallEtaleRingedToposHom B S hS f).toModulesPushforwardIso.symm ≪≫
          ((smallEtaleRingedToposHom B S hS f).toModulesPushforwardIso ≪≫
            pushforwardModulesIsoModulePushforward B S hS f) =
        pushforwardModulesIsoModulePushforward B S hS f :=
  Iso.symm_self_id_assoc _ _

/-- The identification of the two spellings of the direct image of modules is the component-wise
identification `AlgebraicGeometry.Space.pushforwardModulesIsoModulePushforward`, whose components
are the identity on sections. -/
theorem smallEtaleToposPushforwardSpellingIso_eq (f : X ⟶ Y) :
    smallEtaleToposPushforwardSpellingIso f = pushforwardModulesIsoModulePushforward B S hS f :=
  (smallEtaleToposPushforwardSpellingIso_eq_trans f).trans
    ((smallEtaleToposPushforwardSpellingIso_eq_aux₁ f).trans
      ((smallEtaleToposPushforwardSpellingIso_eq_aux₂ f).trans
        (smallEtaleToposPushforwardSpellingIso_eq_aux₃ f)))

/-- The identification of the two spellings of the direct image of modules is the transport
along their equality. -/
theorem smallEtaleToposPushforwardSpellingIso_eq_eqToIso (f : X ⟶ Y) :
    smallEtaleToposPushforwardSpellingIso f =
      eqToIso (pushforwardModules_eq_modulePushforward B S hS f) :=
  (smallEtaleToposPushforwardSpellingIso_eq f).trans
    (pushforwardModulesIsoModulePushforward_eq_eqToIso B S hS f)

/-- **The adjunction of Stacks 03D7 of the modules development is that of the morphism of small
étale ringed topoi**, transported along the identifications of the two spellings of the inverse
and direct images. -/
theorem modulePullbackAdjunction_eq_transport (f : X ⟶ Y) :
    modulePullbackAdjunction B S hS f =
      ((RingedToposHom.pullbackAdjPushforwardModules
          (smallEtaleRingedToposHom B S hS f)).ofNatIsoLeft
        (smallEtaleToposPullbackSpellingIso f)).ofNatIsoRight
        (smallEtaleToposPushforwardSpellingIso f) :=
  pullbackAdjPushforwardModules_ofNatIsoRight_eq (smallEtaleRingedToposHom_toModulesHom_eq f) _ _

end Spelling

/-- **Stacks 03LX for the base change map of direct images, across the transported adjunctions of
the ringed topoi.**  For a cartesian square with `u` étale, the base change map
`u^*(t_*F) ⟶ t'_*(u'^*F)` of the modules development, read as the inverse mate across the
adjunctions of the morphisms of small étale ringed topoi transported along the identifications of
the two spellings of the inverse and direct images, is an isomorphism. -/
theorem isIso_moduleBaseChangeMap_transport {T T' U Z : AlgebraicSpaces B S hS} (u' : T' ⟶ T)
    (t : T ⟶ Z) (t' : T' ⟶ U)
    (u : U ⟶ Z) (sq : IsPullback u' t' t u) (hu : IsEtale B S hS u.hom) :
    IsIso ((mateEquiv
      ((RingedToposHom.pullbackAdjPushforwardModules
          (smallEtaleRingedToposHom B S hS u')).ofNatIsoLeft
        (smallEtaleToposPullbackSpellingIso u') |>.ofNatIsoRight
        (smallEtaleToposPushforwardSpellingIso u'))
      ((RingedToposHom.pullbackAdjPushforwardModules
          (smallEtaleRingedToposHom B S hS u)).ofNatIsoLeft
        (smallEtaleToposPullbackSpellingIso u) |>.ofNatIsoRight
        (smallEtaleToposPushforwardSpellingIso u))).symm
      (TwoSquare.mk _ _ _ _
        ((modulePushforwardCompIso B S hS u' t).hom ≫
          eqToHom (congrArg (fun k : T' ⟶ Z => modulePushforward B S hS k) sq.w) ≫
          (modulePushforwardCompIso B S hS t' u).inv))).natTrans := by
  rw [← modulePullbackAdjunction_eq_transport, ← modulePullbackAdjunction_eq_transport]
  exact isIso_moduleBaseChangeMap_of_isEtale B S hS u' t' t u sq hu

section Factor

variable {X Y Z : AlgebraicSpaces B S hS}

/-- The identification `g^* ⋙ f^* ≅ (f ≫ g)^*` of inverse images of modules along the morphisms
of small étale ringed topoi. -/
def smallEtaleToposPullbackCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    (smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules ⋙
        (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules ≅
      (smallEtaleRingedToposHom B S hS (f ≫ g)).toModulesHom.pullbackModules :=
  (RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS f)
      (smallEtaleRingedToposHom B S hS g)).symm ≪≫
    (smallEtaleRingedToposHom_compTwoIso B S hS f g).pullbackModulesIso

/-- **The identification of inverse images along a composite is conjugate to that of direct
images**, across the adjunctions of Stacks 03D7. -/
theorem conjugateEquiv_smallEtaleToposPullbackCompIso_hom (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv
      (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS (f ≫ g)))
      ((RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS g)).comp
        (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS f)))
      (smallEtaleToposPullbackCompIso f g).hom =
        (smallEtaleRingedToposHom_compTwoIso B S hS f g).pushforwardModulesIso.inv ≫
          (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f)
            (smallEtaleRingedToposHom B S hS g)).hom :=
  RingedToposHom.conjugateEquiv_pullbackModulesCompIso_inv_comp
    (smallEtaleRingedToposHom B S hS f) (smallEtaleRingedToposHom B S hS g)
    (smallEtaleRingedToposHom_compTwoIso B S hS f g)

/-- The identification `(f ≫ g)_* ≅ f_* ⋙ g_*` of direct images of modules along the morphisms of
small étale ringed topoi. -/
def smallEtaleToposPushforwardCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (smallEtaleRingedToposHom_compTwoIso B S hS f g).pushforwardModulesIso.symm ≪≫
    RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f)
      (smallEtaleRingedToposHom B S hS g)

/-- The conjugate of the inverse of the identification of inverse images along a composite is
the inverse of the identification of direct images. -/
theorem conjugateEquiv_smallEtaleToposPullbackCompIso_inv (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv
      ((RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS g)).comp
        (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS f)))
      (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS (f ≫ g)))
      (smallEtaleToposPullbackCompIso f g).inv =
        (smallEtaleToposPushforwardCompIso f g).inv :=
  Stacks.CategoryTheory.conjugateEquiv_inv_of_hom _ _ (smallEtaleToposPullbackCompIso f g)
    (smallEtaleToposPushforwardCompIso f g) (conjugateEquiv_smallEtaleToposPullbackCompIso_hom f g)

/-- The conjugate of a renaming of the inverse image along an equality of morphisms is the
renaming of the direct image. -/
theorem conjugateEquiv_eqToHom_pullbackModules {k₁ k₂ : X ⟶ Z} (h : k₁ = k₂) :
    conjugateEquiv
      (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS k₂))
      (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS k₁))
      (eqToHom (congrArg (fun m : X ⟶ Z ↦
        (smallEtaleRingedToposHom B S hS m).toModulesHom.pullbackModules) h)) =
      eqToHom (congrArg (fun m : X ⟶ Z ↦
        RingedToposHom.pushforwardModules.{u, u + 1, u, u, u + 1, u}
          (smallEtaleRingedToposHom B S hS m)) h.symm) := by
  subst h
  exact conjugateEquiv_id _

/-- The renaming of the direct image of modules along an equality of morphisms commutes with the
identification of its two spellings. -/
theorem eqToHom_comp_smallEtaleToposPushforwardSpellingIso_hom {k₁ k₂ : X ⟶ Y} (h : k₁ = k₂) :
    eqToHom (congrArg (fun m : X ⟶ Y ↦ RingedToposHom.pushforwardModules.{u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS m)) h) ≫ (smallEtaleToposPushforwardSpellingIso k₂).hom =
      (smallEtaleToposPushforwardSpellingIso k₁).hom ≫
        eqToHom (congrArg (fun m : X ⟶ Y ↦ modulePushforward B S hS m) h) := by
  subst h
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- **The base change square of direct images of the small étale ringed topoi is that of the
modules development**, across the identifications of the two spellings of the direct images: for
a commutative square `u' ≫ t = t' ≫ u` of algebraic spaces, the square
`u'_* ⋙ t_* ⟶ (u' ≫ t)_* = (t' ≫ u)_* ⟶ t'_* ⋙ u_*` of the ringed topoi, built from their
composition comparisons, is the square of `AlgebraicGeometry.Space.modulePushforwardCompIso`
(Stacks 03LU) conjugated by the identifications. -/
theorem smallEtaleToposPushforwardCompIso_square_eq {T T' U W : AlgebraicSpaces B S hS}
    (u' : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ U) (u : U ⟶ W) (h : u' ≫ t = t' ≫ u) :
    (smallEtaleToposPushforwardCompIso u' t).inv ≫
        eqToHom (congrArg (fun m : T' ⟶ W ↦
          RingedToposHom.pushforwardModules.{u, u + 1, u, u, u + 1, u}
            (smallEtaleRingedToposHom B S hS m)) h) ≫
        (smallEtaleToposPushforwardCompIso t' u).hom =
      Functor.whiskerLeft (RingedToposHom.pushforwardModules.{u, u + 1, u, u, u + 1, u}
          (smallEtaleRingedToposHom B S hS u'))
          (smallEtaleToposPushforwardSpellingIso t).hom ≫
        Functor.whiskerRight (smallEtaleToposPushforwardSpellingIso u').hom
          (modulePushforward B S hS t) ≫
        ((modulePushforwardCompIso B S hS u' t).hom ≫
          eqToHom (congrArg (fun k : T' ⟶ W ↦ modulePushforward B S hS k) h) ≫
          (modulePushforwardCompIso B S hS t' u).inv) ≫
        Functor.whiskerLeft (modulePushforward B S hS t')
          (smallEtaleToposPushforwardSpellingIso u).inv ≫
        Functor.whiskerRight (smallEtaleToposPushforwardSpellingIso t').inv
          (RingedToposHom.pushforwardModules.{u, u + 1, u, u, u + 1, u}
            (smallEtaleRingedToposHom B S hS u)) := by
  have hτa := RingedToposHom.TwoIso.pushforwardModulesIso_eq_pushforwardModulesIsoOfNatIso
    (smallEtaleRingedToposHom_compTwoIso B S hS u' t)
    (smallEtaleRingedToposHom_comp_fSharpRing B S hS u' t)
  have hτb := RingedToposHom.TwoIso.pushforwardModulesIso_eq_pushforwardModulesIsoOfNatIso
    (smallEtaleRingedToposHom_compTwoIso B S hS t' u)
    (smallEtaleRingedToposHom_comp_fSharpRing B S hS t' u)
  exact baseChangeSquare_eq_of_eqToIso _ _ _ _ _ _ _ _
    (smallEtaleToposPushforwardSpellingIso_eq_eqToIso u')
    (smallEtaleToposPushforwardSpellingIso_eq_eqToIso t)
    (smallEtaleToposPushforwardSpellingIso_eq_eqToIso t')
    (smallEtaleToposPushforwardSpellingIso_eq_eqToIso u) _ _ _ _ _ _ hτa hτb _ _ _ _ _ _

/-- **Stacks 03LX across the small étale ringed topoi.**  For a cartesian square of algebraic
spaces with `u` étale, the base change map `u^*(t_*F) ⟶ t'_*(u'^*F)` of direct images of the
small étale ringed topoi — the inverse mate, under the adjunctions of Stacks 03D7, of the square
of their composition comparisons — is an isomorphism. -/
theorem isIso_mateEquiv_symm_smallEtaleToposPushforwardCompIso_square
    {T T' U W : AlgebraicSpaces B S hS}
    (u' : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ U) (u : U ⟶ W) (sq : IsPullback u' t' t u)
    (hu : IsEtale B S hS u.hom) :
    IsIso ((mateEquiv
      (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS u'))
      (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS u))).symm
      (TwoSquare.mk _ _ _ _
        ((smallEtaleToposPushforwardCompIso u' t).inv ≫
          eqToHom (congrArg (fun m : T' ⟶ W ↦
            RingedToposHom.pushforwardModules.{u, u + 1, u, u, u + 1, u}
              (smallEtaleRingedToposHom B S hS m)) sq.w) ≫
          (smallEtaleToposPushforwardCompIso t' u).hom))).natTrans := by
  have := isIso_moduleBaseChangeMap_transport u' t t' u sq hu
  exact @Adjunction.isIso_mateEquiv_symm_of_transport _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ (smallEtaleToposPullbackSpellingIso u') (smallEtaleToposPushforwardSpellingIso u')
    (smallEtaleToposPullbackSpellingIso u) (smallEtaleToposPushforwardSpellingIso u)
    (smallEtaleToposPushforwardSpellingIso t) (smallEtaleToposPushforwardSpellingIso t') _ _
    (smallEtaleToposPushforwardCompIso_square_eq u' t t' u sq.w) this

/-- **The square of inverse images of a commutative square is conjugate to the square of direct
images**: for `u' ≫ t = t' ≫ u`, the conjugate of
`u^* ⋙ t'^* ≅ (t' ≫ u)^* = (u' ≫ t)^* ≅ t^* ⋙ u'^*` across the composite adjunctions of
Stacks 03D7 is `u'_* ⋙ t_* ≅ (u' ≫ t)_* = (t' ≫ u)_* ≅ t'_* ⋙ u_*`. -/
theorem conjugateEquiv_smallEtaleToposPullbackCompIso_square {T T' U W : AlgebraicSpaces B S hS}
    (u' : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ U) (u : U ⟶ W) (h : u' ≫ t = t' ≫ u) :
    conjugateEquiv
      ((RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS t)).comp
        (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS u')))
      ((RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS u)).comp
        (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS t')))
      ((smallEtaleToposPullbackCompIso t' u).hom ≫
        eqToHom (congrArg (fun m : T' ⟶ W ↦
          (smallEtaleRingedToposHom B S hS m).toModulesHom.pullbackModules) h.symm) ≫
        (smallEtaleToposPullbackCompIso u' t).inv) =
      (smallEtaleToposPushforwardCompIso u' t).inv ≫
        eqToHom (congrArg (fun m : T' ⟶ W ↦
          RingedToposHom.pushforwardModules.{u, u + 1, u, u, u + 1, u}
            (smallEtaleRingedToposHom B S hS m)) h) ≫
        (smallEtaleToposPushforwardCompIso t' u).hom := by
  have hc := conjugateEquiv_smallEtaleToposPullbackCompIso_inv u' t
  have hb := conjugateEquiv_eqToHom_pullbackModules h.symm
  have ha := conjugateEquiv_smallEtaleToposPullbackCompIso_hom t' u
  exact conjugateEquiv_comp_comp_eq _ _ _ _ _ _ _ hc hb ha

/-- **The base change map of inverse images of a cartesian square with an étale side is
invertible**, for the small étale ringed topoi: the mate `t_* ⋙ u^* ⟶ u'^* ⋙ t'_*` of the square of
inverse images is invertible. -/
theorem isIso_mateEquiv_smallEtaleToposPullbackCompIso_square {T T' U W : AlgebraicSpaces B S hS}
    (u' : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ U) (u : U ⟶ W) (sq : IsPullback u' t' t u)
    (hu : IsEtale B S hS u.hom) :
    IsIso (mateEquiv
      (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS t))
      (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS t'))
      (TwoSquare.mk _ _ _ _ ((smallEtaleToposPullbackCompIso t' u).hom ≫
        eqToHom (congrArg (fun m : T' ⟶ W ↦
          (smallEtaleRingedToposHom B S hS m).toModulesHom.pullbackModules) sq.w.symm) ≫
        (smallEtaleToposPullbackCompIso u' t).inv))).natTrans :=
  isIso_mateEquiv_natTrans_of_conjugateEquiv_eq _ _
    (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS u))
    (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS u')) _ _
    (conjugateEquiv_smallEtaleToposPullbackCompIso_square u' t t' u sq.w)
    (isIso_mateEquiv_symm_smallEtaleToposPushforwardCompIso_square u' t t' u sq hu)

/-- **Extension by zero is left adjoint to the inverse image of modules along an étale morphism**
of algebraic spaces, the inverse image being that of the morphism of small étale ringed topoi:
Stacks 03DJ read through the identification of Stacks 03LW. -/
def etaleLowerShriekToposAdjunction {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) :
    etaleExtensionByZero B S hS f hf ⊣
      (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules :=
  (etaleModuleLowerShriekAdjunction B S hS f hf).ofNatIsoRight
    (pullbackModulesIsoEtaleRestriction B S hS f hf).symm

/-- **The base change map for extension by zero**, `u'_!(t'^*F) ⟶ t^*(u_!F)`, for a commutative
square `u' ≫ t = t' ≫ u` with `u` and `u'` étale: the inverse mate, under the adjunctions of
extension by zero, of the identification `u^* ⋙ t'^* ≅ t^* ⋙ u'^*` of inverse images. -/
def extensionByZeroBaseChangeModules {T T' U W : AlgebraicSpaces B S hS} (u' : T' ⟶ T)
    (t : T ⟶ W) (t' : T' ⟶ U) (u : U ⟶ W) (hu : IsEtale B S hS u.hom)
    (hu' : IsEtale B S hS u'.hom) (h : u' ≫ t = t' ≫ u) :
    (smallEtaleRingedToposHom B S hS t').toModulesHom.pullbackModules ⋙
        etaleExtensionByZero B S hS u' hu' ⟶
      etaleExtensionByZero B S hS u hu ⋙
        (smallEtaleRingedToposHom B S hS t).toModulesHom.pullbackModules :=
  ((mateEquiv (etaleLowerShriekToposAdjunction u hu) (etaleLowerShriekToposAdjunction u' hu')).symm
    (TwoSquare.mk _ _ _ _ ((smallEtaleToposPullbackCompIso t' u).hom ≫
      eqToHom (congrArg (fun m : T' ⟶ W ↦
        (smallEtaleRingedToposHom B S hS m).toModulesHom.pullbackModules) h.symm) ≫
      (smallEtaleToposPullbackCompIso u' t).inv))).natTrans

/-- **Extension by zero commutes with base change** (Stacks 03DJ with 03LX): for a cartesian
square of algebraic spaces with `u` étale, the base change map `u'_!(t'^*F) ⟶ t^*(u_!F)` is an
isomorphism of modules. -/
theorem isIso_extensionByZeroBaseChangeModules {T T' U W : AlgebraicSpaces B S hS}
    (u' : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ U) (u : U ⟶ W) (sq : IsPullback u' t' t u)
    (hu : IsEtale B S hS u.hom) (hu' : IsEtale B S hS u'.hom) :
    IsIso (extensionByZeroBaseChangeModules u' t t' u hu hu' sq.w) :=
  @Adjunction.isIso_mateEquiv_symm_natTrans_of_isIso _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (etaleLowerShriekToposAdjunction u hu) (etaleLowerShriekToposAdjunction u' hu')
    (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS t))
    (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS t')) _
    (isIso_mateEquiv_smallEtaleToposPullbackCompIso_square u' t t' u sq hu)

end Factor

end AlgebraicGeometry.Space
