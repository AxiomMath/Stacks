module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ObjectwiseFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification
import StacksCore.Tactic.StacksAttribute

/-!
# Sheaves of modules over a constant sheaf of rings

Let `(C, J)` be a site and `R` a commutative ring. A presheaf of `R`-modules on `C` is the same
thing as a presheaf of modules over the constant presheaf of rings with value `R`, and
sheafifying the latter over a sheaf of rings presenting the constant presheaf of rings turns a
sheaf of `R`-modules into a sheaf of modules over that sheaf of rings. This file builds that
bridge and transports the two flatness criteria of Stacks 03ES and 03ET across it: a sheaf of
`R`-modules whose sections over every object form a flat `R`-module becomes a flat sheaf of
modules.

## Main definitions

* `Stacks.ConstantSheaf.constantRingPresheaf`: the constant presheaf of commutative rings.
* `Stacks.ConstantSheaf.ofConstantRingPresheaf` and
  `Stacks.ConstantSheaf.constantRingPresheafOfModules`: a presheaf of `R`-modules read as a
  presheaf of modules over `constantRingPresheaf`, and the functor doing so.
* `Stacks.ConstantSheaf.constantRingSheaf` and `Stacks.ConstantSheaf.constantRingSheafMap`: the
  constant sheaf of commutative rings and the canonical locally bijective comparison from the
  constant presheaf of rings to it.
* `Stacks.ConstantSheaf.toConstantRingPresheaf` and
  `Stacks.ConstantSheaf.constantRingPresheafOfModulesInverse`: the inverse reading, and the
  functor doing it; `Stacks.ConstantSheaf.constantRingPresheafEquivalence` packages the two
  readings as an equivalence of categories whose unit and counit are identities.
* `Stacks.ConstantSheaf.moduleSheafOfConstantRing`: a sheaf of modules over the sheaf of rings,
  read back as a sheaf of `R`-modules; the right adjoint of the bridge.
* `Stacks.ConstantSheaf.ringAsModuleSheaf`: the sheaf of rings read as a sheaf of `R`-modules.
* `Stacks.ConstantSheaf.constantModuleToUnit`: the map to the structure sheaf induced by an
  `R`-linear map `M ⟶ R`; for an ideal `I` and its inclusion this exhibits `I̲` as a sheaf of
  ideals of the sheaf of rings.
* `Stacks.ConstantSheaf.sheafOfModulesOfConstantRingFunctor` and
  `Stacks.ConstantSheaf.sheafOfModulesOfConstantRing`: the functor reading a sheaf of
  `R`-modules as a sheaf of modules over a sheaf of rings presenting the constant presheaf of
  rings, and its value on a sheaf; `Stacks.ConstantSheaf.sheafOfModulesOfConstantRingMap` is its
  value on a morphism.

## Main results

* `Stacks.ConstantSheaf.sheafOfModulesOfConstantRingAdjunction`: **the bridge is a left
  adjoint**, with `Stacks.ConstantSheaf.moduleSheafOfConstantRing` as its right adjoint; hence
  it preserves colimits, which is
  `Stacks.ConstantSheaf.preservesColimits_sheafOfModulesOfConstantRingFunctor`.
* `Stacks.PresheafOfModules.isIso_sheafification_map`: sheafification of presheaves of modules
  inverts the locally bijective morphisms.
* `Stacks.ConstantSheaf.presheafOfConstantRingPresheafIso`: the presheaf of abelian groups
  underlying `ofConstantRingPresheaf F` is the one underlying `F`.
* `Stacks.ConstantSheaf.sheafOfModulesOfConstantRingIso`: the sheaf of abelian groups underlying
  `sheafOfModulesOfConstantRing J a F` is the one underlying `F`; so the bridge does not change
  the sections.
* `Stacks.ConstantSheaf.isFlat_ofConstantRingPresheaf`: by Stacks 03ES, a presheaf of
  `R`-modules with flat sections is flat over the constant presheaf of rings.
* `Stacks.ConstantSheaf.isFlat_sheafOfModulesOfConstantRing`: by Stacks 03ET, a sheaf of
  `R`-modules with flat sections is flat over the sheaf of rings.

## Implementation notes

The constant presheaf of rings has identity restriction maps, so the restriction maps of a
presheaf of modules over it are honest `R`-linear maps rather than semilinear ones; this is why
`ofConstantRingPresheaf` can take the restriction maps of `F` unchanged.

`ofConstantRingPresheaf` and `toConstantRingPresheaf` are mutually inverse on the nose, which is
what lets `constantModuleToUnit` be assembled from the sheafification counit: the bridge applied
to `ringAsModuleSheaf` is literally the sheafification of the restriction of scalars of the
structure sheaf, so the counit is a map out of it.

The sheaf-level statements are phrased for an arbitrary sheaf of rings `Osharp` equipped with a
locally bijective comparison `a` from the constant presheaf of rings, which is the form in which
Stacks 03ET is available. `constantRingSheafMap` exhibits the constant sheaf of rings as such an
`Osharp`, so the generality is not vacuous.

## References

* [Stacks Project, Tag 03ES](https://stacks.math.columbia.edu/tag/03ES)
* [Stacks Project, Tag 03ET](https://stacks.math.columbia.edu/tag/03ET)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w

namespace Stacks.PresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{w}} {R : Sheaf J RingCat.{w}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- Sheafification of presheaves of modules inverts a morphism whose underlying morphism of
presheaves of abelian groups is locally bijective: the sheafification of such a morphism is an
isomorphism of sheaves of modules.

A morphism of sheaves of modules is an isomorphism as soon as the underlying morphism of sheaves
of abelian groups is one, and there the statement is the defining property of the sheafification
of abelian presheaves, `CategoryTheory.GrothendieckTopology.W`. -/
theorem isIso_sheafification_map {P Q : PresheafOfModules.{w} R₀} (f : P ⟶ Q)
    [Presheaf.IsLocallyInjective J ((_root_.PresheafOfModules.toPresheaf R₀).map f)]
    [Presheaf.IsLocallySurjective J ((_root_.PresheafOfModules.toPresheaf R₀).map f)] :
    IsIso ((_root_.PresheafOfModules.sheafification α).map f) := by
  have h : IsIso ((SheafOfModules.toSheaf R).map
      ((_root_.PresheafOfModules.sheafification α).map f)) := by
    have h2 : (SheafOfModules.toSheaf R).map
          ((_root_.PresheafOfModules.sheafification α).map f) =
        (presheafToSheaf J AddCommGrpCat.{w}).map
          ((_root_.PresheafOfModules.toPresheaf R₀).map f) := rfl
    rw [h2]
    exact (J.W_iff _).1 (J.W_of_isLocallyBijective _)
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf R)

end Stacks.PresheafOfModules

namespace Stacks.ConstantSheaf

open AlgebraicGeometry.SheafOfModules (ringPresheaf)

variable (C : Type u) [Category.{v} C] (R : Type w) [CommRing R]

/-- The constant presheaf of commutative rings with value `R`. -/
abbrev constantRingPresheaf : Cᵒᵖ ⥤ CommRingCat.{w} :=
  (Functor.const Cᵒᵖ).obj (CommRingCat.of R)

variable {C R}

/-- A presheaf of `R`-modules, read as a presheaf of modules over the constant presheaf of
commutative rings with value `R`. The restriction maps of the constant presheaf of rings are
identities, so the restriction maps of `F` can be used unchanged. -/
def ofConstantRingPresheaf (F : Cᵒᵖ ⥤ ModuleCat.{w} R) :
    PresheafOfModules.{w} (ringPresheaf (constantRingPresheaf C R)) where
  obj := F.obj
  map f := F.map f
  map_id U := by
    ext x
    exact congrArg (fun g : F.obj U ⟶ F.obj U => g.hom x) (F.map_id U)
  map_comp f g := by
    ext x
    exact congrArg (fun g : _ ⟶ _ => ModuleCat.Hom.hom g x) (F.map_comp f g)

/-- The module of sections of `ofConstantRingPresheaf F` over `U` is that of `F`. -/
@[simp]
theorem ofConstantRingPresheaf_obj (F : Cᵒᵖ ⥤ ModuleCat.{w} R) (U : Cᵒᵖ) :
    (ofConstantRingPresheaf F).obj U = F.obj U :=
  rfl

/-- The functor reading a presheaf of `R`-modules as a presheaf of modules over the constant
presheaf of commutative rings with value `R`. -/
def constantRingPresheafOfModules (C : Type u) [Category.{v} C] (R : Type w) [CommRing R] :
    (Cᵒᵖ ⥤ ModuleCat.{w} R) ⥤ PresheafOfModules.{w} (ringPresheaf (constantRingPresheaf C R)) where
  obj F := ofConstantRingPresheaf F
  map {F G} φ :=
    { app := fun U => φ.app U
      naturality := by
        intro U V f
        ext x
        exact congrArg (fun g : F.obj U ⟶ G.obj V => ModuleCat.Hom.hom g x) (φ.naturality f) }
  map_id F := by ext U x; rfl
  map_comp φ ψ := by ext U x; rfl

/-- A presheaf of modules over the constant presheaf of commutative rings with value `R`, read
back as a presheaf of `R`-modules. This is inverse to `ofConstantRingPresheaf` on the nose. -/
def toConstantRingPresheaf (P : PresheafOfModules.{w} (ringPresheaf (constantRingPresheaf C R))) :
    Cᵒᵖ ⥤ ModuleCat.{w} R where
  obj U := P.obj U
  map f := P.map f
  map_id U := by
    ext x
    exact congrArg (fun g : P.obj U ⟶ P.obj U => ModuleCat.Hom.hom g x) (P.map_id U)
  map_comp f g := by
    ext x
    exact congrArg (fun g : _ ⟶ _ => ModuleCat.Hom.hom g x) (P.map_comp f g)

/-- The functor reading a presheaf of modules over the constant presheaf of commutative rings
with value `R` back as a presheaf of `R`-modules, inverse to
`constantRingPresheafOfModules`. -/
def constantRingPresheafOfModulesInverse (C : Type u) [Category.{v} C] (R : Type w) [CommRing R] :
    PresheafOfModules.{w} (ringPresheaf (constantRingPresheaf C R)) ⥤
      (Cᵒᵖ ⥤ ModuleCat.{w} R) where
  obj P := toConstantRingPresheaf P
  map {P Q} τ :=
    { app := fun U => τ.app U
      naturality := by
        intro U V f
        ext x
        exact congrArg (fun g : P.obj U ⟶ Q.obj V => ModuleCat.Hom.hom g x) (τ.naturality f) }
  map_id P := rfl
  map_comp τ σ := rfl

/-- Reading a presheaf of modules over the constant presheaf of rings back as a presheaf of
`R`-modules and then over the constant presheaf of rings again returns it unchanged. -/
@[simp]
theorem ofConstantRingPresheaf_toConstantRingPresheaf
    (P : PresheafOfModules.{w} (ringPresheaf (constantRingPresheaf C R))) :
    ofConstantRingPresheaf (toConstantRingPresheaf P) = P :=
  rfl

/-- Reading a presheaf of `R`-modules over the constant presheaf of rings and back again returns
it unchanged. -/
@[simp]
theorem toConstantRingPresheaf_ofConstantRingPresheaf (F : Cᵒᵖ ⥤ ModuleCat.{w} R) :
    toConstantRingPresheaf (ofConstantRingPresheaf F) = F :=
  rfl

/-- The two readings of a presheaf of `R`-modules are an equivalence of categories, and an
equivalence whose unit and counit are identities: presheaves of `R`-modules and presheaves of
modules over the constant presheaf of rings with value `R` are the same thing. -/
def constantRingPresheafEquivalence (C : Type u) [Category.{v} C] (R : Type w) [CommRing R] :
    (Cᵒᵖ ⥤ ModuleCat.{w} R) ≌
      PresheafOfModules.{w} (ringPresheaf (constantRingPresheaf C R)) where
  functor := constantRingPresheafOfModules C R
  inverse := constantRingPresheafOfModulesInverse C R
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The presheaf of abelian groups underlying `ofConstantRingPresheaf F` is the one underlying
`F`: reading a presheaf of `R`-modules as a presheaf of modules over the constant presheaf of
rings does not change the sections. -/
noncomputable def presheafOfConstantRingPresheafIso (F : Cᵒᵖ ⥤ ModuleCat.{w} R) :
    (ofConstantRingPresheaf F).presheaf ≅ F ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w} :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- **Stacks 03ES.** A presheaf of `R`-modules whose module of sections over every object is
flat is a flat presheaf of modules over the constant presheaf of rings. -/
theorem isFlat_ofConstantRingPresheaf (F : Cᵒᵖ ⥤ ModuleCat.{w} R)
    (hF : ∀ U : Cᵒᵖ, Module.Flat R (F.obj U)) :
    AlgebraicGeometry.SheafOfModules.PresheafOfModules.IsFlat (ofConstantRingPresheaf F) :=
  AlgebraicGeometry.SheafOfModules.PresheafOfModules.isFlat_of_objectwise_flat _ hF

section Sheaf

variable (J : GrothendieckTopology C)

section ConstantRingSheaf

variable [HasWeakSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The constant sheaf of commutative rings with value `R`. -/
noncomputable abbrev constantRingSheaf (R : Type w) [CommRing R] : Sheaf J CommRingCat.{w} :=
  (constantSheaf J CommRingCat.{w}).obj (CommRingCat.of R)

/-- The canonical comparison from the constant presheaf of rings to the ring presheaf underlying
the constant sheaf of rings. -/
noncomputable abbrev constantRingSheafMap (R : Type w) [CommRing R] :
    ringPresheaf (constantRingPresheaf C R) ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf (constantRingSheaf J R)).obj :=
  Functor.whiskerRight (toSheafify J (constantRingPresheaf C R)) (forget₂ CommRingCat RingCat)

/-- The comparison `constantRingSheafMap J R` is locally injective. -/
instance isLocallyInjective_constantRingSheafMap :
    Presheaf.IsLocallyInjective J (constantRingSheafMap J R) := by
  apply (Presheaf.isLocallyInjective_forget_iff _ _).mp
  change Presheaf.IsLocallyInjective _
    (Functor.whiskerRight (toSheafify J (constantRingPresheaf C R)) (forget CommRingCat))
  infer_instance

/-- The comparison `constantRingSheafMap J R` is locally surjective. -/
instance isLocallySurjective_constantRingSheafMap :
    Presheaf.IsLocallySurjective J (constantRingSheafMap J R) := by
  apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
  change Presheaf.IsLocallySurjective _
    (Functor.whiskerRight (toSheafify J (constantRingPresheaf C R)) (forget CommRingCat))
  infer_instance

end ConstantRingSheaf

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {Osharp : Sheaf J CommRingCat.{w}}
  (a : ringPresheaf (constantRingPresheaf C R) ⟶
    (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)
  [Presheaf.IsLocallyInjective J a] [Presheaf.IsLocallySurjective J a]

/-- The functor reading a sheaf of `R`-modules as a sheaf of modules over a sheaf of rings
`Osharp` presented by the constant presheaf of rings with value `R`: take the underlying
presheaf, read it over the constant presheaf of rings, and sheafify along `a`. -/
noncomputable def sheafOfModulesOfConstantRingFunctor :
    Sheaf J (ModuleCat.{w} R) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp) :=
  sheafToPresheaf J (ModuleCat.{w} R) ⋙ constantRingPresheafOfModules C R ⋙
    PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf Osharp) a

/-- A sheaf of `R`-modules, read as a sheaf of modules over a sheaf of rings `Osharp` presented
by the constant presheaf of rings with value `R`. Sheafification extends the action of the
constant scalars to the sections of `Osharp`. -/
noncomputable def sheafOfModulesOfConstantRing (F : Sheaf J (ModuleCat.{w} R)) :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp) :=
  (sheafOfModulesOfConstantRingFunctor J a).obj F

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The functor `sheafOfModulesOfConstantRingFunctor J a` sends `F` to
`sheafOfModulesOfConstantRing J a F`. -/
@[simp]
theorem sheafOfModulesOfConstantRingFunctor_obj (F : Sheaf J (ModuleCat.{w} R)) :
    (sheafOfModulesOfConstantRingFunctor J a).obj F = sheafOfModulesOfConstantRing J a F :=
  rfl

/-- A morphism of sheaves of `R`-modules, read as a morphism of sheaves of modules over
`Osharp`. -/
noncomputable abbrev sheafOfModulesOfConstantRingMap {F G : Sheaf J (ModuleCat.{w} R)}
    (φ : F ⟶ G) : sheafOfModulesOfConstantRing J a F ⟶ sheafOfModulesOfConstantRing J a G :=
  (sheafOfModulesOfConstantRingFunctor J a).map φ

/-- The sheaf of abelian groups underlying `sheafOfModulesOfConstantRing J a F` is the one
underlying `F`: the bridge does not change the sections. -/
noncomputable def sheafOfModulesOfConstantRingIso
    [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})]
    (F : Sheaf J (ModuleCat.{w} R)) :
    (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)).obj
        (sheafOfModulesOfConstantRing J a F) ≅
      (sheafCompose J (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})).obj F :=
  (presheafToSheaf J AddCommGrpCat.{w}).mapIso (presheafOfConstantRingPresheafIso F.obj) ≪≫
    (sheafificationIso ((sheafCompose J
      (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})).obj F)).symm

/-! ### The right adjoint, and the structure sheaf as a sheaf of `R`-modules -/

/-- A sheaf of modules over `Osharp`, read as a sheaf of `R`-modules by restricting the scalars
along `a`. It is a sheaf because its presheaf of abelian groups is unchanged. This is the right
adjoint of the bridge. -/
noncomputable def moduleSheafOfConstantRing :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp) ⥤
      Sheaf J (ModuleCat.{w} R) where
  obj Z := ⟨toConstantRingPresheaf ((PresheafOfModules.restrictScalars a).obj Z.val),
    Presheaf.isSheaf_of_isSheaf_comp J _ (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) Z.isSheaf⟩
  map g := CategoryTheory.Sheaf.homEquiv.symm
    ((constantRingPresheafOfModulesInverse C R).map
      ((PresheafOfModules.restrictScalars a).map
        ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)).map g)))
  map_id Z := by
    apply CategoryTheory.Sheaf.hom_ext
    rfl
  map_comp g h := by
    apply CategoryTheory.Sheaf.hom_ext
    rfl

/-- The sheaf of rings `Osharp`, read as a presheaf of modules over the constant presheaf of
rings with value `R` by restricting the scalars along `a`. -/
noncomputable abbrev unitOverConstantRing :
    PresheafOfModules.{w} (ringPresheaf (constantRingPresheaf C R)) :=
  (PresheafOfModules.restrictScalars a).obj
    (PresheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)

/-- The sheaf of rings `Osharp`, read as a presheaf of `R`-modules: its sections over `U` are
those of `Osharp`, with `r : R` acting as multiplication by `a_U r`. -/
noncomputable abbrev ringAsModulePresheaf : Cᵒᵖ ⥤ ModuleCat.{w} R :=
  toConstantRingPresheaf (unitOverConstantRing J a)

/-- The sheaf of rings `Osharp`, read as a sheaf of `R`-modules: the value of the right adjoint
at the structure sheaf. -/
noncomputable abbrev ringAsModuleSheaf : Sheaf J (ModuleCat.{w} R) :=
  (moduleSheafOfConstantRing J a).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Osharp))

/-- The section `1` of the structure sheaf, read as a section of `Osharp` over the constant
presheaf of rings. -/
noncomputable def constantRingUnitSection : (unitOverConstantRing J a).sections :=
  PresheafOfModules.sectionsMk
    (fun U => (1 : ((Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U : RingCat.{w})))
    (fun U V f => by
      change ((Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.map f).hom 1 = 1
      exact map_one _)

/-- The map of presheaves of modules over the constant presheaf of rings which sends the
constant section `r` to `a_U r`, obtained from the unit section `1` of `Osharp`. -/
noncomputable def unitToUnitOverConstantRing :
    PresheafOfModules.unit (ringPresheaf (constantRingPresheaf C R)) ⟶ unitOverConstantRing J a :=
  (PresheafOfModules.unitHomEquiv (unitOverConstantRing J a)).symm (constantRingUnitSection J a)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [J.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify J AddCommGrpCat] [Presheaf.IsLocallyInjective J a]
  [Presheaf.IsLocallySurjective J a] in
/-- `unitToUnitOverConstantRing` sends a constant scalar `r` to `a_U r`. -/
theorem unitToUnitOverConstantRing_app_apply (U : Cᵒᵖ)
    (r : ((ringPresheaf (constantRingPresheaf C R)).obj U : RingCat.{w})) :
    ((unitToUnitOverConstantRing J a).app U).hom r = (a.app U).hom r :=
  mul_one ((a.app U).hom r)

section ConstantScalarIdeal

variable [HasWeakSheafify J (ModuleCat.{w} R)]

/-- **The bridge is a left adjoint.** Reading a sheaf of `R`-modules as a sheaf of modules over
`Osharp` is left adjoint to restricting the scalars back along `a`: a map of `Osharp`-modules out
of the bridge of `F` is the same thing as a map of sheaves of `R`-modules from `F` to the
restriction of scalars of the target. It is the sheafification adjunction of
`PresheafOfModules`, read through the two on-the-nose readings of a presheaf of `R`-modules and
the full faithfulness of `sheafToPresheaf`. -/
noncomputable def sheafOfModulesOfConstantRingAdjunction :
    sheafOfModulesOfConstantRingFunctor J a ⊣ moduleSheafOfConstantRing J a :=
  Adjunction.restrictFullyFaithful
    ((constantRingPresheafEquivalence C R).toAdjunction.comp
      (PresheafOfModules.sheafificationAdjunction a))
    (fullyFaithfulSheafToPresheaf J (ModuleCat.{w} R))
    (Functor.FullyFaithful.id (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)))
    (Iso.refl _) (Iso.refl _)

/-- The functor `sheafOfModulesOfConstantRingFunctor J a` preserves colimits. -/
instance preservesColimits_sheafOfModulesOfConstantRingFunctor :
    Limits.PreservesColimitsOfSize.{w, w} (sheafOfModulesOfConstantRingFunctor J a) :=
  (sheafOfModulesOfConstantRingAdjunction J a).leftAdjoint_preservesColimits

/-- An `R`-linear map `φ : M ⟶ R` induces a map from the constant sheaf of `R`-modules on `M`
to `Osharp` read as a sheaf of `R`-modules, carrying a constant section `m` to `a_U (φ m)`. It is
obtained from the corresponding map of constant presheaves by the universal property of
sheafification. -/
noncomputable def constantToRingAsModule {M : ModuleCat.{w} R} (φ : M ⟶ ModuleCat.of R R) :
    (constantSheaf J (ModuleCat.{w} R)).obj M ⟶ ringAsModuleSheaf J a :=
  ((sheafificationAdjunction J (ModuleCat.{w} R)).homEquiv ((Functor.const Cᵒᵖ).obj M)
      (ringAsModuleSheaf J a)).symm
    ((constantRingPresheafOfModulesInverse C R).map
      ((constantRingPresheafOfModules C R).map ((Functor.const Cᵒᵖ).map φ) ≫
        unitToUnitOverConstantRing J a))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [J.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify J AddCommGrpCat] [Presheaf.IsLocallyInjective J a]
  [Presheaf.IsLocallySurjective J a] in
/-- The value formula for `constantToRingAsModule`: on the image of a constant section `m` under
the sheafification unit, it is `a_U (φ m)`. -/
theorem constantToRingAsModule_app_toSheafify {M : ModuleCat.{w} R} (φ : M ⟶ ModuleCat.of R R)
    (U : Cᵒᵖ) (m : M) :
    ((constantToRingAsModule J a φ).hom.app U).hom
        (((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app U).hom m) =
      (a.app U).hom (φ.hom m) := by
  have key := ((sheafificationAdjunction J (ModuleCat.{w} R)).homEquiv
    ((Functor.const Cᵒᵖ).obj M) (ringAsModuleSheaf J a)).apply_symm_apply
      ((constantRingPresheafOfModulesInverse C R).map
        ((constantRingPresheafOfModules C R).map ((Functor.const Cᵒᵖ).map φ) ≫
          unitToUnitOverConstantRing J a))
  rw [Adjunction.homEquiv_unit] at key
  have hval := congrArg (fun k : (Functor.const Cᵒᵖ).obj M ⟶ ringAsModulePresheaf J a =>
    (k.app U).hom m) key
  exact hval.trans (unitToUnitOverConstantRing_app_apply J a U (φ.hom m))

/-- An `R`-linear map `φ : M ⟶ R` induces a map of sheaves of modules over `Osharp` from the
constant sheaf on `M`, read over `Osharp`, to the structure sheaf. For `M` an ideal `I` of `R`
and `φ` its inclusion this exhibits the constant sheaf `I̲` as a sheaf of ideals of `Osharp`,
which is what makes the product of `I̲` with an `Osharp`-module meaningful. -/
noncomputable def constantModuleToUnit {M : ModuleCat.{w} R} (φ : M ⟶ ModuleCat.of R R) :
    sheafOfModulesOfConstantRing J a ((constantSheaf J (ModuleCat.{w} R)).obj M) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Osharp) :=
  sheafOfModulesOfConstantRingMap J a (constantToRingAsModule J a φ) ≫
    (PresheafOfModules.sheafificationAdjunction a).counit.app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Osharp))

end ConstantScalarIdeal

/-- **Stacks 03ET.** A sheaf of `R`-modules whose module of sections over every object is flat
is flat as a sheaf of modules over a sheaf of rings presented by the constant presheaf of
rings. -/
theorem isFlat_sheafOfModulesOfConstantRing (F : Sheaf J (ModuleCat.{w} R))
    (hF : ∀ U : Cᵒᵖ, Module.Flat R (F.obj.obj U)) :
    AlgebraicGeometry.SheafOfModules.IsFlat (sheafOfModulesOfConstantRing J a F) :=
  Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification J a
    (ofConstantRingPresheaf F.obj) (isFlat_ofConstantRingPresheaf F.obj hF)

end Sheaf

end Stacks.ConstantSheaf

end
