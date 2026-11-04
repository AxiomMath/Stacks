module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseChangeUnitor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackLocalGeneration
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite presentation of sheaves of modules: the local criterion, and transport along a functor

A sheaf of modules on a ringed site is *of finite presentation* when it is locally the cokernel
of a map between finite free modules. Mathlib formalizes this as
`SheafOfModules.IsFinitePresentation`: the existence of a `SheafOfModules.QuasicoherentData`,
i.e. of a *fixed family* of objects `X i` of the site covering the terminal object together
with a finite `SheafOfModules.Presentation` of `M.over (X i)` for each `i`.

This file proves three things. First, the fixed family can be replaced by a condition *local on
each object*: a sheaf of modules with a finite global presentation on the members of some
covering of each object is of finite presentation. Second, quasicoherent data transports along a
functor between categories of sheaves of modules on two different sites, once that functor is
given together with a family of *localized* functors. Third, for the pullback
`f^*F = O_C ⊗_{f⁻¹O_D} f⁻¹F` along a morphism of ringed topoi, a finite global presentation of
`F` pulls back to a finite global presentation of `f^*F`, and `f^*F` is of finite presentation
as soon as `f⁻¹F` has a finite global presentation on the members of a covering of each object.

## Main definitions

* `Stacks.SheafOfModules.QuasicoherentData.MapData`: the data under which quasicoherent data
  transports along a functor — a covering family of the source site, an assignment of a
  member of the given covering of the target site to each of its objects, and for each a
  colimit-preserving functor between slice categories of modules carrying the structure sheaf
  to the structure sheaf and computing the restriction of `F.obj M`.
* `Stacks.SheafOfModules.QuasicoherentData.map`: the transported quasicoherent data.
* `Stacks.Sheaves.FinitePresentation.pullbackModulesUnitIso`: the pullback of `O_D` along a
  morphism of ringed topoi is `O_C`.
* `Stacks.Sheaves.FinitePresentation.extendScalarsOver`: extension of scalars on a slice site,
  with its adjunction, its unit isomorphism and its comparison with restriction to the slice.
* `Stacks.Sheaves.FinitePresentation.presentationExtendScalarsOver`: a presentation restricted
  to a slice site, transported across extension of scalars.
* `Stacks.Sheaves.FinitePresentation.presentationPullbackModules`: a global presentation
  transported along the pullback.

## Main results

* `Stacks.SheafOfModules.isFinitePresentation_of_locally_presented`: the local criterion.
* `Stacks.SheafOfModules.isFinitePresentation_of_mapData`: finite presentation is preserved by
  a functor admitting a `MapData`.
* `Stacks.Sheaves.FinitePresentation.preservesColimitsOfSize_pullbackModules`: pullback along a
  morphism of ringed topoi preserves colimits.
* `Stacks.Sheaves.FinitePresentation.presentationPullbackModules_isFinite`: the pullback of a
  finite global presentation is finite, with the *same* index types for its generators and its
  relations.
* `Stacks.Sheaves.FinitePresentation.isFinitePresentation_pullbackModules_of_inverseImage_local`:
  `f^*F` is of finite presentation when `f⁻¹F` has finite global presentations on the members of
  a covering of each object.

## References

* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules

/-! ### The local criterion for finite presentation -/

section Local

universe u v u₁

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The local criterion for finite presentation.** A sheaf of modules that has a finite
global presentation on each member of some covering of each object of the site is of finite
presentation. -/
theorem isFinitePresentation_of_locally_presented (M : _root_.SheafOfModules.{u} R)
    (hM : ∀ U : C, ∃ T : J.Cover U, ∀ (V : C) (g : V ⟶ U), T g →
      ∃ P : (M.over V).Presentation, P.IsFinite) :
    M.IsFinitePresentation :=
  isFinitePresentation_of_coversTop
    (Subtype.val (p := fun V : C => ∃ P : (M.over V).Presentation, P.IsFinite))
    (fun U => by
      obtain ⟨T, hT⟩ := hM U
      exact J.superset_covering (fun Z g hg => ⟨⟨Z, hT Z g hg⟩, ⟨𝟙 Z⟩⟩) T.2)
    (fun i => i.2)

end Local

/-! ### Transporting quasicoherent data along a functor -/

section Map

universe u v u₁ v' u' w w'

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} {S : Sheaf J RingCat.{u}}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D} {R : Sheaf K RingCat.{u}}
  [∀ W : D, HasWeakSheafify (K.over W) AddCommGrpCat.{u}]
  [∀ W : D, (K.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The data needed to transport a `SheafOfModules.QuasicoherentData` along a functor
`F : Mod(R) ⥤ Mod(S)`, where `R` lives on the site `(D, K)` and `S` on `(C, J)`: a family of
objects of the source site `C` covering its terminal object, an assignment of a member of the
given covering of `(D, K)` to each of them, and, for each, a colimit-preserving functor between
the two slice categories of modules that carries the structure sheaf to the structure sheaf and
`M` restricted to the chosen object of `D` to `F.obj M` restricted to the object of `C`.

`F` itself occurs only in the field `overIso`: `functor i` is not required to be a localization
of `F`, and the two agree only at the object `M`. -/
structure QuasicoherentData.MapData (F : _root_.SheafOfModules.{u} R ⥤
    _root_.SheafOfModules.{u} S) {M : _root_.SheafOfModules.{u} R}
    (q : M.QuasicoherentData.{w}) where
  /-- the index type of the covering family of the source site -/
  I : Type w'
  /-- a family of objects of the source site covering its terminal object -/
  X : I → C
  /-- the family `X` covers the terminal object of the source site -/
  coversTop : J.CoversTop X
  /-- the member of the given covering of the target site at which `functor i` is taken; it is
  unconstrained, the only link to `X i` being through `overIso` -/
  index : I → q.I
  /-- a functor between the slice categories of modules over `q.X (index i)` and over `X i` -/
  functor (i : I) :
    _root_.SheafOfModules.{u} (R.over (q.X (index i))) ⥤
      _root_.SheafOfModules.{u} (S.over (X i))
  /-- the functor preserves colimits, hence the cokernel diagram of a presentation -/
  preservesColimits (i : I) : PreservesColimitsOfSize.{u, u} (functor i)
  /-- the functor carries the structure sheaf to the structure sheaf -/
  unitIso (i : I) : _root_.SheafOfModules.unit (S.over (X i)) ≅
    (functor i).obj (_root_.SheafOfModules.unit (R.over (q.X (index i))))
  /-- the functor computes the restriction of `F.obj M` -/
  overIso (i : I) :
    (functor i).obj (M.over (q.X (index i))) ≅ (F.obj M).over (X i)

variable [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {F : _root_.SheafOfModules.{u} R ⥤ _root_.SheafOfModules.{u} S}
  {M : _root_.SheafOfModules.{u} R}

/-- **Quasicoherent data transported along a functor.** Given quasicoherent data `q` for `M`
and a `MapData` `L` for `F` relative to `q`, the transported presentations assemble into
quasicoherent data for `F.obj M`. -/
noncomputable def QuasicoherentData.map (q : M.QuasicoherentData.{w})
    (L : QuasicoherentData.MapData F q) :
    (F.obj M).QuasicoherentData.{w'} where
  I := L.I
  X := L.X
  coversTop := L.coversTop
  presentation i :=
    let _ : ∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{u} :=
      fun _ => AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
    let _ : ∀ W : D, HasSheafify (K.over W) AddCommGrpCat.{u} :=
      fun _ => AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
    let _ := L.preservesColimits i
    ((q.presentation (L.index i)).map (L.functor i) (L.unitIso i)).ofIsIso (L.overIso i).hom

/-- Quasicoherent data whose presentations are finite transports to quasicoherent data whose
presentations are finite. -/
instance QuasicoherentData.isFinitePresentation_map (q : M.QuasicoherentData.{w})
    [q.IsFinitePresentation] (L : QuasicoherentData.MapData F q) :
    (QuasicoherentData.map q L).IsFinitePresentation where
  isFinite_presentation i := by
    let _ : ∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{u} :=
      fun _ => AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
    let _ : ∀ W : D, HasSheafify (K.over W) AddCommGrpCat.{u} :=
      fun _ => AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
    let _ := L.preservesColimits i
    exact inferInstanceAs
      (((q.presentation (L.index i)).map (L.functor i) (L.unitIso i)).ofIsIso
        (L.overIso i).hom).IsFinite

/-- **Finite presentation is preserved by a functor admitting a `MapData`.** One quasicoherent
datum witnessing finite presentation of `M`, together with a `MapData` for `F` relative to it,
suffices; the index universe of the datum is arbitrary. -/
theorem isFinitePresentation_of_mapData {q : M.QuasicoherentData.{w}}
    (hq : q.IsFinitePresentation) (L : QuasicoherentData.MapData F q) :
    (F.obj M).IsFinitePresentation := by
  let _ := hq
  exact ⟨(QuasicoherentData.map q L).shrink, inferInstance⟩

/-- `isFinitePresentation_of_mapData` in the form that quantifies over all quasicoherent data
of `M` witnessing finite presentation, with no datum supplied by the caller. -/
theorem isFinitePresentation_of_forall_mapData (M : _root_.SheafOfModules.{u} R)
    (L : ∀ q : M.QuasicoherentData.{u'}, q.IsFinitePresentation →
      QuasicoherentData.MapData F q)
    [M.IsFinitePresentation] :
    (F.obj M).IsFinitePresentation := by
  obtain ⟨q, hq⟩ := _root_.SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  exact isFinitePresentation_of_mapData hq (L q hq)

end Map

end Stacks.SheafOfModules


namespace Stacks.Sheaves.FinitePresentation

/-! ### Pullback along a morphism of ringed topoi: the global statement -/

section RingedTopos

open AlgebraicGeometry Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe v u v' u' w w'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : RingedToposHom X Y)

/-- The inverse image of the structure sheaf of the target, viewed as a module over the
inverse-image sheaf of rings, is the structure sheaf of that ring. -/
noncomputable def inverseImageModulesUnitIso :
    _root_.SheafOfModules.unit
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≅
      (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  let _ := f.toToposHom.preservesFiniteLimits
  pullbackModuleUnitIso X.J f.toToposHom.inverseImage (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)

/-- Extension of scalars along the inverse-image form of the structure map carries the
structure sheaf of `f⁻¹O_D` to the structure sheaf `O_C`. -/
noncomputable def extendScalarsFSharpUnitIso :
    (extendScalarsFSharp f).obj (_root_.SheafOfModules.unit
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ≅
      _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  Stacks.SheafOfModules.ChangeOfRings.baseChangeUnitor _
    (extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)

/-- **The structure sheaf is its own pullback.** The pullback of `O_D`, viewed as a module over
itself, along a morphism of ringed topoi is `O_C`. -/
noncomputable def pullbackModulesUnitIso :
    _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≅
      (f.pullbackModules).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  (extendScalarsFSharpUnitIso f).symm ≪≫
    (extendScalarsFSharp f).mapIso (inverseImageModulesUnitIso f)

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- Pullback along a morphism of ringed topoi preserves colimits, being a left adjoint. -/
instance preservesColimitsOfSize_pullbackModules :
    PreservesColimitsOfSize.{w, w} (f.pullbackModules) :=
  (pullbackAdjPushforwardModules f).leftAdjoint_preservesColimits

end RingedTopos

/-! ### Extension of scalars and restriction to a slice site, at the level of presentations -/

section ExtendScalarsOver

open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.LocalGeneration

universe v u w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : A₁ ⟶ A₂)
  (h₁ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₁))
  (h₂ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₂))
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Extension of scalars on a slice site.** Extension of scalars along `θ` on the slice site
over `V`, between the categories of modules over `(commRingSheaf J A₁ h₁).over V` and over
`(commRingSheaf J A₂ h₂).over V`. -/
noncomputable def extendScalarsOver (V : C) :
    _root_.SheafOfModules.{w} ((commRingSheaf J A₁ h₁).over V) ⥤
      _root_.SheafOfModules.{w} ((commRingSheaf J A₂ h₂).over V) :=
  extendScalars (J.over V) (Functor.whiskerLeft (Over.forget V).op θ)
    ((commRingSheaf J A₁ h₁).over V).property
    ((commRingSheaf J A₂ h₂).over V).property

/-- Extension of scalars on the slice site over `V` is left adjoint to restriction of
scalars. -/
noncomputable def extendScalarsOverAdj (V : C) :
    extendScalarsOver θ h₁ h₂ V ⊣ _root_.SheafOfModules.restrictScalars
      (commRingSheafMap (J.over V) (Functor.whiskerLeft (Over.forget V).op θ)
        ((commRingSheaf J A₁ h₁).over V).property
        ((commRingSheaf J A₂ h₂).over V).property) :=
  extendRestrictScalarsAdjunction (J.over V) (Functor.whiskerLeft (Over.forget V).op θ)
    ((commRingSheaf J A₁ h₁).over V).property
    ((commRingSheaf J A₂ h₂).over V).property

omit [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Extension of scalars on a slice site preserves colimits, being a left adjoint. -/
instance preservesColimitsOfSize_extendScalarsOver (V : C) :
    PreservesColimitsOfSize.{w, w} (extendScalarsOver θ h₁ h₂ V) :=
  (extendScalarsOverAdj θ h₁ h₂ V).leftAdjoint_preservesColimits

/-- Extension of scalars on a slice site carries the structure sheaf to the structure
sheaf. -/
noncomputable def extendScalarsOverUnitIso (V : C) :
    _root_.SheafOfModules.unit ((commRingSheaf J A₂ h₂).over V) ≅
      (extendScalarsOver θ h₁ h₂ V).obj
        (_root_.SheafOfModules.unit ((commRingSheaf J A₁ h₁).over V)) :=
  (Stacks.SheafOfModules.ChangeOfRings.baseChangeUnitor _
    (extendScalarsOverAdj θ h₁ h₂ V)).symm

/-- Extension of scalars on the slice site over `V` commutes with restriction to `V`:
`Stacks.Sheaves.LocalGeneration.extendScalarsOverIso`, with source spelled through
`extendScalarsOver`. -/
noncomputable def extendScalarsOverObjIso
    (M : _root_.SheafOfModules.{w} (commRingSheaf J A₁ h₁)) (V : C) :
    (extendScalarsOver θ h₁ h₂ V).obj (M.over V) ≅
      ((extendScalars J θ h₁ h₂).obj M).over V :=
  extendScalarsOverIso θ h₁ h₂ V M

/-- **Extension of scalars transports a presentation through restriction to a slice site.**
A presentation of `M` restricted to `V` gives a presentation of the extension of scalars of
`M`, restricted to `V`. -/
noncomputable def presentationExtendScalarsOver
    (M : _root_.SheafOfModules.{w} (commRingSheaf J A₁ h₁)) (V : C)
    (P : (M.over V).Presentation) :
    (((extendScalars J θ h₁ h₂).obj M).over V).Presentation :=
  let _ : ∀ W : C, HasSheafify (J.over W) AddCommGrpCat.{w} :=
    fun _ => AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  (P.map (extendScalarsOver θ h₁ h₂ V) (extendScalarsOverUnitIso θ h₁ h₂ V)).ofIsIso
    (extendScalarsOverObjIso θ h₁ h₂ M V).hom

/-- The presentation transported by `presentationExtendScalarsOver` is finite when `P` is; the
finiteness of `P` is taken as an explicit hypothesis `hP`. -/
theorem isFinite_presentationExtendScalarsOver
    (M : _root_.SheafOfModules.{w} (commRingSheaf J A₁ h₁)) (V : C)
    (P : (M.over V).Presentation) (hP : P.IsFinite) :
    (presentationExtendScalarsOver θ h₁ h₂ M V P).IsFinite :=
  let _ : ∀ W : C, HasSheafify (J.over W) AddCommGrpCat.{w} :=
    fun _ => AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let _ := hP
  inferInstanceAs (_root_.SheafOfModules.Presentation.ofIsIso
    (extendScalarsOverObjIso θ h₁ h₂ M V).hom
    (P.map (extendScalarsOver θ h₁ h₂ V) (extendScalarsOverUnitIso θ h₁ h₂ V))).IsFinite

end ExtendScalarsOver

/-! ### Pullback along a morphism of ringed topoi: the global case -/

section Global

open AlgebraicGeometry Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe v u v' u' w

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y)

/-- A global presentation of a sheaf of `O_D`-modules `F` transports along the pullback to a
global presentation of `f^*F`, with the *same* index types for generators and relations. -/
noncomputable def presentationPullbackModules
    {F : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (P : F.Presentation) :
    ((f.pullbackModules).obj F).Presentation :=
  let _ : HasSheafify X.J AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let _ : HasSheafify Y.J AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  P.map (f.pullbackModules) (pullbackModulesUnitIso f)

/-- The presentation transported along the pullback is finite when the original is, with the
same index types. -/
instance presentationPullbackModules_isFinite
    {F : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (P : F.Presentation) [P.IsFinite] :
    (presentationPullbackModules f P).IsFinite := by
  let _ : HasSheafify X.J AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let _ : HasSheafify Y.J AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  exact inferInstanceAs (P.map (f.pullbackModules) (pullbackModulesUnitIso f)).IsFinite

end Global

/-! ### Pullback along a morphism of ringed topoi: reduction of the local case -/

section Reduction

open AlgebraicGeometry Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe v u v' u' w

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **Pullback preserves finite presentation, given the inverse-image factor.** If the inverse
image `f⁻¹F` has a finite global presentation on the members of some covering of each object of
the source site (the hypothesis `hF`), then the pullback `f^*F = O_C ⊗_{f⁻¹O_D} f⁻¹F` is of
finite presentation. -/
theorem isFinitePresentation_pullbackModules_of_inverseImage_local
    (F : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hF : ∀ U : X.C, ∃ T : X.J.Cover U, ∀ (V : X.C) (g : V ⟶ U), T g →
      ∃ P : (((inverseImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F).over V).Presentation,
        P.IsFinite) :
    ((f.pullbackModules).obj F).IsFinitePresentation := by
  refine Stacks.SheafOfModules.isFinitePresentation_of_locally_presented _ fun U => ?_
  obtain ⟨T, hT⟩ := hF U
  refine ⟨T, fun V g hg => ?_⟩
  obtain ⟨P, hP⟩ := hT V g hg
  exact ⟨presentationExtendScalarsOver (fSharpCommRing f)
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
      ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F) V P,
    isFinite_presentationExtendScalarsOver (fSharpCommRing f) _ _ _ V P hP⟩

end Reduction

end Stacks.Sheaves.FinitePresentation

end
