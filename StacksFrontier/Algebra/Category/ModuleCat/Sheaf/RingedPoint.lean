module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.CategoryTheory.Sites.Point.Defs
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.PUnit
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The ringed point of a point of a ringed topos

Let `(Sh(C), O)` be a ringed topos and let `p` be a point of `Sh(C)`, that is a morphism of
topoi `p : Sh(pt) → Sh(C)`, given by the stalk functor `p⁻¹` and the skyscraper functor `p_*`.
The *ringed point* over `p` is the ringed topos `(Sh(pt), O_p)` with `O_p = p⁻¹O`, together
with the morphism of ringed topoi `(p, p♯) : (Sh(pt), O_p) ⟶ (Sh(C), O)` whose structure map
is the identity of `p⁻¹O` in its inverse-image form. The modules over `O_p` are the modules on
the point.

The site `pt` has one object, one morphism and the trivial topology, so that `Sh(pt) = Sets`;
`PointSite` is that site, with the universes of its objects and morphisms free, and
`pointSiteSheafEquiv` is the equivalence with `Type w`.

## Main definitions

* `Stacks.Sheaves.RingedPoint.PointSite`: the site of the point.
* `Stacks.Sheaves.RingedPoint.pointSiteSheafEquiv`: `Sh(pt) = Sets`.
* `Stacks.Sheaves.RingedPoint.RingedPointSituation`: the ringed point over a point of a ringed
  topos, as data: the ringed topos of the point, the identification of its topos with sets, the
  morphism of ringed topoi, and the three identifications of its inverse image, direct image
  and structure sheaf with the stalk functor, the skyscraper functor and `p⁻¹O`.
* `Stacks.Sheaves.RingedPoint.ringedPointSituation`: the ringed point over a given point.
* `Stacks.Sheaves.RingedPoint.RingedPointSituation.stalkModules`: the module-valued stalk, the
  inverse image of modules of Stacks 03D2 read over `O_p`.
* `Stacks.Sheaves.RingedPoint.presheafRestrictScalarsCompIsoId`,
  `sheafRestrictScalarsCompIsoId`, `restrictScalarsEquivalenceOfIso`: restriction of scalars
  along an isomorphism of sheaves of rings is an equivalence of the categories of modules.
* `Stacks.Sheaves.RingedPoint.presheafRestrictScalarsEquivalenceOfIso` and
  `Stacks.Sheaves.RingedPoint.presheafRestrictScalars_isEquivalence`: the same for presheaves
  of rings and presheaves of modules, as an equivalence and as a property of the functor.
* `Stacks.Sheaves.RingedPoint.restrictScalarsAdjunctionOfEq`: that equivalence as an adjunction,
  with the right-hand restriction taken along a morphism only *equal* to the isomorphism.
* `Stacks.Sheaves.RingedPoint.RingedPointSituation.inverseImageAdjunction` and
  `Stacks.Sheaves.RingedPoint.RingedPointSituation.pointPushforwardIso`: the adjunction
  `p⁻¹ ⊣ p_*` as the ringed point presents it, and the resulting canonical identification of the
  skyscraper functor of the point with the direct image along the ringed point.
* `Stacks.Sheaves.RingedPoint.restrictScalarsObjUnitIso`: that equivalence carries the structure
  sheaf to the structure sheaf.

## Main results

* `Stacks.Sheaves.RingedPoint.RingedPointSituation.pullbackStalkIso`: pullback of modules of
  Stacks 03D6 to the ringed point is the module-valued stalk: the canonical map `p^*M → p⁻¹M` is
  linear over `O_p` and natural in `M`.
* `Stacks.Sheaves.RingedPoint.RingedPointSituation.pullbackUnderlyingImageIso` and
  `Stacks.Sheaves.RingedPoint.RingedPointSituation.pullbackUnderlyingIso`: the pullback of a
  module to the ringed point has, naturally, the inverse image of the underlying sheaf, and
  hence the stalk of the underlying sheaf.
* `Stacks.Sheaves.RingedPoint.RingedPointSituation.pushforwardUnderlyingStalkIso`: the direct
  image of a module from the ringed point has, naturally, the skyscraper sheaf of the
  underlying sheaf.

## References

* [Stacks Project, Section 18.37, the situation preceding Tag
  05V8](https://stacks.math.columbia.edu/tag/05V8)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sheaves.RingedPoint

universe v u w vₚ uₚ

/-- The site of the point: one object, one morphism, in prescribed universes. -/
abbrev PointSite := ULiftHom.{vₚ} (ULift.{uₚ} (Discrete PUnit.{1}))

/-- The category structure on `ULift (Discrete PUnit)` underlying the site of the point. -/
instance pointSiteInnerCategory :
    Category.{0, uₚ} (ULift.{uₚ} (Discrete PUnit.{1})) :=
  uliftCategory (Discrete PUnit.{1})

/-- The category structure on the site of the point. -/
instance pointSiteCategory : Category.{vₚ, uₚ} (PointSite.{vₚ, uₚ}) :=
  ULiftHom.category

/-- The site of the point has one object and one morphism. -/
def pointSiteEquiv : PointSite.{vₚ, uₚ} ≌ Discrete PUnit.{1} :=
  (ULiftHom.equiv (C := ULift.{uₚ} (Discrete PUnit.{1}))).symm.trans
    (ULift.equivalence (C := Discrete PUnit.{1})).symm

/-- Presheaves of sets on the site of the point are sets. -/
def pointSitePresheafEquiv : (PointSite.{vₚ, uₚ}ᵒᵖ ⥤ Type w) ≌ Type w :=
  let e₁ : (PointSite.{vₚ, uₚ}ᵒᵖ ⥤ Type w) ≌ ((Discrete PUnit.{1})ᵒᵖ ⥤ Type w) :=
    ((Functor.whiskeringLeft (PointSite.{vₚ, uₚ}ᵒᵖ) ((Discrete PUnit.{1})ᵒᵖ)
      (Type w)).obj pointSiteEquiv.op.functor).asEquivalence.symm
  let e₀ : Discrete PUnit.{1} ≌ Discrete PUnit.{w + 1} :=
    Discrete.equivalence Equiv.punitEquivPUnit
  let e₂ : ((Discrete PUnit.{1})ᵒᵖ ⥤ Type w) ≌ ((Discrete PUnit.{w + 1})ᵒᵖ ⥤ Type w) :=
    ((Functor.whiskeringLeft ((Discrete PUnit.{1})ᵒᵖ) ((Discrete PUnit.{w + 1})ᵒᵖ)
      (Type w)).obj e₀.op.functor).asEquivalence.symm
  let e₃ : ((Discrete PUnit.{w + 1})ᵒᵖ ⥤ Type w) ≌ (Discrete PUnit.{w + 1} ⥤ Type w) :=
    ((Functor.whiskeringLeft ((Discrete PUnit.{w + 1})ᵒᵖ) (Discrete PUnit.{w + 1})
      (Type w)).obj (Discrete.opposite PUnit.{w + 1}).functor).asEquivalence.symm
  e₁.trans (e₂.trans (e₃.trans Functor.equiv))

/-- Sheaves of sets for the trivial topology on the site of the point are sets, `Sh(pt) = Sets`. -/
def pointSiteSheafEquiv :
    Sheaf (⊥ : GrothendieckTopology (PointSite.{vₚ, uₚ})) (Type w) ≌ Type w :=
  (sheafBotEquivalence (Type w)).trans pointSitePresheafEquiv

/-- For the trivial topology, every functor between the value categories composes with sheaves. -/
instance hasSheafComposeBot {T : Type u} [Category.{v} T] {A : Type*} [Category A]
    {B : Type*} [Category B] (F : A ⥤ B) :
    (⊥ : GrothendieckTopology T).HasSheafCompose F :=
  ⟨fun _ _ ↦ Presheaf.isSheaf_bot _⟩

open AlgebraicGeometry Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPushforward

variable (X : RingedTopos.{v, u, w})
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})]
  (p : PointOfTopos.{w, v, u} X.J)

/-- The *ringed point* over a point `p` of a ringed topos `(Sh(C), O)`: a ringed topos whose
underlying topos is the category of sets, a morphism of ringed topoi from it to `(Sh(C), O)` whose
underlying morphism of topoi is `p`, and the identification `O_p = p⁻¹O` of its structure sheaf
with the inverse image of `O`, with the structure map of the morphism the identity under that
identification. -/
structure RingedPointSituation where
  /-- The ringed topos of the point. -/
  point : RingedTopos.{vₚ, uₚ, w}
  [pointHasSheafComposeForget₂ :
    point.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [pointHasSheafComposeForgetRing : point.J.HasSheafCompose (forget RingCat.{w})]
  /-- Its topos is the category of sets. -/
  pointEquiv : point.Topos ≌ Type w
  /-- The morphism of ringed topoi from the point. -/
  toRingedToposHom : RingedToposHom point X
  /-- Its inverse image is the stalk functor of `p`. -/
  inverseImageIso :
    toRingedToposHom.toToposHom.inverseImage ⋙ pointEquiv.functor ≅ p.inverseImage
  /-- The structure sheaf of the point is the inverse image of the structure sheaf. -/
  ringIso :
    inverseImageRingSheaf toRingedToposHom.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≅
      Stacks.SheafOfModules.Tensor.ringSheaf point.O
  /-- Under that identification the structure map of the morphism is the identity. -/
  ringIso_hom : ringIso.hom = toRingedToposHom.fSharpInverseImage
  /-- Its direct image is the skyscraper functor of `p`. -/
  pushforwardIso :
    pointEquiv.inverse ⋙ toRingedToposHom.toToposHom.pushforward ≅ p.pushforward

attribute [instance] RingedPointSituation.pointHasSheafComposeForget₂
  RingedPointSituation.pointHasSheafComposeForgetRing

/-- The ringed point associated to a point of a ringed topos: the site of the point with the
trivial topology, carrying the inverse image of the structure sheaf. -/
def ringedPointSituation : RingedPointSituation.{v, u, w, vₚ, uₚ} X p := by
  let e : Sheaf (⊥ : GrothendieckTopology (PointSite.{vₚ, uₚ})) (Type w) ≌ Type w :=
    pointSiteSheafEquiv
  let f : MorphismOfTopoi
      (Sheaf (⊥ : GrothendieckTopology (PointSite.{vₚ, uₚ})) (Type w)) X.Topos :=
    { pushforward := e.functor ⋙ p.pushforward
      inverseImage := p.inverseImage ⋙ e.inverse
      adj := p.adj.comp e.symm.toAdjunction
      preservesFiniteLimits := by
        let _ : PreservesFiniteLimits p.inverseImage := p.preservesFiniteLimits
        exact comp_preservesFiniteLimits _ _ }
  letI : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  let pt : RingedTopos.{vₚ, uₚ, w} :=
    { C := PointSite.{vₚ, uₚ}
      J := ⊥
      O := ⟨inverseImageCommRingPresheaf (⊥ : GrothendieckTopology (PointSite.{vₚ, uₚ}))
        f.inverseImage (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (ringSheaf_mul_comm X),
        Presheaf.isSheaf_bot _⟩ }
  let g : RingedToposHom pt X :=
    { toToposHom := f
      fSharp := ringUnit f (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      fSharpInverseImage := 𝟙 _
      fSharp_adjunct := by
        change (sheafCompose X.J (forget RingCat.{w})).map
            (ringUnit f (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) =
          f.adj.homEquiv (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (Sheaf.ringSheaf
                (inverseImageRingSheaf f (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            ((sheafCompose (⊥ : GrothendieckTopology (PointSite.{vₚ, uₚ}))
              (forget RingCat.{w})).map
                (𝟙 (inverseImageRingSheaf f (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
        rw [CategoryTheory.Functor.map_id]
        exact (homEquiv_id_eq_ringUnit f (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).symm }
  exact
    { point := pt
      pointEquiv := e
      toRingedToposHom := g
      inverseImageIso := Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ e.counitIso ≪≫ Functor.rightUnitor _
      ringIso := Iso.refl _
      ringIso_hom := rfl
      pushforwardIso := (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight e.counitIso _ ≪≫ Functor.leftUnitor _ }

/-- Restriction of scalars does not change the underlying sheaf of abelian groups. -/
def restrictScalarsCompToSheaf {T : Type u} [Category.{v} T] {J : GrothendieckTopology T}
    {R R' : Sheaf J RingCat.{w}} (α : R ⟶ R') :
    SheafOfModules.restrictScalars.{w} α ⋙ SheafOfModules.toSheaf R ≅
      SheafOfModules.toSheaf R' :=
  Iso.refl _

/-! ## Restriction of scalars along an isomorphism of sheaves of rings

Restricting along `α : R ⟶ S` and then along a section `β : S ⟶ R` of it is naturally the
identity. Consequently restriction along an isomorphism of sheaves of rings is an equivalence
of the categories of modules, with restriction along the inverse as its quasi-inverse.
-/

/-- Restricting a presheaf of `S`-modules along `α : R ⟶ S` and then along a section `β : S ⟶ R` of
`α` returns it, naturally. -/
def presheafRestrictScalarsCompIsoId {T : Type u} [Category.{v} T]
    {R S : Tᵒᵖ ⥤ RingCat.{w}} (α : R ⟶ S) (β : S ⟶ R) (h : β ≫ α = 𝟙 S) :
    PresheafOfModules.restrictScalars.{w} α ⋙ PresheafOfModules.restrictScalars.{w} β ≅
      𝟭 (PresheafOfModules.{w} S) := by
  let objectIso (M : PresheafOfModules.{w} S) (Z : Tᵒᵖ) :
      (((PresheafOfModules.restrictScalars.{w} α ⋙
        PresheafOfModules.restrictScalars.{w} β).obj M).obj Z) ≅ M.obj Z := by
    let a := (β.app Z).hom
    let b := (α.app Z).hom
    have hba : b.comp a = RingHom.id (S.obj Z) := by
      simpa using congrArg (fun z ↦ (z.app Z).hom) h
    exact (ModuleCat.restrictScalarsComp'App a b (b.comp a) rfl (M.obj Z)).symm ≪≫
      ModuleCat.restrictScalarsId'App (b.comp a) hba (M.obj Z)
  let iso (M : PresheafOfModules.{w} S) :
      ((PresheafOfModules.restrictScalars.{w} α ⋙
        PresheafOfModules.restrictScalars.{w} β).obj M) ≅ M := by
    let hom :
        ((PresheafOfModules.restrictScalars.{w} α ⋙
          PresheafOfModules.restrictScalars.{w} β).obj M) ⟶ M :=
      PresheafOfModules.Hom.mk (fun Z ↦ (objectIso M Z).hom) (by intro Z Z' g; ext x; rfl)
    let inv : M ⟶
        (PresheafOfModules.restrictScalars.{w} α ⋙
          PresheafOfModules.restrictScalars.{w} β).obj M :=
      PresheafOfModules.Hom.mk (fun Z ↦ (objectIso M Z).inv) (by intro Z Z' g; ext x; rfl)
    refine ⟨hom, inv, ?_, ?_⟩ <;> ext <;> simp [hom, inv, objectIso]
  exact NatIso.ofComponents iso fun _ ↦ by ext; rfl

/-- Restriction of scalars along an isomorphism of presheaves of rings is an equivalence of the
categories of presheaves of modules, with restriction along the inverse isomorphism as its
quasi-inverse. -/
def presheafRestrictScalarsEquivalenceOfIso {T : Type u} [Category.{v} T]
    {R S : Tᵒᵖ ⥤ RingCat.{w}} (e : R ≅ S) :
    PresheafOfModules.{w} R ≌ PresheafOfModules.{w} S := by
  refine ⟨PresheafOfModules.restrictScalars e.inv, PresheafOfModules.restrictScalars e.hom,
    (presheafRestrictScalarsCompIsoId e.inv e.hom (by simp)).symm,
    presheafRestrictScalarsCompIsoId e.hom e.inv (by simp), ?_⟩
  intro M
  ext
  simp [presheafRestrictScalarsCompIsoId, ModuleCat.restrictScalarsComp'App,
    ModuleCat.restrictScalarsId'App]
  rfl

/-- Restriction of scalars along an isomorphism of presheaves of rings is an equivalence of the
categories of presheaves of modules, in the form of a property of the functor. -/
lemma presheafRestrictScalars_isEquivalence {T : Type u} [Category.{v} T]
    {R S : Tᵒᵖ ⥤ RingCat.{w}} (α : R ⟶ S) [IsIso α] :
    (PresheafOfModules.restrictScalars.{w} α).IsEquivalence :=
  (presheafRestrictScalarsEquivalenceOfIso (asIso α).symm).isEquivalence_functor

/-- Restricting a sheaf of `S`-modules along `α : R ⟶ S` and then along a section `β : S ⟶ R` of
`α` returns it, naturally. -/
def sheafRestrictScalarsCompIsoId {T : Type u} [Category.{v} T] {J : GrothendieckTopology T}
    {R S : Sheaf J RingCat.{w}} (α : R ⟶ S) (β : S ⟶ R) (h : β ≫ α = 𝟙 S) :
    SheafOfModules.restrictScalars.{w} α ⋙ SheafOfModules.restrictScalars.{w} β ≅
      𝟭 (SheafOfModules.{w} S) := by
  let e := presheafRestrictScalarsCompIsoId α.hom β.hom (congrArg (fun q : S ⟶ S ↦ q.hom) h)
  refine NatIso.ofComponents (fun M ↦ ⟨⟨(e.app M.val).hom⟩, ⟨(e.app M.val).inv⟩,
    SheafOfModules.hom_ext (e.app M.val).hom_inv_id,
    SheafOfModules.hom_ext (e.app M.val).inv_hom_id⟩) fun φ ↦ ?_
  ext Z x
  exact congrArg (fun g ↦ g.app Z x) (e.hom.naturality φ.val)

/-- Restricting a sheaf of `Q`-modules along `x : P ⟶ Q`, then along `y : O ⟶ P`, then along
`z : Q ⟶ O` returns it, naturally, as soon as the composite `z ≫ y ≫ x` is the identity. -/
noncomputable def sheafRestrictScalarsComp₃IsoId' {T : Type u} [Category.{v} T]
    {J : GrothendieckTopology T} {O P Q : Sheaf J RingCat.{w}}
    (x : P ⟶ Q) (y : O ⟶ P) (z : Q ⟶ O) (h : z ≫ (y ≫ x) = 𝟙 Q) :
    SheafOfModules.restrictScalars.{w} x ⋙ (SheafOfModules.restrictScalars.{w} y ⋙
        SheafOfModules.restrictScalars.{w} z) ≅ 𝟭 (SheafOfModules.{w} Q) :=
  sheafRestrictScalarsCompIsoId (y ≫ x) z h

/-- The three-fold cancellation of restrictions of scalars is the identity on sections. -/
theorem sheafRestrictScalarsComp₃IsoId_val_app' {T : Type u} [Category.{v} T]
    {J : GrothendieckTopology T} {O P Q : Sheaf J RingCat.{w}}
    (x : P ⟶ Q) (y : O ⟶ P) (z : Q ⟶ O) (h : z ≫ (y ≫ x) = 𝟙 Q)
    (M : SheafOfModules.{w} Q) (U : Tᵒᵖ) (m : (M.val.obj U)) :
    ((sheafRestrictScalarsComp₃IsoId' x y z h).hom.app M).val.app U m = m :=
  rfl

/-- Restriction of scalars along an isomorphism of sheaves of rings is an equivalence of the
categories of sheaves of modules. -/
def restrictScalarsEquivalenceOfIso {T : Type u} [Category.{v} T]
    {J : GrothendieckTopology T} {R S : Sheaf J RingCat.{w}} (e : R ≅ S) :
    SheafOfModules.{w} R ≌ SheafOfModules.{w} S := by
  refine ⟨SheafOfModules.restrictScalars e.inv, SheafOfModules.restrictScalars e.hom,
    (sheafRestrictScalarsCompIsoId e.inv e.hom (by simp)).symm,
    sheafRestrictScalarsCompIsoId e.hom e.inv (by simp), ?_⟩
  intro M
  ext
  simp [sheafRestrictScalarsCompIsoId, presheafRestrictScalarsCompIsoId,
    ModuleCat.restrictScalarsComp'App, ModuleCat.restrictScalarsId'App]
  rfl

/-- Restriction of scalars along the inverse of an isomorphism `e` of sheaves of rings is left
adjoint to restriction of scalars along any morphism `α` *equal* to `e.hom`, the equivalence of
`restrictScalarsEquivalenceOfIso` being an adjoint pair. -/
def restrictScalarsAdjunctionOfEq {T : Type u} [Category.{v} T]
    {J : GrothendieckTopology T} {R S : Sheaf J RingCat.{w}} (e : R ≅ S) (α : R ⟶ S)
    (h : α = e.hom) :
    SheafOfModules.restrictScalars.{w} e.inv ⊣ SheafOfModules.restrictScalars.{w} α := by
  subst h
  exact (restrictScalarsEquivalenceOfIso e).toAdjunction

/-- The counit of `restrictScalarsAdjunctionOfEq` is the identity on underlying sheaves of sets. -/
lemma moduleSheafFunctor_map_restrictScalarsAdjunctionOfEq_counit_app {T : Type u}
    [Category.{v} T] {J : GrothendieckTopology T} [J.HasSheafCompose (forget AddCommGrpCat.{w})]
    {R S : Sheaf J RingCat.{w}} (e : R ≅ S) (α : R ⟶ S) (h : α = e.hom)
    (M : SheafOfModules.{w} S) :
    (Sheaf.moduleSheafFunctor S).map ((restrictScalarsAdjunctionOfEq e α h).counit.app M) =
      𝟙 _ := by
  subst h
  apply (sheafToPresheaf J (Type w)).map_injective
  ext Z x
  rfl

section Unit

variable {T : Type u} [Category.{v} T] {J : GrothendieckTopology T} {R S : Sheaf J RingCat.{w}}

/-- The isomorphism `e : R ≅ S` of sheaves of rings, read as a morphism of the underlying sheaves
of abelian groups from the restriction of scalars of `R` as a module over itself to `S` as a module
over itself. -/
def restrictScalarsObjUnitPresheafHom (e : R ≅ S) :
    ((restrictScalarsEquivalenceOfIso e).functor.obj
        (SheafOfModules.unit R)).val.presheaf ⟶ (SheafOfModules.unit S).val.presheaf :=
  Functor.whiskerRight e.hom.hom (forget₂ RingCat.{w} AddCommGrpCat.{w})

/-- `Stacks.Sheaves.RingedPoint.restrictScalarsObjUnitPresheafHom` read in the other direction. -/
def restrictScalarsObjUnitPresheafInv (e : R ≅ S) :
    (SheafOfModules.unit S).val.presheaf ⟶
      ((restrictScalarsEquivalenceOfIso e).functor.obj (SheafOfModules.unit R)).val.presheaf :=
  Functor.whiskerRight e.inv.hom (forget₂ RingCat.{w} AddCommGrpCat.{w})

/-- Restriction of scalars along an isomorphism `e : R ≅ S` of sheaves of rings carries the
structure sheaf to the structure sheaf: `R` as a module over itself, restricted along
`e.inv : S ⟶ R`, is isomorphic via `e` to `S` as a module over itself. -/
def restrictScalarsObjUnitIso (e : R ≅ S) :
    (restrictScalarsEquivalenceOfIso e).functor.obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit S where
  hom.val := PresheafOfModules.homMk (restrictScalarsObjUnitPresheafHom e) fun X r m => by
    have h : (e.hom.hom.app X).hom ((e.inv.hom.app X).hom r) = r :=
      congrArg (fun q : S ⟶ S => (q.hom.app X).hom r) e.inv_hom_id
    exact ((e.hom.hom.app X).hom.map_mul ((e.inv.hom.app X).hom r) m).trans
      (congrArg (fun t => t * (e.hom.hom.app X).hom m) h)
  inv.val := PresheafOfModules.homMk (restrictScalarsObjUnitPresheafInv e)
    fun X r m => (e.inv.hom.app X).hom.map_mul r m
  hom_inv_id := by
    ext X a
    exact congrArg (fun q : R ⟶ R => (q.hom.app X).hom a) e.hom_inv_id
  inv_hom_id := by
    ext X
    exact congrArg (fun q : S ⟶ S => (q.hom.app X).hom 1) e.inv_hom_id

end Unit

namespace RingedPointSituation

variable {X : RingedTopos.{v, u, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})]
  {p : PointOfTopos.{w, v, u} X.J}
  (s : RingedPointSituation.{v, u, w, vₚ, uₚ} X p)

/-- The module-valued stalk at a point of a ringed topos: the inverse image of modules of
Stacks 03D2, with its scalar action read over `O_p` along the identification `p⁻¹O ≅ O_p`. -/
def stalkModules :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O) :=
  inverseImageModules s.toRingedToposHom.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
    SheafOfModules.restrictScalars s.ringIso.inv

/-- The adjunction `p⁻¹ ⊣ p_*` of the point, as the ringed point situation presents it: the
adjunction of the morphism of topoi out of the ringed point, composed with `Sh(pt) = Sets` and read
through the identification of its inverse image with the stalk functor. Its left adjoint is the
stalk functor `p⁻¹` on the nose. -/
def inverseImageAdjunction :
    p.inverseImage ⊣ s.pointEquiv.inverse ⋙ s.toRingedToposHom.toToposHom.pushforward :=
  Adjunction.ofNatIsoLeft
    (s.toRingedToposHom.toToposHom.adj.comp s.pointEquiv.toAdjunction) s.inverseImageIso

/-- The canonical identification of the direct image along the morphism out of the ringed point
with the skyscraper functor of the point, as two right adjoints of the stalk functor `p⁻¹`. -/
def pointPushforwardIso :
    s.pointEquiv.inverse ⋙ s.toRingedToposHom.toToposHom.pushforward ≅ p.pushforward :=
  s.inverseImageAdjunction.rightAdjointUniq p.adj

/-- The direct image of modules along the morphism of ringed topoi out of the ringed point has
underlying sheaf the skyscraper sheaf of the point, naturally in the module. -/
def pushforwardUnderlyingStalkIso :
    pushforwardModules s.toRingedToposHom ⋙
        Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≅
      Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O) ⋙
        s.pointEquiv.functor ⋙ p.pushforward :=
  let f := s.toRingedToposHom.toToposHom
  let hPush : f.pushforward ≅ s.pointEquiv.functor ⋙ p.pushforward :=
    (Functor.leftUnitor f.pushforward).symm ≪≫
      Functor.isoWhiskerRight s.pointEquiv.unitIso f.pushforward ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft s.pointEquiv.functor s.pushforwardIso
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp) ≪≫
    Functor.isoWhiskerLeft
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O)) hPush

/-- The underlying sheaf of the module-valued stalk is the inverse image of the underlying sheaf,
naturally in the module. -/
def stalkModulesUnderlyingImageIso :
    s.stalkModules ⋙ Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O) ≅
      Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        s.toRingedToposHom.toToposHom.inverseImage :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (inverseImageModules s.toRingedToposHom.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (restrictScalarsCompToSheaf s.ringIso.inv)
          (sheafCompose s.point.J (forget AddCommGrpCat.{w}))) ≪≫
    (Stacks.Sheaves.ToposPullback.pullbackModule s.point.J X.J
      s.toRingedToposHom.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).moduleIso

/-- The module-valued stalk has underlying sheaf the stalk of the underlying sheaf, naturally in
the module. -/
def stalkModulesUnderlyingIso :
    s.stalkModules ⋙ Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O) ⋙
        s.pointEquiv.functor ≅
      Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙ p.inverseImage :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerRight s.stalkModulesUnderlyingImageIso s.pointEquiv.functor ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      s.inverseImageIso

section Pullback

variable [HasWeakSheafify s.point.J AddCommGrpCat.{w}]
  [s.point.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- At a ringed point, restriction of scalars along the inverse of the structure map is left
adjoint to restriction of scalars along the structure map itself. -/
def ringIsoRestrictScalarsAdjunction :
    SheafOfModules.restrictScalars s.ringIso.inv ⊣
      SheafOfModules.restrictScalars (commRingSheafMap s.point.J
        (fSharpCommRing s.toRingedToposHom)
        (inverseImageRingSheaf s.toRingedToposHom.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O).property) :=
  restrictScalarsAdjunctionOfEq s.ringIso _
    ((commRingSheafMap_fSharpCommRing s.toRingedToposHom).trans s.ringIso_hom.symm)

omit [HasWeakSheafify s.point.J AddCommGrpCat.{w}]
  [s.point.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The counit of `ringIsoRestrictScalarsAdjunction` is the identity on underlying sheaves of
sets. -/
lemma moduleSheafFunctor_map_ringIsoRestrictScalarsAdjunction_counit_app
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O)).map
        (s.ringIsoRestrictScalarsAdjunction.counit.app M) = 𝟙 _ :=
  moduleSheafFunctor_map_restrictScalarsAdjunctionOfEq_counit_app _ _ _ M

/-- At a ringed point, extension of scalars along the structure map is restriction of scalars along
its inverse. -/
def extendScalarsFSharpIsoRestrictScalars :
    extendScalarsFSharp s.toRingedToposHom ≅
      SheafOfModules.restrictScalars s.ringIso.inv :=
  (extendRestrictScalarsAdjunction s.point.J (fSharpCommRing s.toRingedToposHom)
    (inverseImageRingSheaf s.toRingedToposHom.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O).property).leftAdjointUniq
      s.ringIsoRestrictScalarsAdjunction

/-- The pullback of modules to a ringed point is the module-valued stalk: the canonical
identification `p^*M ≅ p⁻¹M` is linear over `O_p` and natural in the module. -/
def pullbackStalkIso :
    s.toRingedToposHom.pullbackModules ≅ s.stalkModules :=
  Functor.isoWhiskerLeft
    (inverseImageModules s.toRingedToposHom.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    s.extendScalarsFSharpIsoRestrictScalars

/-- The component of `pullbackStalkIso` is the component of `extendScalarsFSharpIsoRestrictScalars`
at the inverse image of the module. -/
lemma pullbackStalkIso_hom_app
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    s.pullbackStalkIso.hom.app N =
      s.extendScalarsFSharpIsoRestrictScalars.hom.app
        ((inverseImageModules s.toRingedToposHom.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj N) := rfl

/-- The underlying sheaf of the pullback of a module to the ringed point is the inverse image of
its underlying sheaf, naturally in the module. -/
def pullbackUnderlyingImageIso :
    s.toRingedToposHom.pullbackModules ⋙
        Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O) ≅
      Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        s.toRingedToposHom.toToposHom.inverseImage :=
  Functor.isoWhiskerRight s.pullbackStalkIso
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O)) ≪≫
    s.stalkModulesUnderlyingImageIso

/-- The component of `pullbackUnderlyingImageIso` is the underlying map of the component of
`pullbackStalkIso`. -/
lemma pullbackUnderlyingImageIso_hom_app
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    s.pullbackUnderlyingImageIso.hom.app N =
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O)).map
        (s.pullbackStalkIso.hom.app N) := rfl

/-- The pullback of modules to a ringed point has, naturally, the underlying stalk of the original
module. -/
def pullbackUnderlyingIso :
    s.toRingedToposHom.pullbackModules ⋙
        Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O) ⋙
          s.pointEquiv.functor ≅
      Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙ p.inverseImage :=
  Functor.isoWhiskerRight s.pullbackStalkIso
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O) ⋙
        s.pointEquiv.functor) ≪≫
    s.stalkModulesUnderlyingIso

end Pullback

end RingedPointSituation

end Stacks.Sheaves.RingedPoint
