module

public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleCokernelFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleSliceEssImage
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleSliceBaseChange
public import StacksFrontier.CategoryTheory.Sites.Descent.TestObjectDescentData

/-!
# The transitions of the descent datum of Tag 03OJ

Let `S` be a scheme and let a site `C` of schemes over `S` satisfy the conditions of Tag 03OJ.
The member-local step (`Stacks.Sites.exists_cover_cokernel_iso_sliceModuleOver`) presents a
quasi-coherent `𝒪`-module `𝒢` on the site, on the slice at each member `V` of a covering family
of the final object, as `coker(φ)ᵃ` for a morphism `φ` of free modules on the underlying scheme of
`V`.  This file builds the transition isomorphisms which glue those cokernels into a descent datum
for the family of structure morphisms of the members.

## The transitions

Fix two members `V`, `V'` with their local data, an object `T` of the site, and morphisms of
schemes `α : T ⟶ V`, `β : T ⟶ V'` over `S`.  A morphism `χ : α⁺ coker(φ) ⟶ β⁺ coker(φ')` is
**good** (`Stacks.Sites.SliceCokernelDatum.Good`) when, after pulling it back to any object `W` of
the site, it commutes with the two local identifications of the sections over `W` with `𝒢(W)`.
Good morphisms are unique (`Stacks.Sites.SliceCokernelDatum.Good.ext`): two of them have the same
associated module on the slice at `T`, and Descent, Lemma 0GN7 over an arbitrary base is faithful
for a pulled-back cokernel of free modules.  The identity is good, good morphisms compose, and
the pullback of a good morphism is good; so once good morphisms exist the three laws of a descent
datum hold by uniqueness alone.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.transport`: a morphism `α⁺ A ⟶ β⁺ B` pulled back along `g`,
  read between the pullbacks along the composites.
* `Stacks.Sites.SliceCokernelDatum`: the local datum on the slice at one object.
* `Stacks.Sites.SliceCokernelDatum.Good`: the defining property of the transitions.

## Main results

* `AlgebraicGeometry.modulePullbackPseudofunctor_pullHom_eq`: the pullback of a morphism of
  pullbacks by the pseudofunctor of sheaves of modules is `transport`.
* `Stacks.Sites.SliceCokernelDatum.Good.ext`: uniqueness of good morphisms.
* `Stacks.Sites.SliceCokernelDatum.good_id`, `…Good.comp` and `…Good.pullHom`: the identity is
  good, and goodness is stable under composition and pullback.

## References

* [Stacks Project, Tag 03OJ](https://stacks.math.columbia.edu/tag/03OJ)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X X₁ X₂ Y : Scheme.{u}} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂} {M₁ : X₁.Modules}
  {M₂ : X₂.Modules}

/-- **A morphism of pullbacks, pulled back along `g` and read between the pullbacks along the
composites.**  For `χ : f₁⁺ M₁ ⟶ f₂⁺ M₂` and `g : Y ⟶ X`, this is `g⁺ χ` conjugated by the
comparisons `g⁺ f₁⁺ ≅ (g ≫ f₁)⁺` and `g⁺ f₂⁺ ≅ (g ≫ f₂)⁺`, followed by the identifications of
the composites with two given morphisms. -/
public noncomputable def transport (g : Y ⟶ X) {gf₁ : Y ⟶ X₁} {gf₂ : Y ⟶ X₂}
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂)
    (χ : (Scheme.Modules.pullback f₁).obj M₁ ⟶ (Scheme.Modules.pullback f₂).obj M₂) :
    (Scheme.Modules.pullback gf₁).obj M₁ ⟶ (Scheme.Modules.pullback gf₂).obj M₂ :=
  (Scheme.Modules.pullbackCongr h₁).inv.app M₁ ≫ (Scheme.Modules.pullbackComp g f₁).inv.app M₁ ≫
    (Scheme.Modules.pullback g).map χ ≫ (Scheme.Modules.pullbackComp g f₂).hom.app M₂ ≫
      (Scheme.Modules.pullbackCongr h₂).hom.app M₂

/-- `transport` of a composite is the composite of the transports. -/
public theorem transport_comp {X₃ : Scheme.{u}} {f₃ : X ⟶ X₃} {M₃ : X₃.Modules} (g : Y ⟶ X)
    {gf₁ : Y ⟶ X₁} {gf₂ : Y ⟶ X₂} {gf₃ : Y ⟶ X₃} (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂)
    (h₃ : g ≫ f₃ = gf₃)
    (χ : (Scheme.Modules.pullback f₁).obj M₁ ⟶ (Scheme.Modules.pullback f₂).obj M₂)
    (ψ : (Scheme.Modules.pullback f₂).obj M₂ ⟶ (Scheme.Modules.pullback f₃).obj M₃) :
    transport g h₁ h₃ (χ ≫ ψ) = transport g h₁ h₂ χ ≫ transport g h₂ h₃ ψ := by
  simp only [transport, Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]

/-- `transport` of the identity along equal composites is the identity. -/
public theorem transport_id (g : Y ⟶ X) {gf₁ : Y ⟶ X₁} (h₁ : g ≫ f₁ = gf₁) (h₁' : g ≫ f₁ = gf₁) :
    transport g h₁ h₁' (𝟙 ((Scheme.Modules.pullback f₁).obj M₁)) = 𝟙 _ := by
  simp only [transport]
  rw [(Scheme.Modules.pullback g).map_id]
  simp

/-- The pullback of a morphism of pullbacks, recovered from its `transport`. -/
public theorem pullback_map_eq_transport (g : Y ⟶ X) {gf₁ : Y ⟶ X₁} {gf₂ : Y ⟶ X₂}
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂)
    (χ : (Scheme.Modules.pullback f₁).obj M₁ ⟶ (Scheme.Modules.pullback f₂).obj M₂) :
    (Scheme.Modules.pullback g).map χ =
      (Scheme.Modules.pullbackComp g f₁).hom.app M₁ ≫ (Scheme.Modules.pullbackCongr h₁).hom.app M₁ ≫
        transport g h₁ h₂ χ ≫ (Scheme.Modules.pullbackCongr h₂).inv.app M₂ ≫
          (Scheme.Modules.pullbackComp g f₂).inv.app M₂ := by
  simp only [transport, Category.assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
  exact (Category.comp_id _).symm

end Scheme.Modules

/-- **The pullback of a morphism of pullbacks by the pseudofunctor of sheaves of modules is
`AlgebraicGeometry.Scheme.Modules.transport`.**  This is
`AlgebraicGeometry.modulePullbackPseudofunctor_pullHom` with the two modules and the two
morphisms to the targets allowed to differ. -/
public theorem modulePullbackPseudofunctor_pullHom_eq {X X₁ X₂ Y : Scheme.{u}} {f₁ : X ⟶ X₁}
    {f₂ : X ⟶ X₂} {M₁ : X₁.Modules} {M₂ : X₂.Modules}
    (φ : (Scheme.Modules.pullback f₁).obj M₁ ⟶ (Scheme.Modules.pullback f₂).obj M₂)
    (g : Y ⟶ X) (gf₁ : Y ⟶ X₁) (gf₂ : Y ⟶ X₂) (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    pullHom (F := modulePullbackPseudofunctor) φ g gf₁ gf₂ h₁ h₂ =
      Scheme.Modules.transport g h₁ h₂ φ := by
  subst h₁ h₂
  simp only [Scheme.Modules.transport, Scheme.Modules.pullbackCongr, eqToIso_refl,
    Iso.refl_inv, Iso.refl_hom, NatTrans.id_app, Category.id_comp, Category.comp_id]
  rfl



/-- Global sections of the components of a natural isomorphism of functors to modules on a
scheme cancel. -/
public theorem natIso_app_top_inv_hom {D : Type*} [Category D] {Y : Scheme.{u}}
    {G G' : D ⥤ Y.Modules} (e : G ≅ G') (P : D) (x : Γ(G'.obj P, ⊤)) :
    ((e.hom.app P).app ⊤) (((e.inv.app P).app ⊤) x) = x := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id_app]
  rfl

/-- Global sections of the components of a natural isomorphism of functors to modules on a
scheme cancel. -/
public theorem natIso_app_top_hom_inv {D : Type*} [Category D] {Y : Scheme.{u}}
    {G G' : D ⥤ Y.Modules} (e : G ≅ G') (P : D) (x : Γ(G.obj P, ⊤)) :
    ((e.inv.app P).app ⊤) (((e.hom.app P).app ⊤) x) = x := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id_app]
  rfl

/-- **`AlgebraicGeometry.pullbackSectionsMap` along an arrow with identity underlying morphism**
is the transport along the equality of the two structure morphisms. -/
public theorem pullbackSectionsMap_homMk_id {Y A : Scheme.{u}} (F : Y.Modules) {f₁ f₂ : A ⟶ Y}
    (w : 𝟙 A ≫ f₂ = f₁) (h : f₂ = f₁) (m : Γ((Scheme.Modules.pullback f₂).obj F, ⊤)) :
    pullbackSectionsMap F (Over.homMk (𝟙 A) w : Over.mk f₁ ⟶ Over.mk f₂) m =
      ((Scheme.Modules.pullbackCongr h).hom.app F).app ⊤ m := by
  subst h
  have h1 : (Over.homMk (𝟙 A) w : Over.mk f₂ ⟶ Over.mk f₂) = 𝟙 _ := by ext; rfl
  rw [h1]
  exact congr($((quasiCoherentPresheafConstruction Y F).functor.map_id (op (Over.mk f₂))) m)

/-- Pulling back along `f` and then `g`, undoing the comparison, and reading the sections through
the identity of the underlying scheme recovers the section.  Stated at abstract morphisms, where
the two spellings of the composite agree on the nose. -/
public theorem pullbackSectionsMap_comp_inv {A Z Y : Scheme.{u}} (F : Y.Modules) (f : A ⟶ Z)
    (g : Z ⟶ Y) {k : A ⟶ Y} (h : f ≫ g = k) (x : Γ((Scheme.Modules.pullback k).obj F, ⊤)) :
    pullbackSectionsMap F
        (Over.homMk (𝟙 A) ((Category.id_comp _).trans h) : Over.mk k ⟶ Over.mk (f ≫ g))
        (((Scheme.Modules.pullbackComp f g).hom.app F).app ⊤
          (((Scheme.Modules.pullbackComp f g).inv.app F).app ⊤
            (((Scheme.Modules.pullbackCongr h).inv.app F).app ⊤ x))) = x := by
  rw [natIso_app_top_inv_hom]
  exact (pullbackSectionsMap_homMk_id F _ h _).trans
    (natIso_app_top_inv_hom (Scheme.Modules.pullbackCongr h) F x)

/-- **The pullback of a cokernel of free modules is a cokernel of free modules.**  Pullback is
a left adjoint, so it preserves cokernels, and it carries free modules to free modules. -/
public noncomputable def pullbackCokernelFreeIso {X Y : Scheme.{u}} (g : Y ⟶ X) {L L' : Type u}
    (φ : SheafOfModules.free (R := X.ringCatSheaf) L' ⟶
      SheafOfModules.free (R := X.ringCatSheaf) L) :
    (Scheme.Modules.pullback g).obj (cokernel (C := X.Modules) φ) ≅
      cokernel (C := Y.Modules) ((Scheme.Modules.pullbackFreeIso g L').inv ≫
        (Scheme.Modules.pullback g).map φ ≫ (Scheme.Modules.pullbackFreeIso g L).hom) := by
  have : (Scheme.Modules.pullback g).IsLeftAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).isLeftAdjoint
  exact PreservesCokernel.iso (Scheme.Modules.pullback g) φ ≪≫
    cokernel.mapIso _ _ (Scheme.Modules.pullbackFreeIso g L') (Scheme.Modules.pullbackFreeIso g L)
      (Iso.hom_inv_id_assoc _ _).symm


/-- `AlgebraicGeometry.Scheme.Modules.transport` along the identity is the identity. -/
public theorem Scheme.Modules.transport_id_left {X X₁ X₂ : Scheme.{u}} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}
    {M₁ : X₁.Modules} {M₂ : X₂.Modules} (h₁ : 𝟙 X ≫ f₁ = f₁) (h₂ : 𝟙 X ≫ f₂ = f₂)
    (χ : (Scheme.Modules.pullback f₁).obj M₁ ⟶ (Scheme.Modules.pullback f₂).obj M₂) :
    Scheme.Modules.transport (𝟙 X) h₁ h₂ χ = χ :=
  (modulePullbackPseudofunctor_pullHom_eq χ (𝟙 X) f₁ f₂ h₁ h₂).symm.trans
    (CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_id
      (F := modulePullbackPseudofunctor) χ)

end AlgebraicGeometry

namespace Stacks.Sites

open _root_.AlgebraicGeometry

attribute [local instance] CategoryTheory.hasWeakSheafify_addCommGrpCat_of_essentiallySmall
  CategoryTheory.wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall
  CategoryTheory.hasSheafify_addCommGrpCat_of_essentiallySmall

variable (S : Scheme.{u}) {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S)
  (K : Precoverage C) [K.HasPullbacks] [K.IsStableUnderBaseChange]
  (hSh : ∀ (X : C) (F : ((toOver.obj X).left).Modules) (_ : F.IsQuasicoherent),
    Presheaf.IsSheaf (K.toGrothendieck.over X)
      (associatedPresheaf ((toOver.obj X).left) F (sliceToOver S toOver X)))
  (hR : Presheaf.IsSheaf K.toGrothendieck (structurePresheaf S toOver))
  (M : SheafOfModules.{u} (siteStructureSheaf S toOver K.toGrothendieck hR))


/-- **Descent, Lemma 0GN7 transfers along an isomorphism of the source.** -/
public theorem bijective_associatedModuleMap_of_iso {S' : Scheme.{u}} {C' : Type (u + 1)}
    [Category.{u} C'] (toOver' : C' ⥤ Over S') {P Q N : S'.Modules} [P.IsQuasicoherent]
    [Q.IsQuasicoherent] [N.IsQuasicoherent] (ι : P ≅ Q)
    (h : Function.Bijective fun χ : Q ⟶ N => associatedModuleMap S' toOver' χ) :
    Function.Bijective fun χ : P ⟶ N => associatedModuleMap S' toOver' χ := by
  have hAB : associatedModuleMap S' toOver' ι.hom ≫ associatedModuleMap S' toOver' ι.inv = 𝟙 _ := by
    rw [← associatedModuleMap_comp, ι.hom_inv_id, associatedModuleMap_id]
  have hBA : associatedModuleMap S' toOver' ι.inv ≫ associatedModuleMap S' toOver' ι.hom = 𝟙 _ := by
    rw [← associatedModuleMap_comp, ι.inv_hom_id, associatedModuleMap_id]
  have heq : (fun χ : P ⟶ N => associatedModuleMap S' toOver' χ) =
      (fun c => associatedModuleMap S' toOver' ι.hom ≫ c) ∘
        (fun χ : Q ⟶ N => associatedModuleMap S' toOver' χ) ∘ (fun χ : P ⟶ N => ι.inv ≫ χ) := by
    funext χ
    simp only [Function.comp_apply, ← associatedModuleMap_comp, Iso.hom_inv_id_assoc]
  rw [heq]
  refine Function.Bijective.comp ?_ (h.comp ?_)
  · exact (Iso.homFromEquiv ⟨_, _, hBA, hAB⟩).bijective
  · exact ι.homFromEquiv.bijective

/-- **The local datum of the third assertion of Tag 03OJ on the slice at `X`**: a morphism `φ`
of free modules on the underlying scheme of `X` and an isomorphism of `coker(φ)ᵃ`, formed on the
slice site, with the restriction of `M` to the slice.  This is what
`Stacks.Sites.exists_cover_cokernel_iso_sliceModuleOver` produces on each member of a covering
family of the final object. -/
public structure SliceCokernelDatum (X : C) where
  /-- The generators. -/
  L : Type u
  /-- The relations. -/
  L' : Type u
  /-- The presenting morphism of free modules. -/
  φ : SheafOfModules.free (R := ((toOver.obj X).left).ringCatSheaf) L' ⟶
    SheafOfModules.free (R := ((toOver.obj X).left).ringCatSheaf) L
  /-- The identification of `coker(φ)ᵃ` with the restriction of `M` to the slice. -/
  iso : siteAssociatedModule ((toOver.obj X).left) (cokernel (C := ((toOver.obj X).left).Modules) φ)
      (sliceToOver S toOver X) (K.toGrothendieck.over X)
      (isSheaf_structurePresheaf_sliceToOver S toOver X K.toGrothendieck hR)
      (hSh X _ inferInstance) ≅
    sliceModuleOver S toOver X K.toGrothendieck hR M

namespace SliceCokernelDatum

variable {S toOver K hSh hR M}

/-- The local quasi-coherent module of the datum: the cokernel of its presenting morphism. -/
public noncomputable abbrev F {X : C} (d : SliceCokernelDatum S toOver K hSh hR M X) :
    ((toOver.obj X).left).Modules :=
  cokernel (C := ((toOver.obj X).left).Modules) d.φ

/-- The datum's isomorphism at the object `a : W ⟶ X` of the slice, on sections. -/
public noncomputable def θIso {X : C} (d : SliceCokernelDatum S toOver K hSh hR M X) {W : C}
    (a : W ⟶ X) := (PresheafOfModules.evaluation _ (op (Over.mk a))).mapIso
  ((SheafOfModules.forget _).mapIso d.iso)

/-- **The local identification of sections.**  For an arrow `a : W ⟶ X` of the site, the
sections over `W` of the pullback of the local module along `a` are identified with `M(W)`: this
is the component of the datum's isomorphism at the object `a` of the slice. -/
public noncomputable def θ {X : C} (d : SliceCokernelDatum S toOver K hSh hR M X) {W : C}
    (a : W ⟶ X) :
    Γ((Scheme.Modules.pullback (toOver.map a).left).obj d.F, ⊤) → M.val.obj (op W) :=
  fun y => (d.θIso a).hom y

/-- The inverse of `Stacks.Sites.SliceCokernelDatum.θ`. -/
public noncomputable def θinv {X : C} (d : SliceCokernelDatum S toOver K hSh hR M X) {W : C}
    (a : W ⟶ X) :
    M.val.obj (op W) → Γ((Scheme.Modules.pullback (toOver.map a).left).obj d.F, ⊤) :=
  fun m => (d.θIso a).inv m

omit [K.HasPullbacks] [K.IsStableUnderBaseChange] in
/-- `Stacks.Sites.SliceCokernelDatum.θinv` is a left inverse of `θ`. -/
public theorem θinv_θ {X : C} (d : SliceCokernelDatum S toOver K hSh hR M X) {W : C}
    (a : W ⟶ X) (y : Γ((Scheme.Modules.pullback (toOver.map a).left).obj d.F, ⊤)) :
    d.θinv a (d.θ a y) = y :=
  (d.θIso a).hom_inv_id_apply y

omit [K.HasPullbacks] [K.IsStableUnderBaseChange] in
/-- `Stacks.Sites.SliceCokernelDatum.θinv` is a right inverse of `θ`. -/
public theorem θ_θinv {X : C} (d : SliceCokernelDatum S toOver K hSh hR M X) {W : C}
    (a : W ⟶ X) (m : M.val.obj (op W)) :
    d.θ a (d.θinv a m) = m :=
  (d.θIso a).inv_hom_id_apply m

omit [K.HasPullbacks] [K.IsStableUnderBaseChange] in
/-- The local identification of sections is injective. -/
public theorem θ_injective {X : C} (d : SliceCokernelDatum S toOver K hSh hR M X) {W : C}
    (a : W ⟶ X) : Function.Injective (d.θ a) :=
  fun y y' h => (d.θinv_θ a y).symm.trans ((congrArg (d.θinv a) h).trans (d.θinv_θ a y'))

/-- **The defining property of the transitions of the descent datum of Tag 03OJ.**  A morphism
`χ : α⁺ coker(φ) ⟶ β⁺ coker(φ')` over an object `T` of the site is good when, transported to any
object `W` of the site mapping to `T` over `S`, it carries the local identification of the
sections over `W` given by the datum at `X` to the one given by the datum at `Y`. -/
public def Good {X Y T : C} (d : SliceCokernelDatum S toOver K hSh hR M X)
    (d' : SliceCokernelDatum S toOver K hSh hR M Y)
    (α : (toOver.obj T).left ⟶ (toOver.obj X).left) (β : (toOver.obj T).left ⟶ (toOver.obj Y).left)
    (χ : (Scheme.Modules.pullback α).obj d.F ⟶ (Scheme.Modules.pullback β).obj d'.F) : Prop :=
  ∀ (W : C) (g : (toOver.obj W).left ⟶ (toOver.obj T).left)
    (_ : g ≫ (toOver.obj T).hom = (toOver.obj W).hom) (a : W ⟶ X) (b : W ⟶ Y)
    (ha : g ≫ α = (toOver.map a).left) (hb : g ≫ β = (toOver.map b).left)
    (y : Γ((Scheme.Modules.pullback (toOver.map a).left).obj d.F, ⊤)),
    d'.θ b ((Scheme.Modules.transport g ha hb χ).app ⊤ y) = d.θ a y

/-- The underlying morphism of schemes of a composite arrow of the site. -/
private theorem map_left_comp_eq {W X Y : C} (u : W ⟶ X) (v : X ⟶ Y) :
    (toOver.map u).left ≫ (toOver.map v).left = (toOver.map (u ≫ v)).left := by
  rw [Functor.map_comp, Over.comp_left]

variable [toOver.Full] [toOver.Faithful]

omit [toOver.Full] in
/-- An arrow of the site is determined by its underlying morphism of schemes. -/
public theorem eq_of_map_left_eq {W X : C} {a b : W ⟶ X}
    (h : (toOver.map a).left = (toOver.map b).left) : a = b :=
  toOver.map_injective (Over.OverMorphism.ext h)

omit [toOver.Faithful] in
/-- **A morphism of schemes over `S` between the underlying schemes of two objects of the site
comes from an arrow of the site.**  This is condition (1) of Tag 03OJ. -/
public theorem exists_map_left_eq {W X : C} (g : (toOver.obj W).left ⟶ (toOver.obj X).left)
    (hg : g ≫ (toOver.obj X).hom = (toOver.obj W).hom) : ∃ a : W ⟶ X, (toOver.map a).left = g :=
  ⟨toOver.preimage (Over.homMk g hg), by rw [toOver.map_preimage]; rfl⟩

omit [toOver.Full] [K.HasPullbacks] [K.IsStableUnderBaseChange] in
/-- **The identity is good.** -/
public theorem good_id {X T : C} (d : SliceCokernelDatum S toOver K hSh hR M X)
    (α : (toOver.obj T).left ⟶ (toOver.obj X).left) :
    Good d d α α (𝟙 _) := by
  intro W g _ a b ha hb y
  obtain rfl : a = b := eq_of_map_left_eq (toOver := toOver) (ha.symm.trans hb)
  rw [Scheme.Modules.transport_id]
  rfl

omit [toOver.Faithful] [K.HasPullbacks] [K.IsStableUnderBaseChange] in
/-- **Good morphisms compose.** -/
public theorem Good.comp {X Y Z T : C} {d : SliceCokernelDatum S toOver K hSh hR M X}
    {d' : SliceCokernelDatum S toOver K hSh hR M Y}
    {d'' : SliceCokernelDatum S toOver K hSh hR M Z}
    {α : (toOver.obj T).left ⟶ (toOver.obj X).left}
    {β : (toOver.obj T).left ⟶ (toOver.obj Y).left}
    {γ : (toOver.obj T).left ⟶ (toOver.obj Z).left}
    (hβ : β ≫ (toOver.obj Y).hom = (toOver.obj T).hom)
    {χ : (Scheme.Modules.pullback α).obj d.F ⟶ (Scheme.Modules.pullback β).obj d'.F}
    {ψ : (Scheme.Modules.pullback β).obj d'.F ⟶ (Scheme.Modules.pullback γ).obj d''.F}
    (hχ : Good d d' α β χ) (hψ : Good d' d'' β γ ψ) : Good d d'' α γ (χ ≫ ψ) := by
  intro W g hg a c ha hc y
  obtain ⟨b, hb⟩ := exists_map_left_eq (toOver := toOver) (g ≫ β) (by rw [Category.assoc, hβ, hg])
  rw [Scheme.Modules.transport_comp g ha hb.symm hc χ ψ, Scheme.Modules.Hom.comp_app]
  exact (hψ W g hg b c hb.symm hc _).trans (hχ W g hg a b ha hb.symm y)

omit [toOver.Full] [toOver.Faithful] [K.HasPullbacks] [K.IsStableUnderBaseChange] in
/-- **The pullback of a good morphism is good.**  Its transport to `W` is the transport of the
original morphism along the composite, by `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat`
`.pullHom_pullHom`. -/
public theorem Good.pullHom {X Y T T' : C} {d : SliceCokernelDatum S toOver K hSh hR M X}
    {d' : SliceCokernelDatum S toOver K hSh hR M Y}
    {α : (toOver.obj T).left ⟶ (toOver.obj X).left}
    {β : (toOver.obj T).left ⟶ (toOver.obj Y).left}
    {χ : (Scheme.Modules.pullback α).obj d.F ⟶ (Scheme.Modules.pullback β).obj d'.F}
    (hχ : Good d d' α β χ) (c : (toOver.obj T').left ⟶ (toOver.obj T).left)
    (hc : c ≫ (toOver.obj T).hom = (toOver.obj T').hom)
    (α' : (toOver.obj T').left ⟶ (toOver.obj X).left)
    (β' : (toOver.obj T').left ⟶ (toOver.obj Y).left) (h₁ : c ≫ α = α') (h₂ : c ≫ β = β') :
    Good d d' α' β'
      (CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := modulePullbackPseudofunctor) χ c α' β' h₁ h₂) := by
  intro W g hg a b ha hb y
  have key : Scheme.Modules.transport g ha hb
      (CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := modulePullbackPseudofunctor) χ c α' β' h₁ h₂) =
      Scheme.Modules.transport (g ≫ c) (by rw [Category.assoc, h₁, ha])
        (by rw [Category.assoc, h₂, hb]) χ := by
    refine (modulePullbackPseudofunctor_pullHom_eq _ g _ _ ha hb).symm.trans ?_
    refine Eq.trans ?_ (modulePullbackPseudofunctor_pullHom_eq χ (g ≫ c) _ _ _ _)
    exact CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_pullHom _ _ _ _ _ _ _
      h₁ h₂ ha hb
  rw [key]
  exact hχ W (g ≫ c) (by rw [Category.assoc, hc, hg]) a b _ _ y


/-! ### The local identifications on the slice at an object -/

/-- **Comparison of the two routes from the slice at `T` to the schemes over `X`**, for an arrow
`a : T ⟶ X` of the site: reading an object of the slice at `T` as a scheme over `T` and composing
with `a`, or composing with `a` in the site first.  The underlying schemes agree; the structure
morphisms agree by functoriality of `toOver`. -/
public def sliceOverMapIso {T X : C} (a : T ⟶ X) :
    sliceToOver S toOver T ⋙ Over.map (toOver.map a).left ≅ Over.map a ⋙ sliceToOver S toOver X :=
  NatIso.ofComponents
    (fun T' => Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ (toOver.map (T'.hom ≫ a)).left = (toOver.map T'.hom).left ≫ (toOver.map a).left
      rw [Category.id_comp, Functor.map_comp, Over.comp_left]))
    (fun {T₁ T₂} v => Over.OverMorphism.ext (by
      change (toOver.map v.left).left ≫ 𝟙 _ = 𝟙 _ ≫ (toOver.map v.left).left
      exact (Category.comp_id _).trans (Category.id_comp _).symm))

/-- **The local identification of sections on the slice at `T`**, for an arrow `a : T ⟶ X` of
the site and the datum at `X`: the presheaf of sections of the pullback of the local module along
`a`, on the slice at `T`, is the restriction of `M`.  It is the base change of the presheaf of
Tag 03DS along `a` (`Stacks.Sites.quasiCoherentPresheafBaseChangeIso`), the comparison
`Stacks.Sites.SliceCokernelDatum.sliceOverMapIso`, and the datum's isomorphism restricted along
`CategoryTheory.Over.map a`. -/
public noncomputable def sectionsIso {X : C} (d : SliceCokernelDatum S toOver K hSh hR M X)
    {T : C} (a : T ⟶ X) :
    associatedPresheaf ((toOver.obj T).left)
        ((Scheme.Modules.pullback (toOver.map a).left).obj d.F) (sliceToOver S toOver T) ≅
      (Over.forget T).op ⋙ M.val.presheaf :=
  (Functor.isoWhiskerLeft (sliceToOver S toOver T).op
      (quasiCoherentPresheafBaseChangeIso d.F (Over.mk (toOver.map a).left))).symm ≪≫
    Functor.isoWhiskerRight (NatIso.op (sliceOverMapIso a)).symm
      (quasiCoherentPresheafFunctor _ d.F) ≪≫
    Functor.isoWhiskerLeft (Over.map a).op
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).mapIso d.iso) ≪≫
    (Iso.refl ((Over.forget T).op ⋙ M.val.presheaf) :
      (Over.map a).op ⋙ (sliceModuleOver S toOver X K.toGrothendieck hR M).val.presheaf ≅ _)

omit [toOver.Full] [toOver.Faithful] [K.HasPullbacks] [K.IsStableUnderBaseChange] in
/-- **The local identification of sections on the slice at `T`, on a section.** -/
public theorem sectionsIso_hom_app_apply {X : C} (d : SliceCokernelDatum S toOver K hSh hR M X)
    {T : C} (a : T ⟶ X) (T' : Over T)
    (m : Γ((Scheme.Modules.pullback (toOver.map T'.hom).left).obj
      ((Scheme.Modules.pullback (toOver.map a).left).obj d.F), ⊤)) :
    (d.sectionsIso a).hom.app (op T') m =
      d.θ (T'.hom ≫ a) (pullbackSectionsMap d.F ((sliceOverMapIso a).inv.app T')
        (((Scheme.Modules.pullbackComp (toOver.map T'.hom).left (toOver.map a).left).hom.app
          d.F).app ⊤ m)) :=
  rfl


/-- **The local identification of sections on the slice at `T`, as an isomorphism of presheaves
of modules.** -/
public noncomputable def sectionsModuleIso {X : C}
    (d : SliceCokernelDatum S toOver K hSh hR M X) {T : C} (a : T ⟶ X) :
    (siteAssociatedModule ((toOver.obj T).left)
        ((Scheme.Modules.pullback (toOver.map a).left).obj d.F) (sliceToOver S toOver T)
        (K.toGrothendieck.over T)
        (isSheaf_structurePresheaf_sliceToOver S toOver T K.toGrothendieck hR)
        (hSh T _ inferInstance)).val ≅
      (sliceModuleOver S toOver T K.toGrothendieck hR M).val :=
  PresheafOfModules.isoOfPresheafIso (d.sectionsIso a) (fun T' r m => by
    obtain ⟨T'⟩ := T'
    refine Eq.trans (d.sectionsIso_hom_app_apply a T' (r • m)) ?_
    refine Eq.trans (congrArg (d.θ (T'.hom ≫ a))
      ((congrArg (pullbackSectionsMap d.F ((sliceOverMapIso a).inv.app T'))
        (Scheme.Modules.Hom.app_smul _ r m)).trans
        (pullbackSectionsMap_smul d.F ((sliceOverMapIso a).inv.app T') r _))) ?_
    exact (d.θIso (T'.hom ≫ a)).hom.hom.map_smul r _)


section Existence

variable [EssentiallySmall.{u} C]
  (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
    R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
      ∃ Q : Presieve T, Q ∈ K T ∧
        Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows)

include hSh hR hZariski in
/-- **Descent, Lemma 0GN7 on the slice at an object, for a cokernel of free modules.** -/
public theorem bijective_slice_cokernel (T : C) {L L' : Type u}
    (φ : SheafOfModules.free (R := ((toOver.obj T).left).ringCatSheaf) L' ⟶
      SheafOfModules.free (R := ((toOver.obj T).left).ringCatSheaf) L)
    {N : ((toOver.obj T).left).Modules} [N.IsQuasicoherent] :
    Function.Bijective fun χ : cokernel (C := ((toOver.obj T).left).Modules) φ ⟶ N =>
      associatedModuleMap ((toOver.obj T).left) (sliceToOver S toOver T) χ := by
  have : EssentiallySmall.{u} (Over T) := Stacks.essentiallySmall_over T
  have : (sliceToOver S toOver T).Faithful :=
    inferInstanceAs (Over.post (X := T) (toOver ⋙ Over.forget S)).Faithful
  have := sliceToOver_full S toOver T
  have := isIso_sliceToOver_obj_mkId_hom S toOver T
  have hJ := CategoryTheory.over_toGrothendieck_eq_toGrothendieck_comap_forget K T
  have hSh' : ∀ (P : ((toOver.obj T).left).Modules) (_ : P.IsQuasicoherent),
      Presheaf.IsSheaf (K.comap (Over.forget T)).toGrothendieck
        (associatedPresheaf ((toOver.obj T).left) P (sliceToOver S toOver T)) := by
    intro P hP
    rw [← hJ]
    exact hSh T P hP
  have hR' : Presheaf.IsSheaf (K.comap (Over.forget T)).toGrothendieck
      (structurePresheaf ((toOver.obj T).left) (sliceToOver S toOver T)) := by
    rw [← hJ]
    exact isSheaf_structurePresheaf_sliceToOver S toOver T K.toGrothendieck hR
  exact bijective_associatedModuleMap_cokernel ((toOver.obj T).left) (sliceToOver S toOver T)
    (K.comap (Over.forget T)) hR' (Over.mk (𝟙 T)) φ (hSh' _ inferInstance) (hSh' _ inferInstance)
    (hSh' _ inferInstance) (hSh' _ inferInstance)
    (zariskiRefinement_sliceToOver S toOver K hZariski T)

include hZariski in
/-- **Descent, Lemma 0GN7 on the slice at an object, for the pullback of a local module.** -/
public theorem bijective_slice_pullback {X T : C} (d : SliceCokernelDatum S toOver K hSh hR M X)
    (α : (toOver.obj T).left ⟶ (toOver.obj X).left) {N : ((toOver.obj T).left).Modules}
    [N.IsQuasicoherent] :
    Function.Bijective fun χ : (Scheme.Modules.pullback α).obj d.F ⟶ N =>
      associatedModuleMap ((toOver.obj T).left) (sliceToOver S toOver T) χ :=
  bijective_associatedModuleMap_of_iso _ (pullbackCokernelFreeIso α d.φ)
    (bijective_slice_cokernel (S := S) (toOver := toOver) (K := K) (hSh := hSh) (hR := hR)
      hZariski T _)

include hZariski in
/-- **Good morphisms exist**, over arrows of the site: Descent, Lemma 0GN7 on the slice at `T`
produces a morphism whose associated module is the composite of the two local identifications of
sections, and that is goodness read at each object over `T`. -/
public theorem exists_good {X Y T : C} (d : SliceCokernelDatum S toOver K hSh hR M X)
    (d' : SliceCokernelDatum S toOver K hSh hR M Y) (a : T ⟶ X) (b : T ⟶ Y) :
    ∃ χ, Good d d' (toOver.map a).left (toOver.map b).left χ := by
  obtain ⟨χ, hχ⟩ := (bijective_slice_pullback hZariski d
    (toOver.map a).left (N := (Scheme.Modules.pullback (toOver.map b).left).obj d'.F)).2
    ((d.sectionsModuleIso a).hom ≫ (d'.sectionsModuleIso b).inv)
  refine ⟨χ, ?_⟩
  intro W g hg a' b' ha hb y
  obtain ⟨w, rfl⟩ := exists_map_left_eq (toOver := toOver) g hg
  obtain rfl : a' = w ≫ a := eq_of_map_left_eq (toOver := toOver)
    (ha.symm.trans (map_left_comp_eq w a))
  obtain rfl : b' = w ≫ b := eq_of_map_left_eq (toOver := toOver)
    (hb.symm.trans (map_left_comp_eq w b))
  have h1 := congrArg (fun ψ => PresheafOfModules.Hom.app ψ (op (Over.mk w))) hχ
  have hχw : ∀ m, ((Scheme.Modules.pullback (toOver.map w).left).map χ).app ⊤ m =
      (d'.sectionsIso b).inv.app (op (Over.mk w)) ((d.sectionsIso a).hom.app (op (Over.mk w)) m) :=
    fun m => (congr($h1 m)).trans rfl
  have hA : ∀ x, (d.sectionsIso a).hom.app (op (Over.mk w))
      (((Scheme.Modules.pullbackComp (toOver.map w).left (toOver.map a).left).inv.app d.F).app ⊤
        (((Scheme.Modules.pullbackCongr ha).inv.app d.F).app ⊤ x)) = d.θ (w ≫ a) x := by
    intro x
    exact (d.sectionsIso_hom_app_apply a (Over.mk w) _).trans (congrArg (d.θ (w ≫ a))
      (pullbackSectionsMap_comp_inv d.F (toOver.map w).left (toOver.map a).left ha x))
  have hB : ∀ n : Γ((Scheme.Modules.pullback (toOver.map w).left).obj
      ((Scheme.Modules.pullback (toOver.map b).left).obj d'.F), ⊤),
      (d'.sectionsIso b).hom.app (op (Over.mk w)) n = d'.θ (w ≫ b)
        (((Scheme.Modules.pullbackCongr hb).hom.app d'.F).app ⊤
          (((Scheme.Modules.pullbackComp (toOver.map w).left (toOver.map b).left).hom.app
            d'.F).app ⊤ n)) := fun n =>
    (d'.sectionsIso_hom_app_apply b (Over.mk w) n).trans (congrArg (d'.θ (w ≫ b))
      (pullbackSectionsMap_homMk_id d'.F ((Category.id_comp _).trans hb) hb _))
  simp only [Scheme.Modules.transport, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [hχw, hA]
  exact (hB _).symm.trans (((d'.sectionsIso b).app (op (Over.mk w))).inv_hom_id_apply _)

include hZariski in
/-- **Good morphisms exist**, over morphisms of schemes over `S`. -/
public theorem exists_good' {X Y T : C} (d : SliceCokernelDatum S toOver K hSh hR M X)
    (d' : SliceCokernelDatum S toOver K hSh hR M Y)
    (α : (toOver.obj T).left ⟶ (toOver.obj X).left) (β : (toOver.obj T).left ⟶ (toOver.obj Y).left)
    (hα : α ≫ (toOver.obj X).hom = (toOver.obj T).hom)
    (hβ : β ≫ (toOver.obj Y).hom = (toOver.obj T).hom) :
    ∃ χ, Good d d' α β χ := by
  obtain ⟨a, rfl⟩ := exists_map_left_eq (toOver := toOver) α hα
  obtain ⟨b, rfl⟩ := exists_map_left_eq (toOver := toOver) β hβ
  exact exists_good hZariski d d' a b

include hZariski in
/-- **Good morphisms are unique.**  Their pullbacks to every object over `T` agree on sections, so
their associated modules on the slice at `T` agree, and Descent, Lemma 0GN7 on that slice is
faithful for the pullback of a cokernel of free modules. -/
public theorem Good.ext {X Y T : C} {d : SliceCokernelDatum S toOver K hSh hR M X}
    {d' : SliceCokernelDatum S toOver K hSh hR M Y}
    {α : (toOver.obj T).left ⟶ (toOver.obj X).left} {β : (toOver.obj T).left ⟶ (toOver.obj Y).left}
    (hα : α ≫ (toOver.obj X).hom = (toOver.obj T).hom)
    (hβ : β ≫ (toOver.obj Y).hom = (toOver.obj T).hom)
    {χ χ' : (Scheme.Modules.pullback α).obj d.F ⟶ (Scheme.Modules.pullback β).obj d'.F}
    (h : Good d d' α β χ) (h' : Good d d' α β χ') : χ = χ' := by
  obtain ⟨a, rfl⟩ := exists_map_left_eq (toOver := toOver) α hα
  obtain ⟨b, rfl⟩ := exists_map_left_eq (toOver := toOver) β hβ
  refine (bijective_slice_pullback hZariski d (toOver.map a).left
    (N := (Scheme.Modules.pullback (toOver.map b).left).obj d'.F)).1 ?_
  refine PresheafOfModules.hom_ext (fun Z => ?_)
  obtain ⟨Z⟩ := Z
  refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  change ((Scheme.Modules.pullback (toOver.map Z.hom).left).map χ).app ⊤ m =
    ((Scheme.Modules.pullback (toOver.map Z.hom).left).map χ').app ⊤ m
  have ha := map_left_comp_eq (toOver := toOver) Z.hom a
  have hb := map_left_comp_eq (toOver := toOver) Z.hom b
  have key' : (Scheme.Modules.transport _ ha hb χ).app ⊤ =
      (Scheme.Modules.transport _ ha hb χ').app ⊤ := by
    ext y
    exact d'.θ_injective (Z.hom ≫ b) ((h Z.left _ (Over.w (toOver.map Z.hom)) _ _ ha hb y).trans
      (h' Z.left _ (Over.w (toOver.map Z.hom)) _ _ ha hb y).symm)
  rw [Scheme.Modules.pullback_map_eq_transport _ ha hb χ,
    Scheme.Modules.pullback_map_eq_transport _ ha hb χ']
  simp only [Scheme.Modules.Hom.comp_app]
  rw [key']

variable {ι : Type*} (V : ι → C) (dd : ∀ i, SliceCokernelDatum S toOver K hSh hR M (V i))

include hZariski in
/-- **The transitions of the descent datum of Tag 03OJ**, over every object of the site: the
unique good morphisms. -/
public noncomputable def testTransitions :
    Stacks.Descent.TestTransitions modulePullbackPseudofunctor (fun T : C => (toOver.obj T).left)
      (fun T => (toOver.obj T).hom) V (fun i => (dd i).F) where
  τ T i j α β hα hβ := (exists_good' hZariski (dd i) (dd j) α β hα hβ).choose
  pullHom_τ T T' c hc i j α β hα hβ α' β' h₁ h₂ :=
    Good.ext hZariski
      ((congrArg (· ≫ (toOver.obj (V i)).hom) h₁).symm.trans (by rw [Category.assoc, hα, hc]))
      ((congrArg (· ≫ (toOver.obj (V j)).hom) h₂).symm.trans (by rw [Category.assoc, hβ, hc]))
      (((exists_good' hZariski (dd i) (dd j) α β hα hβ).choose_spec).pullHom c hc α' β' h₁ h₂)
      (exists_good' hZariski (dd i) (dd j) α' β'
        ((congrArg (· ≫ (toOver.obj (V i)).hom) h₁).symm.trans (by rw [Category.assoc, hα, hc]))
        ((congrArg (· ≫ (toOver.obj (V j)).hom) h₂).symm.trans
          (by rw [Category.assoc, hβ, hc]))).choose_spec
  τ_self T i α hα :=
    Good.ext hZariski hα hα (exists_good' hZariski (dd i) (dd i) α α hα hα).choose_spec
      (good_id (dd i) α)
  τ_comp T i j k α β γ hα hβ hγ :=
    Good.ext hZariski hα hγ
      (((exists_good' hZariski (dd i) (dd j) α β hα hβ).choose_spec).comp hβ
        (exists_good' hZariski (dd j) (dd k) β γ hβ hγ).choose_spec)
      (exists_good' hZariski (dd i) (dd k) α γ hα hγ).choose_spec

include hZariski in
/-- The transitions of `Stacks.Sites.SliceCokernelDatum.testTransitions` are good. -/
public theorem good_testTransitions (T : C) {i j : ι}
    (α : (toOver.obj T).left ⟶ (toOver.obj (V i)).left)
    (β : (toOver.obj T).left ⟶ (toOver.obj (V j)).left)
    (hα : α ≫ (toOver.obj (V i)).hom = (toOver.obj T).hom)
    (hβ : β ≫ (toOver.obj (V j)).hom = (toOver.obj T).hom) :
    Good (dd i) (dd j) α β ((testTransitions hZariski V dd).τ T α β hα hβ) := by
  delta testTransitions
  exact (exists_good' hZariski (dd i) (dd j) α β hα hβ).choose_spec

omit [toOver.Full] [toOver.Faithful] [EssentiallySmall.{u} C] [K.HasPullbacks]
  [K.IsStableUnderBaseChange] in
/-- **A good morphism, read at its own base**: it carries the local identification of sections
through `X` to the one through `Y`. -/
public theorem Good.apply_self {X Y T : C} {d : SliceCokernelDatum S toOver K hSh hR M X}
    {d' : SliceCokernelDatum S toOver K hSh hR M Y} {a : T ⟶ X} {b : T ⟶ Y}
    {χ : (Scheme.Modules.pullback (toOver.map a).left).obj d.F ⟶
      (Scheme.Modules.pullback (toOver.map b).left).obj d'.F}
    (h : Good d d' (toOver.map a).left (toOver.map b).left χ)
    (y : Γ((Scheme.Modules.pullback (toOver.map a).left).obj d.F, ⊤)) :
    d'.θ b (χ.app ⊤ y) = d.θ a y := by
  have := h T (𝟙 _) (Category.id_comp _) a b (Category.id_comp _) (Category.id_comp _) y
  rwa [Scheme.Modules.transport_id_left] at this

end Existence

end SliceCokernelDatum

end Stacks.Sites

end
