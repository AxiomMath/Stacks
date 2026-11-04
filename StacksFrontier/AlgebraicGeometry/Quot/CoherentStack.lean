module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHom
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModule
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite

/-!
# The category of coherent sheaves with proper support (Stacks 08KB)

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site.
Stacks 08KB introduces the category `Coh_{X/Y}` whose objects are the triples `(T, g, F)` with
`T` a scheme of the site over `S`, `g : T ⟶ Y` a morphism to the base and `F` a quasi-coherent
`𝒪_{X_T}`-module of finite presentation, flat over `T` and with support proper over `T`, where
`X_T = X ×_Y T`.  A morphism `(T, g, F) ⟶ (T', g', F')` is a pair `(h, φ)` of a morphism
`h : T ⟶ T'` over `Y` and an isomorphism `φ : (X_h)^*F' ⟶ F` of `𝒪_{X_T}`-modules, `X_h` being
the induced morphism of base changes.  Composition composes the base maps and the inverse
images of the module isomorphisms, and the projection `(T, g, F) ↦ (T, g)` is a functor to the
schemes over `Y`.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation`: **Stacks 08KB**, the standing data — the
  finitely presented morphism of algebraic spaces.
* `AlgebraicGeometry.Space.CoherentObject`: **Stacks 08KB**, the objects of `Coh_{X/Y}`.
* `AlgebraicGeometry.Space.CoherentHom`: **Stacks 08KB**, the morphisms of `Coh_{X/Y}`.
* `AlgebraicGeometry.Space.CoherentHom.id` and `AlgebraicGeometry.Space.CoherentHom.comp`: the
  identities and the composition of `Coh_{X/Y}`.
* `AlgebraicGeometry.Space.CoherentSituation.idComparison` and
  `AlgebraicGeometry.Space.CoherentSituation.compComparison`: the comparisons of Stacks 03LU
  for the morphisms of base changes induced by an identity and by a composite, and
  `AlgebraicGeometry.Space.CoherentSituation.relativeMapComparison` the identification induced
  by an equality of base maps.
* `CategoryTheory.Functor.fibreComp`: the composite of two fibre morphisms along a comparison
  of a functor with a composite, which is what the composition of `Coh_{X/Y}` is.
* `AlgebraicGeometry.Space.CoherentCategoryData`: the category structure on the objects
  together with its projection to the schemes over `Y`, and the identification of its
  hom-sets, identities, composition and projection with the ones above.  This is the
  *specification* of that category structure; no value of it is constructed here, because
  08KB names `Coh_{X/Y}` a category by designation and does not verify it.

## Main results

* `AlgebraicGeometry.Space.CoherentHom.ext`: a morphism is determined by its base map and its
  module isomorphism.
* `CategoryTheory.Functor.fibreComp_id_left`, `CategoryTheory.Functor.fibreComp_id_right` and
  `CategoryTheory.Functor.fibreComp_assoc`: the two unit laws and the associativity law for
  composition of fibre morphisms, each taking the relevant coherence of the comparisons as a
  hypothesis in the shape a consumer already has it.
* `AlgebraicGeometry.Space.idComparison_comp_fac`,
  `AlgebraicGeometry.Space.comp_idComparison_fac` and
  `AlgebraicGeometry.Space.compComparison_assoc`: those three coherences, for the comparisons
  of the morphisms of base changes.  Together with the three laws above they are exactly the
  input the category laws of `Coh_{X/Y}` need.

## Implementation notes

**The category laws are conditional, the objects, morphisms, identities and composition are
not.**  Composition is associative and unital exactly because the inverse images of 03LU are
pseudofunctorial, and that pseudofunctoriality is not available in this development; it is
carried as the single hypothesis `AlgebraicGeometry.Space.ModulePushforwardCoherence`, the
coherence data for the *direct* images, from which the inverse-image coherences follow.  This
is the same condition, in the same shape, as the one carried by the relative Hom functor of
Stacks 08JT in `StacksFrontier/AlgebraicGeometry/Quot/RelativeHom.lean`.  The three pieces of data
08KB fixes — the standing data, the objects and the morphisms — are unconditional, and they are
what the tag attributes sit on.

The triple `(T, g)` is an object of `AlgebraicGeometry.Space.SchemesOver`, a costructured arrow
of the inclusion of schemes as algebraic spaces, so a morphism of such triples is a morphism of
schemes over `S` together with the commutation with the two morphisms to `Y` — exactly the
datum `h` of the source.  The base change `X_T`, its projection to `T` and the induced morphism
`X_h` of base changes are `AlgebraicGeometry.Space.baseChangeSpace`,
`AlgebraicGeometry.Space.baseChangeInclusion` and `AlgebraicGeometry.Space.baseChangeMap` of
the same file; `X_h` is the morphism *induced by the universal property*, so
`AlgebraicGeometry.Space.baseChangeMap_comp` is an honest equality of morphisms and no
cartesian-square conditions have to be carried in the morphism structure.

The module isomorphism is recorded as a morphism together with
`CategoryTheory.IsIso` rather than as a `CategoryTheory.Iso`, which is what makes
`AlgebraicGeometry.Space.CoherentHom.ext` a two-field extensionality lemma in the shape of
`CategoryTheory.Grothendieck.ext`: the type of the morphism depends on the base map, so the
comparison of two morphisms transports along an equality of base maps, and transporting a
single morphism is `CategoryTheory.eqToHom` while transporting an isomorphism is not.

The three category laws are reduced to the abstract composition calculus of
`CategoryTheory.Functor.fibreComp` below, which takes the relevant coherence of Stacks 03LU
as a hypothesis in the shape the consumer already has it.  This is not a matter of taste: the
comparisons of inverse images contain `CategoryTheory.eqToIso` factors, and the implementation
notes of `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCoherence.lean`
record that the kernel does not finish checking a proof of a statement that projects the
underlying morphism of such a comparison.  Factoring through a general statement about an
abstract comparison leaves only a syntactic match at the point of use, as it does for the
relative Hom functor.

Closedness of the support is carried as an existential in the object, as is the
locally-finite-type hypothesis on the projection `X_T ⟶ T`, because
`AlgebraicGeometry.Space.IsProperOver` of Stacks 0CZD takes both as arguments: there is no
result in this development showing the support of a module of finite presentation to be closed.

The module universe is the universe of the structure rings, as it is for
`AlgebraicGeometry.Space.modulePullback`.

## References

* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

/-! ### Composing fibre morphisms along a comparison of inverse images

This section is general category theory and belongs in a file of its own next to
`StacksFrontier/CategoryTheory/Functor/ConjugateHom.lean`, whose `CategoryTheory.Functor.conjHom`
plays the same role for a morphism between two values of one functor that
`CategoryTheory.Functor.fibreComp` plays for a morphism out of a value of one functor.  It is
here because nothing else consumes it yet. -/

namespace CategoryTheory.Functor

/-- The composite of two fibre morphisms along a comparison of a functor with a composite.

Let `La : C₁ ⥤ C₀`, `Lb : C₂ ⥤ C₁` and `Lab : C₂ ⥤ C₀` carry a comparison `τ : Lab ≅ Lb ⋙ La`.
A morphism `b : Lb.obj M'' ⟶ M'` and a morphism `a : La.obj M' ⟶ M` then compose to a morphism
`Lab.obj M'' ⟶ M`: apply `La` to `b`, read its source through `τ`, and follow by `a`.

This is the shape of composition in a category whose objects are pairs of a test object and a
module on the corresponding base change, and whose morphisms carry a comparison of the inverse
image of the target module with the source module. -/
def fibreComp {C₀ : Type*} {C₁ : Type*} {C₂ : Type*} [Category* C₀] [Category* C₁]
    [Category* C₂] {La : C₁ ⥤ C₀} {Lb : C₂ ⥤ C₁} {Lab : C₂ ⥤ C₀} (τ : Lab ≅ Lb ⋙ La)
    {M : C₀} {M' : C₁} {M'' : C₂} (a : La.obj M' ⟶ M) (b : Lb.obj M'' ⟶ M') :
    Lab.obj M'' ⟶ M :=
  τ.hom.app M'' ≫ La.map b ≫ a

/-- Two whiskerings by the same functor, adjacent in a left-associated chain of comparisons,
merge into one.  This is `CategoryTheory.Functor.isoWhiskerLeft_trans` in the shape a `simp`
call can apply repeatedly to such a chain. -/
theorem trans_isoWhiskerLeft_trans {C : Type*} {D : Type*} {E : Type*} [Category* C]
    [Category* D] [Category* E] (F : C ⥤ D) {G H K : D ⥤ E} {X : C ⥤ E} (ξ : X ≅ F ⋙ G)
    (α : G ≅ H) (β : H ≅ K) :
    (ξ ≪≫ isoWhiskerLeft F α) ≪≫ isoWhiskerLeft F β =
      ξ ≪≫ isoWhiskerLeft F (α ≪≫ β) := by
  rw [isoWhiskerLeft_trans, Iso.trans_assoc]

/-- **The unit law at the source for composition of fibre morphisms.**  If the comparison `τ`
followed by whiskering an identification `γ : La ≅ 𝟭` into it is an identification `w` of
`Lab` with `Lb`, then composing with the component of `γ` transports along `w`. -/
theorem fibreComp_id_left {C₀ : Type*} {C₂ : Type*} [Category* C₀] [Category* C₂]
    {La : C₀ ⥤ C₀} {Lb : C₂ ⥤ C₀} {Lab : C₂ ⥤ C₀} (γ : La ≅ 𝟭 C₀) (τ : Lab ≅ Lb ⋙ La)
    (w : Lab ≅ Lb) (hfac : τ ≪≫ isoWhiskerLeft Lb γ ≪≫ rightUnitor Lb = w)
    {M : C₀} {M'' : C₂} (b : Lb.obj M'' ⟶ M) :
    fibreComp τ (γ.hom.app M) b = w.hom.app M'' ≫ b := by
  subst hfac
  have hn := γ.hom.naturality b
  dsimp at hn
  simp only [fibreComp, Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
    rightUnitor_hom_app, Category.assoc]
  rw [hn]
  simp

/-- **The unit law at the target for composition of fibre morphisms.**  If the comparison `τ`
followed by whiskering an identification `γ : Lb ≅ 𝟭` into it is an identification `w` of
`Lab` with `La`, then composing the component of `γ` transports along `w`. -/
theorem fibreComp_id_right {C₀ : Type*} {C₁ : Type*} [Category* C₀] [Category* C₁]
    {La : C₁ ⥤ C₀} {Lb : C₁ ⥤ C₁} {Lab : C₁ ⥤ C₀} (γ : Lb ≅ 𝟭 C₁) (τ : Lab ≅ Lb ⋙ La)
    (w : Lab ≅ La) (hfac : τ ≪≫ isoWhiskerRight γ La ≪≫ leftUnitor La = w)
    {M : C₀} {M' : C₁} (a : La.obj M' ⟶ M) :
    fibreComp τ a (γ.hom.app M') = w.hom.app M' ≫ a := by
  subst hfac
  simp [fibreComp]

/-- **The associativity law for composition of fibre morphisms.**  If the two bracketings of
the comparisons for a triple composite agree up to an identification `w` of the two comparisons
along the triple composite, then the two bracketings of the composite of three fibre morphisms
agree up to transport along `w`. -/
theorem fibreComp_assoc {C₀ : Type*} {C₁ : Type*} {C₂ : Type*} {C₃ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]
    {Lp : C₁ ⥤ C₀} {Lq : C₂ ⥤ C₁} {Lr : C₃ ⥤ C₂} {Lpq : C₂ ⥤ C₀} {Lqr : C₃ ⥤ C₁}
    {L₁ : C₃ ⥤ C₀} {L₂ : C₃ ⥤ C₀} (τ₁ : Lpq ≅ Lq ⋙ Lp) (τ₂ : L₁ ≅ Lr ⋙ Lpq)
    (τ₃ : Lqr ≅ Lr ⋙ Lq) (τ₄ : L₂ ≅ Lqr ⋙ Lp) (w : L₁ ≅ L₂)
    (hfac : τ₂ ≪≫ isoWhiskerLeft Lr τ₁ =
      w ≪≫ τ₄ ≪≫ isoWhiskerRight τ₃ Lp ≪≫ associator Lr Lq Lp)
    {M : C₀} {M' : C₁} {M'' : C₂} {M''' : C₃} (a : Lp.obj M' ⟶ M) (b : Lq.obj M'' ⟶ M')
    (c : Lr.obj M''' ⟶ M'') :
    fibreComp τ₂ (fibreComp τ₁ a b) c =
      w.hom.app M''' ≫ fibreComp τ₄ a (fibreComp τ₃ b c) := by
  have h := NatTrans.congr_app (congrArg Iso.hom hfac) M'''
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
    isoWhiskerRight_hom, whiskerRight_app, associator_hom_app, Category.comp_id] at h
  have hn := τ₁.hom.naturality c
  dsimp at hn
  simp only [fibreComp, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, reassoc_of% h]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

/-! ### The standing data -/

/-- **Stacks 08KB, the standing data.**  A morphism `f : X ⟶ Y` of algebraic spaces over `S` of
finite presentation: the relative algebraic space whose coherent sheaves with proper support
the category `Coh_{X/Y}` classifies. -/
@[stacks 08KB "the relative algebraic space"]
structure CoherentSituation (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) where
  /-- The source of the morphism. -/
  X : AlgebraicSpaces B S hS
  /-- The target of the morphism, the base over which the category is formed. -/
  Y : AlgebraicSpaces B S hS
  /-- The morphism itself. -/
  f : X ⟶ Y
  /-- It is of finite presentation (Stacks 03XP). -/
  finitePresentation : IsFinitePresentation B S hS f.hom

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Replacing the second factor of the composite by an equal morphism changes the comparison of
`AlgebraicGeometry.Space.modulePullbackTriangle` only by the induced identification of the two
inverse images.  This is the companion of
`AlgebraicGeometry.Space.modulePullbackTriangle_congr_left` for the other factor, and belongs
beside it in `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCoherence.lean`. -/
theorem modulePullbackTriangle_congr_right {X Y Z : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {g g' : Y ⟶ Z} (hgg : g = g') {k : X ⟶ Z} (hk : f ≫ g = k) (hk' : f ≫ g' = k) :
    modulePullbackTriangle B S hS hk =
      modulePullbackTriangle B S hS hk' ≪≫
        Functor.isoWhiskerRight
          (eqToIso (congrArg (modulePullback B S hS) hgg.symm))
          (modulePullback B S hS f) := by
  subst hgg
  have hE : modulePullbackTriangle B S hS hk = modulePullbackTriangle B S hS hk' := rfl
  rw [hE]
  simp

namespace CoherentSituation

variable (D : CoherentSituation B S hS)

/-- The base change `X_T = X ×_Y T` of the situation to a scheme `T` over `Y`. -/
abbrev space (T : SchemesOver D.Y) : AlgebraicSpaces B S hS := baseChangeSpace D.f T

/-- The projection `X_T ⟶ T` of the base change to its test scheme. -/
abbrev projection (T : SchemesOver D.Y) :
    D.space T ⟶ (schemeSpaceFunctor B S hS).obj T.left :=
  baseChangeInclusion D.f T

/-- The morphism `X_h : X_T ⟶ X_{T'}` of base changes induced by a morphism `h : T ⟶ T'` of
schemes over `Y`. -/
abbrev relativeMap {T T' : SchemesOver D.Y} (h : T ⟶ T') : D.space T ⟶ D.space T' :=
  baseChangeMap D.f h

/-- The support of an `𝒪_{X_T}`-module, as a subset of the points of `X_T` (Stacks 04KA). -/
abbrev support (T : SchemesOver D.Y)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) :
    Set (points B S hS (D.space T).1) :=
  supportOfSheaf B S hS (D.space T).1 ((SheafOfModules.toSheaf _).obj F)

/-- The identification of the inverse images along the morphisms of base changes induced by two
equal morphisms of test schemes. -/
def relativeMapComparison {T T' : SchemesOver D.Y} {h h' : T ⟶ T'} (e : h = h') :
    modulePullback B S hS (D.relativeMap h) ≅ modulePullback B S hS (D.relativeMap h') :=
  eqToIso (congrArg (fun k : T ⟶ T' => modulePullback B S hS (D.relativeMap k)) e)

/-- The identification `(X_{𝟙 T})^* ≅ 𝟭` of the inverse image along the morphism of base
changes induced by an identity with the identity functor.

It is the unit law of Stacks 03LU, read through the identification of the induced morphism of
base changes with the identity. -/
def idComparison (hc : ModulePushforwardCoherence B S hS) (T : SchemesOver D.Y) :
    modulePullback B S hS (D.relativeMap (𝟙 T)) ≅
      𝟭 (Modules.{u, u} B S hS (D.space T).1 (D.space T).2) :=
  eqToIso (congrArg (modulePullback B S hS) (baseChangeMap_id D.f T)) ≪≫
    hc.modulePullbackIdIso (D.space T)

/-- The comparison `(X_{h ≫ h'})^* ≅ (X_{h'})^* ⋙ (X_h)^*` of the inverse image along the
morphism of base changes induced by a composite with the iterated inverse image.

It is the comparison of Stacks 03LU at the equality `X_h ≫ X_{h'} = X_{h ≫ h'}` of
`AlgebraicGeometry.Space.baseChangeMap_comp`, which is why it is unconditional. -/
def compComparison {T T' T'' : SchemesOver D.Y} (h : T ⟶ T') (h' : T' ⟶ T'') :
    modulePullback B S hS (D.relativeMap (h ≫ h')) ≅
      modulePullback B S hS (D.relativeMap h') ⋙ modulePullback B S hS (D.relativeMap h) :=
  modulePullbackTriangle B S hS (baseChangeMap_comp D.f h h').symm

end CoherentSituation

/-! ### The coherences of the comparisons of inverse images along morphisms of base changes -/

/-- The morphisms of base changes induced by two composable morphisms compose to the one induced
by their composite. -/
private theorem relativeMap_comp_eq (D : CoherentSituation B S hS) {T T' T'' : SchemesOver D.Y}
    (h : T ⟶ T') (h' : T' ⟶ T'') :
    D.relativeMap h ≫ D.relativeMap h' = D.relativeMap (h ≫ h') :=
  (baseChangeMap_comp D.f h h').symm

/-- Equal morphisms of test schemes induce equal morphisms of base changes. -/
private theorem relativeMap_congr (D : CoherentSituation B S hS) {T T' : SchemesOver D.Y}
    {h h' : T ⟶ T'} (e : h = h') : D.relativeMap h = D.relativeMap h' :=
  congrArg _ e

/-- The comparison for a composite whose first factor is an identity is the identity law. -/
theorem idComparison_comp_fac (hc : ModulePushforwardCoherence B S hS)
    (D : CoherentSituation B S hS) {T T' : SchemesOver D.Y} (h : T ⟶ T') :
    D.compComparison (𝟙 T) h ≪≫
        Functor.isoWhiskerLeft (modulePullback B S hS (D.relativeMap h))
          (D.idComparison hc T) ≪≫
        Functor.rightUnitor (modulePullback B S hS (D.relativeMap h)) =
      D.relativeMapComparison (Category.id_comp h) := by
  have hff : D.relativeMap (𝟙 T) = 𝟙 (D.space T) := baseChangeMap_id D.f T
  have hk : D.relativeMap (𝟙 T) ≫ D.relativeMap h = D.relativeMap (𝟙 T ≫ h) :=
    relativeMap_comp_eq D (𝟙 T) h
  have hk1 : 𝟙 (D.space T) ≫ D.relativeMap h = D.relativeMap (𝟙 T ≫ h) := by
    rw [← hff]; exact hk
  have hkk : D.relativeMap (𝟙 T ≫ h) = D.relativeMap h :=
    relativeMap_congr D (Category.id_comp h)
  have hk2 : 𝟙 (D.space T) ≫ D.relativeMap h = D.relativeMap h := Category.id_comp _
  have e1 : D.compComparison (𝟙 T) h = modulePullbackTriangle B S hS hk := rfl
  rw [e1, modulePullbackTriangle_congr_left hff hk hk1,
    modulePullbackTriangle_congr hk1 hk2 hkk, modulePullbackTriangle_eq hk2,
    hc.modulePullbackCompIso_id_left (D.relativeMap h)]
  simp only [CoherentSituation.idComparison]
  rw [Functor.isoWhiskerLeft_trans]
  simp only [← Iso.trans_assoc, Functor.trans_isoWhiskerLeft_trans, eqToIso_trans, eqToIso_refl,
    Iso.refl_trans, Iso.trans_refl, Functor.isoWhiskerLeft_refl,
    CoherentSituation.relativeMapComparison]
  simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

/-- The comparison for a composite whose second factor is an identity is the identity law. -/
theorem comp_idComparison_fac (hc : ModulePushforwardCoherence B S hS)
    (D : CoherentSituation B S hS) {T T' : SchemesOver D.Y} (h : T ⟶ T') :
    D.compComparison h (𝟙 T') ≪≫
        Functor.isoWhiskerRight (D.idComparison hc T')
          (modulePullback B S hS (D.relativeMap h)) ≪≫
        Functor.leftUnitor (modulePullback B S hS (D.relativeMap h)) =
      D.relativeMapComparison (Category.comp_id h) := by
  have hff : D.relativeMap (𝟙 T') = 𝟙 (D.space T') := baseChangeMap_id D.f T'
  have hk : D.relativeMap h ≫ D.relativeMap (𝟙 T') = D.relativeMap (h ≫ 𝟙 T') :=
    relativeMap_comp_eq D h (𝟙 T')
  have hk1 : D.relativeMap h ≫ 𝟙 (D.space T') = D.relativeMap (h ≫ 𝟙 T') := by
    rw [← hff]; exact hk
  have hkk : D.relativeMap (h ≫ 𝟙 T') = D.relativeMap h :=
    relativeMap_congr D (Category.comp_id h)
  have hk2 : D.relativeMap h ≫ 𝟙 (D.space T') = D.relativeMap h := Category.comp_id _
  have e1 : D.compComparison h (𝟙 T') = modulePullbackTriangle B S hS hk := rfl
  rw [e1, modulePullbackTriangle_congr_right hff hk hk1,
    modulePullbackTriangle_congr hk1 hk2 hkk, modulePullbackTriangle_eq hk2,
    hc.modulePullbackCompIso_id_right (D.relativeMap h)]
  apply Iso.ext
  ext M
  simp [CoherentSituation.idComparison, CoherentSituation.relativeMapComparison]

/-- The associativity coherence of the comparisons for composites of morphisms of test
schemes. -/
theorem compComparison_assoc (hc : ModulePushforwardCoherence B S hS)
    (D : CoherentSituation B S hS) {T T' T'' T''' : SchemesOver D.Y} (h : T ⟶ T')
    (h' : T' ⟶ T'') (h'' : T'' ⟶ T''') :
    D.compComparison (h ≫ h') h'' ≪≫
        Functor.isoWhiskerLeft (modulePullback B S hS (D.relativeMap h''))
          (D.compComparison h h') =
      D.relativeMapComparison (Category.assoc h h' h'') ≪≫
        D.compComparison h (h' ≫ h'') ≪≫
        Functor.isoWhiskerRight (D.compComparison h' h'')
          (modulePullback B S hS (D.relativeMap h)) ≪≫
        Functor.associator (modulePullback B S hS (D.relativeMap h''))
          (modulePullback B S hS (D.relativeMap h'))
          (modulePullback B S hS (D.relativeMap h)) := by
  have hk : D.relativeMap h ≫ D.relativeMap h' = D.relativeMap (h ≫ h') :=
    relativeMap_comp_eq D h h'
  have hq : D.relativeMap h' ≫ D.relativeMap h'' = D.relativeMap (h' ≫ h'') :=
    relativeMap_comp_eq D h' h''
  have hkr : D.relativeMap (h ≫ h') ≫ D.relativeMap h'' = D.relativeMap ((h ≫ h') ≫ h'') :=
    relativeMap_comp_eq D (h ≫ h') h''
  have hr' : D.relativeMap h ≫ D.relativeMap (h' ≫ h'') = D.relativeMap (h ≫ h' ≫ h'') :=
    relativeMap_comp_eq D h (h' ≫ h'')
  have hrr : D.relativeMap ((h ≫ h') ≫ h'') = D.relativeMap (h ≫ h' ≫ h'') :=
    relativeMap_congr D (Category.assoc h h' h'')
  have hr : D.relativeMap h ≫ D.relativeMap (h' ≫ h'') = D.relativeMap ((h ≫ h') ≫ h'') :=
    hr'.trans hrr.symm
  have e1 : D.compComparison (h ≫ h') h'' = modulePullbackTriangle B S hS hkr := rfl
  have e2 : D.compComparison h h' = modulePullbackTriangle B S hS hk := rfl
  have e3 : D.compComparison h' h'' = modulePullbackTriangle B S hS hq := rfl
  have e4 : D.compComparison h (h' ≫ h'') = modulePullbackTriangle B S hS hr' := rfl
  rw [e1, e2, e3, e4, hc.modulePullbackTriangle_comp hk hq hr hkr,
    modulePullbackTriangle_congr hr hr' hrr, Iso.trans_assoc]
  rfl

/-! ### Objects and morphisms -/

/-- **Stacks 08KB, the objects.**  An object of `Coh_{X/Y}`: a scheme `T` of the site over `Y`
together with a quasi-coherent `𝒪_{X_T}`-module of finite presentation which is flat over `T`
and whose support is proper over `T`. -/
@[stacks 08KB "objects"]
structure CoherentObject (D : CoherentSituation B S hS) where
  /-- The test scheme over `Y`, that is, the pair `(T, g)` of the source. -/
  T : SchemesOver D.Y
  /-- The module on the base change `X_T`. -/
  F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2
  /-- It is quasi-coherent (Stacks 03G9). -/
  quasicoherent : F.IsQuasicoherentOnSite
  /-- It is of finite presentation (Stacks 03DL). -/
  finitePresentation : F.IsFinitePresentationOnSite
  /-- It is flat over the test scheme (Stacks 05VV). -/
  flat : IsFlatOver B S hS (D.space T).2 (D.projection T).hom F
  /-- Its support is a closed subset proper over the test scheme (Stacks 0CZD).  The
  locally-finite-type hypothesis on the projection and the closedness of the support are
  existentially quantified because properness over the test scheme is stated for a closed
  subset of the points of the source of a morphism locally of finite type. -/
  properSupport : ∃ (hp : IsLocallyOfFiniteType B S hS (D.projection T).hom)
      (hU : IsClosed (D.support T F)),
      IsProperOver B S hS (D.space T).2
        ((schemeSpaceFunctor B S hS).obj T.left).2 (D.projection T).hom hp (D.support T F) hU

/-- **Stacks 08KB, the morphisms.**  A morphism of `Coh_{X/Y}`: a morphism `h : T ⟶ T'` of
test schemes over `Y` together with an isomorphism `(X_h)^*F' ⟶ F` of `𝒪_{X_T}`-modules. -/
@[stacks 08KB "morphisms"]
structure CoherentHom {D : CoherentSituation B S hS} (A A' : CoherentObject D) where
  /-- The morphism of test schemes over `Y`. -/
  base : A.T ⟶ A'.T
  /-- The comparison of the inverse image of the module of the target with the module of the
  source. -/
  fibre : (modulePullback B S hS (D.relativeMap base)).obj A'.F ⟶ A.F
  /-- The comparison is an isomorphism. -/
  isIso_fibre : IsIso fibre

namespace CoherentHom

variable {D : CoherentSituation B S hS} {A A' : CoherentObject D}

attribute [instance] isIso_fibre

/-- Two morphisms of `Coh_{X/Y}` with the same base map and the same module comparison, read
through the identification of the two inverse images that the equality of base maps induces,
are equal. -/
@[ext (iff := false)]
theorem ext {m n : CoherentHom A A'} (hbase : m.base = n.base)
    (hfibre : eqToHom (by rw [hbase]) ≫ m.fibre = n.fibre) : m = n := by
  obtain ⟨mb, mf, mi⟩ := m
  obtain ⟨nb, nf, ni⟩ := n
  change mb = nb at hbase
  subst hbase
  simp only [eqToHom_refl, Category.id_comp] at hfibre
  subst hfibre
  rfl

/-- **Stacks 08KB, the identity.**  The identity of an object of `Coh_{X/Y}`: the identity of
its test scheme, with the identity law of Stacks 03LU as its module comparison. -/
def id (hc : ModulePushforwardCoherence B S hS) (A : CoherentObject D) : CoherentHom A A where
  base := 𝟙 A.T
  fibre := (D.idComparison hc A.T).hom.app A.F
  isIso_fibre := inferInstance

/-- **Stacks 08KB, the composition.**  The composite of two morphisms of `Coh_{X/Y}`: the
composite of the base maps, with the inverse image of the second module comparison followed by
the first, read through the comparison of Stacks 03LU for the composite. -/
def comp {A'' : CoherentObject D} (m : CoherentHom A A') (n : CoherentHom A' A'') :
    CoherentHom A A'' where
  base := m.base ≫ n.base
  fibre := Functor.fibreComp (D.compComparison m.base n.base) m.fibre n.fibre
  isIso_fibre := by
    change IsIso ((D.compComparison m.base n.base).hom.app A''.F ≫
      (modulePullback B S hS (D.relativeMap m.base)).map n.fibre ≫ m.fibre)
    infer_instance

end CoherentHom

/-! ### The category and its projection -/

/-- The category structure on the objects of `Coh_{X/Y}` together with its projection to the
schemes over `Y`, and the identification of its hom-sets, identities, composition and
projection with `AlgebraicGeometry.Space.CoherentHom`,
`AlgebraicGeometry.Space.CoherentHom.id` and `AlgebraicGeometry.Space.CoherentHom.comp`.

Bundling the category with those identifications is what makes it the category of the source
rather than some category on the same objects. -/
structure CoherentCategoryData (hc : ModulePushforwardCoherence B S hS)
    (D : CoherentSituation B S hS) where
  /-- The category structure on the objects. -/
  category : Category.{u + 1} (CoherentObject D)
  /-- The projection to the schemes over `Y`. -/
  projection : letI : Category.{u + 1} (CoherentObject D) := category
    CoherentObject D ⥤ SchemesOver D.Y
  /-- The hom-sets are the pairs of a base map and a module comparison. -/
  hom_type : letI : Category.{u + 1} (CoherentObject D) := category
    ∀ A A' : CoherentObject D, (A ⟶ A') = CoherentHom A A'
  /-- The identity is the one of `AlgebraicGeometry.Space.CoherentHom.id`. -/
  identity : letI : Category.{u + 1} (CoherentObject D) := category
    ∀ A : CoherentObject D, (Equiv.cast (hom_type A A)) (𝟙 A) = CoherentHom.id hc A
  /-- Composition is the one of `AlgebraicGeometry.Space.CoherentHom.comp`. -/
  composition : letI : Category.{u + 1} (CoherentObject D) := category
    ∀ {A A' A'' : CoherentObject D} (m : A ⟶ A') (n : A' ⟶ A''),
      (Equiv.cast (hom_type A A'')) (m ≫ n) =
        CoherentHom.comp ((Equiv.cast (hom_type A A')) m)
          ((Equiv.cast (hom_type A' A'')) n)
  /-- The projection forgets the module. -/
  projection_obj : ∀ A : CoherentObject D, projection.obj A = A.T
  /-- The projection acts on morphisms by taking the base map. -/
  projection_map : letI : Category.{u + 1} (CoherentObject D) := category
    ∀ {A A' : CoherentObject D} (m : A ⟶ A'),
      projection.map m = eqToHom (projection_obj A) ≫
        ((Equiv.cast (hom_type A A')) m).base ≫ eqToHom (projection_obj A').symm

end AlgebraicGeometry.Space

end
