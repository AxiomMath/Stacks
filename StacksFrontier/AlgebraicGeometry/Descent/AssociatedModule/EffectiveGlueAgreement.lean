module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ObjRestrictRestrFunBridgeEffectivity

/-!
# The agreement of the local isomorphisms of Stacks 03DX (1) over a fibre product

The file `ObjRestrictRestrFunBridgeEffectivity.lean` (in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/`) reduces the essential
surjectivity of Stacks 03DX (1) to **one** statement: that the local isomorphisms

    `𝓕^a|_{(Sch/X_i)_fppf} ≅ 𝒢|_{(Sch/X_i)_fppf}`

read off the effectivity of the descent datum agree over the fibre products `X i ×_S X j`.  Its
implementation notes name the two unconditional reductions the agreement decomposes into.  **This
file carries out both of them**, and proves the agreement in the `objRestrict` spelling:
`AlgebraicGeometry.BigFppfOver.restrictObjRestrictIso_effectiveGlueObjRestrictIso_eq`.

## The two reductions

Write `g₁ : Z ⟶ X i` and `g₂ : Z ⟶ X j` for the two projections of `Z = X i ×_S X j`, `𝓕` for
the glued module, `ι_i` for the component of the effectivity isomorphism and `lac` for
`AlgebraicGeometry.BigFppfOver.localAssociatedModuleComparison`.

* **The naturality computation.**  Restricting the local isomorphism at `X i` to `Z` gives

      `lac(g₁, (objHom (X i))^*𝓕, 03DV at 𝓕)⁻¹ ≫ (g₁^*ι_i)^a ≫ lac(g₁, 𝓕_i, e_i)`,

  which is naturality of `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` in the
  module and nothing else.  It is `Stacks.restrict_comparison_trans`, proved at abstract
  categories, instantiated by
  `AlgebraicGeometry.BigFppfOver.restrict_effectiveGlueObjRestrictIso`.
* **The descent condition.**  `CategoryTheory.Pseudofunctor.DescentData.Hom.comm` of the
  effectivity isomorphism identifies the two middle factors up to the transition of the canonical
  descent datum of `𝓕`; and the compatibility of Stacks 03DV with composition — the component at
  `𝓕` of `AlgebraicGeometry.BigFppfOver.NatIsoCompSquare`, unconditional by
  `…natIsoCompSquare_of_sectionsCocycle` fed `…sectionsCocycle` — identifies that transition with
  the difference of the two comparisons of the ambient module `𝓕^a`.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.restrictObjRestrictIso`: the restriction of a local isomorphism
  along a morphism of the big fppf site, contracted by
  `AlgebraicGeometry.BigFppfOver.objRestrictComp`.

## Main results

* `Stacks.restrict_comparison_trans`, `Stacks.map_eq_of_comp_eq`, `Stacks.hom_comp_inv_eq` and
  `Stacks.iso_trans_eq_of_squares_map`: the category theory, at abstract categories.
* `AlgebraicGeometry.canonicalDescentFunctor_obj_obj_hom` and
  `AlgebraicGeometry.map_canonicalDescentFunctor_obj_obj_hom`: the transitions of the canonical
  descent datum of a quasi-coherent module, in the `AlgebraicGeometry.pullModComp` spelling.
* `AlgebraicGeometry.descentDataHom_conjugate_agree`: **the agreement, at abstract schemes.**
* `AlgebraicGeometry.BigFppfOver`
  `.associatedModule_map_pullModComp_comp_localAssociatedModuleComparison`: the compatibility of
  Stacks 03DV with composition, read at a module on `S`.
* `AlgebraicGeometry.BigFppfOver.restrict_effectiveGlueObjRestrictIso`: the naturality
  computation.
* `AlgebraicGeometry.BigFppfOver.associatedModule_map_memberDatum_hom` and
  `…localAssociatedModuleComparison_glue_hom_comp_inv`: the two halves of the descent condition,
  at an arbitrary pair of morphisms into two members.
* `AlgebraicGeometry.BigFppfOver.restrictObjRestrictIso_effectiveGlueObjRestrictIso_eq`: **the
  agreement of the local isomorphisms of Stacks 03DX (1) along two morphisms `a₁ : Z ⟶ X i` and
  `a₂ : Z ⟶ X j` into two members**, in the `objRestrict` spelling, unconditionally.  At the two
  projections of `X i ×_S X j` this is the agreement
  `AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_agree` asks for, read in that
  spelling.  It is stated at an arbitrary pair because every pair factors through the fibre
  product (`AlgebraicGeometry.BigFppfOver.exists_hom_memberProd`) and because the transport
  across the bridge needs it at the pair `(A.hom ≫ a₁, A.hom ≫ a₂)` for every object `A` of the
  slice at `Z`.

## Implementation notes

Nothing here carries a `stacks` attribute.

Every statement that mentions both spellings of the pullback of sheaves of modules on a scheme —
`AlgebraicGeometry.Scheme.Modules.pullback` on one side, the pullback functor of
`AlgebraicGeometry.modulePullbackPseudofunctor` on the other — is a declaration of its own, and
the identification is performed where the schemes, the covering family and the module are
variables.  That is not decoration: at the concrete family of Stacks 03DX (1) each such
identification costs a sizeable fraction of the heartbeat budget, and a single declaration
performing four of them does not elaborate.  `AlgebraicGeometry.descentDataHom_conjugate_agree`
is where they are concentrated; its consumer matches it by first-order unification alone.

**How this reaches the `homRestr` spelling.**  The hypothesis of
`AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_agree` is stated with `homRestr`,
the relocalization of the internal hom, while what is proved here is the equality of the two
restrictions in the `objRestrict` spelling.  `homRestr_app_eq` reduces the first to the equality,
for every object `A` of the slice at `Z`, of the components

    `(objRestrictPreimageIso θ_i).hom.val.app (op ((Over.map a₁).obj A))`

for the two members; `Stacks.SectionsComponents.pushforward_map_val_app` and
`AlgebraicGeometry.BigFppfOver.objRestrictFunctor_map_objRestrictPreimageIso` rewrite each of
those as a component of `θ_i` at an object of the big fppf site of the scheme of `X i`, and
`AlgebraicGeometry.BigFppfOver.restrictObjRestrictIso` relates the two through the components of
`AlgebraicGeometry.BigFppfOver.objRestrictComp`.  Two indices of the site occur,
`(Over.map a₁).obj A` and `CategoryTheory.Over.iteratedSliceBackward` of its image downstairs,
and they differ by `CategoryTheory.Over.w` of `a₁` together with associativity — exactly the
transport that `objRestrictComp` performs; so the identity to prove is the naturality of the
component of `θ_i` along the canonical arrow of the site that has the identity underneath,
matched against the component of `objRestrictComp`.

The delicate step is the component of `objRestrictComp`, and it is carried out in two files on
top of this one.
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/EffectiveGlueAgreementBridge.lean`
exhibits that component as restriction along a reassociation arrow of the site, and
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/EffectiveGlueAgreementTransport.lean`
assembles the transport and closes the clause.  What they must avoid, and what every statement
added here must avoid too, is a statement in which the elaborator has to *discover* that the
sections of two restrictions are the sections of the module itself: neither

    `((objRestrictComp B S hS g).app M).hom.val.app (Opposite.op W) = M.val.map u.op`

nor the underlying carrier-type identification

    `↥(((objRestrict B S hS T ⋙ objRestrict B _ _ (Over.mk g.left)).obj M).val.obj (op W)) =
      ↥(M.val.obj (op (Over.mk ((W.hom ≫ g.left) ≫ T.hom))))`

fits in the heartbeat budget, because the base of the inner restriction is
`AlgebraicGeometry.BigFppfOver.objScheme` of `T` and the identification of
`AlgebraicGeometry.BigFppfOver.structureSheaf` there with the restriction of the structure sheaf
of the whole site unfolds a semireducible definition.  The same identification *one* restriction
deep is cheap — `((objRestrict B S hS T).obj M).val.obj (op V) =
M.val.obj (op ((Over.map T.hom).obj V))` is `rfl` in a second — so the composite is reached by
composing two instances of that single-step identity stated with the base as a variable, and
every statement downstream carries it as an explicit `cast`: the design of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SectionsComponentsInduced.lean`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 023B](https://stacks.math.columbia.edu/tag/023B)
-/

@[expose] public section

open CategoryTheory Opposite

universe t v' v u' u w

namespace Stacks

section Abstract

variable {𝔄 : Type*} [Category 𝔄] {𝔅 : Type*} [Category 𝔅] {ℭ : Type*} [Category ℭ]
  {𝔛 : Type*} [Category 𝔛] {𝔵 : Type*} [Category 𝔵]
  {P : 𝔄 ⥤ 𝔅} {P' : 𝔄 ⥤ ℭ} {Q : 𝔅 ⥤ ℭ} (κ : P ⋙ Q ≅ P')
  {aX : 𝔛 ⥤ 𝔅} {aZ : 𝔵 ⥤ ℭ} {pb : 𝔛 ⥤ 𝔵} (N : pb ⋙ aZ ≅ aX ⋙ Q)

/-- **The restriction of a transported comparison, abstractly.**  The conjugate by `κ` of a
comparison `aX.obj F₀ ≅ P.obj M` corrected by an isomorphism `ι : F₀ ≅ F₁` and a second
comparison `e : aX.obj F₁ ≅ P.obj G` is the composite of the two transported comparisons with
the image of `ι`.  This is naturality of `N` at `ι` and nothing else. -/
public theorem restrict_comparison_trans {F₀ F₁ : 𝔛} {M G : 𝔄} (ι : F₀ ≅ F₁)
    (d : aX.obj F₀ ≅ P.obj M) (e : aX.obj F₁ ≅ P.obj G) :
    (κ.app M).symm ≪≫ Q.mapIso (d.symm ≪≫ aX.mapIso ι ≪≫ e) ≪≫ κ.app G =
      (N.app F₀ ≪≫ Q.mapIso d ≪≫ κ.app M).symm ≪≫ aZ.mapIso (pb.mapIso ι) ≪≫
        (N.app F₁ ≪≫ Q.mapIso e ≪≫ κ.app G) := by
  have key : N.inv.app F₀ ≫ aZ.map (pb.map ι.hom) ≫ N.hom.app F₁ = Q.map (aX.map ι.hom) := by
    rw [show aZ.map (pb.map ι.hom) ≫ N.hom.app F₁ = (pb ⋙ aZ).map ι.hom ≫ N.hom.app F₁ from rfl,
      N.hom.naturality ι.hom, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    rfl
  refine Iso.ext ?_
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  rw [reassoc_of% key]

end Abstract

/-- **An identity between composites is carried by a functor**, in the orientation that keeps the
two factors apart.  This is `CategoryTheory.Functor.map_comp` twice; it is stated at abstract
categories so that no composition at a concrete category of sheaves of modules has to be
recognized through its instance. -/
public theorem map_eq_of_comp_eq {𝒞 : Type*} [Category 𝒞] {𝒟 : Type*} [Category 𝒟]
    (A : 𝒞 ⥤ 𝒟) {a b c d : 𝒞} (u : a ⟶ b) (v : b ⟶ d) (x : a ⟶ c) (y : c ⟶ d)
    (h : u ≫ v = x ≫ y) : A.map u ≫ A.map v = A.map x ≫ A.map y :=
  (A.map_comp u v).symm.trans ((congrArg A.map h).trans (A.map_comp x y))

/-- **Two comparisons with a common target are related by the composite of two comparisons with
a common source**, as soon as both are compatible with one comparison out of that source. -/
public theorem hom_comp_inv_eq {𝒞 : Type*} [Category 𝒞] {U₁ U₂ V R : 𝒞} (L₁ : U₁ ≅ V)
    (L₂ : U₂ ≅ V) (NZ : R ≅ V) (c₁ : R ≅ U₁) (c₂ : R ≅ U₂)
    (h₁ : c₁.hom ≫ L₁.hom = NZ.hom) (h₂ : c₂.hom ≫ L₂.hom = NZ.hom) :
    L₁.hom ≫ L₂.inv = c₁.inv ≫ c₂.hom := by
  have hL₁ : L₁.hom = c₁.inv ≫ NZ.hom := by rw [← h₁, Iso.inv_hom_id_assoc]
  rw [hL₁, Category.assoc, ← h₂, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The algebra of the combination step.**  A square `h` in a category, carried by a functor
`A`, together with comparisons `L₁`, `L₂` out of the two sources and `K₁`, `K₂` out of the two
targets: the two conjugates agree as soon as `A.map v` is the composite of the comparisons of the
targets and the composite of the comparisons of the sources is `A.map x`.

Everything is phrased with `A.map` of a morphism of the source category, which is what lets a
consumer match it against a goal by first-order unification alone: the four morphisms are read
off the goal, and the only identification left is the one between the square's own factors and
their spellings in the goal. -/
public theorem iso_trans_eq_of_squares_map {𝒞 : Type*} [Category 𝒞] {𝒟 : Type*} [Category 𝒟]
    (A : 𝒞 ⥤ 𝒟) {a b c d : 𝒞} {V Y : 𝒟} (L₁ : A.obj a ≅ V) (L₂ : A.obj c ≅ V)
    (K₁ : A.obj b ≅ Y) (K₂ : A.obj d ≅ Y) (u : a ⟶ b) (v : b ⟶ d) (x : a ⟶ c) (y : c ⟶ d)
    (hv : A.map v = K₁.hom ≫ K₂.inv) (ht : L₁.hom ≫ L₂.inv = A.map x)
    (h : u ≫ v = x ≫ y) :
    L₁.inv ≫ A.map u ≫ K₁.hom = L₂.inv ≫ A.map y ≫ K₂.hom := by
  have hm := map_eq_of_comp_eq A u v x y h
  rw [hv, ← ht] at hm
  simpa using congr(L₁.inv ≫ $hm ≫ K₂.hom)

end Stacks

namespace AlgebraicGeometry

/-- **The transitions of the canonical descent datum of a quasi-coherent module**, in the
`AlgebraicGeometry.pullModComp` spelling: the transition over an object mapping to two members
of the family is the inverse of the comparison of iterated pullbacks at the first index followed
by the comparison at the second. -/
public theorem canonicalDescentFunctor_obj_obj_hom {Iw : Type t} {S : Scheme.{u}}
    {Y : Iw → Scheme.{u}} (f : ∀ i, Y i ⟶ S)
    (W : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)
    {V : Scheme.{u}} (q : V ⟶ S) (i j : Iw) (f₁ : V ⟶ Y i) (f₂ : V ⟶ Y j)
    (h₁ : f₁ ≫ f i = q) (h₂ : f₂ ≫ f j = q) :
    (((canonicalDescentFunctor f).obj W).obj).hom q f₁ f₂ h₁ h₂ =
      (pullModComp f₁ (f i) q h₁ W.obj).inv ≫ (pullModComp f₂ (f j) q h₂ W.obj).hom := rfl

/-- **The pullback functor of the pullback pseudofunctor is the pullback of modules**, on
morphisms.  The two spellings are the same functor; the identity is recorded at arbitrary
morphisms of schemes, where it is `rfl` at no cost. -/
public theorem modulePullbackPseudofunctor_map_toFunctor_map {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    {M N : Z.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.pullback f).map φ =
      (modulePullbackPseudofunctor.map f.op.toLoc).toFunctor.map φ := rfl

/-- **The same, carried by a functor and split** into the two comparisons. -/
public theorem map_canonicalDescentFunctor_obj_obj_hom {Iw : Type t} {S : Scheme.{u}}
    {Y : Iw → Scheme.{u}} (f : ∀ i, Y i ⟶ S)
    (W : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)
    {V : Scheme.{u}} (q : V ⟶ S) (i j : Iw) (f₁ : V ⟶ Y i) (f₂ : V ⟶ Y j)
    (h₁ : f₁ ≫ f i = q) (h₂ : f₂ ≫ f j = q)
    {𝒟 : Type*} [CategoryTheory.Category 𝒟] (A : V.Modules ⥤ 𝒟) :
    A.map ((((canonicalDescentFunctor f).obj W).obj).hom q f₁ f₂ h₁ h₂) =
      A.map (pullModComp f₁ (f i) q h₁ W.obj).inv ≫
        A.map (pullModComp f₂ (f j) q h₂ W.obj).hom :=
  (congrArg A.map (canonicalDescentFunctor_obj_obj_hom f W q i j f₁ f₂ h₁ h₂)).trans
    (A.map_comp _ _)

/-- **The agreement of two transported comparisons over a morphism of descent data, abstractly.**
Let `Ψ` be a morphism from the canonical descent datum of a quasi-coherent module `W` to a
descent datum `D`, let `V` be a scheme mapping to two members of the family, let `A` be any
functor out of the modules on `V`, and let `L₁`, `L₂` and `K₁`, `K₂` be comparisons of the
images under `A` of the two pullbacks of `W` and of the two components of `D`.  If `A` carries
the transition of `D` to the composite of the comparisons of the components (`hv`), and the
composite of the comparisons of the pullbacks of `W` is the transition of the canonical datum
(`ht`), then the two conjugates of the components of `Ψ` agree.

Every identification between the two spellings of the pullback of sheaves of modules on a scheme
and every unfolding of the canonical descent datum happens here, where the schemes, the family
and the module are variables; a consumer at a concrete site matches the statement by first-order
unification alone. -/
public theorem descentDataHom_conjugate_agree {Iw : Type t} {S : Scheme.{u}}
    {Y : Iw → Scheme.{u}} (f : ∀ i, Y i ⟶ S)
    (W : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)
    {D : modulePullbackPseudofunctor.DescentData f}
    (Ψ : ((canonicalDescentFunctor f).obj W).obj ⟶ D)
    {V : Scheme.{u}} (q : V ⟶ S) (i j : Iw) (f₁ : V ⟶ Y i) (f₂ : V ⟶ Y j)
    (h₁ : f₁ ≫ f i = q) (h₂ : f₂ ≫ f j = q)
    {𝒟 : Type*} [CategoryTheory.Category 𝒟] (A : V.Modules ⥤ 𝒟) {Vt Yt : 𝒟}
    (L₁ : A.obj ((Scheme.Modules.pullback f₁).obj
      ((Scheme.Modules.pullback (f i)).obj W.obj)) ≅ Vt)
    (L₂ : A.obj ((Scheme.Modules.pullback f₂).obj
      ((Scheme.Modules.pullback (f j)).obj W.obj)) ≅ Vt)
    (K₁ : A.obj ((Scheme.Modules.pullback f₁).obj (D.obj i)) ≅ Yt)
    (K₂ : A.obj ((Scheme.Modules.pullback f₂).obj (D.obj j)) ≅ Yt)
    (hv : A.map (D.hom q f₁ f₂ h₁ h₂) = K₁.hom ≫ K₂.inv)
    (ht : L₁.hom ≫ L₂.inv =
      A.map (pullModComp f₁ (f i) q h₁ W.obj).inv ≫
        A.map (pullModComp f₂ (f j) q h₂ W.obj).hom) :
    L₁.inv ≫ A.map ((Scheme.Modules.pullback f₁).map (Ψ.hom i)) ≫ K₁.hom =
      L₂.inv ≫ A.map ((Scheme.Modules.pullback f₂).map (Ψ.hom j)) ≫ K₂.hom :=
  Stacks.iso_trans_eq_of_squares_map A L₁ L₂ K₁ K₂
    ((Scheme.Modules.pullback f₁).map (Ψ.hom i)) (D.hom q f₁ f₂ h₁ h₂)
    ((((canonicalDescentFunctor f).obj W).obj).hom q f₁ f₂ h₁ h₂)
    ((Scheme.Modules.pullback f₂).map (Ψ.hom j)) hv
    (ht.trans (map_canonicalDescentFunctor_obj_obj_hom f W q i j f₁ f₂ h₁ h₂ A).symm)
    (Ψ.comm q f₁ f₂ h₁ h₂)

end AlgebraicGeometry

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The restriction of a local isomorphism along a morphism of the big fppf site.**  An
isomorphism of the restrictions of two modules to the big fppf site of the scheme of `T` is
carried to `T'` by restricting along `g : T' ⟶ T` and contracting the iterated restriction with
`AlgebraicGeometry.BigFppfOver.objRestrictComp`. -/
public noncomputable def restrictObjRestrictIso {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N) :
    (objRestrict B S hS T').obj M ≅ (objRestrict B S hS T').obj N :=
  ((objRestrictComp B S hS g).app M).symm ≪≫
    (objRestrict B (objScheme B S hS T) (contains_objScheme B S hS T)
      (Over.mk g.left)).mapIso θ ≪≫ (objRestrictComp B S hS g).app N

/-- **The compatibility of Stacks 03DV with composition, read at a module on `S`.**  The
comparison of Stacks 03DV at `T'` is the comparison of iterated pullbacks followed by the
comparison `AlgebraicGeometry.BigFppfOver.localAssociatedModuleComparison` at `g` of the local
datum of `𝓕^a` on `T` supplied by Stacks 03DV itself.

This is the component at `𝓕` of `AlgebraicGeometry.BigFppfOver.NatIsoCompSquare`, which
`AlgebraicGeometry.BigFppfOver.natIsoCompSquare_of_sectionsCocycle` proves unconditionally. -/
public theorem associatedModule_map_pullModComp_comp_localAssociatedModuleComparison
    {T T' : BigFppfOver B S hS} (g : T' ⟶ T) (𝓕 : S.Modules) :
    (associatedModule B (objScheme B S hS T') (contains_objScheme B S hS T')).map
          (pullModComp (objHom B (objScheme B S hS T) (contains_objScheme B S hS T)
              (Over.mk g.left)) (objHom B S hS T) (objHom B S hS T')
            (objHom_comp B S hS g) 𝓕).hom ≫
        (localAssociatedModuleComparison B S hS ((associatedModule B S hS).obj 𝓕) g
          ((Scheme.Modules.pullback (objHom B S hS T)).obj 𝓕)
          ((associatedModuleObjRestrictNatIso B S hS T).app 𝓕)).hom =
      ((associatedModuleObjRestrictNatIso B S hS T').app 𝓕).hom := by
  have hsq := NatTrans.congr_app
    (congrArg Iso.hom (natIsoCompSquare_of_sectionsCocycle B S hS g (sectionsCocycle B S hS g))) 𝓕
  have hc0 : (pullModComp (objHom B (objScheme B S hS T) (contains_objScheme B S hS T)
          (Over.mk g.left)) (objHom B S hS T) (objHom B S hS T')
        (objHom_comp B S hS g) 𝓕).hom =
      (Scheme.Modules.pullbackCongr (objHom_comp B S hS g)).inv.app 𝓕 ≫
        (Scheme.Modules.pullbackComp (objHom B (objScheme B S hS T)
          (contains_objScheme B S hS T) (Over.mk g.left)) (objHom B S hS T)).inv.app 𝓕 :=
    congrArg Iso.inv (pullModComp_symm_app (objHom B (objScheme B S hS T)
      (contains_objScheme B S hS T) (Over.mk g.left)) (objHom B S hS T)
      (objHom B S hS T') (objHom_comp B S hS g) 𝓕)
  rw [show ((associatedModuleObjRestrictNatIso B S hS T').app 𝓕).hom =
      (associatedModuleObjRestrictNatIso B S hS T').hom.app 𝓕 from rfl, ← hsq]
  simp only [localAssociatedModuleComparison, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.app_hom, Functor.mapIso_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    NatTrans.comp_app, Category.id_comp]
  rw [hc0]
  congr 1

variable {I : Type w} (X : I → BigFppfOver B S hS) (G : SheafOfModules.{u} (structureSheaf B S hS))
  (F : ∀ i, (objScheme B S hS (X i)).Modules) (hF : ∀ i, (F i).IsQuasicoherent)
  (e : ∀ i, (associatedModule B (objScheme B S hS (X i))
    (contains_objScheme B S hS (X i))).obj (F i) ≅ (objRestrict B S hS (X i)).obj G)

/-- **The naturality computation**: the restriction of the local isomorphism of Stacks 03DX (1)
at `X i` along `g : Z ⟶ X i` is the comparison at `g` of the local datum of `𝓕^a` on `X i`
supplied by Stacks 03DV, inverted, followed by the pullback of the component of the effectivity
isomorphism and by the comparison at `g` of the given local datum of `𝒢`. -/
public theorem restrict_effectiveGlueObjRestrictIso
    (heff : (memberQcohDatum B S hS X G F hF e).IsEffective) (i : I)
    {Z : BigFppfOver B S hS} (g : Z ⟶ X i) :
    restrictObjRestrictIso B S hS g
        (effectiveGlueObjRestrictIso B S hS X G F hF e heff i) =
      (localAssociatedModuleComparison B S hS
          ((associatedModule B S hS).obj (effectiveGlueModule B S hS X G F hF e heff)) g
          ((Scheme.Modules.pullback (objHom B S hS (X i))).obj
            (effectiveGlueModule B S hS X G F hF e heff))
          ((associatedModuleObjRestrictNatIso B S hS (X i)).app
            (effectiveGlueModule B S hS X G F hF e heff))).symm ≪≫
        (associatedModule B (objScheme B S hS Z) (contains_objScheme B S hS Z)).mapIso
            ((Scheme.Modules.pullback (objHomOver B S hS g)).mapIso
              (effectiveGlueComponentIso B S hS X G F hF e heff i)) ≪≫
          localAssociatedModuleComparison B S hS G g (F i) (e i) :=
  Stacks.restrict_comparison_trans (objRestrictComp B S hS g)
    (associatedModuleObjRestrictNatIso B (objScheme B S hS (X i))
      (contains_objScheme B S hS (X i)) (Over.mk g.left))
    (effectiveGlueComponentIso B S hS X G F hF e heff i)
    ((associatedModuleObjRestrictNatIso B S hS (X i)).app
      (effectiveGlueModule B S hS X G F hF e heff)) (e i)

/-- **The transition of the datum of Stacks 03DX (1) over an object mapping to two members,
read through Stacks 03DV.**  Its associated module on the scheme of `Z` is the comparison of
Stacks 03DV at `a₁` followed by the inverse of the comparison at `a₂`.

Every pair of morphisms into two members factors through the fibre product by
`AlgebraicGeometry.BigFppfOver.exists_hom_memberProd`, so the identification holds at an
arbitrary pair and not only at the two projections. -/
public theorem associatedModule_map_memberDatum_hom {Z : BigFppfOver B S hS} {i j : I}
    (a₁ : Z ⟶ X i) (a₂ : Z ⟶ X j) :
    (associatedModule B (objScheme B S hS Z) (contains_objScheme B S hS Z)).map
        (X := (Scheme.Modules.pullback (objHomOver B S hS a₁)).obj (F i))
        (Y := (Scheme.Modules.pullback (objHomOver B S hS a₂)).obj (F j))
        ((memberDatum B S hS X G F hF e).hom (objHom B S hS Z)
          (objHomOver B S hS a₁) (objHomOver B S hS a₂)
          (objHom_comp B S hS a₁) (objHom_comp B S hS a₂)) =
      (localAssociatedModuleComparison B S hS G a₁ (F i) (e i)).hom ≫
        (localAssociatedModuleComparison B S hS G a₂ (F j) (e j)).inv := by
  obtain ⟨m, hm₁, hm₂⟩ := exists_hom_memberProd B S hS X a₁ a₂
  exact (congrArg (associatedModule B (objScheme B S hS Z) (contains_objScheme B S hS Z)).map
      (memberDatum_hom_eq_transitionIso B S hS X G F hF e m hm₁.symm hm₂.symm
        (objHom B S hS Z) (objHom_comp B S hS a₁) (objHom_comp B S hS a₂))).trans
    (associatedModule_map_transitionIso B S hS G a₁ a₂ (hF i) (e i) (hF j) (e j))

/-- The component of the effectivity isomorphism, read as a component of the isomorphism of
descent data it is formed from. -/
public theorem effectiveGlueComponentIso_hom
    (heff : (memberQcohDatum B S hS X G F hF e).IsEffective) (i : I) :
    (effectiveGlueComponentIso B S hS X G F hF e heff i).hom =
      (effectiveGlueDatumIso B S hS X G F hF e heff).hom.hom i := rfl

/-- **The two comparisons of the ambient module at two morphisms into two members differ by the
transition of the canonical descent datum of the glued module.**  Both are compatible, by
`AlgebraicGeometry.BigFppfOver`
`.associatedModule_map_pullModComp_comp_localAssociatedModuleComparison`, with the comparison of
Stacks 03DV at `Z` itself. -/
public theorem localAssociatedModuleComparison_glue_hom_comp_inv
    (heff : (memberQcohDatum B S hS X G F hF e).IsEffective) {Z : BigFppfOver B S hS} {i j : I}
    (a₁ : Z ⟶ X i) (a₂ : Z ⟶ X j) :
    (localAssociatedModuleComparison B S hS
        ((associatedModule B S hS).obj (effectiveGlueModule B S hS X G F hF e heff)) a₁
        ((Scheme.Modules.pullback (objHom B S hS (X i))).obj
          (effectiveGlueModule B S hS X G F hF e heff))
        ((associatedModuleObjRestrictNatIso B S hS (X i)).app
          (effectiveGlueModule B S hS X G F hF e heff))).hom ≫
      (localAssociatedModuleComparison B S hS
          ((associatedModule B S hS).obj (effectiveGlueModule B S hS X G F hF e heff)) a₂
          ((Scheme.Modules.pullback (objHom B S hS (X j))).obj
            (effectiveGlueModule B S hS X G F hF e heff))
          ((associatedModuleObjRestrictNatIso B S hS (X j)).app
            (effectiveGlueModule B S hS X G F hF e heff))).inv =
      (associatedModule B (objScheme B S hS Z) (contains_objScheme B S hS Z)).map
          (pullModComp (objHomOver B S hS a₁) (memberStructureHom B S hS X i)
            (objHom B S hS Z) (objHom_comp B S hS a₁)
            (Functor.essImage.witness heff).obj).inv ≫
        (associatedModule B (objScheme B S hS Z) (contains_objScheme B S hS Z)).map
          (pullModComp (objHomOver B S hS a₂) (memberStructureHom B S hS X j)
            (objHom B S hS Z) (objHom_comp B S hS a₂)
            (Functor.essImage.witness heff).obj).hom :=
  Stacks.hom_comp_inv_eq _ _
    ((associatedModuleObjRestrictNatIso B S hS Z).app (effectiveGlueModule B S hS X G F hF e heff))
    ((associatedModule B (objScheme B S hS Z) (contains_objScheme B S hS Z)).mapIso
      (pullModComp (objHomOver B S hS a₁) (objHom B S hS (X i)) (objHom B S hS Z)
        (objHom_comp B S hS a₁) (effectiveGlueModule B S hS X G F hF e heff)))
    ((associatedModule B (objScheme B S hS Z) (contains_objScheme B S hS Z)).mapIso
      (pullModComp (objHomOver B S hS a₂) (objHom B S hS (X j)) (objHom B S hS Z)
        (objHom_comp B S hS a₂) (effectiveGlueModule B S hS X G F hF e heff)))
    (associatedModule_map_pullModComp_comp_localAssociatedModuleComparison B S hS a₁
      (effectiveGlueModule B S hS X G F hF e heff))
    (associatedModule_map_pullModComp_comp_localAssociatedModuleComparison B S hS a₂
      (effectiveGlueModule B S hS X G F hF e heff))

/-- **The restrictions of the local isomorphisms of Stacks 03DX (1) along two morphisms into two
members agree.**  Everything the agreement needs is now in place: the naturality computation
`AlgebraicGeometry.BigFppfOver.restrict_effectiveGlueObjRestrictIso` rewrites each restriction as
a comparison of Stacks 03DV conjugating the component of the effectivity isomorphism;
`CategoryTheory.Pseudofunctor.DescentData.Hom.comm` of that isomorphism, read through Stacks 03DV
by `AlgebraicGeometry.BigFppfOver.associatedModule_map_memberDatum_hom`, identifies the two
conjugates up to the transition of the canonical descent datum of the glued module; and the
compatibility of Stacks 03DV with composition — the component at `𝓕` of
`AlgebraicGeometry.BigFppfOver.NatIsoCompSquare`, unconditional by
`…natIsoCompSquare_of_sectionsCocycle` — identifies that transition with the difference of the
two comparisons of the ambient module `𝓕^a`.

Taken at the two projections of `X i ×_S X j` this is the agreement that
`AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_agree` asks for, read in the
`objRestrict` spelling. -/
public theorem restrictObjRestrictIso_effectiveGlueObjRestrictIso_eq
    (heff : (memberQcohDatum B S hS X G F hF e).IsEffective) {Z : BigFppfOver B S hS} {i j : I}
    (a₁ : Z ⟶ X i) (a₂ : Z ⟶ X j) :
    restrictObjRestrictIso B S hS a₁
        (effectiveGlueObjRestrictIso B S hS X G F hF e heff i) =
      restrictObjRestrictIso B S hS a₂
        (effectiveGlueObjRestrictIso B S hS X G F hF e heff j) := by
  rw [restrict_effectiveGlueObjRestrictIso, restrict_effectiveGlueObjRestrictIso]
  refine Iso.ext ?_
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  exact descentDataHom_conjugate_agree (memberStructureHom B S hS X)
    (Functor.essImage.witness heff) (effectiveGlueDatumIso B S hS X G F hF e heff).hom
    (objHom B S hS Z) i j (objHomOver B S hS a₁) (objHomOver B S hS a₂)
    (objHom_comp B S hS a₁) (objHom_comp B S hS a₂)
    (associatedModule B (objScheme B S hS Z) (contains_objScheme B S hS Z)) _ _ _ _
    (associatedModule_map_memberDatum_hom B S hS X G F hF e a₁ a₂)
    (localAssociatedModuleComparison_glue_hom_comp_inv B S hS X G F hF e heff a₁ a₂)

end AlgebraicGeometry.BigFppfOver

end
