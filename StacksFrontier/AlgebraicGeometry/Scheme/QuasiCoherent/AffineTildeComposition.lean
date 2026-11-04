module

public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.CategoryTheory.Adjunction.Mates

/-!
# Composition and unit compatibilities of the affine pullback comparison

Let `f : R ⟶ S` and `g : S ⟶ T` be homomorphisms of commutative rings. The comparison
`AlgebraicGeometry.pullbackTildeIso` identifies the pullback of an associated sheaf along
`Spec f` with the associated sheaf of an extension of scalars along `f`. These comparisons are
compatible with composition: the comparison for `f ≫ g` is the comparison for `f` followed by the
comparison for `g`, read through the canonical factorization of the pullback along `Spec (f ≫ g)`
and through `ModuleCat.extendScalarsComp`. At an identity ring homomorphism the comparison is the
canonical identification of the pullback along an identity and of an extension of scalars along an
identity.

Both statements are deduced from a characterization of `pullbackTildeIso` on the side of the
*right* adjoints: `pullbackTildeIso R S f` is the unique natural isomorphism whose conjugate,
with respect to the pullback--global-sections adjunction and the extension--global-sections
adjunction, is the inverse of `pushforwardΓIso R S f`. Conjugation is a bijection, so the
composition statement becomes one equation between natural transformations built from
pushforward, global sections and restriction of scalars, which is
`AlgebraicGeometry.pushforwardΓIso_inv_comp`.

## Main definitions

* `AlgebraicGeometry.pushforwardSpecMapCompIso`: the composite of the pushforwards along `Spec g`
  and `Spec f` is the pushforward along `Spec (f ≫ g)`.
* `AlgebraicGeometry.pullbackSpecMapCompIso`: the pullback along `Spec (f ≫ g)` factors as the
  pullback along `Spec f` followed by the pullback along `Spec g`.
* `AlgebraicGeometry.pushforwardSpecMapIdIso`: the pushforward along `Spec (𝟙 R)` is the identity
  functor.
* `AlgebraicGeometry.pullbackSpecMapIdIso`: the pullback along `Spec (𝟙 R)` is the identity
  functor.

## Main results

* `AlgebraicGeometry.conjugateEquiv_pullbackTildeIso_hom` and
  `AlgebraicGeometry.eq_pullbackTildeIso_of_conjugateEquiv`: the affine pullback comparison is
  the natural isomorphism whose conjugate is the inverse of `pushforwardΓIso`.
* `AlgebraicGeometry.conjugateEquiv_pullbackSpecMapCompIso_hom` and
  `AlgebraicGeometry.conjugateEquiv_pullbackSpecMapIdIso_hom`: the conjugates of the two
  factorizations of a pullback are the corresponding factorizations of a pushforward.
* `AlgebraicGeometry.pushforwardΓIso_inv_comp` and `AlgebraicGeometry.pushforwardΓIso_inv_id`:
  the compatibilities of `pushforwardΓIso` with composition and with the identity.
* `AlgebraicGeometry.pullbackTildeIso_comp`: the affine pullback comparison is compatible with
  composition of ring homomorphisms.
* `AlgebraicGeometry.pullbackTildeIso_id`: the affine pullback comparison at an identity ring
  homomorphism is the canonical identification.

## Implementation notes

The argument is entirely two-categorical: it uses `CategoryTheory.conjugateEquiv` and its
calculus (`CategoryTheory.conjugateEquiv_comp`,
`CategoryTheory.conjugateEquiv_whiskerLeft`, `CategoryTheory.conjugateEquiv_whiskerRight`,
`CategoryTheory.conjugateEquiv_associator_hom` and the two unitors) together with
`Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom`, which identifies the
conjugate of a comparison of left adjoints induced by a comparison of right adjoints. That
last result, and the related `CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_comp`,
already live in `StacksFrontier.CategoryTheory.Adjunction.Mates` and
`StacksFrontier.CategoryTheory.Adjunction.UniqueComp`; neither needs to be redeveloped here.

Pushing the comparison to the side of the right adjoints is what keeps the whole argument small.
`AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv` is used only as an equation
between natural transformations, never evaluated on sections, so the pullback functor and the
unit of the pullback--pushforward adjunction never meet the section-level API. The only
section-level computations are the two compatibilities of `pushforwardΓIso`, where every
component is the identity on elements; they are stated through
`AlgebraicGeometry.Scheme.Modules.Hom.app` and cite Mathlib's `rfl` lemmas
`Scheme.Modules.pushforwardComp_hom_app_app`, `Scheme.Modules.pushforwardId_inv_app_app`,
`Scheme.Modules.pushforwardCongr_inv_app_app` and `Scheme.Modules.Hom.comp_app` rather than
re-deriving them, and the bridge to `AffineTilde.lean`'s spelling of a section is left to
definitional unfolding of a *variable* morphism.

The shared universe is imposed by Mathlib's `tilde.functor` and the scheme-module API; the
statements hold in every such universe.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/
@[expose] public noncomputable section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction
open scoped ChangeOfRings

universe u

/-- The conjugate of the inverse of an isomorphism of left adjoints is the inverse of the
conjugate of the isomorphism. -/
private theorem conjugateEquiv_iso_inv {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} {adj₁ : L₁ ⊣ R₁} {adj₂ : L₂ ⊣ R₂} {e : L₂ ≅ L₁}
    {t : R₁ ≅ R₂} (h : conjugateEquiv adj₁ adj₂ e.hom = t.hom) :
    conjugateEquiv adj₂ adj₁ e.inv = t.inv := by
  have h2 : t.hom ≫ conjugateEquiv adj₂ adj₁ e.inv = 𝟙 _ := by
    rw [← h]
    exact conjugateEquiv_comm adj₁ adj₂ e.inv_hom_id
  rw [← Category.id_comp (conjugateEquiv adj₂ adj₁ e.inv), ← t.inv_hom_id, Category.assoc, h2,
    Category.comp_id]

/-- The conjugate of the affine pullback comparison, with respect to the composite
pullback--global-sections adjunction and the composite extension--global-sections adjunction,
is the inverse of the comparison `pushforwardΓIso` of the two right adjoints. -/
public theorem conjugateEquiv_pullbackTildeIso_hom (R S : CommRingCat.{u}) (f : R ⟶ S) :
    conjugateEquiv ((ModuleCat.extendRestrictScalarsAdj f.hom).comp (tilde.adjunction (R := S)))
      ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)))
      (pullbackTildeIso R S f).hom = (pushforwardΓIso R S f).inv :=
  Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _

/-- A natural isomorphism from the pullback of associated sheaves along `Spec f` to the
associated sheaves of extensions of scalars along `f` whose conjugate is the inverse of
`pushforwardΓIso R S f` is `AlgebraicGeometry.pullbackTildeIso`. -/
public theorem eq_pullbackTildeIso_of_conjugateEquiv (R S : CommRingCat.{u}) (f : R ⟶ S)
    (e : tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map f) ≅
      ModuleCat.extendScalars f.hom ⋙ tilde.functor S)
    (he : conjugateEquiv ((ModuleCat.extendRestrictScalarsAdj f.hom).comp
        (tilde.adjunction (R := S)))
        ((tilde.adjunction (R := R)).comp
          (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)))
        e.hom = (pushforwardΓIso R S f).inv) :
    e = pullbackTildeIso R S f :=
  Iso.ext ((conjugateEquiv ((ModuleCat.extendRestrictScalarsAdj f.hom).comp
    (tilde.adjunction (R := S))) ((tilde.adjunction (R := R)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)))).injective
    (he.trans (conjugateEquiv_pullbackTildeIso_hom R S f).symm))

/-- The comparison of the pushforwards along two equal morphisms of schemes is the identity when
the two morphisms are the same term. -/
private theorem pushforwardCongr_inv_eq_id {X Y : Scheme.{u}} (p : X ⟶ Y) :
    (Scheme.Modules.pushforwardCongr (rfl : p = p)).inv = 𝟙 _ := by
  refine NatTrans.ext (funext fun M => Scheme.Modules.hom_ext _ _ fun U => ?_)
  rw [Scheme.Modules.pushforwardCongr_inv_app_app, NatTrans.id_app,
    Scheme.Modules.Hom.id_app, eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- The conjugate of the comparison of the pullbacks along two equal morphisms of schemes is the
inverse of the comparison of the pushforwards along those morphisms. -/
public theorem conjugateEquiv_pullbackCongr_hom {X Y : Scheme.{u}} {p q : X ⟶ Y} (h : p = q) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction q)
        (Scheme.Modules.pullbackPushforwardAdjunction p)
        (Scheme.Modules.pullbackCongr h).hom =
      (Scheme.Modules.pushforwardCongr h).inv := by
  subst h
  rw [pushforwardCongr_inv_eq_id,
    show (Scheme.Modules.pullbackCongr (rfl : p = p)).hom = 𝟙 _ from rfl, conjugateEquiv_id]

/-- On global sections, the comparison of the pushforwards along two equal morphisms of schemes
is the identity. -/
private theorem pushforwardCongr_inv_app_appTop {X Y : Scheme.{u}} {p q : X ⟶ Y} (h : p = q)
    (M : X.Modules) (x : Γ((Scheme.Modules.pushforward q).obj M, ⊤)) :
    ((Scheme.Modules.pushforwardCongr h).inv.app M).app ⊤ x = x := by
  subst h
  rw [Scheme.Modules.pushforwardCongr_inv_app_app, eqToHom_refl, op_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- The pushforward of sheaves of modules along `Spec g` followed by the pushforward along
`Spec f` is the pushforward along `Spec (f ≫ g)`. -/
public noncomputable def pushforwardSpecMapCompIso (R S T : CommRingCat.{u}) (f : R ⟶ S)
    (g : S ⟶ T) :
    Scheme.Modules.pushforward (Spec.map g) ⋙ Scheme.Modules.pushforward (Spec.map f) ≅
      Scheme.Modules.pushforward (Spec.map (f ≫ g)) :=
  Scheme.Modules.pushforwardComp (Spec.map g) (Spec.map f) ≪≫
    (Scheme.Modules.pushforwardCongr (Spec.map_comp f g)).symm

/-- The pullback of sheaves of modules along `Spec (f ≫ g)` factors as the pullback along
`Spec f` followed by the pullback along `Spec g`. -/
public noncomputable def pullbackSpecMapCompIso (R S T : CommRingCat.{u}) (f : R ⟶ S)
    (g : S ⟶ T) :
    Scheme.Modules.pullback (Spec.map (f ≫ g)) ≅
      Scheme.Modules.pullback (Spec.map f) ⋙ Scheme.Modules.pullback (Spec.map g) :=
  Scheme.Modules.pullbackCongr (Spec.map_comp f g) ≪≫
    (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).symm

/-- The pushforward of sheaves of modules along `Spec (𝟙 R)` is the identity functor. -/
public noncomputable def pushforwardSpecMapIdIso (R : CommRingCat.{u}) :
    Scheme.Modules.pushforward (Spec.map (𝟙 R)) ≅ 𝟭 (Spec R).Modules :=
  Scheme.Modules.pushforwardCongr (Spec.map_id R) ≪≫ Scheme.Modules.pushforwardId (Spec R)

/-- The pullback of sheaves of modules along `Spec (𝟙 R)` is the identity functor. -/
public noncomputable def pullbackSpecMapIdIso (R : CommRingCat.{u}) :
    Scheme.Modules.pullback (Spec.map (𝟙 R)) ≅ 𝟭 (Spec R).Modules :=
  Scheme.Modules.pullbackCongr (Spec.map_id R) ≪≫ Scheme.Modules.pullbackId (Spec R)

/-- The conjugate of the factorization `pullbackSpecMapCompIso` of the pullback along
`Spec (f ≫ g)` is the factorization `pushforwardSpecMapCompIso` of the pushforward. -/
public theorem conjugateEquiv_pullbackSpecMapCompIso_hom (R S T : CommRingCat.{u})
    (f : R ⟶ S) (g : S ⟶ T) :
    conjugateEquiv
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).comp
          (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g)))
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (f ≫ g)))
        (pullbackSpecMapCompIso R S T f g).hom =
      (pushforwardSpecMapCompIso R S T f g).hom := by
  rw [show (pullbackSpecMapCompIso R S T f g).hom =
      (Scheme.Modules.pullbackCongr (Spec.map_comp f g)).hom ≫
        (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).inv from rfl,
    ← conjugateEquiv_comp _
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g ≫ Spec.map f)) _,
    Scheme.Modules.conjugateEquiv_pullbackComp_inv, conjugateEquiv_pullbackCongr_hom]
  rfl

/-- The conjugate of the identification `pullbackSpecMapIdIso` of the pullback along `Spec (𝟙 R)`
with the identity functor is the inverse of the identification `pushforwardSpecMapIdIso` of the
pushforward. -/
public theorem conjugateEquiv_pullbackSpecMapIdIso_hom (R : CommRingCat.{u}) :
    conjugateEquiv Adjunction.id
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (𝟙 R)))
        (pullbackSpecMapIdIso R).hom = (pushforwardSpecMapIdIso R).inv := by
  rw [show (pullbackSpecMapIdIso R).hom =
      (Scheme.Modules.pullbackCongr (Spec.map_id R)).hom ≫
        (Scheme.Modules.pullbackId (Spec R)).hom from rfl,
    ← conjugateEquiv_comp _ (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 (Spec R))) _,
    Scheme.Modules.conjugateEquiv_pullbackId_hom, conjugateEquiv_pullbackCongr_hom]
  rfl

/-- The conjugate of the inverse of `ModuleCat.extendScalarsComp` is
`ModuleCat.restrictScalarsComp`; both are values of the same conjugation bijection. -/
private theorem conjugateEquiv_extendScalarsComp_inv (R S T : CommRingCat.{u}) (f : R ⟶ S)
    (g : S ⟶ T) :
    conjugateEquiv (ModuleCat.extendRestrictScalarsAdj (f ≫ g).hom)
        ((ModuleCat.extendRestrictScalarsAdj f.hom).comp
          (ModuleCat.extendRestrictScalarsAdj g.hom))
        (ModuleCat.extendScalarsComp f.hom g.hom).inv =
      (ModuleCat.restrictScalarsComp f.hom g.hom).hom := by
  exact ((conjugateEquiv _ _).eq_symm_apply).1 rfl

/-- The conjugate of the inverse of `ModuleCat.extendScalarsId` is
`ModuleCat.restrictScalarsId`; both are values of the same conjugation bijection. -/
private theorem conjugateEquiv_extendScalarsId_inv (R : CommRingCat.{u}) :
    conjugateEquiv (ModuleCat.extendRestrictScalarsAdj (CommRingCat.Hom.hom (𝟙 R)))
        Adjunction.id (ModuleCat.extendScalarsId R).inv =
      (ModuleCat.restrictScalarsId R).hom := by
  exact ((conjugateEquiv _ _).eq_symm_apply).1 rfl

/-- On global sections, `pushforwardSpecMapCompIso` is the identity. -/
private theorem pushforwardSpecMapCompIso_hom_app_appTop (R S T : CommRingCat.{u})
    (f : R ⟶ S) (g : S ⟶ T) (N : (Spec T).Modules)
    (x : Γ((Scheme.Modules.pushforward (Spec.map g) ⋙
      Scheme.Modules.pushforward (Spec.map f)).obj N, ⊤)) :
    ((pushforwardSpecMapCompIso R S T f g).hom.app N).app ⊤ x = x := by
  have h1 := congr($(Scheme.Modules.pushforwardComp_hom_app_app (Spec.map g) (Spec.map f)
    (M := N) ⊤) x)
  rw [show (pushforwardSpecMapCompIso R S T f g).hom =
      (Scheme.Modules.pushforwardComp (Spec.map g) (Spec.map f)).hom ≫
        (Scheme.Modules.pushforwardCongr (Spec.map_comp f g)).inv from rfl,
    NatTrans.comp_app, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, h1]
  exact pushforwardCongr_inv_app_appTop (Spec.map_comp f g) N x

/-- On global sections, the inverse of `pushforwardSpecMapIdIso` is the identity. -/
private theorem pushforwardSpecMapIdIso_inv_app_appTop (R : CommRingCat.{u})
    (N : (Spec R).Modules) (x : Γ(N, ⊤)) :
    ((pushforwardSpecMapIdIso R).inv.app N).app ⊤ x = x := by
  have h1 := congr($(Scheme.Modules.pushforwardId_inv_app_app (X := Spec R) (M := N)
    (U := ⊤)) x)
  rw [show (pushforwardSpecMapIdIso R).inv =
      (Scheme.Modules.pushforwardId (Spec R)).inv ≫
        (Scheme.Modules.pushforwardCongr (Spec.map_id R)).inv from rfl,
    NatTrans.comp_app, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, h1]
  exact pushforwardCongr_inv_app_appTop (Spec.map_id R) N x

/-- The global-sections comparison for a pushforward is compatible with composition: the
comparison for `f ≫ g` is the comparison for `g` followed by the comparison for `f`, read
through `pushforwardSpecMapCompIso` and `ModuleCat.restrictScalarsComp`. -/
public theorem pushforwardΓIso_inv_comp (R S T : CommRingCat.{u}) (f : R ⟶ S) (g : S ⟶ T) :
    (pushforwardΓIso R T (f ≫ g)).inv =
      Functor.whiskerLeft (moduleSpecΓFunctor (R := T))
          (ModuleCat.restrictScalarsComp f.hom g.hom).hom ≫
        (Functor.associator (moduleSpecΓFunctor (R := T))
          (ModuleCat.restrictScalars g.hom) (ModuleCat.restrictScalars f.hom)).inv ≫
        Functor.whiskerRight (pushforwardΓIso S T g).inv (ModuleCat.restrictScalars f.hom) ≫
        (Functor.associator (Scheme.Modules.pushforward (Spec.map g))
          (moduleSpecΓFunctor (R := S)) (ModuleCat.restrictScalars f.hom)).hom ≫
        Functor.whiskerLeft (Scheme.Modules.pushforward (Spec.map g))
          (pushforwardΓIso R S f).inv ≫
        (Functor.associator (Scheme.Modules.pushforward (Spec.map g))
          (Scheme.Modules.pushforward (Spec.map f)) (moduleSpecΓFunctor (R := R))).inv ≫
        Functor.whiskerRight (pushforwardSpecMapCompIso R S T f g).hom
          (moduleSpecΓFunctor (R := R)) := by
  ext N x
  exact (pushforwardSpecMapCompIso_hom_app_appTop R S T f g N
    (x : Γ((Scheme.Modules.pushforward (Spec.map g) ⋙
      Scheme.Modules.pushforward (Spec.map f)).obj N, ⊤))).symm

/-- The global-sections comparison for a pushforward along `Spec (𝟙 R)` is the canonical
identification: the pushforward along `Spec (𝟙 R)` is the identity functor and restriction of
scalars along the identity of `R` is the identity functor. -/
public theorem pushforwardΓIso_inv_id (R : CommRingCat.{u}) :
    (pushforwardΓIso R R (𝟙 R)).inv =
      Functor.whiskerLeft (moduleSpecΓFunctor (R := R)) (ModuleCat.restrictScalarsId R).hom ≫
        (Functor.rightUnitor (moduleSpecΓFunctor (R := R))).hom ≫
        (Functor.leftUnitor (moduleSpecΓFunctor (R := R))).inv ≫
        Functor.whiskerRight (pushforwardSpecMapIdIso R).inv
          (moduleSpecΓFunctor (R := R)) := by
  ext N x
  exact (pushforwardSpecMapIdIso_inv_app_appTop R N (x : Γ(N, ⊤))).symm

/-- The affine pullback comparison is compatible with composition: for ring homomorphisms
`f : R ⟶ S` and `g : S ⟶ T`, the comparison for `f ≫ g` agrees with the comparison for `f`
followed by the comparison for `g`, modulo the canonical factorization of the pullback along
`Spec (f ≫ g)` and `ModuleCat.extendScalarsComp`. -/
public theorem pullbackTildeIso_comp (R S T : CommRingCat.{u}) (f : R ⟶ S) (g : S ⟶ T) :
    pullbackTildeIso R T (f ≫ g) =
      Functor.isoWhiskerLeft (tilde.functor R) (pullbackSpecMapCompIso R S T f g) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (pullbackTildeIso R S f)
          (Scheme.Modules.pullback (Spec.map g)) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (ModuleCat.extendScalars f.hom) (pullbackTildeIso S T g) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (ModuleCat.extendScalarsComp f.hom g.hom).symm
          (tilde.functor T) := by
  refine (eq_pullbackTildeIso_of_conjugateEquiv R T (f ≫ g) _ ?_).symm
  have step0 := conjugateEquiv_whiskerLeft
    ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g)))
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (f ≫ g)))
    (tilde.adjunction (R := R)) (pullbackSpecMapCompIso R S T f g).hom
  rw [conjugateEquiv_pullbackSpecMapCompIso_hom] at step0
  have step1 := conjugateEquiv_iso_inv (conjugateEquiv_associator_hom
    (tilde.adjunction (R := R)) (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g)))
  have step2 := conjugateEquiv_whiskerRight
    ((ModuleCat.extendRestrictScalarsAdj f.hom).comp (tilde.adjunction (R := S)))
    ((tilde.adjunction (R := R)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)))
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g))
    (pullbackTildeIso R S f).hom
  rw [conjugateEquiv_pullbackTildeIso_hom] at step2
  have step3 := conjugateEquiv_associator_hom (ModuleCat.extendRestrictScalarsAdj f.hom)
    (tilde.adjunction (R := S)) (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g))
  have step4 := conjugateEquiv_whiskerLeft
    ((ModuleCat.extendRestrictScalarsAdj g.hom).comp (tilde.adjunction (R := T)))
    ((tilde.adjunction (R := S)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g)))
    (ModuleCat.extendRestrictScalarsAdj f.hom) (pullbackTildeIso S T g).hom
  rw [conjugateEquiv_pullbackTildeIso_hom] at step4
  have step5 := conjugateEquiv_iso_inv (conjugateEquiv_associator_hom
    (ModuleCat.extendRestrictScalarsAdj f.hom) (ModuleCat.extendRestrictScalarsAdj g.hom)
    (tilde.adjunction (R := T)))
  have step6 := conjugateEquiv_whiskerRight
    (ModuleCat.extendRestrictScalarsAdj (f ≫ g).hom)
    ((ModuleCat.extendRestrictScalarsAdj f.hom).comp
      (ModuleCat.extendRestrictScalarsAdj g.hom))
    (tilde.adjunction (R := T)) (ModuleCat.extendScalarsComp f.hom g.hom).inv
  rw [conjugateEquiv_extendScalarsComp_inv] at step6
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom]
  rw [pushforwardΓIso_inv_comp R S T f g, ← step6, ← step5, ← step4, ← step3, ← step2,
    ← step1, ← step0, conjugateEquiv_comp, conjugateEquiv_comp, conjugateEquiv_comp,
    conjugateEquiv_comp, conjugateEquiv_comp, conjugateEquiv_comp]
  simp only [Category.assoc]

/-- The affine pullback comparison at an identity ring homomorphism is the canonical
identification: the pullback along `Spec (𝟙 R)` is the identity functor and extension of scalars
along the identity of `R` is the identity functor. -/
public theorem pullbackTildeIso_id (R : CommRingCat.{u}) :
    pullbackTildeIso R R (𝟙 R) =
      Functor.isoWhiskerLeft (tilde.functor R) (pullbackSpecMapIdIso R) ≪≫
        (tilde.functor R).rightUnitor ≪≫ (tilde.functor R).leftUnitor.symm ≪≫
        Functor.isoWhiskerRight (ModuleCat.extendScalarsId R).symm (tilde.functor R) := by
  refine (eq_pullbackTildeIso_of_conjugateEquiv R R (𝟙 R) _ ?_).symm
  have step0 := conjugateEquiv_whiskerLeft Adjunction.id
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (𝟙 R)))
    (tilde.adjunction (R := R)) (pullbackSpecMapIdIso R).hom
  rw [conjugateEquiv_pullbackSpecMapIdIso_hom] at step0
  have step1 := conjugateEquiv_rightUnitor_hom (tilde.adjunction (R := R))
  have step2 := conjugateEquiv_iso_inv
    (t := (Functor.rightUnitor (moduleSpecΓFunctor (R := R))).symm)
    (conjugateEquiv_leftUnitor_hom (tilde.adjunction (R := R)))
  rw [Iso.symm_inv] at step2
  have step3 := conjugateEquiv_whiskerRight
    (ModuleCat.extendRestrictScalarsAdj (CommRingCat.Hom.hom (𝟙 R))) Adjunction.id
    (tilde.adjunction (R := R)) (ModuleCat.extendScalarsId R).inv
  rw [conjugateEquiv_extendScalarsId_inv] at step3
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom]
  rw [pushforwardΓIso_inv_id R, ← step3, ← step2, ← step1, ← step0,
    conjugateEquiv_comp, conjugateEquiv_comp, conjugateEquiv_comp]
  simp only [Category.assoc]

end AlgebraicGeometry
