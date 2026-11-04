module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackCategory
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorPullback

/-!
# Morphisms of `Coh_{X/B}` pinned by presentations

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation and let `F` be an
`𝒪_X`-module.  For a morphism `h : T' ⟶ T` of test schemes over `B`, the comparison of
Stacks 03LU for the equality `X_h ≫ (X_T ⟶ X) = (X_{T'} ⟶ X)` identifies the base change
`F_{T'}` with the inverse image `(X_h)^*F_T`.  A morphism of `Coh_{X/B}` with base map `h` from an
object `(T', 𝒢')` to an object `(T, 𝒢)` has as module comparison a morphism
`φ : (X_h)^*𝒢 ⟶ 𝒢'`; when the modules are presented as quotients `p : F_T ⟶ 𝒢` and
`p' : F_{T'} ⟶ 𝒢'`, the comparison is *pinned* by the two presentations if it carries the inverse
image of `p`, read through `F_{T'} ≅ (X_h)^*F_T`, to `p'`.  Since the inverse image of an
epimorphism is one, a comparison is determined by the two presentations pinning it, and the
identities and composites of `Coh_{X/B}` are pinned exactly when the coherences of Stacks 03LU
say so.  This is the device by which the functor laws for morphisms into `Coh_{X/B}` defined from
quotients are proved, in particular for the morphism `Quot_{F/X/B} ⟶ Coh_{X/B}` of Stacks 0DP6.

## Main definitions

* `CategoryTheory.Functor.conjMap`: a morphism out of a value of a functor, read through a
  comparison of functors.
* `CategoryTheory.Functor.IsPinned`: a fibre morphism carries one morphism, read through a
  comparison, to another.
* `AlgebraicGeometry.Space.CoherentSituation.presentationComparison`: the comparison
  `F_{T'} ≅ (X_h)^*F_T`.

## Main results

* `CategoryTheory.Functor.IsPinned.eq`: a fibre morphism is determined by two morphisms pinning
  it, the first an epimorphism.
* `CategoryTheory.Functor.isPinned_hom_app_of_eq_rightUnitor` and
  `CategoryTheory.Functor.isPinned_fibreComp`: the unit and composition laws for pinned
  morphisms, for arbitrary functors.
* `AlgebraicGeometry.Space.CoherentSituation.presentationComparison_id` and
  `AlgebraicGeometry.Space.CoherentSituation.presentationComparison_comp`: the comparisons along
  an identity and a composite are given by the unit and associativity laws of Stacks 03LU.
* `AlgebraicGeometry.Space.CoherentSituation.mk_eq_mk_of_isPinned`,
  `AlgebraicGeometry.Space.CoherentSituation.isPinned_idComparison` and
  `AlgebraicGeometry.Space.CoherentSituation.isPinned_fibreComp`: two morphisms of `Coh_{X/B}`
  with the same base map and pinned module comparisons are equal, and the module comparisons of
  identities and composites are pinned.

## Implementation notes

The identities between comparisons of inverse images are proved for arbitrary functors and
isomorphisms of functors and then instantiated.  Proving them in place would ask the elaborator to
reduce composites of functors one of whose factors is the inverse image of `𝒪`-modules, which it
does by unfolding the inverse image — the nonterminating reduction recorded in the implementation
notes of `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCoherence.lean`.

## References

* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0DP6](https://stacks.math.columbia.edu/tag/0DP6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits


namespace CategoryTheory.Functor

variable {C D₀ D₁ D₂ : Type*} [Category* C] [Category* D₀] [Category* D₁] [Category* D₂]

/-- **A morphism out of a value of `P₁`, read through a comparison `e : P₂ ≅ P₁ ⋙ L`**: the
morphism `P₂ M ⟶ L Q` obtained by applying `L` to `π : P₁ M ⟶ Q` and precomposing with the
component of `e`.  For `π` the projection onto a quotient this is
`CategoryTheory.Functor.conjQuotientProjection`. -/
def conjMap {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L) {M : C} {Q : D₁}
    (π : P₁.obj M ⟶ Q) : P₂.obj M ⟶ L.obj Q :=
  e.hom.app M ≫ L.map π

/-- Reading the projection onto a quotient through a comparison is
`CategoryTheory.Functor.conjQuotientProjection`. -/
theorem conjMap_cokernel_π [Abelian D₁] {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂}
    (e : P₂ ≅ P₁ ⋙ L) {M : C} (K : Subobject (P₁.obj M)) :
    conjMap e (Limits.cokernel.π K.arrow) = conjQuotientProjection e K :=
  rfl

/-- A morphism read through a comparison is an epimorphism when it is one and the functor
preserves epimorphisms. -/
theorem epi_conjMap {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} [L.PreservesEpimorphisms]
    (e : P₂ ≅ P₁ ⋙ L) {M : C} {Q : D₁} (π : P₁.obj M ⟶ Q) [Epi π] : Epi (conjMap e π) := by
  unfold conjMap
  infer_instance

/-- **A fibre morphism is pinned by two morphisms.**  For a comparison `e : P₂ ≅ P₁ ⋙ L`, a
morphism `φ : L Q ⟶ Q'` is pinned by `π : P₁ M ⟶ Q` and `π' : P₂ M ⟶ Q'` when it carries `π`,
read through `e`, to `π'`.  This is the condition that determines the module comparison of a
morphism of a category of pairs of a test object and a module on the corresponding base change,
once the modules are presented as quotients. -/
def IsPinned {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L) {M : C} {Q : D₁}
    {Q' : D₂} (φ : L.obj Q ⟶ Q') (π : P₁.obj M ⟶ Q) (π' : P₂.obj M ⟶ Q') : Prop :=
  conjMap e π ≫ φ = π'

/-- **A fibre morphism is determined by two morphisms pinning it**, when the first is an
epimorphism and the functor preserves epimorphisms. -/
theorem IsPinned.eq {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} [L.PreservesEpimorphisms]
    {e : P₂ ≅ P₁ ⋙ L} {M : C} {Q : D₁} {Q' : D₂} {φ ψ : L.obj Q ⟶ Q'} {π : P₁.obj M ⟶ Q}
    [Epi π] {π' : P₂.obj M ⟶ Q'} (hφ : IsPinned e φ π π') (hψ : IsPinned e ψ π π') : φ = ψ := by
  have : Epi (conjMap e π) := epi_conjMap e π
  exact (cancel_epi (conjMap e π)).1 (hφ.trans hψ.symm)

/-- **The unit law for pinned morphisms.**  If a comparison `e : P ≅ P ⋙ L` is whiskering `P`
with the inverse of an isomorphism `δ : L ≅ 𝟭`, the components of `δ` are pinned by any morphism
and itself. -/
theorem isPinned_hom_app_of_eq_rightUnitor {P : C ⥤ D₁} {L : D₁ ⥤ D₁} (δ : L ≅ 𝟭 D₁)
    (e : P ≅ P ⋙ L) (hfac : e = (rightUnitor P).symm ≪≫ isoWhiskerLeft P δ.symm) {M : C}
    {Q : D₁} (π : P.obj M ⟶ Q) : IsPinned e (δ.hom.app Q) π π := by
  subst hfac
  simp [IsPinned, conjMap]

/-- **The composition law for pinned morphisms.**  Let `c₁ : P₁ ≅ P₀ ⋙ L₁`,
`c₂ : P₂ ≅ P₁ ⋙ L₂` and `c : P₂ ≅ P₀ ⋙ L` be comparisons and `τ : L ≅ L₁ ⋙ L₂` a comparison of
a functor with a composite, with `c` the composite of `c₂` and `c₁` read through `τ`.  If `φ₁` is
pinned by `π₀` and `π₁` and `φ₂` by `π₁` and `π₂`, the composite of the two fibre morphisms along
`τ` is pinned by `π₀` and `π₂`. -/
theorem isPinned_fibreComp {P₀ : C ⥤ D₀} {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂}
    {L₁ : D₀ ⥤ D₁} {L₂ : D₁ ⥤ D₂} {L : D₀ ⥤ D₂}
    {c₁ : P₁ ≅ P₀ ⋙ L₁} {c₂ : P₂ ≅ P₁ ⋙ L₂} {c : P₂ ≅ P₀ ⋙ L} (τ : L ≅ L₁ ⋙ L₂)
    (hfac : c = (c₂ ≪≫ isoWhiskerRight c₁ L₂ ≪≫ associator P₀ L₁ L₂) ≪≫
      (isoWhiskerLeft P₀ τ).symm)
    {M : C} {Q₀ : D₀} {Q₁ : D₁} {Q₂ : D₂} {π₀ : P₀.obj M ⟶ Q₀} {π₁ : P₁.obj M ⟶ Q₁}
    {π₂ : P₂.obj M ⟶ Q₂} {φ₁ : L₁.obj Q₀ ⟶ Q₁} {φ₂ : L₂.obj Q₁ ⟶ Q₂}
    (h₁ : IsPinned c₁ φ₁ π₀ π₁) (h₂ : IsPinned c₂ φ₂ π₁ π₂) :
    IsPinned c (fibreComp τ φ₂ φ₁) π₀ π₂ := by
  unfold IsPinned at h₁ h₂ ⊢
  subst hfac h₁ h₂
  have hn := τ.inv.naturality π₀
  simp only [Functor.comp_map] at hn
  simp only [conjMap, fibreComp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, whiskerRight_app, associator_hom_app, isoWhiskerLeft_inv,
    whiskerLeft_app, Category.id_comp, Category.assoc, Functor.map_comp]
  rw [reassoc_of% hn.symm, Iso.inv_hom_id_app_assoc]

end CategoryTheory.Functor

/-- The inverse of the isomorphism induced by an equality of objects is the isomorphism induced by
the reversed equality. -/
theorem CategoryTheory.eqToIso_symm_eq {C : Type*} [Category* C] {X Y : C} (p : X = Y) :
    (eqToIso p).symm = eqToIso p.symm :=
  rfl

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Morphisms of `Coh_{X/B}` pinned by presentations -/

namespace CoherentSituation

variable (D : CoherentSituation B S hS)

/-- The comparison `F_{T'} ≅ (X_h)^*F_T` of the base changes of an `𝒪_X`-module along a morphism
`h : T' ⟶ T` of test schemes, as an isomorphism of the two inverse-image functors: the comparison
of Stacks 03LU for the equality `X_h ≫ (X_T ⟶ X) = (X_{T'} ⟶ X)`. -/
def presentationComparison {T' T : SchemesOver D.Y} (h : T' ⟶ T) :
    modulePullback B S hS (baseChangeProjection D.f T') ≅
      modulePullback B S hS (baseChangeProjection D.f T) ⋙
        modulePullback B S hS (D.relativeMap h) :=
  modulePullbackTriangle B S hS (baseChangeMap_comp_projection D.f h)

/-- **The comparison along an identity is the unit law of Stacks 03LU**, read through the
comparison `(X_{𝟙 T})^* ≅ 𝟭` of `Coh_{X/B}`. -/
theorem presentationComparison_id (T : SchemesOver D.Y) :
    D.presentationComparison (𝟙 T) =
      (Functor.rightUnitor (modulePullback B S hS (baseChangeProjection D.f T))).symm ≪≫
        Functor.isoWhiskerLeft (modulePullback B S hS (baseChangeProjection D.f T))
          (D.idComparison (modulePushforwardCoherence B S hS) T).symm := by
  rw [presentationComparison,
    modulePullbackTriangle_congr_left (baseChangeMap_id D.f T)
      (baseChangeMap_comp_projection D.f (𝟙 T)) (Category.id_comp (baseChangeProjection D.f T)),
    (modulePushforwardCoherence B S hS).modulePullbackTriangle_id, idComparison,
    Iso.trans_symm, Functor.isoWhiskerLeft_trans, Iso.trans_assoc, eqToIso_symm_eq]

/-- **The comparison along a composite is the associativity law of Stacks 03LU**, read through
the comparison `(X_{h ≫ k})^* ≅ (X_k)^* ⋙ (X_h)^*` of `Coh_{X/B}`. -/
theorem presentationComparison_comp {T'' T' T : SchemesOver D.Y} (h : T'' ⟶ T') (k : T' ⟶ T) :
    D.presentationComparison (h ≫ k) =
      (D.presentationComparison h ≪≫
          Functor.isoWhiskerRight (D.presentationComparison k)
            (modulePullback B S hS (D.relativeMap h)) ≪≫
          Functor.associator (modulePullback B S hS (baseChangeProjection D.f T))
            (modulePullback B S hS (D.relativeMap k))
            (modulePullback B S hS (D.relativeMap h))) ≪≫
        (Functor.isoWhiskerLeft (modulePullback B S hS (baseChangeProjection D.f T))
          (D.compComparison h k)).symm := by
  calc D.presentationComparison (h ≫ k)
      = (D.presentationComparison (h ≫ k) ≪≫
            Functor.isoWhiskerLeft (modulePullback B S hS (baseChangeProjection D.f T))
              (D.compComparison h k)) ≪≫
          (Functor.isoWhiskerLeft (modulePullback B S hS (baseChangeProjection D.f T))
            (D.compComparison h k)).symm := by
        simp
    _ = _ := by
        rw [presentationComparison, presentationComparison, presentationComparison,
          compComparison, (modulePushforwardCoherence B S hS).modulePullbackTriangle_comp
            (baseChangeMap_comp D.f h k).symm (baseChangeMap_comp_projection D.f k)
            (baseChangeMap_comp_projection D.f h) (baseChangeMap_comp_projection D.f (h ≫ k))]

variable {D}

/-- **Two morphisms of `Coh_{X/B}` with the same base map are equal when their module comparisons
are pinned by the same presentations** `p : F_T ⟶ 𝒢` of the module of the target and
`p' : F_{T'} ⟶ 𝒢'` of the module of the source, for an `𝒪_X`-module `F`, with `p` an
epimorphism: the module comparisons then agree, the inverse image of an epimorphism being one by
the adjunction of Stacks 03LU. -/
theorem mk_eq_mk_of_isPinned (F : Modules.{u, u} B S hS D.X.1 D.X.2) {A' A : CoherentObject D}
    (h : A'.T ⟶ A.T) {φ ψ : (modulePullback B S hS (D.relativeMap h)).obj A.F ⟶ A'.F}
    (hφ : IsIso φ) (hψ : IsIso ψ)
    {p : (modulePullback B S hS (baseChangeProjection D.f A.T)).obj F ⟶ A.F} (hp : Epi p)
    {p' : (modulePullback B S hS (baseChangeProjection D.f A'.T)).obj F ⟶ A'.F}
    (hm : Functor.IsPinned (D.presentationComparison h) φ p p')
    (hn : Functor.IsPinned (D.presentationComparison h) ψ p p') :
    (CoherentHom.mk h φ hφ : CoherentHom A' A) = CoherentHom.mk h ψ hψ := by
  have := modulePullback_preservesEpimorphisms (D.relativeMap h)
  obtain rfl : φ = ψ := Functor.IsPinned.eq hm hn
  rfl

/-- **The unit law of Stacks 03LU is pinned by any presentation.** -/
theorem isPinned_idComparison (F : Modules.{u, u} B S hS D.X.1 D.X.2) (T : SchemesOver D.Y)
    {Q : Modules.{u, u} B S hS (D.space T).1 (D.space T).2}
    (p : (modulePullback B S hS (baseChangeProjection D.f T)).obj F ⟶ Q) :
    Functor.IsPinned (D.presentationComparison (𝟙 T))
      ((D.idComparison (modulePushforwardCoherence B S hS) T).hom.app Q) p p :=
  Functor.isPinned_hom_app_of_eq_rightUnitor
    (D.idComparison (modulePushforwardCoherence B S hS) T)
    (D.presentationComparison (𝟙 T)) (D.presentationComparison_id T) p

/-- **A composite of pinned module comparisons is pinned**, by the associativity coherence of
the comparisons of inverse images of Stacks 03LU. -/
theorem isPinned_fibreComp {F : Modules.{u, u} B S hS D.X.1 D.X.2}
    {T'' T' T : SchemesOver D.Y} {h : T'' ⟶ T'} {k : T' ⟶ T}
    {Q : Modules.{u, u} B S hS (D.space T).1 (D.space T).2}
    {Q' : Modules.{u, u} B S hS (D.space T').1 (D.space T').2}
    {Q'' : Modules.{u, u} B S hS (D.space T'').1 (D.space T'').2}
    {φ : (modulePullback B S hS (D.relativeMap h)).obj Q' ⟶ Q''}
    {ψ : (modulePullback B S hS (D.relativeMap k)).obj Q ⟶ Q'}
    {p : (modulePullback B S hS (baseChangeProjection D.f T)).obj F ⟶ Q}
    {p' : (modulePullback B S hS (baseChangeProjection D.f T')).obj F ⟶ Q'}
    {p'' : (modulePullback B S hS (baseChangeProjection D.f T'')).obj F ⟶ Q''}
    (hφ : Functor.IsPinned (D.presentationComparison h) φ p' p'')
    (hψ : Functor.IsPinned (D.presentationComparison k) ψ p p') :
    Functor.IsPinned (D.presentationComparison (h ≫ k))
      (Functor.fibreComp (D.compComparison h k) φ ψ) p p'' :=
  Functor.isPinned_fibreComp (D.compComparison h k) (D.presentationComparison_comp h k) hψ hφ

/-- The identity of `Coh_{X/B}` is the morphism whose base map is the identity and whose module
comparison is the unit law of Stacks 03LU. -/
theorem coherentHom_id_eq_mk (A : CoherentObject D) :
    CoherentHom.id (modulePushforwardCoherence B S hS) A =
      CoherentHom.mk (𝟙 A.T)
        ((D.idComparison (modulePushforwardCoherence B S hS) A.T).hom.app A.F)
        (Iso.isIso_hom ((D.idComparison (modulePushforwardCoherence B S hS) A.T).app A.F)) :=
  rfl

/-- The composite of two morphisms of `Coh_{X/B}` given by their components. -/
theorem coherentHom_mk_comp_mk {A'' A' A : CoherentObject D} (h : A''.T ⟶ A'.T)
    (k : A'.T ⟶ A.T) (φ : (modulePullback B S hS (D.relativeMap h)).obj A'.F ⟶ A''.F)
    (hφ : IsIso φ) (ψ : (modulePullback B S hS (D.relativeMap k)).obj A.F ⟶ A'.F)
    (hψ : IsIso ψ) (hc : IsIso (Functor.fibreComp (D.compComparison h k) φ ψ)) :
    (CoherentHom.mk h φ hφ : CoherentHom A'' A').comp (CoherentHom.mk k ψ hψ) =
      CoherentHom.mk (h ≫ k) (Functor.fibreComp (D.compComparison h k) φ ψ) hc :=
  rfl

end CoherentSituation

end AlgebraicGeometry.Space

end
