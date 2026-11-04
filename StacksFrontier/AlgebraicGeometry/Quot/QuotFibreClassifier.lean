module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotFibreHomFunctor

/-!
# Maps out of `F_T`, pulled back along the morphisms of `Coh_{X/B}`

The fibre of `Quot_{F/X/B} ⟶ Coh_{X/B}` over an object of `Coh_{X/B}` is computed through the
maps `F_T ⟶ 𝒢` out of the base change of `F` into the module of an object `(T, 𝒢)` of
`Coh_{X/B}`.  Such maps pull back along a morphism `(h, α) : (T', 𝒢') ⟶ (T, 𝒢)` of `Coh_{X/B}`:
`F_{T'} ≅ (X_h)^* F_T ⟶ (X_h)^* 𝒢 ≅ 𝒢'`.  This file proves that the pullback is functorial, and
that pulling back the projection `F_T ⟶ F_T/K` of a quotient along the morphism of `Coh_{X/B}`
attached to a morphism of test schemes gives the projection of the pulled-back quotient.

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.pullMapOf`: the pullback of a map `F_T ⟶ 𝒢` along a
  morphism of test schemes and a module comparison, the two components of a morphism of
  `Coh_{X/B}`.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.pullMapOf_comp`: the pullback along a composite is the
  iterated pullback.
* `AlgebraicGeometry.Space.QuotSituation.homOfPullMap_pullMapOf_of_factorization`: reading a
  pulled-back map as a homomorphism of inverse images
  (`AlgebraicGeometry.Space.QuotSituation.homOfPullMap`) is natural.
* `AlgebraicGeometry.Space.QuotSituation.pullMapOf_quotientFibreIso_quotientProjection`: the
  pullback of the projection onto a quotient along the comparison attached to a morphism of test
  schemes is the projection onto the pulled-back quotient.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local implicit_reducible] AlgebraicGeometry.Space.QuotSituation.toCoherentSituation

namespace CategoryTheory.Functor

variable {C : Type*} {D₀ : Type*} {D₁ : Type*} {D₂ : Type*} [Category* C] [Category* D₀]
  [Category* D₁] [Category* D₂]

/-- The naturality of reading maps `P₁ X ⟶ M` as maps `L₁ (P₀ X) ⟶ L₁ G` through comparisons
`P₁ ≅ P₀ ⋙ L₁` and `L₁ G ≅ M`, for abstract functors: pulling back along `L₂` and a comparison
factoring through `τ : L ≅ L₁ ⋙ L₂` conjugates by `τ`. -/
theorem conj_pull_of_eq_compWhisker {P₀ : C ⥤ D₀} {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L₁ : D₀ ⥤ D₁}
    {L₂ : D₁ ⥤ D₂} {L : D₀ ⥤ D₂} (c₁ : P₁ ≅ P₀ ⋙ L₁) (c₂ : P₂ ≅ P₁ ⋙ L₂) (c : P₂ ≅ P₀ ⋙ L)
    (τ : L ≅ L₁ ⋙ L₂)
    (hfac : c = (c₂ ≪≫ isoWhiskerRight c₁ L₂ ≪≫ associator P₀ L₁ L₂) ≪≫
      (isoWhiskerLeft P₀ τ).symm) (X : C) {G : D₀} {M₁ : D₁} {M₂ : D₂}
    (ψ : L₁.obj G ≅ M₁) (α : L₂.obj M₁ ≅ M₂) (v : P₁.obj X ⟶ M₁) :
    c.inv.app X ≫ (c₂.hom.app X ≫ L₂.map v ≫ α.hom) ≫
        (τ.app G ≪≫ L₂.mapIso ψ ≪≫ α).inv =
      τ.hom.app (P₀.obj X) ≫ L₂.map (c₁.inv.app X ≫ v ≫ ψ.inv) ≫ τ.inv.app G := by
  subst hfac
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, isoWhiskerLeft_hom,
    whiskerLeft_app, associator_inv_app, isoWhiskerRight_inv, whiskerRight_app,
    Iso.app_inv, mapIso_inv, Category.assoc, Category.id_comp, Functor.map_comp,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id_app_assoc]

/-- The characterization of a conjugated homomorphism through comparisons, for abstract
functors: if `u` corresponds to `v` through `c₁` and `ψ`, then its conjugate by `τ` corresponds to
the pullback of `v` along `c₂` and `α` through `c` and the composite identification `ψ'`. -/
theorem conj_char_of_formulas {P₀ : C ⥤ D₀} {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L₁ : D₀ ⥤ D₁}
    {L₂ : D₁ ⥤ D₂} {L : D₀ ⥤ D₂} (c₁ : P₁ ≅ P₀ ⋙ L₁) (c₂ : P₂ ≅ P₁ ⋙ L₂) (c : P₂ ≅ P₀ ⋙ L)
    (τ : L ≅ L₁ ⋙ L₂) (X : C) {G : D₀} {M₁ : D₁} {M₂ : D₂}
    (ψ : L₁.obj G ⟶ M₁) (α : L₂.obj M₁ ⟶ M₂) (ψ' : L.obj G ⟶ M₂)
    (hc : c.hom.app X = c₂.hom.app X ≫ L₂.map (c₁.hom.app X) ≫ τ.inv.app (P₀.obj X))
    (hψ' : ψ' = fibreComp τ α ψ) (u : L₁.obj (P₀.obj X) ⟶ L₁.obj G) (v : P₁.obj X ⟶ M₁)
    (hu : c₁.hom.app X ≫ u ≫ ψ = v) :
    c.hom.app X ≫ (τ.hom.app (P₀.obj X) ≫ L₂.map u ≫ τ.inv.app G) ≫ ψ' =
      c₂.hom.app X ≫ L₂.map v ≫ α := by
  subst hu hψ'
  rw [hc]
  unfold fibreComp
  simp

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space.QuotSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : QuotSituation B S hS)

/-- **The pullback of a map `F_T ⟶ 𝒢` along a morphism `h : T' ⟶ T` of test schemes and a
comparison `α : (X_h)^* 𝒢 ⟶ 𝒢'`**: `F_{T'} ≅ (X_h)^* F_T ⟶ (X_h)^* 𝒢 ⟶ 𝒢'`. -/
def pullMapOf {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    {M : Modules.{u, u} B S hS (D.space T).1 (D.space T).2}
    {M' : Modules.{u, u} B S hS (D.space T').1 (D.space T').2}
    (α : (modulePullback B S hS (D.relativeMap h)).obj M ⟶ M')
    (v : D.baseChangeModule T ⟶ M) : D.baseChangeModule T' ⟶ M' :=
  (D.baseChangeComparison h).hom.app D.F ≫ (modulePullback B S hS (D.relativeMap h)).map v ≫ α

/-- The pullback of `v` along `h` and `α` is `F_{T'} ≅ (X_h)^* F_T ⟶ (X_h)^* 𝒢 ⟶ 𝒢'`. -/
theorem pullMapOf_def {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    {M : Modules.{u, u} B S hS (D.space T).1 (D.space T).2}
    {M' : Modules.{u, u} B S hS (D.space T').1 (D.space T').2}
    (α : (modulePullback B S hS (D.relativeMap h)).obj M ⟶ M')
    (v : D.baseChangeModule T ⟶ M) :
    D.pullMapOf h α v =
      (D.baseChangeComparison h).hom.app D.F ≫ (modulePullback B S hS (D.relativeMap h)).map v ≫
        α :=
  rfl

/-- **The pullback along a composite is the iterated pullback**, for an abstract comparison `τ`
of the iterated inverse images through which the base-change comparison of the composite
factors. -/
theorem pullMapOf_comp_of_factorization {T₂ T₁ T₀ : SchemesOver D.Y} (h : T₂ ⟶ T₁)
    (k : T₁ ⟶ T₀)
    (τ : modulePullback B S hS (D.relativeMap (h ≫ k)) ≅
      modulePullback B S hS (D.relativeMap k) ⋙ modulePullback B S hS (D.relativeMap h))
    (hτ : D.baseChangeComparison (h ≫ k) =
      (D.baseChangeComparison h ≪≫
          Functor.isoWhiskerRight (D.baseChangeComparison k)
            (modulePullback B S hS (D.relativeMap h)) ≪≫
          Functor.associator (modulePullback B S hS (D.sourceProjection T₀))
            (modulePullback B S hS (D.relativeMap k))
            (modulePullback B S hS (D.relativeMap h))) ≪≫
        (Functor.isoWhiskerLeft (modulePullback B S hS (D.sourceProjection T₀)) τ).symm)
    {M₀ : Modules.{u, u} B S hS (D.space T₀).1 (D.space T₀).2}
    {M₁ : Modules.{u, u} B S hS (D.space T₁).1 (D.space T₁).2}
    {M₂ : Modules.{u, u} B S hS (D.space T₂).1 (D.space T₂).2}
    (α : (modulePullback B S hS (D.relativeMap h)).obj M₁ ⟶ M₂)
    (β : (modulePullback B S hS (D.relativeMap k)).obj M₀ ⟶ M₁)
    (v : D.baseChangeModule T₀ ⟶ M₀) :
    D.pullMapOf (h ≫ k) (Functor.fibreComp τ α β) v =
      D.pullMapOf h α (D.pullMapOf k β v) := by
  have hn := D.comparison_inv_naturality h k τ v
  have hc := Functor.hom_app_of_eq_compWhisker _ _ _ τ hτ D.F
  rw [pullMapOf_def, pullMapOf_def, pullMapOf_def, hc, Functor.fibreComp]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn]
  simp only [Iso.inv_hom_id_app_assoc]

/-- **The pullback along a composite is the iterated pullback**, the comparison of the composite
being built from the two comparisons by the composition comparison of Stacks 03LU. -/
theorem pullMapOf_comp {T₂ T₁ T₀ : SchemesOver D.Y} (h : T₂ ⟶ T₁) (k : T₁ ⟶ T₀)
    {M₀ : Modules.{u, u} B S hS (D.space T₀).1 (D.space T₀).2}
    {M₁ : Modules.{u, u} B S hS (D.space T₁).1 (D.space T₁).2}
    {M₂ : Modules.{u, u} B S hS (D.space T₂).1 (D.space T₂).2}
    (α : (modulePullback B S hS (D.relativeMap h)).obj M₁ ⟶ M₂)
    (β : (modulePullback B S hS (D.relativeMap k)).obj M₀ ⟶ M₁)
    (v : D.baseChangeModule T₀ ⟶ M₀) :
    D.pullMapOf (h ≫ k) (Functor.fibreComp
        (D.toCoherentSituation.compComparison h k) α β) v =
      D.pullMapOf h α (D.pullMapOf k β v) :=
  D.pullMapOf_comp_of_factorization h k (D.toCoherentSituation.compComparison h k)
    (D.baseChangeComparison_comp_compComparison (modulePushforwardCoherence B S hS) h k) α β v

/-- **Pulling back the projection onto a quotient along the module comparison attached to a
morphism of test schemes gives the projection onto the pulled-back quotient**, for any
identification of the pulled-back kernel. -/
theorem pullMapOf_quotientFibreIso_quotientProjection {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    {K : Subobject (D.baseChangeModule T)} {K' : Subobject (D.baseChangeModule T')}
    (hK : D.quotientPullback h K = K') :
    D.pullMapOf h (D.quotientFibreIso h K K' hK).inv (D.quotientProjection T K) =
      D.quotientProjection T' K' := by
  rw [pullMapOf_def, ← Category.assoc, Iso.comp_inv_eq, D.quotientFibreIso_hom]
  subst hK
  rw [eqToHom_refl, Category.id_comp]
  exact (D.quotientProjection_comp_quotientPullbackCokernelIso_hom h K).symm

/-- **A map `F_{T'} ⟶ 𝒢'` read as a homomorphism of inverse images along `h : T' ⟶ T`**, through
an identification `ψ : (X_h)^* 𝒢 ≅ 𝒢'`: `(X_h)^* F_T ≅ F_{T'} ⟶ 𝒢' ≅ (X_h)^* 𝒢`.  This is how a
map out of `F_{T'}` becomes a section of the relative Hom functor of
`AlgebraicGeometry.Space.QuotSituation.fibreHomFunctor`. -/
def homOfPullMap {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    {G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2}
    {M : Modules.{u, u} B S hS (D.space T').1 (D.space T').2}
    (ψ : (modulePullback B S hS (D.relativeMap h)).obj G ≅ M)
    (v : D.baseChangeModule T' ⟶ M) :
    (modulePullback B S hS (D.relativeMap h)).obj (D.baseChangeModule T) ⟶
      (modulePullback B S hS (D.relativeMap h)).obj G :=
  (D.baseChangeComparison h).inv.app D.F ≫ v ≫ ψ.inv

/-- The homomorphism attached to `v` through `ψ` is `(X_h)^* F_T ≅ F_{T'} ⟶ 𝒢' ≅ (X_h)^* 𝒢`. -/
theorem homOfPullMap_def {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    {G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2}
    {M : Modules.{u, u} B S hS (D.space T').1 (D.space T').2}
    (ψ : (modulePullback B S hS (D.relativeMap h)).obj G ≅ M)
    (v : D.baseChangeModule T' ⟶ M) :
    D.homOfPullMap h ψ v = (D.baseChangeComparison h).inv.app D.F ≫ v ≫ ψ.inv :=
  rfl

/-- **Reading pulled-back maps as homomorphisms of inverse images is natural**, for an abstract
comparison `τ` of the iterated inverse images through which the base-change comparison of the
composite factors: the homomorphism attached to the pullback of `v` along `(k, α)`, through the
composite identification, is the conjugate by `τ` of the inverse image along `k` of the
homomorphism attached to `v`.  Both sides are written out
(`AlgebraicGeometry.Space.QuotSituation.homOfPullMap_def`,
`AlgebraicGeometry.Space.QuotSituation.pullMapOf_def`), which is the form in which the kernel
checks the instantiation of `CategoryTheory.Functor.conj_pull_of_eq_compWhisker`. -/
theorem homOfPullMap_pullMapOf_of_factorization {T₂ T₁ T₀ : SchemesOver D.Y} (k : T₂ ⟶ T₁)
    (h : T₁ ⟶ T₀)
    (τ : modulePullback B S hS (D.relativeMap (k ≫ h)) ≅
      modulePullback B S hS (D.relativeMap h) ⋙ modulePullback B S hS (D.relativeMap k))
    (hτ : D.baseChangeComparison (k ≫ h) =
      (D.baseChangeComparison k ≪≫
          Functor.isoWhiskerRight (D.baseChangeComparison h)
            (modulePullback B S hS (D.relativeMap k)) ≪≫
          Functor.associator (modulePullback B S hS (D.sourceProjection T₀))
            (modulePullback B S hS (D.relativeMap h))
            (modulePullback B S hS (D.relativeMap k))) ≪≫
        (Functor.isoWhiskerLeft (modulePullback B S hS (D.sourceProjection T₀)) τ).symm)
    {G : Modules.{u, u} B S hS (D.space T₀).1 (D.space T₀).2}
    {M₁ : Modules.{u, u} B S hS (D.space T₁).1 (D.space T₁).2}
    {M₂ : Modules.{u, u} B S hS (D.space T₂).1 (D.space T₂).2}
    (ψ : (modulePullback B S hS (D.relativeMap h)).obj G ≅ M₁)
    (α : (modulePullback B S hS (D.relativeMap k)).obj M₁ ≅ M₂)
    (v : D.baseChangeModule T₁ ⟶ M₁) :
    (D.baseChangeComparison (k ≫ h)).inv.app D.F ≫
        ((D.baseChangeComparison k).hom.app D.F ≫
          (modulePullback B S hS (D.relativeMap k)).map v ≫ α.hom) ≫
        (τ.app G ≪≫ (modulePullback B S hS (D.relativeMap k)).mapIso ψ ≪≫ α).inv =
      τ.hom.app ((modulePullback B S hS (D.sourceProjection T₀)).obj D.F) ≫
        (modulePullback B S hS (D.relativeMap k)).map
          ((D.baseChangeComparison h).inv.app D.F ≫ v ≫ ψ.inv) ≫ τ.inv.app G :=
  Functor.conj_pull_of_eq_compWhisker (D.baseChangeComparison h)
    (D.baseChangeComparison k) (D.baseChangeComparison (k ≫ h)) τ hτ D.F ψ α v

/-- The module comparison of a morphism of `Coh_{X/B}`, as an isomorphism. -/
def cohFibreIso {E' E : CoherentObject D.toCoherentSituation} (e : CoherentHom E' E) :
    (modulePullback B S hS (D.relativeMap e.base)).obj E.F ≅ E'.F :=
  @asIso _ _ _ _ e.fibre e.isIso_fibre

/-- The forward map of `cohFibreIso e` is the module comparison of `e`. -/
theorem cohFibreIso_hom {E' E : CoherentObject D.toCoherentSituation} (e : CoherentHom E' E) :
    (D.cohFibreIso e).hom = e.fibre :=
  rfl

/-- The map out of `F_{E'.T}` attached through `a ≫ e` to the conjugate of a homomorphism `u`
is the pullback along `a` of the map attached to `u` through `e`. -/
theorem pullMapOf_conj_comp {E' E A : CoherentObject D.toCoherentSituation}
    (a : CoherentHom E' E) (e : CoherentHom E A)
    (u : (modulePullback B S hS (D.relativeMap e.base)).obj
        ((modulePullback B S hS (D.sourceProjection A.T)).obj D.F) ⟶
      (modulePullback B S hS (D.relativeMap e.base)).obj A.F)
    (v : D.baseChangeModule E.T ⟶ E.F)
    (hu : (D.baseChangeComparison e.base).hom.app D.F ≫ u ≫ e.fibre = v) :
    (D.baseChangeComparison (a.base ≫ e.base)).hom.app D.F ≫
        ((D.toCoherentSituation.compComparison a.base e.base).hom.app
            ((modulePullback B S hS (D.sourceProjection A.T)).obj D.F) ≫
          (modulePullback B S hS (D.relativeMap a.base)).map u ≫
          (D.toCoherentSituation.compComparison a.base e.base).inv.app A.F) ≫
        (CoherentHom.comp a e).fibre =
      (D.baseChangeComparison a.base).hom.app D.F ≫
        (modulePullback B S hS (D.relativeMap a.base)).map v ≫ a.fibre :=
  Functor.conj_char_of_formulas (D.baseChangeComparison e.base)
    (D.baseChangeComparison a.base) (D.baseChangeComparison (a.base ≫ e.base))
    (D.toCoherentSituation.compComparison a.base e.base) D.F e.fibre a.fibre
    (CoherentHom.comp a e).fibre
    (Functor.hom_app_of_eq_compWhisker (D.baseChangeComparison e.base)
      (D.baseChangeComparison a.base) (D.baseChangeComparison (a.base ≫ e.base))
      (D.toCoherentSituation.compComparison a.base e.base)
      (D.baseChangeComparison_comp_compComparison (modulePushforwardCoherence B S hS)
        a.base e.base) D.F)
    (CoherentHom.comp_fibre a e) u v hu

/-- The homomorphism attached to a map `v` gives `v` back. -/
theorem homOfPullMap_spec {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    {G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2}
    {M : Modules.{u, u} B S hS (D.space T').1 (D.space T').2}
    (ψ : (modulePullback B S hS (D.relativeMap h)).obj G ≅ M)
    (v : D.baseChangeModule T' ⟶ M) :
    (D.baseChangeComparison h).hom.app D.F ≫ D.homOfPullMap h ψ v ≫ ψ.hom = v := by
  rw [homOfPullMap_def]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_app_assoc]

/-- The homomorphism attached to a map `v` is the only one giving `v` back. -/
theorem homOfPullMap_unique {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    {G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2}
    {M : Modules.{u, u} B S hS (D.space T').1 (D.space T').2}
    (ψ : (modulePullback B S hS (D.relativeMap h)).obj G ≅ M)
    (v : D.baseChangeModule T' ⟶ M)
    (w : (modulePullback B S hS (D.relativeMap h)).obj
        ((modulePullback B S hS (D.sourceProjection T)).obj D.F) ⟶
      (modulePullback B S hS (D.relativeMap h)).obj G)
    (hw : (D.baseChangeComparison h).hom.app D.F ≫ w ≫ ψ.hom = v) :
    w = D.homOfPullMap h ψ v := by
  rw [homOfPullMap_def, ← hw]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_app_assoc]

/-- **Reading pulled-back maps as homomorphisms of inverse images is natural, along morphisms of
`Coh_{X/B}`.**  The conjugate, by the composition comparison of Stacks 03LU, of the homomorphism
attached to `v` through `e` is the homomorphism attached through `a ≫ e` to the pullback of `v`
along `a`.  It is proved through the characterization
`AlgebraicGeometry.Space.QuotSituation.homOfPullMap_unique`, so that no inverse of a comparison of
`Coh_{X/B}` is computed. -/
theorem homOfPullMap_comp_eq {E' E A : CoherentObject D.toCoherentSituation}
    (a : CoherentHom E' E) (e : CoherentHom E A) (v : D.baseChangeModule E.T ⟶ E.F) :
    (D.toCoherentSituation.compComparison a.base e.base).hom.app
          ((modulePullback B S hS (D.sourceProjection A.T)).obj D.F) ≫
        (modulePullback B S hS (D.relativeMap a.base)).map
          (D.homOfPullMap e.base (D.cohFibreIso e) v) ≫
        (D.toCoherentSituation.compComparison a.base e.base).inv.app A.F =
      D.homOfPullMap (a.base ≫ e.base) (D.cohFibreIso (CoherentHom.comp a e))
        (D.pullMapOf a.base a.fibre v) :=
  D.homOfPullMap_unique (a.base ≫ e.base) (D.cohFibreIso (CoherentHom.comp a e))
    (D.pullMapOf a.base a.fibre v) _
    (D.pullMapOf_conj_comp a e (D.homOfPullMap e.base (D.cohFibreIso e) v) v
      (D.homOfPullMap_spec e.base (D.cohFibreIso e) v))

end AlgebraicGeometry.Space.QuotSituation

end
