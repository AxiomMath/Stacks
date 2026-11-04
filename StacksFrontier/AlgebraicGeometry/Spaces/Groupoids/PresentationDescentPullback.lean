module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.Canonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.CanonicalFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.CanonicalPaste
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RelationHomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PresentationSchemeDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedSpaceMapCompSpelling

/-!
# Descent data and inverse images along a morphism of presentations

Let `f : Y ⟶ X` be a morphism of algebraic spaces, `φ : U ⟶ X`, `φ' : U' ⟶ Y` coverings with
relations `t, s : R ⟶ U` and `t', s' : R' ⟶ U'`, and `fU : U' ⟶ U`, `ρ : R' ⟶ R` lying over `f`.
The canonical descent datum of `f^*D` on `U'` is computed from that of `D` on `U`: it is carried,
by `φ'^*f^*D ≅ fU^*φ^*D`, to the pullback along `ρ` of the descent datum of `D`.  For represented
relations, the pullback of a scheme transition `τ` along a morphism of relations is
`AlgebraicGeometry.Space.schemeTransitionPullback`, read through the identifications
`g^*(M^a) ≅ (g^*M)^a` of Stacks 03DX by the lemmas of the last section.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A transport along an equality of the first morphism, absorbed into the canonical
comparison. -/
theorem eqToIso_trans_canonicalComparison {A P Q R : AlgebraicSpaces B S hS} {a a' : P ⟶ Q}
    (b : P ⟶ R) (fi : Q ⟶ A) (fj : R ⟶ A) (e : a = a') (h' : a' ≫ fi = b ≫ fj)
    (M : Modules.{u, u} B S hS A.1 A.2) :
    eqToIso (congrArg (fun q : P ⟶ Q => (modulePullback B S hS q).obj
        ((modulePullback B S hS fi).obj M)) e) ≪≫ canonicalComparison a' b fi fj h' M =
      canonicalComparison a b fi fj (e ▸ h') M := by
  subst e
  simp

/-- The canonical comparison between the inverse images along two equal morphisms is the
transport along their equality. -/
theorem canonicalComparison_self {A P Q : AlgebraicSpaces B S hS} {a b : P ⟶ Q} (fi : Q ⟶ A)
    (e : a = b) (h : a ≫ fi = b ≫ fi) (M : Modules.{u, u} B S hS A.1 A.2) :
    canonicalComparison a b fi fi h M = eqToIso (congrArg (fun q : P ⟶ Q =>
        (modulePullback B S hS q).obj ((modulePullback B S hS fi).obj M)) e) := by
  subst e
  rw [canonicalComparison]
  simp

/-- The canonical comparison unfolded into the comparisons of iterated inverse images. -/
theorem canonicalComparison_def {A P Q R : AlgebraicSpaces B S hS} (a : P ⟶ Q) (b : P ⟶ R)
    (fi : Q ⟶ A) (fj : R ⟶ A) (h : a ≫ fi = b ≫ fj) (M : Modules.{u, u} B S hS A.1 A.2) :
    canonicalComparison a b fi fj h M =
      (pullbackComparison B S hS a fi (a ≫ fi) rfl M).symm ≪≫
        eqToIso (congrArg (fun q : P ⟶ A => (modulePullback B S hS q).obj M) h) ≪≫
        pullbackComparison B S hS b fj (b ≫ fj) rfl M := rfl

/-- `pair_coherence`, solved for the inverse image of the canonical comparison. -/
theorem mapIso_canonicalComparison {A P Q R T : AlgebraicSpaces B S hS} (v : T ⟶ P) (a : P ⟶ Q)
    (b : P ⟶ R) (fi : Q ⟶ A) (fj : R ⟶ A) (h : a ≫ fi = b ≫ fj)
    (M : Modules.{u, u} B S hS A.1 A.2) :
    (modulePullback B S hS v).mapIso (canonicalComparison a b fi fj h M) =
      (pullbackComparison B S hS v a (v ≫ a) rfl ((modulePullback B S hS fi).obj M)).symm ≪≫
        canonicalComparison (v ≫ a) (v ≫ b) fi fj
          (by rw [Category.assoc, Category.assoc, h]) M ≪≫
        pullbackComparison B S hS v b (v ≫ b) rfl ((modulePullback B S hS fj).obj M) := by
  rw [← pair_coherence B S hS v a b fi fj h M]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id, Iso.trans_refl]

/-- **The canonical comparison along a pair over a square.**  The comparison `t'^*φ'^*f^*D ≅
s'^*φ'^*f^*D` factors through `fU^*φ^*D` and the comparison along `ρ ≫ t, ρ ≫ s`. -/
theorem canonicalComparison_eq_of_square {X Y U U' R R' : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (φ : U ⟶ X) (φ' : U' ⟶ Y) (fU : U' ⟶ U) (t s : R ⟶ U) (t' s' : R' ⟶ U')
    (ρ : R' ⟶ R) (hsq : φ' ≫ f = fU ≫ φ) (ht : t' ≫ fU = ρ ≫ t) (hs : ρ ≫ s = s' ≫ fU)
    (hw : t ≫ φ = s ≫ φ) (hw' : t' ≫ φ' = s' ≫ φ') (D : Modules.{u, u} B S hS X.1 X.2) :
    canonicalComparison t' s' φ' φ' hw' ((modulePullback B S hS f).obj D) =
      (modulePullback B S hS t').mapIso (canonicalComparison φ' fU f φ hsq D) ≪≫
        canonicalComparison t' ρ fU t ht ((modulePullback B S hS φ).obj D) ≪≫
        (modulePullbackCompIso B S hS ρ t).app ((modulePullback B S hS φ).obj D) ≪≫
        canonicalComparison (ρ ≫ t) (ρ ≫ s) φ φ (by rw [Category.assoc, Category.assoc, hw]) D ≪≫
        ((modulePullbackCompIso B S hS ρ s).app ((modulePullback B S hS φ).obj D)).symm ≪≫
        canonicalComparison ρ s' s fU hs ((modulePullback B S hS φ).obj D) ≪≫
        (modulePullback B S hS s').mapIso (canonicalComparison fU φ' φ f hsq.symm D) := by
  rw [mapIso_canonicalComparison, mapIso_canonicalComparison]
  rw [canonicalComparison_def t' ρ fU t ht, canonicalComparison_def ρ s' s fU hs]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, pullbackComparison_rfl, Iso.symm_symm_eq]
  have h1 := canonicalComparison_trans_eqToIso (t' ≫ φ') f φ
    (by rw [Category.assoc, Category.assoc, hsq]) ht D
  have h2 := eqToIso_trans_canonicalComparison (s' ≫ φ') φ f hs
    (by rw [Category.assoc, Category.assoc, hsq]) D
  rw [Iso.subst_trans₂ h1, Iso.subst_trans₂ h2,
    Iso.subst_trans₂ (canonicalComparison_trans B S hS (t' ≫ φ') (ρ ≫ t) (ρ ≫ s) f φ φ _ _ D),
    Iso.subst_trans₂ (canonicalComparison_trans B S hS (t' ≫ φ') (ρ ≫ s) (s' ≫ φ') f φ f _ _ D),
    canonicalComparison_self f hw', canonicalComparison_eq]

end AlgebraicGeometry.Space.QuasiCoherentDescent

namespace AlgebraicGeometry.Space

open QuasiCoherentDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Carrying transitions is closed under composition of the morphisms. -/
theorem TransitionCommutes.trans {U V : AlgebraicSpaces B S hS} {a b : V ⟶ U}
    {F G H : Modules.{u, u} B S hS U.1 U.2}
    {α : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F}
    {β : (modulePullback B S hS a).obj G ⟶ (modulePullback B S hS b).obj G}
    {γ : (modulePullback B S hS a).obj H ⟶ (modulePullback B S hS b).obj H}
    {f : F ⟶ G} {g : G ⟶ H} (hf : TransitionCommutes B S hS α β f)
    (hg : TransitionCommutes B S hS β γ g) : TransitionCommutes B S hS α γ (f ≫ g) := by
  unfold TransitionCommutes at hf hg ⊢
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, hf, Category.assoc, hg,
    Category.assoc]

/-- **The descent datum of an inverse image along a morphism of presentations.**  If `c`
carries the canonical descent datum of `D` to `β`, and `ε` carries the pullback of `β` along `ρ`
to `β'`, then `φ'^*f^*D ≅ fU^*φ^*D ≅ fU^*C ≅ C'` carries the canonical datum of `f^*D` to `β'`. -/
theorem transitionCommutes_canonicalComparison_of_square {X Y U U' R R' : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (φ : U ⟶ X) (φ' : U' ⟶ Y) (fU : U' ⟶ U) (t s : R ⟶ U) (t' s' : R' ⟶ U')
    (ρ : R' ⟶ R) (hsq : φ' ≫ f = fU ≫ φ) (ht : t' ≫ fU = ρ ≫ t) (hs : ρ ≫ s = s' ≫ fU)
    (hw : t ≫ φ = s ≫ φ) (hw' : t' ≫ φ' = s' ≫ φ') (D : Modules.{u, u} B S hS X.1 X.2)
    {C : Modules.{u, u} B S hS U.1 U.2} (c : (modulePullback B S hS φ).obj D ≅ C)
    (αX : (modulePullback B S hS t).obj ((modulePullback B S hS φ).obj D) ⟶
      (modulePullback B S hS s).obj ((modulePullback B S hS φ).obj D))
    (hα : (canonicalComparison (ρ ≫ t) (ρ ≫ s) φ φ
        (by rw [Category.assoc, Category.assoc, hw]) D).hom = modulePullbackReindex ρ αX)
    (β : (modulePullback B S hS t).obj C ⟶ (modulePullback B S hS s).obj C)
    (hcomm : TransitionCommutes B S hS αX β c.hom)
    {C' : Modules.{u, u} B S hS U'.1 U'.2} (ε : (modulePullback B S hS fU).obj C ≅ C')
    (β' : (modulePullback B S hS t').obj C' ⟶ (modulePullback B S hS s').obj C')
    (hC : TransitionCommutes B S hS ((canonicalComparison t' ρ fU t ht C).hom ≫
      (modulePullback B S hS ρ).map β ≫ (canonicalComparison ρ s' s fU hs C).hom) β' ε.hom) :
    TransitionCommutes B S hS
      (canonicalComparison t' s' φ' φ' hw' ((modulePullback B S hS f).obj D)).hom β'
      ((canonicalComparison φ' fU f φ hsq D).hom ≫ (modulePullback B S hS fU).map c.hom ≫
        ε.hom) := by
  have hA := congrArg Iso.hom
    (canonicalComparison_eq_of_square f φ φ' fU t s t' s' ρ hsq ht hs hw hw' D)
  have hinv : (canonicalComparison fU φ' φ f hsq.symm D).hom =
      (canonicalComparison φ' fU f φ hsq D).inv := by
    have h := congrArg Iso.hom
      (canonicalComparison_trans B S hS φ' fU φ' f φ f hsq hsq.symm D)
    rw [canonicalComparison_self f rfl, Iso.trans_hom, eqToIso_refl, Iso.refl_hom] at h
    exact (Iso.inv_ext h).symm
  have hnt := canonicalComparison_naturality B S hS t' ρ fU t ht c.hom
  have hns := canonicalComparison_naturality B S hS ρ s' s fU hs c.hom
  unfold TransitionCommutes at hcomm hC ⊢
  rw [hA]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, hinv,
    hα, modulePullbackReindex, Category.assoc, Functor.map_comp, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc (modulePullback B S hS s') (canonicalComparison φ' fU f φ hsq D).inv,
    (canonicalComparison φ' fU f φ hsq D).inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [← reassoc_of% hns, ← Functor.map_comp_assoc, hcomm, Functor.map_comp_assoc,
    ← reassoc_of% hnt]
  simp only [Category.assoc] at hC
  rw [hC]

/-- An isomorphism carrying one transition to another carries the second back to the first by its
inverse. -/
theorem TransitionCommutes.inv {U V : AlgebraicSpaces B S hS} {a b : V ⟶ U}
    {F G : Modules.{u, u} B S hS U.1 U.2}
    {α : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F}
    {β : (modulePullback B S hS a).obj G ⟶ (modulePullback B S hS b).obj G}
    {e : Iso.{u + 1} F G} (h : TransitionCommutes B S hS α β e.hom) :
    TransitionCommutes B S hS β α e.inv := by
  unfold TransitionCommutes at h ⊢
  calc β ≫ (modulePullback B S hS b).map e.inv =
      (modulePullback B S hS a).map e.inv ≫ ((modulePullback B S hS a).map e.hom ≫ β) ≫
        (modulePullback B S hS b).map e.inv := by
        simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
          CategoryTheory.Functor.map_id, Category.id_comp]
    _ = (modulePullback B S hS a).map e.inv ≫ α := by
        rw [← h]
        simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
          CategoryTheory.Functor.map_id, Category.comp_id]

/-- **Gluing a morphism along an étale presentation from charts carrying the transitions.**  Let
`X = U/R` be an étale presentation with atlas `φ`, and `κ_M : φ^*M ⟶ C`, `κ_N : D ⟶ φ^*N` carry the
canonical descent datum of `M` to a transition `β_M` on `R`, and a transition `β_N` to that of `N`.
A morphism `θ : C ⟶ D` carrying `β_M` to `β_N` makes `κ_M ≫ θ ≫ κ_N` the inverse image of a unique
morphism `M ⟶ N`. -/
theorem Presentation.existsUnique_modulePullback_atlas_map_eq_of_transitionCommutes
    {X : AlgebraicSpaces B S hS} (P : Presentation B S hS X.1 X.2)
    {M N : Modules.{u, u} B S hS X.1 X.2}
    {C D : Modules.{u, u} B S hS (yoneda.obj P.U) (isAlgebraicSpace_yoneda B S hS P.U)}
    {βM : (modulePullback B S hS P.relationTarget).obj C ⟶
      (modulePullback B S hS P.relationSource).obj C}
    {βN : (modulePullback B S hS P.relationTarget).obj D ⟶
      (modulePullback B S hS P.relationSource).obj D}
    {κM : (modulePullback B S hS P.atlas).obj M ⟶ C}
    {κN : D ⟶ (modulePullback B S hS P.atlas).obj N}
    (hM : TransitionCommutes B S hS
      (canonicalComparison P.relationTarget P.relationSource P.atlas P.atlas
        P.relationTarget_comp_atlas M).hom βM κM)
    (hN : TransitionCommutes B S hS βN
      (canonicalComparison P.relationTarget P.relationSource P.atlas P.atlas
        P.relationTarget_comp_atlas N).hom κN)
    {θ : C ⟶ D} (hθ : TransitionCommutes B S hS βM βN θ) :
    ∃! χ : M ⟶ N, (modulePullback B S hS P.atlas).map χ = κM ≫ θ ≫ κN :=
  P.existsUnique_modulePullback_atlas_map_eq _ (hM.trans (hθ.trans hN)).symm

section Represented

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U R U' R' : BigFppfOver B S hS} (t s : R ⟶ U) (t' s' : R' ⟶ U') (fU : U' ⟶ U) (fR : R' ⟶ R)
  (ht : t' ≫ fU = fR ≫ t) (hs : fR ≫ s = s' ≫ fU)
  (M : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory)
  (τ : quasicoherentPullbackObj B S hS t M ⟶ quasicoherentPullbackObj B S hS s M)

/-- **The pullback of a scheme transition along a morphism of relations**: for `fU : U' ⟶ U` and
`fR : R' ⟶ R` over `t' ≫ fU = fR ≫ t` and `fR ≫ s = s' ≫ fU`, the transition
`t'^*(fU^*M) ⟶ s'^*(fU^*M)` read from the reindexing `fR^*τ` of `τ : t^*M ⟶ s^*M`. -/
def schemeTransitionPullback :
    quasicoherentPullbackObj B S hS t' (quasicoherentPullbackObj B S hS fU M) ⟶
      quasicoherentPullbackObj B S hS s' (quasicoherentPullbackObj B S hS fU M) :=
  (quasicoherentPullbackCompIso B S hS t' fU M).hom ≫
    eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M) ht) ≫
      schemeTransitionReindex B S hS t s M τ fR ≫
        eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M) hs) ≫
          (quasicoherentPullbackCompIso B S hS s' fU M).inv

/-- The canonical comparison written with the contractions of iterated inverse images. -/
theorem canonicalComparison_eq_compIso {A P Q R : AlgebraicSpaces B S hS} (a : P ⟶ Q)
    (b : P ⟶ R) (fi : Q ⟶ A) (fj : R ⟶ A) (h : a ≫ fi = b ≫ fj)
    (N : Modules.{u, u} B S hS A.1 A.2) :
    QuasiCoherentDescent.canonicalComparison a b fi fj h N =
      (modulePullbackCompIso B S hS a fi).app N ≪≫
        eqToIso (congrArg (fun q : P ⟶ A => (modulePullback B S hS q).obj N) h) ≪≫
        ((modulePullbackCompIso B S hS b fj).app N).symm := by
  rw [QuasiCoherentDescent.canonicalComparison_def, QuasiCoherentDescent.pullbackComparison_rfl,
    QuasiCoherentDescent.pullbackComparison_rfl, Iso.symm_symm_eq]

/-- The transport along an equality of morphisms is the transport of `eqToIso`. -/
theorem eqToIso_hom_eq_pullbackTransport {A P : AlgebraicSpaces B S hS} {f g : P ⟶ A} (h : f = g)
    (N : Modules.{u, u} B S hS A.1 A.2) :
    (eqToIso (congrArg (fun q : P ⟶ A => (modulePullback B S hS q).obj N) h)).hom =
      pullbackTransport N h := rfl

/-- The morphism underlying the composite of the contractions and the transport. -/
theorem canonicalComparison_compIso_hom_eq {A P Q R : AlgebraicSpaces B S hS} (a : P ⟶ Q)
    (b : P ⟶ R) (fi : Q ⟶ A) (fj : R ⟶ A) (h : a ≫ fi = b ≫ fj)
    (N : Modules.{u, u} B S hS A.1 A.2) :
    ((modulePullbackCompIso B S hS a fi).app N ≪≫
        eqToIso (congrArg (fun q : P ⟶ A => (modulePullback B S hS q).obj N) h) ≪≫
        ((modulePullbackCompIso B S hS b fj).app N).symm).hom =
      ((modulePullbackCompIso B S hS a fi).app N).hom ≫
        (eqToIso (congrArg (fun q : P ⟶ A => (modulePullback B S hS q).obj N) h)).hom ≫
        ((modulePullbackCompIso B S hS b fj).app N).inv := rfl

/-- `AlgebraicGeometry.Space.canonicalComparison_eq_compIso`, read on the morphisms. -/
theorem canonicalComparison_hom_eq_compIso {A P Q R : AlgebraicSpaces B S hS} (a : P ⟶ Q)
    (b : P ⟶ R) (fi : Q ⟶ A) (fj : R ⟶ A) (h : a ≫ fi = b ≫ fj)
    (N : Modules.{u, u} B S hS A.1 A.2) :
    (QuasiCoherentDescent.canonicalComparison a b fi fj h N).hom =
      ((modulePullbackCompIso B S hS a fi).app N).hom ≫ pullbackTransport N h ≫
        ((modulePullbackCompIso B S hS b fj).app N).inv :=
  (congrArg Iso.hom (canonicalComparison_eq_compIso B S hS a b fi fj h N)).trans
    ((canonicalComparison_compIso_hom_eq B S hS a b fi fj h N).trans
      (congrArg (fun x => ((modulePullbackCompIso B S hS a fi).app N).hom ≫ x ≫
        ((modulePullbackCompIso B S hS b fj).app N).inv)
        (eqToIso_hom_eq_pullbackTransport B S hS h N)))

/-- The module attached to a transport along an equality of quasi-coherent modules on a scheme
is the transport along the equality of the attached modules. -/
theorem representedQuasicoherentSchemeEquivalence_map_eqToHom_hom {V : BigFppfOver B S hS}
    {M M' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf).FullSubcategory} (p : M = M') :
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map (eqToHom p)).hom =
      eqToHom (congrArg (fun Z => ((representedQuasicoherentSchemeEquivalence B S hS V).functor.obj
        Z).obj) p) := by
  subst p
  rw [eqToHom_refl, eqToHom_refl, CategoryTheory.Functor.map_id]
  rfl

/-- The identification `g^*(M^a) ≅ (g^*M)^a` is compatible with transport along an equality
`g = g'`. -/
theorem pullbackTransport_modulePullbackRepresentedQuasicoherentIso_hom {V U : BigFppfOver B S hS}
    {g g' : V ⟶ U} (e : g = g')
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    pullbackTransport _ (congrArg (representedSpaceMap B S hS) e) ≫
        (modulePullbackRepresentedQuasicoherentIso B S hS g' M).hom =
      (modulePullbackRepresentedQuasicoherentIso B S hS g M).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
          (eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M) e))).hom := by
  subst e
  simp only [pullbackTransport, eqToIso_refl, Iso.refl_hom, eqToHom_refl,
    CategoryTheory.Functor.map_id]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- Two composites of two transports along equalities of morphisms with the same ends agree. -/
theorem pullbackTransport_comp_eq {T Y : AlgebraicSpaces B S hS} (N : Modules.{u, u} B S hS Y.1 Y.2)
    {a b c d : T ⟶ Y} (h₁ : a = b) (h₂ : b = c) (h₃ : a = d) (h₄ : d = c) :
    pullbackTransport N h₁ ≫ pullbackTransport N h₂ =
      pullbackTransport N h₃ ≫ pullbackTransport N h₄ := by
  subst h₁ h₂ h₄
  simp [pullbackTransport]

/-- A composite of three transports along equalities of morphisms is the transport along the
composite equality. -/
theorem pullbackTransport_comp_comp {T Y : AlgebraicSpaces B S hS}
    (N : Modules.{u, u} B S hS Y.1 Y.2) {a b c d : T ⟶ Y} (h₁ : a = b) (h₂ : b = c) (h₃ : c = d)
    (h₄ : a = d) :
    pullbackTransport N h₁ ≫ pullbackTransport N h₂ ≫ pullbackTransport N h₃ =
      pullbackTransport N h₄ := by
  subst h₁ h₂ h₃
  simp [pullbackTransport]

/-- The transport along an equality of morphisms, as the component of the transport of the
inverse image functors. -/
theorem eqToIso_modulePullback_app_hom {T Y : AlgebraicSpaces B S hS} {a b : T ⟶ Y} (h : a = b)
    (N : Modules.{u, u} B S hS Y.1 Y.2) :
    ((eqToIso (congrArg (modulePullback B S hS) h)).app N).hom = pullbackTransport N h := by
  subst h
  rfl

/-- The module attached to an isomorphism of quasi-coherent modules on a scheme, composed with the
module attached to its inverse. -/
theorem representedQuasicoherentSchemeEquivalence_map_hom_inv {V : BigFppfOver B S hS}
    {N N' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf).FullSubcategory} (e : N ≅ N') :
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map e.hom).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map e.inv).hom = 𝟙 _ :=
  ((ObjectProperty.ι _).mapIso ((representedQuasicoherentSchemeEquivalence B S hS V).functor.mapIso
    e)).hom_inv_id

/-- The module attached to the inverse of an isomorphism of quasi-coherent modules on a scheme,
composed with the module attached to it. -/
theorem representedQuasicoherentSchemeEquivalence_map_inv_hom {V : BigFppfOver B S hS}
    {N N' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf).FullSubcategory} (e : N ≅ N') :
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map e.inv).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map e.hom).hom = 𝟙 _ :=
  ((ObjectProperty.ι _).mapIso ((representedQuasicoherentSchemeEquivalence B S hS V).functor.mapIso
    e)).inv_hom_id

private theorem comp_eq_of_readings {𝒞 : Type*} [Category 𝒞] {A₀ A₁ A₂ A₃ A₄ A₅ : 𝒞}
    {a : A₀ ⟶ A₁} {k : A₀ ⟶ A₅} {p : A₅ ⟶ A₁} {b : A₁ ⟶ A₂} {c : A₀ ⟶ A₃} {d : A₃ ⟶ A₄}
    {e : A₄ ⟶ A₂} {e' : A₂ ⟶ A₄} (ha : a = k ≫ p) (H : a ≫ b = c ≫ d ≫ e)
    (he : e ≫ e' = 𝟙 _) : c ≫ d = k ≫ p ≫ b ≫ e' := by
  rw [← Category.assoc k, ← ha, reassoc_of% H, he, Category.comp_id]

/-- `AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso_comp`, read on the
morphisms and solved for the identification along `h`. -/
theorem modulePullbackRepresentedQuasicoherentIso_comp_hom {W V U : BigFppfOver B S hS}
    (h : W ⟶ V) (g : V ⟶ U)
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    (modulePullback B S hS (representedSpaceMap B S hS h)).map
        (modulePullbackRepresentedQuasicoherentIso B S hS g M).hom ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS h
        (quasicoherentPullbackObj B S hS g M)).hom =
    ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h)
        (representedSpaceMap B S hS g)).app
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj).hom ≫
      pullbackTransport _ (representedSpaceMap_comp B S hS h g) ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS (h ≫ g) M).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS W).functor.map
        (quasicoherentPullbackCompIso B S hS h g M).inv).hom :=
  comp_eq_of_readings
    (congrArg (fun x => ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h)
        (representedSpaceMap B S hS g)).app
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj).hom ≫ x)
      (eqToIso_modulePullback_app_hom B S hS (representedSpaceMap_comp B S hS h g) _))
    (congrArg Iso.hom (modulePullbackRepresentedQuasicoherentIso_comp B S hS h g M))
    (representedQuasicoherentSchemeEquivalence_map_hom_inv B S hS
      (quasicoherentPullbackCompIso B S hS h g M))

/-- The module attached to `AlgebraicGeometry.Space.schemeTransitionPullback`, factor by
factor. -/
theorem representedQuasicoherentSchemeEquivalence_map_schemeTransitionPullback_hom :
    ((representedQuasicoherentSchemeEquivalence B S hS R').functor.map
        (schemeTransitionPullback B S hS t s t' s' fU fR ht hs M τ)).hom =
      ((representedQuasicoherentSchemeEquivalence B S hS R').functor.map
          (quasicoherentPullbackCompIso B S hS t' fU M).hom).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS R').functor.map
          (eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M) ht))).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS R').functor.map
          (schemeTransitionReindex B S hS t s M τ fR)).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS R').functor.map
          (eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M) hs))).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS R').functor.map
          (quasicoherentPullbackCompIso B S hS s' fU M).inv).hom := by
  simp only [schemeTransitionPullback, CategoryTheory.Functor.map_comp,
    ObjectProperty.FullSubcategory.comp_hom]

private theorem comp_comp_eq_of_readings {𝒞 : Type*} [Category 𝒞] {A₀ A₁ A₂ A₃ A₄ A₅ : 𝒞}
    {p₁ : A₀ ⟶ A₁} {p₂ : A₁ ⟶ A₂} {p₃ : A₀ ⟶ A₃} {p₄ : A₃ ⟶ A₂} {r : A₂ ⟶ A₄} {r' : A₃ ⟶ A₅}
    {e : A₅ ⟶ A₄} (htr : p₁ ≫ p₂ = p₃ ≫ p₄) (h : p₄ ≫ r = r' ≫ e) :
    p₁ ≫ p₂ ≫ r = p₃ ≫ r' ≫ e := by
  rw [← h, ← reassoc_of% htr]

/-- The two routes from `t'^*(fU^*(M^a))` to `((fR ≫ t)^*M)^a` along the target side. -/
theorem pullbackTransport_target_modulePullbackRepresentedQuasicoherentIso :
    pullbackTransport _ (representedSpaceMap_comp_eq_of_comp_eq B S hS ht) ≫
      pullbackTransport
        (f := CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (representedSpaceMap B S hS fR)
          (representedSpaceMap B S hS t)) _
        (representedSpaceMap_comp B S hS fR t) ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS (fR ≫ t) M).hom =
    pullbackTransport
      (f := CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (representedSpaceMap B S hS t')
        (representedSpaceMap B S hS fU)) _
        (representedSpaceMap_comp B S hS t' fU) ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS (t' ≫ fU) M).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS R').functor.map
        (eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M) ht))).hom :=
  comp_comp_eq_of_readings
    (pullbackTransport_comp_eq B S hS _ _ _ _ (congrArg (representedSpaceMap B S hS) ht))
    (pullbackTransport_modulePullbackRepresentedQuasicoherentIso_hom B S hS ht M)

private theorem inv_comp_eq_of_readings {𝒞 : Type*} [Category 𝒞] {A₀ A₁ A₂ A₃ A₄ A₅ : 𝒞}
    {ri : A₀ ⟶ A₁} {q : A₁ ⟶ A₂} {p : A₂ ⟶ A₃} {q' : A₃ ⟶ A₄} {P : A₁ ⟶ A₄} {r' : A₄ ⟶ A₅}
    {r : A₁ ⟶ A₀} {e : A₀ ⟶ A₅} (htr : q ≫ p ≫ q' = P) (h : P ≫ r' = r ≫ e)
    (hr : ri ≫ r = 𝟙 _) : ri ≫ q ≫ p ≫ q' ≫ r' = e := by
  have h' : q ≫ p ≫ q' ≫ r' = r ≫ e := by
    rw [← h, ← htr]
    simp only [Category.assoc]
  rw [h', ← Category.assoc, hr, Category.id_comp]

/-- The two routes from `((fR ≫ s)^*M)^a` to `((s' ≫ fU)^*M)^a` along the source side. -/
theorem modulePullbackRepresentedQuasicoherentIso_inv_source_pullbackTransport :
    (modulePullbackRepresentedQuasicoherentIso B S hS (fR ≫ s) M).inv ≫
      pullbackTransport
        (g := CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (representedSpaceMap B S hS fR)
          (representedSpaceMap B S hS s)) _
        (representedSpaceMap_comp B S hS fR s).symm ≫
      pullbackTransport _ (representedSpaceMap_comp_eq_of_comp_eq B S hS hs) ≫
      pullbackTransport
        (f := CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (representedSpaceMap B S hS s')
          (representedSpaceMap B S hS fU)) _
        (representedSpaceMap_comp B S hS s' fU) ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS (s' ≫ fU) M).hom =
    ((representedQuasicoherentSchemeEquivalence B S hS R').functor.map
      (eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M) hs))).hom :=
  inv_comp_eq_of_readings
    (pullbackTransport_comp_comp B S hS _ _ _ _ (congrArg (representedSpaceMap B S hS) hs))
    (pullbackTransport_modulePullbackRepresentedQuasicoherentIso_hom B S hS hs M)
    (modulePullbackRepresentedQuasicoherentIso B S hS (fR ≫ s) M).inv_hom_id

/-- `AlgebraicGeometry.Space.transitionReindex_representedSchemeTransition` with the transports
along the composites of represented morphisms taken in `AlgebraicSpaces`. -/
theorem transitionReindex_representedSchemeTransition_algebraicSpaces :
    transitionReindex B S hS (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
        (V := ⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩)
        (a := representedSpaceMap B S hS t) (b := representedSpaceMap B S hS s)
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
        (representedSchemeTransition B S hS t s M τ) (representedSpaceMap B S hS fR) =
      pullbackTransport
        (f := CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (representedSpaceMap B S hS fR)
          (representedSpaceMap B S hS t)) _
          (representedSpaceMap_comp B S hS fR t) ≫
        (modulePullbackRepresentedQuasicoherentIso B S hS (fR ≫ t) M).hom ≫
          ((representedQuasicoherentSchemeEquivalence B S hS R').functor.map
            (schemeTransitionReindex B S hS t s M τ fR)).hom ≫
            (modulePullbackRepresentedQuasicoherentIso B S hS (fR ≫ s) M).inv ≫
              pullbackTransport
                (g := CategoryStruct.comp (obj := AlgebraicSpaces B S hS)
                  (representedSpaceMap B S hS fR) (representedSpaceMap B S hS s)) _
                (representedSpaceMap_comp B S hS fR s).symm :=
  transitionReindex_representedSchemeTransition B S hS t s M τ fR

private theorem transitionCommutes_pullback_of_readings {𝒞 : Type*} [Category 𝒞]
    {A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 : 𝒞}
    {c₁ : A0 ⟶ A3} {X : A3 ⟶ A4} {c₂ : A4 ⟶ A7} {Ms : A7 ⟶ A8} {Mt : A0 ⟶ A13} {R : A13 ⟶ A8}
    {k₁ : A0 ⟶ A1} {p₁ : A1 ⟶ A2} {k₂ : A2 ⟶ A3} {l₁ : A4 ⟶ A5} {p₂ : A5 ⟶ A6} {l₂ : A6 ⟶ A7}
    {q₁ : A2 ⟶ A9} {ρt : A9 ⟶ A10} {Eσ : A10 ⟶ A11} {ρs : A11 ⟶ A12} {q₂ : A12 ⟶ A5}
    {ρt' : A13 ⟶ A14} {Eτ : A14 ⟶ A15} {ρs'i : A15 ⟶ A8} {ρs' : A8 ⟶ A15}
    {q₃ : A1 ⟶ A16} {ρtf : A16 ⟶ A17} {Ei₁ : A17 ⟶ A14} {Eh₁ : A14 ⟶ A17} {Eet : A17 ⟶ A10}
    {Ees : A11 ⟶ A18} {Ei₂ : A18 ⟶ A15} {m : A7 ⟶ A6} {q₄ : A6 ⟶ A19} {ρsf : A19 ⟶ A18}
    (hc₁ : c₁ = k₁ ≫ p₁ ≫ k₂) (hc₂ : c₂ = l₁ ≫ p₂ ≫ l₂)
    (hX : k₂ ≫ X ≫ l₁ = q₁ ≫ ρt ≫ Eσ ≫ ρs ≫ q₂) (hR : R = ρt' ≫ Eτ ≫ ρs'i)
    (h₄ : Mt ≫ ρt' = k₁ ≫ q₃ ≫ ρtf ≫ Ei₁) (h₅ : Ms ≫ ρs' = m ≫ q₄ ≫ ρsf ≫ Ei₂)
    (h₆ : Eτ = Eh₁ ≫ Eet ≫ Eσ ≫ Ees ≫ Ei₂) (h₇ : Ei₁ ≫ Eh₁ = 𝟙 _) (h₈ : l₂ ≫ m = 𝟙 _)
    (h₉ : ρs' ≫ ρs'i = 𝟙 _) (h₁₁ : p₁ ≫ q₁ ≫ ρt = q₃ ≫ ρtf ≫ Eet)
    (h₁₂ : ρs ≫ q₂ ≫ p₂ ≫ q₄ ≫ ρsf = Ees) :
    (c₁ ≫ X ≫ c₂) ≫ Ms = Mt ≫ R := by
  have h₅' : q₄ ≫ ρsf ≫ Ei₂ = l₂ ≫ Ms ≫ ρs' := by
    rw [h₅, reassoc_of% h₈]
  have key : ρs ≫ q₂ ≫ p₂ ≫ l₂ ≫ Ms = Ees ≫ Ei₂ ≫ ρs'i := by
    rw [← h₁₂]
    simp only [Category.assoc]
    rw [reassoc_of% h₅', h₉, Category.comp_id]
  rw [hc₁, hc₂, hR, h₆]
  simp only [Category.assoc]
  rw [reassoc_of% h₄, reassoc_of% h₇, reassoc_of% hX, reassoc_of% h₁₁, key]

private theorem transitionCommutes_of_readings {U V : AlgebraicSpaces B S hS} {a b : V ⟶ U}
    {F G : Modules.{u, u} B S hS U.1 U.2}
    {α : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F}
    {β : (modulePullback B S hS a).obj G ⟶ (modulePullback B S hS b).obj G} {f : F ⟶ G}
    {A1 A2 A3 A4 A5 A6 A9 A10 A11 A12 A14 A15 A16 A17 A18 A19 : Modules.{u, u} B S hS V.1 V.2}
    {c₁ : (modulePullback B S hS a).obj F ⟶ A3} {X : A3 ⟶ A4}
    {c₂ : A4 ⟶ (modulePullback B S hS b).obj F}
    {k₁ : (modulePullback B S hS a).obj F ⟶ A1} {p₁ : A1 ⟶ A2} {k₂ : A2 ⟶ A3} {l₁ : A4 ⟶ A5}
    {p₂ : A5 ⟶ A6} {l₂ : A6 ⟶ (modulePullback B S hS b).obj F}
    {q₁ : A2 ⟶ A9} {ρt : A9 ⟶ A10} {Eσ : A10 ⟶ A11} {ρs : A11 ⟶ A12} {q₂ : A12 ⟶ A5}
    {ρt' : (modulePullback B S hS a).obj G ⟶ A14} {Eτ : A14 ⟶ A15}
    {ρs'i : A15 ⟶ (modulePullback B S hS b).obj G} {ρs' : (modulePullback B S hS b).obj G ⟶ A15}
    {q₃ : A1 ⟶ A16} {ρtf : A16 ⟶ A17} {Ei₁ : A17 ⟶ A14} {Eh₁ : A14 ⟶ A17} {Eet : A17 ⟶ A10}
    {Ees : A11 ⟶ A18} {Ei₂ : A18 ⟶ A15} {m : (modulePullback B S hS b).obj F ⟶ A6}
    {q₄ : A6 ⟶ A19} {ρsf : A19 ⟶ A18}
    (hα : α = c₁ ≫ X ≫ c₂) (hc₁ : c₁ = k₁ ≫ p₁ ≫ k₂) (hc₂ : c₂ = l₁ ≫ p₂ ≫ l₂)
    (hX : k₂ ≫ X ≫ l₁ = q₁ ≫ ρt ≫ Eσ ≫ ρs ≫ q₂) (hR : β = ρt' ≫ Eτ ≫ ρs'i)
    (h₄ : (modulePullback B S hS a).map f ≫ ρt' = k₁ ≫ q₃ ≫ ρtf ≫ Ei₁)
    (h₅ : (modulePullback B S hS b).map f ≫ ρs' = m ≫ q₄ ≫ ρsf ≫ Ei₂)
    (h₆ : Eτ = Eh₁ ≫ Eet ≫ Eσ ≫ Ees ≫ Ei₂) (h₇ : Ei₁ ≫ Eh₁ = 𝟙 _) (h₈ : l₂ ≫ m = 𝟙 _)
    (h₉ : ρs' ≫ ρs'i = 𝟙 _) (h₁₁ : p₁ ≫ q₁ ≫ ρt = q₃ ≫ ρtf ≫ Eet)
    (h₁₂ : ρs ≫ q₂ ≫ p₂ ≫ q₄ ≫ ρsf = Ees) :
    TransitionCommutes B S hS α β f := by
  unfold TransitionCommutes
  rw [hα]
  exact transitionCommutes_pullback_of_readings hc₁ hc₂ hX hR h₄ h₅ h₆ h₇ h₈ h₉ h₁₁ h₁₂

/-- `AlgebraicGeometry.Space.representedSchemeTransition` unfolded. -/
theorem representedSchemeTransition_eq {U R : BigFppfOver B S hS} (t s : R ⟶ U)
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory)
    (τ : quasicoherentPullbackObj B S hS t M ⟶ quasicoherentPullbackObj B S hS s M) :
    representedSchemeTransition B S hS t s M τ =
      (modulePullbackRepresentedQuasicoherentIso B S hS t M).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map τ).hom ≫
          (modulePullbackRepresentedQuasicoherentIso B S hS s M).inv :=
  rfl

/-- **The pullback of a represented scheme transition along a morphism of relations.**  The
pullback along `fR` of `τ^a`, read between `t'^*(fU^*(M^a))` and `s'^*(fU^*(M^a))` by the canonical
comparisons, is carried by `fU^*(M^a) ≅ (fU^*M)^a` to the transition attached to
`AlgebraicGeometry.Space.schemeTransitionPullback`. -/
theorem transitionCommutes_representedSchemeTransition_pullback :
    TransitionCommutes B S hS
      ((canonicalComparison (representedSpaceMap B S hS t') (representedSpaceMap B S hS fR)
          (representedSpaceMap B S hS fU) (representedSpaceMap B S hS t)
          (representedSpaceMap_comp_eq_of_comp_eq B S hS ht)
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj).hom ≫
        (modulePullback B S hS (representedSpaceMap B S hS fR)).map
          (representedSchemeTransition B S hS t s M τ) ≫
        (canonicalComparison (representedSpaceMap B S hS fR) (representedSpaceMap B S hS s')
          (representedSpaceMap B S hS s) (representedSpaceMap B S hS fU)
          (representedSpaceMap_comp_eq_of_comp_eq B S hS hs)
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj).hom)
      (representedSchemeTransition B S hS t' s' (quasicoherentPullbackObj B S hS fU M)
        (schemeTransitionPullback B S hS t s t' s' fU fR ht hs M τ))
      (modulePullbackRepresentedQuasicoherentIso B S hS fU M).hom :=
  transitionCommutes_of_readings B S hS rfl
    (canonicalComparison_hom_eq_compIso B S hS _ _ _ _ _ _)
    (canonicalComparison_hom_eq_compIso B S hS _ _ _ _ _ _)
    (transitionReindex_representedSchemeTransition_algebraicSpaces B S hS t s fR M τ)
    (representedSchemeTransition_eq B S hS t' s' _ _)
    (modulePullbackRepresentedQuasicoherentIso_comp_hom B S hS t' fU M)
    (modulePullbackRepresentedQuasicoherentIso_comp_hom B S hS s' fU M)
    (representedQuasicoherentSchemeEquivalence_map_schemeTransitionPullback_hom B S hS t s
      t' s' fU fR ht hs M τ)
    (representedQuasicoherentSchemeEquivalence_map_inv_hom B S hS
      (quasicoherentPullbackCompIso B S hS t' fU M))
    ((modulePullbackCompIso B S hS (representedSpaceMap B S hS s')
      (representedSpaceMap B S hS fU)).app
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj).inv_hom_id
    (modulePullbackRepresentedQuasicoherentIso B S hS s'
      (quasicoherentPullbackObj B S hS fU M)).hom_inv_id
    (pullbackTransport_target_modulePullbackRepresentedQuasicoherentIso B S hS t t' fU fR ht M)
    (modulePullbackRepresentedQuasicoherentIso_inv_source_pullbackTransport B S hS s s' fU fR
      hs M)

end Represented

end AlgebraicGeometry.Space
