module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackKernelMorphism

/-!
# Automorphisms of an object of `Coh_{X/Y}` over the identity of its test scheme

A morphism `m : A ⟶ A` of `Coh_{X/Y}` whose base is the identity of the test scheme `T` of `A`
is the same as an automorphism of the module `ℱ` of `A`: its module comparison
`(X_{𝟙})^*ℱ ⟶ ℱ` read through the identity law of Stacks 03LU. This file records how these
module automorphisms compose, how they restrict along a morphism `σ` of `Coh_{X/Y}` fixed by
them, and how they are carried along a morphism `m : A ⟶ A` commuting with them.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.autOf`: the module automorphism of a module
  comparison over the identity.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.autOf_comp`.
* `AlgebraicGeometry.Space.CoherentSituation.map_autOf_comp_of_eq`.
* `AlgebraicGeometry.Space.CoherentSituation.fibre_comp_autOf_of_eq`.

## Implementation notes

The base of a morphism over the identity is equal to the identity but is not the identity as an
expression, so every statement takes the base as a variable together with an equation to the
identity, and the module comparisons as variables related by the comparisons of Stacks 03LU;
the proofs substitute the equations away before computing.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

namespace CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : CoherentSituation B S hS)

/-- The identity law along the identity itself. -/
theorem idAppOf_refl (T : SchemesOver D.Y)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) :
    D.idAppOf (𝟙 T) rfl F = D.idApp T F :=
  rfl

/-- The identity law of Stacks 03LU is natural. -/
@[reassoc]
theorem map_idApp {T : SchemesOver D.Y}
    {F F' : Modules.{u, u} B S hS (D.space T).1 (D.space T).2} (φ : F ⟶ F') :
    (modulePullback B S hS (D.relativeMap (𝟙 T))).map φ ≫ D.idApp T F' = D.idApp T F ≫ φ :=
  (D.idComparison (modulePushforwardCoherence B S hS) T).hom.naturality φ

/-- The comparison for a composite whose first factor is an identity, followed by the identity
law, is the identification of the inverse images along `𝟙 ≫ h = h`. -/
theorem compComparison_id_comp_idApp {T T' : SchemesOver D.Y} (h : T ⟶ T')
    (F : Modules.{u, u} B S hS (D.space T').1 (D.space T').2) :
    (D.compComparison (𝟙 T) h).hom.app F ≫
        D.idApp T ((modulePullback B S hS (D.relativeMap h)).obj F) =
      eqToHom (congrArg (fun g => (modulePullback B S hS (D.relativeMap g)).obj F)
        (Category.id_comp h)) := by
  have e := congrArg (fun i => i.hom.app F)
    (idComparison_comp_fac (modulePushforwardCoherence B S hS) D h)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at e
  refine (Category.comp_id _).symm.trans ((Category.assoc _ _ _).trans (e.trans ?_))
  simp [CoherentSituation.relativeMapComparison]

/-- The comparison of Stacks 03LU at any equation `X_{𝟙} ≫ X_g = X_k`, followed by the identity
law, is the identification of the inverse images along `X_k = X_g`. -/
theorem modulePullbackTriangle_id_comp_idApp {T T' : SchemesOver D.Y} (g k : T ⟶ T')
    (hih : D.relativeMap (𝟙 T) ≫ D.relativeMap g = D.relativeMap k)
    (hkg : D.relativeMap k = D.relativeMap g)
    (F : Modules.{u, u} B S hS (D.space T').1 (D.space T').2) :
    (modulePullbackTriangle B S hS hih).hom.app F ≫
        D.idApp T ((modulePullback B S hS (D.relativeMap g)).obj F) =
      eqToHom (congrArg (fun φ => (modulePullback B S hS φ).obj F) hkg) := by
  have hk : D.relativeMap (𝟙 T) ≫ D.relativeMap g = D.relativeMap (𝟙 T ≫ g) :=
    (baseChangeMap_comp D.f (𝟙 T) g).symm
  have hkk : D.relativeMap k = D.relativeMap (𝟙 T ≫ g) :=
    hkg.trans (congrArg (fun g' => D.relativeMap g') (Category.id_comp g).symm)
  rw [modulePullbackTriangle_congr hih hk hkk]
  have e1 : modulePullbackTriangle B S hS hk = D.compComparison (𝟙 T) g := rfl
  rw [e1, Iso.trans_hom, NatTrans.comp_app, Category.assoc, compComparison_id_comp_idApp]
  rw [eqToIso.hom, eqToHom_app, eqToHom_trans]

/-- The comparison of Stacks 03LU at any equation `X_g ≫ X_{𝟙} = X_k`, followed by the inverse
image of the identity law, is the identification of the inverse images along `X_k = X_g`. -/
theorem modulePullbackTriangle_comp_map_idApp {T T' : SchemesOver D.Y} (g k : T ⟶ T')
    (hih : D.relativeMap g ≫ D.relativeMap (𝟙 T') = D.relativeMap k)
    (hkg : D.relativeMap k = D.relativeMap g)
    (F : Modules.{u, u} B S hS (D.space T').1 (D.space T').2) :
    (modulePullbackTriangle B S hS hih).hom.app F ≫
        (modulePullback B S hS (D.relativeMap g)).map (D.idApp T' F) =
      eqToHom (congrArg (fun φ => (modulePullback B S hS φ).obj F) hkg) := by
  have hk : D.relativeMap g ≫ D.relativeMap (𝟙 T') = D.relativeMap (g ≫ 𝟙 T') :=
    (baseChangeMap_comp D.f g (𝟙 T')).symm
  have hkk : D.relativeMap k = D.relativeMap (g ≫ 𝟙 T') :=
    hkg.trans (congrArg (fun g' => D.relativeMap g') (Category.comp_id g).symm)
  rw [modulePullbackTriangle_congr hih hk hkk]
  have e1 : modulePullbackTriangle B S hS hk = D.compComparison g (𝟙 T') := rfl
  rw [e1, Iso.trans_hom, NatTrans.comp_app, Category.assoc, compComparison_comp_idApp]
  rw [eqToIso.hom, eqToHom_app, eqToHom_trans]

/-! ### The module automorphism of a morphism over the identity -/

/-- The module automorphism of a module comparison `(X_e)^*ℱ ⟶ ℱ` along an endomorphism `e` of
the test scheme equal to the identity. -/
def autOf {T : SchemesOver D.Y} (e : T ⟶ T) (he : e = 𝟙 T)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (θ : (modulePullback B S hS (D.relativeMap e)).obj F ⟶ F) : F ⟶ F :=
  inv (D.idAppOf e he F) ≫ θ

/-- The module automorphism `autOf e he F θ` of an isomorphism `θ` is an isomorphism. -/
instance {T : SchemesOver D.Y} (e : T ⟶ T) (he : e = 𝟙 T)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (θ : (modulePullback B S hS (D.relativeMap e)).obj F ⟶ F) [IsIso θ] :
    IsIso (D.autOf e he F θ) := by
  unfold autOf
  infer_instance

/-- The module automorphism of the identity law followed by `α` is `α`. -/
theorem autOf_refl_idApp {T : SchemesOver D.Y}
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) (α : F ⟶ F) :
    D.autOf (𝟙 T) rfl F (D.idApp T F ≫ α) = α :=
  IsIso.inv_hom_id_assoc (D.idApp T F) α

/-- Every module endomorphism of a module comparison over the identity is the identity law
followed by an endomorphism. -/
private theorem exists_idApp_comp_eq {T : SchemesOver D.Y}
    {F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2}
    (θ : (modulePullback B S hS (D.relativeMap (𝟙 T))).obj F ⟶ F) :
    ∃ α : F ⟶ F, θ = D.idApp T F ≫ α :=
  ⟨inv (D.idApp T F) ≫ θ, by simp⟩

/-- The comparison of Stacks 03LU at an equation `X_σ ≫ X_{𝟙} = X_σ`, followed by the inverse
image of the identity law, is the identity. -/
private theorem modulePullbackTriangle_comp_map_idApp_self {T₀ T : SchemesOver D.Y} (σ : T₀ ⟶ T)
    (hih : D.relativeMap σ ≫ D.relativeMap (𝟙 T) = D.relativeMap σ)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) :
    (modulePullbackTriangle B S hS hih).hom.app F ≫
        (modulePullback B S hS (D.relativeMap σ)).map (D.idApp T F) = 𝟙 _ := by
  exact (modulePullbackTriangle_comp_map_idApp D σ σ hih rfl F).trans (eqToHom_refl _ _)

/-- `AlgebraicGeometry.Space.CoherentSituation.autOf_comp` for module comparisons written
through the identity law. -/
theorem autOf_comp_aux {T : SchemesOver D.Y}
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) (α₁ α₂ : F ⟶ F)
    (θ₃ : (modulePullback B S hS (D.relativeMap (𝟙 T))).obj F ⟶ F)
    (hih : D.relativeMap (𝟙 T) ≫ D.relativeMap (𝟙 T) = D.relativeMap (𝟙 T))
    (hθ : θ₃ = (modulePullbackTriangle B S hS hih).hom.app F ≫
      (modulePullback B S hS (D.relativeMap (𝟙 T))).map (D.idApp T F ≫ α₂) ≫
        D.idApp T F ≫ α₁) :
    D.autOf (𝟙 T) rfl F θ₃ = D.autOf (𝟙 T) rfl F (D.idApp T F ≫ α₂) ≫
      D.autOf (𝟙 T) rfl F (D.idApp T F ≫ α₁) := by
  have e := D.modulePullbackTriangle_comp_map_idApp_self (𝟙 T) hih F
  have hθ' : θ₃ = D.idApp T F ≫ α₂ ≫ α₁ := by
    rw [hθ, Functor.map_comp, Category.assoc, ← Category.assoc
      ((modulePullbackTriangle B S hS hih).hom.app F), e, Category.id_comp, map_idApp_assoc]
  rw [hθ', autOf_refl_idApp, autOf_refl_idApp, autOf_refl_idApp]

/-- `AlgebraicGeometry.Space.CoherentSituation.autOf_comp` over the identity itself. -/
theorem autOf_comp_refl {T : SchemesOver D.Y}
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (θ₁ θ₂ θ₃ : (modulePullback B S hS (D.relativeMap (𝟙 T))).obj F ⟶ F)
    (hih : D.relativeMap (𝟙 T) ≫ D.relativeMap (𝟙 T) = D.relativeMap (𝟙 T))
    (hθ : θ₃ = (modulePullbackTriangle B S hS hih).hom.app F ≫
      (modulePullback B S hS (D.relativeMap (𝟙 T))).map θ₂ ≫ θ₁) :
    D.autOf (𝟙 T) rfl F θ₃ = D.autOf (𝟙 T) rfl F θ₂ ≫ D.autOf (𝟙 T) rfl F θ₁ := by
  obtain ⟨α₂, rfl⟩ := D.exists_idApp_comp_eq θ₂
  obtain ⟨α₁, rfl⟩ := D.exists_idApp_comp_eq θ₁
  exact D.autOf_comp_aux F α₁ α₂ θ₃ hih hθ

/-- **Module automorphisms compose**, in the opposite order, along a comparison of Stacks 03LU
for the composite. -/
theorem autOf_comp {T : SchemesOver D.Y} (e₁ e₂ e₃ : T ⟶ T) (h₁ : e₁ = 𝟙 T) (h₂ : e₂ = 𝟙 T)
    (h₃ : e₃ = 𝟙 T) (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (θ₁ : (modulePullback B S hS (D.relativeMap e₁)).obj F ⟶ F)
    (θ₂ : (modulePullback B S hS (D.relativeMap e₂)).obj F ⟶ F)
    (θ₃ : (modulePullback B S hS (D.relativeMap e₃)).obj F ⟶ F)
    (hih : D.relativeMap e₁ ≫ D.relativeMap e₂ = D.relativeMap e₃)
    (hθ : θ₃ = (modulePullbackTriangle B S hS hih).hom.app F ≫
      (modulePullback B S hS (D.relativeMap e₁)).map θ₂ ≫ θ₁) :
    D.autOf e₃ h₃ F θ₃ = D.autOf e₂ h₂ F θ₂ ≫ D.autOf e₁ h₁ F θ₁ := by
  subst h₁ h₂ h₃
  exact D.autOf_comp_refl F θ₁ θ₂ θ₃ hih hθ

/-- `AlgebraicGeometry.Space.CoherentSituation.map_autOf_comp_of_eq` for a module comparison
written through the identity law. -/
theorem map_autOf_comp_of_eq_aux {T₀ T : SchemesOver D.Y} (σ : T₀ ⟶ T)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    {G : Modules.{u, u} B S hS (D.space T₀).1 (D.space T₀).2}
    (ψ : (modulePullback B S hS (D.relativeMap σ)).obj F ⟶ G) (α : F ⟶ F)
    (hih : D.relativeMap σ ≫ D.relativeMap (𝟙 T) = D.relativeMap σ)
    (hψ : ψ = (modulePullbackTriangle B S hS hih).hom.app F ≫
      (modulePullback B S hS (D.relativeMap σ)).map (D.idApp T F ≫ α) ≫ ψ) :
    (modulePullback B S hS (D.relativeMap σ)).map (D.autOf (𝟙 T) rfl F (D.idApp T F ≫ α)) ≫ ψ =
      ψ := by
  have e := D.modulePullbackTriangle_comp_map_idApp_self σ hih F
  rw [autOf_refl_idApp]
  conv_rhs => rw [hψ, Functor.map_comp, Category.assoc, ← Category.assoc
    ((modulePullbackTriangle B S hS hih).hom.app F), e, Category.id_comp]

/-- `AlgebraicGeometry.Space.CoherentSituation.map_autOf_comp_of_eq` over the identity itself. -/
theorem map_autOf_comp_of_eq_refl {T₀ T : SchemesOver D.Y} (σ : T₀ ⟶ T)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    {G : Modules.{u, u} B S hS (D.space T₀).1 (D.space T₀).2}
    (ψ : (modulePullback B S hS (D.relativeMap σ)).obj F ⟶ G)
    (θ : (modulePullback B S hS (D.relativeMap (𝟙 T))).obj F ⟶ F)
    (hih : D.relativeMap σ ≫ D.relativeMap (𝟙 T) = D.relativeMap σ)
    (hψ : ψ = (modulePullbackTriangle B S hS hih).hom.app F ≫
      (modulePullback B S hS (D.relativeMap σ)).map θ ≫ ψ) :
    (modulePullback B S hS (D.relativeMap σ)).map (D.autOf (𝟙 T) rfl F θ) ≫ ψ = ψ := by
  obtain ⟨α, rfl⟩ := D.exists_idApp_comp_eq θ
  exact D.map_autOf_comp_of_eq_aux σ F ψ α hih hψ

/-- **A module automorphism fixing a module comparison along `σ`** acts trivially along `σ`. -/
theorem map_autOf_comp_of_eq {T₀ T : SchemesOver D.Y} (σ : T₀ ⟶ T) (e : T ⟶ T)
    (he : e = 𝟙 T) (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    {G : Modules.{u, u} B S hS (D.space T₀).1 (D.space T₀).2}
    (ψ : (modulePullback B S hS (D.relativeMap σ)).obj F ⟶ G)
    (θ : (modulePullback B S hS (D.relativeMap e)).obj F ⟶ F)
    (hih : D.relativeMap σ ≫ D.relativeMap e = D.relativeMap σ)
    (hψ : ψ = (modulePullbackTriangle B S hS hih).hom.app F ≫
      (modulePullback B S hS (D.relativeMap σ)).map θ ≫ ψ) :
    (modulePullback B S hS (D.relativeMap σ)).map (D.autOf e he F θ) ≫ ψ = ψ := by
  subst he
  exact D.map_autOf_comp_of_eq_refl σ F ψ θ hih hψ

/-- `AlgebraicGeometry.Space.CoherentSituation.fibre_comp_autOf_of_eq` for module comparisons
written through the identity law. -/
theorem fibre_comp_autOf_of_eq_aux {T : SchemesOver D.Y} (g k : T ⟶ T)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) (αa αb : F ⟶ F)
    (θm : (modulePullback B S hS (D.relativeMap g)).obj F ⟶ F)
    (hih₁ : D.relativeMap (𝟙 T) ≫ D.relativeMap g = D.relativeMap k)
    (hih₂ : D.relativeMap g ≫ D.relativeMap (𝟙 T) = D.relativeMap k)
    (h : (modulePullbackTriangle B S hS hih₁).hom.app F ≫
        (modulePullback B S hS (D.relativeMap (𝟙 T))).map θm ≫ D.idApp T F ≫ αb =
      (modulePullbackTriangle B S hS hih₂).hom.app F ≫
        (modulePullback B S hS (D.relativeMap g)).map (D.idApp T F ≫ αa) ≫ θm) :
    θm ≫ D.autOf (𝟙 T) rfl F (D.idApp T F ≫ αb) =
      (modulePullback B S hS (D.relativeMap g)).map (D.autOf (𝟙 T) rfl F (D.idApp T F ≫ αa)) ≫
        θm := by
  have hkg : D.relativeMap k = D.relativeMap g :=
    hih₂.symm.trans ((congrArg (D.relativeMap g ≫ ·) (baseChangeMap_id D.f T)).trans
      (Category.comp_id _))
  have e₁ := modulePullbackTriangle_id_comp_idApp D g k hih₁ hkg F
  have e₂ := modulePullbackTriangle_comp_map_idApp D g k hih₂ hkg F
  rw [map_idApp_assoc, ← Category.assoc ((modulePullbackTriangle B S hS hih₁).hom.app F), e₁,
    Functor.map_comp, Category.assoc, ← Category.assoc
      ((modulePullbackTriangle B S hS hih₂).hom.app F), e₂] at h
  rw [autOf_refl_idApp, autOf_refl_idApp]
  exact (cancel_epi _).1 h

/-- `AlgebraicGeometry.Space.CoherentSituation.fibre_comp_autOf_of_eq` over the identity
itself. -/
theorem fibre_comp_autOf_of_eq_refl {T : SchemesOver D.Y} (g k : T ⟶ T)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (θa θb : (modulePullback B S hS (D.relativeMap (𝟙 T))).obj F ⟶ F)
    (θm : (modulePullback B S hS (D.relativeMap g)).obj F ⟶ F)
    (hih₁ : D.relativeMap (𝟙 T) ≫ D.relativeMap g = D.relativeMap k)
    (hih₂ : D.relativeMap g ≫ D.relativeMap (𝟙 T) = D.relativeMap k)
    (h : (modulePullbackTriangle B S hS hih₁).hom.app F ≫
        (modulePullback B S hS (D.relativeMap (𝟙 T))).map θm ≫ θb =
      (modulePullbackTriangle B S hS hih₂).hom.app F ≫
        (modulePullback B S hS (D.relativeMap g)).map θa ≫ θm) :
    θm ≫ D.autOf (𝟙 T) rfl F θb =
      (modulePullback B S hS (D.relativeMap g)).map (D.autOf (𝟙 T) rfl F θa) ≫ θm := by
  obtain ⟨αa, rfl⟩ := D.exists_idApp_comp_eq θa
  obtain ⟨αb, rfl⟩ := D.exists_idApp_comp_eq θb
  exact D.fibre_comp_autOf_of_eq_aux g k F αa αb θm hih₁ hih₂ h

/-- **A module comparison commuting with two module automorphisms carries one to the other**: if
`b ≫ m = m ≫ a` with `a`, `b` over the identity and `m` over `g`, the module comparisons satisfy
`θ_m ≫ α_b = g^* α_a ≫ θ_m`. -/
theorem fibre_comp_autOf_of_eq {T : SchemesOver D.Y} (g k ea eb : T ⟶ T) (ha : ea = 𝟙 T)
    (hb : eb = 𝟙 T) (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (θa : (modulePullback B S hS (D.relativeMap ea)).obj F ⟶ F)
    (θb : (modulePullback B S hS (D.relativeMap eb)).obj F ⟶ F)
    (θm : (modulePullback B S hS (D.relativeMap g)).obj F ⟶ F)
    (hih₁ : D.relativeMap eb ≫ D.relativeMap g = D.relativeMap k)
    (hih₂ : D.relativeMap g ≫ D.relativeMap ea = D.relativeMap k)
    (h : (modulePullbackTriangle B S hS hih₁).hom.app F ≫
        (modulePullback B S hS (D.relativeMap eb)).map θm ≫ θb =
      (modulePullbackTriangle B S hS hih₂).hom.app F ≫
        (modulePullback B S hS (D.relativeMap g)).map θa ≫ θm) :
    θm ≫ D.autOf eb hb F θb =
      (modulePullback B S hS (D.relativeMap g)).map (D.autOf ea ha F θa) ≫ θm := by
  subst ha hb
  exact D.fibre_comp_autOf_of_eq_refl g k F θa θb θm hih₁ hih₂ h

/-- **A module automorphism determines its module comparison.** -/
theorem eq_of_autOf_eq {T : SchemesOver D.Y} (e : T ⟶ T) (he : e = 𝟙 T)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (θ θ' : (modulePullback B S hS (D.relativeMap e)).obj F ⟶ F)
    (h : D.autOf e he F θ = D.autOf e he F θ') : θ = θ' :=
  (cancel_epi (inv (D.idAppOf e he F))).1 h

/-- **A morphism of `Coh_{X/Y}` over the identity is determined by its module automorphism.** -/
theorem _root_.AlgebraicGeometry.Space.CoherentHom.eq_of_autOf_eq {A : CoherentObject D}
    (m n : CoherentHom A A) (hm : m.base = 𝟙 A.T) (hn : n.base = 𝟙 A.T)
    (h : D.autOf m.base hm A.F m.fibre = D.autOf n.base hn A.F n.fibre) : m = n := by
  obtain ⟨mb, mf, mi⟩ := m
  obtain ⟨nb, nf, ni⟩ := n
  change mb = 𝟙 _ at hm
  change nb = 𝟙 _ at hn
  subst hm hn
  have h' : mf = nf := D.eq_of_autOf_eq (𝟙 A.T) rfl A.F mf nf h
  subst h'
  rfl

end CoherentSituation

end AlgebraicGeometry.Space

end
