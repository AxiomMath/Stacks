module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.EtaleLevelInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LevelUnitStalkMathlibComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportRestrictScalarsComp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTowerSystem

/-!
# The levels of the inverse image of an ℓ-adic sheaf and the transitions

Let `g : X' ⟶ X` be a morphism of the big étale site `B` and `F = (Fₙ)` an ℓ-adic sheaf on `X`.
The identification `λₙ : g⁻¹ Fₙ ≅ (g⁻¹F)ₙ` of sheaves of `ℤ/ℓⁿ⁺¹`-modules on Mathlib's small étale
site of `X'` (`Stacks.EtaleCohomology.LAdicSheaf.etaleLevelInverseImageIso`) is compatible with the
transitions: `g⁻¹(Fₙ₊₁ → Fₙ)`, read through `g⁻¹ ∘ res ≅ res ∘ g⁻¹` and `λₙ`, is `λₙ₊₁` followed
by the transition of `g⁻¹F`
(`Stacks.EtaleCohomology.LAdicSheaf.etaleLevelInverseImageIso_transition`). This is the
`ℤ/ℓⁿ⁺¹`-form of `Stacks.EtaleCohomology.padicLevelInverseImageIso_transition`, the form in which
the levels of `i⁻¹ G` enter the twist `𝓗om(μ_{ℓⁿ⁺¹}, (i⁻¹ G)ₙ)` in the tower form of
cohomological purity of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

All the comparisons are mates of strict commutations of direct images, so the proof is by
adjunction: the adjoint of `λₙ` is the unit of the bounded sites followed by the comparison of
direct images (`AlgebraicGeometry.SmallEtale.sheafEquiv_map_unit_comp_pushforwardBaseChangeIso`),
and the comparison of direct images commutes with restriction of scalars
(`Stacks.EtaleCohomology.sheafEquivRestrictScalarsIso_inv_comp_pushforwardBaseChangeIso`), which is
checked after reading it back on the bounded site.

## Main results

* `AlgebraicGeometry.SmallEtale.sheafEquiv_unit_comp_inverse_map_pushforwardBaseChangeIso_hom`.
* `Stacks.EtaleCohomology.sheafEquivRestrictScalarsIso_inv_comp_pushforwardBaseChangeIso`.
* `Stacks.EtaleCohomology.LAdicSheaf.etaleLevelInverseImageIso_transition`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.InverseSystem

universe v' u' u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S) (A : Type u') [Category.{v'} A]
  [HasLimitsOfSize.{u, u} A]

/-- An adjoint transpose through an equivalence, on variables: `η ≫ F(e a ≫ e b ≫ ε) = a ≫ b`. -/
theorem unit_comp_map_comp_comp_counit {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {a b₁ : D} {p p₁ p₂ r : C} (η : a ⟶ F.obj p) (θ : p ⟶ r) (ea : p ⟶ p₁) (eb : p₁ ⟶ p₂)
    (ε : p₂ ⟶ r) (x : a ⟶ b₁) (y : b₁ ⟶ F.obj r) (η₁ : b₁ ⟶ F.obj p₁) (η₂ : F.obj r ⟶ F.obj p₂)
    (hθ : θ = ea ≫ eb ≫ ε) (h₁ : η ≫ F.map ea = x ≫ η₁)
    (h₂ : η₁ ≫ F.map eb = y ≫ η₂) (h₃ : η₂ ≫ F.map ε = 𝟙 _) :
    η ≫ F.map θ = x ≫ y := by
  rw [hθ, F.map_comp, F.map_comp, reassoc_of% h₁, reassoc_of% h₂, h₃, Category.comp_id]

/-- **The comparison of direct images, read back on the bounded site**: after the unit of the
equivalence of the two presentations of the small étale site, it is the direct image of the unit
followed by the comparison `f_* ⋙ ρ_S ≅ ρ_T ⋙ f_*` of the restrictions. -/
theorem sheafEquiv_unit_comp_inverse_map_pushforwardBaseChangeIso_hom
    (Q : Sheaf (topology B T.obj T.property) A) :
    (sheafEquiv B S.1 S.property A).unit.app ((B.smallPushforward f A).obj Q) ≫
        (sheafEquiv B S.1 S.property A).inverse.map
          ((sheafEquivFunctorPushforwardBaseChangeIso B f A).hom.app Q) =
      (B.smallPushforward f A).map ((sheafEquiv B T.1 T.property A).unit.app Q) ≫
        (toEtaleSitePushforwardBaseChangeIso B f A).inv.app
          ((sheafEquiv B T.1 T.property A).functor.obj Q) := by
  let eS := sheafEquiv B S.1 S.property A
  let eT := sheafEquiv B T.1 T.property A
  let W := ((Stacks.EtaleCohomology.smallEtaleBaseChange
    (B.inclusion.map f)).sheafPushforwardContinuous
      A S.obj.smallEtaleTopology T.obj.smallEtaleTopology).obj (eT.functor.obj Q)
  have hθ : (sheafEquivFunctorPushforwardBaseChangeIso B f A).hom.app Q =
      eS.functor.map ((B.smallPushforward f A).map (eT.unit.app Q)) ≫
        eS.functor.map ((toEtaleSitePushforwardBaseChangeIso B f A).inv.app (eT.functor.obj Q)) ≫
        eS.counit.app W := by
    simp [sheafEquivFunctorPushforwardBaseChangeIso]
    rfl
  exact unit_comp_map_comp_comp_counit eS.inverse _ _ _ _ _ _ _ _ _ hθ
    (eS.unit_naturality _) (eS.unit_naturality _) (eS.unit_inverse_comp W)

end AlgebraicGeometry.SmallEtale

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

section RestrictScalars

/-- A one-sided inverse read through a factorization, on variables. -/
theorem unit_comp_eq_of_hom_eq {C : Type*} [Category* C] {a b c : C} (η : a ⟶ b) (i : b ⟶ c)
    (hm : c ⟶ b) (r : c ⟶ a) (r' : a ⟶ c) (h : hm = r ≫ η) (hi : hm ≫ i = 𝟙 _)
    (hr : r' ≫ r = 𝟙 _) : η ≫ i = r' := by
  rw [← Category.id_comp η, ← hr, Category.assoc, Category.assoc, ← reassoc_of% h, hi,
    Category.comp_id]

variable (B : BigEtaleSite.{u}) {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

/-- The comparison of reading sheaves on Mathlib's small étale site with `res_ρ`, after the unit
of the equivalence of the two presentations: the restriction of scalars of the unit. -/
theorem sheafEquiv_unit_comp_inverse_map_sheafEquivRestrictScalarsIso_inv (S : Scheme.{u})
    (hS : B.Contains S) (G : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{u + 1} Λ')) :
    (SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Λ)).unitIso.hom.app
        ((sheafCompose (SmallEtale.topology B S hS) (ModuleCat.restrictScalars.{u + 1} ρ)).obj G) ≫
      (SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Λ)).inverse.map
        ((sheafEquivRestrictScalarsIso B S hS ρ).inv.app G) =
    (sheafCompose (SmallEtale.topology B S hS) (ModuleCat.restrictScalars.{u + 1} ρ)).map
      ((SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Λ')).unitIso.hom.app G) :=
  unit_comp_eq_of_hom_eq _ _ _ _ _
    (sheafEquiv_inverse_map_sheafEquivRestrictScalarsIso_hom_app B S hS ρ G)
    ((SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Λ)).inverse.mapIso
      ((sheafEquivRestrictScalarsIso B S hS ρ).app G)).hom_inv_id
    ((sheafCompose (SmallEtale.topology B S hS) (ModuleCat.restrictScalars.{u + 1} ρ)).mapIso
      ((SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Λ')).unitIso.app G)).hom_inv_id

variable {S T : B.Scheme} (f : T ⟶ S)

/-- The chain of the commutation of the comparison of direct images with restriction of scalars,
on variables. -/
theorem restrictScalars_pushforward_chain {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {a b' c' : D} {p q r t : C} (η : a ⟶ F.obj p) (s : p ⟶ q) (tt : q ⟶ r) (θ : p ⟶ t)
    (d : t ⟶ r) (r₁ : a ⟶ F.obj q) (r₂ : a ⟶ b') (p₁ p₂ : b' ⟶ F.obj r) (r₃ : a ⟶ c')
    (p₀ : c' ⟶ F.obj t) (w : c' ⟶ b')
    (hs : η ≫ F.map s = r₁) (ht : r₁ ≫ F.map tt = r₂ ≫ p₁) (hp : p₁ = p₂)
    (hθ : η ≫ F.map θ = r₃ ≫ p₀) (hn : p₀ ≫ F.map d = w ≫ p₂) (hu : r₃ ≫ w = r₂) :
    η ≫ F.map (s ≫ tt) = η ≫ F.map (θ ≫ d) := by
  rw [F.map_comp, F.map_comp, reassoc_of% hs, ht, reassoc_of% hθ, hn, reassoc_of% hu, hp]

/-- The comparison of the restrictions along the two base changes commutes with restriction of
scalars: it is made of restriction maps of sections. -/
theorem restrictScalars_map_toEtaleSitePushforwardBaseChangeIso_inv
    (M : Sheaf T.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (sheafCompose (SmallEtale.topology B S.1 S.property) (ModuleCat.restrictScalars.{u + 1} ρ)).map
        ((toEtaleSitePushforwardBaseChangeIso B f (ModuleCat.{u + 1} Λ')).inv.app M) =
      (toEtaleSitePushforwardBaseChangeIso B f (ModuleCat.{u + 1} Λ)).inv.app
        ((etaleModuleRestrictScalars ρ T.1).obj M) :=
  Sheaf.hom_ext <| NatTrans.ext <| funext fun _ =>
    ModuleCat.hom_ext <| LinearMap.ext fun _ => rfl

/-- **The comparison of direct images of the two presentations of the small étale site commutes
with restriction of scalars.** -/
theorem sheafEquivRestrictScalarsIso_inv_comp_pushforwardBaseChangeIso
    (Q : Sheaf (SmallEtale.topology B T.1 T.property) (ModuleCat.{u + 1} Λ')) :
    (sheafEquivRestrictScalarsIso B S.1 S.property ρ).inv.app
        ((B.smallPushforward f (ModuleCat.{u + 1} Λ')).obj Q) ≫
      (etaleModuleRestrictScalars ρ S.1).map
        ((sheafEquivFunctorPushforwardBaseChangeIso B f (ModuleCat.{u + 1} Λ')).hom.app Q) =
    (sheafEquivFunctorPushforwardBaseChangeIso B f (ModuleCat.{u + 1} Λ)).hom.app
        ((sheafCompose (SmallEtale.topology B T.1 T.property)
          (ModuleCat.restrictScalars.{u + 1} ρ)).obj Q) ≫
      (etaleModuleDirectImage.{u, 0} Λ (B.inclusion.map f)).map
        ((sheafEquivRestrictScalarsIso B T.1 T.property ρ).inv.app Q) := by
  let eS := SmallEtale.sheafEquiv B S.1 S.property (ModuleCat.{u + 1} Λ)
  let eS' := SmallEtale.sheafEquiv B S.1 S.property (ModuleCat.{u + 1} Λ')
  let eT := SmallEtale.sheafEquiv B T.1 T.property (ModuleCat.{u + 1} Λ)
  let eT' := SmallEtale.sheafEquiv B T.1 T.property (ModuleCat.{u + 1} Λ')
  let resS :=
    sheafCompose (SmallEtale.topology B S.1 S.property) (ModuleCat.restrictScalars.{u + 1} ρ)
  let resT :=
    sheafCompose (SmallEtale.topology B T.1 T.property) (ModuleCat.restrictScalars.{u + 1} ρ)
  have hs := sheafEquiv_unit_comp_inverse_map_sheafEquivRestrictScalarsIso_inv B ρ S.1 S.property
    ((B.smallPushforward f (ModuleCat.{u + 1} Λ')).obj Q)
  have hθ' := SmallEtale.sheafEquiv_unit_comp_inverse_map_pushforwardBaseChangeIso_hom B f
    (ModuleCat.{u + 1} Λ') Q
  have ht := ((resS.map_comp _ _).symm.trans (congrArg resS.map hθ')).trans (resS.map_comp _ _)
  have hp := restrictScalars_map_toEtaleSitePushforwardBaseChangeIso_inv B ρ f (eT'.functor.obj Q)
  have hθ := SmallEtale.sheafEquiv_unit_comp_inverse_map_pushforwardBaseChangeIso_hom B f
    (ModuleCat.{u + 1} Λ) (resT.obj Q)
  have hn := ((toEtaleSitePushforwardBaseChangeIso B f (ModuleCat.{u + 1} Λ)).inv.naturality
    ((sheafEquivRestrictScalarsIso B T.1 T.property ρ).inv.app Q)).symm
  have hu := (((B.smallPushforward f (ModuleCat.{u + 1} Λ)).map_comp _ _).symm.trans
    (congrArg (B.smallPushforward f (ModuleCat.{u + 1} Λ)).map
      (sheafEquiv_unit_comp_inverse_map_sheafEquivRestrictScalarsIso_inv B ρ T.1 T.property Q)))
  apply (eS.toAdjunction.homEquiv _ _).injective
  refine (Adjunction.homEquiv_unit _ _ _ _).trans
    (Eq.trans ?_ (Adjunction.homEquiv_unit _ _ _ _).symm)
  exact restrictScalars_pushforward_chain eS.inverse _ _ _ _ _ _ _ _ _ _ _ _ hs ht hp hθ hn hu

end RestrictScalars

/-! ### The transitions -/

/-- The chain of the compatibility of the levels of the inverse image with the transitions, on
variables: both adjoint transposes are rewritten to `e₁ ≫ e(res η) ≫ θ ≫ D s₃`. -/
theorem level_transition_chain {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {G : D ⥤ C}
    (adj : L ⊣ G) {o₀ o₅ o₆ o₇ o₈ o₉ o₁₁ : C} {m₂ m₃ m₄ : D}
    (eT : o₀ ⟶ o₅) (b : L.obj o₅ ⟶ m₂) (c : m₂ ⟶ m₃) (d : L.obj o₀ ⟶ m₄) (e : m₄ ⟶ m₃)
    (Rη : o₅ ⟶ G.obj m₂) (e₁ : o₀ ⟶ o₆) (s₁ : o₆ ⟶ o₅) (Reη : o₅ ⟶ o₇) (Rθ : o₇ ⟶ G.obj m₃)
    (eRη : o₆ ⟶ o₈) (s₂ : o₈ ⟶ o₇) (θr : o₈ ⟶ o₉) (Ds₃ : o₉ ⟶ G.obj m₃)
    (eη' : o₀ ⟶ o₁₁) (θ' : o₁₁ ⟶ G.obj m₄) (Dι : G.obj m₄ ⟶ o₉) (eι : o₁₁ ⟶ o₈)
    (hb : adj.unit.app o₅ ≫ G.map b = Rη) (hc : Rη ≫ G.map c = Reη ≫ Rθ) (hT : eT = e₁ ≫ s₁)
    (hd : s₁ ≫ Reη = eRη ≫ s₂) (he : s₂ ≫ Rθ = θr ≫ Ds₃)
    (hf : adj.unit.app o₀ ≫ G.map d = eη' ≫ θ') (hg : G.map e = Dι ≫ Ds₃)
    (hh : θ' ≫ Dι = eι ≫ θr) (hi : eη' ≫ eι = e₁ ≫ eRη) :
    adj.homEquiv _ _ (L.map eT ≫ b ≫ c) = adj.homEquiv _ _ (d ≫ e) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, G.map_comp, G.map_comp, G.map_comp,
    adj.unit_naturality_assoc, reassoc_of% hb, hc, hT, Category.assoc, reassoc_of% hd, he,
    reassoc_of% hf, hg, reassoc_of% hh, reassoc_of% hi]

section Transition

variable (B : BigEtaleSite.{u}) {X X' : B.Scheme} [IsNoetherian X.1] [IsNoetherian X'.1]
  (g : X' ⟶ X) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **The identification `g⁻¹ Fₙ ≅ (g⁻¹F)ₙ` is compatible with the transitions**: the inverse
image of the transition `Fₙ₊₁ ⟶ res Fₙ`, read through `g⁻¹ ∘ res ≅ res ∘ g⁻¹` and
`g⁻¹ Fₙ ≅ (g⁻¹F)ₙ`, is `g⁻¹ Fₙ₊₁ ≅ (g⁻¹F)ₙ₊₁` followed by the transition of `g⁻¹F`, as morphisms
of sheaves of `ℤ/ℓⁿ⁺²`-modules on Mathlib's small étale site of `X'`. -/
theorem LAdicSheaf.etaleLevelInverseImageIso_transition (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (n : ℕ) :
    (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) (B.inclusion.map g)).map
        (LAdicSheaf.etaleTransition B X ℓ F n) ≫
      (etaleModuleInverseImageRestrictScalars (levelCast ℓ n) (B.inclusion.map g)).hom.app
        (LAdicSheaf.etaleLevel B X ℓ F n) ≫
      (etaleModuleRestrictScalars (levelCast ℓ n) X'.1).map
        (LAdicSheaf.etaleLevelInverseImageIso B g ℓ F n).hom =
    (LAdicSheaf.etaleLevelInverseImageIso B g ℓ F (n + 1)).hom ≫
      LAdicSheaf.etaleTransition B X' ℓ (LAdicSheaf.inverseImage g F) n := by
  let res := etaleModuleRestrictScalars (levelCast ℓ n) X.1
  let Q := (LAdicSheaf.levelPullback g n).obj (F.level n)
  have hb := etaleModuleInverseImageRestrictScalars_unit (levelCast ℓ n) (B.inclusion.map g)
    (LAdicSheaf.etaleLevel B X ℓ F n)
  have h₁ := SmallEtale.sheafEquiv_map_unit_comp_pushforwardBaseChangeIso B g
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (etaleModuleInverseImageAdj.{u, 0} (ZMod (ℓ ^ (n + 1))) (B.inclusion.map g))
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafAdjunctionContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) _ _) (F.level n)
  have hc := ((res.map_comp _ _).symm.trans (congrArg res.map h₁.symm)).trans (res.map_comp _ _)
  have hd := ((sheafEquivRestrictScalarsIso B X.1 X.property (levelCast ℓ n)).inv.naturality
    ((LAdicSheaf.levelAdjunction g n).unit.app (F.level n))).symm
  have he := sheafEquivRestrictScalarsIso_inv_comp_pushforwardBaseChangeIso B (levelCast ℓ n) g Q
  have hf := (SmallEtale.sheafEquiv_map_unit_comp_pushforwardBaseChangeIso B g
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1))))
    (etaleModuleInverseImageAdj.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) (B.inclusion.map g))
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafAdjunctionContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1)))) _ _) (F.level (n + 1))).symm
  have hg := (etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) (B.inclusion.map g)).map_comp
    ((SmallEtale.sheafEquiv B X'.1 X'.property
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1))))).functor.map
      (LAdicSheaf.inverseImageTransition g F n))
    ((sheafEquivRestrictScalarsIso B X'.1 X'.property (levelCast ℓ n)).inv.app Q)
  have hh := ((SmallEtale.sheafEquivFunctorPushforwardBaseChangeIso B g
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1))))).hom.naturality
      (LAdicSheaf.inverseImageTransition g F n)).symm
  have k : (LAdicSheaf.levelAdjunction g (n + 1)).unit.app (F.level (n + 1)) ≫
      (LAdicSheaf.levelPushforward g (n + 1)).map (LAdicSheaf.inverseImageTransition g F n) =
      F.transition n ≫ (LAdicSheaf.levelRestrict X n).map
        ((LAdicSheaf.levelAdjunction g n).unit.app (F.level n)) :=
    (((LAdicSheaf.levelAdjunction g (n + 1)).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)).trans (congrArg (_ ≫ ·) (Category.comp_id _))
  let e₂ :=
    (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1))))).functor
  have hi := (e₂.map_comp _ _).symm.trans ((congrArg e₂.map k).trans (e₂.map_comp _ _))
  apply ((etaleModuleInverseImageAdj.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) (B.inclusion.map g)).homEquiv
    _ _).injective
  exact level_transition_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb hc rfl hd he hf hg hh hi

end Transition

end Stacks.EtaleCohomology

end
