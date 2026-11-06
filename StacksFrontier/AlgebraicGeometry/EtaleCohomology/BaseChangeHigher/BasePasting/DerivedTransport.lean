module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting.AbstractPasting

/-!
# Transporting the derived comparison along isomorphisms of exact functors

The comparison descended from a square read through isomorphisms of its two exact horizontal
functors is the comparison of the transported square, conjugated by the right derived functors of
those isomorphisms (`Stacks.Cohomology.BaseChange.derived_transport`).  The file also contains the
abstract shapes `pentagonChase` and `transportAux` of the chases used for the étale composite
extension, and the comparison of `mate` with Mathlib's `mateEquiv`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.Cohomology.BaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Reassoc2

variable {𝒞 : Type*} [Category* 𝒞]

/-- Solving a morphism out of a factorization through two isomorphisms. -/
public theorem cancelIsos {X₀ X₁ Y₀ Y₁ : 𝒞} (i : X₀ ≅ X₁) (j : Y₀ ≅ Y₁) (x : X₁ ⟶ Y₁)
    (y : X₀ ⟶ Y₀) (h : y = i.hom ≫ x ≫ j.inv) : x = i.inv ≫ y ≫ j.hom := by
  simp [h]

/-- Cancelling two isomorphisms across a commuting square. -/
public theorem isoCancel {X₀ X₁ Y₀ Y₁ : 𝒞} (i : X₀ ≅ X₁) (j : Y₀ ≅ Y₁) (x : X₁ ⟶ Y₁)
    (m : X₀ ⟶ Y₀) (h : i.hom ≫ x = m ≫ j.hom) : x ≫ j.inv = i.inv ≫ m := by
  rwa [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]

/-- A functor applied to a threefold composite. -/
public theorem mapComp₃ {𝒟 : Type*} [Category* 𝒟] (Φ : 𝒞 ⥤ 𝒟) {X₀ X₁ X₂ X₃ : 𝒞}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) :
    Φ.map a ≫ Φ.map b ≫ Φ.map c = Φ.map (a ≫ b ≫ c) := by simp

/-- **The shape of the three-pentagon chase, in an arbitrary category.**  From the three
pentagon identities `h₁`, `h₂`, `h₃` the horizontal paste on the left is the whiskered
comparison on the right. -/
public theorem pentagonChase {U₀ U₁ U₂ U₃ U₄ U₅ U₆ U₇ V₁ V₂ V₃ : 𝒞}
    (α₁ : U₀ ≅ U₁) (α₂ : U₄ ≅ U₃) (α₃ : U₆ ≅ U₇)
    (wlA : U₁ ≅ U₂) (wlB : U₃ ≅ U₂) (wrD : U₄ ≅ U₅) (wrE : U₆ ≅ U₅)
    (Rc : U₂ ≅ V₂) (Sc : U₅ ≅ V₂) (M : V₁ ≅ V₂) (N : V₃ ≅ V₂) (wlΨ : U₇ ≅ V₃)
    (wrΦ : U₀ ⟶ V₁)
    (h₁ : wlA.hom ≫ Rc.hom = α₁.inv ≫ wrΦ ≫ M.hom)
    (h₂ : wlB.hom ≫ Rc.hom = α₂.inv ≫ wrD.hom ≫ Sc.hom)
    (h₃ : wlΨ.hom ≫ N.hom = α₃.inv ≫ wrE.hom ≫ Sc.hom) :
    α₁.hom ≫ wlA.hom ≫ wlB.inv ≫ α₂.inv ≫ wrD.hom ≫ wrE.inv ≫ α₃.hom =
      wrΦ ≫ M.hom ≫ N.inv ≫ wlΨ.inv := by
  have k₂ : wlB.inv ≫ α₂.inv ≫ wrD.hom = Rc.hom ≫ Sc.inv := by
    calc wlB.inv ≫ α₂.inv ≫ wrD.hom
        = (wlB.inv ≫ α₂.inv ≫ wrD.hom ≫ Sc.hom) ≫ Sc.inv := by simp
      _ = (wlB.inv ≫ wlB.hom ≫ Rc.hom) ≫ Sc.inv := by rw [← h₂]
      _ = Rc.hom ≫ Sc.inv := by simp
  have k₁ : α₁.hom ≫ wlA.hom ≫ Rc.hom = wrΦ ≫ M.hom := by rw [h₁, Iso.hom_inv_id_assoc]
  have k₃ : Sc.inv ≫ wrE.inv ≫ α₃.hom = N.inv ≫ wlΨ.inv := by
    calc Sc.inv ≫ wrE.inv ≫ α₃.hom
        = (N.inv ≫ wlΨ.inv) ≫ (wlΨ.hom ≫ N.hom) ≫ Sc.inv ≫ wrE.inv ≫ α₃.hom := by simp
      _ = (N.inv ≫ wlΨ.inv) ≫ (α₃.inv ≫ wrE.hom ≫ Sc.hom) ≫
            Sc.inv ≫ wrE.inv ≫ α₃.hom := by rw [h₃]
      _ = N.inv ≫ wlΨ.inv := by simp
  rw [reassoc_of% k₂, reassoc_of% k₁, k₃]

/-- The shape of the transport chase, in an arbitrary category. -/
public theorem transportAux {X₀ X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ Z₁ Z₂ Z₃ : 𝒞}
    {u : X₀ ⟶ X₁} {a : X₁ ⟶ X₂} {b : X₂ ⟶ X₃} {c : X₃ ⟶ X₄}
    {a' : X₀ ⟶ Y₁} {u₁ : Y₁ ⟶ X₂}
    {i₁ : Y₁ ⟶ Y₂} {p₁ : Y₂ ⟶ Y₃} {q₁ : Y₃ ⟶ Y₄} {r₁ : Y₄ ⟶ X₃}
    {i : X₀ ⟶ Z₁} {m : Z₁ ⟶ Y₂} {p : Z₁ ⟶ Z₂} {n : Y₃ ⟶ Z₂} {s : Y₄ ⟶ Z₃}
    {q : Z₂ ⟶ Z₃} {r : Z₃ ⟶ X₄}
    (h₁ : u ≫ a = a' ≫ u₁)
    (h₂ : u₁ ≫ b = i₁ ≫ p₁ ≫ q₁ ≫ r₁)
    (h₃ : a' ≫ i₁ = i ≫ m)
    (h₄ : r₁ ≫ c = s ≫ r)
    (h₅ : q₁ ≫ s = n ≫ q)
    (h₆ : m ≫ p₁ ≫ n = p) :
    u ≫ a ≫ b ≫ c = i ≫ p ≫ q ≫ r := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₄, reassoc_of% h₃, reassoc_of% h₅, reassoc_of% h₆]

end Reassoc2

section TransportUnits

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [EnoughInjectives A] {G G₁ : A ⥤ B} [G.Additive] [G₁.Additive]

/-- The component of the derived transformation induced by an isomorphism of additive
functors, read through the two derived-functor units. -/
public theorem unit_comp_rightDerivedFunctorPlusNatIso_hom (α : G ≅ G₁)
    (M : HomotopyCategory.Plus A) :
    G.rightDerivedFunctorPlusUnith.app M ≫
        (Functor.rightDerivedFunctorPlusNatIso α).hom.app
          (DerivedCategory.Plus.Qh.obj M) =
      DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusNatIso α).hom.app M) ≫
        G₁.rightDerivedFunctorPlusUnith.app M :=
  Functor.rightDerivedNatTrans_app G.rightDerivedFunctorPlus G₁.rightDerivedFunctorPlus
    G.rightDerivedFunctorPlusUnith G₁.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso A)
    (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryPlusNatIso α)
      DerivedCategory.Plus.Qh).hom M

/-- The inverse form of `unit_comp_rightDerivedFunctorPlusNatIso_hom`. -/
public theorem unit_comp_rightDerivedFunctorPlusNatIso_inv (α : G ≅ G₁)
    (M : HomotopyCategory.Plus A) :
    G₁.rightDerivedFunctorPlusUnith.app M ≫
        (Functor.rightDerivedFunctorPlusNatIso α).inv.app
          (DerivedCategory.Plus.Qh.obj M) =
      DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusNatIso α).inv.app M) ≫
        G.rightDerivedFunctorPlusUnith.app M :=
  Functor.rightDerivedNatTrans_app G₁.rightDerivedFunctorPlus G.rightDerivedFunctorPlus
    G₁.rightDerivedFunctorPlusUnith G.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso A)
    (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryPlusNatIso α)
      DerivedCategory.Plus.Qh).inv M

variable [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]

/-- For exact functors, the derived transformation induced by an isomorphism is the
degreewise one, read through the two comparisons with the degreewise action. -/
public theorem rightDerivedFunctorPlusNatIso_hom_app_exactUnitIso_inv (α : G ≅ G₁)
    (M : HomotopyCategory.Plus A) :
    (Functor.rightDerivedFunctorPlusNatIso α).hom.app
          (DerivedCategory.Plus.Qh.obj M) ≫ (exactUnitIso G₁).inv.app M =
      (exactUnitIso G).inv.app M ≫
        DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusNatIso α).hom.app M) :=
  isoCancel ((exactUnitIso G).app M) ((exactUnitIso G₁).app M) _ _
    (unit_comp_rightDerivedFunctorPlusNatIso_hom α M)

end TransportUnits

section Transport

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  (F : A ⥤ B) (F' : C ⥤ D) {G G₁ : B ⥤ D} {G' G₁' : A ⥤ C}
  [F.Additive] [F'.Additive] [G.Additive] [G₁.Additive] [G'.Additive] [G₁'.Additive]

omit [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C] in
/-- **The degreewise comparison transported along isomorphisms of the two horizontal
functors.** -/
public theorem mapPlus_transport (α : G ≅ G₁) (β : G' ≅ G₁') (τ₁ : F ⋙ G₁ ⟶ G₁' ⋙ F')
    (K : HomotopyCategory.Plus A) :
    (Functor.mapHomotopyCategoryPlusNatIso α).hom.app
          (F.mapHomotopyCategoryPlus.obj K) ≫
        (mapPlus τ₁).app K ≫
        F'.mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusNatIso β).inv.app K) =
      (mapPlus (Functor.whiskerLeft F α.hom ≫ τ₁ ≫
        Functor.whiskerRight β.inv F')).app K := by
  ext
  rfl

variable [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]

/-- **Transport of the derived comparison along isomorphisms of its two horizontal
functors, at a bounded below complex.** -/
public theorem derived_transport_app (α : G ≅ G₁) (β : G' ≅ G₁')
    (τ₁ : F ⋙ G₁ ⟶ G₁' ⋙ F') (K : HomotopyCategory.Plus A) :
    (compUnit F G).app K ≫
        (derived F F' G G'
            (Functor.whiskerLeft F α.hom ≫ τ₁ ≫ Functor.whiskerRight β.inv F')
            (exactUnitIso G)).app (DerivedCategory.Plus.Qh.obj K) =
      (compUnit F G).app K ≫
        (Functor.rightDerivedFunctorPlusNatIso α).hom.app
            (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) ≫
          (derived F F' G₁ G₁' τ₁ (exactUnitIso G₁)).app
              (DerivedCategory.Plus.Qh.obj K) ≫
            F'.rightDerivedFunctorPlus.map
              ((Functor.rightDerivedFunctorPlusNatIso β).inv.app
                (DerivedCategory.Plus.Qh.obj K)) := by
  have h₄ : F'.rightDerivedFunctorPlus.map (G₁'.rightDerivedFunctorPlusUnith.app K) ≫
      F'.rightDerivedFunctorPlus.map
        ((Functor.rightDerivedFunctorPlusNatIso β).inv.app
          (DerivedCategory.Plus.Qh.obj K)) =
      F'.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Qh.map
            ((Functor.mapHomotopyCategoryPlusNatIso β).inv.app K)) ≫
        F'.rightDerivedFunctorPlus.map (G'.rightDerivedFunctorPlusUnith.app K) := by
    rw [← Functor.map_comp, ← Functor.map_comp,
      unit_comp_rightDerivedFunctorPlusNatIso_inv]
  have h₆ : DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusNatIso α).hom.app
          (F.mapHomotopyCategoryPlus.obj K)) ≫
      DerivedCategory.Plus.Qh.map ((mapPlus τ₁).app K) ≫
        DerivedCategory.Plus.Qh.map
          (F'.mapHomotopyCategoryPlus.map
            ((Functor.mapHomotopyCategoryPlusNatIso β).inv.app K)) =
      DerivedCategory.Plus.Qh.map
        ((mapPlus (Functor.whiskerLeft F α.hom ≫ τ₁ ≫
          Functor.whiskerRight β.inv F')).app K) :=
    (mapComp₃ DerivedCategory.Plus.Qh _ _ _).trans
      (congrArg (fun t ↦ DerivedCategory.Plus.Qh.map t)
        (mapPlus_transport F F' α β τ₁ K))
  rw [compUnit_app, derived_fac_app, onHomotopy_app]
  refine Eq.symm (transportAux
      ((Functor.rightDerivedFunctorPlusNatIso α).hom.naturality
        (F.rightDerivedFunctorPlusUnith.app K))
      ((derived_fac_app F F' G₁ G₁' τ₁ (exactUnitIso G₁) K).trans
        (onHomotopy_app F F' G₁ G₁' τ₁ (exactUnitIso G₁) K))
      (rightDerivedFunctorPlusNatIso_hom_app_exactUnitIso_inv α
        (F.mapHomotopyCategoryPlus.obj K))
      h₄
      (F'.rightDerivedFunctorPlusUnith.naturality
        ((Functor.mapHomotopyCategoryPlusNatIso β).inv.app K)).symm
      h₆)

/-- **Transport of the derived comparison along isomorphisms of its two exact horizontal
functors.**  The comparison descended from a comparison read through isomorphisms `α` and
`β` of the two horizontal functors is the comparison of the transported square, conjugated
by the right derived functors of `α` and `β`.  Both sides have the same composite with the
derived-functor unit of `RF`, which determines them. -/
public theorem derived_transport (α : G ≅ G₁) (β : G' ≅ G₁')
    (τ₁ : F ⋙ G₁ ⟶ G₁' ⋙ F') :
    derived F F' G G'
        (Functor.whiskerLeft F α.hom ≫ τ₁ ≫ Functor.whiskerRight β.inv F')
        (exactUnitIso G) =
      Functor.whiskerLeft F.rightDerivedFunctorPlus
          (Functor.rightDerivedFunctorPlusNatIso α).hom ≫
        derived F F' G₁ G₁' τ₁ (exactUnitIso G₁) ≫
          Functor.whiskerRight (Functor.rightDerivedFunctorPlusNatIso β).inv
            F'.rightDerivedFunctorPlus :=
  Functor.rightDerived_ext (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus)
    (compUnit F G) (HomotopyCategory.Plus.quasiIso A) _ _ _
    (NatTrans.ext (funext fun K ↦ derived_transport_app F F' α β τ₁ K))

end Transport

section MateForm

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]

/-- **The mate of a commutative square of adjunctions is Mathlib's mate**, read in the
inverse direction of the mates correspondence. -/
public theorem mate_eq_mateEquiv_symm {G : B ⥤ D} {P : D ⥤ B} (adj : G ⊣ P)
    {G' : A ⥤ C} {P' : C ⥤ A} (adj' : G' ⊣ P') (F : A ⥤ B) (F' : C ⥤ D)
    (ε : P' ⋙ F ≅ F' ⋙ P) :
    mate adj adj' F F' ε =
      ((mateEquiv adj' adj).symm (TwoSquare.mk P' F' F P ε.hom)).natTrans := by
  ext X
  simp [mate, mateEquiv]

/-- The conjugate of the comparison of left adjoints attached to an isomorphism of composite
right adjoints is the inverse of that isomorphism. -/
public theorem conjugateEquiv_leftAdjointCompIso_hom
    {F₀₁ : A ⥤ B} {F₁₂ : B ⥤ C} {F₀₂ : A ⥤ C}
    {G₁₀ : B ⥤ A} {G₂₁ : C ⥤ B} {G₂₀ : C ⥤ A}
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₀₂ : F₀₂ ⊣ G₂₀)
    (e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀) :
    conjugateEquiv adj₀₂ (adj₀₁.comp adj₁₂)
        (Adjunction.leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e₀₁₂).hom = e₀₁₂.inv := by
  have h := conjugateEquiv_comp adj₀₂ (adj₀₁.comp adj₁₂) adj₀₂
    (Adjunction.leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e₀₁₂).hom
    (Adjunction.leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e₀₁₂).inv
  rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv, Iso.inv_hom_id,
    conjugateEquiv_id] at h
  rw [← Category.comp_id (conjugateEquiv adj₀₂ (adj₀₁.comp adj₁₂) _), ← e₀₁₂.hom_inv_id,
    ← Category.assoc, h, Category.id_comp]

/-- Taking mates commutes with whiskering the two vertical functors of a 2-square. -/
public lemma mateEquiv_whisker {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {G G' : A ⥤ C} {H H' : B ⥤ D}
    (α : TwoSquare G L₁ L₂ H) (φ : G' ⟶ G) (ψ : H ⟶ H') :
    mateEquiv adj₁ adj₂ ((α.whiskerTop φ).whiskerBottom ψ) =
      ((mateEquiv adj₁ adj₂ α).whiskerRight φ).whiskerLeft ψ := by
  refine TwoSquare.ext _ _ fun d ↦ ?_
  simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, mateEquiv]

end MateForm

end Stacks.Cohomology.BaseChange

end
