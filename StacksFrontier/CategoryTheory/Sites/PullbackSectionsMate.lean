module

public import StacksFrontier.CategoryTheory.Sites.PullbackSectionsComparison

/-!
# The restriction map on sections of a sheaf pullback reflects inverse images

Let `a : C ⥤ D`, `b : D ⥤ E` and `c : C ⥤ E` be continuous functors of sites with a
factorization `a ⋙ b ≅ c`. The arrow `a⁻¹F ⟶ b_* c⁻¹F` of
`CategoryTheory.sheafPullbackRestriction` has an adjunct `b⁻¹a⁻¹F ⟶ c⁻¹F` under the adjunction
for `b`, and that adjunct is an isomorphism: it is the canonical comparison of the two left
adjoints of `c_*`.

Consequently the map of global sections induced by `sheafPullbackRestriction` *reflects*
inverse images: two global sections of `a⁻¹F` with the same image in the global sections of
`c⁻¹F` have the same inverse image along `b`. This is what turns a statement about sections
over the objects of a big site into a statement about pullbacks of sheaves on small sites.

## Main definitions

* `CategoryTheory.sheafPullbackRestrictionAdjunct` — the `b`-adjunct `b⁻¹a⁻¹F ⟶ c⁻¹F` of
  `CategoryTheory.sheafPullbackRestriction`.
* `CategoryTheory.isTerminalConstPUnit` and
  `CategoryTheory.isTerminalConstantSheafPUnit` — the constant presheaf, resp. the constant
  sheaf, at a singleton is terminal, and `CategoryTheory.terminalIsoConstantSheafPUnit`
  identifies the latter with a terminal sheaf.
* `CategoryTheory.Sheaf.ΓEquivHomTerminal` — global sections of a sheaf of types as the
  morphisms to it from a terminal sheaf.

## Main results

* `CategoryTheory.isIso_sheafPullbackRestrictionAdjunct` — the adjunct is an isomorphism.
* `CategoryTheory.sheafPullbackSectionsRestriction_eq` — the map of global sections induced by
  `sheafPullbackRestriction` is the map `Sheaf.Γ` induces on it, up to the comparison of the two
  identifications of global sections with sections at a terminal object.
* `CategoryTheory.sheafPullback_map_eq_of_comp_sheafPullbackRestriction_eq` and
  `CategoryTheory.sheafPullback_map_eq_of_sheafPullbackSectionsRestriction_eq` — the restriction
  map, resp. the induced map on global sections, reflects inverse images along `b`.

## Implementation notes

The adjunct is identified with `CategoryTheory.Adjunction.leftAdjointUniq` applied to the
composite adjunction, transported along `Functor.sheafPushforwardContinuousComp'`, and to the
adjunction for `c`. The identification is by uniqueness of adjuncts: both morphisms have the
unit of the adjunction for `c` as their adjunct.

A terminal sheaf of types is exhibited concretely as the constant sheaf at a singleton, which
is the sheafification of a terminal presheaf; sheafification preserves finite limits, so that
sheafification is terminal. Mathlib's `CategoryTheory.Sheaf.ΓObjEquivHom` then identifies
global sections with morphisms out of it.

## References

* [Stacks Project, Tag 09XN](https://stacks.math.columbia.edu/tag/09XN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃ w

namespace CategoryTheory

section Terminal

/-- The constant presheaf at a singleton is a terminal presheaf. -/
public def isTerminalConstPUnit (D : Type u₂) [Category.{v₂} D] :
    IsTerminal ((Functor.const Dᵒᵖ).obj (PUnit.{w + 1} : Type w)) :=
  IsTerminal.ofUniqueHom (fun _ => { app := fun _ => ↾(fun _ => PUnit.unit) })
    (fun _ _ => by
      ext _ _
      rfl)

variable {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D)

/-- The constant sheaf at a singleton is a terminal sheaf: it is the sheafification of a
terminal presheaf, and sheafification preserves finite limits. -/
public def isTerminalConstantSheafPUnit [HasSheafify K (Type w)] :
    IsTerminal ((constantSheaf K (Type w)).obj (PUnit.{w + 1} : Type w)) :=
  (isTerminalConstPUnit D).isTerminalObj (presheafToSheaf K (Type w)) _

variable [HasSheafify K (Type w)] [HasTerminal D] [HasTerminal (Sheaf K (Type w))]

/-- The canonical isomorphism of a terminal sheaf of types with the constant sheaf at a
singleton. -/
public def terminalIsoConstantSheafPUnit :
    (⊤_ (Sheaf K (Type w))) ≅ (constantSheaf K (Type w)).obj (PUnit.{w + 1} : Type w) :=
  terminalIsTerminal.uniqueUpToIso (isTerminalConstantSheafPUnit K)

/-- Global sections of a sheaf of types are the morphisms to it from a terminal sheaf. -/
public def Sheaf.ΓEquivHomTerminal (H : Sheaf K (Type w)) :
    (Sheaf.Γ K (Type w)).obj H ≃ ((⊤_ (Sheaf K (Type w))) ⟶ H) :=
  (Sheaf.ΓObjEquivHom K H (PUnit.{w + 1} : Type w)).trans
    { toFun := fun f => (terminalIsoConstantSheafPUnit K).hom ≫ f
      invFun := fun g => (terminalIsoConstantSheafPUnit K).inv ≫ g
      left_inv := (terminalIsoConstantSheafPUnit K).inv_hom_id_assoc
      right_inv := (terminalIsoConstantSheafPUnit K).hom_inv_id_assoc }

/-- `CategoryTheory.Sheaf.ΓEquivHomTerminal` is natural: the global sections map induced by a
morphism of sheaves becomes postcomposition with that morphism. -/
public lemma Sheaf.ΓEquivHomTerminal_naturality {H H' : Sheaf K (Type w)} (ρ : H ⟶ H')
    (s : (Sheaf.Γ K (Type w)).obj H) :
    Sheaf.ΓEquivHomTerminal K H' ((Sheaf.Γ K (Type w)).map ρ s) =
      Sheaf.ΓEquivHomTerminal K H s ≫ ρ := by
  dsimp only [Sheaf.ΓEquivHomTerminal, Equiv.trans_apply, Equiv.coe_fn_mk]
  rw [Sheaf.ΓObjEquivHom_naturality, Category.assoc]

end Terminal

section Sections

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  (a : C ⥤ D) (b : D ⥤ E) (c : C ⥤ E)
  [a.IsContinuous J K] [b.IsContinuous K L] [c.IsContinuous J L]
  [(a.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
  [(c.sheafPushforwardContinuous (Type w) J L).IsRightAdjoint]
  [HasTerminal D] [HasTerminal E]
  [HasWeakSheafify K (Type w)] [HasWeakSheafify L (Type w)]

/-- The map of global sections induced by `CategoryTheory.sheafPullbackRestriction` is the map
`Sheaf.Γ` induces on `sheafPullbackRestriction` itself, followed by the comparison of the two
identifications of global sections with sections at a terminal object. -/
public lemma sheafPullbackSectionsRestriction_eq (e : a ⋙ b ≅ c) {T : D}
    (hT : IsTerminal T) (hbT : IsTerminal (b.obj T)) (F : Sheaf J (Type w)) :
    sheafPullbackSectionsRestriction J K L a b c e hT hbT F =
      (Sheaf.Γ K (Type w)).map (sheafPullbackRestriction J K L a b c e F) ≫
        ((Sheaf.ΓNatIsoSheafSections K (Type w) hT).hom.app
            ((b.sheafPushforwardContinuous (Type w) K L).obj
              ((c.sheafPullback (Type w) J L).obj F)) ≫
          (Sheaf.ΓNatIsoSheafSections L (Type w) hbT).inv.app
            ((c.sheafPullback (Type w) J L).obj F)) :=
  ((Sheaf.ΓNatIsoSheafSections K (Type w) hT).hom.naturality_assoc
    (sheafPullbackRestriction J K L a b c e F) _).symm

/-- The map of global sections induced by `CategoryTheory.sheafPullbackRestriction` differs from
the map `Sheaf.Γ` induces on `sheafPullbackRestriction` by an isomorphism, so the two have the
same fibres. -/
public lemma Γ_map_sheafPullbackRestriction_eq_of_sections_eq (e : a ⋙ b ≅ c) {T : D}
    (hT : IsTerminal T) (hbT : IsTerminal (b.obj T)) (F : Sheaf J (Type w))
    (s₁ s₂ : (Sheaf.Γ K (Type w)).obj ((a.sheafPullback (Type w) J K).obj F))
    (h : sheafPullbackSectionsRestriction J K L a b c e hT hbT F s₁ =
      sheafPullbackSectionsRestriction J K L a b c e hT hbT F s₂) :
    (Sheaf.Γ K (Type w)).map (sheafPullbackRestriction J K L a b c e F) s₁ =
      (Sheaf.Γ K (Type w)).map (sheafPullbackRestriction J K L a b c e F) s₂ := by
  have h₁ : IsIso ((Sheaf.ΓNatIsoSheafSections K (Type w) hT).hom.app
      ((b.sheafPushforwardContinuous (Type w) K L).obj
        ((c.sheafPullback (Type w) J L).obj F))) :=
    ((Sheaf.ΓNatIsoSheafSections K (Type w) hT).app _).isIso_hom
  have h₂ : IsIso ((Sheaf.ΓNatIsoSheafSections L (Type w) hbT).inv.app
      ((c.sheafPullback (Type w) J L).obj F)) :=
    ((Sheaf.ΓNatIsoSheafSections L (Type w) hbT).app _).isIso_inv
  have := IsIso.comp_isIso' h₁ h₂
  simp only [sheafPullbackSectionsRestriction_eq, ConcreteCategory.comp_apply] at h
  exact (mono_iff_injective _).mp inferInstance h

end Sections

section Adjunct

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  (a : C ⥤ D) (b : D ⥤ E) (c : C ⥤ E)
  [a.IsContinuous J K] [b.IsContinuous K L] [c.IsContinuous J L]
  [(a.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
  [(b.sheafPushforwardContinuous (Type w) K L).IsRightAdjoint]
  [(c.sheafPushforwardContinuous (Type w) J L).IsRightAdjoint]

/-- The adjunct, under the adjunction for `b`, of `CategoryTheory.sheafPullbackRestriction`. -/
public def sheafPullbackRestrictionAdjunct (e : a ⋙ b ≅ c) (F : Sheaf J (Type w)) :
    (b.sheafPullback (Type w) K L).obj ((a.sheafPullback (Type w) J K).obj F) ⟶
      (c.sheafPullback (Type w) J L).obj F :=
  ((b.sheafAdjunctionContinuous (Type w) K L).homEquiv _ _).symm
    (sheafPullbackRestriction J K L a b c e F)

/-- The adjunct of `CategoryTheory.sheafPullbackRestriction` is an isomorphism: both it and the
canonical comparison of the two left adjoints of `c_*` have the unit of the adjunction for `c`
as their adjunct. -/
public instance isIso_sheafPullbackRestrictionAdjunct (e : a ⋙ b ≅ c) (F : Sheaf J (Type w)) :
    IsIso (sheafPullbackRestrictionAdjunct J K L a b c e F) := by
  let adjA := a.sheafAdjunctionContinuous (Type w) J K
  let adjB := b.sheafAdjunctionContinuous (Type w) K L
  let adjC := c.sheafAdjunctionContinuous (Type w) J L
  let cmp := Functor.sheafPushforwardContinuousComp' e (Type w) J K L
  let adj1 := (adjA.comp adjB).ofNatIsoRight cmp
  have hA : adjA.homEquiv _ _ (sheafPullbackRestriction J K L a b c e F) =
      adjC.unit.app F ≫ cmp.inv.app _ :=
    (adjA.homEquiv _ _).apply_symm_apply _
  have hB : adjB.homEquiv _ _ (sheafPullbackRestrictionAdjunct J K L a b c e F) =
      sheafPullbackRestriction J K L a b c e F :=
    (adjB.homEquiv _ _).apply_symm_apply _
  have key : adj1.homEquiv F _ (sheafPullbackRestrictionAdjunct J K L a b c e F) =
      adjC.unit.app F := by
    rw [Adjunction.homEquiv_ofNatIsoRight_apply]
    simp only [Adjunction.comp_homEquiv, Equiv.trans_apply]
    rw [hB, hA, Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _
  have heq : sheafPullbackRestrictionAdjunct J K L a b c e F =
      (Adjunction.leftAdjointUniq adj1 adjC).hom.app F :=
    (adj1.homEquiv _ _).injective
      (key.trans (Adjunction.homEquiv_leftAdjointUniq_hom_app adj1 adjC F).symm)
  rw [heq]
  infer_instance

/-- Two morphisms into `a⁻¹F` which agree after `CategoryTheory.sheafPullbackRestriction` have
the same inverse image along `b`. -/
public lemma sheafPullback_map_eq_of_comp_sheafPullbackRestriction_eq (e : a ⋙ b ≅ c)
    (F : Sheaf J (Type w)) {Z : Sheaf K (Type w)}
    (σ₁ σ₂ : Z ⟶ (a.sheafPullback (Type w) J K).obj F)
    (h : σ₁ ≫ sheafPullbackRestriction J K L a b c e F =
      σ₂ ≫ sheafPullbackRestriction J K L a b c e F) :
    (b.sheafPullback (Type w) K L).map σ₁ = (b.sheafPullback (Type w) K L).map σ₂ := by
  let adjB := b.sheafAdjunctionContinuous (Type w) K L
  have hcomp : ∀ σ : Z ⟶ (a.sheafPullback (Type w) J K).obj F,
      adjB.homEquiv _ _ ((b.sheafPullback (Type w) K L).map σ ≫
          sheafPullbackRestrictionAdjunct J K L a b c e F) =
        σ ≫ sheafPullbackRestriction J K L a b c e F := by
    intro σ
    rw [adjB.homEquiv_naturality_left]
    exact congrArg _ ((adjB.homEquiv _ _).apply_symm_apply _)
  exact (cancel_mono (sheafPullbackRestrictionAdjunct J K L a b c e F)).mp
    ((adjB.homEquiv _ _).injective ((hcomp σ₁).trans (h.trans (hcomp σ₂).symm)))

variable [HasTerminal D] [HasTerminal E]
  [HasWeakSheafify K (Type w)] [HasWeakSheafify L (Type w)]
  [HasSheafify K (Type w)] [HasTerminal (Sheaf K (Type w))]

/-- **The restriction map on global sections reflects inverse images.** Two global sections of
`a⁻¹F` with the same image under `CategoryTheory.sheafPullbackSectionsRestriction` have the same
inverse image along `b`, as morphisms out of the inverse image of a terminal sheaf. -/
public lemma sheafPullback_map_eq_of_sheafPullbackSectionsRestriction_eq (e : a ⋙ b ≅ c)
    {T : D} (hT : IsTerminal T) (hbT : IsTerminal (b.obj T)) (F : Sheaf J (Type w))
    (s₁ s₂ : (Sheaf.Γ K (Type w)).obj ((a.sheafPullback (Type w) J K).obj F))
    (h : sheafPullbackSectionsRestriction J K L a b c e hT hbT F s₁ =
      sheafPullbackSectionsRestriction J K L a b c e hT hbT F s₂) :
    (b.sheafPullback (Type w) K L).map (Sheaf.ΓEquivHomTerminal K _ s₁) =
      (b.sheafPullback (Type w) K L).map (Sheaf.ΓEquivHomTerminal K _ s₂) := by
  refine sheafPullback_map_eq_of_comp_sheafPullbackRestriction_eq J K L a b c e F _ _ ?_
  rw [← Sheaf.ΓEquivHomTerminal_naturality, ← Sheaf.ΓEquivHomTerminal_naturality]
  exact congrArg _
    (Γ_map_sheafPullbackRestriction_eq_of_sections_eq J K L a b c e hT hbT F s₁ s₂ h)

end Adjunct

end CategoryTheory
