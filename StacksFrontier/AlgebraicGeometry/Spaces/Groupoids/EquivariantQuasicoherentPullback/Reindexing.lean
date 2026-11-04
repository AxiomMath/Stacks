module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivariantPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompIsoAssoc

/-!
# Reindexing and flattening of inverse images of `𝒪`-modules

The category-level pasting and congruence lemmas, and the reindexing and flattening calculus for
the inverse image of `𝒪`-modules on algebraic spaces, that the pullback of equivariant
quasi-coherent modules of Stacks 043U is built from: the reindexing identities in the two
spellings of the development, the flattening of a reindexed conjugated transition morphism
(`AlgebraicGeometry.Space.modulePullbackFlatten_modulePullbackReindex_conjugate`), and the
naturality of a conjugated transition morphism in the module
(`AlgebraicGeometry.Space.modulePullbackConjugate_naturality`).

See `StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivariantQuasicoherentPullback` for the
overview and the implementation notes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj

universe u

/-! ### Pasting and congruence in an arbitrary category -/

namespace CategoryTheory

variable {C : Type*} [Category C]

/-- Congruence of a composite in both factors. -/
theorem comp₂_congr {A B D : C} {f f' : A ⟶ B} {g g' : B ⟶ D} (hf : f = f') (hg : g = g') :
    f ≫ g = f' ≫ g' := by
  rw [hf, hg]

/-- Congruence of a threefold composite in all three factors. -/
theorem comp₃_congr {A B D E : C} {f f' : A ⟶ B} {g g' : B ⟶ D} {h h' : D ⟶ E}
    (hf : f = f') (hg : g = g') (hh : h = h') : f ≫ g ≫ h = f' ≫ g' ≫ h' := by
  rw [hf, hg, hh]

/-- Congruence of a fivefold composite in all five factors. -/
theorem comp₅_congr {A₁ A₂ A₃ A₄ A₅ A₆ : C} {f₁ f₁' : A₁ ⟶ A₂} {f₂ f₂' : A₂ ⟶ A₃}
    {f₃ f₃' : A₃ ⟶ A₄} {f₄ f₄' : A₄ ⟶ A₅} {f₅ f₅' : A₅ ⟶ A₆}
    (h₁ : f₁ = f₁') (h₂ : f₂ = f₂') (h₃ : f₃ = f₃') (h₄ : f₄ = f₄') (h₅ : f₅ = f₅') :
    f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅ = f₁' ≫ f₂' ≫ f₃' ≫ f₄' ≫ f₅' := by
  rw [h₁, h₂, h₃, h₄, h₅]

/-- A fivefold composite bracketed as a transport, a block of three and a transport, read with
all brackets to the right. -/
theorem comp_assoc₅ {A₁ A₂ A₃ A₄ A₅ A₆ : C} (f₁ : A₁ ⟶ A₂) (f₂ : A₂ ⟶ A₃) (f₃ : A₃ ⟶ A₄)
    (f₄ : A₄ ⟶ A₅) (f₅ : A₅ ⟶ A₆) :
    f₁ ≫ (f₂ ≫ f₃ ≫ f₄) ≫ f₅ = f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅ := by
  simp

/-- A morphism is the composite of two identities with it. -/
theorem id_comp_comp_id {A B : C} (f : A ⟶ B) : f = 𝟙 A ≫ f ≫ 𝟙 B := by
  simp

/-- Merging the transports on either side of a morphism sandwiched between four of them. -/
theorem comp_transport_merge {A A' B₁ B₂ D D' : C} (t₁ : A ⟶ A') (t₂ : A' ⟶ B₁) (R : B₁ ⟶ B₂)
    (t₃ : B₂ ⟶ D) (t₄ : D ⟶ D') (k₁ : A ⟶ B₁) (k₂ : B₂ ⟶ D') (h₁ : t₁ ≫ t₂ = k₁)
    (h₂ : t₃ ≫ t₄ = k₂) :
    t₁ ≫ (t₂ ≫ R ≫ t₃) ≫ t₄ = k₁ ≫ R ≫ k₂ := by
  rw [← h₁, ← h₂]
  simp

/-- **Five commuting squares in a row paste into one.** -/
theorem comp_naturality₅ {X₁ X₂ X₃ X₄ X₅ X₆ Y₁ Y₂ Y₃ Y₄ Y₅ Y₆ : C}
    {a₁ : X₁ ⟶ X₂} {a₂ : X₂ ⟶ X₃} {a₃ : X₃ ⟶ X₄} {a₄ : X₄ ⟶ X₅} {a₅ : X₅ ⟶ X₆}
    {b₁ : Y₁ ⟶ Y₂} {b₂ : Y₂ ⟶ Y₃} {b₃ : Y₃ ⟶ Y₄} {b₄ : Y₄ ⟶ Y₅} {b₅ : Y₅ ⟶ Y₆}
    {n₁ : X₁ ⟶ Y₁} {n₂ : X₂ ⟶ Y₂} {n₃ : X₃ ⟶ Y₃} {n₄ : X₄ ⟶ Y₄} {n₅ : X₅ ⟶ Y₅}
    {n₆ : X₆ ⟶ Y₆}
    (h₁ : a₁ ≫ n₂ = n₁ ≫ b₁) (h₂ : a₂ ≫ n₃ = n₂ ≫ b₂) (h₃ : a₃ ≫ n₄ = n₃ ≫ b₃)
    (h₄ : a₄ ≫ n₅ = n₄ ≫ b₄) (h₅ : a₅ ≫ n₆ = n₅ ≫ b₅) :
    (a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅) ≫ n₆ = n₁ ≫ b₁ ≫ b₂ ≫ b₃ ≫ b₄ ≫ b₅ := by
  have e : n₁ ≫ b₁ ≫ b₂ ≫ b₃ ≫ b₄ ≫ b₅ = a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅ ≫ n₆ := by
    rw [reassoc_of% h₁.symm, reassoc_of% h₂.symm, reassoc_of% h₃.symm, reassoc_of% h₄.symm,
      h₅.symm]
  rw [e]
  simp

/-- Conjugating by two isomorphisms and then undoing the conjugation is the identity. -/
theorem Iso.inv_comp_conjugate₃_comp_hom {A B B₁ B₂ D E : C} (u : A ≅ B) (v : D ≅ E)
    (z₁ : B ⟶ B₁) (z₂ : B₁ ⟶ B₂) (z₃ : B₂ ⟶ E) :
    u.inv ≫ (u.hom ≫ z₁ ≫ z₂ ≫ z₃ ≫ v.inv) ≫ v.hom = z₁ ≫ z₂ ≫ z₃ := by
  simp

end CategoryTheory

/-! ### Pasting and sandwich lemmas carried in this file's own namespace

The four lemmas below are general-purpose category glue, but they are the ones this file
introduces, so they are kept out of the root `CategoryTheory` namespace: that namespace is shared
by the whole library, and `CategoryTheory.comp_naturality₃` is already taken by
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuasicoherentColimits.lean`, which states the
same pasting with every equation written the other way round and the conclusion bracketed to the
right. -/

namespace Stacks.AlgebraicGeometry.EquivariantQuasicoherentPullback

variable {C : Type*} [Category C]

/-- **Three commuting squares in a row paste into one**, with the composite along the top row
written first in every equation, which is the orientation of `CategoryTheory.NatTrans.naturality`
and of `CategoryTheory.comp_naturality₅` above. -/
theorem comp_naturality₃_comp_left {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : C}
    {a₁ : X₁ ⟶ X₂} {a₂ : X₂ ⟶ X₃} {a₃ : X₃ ⟶ X₄}
    {b₁ : Y₁ ⟶ Y₂} {b₂ : Y₂ ⟶ Y₃} {b₃ : Y₃ ⟶ Y₄}
    {n₁ : X₁ ⟶ Y₁} {n₂ : X₂ ⟶ Y₂} {n₃ : X₃ ⟶ Y₃} {n₄ : X₄ ⟶ Y₄}
    (h₁ : a₁ ≫ n₂ = n₁ ≫ b₁) (h₂ : a₂ ≫ n₃ = n₂ ≫ b₂) (h₃ : a₃ ≫ n₄ = n₃ ≫ b₃) :
    (a₁ ≫ a₂ ≫ a₃) ≫ n₄ = n₁ ≫ b₁ ≫ b₂ ≫ b₃ := by
  have e : n₁ ≫ b₁ ≫ b₂ ≫ b₃ = a₁ ≫ a₂ ≫ a₃ ≫ n₄ := by
    rw [reassoc_of% h₁.symm, reassoc_of% h₂.symm, h₃.symm]
  rw [e]
  simp

/-- Merging the transports around a pair of morphisms separated by a transport: the outer pairs
of transports merge, and the transport between the two morphisms is left alone. -/
theorem comp_transport_merge₂ {P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ : C}
    (t₁ : P₀ ⟶ P₁) (t₂ : P₁ ⟶ P₂) (x : P₂ ⟶ P₃) (t₃ : P₃ ⟶ P₄) (y : P₄ ⟶ P₅)
    (t₄ : P₅ ⟶ P₆) (t₅ : P₆ ⟶ P₇) (k₁ : P₀ ⟶ P₂) (k₂ : P₅ ⟶ P₇)
    (h₁ : t₁ ≫ t₂ = k₁) (h₂ : t₄ ≫ t₅ = k₂) :
    t₁ ≫ (t₂ ≫ (x ≫ t₃ ≫ y) ≫ t₄) ≫ t₅ = k₁ ≫ x ≫ t₃ ≫ y ≫ k₂ := by
  rw [← h₁, ← h₂]
  simp

/-- A morphism sandwiched between two pairs of mutually inverse morphisms is itself. -/
theorem sandwich_cancel {A A' D D' : C} {t₁ : A ⟶ A'} {s₁ : A' ⟶ A} {t₂ : D ⟶ D'}
    {s₂ : D' ⟶ D} (h₁ : s₁ ≫ t₁ = 𝟙 A') (h₂ : t₂ ≫ s₂ = 𝟙 D) (x : A' ⟶ D) :
    s₁ ≫ (t₁ ≫ x ≫ t₂) ≫ s₂ = x := by
  rw [Category.assoc, Category.assoc, h₂, Category.comp_id, ← Category.assoc, h₁,
    Category.id_comp]

/-- Two sandwiched morphisms whose inner pair of sides cancel compose to the sandwich of their
composite. -/
theorem sandwich_comp_sandwich {A₀ A₁ B₁ B₀ D₁ D₀ : C} (t₁ : A₀ ⟶ A₁) (x : A₁ ⟶ B₁)
    (t₂ : B₁ ⟶ B₀) (t₃ : B₀ ⟶ B₁) (y : B₁ ⟶ D₁) (t₄ : D₁ ⟶ D₀) (h : t₂ ≫ t₃ = 𝟙 B₁) :
    (t₁ ≫ x ≫ t₂) ≫ t₃ ≫ y ≫ t₄ = t₁ ≫ (x ≫ y) ≫ t₄ := by
  simp only [Category.assoc]
  rw [← Category.assoc t₂ t₃, h, Category.id_comp]

end Stacks.AlgebraicGeometry.EquivariantQuasicoherentPullback

open Stacks.AlgebraicGeometry.EquivariantQuasicoherentPullback

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}

/-! ### The reindexing calculus in the two spellings of the development -/

/-- Reindexing the canonical identification of two inverse images along a further morphism is
again such an identification. -/
theorem modulePullbackReindex_pullbackTransport {U V W : AlgebraicSpaces 𝒞 S hS}
    (w : W ⟶ V) {c d : V ⟶ U} (hcd : c = d) (F : Modules.{u, u} 𝒞 S hS U.1 U.2)
    (e : w ≫ c = w ≫ d) :
    modulePullbackReindex w (pullbackTransport F hcd) = pullbackTransport F e := by
  rw [pullbackTransport_eq_eqToHom, pullbackTransport_eq_eqToHom]
  exact modulePullbackReindex_eqToHom w F hcd

/-- Flattening the canonical identification of two inverse images of an inverse image is again
such an identification. -/
theorem modulePullbackFlatten_pullbackTransport {U U' V' : AlgebraicSpaces 𝒞 S hS}
    (g : U' ⟶ U) {c d : V' ⟶ U'} (hcd : c = d) (F : Modules.{u, u} 𝒞 S hS U.1 U.2)
    (e : c ≫ g = d ≫ g) :
    modulePullbackFlatten g
        (pullbackTransport ((modulePullback 𝒞 S hS g).obj F) hcd) = pullbackTransport F e := by
  rw [pullbackTransport_eq_eqToHom, pullbackTransport_eq_eqToHom]
  exact modulePullbackFlatten_eqToHom g F hcd

/-- Two canonical identifications of inverse images compose to a third. -/
theorem pullbackTransport_comp {T X : AlgebraicSpaces 𝒞 S hS}
    (F : Modules.{u, u} 𝒞 S hS X.1 X.2) {f g h : T ⟶ X} (h₁ : f = g) (h₂ : g = h)
    (h₃ : f = h) :
    pullbackTransport F h₁ ≫ pullbackTransport F h₂ = pullbackTransport F h₃ :=
  calc pullbackTransport F h₁ ≫ pullbackTransport F h₂
      = eqToHom (congrArg (fun k : T ⟶ X => (modulePullback 𝒞 S hS k).obj F) h₁) ≫
          eqToHom (congrArg (fun k : T ⟶ X => (modulePullback 𝒞 S hS k).obj F) h₂) :=
        comp₂_congr (pullbackTransport_eq_eqToHom F h₁) (pullbackTransport_eq_eqToHom F h₂)
    _ = eqToHom (congrArg (fun k : T ⟶ X => (modulePullback 𝒞 S hS k).obj F) h₃) :=
        eqToHom_trans _ _
    _ = pullbackTransport F h₃ := (pullbackTransport_eq_eqToHom F h₃).symm

/-- Flattening a fivefold composite. -/
theorem modulePullbackFlatten_comp₅ {U U' V' : AlgebraicSpaces 𝒞 S hS} (g : U' ⟶ U)
    {a₁ a₂ a₃ a₄ a₅ a₆ : V' ⟶ U'} (F : Modules.{u, u} 𝒞 S hS U.1 U.2)
    (α₁ : (modulePullback 𝒞 S hS a₁).obj ((modulePullback 𝒞 S hS g).obj F) ⟶
      (modulePullback 𝒞 S hS a₂).obj ((modulePullback 𝒞 S hS g).obj F))
    (α₂ : (modulePullback 𝒞 S hS a₂).obj ((modulePullback 𝒞 S hS g).obj F) ⟶
      (modulePullback 𝒞 S hS a₃).obj ((modulePullback 𝒞 S hS g).obj F))
    (α₃ : (modulePullback 𝒞 S hS a₃).obj ((modulePullback 𝒞 S hS g).obj F) ⟶
      (modulePullback 𝒞 S hS a₄).obj ((modulePullback 𝒞 S hS g).obj F))
    (α₄ : (modulePullback 𝒞 S hS a₄).obj ((modulePullback 𝒞 S hS g).obj F) ⟶
      (modulePullback 𝒞 S hS a₅).obj ((modulePullback 𝒞 S hS g).obj F))
    (α₅ : (modulePullback 𝒞 S hS a₅).obj ((modulePullback 𝒞 S hS g).obj F) ⟶
      (modulePullback 𝒞 S hS a₆).obj ((modulePullback 𝒞 S hS g).obj F)) :
    modulePullbackFlatten g (α₁ ≫ α₂ ≫ α₃ ≫ α₄ ≫ α₅) =
      modulePullbackFlatten g α₁ ≫ modulePullbackFlatten g α₂ ≫
        modulePullbackFlatten g α₃ ≫ modulePullbackFlatten g α₄ ≫
        modulePullbackFlatten g α₅ :=
  calc modulePullbackFlatten g (α₁ ≫ α₂ ≫ α₃ ≫ α₄ ≫ α₅)
      = modulePullbackFlatten g α₁ ≫ modulePullbackFlatten g (α₂ ≫ α₃ ≫ α₄ ≫ α₅) :=
        modulePullbackFlatten_comp_morphism g _ _
    _ = modulePullbackFlatten g α₁ ≫
          (modulePullbackFlatten g α₂ ≫ modulePullbackFlatten g (α₃ ≫ α₄ ≫ α₅)) :=
        congrArg (fun x => modulePullbackFlatten g α₁ ≫ x)
          (modulePullbackFlatten_comp_morphism g _ _)
    _ = modulePullbackFlatten g α₁ ≫ modulePullbackFlatten g α₂ ≫
          (modulePullbackFlatten g α₃ ≫ modulePullbackFlatten g (α₄ ≫ α₅)) :=
        congrArg
          (fun x => modulePullbackFlatten g α₁ ≫ modulePullbackFlatten g α₂ ≫ x)
          (modulePullbackFlatten_comp_morphism g _ _)
    _ = modulePullbackFlatten g α₁ ≫ modulePullbackFlatten g α₂ ≫
          modulePullbackFlatten g α₃ ≫
          (modulePullbackFlatten g α₄ ≫ modulePullbackFlatten g α₅) :=
        congrArg
          (fun x => modulePullbackFlatten g α₁ ≫ modulePullbackFlatten g α₂ ≫
            modulePullbackFlatten g α₃ ≫ x)
          (modulePullbackFlatten_comp_morphism g _ _)

/-- Reindexing a transition morphism is natural in the module. -/
theorem modulePullbackReindex_naturality {U V W : AlgebraicSpaces 𝒞 S hS} (f : W ⟶ V)
    {a b : V ⟶ U} {M N : Modules.{u, u} 𝒞 S hS U.1 U.2}
    {α : (modulePullback 𝒞 S hS a).obj M ⟶ (modulePullback 𝒞 S hS b).obj M}
    {β : (modulePullback 𝒞 S hS a).obj N ⟶ (modulePullback 𝒞 S hS b).obj N}
    (φ : M ⟶ N)
    (hφ : α ≫ (modulePullback 𝒞 S hS b).map φ = (modulePullback 𝒞 S hS a).map φ ≫ β) :
    (modulePullback 𝒞 S hS (f ≫ a)).map φ ≫ modulePullbackReindex f β =
      modulePullbackReindex f α ≫ (modulePullback 𝒞 S hS (f ≫ b)).map φ := by
  simp only [modulePullbackReindex, Category.assoc]
  rw [NatTrans.naturality_assoc]
  show _ ≫ (modulePullback 𝒞 S hS f).map ((modulePullback 𝒞 S hS a).map φ) ≫ _ = _
  rw [← Functor.map_comp_assoc, ← hφ, Functor.map_comp]
  simp only [Category.assoc]
  rw [← (modulePullbackCompIso 𝒞 S hS f b).hom.naturality φ]
  rfl

/-- **Reindexing twice is reindexing along the composite**, with the composite given as a
separate morphism together with an equation identifying it.  Taking the composite abstractly is
what makes this usable: a statement that mentions `w ≫ m` inside
`(AlgebraicGeometry.Space.modulePullback _).obj` forces the elaborator to reconcile
`w ≫ m ≫ a` with `(w ≫ m) ≫ a` underneath the inverse image, which does not terminate. -/
theorem modulePullbackReindex_comp' (hassoc : ModulePullbackCompIsoAssoc 𝒞 S hS)
    {U V W W' : AlgebraicSpaces 𝒞 S hS} (w : W' ⟶ W) (m : W ⟶ V) (n : W' ⟶ V)
    (hn : w ≫ m = n) {a b : V ⟶ U} {M : Modules.{u, u} 𝒞 S hS U.1 U.2}
    (α : (modulePullback 𝒞 S hS a).obj M ⟶ (modulePullback 𝒞 S hS b).obj M)
    (e₁ : w ≫ m ≫ a = n ≫ a) (e₂ : n ≫ b = w ≫ m ≫ b) :
    modulePullbackReindex w (modulePullbackReindex m α) =
      pullbackTransport M e₁ ≫ modulePullbackReindex n α ≫ pullbackTransport M e₂ := by
  subst hn
  exact (hassoc.modulePullbackReindex_comp w m α).trans (id_comp_comp_id _)

/-! ### Flattening a reindexed conjugated transition morphism -/

/-- Reindexing a transport, a reindexed morphism and a transport in a row splits into the
reindexed pieces. -/
private theorem modulePullbackReindex_transport_comp
    {U V V' W : AlgebraicSpaces 𝒞 S hS} {c d : V' ⟶ U} {a b : V ⟶ U} (m : V' ⟶ V)
    (ha : c = m ≫ a) (hb : m ≫ b = d) (F : Modules.{u, u} 𝒞 S hS U.1 U.2)
    (α : (modulePullback 𝒞 S hS a).obj F ⟶ (modulePullback 𝒞 S hS b).obj F) (w : W ⟶ V')
    (e₁ : w ≫ c = w ≫ m ≫ a) (e₂ : w ≫ m ≫ b = w ≫ d) :
    modulePullbackReindex w (pullbackTransport F ha ≫
        modulePullbackReindex m α ≫ pullbackTransport F hb) =
      pullbackTransport F e₁ ≫ modulePullbackReindex w (modulePullbackReindex m α) ≫
        pullbackTransport F e₂ :=
  (modulePullbackReindex_comp_morphism w _ _).trans
    ((congrArg (fun x => modulePullbackReindex w (pullbackTransport F ha) ≫ x)
          (modulePullbackReindex_comp_morphism w _ _)).trans
      (comp₃_congr (modulePullbackReindex_pullbackTransport w ha F e₁) rfl
        (modulePullbackReindex_pullbackTransport w hb F e₂)))

/-- Contracting two reindexings inside a transport sandwich, with the composite given as a
separate morphism `n` together with an equation identifying it. -/
private theorem pullbackTransport_reindex_reindex_transport
    (hassoc : ModulePullbackCompIsoAssoc 𝒞 S hS)
    {U V V' W : AlgebraicSpaces 𝒞 S hS} {c d : V' ⟶ U} {a b : V ⟶ U} (m : V' ⟶ V)
    (F : Modules.{u, u} 𝒞 S hS U.1 U.2)
    (α : (modulePullback 𝒞 S hS a).obj F ⟶ (modulePullback 𝒞 S hS b).obj F)
    (w : W ⟶ V') (n : W ⟶ V) (hn : w ≫ m = n)
    (e₁ : w ≫ c = w ≫ m ≫ a) (e₂ : w ≫ m ≫ b = w ≫ d)
    (E₁ : w ≫ c = n ≫ a) (E₂ : n ≫ b = w ≫ d) :
    pullbackTransport F e₁ ≫ modulePullbackReindex w (modulePullbackReindex m α) ≫
        pullbackTransport F e₂ =
      pullbackTransport F E₁ ≫ modulePullbackReindex n α ≫ pullbackTransport F E₂ :=
  have e₃ : w ≫ m ≫ a = n ≫ a := congrArg (· ≫ a) hn
  have e₄ : n ≫ b = w ≫ m ≫ b := congrArg (· ≫ b) hn.symm
  (comp₃_congr rfl (modulePullbackReindex_comp' hassoc w m n hn α e₃ e₄) rfl).trans
    (comp_transport_merge _ _ _ _ _ _ _ (pullbackTransport_comp F e₁ e₃ E₁)
      (pullbackTransport_comp F e₄ e₂ E₂))

/-- **Flattening a reindexed conjugated transition morphism is reindexing the original one.**

Let `g : U' ⟶ U` and let `m : V' ⟶ V` carry a parallel pair `a' b' : V' ⟶ U'` to a parallel pair
`a b : V ⟶ U`, in the sense that `a' ≫ g = m ≫ a` and `b' ≫ g = m ≫ b`.  A transition morphism
`α : a^*ℱ ⟶ b^*ℱ` then has a conjugate transition morphism on `g^*ℱ`, namely the reindexing of
`α` along `m` read through the comparisons of Stacks 03LU and the two squares; this is the shape
of `AlgebraicGeometry.Space.equivariantModulePullbackTransition`.  Reindexing that conjugate
along a further morphism `w` and flattening along `g` reindexes `α` along `m` and then `w`. -/
theorem modulePullbackFlatten_modulePullbackReindex_conjugate
    (hassoc : ModulePullbackCompIsoAssoc 𝒞 S hS)
    {U U' V V' W : AlgebraicSpaces 𝒞 S hS}
    (g : U' ⟶ U) {a b : V ⟶ U} {a' b' : V' ⟶ U'} (m : V' ⟶ V)
    (ha : a' ≫ g = m ≫ a) (hb : b' ≫ g = m ≫ b)
    (F : Modules.{u, u} 𝒞 S hS U.1 U.2)
    (α : (modulePullback 𝒞 S hS a).obj F ⟶ (modulePullback 𝒞 S hS b).obj F) (w : W ⟶ V')
    (e₁ : w ≫ a' ≫ g = w ≫ m ≫ a) (e₂ : w ≫ m ≫ b = w ≫ b' ≫ g) :
    modulePullbackFlatten g (modulePullbackReindex w
        ((modulePullbackCompIso 𝒞 S hS a' g).hom.app F ≫ pullbackTransport F ha ≫
          modulePullbackReindex m α ≫ pullbackTransport F hb.symm ≫
          (modulePullbackCompIso 𝒞 S hS b' g).inv.app F)) =
      pullbackTransport F e₁ ≫
        modulePullbackReindex w (modulePullbackReindex m α) ≫ pullbackTransport F e₂ :=
  have hcancel :
      modulePullbackFlatten g
          ((modulePullbackCompIso 𝒞 S hS a' g).hom.app F ≫ pullbackTransport F ha ≫
            modulePullbackReindex m α ≫ pullbackTransport F hb.symm ≫
            (modulePullbackCompIso 𝒞 S hS b' g).inv.app F) =
        pullbackTransport F ha ≫ modulePullbackReindex m α ≫ pullbackTransport F hb.symm :=
    Iso.inv_comp_conjugate₃_comp_hom ((modulePullbackCompIso 𝒞 S hS a' g).app F)
      ((modulePullbackCompIso 𝒞 S hS b' g).app F) (pullbackTransport F ha)
      (modulePullbackReindex m α) (pullbackTransport F hb.symm)
  calc modulePullbackFlatten g (modulePullbackReindex w
          ((modulePullbackCompIso 𝒞 S hS a' g).hom.app F ≫ pullbackTransport F ha ≫
            modulePullbackReindex m α ≫ pullbackTransport F hb.symm ≫
            (modulePullbackCompIso 𝒞 S hS b' g).inv.app F))
      = modulePullbackReindex w (modulePullbackFlatten g
          ((modulePullbackCompIso 𝒞 S hS a' g).hom.app F ≫ pullbackTransport F ha ≫
            modulePullbackReindex m α ≫ pullbackTransport F hb.symm ≫
            (modulePullbackCompIso 𝒞 S hS b' g).inv.app F)) :=
        hassoc.modulePullbackFlatten_reindex w g _
    _ = modulePullbackReindex w (pullbackTransport F ha ≫ modulePullbackReindex m α ≫
          pullbackTransport F hb.symm) := congrArg (fun x => modulePullbackReindex w x) hcancel
    _ = pullbackTransport F e₁ ≫
          modulePullbackReindex w (modulePullbackReindex m α) ≫ pullbackTransport F e₂ :=
        modulePullbackReindex_transport_comp m ha hb.symm F α w e₁ e₂

/-- **Flattening a reindexed conjugated transition morphism, read as a transport, a reindexing
and a transport.**

This is `AlgebraicGeometry.Space.modulePullbackFlatten_modulePullbackReindex_conjugate` with the
two reindexings contracted: the composite `w ≫ m` is given as a separate morphism `n` together
with an equation identifying it, and the two equal composites on either side are identified by
the canonical transports.  It is the shape in which the inverse image of an equivariant module
consumes the calculus, and the conjugate is written out rather than named, because a defeq
obligation with a definition on one side and a composite of `𝒪`-module morphisms on the other
does not terminate; see the implementation notes. -/
theorem modulePullbackFlatten_reindex_conjugate
    (hassoc : ModulePullbackCompIsoAssoc 𝒞 S hS)
    {U U' V V' W : AlgebraicSpaces 𝒞 S hS}
    (g : U' ⟶ U) {a b : V ⟶ U} {a' b' : V' ⟶ U'} (m : V' ⟶ V)
    (ha : a' ≫ g = m ≫ a) (hb : b' ≫ g = m ≫ b)
    (F : Modules.{u, u} 𝒞 S hS U.1 U.2)
    (α : (modulePullback 𝒞 S hS a).obj F ⟶ (modulePullback 𝒞 S hS b).obj F)
    (w : W ⟶ V') (n : W ⟶ V) (hn : w ≫ m = n)
    (E₁ : w ≫ a' ≫ g = n ≫ a) (E₂ : n ≫ b = w ≫ b' ≫ g) :
    modulePullbackFlatten g (modulePullbackReindex w
        ((modulePullbackCompIso 𝒞 S hS a' g).hom.app F ≫ pullbackTransport F ha ≫
          modulePullbackReindex m α ≫ pullbackTransport F hb.symm ≫
          (modulePullbackCompIso 𝒞 S hS b' g).inv.app F)) =
      pullbackTransport F E₁ ≫ modulePullbackReindex n α ≫ pullbackTransport F E₂ :=
  (modulePullbackFlatten_modulePullbackReindex_conjugate hassoc g m ha hb F α w
      (congrArg (w ≫ ·) ha) (congrArg (w ≫ ·) hb.symm)).trans
    (pullbackTransport_reindex_reindex_transport hassoc m F α w n hn _ _ E₁ E₂)

/-- **A conjugated transition morphism is natural in the module.**  Five commuting squares — the
two comparisons of Stacks 03LU, the two transports and the naturality of reindexing — paste into
one. -/
theorem modulePullbackConjugate_naturality
    {U U' V V' : AlgebraicSpaces 𝒞 S hS} (g : U' ⟶ U) {a b : V ⟶ U} {a' b' : V' ⟶ U'}
    (m : V' ⟶ V) (ha : a' ≫ g = m ≫ a) (hb : b' ≫ g = m ≫ b)
    {M N : Modules.{u, u} 𝒞 S hS U.1 U.2}
    (α : (modulePullback 𝒞 S hS a).obj M ⟶ (modulePullback 𝒞 S hS b).obj M)
    (β : (modulePullback 𝒞 S hS a).obj N ⟶ (modulePullback 𝒞 S hS b).obj N)
    (φ : M ⟶ N)
    (hφ : α ≫ (modulePullback 𝒞 S hS b).map φ = (modulePullback 𝒞 S hS a).map φ ≫ β) :
    ((modulePullbackCompIso 𝒞 S hS a' g).hom.app M ≫ pullbackTransport M ha ≫
        modulePullbackReindex m α ≫ pullbackTransport M hb.symm ≫
        (modulePullbackCompIso 𝒞 S hS b' g).inv.app M) ≫
          (modulePullback 𝒞 S hS b').map ((modulePullback 𝒞 S hS g).map φ) =
      (modulePullback 𝒞 S hS a').map ((modulePullback 𝒞 S hS g).map φ) ≫
        (modulePullbackCompIso 𝒞 S hS a' g).hom.app N ≫ pullbackTransport N ha ≫
          modulePullbackReindex m β ≫ pullbackTransport N hb.symm ≫
          (modulePullbackCompIso 𝒞 S hS b' g).inv.app N :=
  comp_naturality₅ ((modulePullbackCompIso 𝒞 S hS a' g).hom.naturality φ).symm
    (pullbackTransport_naturality φ ha).symm
    (modulePullbackReindex_naturality m φ hφ).symm
    (pullbackTransport_naturality φ hb.symm).symm
    ((modulePullbackCompIso 𝒞 S hS b' g).inv.naturality φ).symm

/-- **Reindexing a transport, a reindexed morphism and a transport in a row.**  The transports
are absorbed into the two ends and the two reindexings contract, with the composite given as a
separate morphism `n` together with an equation identifying it. -/
theorem modulePullbackReindex_transport_sandwich
    (hassoc : ModulePullbackCompIsoAssoc 𝒞 S hS)
    {U V V' W : AlgebraicSpaces 𝒞 S hS} {c d : V' ⟶ U} {a b : V ⟶ U} (m : V' ⟶ V)
    (ha : c = m ≫ a) (hb : m ≫ b = d) (F : Modules.{u, u} 𝒞 S hS U.1 U.2)
    (α : (modulePullback 𝒞 S hS a).obj F ⟶ (modulePullback 𝒞 S hS b).obj F)
    (w : W ⟶ V') (n : W ⟶ V) (hn : w ≫ m = n)
    (E₁ : w ≫ c = n ≫ a) (E₂ : n ≫ b = w ≫ d) :
    modulePullbackReindex w (pullbackTransport F ha ≫
        modulePullbackReindex m α ≫ pullbackTransport F hb) =
      pullbackTransport F E₁ ≫ modulePullbackReindex n α ≫ pullbackTransport F E₂ :=
  (modulePullbackReindex_transport_comp m ha hb F α w (congrArg (w ≫ ·) ha)
      (congrArg (w ≫ ·) hb)).trans
    (pullbackTransport_reindex_reindex_transport hassoc m F α w n hn _ _ E₁ E₂)

/-- **Unflattening a morphism between two inverse images is natural in the module.** -/
theorem modulePullbackUnflatten_naturality {U U' V : AlgebraicSpaces 𝒞 S hS} (g : U' ⟶ U)
    {a b : V ⟶ U'} {M N : Modules.{u, u} 𝒞 S hS U.1 U.2} (φ : M ⟶ N)
    (ζ : (modulePullback 𝒞 S hS (a ≫ g)).obj M ⟶ (modulePullback 𝒞 S hS (b ≫ g)).obj M)
    (ξ : (modulePullback 𝒞 S hS (a ≫ g)).obj N ⟶ (modulePullback 𝒞 S hS (b ≫ g)).obj N)
    (hζ : ζ ≫ (modulePullback 𝒞 S hS (b ≫ g)).map φ =
      (modulePullback 𝒞 S hS (a ≫ g)).map φ ≫ ξ) :
    modulePullbackUnflatten g ζ ≫
        (modulePullback 𝒞 S hS b).map ((modulePullback 𝒞 S hS g).map φ) =
      (modulePullback 𝒞 S hS a).map ((modulePullback 𝒞 S hS g).map φ) ≫
        modulePullbackUnflatten g ξ := by
  simp only [modulePullbackUnflatten]
  exact comp_naturality₃_comp_left ((modulePullbackCompIso 𝒞 S hS a g).hom.naturality φ).symm hζ
    ((modulePullbackCompIso 𝒞 S hS b g).inv.naturality φ).symm

/-- **A transport, a reindexed morphism and a transport in a row are natural in the module.** -/
theorem transportReindexTransport_naturality {U V V' : AlgebraicSpaces 𝒞 S hS}
    {c d : V' ⟶ U} {a b : V ⟶ U} (m : V' ⟶ V) (ha : c = m ≫ a) (hb : m ≫ b = d)
    {M N : Modules.{u, u} 𝒞 S hS U.1 U.2}
    (α : (modulePullback 𝒞 S hS a).obj M ⟶ (modulePullback 𝒞 S hS b).obj M)
    (β : (modulePullback 𝒞 S hS a).obj N ⟶ (modulePullback 𝒞 S hS b).obj N)
    (φ : M ⟶ N)
    (hφ : α ≫ (modulePullback 𝒞 S hS b).map φ = (modulePullback 𝒞 S hS a).map φ ≫ β) :
    (pullbackTransport M ha ≫ modulePullbackReindex m α ≫ pullbackTransport M hb) ≫
        (modulePullback 𝒞 S hS d).map φ =
      (modulePullback 𝒞 S hS c).map φ ≫
        pullbackTransport N ha ≫ modulePullbackReindex m β ≫ pullbackTransport N hb :=
  comp_naturality₃_comp_left (pullbackTransport_naturality φ ha).symm
    (modulePullbackReindex_naturality m φ hφ).symm
    (pullbackTransport_naturality φ hb).symm

/-- The composite of two reindexings of a transition morphism, as a chain of `≫`. -/
theorem transitionPair_eq_comp {U V W : AlgebraicSpaces 𝒞 S hS}
    (F : Modules.{u, u} 𝒞 S hS U.1 U.2) {a b : V ⟶ U}
    (α : (modulePullback 𝒞 S hS a).obj F ⟶ (modulePullback 𝒞 S hS b).obj F) (p q : W ⟶ V)
    (hm : p ≫ b = q ≫ a) :
    transitionPair 𝒞 S hS F α p q hm =
      modulePullbackReindex p α ≫ pullbackTransport F hm ≫ modulePullbackReindex q α :=
  (comp₃_eq (transitionReindex 𝒞 S hS F α p) (pullbackTransport F hm)
      (transitionReindex 𝒞 S hS F α q)).trans
    (comp₃_congr (transitionReindex_eq_modulePullbackReindex F α p) rfl
      (transitionReindex_eq_modulePullbackReindex F α q))

/-- The right-hand side of a cocycle condition, as a chain of `≫`. -/
theorem transitionComposite_eq_comp {U V W : AlgebraicSpaces 𝒞 S hS}
    (F : Modules.{u, u} 𝒞 S hS U.1 U.2) {a b : V ⟶ U}
    (α : (modulePullback 𝒞 S hS a).obj F ⟶ (modulePullback 𝒞 S hS b).obj F) (p q r : W ⟶ V)
    (ht : r ≫ a = p ≫ a) (hm : p ≫ b = q ≫ a) (hs : r ≫ b = q ≫ b) :
    transitionComposite 𝒞 S hS F α p q r ht hm hs =
      pullbackTransport F ht ≫
        (modulePullbackReindex p α ≫ pullbackTransport F hm ≫
          modulePullbackReindex q α) ≫
        pullbackTransport F hs.symm :=
  (comp₃_eq (pullbackTransport F ht) (transitionPair 𝒞 S hS F α p q hm)
      (pullbackTransport F hs.symm)).trans
    (comp₃_congr rfl (transitionPair_eq_comp F α p q hm) rfl)

end AlgebraicGeometry.Space

end
