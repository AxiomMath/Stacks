module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivariantQuasicoherentPullback.Reindexing

/-!
# Transferring the laws of a transition morphism along flattening

The transfer of the reindexing calculus and of the cocycle law along flattening, for abstract
morphisms of algebraic spaces, and the named flattening
`AlgebraicGeometry.Space.modulePullbackFlatten'`, which takes the two composites along the
connecting morphism as separate morphisms together with equations identifying them, so that no
statement mentions a bracketing underneath the inverse image.  The main result is
`AlgebraicGeometry.Space.modulePullbackReindex_cocycle_of_flatten`.

See `StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivariantQuasicoherentPullback` for the
overview and the section on the named flattening.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj

universe u

open Stacks.AlgebraicGeometry.EquivariantQuasicoherentPullback

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}

/-! ### Transferring the laws of a transition morphism along flattening -/

section CocycleTransfer

variable {U U' V V' W : AlgebraicSpaces 𝒞 S hS} (g : U' ⟶ U) {a b : V ⟶ U} {a' b' : V' ⟶ U'}
  (m : V' ⟶ V) {ha : a' ≫ g = m ≫ a} {hb : m ≫ b = b' ≫ g}
  (F : Modules.{u, u} 𝒞 S hS U.1 U.2)
  (α : (modulePullback 𝒞 S hS a).obj F ⟶ (modulePullback 𝒞 S hS b).obj F)
  (β : (modulePullback 𝒞 S hS a').obj ((modulePullback 𝒞 S hS g).obj F) ⟶
    (modulePullback 𝒞 S hS b').obj ((modulePullback 𝒞 S hS g).obj F))

/-- Two parallel morphisms matched by `m`, read after a test morphism: from `a' ≫ g = m ≫ a` and
`x ≫ m = x'` one gets `x ≫ a' ≫ g = x' ≫ a`. -/
theorem comp_comp_eq_of_matched (ha : a' ≫ g = m ≫ a) {x : W ⟶ V'} {x' : W ⟶ V}
    (hx : x ≫ m = x') : x ≫ a' ≫ g = x' ≫ a := by
  subst hx
  rw [ha, Category.assoc]

/-- **Flattening the reindexing of a conjugated transition morphism along a test morphism.**

If the flattening of `β` is the reindexing of `α` along `m` read between the two transports, then
the flattening of the reindexing of `β` along `w` is the reindexing of `α` along the image of `w`
under `m`, again read between two transports. -/
theorem modulePullbackFlatten_reindex_of_flatten
    (hassoc : ModulePullbackCompIsoAssoc 𝒞 S hS)
    (hβ : modulePullbackFlatten g β =
      pullbackTransport F ha ≫ modulePullbackReindex m α ≫ pullbackTransport F hb)
    (w : W ⟶ V') (n : W ⟶ V) (hn : w ≫ m = n)
    (E₁ : w ≫ a' ≫ g = n ≫ a) (E₂ : n ≫ b = w ≫ b' ≫ g) :
    modulePullbackFlatten g (modulePullbackReindex w β) =
      pullbackTransport F E₁ ≫ modulePullbackReindex n α ≫ pullbackTransport F E₂ :=
  (hassoc.modulePullbackFlatten_reindex w g β).trans
    ((congrArg (modulePullbackReindex w) hβ).trans
      (modulePullbackReindex_transport_sandwich hassoc m ha hb F α w n hn E₁ E₂))

/-- **The left-hand side of a cocycle law for `β`, flattened**: the reindexings of `α` along the
two images under `m` of the first two test morphisms, between three transports. -/
theorem modulePullbackFlatten_reindex_cocycle_left
    (hassoc : ModulePullbackCompIsoAssoc 𝒞 S hS)
    (hβ : modulePullbackFlatten g β =
      pullbackTransport F ha ≫ modulePullbackReindex m α ≫ pullbackTransport F hb)
    (R : W ⟶ V') (P' Q' R' : W ⟶ V) (hR : R ≫ m = R')
    (ht' : R' ≫ a = P' ≫ a) (hm' : P' ≫ b = Q' ≫ a) (hs' : R' ≫ b = Q' ≫ b)
    (hcoc : modulePullbackReindex R' α =
      pullbackTransport F ht' ≫
        (modulePullbackReindex P' α ≫ pullbackTransport F hm' ≫
          modulePullbackReindex Q' α) ≫
        pullbackTransport F hs'.symm)
    (K₁ : R ≫ a' ≫ g = P' ≫ a) (K₃ : Q' ≫ b = R ≫ b' ≫ g) :
    modulePullbackFlatten g (modulePullbackReindex R β) =
      pullbackTransport F K₁ ≫ modulePullbackReindex P' α ≫ pullbackTransport F hm' ≫
        modulePullbackReindex Q' α ≫ pullbackTransport F K₃ :=
  (modulePullbackFlatten_reindex_of_flatten g m F α β hassoc hβ R R' hR
        (comp_comp_eq_of_matched g m ha hR)
        (comp_comp_eq_of_matched g m hb.symm hR).symm).trans
    ((comp₃_congr rfl hcoc rfl).trans
      (comp_transport_merge₂ _ _ _ _ _ _ _ _ _
        (pullbackTransport_comp F (comp_comp_eq_of_matched g m ha hR) ht' K₁)
        (pullbackTransport_comp F hs'.symm
          (comp_comp_eq_of_matched g m hb.symm hR).symm K₃)))

end CocycleTransfer

/-! ### Flattening with the composites named -/

section FlattenNamed

/-- Two opposite canonical identifications compose to the identity. -/
theorem pullbackTransport_comp_self {T X : AlgebraicSpaces 𝒞 S hS}
    (F : Modules.{u, u} 𝒞 S hS X.1 X.2) {a b : T ⟶ X} (h₁ : a = b) (h₂ : b = a) :
    pullbackTransport F h₁ ≫ pullbackTransport F h₂ = 𝟙 _ :=
  pullbackTransport_comp F h₁ h₂ rfl

variable {U U' V V' W : AlgebraicSpaces 𝒞 S hS}

/-- **Flattening a morphism between two inverse images of an inverse image, with the two
composites along `g` given as separate morphisms `c` and `d` together with equations
identifying them.**  The result is a morphism `c^*M ⟶ d^*M`, so no bracketing of a composite
occurs underneath the inverse image; see the implementation notes. -/
def modulePullbackFlatten' (g : U' ⟶ U) {a b : V' ⟶ U'} {c d : V' ⟶ U}
    (hc : a ≫ g = c) (hd : b ≫ g = d) {M : Modules.{u, u} 𝒞 S hS U.1 U.2}
    (α : (modulePullback 𝒞 S hS a).obj ((modulePullback 𝒞 S hS g).obj M) ⟶
      (modulePullback 𝒞 S hS b).obj ((modulePullback 𝒞 S hS g).obj M)) :
    (modulePullback 𝒞 S hS c).obj M ⟶ (modulePullback 𝒞 S hS d).obj M :=
  comp₃ (pullbackTransport M hc.symm) (modulePullbackFlatten g α) (pullbackTransport M hd)

/-- The named flattening is the flattening between the two canonical identifications. -/
theorem modulePullbackFlatten'_eq_comp (g : U' ⟶ U) {a b : V' ⟶ U'} {c d : V' ⟶ U}
    (hc : a ≫ g = c) (hd : b ≫ g = d) {M : Modules.{u, u} 𝒞 S hS U.1 U.2}
    (α : (modulePullback 𝒞 S hS a).obj ((modulePullback 𝒞 S hS g).obj M) ⟶
      (modulePullback 𝒞 S hS b).obj ((modulePullback 𝒞 S hS g).obj M)) :
    modulePullbackFlatten' g hc hd α =
      pullbackTransport M hc.symm ≫ modulePullbackFlatten g α ≫ pullbackTransport M hd :=
  comp₃_eq (pullbackTransport M hc.symm) (modulePullbackFlatten g α) (pullbackTransport M hd)

/-- Flattening is the named flattening read back between the two canonical identifications. -/
theorem modulePullbackFlatten_eq_conjugate_flatten' (g : U' ⟶ U) {a b : V' ⟶ U'}
    {c d : V' ⟶ U} (hc : a ≫ g = c) (hd : b ≫ g = d)
    {M : Modules.{u, u} 𝒞 S hS U.1 U.2}
    (α : (modulePullback 𝒞 S hS a).obj ((modulePullback 𝒞 S hS g).obj M) ⟶
      (modulePullback 𝒞 S hS b).obj ((modulePullback 𝒞 S hS g).obj M)) :
    modulePullbackFlatten g α =
      pullbackTransport M hc ≫ modulePullbackFlatten' g hc hd α ≫
        pullbackTransport M hd.symm :=
  (sandwich_cancel (pullbackTransport_comp_self M hc hc.symm)
      (pullbackTransport_comp_self M hd hd.symm) (modulePullbackFlatten g α)).symm.trans
    (comp₃_congr rfl (modulePullbackFlatten'_eq_comp g hc hd α).symm rfl)

/-- **The named flattening is injective.** -/
theorem modulePullbackFlatten'_injective (g : U' ⟶ U) {a b : V' ⟶ U'} {c d : V' ⟶ U}
    (hc : a ≫ g = c) (hd : b ≫ g = d) {M : Modules.{u, u} 𝒞 S hS U.1 U.2} :
    Function.Injective (modulePullbackFlatten' g hc hd (M := M)) := fun α α' h =>
  modulePullbackFlatten_injective g
    ((modulePullbackFlatten_eq_conjugate_flatten' g hc hd α).trans
      ((comp₃_congr rfl h rfl).trans
        (modulePullbackFlatten_eq_conjugate_flatten' g hc hd α').symm))

/-- **The named flattening is compatible with composition.** -/
theorem modulePullbackFlatten'_comp_morphism (g : U' ⟶ U) {a b e : V' ⟶ U'}
    {c d k : V' ⟶ U} (hc : a ≫ g = c) (hd : b ≫ g = d) (hk : e ≫ g = k)
    {M : Modules.{u, u} 𝒞 S hS U.1 U.2}
    (α : (modulePullback 𝒞 S hS a).obj ((modulePullback 𝒞 S hS g).obj M) ⟶
      (modulePullback 𝒞 S hS b).obj ((modulePullback 𝒞 S hS g).obj M))
    (α' : (modulePullback 𝒞 S hS b).obj ((modulePullback 𝒞 S hS g).obj M) ⟶
      (modulePullback 𝒞 S hS e).obj ((modulePullback 𝒞 S hS g).obj M)) :
    modulePullbackFlatten' g hc hk (α ≫ α') =
      modulePullbackFlatten' g hc hd α ≫ modulePullbackFlatten' g hd hk α' :=
  (modulePullbackFlatten'_eq_comp g hc hk (α ≫ α')).trans
    ((comp₃_congr rfl (modulePullbackFlatten_comp_morphism g α α') rfl).trans
      ((sandwich_comp_sandwich (pullbackTransport M hc.symm) (modulePullbackFlatten g α)
            (pullbackTransport M hd) (pullbackTransport M hd.symm)
            (modulePullbackFlatten g α') (pullbackTransport M hk)
            (pullbackTransport_comp_self M hd hd.symm)).symm.trans
        (comp₂_congr (modulePullbackFlatten'_eq_comp g hc hd α)
          (modulePullbackFlatten'_eq_comp g hd hk α')).symm))

/-- The named flattening of a fivefold composite. -/
theorem modulePullbackFlatten'_comp₅ (g : U' ⟶ U) {a₁ a₂ a₃ a₄ a₅ a₆ : V' ⟶ U'}
    {c₁ c₂ c₃ c₄ c₅ c₆ : V' ⟶ U} (h₁ : a₁ ≫ g = c₁) (h₂ : a₂ ≫ g = c₂)
    (h₃ : a₃ ≫ g = c₃) (h₄ : a₄ ≫ g = c₄) (h₅ : a₅ ≫ g = c₅) (h₆ : a₆ ≫ g = c₆)
    {M : Modules.{u, u} 𝒞 S hS U.1 U.2}
    (α₁ : (modulePullback 𝒞 S hS a₁).obj ((modulePullback 𝒞 S hS g).obj M) ⟶
      (modulePullback 𝒞 S hS a₂).obj ((modulePullback 𝒞 S hS g).obj M))
    (α₂ : (modulePullback 𝒞 S hS a₂).obj ((modulePullback 𝒞 S hS g).obj M) ⟶
      (modulePullback 𝒞 S hS a₃).obj ((modulePullback 𝒞 S hS g).obj M))
    (α₃ : (modulePullback 𝒞 S hS a₃).obj ((modulePullback 𝒞 S hS g).obj M) ⟶
      (modulePullback 𝒞 S hS a₄).obj ((modulePullback 𝒞 S hS g).obj M))
    (α₄ : (modulePullback 𝒞 S hS a₄).obj ((modulePullback 𝒞 S hS g).obj M) ⟶
      (modulePullback 𝒞 S hS a₅).obj ((modulePullback 𝒞 S hS g).obj M))
    (α₅ : (modulePullback 𝒞 S hS a₅).obj ((modulePullback 𝒞 S hS g).obj M) ⟶
      (modulePullback 𝒞 S hS a₆).obj ((modulePullback 𝒞 S hS g).obj M)) :
    modulePullbackFlatten' g h₁ h₆ (α₁ ≫ α₂ ≫ α₃ ≫ α₄ ≫ α₅) =
      modulePullbackFlatten' g h₁ h₂ α₁ ≫ modulePullbackFlatten' g h₂ h₃ α₂ ≫
        modulePullbackFlatten' g h₃ h₄ α₃ ≫ modulePullbackFlatten' g h₄ h₅ α₄ ≫
        modulePullbackFlatten' g h₅ h₆ α₅ :=
  calc modulePullbackFlatten' g h₁ h₆ (α₁ ≫ α₂ ≫ α₃ ≫ α₄ ≫ α₅)
      = modulePullbackFlatten' g h₁ h₂ α₁ ≫
          modulePullbackFlatten' g h₂ h₆ (α₂ ≫ α₃ ≫ α₄ ≫ α₅) :=
        modulePullbackFlatten'_comp_morphism g h₁ h₂ h₆ α₁ _
    _ = modulePullbackFlatten' g h₁ h₂ α₁ ≫
          (modulePullbackFlatten' g h₂ h₃ α₂ ≫
            modulePullbackFlatten' g h₃ h₆ (α₃ ≫ α₄ ≫ α₅)) :=
        congrArg (fun x => modulePullbackFlatten' g h₁ h₂ α₁ ≫ x)
          (modulePullbackFlatten'_comp_morphism g h₂ h₃ h₆ α₂ _)
    _ = modulePullbackFlatten' g h₁ h₂ α₁ ≫ modulePullbackFlatten' g h₂ h₃ α₂ ≫
          (modulePullbackFlatten' g h₃ h₄ α₃ ≫
            modulePullbackFlatten' g h₄ h₆ (α₄ ≫ α₅)) :=
        congrArg
          (fun x => modulePullbackFlatten' g h₁ h₂ α₁ ≫
            modulePullbackFlatten' g h₂ h₃ α₂ ≫ x)
          (modulePullbackFlatten'_comp_morphism g h₃ h₄ h₆ α₃ _)
    _ = modulePullbackFlatten' g h₁ h₂ α₁ ≫ modulePullbackFlatten' g h₂ h₃ α₂ ≫
          modulePullbackFlatten' g h₃ h₄ α₃ ≫
          (modulePullbackFlatten' g h₄ h₅ α₄ ≫ modulePullbackFlatten' g h₅ h₆ α₅) :=
        congrArg
          (fun x => modulePullbackFlatten' g h₁ h₂ α₁ ≫
            modulePullbackFlatten' g h₂ h₃ α₂ ≫ modulePullbackFlatten' g h₃ h₄ α₃ ≫ x)
          (modulePullbackFlatten'_comp_morphism g h₄ h₅ h₆ α₄ α₅)

/-- **The named flattening of a canonical identification is a canonical identification.** -/
theorem modulePullbackFlatten'_pullbackTransport (g : U' ⟶ U) {a b : V' ⟶ U'}
    {c d : V' ⟶ U} (hc : a ≫ g = c) (hd : b ≫ g = d) (hab : a = b)
    (M : Modules.{u, u} 𝒞 S hS U.1 U.2) (e : c = d) :
    modulePullbackFlatten' g hc hd
        (pullbackTransport ((modulePullback 𝒞 S hS g).obj M) hab) = pullbackTransport M e :=
  have e₁ : a ≫ g = b ≫ g := congrArg (· ≫ g) hab
  have e₂ : a ≫ g = d := e₁.trans hd
  (modulePullbackFlatten'_eq_comp g hc hd _).trans
    ((comp₃_congr rfl (modulePullbackFlatten_pullbackTransport g hab M e₁) rfl).trans
      ((comp₂_congr rfl (pullbackTransport_comp M e₁ hd e₂)).trans
        (pullbackTransport_comp M hc.symm e₂ e)))

/-- The flattening of a reindexed transition morphism, as a named threefold composite. -/
theorem modulePullbackFlatten_reindex_comp₃
    (hassoc : ModulePullbackCompIsoAssoc 𝒞 S hS) (g : U' ⟶ U) {a b : V ⟶ U}
    {a' b' : V' ⟶ U'} (m : V' ⟶ V) {ha : a' ≫ g = m ≫ a} {hb : m ≫ b = b' ≫ g}
    (F : Modules.{u, u} 𝒞 S hS U.1 U.2)
    (α : (modulePullback 𝒞 S hS a).obj F ⟶ (modulePullback 𝒞 S hS b).obj F)
    (β : (modulePullback 𝒞 S hS a').obj ((modulePullback 𝒞 S hS g).obj F) ⟶
      (modulePullback 𝒞 S hS b').obj ((modulePullback 𝒞 S hS g).obj F))
    (hβ : modulePullbackFlatten g β =
      pullbackTransport F ha ≫ modulePullbackReindex m α ≫ pullbackTransport F hb)
    (w : W ⟶ V') (n : W ⟶ V) (hn : w ≫ m = n) :
    modulePullbackFlatten g (modulePullbackReindex w β) =
      comp₃ (pullbackTransport F (comp_comp_eq_of_matched g m ha hn))
        (modulePullbackReindex n α)
        (pullbackTransport F (comp_comp_eq_of_matched g m hb.symm hn).symm) :=
  (modulePullbackFlatten_reindex_of_flatten g m F α β hassoc hβ w n hn
        (comp_comp_eq_of_matched g m ha hn)
        (comp_comp_eq_of_matched g m hb.symm hn).symm).trans (comp₃_eq _ _ _).symm

/-- The flattening of a reindexed transition morphism, as a named threefold composite between
canonical identifications whose composites are bracketed to the left. -/
theorem modulePullbackFlatten_reindex_comp₃'
    (hassoc : ModulePullbackCompIsoAssoc 𝒞 S hS) (g : U' ⟶ U) {a b : V ⟶ U}
    {a' b' : V' ⟶ U'} (m : V' ⟶ V) {ha : a' ≫ g = m ≫ a} {hb : m ≫ b = b' ≫ g}
    (F : Modules.{u, u} 𝒞 S hS U.1 U.2)
    (α : (modulePullback 𝒞 S hS a).obj F ⟶ (modulePullback 𝒞 S hS b).obj F)
    (β : (modulePullback 𝒞 S hS a').obj ((modulePullback 𝒞 S hS g).obj F) ⟶
      (modulePullback 𝒞 S hS b').obj ((modulePullback 𝒞 S hS g).obj F))
    (hβ : modulePullbackFlatten g β =
      pullbackTransport F ha ≫ modulePullbackReindex m α ≫ pullbackTransport F hb)
    (w : W ⟶ V') (n : W ⟶ V) (hn : w ≫ m = n)
    (hc : (w ≫ a') ≫ g = n ≫ a) (hd : (w ≫ b') ≫ g = n ≫ b) :
    modulePullbackFlatten g (modulePullbackReindex w β) =
      comp₃ (pullbackTransport F hc) (modulePullbackReindex n α)
        (pullbackTransport F hd.symm) :=
  (modulePullbackFlatten_reindex_comp₃ hassoc g m F α β hβ w n hn).trans rfl

/-- The flattening of a reindexed transition morphism, between canonical identifications whose
composites are bracketed to the left. -/
theorem modulePullbackFlatten_reindex_of_flatten'
    (hassoc : ModulePullbackCompIsoAssoc 𝒞 S hS) (g : U' ⟶ U) {a b : V ⟶ U}
    {a' b' : V' ⟶ U'} (m : V' ⟶ V) {ha : a' ≫ g = m ≫ a} {hb : m ≫ b = b' ≫ g}
    (F : Modules.{u, u} 𝒞 S hS U.1 U.2)
    (α : (modulePullback 𝒞 S hS a).obj F ⟶ (modulePullback 𝒞 S hS b).obj F)
    (β : (modulePullback 𝒞 S hS a').obj ((modulePullback 𝒞 S hS g).obj F) ⟶
      (modulePullback 𝒞 S hS b').obj ((modulePullback 𝒞 S hS g).obj F))
    (hβ : modulePullbackFlatten g β =
      pullbackTransport F ha ≫ modulePullbackReindex m α ≫ pullbackTransport F hb)
    (w : W ⟶ V') (n : W ⟶ V) (hn : w ≫ m = n)
    (hc : (w ≫ a') ≫ g = n ≫ a) (hd : (w ≫ b') ≫ g = n ≫ b) :
    modulePullbackFlatten g (modulePullbackReindex w β) =
      pullbackTransport F hc ≫ modulePullbackReindex n α ≫ pullbackTransport F hd.symm :=
  (modulePullbackFlatten_reindex_comp₃' hassoc g m F α β hβ w n hn hc hd).trans
    (comp₃_eq _ _ _)

/-- **The named flattening of a reindexed transition morphism is the reindexing of the given
transition morphism along the pushed test morphism**, with no transports left over.  This is the
identity that makes the cocycle law go through. -/
theorem modulePullbackFlatten'_reindex_of_flatten
    (hassoc : ModulePullbackCompIsoAssoc 𝒞 S hS) (g : U' ⟶ U) {a b : V ⟶ U}
    {a' b' : V' ⟶ U'} (m : V' ⟶ V) {ha : a' ≫ g = m ≫ a} {hb : m ≫ b = b' ≫ g}
    (F : Modules.{u, u} 𝒞 S hS U.1 U.2)
    (α : (modulePullback 𝒞 S hS a).obj F ⟶ (modulePullback 𝒞 S hS b).obj F)
    (β : (modulePullback 𝒞 S hS a').obj ((modulePullback 𝒞 S hS g).obj F) ⟶
      (modulePullback 𝒞 S hS b').obj ((modulePullback 𝒞 S hS g).obj F))
    (hβ : modulePullbackFlatten g β =
      pullbackTransport F ha ≫ modulePullbackReindex m α ≫ pullbackTransport F hb)
    (w : W ⟶ V') (n : W ⟶ V) (hn : w ≫ m = n)
    (hc : (w ≫ a') ≫ g = n ≫ a) (hd : (w ≫ b') ≫ g = n ≫ b) :
    modulePullbackFlatten' g hc hd (modulePullbackReindex w β) =
      modulePullbackReindex n α :=
  (modulePullbackFlatten'_eq_comp g hc hd _).trans
    ((comp₃_congr rfl
          (modulePullbackFlatten_reindex_of_flatten' hassoc g m F α β hβ w n hn hc hd)
          rfl).trans
      ((comp_transport_merge _ _ _ _ _ _ _ (pullbackTransport_comp_self F hc.symm hc)
            (pullbackTransport_comp_self F hd.symm hd)).trans
        (id_comp_comp_id (modulePullbackReindex n α)).symm))

/-- Two parallel morphisms matched by `m`, read after a test morphism, with the composite along
`g` bracketed to the left. -/
theorem comp_comp_eq_of_matched_left (g : U' ⟶ U) (m : V' ⟶ V) {a : V ⟶ U} {a' : V' ⟶ U'}
    (ha : a' ≫ g = m ≫ a) {x : W ⟶ V'} {x' : W ⟶ V} (hx : x ≫ m = x') :
    (x ≫ a') ≫ g = x' ≫ a :=
  comp_comp_eq_of_matched g m ha hx

/-- **The cocycle law transfers along flattening.**

If the flattening of `β` along `g` is the reindexing of `α` along `m` between the two
transports, and `α` satisfies the cocycle law at a triple of test morphisms, then `β` satisfies
it at any triple of test morphisms pushed to that one by `m`.  Both sides of the law for `β`
are flattened factor by factor, where they become the corresponding sides of the law for `α`
with no transports left over, and the named flattening is injective. -/
theorem modulePullbackReindex_cocycle_of_flatten
    (hassoc : ModulePullbackCompIsoAssoc 𝒞 S hS) (g : U' ⟶ U) {a b : V ⟶ U}
    {a' b' : V' ⟶ U'} (m : V' ⟶ V) {ha : a' ≫ g = m ≫ a} {hb : m ≫ b = b' ≫ g}
    (F : Modules.{u, u} 𝒞 S hS U.1 U.2)
    (α : (modulePullback 𝒞 S hS a).obj F ⟶ (modulePullback 𝒞 S hS b).obj F)
    (β : (modulePullback 𝒞 S hS a').obj ((modulePullback 𝒞 S hS g).obj F) ⟶
      (modulePullback 𝒞 S hS b').obj ((modulePullback 𝒞 S hS g).obj F))
    (hβ : modulePullbackFlatten g β =
      pullbackTransport F ha ≫ modulePullbackReindex m α ≫ pullbackTransport F hb)
    (P Q R : W ⟶ V') (P' Q' R' : W ⟶ V) (hP : P ≫ m = P') (hQ : Q ≫ m = Q')
    (hR : R ≫ m = R') (ht : R ≫ a' = P ≫ a') (hm : P ≫ b' = Q ≫ a')
    (hs : R ≫ b' = Q ≫ b') (ht' : R' ≫ a = P' ≫ a) (hm' : P' ≫ b = Q' ≫ a)
    (hs' : R' ≫ b = Q' ≫ b)
    (hcoc : modulePullbackReindex R' α =
      pullbackTransport F ht' ≫
        (modulePullbackReindex P' α ≫ pullbackTransport F hm' ≫
          modulePullbackReindex Q' α) ≫
        pullbackTransport F hs'.symm) :
    modulePullbackReindex R β =
      pullbackTransport ((modulePullback 𝒞 S hS g).obj F) ht ≫
        (modulePullbackReindex P β ≫
          pullbackTransport ((modulePullback 𝒞 S hS g).obj F) hm ≫
          modulePullbackReindex Q β) ≫
        pullbackTransport ((modulePullback 𝒞 S hS g).obj F) hs.symm :=
  have K₀ : (R ≫ a') ≫ g = R' ≫ a := comp_comp_eq_of_matched_left g m ha hR
  have K₁ : (P ≫ a') ≫ g = P' ≫ a := comp_comp_eq_of_matched_left g m ha hP
  have K₂ : (P ≫ b') ≫ g = P' ≫ b := comp_comp_eq_of_matched_left g m hb.symm hP
  have K₃ : (Q ≫ a') ≫ g = Q' ≫ a := comp_comp_eq_of_matched_left g m ha hQ
  have K₄ : (Q ≫ b') ≫ g = Q' ≫ b := comp_comp_eq_of_matched_left g m hb.symm hQ
  have K₅ : (R ≫ b') ≫ g = R' ≫ b := comp_comp_eq_of_matched_left g m hb.symm hR
  modulePullbackFlatten'_injective g K₀ K₅ <|
    calc modulePullbackFlatten' g K₀ K₅ (modulePullbackReindex R β)
        = modulePullbackReindex R' α :=
          modulePullbackFlatten'_reindex_of_flatten hassoc g m F α β hβ R R' hR K₀ K₅
      _ = pullbackTransport F ht' ≫ modulePullbackReindex P' α ≫
            pullbackTransport F hm' ≫ modulePullbackReindex Q' α ≫
            pullbackTransport F hs'.symm := hcoc.trans (comp_assoc₅ _ _ _ _ _)
      _ = modulePullbackFlatten' g K₀ K₁
              (pullbackTransport ((modulePullback 𝒞 S hS g).obj F) ht) ≫
            modulePullbackFlatten' g K₁ K₂ (modulePullbackReindex P β) ≫
            modulePullbackFlatten' g K₂ K₃
              (pullbackTransport ((modulePullback 𝒞 S hS g).obj F) hm) ≫
            modulePullbackFlatten' g K₃ K₄ (modulePullbackReindex Q β) ≫
            modulePullbackFlatten' g K₄ K₅
              (pullbackTransport ((modulePullback 𝒞 S hS g).obj F) hs.symm) :=
          comp₅_congr (modulePullbackFlatten'_pullbackTransport g K₀ K₁ ht F ht').symm
            (modulePullbackFlatten'_reindex_of_flatten hassoc g m F α β hβ P P' hP K₁
              K₂).symm
            (modulePullbackFlatten'_pullbackTransport g K₂ K₃ hm F hm').symm
            (modulePullbackFlatten'_reindex_of_flatten hassoc g m F α β hβ Q Q' hQ K₃
              K₄).symm
            (modulePullbackFlatten'_pullbackTransport g K₄ K₅ hs.symm F hs'.symm).symm
      _ = modulePullbackFlatten' g K₀ K₅
            (pullbackTransport ((modulePullback 𝒞 S hS g).obj F) ht ≫
              (modulePullbackReindex P β ≫
                pullbackTransport ((modulePullback 𝒞 S hS g).obj F) hm ≫
                modulePullbackReindex Q β) ≫
              pullbackTransport ((modulePullback 𝒞 S hS g).obj F) hs.symm) :=
          (modulePullbackFlatten'_comp₅ g K₀ K₁ K₂ K₃ K₄ K₅ _ _ _ _ _).symm.trans
            (congrArg (modulePullbackFlatten' g K₀ K₅) (comp_assoc₅ _ _ _ _ _).symm)

end FlattenNamed

end AlgebraicGeometry.Space

end
