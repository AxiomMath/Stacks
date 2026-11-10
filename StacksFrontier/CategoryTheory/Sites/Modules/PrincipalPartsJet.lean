module

public import StacksFrontier.CategoryTheory.Sites.Modules.PrincipalPartsSequence
import StacksCore.Tactic.StacksAttribute

/-!
# The first-order jet sheaf, and the inclusion of the sequence of principal parts is mono

Let `φ : O₁ ⟶ O₂` be a morphism of sheaves of commutative rings on a site and let `F` be a
sheaf of `O₂`-modules. The sequence of principal parts (Tag 09CW)
`0 → Ω_{O₂/O₁} ⊗ F → P¹_{O₂/O₁}(F) → F → 0`
is proved to be a complex, exact in the middle and surjective on the right in
`StacksFrontier/CategoryTheory/Sites/Modules/PrincipalPartsSequence.lean`. This file proves the
remaining clause, that the inclusion is a *monomorphism*, and so completes Tag 09CW.

The argument is the first-order jet sheaf. For order-one symbol data `δ` relating two
presheaves of `R`-modules `A` and `F` — a family of maps `δ X : R(X) × F(X) → A(X)`, additive
in each variable, linear in the second, satisfying the Leibniz rule in the first and
compatible with restriction — the product `A ⊕ F` carries the twisted scalar action
`b (a, x) = (b a + δ b x, b x)`, and `x ↦ (0, x)` is then an operator of order at most one
whose commutator with `b` is `x ↦ -δ b x`. Taking `A = (Ω_{O₂/O₁} ⊗ F)^#` and
`δ X b x = -(x ⊗ d b)` and applying Tag 09CT gives a morphism
`α : P¹_{O₂/O₁}(F) ⟶ Jet(F)` carrying the universal operator to the jet operator, and then
`ι ≫ α` is the inclusion `(Ω_{O₂/O₁} ⊗ F)^# ⟶ Jet(F)` of the symbol component, which is
injective on sections. A morphism whose composite with another is a monomorphism is one.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.internalHomMk`: a morphism *into* an internal hom, built
  from a bare family of slice morphisms with additivity, linearity and
  restriction-compatibility as hypotheses. This is the inverse datum of
  `AlgebraicGeometry.SheafOfModules.pairingHom`.
* `AlgebraicGeometry.SheafOfModules.pairingCurry`: **the curried form of a natural bilinear
  pairing**, a morphism `N ⟶ 𝓗om_O(M, P)` out of a family of pairings
  `M(X) × N(X) → P(X)`. This is the unit side of the tensor–internal-hom adjunction for
  presheaves of modules, which the library does not otherwise have.
* `AlgebraicGeometry.SheafOfModules.OrderOneSymbol`: **order-one symbol data**, the structure
  that defines a jet presheaf.
* `AlgebraicGeometry.SheafOfModules.OrderOneSymbol.Sections`,
  `AlgebraicGeometry.SheafOfModules.OrderOneSymbol.instModule` and
  `AlgebraicGeometry.SheafOfModules.OrderOneSymbol.jet`: the sections of the jet presheaf,
  their twisted scalar action, and the jet presheaf of modules itself.
* `AlgebraicGeometry.SheafOfModules.OrderOneSymbol.jetInl` and
  `AlgebraicGeometry.SheafOfModules.OrderOneSymbol.jetSnd`: the inclusion of the symbol
  component and the projection onto the base component.
* `AlgebraicGeometry.SheafOfModules.jetSheaf` and
  `AlgebraicGeometry.SheafOfModules.jetOp`: the jet sheaf of modules and its universal
  operator `x ↦ (0, x)`.
* `AlgebraicGeometry.SheafOfModules.principalPartsδ` and
  `AlgebraicGeometry.SheafOfModules.principalPartsSymbolData`: the symbol
  `δ X b x = -(x ⊗ d b)` of the sequence of principal parts, and its symbol data.
* `AlgebraicGeometry.SheafOfModules.principalPartsJet` and
  `AlgebraicGeometry.SheafOfModules.principalPartsJetDesc`: the jet sheaf of the sequence of
  principal parts and the morphism `P¹_{O₂/O₁}(F) ⟶ Jet(F)` supplied by Tag 09CT.
* `AlgebraicGeometry.SheafOfModules.tensorDifferentialsCurry`: the curried form of a morphism
  out of `(Ω_{O₂/O₁} ⊗ F)^#`.

## Main results

* `AlgebraicGeometry.SheafOfModules.isGlobalDiffOpOfOrder_one_mk`: **the sectionwise
  criterion for an operator to have order at most one.** This is the converse of
  `globalDiffOp_naturality`, `isGlobalDiffOpOfOrder_one_base` and
  `isGlobalDiffOpOfOrder_one_bracket` taken together.
* `AlgebraicGeometry.SheafOfModules.OrderOneSymbol.jet_isSheaf`: **the jet presheaf of two
  sheaves is a sheaf**, because its underlying presheaf of abelian groups is the product of
  the two components.
* `AlgebraicGeometry.SheafOfModules.mono_jetSheafInl`: the inclusion of the symbol component
  into the jets is a monomorphism, being injective on sections.
* `AlgebraicGeometry.SheafOfModules.hom_ext_of_tensorDifferentialsCurry`: **a morphism out of
  `(Ω_{O₂/O₁} ⊗ F)^#` is determined by its curried form.**
* `AlgebraicGeometry.SheafOfModules.principalPartsInclusion_comp_jetDesc`: **the composite of
  the inclusion with the retraction onto the jet sheaf is the inclusion of the symbol
  component.**
* `AlgebraicGeometry.SheafOfModules.mono_principalPartsInclusion_app`: **the inclusion of the
  sequence of principal parts is a monomorphism.**
* `AlgebraicGeometry.SheafOfModules.exists_shortExact_principalPartsSequence'`: **Tag 09CW**,
  the sequence of principal parts is a short exact sequence, with no residual hypothesis.

## Implementation notes

*Why a jet sheaf, and why the curried pairing.* Tags 04BL and 09CT are universal properties
of morphisms *out of* `Ω_{O₂/O₁}` and *out of* `P¹_{O₂/O₁}(F)`, whereas injectivity of the
inclusion is a statement about a morphism *into* `P¹_{O₂/O₁}(F)`; neither property alone can
see it. The jet sheaf converts the question into one about a morphism out of
`P¹_{O₂/O₁}(F)`: it is a target for an order-one operator, so Tag 09CT produces the
retraction `α`. Identifying `ι ≫ α` with the inclusion of the symbol component is then the
one genuine extra input, because the sections of `(Ω_{O₂/O₁} ⊗ F)^#` are not of the form
`x ⊗ d b`. `pairingCurry` supplies it: two morphisms out of `(Ω_{O₂/O₁} ⊗ F)^#` have equal
curried forms as soon as those agree on the differentials, by Tag 04BL's uniqueness, and a
morphism is determined by its curried form, by the sheafification adjunction together with
the fact that a morphism out of an objectwise tensor product is determined on pure tensors.
No statement about local generation of `Ω_{O₂/O₁}` by differentials, and no comparison of
`Ω_{O₂/O₁}` with the presheaf of objectwise Kähler differentials (Tag 08TP), is needed.

*The sheaf condition of the jet presheaf.* The twisted scalar action plays no part in it: the
underlying presheaf of abelian groups of the jets is the product of the two components, and a
product of sheaves is a sheaf. The two projections are morphisms of presheaves of abelian
groups — only the symbol component fails to be linear, which is the whole point — so they
form a binary fan, `jetIsLimit` proves it is a limit, and
`CategoryTheory.Sheaf.isSheaf_of_isLimit` concludes.

*The jet sections are a type synonym.* `OrderOneSymbol.Sections` is a `def` for
`A(X) × F(X)`, not that product itself, so that the twisted `Module` instance is the one
instance search finds and `Prod.instModule` is not. It cannot be avoided by building the
`ModuleCat` object directly, because `ModuleCat.mk` is private and `ModuleCat.of` demands
instances.

*Universes.* The site is `C : Type u` with `Category.{v} C`, the structure sheaves are
`CommRingCat.{w}`-valued and the coefficient sheaves of modules live in
`SheafOfModules.{max u v w m}`, which is the variable block of Tags 04BL and 09CT and is
forced rather than chosen there. The generic sections are stated at one free module universe
`t`; `internalHomMk` and `pairingCurry` take `M` and `P` in `PresheafOfModules.{t}` and the
source `N` in `PresheafOfModules.{max u v t}`, which is forced — the internal hom of two
presheaves of modules in universe `t` lives in `max u v t`, since its sections over `U` are
morphisms on the slice site. Writing all three at `max u v t` also elaborates but then every
*application* is stuck on `max u v ?t =?= max u v w m`; with `M` and `P` at `t` the universe
is pinned directly by `M` and nothing is stuck. Nothing is narrowed.

*Spelling.* `(Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj` and `Oforget O₂.obj` are
definitionally equal presheaves of rings but `CategoryTheory.sheafCompose` unfolds at neither
reducible nor instance transparency. The objectwise tensor product is taken over the second
spelling and the sheaves of modules over the first, so `r • x` for `r` a section in the second
spelling and `x` a section of a sheaf of modules does not even elaborate: it fails at `HSMul`, not
at a rewrite. `sectionsModuleOverOforget` is the bridge — the same device as
`AlgebraicGeometry.SheafOfModules.sectionsModuleOfSite` — and every statement in the last three
sections is written with scalars in the `Oforget` spelling, crossing to the other only where a
lemma is *applied*. For the same reason the computations there are chains of `Eq.trans` and
`congrArg` rather than `simp only`: after `TensorProduct.tmul_add` fires, the addition is
`TensorProduct`'s and no longer `ModuleCat`'s, so a `map_add` stated at the `ModuleCat` spelling
does not match syntactically even though it is definitionally the same.

## References

* [Stacks Project, Tag 09CW](https://stacks.math.columbia.edu/tag/09CW), the sequence of
  principal parts.
* [Stacks Project, Tag 09CT](https://stacks.math.columbia.edu/tag/09CT), the sheaf of
  principal parts, and [Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), relative
  differentials.
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM), the internal hom of
  sheaves of modules.
-/
@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits TensorProduct

universe v u w m t

namespace AlgebraicGeometry.SheafOfModules

section MapId

/-- Restricting a section of a presheaf of modules along an identity is the section itself. -/
theorem map_id_apply {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}
    (M : PresheafOfModules.{t} R) (X : Cᵒᵖ) (x : M.obj X) : M.map (𝟙 X) x = x := by
  rw [M.map_id]
  rfl

end MapId

section InternalHomMk

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (M P : PresheafOfModules.{t} (Oforget O))
  (N : PresheafOfModules.{max u v t} (Oforget O))
  (e : ∀ X : Cᵒᵖ, N.obj X → ((restrFun O X.unop).obj M ⟶ (restrFun O X.unop).obj P))
  (hadd : ∀ (X : Cᵒᵖ) (n n' : N.obj X), e X (n + n') = e X n + e X n')
  (hsmul : ∀ (X : Cᵒᵖ) (r : (Oforget O).obj X) (n : N.obj X),
    e X (r • n) = smulHom O M P X.unop r (e X n))
  (hnat : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) (n : N.obj X),
    e Y (N.map f n) = homRestr O M P f.unop (e X n))

include hadd hsmul hnat in
/-- **A morphism into the internal hom, from a bare family of slice morphisms.** This is the
inverse datum of `AlgebraicGeometry.SheafOfModules.pairingHom`: the same three hypotheses that
turn a family of sections of `𝓗om_O(M, P)` into a pairing out of the tensor product turn it
into a morphism into the internal hom. -/
noncomputable def internalHomMk : N ⟶ internalHom O M P where
  app X := ModuleCat.homAddEquiv.symm
    { toFun := e X
      map_add' := hadd X
      map_smul' := hsmul X }
  naturality {X Y} f := by
    ext n
    exact hnat f n

include hadd hsmul hnat in
/-- The component of `internalHomMk` at `X` sends a section `n` to `e X n`. -/
@[simp]
theorem internalHomMk_app_apply (X : Cᵒᵖ) (n : N.obj X) :
    ((internalHomMk O M P N e hadd hsmul hnat).app X).hom n = e X n := rfl

end InternalHomMk

/-- Two morphisms of presheaves of modules are equal if they agree on every section. -/
private theorem hom_ext_apply {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}
    {M N : PresheafOfModules.{t} R} {f g : M ⟶ N}
    (h : ∀ (X : Cᵒᵖ) (x : M.obj X), (f.app X).hom x = (g.app X).hom x) : f = g :=
  PresheafOfModules.hom_ext fun X ↦ ModuleCat.hom_ext (LinearMap.ext (h X))

section Curry

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (M P : PresheafOfModules.{t} (Oforget O))
  (N : PresheafOfModules.{max u v t} (Oforget O))
  (p : ∀ X : Cᵒᵖ, M.obj X → N.obj X → P.obj X)
  (hadd₁ : ∀ (X : Cᵒᵖ) (x x' : M.obj X) (n : N.obj X), p X (x + x') n = p X x n + p X x' n)
  (hsmul₁ : ∀ (X : Cᵒᵖ) (r : (Oforget O).obj X) (x : M.obj X) (n : N.obj X),
    p X (r • x) n = r • p X x n)
  (hadd₂ : ∀ (X : Cᵒᵖ) (x : M.obj X) (n n' : N.obj X), p X x (n + n') = p X x n + p X x n')
  (hsmul₂ : ∀ (X : Cᵒᵖ) (r : (Oforget O).obj X) (x : M.obj X) (n : N.obj X),
    p X x (r • n) = r • p X x n)
  (hnat : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) (x : M.obj X) (n : N.obj X),
    p Y (M.restrictₛₗ f x) (N.restrictₛₗ f n) = P.restrictₛₗ f (p X x n))

include hadd₁ hsmul₁ in
/-- The pairing against a fixed section of `N`, at one object of the slice site. -/
noncomputable def pairingCurryAppApp (X : Cᵒᵖ) (n : N.obj X) (V : (Over X.unop)ᵒᵖ) :
    ((restrFun O X.unop).obj M).obj V ⟶ ((restrFun O X.unop).obj P).obj V :=
  ModuleCat.homAddEquiv.symm
    { toFun x := p (op V.unop.left) x (N.map V.unop.hom.op n)
      map_add' x x' := hadd₁ (op V.unop.left) x x' _
      map_smul' r x := hsmul₁ (op V.unop.left) r x _ }

include hadd₁ hsmul₁ hnat in
/-- The pairing against a fixed section of `N`, as a morphism on the slice site: a section
over `X` of the internal hom `𝓗om_O(M, P)`. -/
noncomputable def pairingCurryApp (X : Cᵒᵖ) (n : N.obj X) :
    (restrFun O X.unop).obj M ⟶ (restrFun O X.unop).obj P where
  app V := pairingCurryAppApp O M P N p hadd₁ hsmul₁ X n V
  naturality {V W} g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hres : N.map W.unop.hom.op n =
        N.map ((Over.forget X.unop).map g.unop).op (N.map V.unop.hom.op n) := by
      have hcomp : ((Over.forget X.unop).map g.unop) ≫ V.unop.hom = W.unop.hom := Over.w g.unop
      rw [← hcomp, op_comp, N.map_comp_apply]
    refine Eq.trans ?_ (hnat ((Over.forget X.unop).map g.unop).op x (N.map V.unop.hom.op n))
    exact congrArg (fun z : N.obj (op W.unop.left) ↦
      p (op W.unop.left) (M.map ((Over.forget X.unop).map g.unop).op x) z) hres

include hadd₁ hsmul₁ hnat in
/-- At an object `V` of the slice site, the pairing against `n` sends `x` to the pairing of `x`
with the restriction of `n` to `V`. -/
@[simp]
theorem pairingCurryApp_app_apply (X : Cᵒᵖ) (n : N.obj X) (V : (Over X.unop)ᵒᵖ)
    (x : M.obj (op V.unop.left)) :
    ((pairingCurryApp O M P N p hadd₁ hsmul₁ hnat X n).app V).hom x =
      p (op V.unop.left) x (N.map V.unop.hom.op n) := rfl

include hadd₁ hsmul₁ hadd₂ hnat in
/-- The pairing against a section of `N` is additive in that section. -/
theorem pairingCurryApp_add (X : Cᵒᵖ) (n n' : N.obj X) :
    pairingCurryApp O M P N p hadd₁ hsmul₁ hnat X (n + n') =
      pairingCurryApp O M P N p hadd₁ hsmul₁ hnat X n +
        pairingCurryApp O M P N p hadd₁ hsmul₁ hnat X n' := by
  refine hom_ext_apply fun V x ↦ ?_
  rw [PresheafOfModules.add_app]
  simp only [ModuleCat.hom_add, LinearMap.add_apply]
  refine Eq.trans (congrArg (fun z : N.obj (op V.unop.left) ↦ p (op V.unop.left) x z)
    (map_add (N.map V.unop.hom.op).hom n n')) ?_
  exact hadd₂ (op V.unop.left) x _ _

include hadd₁ hsmul₁ hsmul₂ hnat in
/-- The pairing against `r • n` is `r` times the pairing against `n`. -/
theorem pairingCurryApp_smul (X : Cᵒᵖ) (r : (Oforget O).obj X) (n : N.obj X) :
    pairingCurryApp O M P N p hadd₁ hsmul₁ hnat X (r • n) =
      smulHom O M P X.unop r (pairingCurryApp O M P N p hadd₁ hsmul₁ hnat X n) := by
  refine hom_ext_apply fun V x ↦ ?_
  refine Eq.trans (congrArg (fun z : N.obj (op V.unop.left) ↦ p (op V.unop.left) x z)
    (PresheafOfModules.map_smul N V.unop.hom.op r n)) ?_
  exact hsmul₂ (op V.unop.left) (fRestr O X.unop r V) x _

include hadd₁ hsmul₁ hnat in
/-- The pairing against a restricted section is the restriction of the pairing against the
section. -/
theorem pairingCurryApp_restr {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : N.obj X) :
    pairingCurryApp O M P N p hadd₁ hsmul₁ hnat Y (N.map f n) =
      homRestr O M P f.unop (pairingCurryApp O M P N p hadd₁ hsmul₁ hnat X n) := by
  refine hom_ext_apply fun W x ↦ ?_
  refine Eq.trans (congrArg (fun z : N.obj (op W.unop.left) ↦ p (op W.unop.left) x z) ?_) rfl
  exact (N.map_comp_apply f W.unop.hom.op n).symm

include hadd₁ hsmul₁ hadd₂ hsmul₂ hnat in
/-- **The curried form of a natural bilinear pairing**: the morphism
`N ⟶ 𝓗om_O(M, P)` attached to a family of pairings `M(X) × N(X) → P(X)`, bilinear and
compatible with restriction. -/
noncomputable def pairingCurry : N ⟶ internalHom O M P :=
  internalHomMk O M P N (pairingCurryApp O M P N p hadd₁ hsmul₁ hnat)
    (pairingCurryApp_add O M P N p hadd₁ hsmul₁ hadd₂ hnat)
    (pairingCurryApp_smul O M P N p hadd₁ hsmul₁ hsmul₂ hnat)
    (fun _ _ f n ↦ pairingCurryApp_restr O M P N p hadd₁ hsmul₁ hnat f n)

include hadd₁ hsmul₁ hadd₂ hsmul₂ hnat in
/-- **The curried pairing is pinned by the pairing**: evaluating it at the terminal object of
the slice site recovers the pairing. -/
theorem pairingCurry_evalTerminal (X : Cᵒᵖ) (x : M.obj X) (n : N.obj X) :
    evalTerminal O M P
        (((pairingCurry O M P N p hadd₁ hsmul₁ hadd₂ hsmul₂ hnat).app X).hom n) x =
      p X x n :=
  congrArg (fun z : N.obj X ↦ p X x z) (map_id_apply N X n)

end Curry


section OrderOneCriterion

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O₁ O₂ : Sheaf J RingCat.{w}} (phi : O₁ ⟶ O₂)
  {F G : _root_.SheafOfModules.{t} O₂} (D : DiffOp.GlobalOp F G)
  (hnat : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) (x : F.val.obj X),
    D Y (F.val.map f x) = G.val.map f (D X x))
  (hbr : ∀ (X : Cᵒᵖ) (b r : O₂.obj.obj X) (x : F.val.obj X),
    D X (b • r • x) - b • D X (r • x) = r • (D X (b • x) - b • D X x))

include hnat in
/-- An operator compatible with restriction of sections is natural on every slice site. -/
theorem isNatural_restrict (U : C) : (D.restrict U).IsNatural := fun _ _ h s ↦ hnat h.left.op s

include hnat hbr in
/-- **The commutator of an operator with linear commutators is an operator of order zero.** -/
theorem isDiffOpOfOrder_zero_commutator_restrict (V : C) (g : O₂.obj.obj (op V)) :
    DiffOp.IsDiffOpOfOrder phi 0 (DiffOp.RawOp.commutator g (D.restrict V)) := by
  refine ⟨?_, ?_⟩
  · intro Z Z' h s
    have hscalar : (O₂.obj.map Z.hom.op) g
        = (O₂.obj.map h.left.op) ((O₂.obj.map Z'.hom.op) g) := by
      have hcomp : h.left ≫ Z'.hom = Z.hom := Over.w h
      rw [← hcomp, op_comp, Functor.map_comp]
      rfl
    change D (op Z.left) ((O₂.obj.map Z.hom.op) g • F.val.map h.left.op s) -
        (O₂.obj.map Z.hom.op) g • D (op Z.left) (F.val.map h.left.op s) =
      G.val.map h.left.op (D (op Z'.left) ((O₂.obj.map Z'.hom.op) g • s) -
        (O₂.obj.map Z'.hom.op) g • D (op Z'.left) s)
    rw [hscalar]
    exact diffOpSymbol_restriction ((O₂.obj.map h.left.op)).hom
      (F.val.map h.left.op).hom.toAddMonoidHom (G.val.map h.left.op).hom.toAddMonoidHom
      (fun r y ↦ PresheafOfModules.map_smul F.val h.left.op r y)
      (fun r y ↦ PresheafOfModules.map_smul G.val h.left.op r y)
      (D (op Z'.left)) (D (op Z.left)) (fun y ↦ hnat h.left.op y)
      ((O₂.obj.map Z'.hom.op) g) s
  · intro Z r s
    exact hbr (op Z.left) ((O₂.obj.map Z.hom.op) g) r s

include hnat hbr in
/-- **The sectionwise criterion for an operator to have order at most one.** This is the
converse of `AlgebraicGeometry.SheafOfModules.globalDiffOp_naturality`,
`AlgebraicGeometry.SheafOfModules.isGlobalDiffOpOfOrder_one_base` and
`AlgebraicGeometry.SheafOfModules.isGlobalDiffOpOfOrder_one_bracket` together: compatibility
with restriction, linearity over the base sheaf of rings and linearity of each commutator are
not merely consequences of order at most one, they characterize it. -/
theorem isGlobalDiffOpOfOrder_one_mk
    (hbase : ∀ (X : Cᵒᵖ) (a : O₁.obj.obj X) (x : F.val.obj X),
      D X (DiffOp.sectionRingHom phi X a • x) = DiffOp.sectionRingHom phi X a • D X x) :
    DiffOp.IsGlobalDiffOpOfOrder phi 1 D := fun U ↦
  ⟨isNatural_restrict D hnat U, fun Y a s ↦ hbase (op Y.left) a s,
    fun Y g ↦ isDiffOpOfOrder_zero_commutator_restrict phi D hnat hbr Y.left g⟩

end OrderOneCriterion


section Jet

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}

/-- **Order-one symbol data** relating two presheaves of `R`-modules: a family of maps
`δ X : R(X) × F(X) → A(X)`, additive in each variable, linear in the second, satisfying the
Leibniz rule in the first and compatible with restriction. The twisted module structure on
`A ⊕ F` that these data define is the *jet* presheaf, for which `x ↦ (0, x)` is an operator
of order at most one with symbol `δ`.

For the sequence of principal parts, `A` is the sheafified tensor product
`(Ω_{O₂/O₁} ⊗ F)^#`, `F` is the coefficient module and `δ X b x = -(x ⊗ d b)`. -/
structure OrderOneSymbol (A F : PresheafOfModules.{t} R) where
  /-- the symbol: a family of maps `R(X) × F(X) → A(X)` -/
  δ : ∀ X : Cᵒᵖ, R.obj X → F.obj X → A.obj X
  /-- the symbol is additive in the scalar -/
  add_left : ∀ (X : Cᵒᵖ) (b b' : R.obj X) (x : F.obj X), δ X (b + b') x = δ X b x + δ X b' x
  /-- the symbol is additive in the section -/
  add_right : ∀ (X : Cᵒᵖ) (b : R.obj X) (x y : F.obj X), δ X b (x + y) = δ X b x + δ X b y
  /-- the symbol is linear in the section -/
  smul_right : ∀ (X : Cᵒᵖ) (b r : R.obj X) (x : F.obj X), δ X b (r • x) = r • δ X b x
  /-- the Leibniz rule in the scalar -/
  leibniz : ∀ (X : Cᵒᵖ) (b b' : R.obj X) (x : F.obj X),
    δ X (b * b') x = b • δ X b' x + b' • δ X b x
  /-- the symbol is compatible with restriction -/
  map : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) (b : R.obj X) (x : F.obj X),
    δ Y ((R.map f).hom b) (F.restrictₛₗ f x) = A.restrictₛₗ f (δ X b x)

namespace OrderOneSymbol

variable {A F : PresheafOfModules.{t} R} (S : OrderOneSymbol A F)

/-- The symbol of the zero scalar vanishes. -/
theorem δ_zero_left (X : Cᵒᵖ) (x : F.obj X) : S.δ X 0 x = 0 := by
  have h := S.add_left X 0 0 x
  rw [add_zero] at h
  exact left_eq_add.mp h

/-- The symbol of the zero section vanishes. -/
theorem δ_zero_right (X : Cᵒᵖ) (b : R.obj X) : S.δ X b 0 = 0 := by
  have h := S.add_right X b 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

/-- The symbol of the unit scalar vanishes. -/
theorem δ_one (X : Cᵒᵖ) (x : F.obj X) : S.δ X 1 x = 0 := by
  have h := S.leibniz X 1 1 x
  rw [mul_one, one_smul] at h
  exact left_eq_add.mp h

/-- The sections of the jet presheaf over `X`: the product of the two components, carrying
the module structure twisted by the symbol. -/
def Sections (_S : OrderOneSymbol A F) (X : Cᵒᵖ) : Type t := A.obj X × F.obj X

/-- The additive group structure on jets is that of the product of the two components. -/
instance (X : Cᵒᵖ) : AddCommGroup (S.Sections X) :=
  inferInstanceAs (AddCommGroup (A.obj X × F.obj X))

/-- The symbol component of a jet. -/
abbrev Sections.diff {X : Cᵒᵖ} (z : S.Sections X) : A.obj X := Prod.fst z

/-- The base component of a jet. -/
abbrev Sections.base {X : Cᵒᵖ} (z : S.Sections X) : F.obj X := Prod.snd z

/-- A jet, from its symbol component and its base component. -/
abbrev Sections.mk {X : Cᵒᵖ} (a : A.obj X) (x : F.obj X) : S.Sections X := (a, x)

/-- The symbol component of `Sections.mk S a x` is `a`. -/
@[simp] theorem Sections.diff_mk {X : Cᵒᵖ} (a : A.obj X) (x : F.obj X) :
    (Sections.mk S a x).diff = a := rfl

/-- The base component of `Sections.mk S a x` is `x`. -/
@[simp] theorem Sections.base_mk {X : Cᵒᵖ} (a : A.obj X) (x : F.obj X) :
    (Sections.mk S a x).base = x := rfl

/-- The symbol component of a sum of jets is the sum of the symbol components. -/
@[simp] theorem Sections.add_diff {X : Cᵒᵖ} (z z' : S.Sections X) :
    (z + z').diff = z.diff + z'.diff := rfl

/-- The base component of a sum of jets is the sum of the base components. -/
@[simp] theorem Sections.add_base {X : Cᵒᵖ} (z z' : S.Sections X) :
    (z + z').base = z.base + z'.base := rfl

/-- Two jets with the same symbol component and the same base component are equal. -/
theorem Sections.ext' {X : Cᵒᵖ} {z z' : S.Sections X}
    (hd : z.diff = z'.diff) (hb : z.base = z'.base) : z = z' :=
  Prod.ext hd hb

/-- **The twisted scalar action on jets**: `b (a, x) = (b a + δ b x, b x)`. -/
noncomputable instance instModule (X : Cᵒᵖ) : Module (R.obj X) (S.Sections X) where
  smul b z := Sections.mk S (b • z.diff + S.δ X b z.base) (b • z.base)
  one_smul z := Sections.ext' S (by
      change (1 : R.obj X) • z.diff + S.δ X 1 z.base = z.diff
      rw [S.δ_one, one_smul, add_zero]) (by
      change (1 : R.obj X) • z.base = z.base
      rw [one_smul])
  mul_smul b b' z := Sections.ext' S (by
      change (b * b') • z.diff + S.δ X (b * b') z.base =
        b • (b' • z.diff + S.δ X b' z.base) + S.δ X b (b' • z.base)
      rw [S.leibniz, S.smul_right, smul_add, mul_smul]
      abel) (by
      change (b * b') • z.base = b • b' • z.base
      rw [mul_smul])
  smul_zero b := Sections.ext' S (by
      change b • (0 : A.obj X) + S.δ X b (0 : F.obj X) = (0 : A.obj X)
      rw [S.δ_zero_right, smul_zero, add_zero]) (by
      change b • (0 : F.obj X) = (0 : F.obj X)
      rw [smul_zero])
  smul_add b z z' := Sections.ext' S (by
      change b • (z.diff + z'.diff) + S.δ X b (z.base + z'.base) =
        (b • z.diff + S.δ X b z.base) + (b • z'.diff + S.δ X b z'.base)
      rw [S.add_right, smul_add]
      abel) (by
      change b • (z.base + z'.base) = b • z.base + b • z'.base
      rw [smul_add])
  add_smul b b' z := Sections.ext' S (by
      change (b + b') • z.diff + S.δ X (b + b') z.base =
        (b • z.diff + S.δ X b z.base) + (b' • z.diff + S.δ X b' z.base)
      rw [S.add_left, add_smul]
      abel) (by
      change (b + b') • z.base = b • z.base + b' • z.base
      rw [add_smul])
  zero_smul z := Sections.ext' S (by
      change (0 : R.obj X) • z.diff + S.δ X 0 z.base = (0 : A.obj X)
      rw [S.δ_zero_left, zero_smul, add_zero]) (by
      change (0 : R.obj X) • z.base = (0 : F.obj X)
      rw [zero_smul])

/-- The symbol component of `b • z` is `b • z.diff + δ b z.base`. -/
@[simp] theorem smul_diff {X : Cᵒᵖ} (b : R.obj X) (z : S.Sections X) :
    (b • z).diff = b • z.diff + S.δ X b z.base := rfl

/-- The base component of `b • z` is `b • z.base`. -/
@[simp] theorem smul_base {X : Cᵒᵖ} (b : R.obj X) (z : S.Sections X) :
    (b • z).base = b • z.base := rfl

/-- The underlying function of the restriction map of the jet presheaf. -/
noncomputable def jetMapFun {X Y : Cᵒᵖ} (f : X ⟶ Y) (z : S.Sections X) : S.Sections Y :=
  Sections.mk S (A.restrictₛₗ f z.diff) (F.restrictₛₗ f z.base)

/-- The restriction of a jet has, as symbol component, the restriction of its symbol
component. -/
@[simp] theorem jetMapFun_diff {X Y : Cᵒᵖ} (f : X ⟶ Y) (z : S.Sections X) :
    Sections.diff S (S.jetMapFun f z) = A.restrictₛₗ f (Sections.diff S z) := rfl

/-- The restriction of a jet has, as base component, the restriction of its base component. -/
@[simp] theorem jetMapFun_base {X Y : Cᵒᵖ} (f : X ⟶ Y) (z : S.Sections X) :
    Sections.base S (S.jetMapFun f z) = F.restrictₛₗ f (Sections.base S z) := rfl

/-- Restriction of jets is additive. -/
theorem jetMapFun_add {X Y : Cᵒᵖ} (f : X ⟶ Y) (z z' : S.Sections X) :
    S.jetMapFun f (z + z') = S.jetMapFun f z + S.jetMapFun f z' :=
  Sections.ext' S (map_add (A.restrictₛₗ f) _ _) (map_add (F.restrictₛₗ f) _ _)

/-- Restriction of jets is semilinear along the restriction map of `R` for the twisted
action. -/
theorem jetMapFun_smul {X Y : Cᵒᵖ} (f : X ⟶ Y) (b : R.obj X) (z : S.Sections X) :
    S.jetMapFun f (b • z) = (R.map f).hom b • S.jetMapFun f z := by
  refine Sections.ext' S ?_ ?_
  · change A.restrictₛₗ f (b • Sections.diff S z + S.δ X b (Sections.base S z)) =
      (R.map f).hom b • A.restrictₛₗ f (Sections.diff S z) +
        S.δ Y ((R.map f).hom b) (F.restrictₛₗ f (Sections.base S z))
    rw [map_add, S.map f b (Sections.base S z), map_smulₛₗ]
  · change F.restrictₛₗ f (b • Sections.base S z) =
      (R.map f).hom b • F.restrictₛₗ f (Sections.base S z)
    rw [map_smulₛₗ]

/-- The restriction map of the jet presheaf. -/
noncomputable def jetMap {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ModuleCat.of (R.obj X) (S.Sections X) ⟶
      (ModuleCat.restrictScalars (R.map f).hom).obj
        (ModuleCat.of (R.obj Y) (S.Sections Y)) :=
  ModuleCat.homAddEquiv.symm
    { toFun := S.jetMapFun f
      map_add' := fun z z' ↦ S.jetMapFun_add f z z'
      map_smul' := fun b z ↦ S.jetMapFun_smul f b z }

/-- The restriction map of the jet presheaf is `jetMapFun`. -/
@[simp] theorem jetMap_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (z : S.Sections X) :
    (S.jetMap f).hom z = S.jetMapFun f z := rfl

/-- **The jet presheaf of modules attached to order-one symbol data.** Its sections are the
pairs `(a, x)` with `a` in the symbol component and `x` in the base component, with the
scalar action twisted by the symbol. -/
noncomputable def jet : PresheafOfModules.{t} R where
  obj X := ModuleCat.of (R.obj X) (S.Sections X)
  map f := S.jetMap f
  map_id X := by
    ext z
    refine Sections.ext' S ?_ ?_
    · change A.restrictₛₗ (𝟙 X) (Sections.diff S z) = Sections.diff S z
      rw [A.restrictₛₗ_apply, A.map_id]
      rfl
    · change F.restrictₛₗ (𝟙 X) (Sections.base S z) = Sections.base S z
      rw [F.restrictₛₗ_apply, F.map_id]
      rfl
  map_comp f g := by
    ext z
    refine Sections.ext' S ?_ ?_
    · change A.restrictₛₗ (f ≫ g) (Sections.diff S z) =
        A.restrictₛₗ g (A.restrictₛₗ f (Sections.diff S z))
      rw [A.restrictₛₗ_apply, A.restrictₛₗ_apply, A.restrictₛₗ_apply, A.map_comp_apply]
    · change F.restrictₛₗ (f ≫ g) (Sections.base S z) =
        F.restrictₛₗ g (F.restrictₛₗ f (Sections.base S z))
      rw [F.restrictₛₗ_apply, F.restrictₛₗ_apply, F.restrictₛₗ_apply, F.map_comp_apply]

/-- The module of sections of the jet presheaf over `X` is `S.Sections X`. -/
@[simp] theorem jet_obj (X : Cᵒᵖ) :
    S.jet.obj X = ModuleCat.of (R.obj X) (S.Sections X) := rfl

/-- The restriction maps of the jet presheaf are given by `jetMapFun`. -/
@[simp] theorem jet_map_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (z : S.Sections X) :
    S.jet.map f z = S.jetMapFun f z := rfl

/-- **The inclusion of the symbol component into the jets**, `a ↦ (a, 0)`. -/
noncomputable def jetInl : A ⟶ S.jet where
  app X := ModuleCat.ofHom
    { toFun a := Sections.mk S a 0
      map_add' a a' := Sections.ext' S rfl (by
        change (0 : F.obj X) = 0 + 0
        rw [add_zero])
      map_smul' b a := Sections.ext' S (by
        change b • a = b • a + S.δ X b (0 : F.obj X)
        rw [S.δ_zero_right, add_zero]) (by
        change (0 : F.obj X) = b • (0 : F.obj X)
        rw [smul_zero]) }
  naturality {X Y} f := by
    ext a
    refine Sections.ext' S rfl ?_
    change (0 : F.obj Y) = F.restrictₛₗ f (0 : F.obj X)
    rw [map_zero]

/-- The inclusion of the symbol component sends `a` to `(a, 0)`. -/
@[simp] theorem jetInl_app_apply (X : Cᵒᵖ) (a : A.obj X) :
    (S.jetInl.app X).hom a = Sections.mk S a 0 := rfl

/-- The inclusion of the symbol component is injective on sections. -/
theorem jetInl_app_injective (X : Cᵒᵖ) : Function.Injective (S.jetInl.app X).hom :=
  fun _ _ h ↦ congrArg (Sections.diff S) h

/-- **The projection of the jets onto the base module.** -/
noncomputable def jetSnd : S.jet ⟶ F where
  app X := ModuleCat.ofHom
    { toFun := Sections.base S
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  naturality {X Y} f := by
    ext z
    rfl

/-- The projection onto the base module sends a jet to its base component. -/
@[simp] theorem jetSnd_app_apply (X : Cᵒᵖ) (z : S.Sections X) :
    (S.jetSnd.app X).hom z = Sections.base S z := rfl

section Sheaf

variable {J : GrothendieckTopology C}

/-- The symbol component of a jet, as a morphism of presheaves of abelian groups. -/
noncomputable def jetFstPresheaf : S.jet.presheaf ⟶ A.presheaf where
  app X := AddCommGrpCat.ofHom (AddMonoidHom.mk' (Sections.diff S) (fun _ _ ↦ rfl))
  naturality {X Y} f := by
    ext z
    rfl

/-- The base component of a jet, as a morphism of presheaves of abelian groups. -/
noncomputable def jetSndPresheaf : S.jet.presheaf ⟶ F.presheaf where
  app X := AddCommGrpCat.ofHom (AddMonoidHom.mk' (Sections.base S) (fun _ _ ↦ rfl))
  naturality {X Y} f := by
    ext z
    rfl

/-- The jet presheaf, as a binary fan on its two components. -/
noncomputable def jetBinaryFan : BinaryFan A.presheaf F.presheaf :=
  BinaryFan.mk (jetFstPresheaf S) (jetSndPresheaf S)

/-- **The jet presheaf is the product of its two components** as a presheaf of abelian
groups. -/
noncomputable def jetIsLimit : IsLimit (jetBinaryFan S) :=
  BinaryFan.isLimitMk
    (fun s ↦
      { app X := AddCommGrpCat.ofHom
          (AddMonoidHom.prod (s.fst.app X).hom (s.snd.app X).hom)
        naturality := fun {X Y} f ↦ by
          ext y
          refine Sections.ext' S ?_ ?_
          · exact congrArg (fun g : s.pt.obj X ⟶ A.presheaf.obj Y ↦
              (ConcreteCategory.hom g) y) (s.fst.naturality f)
          · exact congrArg (fun g : s.pt.obj X ⟶ F.presheaf.obj Y ↦
              (ConcreteCategory.hom g) y) (s.snd.naturality f) })
    (fun s ↦ by ext y; rfl)
    (fun s ↦ by ext y; rfl)
    (fun s m h₁ h₂ ↦ by
      ext X y
      refine Sections.ext' S ?_ ?_
      · exact congrArg (fun g : s.pt.obj X ⟶ A.presheaf.obj X ↦
          (ConcreteCategory.hom g) y) (NatTrans.congr_app h₁ X)
      · exact congrArg (fun g : s.pt.obj X ⟶ F.presheaf.obj X ↦
          (ConcreteCategory.hom g) y) (NatTrans.congr_app h₂ X))

/-- **The jet presheaf of two sheaves is a sheaf.** -/
theorem jet_isSheaf (hA : Presheaf.IsSheaf J A.presheaf)
    (hF : Presheaf.IsSheaf J F.presheaf) : Presheaf.IsSheaf J S.jet.presheaf := by
  apply CategoryTheory.Sheaf.isSheaf_of_isLimit (E := (Cone.postcompose
    (pairComp (⟨A.presheaf, hA⟩ : Sheaf J AddCommGrpCat.{t})
      ⟨F.presheaf, hF⟩ (sheafToPresheaf J AddCommGrpCat.{t})).inv).obj (jetBinaryFan S))
  exact (IsLimit.postcomposeInvEquiv _ _).invFun (jetIsLimit S)

end Sheaf

end OrderOneSymbol

end Jet


section JetOperator

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O₁ O₂ : Sheaf J RingCat.{w}} (phi : O₁ ⟶ O₂)
  {A F : _root_.SheafOfModules.{max u v w m} O₂} (S : OrderOneSymbol A.val F.val)

/-- **The jet sheaf of modules attached to order-one symbol data.** -/
noncomputable def jetSheaf : _root_.SheafOfModules.{max u v w m} O₂ where
  val := S.jet
  isSheaf := S.jet_isSheaf A.isSheaf F.isSheaf

/-- The underlying presheaf of the jet sheaf is the jet presheaf. -/
@[simp] theorem jetSheaf_val : (jetSheaf.{v, u, w, m} S).val = S.jet := rfl

/-- The inclusion of the symbol component into the jets, as a morphism of sheaves. -/
noncomputable def jetSheafInl : A ⟶ jetSheaf.{v, u, w, m} S := ⟨S.jetInl⟩

/-- The inclusion of the symbol component into the jet sheaf sends `a` to `(a, 0)`. -/
@[simp] theorem jetSheafInl_app_apply (X : Cᵒᵖ) (a : A.val.obj X) :
    ((jetSheafInl.{v, u, w, m} S).val.app X).hom a = OrderOneSymbol.Sections.mk S a 0 := rfl

/-- **The inclusion of the symbol component into the jet sheaf is a monomorphism.** -/
theorem mono_jetSheafInl : Mono (jetSheafInl.{v, u, w, m} S) :=
  (_root_.SheafOfModules.forget O₂).mono_of_mono_map
    (PresheafOfModules.mono_of_injective (f := S.jetInl)
      (fun ⦃X⦄ ↦ S.jetInl_app_injective X))

/-- **The universal operator of the jet sheaf**, the additive map `x ↦ (0, x)`. -/
noncomputable def jetOp : DiffOp.GlobalOp F (jetSheaf.{v, u, w, m} S) := fun X ↦
  AddMonoidHom.mk' (fun x ↦ OrderOneSymbol.Sections.mk S 0 x)
    (fun x y ↦ OrderOneSymbol.Sections.ext' S (by
      change (0 : A.val.obj X) = 0 + 0
      rw [add_zero]) rfl)

/-- The jet operator sends `x` to `(0, x)`. -/
@[simp] theorem jetOp_apply (X : Cᵒᵖ) (x : F.val.obj X) :
    jetOp.{v, u, w, m} S X x = OrderOneSymbol.Sections.mk S 0 x := rfl

/-- The jet operator commutes with restriction of sections. -/
theorem jetOp_naturality ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) (x : F.val.obj X) :
    jetOp.{v, u, w, m} S Y (F.val.map f x) =
      (jetSheaf.{v, u, w, m} S).val.map f (jetOp.{v, u, w, m} S X x) :=
  OrderOneSymbol.Sections.ext' S (map_zero (A.val.restrictₛₗ f)).symm rfl

/-- **The commutators of the jet operator are linear.** -/
theorem jetOp_bracket (X : Cᵒᵖ) (b r : O₂.obj.obj X) (x : F.val.obj X) :
    jetOp.{v, u, w, m} S X (b • r • x) - b • jetOp.{v, u, w, m} S X (r • x) =
      r • (jetOp.{v, u, w, m} S X (b • x) - b • jetOp.{v, u, w, m} S X x) := by
  refine OrderOneSymbol.Sections.ext' S ?_ ?_
  · change (0 : A.val.obj X) - (b • (0 : A.val.obj X) + S.δ X b (r • x)) =
      r • ((0 : A.val.obj X) - (b • (0 : A.val.obj X) + S.δ X b x)) +
        S.δ X r (b • x - b • x)
    simp only [smul_zero, zero_add, zero_sub, sub_self, S.δ_zero_right, add_zero,
      S.smul_right, smul_neg]
  · change b • r • x - b • r • x = r • (b • x - b • x)
    rw [sub_self, sub_self, smul_zero]

include phi in
/-- **The jet operator has order at most one** when the symbol vanishes on scalars coming
from the base sheaf of rings. -/
theorem jetOp_isGlobalDiffOpOfOrder
    (hbase : ∀ (X : Cᵒᵖ) (a : O₁.obj.obj X) (x : F.val.obj X),
      S.δ X (DiffOp.sectionRingHom phi X a) x = 0) :
    DiffOp.IsGlobalDiffOpOfOrder phi 1 (jetOp.{v, u, w, m} S) :=
  isGlobalDiffOpOfOrder_one_mk phi _ (fun _ _ f x ↦ jetOp_naturality.{v, u, w, m} S f x)
    (fun X b r x ↦ jetOp_bracket.{v, u, w, m} S X b r x)
    (fun X a x ↦ OrderOneSymbol.Sections.ext' S (by
      change (0 : A.val.obj X) =
        DiffOp.sectionRingHom phi X a • (0 : A.val.obj X) +
          S.δ X (DiffOp.sectionRingHom phi X a) x
      rw [hbase X a x, smul_zero, add_zero]) rfl)

end JetOperator


section PrincipalParts

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w m}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w m}]
  {O₁ O₂ : Sheaf J CommRingCat.{w}} (φ : O₁ ⟶ O₂)
  (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))

/-- The module structure that the sections of a sheaf of `O₂`-modules already carry, written
over the sections of the underlying *presheaf* of rings. -/
local instance sectionsModuleOverOforget
    {G : PresheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj} {X : Cᵒᵖ} :
    Module ((Oforget O₂.obj).obj X) (G.obj X) :=
  inferInstanceAs (Module ((Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj.obj X) (G.obj X))

/-- The sheafified tensor product `(Ω_{O₂/O₁} ⊗ F)^#`. -/
noncomputable abbrev tensorDifferentials :
    _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w m, max u v w m}
    O₂).obj F).obj (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ)

/-- The sheafification map `F ⊗ Ω_{O₂/O₁} ⟶ (F ⊗ Ω_{O₂/O₁})^#`, as a morphism of presheaves
of modules: the unit of the sheafification adjunction. -/
noncomputable def tensorDifferentialsUnit :
    PresheafOfModules.tensorObj F.val
        (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val ⟶
      (_root_.SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O₂)).obj
        (tensorDifferentials.{v, u, w, m} φ F) :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).unit.app
      (PresheafOfModules.tensorObj F.val
        (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val)

/-- **The symbol of the sequence of principal parts**, as a family of maps: minus the image
of the pure tensor `x ⊗ d b` in the sheafified tensor product. -/
noncomputable def principalPartsδ (X : Cᵒᵖ) (b : (Oforget O₂.obj).obj X)
    (x : F.val.obj X) : (tensorDifferentials.{v, u, w, m} φ F).val.obj X :=
  -((tensorDifferentialsUnit.{v, u, w, m} φ F).app X).hom
    (x ⊗ₜ[(Oforget O₂.obj).obj X] (universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).d b)

/-- Minus the sheafification unit is additive. -/
private theorem neg_unit_add (X : Cᵒᵖ)
    (s t : (PresheafOfModules.tensorObj F.val
      (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val).obj X) :
    -(((tensorDifferentialsUnit.{v, u, w, m} φ F).app X).hom (s + t)) =
      -(((tensorDifferentialsUnit.{v, u, w, m} φ F).app X).hom s) +
        -(((tensorDifferentialsUnit.{v, u, w, m} φ F).app X).hom t) :=
  (congrArg Neg.neg (map_add ((tensorDifferentialsUnit.{v, u, w, m} φ F).app X).hom _ _)).trans
    (neg_add _ _)

/-- Minus the sheafification unit is compatible with scalar multiplication. -/
private theorem neg_unit_smul (X : Cᵒᵖ) (c : (Oforget O₂.obj).obj X)
    (t : (PresheafOfModules.tensorObj F.val
      (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val).obj X) :
    -(((tensorDifferentialsUnit.{v, u, w, m} φ F).app X).hom (c • t)) =
      c • -(((tensorDifferentialsUnit.{v, u, w, m} φ F).app X).hom t) :=
  (congrArg Neg.neg (((tensorDifferentialsUnit.{v, u, w, m} φ F).app X).hom.map_smul c t)).trans
    (smul_neg c _).symm

/-- Minus the sheafification unit of a pure tensor is linear in the differential. -/
private theorem neg_unit_tmul_smul (X : Cᵒᵖ) (c : (Oforget O₂.obj).obj X) (x : F.val.obj X)
    (ω : (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val.obj X) :
    -(((tensorDifferentialsUnit.{v, u, w, m} φ F).app X).hom
        (x ⊗ₜ[(Oforget O₂.obj).obj X] (c • ω))) =
      c • -(((tensorDifferentialsUnit.{v, u, w, m} φ F).app X).hom
        (x ⊗ₜ[(Oforget O₂.obj).obj X] ω)) :=
  Eq.trans (congrArg (fun t ↦ -(((tensorDifferentialsUnit.{v, u, w, m} φ F).app X).hom t))
    ((TensorProduct.mk ((Oforget O₂.obj).obj X) (F.val.obj X)
      ((moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val.obj X) x).map_smul c ω))
    (neg_unit_smul.{v, u, w, m} φ F X c _)

/-- The symbol of the sequence of principal parts is additive in the scalar. -/
theorem principalPartsδ_add_left (X : Cᵒᵖ) (b b' : (Oforget O₂.obj).obj X)
    (x : F.val.obj X) :
    principalPartsδ.{v, u, w, m} φ F X (b + b') x =
      principalPartsδ.{v, u, w, m} φ F X b x + principalPartsδ.{v, u, w, m} φ F X b' x := by
  unfold principalPartsδ
  rw [map_add, TensorProduct.tmul_add]
  exact neg_unit_add.{v, u, w, m} φ F X _ _

/-- The symbol of the sequence of principal parts is additive in the section. -/
theorem principalPartsδ_add_right (X : Cᵒᵖ) (b : (Oforget O₂.obj).obj X)
    (x y : F.val.obj X) :
    principalPartsδ.{v, u, w, m} φ F X b (x + y) =
      principalPartsδ.{v, u, w, m} φ F X b x + principalPartsδ.{v, u, w, m} φ F X b y := by
  unfold principalPartsδ
  rw [TensorProduct.add_tmul]
  exact neg_unit_add.{v, u, w, m} φ F X _ _

/-- The symbol of the sequence of principal parts is linear in the section. -/
theorem principalPartsδ_smul_right (X : Cᵒᵖ) (b r : (Oforget O₂.obj).obj X)
    (x : F.val.obj X) :
    principalPartsδ.{v, u, w, m} φ F X b (r • x) =
      r • principalPartsδ.{v, u, w, m} φ F X b x := by
  unfold principalPartsδ
  exact neg_unit_smul.{v, u, w, m} φ F X r (x ⊗ₜ[(Oforget O₂.obj).obj X]
    (universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).d b)

/-- The symbol of the sequence of principal parts satisfies the Leibniz rule in the
scalar. -/
theorem principalPartsδ_leibniz (X : Cᵒᵖ) (b b' : (Oforget O₂.obj).obj X)
    (x : F.val.obj X) :
    principalPartsδ.{v, u, w, m} φ F X (b * b') x =
      b • principalPartsδ.{v, u, w, m} φ F X b' x +
        b' • principalPartsδ.{v, u, w, m} φ F X b x := by
  unfold principalPartsδ
  rw [(universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).d_mul, TensorProduct.tmul_add]
  exact (neg_unit_add.{v, u, w, m} φ F X _ _).trans
    (congrArg₂ (· + ·) (neg_unit_tmul_smul.{v, u, w, m} φ F X b _ _)
      (neg_unit_tmul_smul.{v, u, w, m} φ F X b' _ _))

/-- The symbol of the sequence of principal parts is compatible with restriction. -/
theorem principalPartsδ_map ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) (b : (Oforget O₂.obj).obj X)
    (x : F.val.obj X) :
    principalPartsδ.{v, u, w, m} φ F Y (((Oforget O₂.obj).map f).hom b)
        (F.val.restrictₛₗ f x) =
      (tensorDifferentials.{v, u, w, m} φ F).val.restrictₛₗ f
        (principalPartsδ.{v, u, w, m} φ F X b x) := by
  have hd : (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val.map f
        ((universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).d b) =
      (universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).d
        (((Oforget O₂.obj).map f).hom b) :=
    ((universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).d_map f b).symm
  have key : ((tensorDifferentialsUnit.{v, u, w, m} φ F).app Y).hom
        ((F.val.restrictₛₗ f x) ⊗ₜ[(Oforget O₂.obj).obj Y]
          (universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).d
            (((Oforget O₂.obj).map f).hom b)) =
      (tensorDifferentials.{v, u, w, m} φ F).val.restrictₛₗ f
        (((tensorDifferentialsUnit.{v, u, w, m} φ F).app X).hom
          (x ⊗ₜ[(Oforget O₂.obj).obj X]
            (universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).d b)) := by
    refine Eq.trans (congrArg (fun z :
      (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val.obj Y ↦
        ((tensorDifferentialsUnit.{v, u, w, m} φ F).app Y).hom
          ((F.val.restrictₛₗ f x) ⊗ₜ[(Oforget O₂.obj).obj Y] z)) hd.symm) ?_
    exact PresheafOfModules.naturality_apply (tensorDifferentialsUnit.{v, u, w, m} φ F) f
      (x ⊗ₜ[(Oforget O₂.obj).obj X]
        (universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).d b)
  refine Eq.trans (congrArg Neg.neg key) ?_
  exact (map_neg ((tensorDifferentials.{v, u, w, m} φ F).val.restrictₛₗ f) _).symm

/-- **The order-one symbol data of the sequence of principal parts.** -/
noncomputable def principalPartsSymbolData :
    OrderOneSymbol (tensorDifferentials.{v, u, w, m} φ F).val F.val where
  δ := principalPartsδ.{v, u, w, m} φ F
  add_left := principalPartsδ_add_left.{v, u, w, m} φ F
  add_right := principalPartsδ_add_right.{v, u, w, m} φ F
  smul_right := principalPartsδ_smul_right.{v, u, w, m} φ F
  leibniz := principalPartsδ_leibniz.{v, u, w, m} φ F
  map := principalPartsδ_map.{v, u, w, m} φ F

/-- The symbol of `principalPartsSymbolData` is `principalPartsδ`. -/
@[simp] theorem principalPartsSymbolData_δ (X : Cᵒᵖ) (b : (Oforget O₂.obj).obj X)
    (x : F.val.obj X) :
    (principalPartsSymbolData.{v, u, w, m} φ F).δ X b x =
      principalPartsδ.{v, u, w, m} φ F X b x := rfl

/-- The symbol of the sequence of principal parts vanishes on scalars coming from `O₁`. -/
theorem principalPartsδ_base (X : Cᵒᵖ) (a : O₁.obj.obj X) (x : F.val.obj X) :
    principalPartsδ.{v, u, w, m} φ F X ((φ.hom.app X).hom a) x = 0 := by
  have hd : (universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).d ((φ.hom.app X).hom a) = 0 :=
    PresheafOfModulesOfCommRing.Derivation'.d_app _ a
  refine Eq.trans (congrArg
    (fun z : (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val.obj X ↦
      -(((tensorDifferentialsUnit.{v, u, w, m} φ F).app X).hom
        (x ⊗ₜ[(Oforget O₂.obj).obj X] z))) hd) ?_
  refine Eq.trans (congrArg
    (fun z ↦ -(((tensorDifferentialsUnit.{v, u, w, m} φ F).app X).hom z))
    (TensorProduct.tmul_zero
      ((moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val.obj X) x)) ?_
  exact Eq.trans (congrArg Neg.neg
    (map_zero ((tensorDifferentialsUnit.{v, u, w, m} φ F).app X).hom)) neg_zero

/-- **The first-order jet sheaf of the sequence of principal parts**: the sheafified tensor
product and the coefficient module, with the scalar action twisted by the symbol. -/
noncomputable abbrev principalPartsJet :
    _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) :=
  jetSheaf.{v, u, w, m} (principalPartsSymbolData.{v, u, w, m} φ F)

/-- The jet operator of the sequence of principal parts has order at most one. -/
theorem principalPartsJetOp_isGlobalDiffOpOfOrder :
    DiffOp.IsGlobalDiffOpOfOrder (underlyingRingSheafMapOfSite φ) 1
      (jetOp.{v, u, w, m} (principalPartsSymbolData.{v, u, w, m} φ F)) :=
  jetOp_isGlobalDiffOpOfOrder.{v, u, w, m} (underlyingRingSheafMapOfSite φ) _
    (fun X a x ↦ principalPartsδ_base.{v, u, w, m} φ F X a x)

/-- **The retraction of the sequence of principal parts onto the jet sheaf**: the morphism
`P¹_{O₂/O₁}(F) ⟶ Jet(F)` supplied by Tag 09CT for the jet operator. -/
noncomputable def principalPartsJetDesc :
    principalPartsOne.{v, u, w, m} φ F ⟶ principalPartsJet.{v, u, w, m} φ F :=
  (existsUnique_descDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F
    (principalPartsJet.{v, u, w, m} φ F) 1
    (jetOp.{v, u, w, m} (principalPartsSymbolData.{v, u, w, m} φ F))
    (principalPartsJetOp_isGlobalDiffOpOfOrder.{v, u, w, m} φ F)).choose

/-- The retraction carries the universal operator of order at most one to the jet
operator. -/
theorem principalPartsJetDesc_universalDiffOp (X : Cᵒᵖ) (x : F.val.obj X) :
    ((principalPartsJetDesc.{v, u, w, m} φ F).val.app X).hom
        (universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X x) =
      jetOp.{v, u, w, m} (principalPartsSymbolData.{v, u, w, m} φ F) X x :=
  congrArg (fun D : DiffOp.GlobalOp F (principalPartsJet.{v, u, w, m} φ F) ↦ D X x)
    (existsUnique_descDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F
      (principalPartsJet.{v, u, w, m} φ F) 1
      (jetOp.{v, u, w, m} (principalPartsSymbolData.{v, u, w, m} φ F))
      (principalPartsJetOp_isGlobalDiffOpOfOrder.{v, u, w, m} φ F)).choose_spec.1


section Comparison

variable (T : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
  (g : tensorDifferentials.{v, u, w, m} φ F ⟶ T)

/-- The pairing attached to a morphism out of the sheafified tensor product: the value of the
morphism on the image of a pure tensor. -/
noncomputable def tensorDifferentialsPairing (X : Cᵒᵖ) (x : F.val.obj X)
    (ω : (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val.obj X) : T.val.obj X :=
  (g.val.app X).hom (((tensorDifferentialsUnit.{v, u, w, m} φ F).app X).hom
    (x ⊗ₜ[(Oforget O₂.obj).obj X] ω))

/-- The pairing is the composite of the sheafification unit with `g`, applied to a pure tensor. -/
private theorem pairing_eq_comp (X : Cᵒᵖ) (x : F.val.obj X)
    (ω : (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val.obj X) :
    tensorDifferentialsPairing.{v, u, w, m} φ F T g X x ω =
      ((tensorDifferentialsUnit.{v, u, w, m} φ F ≫ g.val).app X).hom
        (x ⊗ₜ[(Oforget O₂.obj).obj X] ω) := rfl

/-- The pairing attached to a morphism out of the sheafified tensor product is additive in the
section of `F`. -/
theorem tensorDifferentialsPairing_add_left (X : Cᵒᵖ) (x x' : F.val.obj X)
    (ω : (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val.obj X) :
    tensorDifferentialsPairing.{v, u, w, m} φ F T g X (x + x') ω =
      tensorDifferentialsPairing.{v, u, w, m} φ F T g X x ω +
        tensorDifferentialsPairing.{v, u, w, m} φ F T g X x' ω := by
  rw [pairing_eq_comp, pairing_eq_comp, pairing_eq_comp, TensorProduct.add_tmul]
  exact map_add _ _ _

/-- The pairing attached to a morphism out of the sheafified tensor product is linear in the
section of `F`. -/
theorem tensorDifferentialsPairing_smul_left (X : Cᵒᵖ) (r : (Oforget O₂.obj).obj X)
    (x : F.val.obj X) (ω : (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val.obj X) :
    tensorDifferentialsPairing.{v, u, w, m} φ F T g X (r • x) ω =
      r • tensorDifferentialsPairing.{v, u, w, m} φ F T g X x ω := by
  rw [pairing_eq_comp, pairing_eq_comp]
  exact ((tensorDifferentialsUnit.{v, u, w, m} φ F ≫ g.val).app X).hom.map_smul r
    (x ⊗ₜ[(Oforget O₂.obj).obj X] ω)

/-- The pairing attached to a morphism out of the sheafified tensor product is additive in the
differential. -/
theorem tensorDifferentialsPairing_add_right (X : Cᵒᵖ) (x : F.val.obj X)
    (ω ω' : (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val.obj X) :
    tensorDifferentialsPairing.{v, u, w, m} φ F T g X x (ω + ω') =
      tensorDifferentialsPairing.{v, u, w, m} φ F T g X x ω +
        tensorDifferentialsPairing.{v, u, w, m} φ F T g X x ω' := by
  rw [pairing_eq_comp, pairing_eq_comp, pairing_eq_comp, TensorProduct.tmul_add]
  exact map_add _ _ _

/-- The pairing attached to a morphism out of the sheafified tensor product is linear in the
differential. -/
theorem tensorDifferentialsPairing_smul_right (X : Cᵒᵖ) (r : (Oforget O₂.obj).obj X)
    (x : F.val.obj X) (ω : (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val.obj X) :
    tensorDifferentialsPairing.{v, u, w, m} φ F T g X x (r • ω) =
      r • tensorDifferentialsPairing.{v, u, w, m} φ F T g X x ω := by
  rw [pairing_eq_comp, pairing_eq_comp]
  exact (congrArg ((tensorDifferentialsUnit.{v, u, w, m} φ F ≫ g.val).app X).hom
    ((TensorProduct.mk ((Oforget O₂.obj).obj X) (F.val.obj X)
      ((moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val.obj X) x).map_smul r ω)).trans
    (((tensorDifferentialsUnit.{v, u, w, m} φ F ≫ g.val).app X).hom.map_smul r _)

/-- The pairing attached to a morphism out of the sheafified tensor product is compatible with
restriction. -/
theorem tensorDifferentialsPairing_restr ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) (x : F.val.obj X)
    (ω : (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val.obj X) :
    tensorDifferentialsPairing.{v, u, w, m} φ F T g Y (F.val.restrictₛₗ f x)
        ((moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val.restrictₛₗ f ω) =
      T.val.restrictₛₗ f (tensorDifferentialsPairing.{v, u, w, m} φ F T g X x ω) := by
  refine Eq.trans (congrArg (fun z ↦ (g.val.app Y).hom z)
    (PresheafOfModules.naturality_apply (tensorDifferentialsUnit.{v, u, w, m} φ F) f
      (x ⊗ₜ[(Oforget O₂.obj).obj X] ω))) ?_
  exact PresheafOfModules.naturality_apply g.val f _

/-- **The curried form of a morphism out of the sheafified tensor product**: the morphism
`Ω_{O₂/O₁} ⟶ 𝓗om_{O₂}(F, T)` that pairs a differential with a section of `F`. -/
noncomputable def tensorDifferentialsCurry :
    moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ ⟶ internalHomSheafOfModules F T :=
  ⟨pairingCurry O₂.obj F.val T.val (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val
    (tensorDifferentialsPairing.{v, u, w, m} φ F T g)
    (tensorDifferentialsPairing_add_left.{v, u, w, m} φ F T g)
    (tensorDifferentialsPairing_smul_left.{v, u, w, m} φ F T g)
    (tensorDifferentialsPairing_add_right.{v, u, w, m} φ F T g)
    (tensorDifferentialsPairing_smul_right.{v, u, w, m} φ F T g)
    (tensorDifferentialsPairing_restr.{v, u, w, m} φ F T g)⟩

/-- The curried morphism is pinned by the pairing. -/
theorem tensorDifferentialsCurry_evalTerminal (X : Cᵒᵖ) (x : F.val.obj X)
    (ω : (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val.obj X) :
    evalTerminal O₂.obj F.val T.val
        (((tensorDifferentialsCurry.{v, u, w, m} φ F T g).val.app X).hom ω) x =
      (g.val.app X).hom (((tensorDifferentialsUnit.{v, u, w, m} φ F).app X).hom
        (x ⊗ₜ[(Oforget O₂.obj).obj X] ω)) :=
  pairingCurry_evalTerminal O₂.obj F.val T.val
    (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val
    (tensorDifferentialsPairing.{v, u, w, m} φ F T g)
    (tensorDifferentialsPairing_add_left.{v, u, w, m} φ F T g)
    (tensorDifferentialsPairing_smul_left.{v, u, w, m} φ F T g)
    (tensorDifferentialsPairing_add_right.{v, u, w, m} φ F T g)
    (tensorDifferentialsPairing_smul_right.{v, u, w, m} φ F T g)
    (tensorDifferentialsPairing_restr.{v, u, w, m} φ F T g) X x ω

/-- **Currying is injective**: a morphism out of the sheafified tensor product is determined
by the pairing it induces. -/
theorem hom_ext_of_tensorDifferentialsCurry
    {g₁ g₂ : tensorDifferentials.{v, u, w, m} φ F ⟶ T}
    (h : tensorDifferentialsCurry.{v, u, w, m} φ F T g₁ =
      tensorDifferentialsCurry.{v, u, w, m} φ F T g₂) : g₁ = g₂ := by
  have hpre : tensorDifferentialsUnit.{v, u, w, m} φ F ≫ g₁.val =
      tensorDifferentialsUnit.{v, u, w, m} φ F ≫ g₂.val := by
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x ω
    refine Eq.trans
      (tensorDifferentialsCurry_evalTerminal.{v, u, w, m} φ F T g₁ X x ω).symm ?_
    refine Eq.trans ?_ (tensorDifferentialsCurry_evalTerminal.{v, u, w, m} φ F T g₂ X x ω)
    exact congrArg (fun k : moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ ⟶
        internalHomSheafOfModules F T ↦
      evalTerminal O₂.obj F.val T.val (X := X) ((ConcreteCategory.hom (k.val.app X)) ω) x) h
  refine ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).homEquiv _ _).injective ?_
  exact hpre

end Comparison

section Mono

/-- **The retraction carries the symbol of the universal operator to the symbol component**:
on the image of the pure tensor `x ⊗ d b` the composite of the inclusion with the retraction
is the inclusion of the symbol component. -/
theorem jetDesc_inclusion_toSheafify_tmul_d (X : Cᵒᵖ) (x : F.val.obj X)
    (b : (Oforget O₂.obj).obj X) :
    (((principalPartsJetDesc.{v, u, w, m} φ F)).val.app X).hom
        ((((principalPartsInclusion.{v, u, w, m} φ).app F).val.app X).hom
          (((tensorDifferentialsUnit.{v, u, w, m} φ F).app X).hom
            (x ⊗ₜ[(Oforget O₂.obj).obj X]
              (universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).d b))) =
      ((jetSheafInl.{v, u, w, m}
          (principalPartsSymbolData.{v, u, w, m} φ F)).val.app X).hom
        (((tensorDifferentialsUnit.{v, u, w, m} φ F).app X).hom
          (x ⊗ₜ[(Oforget O₂.obj).obj X]
            (universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).d b)) := by
  have h1 : (((principalPartsInclusion.{v, u, w, m} φ).app F).val.app X).hom
        (((tensorDifferentialsUnit.{v, u, w, m} φ F).app X).hom
          (x ⊗ₜ[(Oforget O₂.obj).obj X]
            (universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).d b)) =
      universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X (b • x) -
        b • universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X x :=
    principalPartsInclusion_toSheafify_tmul_d.{v, u, w, m} φ F X x b
  refine Eq.trans (congrArg
    (fun z ↦ ((principalPartsJetDesc.{v, u, w, m} φ F).val.app X).hom z) h1) ?_
  have hsm := ((principalPartsJetDesc.{v, u, w, m} φ F).val.app X).hom.map_smul b
    (universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X x)
  refine Eq.trans (map_sub ((principalPartsJetDesc.{v, u, w, m} φ F).val.app X).hom _ _) ?_
  refine Eq.trans (congrArg₂ (fun pp qq ↦ pp - qq)
    (principalPartsJetDesc_universalDiffOp.{v, u, w, m} φ F X (b • x))
    (Eq.trans hsm (congrArg (fun z ↦ b • z)
      (principalPartsJetDesc_universalDiffOp.{v, u, w, m} φ F X x)))) ?_
  refine OrderOneSymbol.Sections.ext' (principalPartsSymbolData.{v, u, w, m} φ F) ?_ ?_
  · change (0 : (tensorDifferentials.{v, u, w, m} φ F).val.obj X) -
        (b • (0 : (tensorDifferentials.{v, u, w, m} φ F).val.obj X) +
          principalPartsδ.{v, u, w, m} φ F X b x) =
      ((tensorDifferentialsUnit.{v, u, w, m} φ F).app X).hom
        (x ⊗ₜ[(Oforget O₂.obj).obj X]
          (universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).d b)
    rw [smul_zero, zero_add, zero_sub, principalPartsδ]
    exact neg_neg _
  · change b • x - b • x = (0 : F.val.obj X)
    rw [sub_self]

/-- **The retraction carries the inclusion of the sequence of principal parts to the
inclusion of the symbol component into the jets.** -/
theorem principalPartsInclusion_comp_jetDesc :
    (principalPartsInclusion.{v, u, w, m} φ).app F ≫
        principalPartsJetDesc.{v, u, w, m} φ F =
      jetSheafInl.{v, u, w, m} (principalPartsSymbolData.{v, u, w, m} φ F) := by
  refine hom_ext_of_tensorDifferentialsCurry.{v, u, w, m} φ F _ ?_
  refine (existsUnique_descDerivation.{v, u, w, m} O₁ O₂ φ _
    ((universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).postcomp
      (tensorDifferentialsCurry.{v, u, w, m} φ F _
        (jetSheafInl.{v, u, w, m}
          (principalPartsSymbolData.{v, u, w, m} φ F))).val)).unique ?_ rfl
  ext X b
  refine hom_ext_apply fun V x ↦ ?_
  have hd : (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val.map V.unop.hom.op
        ((universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).d b) =
      (universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).d
        (((Oforget O₂.obj).map V.unop.hom.op).hom b) :=
    ((universalDerivationOfSite.{v, u, w, m} O₁ O₂ φ).d_map V.unop.hom.op b).symm
  refine Eq.trans (congrArg
    (fun z : (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val.obj (op V.unop.left) ↦
      tensorDifferentialsPairing.{v, u, w, m} φ F _
        ((principalPartsInclusion.{v, u, w, m} φ).app F ≫
          principalPartsJetDesc.{v, u, w, m} φ F) (op V.unop.left) x z) hd) ?_
  refine Eq.trans (jetDesc_inclusion_toSheafify_tmul_d.{v, u, w, m} φ F (op V.unop.left) x
    (((Oforget O₂.obj).map V.unop.hom.op).hom b)) ?_
  exact (congrArg
    (fun z : (moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ).val.obj (op V.unop.left) ↦
      tensorDifferentialsPairing.{v, u, w, m} φ F _
        (jetSheafInl.{v, u, w, m} (principalPartsSymbolData.{v, u, w, m} φ F))
        (op V.unop.left) x z) hd).symm

/-- **The inclusion of the sequence of principal parts is a monomorphism.** -/
instance mono_principalPartsInclusion_app :
    Mono ((principalPartsInclusion.{v, u, w, m} φ).app F) := by
  have h : Mono ((principalPartsInclusion.{v, u, w, m} φ).app F ≫
      principalPartsJetDesc.{v, u, w, m} φ F) := by
    rw [principalPartsInclusion_comp_jetDesc.{v, u, w, m} φ F]
    exact mono_jetSheafInl.{v, u, w, m} (principalPartsSymbolData.{v, u, w, m} φ F)
  exact mono_of_mono _ (principalPartsJetDesc.{v, u, w, m} φ F)

/-- **The sequence of principal parts is a short exact sequence.** -/
@[stacks 09CW "field 8 ALONE: the short exact sequence of the principal-parts sequence, \
now",
  stacks 09DG "the sequence for a term of the standard resolution",
  sga "6 II AppII.1.2.4" "n = 1"]
theorem exists_shortExact_principalPartsSequence' :
    ∃ h : (principalPartsInclusion.{v, u, w, m} φ).app F ≫
        (principalPartsProjection.{v, u, w, m}
          (underlyingRingSheafMapOfSite φ) 1).app F = 0,
      (ShortComplex.mk ((principalPartsInclusion.{v, u, w, m} φ).app F)
        ((principalPartsProjection.{v, u, w, m}
          (underlyingRingSheafMapOfSite φ) 1).app F) h).ShortExact :=
  exists_shortExact_principalPartsSequence.{v, u, w, m} φ F

end Mono

end PrincipalParts

end AlgebraicGeometry.SheafOfModules

end
