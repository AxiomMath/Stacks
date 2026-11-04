module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatChangeOfRings
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PrincipalPartsUniversal
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
import StacksCore.Tactic.StacksAttribute

/-!
# The symbol of a differential operator of order at most one

Let `φ : O₁ ⟶ O₂` be a morphism of sheaves of commutative rings on a site and let `F` be a
sheaf of `O₂`-modules. For a differential operator `D : F → P` of order at most one, the
assignment `x ⊗ d b ↦ D (b • x) - b • D x` is well defined and linear: this is the *symbol*
of `D`. Applied to the universal operator of order at most one out of `F`, whose target is
the sheaf of principal parts `P¹_{O₂/O₁}(F)` (Tag 09CT), it produces a morphism of presheaves
of modules
`F ⊗_{O₂} Ω_{O₂/O₁} ⟶ P¹_{O₂/O₁}(F)`
natural in `F`, where `Ω_{O₂/O₁}` here means the *presheaf* `X ↦ Ω[O₂(X)⁄O₁(X)]` of objectwise
relative Kähler differentials. This is the first map of the sequence of principal parts of
Tag 09CW, before sheafification; see the implementation notes for what remains.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.diffOpBracket`: the commutator of an additive operator
  with a scalar, as a linear map. Its linearity *is* the order-at-most-one condition.
* `AlgebraicGeometry.SheafOfModules.diffOpSymbol`: the symbol of an order-at-most-one
  operator `D : M → P` of modules over a ring map `R → S`, the `S`-linear map
  `M ⊗[S] Ω[S⁄R] → P` carrying `x ⊗ d b` to `D (b • x) - b • D x`.
* `AlgebraicGeometry.SheafOfModules.relativeDifferentialsPresheaf`: the presheaf of
  objectwise relative Kähler differentials `X ↦ Ω[O₂(X)⁄O₁(X)]`.
* `AlgebraicGeometry.SheafOfModules.principalPartsSymbolSource`: the objectwise tensor
  product of a sheaf of modules with that presheaf.
* `AlgebraicGeometry.SheafOfModules.principalPartsSymbolApp` and
  `AlgebraicGeometry.SheafOfModules.principalPartsSymbol`: the symbol of the universal
  differential operator of order at most one, objectwise and as a morphism of presheaves of
  modules.

## Main results

* `AlgebraicGeometry.SheafOfModules.diffOpBracket_mul`: the Leibniz rule satisfied by the
  commutator, which is what makes the symbol exist.
* `AlgebraicGeometry.SheafOfModules.diffOpSymbol_tmul_D`: the symbol is pinned by
  `x ⊗ d b ↦ D (b • x) - b • D x`.
* `AlgebraicGeometry.SheafOfModules.tensorKaehler_ext`: two linear maps out of
  `M ⊗[S] Ω[S⁄R]` agree as soon as they agree on the `x ⊗ d b`.
* `AlgebraicGeometry.SheafOfModules.isGlobalDiffOpOfOrder_one_base`,
  `AlgebraicGeometry.SheafOfModules.isGlobalDiffOpOfOrder_one_bracket` and
  `AlgebraicGeometry.SheafOfModules.globalDiffOp_naturality`: the sectionwise content of a
  global differential operator of order at most one — linearity over the base, linearity of
  each commutator, and compatibility with restriction.
* `AlgebraicGeometry.SheafOfModules.principalPartsSymbolApp_tmul_d`,
  `AlgebraicGeometry.SheafOfModules.principalPartsSymbolApp_naturality` and
  `AlgebraicGeometry.SheafOfModules.principalPartsSymbol_naturality`: the symbol of the
  universal operator is pinned on `x ⊗ d b`, compatible with restriction of sections, and
  natural in the coefficient module.

## Implementation notes

The order-at-most-one hypothesis enters exactly once, as the linearity of each commutator
`x ↦ D (b • x) - b • D x`; the Leibniz rule `diffOpBracket_mul` is a rearrangement of that
linearity, and nothing else about `DiffOp.IsDiffOpOfOrder` is used. That is why the
commutative-algebra core is stated for a bare additive map `D : M →+ P` together with two
equations rather than for a bundled differential operator: it is then applicable both to the
universal operator of `AlgebraicGeometry.SheafOfModules.moduleOfPrincipalParts` and, with no
change, to any other order-at-most-one operator.

Spelling discipline. The structure sheaf of a sheaf of commutative rings has two
definitionally equal but syntactically distinct descriptions as a presheaf of rings: through
`Stacks.SheafOfModules.Tensor.ringSheaf`, which is what `SheafOfModules`
is taken over, and through `AlgebraicGeometry.SheafOfModules.ringPresheaf`, which is what the
objectwise tensor product is taken over. Neither unfolds at instance or at reducible
transparency, because `CategoryTheory.sheafCompose` sits between them, so `rw` and `simp`
cannot cross from one to the other even though `rfl` identifies them. Three devices are used
instead, and no transparency option is set: `sectionsModuleOfSite` restates the module
structure in the second spelling, so that instance search finds it; `diffOpSymbol_restriction`
states the compatibility with restriction for *plain maps* with the semilinearity and
intertwining equations as hypotheses, and is applied by `exact`; and the rewriting steps are
`Eq.trans` and `congrArg` rather than `rw`, since those are checked up to definitional
equality. The same lemma stated with `rw` in place of `exact` does not go through.

Universes. The site is `C : Type u` with `Category.{v} C`, the structure sheaves are
`CommRingCat.{w}`-valued, and coefficient sheaves of modules live in
`SheafOfModules.{max u v w m}` for a free universe parameter `m`. This is the universe in
which Tag 09CT is available and it is forced rather than chosen; see the universe discussion
accompanying `AlgebraicGeometry.SheafOfModules.derivationsFunctor_isCorepresentable`
(Stacks 04BL). The presheaf of objectwise
differentials lives in `PresheafOfModules.{w}`, the universe of the structure sheaf, which is
why the objectwise tensor product of `StacksFrontier/CategoryTheory/Sites/Modules/Flat.lean` is
used: it allows the two module universes to differ, whereas Mathlib's monoidal structure on
presheaves of modules requires them to agree. Nothing is narrowed: `u`, `v`, `w`, `m` are
free and the site is an arbitrary category, not assumed small.

What is *not* here. Tag 09CW asks for a short exact sequence
`0 → Ω_{O₂/O₁} ⊗ F → P¹(F) → F → 0`, with `Ω_{O₂/O₁}` the corepresenting *sheaf* of Tag 04BL
and the tensor product the sheafified one. Passing from the morphism constructed here to that
one needs two comparison isomorphisms that this branch does not yet have: Tag 08TP, that
`Ω_{O₂/O₁}` is the sheaf associated to `relativeDifferentialsPresheaf`, and Tag 0GMW at
independent module and ring universes, that sheafification commutes with the tensor product.
Exactness is then the sectionwise statement
`LinearMap.IsDifferentialOperatorOfOrderLE.exists_shortExact_principalParts` (Tag 09CN)
together with Tag 09CV. The retraction `P¹(F) ⟶ F` and the functoriality of `P¹` are already
available as `AlgebraicGeometry.SheafOfModules.principalPartsProjection` and
`AlgebraicGeometry.SheafOfModules.principalPartsFunctor`.

## References

* [Stacks Project, Tag 09CT](https://stacks.math.columbia.edu/tag/09CT), the sheaf of
  principal parts, and [Tag 09CW](https://stacks.math.columbia.edu/tag/09CW), the sequence of
  principal parts.
* [Stacks Project, Tag 09CN](https://stacks.math.columbia.edu/tag/09CN), the
  commutative-algebra form of that sequence.
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), relative
  differentials.
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct

universe v u w m t

namespace AlgebraicGeometry.SheafOfModules

/-- The module structure that the sections of a sheaf of modules over the sheaf of rings
underlying a sheaf of commutative rings already carry, written over the sections of the
underlying *presheaf* of rings. -/
local instance sectionsModuleOfSite {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {O : Sheaf J CommRingCat.{w}}
    {G : _root_.SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf O)} {X : Cᵒᵖ} :
    Module ((ringPresheaf O.obj).obj X) (G.val.obj X) :=
  inferInstanceAs (Module ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X) (G.val.obj X))

section Symbol

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {M P : Type*} [AddCommGroup M] [Module S M] [AddCommGroup P] [Module S P]
  (D : M →+ P)
  (hbracket : ∀ (b r : S) (x : M), D (b • r • x) - b • D (r • x) = r • (D (b • x) - b • D x))

/-- The commutator of an additive operator `D : M → P` with a scalar `b : S`, as an
`S`-linear map. The hypothesis `hbracket` is exactly the `S`-linearity of this commutator,
which is what it means for `D` to be a differential operator of order at most one. -/
def diffOpBracket (b : S) : M →ₗ[S] P where
  toFun x := D (b • x) - b • D x
  map_add' x y := by
    simp only [smul_add, map_add]
    abel
  map_smul' r x := hbracket b r x

/-- The commutator `diffOpBracket D hbracket b` sends `x` to `D (b • x) - b • D x`. -/
@[simp]
lemma diffOpBracket_apply (b : S) (x : M) :
    diffOpBracket D hbracket b x = D (b • x) - b • D x := rfl

/-- The commutator with a scalar is additive in the scalar. -/
lemma diffOpBracket_add (b b' : S) :
    diffOpBracket D hbracket (b + b') =
      diffOpBracket D hbracket b + diffOpBracket D hbracket b' := by
  ext x
  simp only [diffOpBracket_apply, LinearMap.add_apply, add_smul, map_add]
  abel

/-- **The Leibniz rule for the symbol.** The commutator of `D` with a product of scalars is
determined by the commutators with the factors; this is where order at most one is used. -/
lemma diffOpBracket_mul (b b' : S) :
    diffOpBracket D hbracket (b * b') =
      b • diffOpBracket D hbracket b' + b' • diffOpBracket D hbracket b := by
  ext x
  simp only [diffOpBracket_apply, LinearMap.add_apply, LinearMap.smul_apply, mul_smul]
  rw [sub_eq_iff_eq_add.1 (hbracket b b' x), smul_sub, smul_sub, smul_comm b' b (D x)]
  abel

/-- The commutator of `D` with a scalar coming from the base ring vanishes: that is the
linearity of `D` over the base ring. -/
lemma diffOpBracket_algebraMap
    (hbase : ∀ (a : R) (x : M), D (algebraMap R S a • x) = algebraMap R S a • D x) (a : R) :
    diffOpBracket D hbracket (algebraMap R S a) = 0 := by
  ext x
  simp only [diffOpBracket_apply, LinearMap.zero_apply, hbase a x, sub_self]

/-- **The symbol map.** For a differential operator `D : M → P` of order at most one, the
`S`-linear map `M ⊗[S] Ω[S⁄R] → P` carrying `x ⊗ d b` to `D (b • x) - b • D x`. It is the
map `ι` of the sequence of principal parts, in its commutative-algebra form. -/
noncomputable def diffOpSymbol
    (hbase : ∀ (a : R) (x : M), D (algebraMap R S a • x) = algebraMap R S a • D x) :
    M ⊗[S] Ω[S⁄R] →ₗ[S] P :=
  let : Module R (M →ₗ[S] P) := Module.compHom _ (algebraMap R S)
  let : IsScalarTower R S (M →ₗ[S] P) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  TensorProduct.lift (Derivation.liftKaehlerDifferential
    (Derivation.mk'
      { toFun := diffOpBracket D hbracket
        map_add' := diffOpBracket_add D hbracket
        map_smul' := fun a b ↦ by
          rw [RingHom.id_apply, Algebra.smul_def a b, diffOpBracket_mul D hbracket,
            diffOpBracket_algebraMap D hbracket hbase, smul_zero, add_zero]
          rfl }
      (diffOpBracket_mul D hbracket))).flip

/-- The symbol map sends `x ⊗ d b` to `D (b • x) - b • D x`. -/
@[simp]
lemma diffOpSymbol_tmul_D
    (hbase : ∀ (a : R) (x : M), D (algebraMap R S a • x) = algebraMap R S a • D x)
    (x : M) (b : S) :
    diffOpSymbol D hbracket hbase (x ⊗ₜ[S] KaehlerDifferential.D R S b) =
      D (b • x) - b • D x := by
  simp only [diffOpSymbol, TensorProduct.lift.tmul, LinearMap.flip_apply,
    Derivation.liftKaehlerDifferential_comp_D, Derivation.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, diffOpBracket_apply]

/-- Two linear maps out of `M ⊗[S] Ω[S⁄R]` agree as soon as they agree on the elements
`x ⊗ d b`, because the differentials `d b` span `Ω[S⁄R]`. -/
lemma tensorKaehler_ext {N : Type*} [AddCommGroup N] [Module S N]
    {f g : M ⊗[S] Ω[S⁄R] →ₗ[S] N}
    (h : ∀ (x : M) (b : S),
      f (x ⊗ₜ[S] KaehlerDifferential.D R S b) =
        g (x ⊗ₜ[S] KaehlerDifferential.D R S b)) :
    f = g := by
  refine TensorProduct.ext' fun x ω ↦ ?_
  have key : f.comp (TensorProduct.mk S M Ω[S⁄R] x) =
      g.comp (TensorProduct.mk S M Ω[S⁄R] x) :=
    LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation R S) (h x)
  exact LinearMap.congr_fun key ω

end Symbol

section Restriction

/-- **Plain-map form of the compatibility of the symbol with restriction.** If an additive
`μ : M → M'` and an additive `π : P → P'` are semilinear along a ring map `σ`, and intertwine
two additive operators `D`, `D'`, then the two symbols agree. The hypotheses are given as
plain maps rather than as morphisms of presheaves of modules, and the lemma is applied by
`exact`: the ring of sections of a sheaf of commutative rings has two definitionally equal
but syntactically distinct spellings, and `rw` and `simp` cannot cross between them. -/
lemma diffOpSymbol_restriction {T T' : Type*} [Ring T] [Ring T']
    {M M' P P' : Type*} [AddCommGroup M] [Module T M] [AddCommGroup P] [Module T P]
    [AddCommGroup M'] [Module T' M'] [AddCommGroup P'] [Module T' P']
    (σ : T →+* T') (μ : M →+ M') (π : P →+ P')
    (hμ : ∀ (r : T) (y : M), μ (r • y) = σ r • μ y)
    (hπ : ∀ (r : T) (y : P), π (r • y) = σ r • π y)
    (D : M →+ P) (D' : M' →+ P') (hD : ∀ y, D' (μ y) = π (D y)) (b : T) (x : M) :
    D' (σ b • μ x) - σ b • D' (μ x) = π (D (b • x) - b • D x) := by
  rw [map_sub, hπ, ← hD, ← hD, hμ]

end Restriction

section Sections

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O₁ O₂ : Sheaf J RingCat.{w}} (phi : O₁ ⟶ O₂)
  {F G : _root_.SheafOfModules.{m} O₂} {D : DiffOp.GlobalOp F G}

/-- The sections of a global differential operator of order at most one are linear over the
sections of the base sheaf of rings. -/
lemma isGlobalDiffOpOfOrder_one_base
    (hD : DiffOp.IsGlobalDiffOpOfOrder phi 1 D) (X : Cᵒᵖ)
    (a : O₁.obj.obj X) (x : F.val.obj X) :
    D X (DiffOp.sectionRingHom phi X a • x) = DiffOp.sectionRingHom phi X a • D X x :=
  DiffOp.RawOp.isO1Linear_of_isDiffOpOfOrder phi 1 (D.restrict X.unop) (hD X.unop)
    (Over.mk (𝟙 X.unop)) a x

/-- The commutator of a global differential operator of order at most one with a section of
the structure sheaf is linear over the sections of the structure sheaf. This is the
sectionwise content of "order at most one". -/
lemma isGlobalDiffOpOfOrder_one_bracket
    (hD : DiffOp.IsGlobalDiffOpOfOrder phi 1 D) (X : Cᵒᵖ)
    (b r : O₂.obj.obj X) (x : F.val.obj X) :
    D X (b • r • x) - b • D X (r • x) = r • (D X (b • x) - b • D X x) := by
  have h := ((hD X.unop).2.2 (Over.mk (𝟙 X.unop)) b).2 (Over.mk (𝟙 X.unop)) r x
  simp only [Over.mk_left, op_unop, DiffOp.RawOp.commutator, Over.mk_hom, op_id,
    CategoryTheory.Functor.map_id, RingCat.hom_id, RingHom.id_apply, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk] at h
  exact h

/-- A global differential operator is compatible with restriction of sections. -/
lemma globalDiffOp_naturality {k : ℕ}
    (hD : DiffOp.IsGlobalDiffOpOfOrder phi k D) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.val.obj X) :
    D Y (F.val.map f x) = G.val.map f (D X x) :=
  DiffOp.RawOp.isNatural_of_isDiffOpOfOrder phi k (D.restrict X.unop) (hD X.unop)
    (Over.mk f.unop) (Over.mk (𝟙 X.unop)) (Over.homMk f.unop (by simp)) x

end Sections

section PrincipalPartsSymbol

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O₁ O₂ : Sheaf J CommRingCat.{w}} (φ : O₁ ⟶ O₂)

/-- The morphism of underlying sheaves of rings induced by a morphism of sheaves of
commutative rings: `Stacks.FlatChangeOfRings.ringSheafMap`. -/
alias underlyingRingSheafMapOfSite := Stacks.FlatChangeOfRings.ringSheafMap

/-- The presheaf of objectwise relative differentials, `X ↦ Ω[O₂(X)⁄O₁(X)]`. -/
noncomputable abbrev relativeDifferentialsPresheaf :
    PresheafOfModules.{w} (ringPresheaf O₂.obj) :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom

variable (F : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))

/-- The objectwise tensor product of a sheaf of modules with the presheaf of objectwise
relative differentials: the source of the symbol of the universal order-one operator. -/
noncomputable abbrev principalPartsSymbolSource :
    PresheafOfModules.{max u v w m} (ringPresheaf O₂.obj) :=
  PresheafOfModules.tensorObj F.val (relativeDifferentialsPresheaf φ)

/-- The value at an object of the symbol of the universal differential operator of order at
most one: the linear map carrying `x ⊗ d b` to `D (b • x) - b • D x`. -/
@[ega "IV 16.11.1" "special case"]
noncomputable def principalPartsSymbolApp (X : Cᵒᵖ) :
    (principalPartsSymbolSource.{v, u, w, m} φ F).obj X ⟶
      (moduleOfPrincipalParts.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1).val.obj X :=
  let : Module ((ringPresheaf O₂.obj).obj X)
      ((moduleOfPrincipalParts.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1).val.obj X) :=
    inferInstanceAs (Module ((Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj.obj X) _)
  let : Algebra (O₁.obj.obj X) ((ringPresheaf O₂.obj).obj X) := (φ.hom.app X).hom.toAlgebra
  ModuleCat.ofHom (diffOpSymbol
    (universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X)
    (isGlobalDiffOpOfOrder_one_bracket _
      (universalDiffOp_isGlobalDiffOpOfOrder.{v, u, w, m}
        (underlyingRingSheafMapOfSite φ) F 1) X)
    (fun a x ↦ isGlobalDiffOpOfOrder_one_base _
      (universalDiffOp_isGlobalDiffOpOfOrder.{v, u, w, m}
        (underlyingRingSheafMapOfSite φ) F 1) X a x))

/-- **The symbol is pinned by its values on `x ⊗ d b`:** it carries `x ⊗ d b` to
`D (b • x) - b • D x`, where `D` is the universal differential operator of order at most
one out of `F`. -/
lemma principalPartsSymbolApp_tmul_d (X : Cᵒᵖ) (x : F.val.obj X)
    (b : (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj.obj X) :
    (principalPartsSymbolApp.{v, u, w, m} φ F X).hom
        (x ⊗ₜ[(ringPresheaf O₂.obj).obj X]
          CommRingCat.KaehlerDifferential.d (f := φ.hom.app X) b) =
      universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X (b • x) -
        b • universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X x := by
  let : Algebra (O₁.obj.obj X) ((ringPresheaf O₂.obj).obj X) := (φ.hom.app X).hom.toAlgebra
  apply diffOpSymbol_tmul_D
  exact fun a y ↦ isGlobalDiffOpOfOrder_one_base _
    (universalDiffOp_isGlobalDiffOpOfOrder.{v, u, w, m}
      (underlyingRingSheafMapOfSite φ) F 1) X a y

/-- The symbol of the universal operator intertwines a semilinear map of coefficients and a
semilinear map of principal parts that intertwine the universal operators. -/
private lemma principalPartsSymbolApp_intertwine
    (G : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (X Y : Cᵒᵖ)
    (σ : (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj.obj X →+*
      (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj.obj Y)
    (μ : F.val.obj X →+ G.val.obj Y)
    (π : (moduleOfPrincipalParts.{v, u, w, m}
        (underlyingRingSheafMapOfSite φ) F 1).val.obj X →+
      (moduleOfPrincipalParts.{v, u, w, m} (underlyingRingSheafMapOfSite φ) G 1).val.obj Y)
    (hμ : ∀ (r : (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj.obj X) (y : F.val.obj X),
      μ (r • y) = σ r • μ y)
    (hπ : ∀ (r : (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj.obj X)
      (y : (moduleOfPrincipalParts.{v, u, w, m}
        (underlyingRingSheafMapOfSite φ) F 1).val.obj X), π (r • y) = σ r • π y)
    (hD : ∀ y, universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) G 1 Y (μ y) =
      π (universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X y))
    (b : (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj.obj X) (x : F.val.obj X) :
    (principalPartsSymbolApp.{v, u, w, m} φ G Y).hom
        (μ x ⊗ₜ[(ringPresheaf O₂.obj).obj Y]
          CommRingCat.KaehlerDifferential.d (f := φ.hom.app Y) (σ b)) =
      π ((principalPartsSymbolApp.{v, u, w, m} φ F X).hom
        (x ⊗ₜ[(ringPresheaf O₂.obj).obj X]
          CommRingCat.KaehlerDifferential.d (f := φ.hom.app X) b)) := by
  refine Eq.trans (principalPartsSymbolApp_tmul_d.{v, u, w, m} φ G Y (μ x) (σ b))
    (Eq.trans ?_ (congrArg π (principalPartsSymbolApp_tmul_d.{v, u, w, m} φ F X x b).symm))
  exact diffOpSymbol_restriction σ μ π hμ hπ
    (universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1 X)
    (universalDiffOp.{v, u, w, m} (underlyingRingSheafMapOfSite φ) G 1 Y) hD b x

/-- **The symbol is compatible with restriction of sections**, hence assembles into a
morphism of presheaves of modules. -/
lemma principalPartsSymbolApp_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (principalPartsSymbolSource.{v, u, w, m} φ F).map f ≫
        (ModuleCat.restrictScalars ((ringPresheaf O₂.obj).map f).hom).map
          (principalPartsSymbolApp.{v, u, w, m} φ F Y) =
      principalPartsSymbolApp.{v, u, w, m} φ F X ≫
        (moduleOfPrincipalParts.{v, u, w, m}
          (underlyingRingSheafMapOfSite φ) F 1).val.map f := by
  let : Algebra (O₁.obj.obj X) ((ringPresheaf O₂.obj).obj X) := (φ.hom.app X).hom.toAlgebra
  apply ModuleCat.hom_ext
  apply tensorKaehler_ext
  intro x b
  show (principalPartsSymbolApp.{v, u, w, m} φ F Y).hom
      ((principalPartsSymbolSource.{v, u, w, m} φ F).map f
        (x ⊗ₜ[(ringPresheaf O₂.obj).obj X]
          CommRingCat.KaehlerDifferential.d (f := φ.hom.app X) b)) =
    ((moduleOfPrincipalParts.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1).val.map f)
      ((principalPartsSymbolApp.{v, u, w, m} φ F X).hom
        (x ⊗ₜ[(ringPresheaf O₂.obj).obj X]
          CommRingCat.KaehlerDifferential.d (f := φ.hom.app X) b))
  have hd : (relativeDifferentialsPresheaf φ).map f
        (CommRingCat.KaehlerDifferential.d (f := φ.hom.app X) b) =
      CommRingCat.KaehlerDifferential.d (f := φ.hom.app Y) ((O₂.obj.map f) b) :=
    PresheafOfModules.DifferentialsConstruction.relativeDifferentials'_map_d φ.hom f b
  have hnat := globalDiffOp_naturality (underlyingRingSheafMapOfSite φ)
    (universalDiffOp_isGlobalDiffOpOfOrder.{v, u, w, m}
      (underlyingRingSheafMapOfSite φ) F 1) f
  let xf : F.val.obj Y := F.val.map f x
  refine Eq.trans (congrArg (fun z : (relativeDifferentialsPresheaf φ).obj Y ↦
    (principalPartsSymbolApp.{v, u, w, m} φ F Y).hom
      (F.val.map f x ⊗ₜ[(ringPresheaf O₂.obj).obj Y] z)) hd) ?_
  exact principalPartsSymbolApp_intertwine.{v, u, w, m} φ F F X Y
    ((Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj.map f).hom (F.val.map f).hom.toAddMonoidHom
    ((moduleOfPrincipalParts.{v, u, w, m}
      (underlyingRingSheafMapOfSite φ) F 1).val.map f).hom.toAddMonoidHom
    (fun r y ↦ PresheafOfModules.map_smul F.val f r y)
    (fun r y ↦ PresheafOfModules.map_smul _ f r y) hnat b x

/-- **The symbol of the universal differential operator of order at most one**, as a morphism
of presheaves of modules from the objectwise tensor product `F ⊗ Ω` of `F` with the presheaf
of objectwise relative differentials to the sheaf of principal parts of order at most one.
It is the map `x ⊗ d b ↦ D (b • x) - b • D x`, that is the first map of the sequence of
principal parts, before sheafification. -/
@[ega "IV 16.11.1" "special case"]
noncomputable def principalPartsSymbol :
    principalPartsSymbolSource.{v, u, w, m} φ F ⟶
      (moduleOfPrincipalParts.{v, u, w, m} (underlyingRingSheafMapOfSite φ) F 1).val where
  app X := principalPartsSymbolApp.{v, u, w, m} φ F X
  naturality f := principalPartsSymbolApp_naturality.{v, u, w, m} φ F f

/-- The component of `principalPartsSymbol` at `X` is `principalPartsSymbolApp φ F X`. -/
@[simp]
lemma principalPartsSymbol_app (X : Cᵒᵖ) :
    (principalPartsSymbol.{v, u, w, m} φ F).app X =
      principalPartsSymbolApp.{v, u, w, m} φ F X := rfl

/-- **The symbol is natural in the coefficient module.** Tensoring a morphism `f : F ⟶ G`
with the presheaf of relative differentials and then taking the symbol of `G` is the symbol
of `F` followed by the induced morphism of sheaves of principal parts. -/
lemma principalPartsSymbol_naturality
    (G : _root_.SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (f : F ⟶ G) :
    (PresheafOfModules.tensorRight (relativeDifferentialsPresheaf φ)).map f.val ≫
        principalPartsSymbol.{v, u, w, m} φ G =
      principalPartsSymbol.{v, u, w, m} φ F ≫
        (principalPartsMap.{v, u, w, m} (underlyingRingSheafMapOfSite φ) f 1).val := by
  apply _root_.PresheafOfModules.hom_ext
  intro X
  let : Algebra (O₁.obj.obj X) ((ringPresheaf O₂.obj).obj X) := (φ.hom.app X).hom.toAlgebra
  apply ModuleCat.hom_ext
  apply tensorKaehler_ext
  intro x b
  exact principalPartsSymbolApp_intertwine.{v, u, w, m} φ F G X X (RingHom.id _)
    (f.val.app X).hom.toAddMonoidHom
    ((principalPartsMap.{v, u, w, m}
      (underlyingRingSheafMapOfSite φ) f 1).val.app X).hom.toAddMonoidHom
    (fun r y ↦ (f.val.app X).hom.map_smul r y)
    (fun r y ↦ ((principalPartsMap.{v, u, w, m}
      (underlyingRingSheafMapOfSite φ) f 1).val.app X).hom.map_smul r y)
    (fun y ↦ (principalPartsMap_universalDiffOp.{v, u, w, m}
      (underlyingRingSheafMapOfSite φ) f 1 X y).symm) b x

end PrincipalPartsSymbol

end AlgebraicGeometry.SheafOfModules

end
